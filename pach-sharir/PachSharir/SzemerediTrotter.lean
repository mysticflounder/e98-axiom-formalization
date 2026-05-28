/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Mathlib
import CrossingLemma

/-!
# Szemerédi–Trotter from the multigraph crossing lemma

Classical point–line incidence bound in `ℝ²`, proved *conditionally* on the
multigraph crossing lemma `CrossingLemma.PDZ.CrossingLemmaMultigraphStatement`,
which enters as the single hypothesis `hCL`. This is internal infrastructure
toward Pach–de Zeeuw Theorem 2.3, not a verbatim paper statement.
-/

set_option linter.style.longLine false

namespace PachSharir.ST

open scoped Classical
open CrossingLemma.PDZ

/-- A line in `ℝ²`: the zero set of a nonzero affine form `a·x + b·y - c`. -/
def IsAffineLine (ℓ : Set (ℝ × ℝ)) : Prop :=
  ∃ a b c : ℝ, (a, b) ≠ (0, 0) ∧ ℓ = {p : ℝ × ℝ | a * p.1 + b * p.2 = c}

/-- Point–line incidence count `|I(P, L)|`. -/
noncomputable def incidences (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ))) : ℕ :=
  ((P ×ˢ L).filter (fun pℓ => pℓ.1 ∈ pℓ.2)).card

/-- The Szemerédi–Trotter bound, conditional on the crossing lemma. -/
def SzemerediTrotterStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ))),
      (∀ ℓ ∈ L, IsAffineLine ℓ) →
        (incidences P L : ℝ) ≤
          C * ((P.card : ℝ) ^ ((2 : ℝ) / 3) * (L.card : ℝ) ^ ((2 : ℝ) / 3)
                + P.card + L.card)

/-- If two affine lines are parallel (`a₁·b₂ = a₂·b₁`) and share a point, they
coincide. Auxiliary to `encard_inter_le_one_of_lines`. -/
lemma affineLine_eq_of_parallel
    {a₁ b₁ c₁ a₂ b₂ c₂ : ℝ}
    (hℓ₁ : ((a₁, b₁) : ℝ × ℝ) ≠ (0, 0)) (hℓ₂ : ((a₂, b₂) : ℝ × ℝ) ≠ (0, 0))
    (hdet : a₁ * b₂ = a₂ * b₁)
    {p : ℝ × ℝ}
    (hp₁ : a₁ * p.1 + b₁ * p.2 = c₁) (hp₂ : a₂ * p.1 + b₂ * p.2 = c₂) :
    {q : ℝ × ℝ | a₁ * q.1 + b₁ * q.2 = c₁} = {q : ℝ × ℝ | a₂ * q.1 + b₂ * q.2 = c₂} := by
  -- Extract a nonzero scalar `λ` with `(a₂, b₂) = λ • (a₁, b₁)`.
  have hne₁ : a₁ ≠ 0 ∨ b₁ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hℓ₁ (Prod.ext h.1 h.2)
  obtain ⟨lam, hlam_a, hlam_b⟩ : ∃ lam : ℝ, a₂ = lam * a₁ ∧ b₂ = lam * b₁ := by
    rcases hne₁ with ha | hb
    · refine ⟨a₂ / a₁, ?_, ?_⟩
      · field_simp
      · have : a₁ * b₂ = a₂ * b₁ := hdet
        field_simp
        nlinarith [this]
    · refine ⟨b₂ / b₁, ?_, ?_⟩
      · have : a₁ * b₂ = a₂ * b₁ := hdet
        field_simp
        nlinarith [this]
      · field_simp
  -- `λ ≠ 0`, else `(a₂, b₂) = 0`.
  have hlam_ne : lam ≠ 0 := by
    rintro rfl
    simp only [zero_mul] at hlam_a hlam_b
    exact hℓ₂ (Prod.ext hlam_a hlam_b)
  -- The constant is scaled too.
  have hc : c₂ = lam * c₁ := by
    rw [← hp₂, ← hp₁, hlam_a, hlam_b]; ring
  -- Now the two equations are scalar multiples; equate the sets.
  ext q
  simp only [Set.mem_setOf_eq]
  rw [hlam_a, hlam_b, hc]
  constructor
  · intro h
    linear_combination lam * h
  · intro h
    have hfac : lam * (a₁ * q.1 + b₁ * q.2) = lam * c₁ := by linear_combination h
    exact mul_left_cancel₀ hlam_ne hfac

/-- Two distinct affine lines meet in at most one point. -/
lemma encard_inter_le_one_of_lines {ℓ₁ ℓ₂ : Set (ℝ × ℝ)}
    (h₁ : IsAffineLine ℓ₁) (h₂ : IsAffineLine ℓ₂) (hne : ℓ₁ ≠ ℓ₂) :
    (ℓ₁ ∩ ℓ₂).Subsingleton := by
  obtain ⟨a₁, b₁, c₁, hℓ₁, rfl⟩ := h₁
  obtain ⟨a₂, b₂, c₂, hℓ₂, rfl⟩ := h₂
  intro p hp q hq
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hp hq
  obtain ⟨hp₁, hp₂⟩ := hp
  obtain ⟨hq₁, hq₂⟩ := hq
  by_contra hpq
  -- The difference vector `(u, v) = p - q` is nonzero and lies in both kernels.
  set u := p.1 - q.1 with hu
  set v := p.2 - q.2 with hv
  have huv : u ≠ 0 ∨ v ≠ 0 := by
    by_contra h
    push_neg at h
    apply hpq
    have h1 : p.1 = q.1 := by simpa [hu, sub_eq_zero] using h.1
    have h2 : p.2 = q.2 := by simpa [hv, sub_eq_zero] using h.2
    exact Prod.ext h1 h2
  have hk1 : a₁ * u + b₁ * v = 0 := by simp only [hu, hv]; nlinarith [hp₁, hq₁]
  have hk2 : a₂ * u + b₂ * v = 0 := by simp only [hu, hv]; nlinarith [hp₂, hq₂]
  -- `D·u = 0` and `D·v = 0`, with `(u,v) ≠ 0`, force the determinant `D` to vanish.
  have hdet : a₁ * b₂ = a₂ * b₁ := by
    rcases huv with hu0 | hv0
    · have hDu : (a₁ * b₂ - a₂ * b₁) * u = 0 := by linear_combination b₂ * hk1 - b₁ * hk2
      have : a₁ * b₂ - a₂ * b₁ = 0 := by
        rcases mul_eq_zero.mp hDu with h | h
        · exact h
        · exact absurd h hu0
      linarith [this]
    · have hDv : (a₁ * b₂ - a₂ * b₁) * v = 0 := by linear_combination a₁ * hk2 - a₂ * hk1
      have : a₁ * b₂ - a₂ * b₁ = 0 := by
        rcases mul_eq_zero.mp hDv with h | h
        · exact h
        · exact absurd h hv0
      linarith [this]
  -- Parallel + common point `p` ⟹ the lines coincide, contradicting `hne`.
  exact hne (affineLine_eq_of_parallel hℓ₁ hℓ₂ hdet hp₁ hp₂)

/-- Two distinct points lie on at most one affine line drawn from a given finite
family `L` of lines. -/
lemma lines_through_two_points_le_one {L : Finset (Set (ℝ × ℝ))}
    (hL : ∀ ℓ ∈ L, IsAffineLine ℓ) {p q : ℝ × ℝ} (hpq : p ≠ q) :
    (L.filter (fun ℓ => p ∈ ℓ ∧ q ∈ ℓ)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro ℓ₁ h₁ ℓ₂ h₂
  simp only [Finset.mem_filter] at h₁ h₂
  obtain ⟨hmem₁, hp₁, hq₁⟩ := h₁
  obtain ⟨hmem₂, hp₂, hq₂⟩ := h₂
  by_contra hℓne
  -- `p` and `q` both lie in `ℓ₁ ∩ ℓ₂`, a subsingleton, forcing `p = q`.
  have hsub := encard_inter_le_one_of_lines (hL ℓ₁ hmem₁) (hL ℓ₂ hmem₂) hℓne
  have : p = q := hsub ⟨hp₁, hp₂⟩ ⟨hq₁, hq₂⟩
  exact hpq this

/-- The crossing-lemma endgame, geometry-free. From the crossing lemma `hCL`
and the incidence bookkeeping of a drawn multigraph `G` (vertices = the `m`
points, `e := G.numEdges ≥ I - n`, multiplicity `≤ 1`, `crossings ≤ n²`),
derive the Szemerédi–Trotter incidence bound for `I` against `m` points and
`n` lines. Reused verbatim by Theorem 2.3 with `M ≥ 1`.

The constant `64` is pinned: in the high-edge regime the crossing lemma gives
`e³ ≤ 64·m²·n²`, so `e ≤ (64·m²·n²)^{1/3} = 4·m^{2/3}·n^{2/3}`, and `I ≤ e + n`
slots under `64·(m^{2/3}n^{2/3} + m + n)` with room to spare; in the low-edge
regime `I < 4m + n ≤ 64·(m + n)`. -/
lemma incidence_bound_of_crossingLemma
    (hCL : CrossingLemmaMultigraphStatement)
    (I m n : ℕ) (G : DrawnMultigraph)
    (hv : G.V.card = m)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (hwd : G.WellDrawn)
    (he : I ≤ G.numEdges + n)
    (hcr : G.crossings ≤ n ^ 2) :
    (I : ℝ) ≤
      64 * ((m : ℝ) ^ ((2 : ℝ) / 3) * (n : ℝ) ^ ((2 : ℝ) / 3) + m + n) := by
  -- Standing nonnegativity facts for the final arithmetic.
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hmr : (0 : ℝ) ≤ (m : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_nonneg hm0 _
  have hnr : (0 : ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_nonneg hn0 _
  have hprod : (0 : ℝ) ≤ (m : ℝ) ^ ((2 : ℝ) / 3) * (n : ℝ) ^ ((2 : ℝ) / 3) :=
    mul_nonneg hmr hnr
  by_cases hthr : 4 * 1 * G.V.card ≤ G.numEdges
  · -- High-edge regime: the crossing lemma applies.
    have hcl := hCL G 1 (by norm_num) hmult hwd hthr
    -- `e³ ≤ 64·m²·crossings ≤ 64·m²·n²`, in ℕ.
    have hcubeNat : G.numEdges ^ 3 ≤ 64 * m ^ 2 * n ^ 2 := by
      have h1 : G.numEdges ^ 3 ≤ 64 * 1 * m ^ 2 * G.crossings := by
        rw [hv] at hcl; exact hcl
      calc G.numEdges ^ 3 ≤ 64 * 1 * m ^ 2 * G.crossings := h1
        _ = 64 * m ^ 2 * G.crossings := by ring
        _ ≤ 64 * m ^ 2 * n ^ 2 := by
            exact Nat.mul_le_mul_left _ hcr
    -- Cast to ℝ.
    have hcubeR : (G.numEdges : ℝ) ^ 3 ≤ 64 * (m : ℝ) ^ 2 * (n : ℝ) ^ 2 := by
      have := (Nat.cast_le (α := ℝ)).mpr hcubeNat
      push_cast at this
      linarith [this]
    -- Identify the cube-root bound `B := 4·m^{2/3}·n^{2/3}` via `B³ = 64·m²·n²`.
    set B : ℝ := 4 * (m : ℝ) ^ ((2 : ℝ) / 3) * (n : ℝ) ^ ((2 : ℝ) / 3) with hB
    have hBnonneg : (0 : ℝ) ≤ B := by
      rw [hB]; positivity
    have hBcube : B ^ 3 = 64 * (m : ℝ) ^ 2 * (n : ℝ) ^ 2 := by
      have e1 : ((m : ℝ) ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) = (m : ℝ) ^ (2 : ℕ) := by
        rw [← Real.rpow_natCast ((m : ℝ) ^ ((2 : ℝ) / 3)) 3, ← Real.rpow_mul hm0]
        norm_num
      have e2 : ((n : ℝ) ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) = (n : ℝ) ^ (2 : ℕ) := by
        rw [← Real.rpow_natCast ((n : ℝ) ^ ((2 : ℝ) / 3)) 3, ← Real.rpow_mul hn0]
        norm_num
      rw [hB]
      calc (4 * (m : ℝ) ^ ((2 : ℝ) / 3) * (n : ℝ) ^ ((2 : ℝ) / 3)) ^ 3
          = 4 ^ (3 : ℕ) * ((m : ℝ) ^ ((2 : ℝ) / 3)) ^ (3 : ℕ)
              * ((n : ℝ) ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) := by ring
        _ = 64 * (m : ℝ) ^ 2 * (n : ℝ) ^ 2 := by rw [e1, e2]; norm_num
    -- Take cube roots: `e ≤ B`.
    have hcubeB : (G.numEdges : ℝ) ^ 3 ≤ B ^ 3 := by rw [hBcube]; exact hcubeR
    have heB : (G.numEdges : ℝ) ≤ B :=
      le_of_pow_le_pow_left₀ (by norm_num) hBnonneg hcubeB
    -- Assemble: `I ≤ e + n ≤ B + n ≤ 64·(m^{2/3}n^{2/3} + m + n)`.
    have heI : (I : ℝ) ≤ (G.numEdges : ℝ) + n := by
      have := (Nat.cast_le (α := ℝ)).mpr he
      push_cast at this
      linarith [this]
    rw [hB] at heB
    nlinarith [heI, heB, hprod, hmr, hnr, hm0, hn0]
  · -- Low-edge regime: `e < 4m`, so `I < 4m + n ≤ 64·(m + n)`.
    push_neg at hthr
    rw [hv] at hthr
    -- `hthr : G.numEdges < 4 * 1 * m`, hence `I ≤ 4·m + n - 1 < 4·m + n`.
    have heINat : I ≤ 4 * m + n := by omega
    have heIR : (I : ℝ) ≤ 4 * (m : ℝ) + (n : ℝ) := by
      have := (Nat.cast_le (α := ℝ)).mpr heINat
      push_cast at this
      linarith [this]
    nlinarith [heIR, hprod, hmr, hnr, hm0, hn0]

/-! ## Phase 2 — Geometric realization (points + lines ⟹ `DrawnMultigraph`)

Turn `(P : Finset (ℝ×ℝ))` and `(L : Finset (Set (ℝ×ℝ)))` into a plane-drawn
multigraph of straight segments so the five hypotheses of
`incidence_bound_of_crossingLemma` hold.

### Task 4 — Order the incident points on a single line and build its edge list
-/

/-- The projection of a point onto the direction vector `(-b, a)` of the line
`{p | a·p.1 + b·p.2 = c}`. This is a strictly monotone affine coordinate along
the line, so it gives a total order on the incident points. -/
noncomputable def lineKeyCoeff (a b : ℝ) (p : ℝ × ℝ) : ℝ := -b * p.1 + a * p.2

/-- The sort key for points on a line `ℓ`. When `ℓ` is an affine line it uses the
chosen coefficients `(a, b)` of `ℓ`'s defining equation (direction projection);
on non-lines it is the constant `0` (never used on the proof path). -/
noncomputable def lineKey (ℓ : Set (ℝ × ℝ)) (p : ℝ × ℝ) : ℝ := by
  classical
  exact if h : IsAffineLine ℓ then lineKeyCoeff h.choose h.choose_spec.choose p else 0

/-- Key injectivity from explicit coefficients: two points of the line
`{a·x + b·y = c}` with equal direction-projection keys coincide. The `2×2`
system `a·Δ = 0`, `-b·Δ' + a·Δ'' = 0` has determinant `a² + b² ≠ 0`. -/
lemma key_inj_coeff (a b c : ℝ) (hab : (a, b) ≠ (0, 0)) (p p' : ℝ × ℝ)
    (hp : a * p.1 + b * p.2 = c) (hp' : a * p'.1 + b * p'.2 = c)
    (hk : lineKeyCoeff a b p = lineKeyCoeff a b p') : p = p' := by
  unfold lineKeyCoeff at hk
  have hsq : a ^ 2 + b ^ 2 ≠ 0 := by
    intro h
    have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
    exact hab (Prod.ext ha hb)
  have e1 : a * (p.1 - p'.1) + b * (p.2 - p'.2) = 0 := by linear_combination hp - hp'
  have e2 : -b * (p.1 - p'.1) + a * (p.2 - p'.2) = 0 := by linear_combination hk
  have hx : (a ^ 2 + b ^ 2) * (p.1 - p'.1) = 0 := by linear_combination a * e1 - b * e2
  have hy : (a ^ 2 + b ^ 2) * (p.2 - p'.2) = 0 := by linear_combination b * e1 + a * e2
  have hx0 : p.1 - p'.1 = 0 := (mul_eq_zero.mp hx).resolve_left hsq
  have hy0 : p.2 - p'.2 = 0 := (mul_eq_zero.mp hy).resolve_left hsq
  exact Prod.ext (by linarith) (by linarith)

/-- **The key is injective on the line.** Distinct points of an affine line get
distinct direction-projection keys, so the per-line sort is strict. -/
lemma lineKey_injOn {ℓ : Set (ℝ × ℝ)} (h : IsAffineLine ℓ) :
    Set.InjOn (lineKey ℓ) ℓ := by
  intro p hp q hq hkey
  set a := h.choose with ha
  set b := h.choose_spec.choose with hb
  set c := h.choose_spec.choose_spec.choose with hc
  obtain ⟨hab, hℓeq⟩ := h.choose_spec.choose_spec.choose_spec
  rw [hℓeq, Set.mem_setOf_eq] at hp hq
  have hk : lineKeyCoeff a b p = lineKeyCoeff a b q := by
    rw [lineKey, dif_pos h, lineKey, dif_pos h] at hkey; exact hkey
  exact key_inj_coeff a b c hab p q hp hq hk

/-- The points of `P` incident to a line `ℓ`, sorted along `ℓ` by the
direction-projection key `lineKey`. Returned as a `List` so consecutive pairs are
well-defined; the underlying multiset is `P.filter (· ∈ ℓ)`. -/
noncomputable def pointsOnLine (P : Finset (ℝ × ℝ)) (ℓ : Set (ℝ × ℝ)) : List (ℝ × ℝ) :=
  (P.filter (fun p => p ∈ ℓ)).toList.mergeSort (fun p q => decide (lineKey ℓ p ≤ lineKey ℓ q))

/-- `pointsOnLine` is a permutation of the incident-point list `(P.filter (· ∈ ℓ)).toList`. -/
lemma pointsOnLine_perm (P : Finset (ℝ × ℝ)) (ℓ : Set (ℝ × ℝ)) :
    (pointsOnLine P ℓ).Perm (P.filter (fun p => p ∈ ℓ)).toList :=
  List.mergeSort_perm _ _

/-- Membership in `pointsOnLine` ⇔ membership in `P` and in `ℓ`. -/
lemma mem_pointsOnLine {P : Finset (ℝ × ℝ)} {ℓ : Set (ℝ × ℝ)} {p : ℝ × ℝ} :
    p ∈ pointsOnLine P ℓ ↔ p ∈ P ∧ p ∈ ℓ := by
  rw [(pointsOnLine_perm P ℓ).mem_iff, Finset.mem_toList, Finset.mem_filter]

/-- `pointsOnLine` has no repeated points (it is a sort of a `Finset`'s element list). -/
lemma pointsOnLine_nodup (P : Finset (ℝ × ℝ)) (ℓ : Set (ℝ × ℝ)) :
    (pointsOnLine P ℓ).Nodup := by
  rw [(pointsOnLine_perm P ℓ).nodup_iff]; exact Finset.nodup_toList _

/-- `|pointsOnLine P ℓ| = |{p ∈ P : p ∈ ℓ}|`: the sorted list keeps every incident
point exactly once. -/
lemma length_pointsOnLine (P : Finset (ℝ × ℝ)) (ℓ : Set (ℝ × ℝ)) :
    (pointsOnLine P ℓ).length = (P.filter (fun p => p ∈ ℓ)).card := by
  rw [(pointsOnLine_perm P ℓ).length_eq, Finset.length_toList]

/-- Consecutive (point, point) pairs along `ℓ`: `k` incident points give `k - 1`
segment edges. -/
noncomputable def edgesOnLine (P : Finset (ℝ × ℝ)) (ℓ : Set (ℝ × ℝ)) :
    List ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (pointsOnLine P ℓ).zip (pointsOnLine P ℓ).tail

/-- **Consecutive points are distinct.** Each edge of `edgesOnLine` joins two
different points, because `pointsOnLine` is `Nodup`: adjacent entries sit at the
consecutive indices `k, k+1`, which are distinct by nodup. -/
lemma edgesOnLine_distinct (P : Finset (ℝ × ℝ)) (ℓ : Set (ℝ × ℝ)) :
    ∀ e ∈ edgesOnLine P ℓ, e.1 ≠ e.2 := by
  intro e he
  obtain ⟨x, y⟩ := e
  have hnd := pointsOnLine_nodup P ℓ
  set l := pointsOnLine P ℓ with hl
  change (x, y) ∈ l.zip l.tail at he
  rw [List.mem_iff_getElem] at he
  obtain ⟨k, hk, hget⟩ := he
  rw [List.length_zip] at hk
  have hkl : k < l.length := lt_of_lt_of_le hk (min_le_left _ _)
  have hktail : k < l.tail.length := lt_of_lt_of_le hk (min_le_right _ _)
  rw [List.length_tail] at hktail
  have hk1 : k + 1 < l.length := by omega
  rw [List.getElem_zip, Prod.mk.injEq] at hget
  obtain ⟨hx, hy⟩ := hget
  have htaileq : l.tail[k] = l[k + 1] := by rw [List.getElem_tail]
  rw [htaileq] at hy
  intro hcontra
  rw [← hx, ← hy] at hcontra
  have := (hnd.getElem_inj_iff (i := k) (hi := hkl) (j := k + 1) (hj := hk1)).mp hcontra
  omega

/-- Both endpoints of every edge of `edgesOnLine P ℓ` lie in `P` (and on `ℓ`). -/
lemma edgesOnLine_mem (P : Finset (ℝ × ℝ)) (ℓ : Set (ℝ × ℝ)) :
    ∀ e ∈ edgesOnLine P ℓ, (e.1 ∈ P ∧ e.1 ∈ ℓ) ∧ (e.2 ∈ P ∧ e.2 ∈ ℓ) := by
  intro e he
  obtain ⟨x, y⟩ := e
  set l := pointsOnLine P ℓ with hl
  change (x, y) ∈ l.zip l.tail at he
  have hx : x ∈ l := List.of_mem_zip he |>.1
  have hy : y ∈ l := by
    have := List.of_mem_zip he |>.2
    exact List.mem_of_mem_tail this
  exact ⟨mem_pointsOnLine.mp hx, mem_pointsOnLine.mp hy⟩

/-- **Edge-count identity.** A line with `k` incident points contributes `k - 1`
segment edges (and none when `k = 0`). -/
lemma length_edgesOnLine (P : Finset (ℝ × ℝ)) (ℓ : Set (ℝ × ℝ)) :
    (edgesOnLine P ℓ).length + 1 = (pointsOnLine P ℓ).length
      ∨ edgesOnLine P ℓ = [] := by
  unfold edgesOnLine
  rcases Nat.eq_zero_or_pos (pointsOnLine P ℓ).length with h | h
  · right
    rw [List.length_eq_zero_iff] at h
    rw [h]; rfl
  · left
    rw [List.length_zip, List.length_tail]
    omega

/-! ### Task 5 — Assemble the global `DrawnMultigraph` of straight segments -/

/-- The straight segment from `p` to `q` as a `SimpleCurveArc`. The parameter
`h : p ≠ q` is required for the injectivity field (`SimpleCurveArc.inj` is *global*
injectivity of `param`, which fails for a degenerate segment); in `stMultigraph`
every edge joins two *distinct* consecutive points of `pointsOnLine`
(`edgesOnLine_distinct`), so the hypothesis is always available. -/
noncomputable def segmentArc (p q : ℝ × ℝ) (h : p ≠ q) : SimpleCurveArc where
  param := fun t => ((1 - (t : ℝ)) • p.1 + (t : ℝ) • q.1,
                     (1 - (t : ℝ)) • p.2 + (t : ℝ) • q.2)
  cont := by fun_prop
  inj := by
    intro s t hst
    simp only [Prod.mk.injEq, smul_eq_mul] at hst
    obtain ⟨h1, h2⟩ := hst
    apply Subtype.ext
    by_contra hne
    have hq1 : q.1 ≠ p.1 ∨ q.2 ≠ p.2 := by
      by_contra hh; push_neg at hh; exact h (Prod.ext hh.1.symm hh.2.symm)
    rcases hq1 with hq | hq
    · have hz : ((s : ℝ) - t) * (q.1 - p.1) = 0 := by nlinarith [h1]
      rcases mul_eq_zero.mp hz with hh | hh
      · exact hne (by linarith)
      · exact hq (by linarith)
    · have hz : ((s : ℝ) - t) * (q.2 - p.2) = 0 := by nlinarith [h2]
      rcases mul_eq_zero.mp hz with hh | hh
      · exact hne (by linarith)
      · exact hq (by linarith)

/-- The consecutive-segment edges of a single line, each bundled with a proof that
its two endpoints are distinct (so it can become a non-degenerate `segmentArc`). -/
noncomputable def edgesOnLineWithProof (P : Finset (ℝ × ℝ)) (ℓ : Set (ℝ × ℝ)) :
    List (Σ' e : (ℝ × ℝ) × (ℝ × ℝ), e.1 ≠ e.2) :=
  (edgesOnLine P ℓ).pmap (fun e he => ⟨e, he⟩) (edgesOnLine_distinct P ℓ)

/-- A bundled edge's underlying pair is a genuine edge of its line. -/
lemma mem_edgesOnLineWithProof {P : Finset (ℝ × ℝ)} {ℓ : Set (ℝ × ℝ)}
    {s : Σ' e : (ℝ × ℝ) × (ℝ × ℝ), e.1 ≠ e.2} (hs : s ∈ edgesOnLineWithProof P ℓ) :
    s.1 ∈ edgesOnLine P ℓ := by
  unfold edgesOnLineWithProof at hs
  rw [List.mem_pmap] at hs
  obtain ⟨e, he, heq⟩ := hs
  rw [← heq]; exact he

/-- `|edgesOnLineWithProof P ℓ| = |edgesOnLine P ℓ|` (the `pmap` only attaches
distinctness proofs, it does not drop or duplicate edges). -/
lemma length_edgesOnLineWithProof (P : Finset (ℝ × ℝ)) (ℓ : Set (ℝ × ℝ)) :
    (edgesOnLineWithProof P ℓ).length = (edgesOnLine P ℓ).length := by
  unfold edgesOnLineWithProof; rw [List.length_pmap]

/-- All consecutive-segment edges over every line of `L`, bundled with
distinctness proofs and concatenated. This is the edge list of `stMultigraph`. -/
noncomputable def allEdges (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ))) :
    List (Σ' e : (ℝ × ℝ) × (ℝ × ℝ), e.1 ≠ e.2) :=
  L.toList.flatMap (fun ℓ => edgesOnLineWithProof P ℓ)

/-- Both endpoints of every edge in `allEdges` lie in `P`. -/
lemma allEdges_mem (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ))) :
    ∀ s ∈ allEdges P L, s.1.1 ∈ P ∧ s.1.2 ∈ P := by
  intro s hs
  unfold allEdges at hs
  rw [List.mem_flatMap] at hs
  obtain ⟨ℓ, hℓ, hsℓ⟩ := hs
  have he := mem_edgesOnLineWithProof hsℓ
  have := edgesOnLine_mem P ℓ s.1 he
  exact ⟨this.1.1, this.2.1⟩

/-- **The drawn multigraph of straight segments.** Vertices `P`; one edge per
consecutive-segment over all lines of `L` (`allEdges`); each edge drawn as the
straight `segmentArc` between its distinct endpoints; `crossings` set to the
clean upper bound `L.card²`.

The crossing-bound encoding: `crossings := L.card ^ 2` rather than the structure's
`crossingCount`. This avoids the `crossingCount` self-reference entirely (it reads
`numEdges`/`arc`, which are the very fields being defined) and makes
`stMultigraph_crossings_le` trivial (`le_refl`); the genuine geometric bound
`crossingCount ≤ L.card²` is then carried by `stMultigraph_wellDrawn`. -/
noncomputable def stMultigraph
    (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ))) : DrawnMultigraph where
  V := P
  numEdges := (allEdges P L).length
  endpoints := fun i => (allEdges P L)[i].1
  endpoints_mem := fun i => allEdges_mem P L ((allEdges P L)[i]) (List.getElem_mem _)
  arc := fun i => segmentArc ((allEdges P L)[i].1).1 ((allEdges P L)[i].1).2 (allEdges P L)[i].2
  crossings := L.card ^ 2

/-! ### Task 6 — Discharge the five Phase-1 hypotheses for `stMultigraph` -/

/-- **Hypothesis `hv`.** Vertices are `P`, so `|V| = |P|` by definition. -/
@[simp] lemma stMultigraph_card_V (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ))) :
    (stMultigraph P L).V.card = P.card := rfl

/-- `numEdges` of `stMultigraph` is the length of the global edge list. -/
lemma stMultigraph_numEdges (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ))) :
    (stMultigraph P L).numEdges = (allEdges P L).length := rfl

/-- **Edge-count identity.** `numEdges = Σ_{ℓ∈L} |edgesOnLine P ℓ|`: the global edge
list is the concatenation of the per-line edge lists. -/
lemma numEdges_eq_sum (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ))) :
    (stMultigraph P L).numEdges = ∑ ℓ ∈ L, (edgesOnLine P ℓ).length := by
  rw [stMultigraph_numEdges, allEdges, List.length_flatMap,
    List.map_congr_left (g := fun ℓ => (edgesOnLine P ℓ).length)
      (fun ℓ _ => length_edgesOnLineWithProof P ℓ),
    Finset.sum_map_toList]

/-- **Incidence double-counting.** `incidences P L = Σ_{ℓ∈L} |{p ∈ P : p ∈ ℓ}|`. -/
lemma incidences_eq_sum (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ))) :
    incidences P L = ∑ ℓ ∈ L, (P.filter (fun p => p ∈ ℓ)).card := by
  rw [incidences, Finset.card_filter, Finset.sum_product_right]
  exact Finset.sum_congr rfl (fun ℓ _ => (Finset.card_filter _ _).symm)

/-- Per-line: a line with `k` incident points has `(P.filter (· ∈ ℓ)).card = k`
incident points and `≥ k - 1` edges, so `incident-count ≤ edge-count + 1`. -/
lemma filter_card_le_edges (P : Finset (ℝ × ℝ)) (ℓ : Set (ℝ × ℝ)) :
    (P.filter (fun p => p ∈ ℓ)).card ≤ (edgesOnLine P ℓ).length + 1 := by
  rw [← length_pointsOnLine]
  rcases length_edgesOnLine P ℓ with h | h
  · omega
  · rw [h, List.length_nil, Nat.zero_add]
    have hle : (pointsOnLine P ℓ).length ≤ 1 := by
      by_contra hc
      push_neg at hc
      unfold edgesOnLine at h
      rw [List.eq_nil_iff_length_eq_zero, List.length_zip, List.length_tail] at h
      omega
    omega

/-- **Hypothesis `he`.** `I ≤ e + n`: summing the per-line bound, a line with `k`
incident points contributes `k - 1` edges, and there are `≤ |L|` lines, so the
`-1` slack costs at most `|L|`. -/
lemma incidences_le_numEdges_add (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    (_hL : ∀ ℓ ∈ L, IsAffineLine ℓ) :
    incidences P L ≤ (stMultigraph P L).numEdges + L.card := by
  rw [numEdges_eq_sum, incidences_eq_sum]
  calc ∑ ℓ ∈ L, (P.filter (fun p => p ∈ ℓ)).card
      ≤ ∑ ℓ ∈ L, ((edgesOnLine P ℓ).length + 1) :=
        Finset.sum_le_sum (fun ℓ _ => filter_card_le_edges P ℓ)
    _ = (∑ ℓ ∈ L, (edgesOnLine P ℓ).length) + L.card := by
        rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]

/-- **Hypothesis `hcr`.** `crossings ≤ n²` holds by definition: the `crossings`
field is set to `L.card ^ 2` (encoding B). The genuine geometric content
(`crossingCount ≤ L.card²`) lives in `stMultigraph_wellDrawn`. -/
@[simp] lemma stMultigraph_crossings_le (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ))) :
    (stMultigraph P L).crossings ≤ L.card ^ 2 := le_refl _

/-! #### Multiplicity bookkeeping (geometry-free combinatorics)

The reduction of `multiplicity` to a sum of per-line `List.countP`s, and the two
facts (M1: only the unique line through `p ≠ q` contributes; M2: a fixed unordered
pair is adjacent at most once in a sorted `Nodup` list) that bound the sum by `1`. -/

/-- The Boolean match predicate for the unordered pair `{p, q}` on an edge. -/
noncomputable def matchPair (p q : ℝ × ℝ) (e : (ℝ × ℝ) × (ℝ × ℝ)) : Bool :=
  decide (e = (p, q) ∨ e = (q, p))

/-- **Generic bridge.** The number of indices `i : Fin l.length` whose entry `l[i]`
satisfies `P` equals `l.countP P`. Lets us reduce a `Finset.card` over edge indices
(as in `DrawnMultigraph.multiplicity`) to a `List.countP`, which composes with
`List.countP_flatMap` over the per-line edge lists. -/
theorem finFilterCard_eq_countP {α : Type*} (P : α → Bool) (l : List α) :
    (Finset.univ.filter (fun i : Fin l.length => P (l[i]) = true)).card = l.countP P := by
  have hstep1 : (Finset.univ.filter (fun i : Fin l.length => P (l[i]) = true)).card
      = ((List.finRange l.length).filter (fun i => P (l[i]))).toFinset.card := by
    rw [List.toFinset_filter, List.toFinset_finRange]
  have hstep2 : ((List.finRange l.length).filter (fun i => P (l[i]))).toFinset.card
      = ((List.finRange l.length).filter (fun i => P (l[i]))).length :=
    List.toFinset_card_of_nodup ((List.nodup_finRange l.length).filter _)
  have hstep3 : ((List.finRange l.length).filter (fun i => P (l[i]))).length
      = (List.finRange l.length).countP (fun i => P (l[i])) :=
    (List.countP_eq_length_filter ..).symm
  have hstep4 : (List.finRange l.length).countP (fun i => P (l[i])) = l.countP P := by
    conv_rhs => rw [← List.map_getElem_finRange l, List.countP_map]
    rfl
  rw [hstep1, hstep2, hstep3, hstep4]

/-- **Index-injectivity ⟹ `countP ≤ 1`.** If no two distinct indices of `l` both
satisfy `P`, then `P` is satisfied at most once. (Proved by the generic bridge plus
`Finset.card_le_one`.) -/
theorem countP_le_one_of_index_inj {α : Type*} (P : α → Bool) (l : List α)
    (h : ∀ i j (hi : i < l.length) (hj : j < l.length), P l[i] → P l[j] → i = j) :
    l.countP P ≤ 1 := by
  rw [← finFilterCard_eq_countP, Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  exact Fin.ext (h a.1 b.1 a.2 b.2 ha hb)

/-- **Multiplicity as a `countP`.** `multiplicity (stMultigraph P L) p q` counts the
edge indices whose endpoint-pair is `(p,q)` or `(q,p)`; this is the `countP` of
`matchPair p q` over the concatenated edge list `allEdges P L`. -/
theorem multiplicity_eq_countP (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ))) (p q : ℝ × ℝ) :
    (stMultigraph P L).multiplicity p q
      = (allEdges P L).countP (fun s => matchPair p q s.1) := by
  show (Finset.univ.filter (fun i : Fin (allEdges P L).length =>
        (allEdges P L)[i].1 = (p,q) ∨ (allEdges P L)[i].1 = (q,p))).card = _
  set l := allEdges P L with hl
  set Pr : (Σ' e : (ℝ × ℝ) × (ℝ × ℝ), e.1 ≠ e.2) → Bool := fun s => matchPair p q s.1 with hPr
  have hfilt : (Finset.univ.filter (fun i : Fin l.length =>
        (l[i].1 = (p,q) ∨ l[i].1 = (q,p)))).card
      = (Finset.univ.filter (fun i : Fin l.length => Pr (l[i]) = true)).card := by
    congr 1
    apply Finset.filter_congr
    intro i _
    rw [hPr]; unfold matchPair; rw [decide_eq_true_eq]
  rw [hfilt, finFilterCard_eq_countP]

/-- Projecting away the distinctness proofs recovers the bare edge list. -/
theorem map_fst_edgesOnLineWithProof (P : Finset (ℝ × ℝ)) (ℓ : Set (ℝ × ℝ)) :
    (edgesOnLineWithProof P ℓ).map (fun s => s.1) = edgesOnLine P ℓ := by
  unfold edgesOnLineWithProof; rw [List.map_pmap]; simp

/-- The per-line `countP` is unchanged by the distinctness-proof bundling. -/
theorem countP_edgesOnLineWithProof (P : Finset (ℝ × ℝ)) (ℓ : Set (ℝ × ℝ)) (p q : ℝ × ℝ) :
    (edgesOnLineWithProof P ℓ).countP (fun s => matchPair p q s.1)
      = (edgesOnLine P ℓ).countP (matchPair p q) := by
  rw [← map_fst_edgesOnLineWithProof P ℓ, List.countP_map]; rfl

/-- **`countP` over `allEdges` is a `Finset.sum` over lines.** `allEdges` is the
`flatMap` of the per-line edge lists, so by `List.countP_flatMap` the total count is
`Σ_{ℓ∈L} (edgesOnLine P ℓ).countP (matchPair p q)`. -/
theorem multiplicity_flatMap_sum (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ))) (p q : ℝ × ℝ) :
    (allEdges P L).countP (fun s => matchPair p q s.1)
      = ∑ ℓ ∈ L, (edgesOnLine P ℓ).countP (matchPair p q) := by
  unfold allEdges
  rw [List.countP_flatMap]
  simp only [Function.comp_def]
  rw [List.map_congr_left (g := fun ℓ => (edgesOnLine P ℓ).countP (matchPair p q))
      (fun ℓ _ => countP_edgesOnLineWithProof P ℓ p q),
    Finset.sum_map_toList]

/-- The `i`-th edge of `edgesOnLine P ℓ` joins the consecutive sorted points
`pointsOnLine[i]` and `pointsOnLine[i+1]` (with `i+1` in range). -/
theorem edgesOnLine_getElem (P : Finset (ℝ × ℝ)) (ℓ : Set (ℝ × ℝ)) (i : ℕ)
    (hi : i < (edgesOnLine P ℓ).length) :
    ∃ (_ : i < (pointsOnLine P ℓ).length) (_ : i + 1 < (pointsOnLine P ℓ).length),
      (edgesOnLine P ℓ)[i] = ((pointsOnLine P ℓ)[i], (pointsOnLine P ℓ)[i+1]) := by
  set l := pointsOnLine P ℓ with hl
  have hilen : i < (l.zip l.tail).length := hi
  rw [List.length_zip] at hilen
  have hkl : i < l.length := lt_of_lt_of_le hilen (min_le_left _ _)
  have hktail : i < l.tail.length := lt_of_lt_of_le hilen (min_le_right _ _)
  rw [List.length_tail] at hktail
  have hk1 : i + 1 < l.length := by omega
  refine ⟨hkl, hk1, ?_⟩
  have hget : (edgesOnLine P ℓ)[i] = (l.zip l.tail)[i]'(by rw [List.length_zip]; exact hilen) := rfl
  rw [hget, List.getElem_zip]
  congr 1
  rw [List.getElem_tail]

/-- **M2 (per-line).** A fixed unordered pair `{p, q}` is adjacent at most once in the
sorted incident-point list: `(edgesOnLine P ℓ).countP (matchPair p q) ≤ 1`. The
ordering is by `lineKey`, the list is `Nodup` (`pointsOnLine_nodup`), so each point
occurs at one position; the two orientations `(p,q)` and `(q,p)` cannot both occur
(they would force `i = j+1` and `i+1 = j`). -/
theorem edgesOnLine_countP_le_one (P : Finset (ℝ × ℝ)) (ℓ : Set (ℝ × ℝ)) (p q : ℝ × ℝ) :
    (edgesOnLine P ℓ).countP (matchPair p q) ≤ 1 := by
  apply countP_le_one_of_index_inj
  intro i j hi hj hPi hPj
  set l := pointsOnLine P ℓ with hl
  have hnd := pointsOnLine_nodup P ℓ
  obtain ⟨hii, hki, hei⟩ := edgesOnLine_getElem P ℓ i hi
  obtain ⟨hij, hkj, hej⟩ := edgesOnLine_getElem P ℓ j hj
  rw [hei] at hPi
  rw [hej] at hPj
  unfold matchPair at hPi hPj
  rw [decide_eq_true_eq] at hPi hPj
  simp only [Prod.mk.injEq] at hPi hPj
  rcases hPi with ⟨hip, hiq⟩ | ⟨hiq, hip⟩ <;>
    rcases hPj with ⟨hjp, hjq⟩ | ⟨hjq, hjp⟩
  · have e : l[i] = l[j] := by rw [hip, hjp]
    exact (hnd.getElem_inj_iff (hi := hii) (hj := hij)).mp e
  · have e1 : l[i] = l[j+1] := by rw [hip, hjp]
    have e2 : l[i+1] = l[j] := by rw [hiq, hjq]
    have hi1 : i = j + 1 := (hnd.getElem_inj_iff (hi := hii) (hj := hkj)).mp e1
    have hj1 : i + 1 = j := (hnd.getElem_inj_iff (hi := hki) (hj := hij)).mp e2
    omega
  · have e1 : l[i+1] = l[j] := by rw [hip, hjp]
    have e2 : l[i] = l[j+1] := by rw [hiq, hjq]
    have hi1 : i + 1 = j := (hnd.getElem_inj_iff (hi := hki) (hj := hij)).mp e1
    have hj1 : i = j + 1 := (hnd.getElem_inj_iff (hi := hii) (hj := hkj)).mp e2
    omega
  · have e : l[i] = l[j] := by rw [hiq, hjq]
    exact (hnd.getElem_inj_iff (hi := hii) (hj := hij)).mp e

/-- **M1 support.** A line not containing both `p` and `q` contributes no matching
edge: every edge of `edgesOnLine P ℓ` has both endpoints on `ℓ`, so a match would
force `p, q ∈ ℓ`. -/
theorem countP_edgesOnLine_eq_zero_of_not_mem (P : Finset (ℝ × ℝ)) (ℓ : Set (ℝ × ℝ))
    {p q : ℝ × ℝ} (h : ¬ (p ∈ ℓ ∧ q ∈ ℓ)) :
    (edgesOnLine P ℓ).countP (matchPair p q) = 0 := by
  rw [List.countP_eq_zero]
  intro e he
  unfold matchPair
  simp only [decide_eq_true_eq]
  intro hcontra
  have hmem := edgesOnLine_mem P ℓ e he
  apply h
  rcases hcontra with heq | heq
  · rw [heq] at hmem; exact ⟨hmem.1.2, hmem.2.2⟩
  · rw [heq] at hmem; exact ⟨hmem.2.2, hmem.1.2⟩

/-- A degenerate pair `{p, p}` contributes no edge: edges join *distinct* points
(`edgesOnLine_distinct`), so no edge equals `(p, p)`. -/
theorem countP_edgesOnLine_eq_zero_of_eq (P : Finset (ℝ × ℝ)) (ℓ : Set (ℝ × ℝ)) (p : ℝ × ℝ) :
    (edgesOnLine P ℓ).countP (matchPair p p) = 0 := by
  rw [List.countP_eq_zero]
  intro e he
  unfold matchPair
  simp only [or_self, decide_eq_true_eq]
  intro hcontra
  have hdist := edgesOnLine_distinct P ℓ e he
  rw [hcontra] at hdist
  exact hdist rfl

/-- **Hypothesis `hmult` (PROVEN, sorry-free).** Multiplicity ≤ 1: at most one
segment joins a given unordered point pair `{p, q}`.

The multiplicity reduces (via `multiplicity_eq_countP` and `multiplicity_flatMap_sum`)
to `Σ_{ℓ∈L} (edgesOnLine P ℓ).countP (matchPair p q)`.

* If `p = q`: every edge has *distinct* endpoints (`edgesOnLine_distinct`), so the
  predicate `edge = (p,p)` is never satisfied; each term is `0`
  (`countP_edgesOnLine_eq_zero_of_eq`), sum `= 0 ≤ 1`.
* If `p ≠ q`: a line not containing both `p, q` contributes `0`
  (`countP_edgesOnLine_eq_zero_of_not_mem`); each remaining term is `≤ 1`
  (`edgesOnLine_countP_le_one`, the M2 fact); and `lines_through_two_points_le_one`
  bounds the number of lines through both by `1`. So the sum is `≤ 1`. -/
lemma stMultigraph_multiplicity_le_one (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    (hL : ∀ ℓ ∈ L, IsAffineLine ℓ) :
    ∀ p q, (stMultigraph P L).multiplicity p q ≤ 1 := by
  intro p q
  rw [multiplicity_eq_countP, multiplicity_flatMap_sum]
  by_cases hpq : p = q
  · subst hpq
    rw [Finset.sum_eq_zero (fun ℓ _ => countP_edgesOnLine_eq_zero_of_eq P ℓ p)]
    norm_num
  · have hterm : ∀ ℓ ∈ L, (edgesOnLine P ℓ).countP (matchPair p q)
        ≤ (if p ∈ ℓ ∧ q ∈ ℓ then 1 else 0) := by
      intro ℓ _
      by_cases hmem : p ∈ ℓ ∧ q ∈ ℓ
      · rw [if_pos hmem]; exact edgesOnLine_countP_le_one P ℓ p q
      · rw [if_neg hmem, countP_edgesOnLine_eq_zero_of_not_mem P ℓ hmem]
    calc ∑ ℓ ∈ L, (edgesOnLine P ℓ).countP (matchPair p q)
        ≤ ∑ ℓ ∈ L, (if p ∈ ℓ ∧ q ∈ ℓ then 1 else 0) := Finset.sum_le_sum hterm
      _ = (L.filter (fun ℓ => p ∈ ℓ ∧ q ∈ ℓ)).card := by
          rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]; simp
      _ ≤ 1 := lines_through_two_points_le_one hL hpq

/-! #### Geometric infrastructure for the crossing bound (W1–W3)

The pieces needed to show `crossingCount (stMultigraph P L) ≤ L.card²`. Three
geometric facts:

* **W1** — Edge → line map `lineForEdge`. Each edge of `allEdges P L` was inserted
  by the `flatMap` over `L.toList` from some `ℓ ∈ L`; we recover that `ℓ`
  (`Classical.choose` on the `mem_flatMap` witness), together with the *line
  membership* of the edge in `edgesOnLineWithProof P (lineForEdge i)`.
* **W2** — Affine combinations of two points of an affine line lie on the line:
  `interiorOfArc (segmentArc p q hpq) ⊆ ℓ` whenever `p, q ∈ ℓ` and `IsAffineLine ℓ`.
  This is a single `linear_combination` discharge of `IsAffineLine`'s linear-equation
  unfolding.
* **W3** — Interior-disjointness of distinct same-line edges. Two ingredients:
  (a) `pointsOnLine` is *strictly* sorted by `lineKey ℓ` (sortedness comes from
  `List.pairwise_mergeSort`; strictness from `lineKey_injOn` + `pointsOnLine_nodup`);
  (b) for an edge `(pts[k], pts[k+1])`, the interior of `segmentArc` has `lineKey`
  values in the open interval `(lineKey ℓ pts[k], lineKey ℓ pts[k+1])`; consecutive
  open intervals of a strict total order are disjoint. -/

/-- **W2.** The open segment between two points `p, q` of an affine line `ℓ` is
contained in `ℓ`: every interior point is `(1-t)•p + t•q` for `t ∈ (0,1)`, which
satisfies the same defining linear equation as `p` and `q`. -/
lemma interiorOfArc_segmentArc_subset_line {ℓ : Set (ℝ × ℝ)}
    (hℓ : IsAffineLine ℓ) {p q : ℝ × ℝ} (hp : p ∈ ℓ) (hq : q ∈ ℓ) (hpq : p ≠ q) :
    interiorOfArc (segmentArc p q hpq) ⊆ ℓ := by
  intro x hx
  unfold interiorOfArc at hx
  simp only [Set.mem_image, Set.mem_setOf_eq] at hx
  obtain ⟨t, _, rfl⟩ := hx
  obtain ⟨a, b, c, _, rfl⟩ := hℓ
  rw [Set.mem_setOf_eq] at hp hq ⊢
  change a * ((1 - (t : ℝ)) • p.1 + (t : ℝ) • q.1)
        + b * ((1 - (t : ℝ)) • p.2 + (t : ℝ) • q.2) = c
  simp only [smul_eq_mul]
  linear_combination (1 - (t : ℝ)) * hp + (t : ℝ) * hq

/-- **lineKey is affine** along an affine line: for any `t ∈ ℝ`,
`lineKey ℓ ((1-t)•p + t•q) = (1-t) * lineKey ℓ p + t * lineKey ℓ q`. Both branches
of `lineKey` are affine in the point coordinates, so this holds unconditionally
in `ℓ` (no `IsAffineLine ℓ` hypothesis required). -/
lemma lineKey_affine_combination (ℓ : Set (ℝ × ℝ)) (p q : ℝ × ℝ) (t : ℝ) :
    lineKey ℓ (((1 - t) • p.1 + t • q.1, (1 - t) • p.2 + t • q.2) : ℝ × ℝ)
    = (1 - t) * lineKey ℓ p + t * lineKey ℓ q := by
  by_cases h : IsAffineLine ℓ
  · unfold lineKey
    rw [dif_pos h, dif_pos h, dif_pos h]
    unfold lineKeyCoeff
    simp only [smul_eq_mul]
    ring
  · unfold lineKey
    rw [dif_neg h, dif_neg h, dif_neg h]
    ring

/-- **lineKey value on an interior arc point** is a *strict* convex combination of
the endpoint keys: there is some `t ∈ (0,1)` with `lineKey ℓ x = (1-t) * key p
+ t * key q`. -/
lemma lineKey_of_mem_interior {ℓ : Set (ℝ × ℝ)}
    {p q : ℝ × ℝ} (hpq : p ≠ q) {x : ℝ × ℝ} (hx : x ∈ interiorOfArc (segmentArc p q hpq)) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ lineKey ℓ x = (1 - t) * lineKey ℓ p + t * lineKey ℓ q := by
  unfold interiorOfArc at hx
  simp only [Set.mem_image, Set.mem_setOf_eq] at hx
  obtain ⟨t, ⟨h0, h1⟩, rfl⟩ := hx
  refine ⟨t.val, h0, h1, ?_⟩
  have heq : (segmentArc p q hpq).param t =
      (((1 - (t : ℝ)) • p.1 + (t : ℝ) • q.1, (1 - (t : ℝ)) • p.2 + (t : ℝ) • q.2)
        : ℝ × ℝ) := rfl
  rw [heq, lineKey_affine_combination]

/-- **W3, sortedness step.** `pointsOnLine P ℓ` is sorted by `lineKey ℓ` (non-strict).
Direct from `List.pairwise_mergeSort` for the transitive total preorder
`decide (lineKey ℓ p ≤ lineKey ℓ q)`. -/
lemma pointsOnLine_pairwise_le (P : Finset (ℝ × ℝ)) (ℓ : Set (ℝ × ℝ)) :
    (pointsOnLine P ℓ).Pairwise (fun p q => lineKey ℓ p ≤ lineKey ℓ q) := by
  unfold pointsOnLine
  have hs := List.pairwise_mergeSort (l := (P.filter (fun p => p ∈ ℓ)).toList)
      (le := fun p q => decide (lineKey ℓ p ≤ lineKey ℓ q))
      (trans := by intro a b c h1 h2; simp at h1 h2 ⊢; linarith)
      (total := by intro a b; simp; by_cases h : lineKey ℓ a ≤ lineKey ℓ b
                   · left; exact h
                   · right; linarith)
  exact hs.imp (fun {a b} hab => by simpa using hab)

/-- **W3, strict sortedness.** When `ℓ` is an affine line, `pointsOnLine P ℓ` is
*strictly* sorted by `lineKey ℓ`: distinct points of an affine line have distinct
keys (`lineKey_injOn`), and the list is `Nodup`. -/
lemma pointsOnLine_pairwise_lt {P : Finset (ℝ × ℝ)} {ℓ : Set (ℝ × ℝ)}
    (h : IsAffineLine ℓ) :
    (pointsOnLine P ℓ).Pairwise (fun p q => lineKey ℓ p < lineKey ℓ q) := by
  have hLE := pointsOnLine_pairwise_le P ℓ
  have hND : (pointsOnLine P ℓ).Pairwise (fun a b => a ≠ b) := pointsOnLine_nodup P ℓ
  have hBoth := hLE.and hND
  apply hBoth.imp_of_mem
  intro a b ha hb ⟨hle, hne⟩
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exfalso; apply hne
    rw [mem_pointsOnLine] at ha hb
    exact lineKey_injOn h ha.2 hb.2 heq

/-- **Strict sortedness, indexed form.** For `i < j` indices into `pointsOnLine`,
the keys are strictly ordered. -/
lemma pointsOnLine_getElem_lt {P : Finset (ℝ × ℝ)} {ℓ : Set (ℝ × ℝ)}
    (h : IsAffineLine ℓ) {i j : ℕ}
    (hi : i < (pointsOnLine P ℓ).length) (hj : j < (pointsOnLine P ℓ).length)
    (hij : i < j) :
    lineKey ℓ (pointsOnLine P ℓ)[i] < lineKey ℓ (pointsOnLine P ℓ)[j] :=
  (List.pairwise_iff_getElem.mp (pointsOnLine_pairwise_lt h)) i j hi hj hij

/-- **W3, key inequality on edges.** Each edge `i` of `edgesOnLine P ℓ` has
*strictly* increasing keys: `lineKey ℓ (edge.1) < lineKey ℓ (edge.2)`. -/
lemma edgesOnLine_lineKey_lt {P : Finset (ℝ × ℝ)} {ℓ : Set (ℝ × ℝ)}
    (h : IsAffineLine ℓ) {i : ℕ} (hi : i < (edgesOnLine P ℓ).length) :
    lineKey ℓ ((edgesOnLine P ℓ)[i]).1 < lineKey ℓ ((edgesOnLine P ℓ)[i]).2 := by
  obtain ⟨hi₁, hi₂, hget⟩ := edgesOnLine_getElem P ℓ i hi
  rw [hget]
  exact pointsOnLine_getElem_lt h hi₁ hi₂ (Nat.lt_succ_self i)

/-- **W3, separation between distinct same-line edges.** For two distinct edges
`i ≠ j` of `edgesOnLine P ℓ` (with `ℓ` an affine line), the closed `lineKey`
intervals `[edge.1, edge.2]` of the two edges only meet at endpoints: w.l.o.g.
`i < j`, then `lineKey ℓ (edges[i]).2 ≤ lineKey ℓ (edges[j]).1`. -/
lemma edgesOnLine_lineKey_separated {P : Finset (ℝ × ℝ)} {ℓ : Set (ℝ × ℝ)}
    (h : IsAffineLine ℓ) {i j : ℕ}
    (hi : i < (edgesOnLine P ℓ).length) (hj : j < (edgesOnLine P ℓ).length)
    (hij : i < j) :
    lineKey ℓ ((edgesOnLine P ℓ)[i]).2 ≤ lineKey ℓ ((edgesOnLine P ℓ)[j]).1 := by
  obtain ⟨hi₁, hi₂, hgeti⟩ := edgesOnLine_getElem P ℓ i hi
  obtain ⟨hj₁, _hj₂, hgetj⟩ := edgesOnLine_getElem P ℓ j hj
  rw [hgeti, hgetj]
  -- We need `lineKey ℓ pts[i+1] ≤ lineKey ℓ pts[j]`. By sortedness with
  -- `i + 1 ≤ j` this is strict if `i + 1 < j`, equality if `i + 1 = j`.
  rcases Nat.lt_or_eq_of_le (Nat.succ_le_of_lt hij) with hlt | heq
  · exact le_of_lt (pointsOnLine_getElem_lt h hi₂ hj₁ hlt)
  · -- `i + 1 = j` case: indices `pts[i+1]` and `pts[j]` are the same point.
    subst heq
    exact le_refl _

/-- **W3, interior disjointness within a single line.** Two distinct edges of
`edgesOnLine P ℓ` have disjoint open-interior arcs. (Crucial: the proof exits
through the `lineKey` intervals, which are *strictly* disjoint by sortedness.) -/
lemma edgesOnLine_interior_disjoint {P : Finset (ℝ × ℝ)} {ℓ : Set (ℝ × ℝ)}
    (hℓ : IsAffineLine ℓ) {i j : ℕ}
    (hi : i < (edgesOnLine P ℓ).length) (hj : j < (edgesOnLine P ℓ).length)
    (hij : i ≠ j)
    (hdi : ((edgesOnLine P ℓ)[i]).1 ≠ ((edgesOnLine P ℓ)[i]).2)
    (hdj : ((edgesOnLine P ℓ)[j]).1 ≠ ((edgesOnLine P ℓ)[j]).2) :
    Disjoint (interiorOfArc (segmentArc ((edgesOnLine P ℓ)[i]).1 ((edgesOnLine P ℓ)[i]).2 hdi))
             (interiorOfArc (segmentArc ((edgesOnLine P ℓ)[j]).1 ((edgesOnLine P ℓ)[j]).2 hdj)) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  rw [Set.eq_empty_iff_forall_notMem]
  intro x ⟨hxi, hxj⟩
  -- Symmetrize: w.l.o.g. `i < j`.
  wlog hij' : i < j with H
  · exact H hℓ hj hi hij.symm hdj hdi x hxj hxi
      (lt_of_le_of_ne (Nat.le_of_not_lt hij') (Ne.symm hij))
  -- Interior point ⟹ `lineKey ℓ x` lies in the open intervals of both edges.
  have hki₁ : lineKey ℓ ((edgesOnLine P ℓ)[i]).1 < lineKey ℓ ((edgesOnLine P ℓ)[i]).2 :=
    edgesOnLine_lineKey_lt hℓ hi
  have hkj₁ : lineKey ℓ ((edgesOnLine P ℓ)[j]).1 < lineKey ℓ ((edgesOnLine P ℓ)[j]).2 :=
    edgesOnLine_lineKey_lt hℓ hj
  -- Separation between intervals.
  have hsep : lineKey ℓ ((edgesOnLine P ℓ)[i]).2 ≤ lineKey ℓ ((edgesOnLine P ℓ)[j]).1 :=
    edgesOnLine_lineKey_separated hℓ hi hj hij'
  -- Convex-combination representation of `lineKey ℓ x` in each interval.
  obtain ⟨ti, hti0, hti1, hxi_key⟩ := lineKey_of_mem_interior (ℓ := ℓ) hdi hxi
  obtain ⟨tj, htj0, htj1, hxj_key⟩ := lineKey_of_mem_interior (ℓ := ℓ) hdj hxj
  -- `lineKey ℓ x` is strictly inside both intervals, contradicting the separation.
  have hxi_in_lo : lineKey ℓ ((edgesOnLine P ℓ)[i]).1 < lineKey ℓ x := by
    rw [hxi_key]; nlinarith
  have hxi_in_hi : lineKey ℓ x < lineKey ℓ ((edgesOnLine P ℓ)[i]).2 := by
    rw [hxi_key]; nlinarith
  have hxj_in_lo : lineKey ℓ ((edgesOnLine P ℓ)[j]).1 < lineKey ℓ x := by
    rw [hxj_key]; nlinarith
  linarith

/-- **W3, bare form.** Same-line interior disjointness phrased on bare edge
entries `e₁, e₂ ∈ edgesOnLine P ℓ` with `e₁ ≠ e₂`. Equivalent in content to
`edgesOnLine_interior_disjoint`, but conveniently shaped for the injection
argument that goes through `lineForEdge` and bare edge data. -/
lemma edgesOnLine_bare_disjoint {P : Finset (ℝ × ℝ)} {ℓ : Set (ℝ × ℝ)}
    (hℓ : IsAffineLine ℓ)
    {e₁ e₂ : (ℝ × ℝ) × (ℝ × ℝ)}
    (he₁ : e₁ ∈ edgesOnLine P ℓ) (he₂ : e₂ ∈ edgesOnLine P ℓ) (hne : e₁ ≠ e₂)
    (hd₁ : e₁.1 ≠ e₁.2) (hd₂ : e₂.1 ≠ e₂.2) :
    Disjoint (interiorOfArc (segmentArc e₁.1 e₁.2 hd₁))
             (interiorOfArc (segmentArc e₂.1 e₂.2 hd₂)) := by
  rw [List.mem_iff_getElem] at he₁ he₂
  obtain ⟨i, hi, hgi⟩ := he₁
  obtain ⟨j, hj, hgj⟩ := he₂
  have hij : i ≠ j := by
    intro h; subst h; rw [hgi] at hgj; exact hne hgj
  have hd₁' : ((edgesOnLine P ℓ)[i]).1 ≠ ((edgesOnLine P ℓ)[i]).2 := by
    rw [hgi]; exact hd₁
  have hd₂' : ((edgesOnLine P ℓ)[j]).1 ≠ ((edgesOnLine P ℓ)[j]).2 := by
    rw [hgj]; exact hd₂
  have hcore := edgesOnLine_interior_disjoint hℓ hi hj hij hd₁' hd₂'
  convert hcore using 4 <;> first | exact hgi.symm | exact hgj.symm

/-! #### Edge-list nodup for the injection step -/

/-- `edgesOnLine P ℓ` is `Nodup`: distinct `i, j` indices give distinct consecutive
pairs `(pts[i], pts[i+1])` (because `pointsOnLine_nodup` separates pts[i] alone). -/
lemma edgesOnLine_nodup (P : Finset (ℝ × ℝ)) (ℓ : Set (ℝ × ℝ)) :
    (edgesOnLine P ℓ).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
  intro i j hi hj hij
  obtain ⟨_, hk1i, hgeti⟩ := edgesOnLine_getElem P ℓ i hi
  obtain ⟨_, _, hgetj⟩ := edgesOnLine_getElem P ℓ j hj
  rw [hgeti, hgetj]
  intro h
  have h1 : (pointsOnLine P ℓ)[i] = (pointsOnLine P ℓ)[j] := by
    have := congrArg Prod.fst h; simpa using this
  have hnd := pointsOnLine_nodup P ℓ
  rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem] at hnd
  exact hnd i j _ _ hij h1

/-- `edgesOnLineWithProof P ℓ` is `Nodup`: the `.pmap` preserves Nodup since the
attached proof component is a `Prop` (subsingleton). -/
lemma edgesOnLineWithProof_nodup (P : Finset (ℝ × ℝ)) (ℓ : Set (ℝ × ℝ)) :
    (edgesOnLineWithProof P ℓ).Nodup := by
  unfold edgesOnLineWithProof
  rw [List.nodup_iff_pairwise_ne, List.pairwise_pmap]
  have hnd := edgesOnLine_nodup P ℓ
  rw [List.nodup_iff_pairwise_ne] at hnd
  apply hnd.imp
  intro a b hne h1 h2 heq
  apply hne
  have hf := congrArg PSigma.fst heq
  simpa using hf

/-- **Cross-line Nodup support.** If a `Σ'` edge entry `s` lies in
`edgesOnLineWithProof P ℓ₁ ∩ edgesOnLineWithProof P ℓ₂` and the lines are affine,
then `ℓ₁ = ℓ₂`. Reason: both `s.1.1` and `s.1.2` lie on both lines (`edgesOnLine_mem`),
and they are distinct (`edgesOnLine_distinct`), so the two lines coincide
(`lines_through_two_points_le_one`). -/
lemma edgesOnLineWithProof_line_unique {P : Finset (ℝ × ℝ)} {L : Finset (Set (ℝ × ℝ))}
    (hL : ∀ ℓ ∈ L, IsAffineLine ℓ)
    {ℓ₁ ℓ₂ : Set (ℝ × ℝ)} (hℓ₁ : ℓ₁ ∈ L) (hℓ₂ : ℓ₂ ∈ L)
    {s : Σ' e : (ℝ × ℝ) × (ℝ × ℝ), e.1 ≠ e.2}
    (h₁ : s ∈ edgesOnLineWithProof P ℓ₁) (h₂ : s ∈ edgesOnLineWithProof P ℓ₂) :
    ℓ₁ = ℓ₂ := by
  have hsℓ₁ : s.1 ∈ edgesOnLine P ℓ₁ := mem_edgesOnLineWithProof h₁
  have hsℓ₂ : s.1 ∈ edgesOnLine P ℓ₂ := mem_edgesOnLineWithProof h₂
  have hmem₁ := edgesOnLine_mem P ℓ₁ s.1 hsℓ₁
  have hmem₂ := edgesOnLine_mem P ℓ₂ s.1 hsℓ₂
  have hdist : s.1.1 ≠ s.1.2 := s.2
  by_contra hne
  -- Two distinct points on two distinct lines, but at most one line through them.
  have hboth_in_L : ∀ ℓ ∈ ({ℓ₁, ℓ₂} : Finset (Set (ℝ × ℝ))), ℓ ∈ L := by
    intro ℓ hℓ
    rcases Finset.mem_insert.mp hℓ with rfl | hℓ
    · exact hℓ₁
    · rw [Finset.mem_singleton] at hℓ; rw [hℓ]; exact hℓ₂
  have hℓ_filter : ({ℓ₁, ℓ₂} : Finset (Set (ℝ × ℝ))) ⊆
      L.filter (fun ℓ => s.1.1 ∈ ℓ ∧ s.1.2 ∈ ℓ) := by
    intro ℓ hℓ
    rcases Finset.mem_insert.mp hℓ with rfl | hℓ
    · exact Finset.mem_filter.mpr ⟨hℓ₁, hmem₁.1.2, hmem₁.2.2⟩
    · rw [Finset.mem_singleton] at hℓ; rw [hℓ]
      exact Finset.mem_filter.mpr ⟨hℓ₂, hmem₂.1.2, hmem₂.2.2⟩
  have h₂' : ({ℓ₁, ℓ₂} : Finset _).card ≤
      (L.filter (fun ℓ => s.1.1 ∈ ℓ ∧ s.1.2 ∈ ℓ)).card :=
    Finset.card_le_card hℓ_filter
  have hcard : ({ℓ₁, ℓ₂} : Finset _).card = 2 := by
    rw [Finset.card_insert_of_notMem (by rwa [Finset.mem_singleton]),
        Finset.card_singleton]
  have hbound : (L.filter (fun ℓ => s.1.1 ∈ ℓ ∧ s.1.2 ∈ ℓ)).card ≤ 1 :=
    lines_through_two_points_le_one hL hdist
  omega

/-- **`allEdges P L` is `Nodup`** (under affineness). Per-line via
`edgesOnLineWithProof_nodup`; cross-line via `edgesOnLineWithProof_line_unique`
(applied through `Pairwise.imp_of_mem` on the `Nodup L.toList`). -/
lemma allEdges_nodup (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    (hL : ∀ ℓ ∈ L, IsAffineLine ℓ) :
    (allEdges P L).Nodup := by
  unfold allEdges
  rw [List.nodup_iff_pairwise_ne]
  rw [show (fun a b : Σ' e : (ℝ × ℝ) × (ℝ × ℝ), e.1 ≠ e.2 => a ≠ b) =
        (fun a b => ¬ a = b) from rfl]
  -- Equivalently: nodup of `flatMap`.
  rw [← List.nodup_iff_pairwise_ne]
  apply List.nodup_flatMap.mpr
  refine ⟨fun ℓ _ => edgesOnLineWithProof_nodup P ℓ, ?_⟩
  -- Pairwise (Disjoint on edgesOnLineWithProof) on L.toList: distinct lines'
  -- edge lists are disjoint (because a shared `s` would force the lines to coincide).
  have hLnd : L.toList.Nodup := Finset.nodup_toList _
  rw [List.nodup_iff_pairwise_ne] at hLnd
  apply hLnd.imp_of_mem
  intro ℓ₁ ℓ₂ h₁L h₂L hne
  rw [Finset.mem_toList] at h₁L h₂L
  -- Disjoint two lists of edges: no element is in both.
  rw [Function.onFun]
  rw [List.disjoint_iff_ne]
  intro s hs t ht heq
  subst heq
  apply hne
  exact edgesOnLineWithProof_line_unique hL h₁L h₂L hs ht

/-! #### W1 — the edge → line map -/

/-- **W1, the line-for-edge witness.** Each entry of `allEdges P L` came from
some `ℓ ∈ L.toList` via the `flatMap`; we name that line. -/
lemma allEdges_mem_witness (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    (i : Fin (stMultigraph P L).numEdges) :
    ∃ ℓ ∈ L.toList, (allEdges P L)[i.val] ∈ edgesOnLineWithProof P ℓ := by
  have hmem : (allEdges P L)[i.val] ∈ allEdges P L := List.getElem_mem _
  unfold allEdges at hmem
  rw [List.mem_flatMap] at hmem
  exact hmem

/-- **W1.** The edge-to-line map, defined via `Classical.choose`. -/
noncomputable def lineForEdge (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    (i : Fin (stMultigraph P L).numEdges) : Set (ℝ × ℝ) :=
  (allEdges_mem_witness P L i).choose

lemma lineForEdge_mem_toList (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    (i : Fin (stMultigraph P L).numEdges) : lineForEdge P L i ∈ L.toList :=
  (allEdges_mem_witness P L i).choose_spec.1

lemma lineForEdge_mem (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    (i : Fin (stMultigraph P L).numEdges) : lineForEdge P L i ∈ L := by
  rw [← Finset.mem_toList]; exact lineForEdge_mem_toList P L i

lemma allEdges_mem_edgesOnLineWithProof_lineForEdge
    (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    (i : Fin (stMultigraph P L).numEdges) :
    (allEdges P L)[i.val] ∈ edgesOnLineWithProof P (lineForEdge P L i) :=
  (allEdges_mem_witness P L i).choose_spec.2

/-- The bare edge underlying `allEdges[i.val]` lies in `edgesOnLine P (lineForEdge i)`. -/
lemma allEdges_fst_mem_edgesOnLine (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    (i : Fin (stMultigraph P L).numEdges) :
    ((allEdges P L)[i.val]).1 ∈ edgesOnLine P (lineForEdge P L i) :=
  mem_edgesOnLineWithProof (allEdges_mem_edgesOnLineWithProof_lineForEdge P L i)

/-- Both endpoints of the bare edge lie on `lineForEdge i`. -/
lemma allEdges_endpoints_on_lineForEdge (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    (i : Fin (stMultigraph P L).numEdges) :
    ((allEdges P L)[i.val]).1.1 ∈ lineForEdge P L i
    ∧ ((allEdges P L)[i.val]).1.2 ∈ lineForEdge P L i := by
  have h := edgesOnLine_mem P (lineForEdge P L i) _ (allEdges_fst_mem_edgesOnLine P L i)
  exact ⟨h.1.2, h.2.2⟩

/-- **Interior of `(stMultigraph P L).arc i` ⊆ `lineForEdge i`** (W2 packaged). -/
lemma stMultigraph_arc_interior_subset_line (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    (hL : ∀ ℓ ∈ L, IsAffineLine ℓ) (i : Fin (stMultigraph P L).numEdges) :
    interiorOfArc ((stMultigraph P L).arc i) ⊆ lineForEdge P L i := by
  have hℓ_aff := hL _ (lineForEdge_mem P L i)
  have hp := (allEdges_endpoints_on_lineForEdge P L i).1
  have hq := (allEdges_endpoints_on_lineForEdge P L i).2
  -- `(stMultigraph P L).arc i = segmentArc ((allEdges P L)[i.val].1).1 ... .2 _`.
  show interiorOfArc (segmentArc ((allEdges P L)[i.val].1).1 ((allEdges P L)[i.val].1).2
        (allEdges P L)[i.val].2) ⊆ lineForEdge P L i
  exact interiorOfArc_segmentArc_subset_line hℓ_aff hp hq _

/-- **W3 + W1 combined.** Two distinct edge indices that share a `lineForEdge`
value have disjoint arc interiors. Uses `allEdges_nodup` to push index-distinctness
to bare-edge-distinctness, then `edgesOnLine_bare_disjoint` on the common line. -/
lemma stMultigraph_same_line_disjoint (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    (hL : ∀ ℓ ∈ L, IsAffineLine ℓ)
    {i j : Fin (stMultigraph P L).numEdges} (hij : i ≠ j)
    (hline : lineForEdge P L i = lineForEdge P L j) :
    Disjoint (interiorOfArc ((stMultigraph P L).arc i))
             (interiorOfArc ((stMultigraph P L).arc j)) := by
  set ℓ := lineForEdge P L i with hℓdef
  have hℓ_aff : IsAffineLine ℓ := hL ℓ (lineForEdge_mem P L i)
  -- Per-line membership of each edge's bare entry.
  have hi_in : ((allEdges P L)[i.val]).1 ∈ edgesOnLine P ℓ :=
    allEdges_fst_mem_edgesOnLine P L i
  have hj_in : ((allEdges P L)[j.val]).1 ∈ edgesOnLine P ℓ := by
    have := allEdges_fst_mem_edgesOnLine P L j
    rwa [← hline] at this
  -- Distinctness of bare entries: i ≠ j combined with allEdges_nodup.
  have hne_bare : ((allEdges P L)[i.val]).1 ≠ ((allEdges P L)[j.val]).1 := by
    intro hne_b
    have hne_full : (allEdges P L)[i.val] = (allEdges P L)[j.val] := by
      -- Two `Σ' e, P e` entries with `P : Prop` are equal iff their `.1`s match.
      apply PSigma.ext hne_b
      apply proof_irrel_heq
    have hnd := allEdges_nodup P L hL
    rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem] at hnd
    apply hij
    apply Fin.ext
    rcases lt_trichotomy i.val j.val with hlt | heq | hgt
    · exact absurd hne_full (hnd _ _ _ _ hlt)
    · exact heq
    · exact absurd hne_full.symm (hnd _ _ _ _ hgt)
  -- Distinctness of endpoints.
  have hd₁ := ((allEdges P L)[i.val]).2
  have hd₂ := ((allEdges P L)[j.val]).2
  -- Apply bare disjointness.
  exact edgesOnLine_bare_disjoint hℓ_aff hi_in hj_in hne_bare hd₁ hd₂


/-- **W4, the line-pair injection.** Maps crossing pairs `(i, j)` of edge indices
to the pair of lines `(lineForEdge i, lineForEdge j) ∈ L ×ˢ L`. We use this as
the witness for `Finset.card_le_card_of_injOn`. -/
noncomputable def crossingLinePair (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    (ij : Fin (stMultigraph P L).numEdges × Fin (stMultigraph P L).numEdges) :
    Set (ℝ × ℝ) × Set (ℝ × ℝ) :=
  (lineForEdge P L ij.1, lineForEdge P L ij.2)

/-- **Hypothesis `hwd` (carries the geometric crossing bound under encoding B).**
`WellDrawn`, i.e. `crossingCount (stMultigraph P L) ≤ L.card²`.

Proof. Map each crossing pair `(i, j)` to the unordered pair of lines `(line(i),
line(j)) ∈ L ×ˢ L` via `crossingLinePair`. On a crossing pair:
* `lineForEdge i ≠ lineForEdge j`: otherwise W3 (`stMultigraph_same_line_disjoint`)
  forces disjoint interiors, contradicting the crossing's nonempty intersection.
* The intersection point lies on `lineForEdge i ∩ lineForEdge j` (W2 packaged via
  `stMultigraph_arc_interior_subset_line`).
* By `encard_inter_le_one_of_lines`, the intersection is `≤ 1` point. So two
  crossing pairs `(i₁, j₁)` and `(i₂, j₂)` mapped to the same line-pair must share
  their crossing point; W3 then forces `i₁ = i₂` and `j₁ = j₂` (within each line,
  at most one edge contains a given point in its interior).
Cardinality: `crossingCount ≤ (L ×ˢ L).card = L.card²`. -/
lemma stMultigraph_wellDrawn (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    (hL : ∀ ℓ ∈ L, IsAffineLine ℓ) :
    (stMultigraph P L).WellDrawn := by
  -- Unfold `WellDrawn` to `crossingCount ≤ L.card²` (under encoding B,
  -- `(stMultigraph P L).crossings = L.card^2`).
  show (stMultigraph P L).crossingCount ≤ (stMultigraph P L).crossings
  rw [show (stMultigraph P L).crossings = L.card ^ 2 from rfl]
  unfold DrawnMultigraph.crossingCount
  -- The crossing set as a Finset.
  set S := Finset.filter (fun ij : Fin (stMultigraph P L).numEdges × Fin (stMultigraph P L).numEdges =>
      ij.1 < ij.2 ∧
      (interiorOfArc ((stMultigraph P L).arc ij.1) ∩
        interiorOfArc ((stMultigraph P L).arc ij.2)).Nonempty) Finset.univ with hSdef
  -- Inject into `L ×ˢ L`.
  have hLcard : (L ×ˢ L).card = L.card ^ 2 := by rw [Finset.card_product]; ring
  rw [← hLcard]
  apply Finset.card_le_card_of_injOn (crossingLinePair P L)
  · -- MapsTo: every crossing pair maps into `L ×ˢ L`.
    intro ij _
    unfold crossingLinePair
    rw [Finset.mem_coe, Finset.mem_product]
    exact ⟨lineForEdge_mem P L _, lineForEdge_mem P L _⟩
  · -- Injectivity on the crossing set.
    intro ij₁ hij₁ ij₂ hij₂ heq
    rw [Finset.mem_coe, Finset.mem_filter] at hij₁ hij₂
    obtain ⟨_, hlt₁, hcross₁⟩ := hij₁
    obtain ⟨_, hlt₂, hcross₂⟩ := hij₂
    -- Decompose `heq` into per-component equalities.
    unfold crossingLinePair at heq
    have hi_eq : lineForEdge P L ij₁.1 = lineForEdge P L ij₂.1 := by
      have := congrArg Prod.fst heq; simpa using this
    have hj_eq : lineForEdge P L ij₁.2 = lineForEdge P L ij₂.2 := by
      have := congrArg Prod.snd heq; simpa using this
    -- Distinct-line property for any crossing pair.
    have hℓne₁ : lineForEdge P L ij₁.1 ≠ lineForEdge P L ij₁.2 := by
      intro hℓ
      have hne_idx : ij₁.1 ≠ ij₁.2 := ne_of_lt hlt₁
      have := stMultigraph_same_line_disjoint P L hL hne_idx hℓ
      rw [Set.disjoint_iff_inter_eq_empty] at this
      rcases hcross₁ with ⟨x, hx⟩
      have hxin : x ∈ interiorOfArc ((stMultigraph P L).arc ij₁.1) ∩
                  interiorOfArc ((stMultigraph P L).arc ij₁.2) := hx
      rw [this] at hxin; exact hxin.elim
    -- Each crossing point lies on both lines.
    obtain ⟨x₁, hx₁⟩ := hcross₁
    obtain ⟨x₂, hx₂⟩ := hcross₂
    have hx₁_on_ℓi : x₁ ∈ lineForEdge P L ij₁.1 :=
      stMultigraph_arc_interior_subset_line P L hL ij₁.1 hx₁.1
    have hx₁_on_ℓj : x₁ ∈ lineForEdge P L ij₁.2 :=
      stMultigraph_arc_interior_subset_line P L hL ij₁.2 hx₁.2
    have hx₂_on_ℓi : x₂ ∈ lineForEdge P L ij₂.1 :=
      stMultigraph_arc_interior_subset_line P L hL ij₂.1 hx₂.1
    have hx₂_on_ℓj : x₂ ∈ lineForEdge P L ij₂.2 :=
      stMultigraph_arc_interior_subset_line P L hL ij₂.2 hx₂.2
    -- The intersection of the two lines is `≤ 1` point, hence `x₁ = x₂`.
    have hℓi_aff : IsAffineLine (lineForEdge P L ij₁.1) := hL _ (lineForEdge_mem P L _)
    have hℓj_aff : IsAffineLine (lineForEdge P L ij₁.2) := hL _ (lineForEdge_mem P L _)
    have hsub := encard_inter_le_one_of_lines hℓi_aff hℓj_aff hℓne₁
    have hx₁_inter : x₁ ∈ lineForEdge P L ij₁.1 ∩ lineForEdge P L ij₁.2 := ⟨hx₁_on_ℓi, hx₁_on_ℓj⟩
    have hx₂_inter : x₂ ∈ lineForEdge P L ij₁.1 ∩ lineForEdge P L ij₁.2 := by
      rw [hi_eq, hj_eq]; exact ⟨hx₂_on_ℓi, hx₂_on_ℓj⟩
    have hxeq : x₁ = x₂ := hsub hx₁_inter hx₂_inter
    -- Now within each line, at most one edge contains a given interior point.
    -- Apply W3 to show ij₁.1 = ij₂.1 and ij₁.2 = ij₂.2.
    apply Prod.ext
    · -- ij₁.1 = ij₂.1
      by_contra hne
      have h_disj := stMultigraph_same_line_disjoint P L hL hne hi_eq
      rw [Set.disjoint_iff_inter_eq_empty] at h_disj
      have hx_both : x₁ ∈ interiorOfArc ((stMultigraph P L).arc ij₁.1) ∩
                          interiorOfArc ((stMultigraph P L).arc ij₂.1) := by
        refine ⟨hx₁.1, ?_⟩
        rw [hxeq]; exact hx₂.1
      rw [h_disj] at hx_both; exact hx_both.elim
    · -- ij₁.2 = ij₂.2
      by_contra hne
      have h_disj := stMultigraph_same_line_disjoint P L hL hne hj_eq
      rw [Set.disjoint_iff_inter_eq_empty] at h_disj
      have hx_both : x₁ ∈ interiorOfArc ((stMultigraph P L).arc ij₁.2) ∩
                          interiorOfArc ((stMultigraph P L).arc ij₂.2) := by
        refine ⟨hx₁.2, ?_⟩
        rw [hxeq]; exact hx₂.2
      rw [h_disj] at hx_both; exact hx_both.elim

/-- **Szemerédi–Trotter**, conditional on the multigraph crossing lemma `hCL`.

Assembled from the Phase-1 combinatorial core `incidence_bound_of_crossingLemma`
and the geometric realization `stMultigraph` with its five discharged hypotheses
(`stMultigraph_card_V`, `stMultigraph_multiplicity_le_one`, `stMultigraph_wellDrawn`,
`incidences_le_numEdges_add`, `stMultigraph_crossings_le`) — all PROVEN sorry-free.
So this is Szemerédi–Trotter conditional on `hCL` alone; the `hCL` hypothesis
threads the crossing lemma at the type level (no `sorryAx`).

Axiom audit: `[propext, Classical.choice, Quot.sound]`. -/
theorem szemerediTrotter_of_crossingLemma
    (hCL : CrossingLemmaMultigraphStatement) :
    SzemerediTrotterStatement := by
  refine ⟨64, by norm_num, ?_⟩
  intro P L hL
  exact incidence_bound_of_crossingLemma hCL
    (incidences P L) P.card L.card (stMultigraph P L)
    (stMultigraph_card_V P L)
    (stMultigraph_multiplicity_le_one P L hL)
    (stMultigraph_wellDrawn P L hL)
    (incidences_le_numEdges_add P L hL)
    (stMultigraph_crossings_le P L)

end PachSharir.ST
