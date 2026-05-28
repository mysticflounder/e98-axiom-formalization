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

end PachSharir.ST
