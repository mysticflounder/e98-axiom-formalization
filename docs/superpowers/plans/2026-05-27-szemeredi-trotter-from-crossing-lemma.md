# Szemerédi–Trotter from the Crossing Lemma — Implementation Plan

> **Status (post-execution, 2026-05-27): COMPLETE.** All four phases shipped on
> local `main` through commit `fc5f70d`. The headline theorem
> `PachSharir.ST.szemerediTrotter_of_crossingLemma : SzemerediTrotterStatement`
> takes a single hypothesis `hCL : CrossingLemmaMultigraphStatement` and has
> independently-verified `#print axioms = [propext, Classical.choice, Quot.sound]`
> — no `sorryAx`. Phase 1 (combinatorial endgame, commit `9d7c092`), Phase 2
> (geometric bridges Tasks 4–6, ff-merged `d08ee11`), and Phase 3 (assembly,
> `d290340`) followed the checkboxes below. The plan's "Known risk" — that the
> geometric `wellDrawn` bound might ship as a labelled residual — was resolved
> in a follow-on Phase 4 (`fc5f70d`, `pach-sharir/ST: close stMultigraph_wellDrawn (W1–W4 geometric crossing bound)`),
> which discharged `stMultigraph_wellDrawn` sorry-free via flatMap edge→line
> inversion + `pointsOnLine` sortedness (`List.sorted_mergeSort`) + the
> `crossingLinePair` injection into `L ×ˢ L`. The unchecked checkboxes below are
> kept as the historical record of execution order.
>
> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.
>
> **Domain caveat (read first):** This is *novel Lean 4 / Mathlib formalization*, not app development. The "complete compile-ready code in every step" convention is relaxed for **proof bodies only**: every *statement, definition, and lemma signature* is given as complete Lean, but proof bodies are specified as a **strategy + the exact Mathlib API to use**, because writing verbatim tactic scripts in advance for unproven mathematics is not honest — discovering the script is the work. The "test" for each task is: the file builds, the `sorry` count is exactly what the task claims, and `#print axioms` shows the expected surface.

**Goal:** Prove classical Szemerédi–Trotter (point–line incidence bound `I ≤ C·(m^{2/3}n^{2/3} + m + n)` in `ℝ²`) as a theorem *conditional on* the multigraph crossing lemma, isolating that lemma as a single named hypothesis.

**Architecture:** A new file `pach-sharir/PachSharir/SzemerediTrotter.lean` (the `pach-sharir` module already `require`s `crossing-lemma`). ST is internal infrastructure toward Theorem 2.3, so it lives inside `pach-sharir`, not in a verbatim paper module. The proof factors into a **geometry-free crossing-lemma endgame** (reusable verbatim by the later Pach–Sharir step) and a **geometric realization** (build a `DrawnMultigraph` of straight segments from points + lines). The crossing lemma enters as one hypothesis `hCL : CrossingLemma.PDZ.CrossingLemmaMultigraphStatement`.

**Tech Stack:** Lean 4 `v4.27.0`, Mathlib `@ v4.27.0`, Lake. Native space `ℝ × ℝ` (matching `crossing-lemma`; the `EuclideanSpace ℝ (Fin 2)` bridge to `Theorem23.lean` is deferred — see Out of Scope). Key Mathlib areas: `Real.rpow`, `Finset.card`, affine lines / `Collinear` / `AffineSubspace`, `Continuous`, `Set.InjOn`.

---

## Scope

**In scope.** A self-contained conditional theorem: `∀ (P : Finset (ℝ×ℝ)) (L : Finset (ℝ×ℝ → Prop or Set)), <line hyps> → I(P,L) ≤ C·(|P|^{2/3}|L|^{2/3} + |P| + |L|)`, proved from `hCL`. The reusable crossing-lemma endgame. All supporting combinatorics, the geometric crossing bound, and the `rpow` arithmetic.

**Out of scope (do NOT touch).**
- `crossing-lemma/` internals — `hCL` is consumed as a hypothesis; we do not discharge `WeakAveragedBound`, `PlanarEdgeBound`, or the arc-separation residual.
- `pdz/`, `incidence-assembly/`, the `Theorem23.lean` verbatim statements.
- The `EuclideanSpace ℝ (Fin 2)` ↔ `ℝ × ℝ` bridge and the d=1 specialization of `Theorem23Statement`. Recorded as a follow-up, not built here.

**The one named hypothesis.** `hCL : CrossingLemma.PDZ.CrossingLemmaMultigraphStatement`. Every theorem body stays `sorry`-free except where this plan *explicitly* labels a residual; the final ST theorem takes `hCL` as an argument.

**DURABLE INVARIANT (#1 priority, overrides everything here).** This plan adds a *new* file in `pach-sharir` and touches neither frozen endpoint artifact, so it inherently preserves the route — but the constraint stands regardless: the downstream endpoint `IncidenceAssembly.pachDeZeeuwTheorem11_unconditional : PachDeZeeuw.PachDeZeeuwIrreducibleCurveDistinctDistancesStatement` (hypothesis-free signature) and the frozen Prop must always typecheck and export with exact name+type. No task may rename, move, re-signature, or add hypotheses to either. See `nthdegree get 01KSNGJQJFN6H7MHC7PM83WTKS`.

**Soundness wart — RESOLVED 2026-05-27 (before this plan runs).** `DrawnMultigraph.crossings : ℕ` was a free field, leaving `CrossingLemmaMultigraphStatement` unsound (the conclusion lower-bounds `crossings`, so `crossings := 0` on a complete multigraph falsified it). Repaired in `crossing-lemma`: added `DrawnMultigraph.crossingCount` (true count of edge-index pairs `i < j` with intersecting arc interiors) and `DrawnMultigraph.WellDrawn G := G.crossingCount ≤ G.crossings`, threaded as a new hypothesis into both `CrossingLemmaMultigraphStatement` and `WeakAveragedBound`; `crossingLemma_of_weakBound` builds green. **Consequence for this plan:** the ST construction sets `crossings := crossingCount`, so `WellDrawn` holds by `le_refl` (Task 6), and the crossing bound becomes a bound on `crossingCount` (Task 6). The endgame lemma (Task 3) takes `WellDrawn` as a hypothesis.

## Line representation decision

A line is represented as a **`Set (ℝ × ℝ)`** carrying a predicate `IsAffineLine : Set (ℝ×ℝ) → Prop` defined as "the set is a 1-dimensional affine subspace" (equivalently `∃ a b c, (a,b) ≠ 0 ∧ ℓ = {p | a*p.1 + b*p.2 = c}`). This matches the `Set`-based curve representation in `Theorem23.lean` (`IsPlaneAlgebraicCurveOfDegreeLE 1`) and gives the two facts the proof needs as lemmas: distinct lines meet in ≤1 point, two distinct points lie on ≤1 line.

## File Structure

- `pach-sharir/PachSharir/SzemerediTrotter.lean` — **new.** All ST content. Responsibility: the conditional ST theorem and its full proof, factored into the three phases below. One file because the phases are tightly coupled and share the `DrawnMultigraph` construction; if it grows past ~600 lines, split the geometric realization into `SzemerediTrotter/Realization.lean`.
- `pach-sharir/PachSharir.lean` — **modify.** Add `import PachSharir.SzemerediTrotter` immediately after the copyright block, before the module docstring (import placement is load-bearing in Lean 4 — see the prior `Theorem23` import).

No other files change.

---

## Phase 1 — The geometry-free crossing-lemma endgame

This phase touches no geometry. It proves: *given* a `DrawnMultigraph` `G` plus the incidence bookkeeping as plain hypotheses, the crossing lemma yields the ST bound. This is the piece Pach–Sharir (Theorem 2.3) reuses verbatim with `M = 1` swapped for general `M`.

### Task 1: Module scaffold + the ST statement

**Files:**
- Create: `pach-sharir/PachSharir/SzemerediTrotter.lean`
- Modify: `pach-sharir/PachSharir.lean` (add import)

- [ ] **Step 1: Write the file header, imports, namespace, and the line predicate + ST statement.**

```lean
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
```

- [ ] **Step 2: Add the import to the module root.** In `pach-sharir/PachSharir.lean`, add `import PachSharir.SzemerediTrotter` directly after the copyright `/- … -/` block and before the `/-! … -/` docstring.

- [ ] **Step 3: Build.**

Run: `cd pach-sharir && ./lake-build.sh`
Expected: builds green, 0 `sorry` in `SzemerediTrotter.lean` (it has only definitions so far).

- [ ] **Step 4: Commit.**

```bash
git add pach-sharir/PachSharir/SzemerediTrotter.lean pach-sharir/PachSharir.lean
git commit -F /tmp/st-commit-1.txt   # "pach-sharir: scaffold Szemerédi–Trotter statement (conditional on crossing lemma)"
```

### Task 2: Two affine-line incidence facts

**Files:**
- Modify: `pach-sharir/PachSharir/SzemerediTrotter.lean`

- [ ] **Step 1: State the two facts.**

```lean
/-- Two distinct affine lines meet in at most one point. -/
lemma encard_inter_le_one_of_lines {ℓ₁ ℓ₂ : Set (ℝ × ℝ)}
    (h₁ : IsAffineLine ℓ₁) (h₂ : IsAffineLine ℓ₂) (hne : ℓ₁ ≠ ℓ₂) :
    (ℓ₁ ∩ ℓ₂).Subsingleton := by
  sorry

/-- Two distinct points lie on at most one affine line drawn from a given finite
family `L` of lines. -/
lemma lines_through_two_points_le_one {L : Finset (Set (ℝ × ℝ))}
    (hL : ∀ ℓ ∈ L, IsAffineLine ℓ) {p q : ℝ × ℝ} (hpq : p ≠ q) :
    (L.filter (fun ℓ => p ∈ ℓ ∧ q ∈ ℓ)).card ≤ 1 := by
  sorry
```

- [ ] **Step 2: Prove `encard_inter_le_one_of_lines`.**
Strategy: unfold both lines to `{p | aᵢx+bᵢy=cᵢ}`. If two distinct points lay in the intersection, the two linear equations would have a 2-dimensional solution set, forcing the coefficient vectors proportional and (by `ℓ₁ ≠ ℓ₂`) the system inconsistent — contradiction. Mathlib API: work with the `2×2` determinant `a₁b₂ - a₂b₁`; if it is nonzero the solution is unique (`Subsingleton`); if zero the lines are parallel/equal and a shared point forces `ℓ₁ = ℓ₂`. Use `Matrix.det_fin_two`, or argue directly with `linarith`/`nlinarith` on the four scalar equations after `Set.Subsingleton` is reduced to `∀ x y ∈ ·, x = y` via `Set.subsingleton_iff`.

- [ ] **Step 3: Prove `lines_through_two_points_le_one`.**
Strategy: `Finset.card_le_one`. Two distinct lines through the same two distinct points `p ≠ q` would have `{p,q} ⊆ ℓ₁ ∩ ℓ₂`, contradicting `encard_inter_le_one_of_lines` (a `Subsingleton` containing two distinct points is impossible — `Set.Subsingleton` + `hpq`). API: `Finset.card_le_one_iff`, `Set.Subsingleton`.

- [ ] **Step 4: Build, verify 0 `sorry` in the two lemmas.**
Run: `cd pach-sharir && ./lake-build.sh && grep -c sorry PachSharir/SzemerediTrotter.lean`
Expected: green; remaining `sorry` count = 0 for these two lemmas (later tasks add their own, tracked separately).

- [ ] **Step 5: Commit.** `git commit -F /tmp/st-commit-2.txt` — "pach-sharir/ST: affine-line incidence facts (≤1 intersection, ≤1 line through 2 points)".

### Task 3: The crossing-lemma endgame (geometry-free)

This is the reusable core. Given a multigraph whose vertices are the `m` points, with at least `I − n` edges, multiplicity ≤ 1, and crossings ≤ `n²`, derive the ST bound. **No lines, no arcs here** — pure consequence of `hCL` + arithmetic.

**Files:**
- Modify: `pach-sharir/PachSharir/SzemerediTrotter.lean`

- [ ] **Step 1: State the endgame lemma.**

```lean
/-- The crossing-lemma endgame, geometry-free. From the crossing lemma `hCL`
and the incidence bookkeeping of a drawn multigraph `G` (vertices = the `m`
points, `e := G.numEdges ≥ I - n`, multiplicity `≤ 1`, `crossings ≤ n²`),
derive the Szemerédi–Trotter incidence bound for `I` against `m` points and
`n` lines. Reused verbatim by Theorem 2.3 with `M ≥ 1`. -/
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
  sorry
```

(Constant `64` is provisional; pin the exact value during the proof — any fixed real works for `SzemerediTrotterStatement`.)

- [ ] **Step 2: Prove it.**
Strategy: case-split on the crossing-lemma threshold `4 * 1 * m ≤ G.numEdges`.
  - **Threshold fails** (`G.numEdges < 4·m`): then `I ≤ G.numEdges + n < 4m + n`, so the bound holds with room to spare (the `+m+n` term dominates). Pure `Nat`/`Real` arithmetic; `omega` + `Nat.cast_le` + `nlinarith`.
  - **Threshold holds:** apply `hCL G 1 (by norm_num) hmult hwd hthresh` to get `e³ ≤ 64·1·m²·cr ≤ 64·m²·n²`. Take cube roots in `ℝ` via `Real.rpow`: `e ≤ (64 m² n²)^{1/3} = 64^{1/3} m^{2/3} n^{2/3}`. Then `I ≤ e + n`. API: `Real.rpow_natCast`, `Real.rpow_le_rpow`, `Real.rpow_natCast`, `Real.rpow_mul`, `Real.rpow_le_rpow_left_iff`, and the monotonicity `pow_le_pow_left`. The cube-root manipulation is the fiddly part: convert `e^3 ≤ K` to `e ≤ K^{1/3}` via `Real.rpow_le_rpow_iff_left`/`Real.le_rpow_inv_iff_of_pos` or by raising both sides to `1/3` with `Real.rpow_le_rpow`.

- [ ] **Step 3: Build, verify the endgame is `sorry`-free.**
Run: `cd pach-sharir && ./lake-build.sh`
Expected: green; `incidence_bound_of_crossingLemma` has no `sorry`.

- [ ] **Step 4: Commit.** "pach-sharir/ST: geometry-free crossing-lemma endgame (e³≤64m²cr ⟹ ST bound)".

---

## Phase 2 — Geometric realization (points + lines ⟹ `DrawnMultigraph`)

The substantive geometric content: turn `P, L` into an actual plane-drawn multigraph of straight segments so the Phase 1 hypotheses hold. **This phase may surface its own residual** (point-ordering-along-a-line and disjoint-segment-interior facts are nontrivial); any residual MUST be a clearly labelled `sorry` with an `OBSTRUCTION`/`CONJECTURED` comment in the `crossing-lemma` house style, never a silent one.

### Task 4: Order the incident points on a single line and build its edge list

**Files:**
- Modify: `pach-sharir/PachSharir/SzemerediTrotter.lean`

- [ ] **Step 1: Define the per-line point ordering and consecutive-pair edges.**

```lean
/-- The points of `P` incident to a line `ℓ`, sorted along `ℓ` by a linear
parameter (projection onto the line's direction vector). Returned as a `List`
so consecutive pairs are well-defined. -/
noncomputable def pointsOnLine (P : Finset (ℝ × ℝ)) (ℓ : Set (ℝ × ℝ)) :
    List (ℝ × ℝ) :=
  sorry

/-- Consecutive (point, point) pairs along `ℓ`: `k` incident points give `k-1`
segment edges. -/
noncomputable def edgesOnLine (P : Finset (ℝ × ℝ)) (ℓ : Set (ℝ × ℝ)) :
    List ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (pointsOnLine P ℓ).zip (pointsOnLine P ℓ).tail
```

- [ ] **Step 2: Implement `pointsOnLine`.**
Strategy: extract `a b c` from `IsAffineLine ℓ`; the direction vector is `(-b, a)`. Sort `P.filter (· ∈ ℓ)` by the key `fun p => -b * p.1 + a * p.2` (projection onto the direction). API: `Finset.sort` with a `LinearOrder` on the key, or `List.mergeSort`. Distinct collinear points have distinct keys (the direction is nonzero), giving a strict order — prove this as a side lemma `keys_injOn`.

- [ ] **Step 3: Prove the edge-count identity.**

```lean
lemma length_edgesOnLine (P : Finset (ℝ × ℝ)) (ℓ : Set (ℝ × ℝ)) :
    (edgesOnLine P ℓ).length + 1 = (pointsOnLine P ℓ).length
      ∨ edgesOnLine P ℓ = [] := by
  sorry
```
Strategy: `List.length_zip`, `List.length_tail`; a list of length `k` has `k-1` consecutive pairs (`k = 0` gives `[]`). Then relate `(pointsOnLine P ℓ).length` to `(P.filter (· ∈ ℓ)).card`.

- [ ] **Step 4: Build, commit.** "pach-sharir/ST: per-line point ordering and consecutive-segment edges".

### Task 5: Assemble the global `DrawnMultigraph` of straight segments

**Files:**
- Modify: `pach-sharir/PachSharir/SzemerediTrotter.lean`

- [ ] **Step 1: Define the straight-segment arc and the assembled multigraph.**

```lean
/-- The straight segment from `p` to `q` as a `SimpleCurveArc` (degenerate when
`p = q`, excluded by construction since edges join distinct ordered points). -/
noncomputable def segmentArc (p q : ℝ × ℝ) : SimpleCurveArc where
  param := fun t => ((1 - (t : ℝ)) • p.1 + (t : ℝ) • q.1,
                     (1 - (t : ℝ)) • p.2 + (t : ℝ) • q.2)
  cont := by sorry
  inj := by sorry   -- requires p ≠ q; thread as a hypothesis or restrict the domain

/-- The drawn multigraph: vertices `P`, edges = all consecutive segments over
all lines of `L`, `crossings` set to the true interior-crossing count. -/
noncomputable def stMultigraph
    (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ))) : DrawnMultigraph :=
  sorry
```

- [ ] **Step 2: Implement `segmentArc`.** `cont`: `Continuous` of affine combination — `continuous_const`, `Continuous.add`, `Continuous.smul`, `continuous_subtype_val`. `inj`: injective on `[0,1]` iff `p ≠ q`; the affine map `t ↦ (1-t)p + tq` is injective when `p ≠ q` (`linarith` on coordinates). **Thread `p ≠ q`** — edges only join distinct consecutive points, so this is available.

- [ ] **Step 3: Implement `stMultigraph`.** `V := P`; `numEdges :=` total length of `edgesOnLine` over `L` (sum); `endpoints :=` indexed lookup into the concatenated edge list; `arc := fun i => segmentArc …`; `crossings :=` the structure's own `crossingCount` (set it to the true interior-crossing count so `WellDrawn` is `le_refl` — note `crossingCount` depends only on `numEdges`/`arc`, set after those, so no circularity). `endpoints_mem`: each consecutive point lies in `P` (from `pointsOnLine ⊆ P`).

- [ ] **Step 4: Build (expect labelled `sorry`s for the geometric obligations), commit.**
Mark every remaining `sorry` with an `OBSTRUCTION`/`CONJECTURED` comment naming what is open. Commit: "pach-sharir/ST: assemble straight-segment DrawnMultigraph (geometric obligations labelled)".

### Task 6: Discharge the three Phase-1 hypotheses for `stMultigraph`

**Files:**
- Modify: `pach-sharir/PachSharir/SzemerediTrotter.lean`

- [ ] **Step 1: State the three bridge lemmas.**

```lean
lemma stMultigraph_card_V (P L) :
    (stMultigraph P L).V.card = P.card := by sorry

/-- Well-drawn for free: the construction sets `crossings := crossingCount`. -/
lemma stMultigraph_wellDrawn (P L) : (stMultigraph P L).WellDrawn := by
  sorry   -- `le_refl _` after unfolding WellDrawn/stMultigraph, if crossings := crossingCount defeq

/-- Multiplicity ≤ 1: at most one segment joins a given ordered pair, because the
pair determines its line (≤1 line through 2 points) and its position on it. -/
lemma stMultigraph_multiplicity_le_one
    (P L) (hL : ∀ ℓ ∈ L, IsAffineLine ℓ) :
    ∀ p q, (stMultigraph P L).multiplicity p q ≤ 1 := by sorry

/-- Edge count vs incidences: `I ≤ e + n`, since a line with `k` incident points
contributes `k-1 ≥ k - 1` edges and there are `≤ n` lines. -/
lemma incidences_le_numEdges_add
    (P L) (hL : ∀ ℓ ∈ L, IsAffineLine ℓ) :
    incidences P L ≤ (stMultigraph P L).numEdges + L.card := by sorry

/-- Crossing bound: `crossings ≤ n²`, since each crossing lies on a pair of
distinct lines and two distinct lines cross ≤ once. -/
lemma stMultigraph_crossings_le
    (P L) (hL : ∀ ℓ ∈ L, IsAffineLine ℓ) :
    (stMultigraph P L).crossings ≤ L.card ^ 2 := by sorry
```

- [ ] **Step 2: Prove `stMultigraph_card_V`** — definitional (`V := P`), `rfl`/`simp [stMultigraph]`.

- [ ] **Step 3: Prove `incidences_le_numEdges_add`** — sum `length_edgesOnLine` over `L`: `Σ (k_ℓ - 1) = (Σ k_ℓ) - #{ℓ : k_ℓ ≥ 1} ≥ I - n`. `Σ k_ℓ = I` by double counting (`incidences` = sum over lines of incident-point counts). API: `Finset.sum_comm`/`Finset.card_eq_sum_…`, `Finset.sum_tsub_le` or careful `Nat` arithmetic with `omega` per line.

- [ ] **Step 4: Prove `stMultigraph_crossings_le`** — map each crossing to the unordered pair of lines carrying its two segments; the map lands in pairs of *distinct* lines (segments on the same line don't cross in their interiors — collinear ordered segments are interior-disjoint, a side lemma) and is ≤1-to-1 per line-pair (`encard_inter_le_one_of_lines`). So `crossings ≤ C(n,2) ≤ n²`. API: `Finset.card_le_card_of_injOn`, `lines_through_two_points_le_one`/`encard_inter_le_one_of_lines`.

- [ ] **Step 5: Prove `stMultigraph_multiplicity_le_one`** — for `p ≠ q`, at most one line contains both (`lines_through_two_points_le_one`), and on that line they are consecutive in at most one segment. For `p = q`, the multiplicity is 0 (no degenerate edges). API: `DrawnMultigraph.multiplicity` unfolded to a `Finset.filter … .card`, bounded via the injection into lines.

- [ ] **Step 6: Build, commit.** Any genuinely-open geometric fact (e.g. interior-disjointness of collinear consecutive segments) stays a labelled `sorry`; otherwise this task closes them. Commit: "pach-sharir/ST: discharge crossing-lemma hypotheses for the segment multigraph".

---

## Phase 3 — Assemble Szemerédi–Trotter

### Task 7: The conditional ST theorem

**Files:**
- Modify: `pach-sharir/PachSharir/SzemerediTrotter.lean`

- [ ] **Step 1: State and prove the top theorem.**

```lean
/-- **Szemerédi–Trotter**, conditional on the multigraph crossing lemma. -/
theorem szemerediTrotter_of_crossingLemma
    (hCL : CrossingLemmaMultigraphStatement) :
    SzemerediTrotterStatement := by
  refine ⟨64, by norm_num, ?_⟩
  intro P L hL
  exact incidence_bound_of_crossingLemma hCL
    (incidences P L) P.card L.card (stMultigraph P L)
    (stMultigraph_card_V P L)
    (stMultigraph_multiplicity_le_one P L hL)
    (stMultigraph_wellDrawn P L)
    (incidences_le_numEdges_add P L hL)
    (stMultigraph_crossings_le P L hL)
```
(Adjust the constant and the `incidenceBoundTerm` shape to match `SzemerediTrotterStatement` exactly; reconcile `m + n` vs the statement's `P.card + L.card` casts.)

- [ ] **Step 2: Build and verify the axiom surface.**
Run:
```bash
cd pach-sharir && ./lake-build.sh
echo '#print axioms PachSharir.ST.szemerediTrotter_of_crossingLemma' >> PachSharir/SzemerediTrotter.lean
./lake-build.sh   # read the printed axioms, then revert the appended line via Edit (not git checkout — uncommitted work nearby)
```
Expected: if Phase 2 closed all geometric residuals, `#print axioms` = `[propext, Classical.choice, Quot.sound]` (the hypothesis `hCL` carries the crossing lemma at the type level, *not* via `sorryAx`). If labelled residuals remain, `sorryAx` appears and the residual list must match exactly what the file's `OBSTRUCTION` comments claim — no surprises.

- [ ] **Step 3: Final `sorry` audit.**
Run: `grep -n sorry pach-sharir/PachSharir/SzemerediTrotter.lean`
Expected: only the explicitly-labelled geometric residuals (ideally none). Each must have an `OBSTRUCTION`/`CONJECTURED` comment.

- [ ] **Step 4: Commit.** "pach-sharir/ST: Szemerédi–Trotter conditional on the crossing lemma".

---

## Self-Review

**Spec coverage.** Statement (Task 1) ✓; the two line-incidence facts the proof rests on (Task 2) ✓; crossing-lemma application + `rpow` endgame (Task 3) ✓; geometric realization (Tasks 4–5) ✓; the hypotheses Phase 1 needs — `card_V`, `multiplicity`, `WellDrawn`, edge count, crossing bound (Task 6) ✓; assembly + axiom audit (Task 7) ✓. The single named hypothesis `hCL` threads from Task 3 through Task 7 ✓.

**Placeholder scan.** Proof bodies are intentionally strategy+API per the domain caveat in the header. Every *statement/signature* is complete Lean. Genuine open geometry (segment interior-disjointness, the `pointsOnLine` ordering facts) is named explicitly and required to be a *labelled* `sorry`, never a silent "TODO".

**Type consistency.** `stMultigraph P L : DrawnMultigraph` is consumed by `incidence_bound_of_crossingLemma` with `m := P.card`, `n := L.card`, `I := incidences P L`; the four bridge lemmas in Task 6 produce exactly the four hypotheses (`hv`, `hmult`, `he`, `hcr`) that lemma demands — signatures checked to line up. `incidences` / `IsAffineLine` / `SzemerediTrotterStatement` names are used consistently across tasks. Reconcile the final constant and the `+ P.card + L.card` cast shape (flagged in Task 7 Step 1).

**Known risk.** Phase 2 is the real difficulty; if `segmentArc.inj` or the collinear-segment interior-disjointness proves harder than budgeted, those become labelled residuals and ST ships as "conditional on `hCL` + N labelled geometric residuals" rather than "conditional on `hCL` alone" — still a clean, honest deliverable, with the residuals as the next plan's targets.
