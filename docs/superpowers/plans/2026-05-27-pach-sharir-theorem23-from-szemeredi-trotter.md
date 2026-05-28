# Pach–Sharir Theorem 2.3 from Szemerédi–Trotter — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.
>
> **Domain caveat (read first):** This is *novel Lean 4 / Mathlib formalization*, not app development. The "complete compile-ready code in every step" convention is relaxed for **proof bodies only**: every *statement, definition, and lemma signature* is given as complete Lean, but proof bodies are specified as a **strategy + the exact Mathlib API to use**, because writing verbatim tactic scripts in advance for unproven mathematics is not honest — discovering the script is the work. The "test" for each task is: the file builds, the `sorry` count is exactly what the task claims, and `#print axioms` shows the expected surface.

**Goal:** Prove `PachSharir.Theorem23Statement` (Pach–Sharir Theorem 2.3 — the `m^{2/3} n^{2/3} + m + n` incidence bound for points and degree-`d` algebraic curves with two degrees of freedom and multiplicity `M`) as a theorem *conditional on the same `hCL` hypothesis already discharging Szemerédi–Trotter*, plus a small named algebraic-geometry input. The proof generalizes the existing `PachSharir.ST.szemerediTrotter_of_crossingLemma` (lines, `M=1`) to curves at multiplicity `M`, reusing the same `incidence_bound_of_crossingLemma`-style combinatorial endgame.

**Architecture:** A new file `pach-sharir/PachSharir/PachSharirCurves.lean` holding the curves generalization, plus a thin discharger inserted into `pach-sharir/PachSharir/Theorem23.lean` (one named theorem reduces `Theorem23Statement` to the new conditional). The bulk of the work lives in `PachSharirCurves.lean`. The crossing lemma enters at the same hypothesis surface (`hCL : CrossingLemma.PDZ.CrossingLemmaMultigraphStatement`), applied at general `M ≥ 1` rather than the ST specialization `M = 1`. One additional named hypothesis — the **per-curve Jordan-arc decomposition bound `hJordan`**, which Milnor–Thom 2.2 discharges for the algebraic case — enters as the single algebraic-geometry input. Both hypotheses thread through the file; Theorem 2.3 itself is then conditional on `hCL` and `hJordan`.

**Tech Stack:** Lean 4 `v4.27.0`, Mathlib `@ v4.27.0`, Lake. Two ambient spaces are in play: the existing `SzemerediTrotter` lives in `ℝ × ℝ` (matching `crossing-lemma`), while `Theorem23Statement` is in `EuclideanSpace ℝ (Fin 2)`. A small bridge `Point2 ≃ ℝ × ℝ` is inevitable. Key Mathlib areas: `Real.rpow`, `Finset.card`/`Finset.sum`, `Continuous`/`Path`, `Set.InjOn`, `MvPolynomial` (for the algebraic-curve predicate, but only to UNPACK it for the connected-component count).

---

## Scope

**In scope.** The conditional theorem
```
∀ d M : ℕ, ∃ C : ℝ, 0 < C ∧
  ∀ P Γ, (∀ γ ∈ Γ, IsPlaneAlgebraicCurveOfDegreeLE d γ) →
         TwoDegreesOfFreedom P Γ M →
           (incidenceCount P Γ : ℝ) ≤ C * incidenceBoundTerm P Γ
```
proved from two named hypotheses: `hCL` (multigraph crossing lemma) and `hJordan` (each degree-`d` plane algebraic curve is the union of `≤ (2d)²` Jordan arcs with overlap ≤ 2 — precise Prop in Phase 2 / Task 4). Concretely, `pachSharir23_of_inputs (hCL) (hJordan) : Theorem23Statement` is `sorry`-free at the end of this plan; the public `theorem23 : Theorem23Statement` either becomes `:= pachSharir23_of_inputs hCL_axiom hJordan_axiom` (if upstream axioms are declared inline) or stays at a single labelled `sorry` (if the project's Tier-B axiom block lives elsewhere). The substantive content — the proof of `pachSharir23_of_inputs` — is sorry-free either way.

**Out of scope (do NOT touch).**
- `crossing-lemma/` internals.
- The `bezout`, `curve-symmetries` statement modules. (`milnor-thom` enters only as the *motivation* for `hJordan` — see Phase 2 — but its `MilnorThom22Statement` is NOT consumed here; the consumer is `incidence-assembly` for Lemma 3.3, not Theorem 2.3.)
- `Corollary 2.4` (the `ℝ^D` generalization). Sketched at the bottom; written up in the next plan.
- Gap B / `incidence-assembly/`.
- The frozen public endpoint `IncidenceAssembly.pachDeZeeuwTheorem11_unconditional`.

**The two named hypotheses.**
1. `hCL : CrossingLemma.PDZ.CrossingLemmaMultigraphStatement` — same one ST consumes, threaded through to general `M ≥ 1`.
2. `hJordan : JordanArcDecompositionStatement` — for every `d : ℕ`, every plane algebraic curve of degree `≤ d` decomposes into `≤ (2d)²` Jordan-arc components (precise Prop in Phase 2 / Task 4). This is the **only** algebraic-geometry hook in Theorem 2.3 itself; it is the same content as the d=2 case of Milnor–Thom Theorem 2.2 plus a real-analytic-1-manifold parametrization fact, but stated as a self-contained Prop so the discharger lives outside this plan.

Both hypotheses appear as explicit `Prop` arguments on the new internal theorem `pachSharir23_of_inputs`; the public `theorem23 : Theorem23Statement` is then discharged at top level using them (in this plan we leave **one** clearly-labelled `sorry` at the `theorem23` discharger if `hJordan` cannot yet be supplied — see Phase 4 — but the conditional `pachSharir23_of_inputs` is sorry-free).

**DURABLE INVARIANT (#1 priority, overrides everything here).** This plan adds a new file in `pach-sharir`, inserts a single theorem term in `Theorem23.lean`, and **does not modify** the frozen public endpoint artifact. The `theorem23 : Theorem23Statement := sorry` body is *replaced* by a proof term (possibly `:= pachSharir23_of_inputs hCL hJordan` if both inputs become available, or otherwise left at `sorry` with the obstruction labelled); its Prop signature is unchanged. The downstream endpoint `IncidenceAssembly.pachDeZeeuwTheorem11_unconditional : PachDeZeeuw.PachDeZeeuwIrreducibleCurveDistinctDistancesStatement` is untouched. See `nthdegree get 01KSNGJQJF`.

**Naming-policy invariant.** `Theorem23.lean` is a paper-faithful module: its statements (`Theorem23Statement`, `TwoDegreesOfFreedom`, `IsPlaneAlgebraicCurveOfDegreeLE`, `incidenceBoundTerm`) are VERBATIM from the paper and may NOT be re-shaped to match the proof. Where this plan's internal lemmas use a different ambient space or a different representation (notably `ℝ × ℝ` vs `EuclideanSpace ℝ (Fin 2)`), the bridge lives in `PachSharirCurves.lean`, not in `Theorem23.lean`. See `nthdegree get 01KSNB1CQ5`.

## Strategy selection

### The four routes considered

**Route A (chosen): Pach–Sharir 1998, direct curve generalization.**
*Source.* Pach & Sharir, "On the number of incidences between points and curves," *Combin. Probab. Comput.* 7 (1998), 121–127. The original direct argument. The same proof template the existing `SzemerediTrotter.lean` already implements for lines, instantiated at general `(M, k=2)`.

Reuses: `hCL` at parameter `M`, the existing `incidence_bound_of_crossingLemma`-style endgame (slightly re-instantiated for `M`), the existing `stMultigraph` segment-realization machinery (replacing "lines" with "Jordan-arc components of curves").

Needs as inputs: `hJordan` (the Milnor–Thom-derived component-count + 1-manifold-parametrization fact). Does NOT need `Bezout21Statement` — the curve-pair-intersection bound `|γ_a ∩ γ_b| ≤ M` is BUILT INTO `TwoDegreesOfFreedom`, so Bézout is upstream of `TwoDegreesOfFreedom` (verified by lemmas in `incidence-assembly`), not internal to Theorem 2.3.

Why over the alternatives: this is the canonical proof, parallels the ST(lines) proof we already have line-for-line, and produces a polynomial-in-`d, M` constant `C_{d, M}` consistent with the paper statement (the precise exponent of `M` in the constant depends on bookkeeping choices — Pach–Sharir's sharp `M^{1/3}` comes from a tighter cube-root; the version here uses `M²·K_d²` which is loose but matches `Theorem23Statement`'s "`∃ C, ...`" envelope). PROVEN classical.

**Route B (rejected): ST(lines) as a black box + rich/poor partition.**
Sharir & Zahl, "Cutting algebraic curves into pseudo-segments…" (2017), §3, and Solymosi–Tao, "An incidence theorem in higher dimensions" (2012). One takes ST(lines) on a *rich-curves* sub-family and a *poor-curves* sub-family separately, with a dyadic partition by incidence count. **Requires polynomial partitioning (Guth–Katz)** in the general curves case, which Mathlib v4.27.0 lacks entirely (no polynomial ham-sandwich, no real-algebraic cell decomposition). Rejected: introduces a much larger Mathlib gap than Route A.

**Route C (rejected): The Spencer–Szemerédi–Trotter purely-graph-theoretic argument.**
Counts point-curve-point triples (rich curves) using a Kővári–Sós–Turán bound on the bipartite incidence graph, then converts. The Kővári–Sós–Turán step is present in Mathlib (under `Combinatorics/Extremal/`) but the conversion to point-curve incidences is not, and the standard form of the argument gives a weaker exponent than `2/3` for general `k = 2`. Rejected on exponent grounds.

**Route D (rejected): Argument via cell decomposition + uniform bound per cell.**
Pach & Agarwal exposition, ch. 4. Decompose `ℝ²` into cells, each containing `O(1)` curves and `O(m/r²)` points for parameter `r`, then bound incidences per cell and sum. Needs cuttings/ε-nets/random sampling for curves — Mathlib has neither. Same blocker as Route B, rejected.

### Adopted strategy summary

**Route A**, with the proof factored into four phases:
1. **Combinatorial core, two-parameter `(M_mult, M_cr)`-parametrized.** Re-derive `incidence_bound_of_crossingLemma` with the multiplicity bound `M_mult` (the parameter `hCL` is called with) decoupled from the crossing bound `M_cr` (the bound on `crossings/n²`). The `M = 1` case in `SzemerediTrotter.lean` has both `= 1` and disappears into the constant `64`. PROVEN classical: same algebra as `M = 1`, with `64` becoming `64·M_mult·M_cr`. CONJECTURED-feasible-in-Lean: a straight generalization of the existing proof; no new Mathlib pieces required.
2. **Jordan-arc decomposition as a named input.** State `JordanArcDecompositionStatement`. PROVEN classical (Milnor–Thom Theorem 2.2 with `D = 2` plus the fact that a smooth real 1-manifold without boundary is locally parametrizable). NEEDS_RESEARCH whether to formally pull from `milnor-thom` here or to keep it as a clean named input — recommendation is the latter (`hJordan` enters as a `Prop` hypothesis, matching the Tier-B convention).
3. **Geometric realization for curve-arc-incident-points.** Generalize `stMultigraph` (currently: vertices = `P`, edges = consecutive points along each LINE) to `pcMultigraph` (vertices = `P`, edges = consecutive points along each JORDAN ARC of each curve). PROVEN classical (same argument as ST(lines), Pach–Sharir 1998 §2 essentially does this). CONJECTURED-feasible-in-Lean: largely structural — the existing `SzemerediTrotter.lean` does 1200+ lines of analogous work and the curve case is morally the same with `Path`-flavoured replacement for the line parametrization. Phase 3 outlines an explicit list of obstructions.
4. **Discharge `Theorem23Statement`.** Wire the conditional `pachSharir23_of_inputs hCL hJordan` to close `theorem23`. Includes the ambient-space bridge `Point2 ≃ ℝ × ℝ`.

The crossing-lemma threshold (after the overlap accounting in Phase 3) becomes `4·(2M)·m ≤ e` (multiplicity gets a factor of 2 from "≤2 arcs per point" overlap times the 2-DOF curve count). The crossing bound from 2-DOF + overlap is `crossings ≤ 4·M·|Γ|²` (factor 4 from the overlap pair). The cube root then gives `e³ ≤ 64·(2M)·(4M)·m²·n² = 512·M²·m²·n²`, so `e ≤ 8·M^{2/3}·m^{2/3}·n^{2/3}`. After `M^{2/3} ≤ M` (valid for `M ≥ 1`) and absorbing the `+K_d·|Γ|` slack from the edges-vs-incidences correction, the public constant is `C_{d,M} := 512·M²·K_d²` with `K_d := (2d)²`, i.e. `C_{d,M} = 512·M²·(2d)⁴`. So the constant depends on `d` and `M` exactly as the paper requires.

### Why the paper's "M^{1/3}" is hidden inside C_{d,M}

Pach–de Zeeuw's Theorem 2.3 (as encoded in `Theorem23Statement`) is `≤ C_{d,M} · max(...)` — the constant absorbs the `M`-dependence. The Pach–Sharir paper's bound writes `M^{1/3}` explicitly; in the Pach–de Zeeuw formulation we lose nothing by inlining the M-dependence into `C_{d,M}`. (We get `M²` rather than `M^{1/3}` only because we are absorbing several constant factors to keep the cube-root identity arithmetic clean; the sharp `M^{1/3}` form is recoverable by tighter bookkeeping but unnecessary for downstream consumers.) This matches `Theorem23.lean` faithfully (`∃ C, 0 < C ∧ ...`).

### Tier-B alignment

`hJordan` is consumed as a `Prop` hypothesis (named axiom in spirit). When `milnor-thom` later supplies a proof term, the discharger in `Theorem23.lean` simply takes the proven term and feeds it; until then the discharger leaves `theorem23` at `sorry` with the obstruction localized to "no proof of `hJordan` yet". This is the same shape as the existing `pachDeZeeuwTheorem11_unconditional` carrying Gap A internally, but at one level down.

---

## File Structure

- `pach-sharir/PachSharir/PachSharirCurves.lean` — **new.** All curves-generalization content. ~700–1000 lines projected, mirroring `SzemerediTrotter.lean`. If it grows past ~700 lines, split into `PachSharirCurves/Multigraph.lean` + `PachSharirCurves/Bridge.lean`.
- `pach-sharir/PachSharir/Theorem23.lean` — **modify.** Replace `theorem23 := sorry` with a discharger term `:= pachSharir23_of_theorem23Inputs hCL hJordan` (or leave `sorry` with a labelled obstruction if either hypothesis is still unavailable at the calling site — see Task 9 for which). The `Prop` signature of `theorem23` is unchanged.
- `pach-sharir/PachSharir.lean` — **modify.** Add `import PachSharir.PachSharirCurves` after the existing imports.

No other files change.

---

## Phase 1 — `(M_mult, M_cr)`-parametrized combinatorial endgame

This phase generalizes `incidence_bound_of_crossingLemma` (currently in `SzemerediTrotter.lean`, hardcoded at `M_mult = M_cr = 1`) to a curves-friendly statement parametrized by two independent multiplicities. It uses NO geometry. PROVEN classical.

### Task 1: New module scaffold + the `(M_mult, M_cr)`-parametrized endgame statement

**Files:**
- Create: `pach-sharir/PachSharir/PachSharirCurves.lean`
- Modify: `pach-sharir/PachSharir.lean` (add import)

- [ ] **Step 1: Write the file header, imports, namespace, and the parametrized endgame signature.**

```lean
/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Mathlib
import CrossingLemma
import PachSharir.SzemerediTrotter
import PachSharir.Theorem23

/-!
# Pach–Sharir Theorem 2.3 from the multigraph crossing lemma

Generalization of `PachSharir.ST.szemerediTrotter_of_crossingLemma` from
straight lines at multiplicity `M = 1` to plane algebraic curves of degree `≤ d`
at multiplicity `M`. Same hypothesis surface (`hCL`) plus one named
algebraic-geometry input (`hJordan` — the Jordan-arc decomposition of plane
algebraic curves, classically supplied by Milnor–Thom Theorem 2.2).

Roadmap: Phase 1 — `M`-parametrized combinatorial endgame; Phase 2 — Jordan-arc
decomposition input; Phase 3 — geometric realization for curve arcs; Phase 4 —
discharger that closes `PachSharir.theorem23`.
-/

set_option linter.style.longLine false

namespace PachSharir.PC

open scoped Classical
open CrossingLemma.PDZ
open PachSharir
```

Then the M-parametrized endgame statement:

```lean
/-- The `(M_mult, M_cr)`-parametrized combinatorial endgame. Compare
`PachSharir.ST.incidence_bound_of_crossingLemma`, which is the
`M_mult = M_cr = 1` specialization. From the crossing lemma `hCL` at
multiplicity `M_mult` and the bookkeeping of a drawn multigraph `G`,
derive a Pach–Sharir-shaped incidence bound. The two parameters are kept
separate because the curve setting consumes `M_mult = 2·M`, `M_cr = 4·M`
where `M` is the 2-DOF multiplicity — coupling them as a single `M`
would force an unnecessary constant blowup. -/
lemma incidence_bound_of_crossingLemma_M
    (hCL : CrossingLemmaMultigraphStatement)
    (M_mult M_cr I m n : ℕ)
    (hM_mult : 1 ≤ M_mult) (hM_cr : 1 ≤ M_cr)
    (G : DrawnMultigraph)
    (hv : G.V.card = m)
    (hmult : ∀ p q, G.multiplicity p q ≤ M_mult)
    (hwd : G.WellDrawn)
    (he : I ≤ G.numEdges + n)
    (hcr : G.crossings ≤ M_cr * n ^ 2) :
    (I : ℝ) ≤
      (64 * (M_mult : ℝ) * (M_cr : ℝ))
        * ((m : ℝ) ^ ((2 : ℝ) / 3) * (n : ℝ) ^ ((2 : ℝ) / 3) + m + n) := by
  sorry
```

The constant `64·M_mult·M_cr` is provisional; the exact arithmetic is: `hCL`
at `M_mult` gives `e³ ≤ 64·M_mult·m²·crossings ≤ 64·M_mult·M_cr·m²·n²`, so
`e ≤ (64·M_mult·M_cr)^{1/3} · m^{2/3} · n^{2/3} = 4·(M_mult·M_cr)^{1/3}·m^{2/3}·n^{2/3}`.
For `M_mult, M_cr ≥ 1` we have `(M_mult·M_cr)^{1/3} ≤ M_mult·M_cr`, and the `+m+n`
slack from `I ≤ e + n` and the low-edge case absorbs into the `64·M_mult·M_cr`
constant comfortably. (For `M_mult = M_cr = 1` this recovers the existing ST
constant `64`.)

- [ ] **Step 2: Add the import to the module root.** In `pach-sharir/PachSharir.lean`, add `import PachSharir.PachSharirCurves` after the existing two imports.

- [ ] **Step 3: Build (statement-only).**
Run: `cd pach-sharir && ./lake-build.sh`
Expected: green; one `sorry` in `PachSharirCurves.lean`.

- [ ] **Step 4: Commit.** "pach-sharir: scaffold PachSharirCurves with M-parametrized endgame statement".

### Task 2: Prove the `(M_mult, M_cr)`-parametrized endgame

This is the substantive proof of Task 1's statement. It is a *direct generalization* of `PachSharir.ST.incidence_bound_of_crossingLemma`, which is already PROVEN sorry-free in `SzemerediTrotter.lean` lines 154–223. The differences from the `M = 1` case:

1. `hCL G M_mult (by exact_mod_cast hM_mult) hmult hwd hthresh` instead of `hCL G 1 (by norm_num) ...`.
2. The crossing bound is `crossings ≤ M_cr·n²`, so the cube becomes `e³ ≤ 64·M_mult·m²·crossings ≤ 64·M_mult·M_cr·m²·n²`.
3. Cube root: `e ≤ (64·M_mult·M_cr·m²·n²)^{1/3} = 4·(M_mult·M_cr)^{1/3}·m^{2/3}·n^{2/3}`. Then bounding by `64·M_mult·M_cr·(m^{2/3}n^{2/3} + m + n)` uses `(M_mult·M_cr)^{1/3} ≤ M_mult·M_cr` (true for `M_mult, M_cr ≥ 1`, where the rhs is a nonneg integer ≥ 1).

**Files:**
- Modify: `pach-sharir/PachSharir/PachSharirCurves.lean`

- [ ] **Step 1: Prove `incidence_bound_of_crossingLemma_M`.**
Strategy: copy the existing proof body from `SzemerediTrotter.lean` lines 164–223 and adjust:
  - `hthr : 4 * 1 * G.V.card ≤ G.numEdges` becomes `hthr : 4 * M_mult * G.V.card ≤ G.numEdges`.
  - `hcl := hCL G M_mult hM_mult hmult hwd hthr` (note `hM_mult : 1 ≤ M_mult` rather than `0 < M_mult`; convert with `Nat.one_le_iff_ne_zero` / `Nat.pos_of_ne_zero` if needed — EXPECTED present).
  - `e³ ≤ 64 * M_mult * m² * crossings ≤ 64 * M_mult * m² * (M_cr * n²) = 64 * M_mult * M_cr * m² * n²`.
  - Set `B := 4 * (M_mult·M_cr)^{1/3} * m^{2/3} * n^{2/3}` so `B³ = 64 * M_mult * M_cr * m² * n²`. API: same `Real.rpow_natCast`, `Real.rpow_mul` used in the M=1 case.
  - Final `nlinarith`: `(I : ℝ) ≤ B + n` and `B ≤ M_mult·M_cr·(...)` since `(M_mult·M_cr)^{1/3} ≤ M_mult·M_cr` for `M_mult·M_cr ≥ 1`. EXPECTED present: `Real.rpow_le_self_of_one_le` (the precise name may differ; if it doesn't, fall back to `Real.rpow_le_rpow_left` at exponent `2/3 ≤ 1` plus arithmetic — see also the very similar derivation already in `SzemerediTrotter.lean` for the `64^{1/3} = 4` step).
  - **Low-edge case** `G.numEdges < 4 * M_mult * m`: `I ≤ G.numEdges + n < 4·M_mult·m + n`. We need this `≤ 64·M_mult·M_cr·(m + n)`, which holds: `4·M_mult·m + n ≤ 64·M_mult·M_cr·m + 64·M_mult·M_cr·n` (since `4 ≤ 64·M_mult·M_cr` for `M_mult, M_cr ≥ 1` — i.e. `M_cr ≥ 1` is also needed; add this as a hypothesis to the lemma if Task 1's signature only has `1 ≤ M_mult`).

**Amendment to Task 1's signature.** Adding `hM_cr : 1 ≤ M_cr` is harmless (the curve case will supply `M_cr = 4·M ≥ 4`) and necessary for the low-edge bound. Update Task 1's signature accordingly during the proof.

- [ ] **Step 2: Build, confirm 0 `sorry` in `incidence_bound_of_crossingLemma_M`.**
Run: `cd pach-sharir && ./lake-build.sh && grep -c sorry PachSharir/PachSharirCurves.lean`
Expected: 0 (only this lemma so far; later phases will add new statements with their own residuals).

- [ ] **Step 3: Commit.** "pach-sharir/PC: prove M-parametrized combinatorial endgame (generalizes ST)".

---

## Phase 2 — Jordan-arc decomposition as a named input

This phase names the algebraic-geometry hook that lets us treat each curve as a finite union of Jordan arcs (which is what the geometric realization in Phase 3 needs in order to define "consecutive points along the curve"). PROVEN classical (Milnor–Thom plus 1-manifold parametrization); CONJECTURED-feasible-in-Lean (`milnor-thom` already has `MilnorThom22Statement` at the Prop level, but its discharger is parked under Tier-B — see `milnor-thom/PLAN.md`).

### Task 3: Define `JordanArc` and `JordanArcCover`

**Files:**
- Modify: `pach-sharir/PachSharir/PachSharirCurves.lean`

- [ ] **Step 1: Define the Jordan-arc vocabulary.**

```lean
/-- A *Jordan arc* in `ℝ²`: the image of a continuous injective map `[0,1] → ℝ²`.
A point `p` is *on* the arc if it lies in this image. -/
structure JordanArc where
  param : Set.Icc (0 : ℝ) 1 → ℝ × ℝ
  cont  : Continuous param
  inj   : Function.Injective param

namespace JordanArc

/-- The point set traced by a Jordan arc. -/
def carrier (J : JordanArc) : Set (ℝ × ℝ) := Set.range J.param

end JordanArc

/-- A *Jordan-arc cover* of `γ ⊆ ℝ²`: a finite list of Jordan arcs whose union
equals `γ`. The list is what carries the cardinality bound; the order matters
only insofar as it indexes the arcs. -/
structure JordanArcCover (γ : Set (ℝ × ℝ)) where
  arcs    : List JordanArc
  cover   : (γ : Set (ℝ × ℝ)) = ⋃ J ∈ arcs, J.carrier
```

(The `cover` field uses `⋃ J ∈ arcs, J.carrier` over a `List` membership; the discharger via `List.toFinset.bind` is routine. If `Set.iUnion` over `List`-membership is awkward in Mathlib v4.27.0, switch to `arcs.foldr (·.carrier ∪ ·) ∅`; both formulations are equivalent and Mathlib supports the `iUnion`-over-list pattern as `Set.iUnion_finset` family.)

- [ ] **Step 2: Build, commit.**
Run: `cd pach-sharir && ./lake-build.sh`
Expected: green, no new `sorry`. Commit: "pach-sharir/PC: JordanArc and JordanArcCover vocabulary".

### Task 4: State the `hJordan` input

**Files:**
- Modify: `pach-sharir/PachSharir/PachSharirCurves.lean`

- [ ] **Step 1: Bridge `Point2 = EuclideanSpace ℝ (Fin 2)` ↔ `ℝ × ℝ`.**

Theorem 2.3's `IsPlaneAlgebraicCurveOfDegreeLE` lives in `EuclideanSpace ℝ (Fin 2)`; our `JordanArc` lives in `ℝ × ℝ`. Define a canonical equivalence and use it to push curves into `ℝ × ℝ`.

```lean
/-- Canonical equiv `EuclideanSpace ℝ (Fin 2) ≃ ℝ × ℝ`. -/
noncomputable def point2Equiv : EuclideanSpace ℝ (Fin 2) ≃ ℝ × ℝ where
  toFun x := (x 0, x 1)
  invFun p := !₂[p.1, p.2]
  left_inv := by sorry
  right_inv := by sorry

/-- The `ℝ × ℝ` shadow of a plane curve. -/
def curveImage (γ : Set (EuclideanSpace ℝ (Fin 2))) : Set (ℝ × ℝ) :=
  point2Equiv '' γ
```

(`!₂[a, b]` is Mathlib notation for `EuclideanSpace ℝ (Fin 2)` literal. EXPECTED present — used in `curve-symmetries`.)

Strategy:
- `left_inv`: `funext i; fin_cases i; simp [point2Equiv, EuclideanSpace.equiv]` — pull the two component-equalities out.
- `right_inv`: `Prod.ext (by simp) (by simp)`.

- [ ] **Step 2: State `JordanArcDecompositionStatement`.**

```lean
/-- **Jordan-arc decomposition input.** Classically: every plane algebraic
curve of degree `≤ d` decomposes into a Jordan-arc cover of at most `(2d)²`
arcs, with each point of the curve lying in at most `2` arcs (boundary
shared-endpoints only, classical 1-manifold structure).

The arc-count bound `(2d)²` is the content of Milnor–Thom Theorem 2.2 for
`D = 2`; the "each point lies in ≤ 2 arcs" clause is the additional 1-manifold
parametrization fact (a connected component of the smooth locus of a
real-algebraic curve is homeomorphic to an interval or circle; circles split
into 2 arcs sharing endpoints, intervals are 1 arc).

This statement is the SINGLE algebraic-geometry input that Pach–Sharir
Theorem 2.3 itself consumes; it is supplied here as a typed `Prop` so the
discharging proof can live in `milnor-thom` (or be axiomatized under the
project's Tier-B convention) without entangling this file. -/
def JordanArcDecompositionStatement : Prop :=
  ∀ (d : ℕ) (γ : Set (EuclideanSpace ℝ (Fin 2))),
    IsPlaneAlgebraicCurveOfDegreeLE d γ →
      ∃ cov : JordanArcCover (curveImage γ),
        cov.arcs.length ≤ (2 * d) ^ 2 ∧
        ∀ p : ℝ × ℝ,
          {i : Fin cov.arcs.length | p ∈ (cov.arcs.get i).carrier}.ncard ≤ 2
```

The overlap clause uses `Set.ncard` over a `Set (Fin cov.arcs.length)` to avoid `DecidablePred (p ∈ J.carrier)`, since membership in a real-curve subset is not generally decidable. `Set.ncard` works without decidability under `Classical.choice` (already in the project's axiom surface). An equivalent formulation with `Finset.card` would require `Classical.dec` to convert to a `Finset`.

- [ ] **Step 3: Add brief commentary linking `hJordan` to `MilnorThom22Statement`.** As block-comment in the file just after the def: cite the classical reference (Milnor 1964; OPMT exposition in Basu–Pollack–Roy ch. 7), note that `MilnorThom22Statement` bounds *connected components* by `(2d)²` (for `D = 2`), while `JordanArcDecompositionStatement` further requires:
  - each component to be Jordan-arc parametrizable (interval ⟹ 1 arc; circle ⟹ 2 arcs sharing endpoints; classical 1-manifold structure of real-algebraic curves),
  - each point lying in ≤ 2 arcs (the boundary-overlap clause).

The arc count is then at most `2 · #components ≤ 2 · (2d)²`. The statement uses the simpler bound `(2d)²` and absorbs the factor 2 into the constant `C_{d,M}` via the Phase 3 accounting. **NOTE on the bound choice**: if the true upper bound is `2·(2d)²` rather than `(2d)²`, simply replace `(2 * d) ^ 2` with `2 * (2 * d) ^ 2` in the statement and propagate the factor of 2 through Phase 3 — the only effect is doubling `K_d` and hence `K_d²` in the constant. {{NEEDS_VALIDATION}}: confirm the exact bound from Milnor 1964 / Basu–Pollack–Roy before fixing the statement; cosmetic only, no obstruction.

- [ ] **Step 4: Build, commit.**
Expected: green; the two `sorry`s on `left_inv`/`right_inv` will be discharged in Task 5, so leave them in the bridge-build commit but **labelled** `-- OBSTRUCTION: routine; discharged in Task 5`. Commit: "pach-sharir/PC: JordanArcDecompositionStatement input and Point2 ↔ ℝ×ℝ bridge".

### Task 5: Discharge the `point2Equiv` bridge

**Files:**
- Modify: `pach-sharir/PachSharir/PachSharirCurves.lean`

- [ ] **Step 1: Prove `point2Equiv.left_inv` and `.right_inv`.**

Strategy: `EuclideanSpace ℝ (Fin 2)` is a `PiLp 2 (fun _ => ℝ)` and definitionally a function `Fin 2 → ℝ`. The two coordinates of a `Fin 2 → ℝ` are `· 0` and `· 1`. After `funext i; fin_cases i`, both branches reduce to `rfl` (after a `simp [!₂_cons, !₂_zero]` if the literal notation is opaque). EXPECTED present: `!₂` notation cases — `Matrix.cons_val_zero`, `Matrix.cons_val_one`, `Matrix.head_cons`, `Matrix.head_fin_const`.

NEEDS_RESEARCH only if `EuclideanSpace.equiv` (the canonical PiLp equiv) interacts badly with `!₂` — the predecessor plan flagged this exact bridge as out-of-scope (`docs/superpowers/plans/2026-05-27-szemeredi-trotter-from-crossing-lemma.md` Scope section), so this is the first time the project actually crosses the boundary. If it gets tricky, fall back to `equiv := (EuclideanSpace.equiv (Fin 2) ℝ).trans (finTwoArrowEquiv ℝ)` or to constructing the equiv via `Prod.ext` on coordinates rather than via the literal.

- [ ] **Step 2: Build, confirm two more `sorry`s closed.**
Run: `cd pach-sharir && ./lake-build.sh && grep -c sorry PachSharir/PachSharirCurves.lean`
Expected: count drops by exactly 2 (the two `sorry`s discharged in this task).

- [ ] **Step 3: Commit.** "pach-sharir/PC: discharge Point2 ↔ ℝ×ℝ equiv".

---

## Phase 3 — Geometric realization for curve arcs

The substantive geometric content: turn `P, Γ, hJordan-output` into an actual plane-drawn multigraph whose vertices are the points and whose edges are consecutive points along each Jordan arc of each curve. This phase mirrors Phase 2 of the predecessor plan (the `stMultigraph` construction for lines) at a more general level. **It may surface its own residuals** — any residual MUST be a labelled `sorry`, never silent.

### Task 6: Per-arc ordering and consecutive-pair edges

**Files:**
- Modify: `pach-sharir/PachSharir/PachSharirCurves.lean`

- [ ] **Step 1: Define the per-Jordan-arc point ordering.**

```lean
/-- The points of `P` lying on a Jordan arc `J`, ordered along `J` by the
inverse parameter. -/
noncomputable def pointsOnArc (P : Finset (ℝ × ℝ)) (J : JordanArc) :
    List (ℝ × ℝ) := sorry

/-- Consecutive pairs along `J`: `k` incident points give `k-1` segment edges
between consecutive points. -/
noncomputable def edgesOnArc (P : Finset (ℝ × ℝ)) (J : JordanArc) :
    List ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (pointsOnArc P J).zip (pointsOnArc P J).tail
```

- [ ] **Step 2: Implement `pointsOnArc`.**

Strategy: take `P.filter (· ∈ J.carrier)`, lift each `p` to its preimage `J.param⁻¹ p ∈ [0, 1]` via injectivity (Mathlib: `Function.invFun` on `J.param` or `Function.Embedding.invOfInjective`; or, since the codomain is a metric space, sort by the canonical `Function.invFunOn`), and sort by that real key. Mathlib lemmas: `Function.Injective.invFun_eq`, `List.mergeSort`. **Key non-trivial step**: lifting `P.filter` to a `List` and using `Function.invFun` gives a value `t` such that `J.param t = p`; uniqueness via injectivity. The sort key `t : ℝ` is then a linear order.

NEEDS_RESEARCH whether Mathlib's `Function.invFun` is enough here or whether we need `Set.injOn_inv_of_injective` (which lives in `Logic/Function/Basic`). If `Function.invFun` is `Classical.choice`-laden, fine — we accept `Classical` axioms (already in the surface).

- [ ] **Step 3: State and prove the analogue of `lineKey_injOn`.**

```lean
/-- The "position along the arc" map is injective on the points of `P` lying on
`J`. (Direct from `J.inj`.) -/
lemma arcKey_injOn (P : Finset (ℝ × ℝ)) (J : JordanArc) :
    Set.InjOn (Function.invFunOn J.param Set.univ) (P.filter (· ∈ J.carrier)) := by
  sorry
```

Strategy: `Function.invFunOn` of an injective function is left-inverse on its range; restrict to `P.filter (· ∈ J.carrier)` whose elements all lie in `Set.range J.param = J.carrier`. EXPECTED present: `Function.invFunOn_eq`, `Function.injOn_iff_invFunOn_left`.

- [ ] **Step 4: Prove the basic `pointsOnArc` lemmas.**

The same set the existing `SzemerediTrotter.lean` proves for `pointsOnLine`:
- `mem_pointsOnArc`: `p ∈ pointsOnArc P J ↔ p ∈ P ∧ p ∈ J.carrier`.
- `pointsOnArc_nodup`: nodup (since `sort` is on injective keys).
- `length_pointsOnArc`: `(pointsOnArc P J).length = (P.filter (· ∈ J.carrier)).card`.
- `length_edgesOnArc`: `(edgesOnArc P J).length = max((pointsOnArc P J).length - 1, 0)`, ergo `≥ (pointsOnArc P J).length - 1`. (Match the bookkeeping in `SzemerediTrotter.lean` line 354.)

All four are routine `List`/`Finset` facts; the corresponding ST proofs in `SzemerediTrotter.lean` lines 287–371 are templates.

- [ ] **Step 5: Build, commit.**
Mark any open `sorry` with `-- OBSTRUCTION: pointsOnArc-ordering`. Commit: "pach-sharir/PC: per-Jordan-arc point ordering and edge list".

### Task 7: Assemble the curve multigraph `pcMultigraph`

**Files:**
- Modify: `pach-sharir/PachSharir/PachSharirCurves.lean`

- [ ] **Step 1: Define the per-arc segment realization.**

For each consecutive pair `(p, q)` on a Jordan arc `J`, the segment-arc in the planar `DrawnMultigraph` sense is the restriction of `J.param` to `[J.param⁻¹ p, J.param⁻¹ q]`. This is the **substantive change from ST**: in ST, the edge from `p` to `q` is the straight segment; here, it is the **sub-arc of `J`** from `p` to `q`. Define:

```lean
/-- The sub-arc of `J` between the consecutive points `p, q ∈ J.carrier`. -/
noncomputable def subArc (J : JordanArc) (p q : ℝ × ℝ)
    (hp : p ∈ J.carrier) (hq : q ∈ J.carrier) (hne : p ≠ q) :
    SimpleCurveArc := by
  sorry
```

Strategy: lift `p, q` to `tp, tq ∈ [0,1]` via `J.inj`; WLOG `tp < tq` (else swap); the sub-arc is `J.param ∘ affineReparam : [0,1] → ℝ × ℝ` where `affineReparam s = (1 - s) tp + s tq`. The `Continuous` field is `J.cont.comp (affine continuity)`; `inj` uses `J.inj` composed with affine injectivity on the embedded interval.

**Concrete obstruction.** `SimpleCurveArc` (defined in `crossing-lemma`) has fields `param`, `cont`, `inj` — see `SzemerediTrotter.lean` line 373 for the `segmentArc` template. The sub-arc construction is identical in shape but uses `J.param ∘ ...` instead of a straight `(1 - t) • p + t • q`. The injectivity proof is where the curves case diverges from lines: we use `J.inj` on the embedded `[tp, tq]` interval (composition of injectives).

NEEDS_RESEARCH whether `SimpleCurveArc` requires `param : Set.Icc 0 1 → ℝ × ℝ` exactly or accepts a more general parametrization — answered by reading `crossing-lemma/CrossingLemma/CrossingLemma.lean` definitions (the surface that `SzemerediTrotter.lean` already uses).

- [ ] **Step 2: Define the global `pcMultigraph`.**

```lean
/-- The drawn multigraph for points + curves + Jordan-arc decompositions.
Vertices = `P`, edges = consecutive segments along each Jordan arc of each
curve. The `crossings` field is set to the structure's own `crossingCount`
(so `WellDrawn` is `le_refl`, per the soundness fix carried by ST).
The `decomp` argument carries a Jordan-arc cover for each curve. Phase 4's
top-level discharger extracts `decomp` from `hJordan` together with the
overlap and length bounds that Tasks 8 Steps 5–6 consume. -/
noncomputable def pcMultigraph
    (P : Finset (ℝ × ℝ)) (Γ : Finset (Set (ℝ × ℝ)))
    (decomp : ∀ γ ∈ Γ, JordanArcCover γ) :
    DrawnMultigraph := sorry
```

Strategy:
- Vertices: `V := P`.
- Edge list: concatenation over `γ ∈ Γ` and `J ∈ (decomp γ).arcs` of `edgesOnArc P J`.
- Each edge's arc: `subArc J p q hp hq hne` (we know `p, q ∈ J.carrier` from `mem_pointsOnArc`; consecutive-distinct from `edgesOnArc_distinct`).
- `endpoints`/`endpoints_mem`: indexed lookup; `endpoints_mem` from `mem_pointsOnArc ⊆ P`.
- `crossings := this.crossingCount`: as the predecessor plan resolved (`SzemerediTrotter.lean` line 28's soundness fix), compute the crossing count over the same edge list and set `crossings` equal to it. `WellDrawn` is then `le_refl _`.

- [ ] **Step 3: Build (expect labelled `sorry`s), commit.**

Mark every remaining `sorry` with an `OBSTRUCTION: ...` comment naming what is open. Commit: "pach-sharir/PC: assemble pcMultigraph (geometric obligations labelled)".

### Task 8: Discharge the five Phase-1 hypotheses for `pcMultigraph`

This mirrors Task 6 of the predecessor plan, but for curve arcs. PROVEN classical; CONJECTURED-feasible-in-Lean by analogy with ST. Each lemma has a direct ST counterpart whose proof structure ports.

**Files:**
- Modify: `pach-sharir/PachSharir/PachSharirCurves.lean`

- [ ] **Step 1: State the five bridge lemmas.**

```lean
variable (P : Finset (ℝ × ℝ)) (Γ : Finset (Set (ℝ × ℝ)))
  (decomp : ∀ γ ∈ Γ, JordanArcCover γ)

/-- The arc-overlap bound: for each curve, every point lies in ≤ 2 of its
Jordan arcs. The `hJordan` hypothesis supplies this clause to the top-level
discharger, which threads it through to Tasks 8 Steps 5–6. -/
def DecompOverlapLe2 : Prop :=
  ∀ (γ : Set (ℝ × ℝ)) (hγ : γ ∈ Γ) (p : ℝ × ℝ),
    {i : Fin (decomp γ hγ).arcs.length | p ∈ ((decomp γ hγ).arcs.get i).carrier}.ncard ≤ 2

/-- The arc-count bound: each curve's Jordan-arc cover has ≤ `Kd` arcs. -/
def DecompArcCountLe (Kd : ℕ) : Prop :=
  ∀ (γ : Set (ℝ × ℝ)) (hγ : γ ∈ Γ),
    (decomp γ hγ).arcs.length ≤ Kd

lemma pcMultigraph_card_V :
    (pcMultigraph P Γ decomp).V.card = P.card := by sorry

lemma pcMultigraph_wellDrawn :
    (pcMultigraph P Γ decomp).WellDrawn := by sorry
    -- `le_refl _` after unfolding WellDrawn/pcMultigraph (crossings := crossingCount).

/-- Multiplicity ≤ 2·M: edges between `p ≠ q` come from arcs of curves through
both; by 2-DOF at most `M` curves pass through `{p, q}`, and on each curve the
pair `{p, q}` lies in at most 2 arcs simultaneously (overlap clause), with each
arc contributing at most 1 consecutive edge between `p, q`. So multiplicity is
`≤ 2·M`. -/
lemma pcMultigraph_multiplicity_le_2M
    (M : ℕ)
    (h2DoF : TwoDegreesOfFreedom_RR P Γ M)
    (hOverlap : DecompOverlapLe2 P Γ decomp) :
    ∀ p q, (pcMultigraph P Γ decomp).multiplicity p q ≤ 2 * M := by sorry

/-- Edge count vs incidences: per arc with `k_J` incident points, contributes
`max(k_J - 1, 0)` edges; summing over arcs and curves gives
`numEdges + (#arcs) ≥ Σ_arcs k_arc ≥ incidences`, hence
`incidences ≤ numEdges + #arcs ≤ numEdges + Kd·|Γ|`. Does NOT need the
overlap clause (only the `≥` direction of the Σ-arcs vs incidences bound). -/
lemma incidences_le_numEdges_add_M
    (Kd : ℕ) (hCount : DecompArcCountLe P Γ decomp Kd) :
    incidences_RR P Γ ≤ (pcMultigraph P Γ decomp).numEdges + Kd * Γ.card := by sorry

/-- Crossings ≤ 4·M·|Γ|²: each crossing is two arc-interiors of distinct
curves meeting at a point; by 2-DOF, any pair of distinct curves has ≤ M
intersection points; each such point lies on at most 2 arcs per curve
(overlap clause), so accounts for at most `2·2 = 4` arc-pair crossings;
summing over ordered curve pairs gives `4·M·|Γ|²`. Arcs from the same curve
don't interior-cross (consecutive sub-arcs of an injective Jordan
parametrization). -/
lemma pcMultigraph_crossings_le_M
    (M : ℕ)
    (h2DoF : TwoDegreesOfFreedom_RR P Γ M)
    (hOverlap : DecompOverlapLe2 P Γ decomp) :
    (pcMultigraph P Γ decomp).crossings ≤ 4 * M * Γ.card ^ 2 := by sorry
```

(`TwoDegreesOfFreedom_RR` and `incidences_RR` are `ℝ × ℝ`-shadow versions of the `Theorem23.lean` definitions, obtained by pushing through `point2Equiv`; defined as helpers earlier in the file.)

- [ ] **Step 2: Prove `pcMultigraph_card_V`** — definitional. `simp [pcMultigraph]`. ST template: `stMultigraph_card_V` (one-liner).

- [ ] **Step 3: Prove `pcMultigraph_wellDrawn`** — `le_refl _` after unfolding. ST template: identical.

- [ ] **Step 4: Prove `incidences_le_numEdges_add_M`.**
Strategy: per Jordan arc `J ⊆ γ`, the number of incident points `k_J = (P.filter (· ∈ J.carrier)).card` satisfies `(edgesOnArc P J).length ≥ k_J - 1` (with the convention `0 - 1 = 0`; the inequality holds vacuously when `k_J = 0`). Summing over arcs and curves: `numEdges ≥ Σ_{γ, J} max(k_J - 1, 0)`. Since `cover` gives `γ = ⋃ J, J.carrier`, each incidence `(p, γ) ∈ I` has `p ∈ γ` ⟹ `p ∈ J.carrier` for at least one `J ∈ decomp γ`, so `Σ_{J ∈ decomp γ} k_J ≥ |{p ∈ P : p ∈ γ}|` = the incidence-count restricted to `γ`. Summing: `Σ_{γ,J} k_J ≥ incidences P Γ`. Combining: `numEdges + |{(γ,J) : k_J ≥ 1}| ≥ Σ_{γ,J} k_J ≥ incidences`, where `|{(γ,J)}| ≤ K_d · |Γ|`. So `incidences ≤ numEdges + K_d · |Γ|`. PROVEN classical, CONJECTURED-feasible-in-Lean.

**OBSTRUCTION (manageable).** Bookkeeping subtlety: in passing from `numEdges ≥ Σ_arcs (k_J - 1)_+` to `numEdges ≥ Σ_arcs k_J - K_d·|Γ|`, we use that each arc contributes a `−1` whether `k_J = 0` (vacuously) or `k_J ≥ 1` (one fewer edge than incident points). Lemma needed: `Σ_arcs k_J ≤ numEdges + #arcs`, where `#arcs ≤ K_d·|Γ|`. The `+#arcs` slack is the "edges-vs-incidences correction" and is the only place `K_d` enters the bound. NEEDS_RESEARCH: precise Mathlib `Finset.sum_le_sum` patterns for `Σ max(a, 0)` vs `Σ a` over `Finset.product`. EXPECTED present; the analogous step in `SzemerediTrotter.lean` `incidences_le_numEdges_add` already does this for lines.

**No overlap-clause is needed for this direction.** Because `Σ_arcs k_J ≥ incidences` holds for ANY cover (each incident point lies in `≥ 1` arc); only the OTHER direction `Σ_arcs k_J ≤ overlap·incidences` requires bounded overlap, and that direction is NOT used here. Phase 3 Step 5 (crossings) IS where the `≤ 2 arcs per point` overlap clause matters; the `hJordan` amendment in Task 4 is needed for THAT step, not this one.

NEEDS_RESEARCH: confirm Pach–Sharir 1998 §2 also uses the one-sided sum bound here; the published proof is brief and a quick check is warranted before Phase 3 commits to the overlap clause shape.

- [ ] **Step 5: Prove `pcMultigraph_crossings_le_M`.**
Strategy:
- Each interior crossing is an unordered pair of arc-indices `(i, j)` whose arc-interiors intersect at some point `x`.
- **Same-curve crossings** (the two arcs come from the same `γ`): the two arcs are sub-arcs of `γ`'s Jordan-arc cover. Two sub-arcs of `γ` (each itself a sub-arc of one Jordan arc `J ∈ decomp γ`) meet only on a measure-zero set; specifically:
  - If both sub-arcs come from the **same Jordan arc** `J`: they correspond to disjoint open intervals `(t_a, t_b), (t_c, t_d) ⊆ (0,1)` (since the sub-arc edges are between consecutive points of `pointsOnArc P J`, and `nodup` gives disjoint intervals). By `J.inj`, the images are interior-disjoint.
  - If they come from **different Jordan arcs** `J₁, J₂` of `γ`: they share at most boundary points (the overlap clause in `hJordan`), so interior-disjoint. **NEEDS_RESEARCH**: this assumes `hJordan` carries an "≤ 2 arcs per point, boundary-only overlap" clause as proposed in the Step 4 OBSTRUCTION resolution.
- **Distinct-curve crossings** (`γ_a ≠ γ_b`): each crossing point lies in `γ_a ∩ γ_b`, of size `≤ M` by `h2DoF.1`. Each such point lies on `≤ 2` arcs of `γ_a` AND `≤ 2` arcs of `γ_b` (overlap clause), so accounts for `≤ 4` arc-pair crossings. Summing over ordered curve pairs: `crossings ≤ 4·M·|Γ|²`.
- API: `Finset.card_le_card_of_injOn` injecting crossings into a product `(ordered-curve-pair) × (arc-pair-on-pair)` of cardinality `|Γ|² · 4`, then bounding the per-curve-pair fiber by `M·4`.

**Caveat on the same-curve interior-disjointness.** Mathlib has no off-the-shelf "two-injective-functions-on-disjoint-intervals have disjoint images." Strategy: prove a one-off `lemma sub_arc_interior_disjoint` in this file from `Function.Injective.image_of_disjoint` (or equivalent), using `J.inj`. If absent in Mathlib, the bare statement is: `J.inj → (s ∩ t = ∅) → (J.param '' s) ∩ (J.param '' t) ⊆ J.param '' (s ∩ t) = ∅`. Trivial composition of `Set.image_inter_subset` + `Function.Injective.image_eq_image`. EXPECTED present; flag NEEDS_RESEARCH only if `Set.InjOn`-flavoured variants are needed.

- [ ] **Step 6: Prove `pcMultigraph_multiplicity_le_2M`.**
Strategy: for `p ≠ q`:
- Each edge from `p` to `q` arises from a unique witness `(γ, J, i)` where `J ∈ decomp γ` and `(p, q)` are positions `i, i+1` on `pointsOnArc P J`.
- Inject the edge set `{e : edge of pcMultigraph | endpoints e = (p,q)}` into the product `(curves through both p, q) × (arc-of-curve containing both p, q) × (1, since pair appears at most once consecutively in any sorted nodup list)`. By 2-DOF clause (b), the first factor has size `≤ M`. By the overlap clause in `hJordan` applied at `p` AND at `q`, the second factor has size `≤ 2` per curve (a curve's Jordan-arc cover puts each point in `≤ 2` arcs; the pair `(p, q)` requires both in the same arc, which is the intersection of `arcs through p` and `arcs through q` — at most `min(2, 2) = 2`). The third factor is 1 by `pointsOnArc_nodup` + position uniqueness.
- So multiplicity `≤ M · 2 · 1 = 2·M`. PROVEN classical (Pach–Sharir 1998 §2 implicit, made explicit here by tracking the overlap factor).

For `p = q`: multiplicity is 0 (no degenerate edges, since `edgesOnArc` zips with `tail` and consecutive elements of a nodup list are distinct).

ST template: `stMultigraph_multiplicity_le_one` in `SzemerediTrotter.lean` lines 693–735 — the M=1, lines case. The curve case ports the same per-line uniqueness argument (sorted nodup + zip-with-tail ⟹ position unique) to per-arc uniqueness, then layers the 2-DOF curve-counting + overlap-factor on top.

**Note on constant accounting.** With the two-parameter Phase 1 endgame `incidence_bound_of_crossingLemma_M (M_mult, M_cr)`, the curve setting supplies `M_mult := 2·M` (from multiplicity here) and `M_cr := 4·M` (from `pcMultigraph_crossings_le_M`). Phase 1 gives `I ≤ 64·(2M)·(4M)·(m^{2/3}n^{2/3} + m + n) = 512·M²·(m^{2/3}n^{2/3} + m + n)`. With the `+K_d·|Γ|` slack from Step 4 (the edges-vs-incidences correction), the `n` term effectively becomes `K_d·|Γ| ≤ K_d·n`, absorbed by the constant `C := 512·M²·K_d² = 512·M²·(2d)⁴`. Task 9 Step 1's `C` matches.

- [ ] **Step 7: Build, audit `sorry` count.**
Run: `cd pach-sharir && ./lake-build.sh && grep -n sorry PachSharir/PachSharirCurves.lean`
Expected: any remaining `sorry`s are labelled `OBSTRUCTION:` with a one-line description.

- [ ] **Step 8: Commit.** "pach-sharir/PC: discharge the five hypotheses for pcMultigraph".

---

## Phase 4 — Discharge `Theorem23Statement`

### Task 9: Wire `pachSharir23_of_inputs` and close `theorem23`

**Files:**
- Modify: `pach-sharir/PachSharir/PachSharirCurves.lean`
- Modify: `pach-sharir/PachSharir/Theorem23.lean`

- [ ] **Step 1: State the assembled theorem in `PachSharirCurves.lean`.**

```lean
/-- **Pach–Sharir Theorem 2.3**, conditional on the multigraph crossing lemma
`hCL` and the Jordan-arc decomposition input `hJordan`. -/
theorem pachSharir23_of_inputs
    (hCL : CrossingLemmaMultigraphStatement)
    (hJordan : JordanArcDecompositionStatement) :
    Theorem23Statement := by
  intro d M
  -- Choose the constant: 512 · M² · K_d² with K_d := (2d)², so C = 512·M²·(2d)⁴.
  -- Phase 1 at (M_mult := 2M, M_cr := 4M) gives 64·(2M)·(4M) = 512·M² as the
  -- m^{2/3}n^{2/3}+m+n constant; K_d² absorbs the +K_d·|Γ| slack from Step 4.
  -- The constant depends ONLY on d and M, matching the paper's `C_{d,M}`.
  refine ⟨512 * ((M : ℝ) ^ 2) * ((2 * d) ^ 2 : ℝ) ^ 2, ?_, ?_⟩
  · positivity
  intro P Γ hΓ h2DoF
  -- Extract Jordan-arc decompositions for each curve via hJordan.
  -- Push P, Γ across point2Equiv into ℝ × ℝ.
  -- Build pcMultigraph; apply incidence_bound_of_crossingLemma_M at param 2M
  -- with crossings ≤ 4·M·|Γ|² and edges-vs-incidences I ≤ numEdges + K_d·|Γ|.
  sorry
```

Strategy: this is wiring — combine
- `hJordan` to extract, for each `γ ∈ Γ`, a `cov : JordanArcCover (curveImage γ)` together with `cov.arcs.length ≤ (2d)²` and the overlap clause (a single `Classical.choice` per curve, packed into a function `decomp` plus accompanying `DecompArcCountLe` and `DecompOverlapLe2` witnesses).
- `pcMultigraph_card_V`, `pcMultigraph_multiplicity_le_2M`, `pcMultigraph_wellDrawn`, `incidences_le_numEdges_add_M`, `pcMultigraph_crossings_le_M`.
- `incidence_bound_of_crossingLemma_M` at `(M_mult := 2M, M_cr := 4M)` with `m := P.card`, `n := Γ.card`.
- Final arithmetic: massage the resulting `64·2M·4M · (m^{2/3} n^{2/3} + m + n)` into `512·M²·K_d² · incidenceBoundTerm P Γ`. The `+K_d·|Γ|` slack from Step 4 is absorbed into the constant via `K_d² ≥ K_d` (since `K_d ≥ 1`); the `+` vs `max` shape needs `m + n ≤ 2·max(m, n) ≤ 2·incidenceBoundTerm`. Standard `nlinarith` after `Real.rpow_nonneg` standing facts.

- [ ] **Step 2: Prove it.**
Substantive but mechanical: the proof is a `have h := incidence_bound_of_crossingLemma_M hCL ...` plus `nlinarith` / `linarith` to absorb the constants and the `incidenceBoundTerm` shape. Each named lemma from Phase 3 fits one of `incidence_bound_of_crossingLemma_M`'s hypotheses.

- [ ] **Step 3: Use `pachSharir23_of_inputs` to discharge `theorem23` in `Theorem23.lean`.**

In `pach-sharir/PachSharir/Theorem23.lean`, replace
```lean
theorem theorem23 : Theorem23Statement := sorry
```
with
```lean
theorem theorem23 : Theorem23Statement := by
  -- Both inputs threaded by Tier-B axiomatization.
  -- TODO(Gap A residual): once milnor-thom supplies a term of
  -- JordanArcDecompositionStatement, replace the second axiom with the proven
  -- term. The crossing lemma hypothesis is the same one ST consumes.
  sorry  -- OBSTRUCTION: needs `hCL : CrossingLemmaMultigraphStatement` and
         -- `hJordan : JordanArcDecompositionStatement` as named axioms or
         -- terms; project policy (Tier-B) accepts them as `axiom` declarations
         -- elsewhere in the development.
```

**Important**: this `sorry` is intentional and required by the project's policy on the public surface (`theorem23 : Theorem23Statement` must remain hypothesis-free in signature; the discharger is allowed to be `sorry` while the named inputs are axiomatized at a higher level). The conditional theorem `PachSharir.PC.pachSharir23_of_inputs` is **fully proved** (no `sorry`); only the public, hypothesis-free packaging stays `sorry` until the upstream `axiom` declarations for `hCL` and `hJordan` are added (a separate, future task that lives in `incidence-assembly` or a new `Tier-B/Axioms.lean` module).

**Alternative**: if Adam decides to axiomatize `hCL` and `hJordan` inline as `axiom` declarations in `Theorem23.lean`, then the discharger becomes `:= pachSharir23_of_inputs hCL_axiom hJordan_axiom` and the file has zero `sorry`s. This decision is upstream of the plan — flag for Adam at the start of Phase 4 (during Task 9 Step 3).

- [ ] **Step 4: Build, axiom audit `pachSharir23_of_inputs`.**

Run:
```bash
cd pach-sharir && ./lake-build.sh
# In a scratch buffer or appended-then-reverted line:
# #print axioms PachSharir.PC.pachSharir23_of_inputs
```
Expected: `[propext, Classical.choice, Quot.sound]` for the conditional theorem (hypotheses thread `hCL` and `hJordan` at the type level, no `sorryAx`). If `sorryAx` appears, an OBSTRUCTION leaked from Phase 3 — match the leaked obligation against the file's `OBSTRUCTION:` comments; if no match, fail loudly.

- [ ] **Step 5: Final `sorry` audit on the full file.**

Run: `grep -n sorry pach-sharir/PachSharir/PachSharirCurves.lean pach-sharir/PachSharir/Theorem23.lean`
Expected:
- `PachSharirCurves.lean`: zero `sorry`s in best case, or each labelled with `OBSTRUCTION:` if any geometric residual remained.
- `Theorem23.lean`: exactly one `sorry` on `theorem23`, labelled with the policy note above; alternative path (inline `axiom`s) yields zero `sorry`s.

- [ ] **Step 6: Commit.** "pach-sharir: discharge Theorem 2.3 conditional on hCL + hJordan (Gap A residual: hJordan still needs upstream supply)".

---

## Dependency Map

| §2 input | Used in | Where it enters | Axiomatizable? |
|----------|---------|-----------------|----------------|
| `Bezout21Statement` | (none) | NOT consumed by Theorem 2.3 in this plan. Bézout enters one level up — in `incidence-assembly/Bridge.lean` it discharges the `TwoDegreesOfFreedom` hypothesis for the auxiliary curves `C_ij` (Lemma 3.3). Theorem 2.3 itself takes `TwoDegreesOfFreedom` as a hypothesis, so this plan never invokes Bézout. | N/A — not used. |
| `MilnorThom22Statement` | (none directly) | NOT consumed directly. Its content is folded into `hJordan` (Task 4): `MilnorThom22Statement D=2 d` bounds the number of *connected components* of a plane algebraic curve by `(2d)²`; `hJordan` requires the slightly stronger "each component decomposes into Jordan arcs", which is `MilnorThom22Statement` + a 1-manifold parametrization fact. The discharger of `hJordan` lives in `milnor-thom` (or in a Tier-B axiom block), NOT in this plan. | YES, robust. `hJordan` is named axiom-friendly. |
| `MilnorThom22FiniteStatement` | (none) | NOT consumed by Theorem 2.3 — this is the finite-set corollary used in `incidence-assembly` (Lemma 3.3 to get `|C_ij ∩ C_kl| ≤ 16·d⁴` for the `TwoDegreesOfFreedom` hypothesis). Not in this plan's scope. | N/A. |
| `Lemma25Statement` / `Lemma26Statement` (curve-symmetries) | (none) | NOT consumed by Theorem 2.3. These enter in `incidence-assembly` for Lemma 3.2 (symmetry branch). | N/A. |

**Summary**: this plan introduces exactly ONE named algebraic-geometry input (`hJordan`), which is content-equivalent to a strengthened `MilnorThom22Statement (D = 2)`. It does NOT consume any of the existing `bezout`/`milnor-thom`/`curve-symmetries` Statement Props directly. Robust to introducing `hJordan` as a named axiom — see Tier-B alignment in the Strategy section.

---

## Known Obstructions

Listed in approximate decreasing order of risk:

1. **`hJordan` strength — including the singular-locus subtlety.** The natural Milnor–Thom output gives a **connected-component bound on the curve**, not a Jordan-arc decomposition. Two further pieces are needed for `hJordan` to be true:
   (a) the smooth locus of an irreducible plane algebraic curve is a real 1-manifold (classical Jacobian-rank argument on partial derivatives),
   (b) the singular locus is finite (for a nonzero `f ∈ ℝ[x, y]`, the simultaneous zero set of `f, ∂_x f, ∂_y f` is finite — Bézout on the partial-system, ≤ `d(d-1)` points), so the Jordan-arc cover only needs to cover the smooth locus + a finite extra set.
   In the Jordan-arc formulation here, the singular points can be absorbed in one of two ways:
   - Pad the cover with trivial arcs (each singular point treated as a "degenerate arc"). Then `JordanArc` must allow degenerate cases; a way to do this without breaking `Function.Injective` is to add an optional "isolated point" mode to `JordanArc` (a sum type `JordanArc ⊕ Point2`).
   - Bound the singular contribution separately and **add** it to the right-hand side as a constant-times-|Γ| term, absorbed into `C_{d,M}`. This is what the classical Pach–Sharir argument does implicitly.
   This plan tacitly chooses the second route: state `hJordan` for the smooth locus only, and add a small constant penalty for singular incidences in the `incidences_le_numEdges_add_M` step (the constant `K_d` already covers it since `K_d = (2d)² ≥ d²` ≥ #singular). NEEDS_VALIDATION during Task 4 — the exact form of `hJordan` must say *what* it covers (whole curve or smooth locus) and *what* the residual is.

   Bottom line: `hJordan` is classical real-algebraic geometry (Milnor 1964 + a singular-locus finite-count via partial-derivative Bézout), NOT in Mathlib v4.27.0. **Two responses are honest:**
   - (a) State `hJordan` exactly as in Task 4 — Jordan-arc cover of `curveImage γ` (possibly excluding finitely many singular points), length `≤ (2d)²`, overlap ≤ 2. The discharging proof is Tier-B-axiomatizable.
   - (b) Restate Theorem 2.3 internally on "smooth real-1-manifold-parametrizable curves" (an abstraction that does NOT require degree-`d` algebraic structure) and then discharge `theorem23` separately by combining the abstract version with `hJordan`. This factoring is cleaner but adds a layer.
   This plan chooses (a). Reconsider if (b) emerges cleaner during Phase 2.

2. **Per-arc cover overlap clause.** The crossing bound (`pcMultigraph_crossings_le_M`, Task 8 Step 5) and the multiplicity bound (`pcMultigraph_multiplicity_le_2M`, Task 8 Step 6) BOTH use a "each point lies in ≤ 2 arcs of any single curve" clause on the Jordan-arc cover. This is true classically for Jordan-arc covers of real 1-manifolds (arcs meet only at endpoints, so each point is either interior to one arc or a shared endpoint of two). The incidences-vs-numEdges step (Task 8 Step 4) does NOT need this clause. **Action**: do Task 4 (state `hJordan`) first WITH the overlap clause built in; Phase 3 then consumes it cleanly. If `hJordan` is supplied without the clause and the project's Milnor–Thom discharger only gives the bare component count, the recovery is to add a small refinement step in Phase 2 (split any boundary-shared arc into two non-overlapping sub-arcs, with a constant blowup in `K_d`).

3. **`Point2 ≃ ℝ × ℝ` equiv.** Inevitable since `SzemerediTrotter` uses `ℝ × ℝ` and `Theorem23Statement` uses `EuclideanSpace ℝ (Fin 2)`. Task 5 isolates it; the `!₂[·, ·]` ↔ `(·,·)` bridge is purely mechanical but has known fiddliness in Mathlib's `PiLp` setup. NEEDS_RESEARCH if `EuclideanSpace.equiv (Fin 2) ℝ` plus `finTwoArrowEquiv` doesn't compose cleanly; fall-back is hand-rolled `Equiv` with explicit `Prod.ext`/`funext` per coordinate.

4. **Same-curve interior-disjointness of consecutive Jordan-sub-arcs.** The lines version (`SzemerediTrotter.lean` line 855 `edgesOnLine_interior_disjoint`) uses linear ordering of points along a line; the curves version needs "consecutive sub-arcs of an injective Jordan parametrization don't share interior points." For a Jordan arc `J` and two consecutive sub-intervals `[t₁, t₂]` and `[t₂, t₃]` of `[0,1]`, their interiors `(t₁, t₂)` and `(t₂, t₃)` are disjoint, so `J.param` (injective) sends them to disjoint sets. **PROVEN classical** by `J.inj` + interval disjointness. Mathlib API: `Function.Injective.injOn`, `Set.injOn_iff_disjoint_of_disjoint_image` (or equivalents). EXPECTED present; trivial.

5. **Multiplicity-bound argument for `pcMultigraph` (Task 8 Step 6).** The `≤ 2·M` edges-between-`p`-and-`q` bound layers two factors: `≤ M` curves through `{p, q}` (2-DOF), and `≤ 2` arcs simultaneously containing both `p` AND `q` per curve (overlap clause). The Lean argument is delicate: it touches the linear-ordering structure of `pointsOnArc` and the membership predicate `p ∈ J.carrier` interacting with the position-uniqueness claim. Budget extra time. PROVEN classical.

6. **`Real.rpow` arithmetic at `(M_mult·M_cr)^{1/3} ≤ M_mult·M_cr`.** Trivial for `M_mult, M_cr ≥ 1`, but the existing ST proof at `M = 1` skips this entirely. The new two-parameter endgame (Task 2) hits it once. EXPECTED present (`Real.rpow_le_rpow_of_exponent_le` or arithmetic from `M ≥ 1, 1/3 ≤ 1`). NEEDS_RESEARCH only if the precise lemma is awkwardly named; `nlinarith` after `Real.rpow_le_rpow_of_exponent_le` should close it.

7. **`incidenceBoundTerm` vs `+` arithmetic.** `Theorem23Statement` uses `max(max(m^{2/3}n^{2/3}, m), n)`; the cube-root estimate naturally gives `m^{2/3}n^{2/3} + m + n`. Converting `+` to `max`: `a + b + c ≤ 3·max(a,b,c)`. Easy `nlinarith`. EXPECTED present.

**No path is unblocked**. Every obstruction has a stated resolution; the riskiest is (1) modulo the discharger-living-elsewhere policy, and (2) modulo the `hJordan` shape amendment.

---

## Corollary 2.4 Sketch (next plan, NOT a phase here)

`Corollary24Statement` (the `ℝ^D` variant of Theorem 2.3 for curves defined by `e` polynomials of degree `≤ d`) follows from `Theorem23Statement` by **generic projection**: a real algebraic curve in `ℝ^D` defined by `e` polynomials of degree `≤ d` projects to a plane algebraic curve in `ℝ²` of bounded degree (degree `≤ d^e` by Bézout-style projection, or `≤ d` plus an additional bookkeeping in the cleanest setup), in such a way that distinct points project to distinct points and distinct curves project to distinct curves (this is what "generic" means — there are positive-measure-many projections that preserve both injectivities on the finite data `P, Γ`).

Two routes in the literature: (a) Pach–de Zeeuw's own argument (cited in §2.2 as a corollary, but the projection isn't proved in the paper — they invoke a standard real-algebraic-geometry projection lemma); (b) extracting it from the abstract Pach–Sharir incidence theorem for "curves with `k = 2` degrees of freedom" — same proof template, the algebraic-geometry hypotheses get folded into the input `hJordan` analogue with `K_{D, e, d}` replacing `K_d = (2d)²`.

For Lean, route (b) is cleaner: it avoids the generic-projection existence statement (which needs a real-algebraic-geometry "generic" predicate Mathlib doesn't have), instead generalizing `JordanArcDecompositionStatement` to:
```
JordanArcDecompositionStatement_D : Prop :=
  ∀ (D e d : ℕ) (γ : Set (EuclideanSpace ℝ (Fin D))),
    IsAlgebraicCurveDefinedBy D e d γ →
      ∃ cov : JordanArcCover (curveImage_D γ),
        cov.arcs.length ≤ K(D, e, d)
```
for some explicit `K(D, e, d) = O((d · max(D, e))^{D-1})` or similar Milnor–Thom-`(D)` derived bound, then re-running the same Phase 3 / Phase 4 machinery in `D`-dimensional ambient space. This is the **next plan to be written**; the Phase 3 machinery here largely ports — the only `D`-specific piece is the bridge `EuclideanSpace ℝ (Fin D) ≃ ℝ^D-style` (which is more involved than the `D = 2` case).

NOT covered in this plan. Flag: write `2026-05-XX-corollary24-from-theorem23.md` after this plan executes.

---

## Self-Review

**Spec coverage.** Strategy selection over 4 routes (Pach–Sharir 1998 chosen, others rejected with reasons) ✓. Conditional theorem `pachSharir23_of_inputs : CrossingLemmaMultigraphStatement → JordanArcDecompositionStatement → Theorem23Statement` is the goal ✓. `(M_mult, M_cr)`-parametrized endgame (Phase 1) ✓; named algebraic-geometry input `hJordan` (Phase 2) ✓; geometric realization for curve arcs (Phase 3) ✓; discharger to `Theorem23.lean` (Phase 4) ✓. Corollary 2.4 sketched, deferred ✓.

**Placeholder scan.** Proof bodies are intentionally strategy+API per the domain caveat in the header. Every *statement/signature* is complete Lean. Genuine open algebraic geometry (`hJordan` discharger) is named explicitly as a `Prop` hypothesis, not silently `sorry`d. The single intentional `sorry` is on `theorem23` itself, gated on the project's Tier-B axiom policy for `hCL` and `hJordan`.

**Type consistency.** Both `hCL` and `hJordan` thread from Task 4 through Task 9 as explicit hypotheses on `pachSharir23_of_inputs`. The `point2Equiv` bridge in Task 5 is the unique place where `EuclideanSpace ℝ (Fin 2)` ↔ `ℝ × ℝ` happens; downstream all of Phase 1, 3, 4 lives in `ℝ × ℝ` except the top-level `theorem23` statement. Names `pachSharir23_of_inputs`, `pcMultigraph`, `incidence_bound_of_crossingLemma_M` are consistent throughout. Phase 3 lemma signatures (`pcMultigraph_multiplicity_le_2M`, `pcMultigraph_crossings_le_M`, `incidences_le_numEdges_add_M`) feed Phase 1's `incidence_bound_of_crossingLemma_M` at `(M_mult := 2M, M_cr := 4M, n := Γ.card, m := P.card)`.

**Known risk.** Phase 3 is the real difficulty, mirroring the predecessor plan. Multiplicity-bound (Task 8 Step 6), crossings-overlap-counting (Task 8 Step 5), and same-curve interior-disjointness (Obstruction 4) are the three specific Lean obstructions; all three have stated resolutions, and one of them (overlap) depends on `hJordan` carrying the right overlap clause from the start. The riskiest math step is the algebraic content of `hJordan` itself (a real 1-manifold component of a plane algebraic curve is a Jordan-arc-decomposable subset of `ℝ²`), but this lives OUTSIDE the plan as an upstream axiomatized input. So the worst-case deliverable for this plan is "Theorem 2.3 proved conditional on `hCL` and `hJordan`," with `theorem23` itself stuck at one labelled `sorry` until the upstream `axiom` block lands — still a clean, honest deliverable, matching how `crossing-lemma` and `incidence-assembly` already ship gaps.

**Citation-and-source check.** Pach–Sharir 1998 (route A, chosen) — cited with exact venue. Sharir–Zahl 2017 and Solymosi–Tao 2012 (route B, rejected) — cited. Pach–Agarwal cell-decomposition (route D, rejected) — cited. Milnor 1964 / Basu–Pollack–Roy ch. 7 (for `hJordan`'s classical content) — cited. The architectural memories `01KSNB1CQ5` (paper-faithful statement constraint), `01KSNGJQJF` (durable endpoint invariant), `01KSP2BRDQ` (crossing-lemma surface) are consulted and honored.
