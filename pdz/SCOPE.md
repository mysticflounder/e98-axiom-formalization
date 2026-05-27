# Formalization Scope: Pach–de Zeeuw, "Distinct distances on algebraic curves in the plane"

Source: `pdz.txt` (arXiv version, Pach & de Zeeuw). Target: Lean 4 + Mathlib.

**Scope target: Theorem 1.1 only** (the single-curve `n^{4/3}` bound). See §1.1 for what
this restriction does and does not buy. Short version: it trims Tier A but removes **none**
of the Tier-B blockers — 1.1 has no independent proof and routes through the full Theorem
1.2 machinery applied to one irreducible component.

Status of this document: scoping only. No Lean written yet. Mathlib-coverage claims
below are at `grep`-confidence over a local checkout (rev `d163059006`, early 2026) and
should be upgraded to elaborator-confidence before committing to a plan — see
**Open questions** at the end.

---

## 1. What the paper proves

- **Theorem 1.1** — A plane algebraic curve `C` of degree `d` containing no line or
  circle: any `n` points on `C` determine `≥ c_d · n^{4/3}` distinct distances.
- **Theorem 1.2** — Two irreducible plane curves `C₁, C₂` of degree `≤ d`, not parallel
  lines / orthogonal lines / concentric circles: `m` points on `C₁` and `n` on `C₂`
  determine `≥ c'_d · min{m^{2/3}n^{2/3}, m², n²}` distinct distances.

1.1 is the special case `C₁ = C₂ = C*` (a max component of `C`) of 1.2. The paper gives
**no independent proof of 1.1**: it picks an irreducible component `C*` with `≥ n/d` of the
points and applies the entire 1.2 argument to `C₁ = C₂ = C*`.

### 1.1 — What targeting Theorem 1.1 only buys

Because `C*` is a single irreducible curve that is **never a line or a circle** (a line or
circle component would put a line/circle in `C`, which 1.1 forbids), Tier A simplifies:

- **Lemma 4.4 (line case) drops entirely** — `C₂` is never a line.
- **Lemma 3.2 always takes the `|Γ₀| ≤ 4dm` symmetry branch**; the "C₂ is a line or
  circle" branch (paper line 569) is dropped.
- **Assumption 3.1 collapses 6 parts → 2**: only (1) rotate so `C*` is not vertical, and
  (2) split the two point-set copies to be disjoint. Parts (3)–(6) (circle centers,
  concentric circles, parallel/orthogonal lines) and their point-removal bookkeeping and
  `1/(4d²)` constant-tracking become **vacuous**.
- `m = n` collapses `max{m^{4/3}n^{4/3}, m², n²} → n^{8/3}` and the result
  `min{m^{2/3}n^{2/3}, m², n²} → n^{4/3}`.

What it does **NOT** buy:

- **No Tier-B blocker is removed.** 1.1 still needs the Pach–Sharir incidence bound
  (Cor 2.4), the Milnor–Thom component bound (Thm 2.2), and real Bézout — identically.
- **Conic machinery stays.** A non-circle conic (ellipse/hyperbola/parabola, degree 2) is
  in scope for 1.1, so **Lemmas 2.6 and 4.3 — the heaviest Tier-A algebra — remain**, as
  do Lemmas 2.5, 3.3–3.7, 4.1, 4.2 and the full Tier-A.5 substrate.

## 2. Proof architecture (dependency DAG)

```
Theorem 1.1  ◄── Theorem 1.2  (set C₁=C₂; pick component with ≥ n/d points)
                     │
   ┌─────────────────┼───────────────────────────────────┐
   │                 │                                     │
 Lemma 3.7        Lemma 3.4  (partition P,Γ into          Lemma 3.6
 (Elekes lower    2-DOF systems via graph colouring)      (Γ₀,P₀ incidence
  bd on |Q|,         │            │                        bound, Bézout)
  Cauchy-Schwarz)    │            │
                  Lemma 3.2     Lemma 3.3                Lemma 3.5
                  (∃ Γ₀ small,  (dim C_ij =1;            (per-part incidence
                   no 3 curves   |finite ∩| ≤ 16d⁴;       bound)
                   ∞-intersect)  ≤2d² ∞-neighbours)         │
                     │              │                        │
        ┌────────────┼──────┐    [Milnor–Thom 2.2]      [Cor 2.4 = Pach–Sharir 2.3
        │     │      │      │     [dim theory]            + generic projection]
     L4.1   L4.2   L4.3   L4.4
     (=dist (deg≥3)(conic)(line)
      ⇒sym)
        │              │
   [Bézout 2.1]   [Lemma 2.6: affine maps fixing a conic]
   [Lemma 2.5:    [conic normal forms]
    ≤4d symmetries]
   [isometry classification]
```

## 3. The decisive split: paper-content vs. black-box inputs

The work cleanly separates into two tiers. **This split is the central scoping decision.**

### Tier B — external "black-box" theorems the paper cites but does not prove

| # | Input | Used by | In Mathlib? | If built from scratch |
|---|-------|---------|-------------|----------------------|
| 2.1 | **Bézout inequality** (real affine plane, ≤ d₁d₂ unless common component) | 2.5, 3.6, 4.1–4.4 | No (only Bézout *rings*). Resultant theory partially present. | **Medium–Large** (resultant route; classical) |
| 2.2 | **Milnor–Thom / Oleinik–Petrovskii** component bound `(2d)^D` | 3.3 | No. No semialgebraic theory at all. | **Research-grade**. Paper only needs the finite-set corollary `≤(2d)^D points`, possibly reachable via complex Bézout+dim — still large. |
| 2.3 / 2.4 | **Pach–Sharir incidence bound** (curves, k DOF) + higher-dim projection | 3.5 | **No — none.** Not even Szemerédi–Trotter. | **Research-grade / multi-person-year.** Biggest blocker. |
| — | Degree of a variety + **Bézout–Heintz** product bound | 3.3 | No notion of variety degree. | **Large–research-grade** |

Verdict: **end-to-end formalization down to Mathlib primitives is not feasible today.**
Items 2.2 and 2.3 are each standalone research formalization projects; 2.3 (incidence
bound) is the single biggest blocker and is irreplaceable in the argument.

**Recommended treatment: axiomatize Tier B as a typed interface** (Lean `axiom`s or a
`structure` of hypotheses), exactly as the neighboring formal-conjectures projects handle
deep external results. Then the paper's actual contribution is formalized *against* that
interface. The axioms are the honest, auditable statement of "what we are trusting."

### Tier A — the paper's own arguments (the real deliverable)

Difficulty assuming Tier B is available as an interface:

| Obligation | Content | Difficulty | Notes |
|-----------|---------|-----------|-------|
| Lemma 3.7 | Elekes lower bound on `|Q|` | **Trivial** | `sq_sum_le_card_mul_sum_sq` is in Mathlib (`Order/Chebyshev`). Done input. |
| Lemma 3.6 | Incidence bound for `Γ₀`, `P₀` | **Small** | Circle-intersection counting via Bézout interface. |
| Lemma 3.4 | Partition into 2-DOF systems | **Small–Medium** | Graph colouring: χ ≤ Δ+1. Mathlib has greedy-colouring bounds. Bookkeeping-heavy. |
| Lemma 3.3 | `dim C_ij = 1`; finite-∩ ≤ 16d⁴; ≤ 2d² ∞-neighbours | **Medium–Large** | Leans hardest on dim theory + Milnor–Thom corollary + variety-degree. Krull height theorem (dim-drop) **is** in Mathlib — encouraging. Unchanged for 1.1. |
| Lemma 3.2 | `∃ Γ₀`, `|Γ₀| ≤ 4dm`, no 3 curves ∞-intersect | **Medium–Large** | Top-level assembly of §4. **1.1: simplified** — always the symmetry branch, no line/circle case. |
| Lemma 4.1 | equal-dist ∩ ⇒ symmetry of C₂ | **Medium** | Isometry reconstruction; uses Bézout (irreducible curve meets its image finitely or equals it). Unchanged. |
| Lemma 4.2 | deg ≥ 3 case, triple ∩ ≤ 2d | **Medium** | Concrete algebra (eqs 2–7) reducing to a conic, + Bézout. `ring`/`linear_combination` friendly. **In scope** (deg-≥3 curves allowed in 1.1). |
| Lemma 4.3 | conic case, triple ∩ ≤ 4 | **Medium–Large** | Long case split on hyperbola/ellipse/parabola; needs Lemma 2.6 + conic normal forms. Heavy symbolic algebra. **Still in scope** — non-circle conics allowed in 1.1. |
| ~~Lemma 4.4~~ | ~~line case, double ∩ ≤ 4~~ | **Dropped** | `C₂ = C*` is never a line in 1.1. |
| Lemma 2.5 | ≤ 4d symmetries unless line/circle | **Medium** | Needs isometry classification + affine composition lemmas (partly derivable from Mathlib's SO(2) classification + Mazur–Ulam). Unchanged. |
| Lemma 2.6 | affine maps fixing a conic | **Medium–Large** | Needs real-conic normal forms (build on `QuadraticForm`+Sylvester) + coefficient matching. **Still in scope.** |
| Assumption 3.1 | the reductions | **Small** | **1.1: collapses to parts (1),(2) only**; (3)–(6) vacuous. |
| Theorem 1.1 | final assembly: pick component `C*` (≥ n/d pts), apply machinery, `m=n` | **Small** | Glue once lemmas land; component-count via `≤ d` factors. |

### Tier A.5 — substrate plumbing (needed before any Tier A lemma)

This is cross-cutting and design-sensitive; mistakes here propagate everywhere:

- `Z_ℝ(f)`, `Z_ℂ(f₁..f_k)` as point sets (ℂ side partly via `Nullstellensatz`).
- **Degree of a curve** = min degree of defining polynomial (bespoke def + API). Touches everything.
- Irreducible components via polynomial factorization (`MvPolynomial` UFD over a field) + `≤ deg` count.
- Real/complex correspondence `X^ℂ`, `X ∩ ℝ^D`, with the degree-`≤ 4d` bookkeeping.
- The `C_ij ⊂ ℝ⁴` construction (eq 1) and the dual `C̃_st`.

Difficulty: **Medium aggregate, high leverage.** Get the definitions right first.

## 4. Recommended phasing

Each phase ≈ a coherent chunk of work; estimates in **sessions** (≈150–200k context / compact),
not wall-clock. Estimates assume Tier B is axiomatized, not proven.

- **Phase 0 — Interface & substrate.** Fix the `C_ij` construction, curve/degree
  definitions, real/complex bridge, and the Tier-B axiom interface (Bézout, Milnor–Thom
  finite-set corollary, Pach–Sharir + Cor 2.4). Deliverable: everything type-checks with
  `sorry`-free statements and `sorry`-ful proofs; the DAG compiles. **~2–3 sessions.**
- **Phase 1 — Easy leaves.** Lemma 3.7 (real proof), 4.4, 3.6, Assumption 3.1. Builds
  confidence in the substrate. **~2 sessions.**
- **Phase 2 — Symmetry track.** Isometry classification + composition lemmas, Lemma 2.5,
  real-conic normal forms, Lemma 2.6. Independent of the incidence track; parallelizable.
  **~3–5 sessions** (conics are the cost).
- **Phase 3 — §4 core.** Lemmas 4.1, 4.2, 4.3, then assemble Lemma 3.2. **~4–6 sessions.**
- **Phase 4 — Incidence track.** Lemma 3.3 (dim theory — partly real proof via Krull
  height, partly axiom), Lemma 3.4, Lemma 3.5, final assembly of 1.2 and 1.1.
  **~3–5 sessions.**
- **Phase 5 — Audit.** Discharge or document every axiom; skeptic pass; confirm no hidden
  `sorry`. **~1–2 sessions.**

**Tier-A total for Theorem 1.1, Tier B axiomatized: ~12–19 sessions** (drops Lemma 4.4,
most of Assumption 3.1, the line/circle branches of 3.2, and the dual-construction
bookkeeping). Front-loaded risk is in Phase 0 (design) and Phase 3 (the §4 assembly).
Phase 2 (conics) is unchanged — it remains the cost driver — because non-circle conics
stay in scope for 1.1.

If Tier B must be *proven* in Mathlib rather than axiomatized, add: real Bézout
(medium–large, several sessions), variety-degree theory (large), and — dominating
everything — Szemerédi–Trotter → Pach–Sharir (a multi-person-year program) and a real
Milnor–Thom (research-grade). That path is **not recommended as a single project**; if
desired, the incidence bound and Milnor–Thom should be spun out as independent Mathlib
contributions on their own timelines.

## 5. Risk register

- **R1 (design).** "Degree of a curve as min-degree polynomial" and the real/complex
  bridge are bespoke definitions with no Mathlib precedent; a wrong choice forces rework
  across all of Tier A. *Mitigation:* prototype the definitions and prove 3.7+4.4 against
  them before scaling.
- **R2 (Lemma 3.2 scope).** §4 is the genuine mathematical heart and the assembly is
  intricate (case analysis over curve type, the "respects `C_ij`" symmetry counting).
  Highest chance of a latent gap. *Mitigation:* skeptic agent pass on §4 specifically.
- **R3 (axiom fidelity).** The Tier-B axioms must state *exactly* what the paper uses
  (e.g. Cor 2.4's higher-dim version with the generic-projection hypotheses, not a
  weaker/stronger variant). A too-strong axiom silently trivializes the theorem.
  *Mitigation:* each axiom annotated with the paper line it encodes; audited in Phase 5.
- **R4 (conic algebra volume).** Lemmas 2.6 & 4.3 are long explicit polynomial
  computations; tedious but not deep. Risk is time, not feasibility.

## 6. Open questions (resolve before locking a plan)

Upgrade these from `grep`-confidence to elaborator-confidence (run live `#find`/loogle or
the DB-backed Mathlib index):

1. Does `RingTheory/Polynomial/Resultant/Basic.lean` give `Res(f,g)=0 ⇔ common factor`
   and degree bounds? — swings real Bézout between medium and large.
2. Is "`A ⊗_K B` is a domain for `A,B` domains over a field" reachable from the
   `Geometrically/Integral` + `LinearDisjoint` + `Flat/Domain` cluster? — swings the
   product-irreducibility step in Lemma 3.3.
3. Is `topologicalKrullDim`/`zeroLocus` connected to `Krull dim ℂ[x]/I` with usable API?
   — determines whether the dim-drop in 3.3 is a small wrapper over the (present) Krull
   height theorem or a medium build.
4. Does `QuadraticForm` + Sylvester reach real-conic reduction cleanly? — swings Lemma 2.6.
5. **Policy decision (needs Adam):** axiomatize Tier B (recommended) vs. attempt to prove
   any of it. {{NEEDS_ADAM_INPUT}}

## 7. Bottom line (Theorem 1.1 target)

Formalizing Theorem 1.1's own argument — Lemmas 2.5, 2.6, 3.1–3.7, 4.1–4.3 (4.4 dropped)
and the final assembly — is a **feasible Lean 4 project of ~12–19 sessions** provided the
three deep external inputs (Bézout, Milnor–Thom component bound, Pach–Sharir incidence
bound) are taken as an audited axiom interface.

**Pach–Sharir is unavoidable for 1.1.** The `n^{4/3}` bound is produced *only* by the
incidence inequality: the chain is `n⁴/|D| ≤ |Q| = |I(P,Γ)| ≤ B_d·n^{8/3}` (Lemma 3.5 =
Corollary 2.4 = higher-dim Pach–Sharir), which rearranges to `|D| ≥ c_d·n^{4/3}`. Remove
the incidence bound and there is no upper bound on the quadruples `Q`, hence no lower bound
on distinct distances. The paper has no alternative route, and the only weaker-exponent
alternative in the literature (Charalambides' `n^{5/4}` via rigidity) still relies on
incidence machinery. So narrowing to 1.1 removes none of the three Tier-B blockers; it only
trims Tier A.

Proving the Tier-B inputs inside Mathlib is out of scope for a single project: the
Pach–Sharir incidence bound alone is a multi-person-year formalization and the single
hardest blocker, with Milnor–Thom a close second.
