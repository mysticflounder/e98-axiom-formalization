# PDZ standalone formalization — build & status

## Scope (read first)

**This module formalizes exactly and only what is needed for Theorem 1.1 of
Pach–de Zeeuw, "Distinct distances on algebraic curves in the plane."**

Theorem 1.1: *a plane algebraic curve of degree `d` containing no line or circle
determines `≥ c_d · n^{4/3}` distinct distances among any `n` points on it.*

Nothing else is in scope. Theorem 1.2 (two curves) appears only as the internal
reduction target that 1.1 routes through with `C₁ = C₂`.

## Locked decisions

- **Toolchain:** `leanprover/lean4:v4.27.0`; **Mathlib only**, pinned
  `mathlib @ v4.27.0` (cache-backed). Also `require`s the sibling `crossing-lemma`
  module by local path (for the eventual incidence bound; not yet imported).
- **Namespace:** `PachDeZeeuw` / `PachDeZeeuw.PDZ` (the schema names the math, not
  the source project). No `Erdos98Proof.*` or `FormalConjectures.*` imports remain.
- **Curve substrate is local.** Mathlib has no "plane algebraic curve of degree
  `d`", so `CurveInterface.lean` defines the vocabulary directly from the paper.

## Status — the reduction chain is done (Mathlib-only, sorry-free, builds green)

`PachDeZeeuw.lean` aggregates the chain; `./lake-build.sh` is green with no
`sorry` and no errors:

- `CurveInterface` — `Point2`/`ℝ²`, `distinctDistances`, and the curve predicates
  `External.{IsBoundedDegreeCurve, IsIrreducibleCurve, IsControlledDegenerate}`,
  each defined exactly as in §2.1 (real zero set of a (irreducible) bivariate
  polynomial of bounded total degree; line-or-circle).
- `Basic` — point types, distances, exceptional-pair predicates,
  `PreparedBipartiteInput`, the Elekes/Cauchy–Schwarz core (Lemma 3.7).
- `AuxiliaryCurves` — the implicit auxiliary curve `C_ij` (paper eq. (1)) and the
  incidence/equal-distance bridge.
- `Theorem12` — Thm 1.2 ⇐ `AuxiliaryIncidenceUpperBoundStatement`.
- `IncidenceBound` — reduces 1.2 down to `PositiveAuxiliaryIncidenceCardBoundStatement`.
- `Theorem11` — Thm 1.1 ⇐ Thm 1.2.

Net: **Theorem 1.1 is proven conditional on the named incidence-bound statement.**

## Curve interface (definitions, §2.1)

| Predicate | Definition |
|-----------|------------|
| `IsBoundedDegreeCurve d C` | `∃ f ≠ 0, totalDegree f ≤ d ∧ C = Z_ℝ(f)` |
| `IsIrreducibleCurve d C` | as above with `Irreducible f` |
| `IsControlledDegenerate C` | `C` is a line `{a·x+b·y=c}, (a,b)≠0` or a circle (metric sphere) |

These matched the existing proofs' constructors exactly, so the whole chain was
reused verbatim — no Erdos98 source was needed.

## Frontier (deferred — "formalize everything eventually")

1. **`PositiveAuxiliaryIncidenceCardBoundStatement`** — the Pach–Sharir incidence
   bound `auxIncidences³ ≤ C·(|P₁|·|P₂|)⁴`, currently an unproven `Prop`
   hypothesis. Route: the sibling `crossing-lemma` module → the ℝ⁴ `auxIncidences`
   bound (the PDZ-specific bridge stays in pdz).
2. **The §2/§4 algebraic-geometry machinery** (Bézout 2.2, Milnor–Thom 2.3,
   singularity 2.4, component cover, symmetry 2.6, conic stabilizer 2.7) — the
   prior incomplete development now sits in **`attic/AlgebraicPrelim.lean`**
   (7021 lines, ~76% was quarantined block-comments; imported by nothing). It is
   parked, not deleted, for cherry-picking when the frontier is attacked. To be
   adjudicated against the paper (revive build-broken-but-legit; rewrite the rest).

## Tooling

- `lake-build.sh` — memory-shimmed, lockfiled `lake build` wrapper (see lean-usage).
- `scripts/comment_map.py` — deterministic Lean block-comment mapper (tracks
  nested `/- -/`); used to separate active code from quarantined comment blocks.
