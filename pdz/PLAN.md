# PDZ standalone formalization — build & refactor plan

## Scope (read first)

**This repository formalizes exactly and only what is needed for Theorem 1.1 of
Pach–de Zeeuw, "Distinct distances on algebraic curves in the plane."**

Theorem 1.1: *a plane algebraic curve of degree `d` containing no line or circle
determines `≥ c_d · n^{4/3}` distinct distances among any `n` points on it.*

Nothing else is in scope. Theorem 1.2 (two curves) appears only as the internal
reduction target that 1.1 routes through with `C₁ = C₂`. Anything not on the
dependency path to Theorem 1.1 — including the rogue crossing-free-Euler tower
construction and any incidence machinery beyond what 1.1 consumes — is out of
scope and is excised or quarantined, never extended.

## Locked decisions

- **Toolchain:** `leanprover/lean4:v4.27.0` (matches formal-conjectures, so the
  result re-upstreams without a port).
- **Dependency:** Mathlib only, pinned `mathlib @ v4.27.0` (cache-backed).
  `FormalConjectures.Util.ProblemImports` is upstream Erdős-statement scaffolding
  and is **not** needed here → replace with `import Mathlib`.
- **Namespace:** `Erdos98Proof.PDZ` / `Erdos98Proof` → `PachDeZeeuw` (the schema
  must name the math, not the source project).
- **All `Erdos98Proof.*` imports are removed.** The only external symbols the
  core needs are the four curve predicates (see Curve interface below).

## What is already done (sorry-free)

The top-level reduction chain is complete and contains no `sorry`:

- `Theorem11`: Thm 1.1 ⇐ Thm 1.2.
- `Theorem12`: Thm 1.2 ⇐ `AuxiliaryIncidenceUpperBoundStatement` (Elekes lower
  bound Lemma 3.7 + the incidence bridge).
- `IncidenceBound`: reduces 1.2 down to `PositiveAuxiliaryIncidenceCardBoundStatement`.
- `AuxiliaryCurves`: the `auxCurve` / `auxIncidences` construction + bridge.
- `Basic`: point types, distances, exceptional-pair predicates,
  `PreparedBipartiteInput`, Elekes Lemma 3.7.

## Live frontier (what remains to prove for 1.1)

1. **`PositiveAuxiliaryIncidenceCardBoundStatement`** — the incidence bound
   `auxIncidences³ ≤ C·(|P₁|·|P₂|)⁴`. Currently an unproven `Prop` plugged in as
   a hypothesis. This is the load-bearing Pach–Sharir step.
2. **5 `sorry`s in `AlgebraicPrelim`** (irreducible-factor-cover lemmas).

## Target structure

```
pdz/
  lakefile.toml · lean-toolchain · lake-build.sh · .gitignore   [done]
  PachDeZeeuw.lean              root aggregator                  [stub done]
  PachDeZeeuw/
    CurveInterface.lean         the 4 curve predicates (replaces External.*)
    Basic.lean                  point types, distances, Prepared input, Lemma 3.7
    Algebra/                    AlgebraicPrelim (7021 lines) split to ≤500-line files
      Curve.lean · Bezout.lean · Conic.lean · FactorCover.lean
    AuxiliaryCurves.lean · Theorem12.lean · IncidenceBound.lean · Theorem11.lean
    Audit.lean                  #guard_msgs / #print axioms trust-surface pin
```

## Curve interface (OPEN — blocks faithful standalone)

The core consumes four predicates currently from `Erdos98Proof.ExternalDefs` /
`EndpointCurve` / `Foundation`:

| Predicate | Meaning | Consumer |
|-----------|---------|----------|
| `IsIrreducibleCurve d c` | irreducible plane curve, degree ≤ d | Thm 1.1/1.2 statements; `AlgebraicPrelim` |
| `IsBoundedDegreeCurve` | degree ≤ d | factor-cover lemmas (the 5 sorries) |
| `IsControlledDegenerate c` | c is a line or circle (excluded case) | Thm 1.1 hypothesis; exceptional bridge |
| `IsLineOrCircleComponent` | c has a line/circle component | component/degeneracy link |

These are the algebraic-curve substrate (Mathlib has no "plane algebraic curve
of degree d"). **Decision needed:** vendor the existing definitions (faithful,
keeps `AlgebraicPrelim` proofs valid) vs. rebuild from the paper (cleaner, risks
rework). Pending: read access to `ExternalDefs.lean`/`EndpointCurve.lean`/
`Foundation.lean`, or confirmation that the predicates are opaque/axiomatic there.

## Crossing-lemma track — EXTRACTED to `../crossing-lemma`

The 7 crossing-lemma/Euler files (`CrossingLemma`, `CrossingLemmaAmplification`,
`CrossingFreeEuler`, `Abstractize`, `ResidualMap`, `ResidualMapProperties`,
`RotationCoherence`) were disconnected from the core chain and are general
combinatorial geometry, so they live in their own self-contained sibling project
`../crossing-lemma` (lib `CrossingLemma`, Mathlib-only). pdz now requires it by
local path (`lakefile.toml` → `crossing-lemma`, resolved in `lake-manifest.json`).

pdz consumes the crossing inequality from there to discharge
`PositiveAuxiliaryIncidenceCardBoundStatement` (via the PDZ-specific bridge:
general crossing lemma → the ℝ⁴ `auxIncidences` bound, which stays in pdz).
The rogue tower `sorry` is excised in the crossing-lemma vendor pass, not here.

## Refactor steps (after the curve-interface decision)

1. `CurveInterface.lean`: localize the four predicates; rewire `Basic`/`Algebra`.
2. Per file: `import Erdos98Proof.*` → `import Mathlib` / local imports;
   `namespace Erdos98Proof[.PDZ]` → `namespace PachDeZeeuw`.
3. Split `AlgebraicPrelim` (7021 lines) into `Algebra/*` ≤500-line files.
4. Wire ported modules into `PachDeZeeuw.lean`; `lake-build.sh` green per module.
5. `Audit.lean`: pin `#print axioms PachDeZeeuw.theorem_1_1` via `#guard_msgs`.
6. Attack the frontier: the incidence bound + the 5 factor-cover sorries.
