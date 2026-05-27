# crossing-lemma — build & vendor plan

## Scope

Self-contained formalization of the **multigraph crossing lemma** (Székely /
Ajtai–Chvátal–Newborn–Szemerédi form), proved via combinatorial maps and the
planar Euler bound. **Depends only on Mathlib.** No `Erdos98Proof.*` /
`Problem98` dependency — an Euler/crossing proof is pure graph combinatorics and
must need nothing from any problem-specific namespace. Where the source code
currently imports `Erdos98Proof.Combinatorics.*`, that is mis-filed general
combinatorics, vendored here and renamed.

Consumed by `../pdz` (Theorem 1.1, distinct distances on algebraic curves),
which requires this project by local path and imports the crossing inequality to
discharge its incidence bound.

## Locked decisions

- **Toolchain / deps:** `leanprover/lean4:v4.27.0`, `mathlib @ v4.27.0` — identical
  to `pdz`, so the cross-project `require` is binary-compatible.
- **Vendor verbatim:** bring the existing code in *exactly as written*; the only
  edits are mechanical — strip `Erdos98Proof.*` imports/namespaces, rename to the
  `CrossingLemma` lib namespace. No re-proving, no restructuring of the math.

## File inventory (12 files)

**7 moved from `pdz` (present, staged in `CrossingLemma/`):**
`CrossingLemma` (Mathlib-only statement surface), `CrossingLemmaAmplification`,
`Abstractize`, `ResidualMap`, `ResidualMapProperties`, `RotationCoherence`,
`CrossingFreeEuler`.

**5 to vendor from erdos98 (`Erdos98Proof.Combinatorics.*`):**
`CombinatorialMap`, `CombinatorialMapEdgeInsertion`, `CombinatorialMapEulerBound`,
`PlaneArcSeparation`, `PlanarEdgeBound`.

Transitive-closure check pending: once the 5 land, scan their imports for any
further `Erdos98Proof.*`; iterate until Mathlib-only.

## State of the source

- `CrossingLemma.lean` — Mathlib-only already; the frozen crossing-inequality
  `Prop` (this is the surface `pdz` imports).
- `CrossingLemmaAmplification.lean` — derandomized amplification; one labelled
  obstruction `sorry` (`subsetAveraging_master`) flagged NOT used by the main
  theorem.
- `CrossingFreeEuler.lean` — carries an exploratory tower-construction `sorry`
  (`residualFaceRegionTower_of_crossingFree`) that is off the critical path and
  slated for removal; excise during the vendor pass.

## Vendor steps (once the 5 files arrive)

1. Confirm the dependency closure is Mathlib-only (scan imports of the 5).
2. Unified rename across all 12: `import Erdos98Proof.*` → `import CrossingLemma.*`
   / `import Mathlib`; `namespace Erdos98Proof[.PDZ | .Combinatorics]` →
   `namespace CrossingLemma[...]`. Resolve cross-file symbol references.
3. Restructure filenames off the transitional `CrossingLemma/CrossingLemma.lean`
   double (statement → `CrossingLemma/Statement.lean`, etc.).
4. Drop the rogue tower `sorry`; confirm the main crossing-lemma theorem's
   axiom/sorry surface.
5. Wire modules into `CrossingLemma.lean`; `lake-build.sh` green.
6. Verify `pdz` can `import CrossingLemma.Statement` and consume the inequality.
