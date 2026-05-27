# Crossing Lemma

A self-contained [Lean 4](https://leanprover.github.io/) / [Mathlib](https://github.com/leanprover-community/mathlib4)
formalization of the **multigraph crossing lemma** (Székely; Ajtai–Chvátal–Newborn–Szemerédi,
multigraph / Pach–Tóth form):

> For a multigraph drawn in the plane with `v` vertices, `e` edges, and edge
> multiplicity at most `M`, if `e ≥ 4·M·v` then the crossing number satisfies
> `e³ ≤ 64·M·v²·cr`.

## Goals

1. **A reusable, dependency-light crossing lemma in Lean.** The crossing
   inequality is the engine behind Szemerédi–Trotter and a wide family of
   incidence bounds in combinatorial geometry. None of this exists in Mathlib
   today; this library provides it as an importable result.
2. **Mathlib-only.** The crossing lemma is pure graph combinatorics — it mentions
   no algebraic curves, no metric geometry, nothing problem-specific. This
   project depends on **Mathlib and nothing else**, and that invariant is
   load-bearing: it is what makes the result reusable across unrelated projects.
3. **A clean, kernel-checked proof via combinatorial maps.** The crossing-free
   case is established through the planar Euler-characteristic bound on the
   residual combinatorial map of a plane drawing; the general bound follows by
   the standard probabilistic (derandomized) amplification.

## Approach

The proof is assembled from:

- **Combinatorial maps** (rotation systems) and their Euler-characteristic bound
  — `CombinatorialMap*`, the planar edge bound `PlanarEdgeBound`.
- **The drawing → abstract-multigraph bridge** (`Abstractize`) and the **residual
  combinatorial map** of a plane drawing (`ResidualMap`, `ResidualMapProperties`,
  `RotationCoherence`).
- **The crossing-free Euler bound** (`CrossingFreeEuler`): a crossing-free plane
  drawing's residual map has Euler characteristic `≥ 2`.
- **The crossing inequality** itself: the frozen statement (`CrossingLemma`) and
  its derandomized amplification from the crossing-free edge bound
  (`CrossingLemmaAmplification`).

## Dependencies & toolchain

- Lean `leanprover/lean4:v4.27.0`
- Mathlib pinned at `v4.27.0` (olean cache available)

These pins match the downstream [`pdz`](#downstream) consumer so the cross-project
import is binary-compatible.

## Building

```bash
lake exe cache get     # fetch prebuilt Mathlib oleans (~5 GB, one time)
./lake-build.sh        # build the library (memory-capped, lock-guarded wrapper)
```

`lake-build.sh` caps per-`lean` memory and serializes concurrent builds; pass
through any `lake build` arguments (e.g. a specific module target).

## Layout

```
CrossingLemma.lean              root aggregator
CrossingLemma/
  CombinatorialMap.lean         rotation systems / combinatorial maps
  CombinatorialMapEdgeInsertion.lean
  CombinatorialMapEulerBound.lean
  PlanarEdgeBound.lean          planar edge bound (Euler consequence)
  PlaneArcSeparation.lean
  Abstractize.lean              plane drawing → abstract multigraph
  ResidualMap.lean              residual combinatorial map of a drawing
  ResidualMapProperties.lean
  RotationCoherence.lean
  CrossingFreeEuler.lean        crossing-free ⇒ Euler characteristic ≥ 2
  CrossingLemma.lean            the crossing-inequality statement
  CrossingLemmaAmplification.lean   derandomized amplification
```

## Status

Work in progress. The crossing-inequality statement layer is Mathlib-only; the
proof layer is being assembled and carries a small number of tracked `sorry`s
(see `PLAN.md` for the live frontier). The axiom/sorry surface of the headline
theorem is pinned and audited as the proof closes.

## Downstream

This library is consumed by the `pdz` project (distinct distances on plane
algebraic curves; Pach–de Zeeuw Theorem 1.1), which imports the crossing
inequality to discharge its point–curve incidence bound.

## Provenance & license

The proof was developed as part of a larger formalization effort and extracted
here as a standalone, Mathlib-only library, preserved as written aside from the
mechanical removal of project-specific namespace dependencies.

`CrossingLemma/CombinatorialMap.lean` is **vendored from
[mathlib4 PR #16074](https://github.com/leanprover-community/mathlib4/pull/16074)**
(combinatorial maps / planar-graph definitions not yet in the pinned Mathlib
`v4.27.0`), © 2024 **Kyle Miller, Rida Hamadani**, under Apache 2.0. Its original
copyright header is preserved in the file. It will be removed in favour of the
upstream module once a Mathlib release including #16074 is pinned.

All other files are © Adam McKenna. The whole repository is licensed under the
Apache License 2.0 — see [`LICENSE`](LICENSE).
