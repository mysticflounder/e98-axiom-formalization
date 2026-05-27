# milnor-thom

Lean 4 / Mathlib formalization of the **Oleĭnik–Petrovskiĭ / Milnor / Thom bound
on connected components of a real zero set** — Pach–de Zeeuw, "Distinct
distances on algebraic curves in the plane," **Theorem 2.2**:

> A zero set in `ℝ^D` defined by polynomials of degree at most `d` has at most
> `(2d)^D` connected components.

Components are counted in the Euclidean topology (not irreducible components).
The paper uses this as a real surrogate for complex Bézout in `ℝ^D`: a finite
real intersection has each point as its own connected component, so `(2d)^D`
bounds the point count (yielding `|C_ij ∩ C_kl| ≤ 16d⁴` in Lemma 3.3, `D = 4`).

## Dependencies

- **Mathlib**, pinned `mathlib @ v4.27.0` (matches the sibling modules). No
  sibling-module dependency.

## Build

```sh
lake exe cache get      # fetch Mathlib oleans once
./lake-build.sh         # build the MilnorThom library
```

`lake-build.sh` is a memory-shimmed, lockfiled wrapper around `lake build`.

## Status

Work in progress — scaffold only. This is the single hardest of the three
algebraic-geometry inputs: Mathlib has **no** semialgebraic / real-algebraic
component theory today. See `PLAN.md` for the design choice (axiomatize the
component bound as a typed interface, per `../pdz/SCOPE.md`'s Tier-B treatment,
vs. attempt the finite-set corollary via complex Bézout + dimension) — this is
an open policy decision.

## License

Apache 2.0 (see the repository-root `LICENSE`).
