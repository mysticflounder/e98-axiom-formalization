# curve-symmetries

Lean 4 / Mathlib formalization of **§2.3, "Symmetries of curves,"** from
Pach–de Zeeuw, "Distinct distances on algebraic curves in the plane":

- **Lemma 2.5** — an irreducible plane algebraic curve of degree `d` has at most
  `4d` symmetries (isometries of `ℝ²` fixing it), unless it is a line or a
  circle.
- **Lemma 2.6** — the affine transformations that fix a conic, classified up to a
  rotation or translation (hyperbola / ellipse / parabola normal forms).

These are the §2 inputs to the §4 symmetry argument: Lemma 2.5 bounds
`|Γ₀| ≤ 4dm` in Lemma 3.2's symmetry branch, and Lemma 2.6 drives the conic case
of Lemma 4.3.

## Dependencies

- **Mathlib**, pinned `mathlib @ v4.27.0` (matches the sibling modules).
- **`bezout`** (sibling module, local path `../bezout`): Lemma 2.5's proof uses
  Bézout's inequality (Theorem 2.1) — a symmetry fixing infinitely many points
  of an irreducible curve fixes the curve.

## Build

```sh
lake exe cache get      # fetch Mathlib oleans once
./lake-build.sh         # build the CurveSymmetries library
```

`lake-build.sh` is a memory-shimmed, lockfiled wrapper around `lake build`.

## Status

Work in progress — scaffold only. See `PLAN.md` for the proof route (isometry
classification for 2.5; real-conic normal forms for 2.6) and the quarantined
seed material in `../pdz/attic/AlgebraicPrelim.lean`.

## License

Apache 2.0 (see the repository-root `LICENSE`).
