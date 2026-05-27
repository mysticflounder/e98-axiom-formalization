# pach-sharir

Lean 4 / Mathlib formalization of the **Pach–Sharir incidence bound**: an upper
bound on the number of incidences between a set of points and a set of
bounded-degree real algebraic curves that form a *system with two degrees of
freedom and multiplicity `M`*.

This is the incidence input behind Pach–de Zeeuw's distinct-distances theorems
(their Theorem 2.3, with the `ℝ^D` variant). The `pdz` module reduces Theorem 1.1
to a specialization of this bound (`PositiveAuxiliaryIncidenceCardBoundStatement`,
once the auxiliary-curve construction and generic projection are in place).

## Dependencies

- **Mathlib**, pinned `mathlib @ v4.27.0` (matches the sibling modules).
- **`crossing-lemma`** (sibling module, local path `../crossing-lemma`): the proof
  is a Szemerédi–Trotter-type argument that bottoms out in the multigraph crossing
  inequality.

## Build

```sh
lake exe cache get      # fetch Mathlib oleans once
./lake-build.sh         # build the PachSharir library
```

`lake-build.sh` is a memory-shimmed, lockfiled wrapper around `lake build`.

## Status

Work in progress — scaffold only. See `PLAN.md` for the statement surface and the
crossing-lemma → Szemerédi–Trotter → Pach–Sharir proof route.

## License

Apache 2.0 (see the repository-root `LICENSE`).
