# bezout

Lean 4 / Mathlib formalization of **Bézout's inequality in the real affine
plane** — Pach–de Zeeuw, "Distinct distances on algebraic curves in the plane,"
**Theorem 2.1**:

> Two algebraic curves in `ℝ²` with degrees `d₁` and `d₂` have at most
> `d₁ · d₂` intersection points, unless they have a common component.

The paper cites this as a classical result ([10, Lemma 14.4]); here it is
formalized for the real plane, as the intersection bound every later argument
(Lemmas 2.5, 3.6, 4.1–4.3, and the §3 incidence assembly) rests on.

## Dependencies

- **Mathlib**, pinned `mathlib @ v4.27.0` (matches the sibling modules). No
  sibling-module dependency: Bézout is a foundational input.

## Build

```sh
lake exe cache get      # fetch Mathlib oleans once
./lake-build.sh         # build the Bezout library
```

`lake-build.sh` is a memory-shimmed, lockfiled wrapper around `lake build`.

## Status

Work in progress — scaffold only. See `PLAN.md` for the resultant-based proof
route. A partial development (resultant specialization, fiber-cardinality
bounds, an irreducible-pair intersection bound) already exists, quarantined, in
`../pdz/attic/AlgebraicPrelim.lean` and is the natural seed for this module.

## License

Apache 2.0 (see the repository-root `LICENSE`).
