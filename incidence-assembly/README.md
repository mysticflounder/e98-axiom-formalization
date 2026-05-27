# incidence-assembly

**Project-specific wiring — not a paper module.** This module assembles the closed
Pach–de Zeeuw **Theorem 1.1** from the paper-faithful sibling modules, keeping all
non-paper glue out of `pdz/` and `pach-sharir/`.

## What it does

It bridges two verbatim paper statements:

- **`pach-sharir`** → `PachSharir.Corollary24Statement` (Pach–de Zeeuw Corollary 2.4,
  the `ℝ^D` Pach–Sharir incidence bound), and
- **`pdz`** → `PachDeZeeuw.PDZ.PositiveAuxiliaryIncidenceCardBoundStatement` (the one
  open hypothesis of the otherwise fully-proven Theorem 1.1 reduction chain).

`IncidenceAssembly.positiveAuxiliaryIncidenceCardBound_of_corollary24` is the paper's
§3 incidence assembly (Lemmas 3.2–3.7): instantiate Corollary 2.4 at `D = 4`, present
the auxiliary curves `C_ij` as algebraic curves, establish the two-degrees-of-freedom
system with multiplicity `M = 16d⁴`, apply the corollary, and convert the real
`max{·}` bound into pdz's cubed-integer statement. `pachDeZeeuwTheorem11_unconditional`
then closes Theorem 1.1.

## The two gaps live here, named and separated

- **Gap A** — `PachSharir.corollary24` (in `pach-sharir`): the verbatim paper theorem,
  `sorry` pending the crossing-lemma → Szemerédi–Trotter → Pach–Sharir formalization.
- **Gap B** — `positiveAuxiliaryIncidenceCardBound_of_corollary24` (here): the §3
  assembly + the real→ℕ-cubed conversion, `sorry` pending Lemmas 3.2–3.7.

`pdz/` itself is **`sorry`-free**. `#print axioms pachDeZeeuwTheorem11_unconditional`
reports `[propext, sorryAx, Classical.choice, Quot.sound]` — the two holes, nothing else.

## Dependencies

- **Mathlib**, pinned `v4.27.0`.
- **`pdz`** (`../pdz`) and **`pach-sharir`** (`../pach-sharir`), both paper modules.

## Build

```sh
lake exe cache get      # fetch Mathlib oleans once
./lake-build.sh         # build the IncidenceAssembly library
```

## License

Apache 2.0 (see the repository-root `LICENSE`).
