# e98-axiom-formalization

Lean 4 / Mathlib formalization work supporting the Erdős #98 effort, organized
as independent but interoperating modules. Each module is its own self-contained
Lake project; together they build toward the analytic and combinatorial inputs
the larger proof consumes.

## Modules

| Module | What it formalizes | Depends on |
|--------|--------------------|------------|
| [`crossing-lemma`](crossing-lemma/) | The multigraph crossing lemma (Székely / Ajtai–Chvátal–Newborn–Szemerédi), via combinatorial maps and the planar Euler bound. | Mathlib only |
| [`pach-sharir`](pach-sharir/) | The Pach–Sharir incidence bound for points and bounded-degree algebraic curves with two degrees of freedom (Pach–de Zeeuw Thm 2.3). | Mathlib + `crossing-lemma` |
| [`pdz`](pdz/) | Pach–de Zeeuw **Theorem 1.1** — distinct distances on a plane algebraic curve (`n^{4/3}` lower bound, no line/circle). | Mathlib + `crossing-lemma` |

The dependency spine: `crossing-lemma` → `pach-sharir` (Szemerédi–Trotter-type
incidence bound) → `pdz` (reduces Theorem 1.1 to a specialization of that bound).
Each arrow is a local-path `require`. Further modules may be added over time.

## Conventions

- **Toolchain:** every module pins `leanprover/lean4:v4.27.0` + `mathlib @ v4.27.0`,
  kept in lockstep so cross-module imports are binary-compatible.
- **Build:** each module has its own `lake-build.sh`; run `lake exe cache get`
  in a module once to fetch Mathlib oleans, then `./lake-build.sh`.
- **Self-contained:** each module depends only on Mathlib and (where stated)
  sibling modules in this repo — never on external problem-specific code.

## Status

Work in progress. See each module's `README.md` / `PLAN.md` for its live frontier
and known `sorry`s.

## License

Apache 2.0 (see [`crossing-lemma/LICENSE`](crossing-lemma/LICENSE)). Vendored
third-party code retains its original copyright headers — notably
`crossing-lemma/CrossingLemma/CombinatorialMap.lean`, © 2024 Kyle Miller &
Rida Hamadani, from [mathlib4 PR #16074](https://github.com/leanprover-community/mathlib4/pull/16074).
