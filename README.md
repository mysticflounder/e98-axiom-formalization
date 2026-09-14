# e98-axiom-formalization

Lean 4 / Mathlib formalization work supporting the Erdős #98 effort, organized
as independent but interoperating modules. Each module is its own self-contained
Lake project; together they build toward the analytic and combinatorial inputs
the larger proof consumes.

## Modules

| Module | What it formalizes | Depends on |
|--------|--------------------|------------|
| [`crossing-lemma`](crossing-lemma/) | The multigraph crossing lemma (Székely / Ajtai–Chvátal–Newborn–Szemerédi), via combinatorial maps and the planar Euler bound. | Mathlib only |
| [`bezout`](bezout/) | Bézout's inequality in the real plane — two curves of degrees `d₁, d₂` meet in `≤ d₁·d₂` points unless they share a component (Pach–de Zeeuw Thm 2.1). | Mathlib only |
| [`milnor-thom`](milnor-thom/) | The Oleĭnik–Petrovskiĭ / Milnor / Thom bound — a real zero set in `ℝ^D` from degree-`≤d` polynomials has `≤ (2d)^D` connected components (Pach–de Zeeuw Thm 2.2). | Mathlib only |
| [`curve-symmetries`](curve-symmetries/) | Symmetries of plane curves — `≤ 4d` symmetries unless a line/circle, and the affine maps fixing a conic (Pach–de Zeeuw §2.3, Lemmas 2.5–2.6). | Mathlib + `bezout` |
| [`pach-sharir`](pach-sharir/) | The Pach–Sharir incidence bound for points and bounded-degree algebraic curves with two degrees of freedom (Pach–de Zeeuw Thm 2.3). | Mathlib + `crossing-lemma` |
| [`pdz`](pdz/) | Pach–de Zeeuw **Theorem 1.1** — distinct distances on a plane algebraic curve (`n^{4/3}` lower bound, no line/circle). Paper module; `sorry`-free, conditional on the open incidence hypothesis. | Mathlib + `crossing-lemma` |
| [`incidence-assembly`](incidence-assembly/) | **Project wiring, not a paper module.** Assembles the closed Theorem 1.1 by bridging `pach-sharir`'s Corollary 2.4 to `pdz`'s open incidence hypothesis (the §3 assembly, Lemmas 3.2–3.7). | Mathlib + `pdz` + `pach-sharir` |

The dependency spine: `crossing-lemma` → `pach-sharir` (Szemerédi–Trotter-type
incidence bound) → `pdz` (reduces Theorem 1.1 to a specialization of that bound)
→ `incidence-assembly` (closes the theorem from the paper modules). Each arrow is
a local-path `require`. The paper modules state theorems verbatim; all
project-specific glue lives in `incidence-assembly`.

`bezout`, `milnor-thom`, and `curve-symmetries` are the paper's §2
algebraic-geometry inputs (Theorems 2.1, 2.2 and Lemmas 2.5–2.6). They are the
deferred frontier of `pdz`: it currently axiomatizes their content behind named
hypotheses, and will `require` them as each is built. Further modules may be
added over time.

## Conventions

- **Toolchain:** every module pins `leanprover/lean4:v4.27.0` + `mathlib @ v4.27.0`,
  kept in lockstep so cross-module imports are binary-compatible.
- **Build:** each module has its own `lake-build.sh`; run `lake exe cache get`
  in a module once to fetch Mathlib oleans, then `./lake-build.sh`.
- **Self-contained:** each module depends only on Mathlib and (where stated)
  sibling modules in this repo — never on external problem-specific code.

## Status

Inventory as of 2026-09-14, taken from the module docs, the Lean source, and the
git log. No build or `#print axioms` was re-run for this inventory; axiom claims
below are as reported by the module docs.

Theorem 1.1 is **not** closed unconditionally. The reduction steps along the
spine are done; the start of the spine (the crossing lemma) and the
Szemerédi–Trotter → Pach–Sharir lift are open.

| Module | State |
|---|---|
| `pdz` | **Done, conditional.** Theorem 1.1 follows from the single named hypothesis `PositiveAuxiliaryIncidenceCardBoundStatement`. The live `PachDeZeeuw/` files contain no `sorry`. Old work is parked in `attic/AlgebraicPrelim.lean` (imported by nothing; 5 `sorry`s). |
| `incidence-assembly` | **Gap B open.** The Corollary 2.4 → pdz-hypothesis bridge (Lemmas 3.2–3.7) is one `sorry` (`IncidenceAssembly/Bridge.lean`). Per its README, `pachDeZeeuwTheorem11_unconditional` reports `sorryAx`, from Gap A and Gap B. |
| `pach-sharir` | **Szemerédi–Trotter for lines closed, conditional on the crossing lemma** as hypothesis `hCL` (docs report axioms `[propext, Classical.choice, Quot.sound]`). **Gap A open:** `theorem23` and `corollary24` are `sorry` (`PachSharir/Theorem23.lean`). Plan: `docs/superpowers/plans/2026-05-27-pach-sharir-theorem23-from-szemeredi-trotter.md`. |
| `crossing-lemma` | **Not proven.** `CrossingLemmaMultigraphStatement` is a `Prop`; `crossingLemma_of_weakBound` derives it from `WeakAveragedBound`, which no file proves. Further open items: one `sorry` in `PlaneArcSeparation.lean` (labelled CONJECTURED); `PlanarEdgeBound.lean` contains `sorry` and is excluded from the aggregator; `subsetAveraging_master` is `sorry`, labelled a proven obstruction and not used by the main theorem. |
| `bezout` (Thm 2.1) | Scaffold only: definitions and `Bezout21Statement`. No proofs, no `sorry`. |
| `milnor-thom` (Thm 2.2) | Scaffold only: statement definitions. Open policy decision: axiomatize the component bound as a typed interface, or attempt the finite-set corollary. |
| `curve-symmetries` (Lemmas 2.5–2.6) | Scaffold only: statement definitions. |

No module declares a top-level `axiom`.

### Open items along the spine

1. **Crossing lemma** — the root hypothesis of everything downstream:
   `WeakAveragedBound`, the planar edge bound, and the arc-separation residual.
2. **Gap A** — Theorem 2.3 / Corollary 2.4 from Szemerédi–Trotter (has a plan).
3. **Gap B** — the §3 assembly, Lemmas 3.2–3.7.
4. **§2 algebraic-geometry inputs** — statements only.

### Known out-of-date docs

- `crossing-lemma/PLAN.md` and `crossing-lemma/README.md` list
  `CrossingFreeEuler.lean`, which does not exist; the PLAN also describes a
  vendor pass that appears to be complete.
- `pdz/PLAN.md` says the module has one `sorry` in the closed theorem; commit
  `d48883e` moved that `sorry` into `incidence-assembly`, and pdz is now
  `sorry`-free.

See each module's `README.md` / `PLAN.md` for its detailed frontier.

## License

Apache 2.0 (see [`crossing-lemma/LICENSE`](crossing-lemma/LICENSE)). Vendored
third-party code retains its original copyright headers — notably
`crossing-lemma/CrossingLemma/CombinatorialMap.lean`, © 2024 Kyle Miller &
Rida Hamadani, from [mathlib4 PR #16074](https://github.com/leanprover-community/mathlib4/pull/16074).
