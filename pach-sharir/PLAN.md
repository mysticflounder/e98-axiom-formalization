# pach-sharir — plan

## Scope

Formalize the **Pach–Sharir incidence bound** (Pach–de Zeeuw §2.2):

> **Theorem 2.3.** If a set `P` of points in `ℝ²` and a set `Γ` of algebraic
> curves in `ℝ²` of degree at most `d` form a system with two degrees of freedom
> and multiplicity `M`, then
> `I(P, Γ) ≤ α_d · (M^{1/3} |P|^{2/3} |Γ|^{2/3} + |P| + |Γ|)`.

and the `ℝ^D` variant (curves each defined by `e` polynomials of degree `≤ d`),
which is what `pdz` actually projects down from.

"Two degrees of freedom, multiplicity `M`": every two points lie on at most `M`
common curves of `Γ`, and every two curves meet in at most `M` common points.

## Why this module exists

`pdz` reduces Theorem 1.1 to `PositiveAuxiliaryIncidenceCardBoundStatement` — a
cubed incidence estimate for the auxiliary curves `C_ij ⊂ ℝ⁴`. The paper proves
that estimate by:

1. showing the `C_ij` form a 2-d.o.f. system (Lemmas 3.2/3.3, via Milnor–Thom
   and Bézout) — *lives in `pdz`*;
2. genericly projecting `ℝ^D → ℝ²` preserving incidences — *lives in `pdz`*;
3. applying **this module's** Pach–Sharir bound to the projected system;
4. absorbing discarded/exceptional cells (Lemmas 3.5/3.6) — *lives in `pdz`*.

So this module owns step 3 (the general incidence theorem); the PDZ-specific
glue stays in `pdz`.

## Proof route

```
multigraph crossing lemma  (crossing-lemma module)
   →  Szemerédi–Trotter-type point/curve incidence argument
      (build the incidence graph, bound crossings, apply the crossing inequality)
   →  Pach–Sharir bound for 2-d.o.f. bounded-degree curve systems (Theorem 2.3)
```

**Validated against the Mathlib v4.27.0 checkout (2026-05):** Mathlib has **no**
Szemerédi–Trotter and no incidence geometry at all — the only "Szemerédi" in the
library is the regularity lemma / Ruzsa–Szemerédi, which is unrelated. So even
the line case is *not* a freebie; the whole chain (crossing lemma → ST → curve
generalization) is built here, under the 2-d.o.f. / multiplicity-`M` hypothesis.
The crossing inequality itself lives in the sibling `crossing-lemma` module (also
not upstream).

Upstream status worth tracking: Mathlib PR
[#16074](https://github.com/leanprover-community/mathlib4/pull/16074)
("feat: combinatorial maps and planar graphs", open as of 2026-05-26) is the
planarity / combinatorial-map substrate that `crossing-lemma` currently vendors.
If it lands, the planar-drawing foundation can be de-vendored — but it supplies
neither ST nor the point/curve incidence argument, which remain bespoke.

## Statement surface (to design)

- `IncidenceSystem` / `TwoDegreesOfFreedom` / `Multiplicity` predicates over a
  finite point set and a finite family of bounded-degree curves.
- `PachSharirIncidenceBound` : the `Prop` stating Theorem 2.3.
- The `ℝ^D` variant consumed by `pdz`.
- An `Audit.lean` pinning `#print axioms` once the proof is sorry-free.

## Toolchain / deps

- `leanprover/lean4:v4.27.0`, `mathlib @ v4.27.0`.
- `require crossing-lemma` (local path `../crossing-lemma`).

## Status

Scaffold only (lakefile, toolchain, build script, root aggregator). No statements
or proofs yet.
