# milnor-thom — plan

## Scope

Formalize **Theorem 2.2** of Pach–de Zeeuw, "Distinct distances on algebraic
curves in the plane":

> **Theorem 2.2.** A zero set in `ℝ^D` defined by polynomials of degree at most
> `d` has at most `(2d)^D` connected components.

Components are Euclidean-topology connected components of the real zero set, not
irreducible components. The result is due to Oleĭnik–Petrovskiĭ, Milnor, and Thom
([2, Chapter 7]).

In practice the paper only consumes the **finite-set corollary**: if the zero
set is finite, each point is its own connected component, so the set has at most
`(2d)^D` points. That corollary (`D = 4`) is what gives `|C_ij ∩ C_kl| ≤ 16d⁴`
in Lemma 3.3. Scope is the statement and this corollary.

## Why this module exists

This is the real-`ℝ^D` substitute for complex Bézout. Over `ℝ`, the size of a
finite zero set need **not** be bounded by the product of the defining degrees
(the paper's own counterexample: the plane `z = 0` met with
`(x(x-1)(x-2))² + (y(y-1)(y-2))²` gives 9 points while the degree product is 6).
The component bound repairs this and is irreplaceable in Lemma 3.3.

## Difficulty / design decision

This is the hardest of the three algebraic-geometry inputs. **Validated against
the Mathlib v4.27.0 checkout (2026-05):** the entire classical proof route is
unsupported —

- **no semialgebraic / real-algebraic-geometry layer** (no `Semialgebraic`, no
  cylindrical algebraic decomposition, no Oleĭnik–Petrovskiĭ–Milnor–Thom);
- **no Morse theory** (no Morse lemma, no "components ≤ critical points", no
  Morse inequalities);
- **no Sard's theorem.** Sard exists only as an external, currently *paused* WIP
  repo, [`fpvandoorn/sard`](https://github.com/fpvandoorn/sard) ("the hard part
  hasn't been started"), so it cannot be leaned on; some groundwork
  (`MeasureZero`, manifold charts) is being upstreamed piecemeal.

Even the finite-set corollary needs a notion of *variety degree* + complex
Bézout for the point count, which Mathlib also lacks (it has resultants and
Krull dimension, but no variety-degree API). This strongly favours route 1.

Two routes:

1. **Axiomatize Theorem 2.2 as a typed interface** (recommended in `SCOPE.md`):
   state it as a `Prop`/`axiom` annotated with the paper line it encodes, and
   build the finite-set corollary against it. This is the honest, auditable
   statement of what the development trusts.
2. **Prove the finite-set corollary directly** via complex Bézout + dimension,
   sidestepping the full topological component bound. Still large; depends on a
   notion of variety degree that Mathlib also lacks.

{{NEEDS_ADAM_INPUT}} — axiomatize (route 1) vs. attempt a proof (route 2). This
mirrors Open Question 5 in `../pdz/SCOPE.md` and should be settled before any
Lean is written here.

## Seed material

The attic carries only *statement-level* scaffolding for this, all quarantined
in `../pdz/attic/AlgebraicPrelim.lean` (e.g. `Theorem23_OPMTStatement`,
`MilnorPoint4ComponentCardBoundStatement`, the `MilnorPoint4*` thickening /
regular-value apparatus, lines ≈2817–3601). Note the attic lettered this **2.3**;
the paper letters it **2.2**. {{UNVALIDATED}} — none of it has been elaborated.

## Statement surface (to design)

- `RealZeroSet (fs : … → MvPolynomial (Fin D) ℝ) : Set (Fin D → ℝ)`.
- `connectedComponents_card_le : (∀ i, totalDegree (fs i) ≤ d) → … ≤ (2*d)^D`
  (or its `axiom` form, per the decision above).
- `finite_realZeroSet_card_le : … → S.Finite → S.ncard ≤ (2*d)^D` (the corollary
  actually consumed by `../pdz`).
- An `Audit.lean` pinning `#print axioms`.

## Toolchain / deps

- `leanprover/lean4:v4.27.0`, `mathlib @ v4.27.0`.
- **Mathlib only**.

## Status

Scaffold only (lakefile, toolchain, build script, root aggregator). No statements
or proofs yet.
