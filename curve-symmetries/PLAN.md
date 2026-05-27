# curve-symmetries — plan

## Scope

Formalize **§2.3 ("Symmetries of curves")** of Pach–de Zeeuw, "Distinct
distances on algebraic curves in the plane" — its two lemmas:

> **Lemma 2.5.** An irreducible plane algebraic curve of degree `d` has at most
> `4d` symmetries, unless it is a line or a circle.

> **Lemma 2.6.** Let `T` be an affine transformation that fixes a conic `C`.
> Then, up to a rotation or a translation, the only possibilities are the
> explicit hyperbola / ellipse / parabola normal forms listed in the paper.

A *symmetry* of a plane curve `C` is an isometry of `ℝ²` with `T(C) = C`;
isometries are rotations, translations, or glide reflections. Scope is exactly
these two lemmas plus the isometry/affine vocabulary they need.

## Why this module exists

Lemma 2.5 supplies the `|Γ₀| ≤ 4dm` count in the symmetry branch of Lemma 3.2
(each symmetry sends each `pᵢ` to a unique `pⱼ`, so respects ≤ `m` curves
`C_ij`, and there are ≤ `4d` symmetries). Lemma 2.6 classifies the affine maps
fixing a conic and is the engine of the conic case of Lemma 4.3 (it forces the
reconstructed map `T` into one of a few forms, each of which yields a
contradiction). Both stay in scope for Theorem 1.1 because non-circle conics are
allowed.

## Proof route

**Lemma 2.5** (isometry classification + Bézout):
```
classify isometries of ℝ²  (rotation / translation / glide reflection)
   →  translation symmetry ⇒ C contains an infinite line-orbit ⇒ (Theorem 2.1) C = line
   →  two rotation centres ⇒ a translation symmetry ⇒ line
   →  single centre c: rotation images of p lie on a circle about c
        ⇒ (Theorem 2.1) C = circle  or  ≤ 2d rotation symmetries
   →  reflections: ≤ 2d by composition with a fixed reflection
   →  total ≤ 4d unless line or circle
```
Mathlib support (validated against the v4.27.0 checkout, 2026-05): Mazur–Ulam
and the orthogonal-group / `LinearIsometryEquiv` building blocks are present, but
the **plane-isometry trichotomy** (every isometry of `ℝ²` is a rotation,
translation, or glide reflection) is *not* packaged — the attic had to build it
(`classify_plane_isometry`, `orientationReversing_affine_is_reflection_or_glide`),
so that classification is real work to be revived/rewritten here. Bézout's
inequality is imported from the sibling `bezout` module.

**Lemma 2.6** (real-conic normal forms): reduce the conic to a normal form via a
rotation/translation, then match coefficients to read off which affine `T` can
fix it. Heavy but elementary symbolic algebra (`ring` / `linear_combination`).
The normalization step is *supported*: `LinearAlgebra/QuadraticForm/Real.lean`
gives Sylvester's law of inertia (`isometryEquivSignWeightedSumSquares`,
`equivalent_signType_weighted_sum_squared`, `equivalent_one_zero_neg_one_…`),
validated present in v4.27.0 — enough to diagonalize the quadratic part to
sign-weighted sum-of-squares and read off ellipse/hyperbola/parabola.

## Dependency on Bézout

This module **requires `../bezout`** (declared in `lakefile.toml`): Lemma 2.5
repeatedly invokes Theorem 2.1 ("by Theorem 2.1, this implies that `C` equals
`l`", etc.). When the first proof here is written, that import becomes live; the
require is declared now so the dependency edge is explicit and the manifest is
correct.

## Seed material

A substantial development already exists, quarantined inside
`../pdz/attic/AlgebraicPrelim.lean` (lines ≈4406–6976, all block-commented):

- `Lemma26_CurveSymmetryBoundStatement`, `ConicWitness`, `ConicNormalFormData`,
  the conic stabilizer normal-form theorems
  (`parabolaModelStabilizer_of_image_eq`, `ellipseModelStabilizer_of_image_eq`,
  `hyperbolaModelStabilizer_of_image_eq`, `conicNormalFormData_of_isIrreducibleConic`);
- the plane-isometry classification (`classify_plane_isometry`,
  `orientationReversing_affine_is_reflection_or_glide`, and the supporting
  rotation/reflection/glide lemmas).

Note the attic lettered the symmetry/stabilizer results **2.5–2.7**; the paper
has only **2.5** and **2.6** (there is no Lemma 2.7 — the attic's
`Lemma27_ConicStabilizerClassification` was an internal refinement, not a paper
result). Per the porting rule: revive what matches the paper, rewrite what
diverges, and re-letter to 2.5 / 2.6.

{{UNVALIDATED}} — the quarantined proofs have never been elaborated; correctness
is unverified until built here.

## Statement surface (to design)

- `IsSymmetry (C : Set Point2) (T : Point2 ≃ᵢ Point2) : Prop` (isometry fixing `C`).
- `symmetries_card_le : IsIrreducibleCurve d C → ¬IsLineOrCircle C → … ≤ 4*d`
  (Lemma 2.5).
- `IsConic`, conic normal-form data, and `affine_fixing_conic_normalForm`
  (Lemma 2.6).
- An `Audit.lean` pinning `#print axioms`.

## Toolchain / deps

- `leanprover/lean4:v4.27.0`, `mathlib @ v4.27.0`.
- `require bezout` (local path `../bezout`) — for Theorem 2.1.

## Status

Statement surface written and building green: `Lemma25Statement` (the ≤ `4d`
symmetry bound, with the literal constant the paper states) and `Lemma26Statement`
(the conic-stabilizer normal-form classification, with its full `ConicModel` /
`ConicNormalFormData` / `ConicStabilizerNormalForm` apparatus ported and
re-lettered from the attic's mis-numbered 2.5–2.7). The discharging terms (which
invoke Theorem 2.1 from `bezout`, and the plane-isometry trichotomy / conic
normalization) are still pending; `Audit.lean` is not yet present.
