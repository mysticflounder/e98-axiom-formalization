# bezout — plan

## Scope

Formalize **Theorem 2.1** (Bézout's inequality) of Pach–de Zeeuw, "Distinct
distances on algebraic curves in the plane":

> **Theorem 2.1 (Bézout's inequality).** Two algebraic curves in `ℝ²` with
> degrees `d₁` and `d₂` have at most `d₁ · d₂` intersection points, unless they
> have a common component.

A curve of degree `d` is `Z_ℝ(f)` with `f` of total degree `≤ d` (§2.1);
"common component" means a shared positive-dimensional factor. Scope is exactly
this statement plus the API needed to apply it downstream (the irreducible-pair
and primitive-pair specializations the later lemmas actually call).

## Why this module exists

Theorem 2.1 is the workhorse intersection bound of the paper. It is used to
prove Lemma 2.5 (a symmetry fixing infinitely many points of an irreducible
curve fixes the curve), Lemma 3.6, Lemmas 4.1–4.3, and the finite-intersection
counts that feed the incidence assembly. The paper cites it as classical; we owe
a real proof.

## Proof route

The paper points at [10, Lemma 14.4]. The standard real-plane route is via
**resultants** over `ℝ[x][y]`:

```
f, g ∈ ℝ[x][y] with no common factor
   →  Res_y(f, g) ∈ ℝ[x] is nonzero, of degree ≤ d₁·d₂
   →  each common zero (x₀, y₀) forces Res_y(f, g)(x₀) = 0     (fibre bound)
   →  ≤ d₁·d₂ admissible x-fibres, ≤ deg_y points per fibre
   →  |Z_ℝ(f) ∩ Z_ℝ(g)| ≤ d₁·d₂                               (after the standard
                                                              no-common-component
                                                              reduction)
```

**Mathlib already supplies the resultant substrate** (validated against the
v4.27.0 checkout, 2026-05): `RingTheory/Polynomial/Resultant/Basic.lean` provides

- `resultant_ne_zero [IsDomain R] (f g) (IsCoprime f g) : resultant f g ≠ 0` —
  the "coprime ⇒ nonzero resultant" direction;
- `resultant_map_map (φ : R →+* S)` — resultant commutes with ring-hom
  specialization, i.e. the fibre-evaluation bridge `Res_y(f,g)(x₀) = Res(f(x₀,·), g(x₀,·))`;
- `resultant_mul_left/right`, `resultant_prod_left/right` — multiplicativity;
- `resultant_eq_prod_roots_sub`, and the Sylvester map `sylvesterMap`/`adjSylvester`
  (the Bézout identity `a·f + b·g = Res`).

So the work is **not** building resultant theory; it is the bivariate-over-`ℝ[x]`
plumbing: viewing `f, g ∈ ℝ[x][y]`, getting `Res_y(f,g) ∈ ℝ[x]` nonzero from a
no-common-factor hypothesis, the fibre count, and the no-common-component
reduction. On this API the module is **medium**, not large (see `../pdz/SCOPE.md`
Open Question 1, now answered).

## Seed material

A partial development already exists, quarantined inside
`../pdz/attic/AlgebraicPrelim.lean`:

- **live (uncommented) substrate**, lines ≈47–1497: `NoCommonCurveComponent` and
  its monotonicity API, the resultant specialization
  (`resultant_vanishes_at_common_zero`, `resultant_ne_zero_of_fraction_coprime`,
  `isCoprime_fraction_map_of_isPrimitive`), fibre-cardinality bounds,
  `coeffline`/`zeroCurry` pair-intersection bounds, `totalDegree`-of-partials and
  `normalizedFactors` degree bounds;
- **quarantined (block-commented)**, lines ≈1704–2799: the capstone theorems
  `primitive_nonvertical_pair_intersection_bound`,
  `irreducible_pair_intersection_bound`, and `theorem22_bezout`.

Per the porting rule: revive what matches the paper, rewrite what diverges, and
re-letter to the paper's **Theorem 2.1** (the attic used a different internal
number — its `theorem22_*` naming does **not** match the paper, where 2.2 is the
Milnor–Thom component bound, not Bézout).

{{UNVALIDATED}} — the quarantined proofs have never been elaborated; the file is
excluded from every build. Their correctness is unverified until built here.

## Statement surface (to design)

- Curve / degree / common-component vocabulary — reuse `../pdz`'s
  `CurveInterface` definitions if they match §2.1, otherwise define locally.
- `bezout_intersection_card_le : … → (C₁ ∩ C₂).ncard ≤ d₁ * d₂`.
- An `Audit.lean` pinning `#print axioms` once the proof is sorry-free.

## Toolchain / deps

- `leanprover/lean4:v4.27.0`, `mathlib @ v4.27.0`.
- **Mathlib only** — foundational input, no sibling-module dependency.

## Status

Statement surface written and building green: `Bezout21Statement` (with the
`realZeroSet` / `NoCommonComponent` vocabulary) states Theorem 2.1 as the named
interface. The discharging term (the resultant-based proof above) is still
pending; `Audit.lean` is not yet present.
