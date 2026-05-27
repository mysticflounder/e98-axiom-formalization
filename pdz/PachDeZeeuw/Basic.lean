/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import FormalConjectures.Util.ProblemImports
import Erdos98Proof.Foundation
import Erdos98Proof.ExternalDefs

/-!
# Pach--de Zeeuw low-level interface

This file starts the no-external-dependency Pach--de Zeeuw lane. The first
goal is the finite counting core used by the Elekes lower bound; the curve
predicates and normalized input wrappers live alongside it so the later PDZ
files can build on a stable namespace.
-/

set_option linter.style.longLine false

namespace Erdos98Proof.PDZ

open EuclideanGeometry

/-- The plane as a 2-vector space. -/
abbrev Point2 := EuclideanSpace ℝ (Fin 2)

/-- The ambient 4-vector space for auxiliary-curve geometry. -/
abbrev Point4 := EuclideanSpace ℝ (Fin 4)

/-- Bipartite distances between two finite point sets in the plane. -/
noncomputable def bipartiteDistances (P Q : Finset Point2) : Finset ℝ :=
  (P.product Q).image (fun pq ↦ dist pq.1 pq.2)

private def lineSet (a b c : ℝ) : Set Point2 :=
  {p : Point2 | a * p 0 + b * p 1 = c}

/-- Parallel-line exceptional pair. -/
def ParallelLinePair (C₁ C₂ : Set Point2) : Prop :=
  ∃ a b c₁ c₂ : ℝ, (a, b) ≠ (0, 0) ∧
    C₁ = lineSet a b c₁ ∧ C₂ = lineSet a b c₂

/-- Orthogonal-line exceptional pair. -/
def OrthogonalLinePair (C₁ C₂ : Set Point2) : Prop :=
  ∃ a₁ b₁ c₁ a₂ b₂ c₂ : ℝ, (a₁, b₁) ≠ (0, 0) ∧ (a₂, b₂) ≠ (0, 0) ∧
    a₁ * a₂ + b₁ * b₂ = 0 ∧
    C₁ = lineSet a₁ b₁ c₁ ∧ C₂ = lineSet a₂ b₂ c₂

/-- Concentric-circle exceptional pair. -/
def ConcentricCirclePair (C₁ C₂ : Set Point2) : Prop :=
  ∃ center : Point2, ∃ r₁ r₂ : ℝ,
    C₁ = Metric.sphere center r₁ ∧ C₂ = Metric.sphere center r₂

/--
Pach--de Zeeuw exceptional curve-pair alternatives for Theorem 1.2:
parallel lines, orthogonal lines, or concentric circles.
-/
def ExceptionalCurvePair (C₁ C₂ : Set Point2) : Prop :=
  ParallelLinePair C₁ C₂ ∨ OrthogonalLinePair C₁ C₂ ∨ ConcentricCirclePair C₁ C₂

lemma exceptionalCurvePair_of_parallelLines {C₁ C₂ : Set Point2}
    (h : ParallelLinePair C₁ C₂) : ExceptionalCurvePair C₁ C₂ :=
  Or.inl h

lemma exceptionalCurvePair_of_orthogonalLines {C₁ C₂ : Set Point2}
    (h : OrthogonalLinePair C₁ C₂) : ExceptionalCurvePair C₁ C₂ :=
  Or.inr (Or.inl h)

lemma exceptionalCurvePair_of_concentricCircles {C₁ C₂ : Set Point2}
    (h : ConcentricCirclePair C₁ C₂) : ExceptionalCurvePair C₁ C₂ :=
  Or.inr (Or.inr h)

lemma ParallelLinePair.left_controlledDegenerate {C₁ C₂ : Set Point2}
    (h : ParallelLinePair C₁ C₂) : External.IsControlledDegenerate C₁ := by
  rcases h with ⟨a, b, c₁, c₂, hab, rfl, rfl⟩
  exact Or.inl ⟨a, b, c₁, hab, rfl⟩

lemma ParallelLinePair.right_controlledDegenerate {C₁ C₂ : Set Point2}
    (h : ParallelLinePair C₁ C₂) : External.IsControlledDegenerate C₂ := by
  rcases h with ⟨a, b, c₁, c₂, hab, rfl, rfl⟩
  exact Or.inl ⟨a, b, c₂, hab, rfl⟩

lemma OrthogonalLinePair.left_controlledDegenerate {C₁ C₂ : Set Point2}
    (h : OrthogonalLinePair C₁ C₂) : External.IsControlledDegenerate C₁ := by
  rcases h with ⟨a₁, b₁, c₁, a₂, b₂, c₂, hab₁, hab₂, _horth, rfl, rfl⟩
  exact Or.inl ⟨a₁, b₁, c₁, hab₁, rfl⟩

lemma OrthogonalLinePair.right_controlledDegenerate {C₁ C₂ : Set Point2}
    (h : OrthogonalLinePair C₁ C₂) : External.IsControlledDegenerate C₂ := by
  rcases h with ⟨a₁, b₁, c₁, a₂, b₂, c₂, hab₁, hab₂, _horth, rfl, rfl⟩
  exact Or.inl ⟨a₂, b₂, c₂, hab₂, rfl⟩

lemma ConcentricCirclePair.left_controlledDegenerate {C₁ C₂ : Set Point2}
    (h : ConcentricCirclePair C₁ C₂) : External.IsControlledDegenerate C₁ := by
  rcases h with ⟨center, r₁, r₂, rfl, rfl⟩
  exact Or.inr ⟨center, r₁, rfl⟩

lemma ConcentricCirclePair.right_controlledDegenerate {C₁ C₂ : Set Point2}
    (h : ConcentricCirclePair C₁ C₂) : External.IsControlledDegenerate C₂ := by
  rcases h with ⟨center, r₁, r₂, rfl, rfl⟩
  exact Or.inr ⟨center, r₂, rfl⟩

lemma ExceptionalCurvePair.left_controlledDegenerate {C₁ C₂ : Set Point2}
    (h : ExceptionalCurvePair C₁ C₂) : External.IsControlledDegenerate C₁ := by
  rcases h with h | h | h
  · exact ParallelLinePair.left_controlledDegenerate h
  · exact OrthogonalLinePair.left_controlledDegenerate h
  · exact ConcentricCirclePair.left_controlledDegenerate h

lemma ExceptionalCurvePair.right_controlledDegenerate {C₁ C₂ : Set Point2}
    (h : ExceptionalCurvePair C₁ C₂) : External.IsControlledDegenerate C₂ := by
  rcases h with h | h | h
  · exact ParallelLinePair.right_controlledDegenerate h
  · exact OrthogonalLinePair.right_controlledDegenerate h
  · exact ConcentricCirclePair.right_controlledDegenerate h

/-- Assumption 3.1 normalization data from Pach--de Zeeuw. -/
structure Assumption31Data
    (C₁ C₂ : Set Point2) (P₁ P₂ : Finset Point2) where
  noVerticalComponent₁ : Prop
  noVerticalComponent₂ : Prop
  pointSetsDisjoint : Disjoint (P₁ : Set Point2) (P₂ : Set Point2)
  sparseParallelFibers : Prop
  sparseOrthogonalFibers : Prop
  sparseConcentricFibers : Prop
  noExceptionalPair : ¬ ExceptionalCurvePair C₁ C₂

/--
Prepared bipartite input satisfying the normalizations of Assumption 3.1:
irreducible curves, finite point sets on the curves, and no exceptional
parallel/orthogonal/concentric configuration.
-/
structure PreparedBipartiteInput (d : ℕ) where
  C₁ : Set Point2
  C₂ : Set Point2
  P₁ : Finset Point2
  P₂ : Finset Point2
  hC₁ : External.IsIrreducibleCurve d C₁
  hC₂ : External.IsIrreducibleCurve d C₂
  hP₁ : (P₁ : Set Point2) ⊆ C₁
  hP₂ : (P₂ : Set Point2) ⊆ C₂
  notExceptional : ¬ ExceptionalCurvePair C₁ C₂
  assumption31 : Assumption31Data C₁ C₂ P₁ P₂

private noncomputable def distanceFiber (P Q : Finset Point2) (r : ℝ) :
    Finset (Point2 × Point2) :=
  (P.product Q).filter (fun pq ↦ dist pq.1 pq.2 = r)

private noncomputable def equalDistanceQuadruplePairs {d : ℕ}
    (X : PreparedBipartiteInput d) :
    Finset ((Point2 × Point2) × (Point2 × Point2)) :=
  ((X.P₁.product X.P₂).product (X.P₁.product X.P₂)).filter
    (fun pp ↦ dist pp.1.1 pp.1.2 = dist pp.2.1 pp.2.2)

private def quadrupleOfPairs :
    (Point2 × Point2) × (Point2 × Point2) → Point2 × Point2 × Point2 × Point2
| ⟨⟨a, b⟩, ⟨c, d⟩⟩ => (a, b, c, d)

private lemma quadrupleOfPairs_injective :
    Function.Injective quadrupleOfPairs := by
  intro x y h
  cases x
  cases y
  simp [quadrupleOfPairs] at h
  aesop

/-- Equal-distance quadruples used by the Elekes lower-bound step. -/
noncomputable def equalDistanceQuadruples {d : ℕ}
    (X : PreparedBipartiteInput d) :
    Finset ((Point2 × Point2) × (Point2 × Point2)) :=
  equalDistanceQuadruplePairs X

/-- The finite Cauchy-style lower bound behind the equal-distance quadruple count. -/
lemma lemma37_equalDistanceQuadruple_lower {d : ℕ}
    (X : PreparedBipartiteInput d) :
    X.P₁.card ^ 2 * X.P₂.card ^ 2 ≤
      (bipartiteDistances X.P₁ X.P₂).card *
        (equalDistanceQuadruples X).card := by
  classical
  let S : Finset (Point2 × Point2) := X.P₁.product X.P₂
  let f : Point2 × Point2 → ℝ := fun pq ↦ dist pq.1 pq.2
  let fibers : ℝ → Finset (Point2 × Point2) := fun r ↦ distanceFiber X.P₁ X.P₂ r
  let qfibers : ℝ → Finset ((Point2 × Point2) × (Point2 × Point2)) := fun r ↦
    fibers r ×ˢ fibers r
  have hS : S.card = X.P₁.card * X.P₂.card := by
    simpa [S] using (Finset.card_product X.P₁ X.P₂)
  have hsum : ∑ r ∈ S.image f, (fibers r).card = S.card := by
    have hsum0 :
        ∑ r ∈ S.image f, (fibers r).card =
          {i ∈ S | ∃ a b, (a ∈ X.P₁ ∧ b ∈ X.P₂) ∧ f (a, b) = f i}.card := by
      simpa [S, f, fibers, distanceFiber] using
        (Finset.sum_card_fiberwise_eq_card_filter S (S.image f) f)
    have hfilter :
        {i ∈ S | ∃ a b, (a ∈ X.P₁ ∧ b ∈ X.P₂) ∧ f (a, b) = f i} = S := by
      apply Finset.filter_true_of_mem
      intro i hi
      rcases Finset.mem_product.mp hi with ⟨hiA, hiB⟩
      exact ⟨i.1, i.2, ⟨⟨hiA, hiB⟩, rfl⟩⟩
    simpa [hfilter] using hsum0
  have hbiUnion :
      ((S.image f).biUnion qfibers).card =
        ∑ r ∈ S.image f, (fibers r).card ^ 2 := by
    rw [Finset.card_biUnion]
    · refine Finset.sum_congr rfl ?_
      intro r hr
      simpa [qfibers, pow_two, Finset.card_product]
    · intro r₁ _hr₁ r₂ _hr₂ hne
      change Disjoint (qfibers r₁) (qfibers r₂)
      rw [Finset.disjoint_left]
      intro q hq₁ hq₂
      rw [Finset.mem_product] at hq₁ hq₂
      rcases hq₁ with ⟨hq₁₁, hq₁₂⟩
      rcases hq₂ with ⟨hq₂₁, hq₂₂⟩
      simp [fibers, distanceFiber] at hq₁₁ hq₂₁
      rcases hq₁₁ with ⟨_, hdist₁⟩
      rcases hq₂₁ with ⟨_, hdist₂⟩
      exact hne (hdist₁.symm.trans hdist₂)
  have hquad_ge :
      ∑ r ∈ S.image f, (fibers r).card ^ 2 ≤ (equalDistanceQuadruples X).card := by
    have hsub : (S.image f).biUnion qfibers ⊆ equalDistanceQuadruples X := by
      intro q hq
      rw [Finset.mem_biUnion] at hq
      rcases hq with ⟨r, hr, hq⟩
      rw [Finset.mem_image] at hr
      rcases hr with ⟨pq, hpq, rfl⟩
      rw [Finset.mem_product] at hq
      rcases hq with ⟨hq₁, hq₂⟩
      simp [fibers, distanceFiber] at hq₁ hq₂
      rcases hq₁ with ⟨hq₁S, hq₁dist⟩
      rcases hq₂ with ⟨hq₂S, hq₂dist⟩
      refine Finset.mem_filter.mpr ?_
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr hq₁S, Finset.mem_product.mpr hq₂S⟩, ?_⟩
      simpa [S, f] using hq₁dist.trans hq₂dist.symm
    calc
      ∑ r ∈ S.image f, (fibers r).card ^ 2 = ((S.image f).biUnion qfibers).card := by
        simpa [qfibers] using hbiUnion.symm
      _ ≤ (equalDistanceQuadruples X).card := Finset.card_le_card hsub
  have hcs :
      S.card ^ 2 ≤ (S.image f).card * ∑ r ∈ S.image f, (fibers r).card ^ 2 := by
    simpa [hsum] using
      (sq_sum_le_card_mul_sum_sq (s := S.image f) (f := fun r ↦ (fibers r).card))
  have hmain : S.card ^ 2 ≤ (S.image f).card * (equalDistanceQuadruples X).card := by
    exact hcs.trans (Nat.mul_le_mul_left _ hquad_ge)
  have hmain' : (X.P₁.card * X.P₂.card) ^ 2 ≤
      (bipartiteDistances X.P₁ X.P₂).card * (equalDistanceQuadruples X).card := by
    rw [hS] at hmain
    simpa [S, f, bipartiteDistances, equalDistanceQuadruples] using hmain
  simpa [Nat.mul_pow] using hmain'

end Erdos98Proof.PDZ
