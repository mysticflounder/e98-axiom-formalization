/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib
import CrossingLemma.Abstractize
import CrossingLemma.ResidualMap
import CrossingLemma.ResidualMapProperties
import CrossingLemma.CombinatorialMapEdgeInsertion
import CrossingLemma.CombinatorialMapEulerBound
import CrossingLemma.PlaneArcSeparation

/-!
# BR-3b — a crossing-free plane drawing's residual map has Euler characteristic ≥ 2

This file is the **lower-bound half** of card BR-3b of the Pach–de Zeeuw route-(B)
bridge: under crossing-freeness, the residual combinatorial map
`residualMap G hARR` of a plane drawing satisfies `2 ≤ χ`.  Combined with the
companion **upper bound** `CombinatorialMap.eulerCharacteristic_le_two` (BR-3a,
the genus inequality `χ = 2 − 2g ≤ 2`, proven sorry-free in
`CombinatorialMapEulerBound.lean`), this pins `χ = 2` — the genus-0 / planar
fact that crossing-freeness encodes.

The file is **OFF the closure aggregator** `CrossingLemma.lean`; it does not affect
`tests/print-axioms-expected.txt`.

## PINNED DESIGN — the tower interface and how it composes

The target

  `theorem two_le_eulerChar_of_crossingFree`
    `(G) (hARR) (hCF : CrossingFree G) (hconn : G.GraphConnected) :`
    `2 ≤ (residualMap G hARR).eulerCharacteristic`

is assembled (see `two_le_eulerChar_of_crossingFree` at the bottom) from:

1. **`eulerChar_iso_invariant`  —  [PROVEN, sorry-free].**
   `CombinatorialMap.Iso M M' → M.eulerCharacteristic = M'.eulerCharacteristic`.
   The coherence ingredient (a): an `Iso`'s carrier equivalence conjugates each
   structure permutation, hence induces `Vertex ≃ Vertex'`, `Edge ≃ Edge'`,
   `Face ≃ Face'` (`Quotient.congr` of `SameCycle`), so the three cardinalities —
   and therefore `χ` — agree.  This is exactly the handle that lets an incremental
   `insertedEdgeMap`-tower (whose dart type is `((D₀ ⊕ Fin 2) ⊕ …)`) be compared to
   the monolithic `residualMap` (dart type `Fin G.numEdges × Bool`).

2. **`facialStep`  —  [PROVEN, sorry-free].**
   A thin re-export of D1-A's
   `EdgeInsertion.eulerCharacteristic_insertedEdgeMap_of_sameCycle`: a *facial*
   edge insertion (corners `c₁ ≠ c₂` on a common `facePerm`-orbit) leaves `χ`
   unchanged.  This is the per-step χ-bookkeeping of the induction.

3. **`eulerChar_eq_two_of_oneFace_tree`  —  [PROVEN, sorry-free].**
   The combinatorial base case: a map with a single face (`card Face = 1`) and the
   tree edge-count (`card Edge + 1 = card Vertex`) has `χ = 2`.  Pure arithmetic on
   the χ-formula; no geometry.  (The fact that the spanning-forest base of the
   drawing *is* such a one-face tree map is part of the tower-construction
   obligation below.)

4. **`FaceRegionInvariant` and `FaceRegionTowerStep`  —  [PROVEN, sorry-free].**
   The replacement for the old disconnected facial certificate: the current
   partial map carries a dictionary from faces to complementary regions, and a
   tower step records the registered crosscut, the two attachment corners, the
   two-sided split, and the isomorphism from the canonical `insertedEdgeMap` to
   the next partial map.  Given this data,
   `FaceRegionTowerStep.eulerCharacteristic_eq` proves the step preserves `χ`.

5. **`ResidualFaceRegionTower`  —  [OPEN construction obligation].**
   This is the exact remaining tower/coherence package: a one-face tree base, a
   finite sequence of maintained crosscut insertions, and a final isomorphism to
   the monolithic `residualMap G hARR`.  The theorem
   `eulerChar_residualMap_eq_two_of_faceRegionTower` is already proved
   sorry-free from such a witness.

6. **`crossingFree_arc_splits_region`  —  [CONJECTURED-feasible; carries the
   `local_arc_separation` geometric `sorry`, NOT a new sorry of this file].**
   The geometry the maintained tower step consumes: a residual edge-arc that is a
   crosscut of a complementary region of the rest of the arrangement splits that
   region into exactly two pieces.  A direct application of (MS)
   `PlaneArcSeparation.local_arc_separation` through the arc-type bridge
   `toPlaneArc`.  It is sorry-free *given* (MS); (MS) itself carries the single
   localized Jordan-strength `sorry` `exists_twoSidedPartition_of_arc`, tracked
   centrally — this file introduces **no** geometric sorry of its own.

The single live missing piece is now:

* **`residualFaceRegionTower_of_crossingFree`  [BLOCKED, `sorry`].**
  Construct `ResidualFaceRegionTower G hARR` from `CrossingFree G` and
  `G.GraphConnected`.  This packages the tower/base construction, face-region
  invariant maintenance, rotation-splice coherence, and final dart-reindexing
  isomorphism.  The old `facialCertificate_of_crossingFree` statement was
  unsound as a standalone theorem and has been removed from the live proof
  surface; the dictionary now appears as explicit data in each
  `FaceRegionTowerStep`.

`two_le_eulerChar_of_crossingFree` then reads `2 ≤ χ` off `χ = 2`
through `eulerChar_residualMap_eq_two`; that theorem is routed through the
explicit tower construction obligation.  It is **not** axiom-clean until
`residualFaceRegionTower_of_crossingFree` is proved.

## Honest status summary

* PROVEN sorry-free:  `eulerChar_iso_invariant`, `facialStep`,
  `eulerChar_eq_two_of_oneFace_tree`, `toPlaneArc` (+ `toPlaneArc_arcInterior`),
  the `FaceRegionInvariant` local dictionary lookup, and the finite
  inserted-face classifier plumbing through
  `FaceRegionInvariant.insertionMaintenance_of_canonicalSplitFaceEquiv`, plus
  the canonical region-pool constructor
  `FaceRegionInvariant.insertionMaintenance_of_canonicalCrosscut`, and the
  generic maintained-tower theorem
  `eulerChar_residualMap_eq_two_of_faceRegionTower`.
* PROVEN modulo (MS)'s tracked geometric `sorry` (no new sorry here):
  `crossingFree_arc_splits_region`.
* BLOCKED, one labelled `sorry`:  `residualFaceRegionTower_of_crossingFree`.
* Assembled target, carrying that tower-construction `sorry`:
  `two_le_eulerChar_of_crossingFree`.
-/

set_option linter.style.longLine false

namespace CrossingLemma.PDZ

open CombinatorialMap
open CrossingLemma.PlaneArcSeparation

/-! ## 1. Euler characteristic is an `Iso`-invariant  [PROVEN, sorry-free]

The coherence ingredient (a).  An isomorphism of combinatorial maps conjugates
each of the three structure permutations; conjugation transports `SameCycle`
classes bijectively, so the `Vertex`/`Edge`/`Face` quotients are equivalent and
the cardinalities — hence `χ` — coincide. -/

section IsoInvariance

variable {D D' : Type*} {M : CombinatorialMap D} {M' : CombinatorialMap D'}

/-- From a permutation conjugation `f ∘ σ = σ' ∘ f` (with `f` an equivalence),
`σ'` is the `permCongr`-conjugate of `σ`. -/
theorem perm_conj_of_comm (f : D ≃ D') (σ : Equiv.Perm D) (σ' : Equiv.Perm D')
    (h : (f : D → D') ∘ σ = σ' ∘ f) : σ' = f.permCongr σ := by
  ext x
  rw [Equiv.permCongr_apply]
  have := congrFun h (f.symm x)
  simp only [Function.comp_apply, Equiv.apply_symm_apply] at this
  exact this.symm

-- `permCongr_sameCycle` (SameCycle of a `permCongr`-conjugate reduces to SameCycle
-- on pre-images) is reused from `ResidualMapProperties` (imported), not redefined.

/-- The `SameCycle` quotients of conjugate permutations are equivalent. -/
noncomputable def quotientSameCycleEquivOfComm
    (f : D ≃ D') (σ : Equiv.Perm D) (σ' : Equiv.Perm D')
    (h : (f : D → D') ∘ σ = σ' ∘ f) :
    Quotient (Equiv.Perm.SameCycle.setoid σ) ≃ Quotient (Equiv.Perm.SameCycle.setoid σ') := by
  have hconj : σ' = f.permCongr σ := perm_conj_of_comm f σ σ' h
  refine Quotient.congr f ?_
  intro a b
  change σ.SameCycle a b ↔ σ'.SameCycle (f a) (f b)
  rw [hconj, permCongr_sameCycle]
  simp only [Equiv.symm_apply_apply]

/-- **(item 1) Euler-characteristic `Iso`-invariance — PROVEN.**  Isomorphic
combinatorial maps have the same Euler characteristic. -/
theorem eulerChar_iso_invariant [Fintype D] [Fintype D']
    (e : CombinatorialMap.Iso M M') :
    M.eulerCharacteristic = M'.eulerCharacteristic := by
  have hV : Fintype.card M.Vertex = Fintype.card M'.Vertex :=
    Fintype.card_congr
      (quotientSameCycleEquivOfComm e.toEquiv M.vertexPerm M'.vertexPerm e.vertex_comm)
  have hE : Fintype.card M.Edge = Fintype.card M'.Edge :=
    Fintype.card_congr
      (quotientSameCycleEquivOfComm e.toEquiv M.edgePerm M'.edgePerm e.edge_comm)
  have hF : Fintype.card M.Face = Fintype.card M'.Face :=
    Fintype.card_congr
      (quotientSameCycleEquivOfComm e.toEquiv M.facePerm M'.facePerm e.face_comm)
  unfold CombinatorialMap.eulerCharacteristic
  rw [hV, hE, hF]

end IsoInvariance

/-! ## 2. The facial χ-step  [PROVEN, sorry-free]

Re-export of D1-A in this namespace's vocabulary: inserting an edge whose two
corners share a face leaves `χ` unchanged. -/

/-- **(item 2) Facial step — PROVEN** (re-export of
`EdgeInsertion.eulerCharacteristic_insertedEdgeMap_of_sameCycle`).  A facial edge
insertion keeps `χ` fixed. -/
theorem facialStep {D : Type*} [Fintype D] [DecidableEq D]
    (M : CombinatorialMap D) (c₁ c₂ : D) (hc : c₁ ≠ c₂)
    (hsame : M.facePerm.SameCycle c₁ c₂) :
    (CrossingLemma.EdgeInsertion.insertedEdgeMap M c₁ c₂).eulerCharacteristic
      = M.eulerCharacteristic :=
  CrossingLemma.EdgeInsertion.eulerCharacteristic_insertedEdgeMap_of_sameCycle M c₁ c₂ hc hsame

/-! ## 3. The combinatorial base case  [PROVEN, sorry-free] -/

/-- **(item 3) Base case — PROVEN.**  A combinatorial map with exactly one face
(`card Face = 1`) and the tree edge-count (`card Edge + 1 = card Vertex`) has Euler
characteristic `2`.  Pure χ-arithmetic; this is the `χ = V − (V−1) + 1 = 2` of a
spanning-tree map. -/
theorem eulerChar_eq_two_of_oneFace_tree {D : Type*} [Fintype D]
    (M : CombinatorialMap D) (hF : Fintype.card M.Face = 1)
    (htree : Fintype.card M.Edge + 1 = Fintype.card M.Vertex) :
    M.eulerCharacteristic = 2 := by
  unfold CombinatorialMap.eulerCharacteristic
  rw [hF]
  have hVE : (Fintype.card M.Vertex : ℤ) = (Fintype.card M.Edge : ℤ) + 1 := by
    exact_mod_cast htree.symm
  rw [hVE]; push_cast; ring

/-! ## 4. The geometric input to a maintained tower step

Bridge a `SimpleCurveArc` (`CrossingLemma`'s arc carrier) to a `SimpleArc Plane`
(`PlaneArcSeparation`'s arc carrier), then feed the (MS) lemma. -/

/-- Re-present a `SimpleCurveArc` as a `PlaneArcSeparation.SimpleArc Plane`.  The
two carriers have the same shape (continuous injective map out of `Icc 0 1`). -/
def toPlaneArc (a : SimpleCurveArc) : SimpleArc Plane where
  toFun := a.param
  continuous_toFun := a.cont
  injective_toFun := a.inj

/-- The `PlaneArcSeparation` arc-interior of `toPlaneArc a` is the `CrossingLemma`
arc-interior of `a` (definitionally equal). -/
theorem toPlaneArc_arcInterior (a : SimpleCurveArc) :
    (toPlaneArc a).arcInterior = interiorOfArc a := rfl

/-- **(item 4) Geometric input — PROVEN modulo (MS)'s tracked `sorry`.**  A
residual edge-arc that is a crosscut of a simply connected complementary region
`R` of a closed arrangement `A` splits `R ∖ arc` into exactly two connected
components.  This is `local_arc_separation` applied through the arc bridge; it
carries the single Jordan-strength `sorry` of (MS), and introduces no new one.

The hypothesis `hArc : ArcInRegion A R (toPlaneArc a)` packages exactly the
crosscut configuration (`A` closed; `R` an open simply connected component of
`Aᶜ`; the arc interior in `R`; both endpoints on `frontier R`). -/
theorem crossingFree_arc_splits_region {A R : Set Plane} {a : SimpleCurveArc}
    (hArc : ArcInRegion A R (toPlaneArc a)) :
    SplitsIntoTwo (regionMinusArc R (toPlaneArc a)) :=
  local_arc_separation hArc

/-! ## 5. Face-region invariant for partial drawings

The old obstruction statement below was unsound because it tried to recover
`Mpart.facePerm.SameCycle c₁ c₂` from a disconnected existential geometric split.
The replacement interface carries the missing dictionary as data: every
combinatorial face has a registered complementary region, and every corner dart
is assigned to the region of its `facePerm` orbit.

This does not prove the topology. It pins the exact data the topology/induction
packet must maintain. -/

/-- A face-region dictionary for a partial residual map.  `A` is the already
placed geometric arrangement.  The map `regionOfFace` registers the complementary
plane region represented by each combinatorial face, and `cornerRegion` records
which registered region a corner dart enters.

The injectivity field is the load-bearing part for the facial certificate: two
corners certified to enter the same registered region must belong to the same
`facePerm` orbit. -/
structure FaceRegionInvariant {D : Type*} (M : CombinatorialMap D)
    (A : Set Plane) where
  /-- Region represented by a combinatorial face. -/
  regionOfFace : M.Face → Set Plane
  /-- Distinct combinatorial faces represent distinct regions. -/
  regionOfFace_injective : Function.Injective regionOfFace
  /-- Registered regions are open in the plane. -/
  region_isOpen : ∀ f, IsOpen (regionOfFace f)
  /-- Registered regions are connected pieces of the complement. -/
  region_preconnected : ∀ f, IsPreconnected (regionOfFace f)
  /-- Registered regions lie in the complement of the already-placed arrangement. -/
  region_subset_compl : ∀ f, regionOfFace f ⊆ Aᶜ
  /-- Distinct registered regions are disjoint. -/
  region_pairwiseDisjoint : ∀ {f g}, f ≠ g → Disjoint (regionOfFace f) (regionOfFace g)
  /-- Region entered by a corner dart. -/
  cornerRegion : D → Set Plane
  /-- Corner regions are exactly the regions of their `facePerm` orbits. -/
  cornerRegion_eq_face : ∀ d, cornerRegion d = regionOfFace (M.Face_mk d)

namespace FaceRegionInvariant

variable {D : Type*} {M : CombinatorialMap D} {A R : Set Plane}

/-- Build a face-region invariant from a region assignment on face orbits.  The
corner-region assignment is then forced: a dart enters the region of its
`facePerm` orbit. -/
def ofFaceRegions
    (regionOfFace : M.Face → Set Plane)
    (hinj : Function.Injective regionOfFace)
    (hopen : ∀ f, IsOpen (regionOfFace f))
    (hpre : ∀ f, IsPreconnected (regionOfFace f))
    (hcompl : ∀ f, regionOfFace f ⊆ Aᶜ)
    (hdisj : ∀ {f g}, f ≠ g → Disjoint (regionOfFace f) (regionOfFace g)) :
    FaceRegionInvariant M A where
  regionOfFace := regionOfFace
  regionOfFace_injective := hinj
  region_isOpen := hopen
  region_preconnected := hpre
  region_subset_compl := hcompl
  region_pairwiseDisjoint := hdisj
  cornerRegion := fun d => regionOfFace (M.Face_mk d)
  cornerRegion_eq_face := fun _ => rfl

/-- A one-face map has a canonical face-region invariant once a single ambient
region is supplied.  This is the base-case constructor for the insertion tower. -/
def ofOneFace
    (hface : Subsingleton M.Face) (R : Set Plane)
    (hopen : IsOpen R) (hpre : IsPreconnected R) (hcompl : R ⊆ Aᶜ) :
    FaceRegionInvariant M A :=
  ofFaceRegions (M := M) (A := A) (fun _ => R)
    (by
      intro f g _
      exact @Subsingleton.elim M.Face hface f g)
    (fun _ => hopen)
    (fun _ => hpre)
    (fun _ => hcompl)
    (by
      intro f g hfg
      exact (hfg (@Subsingleton.elim M.Face hface f g)).elim)

/-- Special case of `ofOneFace` for the empty arrangement and the whole plane. -/
def ofOneFaceEmptyArrangement
    (hface : Subsingleton M.Face) :
    FaceRegionInvariant M (∅ : Set Plane) :=
  ofOneFace (M := M) (A := (∅ : Set Plane)) hface Set.univ
    isOpen_univ
    (by simpa using (isPreconnected_univ : IsPreconnected (Set.univ : Set Plane)))
    (by intro x _; simp)

/-- Constructor specialized to the inserted-edge map.  This is the non-topological
part of building the post-insertion invariant: once the implementation supplies a
region assignment on the new face orbits, the full `FaceRegionInvariant` follows
with corner regions forced by `Face_mk`. -/
def insertedOfFaceRegions
    {D : Type*} [Fintype D] [DecidableEq D]
    (M : CombinatorialMap D) (A' : Set Plane) (c₁ c₂ : D)
    (regionOfFace :
      (CrossingLemma.EdgeInsertion.insertedEdgeMap M c₁ c₂).Face → Set Plane)
    (hinj : Function.Injective regionOfFace)
    (hopen : ∀ f, IsOpen (regionOfFace f))
    (hpre : ∀ f, IsPreconnected (regionOfFace f))
    (hcompl : ∀ f, regionOfFace f ⊆ A'ᶜ)
    (hdisj : ∀ {f g}, f ≠ g → Disjoint (regionOfFace f) (regionOfFace g)) :
    FaceRegionInvariant
      (CrossingLemma.EdgeInsertion.insertedEdgeMap M c₁ c₂) A' :=
  ofFaceRegions (M := CrossingLemma.EdgeInsertion.insertedEdgeMap M c₁ c₂)
    (A := A') regionOfFace hinj hopen hpre hcompl hdisj

/-- The target set of regions after a facial split: every old face except the
split face, plus the two new sides. -/
abbrev SplitFacePool (splitFace : M.Face) :=
  {f : M.Face // f ≠ splitFace} ⊕ Fin 2

/-- Region assignment on the abstract split-face pool.  `Fin 2` indexes the two
new sides supplied by the crosscut theorem. -/
def splitFacePoolRegion
    (hFR : FaceRegionInvariant M A) (splitFace : M.Face)
    (U V : Set Plane) :
    SplitFacePool (M := M) splitFace → Set Plane
  | Sum.inl f => hFR.regionOfFace f.1
  | Sum.inr i => if i = 0 then U else V

/-- The region in an `ArcInRegion` configuration is contained in the complement
of the current arrangement. -/
theorem arcInRegion_region_subset_compl {A R : Set Plane} {β : SimpleArc Plane}
    (hArc : ArcInRegion A R β) : R ⊆ Aᶜ := by
  obtain ⟨x, _hx, hR⟩ := hArc.isComponent
  rw [hR]
  exact connectedComponentIn_subset Aᶜ x

/-- The frontier of a complementary component lies in the closed arrangement. -/
theorem arcInRegion_frontier_subset_arrangement
    {A R : Set Plane} {β : SimpleArc Plane}
    (hArc : ArcInRegion A R β) : frontier R ⊆ A := by
  intro z hzfront
  by_contra hzA
  obtain ⟨x, _hx, hR⟩ := hArc.isComponent
  have hzfront' : z ∈ closure R \ R := by
    simpa [hArc.isOpen_R.frontier_eq] using hzfront
  have hzAcompl : z ∈ Aᶜ := hzA
  have hAopen : IsOpen Aᶜ := hArc.isClosed_A.isOpen_compl
  have hCopen : IsOpen (connectedComponentIn Aᶜ z) :=
    hAopen.connectedComponentIn
  have hzC : z ∈ connectedComponentIn Aᶜ z :=
    mem_connectedComponentIn hzAcompl
  obtain ⟨w, hwC, hwR⟩ :=
    mem_closure_iff.mp hzfront'.1
      (connectedComponentIn Aᶜ z) hCopen hzC
  have hwRx : w ∈ connectedComponentIn Aᶜ x := by
    simpa [hR] using hwR
  have hcc :
      connectedComponentIn Aᶜ x = connectedComponentIn Aᶜ z := by
    calc
      connectedComponentIn Aᶜ x = connectedComponentIn Aᶜ w :=
        connectedComponentIn_eq hwRx
      _ = connectedComponentIn Aᶜ z := (connectedComponentIn_eq hwC).symm
  have hzR : z ∈ R := by
    rw [hR, hcc]
    exact hzC
  exact hzfront'.2 hzR

/-- In a crosscut configuration, the whole arc carrier lies in the old split
region together with the old arrangement.  Interior points lie in `R`; endpoints
lie in `A` because they are on the frontier of a complementary component of the
closed arrangement. -/
theorem arcInRegion_carrier_subset_region_union_arrangement
    {A R : Set Plane} {β : SimpleArc Plane}
    (hArc : ArcInRegion A R β) : β.carrier ⊆ R ∪ A := by
  intro y hy
  rcases hy with ⟨t, rfl⟩
  by_cases ht0 : (t : ℝ) = 0
  · right
    have ht : t = SimpleArc.src := Subtype.ext ht0
    rw [ht]
    exact arcInRegion_frontier_subset_arrangement hArc hArc.src_mem_frontier
  by_cases ht1 : (t : ℝ) = 1
  · right
    have ht : t = SimpleArc.tgt := Subtype.ext ht1
    rw [ht]
    exact arcInRegion_frontier_subset_arrangement hArc hArc.tgt_mem_frontier
  · left
    apply hArc.interior_subset
    refine ⟨t, ?_, rfl⟩
    exact ⟨lt_of_le_of_ne t.2.1 (Ne.symm ht0), lt_of_le_of_ne t.2.2 ht1⟩

/-- The left side of a two-sided partition is contained in the set being
partitioned. -/
theorem isTwoSidedPartition_left_subset {W U V : Set Plane}
    (hsplit : IsTwoSidedPartition W U V) : U ⊆ W := by
  intro x hx
  rw [← hsplit.union_eq]
  exact Or.inl hx

/-- The right side of a two-sided partition is contained in the set being
partitioned. -/
theorem isTwoSidedPartition_right_subset {W U V : Set Plane}
    (hsplit : IsTwoSidedPartition W U V) : V ⊆ W := by
  intro x hx
  rw [← hsplit.union_eq]
  exact Or.inr hx

/-- The left side of a crosscut partition lies in the original region. -/
theorem isTwoSidedPartition_left_subset_regionMinusArc
    {R U V : Set Plane} {β : SimpleArc Plane}
    (hsplit : IsTwoSidedPartition (regionMinusArc R β) U V) :
    U ⊆ R := by
  intro x hx
  exact (isTwoSidedPartition_left_subset hsplit hx).1

/-- The right side of a crosscut partition lies in the original region. -/
theorem isTwoSidedPartition_right_subset_regionMinusArc
    {R U V : Set Plane} {β : SimpleArc Plane}
    (hsplit : IsTwoSidedPartition (regionMinusArc R β) U V) :
    V ⊆ R := by
  intro x hx
  exact (isTwoSidedPartition_right_subset hsplit hx).1

/-- The left side of a crosscut partition avoids the enlarged arrangement
`A ∪ β.carrier`. -/
theorem isTwoSidedPartition_left_subset_inserted_compl
    {A R U V : Set Plane} {β : SimpleArc Plane}
    (hArc : ArcInRegion A R β)
    (hsplit : IsTwoSidedPartition (regionMinusArc R β) U V) :
    U ⊆ (A ∪ β.carrier)ᶜ := by
  intro x hxU
  have hxW := isTwoSidedPartition_left_subset hsplit hxU
  have hxA : x ∈ Aᶜ := arcInRegion_region_subset_compl hArc hxW.1
  rw [Set.mem_compl_iff, Set.mem_union]
  intro hx
  rcases hx with hxA' | hxβ
  · exact hxA hxA'
  · exact hxW.2 hxβ

/-- The right side of a crosscut partition avoids the enlarged arrangement
`A ∪ β.carrier`. -/
theorem isTwoSidedPartition_right_subset_inserted_compl
    {A R U V : Set Plane} {β : SimpleArc Plane}
    (hArc : ArcInRegion A R β)
    (hsplit : IsTwoSidedPartition (regionMinusArc R β) U V) :
    V ⊆ (A ∪ β.carrier)ᶜ := by
  intro x hxV
  have hxW := isTwoSidedPartition_right_subset hsplit hxV
  have hxA : x ∈ Aᶜ := arcInRegion_region_subset_compl hArc hxW.1
  rw [Set.mem_compl_iff, Set.mem_union]
  intro hx
  rcases hx with hxA' | hxβ
  · exact hxA hxA'
  · exact hxW.2 hxβ

/-- Old unsplit face regions avoid the enlarged arrangement, provided the new
arc carrier is contained in the split region together with the old arrangement.
This is the only extra carrier-containment fact needed for the old faces. -/
theorem oldFaceRegion_subset_inserted_compl_of_carrier_subset
    (hFR : FaceRegionInvariant M A) {splitFace : M.Face} {R : Set Plane}
    {β : SimpleArc Plane}
    (hface : hFR.regionOfFace splitFace = R)
    (hcarrier : β.carrier ⊆ R ∪ A)
    (f : {f : M.Face // f ≠ splitFace}) :
    hFR.regionOfFace f.1 ⊆ (A ∪ β.carrier)ᶜ := by
  intro x hxold
  have hxA : x ∈ Aᶜ := hFR.region_subset_compl f.1 hxold
  rw [Set.mem_compl_iff, Set.mem_union]
  intro hx
  rcases hx with hxA' | hxβ
  · exact hxA hxA'
  · rcases hcarrier hxβ with hxR | hxA'
    · have hdisj : Disjoint (hFR.regionOfFace f.1) R := by
        simpa [hface] using hFR.region_pairwiseDisjoint f.2
      exact (Set.disjoint_iff.mp hdisj) ⟨hxold, hxR⟩
    · exact hxA hxA'

/-- Openness of the canonical split-face region assignment. -/
theorem splitFacePoolRegion_isOpen
    (hFR : FaceRegionInvariant M A) (splitFace : M.Face)
    {W U V : Set Plane} (hsplit : IsTwoSidedPartition W U V) :
    ∀ p, IsOpen (splitFacePoolRegion hFR splitFace U V p) := by
  intro p
  cases p with
  | inl f => exact hFR.region_isOpen f.1
  | inr i =>
      fin_cases i <;> simp [splitFacePoolRegion, hsplit.isOpen_left,
        hsplit.isOpen_right]

/-- Preconnectedness of the canonical split-face region assignment. -/
theorem splitFacePoolRegion_preconnected
    (hFR : FaceRegionInvariant M A) (splitFace : M.Face)
    {W U V : Set Plane} (hsplit : IsTwoSidedPartition W U V) :
    ∀ p, IsPreconnected (splitFacePoolRegion hFR splitFace U V p) := by
  intro p
  cases p with
  | inl f => exact hFR.region_preconnected f.1
  | inr i =>
      fin_cases i <;> simp [splitFacePoolRegion, hsplit.preconnected_left,
        hsplit.preconnected_right]

/-- Pairwise disjointness of the canonical split-face region assignment. -/
theorem splitFacePoolRegion_pairwiseDisjoint
    (hFR : FaceRegionInvariant M A) {splitFace : M.Face}
    {R U V : Set Plane} {β : SimpleArc Plane}
    (hface : hFR.regionOfFace splitFace = R)
    (hsplit : IsTwoSidedPartition (regionMinusArc R β) U V) :
    ∀ {p q}, p ≠ q →
      Disjoint (splitFacePoolRegion hFR splitFace U V p)
        (splitFacePoolRegion hFR splitFace U V q) := by
  intro p q hpq
  cases p with
  | inl f =>
      cases q with
      | inl g =>
          apply hFR.region_pairwiseDisjoint
          intro hfg
          exact hpq (congrArg Sum.inl (Subtype.ext hfg))
      | inr i =>
          have hdisjR : Disjoint (hFR.regionOfFace f.1) R := by
            simpa [hface] using hFR.region_pairwiseDisjoint f.2
          fin_cases i
          · simpa [splitFacePoolRegion] using
              hdisjR.mono_right
                (isTwoSidedPartition_left_subset_regionMinusArc hsplit)
          · simpa [splitFacePoolRegion] using
              hdisjR.mono_right
                (isTwoSidedPartition_right_subset_regionMinusArc hsplit)
  | inr i =>
      cases q with
      | inl f =>
          have hdisjR : Disjoint (hFR.regionOfFace f.1) R := by
            simpa [hface] using hFR.region_pairwiseDisjoint f.2
          fin_cases i
          · simpa [splitFacePoolRegion, disjoint_comm] using
              hdisjR.mono_right
                (isTwoSidedPartition_left_subset_regionMinusArc hsplit)
          · simpa [splitFacePoolRegion, disjoint_comm] using
              hdisjR.mono_right
                (isTwoSidedPartition_right_subset_regionMinusArc hsplit)
      | inr j =>
          fin_cases i <;> fin_cases j
          · exact (hpq rfl).elim
          · simpa [splitFacePoolRegion] using hsplit.disjoint
          · simpa [splitFacePoolRegion] using hsplit.disjoint.symm
          · exact (hpq rfl).elim

/-- Injectivity of the canonical split-face region assignment. -/
theorem splitFacePoolRegion_injective
    (hFR : FaceRegionInvariant M A) {splitFace : M.Face}
    {R U V : Set Plane} {β : SimpleArc Plane}
    (hface : hFR.regionOfFace splitFace = R)
    (hsplit : IsTwoSidedPartition (regionMinusArc R β) U V) :
    Function.Injective (splitFacePoolRegion hFR splitFace U V) := by
  intro p q hpq
  by_contra hne
  have hdisj := splitFacePoolRegion_pairwiseDisjoint hFR hface hsplit hne
  cases p with
  | inl f =>
      cases q with
      | inl g =>
          apply hne
          apply congrArg Sum.inl
          apply Subtype.ext
          exact hFR.regionOfFace_injective hpq
      | inr i =>
          fin_cases i
          · obtain ⟨x, hx⟩ := hsplit.nonempty_left
            exact (Set.disjoint_iff.mp hdisj) ⟨hpq.symm ▸ hx, hx⟩
          · obtain ⟨x, hx⟩ := hsplit.nonempty_right
            exact (Set.disjoint_iff.mp hdisj) ⟨hpq.symm ▸ hx, hx⟩
  | inr i =>
      cases q with
      | inl f =>
          fin_cases i
          · obtain ⟨x, hx⟩ := hsplit.nonempty_left
            exact (Set.disjoint_iff.mp hdisj) ⟨hx, hpq ▸ hx⟩
          · obtain ⟨x, hx⟩ := hsplit.nonempty_right
            exact (Set.disjoint_iff.mp hdisj) ⟨hx, hpq ▸ hx⟩
      | inr j =>
          fin_cases i <;> fin_cases j
          · exact hne rfl
          · obtain ⟨x, hx⟩ := hsplit.nonempty_left
            exact (Set.disjoint_iff.mp hdisj) ⟨hx, hpq ▸ hx⟩
          · obtain ⟨x, hx⟩ := hsplit.nonempty_right
            exact (Set.disjoint_iff.mp hdisj) ⟨hx, hpq ▸ hx⟩
          · exact hne rfl

/-- Complement containment for the canonical split-face region assignment after
adding the new arc to the arrangement. -/
theorem splitFacePoolRegion_subset_inserted_compl
    (hFR : FaceRegionInvariant M A) {splitFace : M.Face}
    {R U V : Set Plane} {β : SimpleArc Plane}
    (hArc : ArcInRegion A R β)
    (hface : hFR.regionOfFace splitFace = R)
    (hcarrier : β.carrier ⊆ R ∪ A)
    (hsplit : IsTwoSidedPartition (regionMinusArc R β) U V) :
    ∀ p, splitFacePoolRegion hFR splitFace U V p ⊆ (A ∪ β.carrier)ᶜ := by
  intro p
  cases p with
  | inl f =>
      exact oldFaceRegion_subset_inserted_compl_of_carrier_subset hFR hface hcarrier f
  | inr i =>
      fin_cases i
      · simpa [splitFacePoolRegion] using
          isTwoSidedPartition_left_subset_inserted_compl hArc hsplit
      · simpa [splitFacePoolRegion] using
          isTwoSidedPartition_right_subset_inserted_compl hArc hsplit

/-- Construct the post-insertion invariant from an aligned classification of
inserted face orbits as old unsplit faces plus the two split sides.

This is intentionally not built from cardinality alone: the equivalence must be
the geometric/combinatorial classifier that sends each inserted `facePerm` orbit
to the region it actually bounds. -/
def insertedOfSplitFaceEquiv
    {D : Type*} [Fintype D] [DecidableEq D]
    {M : CombinatorialMap D} {A A' : Set Plane} {c₁ c₂ : D}
    (hFR : FaceRegionInvariant M A) (splitFace : M.Face)
    (U V : Set Plane)
    (faceEquiv :
      (CrossingLemma.EdgeInsertion.insertedEdgeMap M c₁ c₂).Face ≃
        SplitFacePool (M := M) splitFace)
    (hinj : Function.Injective (splitFacePoolRegion hFR splitFace U V))
    (hopen : ∀ p, IsOpen (splitFacePoolRegion hFR splitFace U V p))
    (hpre : ∀ p, IsPreconnected (splitFacePoolRegion hFR splitFace U V p))
    (hcompl : ∀ p, splitFacePoolRegion hFR splitFace U V p ⊆ A'ᶜ)
    (hdisj : ∀ {p q}, p ≠ q →
      Disjoint (splitFacePoolRegion hFR splitFace U V p)
        (splitFacePoolRegion hFR splitFace U V q)) :
    FaceRegionInvariant
      (CrossingLemma.EdgeInsertion.insertedEdgeMap M c₁ c₂) A' :=
  insertedOfFaceRegions M A' c₁ c₂
    (fun f => splitFacePoolRegion hFR splitFace U V (faceEquiv f))
    (by
      intro f g hfg
      exact faceEquiv.injective (hinj hfg))
    (fun f => hopen (faceEquiv f))
    (fun f => hpre (faceEquiv f))
    (fun f => hcompl (faceEquiv f))
    (by
      intro f g hne
      exact hdisj (fun hfg => hne (faceEquiv.injective hfg)))

/-- If two corner darts enter the same registered region, they are on the same
`facePerm` orbit.  This is the corrected replacement for the disconnected
retired `facialCertificate_of_crossingFree` surface: the face-region dictionary
is an explicit hypothesis. -/
theorem sameCycle_of_cornerRegion_eq
    (hFR : FaceRegionInvariant M A) {c₁ c₂ : D}
    (h₁ : hFR.cornerRegion c₁ = R) (h₂ : hFR.cornerRegion c₂ = R) :
    M.facePerm.SameCycle c₁ c₂ := by
  have hregions :
      hFR.regionOfFace (M.Face_mk c₁) = hFR.regionOfFace (M.Face_mk c₂) := by
    calc
      hFR.regionOfFace (M.Face_mk c₁) = hFR.cornerRegion c₁ :=
        (hFR.cornerRegion_eq_face c₁).symm
      _ = R := h₁
      _ = hFR.cornerRegion c₂ := h₂.symm
      _ = hFR.regionOfFace (M.Face_mk c₂) := hFR.cornerRegion_eq_face c₂
  have hfaces : M.Face_mk c₁ = M.Face_mk c₂ :=
    hFR.regionOfFace_injective hregions
  exact Quotient.eq''.mp hfaces

/-- A crosscut insertion certificate for one edge.  It packages the old geometric
crosscut data together with the registered-region facts needed to place the two
attachment corners on one partial-map face. -/
structure CrosscutInsertionCertificate {D : Type*} (M : CombinatorialMap D)
    (A R : Set Plane) (a : SimpleCurveArc) (c₁ c₂ : D) where
  /-- The current partial map has a valid face-region dictionary. -/
  invariant : FaceRegionInvariant M A
  /-- The geometric arc is a crosscut of the registered region. -/
  arcInRegion : ArcInRegion A R (toPlaneArc a)
  /-- The tail attachment corner enters the registered region being split. -/
  tail_corner_region : invariant.cornerRegion c₁ = R
  /-- The head attachment corner enters the registered region being split. -/
  head_corner_region : invariant.cornerRegion c₂ = R

/-- The corrected one-step facial certificate: the geometric/topological content
is carried by `CrosscutInsertionCertificate`, so the Lean proof is just the
face-region dictionary lookup. -/
theorem sameCycle_of_crosscutInsertionCertificate
    {D : Type*} {M : CombinatorialMap D} {A R : Set Plane}
    {a : SimpleCurveArc} {c₁ c₂ : D}
    (hcert : CrosscutInsertionCertificate M A R a c₁ c₂) :
    M.facePerm.SameCycle c₁ c₂ :=
  hcert.invariant.sameCycle_of_cornerRegion_eq
    hcert.tail_corner_region hcert.head_corner_region

/-- Maintenance data for one insertion step.  This is the interface the real
topology packet must produce: after a certified crosscut insertion, the inserted
map has a new face-region dictionary for the enlarged arrangement.

No theorem in this file constructs this data; that construction is exactly the
crosscut/separation maintenance burden. -/
structure InsertionMaintenance {D : Type*} [Fintype D] [DecidableEq D]
    (M : CombinatorialMap D) (A A' R : Set Plane)
    (a : SimpleCurveArc) (c₁ c₂ : D) where
  /-- The old invariant plus the crosscut and corner-region certificate. -/
  certificate : CrosscutInsertionCertificate M A R a c₁ c₂
  /-- The two-sided split of the region being cut by the inserted arc. -/
  split :
    ∃ U V, IsTwoSidedPartition (regionMinusArc R (toPlaneArc a)) U V
  /-- The face-region invariant after the combinatorial insertion. -/
  nextInvariant :
    FaceRegionInvariant
      (CrossingLemma.EdgeInsertion.insertedEdgeMap M c₁ c₂) A'

/-- Maintenance data supplies the facial branch of D1-A. -/
theorem sameCycle_of_insertionMaintenance
    {D : Type*} [Fintype D] [DecidableEq D]
    {M : CombinatorialMap D} {A A' R : Set Plane}
    {a : SimpleCurveArc} {c₁ c₂ : D}
    (hstep : InsertionMaintenance M A A' R a c₁ c₂) :
    M.facePerm.SameCycle c₁ c₂ :=
  sameCycle_of_crosscutInsertionCertificate hstep.certificate

/-- Package one maintenance step once the new face-region dictionary has been
constructed.  This theorem deliberately leaves `hnext` as an explicit input:
building that dictionary is the real topology/coherence obligation. -/
def insertionMaintenance_of_nextInvariant
    {D : Type*} [Fintype D] [DecidableEq D]
    {M : CombinatorialMap D} {A A' R : Set Plane}
    {a : SimpleCurveArc} {c₁ c₂ : D}
    (hFR : FaceRegionInvariant M A)
    (hArc : ArcInRegion A R (toPlaneArc a))
    (hsplit :
      ∃ U V, IsTwoSidedPartition (regionMinusArc R (toPlaneArc a)) U V)
    (htail : hFR.cornerRegion c₁ = R)
    (hhead : hFR.cornerRegion c₂ = R)
    (hnext :
      FaceRegionInvariant
        (CrossingLemma.EdgeInsertion.insertedEdgeMap M c₁ c₂) A') :
    InsertionMaintenance M A A' R a c₁ c₂ where
  certificate :=
    { invariant := hFR
      arcInRegion := hArc
      tail_corner_region := htail
      head_corner_region := hhead }
  split := hsplit
  nextInvariant := hnext

/-- Same as `insertionMaintenance_of_nextInvariant`, but obtains the two-sided
split from the current crosscut theorem.  This introduces no new `sorry`, but it
inherits the existing `exists_twoSidedPartition_of_arc` residual. -/
def insertionMaintenance_of_crosscut_and_nextInvariant
    {D : Type*} [Fintype D] [DecidableEq D]
    {M : CombinatorialMap D} {A A' R : Set Plane}
    {a : SimpleCurveArc} {c₁ c₂ : D}
    (hFR : FaceRegionInvariant M A)
    (hArc : ArcInRegion A R (toPlaneArc a))
    (htail : hFR.cornerRegion c₁ = R)
    (hhead : hFR.cornerRegion c₂ = R)
    (hnext :
      FaceRegionInvariant
        (CrossingLemma.EdgeInsertion.insertedEdgeMap M c₁ c₂) A') :
    InsertionMaintenance M A A' R a c₁ c₂ :=
  insertionMaintenance_of_nextInvariant hFR hArc
    (exists_twoSidedPartition_of_arc hArc) htail hhead hnext

/-- Build one maintenance step directly from a region assignment on the inserted
map's new face orbits.  This is the practical construction surface for the
post-insertion `FaceRegionInvariant`. -/
def insertionMaintenance_of_insertedFaceRegions
    {D : Type*} [Fintype D] [DecidableEq D]
    {M : CombinatorialMap D} {A A' R : Set Plane}
    {a : SimpleCurveArc} {c₁ c₂ : D}
    (hFR : FaceRegionInvariant M A)
    (hArc : ArcInRegion A R (toPlaneArc a))
    (hsplit :
      ∃ U V, IsTwoSidedPartition (regionMinusArc R (toPlaneArc a)) U V)
    (htail : hFR.cornerRegion c₁ = R)
    (hhead : hFR.cornerRegion c₂ = R)
    (regionOfFace :
      (CrossingLemma.EdgeInsertion.insertedEdgeMap M c₁ c₂).Face → Set Plane)
    (hinj : Function.Injective regionOfFace)
    (hopen : ∀ f, IsOpen (regionOfFace f))
    (hpre : ∀ f, IsPreconnected (regionOfFace f))
    (hcompl : ∀ f, regionOfFace f ⊆ A'ᶜ)
    (hdisj : ∀ {f g}, f ≠ g → Disjoint (regionOfFace f) (regionOfFace g)) :
    InsertionMaintenance M A A' R a c₁ c₂ :=
  insertionMaintenance_of_nextInvariant hFR hArc hsplit htail hhead
    (insertedOfFaceRegions M A' c₁ c₂ regionOfFace hinj hopen hpre hcompl hdisj)

/-- Same as `insertionMaintenance_of_insertedFaceRegions`, with the split obtained
from the current crosscut theorem.  It leaves exactly the inserted-face region
assignment and its four invariant facts as inputs. -/
def insertionMaintenance_of_crosscut_and_insertedFaceRegions
    {D : Type*} [Fintype D] [DecidableEq D]
    {M : CombinatorialMap D} {A A' R : Set Plane}
    {a : SimpleCurveArc} {c₁ c₂ : D}
    (hFR : FaceRegionInvariant M A)
    (hArc : ArcInRegion A R (toPlaneArc a))
    (htail : hFR.cornerRegion c₁ = R)
    (hhead : hFR.cornerRegion c₂ = R)
    (regionOfFace :
      (CrossingLemma.EdgeInsertion.insertedEdgeMap M c₁ c₂).Face → Set Plane)
    (hinj : Function.Injective regionOfFace)
    (hopen : ∀ f, IsOpen (regionOfFace f))
    (hpre : ∀ f, IsPreconnected (regionOfFace f))
    (hcompl : ∀ f, regionOfFace f ⊆ A'ᶜ)
    (hdisj : ∀ {f g}, f ≠ g → Disjoint (regionOfFace f) (regionOfFace g)) :
    InsertionMaintenance M A A' R a c₁ c₂ :=
  insertionMaintenance_of_insertedFaceRegions hFR hArc
    (exists_twoSidedPartition_of_arc hArc) htail hhead
    regionOfFace hinj hopen hpre hcompl hdisj

/-- Maintenance constructor from an aligned split-face classifier.  This is the
first surface that has the right mathematical shape for the hard part: classify
the inserted face orbits as old unsplit faces plus the two sides produced by the
crosscut theorem. -/
def insertionMaintenance_of_splitFaceEquiv
    {D : Type*} [Fintype D] [DecidableEq D]
    {M : CombinatorialMap D} {A A' R U V : Set Plane}
    {a : SimpleCurveArc} {c₁ c₂ : D}
    (hFR : FaceRegionInvariant M A) (splitFace : M.Face)
    (hArc : ArcInRegion A R (toPlaneArc a))
    (hsplit : IsTwoSidedPartition (regionMinusArc R (toPlaneArc a)) U V)
    (htail : hFR.cornerRegion c₁ = R)
    (hhead : hFR.cornerRegion c₂ = R)
    (faceEquiv :
      (CrossingLemma.EdgeInsertion.insertedEdgeMap M c₁ c₂).Face ≃
        SplitFacePool (M := M) splitFace)
    (hinj : Function.Injective (splitFacePoolRegion hFR splitFace U V))
    (hopen : ∀ p, IsOpen (splitFacePoolRegion hFR splitFace U V p))
    (hpre : ∀ p, IsPreconnected (splitFacePoolRegion hFR splitFace U V p))
    (hcompl : ∀ p, splitFacePoolRegion hFR splitFace U V p ⊆ A'ᶜ)
    (hdisj : ∀ {p q}, p ≠ q →
      Disjoint (splitFacePoolRegion hFR splitFace U V p)
        (splitFacePoolRegion hFR splitFace U V q)) :
    InsertionMaintenance M A A' R a c₁ c₂ :=
  insertionMaintenance_of_nextInvariant hFR hArc
    ⟨U, V, hsplit⟩ htail hhead
    (insertedOfSplitFaceEquiv hFR splitFace U V faceEquiv
      hinj hopen hpre hcompl hdisj)

/-- Maintenance constructor using the canonical same-face classifier from
`EdgeInsertion.insertedFaceSplitPoolEquiv`.  This removes the arbitrary
`faceEquiv` input in the facial case: the inserted face orbits are classified as
old faces except `M.Face_mk c₁`, plus the two new sides. -/
def insertionMaintenance_of_canonicalSplitFaceEquiv
    {D : Type*} [Fintype D] [DecidableEq D]
    {M : CombinatorialMap D} {A A' R U V : Set Plane}
    {a : SimpleCurveArc} {c₁ c₂ : D}
    (hFR : FaceRegionInvariant M A) (hc : c₁ ≠ c₂)
    (hArc : ArcInRegion A R (toPlaneArc a))
    (hsplit : IsTwoSidedPartition (regionMinusArc R (toPlaneArc a)) U V)
    (htail : hFR.cornerRegion c₁ = R)
    (hhead : hFR.cornerRegion c₂ = R)
    (hinj : Function.Injective (splitFacePoolRegion hFR (M.Face_mk c₁) U V))
    (hopen : ∀ p, IsOpen (splitFacePoolRegion hFR (M.Face_mk c₁) U V p))
    (hpre : ∀ p, IsPreconnected (splitFacePoolRegion hFR (M.Face_mk c₁) U V p))
    (hcompl : ∀ p, splitFacePoolRegion hFR (M.Face_mk c₁) U V p ⊆ A'ᶜ)
    (hdisj : ∀ {p q}, p ≠ q →
      Disjoint (splitFacePoolRegion hFR (M.Face_mk c₁) U V p)
        (splitFacePoolRegion hFR (M.Face_mk c₁) U V q)) :
    InsertionMaintenance M A A' R a c₁ c₂ :=
  insertionMaintenance_of_splitFaceEquiv hFR (M.Face_mk c₁) hArc hsplit htail hhead
    (CrossingLemma.EdgeInsertion.insertedFaceSplitPoolEquiv M c₁ c₂ hc
      (sameCycle_of_crosscutInsertionCertificate
        { invariant := hFR
          arcInRegion := hArc
          tail_corner_region := htail
          head_corner_region := hhead }))
    hinj hopen hpre hcompl hdisj

/-- Canonical maintenance constructor for a genuine crosscut split.  Once the
two sides `U,V` are supplied, this proves all post-split region-pool facts
mechanically.  The only geometric input beyond the maintained old invariant is
the two-sided split; the carrier-containment side condition is derived from
`ArcInRegion`. -/
def insertionMaintenance_of_canonicalCrosscut
    {D : Type*} [Fintype D] [DecidableEq D]
    {M : CombinatorialMap D} {A R U V : Set Plane}
    {a : SimpleCurveArc} {c₁ c₂ : D}
    (hFR : FaceRegionInvariant M A) (hc : c₁ ≠ c₂)
    (hArc : ArcInRegion A R (toPlaneArc a))
    (hsplit : IsTwoSidedPartition (regionMinusArc R (toPlaneArc a)) U V)
    (htail : hFR.cornerRegion c₁ = R)
    (hhead : hFR.cornerRegion c₂ = R) :
    InsertionMaintenance M A (A ∪ (toPlaneArc a).carrier) R a c₁ c₂ := by
  have hface : hFR.regionOfFace (M.Face_mk c₁) = R := by
    calc
      hFR.regionOfFace (M.Face_mk c₁) = hFR.cornerRegion c₁ :=
        (hFR.cornerRegion_eq_face c₁).symm
      _ = R := htail
  exact insertionMaintenance_of_canonicalSplitFaceEquiv hFR hc hArc hsplit htail hhead
    (splitFacePoolRegion_injective hFR hface hsplit)
    (splitFacePoolRegion_isOpen hFR (M.Face_mk c₁) hsplit)
    (splitFacePoolRegion_preconnected hFR (M.Face_mk c₁) hsplit)
    (splitFacePoolRegion_subset_inserted_compl hFR hArc hface
      (arcInRegion_carrier_subset_region_union_arrangement hArc) hsplit)
    (splitFacePoolRegion_pairwiseDisjoint hFR hface hsplit)

/-- Canonical maintenance constructor with the two-sided split chosen from the
current crosscut theorem.  This is a sound replacement for the old disconnected
retired `facialCertificate_of_crossingFree` surface, but it inherits the tracked
`exists_twoSidedPartition_of_arc` residual. -/
noncomputable def insertionMaintenance_of_canonicalCrosscut_exists
    {D : Type*} [Fintype D] [DecidableEq D]
    {M : CombinatorialMap D} {A R : Set Plane}
    {a : SimpleCurveArc} {c₁ c₂ : D}
    (hFR : FaceRegionInvariant M A) (hc : c₁ ≠ c₂)
    (hArc : ArcInRegion A R (toPlaneArc a))
    (htail : hFR.cornerRegion c₁ = R)
    (hhead : hFR.cornerRegion c₂ = R) :
    InsertionMaintenance M A (A ∪ (toPlaneArc a).carrier) R a c₁ c₂ := by
  classical
  let hUV := exists_twoSidedPartition_of_arc hArc
  let U : Set Plane := Classical.choose hUV
  let hV : ∃ V, IsTwoSidedPartition (regionMinusArc R (toPlaneArc a)) U V :=
    Classical.choose_spec hUV
  let V : Set Plane := Classical.choose hV
  have hsplit : IsTwoSidedPartition (regionMinusArc R (toPlaneArc a)) U V :=
    Classical.choose_spec hV
  exact insertionMaintenance_of_canonicalCrosscut hFR hc hArc hsplit htail hhead

/-- A maintained face-region invariant puts the insertion in D1-A's facial
branch, so the Euler characteristic is preserved. -/
theorem eulerCharacteristic_insertedEdgeMap_of_insertionMaintenance
    {D : Type*} [Fintype D] [DecidableEq D]
    {M : CombinatorialMap D} {A A' R : Set Plane}
    {a : SimpleCurveArc} {c₁ c₂ : D} (hc : c₁ ≠ c₂)
    (hstep : InsertionMaintenance M A A' R a c₁ c₂) :
    (CrossingLemma.EdgeInsertion.insertedEdgeMap M c₁ c₂).eulerCharacteristic
      = M.eulerCharacteristic :=
  CrossingLemma.EdgeInsertion.eulerCharacteristic_insertedEdgeMap_of_sameCycle
    M c₁ c₂ hc (sameCycle_of_insertionMaintenance hstep)

/-- One-step Euler preservation for a certified crosscut insertion, modulo the
tracked crosscut split residual `exists_twoSidedPartition_of_arc`. -/
theorem eulerCharacteristic_insertedEdgeMap_of_canonicalCrosscut
    {D : Type*} [Fintype D] [DecidableEq D]
    {M : CombinatorialMap D} {A R : Set Plane}
    {a : SimpleCurveArc} {c₁ c₂ : D} (hc : c₁ ≠ c₂)
    (hFR : FaceRegionInvariant M A)
    (hArc : ArcInRegion A R (toPlaneArc a))
    (htail : hFR.cornerRegion c₁ = R)
    (hhead : hFR.cornerRegion c₂ = R) :
    (CrossingLemma.EdgeInsertion.insertedEdgeMap M c₁ c₂).eulerCharacteristic
      = M.eulerCharacteristic :=
  eulerCharacteristic_insertedEdgeMap_of_insertionMaintenance hc
    (insertionMaintenance_of_canonicalCrosscut_exists hFR hc hArc htail hhead)

end FaceRegionInvariant

/-! ## 6. Generic maintained-invariant tower

The one-step constructor above is local.  The residual-map theorem needs an
iterated tower of such insertions, followed by an isomorphism from the tower's top
map to the monolithic `residualMap`.  The declarations in this section prove the
Euler part of that assembly once the tower data is supplied explicitly.

This is intentionally a theorem over data, not a hidden construction: the
remaining hard work is to build `ResidualFaceRegionTower` from a crossing-free
drawing. -/

/-- A partial drawing state in a face-region insertion tower.  It bundles the
dart type, the partial combinatorial map, the placed arrangement, and the
maintained face-region invariant for that arrangement. -/
structure FaceRegionTowerState where
  /-- Dart carrier of the partial map. -/
  Dart : Type
  /-- Finiteness of the dart carrier. -/
  [fintypeDart : Fintype Dart]
  /-- Decidable equality on darts, needed by `insertedEdgeMap`. -/
  [decidableEqDart : DecidableEq Dart]
  /-- The partial combinatorial map. -/
  map : CombinatorialMap Dart
  /-- The currently placed geometric arrangement. -/
  arrangement : Set Plane
  /-- Maintained dictionary from map faces to complementary regions. -/
  invariant : FaceRegionInvariant map arrangement

attribute [instance] FaceRegionTowerState.fintypeDart
attribute [instance] FaceRegionTowerState.decidableEqDart

/-- One maintained tower step.  It says that the next state is isomorphic to the
canonical `insertedEdgeMap` at the two registered corners, and it supplies the
crosscut split used to maintain the face-region dictionary. -/
structure FaceRegionTowerStep (S T : FaceRegionTowerState) where
  /-- The old complementary region split by the new arc. -/
  region : Set Plane
  /-- The left side of the split region. -/
  leftSide : Set Plane
  /-- The right side of the split region. -/
  rightSide : Set Plane
  /-- The inserted edge arc. -/
  arc : SimpleCurveArc
  /-- First attachment corner in the old map. -/
  c₁ : S.Dart
  /-- Second attachment corner in the old map. -/
  c₂ : S.Dart
  /-- The two attachment corners are distinct. -/
  corners_ne : c₁ ≠ c₂
  /-- The inserted arc is a crosscut of the registered old region. -/
  arcInRegion : ArcInRegion S.arrangement region (toPlaneArc arc)
  /-- The supplied two-sided split of the crossed region. -/
  split :
    IsTwoSidedPartition (regionMinusArc region (toPlaneArc arc)) leftSide rightSide
  /-- The first corner enters the split region. -/
  tail_corner_region : S.invariant.cornerRegion c₁ = region
  /-- The second corner enters the split region. -/
  head_corner_region : S.invariant.cornerRegion c₂ = region
  /-- The next state's arrangement is the old arrangement plus the new arc. -/
  arrangement_eq : T.arrangement = S.arrangement ∪ (toPlaneArc arc).carrier
  /-- The next state's map is the canonical inserted map, up to dart relabelling. -/
  mapIso :
    CombinatorialMap.Iso
      (CrossingLemma.EdgeInsertion.insertedEdgeMap S.map c₁ c₂) T.map

namespace FaceRegionTowerStep

/-- The explicit one-step maintenance data carried by a `FaceRegionTowerStep`. -/
noncomputable def insertionMaintenance {S T : FaceRegionTowerState}
    (hstep : FaceRegionTowerStep S T) :
    FaceRegionInvariant.InsertionMaintenance S.map S.arrangement
      (S.arrangement ∪ (toPlaneArc hstep.arc).carrier) hstep.region hstep.arc
      hstep.c₁ hstep.c₂ :=
  FaceRegionInvariant.insertionMaintenance_of_canonicalCrosscut
    S.invariant hstep.corners_ne hstep.arcInRegion hstep.split
    hstep.tail_corner_region hstep.head_corner_region

/-- One maintained tower step preserves Euler characteristic, after transporting
through the supplied isomorphism to the next state. -/
theorem eulerCharacteristic_eq {S T : FaceRegionTowerState}
    (hstep : FaceRegionTowerStep S T) :
    T.map.eulerCharacteristic = S.map.eulerCharacteristic := by
  have hfac :
      (CrossingLemma.EdgeInsertion.insertedEdgeMap S.map hstep.c₁ hstep.c₂).eulerCharacteristic
        = S.map.eulerCharacteristic :=
    FaceRegionInvariant.eulerCharacteristic_insertedEdgeMap_of_insertionMaintenance
      hstep.corners_ne hstep.insertionMaintenance
  have hiso :
      (CrossingLemma.EdgeInsertion.insertedEdgeMap S.map hstep.c₁ hstep.c₂).eulerCharacteristic
        = T.map.eulerCharacteristic :=
    eulerChar_iso_invariant hstep.mapIso
  exact hiso.symm.trans hfac

end FaceRegionTowerStep

/-- A heterogeneous tower relation generated by maintained face-region insertion
steps.  `FaceRegionEulerTower S T` means `T` is obtained from `S` by finitely many
maintained insertions. -/
inductive FaceRegionEulerTower : FaceRegionTowerState → FaceRegionTowerState → Prop
  /-- The empty tower. -/
  | refl (S : FaceRegionTowerState) : FaceRegionEulerTower S S
  /-- Append one maintained insertion step. -/
  | snoc {S T U : FaceRegionTowerState} :
      FaceRegionEulerTower S T → FaceRegionTowerStep T U → FaceRegionEulerTower S U

/-- Every maintained face-region insertion tower preserves Euler characteristic. -/
theorem eulerCharacteristic_eq_of_faceRegionEulerTower
    {S T : FaceRegionTowerState} (htower : FaceRegionEulerTower S T) :
    T.map.eulerCharacteristic = S.map.eulerCharacteristic := by
  induction htower with
  | refl => rfl
  | snoc htower hstep ih =>
      exact (FaceRegionTowerStep.eulerCharacteristic_eq hstep).trans ih

/-- The exact tower witness needed to prove `χ = 2` for a residual map.  The base
state is a one-face tree map, the tower consists of maintained crosscut
insertions, and the top state is isomorphic to the monolithic residual map. -/
structure ResidualFaceRegionTower (G : DrawnMultigraph)
    (hARR : ArcsRotationRegular G) where
  /-- Base state of the insertion tower. -/
  base : FaceRegionTowerState
  /-- Top state of the insertion tower. -/
  top : FaceRegionTowerState
  /-- The maintained insertion tower from base to top. -/
  tower : FaceRegionEulerTower base top
  /-- The base map has a single face. -/
  base_oneFace : Fintype.card base.map.Face = 1
  /-- The base map has the tree edge count. -/
  base_tree : Fintype.card base.map.Edge + 1 = Fintype.card base.map.Vertex
  /-- The tower top is the monolithic residual map, up to dart relabelling. -/
  topIso : CombinatorialMap.Iso top.map (residualMap G hARR)

/-- A maintained insertion tower proves the residual map has Euler characteristic
`2`.  This is the sound replacement target for the old monolithic obstruction:
all remaining geometry and coherence are isolated in the construction of
`ResidualFaceRegionTower`. -/
theorem eulerChar_residualMap_eq_two_of_faceRegionTower
    (G : DrawnMultigraph) (hARR : ArcsRotationRegular G)
    (htower : ResidualFaceRegionTower G hARR) :
    (residualMap G hARR).eulerCharacteristic = 2 := by
  have hbase :
      htower.base.map.eulerCharacteristic = 2 :=
    eulerChar_eq_two_of_oneFace_tree htower.base.map
      htower.base_oneFace htower.base_tree
  have htowerχ :
      htower.top.map.eulerCharacteristic = htower.base.map.eulerCharacteristic :=
    eulerCharacteristic_eq_of_faceRegionEulerTower htower.tower
  have hiso :
      htower.top.map.eulerCharacteristic =
        (residualMap G hARR).eulerCharacteristic :=
    eulerChar_iso_invariant htower.topIso
  exact hiso.symm.trans (htowerχ.trans hbase)

/-! ## Live tower construction obligation

The old `facialCertificate_of_crossingFree` declaration was removed from the live
surface because its signature was disconnected from the partial map it tried to
certify.  The live route now asks directly for the maintained tower data whose
fields express the missing dictionary and coherence. -/

/-- **Live BR-3b obligation — build the maintained residual tower.**

From a crossing-free, graph-connected drawing with a regular angular rotation
structure, construct the `ResidualFaceRegionTower` witness consumed by
`eulerChar_residualMap_eq_two_of_faceRegionTower`.

This is the remaining hard construction.  It must build:
* a one-face tree base map;
* a finite sequence of `FaceRegionTowerStep`s whose crosscut data maintains the
  face-region invariant;
* the rotation-splice coherence aligning the iterated `insertedEdgeMap` tower
  with the angular `vertexRotation`;
* the final dart-reindexing `Iso` from the tower top to `residualMap G hARR`. -/
noncomputable def residualFaceRegionTower_of_crossingFree (G : DrawnMultigraph)
    (hARR : ArcsRotationRegular G) (hCF : CrossingFree G) (hconn : G.GraphConnected) :
    ResidualFaceRegionTower G hARR := by
  -- OBSTRUCTION: construct the maintained insertion tower described above.
  sorry

/-- Under crossing-freeness and graph-connectivity, the residual combinatorial
map has Euler characteristic exactly `2`.  The proof is now routed only through
the explicit maintained-tower obligation
`residualFaceRegionTower_of_crossingFree`. -/
theorem eulerChar_residualMap_eq_two (G : DrawnMultigraph)
    (hARR : ArcsRotationRegular G) (hCF : CrossingFree G) (hconn : G.GraphConnected) :
    (residualMap G hARR).eulerCharacteristic = 2 :=
  eulerChar_residualMap_eq_two_of_faceRegionTower G hARR
    (residualFaceRegionTower_of_crossingFree G hARR hCF hconn)

/-! ## Assembled target -/

/-- **BR-3b (lower bound) — target, carries the tower-construction obligation.**

A crossing-free, graph-connected plane drawing's residual combinatorial map has
Euler characteristic `≥ 2`.

Read off `χ = 2` from `eulerChar_residualMap_eq_two`, which is routed through
`residualFaceRegionTower_of_crossingFree`.

This theorem is **NOT axiom-clean** until the tower-construction obligation is
proved.  Axiom status is verified centrally; do not assert cleanliness from this
file. -/
theorem two_le_eulerChar_of_crossingFree (G : DrawnMultigraph)
    (hARR : ArcsRotationRegular G) (hCF : CrossingFree G) (hconn : G.GraphConnected) :
    2 ≤ (residualMap G hARR).eulerCharacteristic := by
  rw [eulerChar_residualMap_eq_two G hARR hCF hconn]

/-- **Corollary — χ = 2 for a crossing-free connected drawing.**  The lower bound
of this file meeting the sorry-free upper bound BR-3a.  Carries the same
tower-construction `sorry` as the lower bound. -/
theorem eulerChar_eq_two_of_crossingFree (G : DrawnMultigraph)
    (hARR : ArcsRotationRegular G) (hCF : CrossingFree G) (hconn : G.GraphConnected) :
    (residualMap G hARR).eulerCharacteristic = 2 := by
  have hle : (residualMap G hARR).eulerCharacteristic ≤ 2 :=
    CombinatorialMap.eulerCharacteristic_le_two (residualMap G hARR)
      (residualMap_connected G hARR hconn)
  have hge : 2 ≤ (residualMap G hARR).eulerCharacteristic :=
    two_le_eulerChar_of_crossingFree G hARR hCF hconn
  omega

open Classical in
/-- The number of endpoint-pairs present in the abstractized drawing is bounded
by the number of residual-map edge classes. -/
theorem abstractize_edgePairs_card_le_residualMap_edge_card
    (G : DrawnMultigraph) (hARR : ArcsRotationRegular G) :
    (Finset.univ.image (abstractize G).edgeVerts).card ≤
      Fintype.card (residualMap G hARR).Edge := by
  have hle :
      (Finset.univ.image (abstractize G).edgeVerts).card ≤
        Fintype.card (abstractize G).Edge :=
    Finset.card_image_le
  rw [abstractize_edge_card G] at hle
  rw [residualMap_edge_card G hARR]
  exact hle

open Classical in
/-- If every listed drawing vertex has an incident dart, the residual-map vertex
count matches the abstractized drawing's vertex count. -/
theorem residualMap_vertex_card_eq_abstractize_of_incident
    (G : DrawnMultigraph) (hARR : ArcsRotationRegular G)
    (hincident : ∀ p : ↥G.V, ∃ d : Fin G.numEdges × Bool,
      d ∈ incidentEnds G (p : ℝ × ℝ)) :
    Fintype.card (residualMap G hARR).Vertex =
      Fintype.card (abstractize G).Vertex := by
  rw [residualMap_vertex_card_of_incident G hARR hincident,
    abstractize_vertex_card G]
  exact Fintype.card_coe G.V

/-- A connected drawing with at least two listed vertices has the residual
vertex count required by the abstractized drawing. -/
theorem residualMap_vertex_card_eq_abstractize_of_graphConnected
    (G : DrawnMultigraph) (hARR : ArcsRotationRegular G)
    (hconn : G.GraphConnected) (hcard : 2 ≤ Fintype.card ↥G.V) :
    Fintype.card (residualMap G hARR).Vertex =
      Fintype.card (abstractize G).Vertex :=
  residualMap_vertex_card_eq_abstractize_of_incident G hARR
    (incidentCoverage_of_graphConnected_of_two_le G hconn hcard)

open Classical in
/-- Package a residual tower into the planarization witness consumed by the
abstract planar multigraph edge bound.

The only remaining non-topological card bookkeeping left explicit here is the
nontrivial vertex-count lower bound that rules out isolated singleton drawings. -/
theorem hasGenusZeroSimplePlanarization_of_residualFaceRegionTower
    (G : DrawnMultigraph) (hARR : ArcsRotationRegular G)
    (htower : ResidualFaceRegionTower G hARR)
    (hconn : G.GraphConnected)
    (hloop : ∀ e : Fin G.numEdges, (G.endpoints e).1 ≠ (G.endpoints e).2)
    (hpar : ∀ e e' : Fin G.numEdges,
      s((G.endpoints e).1, (G.endpoints e).2)
        = s((G.endpoints e').1, (G.endpoints e').2) → e = e')
    (hcard : 2 ≤ Fintype.card ↥G.V) :
    HasGenusZeroSimplePlanarization (abstractize G) := by
  refine ⟨Fin G.numEdges × Bool, inferInstance, residualMap G hARR, ?_, ?_, ?_, ?_, ?_⟩
  · exact residualMap_isSimple G hARR hloop hpar
  · exact residualMap_connected G hARR hconn
  · exact eulerChar_residualMap_eq_two_of_faceRegionTower G hARR htower
  · exact residualMap_vertex_card_eq_abstractize_of_graphConnected G hARR hconn hcard
  · exact abstractize_edgePairs_card_le_residualMap_edge_card G hARR

open Classical in
/-- Crossing-free version of the planarization witness, still gated on the live
residual-tower construction and a nontrivial vertex-count lower bound. -/
theorem hasGenusZeroSimplePlanarization_of_crossingFree
    (G : DrawnMultigraph) (hARR : ArcsRotationRegular G)
    (hCF : CrossingFree G) (hconn : G.GraphConnected)
    (hloop : ∀ e : Fin G.numEdges, (G.endpoints e).1 ≠ (G.endpoints e).2)
    (hpar : ∀ e e' : Fin G.numEdges,
      s((G.endpoints e).1, (G.endpoints e).2)
        = s((G.endpoints e').1, (G.endpoints e').2) → e = e')
    (hcard : 2 ≤ Fintype.card ↥G.V) :
    HasGenusZeroSimplePlanarization (abstractize G) :=
  hasGenusZeroSimplePlanarization_of_residualFaceRegionTower G hARR
    (residualFaceRegionTower_of_crossingFree G hARR hCF hconn)
    hconn hloop hpar hcard

open Classical in
/-- Downstream-facing crossing-free planarization witness.  The planar multigraph
edge theorem already assumes `3 ≤ card (abstractize G).Vertex`; this wrapper
derives the weaker nontriviality bound needed for residual vertex bookkeeping. -/
theorem hasGenusZeroSimplePlanarization_of_crossingFree_of_three_le
    (G : DrawnMultigraph) (hARR : ArcsRotationRegular G)
    (hCF : CrossingFree G) (hconn : G.GraphConnected)
    (hloop : ∀ e : Fin G.numEdges, (G.endpoints e).1 ≠ (G.endpoints e).2)
    (hpar : ∀ e e' : Fin G.numEdges,
      s((G.endpoints e).1, (G.endpoints e).2)
        = s((G.endpoints e').1, (G.endpoints e').2) → e = e')
    (hvertex : 3 ≤ Fintype.card (abstractize G).Vertex) :
    HasGenusZeroSimplePlanarization (abstractize G) := by
  have hcard : 2 ≤ Fintype.card ↥G.V := by
    have hcard_abs : 2 ≤ Fintype.card (abstractize G).Vertex := by omega
    rw [abstractize_vertex_card G] at hcard_abs
    simpa [Fintype.card_coe] using hcard_abs
  exact hasGenusZeroSimplePlanarization_of_crossingFree G hARR hCF hconn
    hloop hpar hcard

open Classical in
/-- Crossing-free drawn multigraph edge bound in drawing vocabulary.  This is the
direct consumer of the genus-zero planarization witness and the abstract
planar-multigraph edge theorem. -/
theorem crossingFree_drawnMultigraph_edge_bound
    (G : DrawnMultigraph) (M : ℕ) (hARR : ArcsRotationRegular G)
    (hCF : CrossingFree G) (hconn : G.GraphConnected)
    (hloop : ∀ e : Fin G.numEdges, (G.endpoints e).1 ≠ (G.endpoints e).2)
    (hpar : ∀ e e' : Fin G.numEdges,
      s((G.endpoints e).1, (G.endpoints e).2)
        = s((G.endpoints e').1, (G.endpoints e').2) → e = e')
    (hmult : ∀ p q, G.multiplicity p q ≤ M)
    (hvertex : 3 ≤ Fintype.card (abstractize G).Vertex) :
    G.numEdges ≤ M * (3 * G.V.card - 6) := by
  have hpl : HasGenusZeroSimplePlanarization (abstractize G) :=
    hasGenusZeroSimplePlanarization_of_crossingFree_of_three_le G hARR
      hCF hconn hloop hpar hvertex
  have hbound :=
    planar_multigraph_edge_bound (abstractize G) M hpl
      (abstractize_pairMultiplicityBound G M hmult) hvertex
  rw [abstractize_edge_card G, abstractize_vertex_card G] at hbound
  exact hbound

end CrossingLemma.PDZ
