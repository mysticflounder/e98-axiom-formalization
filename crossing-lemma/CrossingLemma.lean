/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

/-!
# The multigraph crossing lemma

Self-contained formalization of the crossing inequality (Székely /
Ajtai–Chvátal–Newborn–Szemerédi, multigraph form), proved via combinatorial
maps and the planar Euler bound. Depends only on Mathlib.

Consumed by the `pdz` project (distinct distances on algebraic curves) to
discharge its incidence bound. The public surface is the frozen crossing
inequality statement plus its proof.

This root aggregator wires in modules as they are ported off the
`Erdos98Proof.*` namespace onto a Mathlib-only base; see `PLAN.md`.
-/

-- Ported modules (uncomment as each lands on the Mathlib-only base):
-- Statement + amplification:
-- import CrossingLemma.CrossingLemma
-- import CrossingLemma.CrossingLemmaAmplification
-- Combinatorial-map / Euler machinery (the 5 files to vendor in):
-- import CrossingLemma.CombinatorialMap
-- import CrossingLemma.CombinatorialMapEdgeInsertion
-- import CrossingLemma.CombinatorialMapEulerBound
-- import CrossingLemma.PlaneArcSeparation
-- import CrossingLemma.PlanarEdgeBound
-- Drawing -> abstract bridge + residual map:
-- import CrossingLemma.Abstractize
-- import CrossingLemma.ResidualMap
-- import CrossingLemma.ResidualMapProperties
-- import CrossingLemma.RotationCoherence
-- import CrossingLemma.CrossingFreeEuler
