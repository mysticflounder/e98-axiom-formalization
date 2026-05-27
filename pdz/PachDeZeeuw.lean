/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

/-!
# Distinct distances on algebraic curves (Pach--de Zeeuw), Theorem 1.1

Standalone formalization of **Theorem 1.1 only**: a plane algebraic curve of
degree `d` containing no line or circle determines `≥ c_d · n^{4/3}` distinct
distances among any `n` of its points.

This root aggregator imports the project's modules. Modules are wired in as
they are ported off the `Erdos98Proof.*` dependency tree onto Mathlib; see
`PLAN.md` for the port order and the live frontier.
-/

-- Ported modules (uncomment as each lands sorry-free on the Mathlib-only base):
-- import PachDeZeeuw.CurveInterface
-- import PachDeZeeuw.Basic
-- import PachDeZeeuw.AuxiliaryCurves
-- import PachDeZeeuw.Theorem12
-- import PachDeZeeuw.IncidenceBound
-- import PachDeZeeuw.Theorem11
-- import PachDeZeeuw.Audit
