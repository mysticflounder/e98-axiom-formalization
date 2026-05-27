/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

/-!
# Bézout's inequality in the plane

Formalization of **Theorem 2.1** of Pach–de Zeeuw, "Distinct distances on
algebraic curves in the plane":

> **Theorem 2.1 (Bézout's inequality).** Two algebraic curves in `ℝ²` with
> degrees `d₁` and `d₂` have at most `d₁ · d₂` intersection points, unless they
> have a common component.

Here a curve of degree `d` is `Z_ℝ(f)` for a polynomial `f` of total degree
`≤ d` (§2.1 of the paper); a common component is a shared positive-dimensional
factor. The paper cites this as a classical input ([10, Lemma 14.4]); this
module is where it is established for the real affine plane.

Theorem 2.1 is the workhorse intersection bound of the whole development: it
underlies Lemma 2.5 (symmetries), Lemma 3.6, Lemmas 4.1–4.3, and the
finite-intersection counts feeding the §3 incidence assembly.

This root aggregator wires in modules as they land; see `PLAN.md` for the
resultant-based proof route.
-/
