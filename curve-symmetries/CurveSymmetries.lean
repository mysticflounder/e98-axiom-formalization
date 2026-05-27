/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

/-!
# Symmetries of plane algebraic curves

Formalization of **§2.3 ("Symmetries of curves")** of Pach–de Zeeuw, "Distinct
distances on algebraic curves in the plane":

* **Lemma 2.5.** An irreducible plane algebraic curve of degree `d` has at most
  `4d` symmetries (isometries of `ℝ²` that fix it), unless it is a line or a
  circle.
* **Lemma 2.6.** The affine transformations that fix a conic, classified up to a
  rotation or translation (the hyperbola / ellipse / parabola normal forms).

These feed §4: Lemma 2.5 gives `|Γ₀| ≤ 4dm` in the symmetry branch of Lemma 3.2,
and Lemma 2.6 drives the conic case of Lemma 4.3. Lemma 2.5's proof invokes
Bézout's inequality (Theorem 2.1, from the sibling `bezout` module): a symmetry
fixing infinitely many points of an irreducible curve must fix the curve.

This root aggregator wires in modules as they land; see `PLAN.md`.
-/
