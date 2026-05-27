/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

/-!
# The Oleĭnik–Petrovskiĭ–Milnor–Thom connected-components bound

Formalization of **Theorem 2.2** of Pach–de Zeeuw, "Distinct distances on
algebraic curves in the plane":

> **Theorem 2.2.** A zero set in `ℝ^D` defined by polynomials of degree at most
> `d` has at most `(2d)^D` connected components.

"Connected component" is meant in the Euclidean topology on `ℝ^D` (not an
irreducible component). The bound is due to Oleĭnik–Petrovskiĭ, Milnor, and Thom
(exposition in [2, Chapter 7]).

The paper uses Theorem 2.2 as a real substitute for complex Bézout in `ℝ^D`,
where the naive product-of-degrees bound on the size of a finite zero set can
fail. When an intersection of real zero sets is finite, each point is its own
connected component, so `(2d)^D` bounds the number of points — this is how
`|C_ij ∩ C_kl| ≤ 16d⁴` is obtained in Lemma 3.3 (with `D = 4`).

This root aggregator wires in modules as they land; see `PLAN.md`.
-/
