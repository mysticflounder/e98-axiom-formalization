# incidence-assembly — plan

## Scope

The project's wiring layer. It contains **only** glue that connects the
paper-faithful modules; no paper statement is restated or reformulated here. Its
job is to close Pach–de Zeeuw Theorem 1.1 and to localize the two open gaps.

## Gap B — the §3 incidence assembly (`positiveAuxiliaryIncidenceCardBound_of_corollary24`)

Reduce `PachDeZeeuw.PDZ.PositiveAuxiliaryIncidenceCardBoundStatement` to
`PachSharir.Corollary24Statement`. Steps, all currently behind one `sorry`:

1. Instantiate Corollary 2.4 at `D = 4` (the auxiliary curves live in `ℝ⁴`).
2. Present each auxiliary curve `C_ij` as an `IsAlgebraicCurveDefinedBy 4 e d`
   curve (the three defining equations from `pdz`'s `auxCurve`).
3. Establish the two-degrees-of-freedom system with multiplicity `M = 16d⁴`
   (Lemmas 3.2–3.4): the partition of `P, Γ` into 2-DoF subsystems.
4. Apply Corollary 2.4 to each subsystem and reassemble (Lemmas 3.5–3.7).
5. Convert the paper's real-valued `max{|P|^{2/3}|Γ|^{2/3}, |P|, |Γ|}` bound into
   pdz's cubed-integer `(auxIncidences X).card ^ 3 ≤ C * (|P₁|·|P₂|)^4`.

Step 5 is pure arithmetic wiring (real → ℕ cubed); it must stay here, not in
`pach-sharir`. Steps 1–4 are the substantive §3 mathematics and transitively pull
in `bezout` (Theorem 2.1), `milnor-thom` (Theorem 2.2, for `M = 16d⁴`), and
`curve-symmetries` (Lemma 2.5, for Lemma 3.2).

## Dependency on Gap A

Step 4 consumes `PachSharir.corollary24`. Until Gap A is discharged, the closed
theorem rests on it; the `h : Corollary24Statement` hypothesis records the
dependency at the type level even while the body is `sorry`.

## Status

Wiring scaffolded and building. `pdz` is `sorry`-free; the closed theorem
`pachDeZeeuwTheorem11_unconditional` carries exactly Gap A (in `pach-sharir`) and
Gap B (here).
