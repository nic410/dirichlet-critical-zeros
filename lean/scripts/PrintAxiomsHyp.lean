/-
`#print axioms` for the classical inputs proved in `Families/Hyp/*` and the `Zeta23` declarations they use.
Run (after `lake build`):  lake env lean scripts/PrintAxiomsHyp.lean
Expected: every line `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
-/
import Families.Hyp.Reduced

-- the three discharged classical inputs
#print axioms Families.Hyp.MV_LargeSieve_proof
#print axioms Families.Hyp.mvAdd_proof
#print axioms Families.Hyp.mvMult_of_add
#print axioms Families.Hyp.StirlingDigamma_proof
#print axioms Families.Hyp.PNT_dlVP_proof
-- the reduced bundle
#print axioms Families.ClassicalInputsReduced.toFull
-- the `Zeta23` declarations used
#print axioms Zeta23.StirlingVert.re_digamma_stirling'
#print axioms Zeta23.MuFields.re_digamma_vertical
#print axioms Zeta23.MuFields.re_digamma_mono
#print axioms Zeta23.MuFields.abscissa_mem
#print axioms Zeta23.MuFields.trigamma_tail_le
#print axioms Zeta23.MuFields.summable_quarter_line
#print axioms Zeta23.Stirling.differentiableAt_digamma
#print axioms Zeta23.Stirling.hasSum_trigamma
#print axioms MediumPNT
-- the statements, for the record
example : Families.MV_LargeSieve := Families.Hyp.MV_LargeSieve_proof
example : Families.StirlingDigamma := Families.Hyp.StirlingDigamma_proof
example : Families.PNT_dlVP := Families.Hyp.PNT_dlVP_proof
