/-
`#print axioms` for the declarations reported as proved (run with
`lake env lean Families/Phase1/A/Axioms.lean` after `lake build Families.Phase1.A.LocalC`).
-/
import Families.Phase1.A.LocalC

open Families Families.Phase1.A

-- toolkit
#print axioms Families.Phase1.A.aptv
#print axioms Families.Phase1.A.integral_k0
#print axioms Families.Phase1.A.eVariationOn_k0_le
#print axioms Families.Phase1.A.sum_inv_totient_le
#print axioms Families.Phase1.A.sum_sqfree_card_divisors_div_totient_le'
-- the twisted spoke count and `prop:count`
#print axioms Families.Phase1.A.spoke_count
#print axioms Families.Phase1.A.main_term
#print axioms Families.Phase1.A.twisted_count_core
#print axioms Families.Phase1.A.twistedCount
#print axioms Families.Phase1.A.propCount_proof
-- `lem:C`
#print axioms Families.Phase1.A.natConv_decomp
#print axioms Families.Phase1.A.sum_rhoTwist_eq
#print axioms Families.Phase1.A.rhoTwist_mQ_le
#print axioms Families.Phase1.A.ae_pullback_inv
#print axioms Families.Phase1.A.lemC_fixed
#print axioms Families.Phase1.A.lemC_exponents
#print axioms Families.Phase1.A.lemC_of
#print axioms Families.Phase1.A.lemC_of_lemfS

-- the target statements, for the record
example : propCount_Statement := Families.Phase1.A.propCount_proof
example (hΩ : lemOmega_ac_Statement) (hfS : lemfS_Statement) : lemC_Statement :=
  Families.Phase1.A.lemC_of_lemfS hΩ hfS
