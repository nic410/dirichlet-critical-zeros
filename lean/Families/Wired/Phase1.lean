/-
Wiring of the proofs in `Families/Phase1/` into the theorems for the statements of `Families.LemmaA` and
`Families.LemmaC`. The statements are defined there; only their proofs are supplied here.

* `lemOmega_ac`, `lemDual`             — `Families/Phase1/B/*`
* `propCount`, `lemC`                  — `Families/Phase1/A/*`, `lemC` using `lem:fS`(i)
* `propSharpLS`                        — assembly, from `lemDual` and `lemC`
* `lemOmega_d`, `lemOmega_e`, `lemfS`   — `Families/Phase1/B/*`
-/
import Families.Phase1.A.LocalC
import Families.Phase1.A.Count
import Families.Phase1.B.All

namespace Families

/-- `lem:Omega` (a),(c). -/
theorem lemOmega_ac : lemOmega_ac_Statement := Phase1.B.lemOmega_ac_proof

/-- `lem:dual`. -/
theorem lemDual : lemDual_Statement := Phase1.B.lemDual_proof

/-- `prop:count`. -/
theorem propCount : propCount_Statement := Phase1.A.propCount_proof

/-- `lem:C`, from `lem:Omega`(a),(c) and `lem:fS`(i). -/
theorem lemC : lemC_Statement := Phase1.A.lemC_of lemOmega_ac Phase1.B.lemfS_i_proof

/-- `prop:sharpLS`, given the masses hypothesis `lem:WH` (a named classical input). -/
theorem propSharpLS (hWH : lemWH_Statement) : propSharpLS_Statement :=
  Phase1.B.propSharpLS_of_lemC lemC hWH

/-- `lem:Omega`(d). -/
theorem lemOmega_d : lemOmega_d_Statement := Phase1.B.lemOmega_d_proof

/-- `lem:Omega`(e). -/
theorem lemOmega_e : lemOmega_e_Statement := Phase1.B.lemOmega_e_proof

/-- `lem:fS`, all four parts (including the kernel-checked certificate `B < 3.73`). -/
theorem lemfS : lemfS_Statement := Phase1.B.lemfS_proof

end Families
