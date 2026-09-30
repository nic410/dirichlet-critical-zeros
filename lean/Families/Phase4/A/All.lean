/-
All modules of `Families/Phase4/A` (wired in `Families/Wired/Phase4.lean`).

* `Families.Phase4.A.assemblyLimit_proof : assemblyLimit_Statement` (`AssemblyLimit.lean`)
  — the §7.3 limit step; standard axioms only.
* ingredients: `Families.Phase4.A.exists_window` (`lem:windows`, `Windows.lean`),
  `Qf_le_of_close` (continuity of `𝒬_F` on `L¹ ∩ L²`) and `Qf_le_of_band` (uniform kernel comparison)
  (`QfBasic.lean`), `upsilon0`, `dyadic` (the cut-offs `Υ₀`, `ψ_j` of `PrimeSetup`, `Setup.lean`),
  `mkSetup` (a `PrimeSetup` from a window).
* `Conditional.lean`: `Families.Phase4.A.thmConditional_of_components (hProf : profileLS_Statement)
  (hB2 : lemB2_Statement) (hMrat : eqBMrat_Statement) (hC : ClassicalInputs) (hR : PortedReductions) :
  thmConditional_Statement` — the assembly half of `thm:conditional`, proved. `profileLS_Statement`
  (the profile bound `eq:profile` from `LS(C)`, i.e. `prop:TI` re-run with `LS(C)`) is NOT proved:
  it is analytic, not assembly. Also `one_le_of_LS` (`LS(C)` ⇒ `C ≥ 1`, given `lem:WH`).
-/
import Families.Phase4.A.QfBasic
import Families.Phase4.A.Windows
import Families.Phase4.A.Setup
import Families.Phase4.A.AssemblyLimit
import Families.Phase4.A.Conditional
