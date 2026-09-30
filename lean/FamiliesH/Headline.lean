/-
# Theorem 1.4(a): the headline

`thmH : thmH_Statement` is `thmH_of_parts` (proved glue, `FamiliesH.Glue`) applied to
* the families paper's proved theorems, reused unchanged: `Families.lemCTlimit`, `Families.propSharpLS`,
  `Families.lemWH`, `Families.Hyp.MV_LargeSieve_proof`, `Families.Hyp.StirlingDigamma_proof`;
* the hybrid component theorems of `FamiliesH.Components`, all proved (packages V, F, Z, S, TS).

`thmH` is sorry-free: `#print axioms thmH` = `[propext, Classical.choice, Quot.sound]`.
The audit (`scripts/audit.sh`) checks this, that the glue is sorry-free and that `thmH` has no hypotheses.
-/
import FamiliesH.Glue
import FamiliesH.Components

noncomputable section

namespace Families.Hybrid

open Families

/-- **Theorem 1.4(a)** (polynomial height, sharp route). No hypotheses; depends only on the standard
axioms `propext`, `Classical.choice`, `Quot.sound` (see `scripts/audit.sh`). -/
theorem thmH : thmH_Statement :=
  thmH_of_parts lemCTlimit (propSharpLS lemWH) propTIsharpH lemB2H eqBMratH assemblyLimitH lemPLipH
    lemMbeta certH Hyp.MV_LargeSieve_proof Hyp.StirlingDigamma_proof lemWH propZeroH_unconditional
    secondMomentH

end Families.Hybrid
