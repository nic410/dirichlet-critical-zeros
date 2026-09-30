/-
Wiring of the proof in `Families/Phase4/A/*` into the theorem for `assemblyLimit_Statement` (`Families.Main`).
* `assemblyLimit` — `Families/Phase4/A/*`: `lem:windows`, the explicit profile-uniform
  continuity bound for `𝒬_F`, and the choice of fixed data (`mkSetup`).
-/
import Families.Phase4.A.All

namespace Families

/-- The limit part of the assembly (`main.tex` §7.3). -/
theorem assemblyLimit : assemblyLimit_Statement := Phase4.A.assemblyLimit_proof

end Families
