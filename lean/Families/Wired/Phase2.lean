/-
Wiring of the proofs in `Families/Phase2/B/*`.
* `lemCTlimit` — `C_T^+(w_η) → 1` (`lem:CTlimit`), with kernel-checked certificates (`CTNumerics.lean`)
* `lemWH`      — the masses `W`, `H` (`lem:WH`, `c₀ = 8`); discharges the named classical input (b5)
-/
import Families.Phase2.B.All

namespace Families

/-- `lem:CTlimit`. -/
theorem lemCTlimit : lemCTlimit_Statement := Phase2.B.lemCTlimit_proof

/-- `lem:WH` (formerly the named classical hypothesis (b5)). -/
theorem lemWH : lemWH_Statement := Phase2.B.lemWH_proof

end Families
