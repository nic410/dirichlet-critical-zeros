/-
Wiring of the proofs in `Families/Phase3/C/*`.
* `lemB1`   — invisibility of the Ramanujan approximant (`lem:B1`)
* `eqBMrat` — the time-integrated prime form (`eqB:Mrat`)
* `lemB2`   — the flattened norm (`lem:B2`), from the named hypothesis `PNT_dlVP` (discharged in `Families/Hyp`)
* `propTIsharp` — the band-device interface (`prop:TIsharp`)
`lemB2_Statement` has its integral parenthesised (see its docstring); the `example` below checks that it is
literally `lemB2_Statement_fixed`.
-/
import Families.Phase3.C.B1
import Families.Phase3.C.Mrat
import Families.Phase3.C.B2
import Families.Phase3.C.TIsharp

namespace Families

example : lemB2_Statement = Phase3.C.lemB2_Statement_fixed := rfl

/-- `lem:B1`. -/
theorem lemB1 : lemB1_Statement := Phase3.C.lemB1_proof

/-- `eqB:Mrat`. -/
theorem eqBMrat : eqBMrat_Statement := Phase3.C.eqBMrat_proof

/-- `lem:B2`, given the prime number theorem in the weak form `PNT_dlVP`. -/
theorem lemB2 (hPNT : PNT_dlVP) : lemB2_Statement := Phase3.C.lemB2_proof_fixed hPNT

/-- `prop:TIsharp` (the band device), given the large sieve and `lem:WH` (both theorems: `Families/Hyp`,
`Families.lemWH`). -/
theorem propTIsharp (hMV : MV_LargeSieve) (hWH : lemWH_Statement) : propTIsharp_Statement :=
  Phase3.C.propTIsharp_proof hMV hWH

end Families
