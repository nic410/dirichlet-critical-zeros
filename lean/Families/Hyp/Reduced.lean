/-
# The reduced classical inputs

Three of the five classical inputs of `Families.ClassicalInputs` are **theorems** (standard axioms only):

| field | proof | source |
|---|---|---|
| `MV_LargeSieve` | `Families.Hyp.MV_LargeSieve_proof` (`C₀ = 17/4`) | our `lem:dual` + `gauss_per_q` |
| `StirlingDigamma` | `Families.Hyp.StirlingDigamma_proof` | `zeta23` `StirlingVert`, `MuFields`, `Stirling` |
| `PNT_dlVP` | `Families.Hyp.PNT_dlVP_proof` | `zeta23` `MediumPNT` + Mathlib `Chebyshev` |

The masses `lem:WH` (b5) are also a theorem: `Families.lemWH` (`Families/Phase2/B/WH.lean`,
`c₀ = 8`). `ClassicalInputsReduced` is therefore only **Montgomery's 1969 zero-density theorem** (b2),
in the full form `Montgomery69_Density` (all heights).

**Status: the headline does not need `ClassicalInputsReduced`.**
`Families.thmMain : thmMain_Statement` is unconditional: the zero side uses Montgomery 1969 only in the
q-aspect range `T' ≤ Q` (`Families.Hyp.Montgomery.Montgomery69_Density_upTo_proof`, a theorem). The full
`Montgomery69_Density` is not proved. `ClassicalInputsReduced` is used only by the conditional variant
`Families.thmMain_of_montgomery (hC : ClassicalInputsReduced) : thmMain_Statement`.
-/
import Families.Hyp.MVLargeSieve
import Families.Hyp.Stirling
import Families.Hyp.PNT
import Families.Wired.Phase2

namespace Families

/-- **The classical input that is not a theorem**: Montgomery's zero-density theorem in the full form
`Montgomery69_Density` (Invent. Math. 8 (1969), Thm 1; all heights `T' ≥ 2`). `MV_LargeSieve`,
`PNT_dlVP`, `StirlingDigamma` and `lemWH_Statement` are theorems (`Families/Hyp`, `Families.lemWH`).
**Not a hypothesis of the headline** (`Families.thmMain` is unconditional; it uses only the proved
q-aspect restriction `Montgomery69_Density_upTo 1`); used by `Families.thmMain_of_montgomery`. -/
structure ClassicalInputsReduced : Prop where
  /-- (b2) Montgomery's zero-density theorem, `Families.Montgomery69_Density`. -/
  montgomery69 : Montgomery69_Density

/-- The full five-field bundle from the reduced one and the four discharged inputs. -/
theorem ClassicalInputsReduced.toFull (h : ClassicalInputsReduced) : ClassicalInputs :=
  { mvLargeSieve := Hyp.MV_LargeSieve_proof
    montgomery69 := h.montgomery69
    pnt := Hyp.PNT_dlVP_proof
    stirling := Hyp.StirlingDigamma_proof
    masses := lemWH }

end Families
