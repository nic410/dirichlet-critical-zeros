/-
# Zero side, unconditional

`propZero_unconditional : propZero_Statement ∧ lemRvM_lower_Statement` — the paper's `prop:zero` and the
lower half of `lem:RvM`, with **no hypotheses** (standard axioms only):

* `prop:zero` is `propZero_of_upTo` (`Families/Ported/Zero/Assembly.lean`) fed with
  - `Families.Hyp.Montgomery.Montgomery69_Density_upTo_proof 1` (Montgomery 1969 in the q-aspect
    range `2 ≤ T' ≤ Q`; `lem:bad` invokes the bound only at heights `T_j ≤ Q`, for `Q ≥ e²`), and
  - `Families.lemWH` (`lem:WH`);
* the lower half of `lem:RvM` is `lemRvM_lower` (no hypotheses).

The full `Families.Montgomery69_Density` (all heights `T' ≥ 2`, including `Q = 1`, i.e. `ζ`) is **not**
proved and **not** needed.
-/
import Families.Ported.Zero.Assembly
import Families.Wired.Phase2

namespace Families.Ported.Zero

/-- **`prop:zero` and the lower half of `lem:RvM`, unconditionally.** -/
theorem propZero_unconditional : propZero_Statement ∧ lemRvM_lower_Statement :=
  ⟨propZero_of_upTo (Hyp.Montgomery.Montgomery69_Density_upTo_proof 1 one_pos) lemWH, lemRvM_lower⟩

end Families.Ported.Zero
