/-
# `SecondMomentAssembly` (paper §5)

**`Families.Ported.secondMoment_proof (hEF : ExplicitGaborSharp_Statement) : SecondMomentAssembly`.**

The only hypothesis is `lem:explicit` with the sharp prime cut-off, in exactly the form of the second and
third components of `Families.Ported.Zero.gabor_eq_integral`
(`ExplicitGaborSharp_Statement`, `Families/Ported/Second/EFBridge.lean`). Wiring (done in `Families/Ported/Full.lean`):
```
theorem Families.Ported.explicitGaborSharp : Second.ExplicitGaborSharp_Statement :=
  fun P _ τ₀ hQ _ _ _ hq hprim _ k l =>
    let h := Families.Ported.Zero.gabor_eq_integral P hQ τ₀ hq hprim k l
    ⟨h.2.1, h.2.2⟩
```
(`Gabor … k l` is `∑' ρ, gaborTerm …` by `rfl` (`gabor_apply`), and the zero side's `nuChi` unfolds to `nuSharp`.)
-/
import Families.Ported.Second.OfFC2
import Families.Ported.Second.EFBridge
import Families.Ported.Second.FC2

namespace Families.Ported

open Families Families.Ported.Second

/-- **The second-moment assembly** (paper §5), given `lem:explicit`. -/
theorem secondMoment_proof (hEF : ExplicitGaborSharp_Statement) : SecondMomentAssembly :=
  secondMoment_of_fc2 fun hMV hStir hWH => fc2_proof (explicitGabor_of_sharp hEF) hMV hStir hWH

end Families.Ported
