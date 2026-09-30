/-
# `SecondMomentAssembly` from the finite-centre replacement

`secondMoment_of_fc2`: everything of paper §5 except `eq:fc2` (which rests on `lem:explicit`) is proved;
given `eq:fc2` in the form `FC2_Statement`, `SecondMomentAssembly` follows.
-/
import Families.Ported.Second.Assembly
import Families.Ported.Second.McalBound
import Families.Ported.Second.MixSS

namespace Families.Ported.Second

open Families

/-- **§5 modulo `eq:fc2`.** -/
theorem secondMoment_of_fc2
    (hFC2 : MV_LargeSieve → StirlingDigamma → lemWH_Statement → FC2_Statement) :
    SecondMomentAssembly := fun hMV hStir hWH hRvM hB2 hMrat =>
  propSecond_of_parts (hFC2 hMV hStir hWH)
    (mcalBound_of hStir hWH hB2 hMrat (Mmix_small hMV hStir hWH) (SSC_small hMV hWH)) hRvM

end Families.Ported.Second
