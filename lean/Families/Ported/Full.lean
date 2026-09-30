/-
# The paper's ported reductions, fully proved

* `ZeroSideReduction` (§4 + Appendix B) — `Families.Ported.zeroSide_proof`.
* `SecondMomentAssembly` (§5) — `Families.Ported.secondMoment_proof`, whose one premise, the
  explicit formula `lem:explicit` in the sharp-cutoff Gabor form (`Second.ExplicitGaborSharp_Statement`),
  is supplied here by `Families.Ported.Zero.gabor_eq_integral` (Weil's formula for primitive
  `χ` with complex test functions, from `zeta23`).

Note: `SecondMomentAssembly` as stated omits the explicit-formula premise (it is underivable
from its listed premises alone, though true); this file supplies that premise from a proved theorem, so
the bundle `PortedReductions` is a theorem, `Families.portedReductions`.
-/
import Families.Ported.Second.Main
import Families.Ported.Zero.ExplicitFormula
import Families.Ported.Reduced

namespace Families

namespace Ported

/-- `lem:explicit` in the form consumed by the §5 proof, from `gabor_eq_integral`. -/
theorem explicitGaborSharp : Second.ExplicitGaborSharp_Statement :=
  fun P _ τ₀ hQ _ _ _ hq hprim _ k l =>
    let h := Families.Ported.Zero.gabor_eq_integral P hQ τ₀ hq hprim k l
    ⟨h.2.1, h.2.2⟩

/-- `SecondMomentAssembly` (§5), unconditionally. -/
theorem secondMoment : SecondMomentAssembly := secondMoment_proof explicitGaborSharp

end Ported

/-- **Both ported reductions are theorems.** -/
theorem portedReductions : PortedReductions :=
  { zeroSide := Ported.zeroSide_proof
    secondMoment := Ported.secondMoment }

end Families
