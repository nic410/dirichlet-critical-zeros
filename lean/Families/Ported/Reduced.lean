/-
# The reduced ported reductions

`ZeroSideReduction` (the paper's §4 + Appendix B) is a theorem: `Families.Ported.zeroSide_proof`
(`Families/Ported/Zero/*`, standard axioms only). The bundle `PortedReductionsReduced` therefore keeps, of the
paper's own ported reductions, only the §5 second-moment assembly (itself proved: `Families.Ported.secondMoment`).
-/
import Families.Ported.Zero.Assembly

namespace Families

/-- **The ported reduction kept as a hypothesis** in the conditional variants: the §5 second-moment assembly
(`prop:second`, proved as `Families.Ported.secondMoment`). `ZeroSideReduction` is proved (`Families.Ported.zeroSide_proof`). -/
structure PortedReductionsReduced : Prop where
  /-- `SecondMomentAssembly` (paper §5). -/
  secondMoment : SecondMomentAssembly

/-- The full bundle from the reduced one and the proved zero side. -/
theorem PortedReductionsReduced.toFull (h : PortedReductionsReduced) : PortedReductions :=
  { zeroSide := Ported.zeroSide_proof
    secondMoment := h.secondMoment }

end Families
