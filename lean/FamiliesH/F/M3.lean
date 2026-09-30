/-
# Package F: `lem:M3H`(iii) (§9.3; Lemma 5.11(iii) for `L = λℓ_*`)

For `QT > 1` this is literally the families `lemM3_iii_iv` (part (iii)) for `HSetup.toPS` at `Q' = QT`.
For `QT < 1` the range is empty and for `QT = 1` both `g` and `𝒦` vanish, so both sides are `0`.
-/
import FamiliesH.F.M1

noncomputable section

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace Families.Hybrid

open Families

namespace F

/-- **`lem:M3H`(iii)**. -/
theorem lemM3H_iii_proof : lemM3H_iii_Statement := by
  intro P ρ hρ Q T δ hQ hT hδ hδ' y xs c Cmax hc
  obtain ⟨hρ1, hρ2, hρ3, hρ4⟩ := hρ
  have hQT0 : 0 < Q * T := mul_pos (by linarith) hT
  rcases lt_trichotomy (Q * T) 1 with h | h | h
  · -- `QT < 1`: empty range
    have hZ : P.rangeZ Q T = ∅ := P.rangeZ_empty hQT0 h
    have hN : P.range Q T = ∅ := P.range_empty hQT0 h
    simp [hZ, hN, normSq]
  · -- `QT = 1`
    have h0 : ∀ u, P.g Q T u = 0 := P.g_eq_zero_of h
    simp [h0, P.𝒦_eq_zero_of h]
  · exact (Families.lemM3_iii_iv P.toPS ρ hρ1 hρ2 hρ3 hρ4 (Q * T) T δ h hT hδ hδ' y).1 c Cmax hc

end F

end Families.Hybrid
