/-
# Package S: `prop:secondH` and `SecondMomentAssemblyH`

`propSecondH_of_parts`: the finite-centre replacement (`fc2H_proof`), the prime-side bound for `𝓜`
(`mcalBound_ofH`) and the lower half of `lem:RvMH` give `prop:secondH` (Proposition 9.19: "divide by
`a²L²` and use `L = λℓ_*`, `|J| = (1−2θ)T` and `N = (1+o(1))HTℓ_*/2π`"), exactly as in the families
`propSecond_of_parts` with `ℓ → ℓ_*`.

**`secondMomentH_proof : SecondMomentAssemblyH`** (the component `secondMomentH`).
-/
import FamiliesH.S.McalBound
import FamiliesH.S.FC2

noncomputable section

set_option linter.unusedSectionVars false

open scoped BigOperators ContDiff
open MeasureTheory Filter Topology

namespace Families.Hybrid.S

open Families Families.Ported.Second

/-- **`prop:secondH`** from its halves. -/
theorem propSecondH_of_parts (hMV : MV_LargeSieve) (hStir : StirlingDigamma)
    (hWH : lemWH_Statement) (hRvM : lemRvMH_lower_Statement) (hB2 : lemB2H_Statement)
    (hMrat : eqBMratH_Statement) : propSecondH_Statement := by
  intro P W τ₀ c hc hc1 hprof δ hδ
  set Qv := Qf (fun α => c α * min α (1 + 2 * P.ε₃))
    (fun x => P.vfun (x / P.lam) / (P.lam * P.aInt)) with hQv
  have hQv0 : 0 ≤ Qv := Qf_fv_nonneg P.toPS c hc1
  have ha : 0 < P.aInt := aInt_pos P.toPS
  have hpi := Real.pi_pos
  set δ₁ : ℝ := δ / 6 / (2 * Real.pi) with hδ₁
  set δ₂ : ℝ := P.aInt ^ 2 * (δ / 6) / (2 * Real.pi) with hδ₂
  set δ₃ : ℝ := min (1 / 2) (δ / 6 / (Qv + 1)) with hδ₃
  have hδ₁0 : 0 < δ₁ := by positivity
  have hδ₂0 : 0 < δ₂ := by positivity
  have hδ₃0 : 0 < δ₃ := lt_min (by norm_num) (by positivity)
  have hδ₃h : δ₃ ≤ 1 / 2 := min_le_left _ _
  have hδ₃Q : δ₃ * (Qv + 1) ≤ δ / 6 := by
    have := min_le_right (1 / 2 : ℝ) (δ / 6 / (Qv + 1))
    rw [← hδ₃, le_div_iff₀ (by positivity)] at this
    exact this
  obtain ⟨Q₁, hQ₁⟩ := fc2H_proof hMV hStir hWH P W τ₀ δ₁ hδ₁0
  obtain ⟨Q₂, hQ₂⟩ := mcalBound_ofH hMV hStir hWH hB2 hMrat P W c hc hc1 hprof δ₂ hδ₂0
  obtain ⟨Q₃, hQ₃⟩ := hRvM W P.a0 P.kc P.a0_pos P.kc_pos δ₃ hδ₃0
  refine ⟨max (max Q₁ Q₂) (max Q₃ (Real.exp 1)), fun Q hQ T hT => ?_⟩
  have hQ1 : Q₁ ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hQ
  have hQ2 : Q₂ ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hQ
  have hQ3 : Q₃ ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hQ
  have hQe : Real.exp 1 ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hQ
  obtain ⟨hT1, hℓ1, hℓs, -, -, -⟩ := cell_facts P hQe hT
  have hℓs0 : 0 ≤ ellS Q T := by linarith
  have hL : 0 < P.L Q T := mul_pos P.lam_pos (by linarith)
  have hH : 0 ≤ W.H Q := Families.Weight.H_nonneg W Q
  have h1 := hQ₁ Q hQ1 T hT
  have h2 := hQ₂ Q hQ2 T hT
  have h3 : (1 - δ₃) * (W.H Q * T * ellS Q T / (2 * Real.pi)) ≤ Nfam W Q T := hQ₃ Q hQ3 T hT
  rw [← hQv] at h2
  set Y : ℝ := W.H Q * T * ellS Q T / (2 * Real.pi) with hY
  have hT0 : 0 ≤ T := by linarith
  have hY0 : 0 ≤ Y := by positivity
  have haL : 0 < (P.aInt * P.L Q T) ^ 2 := by positivity
  have h1' : P.Mfrak W Q T τ₀ ≤ Mcal2 P.toPS W Q (Q * T) T / (P.aInt * P.L Q T) ^ 2 +
      δ / 6 * Y := by
    have : δ₁ * (W.H Q * T * ellS Q T) = δ / 6 * Y := by
      rw [hδ₁, hY]; field_simp
    linarith
  have h2' : Mcal2 P.toPS W Q (Q * T) T / (P.aInt * P.L Q T) ^ 2 ≤
      (1 - 2 * P.θ) * Y * Qv + δ / 6 * Y := by
    rw [div_le_iff₀ haL]
    refine h2.trans (le_of_eq ?_)
    have hJ : P.Jlen T = (1 - 2 * P.θ) * T := rfl
    have hLl : P.L Q T = P.lam * ellS Q T := rfl
    rw [hJ, hY, hδ₂, hLl]
    field_simp
  exact final_arith hY0 hQv0 (by linarith [P.θ_lt]) (by linarith [P.θ_pos]) hδ hδ₃h hδ₃0.le
    hδ₃Q h1' h2' h3

/-- **`SecondMomentAssemblyH`** (§9.3, Proposition 9.19 via Lemma 9.10): proved. -/
theorem secondMomentH_proof : SecondMomentAssemblyH :=
  fun hMV hStir hWH hRvM hB2 hMrat => propSecondH_of_parts hMV hStir hWH hRvM hB2 hMrat

end Families.Hybrid.S
