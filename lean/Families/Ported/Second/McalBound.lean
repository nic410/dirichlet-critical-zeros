/-
# Prime side (paper §5): the bound for `𝓜`

`mcalBound_of`: `eq:split` + `lem:mumu` + `lem:muLambda` + `lem:ss` + the ratio terms + the identity
`𝒬_F(f_v) = (b/λ + 2I_F)/a²` give `McalBound_Statement` (proof of `prop:second`, Proposition 5.13). The mixed and same-sign
bounds (`lem:muLambda`, `lem:ss`) enter as hypotheses in the exact form proved in
`Families.Ported.Second.MixSS` (`Mmix_small`, `SSC_small`).
-/
import Families.Ported.Second.Ratio

noncomputable section

open scoped BigOperators ContDiff
open Finset MeasureTheory Filter Topology

namespace Families.Ported.Second

open Families

/-- The form of `lem:muLambda` used: `M_{μΛ} = o(H T L² ℓ)` uniformly in `T`. -/
def MmixSmall_Statement : Prop :=
  ∀ (P : PrimeSetup) (W : Weight) (δ : ℝ), 0 < δ → ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ P.heights Q,
    |Mmix P W Q T| ≤ δ * (W.H Q * T * P.L Q ^ 2 * ell Q)

/-- The form of `lem:ss` used: `∑_χ ω_χ ∬ Φ² S S' = o(H T L² ℓ)` uniformly in `T`. -/
def SSCSmall_Statement : Prop :=
  ∀ (P : PrimeSetup) (W : Weight) (δ : ℝ), 0 < δ → ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ P.heights Q,
    ‖SSC P W Q T‖ ≤ δ * (W.H Q * T * P.L Q ^ 2 * ell Q)

/-- **`McalBound_Statement`** from `eq:split` and the bounds for its four parts
(proof of `prop:second`, Proposition 5.13). -/
theorem mcalBound_of (hStir : StirlingDigamma) (hWH : lemWH_Statement) (hB2 : lemB2_Statement)
    (hMrat : eqBMrat_Statement) (hmix : MmixSmall_Statement) (hss : SSCSmall_Statement) :
    McalBound_Statement := by
  intro P W c hc hc1 hprof δ hδ
  have hpi := Real.pi_pos
  set δ' : ℝ := δ / 5 with hδ'
  have hδ'0 : 0 < δ' := by positivity
  obtain ⟨Q₁, h1⟩ := Mmumu_bound hStir hWH P W δ' hδ'0
  obtain ⟨Q₂, h2⟩ := hmix P W δ' hδ'0
  obtain ⟨Q₃, h3⟩ := ratio_bound hB2 hMrat hWH P W c hc hc1 hprof δ' hδ'0
  obtain ⟨Q₄, h4⟩ := hss P W δ' hδ'0
  refine ⟨max (max Q₁ Q₂) (max (max Q₃ Q₄) 2), fun Q hQ T hT => ?_⟩
  have hQ1 : Q₁ ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hQ
  have hQ2 : Q₂ ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hQ
  have hQ3 : Q₃ ≤ Q :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hQ
  have hQ4 : Q₄ ≤ Q :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hQ
  have hQ5 : 2 ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hQ
  have hQ : 1 < Q := by linarith
  have e1 := h1 Q hQ1 T hT
  have e2 := h2 Q hQ2 T hT
  have e3 := h3 Q hQ3 T hT
  have e4 := h4 Q hQ4 T hT
  set X := W.H Q * T * P.L Q ^ 2 * ell Q with hX
  have hX0 : 0 ≤ X := by
    have hH := Families.Weight.H_nonneg W Q
    have hT0 : 0 ≤ T := le_trans (Real.rpow_nonneg (Real.log_nonneg hQ.le) _) hT.1
    have hℓ : 0 ≤ ell Q := Real.log_nonneg hQ.le
    positivity
  -- `eq:split`
  rw [Mcal_split P W hQ T]
  -- the same-sign term
  have hss' : 1 / (2 * Real.pi ^ 2) * (SSC P W Q T).re ≤ δ' * X := by
    have hre : (SSC P W Q T).re ≤ δ' * X := (Complex.re_le_norm _).trans e4
    have hpi2 : 1 ≤ 2 * Real.pi ^ 2 := by
      have : (3 : ℝ) ^ 2 ≤ Real.pi ^ 2 := pow_le_pow_left₀ (by norm_num) Real.pi_gt_three.le 2
      linarith
    have hc0 : 0 ≤ 1 / (2 * Real.pi ^ 2) := by positivity
    have hc1' : 1 / (2 * Real.pi ^ 2) ≤ 1 := by rw [div_le_one (by positivity)]; exact hpi2
    have h0 : 0 ≤ δ' * X := by positivity
    calc 1 / (2 * Real.pi ^ 2) * (SSC P W Q T).re ≤ 1 / (2 * Real.pi ^ 2) * (δ' * X) :=
          mul_le_mul_of_nonneg_left hre hc0
      _ ≤ 1 * (δ' * X) := mul_le_mul_of_nonneg_right hc1' h0
      _ = δ' * X := one_mul _
  have hmix' : 2 * Mmix P W Q T ≤ 2 * (δ' * X) := by
    have := (le_abs_self (Mmix P W Q T)).trans e2
    linarith
  -- the main term
  have ha := aInt_pos P
  have hl := P.lam_pos
  have hQf := Qf_fv_eq (P := P) hc.continuous
  have hLdef : P.L Q = P.lam * ell Q := rfl
  have hmain : (P.aInt * P.L Q) ^ 2 * (W.H Q * P.Jlen T * ell Q / (2 * Real.pi)) *
      Qf (fun α => c α * min α (1 + 2 * P.ε₃)) (fun x => P.vfun (x / P.lam) / (P.lam * P.aInt)) =
      W.H Q * P.Jlen T * P.bInt * P.L Q * ell Q ^ 2 / (2 * Real.pi) +
        W.H Q * P.Jlen T * P.L Q ^ 2 * ell Q * IF P c / Real.pi := by
    rw [hQf, hLdef]
    field_simp
  rw [hmain]
  have e1' := e1
  have e3' := e3
  have hsum : 1 / (2 * Real.pi ^ 2) * ((P.ratioForm W Q T (P.aVec Q)).re + (SSC P W Q T).re) =
      1 / (2 * Real.pi ^ 2) * (P.ratioForm W Q T (P.aVec Q)).re +
        1 / (2 * Real.pi ^ 2) * (SSC P W Q T).re := by ring
  rw [hsum]
  have : δ' * X + 2 * (δ' * X) + δ' * X + δ' * X ≤ δ * X := by
    rw [hδ']; have := mul_nonneg hδ.le hX0; nlinarith
  linarith

end Families.Ported.Second
