/-
# Package S: the archimedean term `M_{μμ}` at polynomial height (Lemma 9.10(a), upper half)

`Mmumu_boundH`: `M_{μμ} ≤ H|J| b L ℓ_*²/(2π) + o(H T L² ℓ_*)`, uniformly on the cell. On `J`,
`|μ_χ(t)| ≤ (ℓ_* + 2πR₀)/(2π)` for `q ≤ Q` (Stirling; `log(q/π) + log T ≤ log(QT) = ℓ_*`): the
`log T` of the families proof is absorbed into `ℓ_*`, so the correction `x = 2πR₀` is a constant.
-/
import FamiliesH.S.Split

noncomputable section

set_option linter.unusedSectionVars false

open scoped BigOperators ContDiff
open Finset MeasureTheory Filter Topology

namespace Families.Hybrid.S

open Families Families.Ported.Second Families.Ported.Second.FC2

/-- **`lem:archH`(a), upper half.** -/
theorem Mmumu_boundH (hStir : StirlingDigamma) (P : HSetup) (W : Weight) (δ : ℝ) (hδ : 0 < δ) :
    ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ P.heights Q,
      Mmumu2 P.toPS W Q (Q * T) T ≤
        W.H Q * P.Jlen T * P.bInt * P.L Q T * ellS Q T ^ 2 / (2 * Real.pi) +
          δ * (W.H Q * T * P.L Q T ^ 2 * ellS Q T) := by
  obtain ⟨R₀, hR₀, hnear⟩ := muChi_near_J hStir
  obtain ⟨CJ, hCJ, hJ2⟩ := J2_PhiSq_le P.toPS
  have hpi := Real.pi_pos
  have hb : 0 ≤ P.bInt := integral_nonneg fun s => sq_nonneg _
  have hl := P.lam_pos
  set x0 : ℝ := 2 * Real.pi * R₀ with hx0
  have hx00 : 0 ≤ x0 := by positivity
  obtain ⟨Q₁, h₁⟩ := L_large P ((3 * P.bInt / (2 * Real.pi) * x0) / (δ / 2) + 1)
  obtain ⟨Q₂, h₂⟩ := L_large P ((CJ + 1) / (δ / 2 * P.lam ^ 2) + x0 + 1)
  refine ⟨max (max Q₁ Q₂) (max (Real.exp 1) 4), fun Q hQ T hT => ?_⟩
  have hQ1' : Q₁ ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hQ
  have hQ2' : Q₂ ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hQ
  have hQe : Real.exp 1 ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hQ
  have hQ4 : (4 : ℝ) ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hQ
  obtain ⟨hT1, hℓ1, hℓs, -, hQT, hlogT⟩ := cell_facts P hQe hT
  have hQ1 : 1 < Q := one_lt_of_exp_one_le hQe
  have hQ0 : 0 < Q := by linarith
  set ℓs := ellS Q T with hℓsdef
  set L := P.L Q T with hLdef
  have hLℓ : L = P.lam * ℓs := rfl
  have e1 := (h₁ Q hQ1' T hT).1
  have e2 := (h₂ Q hQ2' T hT).2
  have hℓsT : ℓs = Real.log Q + Real.log T := by
    rw [hℓsdef]; unfold ellS; rw [Real.log_mul hQ0.ne' (by linarith)]
  have hpi4 : Real.log Real.pi ≤ Real.log Q :=
    Real.log_le_log hpi (by linarith [Real.pi_lt_four])
  have hlpi0 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hH0 : 0 ≤ W.H Q := W.H_nonneg Q
  -- `U = (ℓ_* + x₀)/2π` bounds `|μ_χ|` on `J`
  set U : ℝ := (ℓs + x0) / (2 * Real.pi) with hU
  have hU0 : 0 ≤ U := by rw [hU]; have : 0 ≤ ℓs := by linarith
                         positivity
  have hμU : ∀ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∀ χ : DirichletCharacter ℂ q, ∀ t ∈ P.toPS.J T,
      |muChi χ t| ≤ U := by
    intro q hq χ t ht
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hqQ : (q : ℝ) ≤ Q := by
      have := (Finset.mem_Icc.mp hq).2
      exact (Nat.le_floor_iff hQ0.le).mp this
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
    have hlq := Real.log_le_log hq0 hqQ
    have hlq0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq1)
    have h := hnear P.toPS T hT1 q χ t ht
    have hβ : |1 / (2 * Real.pi) * (Real.log (q / Real.pi) + Real.log T)| ≤ ℓs / (2 * Real.pi) := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi)), one_div_mul_eq_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      rw [Real.log_div hq0.ne' hpi.ne', abs_le]
      constructor <;> linarith
    have := abs_sub_abs_le_abs_sub (muChi χ t)
      (1 / (2 * Real.pi) * (Real.log (q / Real.pi) + Real.log T))
    have e : ℓs / (2 * Real.pi) + R₀ = U := by
      rw [hU, hx0]; field_simp
    linarith
  -- pointwise: `K₂(μ, μ) ≤ U² ∬ Φ²`
  have hQs : 1 < Q * T := hQT
  have hK2 : ∀ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∀ χ : DirichletCharacter ℂ q,
      K2 P.toPS (Q * T) T (muChi χ) (muChi χ) ≤
        U ^ 2 * ∫ t in P.toPS.J T, ∫ t' in P.toPS.J T, PhiSq P.toPS (Q * T) (t - t') := by
    intro q hq χ
    have hμc := muChi_continuous χ
    have hcont := K2_cont (P := P.toPS) hQs hμc hμc
    have hcont1 : Continuous (Function.uncurry fun t t' : ℝ =>
        U ^ 2 * PhiSq P.toPS (Q * T) (t - t')) :=
      continuous_const.mul ((PhiSq_continuous P.toPS hQs).comp
        (continuous_fst.sub continuous_snd))
    unfold K2
    rw [← integral_const_mul]
    have hin : ∀ t, U ^ 2 * ∫ t' in P.toPS.J T, PhiSq P.toPS (Q * T) (t - t') =
        ∫ t' in P.toPS.J T, U ^ 2 * PhiSq P.toPS (Q * T) (t - t') :=
      fun t => (integral_const_mul _ _).symm
    simp_rw [hin]
    have hJ : P.toPS.J T = Set.Icc ((1 + P.toPS.θ) * T) ((2 - P.toPS.θ) * T) := rfl
    rw [hJ]
    refine setIntegral_mono_on (intOn_Icc_outer hcont _ _) (intOn_Icc_outer hcont1 _ _)
      measurableSet_Icc fun t ht => ?_
    refine setIntegral_mono_on (intOn_Icc_inner hcont _ _ t) (intOn_Icc_inner hcont1 _ _ t)
      measurableSet_Icc fun t' ht' => ?_
    have hK0 := PhiSq_nonneg P.toPS (Q * T) (t - t')
    have ha := hμU q hq χ t ht
    have hb' := hμU q hq χ t' ht'
    have hprod : muChi χ t * muChi χ t' ≤ U ^ 2 := by
      have h' : |muChi χ t * muChi χ t'| ≤ U * U := by
        rw [abs_mul]; exact mul_le_mul ha hb' (abs_nonneg _) hU0
      nlinarith [le_abs_self (muChi χ t * muChi χ t')]
    calc PhiSq P.toPS (Q * T) (t - t') * muChi χ t * muChi χ t'
        = PhiSq P.toPS (Q * T) (t - t') * (muChi χ t * muChi χ t') := by ring
      _ ≤ PhiSq P.toPS (Q * T) (t - t') * U ^ 2 := mul_le_mul_of_nonneg_left hprod hK0
      _ = U ^ 2 * PhiSq P.toPS (Q * T) (t - t') := by ring
  -- family sum
  set J2 := ∫ t in P.toPS.J T, ∫ t' in P.toPS.J T, PhiSq P.toPS (Q * T) (t - t') with hJ2def
  have hfam : Mmumu2 P.toPS W Q (Q * T) T ≤ W.H Q * (U ^ 2 * J2) := by
    unfold Mmumu2
    refine (famSum_mono W Q fun q hq χ => hK2 q hq χ).trans (le_of_eq ?_)
    rw [famSum_const]; ring
  have hTpos : 0 < T := by linarith
  have hJ2 : J2 ≤ 2 * Real.pi * P.Jlen T * P.bInt * L + CJ := hJ2 (Q * T) T hQs hTpos
  have hJlen : P.Jlen T ≤ T := by
    unfold HSetup.Jlen
    have : 0 ≤ 2 * P.θ * T := by have := P.θ_pos; positivity
    linarith
  have hJlen0 : 0 ≤ P.Jlen T := by
    unfold HSetup.Jlen
    exact mul_nonneg (by linarith [P.θ_lt]) (by linarith)
  have hL0 : 0 ≤ L := by
    rw [hLℓ]; exact mul_nonneg hl.le (by linarith)
  have hx0ℓ : x0 ≤ ℓs := by
    have : 0 ≤ (CJ + 1) / (δ / 2 * P.lam ^ 2) := by positivity
    linarith
  -- final estimate
  refine hfam.trans ?_
  have hUJ : U ^ 2 * J2 ≤ U ^ 2 * (2 * Real.pi * P.Jlen T * P.bInt * L + CJ) :=
    mul_le_mul_of_nonneg_left hJ2 (sq_nonneg _)
  have hmain : U ^ 2 * (2 * Real.pi * P.Jlen T * P.bInt * L) =
      P.Jlen T * P.bInt * L * (ℓs + x0) ^ 2 / (2 * Real.pi) := by
    rw [hU]; field_simp
  have hsq : (ℓs + x0) ^ 2 ≤ ℓs ^ 2 + 3 * ℓs * x0 := by
    have e : (ℓs + x0) ^ 2 = ℓs ^ 2 + 3 * ℓs * x0 - x0 * (ℓs - x0) := by ring
    rw [e]; linarith [mul_nonneg hx00 (sub_nonneg.mpr hx0ℓ)]
  have hx3 : 3 * P.bInt / (2 * Real.pi) * x0 ≤ δ / 2 * L := by
    have h : (3 * P.bInt / (2 * Real.pi) * x0) / (δ / 2) ≤ L := by linarith
    rw [div_le_iff₀ (by positivity)] at h
    linarith
  have hU1 : U ≤ ℓs := by
    rw [hU, div_le_iff₀ (by positivity)]
    have : 0 ≤ 2 * ℓs * (Real.pi - 1) := mul_nonneg (by linarith) (by linarith [Real.pi_gt_three])
    linarith
  have hCJ' : U ^ 2 * CJ ≤ δ / 2 * (T * L ^ 2 * ℓs) := by
    have h3' : CJ + 1 ≤ δ / 2 * P.lam ^ 2 * ℓs := by
      have h : (CJ + 1) / (δ / 2 * P.lam ^ 2) ≤ ℓs := by
        have : 0 ≤ x0 := hx00
        linarith
      rw [div_le_iff₀ (by positivity)] at h
      linarith
    have hU2 : U ^ 2 ≤ ℓs ^ 2 := pow_le_pow_left₀ hU0 hU1 2
    have e : δ / 2 * (T * L ^ 2 * ℓs) = δ / 2 * P.lam ^ 2 * ℓs * (T * ℓs ^ 2) := by
      rw [hLℓ]; ring
    rw [e]
    calc U ^ 2 * CJ ≤ ℓs ^ 2 * CJ := mul_le_mul_of_nonneg_right hU2 hCJ
      _ ≤ ℓs ^ 2 * (δ / 2 * P.lam ^ 2 * ℓs) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _); linarith
      _ ≤ δ / 2 * P.lam ^ 2 * ℓs * (T * ℓs ^ 2) := by
          have h0 : 0 ≤ δ / 2 * P.lam ^ 2 * ℓs * ℓs ^ 2 := by
            have : 0 ≤ ℓs := by linarith
            positivity
          have := mul_le_mul_of_nonneg_left hT1 h0
          linarith
  have hmain2 : P.Jlen T * P.bInt * L * (ℓs + x0) ^ 2 / (2 * Real.pi) ≤
      P.Jlen T * P.bInt * L * ℓs ^ 2 / (2 * Real.pi) + δ / 2 * (T * L ^ 2 * ℓs) := by
    have hJbL : 0 ≤ P.Jlen T * P.bInt * L := by positivity
    have step1 : P.Jlen T * P.bInt * L * (ℓs + x0) ^ 2 / (2 * Real.pi) ≤
        P.Jlen T * P.bInt * L * (ℓs ^ 2 + 3 * ℓs * x0) / (2 * Real.pi) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hsq hJbL
    have step2 : P.Jlen T * P.bInt * L * (3 * ℓs * x0) / (2 * Real.pi) ≤
        δ / 2 * (T * L ^ 2 * ℓs) := by
      have e : P.Jlen T * P.bInt * L * (3 * ℓs * x0) / (2 * Real.pi) =
          P.Jlen T * L * ℓs * (3 * P.bInt / (2 * Real.pi) * x0) := by ring
      rw [e]
      have hℓs0 : 0 ≤ ℓs := by linarith
      have hJLl : 0 ≤ P.Jlen T * L * ℓs := by positivity
      calc P.Jlen T * L * ℓs * (3 * P.bInt / (2 * Real.pi) * x0)
          ≤ P.Jlen T * L * ℓs * (δ / 2 * L) := mul_le_mul_of_nonneg_left hx3 hJLl
        _ ≤ T * L * ℓs * (δ / 2 * L) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            apply mul_le_mul_of_nonneg_right _ hℓs0
            exact mul_le_mul_of_nonneg_right hJlen hL0
        _ = δ / 2 * (T * L ^ 2 * ℓs) := by ring
    have e : P.Jlen T * P.bInt * L * (ℓs ^ 2 + 3 * ℓs * x0) / (2 * Real.pi) =
        P.Jlen T * P.bInt * L * ℓs ^ 2 / (2 * Real.pi) +
          P.Jlen T * P.bInt * L * (3 * ℓs * x0) / (2 * Real.pi) := by ring
    linarith
  calc W.H Q * (U ^ 2 * J2)
      ≤ W.H Q * (U ^ 2 * (2 * Real.pi * P.Jlen T * P.bInt * L + CJ)) :=
        mul_le_mul_of_nonneg_left hUJ hH0
    _ = W.H Q * (U ^ 2 * (2 * Real.pi * P.Jlen T * P.bInt * L)) + W.H Q * (U ^ 2 * CJ) := by
        ring
    _ ≤ W.H Q * (P.Jlen T * P.bInt * L * ℓs ^ 2 / (2 * Real.pi) +
          δ / 2 * (T * L ^ 2 * ℓs)) + W.H Q * (δ / 2 * (T * L ^ 2 * ℓs)) := by
        rw [hmain]
        exact add_le_add (mul_le_mul_of_nonneg_left hmain2 hH0)
          (mul_le_mul_of_nonneg_left hCJ' hH0)
    _ = W.H Q * P.Jlen T * P.bInt * L * ℓs ^ 2 / (2 * Real.pi) +
          δ * (W.H Q * T * L ^ 2 * ℓs) := by ring

end Families.Hybrid.S
