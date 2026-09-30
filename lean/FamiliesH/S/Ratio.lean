/-
# Package S: the ratio terms at polynomial height (Proposition 9.19, first display)

`ratio_boundH`: under the profile bound (9.15) (`HSetup.ProfileBoundH`),
`M^{rat}_{ΛΛ} = (1/2π²) Re ∑ a_n a_m Δ(n,m) 𝒦(n,m) ≤ H|J|L²ℓ_* I_F/π + o(H T L² ℓ_*)`.
This is the families `Families.Ported.Second.ratio_bound` with `ℓ → ℓ_*`: `eqB:MratH` (`a → b`), the
profile bound, `𝒦(n,n) ≤ 2π|J| g(log n) + O(1)` (`lemM1_diag` at `Q' = QT`) and `lem:B2H` with the test
functions `h(y) = c(y/ℓ_*) g(y)` (`hTest` at `Q' = QT`) and a fixed bump (`hOne`, for `∑ b_n² ≪ Lℓ_*`).
Nothing here involves the size of `Y` relative to `Q²`.
-/
import FamiliesH.S.Basic

noncomputable section

set_option linter.unusedSectionVars false

open scoped BigOperators ContDiff
open Finset MeasureTheory Filter Topology

namespace Families.Hybrid.S

open Families Families.Ported.Second

set_option maxHeartbeats 1600000 in
/-- **Ratio terms** at polynomial height. -/
theorem ratio_boundH (hB2 : lemB2H_Statement) (hMrat : eqBMratH_Statement)
    (hWH : lemWH_Statement) (P : HSetup) (W : Weight) (c : ℝ → ℝ) (hc : ContDiff ℝ ∞ c)
    (hc1 : ∀ α, 1 ≤ c α) (hprof : P.ProfileBoundH W c) (δ : ℝ) (hδ : 0 < δ) :
    ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ P.heights Q,
      1 / (2 * Real.pi ^ 2) * (P.ratioForm W Q T (P.aVec Q T)).re ≤
        W.H Q * P.Jlen T * P.L Q T ^ 2 * ellS Q T * IF P.toPS c / Real.pi +
          δ * (W.H Q * T * P.L Q T ^ 2 * ellS Q T) := by
  have hpi := Real.pi_pos
  have hl := P.lam_pos
  have hIF := IF_nonneg (P := P.toPS) hc1
  set IFv := IF P.toPS c with hIFv
  set δ₀ : ℝ := min 1 (δ / (5 * (3 * IFv / Real.pi + 1))) with hδ₀def
  have hδ₀ : 0 < δ₀ := lt_min one_pos (by positivity)
  have hδ₀1 : δ₀ ≤ 1 := min_le_left _ _
  have hδ₀δ : δ₀ * (3 * IFv / Real.pi + 1) ≤ δ / 5 := by
    have := min_le_right 1 (δ / (5 * (3 * IFv / Real.pi + 1)))
    rw [← hδ₀def, le_div_iff₀ (by positivity)] at this
    linarith
  -- inputs
  obtain ⟨C₁, Q₁, hM⟩ := hMrat P W 1 one_pos
  obtain ⟨Q₂, hP⟩ := hprof δ₀ hδ₀
  obtain ⟨Cd, hCd⟩ := lemM1_diag P.toPS
  obtain ⟨M, hM1, hMb⟩ := Hc_bounded (P := P.toPS) hc
  choose D hD0 hD using fun i => Hc_iteratedDeriv_bounded (P := P.toPS) hc i
  choose D' hD'0 hD' using fun i => Bmp_iteratedDeriv_bounded i
  obtain ⟨C₂, Q₃, hB⟩ := hB2 P D δ₀ hδ₀
  obtain ⟨C₃, Q₄, hB'⟩ := hB2 P D' δ₀ hδ₀
  obtain ⟨cH, Q₅, hcH, hH⟩ := H_lower hWH W
  obtain ⟨cmax, hcmax⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (0 : ℝ) 6) hc.continuous.continuousOn
  have hCd0 : 0 ≤ Cd := by
    have := hCd 2 1 (by norm_num) one_pos 1 le_rfl; exact (norm_nonneg _).trans this
  set C₁' := max C₁ 0
  set C₂' := max C₂ 0
  set C₃' := max C₃ 0
  set cm := max cmax 1
  set B₁ := ∫ x, Bmp x with hB₁
  have hB₁0 : 0 ≤ B₁ := integral_nonneg Bmp_nonneg
  set K₃ : ℝ := 2 * Cd * cm * (2 * (1 + 2 * P.ε₃) * B₁ + C₃') / (2 * Real.pi ^ 2) with hK₃
  have hK₃0 : 0 ≤ K₃ := by
    have := P.ε₃_pos; have : 0 ≤ C₃' := le_max_right _ _; have : 0 ≤ cm := by
      exact le_trans zero_le_one (le_max_right _ _)
    positivity
  -- thresholds
  obtain ⟨QL, hQL⟩ := L_large P ((10 * C₂' * M / Real.pi) / (δ / 5) + K₃ / (δ / 5) + 1)
  refine ⟨max (max (max Q₁ Q₂) (max (max Q₃ Q₄) Q₅))
    (max (max QL (Real.exp 1)) (max (C₁' / (2 * Real.pi ^ 2 * (δ / 5))) (1 / cH))),
    fun Q hQ T hT => ?_⟩
  have hQa := le_trans (le_max_left _ _) hQ
  have hQb := le_trans (le_max_right _ _) hQ
  have hQ1' : Q₁ ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hQa
  have hQ2' : Q₂ ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hQa
  have hQ3' : Q₃ ≤ Q :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hQa
  have hQ4' : Q₄ ≤ Q :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) hQa
  have hQ5' : Q₅ ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hQa
  have hQL' : QL ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hQb
  have hQe : Real.exp 1 ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hQb
  have h3 : C₁' / (2 * Real.pi ^ 2 * (δ / 5)) ≤ Q :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hQb
  have h7 : 1 / cH ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hQb
  obtain ⟨hT1, hℓ1, hℓs, hQQT, hQT, -⟩ := cell_facts P hQe hT
  have hQ1 : 1 < Q := one_lt_of_exp_one_le hQe
  have hQ0 : 0 < Q := by linarith
  have hTpos : 0 < T := by linarith
  have hℓs1 : 1 ≤ ellS Q T := le_trans hℓ1 hℓs
  have hLbig := (hQL Q hQL' T hT).1
  have hL1 : 1 ≤ P.L Q T := by
    have : 0 ≤ (10 * C₂' * M / Real.pi) / (δ / 5) := by
      have : 0 ≤ C₂' := le_max_right _ _
      have : (0 : ℝ) ≤ M := by linarith
      positivity
    have : 0 ≤ K₃ / (δ / 5) := by positivity
    linarith
  have hL1' : 1 ≤ P.toPS.L (Q * T) := hL1
  have hLdef : P.L Q T = P.lam * ellS Q T := rfl
  have hH0 : 0 ≤ W.H Q := Families.Weight.H_nonneg W Q
  have hH1 : 1 ≤ W.H Q := by
    have h := hH Q hQ5'
    have hQ' : 1 ≤ cH * Q := by rw [div_le_iff₀ hcH] at h7; linarith
    have e : cH * Q ^ 2 = (cH * Q) * Q := by ring
    have := mul_le_mul hQ' hQ1.le zero_le_one (by linarith)
    linarith
  have hJlen : P.Jlen T ≤ T := by
    unfold HSetup.Jlen
    have : 0 ≤ 2 * P.θ * T := by have := P.θ_pos; positivity
    linarith
  have hJlen0 : 0 ≤ P.Jlen T := by
    unfold HSetup.Jlen
    exact mul_nonneg (by linarith [P.θ_lt]) (by linarith)
  set X := W.H Q * T * P.L Q T ^ 2 * ellS Q T with hX
  have hX0 : 0 ≤ X := by
    have : 0 ≤ P.L Q T := by linarith
    have : 0 ≤ ellS Q T := by linarith
    positivity
  -- the sums
  set b := P.bVec Q T
  set S1 := ∑ n ∈ P.range Q T, b n ^ 2 * c (Real.log n / ellS Q T) * (P.𝒦 Q T n n).re
  set Sh := ∑ n ∈ P.range Q T, b n ^ 2 * hTest P.toPS c (Q * T) (Real.log n)
  set S0 := ∑ n ∈ P.range Q T, b n ^ 2 * c (Real.log n / ellS Q T)
  set Sb := ∑ n ∈ P.range Q T, b n ^ 2 * hOne P.toPS (Q * T) (Real.log n)
  -- (1) `eqB:MratH`
  have st1 : (P.ratioForm W Q T (P.aVec Q T)).re ≤
      (P.ratioForm W Q T (P.bVec Q T)).re + C₁' * Q⁻¹ := by
    have h := hM Q hQ1' T hT
    rw [Real.rpow_neg_one] at h
    have hre := Complex.re_le_norm (P.ratioForm W Q T (P.aVec Q T) - P.ratioForm W Q T (P.bVec Q T))
    rw [Complex.sub_re] at hre
    have : C₁ * Q⁻¹ ≤ C₁' * Q⁻¹ :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_nonneg.mpr hQ0.le)
    linarith
  -- (2) the profile bound
  have st2 := hP Q hQ2' T hT
  -- (3) `𝒦(n,n) ≤ 2π|J| g(log n) + O(1)`
  have st3 : S1 ≤ 2 * Real.pi * P.Jlen T * Sh + Cd * S0 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn1 := (SC.mem_range_le P.toPS hn).1
    have hK : ‖P.𝒦 Q T n n - 2 * Real.pi * P.Jlen T * P.toPS.g (Q * T) (Real.log n)‖ ≤ Cd :=
      hCd (Q * T) T hQT hTpos n hn1
    have hre : (P.𝒦 Q T n n).re ≤ 2 * Real.pi * P.Jlen T * P.toPS.g (Q * T) (Real.log n) + Cd := by
      have h' := Complex.re_le_norm
        (P.𝒦 Q T n n - 2 * Real.pi * P.Jlen T * P.toPS.g (Q * T) (Real.log n))
      have e : (P.𝒦 Q T n n - 2 * Real.pi * P.Jlen T * P.toPS.g (Q * T) (Real.log n)).re =
          (P.𝒦 Q T n n).re - 2 * Real.pi * P.Jlen T * P.toPS.g (Q * T) (Real.log n) := by
        simp [Complex.sub_re, Complex.mul_re]
      rw [e] at h'
      linarith
    have hbc : 0 ≤ b n ^ 2 * c (Real.log n / ellS Q T) :=
      mul_nonneg (sq_nonneg _) (le_trans zero_le_one (hc1 _))
    have hTe : hTest P.toPS c (Q * T) (Real.log n) =
        c (Real.log n / ellS Q T) * P.toPS.g (Q * T) (Real.log n) := hTest_eq hQT _
    rw [hTe]
    calc b n ^ 2 * c (Real.log n / ellS Q T) * (P.𝒦 Q T n n).re
        ≤ b n ^ 2 * c (Real.log n / ellS Q T) *
            (2 * Real.pi * P.Jlen T * P.toPS.g (Q * T) (Real.log n) + Cd) :=
          mul_le_mul_of_nonneg_left hre hbc
      _ = 2 * Real.pi * P.Jlen T * (b n ^ 2 * (c (Real.log n / ellS Q T) *
            P.toPS.g (Q * T) (Real.log n))) + Cd * (b n ^ 2 * c (Real.log n / ellS Q T)) := by ring
  -- (4) `lem:B2H` with `h = hTest`
  have st4 : Sh ≤ (1 + δ₀) * (P.L Q T ^ 2 * ellS Q T * IFv) +
      C₂' * (P.L Q T * M) * ellS Q T := by
    have h := hB Q hQ3' T hT (hTest P.toPS c (Q * T)) (P.L Q T * M) (hTest_contDiff hc (Q * T))
      (hTest_nonneg hc1 hQT) (hTest_integrable hc hQT) (hTest_le hMb hQT)
      (fun i y => hTest_deriv_bound hc hM1 i (hD i) hL1' y)
    have hI : ∫ s, ellS Q T * Fb P.ε₃ (s / ellS Q T) * hTest P.toPS c (Q * T) s =
        P.L Q T ^ 2 * ellS Q T * IFv := integral_hTest (P := P.toPS) (c := c) hQT
    rw [hI] at h
    have : C₂ * (P.L Q T * M) * ellS Q T ≤ C₂' * (P.L Q T * M) * ellS Q T := by
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg (by linarith) (by linarith))
    linarith
  -- (5) `∑ b² ≪ Lℓ_*` with `h = hOne`
  have st5 : Sb ≤ (1 + δ₀) * (ellS Q T * (1 + 2 * P.ε₃) * (P.L Q T * B₁)) +
      C₃' * 1 * ellS Q T := by
    have h := hB' Q hQ4' T hT (hOne P.toPS (Q * T)) 1 (hOne_contDiff (Q * T)) (hOne_nonneg (Q * T))
      (hOne_integrable hQT) (hOne_le (Q * T)) (fun i y => hOne_deriv_bound i (hD' i) hL1' y)
    have hi : ∫ s, ellS Q T * Fb P.ε₃ (s / ellS Q T) * hOne P.toPS (Q * T) s ≤
        ellS Q T * (1 + 2 * P.ε₃) * (P.L Q T * B₁) := integral_hOne_le (P := P.toPS) hQT
    have : C₃ * 1 * ellS Q T ≤ C₃' * 1 * ellS Q T := by
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) zero_le_one
    have : (1 + δ₀) * (∫ s, ellS Q T * Fb P.ε₃ (s / ellS Q T) * hOne P.toPS (Q * T) s) ≤
        (1 + δ₀) * (ellS Q T * (1 + 2 * P.ε₃) * (P.L Q T * B₁)) :=
      mul_le_mul_of_nonneg_left hi (by linarith)
    linarith
  have hlam2 : P.lam < 2 := lt_of_lt_of_le P.lam_lt (F.betaK_le_two P.kc_pos.le)
  have st6 : S0 ≤ cm * Sb := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have hL0 : 0 ≤ P.toPS.L (Q * T) := by linarith
    obtain ⟨hl0, hl3⟩ := SC.log_le_of_mem_range P.toPS hL0 hn
    have h1 : hOne P.toPS (Q * T) (Real.log n) = 1 := hOne_one hQT hn
    rw [h1, mul_one]
    have hmem : Real.log n / ellS Q T ∈ Set.Icc (0 : ℝ) 6 := by
      refine ⟨div_nonneg hl0 (by linarith), ?_⟩
      rw [div_le_iff₀ (by linarith)]
      have : P.L Q T ≤ 2 * ellS Q T := by
        rw [hLdef]; exact mul_le_mul_of_nonneg_right hlam2.le (by linarith)
      have hl3' : Real.log n ≤ 3 * P.L Q T := hl3
      linarith
    have hcle : c (Real.log n / ellS Q T) ≤ cm := by
      have := hcmax _ hmem
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_max_left _ _))
    calc b n ^ 2 * c (Real.log n / ellS Q T) ≤ b n ^ 2 * cm :=
          mul_le_mul_of_nonneg_left hcle (sq_nonneg _)
      _ = cm * b n ^ 2 := by ring
  -- nonnegativity
  have hSh0 : 0 ≤ Sh := Finset.sum_nonneg fun n _ =>
    mul_nonneg (sq_nonneg _) (hTest_nonneg hc1 hQT _)
  have hcm0 : 0 ≤ cm := le_trans zero_le_one (le_max_right _ _)
  have hC₂'0 : 0 ≤ C₂' := le_max_right _ _
  have hC₃'0 : 0 ≤ C₃' := le_max_right _ _
  have hC₁'0 : 0 ≤ C₁' := le_max_right _ _
  set L := P.L Q T with hLL
  set ℓs := ellS Q T with hℓℓ
  have hL0 : 0 ≤ L := by linarith
  have hℓs0 : 0 ≤ ℓs := by linarith
  -- assemble
  have hR : (P.ratioForm W Q T (P.aVec Q T)).re ≤
      (1 + δ₀) * W.H Q * (2 * Real.pi * P.Jlen T * ((1 + δ₀) * (L ^ 2 * ℓs * IFv) +
        C₂' * (L * M) * ℓs) +
        Cd * (cm * ((1 + δ₀) * (ℓs * (1 + 2 * P.ε₃) * (L * B₁)) + C₃' * 1 * ℓs))) +
      δ₀ * W.H Q * P.Jlen T * L ^ 2 * ℓs + C₁' * Q⁻¹ := by
    have hA : 0 ≤ (1 + δ₀) * W.H Q := by positivity
    have hS1 : S1 ≤ 2 * Real.pi * P.Jlen T * ((1 + δ₀) * (L ^ 2 * ℓs * IFv) +
        C₂' * (L * M) * ℓs) +
        Cd * (cm * ((1 + δ₀) * (ℓs * (1 + 2 * P.ε₃) * (L * B₁)) + C₃' * 1 * ℓs)) := by
      refine st3.trans (add_le_add ?_ ?_)
      · exact mul_le_mul_of_nonneg_left st4 (by positivity)
      · exact mul_le_mul_of_nonneg_left (st6.trans (mul_le_mul_of_nonneg_left st5 hcm0)) hCd0
    have := mul_le_mul_of_nonneg_left hS1 hA
    have st2' : (P.ratioForm W Q T (P.bVec Q T)).re ≤ (1 + δ₀) * W.H Q * S1 +
        δ₀ * W.H Q * P.Jlen T * L ^ 2 * ℓs := st2
    linarith
  -- error terms
  have eT1 : (1 + δ₀) * W.H Q * (2 * Real.pi * P.Jlen T * ((1 + δ₀) * (L ^ 2 * ℓs * IFv))) /
      (2 * Real.pi ^ 2) ≤
      W.H Q * P.Jlen T * L ^ 2 * ℓs * IFv / Real.pi + 3 * δ₀ * IFv / Real.pi * X := by
    have hsq : (1 + δ₀) * (1 + δ₀) ≤ 1 + 3 * δ₀ := by
      have h := mul_le_mul_of_nonneg_left hδ₀1 hδ₀.le
      have e : (1 + δ₀) * (1 + δ₀) = 1 + 2 * δ₀ + δ₀ * δ₀ := by ring
      rw [e]; linarith
    have e : (1 + δ₀) * W.H Q * (2 * Real.pi * P.Jlen T * ((1 + δ₀) * (L ^ 2 * ℓs * IFv))) /
        (2 * Real.pi ^ 2) =
        ((1 + δ₀) * (1 + δ₀)) * (W.H Q * P.Jlen T * L ^ 2 * ℓs * IFv / Real.pi) := by
      field_simp
    have hbase : 0 ≤ W.H Q * P.Jlen T * L ^ 2 * ℓs * IFv / Real.pi := by positivity
    have hJX : W.H Q * P.Jlen T * L ^ 2 * ℓs * IFv / Real.pi ≤ IFv / Real.pi * X := by
      rw [hX]
      have : W.H Q * P.Jlen T * L ^ 2 * ℓs ≤ W.H Q * T * L ^ 2 * ℓs := by gcongr
      have e2 : W.H Q * P.Jlen T * L ^ 2 * ℓs * IFv / Real.pi =
          IFv / Real.pi * (W.H Q * P.Jlen T * L ^ 2 * ℓs) := by ring
      rw [e2]
      exact mul_le_mul_of_nonneg_left this (by positivity)
    rw [e]
    calc (1 + δ₀) * (1 + δ₀) * (W.H Q * P.Jlen T * L ^ 2 * ℓs * IFv / Real.pi)
        ≤ (1 + 3 * δ₀) * (W.H Q * P.Jlen T * L ^ 2 * ℓs * IFv / Real.pi) :=
          mul_le_mul_of_nonneg_right hsq hbase
      _ = W.H Q * P.Jlen T * L ^ 2 * ℓs * IFv / Real.pi +
          3 * δ₀ * (W.H Q * P.Jlen T * L ^ 2 * ℓs * IFv / Real.pi) := by ring
      _ ≤ W.H Q * P.Jlen T * L ^ 2 * ℓs * IFv / Real.pi + 3 * δ₀ * (IFv / Real.pi * X) := by
          have : 0 ≤ 3 * δ₀ := by positivity
          linarith [mul_le_mul_of_nonneg_left hJX this]
      _ = _ := by ring
  have eT2 : (1 + δ₀) * W.H Q * (2 * Real.pi * P.Jlen T * (C₂' * (L * M) * ℓs)) /
      (2 * Real.pi ^ 2) ≤ δ / 5 * X := by
    have h1' : 10 * C₂' * M / Real.pi ≤ δ / 5 * L := by
      have h : (10 * C₂' * M / Real.pi) / (δ / 5) ≤ L := by
        have : 0 ≤ K₃ / (δ / 5) := by positivity
        linarith
      rw [div_le_iff₀ (by positivity)] at h
      linarith
    have e : (1 + δ₀) * W.H Q * (2 * Real.pi * P.Jlen T * (C₂' * (L * M) * ℓs)) /
        (2 * Real.pi ^ 2) =
        (1 + δ₀) * (W.H Q * P.Jlen T * L * ℓs) * (C₂' * M / Real.pi) := by field_simp
    rw [e, hX]
    have hA : (1 + δ₀) * (W.H Q * P.Jlen T * L * ℓs) ≤ 2 * (W.H Q * T * L * ℓs) := by
      have : W.H Q * P.Jlen T * L * ℓs ≤ W.H Q * T * L * ℓs := by gcongr
      have hA0 : 0 ≤ W.H Q * P.Jlen T * L * ℓs := by positivity
      have := mul_le_mul_of_nonneg_right (show 1 + δ₀ ≤ 2 by linarith) hA0
      linarith
    have hB0 : 0 ≤ C₂' * M / Real.pi := by
      have : 0 ≤ M := by linarith
      positivity
    have hT0 : 0 ≤ T := by linarith
    calc (1 + δ₀) * (W.H Q * P.Jlen T * L * ℓs) * (C₂' * M / Real.pi)
        ≤ 2 * (W.H Q * T * L * ℓs) * (C₂' * M / Real.pi) := mul_le_mul_of_nonneg_right hA hB0
      _ = (W.H Q * T * L * ℓs) * (10 * C₂' * M / Real.pi) / 5 := by ring
      _ ≤ (W.H Q * T * L * ℓs) * (δ / 5 * L) / 5 := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          exact mul_le_mul_of_nonneg_left h1' (by positivity)
      _ ≤ δ / 5 * (W.H Q * T * L ^ 2 * ℓs) := by
          have : 0 ≤ δ / 5 * (W.H Q * T * L ^ 2 * ℓs) := by positivity
          have e : W.H Q * T * L * ℓs * (δ / 5 * L) / 5 =
              δ / 5 * (W.H Q * T * L ^ 2 * ℓs) / 5 := by ring
          rw [e]; linarith
  have eT3 : (1 + δ₀) * W.H Q * (Cd * (cm * ((1 + δ₀) * (ℓs * (1 + 2 * P.ε₃) * (L * B₁)) +
      C₃' * 1 * ℓs))) / (2 * Real.pi ^ 2) ≤ δ / 5 * X := by
    have h2' : K₃ ≤ δ / 5 * L := by
      have h : K₃ / (δ / 5) ≤ L := by
        have : 0 ≤ (10 * C₂' * M / Real.pi) / (δ / 5) := by
          have : 0 ≤ M := by linarith
          positivity
        linarith
      rw [div_le_iff₀ (by positivity)] at h
      linarith
    have hε := P.ε₃_pos
    have hinner : Cd * (cm * ((1 + δ₀) * (ℓs * (1 + 2 * P.ε₃) * (L * B₁)) + C₃' * 1 * ℓs)) ≤
        Cd * cm * (2 * (1 + 2 * P.ε₃) * B₁ + C₃') * (L * ℓs) := by
      have hℓL : ℓs ≤ L * ℓs := le_mul_of_one_le_left hℓs0 hL1
      have h1 : (1 + δ₀) * (ℓs * (1 + 2 * P.ε₃) * (L * B₁)) ≤
          2 * (1 + 2 * P.ε₃) * B₁ * (L * ℓs) := by
        have : 0 ≤ ℓs * (1 + 2 * P.ε₃) * (L * B₁) := by positivity
        have e : 2 * (1 + 2 * P.ε₃) * B₁ * (L * ℓs) = 2 * (ℓs * (1 + 2 * P.ε₃) * (L * B₁)) := by
          ring
        rw [e]
        have := mul_le_mul_of_nonneg_right (show 1 + δ₀ ≤ 2 by linarith) this
        linarith
      have h2 : C₃' * 1 * ℓs ≤ C₃' * (L * ℓs) := by
        rw [mul_one]; exact mul_le_mul_of_nonneg_left hℓL hC₃'0
      have hsum := add_le_add h1 h2
      have e : Cd * cm * (2 * (1 + 2 * P.ε₃) * B₁ + C₃') * (L * ℓs) =
          Cd * (cm * (2 * (1 + 2 * P.ε₃) * B₁ * (L * ℓs) + C₃' * (L * ℓs))) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hcm0) hCd0
    have hA : (1 + δ₀) * W.H Q * (Cd * (cm * ((1 + δ₀) * (ℓs * (1 + 2 * P.ε₃) * (L * B₁)) +
        C₃' * 1 * ℓs))) ≤
        2 * W.H Q * (Cd * cm * (2 * (1 + 2 * P.ε₃) * B₁ + C₃') * (L * ℓs)) := by
      have hin0 : 0 ≤ Cd * (cm * ((1 + δ₀) * (ℓs * (1 + 2 * P.ε₃) * (L * B₁)) +
          C₃' * 1 * ℓs)) := by
        positivity
      calc (1 + δ₀) * W.H Q * (Cd * (cm * ((1 + δ₀) * (ℓs * (1 + 2 * P.ε₃) * (L * B₁)) +
            C₃' * 1 * ℓs)))
          ≤ 2 * W.H Q * (Cd * (cm * ((1 + δ₀) * (ℓs * (1 + 2 * P.ε₃) * (L * B₁)) +
            C₃' * 1 * ℓs))) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (show 1 + δ₀ ≤ 2 by linarith) hH0) hin0
        _ ≤ _ := mul_le_mul_of_nonneg_left hinner (by positivity)
    have e : 2 * W.H Q * (Cd * cm * (2 * (1 + 2 * P.ε₃) * B₁ + C₃') * (L * ℓs)) /
        (2 * Real.pi ^ 2) = K₃ * (W.H Q * L * ℓs) := by rw [hK₃]; field_simp
    calc _ ≤ 2 * W.H Q * (Cd * cm * (2 * (1 + 2 * P.ε₃) * B₁ + C₃') * (L * ℓs)) /
            (2 * Real.pi ^ 2) :=
          div_le_div_of_nonneg_right hA (by positivity)
      _ = K₃ * (W.H Q * L * ℓs) := e
      _ ≤ δ / 5 * L * (W.H Q * L * ℓs) := mul_le_mul_of_nonneg_right h2' (by positivity)
      _ ≤ δ / 5 * X := by
          rw [hX]
          have h0 : 0 ≤ δ / 5 * (W.H Q * L ^ 2 * ℓs) := by positivity
          have := mul_le_mul_of_nonneg_left hT1 h0
          have e : δ / 5 * L * (W.H Q * L * ℓs) = δ / 5 * (W.H Q * L ^ 2 * ℓs) * 1 := by
            ring
          rw [e]
          calc δ / 5 * (W.H Q * L ^ 2 * ℓs) * 1 ≤ δ / 5 * (W.H Q * L ^ 2 * ℓs) * T := this
            _ = δ / 5 * (W.H Q * T * L ^ 2 * ℓs) := by ring
  have eT4 : δ₀ * W.H Q * P.Jlen T * L ^ 2 * ℓs / (2 * Real.pi ^ 2) ≤ δ₀ * X := by
    rw [hX, div_le_iff₀ (by positivity)]
    have h0 : 0 ≤ δ₀ * W.H Q * L ^ 2 * ℓs := by positivity
    have hpi2 : 1 ≤ 2 * Real.pi ^ 2 := by
      have : (3 : ℝ) ^ 2 ≤ Real.pi ^ 2 := pow_le_pow_left₀ (by norm_num) Real.pi_gt_three.le 2
      linarith
    have h1 : δ₀ * W.H Q * P.Jlen T * L ^ 2 * ℓs ≤ δ₀ * W.H Q * T * L ^ 2 * ℓs := by gcongr
    have hX' : 0 ≤ δ₀ * (W.H Q * T * L ^ 2 * ℓs) := by
      have : 0 ≤ T := by linarith
      positivity
    have h2 := mul_le_mul_of_nonneg_left hpi2 hX'
    linarith
  have eT5 : C₁' * Q⁻¹ / (2 * Real.pi ^ 2) ≤ δ / 5 * X := by
    have hQ' : C₁' / (2 * Real.pi ^ 2 * (δ / 5)) ≤ Q := h3
    rw [div_le_iff₀ (by positivity)] at hQ'
    have hX1 : 1 ≤ X := by
      rw [hX]
      have hL2 : 1 ≤ L ^ 2 := one_le_pow₀ hL1
      have h1 : 1 ≤ W.H Q * T := one_le_mul_of_one_le_of_one_le hH1 hT1
      have h2 : 1 ≤ W.H Q * T * L ^ 2 := one_le_mul_of_one_le_of_one_le h1 hL2
      exact one_le_mul_of_one_le_of_one_le h2 hℓs1
    rw [div_le_iff₀ (by positivity)]
    have hQinv : C₁' * Q⁻¹ ≤ 2 * Real.pi ^ 2 * (δ / 5) := by
      rw [← div_eq_mul_inv, div_le_iff₀ hQ0]; linarith
    have : 2 * Real.pi ^ 2 * (δ / 5) ≤ δ / 5 * X * (2 * Real.pi ^ 2) := by
      have h0 : 0 ≤ 2 * Real.pi ^ 2 * (δ / 5) := by positivity
      have := mul_le_mul_of_nonneg_left hX1 h0
      linarith
    linarith
  -- conclude
  have hδsum : 3 * δ₀ * IFv / Real.pi * X + δ₀ * X ≤ δ / 5 * X := by
    have : 3 * δ₀ * IFv / Real.pi * X + δ₀ * X = δ₀ * (3 * IFv / Real.pi + 1) * X := by ring
    rw [this]; exact mul_le_mul_of_nonneg_right hδ₀δ hX0
  have hsplit : 1 / (2 * Real.pi ^ 2) * ((1 + δ₀) * W.H Q * (2 * Real.pi * P.Jlen T *
      ((1 + δ₀) * (L ^ 2 * ℓs * IFv) + C₂' * (L * M) * ℓs) +
        Cd * (cm * ((1 + δ₀) * (ℓs * (1 + 2 * P.ε₃) * (L * B₁)) + C₃' * 1 * ℓs))) +
      δ₀ * W.H Q * P.Jlen T * L ^ 2 * ℓs + C₁' * Q⁻¹) =
      (1 + δ₀) * W.H Q * (2 * Real.pi * P.Jlen T * ((1 + δ₀) * (L ^ 2 * ℓs * IFv))) /
        (2 * Real.pi ^ 2) +
      (1 + δ₀) * W.H Q * (2 * Real.pi * P.Jlen T * (C₂' * (L * M) * ℓs)) / (2 * Real.pi ^ 2) +
      (1 + δ₀) * W.H Q * (Cd * (cm * ((1 + δ₀) * (ℓs * (1 + 2 * P.ε₃) * (L * B₁)) +
        C₃' * 1 * ℓs))) / (2 * Real.pi ^ 2) +
      δ₀ * W.H Q * P.Jlen T * L ^ 2 * ℓs / (2 * Real.pi ^ 2) + C₁' * Q⁻¹ / (2 * Real.pi ^ 2) := by
    ring
  have hR' := mul_le_mul_of_nonneg_left hR (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi ^ 2))
  rw [hsplit] at hR'
  have hfin : W.H Q * P.Jlen T * L ^ 2 * ℓs * IFv / Real.pi + 3 * δ₀ * IFv / Real.pi * X +
      δ / 5 * X + δ / 5 * X + δ₀ * X + δ / 5 * X ≤
      W.H Q * P.Jlen T * L ^ 2 * ℓs * IFv / Real.pi + δ * X := by
    have := mul_nonneg hδ.le hX0
    linarith
  have := eT1; have := eT2; have := eT3; have := eT4; have := eT5
  linarith

end Families.Hybrid.S
