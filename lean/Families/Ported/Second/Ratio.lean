/-
# Prime side (paper §5): the ratio terms

`ratio_bound`: under the profile bound `eq:profile`,
`M^{rat}_{ΛΛ} = (1/2π²) Re ∑ a_n a_m Δ(n,m) 𝒦(n,m) ≤ H|J|L²ℓ I_F/π + o(HTL²ℓ)`
(proof of `prop:second`, Proposition 5.13), from `eqB:Mrat` (`a → b`), `eq:profile`, `eq:Kdiag` (`lemM1_diag`) and `lem:B2`
applied with `h(y) = c(y/ℓ) g(y)` (`hTest`) and with a fixed bump (`hOne`, for `∑ b_n² ≪ Lℓ`).
-/
import Families.Ported.Second.Mumu
import Families.Ported.Second.Profile

noncomputable section

open scoped BigOperators ContDiff
open Finset MeasureTheory Filter Topology

namespace Families.Ported.Second

open Families

set_option maxHeartbeats 1600000 in
/-- **Ratio terms** (proof of `prop:second`, Proposition 5.13). -/
theorem ratio_bound (hB2 : lemB2_Statement) (hMrat : eqBMrat_Statement) (hWH : lemWH_Statement)
    (P : PrimeSetup) (W : Weight) (c : ℝ → ℝ) (hc : ContDiff ℝ ∞ c) (hc1 : ∀ α, 1 ≤ c α)
    (hprof : P.ProfileBound W c) (δ : ℝ) (hδ : 0 < δ) :
    ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ P.heights Q,
      1 / (2 * Real.pi ^ 2) * (P.ratioForm W Q T (P.aVec Q)).re ≤
        W.H Q * P.Jlen T * P.L Q ^ 2 * ell Q * IF P c / Real.pi +
          δ * (W.H Q * T * P.L Q ^ 2 * ell Q) := by
  have hpi := Real.pi_pos
  have hl := P.lam_pos
  have hIF := IF_nonneg (P := P) hc1
  set IFv := IF P c with hIFv
  -- the small parameter
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
  obtain ⟨Cd, hCd⟩ := lemM1_diag P
  obtain ⟨M, hM1, hMb⟩ := Hc_bounded (P := P) hc
  choose D hD0 hD using fun i => Hc_iteratedDeriv_bounded (P := P) hc i
  choose D' hD'0 hD' using fun i => Bmp_iteratedDeriv_bounded i
  obtain ⟨C₂, Q₃, hB⟩ := hB2 P D δ₀ hδ₀
  obtain ⟨C₃, Q₄, hB'⟩ := hB2 P D' δ₀ hδ₀
  obtain ⟨cH, Q₅, hcH, hH⟩ := H_lower hWH W
  obtain ⟨cmax, hcmax⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (0 : ℝ) 6) hc.continuous.continuousOn
  -- nonnegative versions of the constants
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
  -- eventualities
  have e1 := eventually_const_le_ell (10 * C₂' * M / Real.pi) (ε := δ / 5 * P.lam) (by positivity)
  have e2 := eventually_const_le_ell K₃ (ε := δ / 5 * P.lam) (by positivity)
  have e3 : ∀ᶠ Q : ℝ in atTop, C₁' / (2 * Real.pi ^ 2 * (δ / 5)) ≤ Q := eventually_ge_atTop _
  have e4 : ∀ᶠ Q : ℝ in atTop, Real.exp 1 ≤ Q := eventually_ge_atTop _
  have e5 : ∀ᶠ Q : ℝ in atTop, Real.exp (1 / P.lam) ≤ Q := eventually_ge_atTop _
  have e6 : ∀ᶠ Q : ℝ in atTop, max (max Q₁ Q₂) (max (max Q₃ Q₄) Q₅) ≤ Q := eventually_ge_atTop _
  have e7 : ∀ᶠ Q : ℝ in atTop, 1 / cH ≤ Q := eventually_ge_atTop _
  obtain ⟨Q₀, hQ₀⟩ := Filter.eventually_atTop.mp
    (e1.and (e2.and (e3.and (e4.and (e5.and (e6.and e7))))))
  refine ⟨Q₀, fun Q hQ T hT => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hQ₀ Q hQ
  have hQ1' : Q₁ ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h6
  have hQ2' : Q₂ ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h6
  have hQ3' : Q₃ ≤ Q :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) h6
  have hQ4' : Q₄ ≤ Q :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_right _ _))) h6
  have hQ5' : Q₅ ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) h6
  have hQ1 : 1 < Q := lt_of_lt_of_le (by have := Real.add_one_le_exp (1 : ℝ); linarith) h4
  have hQ0 : 0 < Q := by linarith
  obtain ⟨hT1, -⟩ := heights_facts P h4 hT
  have hℓ1 : 1 ≤ ell Q := by
    unfold ell; have := Real.log_le_log (Real.exp_pos _) h4; rwa [Real.log_exp] at this
  have hL1 : 1 ≤ P.L Q := Families.Phase3.C.one_le_L P h5
  have hLdef : P.L Q = P.lam * ell Q := rfl
  have hH0 : 0 ≤ W.H Q := Families.Weight.H_nonneg W Q
  have hH1 : 1 ≤ W.H Q := by
    have h := hH Q hQ5'
    have hQ' : 1 ≤ cH * Q := by rw [div_le_iff₀ hcH] at h7; linarith
    have e : cH * Q ^ 2 = (cH * Q) * Q := by ring
    have := mul_le_mul hQ' hQ1.le zero_le_one (by linarith)
    linarith
  have hJlen : P.Jlen T ≤ T := by
    unfold PrimeSetup.Jlen
    have : 0 ≤ 2 * P.θ * T := by have := P.θ_pos; positivity
    linarith
  have hJlen0 : 0 ≤ P.Jlen T := by
    unfold PrimeSetup.Jlen
    exact mul_nonneg (by linarith [P.θ_lt]) (by linarith)
  set X := W.H Q * T * P.L Q ^ 2 * ell Q with hX
  have hX0 : 0 ≤ X := by positivity
  -- the sums
  set b := P.bVec Q T
  set S1 := ∑ n ∈ P.range Q, b n ^ 2 * c (Real.log n / ell Q) * (P.𝒦 Q T n n).re
  set Sh := ∑ n ∈ P.range Q, b n ^ 2 * hTest P c Q (Real.log n)
  set S0 := ∑ n ∈ P.range Q, b n ^ 2 * c (Real.log n / ell Q)
  set Sb := ∑ n ∈ P.range Q, b n ^ 2 * hOne P Q (Real.log n)
  -- (1) `eqB:Mrat`
  have st1 : (P.ratioForm W Q T (P.aVec Q)).re ≤
      (P.ratioForm W Q T (P.bVec Q T)).re + C₁' * Q⁻¹ := by
    have h := hM Q hQ1' T hT
    rw [Real.rpow_neg_one] at h
    have hre := Complex.re_le_norm (P.ratioForm W Q T (P.aVec Q) - P.ratioForm W Q T (P.bVec Q T))
    rw [Complex.sub_re] at hre
    have : C₁ * Q⁻¹ ≤ C₁' * Q⁻¹ :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_nonneg.mpr hQ0.le)
    linarith
  -- (2) the profile bound
  have st2 := hP Q hQ2' T hT
  -- (3) `eq:Kdiag`
  have st3 : S1 ≤ 2 * Real.pi * P.Jlen T * Sh + Cd * S0 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn1 := (SC.mem_range_le P hn).1
    have hK := hCd Q T hQ1 (by linarith) n hn1
    have hre : (P.𝒦 Q T n n).re ≤ 2 * Real.pi * P.Jlen T * P.g Q (Real.log n) + Cd := by
      have h' := Complex.re_le_norm (P.𝒦 Q T n n - 2 * Real.pi * P.Jlen T * P.g Q (Real.log n))
      have e : (P.𝒦 Q T n n - 2 * Real.pi * P.Jlen T * P.g Q (Real.log n)).re =
          (P.𝒦 Q T n n).re - 2 * Real.pi * P.Jlen T * P.g Q (Real.log n) := by
        simp [Complex.sub_re, Complex.mul_re]
      rw [e] at h'
      linarith
    have hbc : 0 ≤ b n ^ 2 * c (Real.log n / ell Q) :=
      mul_nonneg (sq_nonneg _) (le_trans zero_le_one (hc1 _))
    rw [hTest_eq hQ1]
    calc b n ^ 2 * c (Real.log n / ell Q) * (P.𝒦 Q T n n).re
        ≤ b n ^ 2 * c (Real.log n / ell Q) * (2 * Real.pi * P.Jlen T * P.g Q (Real.log n) + Cd) :=
          mul_le_mul_of_nonneg_left hre hbc
      _ = 2 * Real.pi * P.Jlen T * (b n ^ 2 * (c (Real.log n / ell Q) * P.g Q (Real.log n))) +
          Cd * (b n ^ 2 * c (Real.log n / ell Q)) := by ring
  -- (4) `lem:B2` with `h = hTest`
  have st4 : Sh ≤ (1 + δ₀) * (P.L Q ^ 2 * ell Q * IFv) + C₂' * (P.L Q * M) * ell Q := by
    have h := hB Q hQ3' T hT (hTest P c Q) (P.L Q * M) (hTest_contDiff hc Q) (hTest_nonneg hc1 hQ1)
      (hTest_integrable hc hQ1) (hTest_le hMb hQ1)
      (fun i y => hTest_deriv_bound hc hM1 i (hD i) hL1 y)
    rw [integral_hTest hQ1] at h
    have : C₂ * (P.L Q * M) * ell Q ≤ C₂' * (P.L Q * M) * ell Q := by
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg (by linarith) (by linarith))
    linarith
  -- (5) `∑ b² ≪ Lℓ` with `h = hOne`
  have st5 : Sb ≤ (1 + δ₀) * (ell Q * (1 + 2 * P.ε₃) * (P.L Q * B₁)) + C₃' * 1 * ell Q := by
    have h := hB' Q hQ4' T hT (hOne P Q) 1 (hOne_contDiff Q) (hOne_nonneg Q)
      (hOne_integrable hQ1) (hOne_le Q) (fun i y => hOne_deriv_bound i (hD' i) hL1 y)
    have hi := integral_hOne_le (P := P) hQ1
    have : C₃ * 1 * ell Q ≤ C₃' * 1 * ell Q := by
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) zero_le_one
    have : (1 + δ₀) * (∫ s, ell Q * Fb P.ε₃ (s / ell Q) * hOne P Q s) ≤
        (1 + δ₀) * (ell Q * (1 + 2 * P.ε₃) * (P.L Q * B₁)) :=
      mul_le_mul_of_nonneg_left hi (by linarith)
    linarith
  have st6 : S0 ≤ cm * Sb := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have hL0 : 0 ≤ P.L Q := by linarith
    obtain ⟨hl0, hl3⟩ := SC.log_le_of_mem_range P hL0 hn
    rw [hOne_one hQ1 hn, mul_one]
    have hmem : Real.log n / ell Q ∈ Set.Icc (0 : ℝ) 6 := by
      refine ⟨div_nonneg hl0 (by linarith), ?_⟩
      rw [div_le_iff₀ (by linarith)]
      have : P.L Q ≤ 2 * ell Q := by
        rw [hLdef]; exact mul_le_mul_of_nonneg_right P.lam_lt.le (by linarith)
      linarith
    have hcle : c (Real.log n / ell Q) ≤ cm := by
      have := hcmax _ hmem
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_max_left _ _))
    calc b n ^ 2 * c (Real.log n / ell Q) ≤ b n ^ 2 * cm := mul_le_mul_of_nonneg_left hcle (sq_nonneg _)
      _ = cm * b n ^ 2 := by ring
  -- nonnegativity
  have hSh0 : 0 ≤ Sh := Finset.sum_nonneg fun n _ =>
    mul_nonneg (sq_nonneg _) (hTest_nonneg hc1 hQ1 _)
  have hcm0 : 0 ≤ cm := le_trans zero_le_one (le_max_right _ _)
  have hC₂'0 : 0 ≤ C₂' := le_max_right _ _
  have hC₃'0 : 0 ≤ C₃' := le_max_right _ _
  have hC₁'0 : 0 ≤ C₁' := le_max_right _ _
  -- assemble
  have hR : (P.ratioForm W Q T (P.aVec Q)).re ≤
      (1 + δ₀) * W.H Q * (2 * Real.pi * P.Jlen T * ((1 + δ₀) * (P.L Q ^ 2 * ell Q * IFv) + C₂' * (P.L Q * M) * ell Q) +
        Cd * (cm * ((1 + δ₀) * (ell Q * (1 + 2 * P.ε₃) * (P.L Q * B₁)) + C₃' * 1 * ell Q))) +
      δ₀ * W.H Q * P.Jlen T * P.L Q ^ 2 * ell Q + C₁' * Q⁻¹ := by
    have hA : 0 ≤ (1 + δ₀) * W.H Q := by positivity
    have hS1 : S1 ≤ 2 * Real.pi * P.Jlen T * ((1 + δ₀) * (P.L Q ^ 2 * ell Q * IFv) + C₂' * (P.L Q * M) * ell Q) +
        Cd * (cm * ((1 + δ₀) * (ell Q * (1 + 2 * P.ε₃) * (P.L Q * B₁)) + C₃' * 1 * ell Q)) := by
      refine st3.trans (add_le_add ?_ ?_)
      · exact mul_le_mul_of_nonneg_left st4 (by positivity)
      · exact mul_le_mul_of_nonneg_left (st6.trans (mul_le_mul_of_nonneg_left st5 hcm0)) hCd0
    have := mul_le_mul_of_nonneg_left hS1 hA
    have st2' : (P.ratioForm W Q T (P.bVec Q T)).re ≤ (1 + δ₀) * W.H Q * S1 + δ₀ * W.H Q * P.Jlen T * P.L Q ^ 2 * ell Q :=
      st2
    linarith
  -- error terms
  have eT1 : (1 + δ₀) * W.H Q * (2 * Real.pi * P.Jlen T * ((1 + δ₀) * (P.L Q ^ 2 * ell Q * IFv))) / (2 * Real.pi ^ 2) ≤
      W.H Q * P.Jlen T * P.L Q ^ 2 * ell Q * IFv / Real.pi + 3 * δ₀ * IFv / Real.pi * X := by
    have hsq : (1 + δ₀) * (1 + δ₀) ≤ 1 + 3 * δ₀ := by
      have h := mul_le_mul_of_nonneg_left hδ₀1 hδ₀.le
      have e : (1 + δ₀) * (1 + δ₀) = 1 + 2 * δ₀ + δ₀ * δ₀ := by ring
      rw [e]; linarith
    have e : (1 + δ₀) * W.H Q * (2 * Real.pi * P.Jlen T * ((1 + δ₀) * (P.L Q ^ 2 * ell Q * IFv))) / (2 * Real.pi ^ 2) =
        ((1 + δ₀) * (1 + δ₀)) * (W.H Q * P.Jlen T * P.L Q ^ 2 * ell Q * IFv / Real.pi) := by
      field_simp
    have hbase : 0 ≤ W.H Q * P.Jlen T * P.L Q ^ 2 * ell Q * IFv / Real.pi := by positivity
    have hJX : W.H Q * P.Jlen T * P.L Q ^ 2 * ell Q * IFv / Real.pi ≤ IFv / Real.pi * X := by
      rw [hX]
      have : W.H Q * P.Jlen T * P.L Q ^ 2 * ell Q ≤ W.H Q * T * P.L Q ^ 2 * ell Q := by
        have h0 : 0 ≤ W.H Q * P.L Q ^ 2 * ell Q := by positivity
        linarith [mul_le_mul_of_nonneg_left hJlen h0]
      have e2 : W.H Q * P.Jlen T * P.L Q ^ 2 * ell Q * IFv / Real.pi = IFv / Real.pi * (W.H Q * P.Jlen T * P.L Q ^ 2 * ell Q) := by ring
      rw [e2]
      exact mul_le_mul_of_nonneg_left this (by positivity)
    rw [e]
    calc (1 + δ₀) * (1 + δ₀) * (W.H Q * P.Jlen T * P.L Q ^ 2 * ell Q * IFv / Real.pi)
        ≤ (1 + 3 * δ₀) * (W.H Q * P.Jlen T * P.L Q ^ 2 * ell Q * IFv / Real.pi) :=
          mul_le_mul_of_nonneg_right hsq hbase
      _ = W.H Q * P.Jlen T * P.L Q ^ 2 * ell Q * IFv / Real.pi + 3 * δ₀ * (W.H Q * P.Jlen T * P.L Q ^ 2 * ell Q * IFv / Real.pi) := by ring
      _ ≤ W.H Q * P.Jlen T * P.L Q ^ 2 * ell Q * IFv / Real.pi + 3 * δ₀ * (IFv / Real.pi * X) := by
          have : 0 ≤ 3 * δ₀ := by positivity
          linarith [mul_le_mul_of_nonneg_left hJX this]
      _ = _ := by ring
  have eT2 : (1 + δ₀) * W.H Q * (2 * Real.pi * P.Jlen T * (C₂' * (P.L Q * M) * ell Q)) / (2 * Real.pi ^ 2) ≤
      δ / 5 * X := by
    have h1' : 10 * C₂' * M / Real.pi ≤ δ / 5 * P.L Q := by
      rw [hLdef]; unfold ell; linarith
    have e : (1 + δ₀) * W.H Q * (2 * Real.pi * P.Jlen T * (C₂' * (P.L Q * M) * ell Q)) / (2 * Real.pi ^ 2) =
        (1 + δ₀) * (W.H Q * P.Jlen T * P.L Q * ell Q) * (C₂' * M / Real.pi) := by field_simp
    rw [e, hX]
    have hA : (1 + δ₀) * (W.H Q * P.Jlen T * P.L Q * ell Q) ≤ 2 * (W.H Q * T * P.L Q * ell Q) := by
      have h0 : 0 ≤ W.H Q * P.L Q * ell Q := by positivity
      have : W.H Q * P.Jlen T * P.L Q * ell Q ≤ W.H Q * T * P.L Q * ell Q := by
        linarith [mul_le_mul_of_nonneg_left hJlen h0]
      have hA0 : 0 ≤ W.H Q * P.Jlen T * P.L Q * ell Q := by positivity
      have := mul_le_mul_of_nonneg_right (show 1 + δ₀ ≤ 2 by linarith) hA0
      linarith
    have hB0 : 0 ≤ C₂' * M / Real.pi := by
      have : 0 ≤ M := by linarith
      positivity
    calc (1 + δ₀) * (W.H Q * P.Jlen T * P.L Q * ell Q) * (C₂' * M / Real.pi)
        ≤ 2 * (W.H Q * T * P.L Q * ell Q) * (C₂' * M / Real.pi) := mul_le_mul_of_nonneg_right hA hB0
      _ = (W.H Q * T * P.L Q * ell Q) * (10 * C₂' * M / Real.pi) / 5 := by ring
      _ ≤ (W.H Q * T * P.L Q * ell Q) * (δ / 5 * P.L Q) / 5 := by
          apply div_le_div_of_nonneg_right _ (by norm_num)
          exact mul_le_mul_of_nonneg_left h1' (by positivity)
      _ ≤ δ / 5 * (W.H Q * T * P.L Q ^ 2 * ell Q) := by
          have : 0 ≤ δ / 5 * (W.H Q * T * P.L Q ^ 2 * ell Q) := by positivity
          have e : W.H Q * T * P.L Q * ell Q * (δ / 5 * P.L Q) / 5 =
              δ / 5 * (W.H Q * T * P.L Q ^ 2 * ell Q) / 5 := by ring
          rw [e]; linarith
  have eT3 : (1 + δ₀) * W.H Q * (Cd * (cm * ((1 + δ₀) * (ell Q * (1 + 2 * P.ε₃) * (P.L Q * B₁)) +
      C₃' * 1 * ell Q))) / (2 * Real.pi ^ 2) ≤ δ / 5 * X := by
    have h2' : K₃ ≤ δ / 5 * P.L Q := by
      rw [hLdef]; unfold ell; linarith
    have hε := P.ε₃_pos
    have hinner : Cd * (cm * ((1 + δ₀) * (ell Q * (1 + 2 * P.ε₃) * (P.L Q * B₁)) + C₃' * 1 * ell Q)) ≤
        Cd * cm * (2 * (1 + 2 * P.ε₃) * B₁ + C₃') * (P.L Q * ell Q) := by
      have hℓL : ell Q ≤ P.L Q * ell Q := le_mul_of_one_le_left (by linarith) hL1
      have h1 : (1 + δ₀) * (ell Q * (1 + 2 * P.ε₃) * (P.L Q * B₁)) ≤ 2 * (1 + 2 * P.ε₃) * B₁ * (P.L Q * ell Q) := by
        have : 0 ≤ ell Q * (1 + 2 * P.ε₃) * (P.L Q * B₁) := by positivity
        have e : 2 * (1 + 2 * P.ε₃) * B₁ * (P.L Q * ell Q) = 2 * (ell Q * (1 + 2 * P.ε₃) * (P.L Q * B₁)) := by ring
        rw [e]
        have := mul_le_mul_of_nonneg_right (show 1 + δ₀ ≤ 2 by linarith) this
        linarith
      have h2 : C₃' * 1 * ell Q ≤ C₃' * (P.L Q * ell Q) := by
        rw [mul_one]; exact mul_le_mul_of_nonneg_left hℓL hC₃'0
      have hsum := add_le_add h1 h2
      have e : Cd * cm * (2 * (1 + 2 * P.ε₃) * B₁ + C₃') * (P.L Q * ell Q) =
          Cd * (cm * (2 * (1 + 2 * P.ε₃) * B₁ * (P.L Q * ell Q) + C₃' * (P.L Q * ell Q))) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum hcm0) hCd0
    have hA : (1 + δ₀) * W.H Q * (Cd * (cm * ((1 + δ₀) * (ell Q * (1 + 2 * P.ε₃) * (P.L Q * B₁)) +
        C₃' * 1 * ell Q))) ≤ 2 * W.H Q * (Cd * cm * (2 * (1 + 2 * P.ε₃) * B₁ + C₃') * (P.L Q * ell Q)) := by
      have hin0 : 0 ≤ Cd * (cm * ((1 + δ₀) * (ell Q * (1 + 2 * P.ε₃) * (P.L Q * B₁)) + C₃' * 1 * ell Q)) := by
        positivity
      calc (1 + δ₀) * W.H Q * (Cd * (cm * ((1 + δ₀) * (ell Q * (1 + 2 * P.ε₃) * (P.L Q * B₁)) + C₃' * 1 * ell Q)))
          ≤ 2 * W.H Q * (Cd * (cm * ((1 + δ₀) * (ell Q * (1 + 2 * P.ε₃) * (P.L Q * B₁)) + C₃' * 1 * ell Q))) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (show 1 + δ₀ ≤ 2 by linarith) hH0) hin0
        _ ≤ _ := mul_le_mul_of_nonneg_left hinner (by positivity)
    have e : 2 * W.H Q * (Cd * cm * (2 * (1 + 2 * P.ε₃) * B₁ + C₃') * (P.L Q * ell Q)) / (2 * Real.pi ^ 2) =
        K₃ * (W.H Q * P.L Q * ell Q) := by rw [hK₃]; field_simp
    calc _ ≤ 2 * W.H Q * (Cd * cm * (2 * (1 + 2 * P.ε₃) * B₁ + C₃') * (P.L Q * ell Q)) / (2 * Real.pi ^ 2) :=
          div_le_div_of_nonneg_right hA (by positivity)
      _ = K₃ * (W.H Q * P.L Q * ell Q) := e
      _ ≤ δ / 5 * P.L Q * (W.H Q * P.L Q * ell Q) := mul_le_mul_of_nonneg_right h2' (by positivity)
      _ ≤ δ / 5 * X := by
          rw [hX]
          have h0 : 0 ≤ δ / 5 * (W.H Q * P.L Q ^ 2 * ell Q) := by positivity
          have := mul_le_mul_of_nonneg_left hT1 h0
          have e : δ / 5 * P.L Q * (W.H Q * P.L Q * ell Q) = δ / 5 * (W.H Q * P.L Q ^ 2 * ell Q) * 1 := by
            ring
          rw [e]
          calc δ / 5 * (W.H Q * P.L Q ^ 2 * ell Q) * 1 ≤ δ / 5 * (W.H Q * P.L Q ^ 2 * ell Q) * T :=
                this
            _ = δ / 5 * (W.H Q * T * P.L Q ^ 2 * ell Q) := by ring
  have eT4 : δ₀ * W.H Q * P.Jlen T * P.L Q ^ 2 * ell Q / (2 * Real.pi ^ 2) ≤ δ₀ * X := by
    rw [hX, div_le_iff₀ (by positivity)]
    have h0 : 0 ≤ δ₀ * W.H Q * P.L Q ^ 2 * ell Q := by positivity
    have hpi2 : 1 ≤ 2 * Real.pi ^ 2 := by
      have : (3 : ℝ) ^ 2 ≤ Real.pi ^ 2 := pow_le_pow_left₀ (by norm_num) Real.pi_gt_three.le 2
      linarith
    have h1 : δ₀ * W.H Q * P.Jlen T * P.L Q ^ 2 * ell Q ≤ δ₀ * W.H Q * T * P.L Q ^ 2 * ell Q := by
      linarith [mul_le_mul_of_nonneg_left hJlen h0]
    have hX' : 0 ≤ δ₀ * (W.H Q * T * P.L Q ^ 2 * ell Q) := by positivity
    have h2 := mul_le_mul_of_nonneg_left hpi2 hX'
    linarith
  have eT5 : C₁' * Q⁻¹ / (2 * Real.pi ^ 2) ≤ δ / 5 * X := by
    have hQ' : C₁' / (2 * Real.pi ^ 2 * (δ / 5)) ≤ Q := h3
    rw [div_le_iff₀ (by positivity)] at hQ'
    have hX1 : 1 ≤ X := by
      rw [hX]
      have hL2 : 1 ≤ P.L Q ^ 2 := one_le_pow₀ hL1
      have h1 : 1 ≤ W.H Q * T := one_le_mul_of_one_le_of_one_le hH1 hT1
      have h2 : 1 ≤ W.H Q * T * P.L Q ^ 2 := one_le_mul_of_one_le_of_one_le h1 hL2
      exact one_le_mul_of_one_le_of_one_le h2 hℓ1
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
      ((1 + δ₀) * (P.L Q ^ 2 * ell Q * IFv) + C₂' * (P.L Q * M) * ell Q) +
        Cd * (cm * ((1 + δ₀) * (ell Q * (1 + 2 * P.ε₃) * (P.L Q * B₁)) + C₃' * 1 * ell Q))) +
      δ₀ * W.H Q * P.Jlen T * P.L Q ^ 2 * ell Q + C₁' * Q⁻¹) =
      (1 + δ₀) * W.H Q * (2 * Real.pi * P.Jlen T * ((1 + δ₀) * (P.L Q ^ 2 * ell Q * IFv))) / (2 * Real.pi ^ 2) +
      (1 + δ₀) * W.H Q * (2 * Real.pi * P.Jlen T * (C₂' * (P.L Q * M) * ell Q)) / (2 * Real.pi ^ 2) +
      (1 + δ₀) * W.H Q * (Cd * (cm * ((1 + δ₀) * (ell Q * (1 + 2 * P.ε₃) * (P.L Q * B₁)) +
        C₃' * 1 * ell Q))) / (2 * Real.pi ^ 2) +
      δ₀ * W.H Q * P.Jlen T * P.L Q ^ 2 * ell Q / (2 * Real.pi ^ 2) + C₁' * Q⁻¹ / (2 * Real.pi ^ 2) := by ring
  have hR' := mul_le_mul_of_nonneg_left hR (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi ^ 2))
  rw [hsplit] at hR'
  have hfin : W.H Q * P.Jlen T * P.L Q ^ 2 * ell Q * IFv / Real.pi + 3 * δ₀ * IFv / Real.pi * X + δ / 5 * X +
      δ / 5 * X + δ₀ * X + δ / 5 * X ≤ W.H Q * P.Jlen T * P.L Q ^ 2 * ell Q * IFv / Real.pi + δ * X := by
    have := mul_nonneg hδ.le hX0
    linarith
  have := eT1; have := eT2; have := eT3; have := eT4; have := eT5
  linarith

end Families.Ported.Second
