/-
**`prop:TIsharp`** (Proposition 6.24), the band-device interface:
`Families.Phase3.C.propTIsharp_proof (hMV : MV_LargeSieve) (hWH : lemWH_Statement) : propTIsharp_Statement`.

Route (the TeX's Steps 0–5, see `TIsharpBasic`, `TIsharpFarey`, `TIsharpNorms`, `TIsharpLocal`,
`TIsharpLevels`, `TIsharpStep5`); the only deviations are in the proof, not the statement:
* the localisation scale is the fixed `δ = 1/4` (the TeX's `δ = T^{−1/2}` is not needed: the tails
  are `≪ κ^{−1} Q² L³ = o(H|J|L²ℓ)` because `|J| ≍ T ≥ ℓ^{a₀} → ∞`);
* the splitting parameter `κ` of `lem:M3`(i)/`eqC:seminorm` is a fixed small multiple of the target
  `δ'` (the TeX takes `κ_T = T^{−1/4}`); the `o(1)` of the statement absorbs `(1+κ)³`;
* in regime (iii) the sharp large sieve and the large sieves are applied on all of `[1, Y]` (an interval
  of `⌊Y⌋ ≤ Q^{2−ε₁}` integers), which is allowed since `x_b^s(u)` lies in `[1, Y]`;
* `‖a‖² ≪ L²` and `‖a♯‖² ≪ (1+ℓ)(1+L)` are proved without PNT (`TIsharpNorms`).

Proved inputs used: `propSharpLS` (given `lemWH_Statement`; `Families.Wired.Phase1`), `CTp_ge_one`,
`H_lower_eventually` (`Families.Assembly`), `lemOmega_ac`, `lemmaS_rough`, `lemM2`, `lemM3_i`,
`lemM3_iii_iv`, `lemM1_diag`, `ratioForm_re_eq` (`lem:M1`), `famForm_ab_close` (Step 0, via `lem:B1`),
and `lem:B2` step-(4) machinery (`piece_e`, `Fh_deriv_bound`) with `h ≡ 1`. The classical
input `MV_LargeSieve` enters through `eq:MVLS` (tails, prime powers) and the additive large sieve
(levels `e ≤ E₀`). Hypotheses of `propTIsharp_Statement` not needed by this proof: `ε < ε₁/4`, the
smoothness of `C̃_ε`, `C̃_ε ≤ C_max`, `C̃_ε = 1` on `(−∞, 1−2ε]` and `C̃_ε = C_T^+` on `[1+2ε, ∞)`.
-/
import Families.Phase3.C.TIsharpErr

noncomputable section

open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory Filter Topology

namespace Families.Phase3.C

open Families

/-! ### Asymptotic facts -/

/-- The error term of `prop:sharpLS` tends to `0`. -/
lemma sharpLS_err_tendsto (W : Weight) (c : ℝ) {ε : ℝ} (hε : 0 < ε) (C : ℝ) :
    Tendsto (fun Q : ℝ => c * ((W.Vw + W.wtmax * W.η⁻¹ ^ 2) / W.Iw * Q ^ (-ε / 4) *
      Real.log Q ^ 3 + (Q ^ (-ε / 2) + W.Vw / W.Iw * Q ^ (-(1 / 2 : ℝ))) * C)) atTop (𝓝 0) := by
  set A := (W.Vw + W.wtmax * W.η⁻¹ ^ 2) / W.Iw
  set B := W.Vw / W.Iw
  have h1 : Tendsto (fun Q : ℝ => Q ^ (-ε / 4) * Real.log Q ^ 3) atTop (𝓝 0) := by
    have := tendsto_rpow_neg_mul_log_pow (r := ε / 4) (by linarith) 3
    refine this.congr' (Eventually.of_forall fun Q => ?_)
    rw [neg_div]
  have h2 : Tendsto (fun Q : ℝ => Q ^ (-ε / 2)) atTop (𝓝 0) := by
    have := tendsto_rpow_neg_atTop (y := ε / 2) (by linarith)
    refine this.congr' (Eventually.of_forall fun Q => ?_)
    rw [neg_div]
  have h3 : Tendsto (fun Q : ℝ => Q ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by norm_num)
  have := ((h1.const_mul A).add ((h2.add (h3.const_mul B)).mul_const C)).const_mul c
  simp only [mul_zero, add_zero, zero_mul] at this
  refine this.congr' (Eventually.of_forall fun Q => ?_)
  simp only [mul_assoc]

lemma eventually_le_log_rpow {a B : ℝ} (ha : 0 < a) :
    ∀ᶠ Q : ℝ in atTop, B ≤ Real.log Q ^ a :=
  ((tendsto_rpow_atTop ha).comp Real.tendsto_log_atTop).eventually_ge_atTop B

lemma eventually_le_mul_sq {B c : ℝ} (hc : 0 < c) : ∀ᶠ Q : ℝ in atTop, B ≤ c * Q ^ 2 := by
  have : Tendsto (fun Q : ℝ => c * Q ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num)).const_mul_atTop hc
  exact this.eventually_ge_atTop B

lemma sum_sq_bVec_le (P : PrimeSetup) (Q T : ℝ) :
    ∑ n ∈ P.range Q, P.bVec Q T n ^ 2 ≤
      2 * ∑ n ∈ P.range Q, P.aVec Q n ^ 2 + 2 * ∑ n ∈ P.range Q, P.aSharp Q T n ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun n _ => ?_
  unfold PrimeSetup.bVec
  nlinarith [sq_nonneg (P.aVec Q n + P.aSharp Q T n)]

lemma sum_sq_mul_𝒦_le (P : PrimeSetup) {Q T Kmax : ℝ} (y : ℕ → ℝ)
    (hK : ∀ n ∈ P.range Q, (P.𝒦 Q T n n).re ≤ Kmax) :
    ∑ n ∈ P.range Q, y n ^ 2 * (P.𝒦 Q T n n).re ≤ Kmax * ∑ n ∈ P.range Q, y n ^ 2 := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun n hn => by
    rw [mul_comm Kmax]; exact mul_le_mul_of_nonneg_left (hK n hn) (sq_nonneg _)

/-! ### `prop:TIsharp` -/

set_option maxHeartbeats 400000 in
/-- **`prop:TIsharp`** (band device), from the large sieve `MV_LargeSieve` and `lem:WH`. -/
theorem propTIsharp_proof (hMV : MV_LargeSieve) (hWH : lemWH_Statement) :
    propTIsharp_Statement := by
  intro P W hCT ε hε hε3 _hεε₁ Cband hCband hband Ct _ hCtr _ hCtband hCtCT _ δ' hδ'
  obtain ⟨C₀, hmult, hadd⟩ := hMV
  set C₀' := max C₀ 0 with hC₀'
  have hC₀'0 : 0 ≤ C₀' := le_max_right _ _
  -- the parameters `η`, `d`, `κ`
  set η := min δ' 1 with hη
  have hη0 : 0 < η := lt_min hδ' one_pos
  have hη1 : η ≤ 1 := min_le_right _ _
  have hηδ : η ≤ δ' := min_le_left _ _
  set d := η / 4 with hd
  set κ := η / 10 with hκ
  have hd0 : 0 < d := by positivity
  have hκ0 : 0 < κ := by positivity
  have hκ1 : κ ≤ 1 := by linarith
  have hfac : (1 + κ) ^ 3 * (1 + d) ≤ 1 + δ' := by
    have : (1 + κ) ^ 3 * (1 + d) ≤ 1 + η := by
      rw [hκ, hd]; nlinarith [sq_nonneg η, mul_pos hη0 hη0, pow_pos hη0 3, pow_pos hη0 4]
    linarith
  set CT := (CTp W).toReal with hCTdef
  have hSharpAll := propSharpLS hWH
  have hCT1 : 1 ≤ CT := CTp_ge_one hSharpAll hWH W hCT
  have hCt1 : ∀ α, 1 ≤ Ct α := fun α => (hCtr α).1
  -- the constants
  obtain ⟨Cab, Qab, hCab0, hab⟩ := famForm_ab_close P W 3 (by norm_num)
  obtain ⟨Qi, hi⟩ := regime_i_bound P hWH W hε (by linarith) hd0
  obtain ⟨Qii, hii⟩ := regime_ii_bound P W hε hε3 hband hd0
  obtain ⟨CF, QF, hCF0, hF⟩ := levelForm_xsSharp_le P hadd W
  obtain ⟨cS, hcS⟩ := hSharpAll
  set ε' := min P.ε₁ (1 / 2) with hε'
  have hε'0 : 0 < ε' := lt_min P.ε₁_pos (by norm_num)
  obtain ⟨QS, hS⟩ := hcS ε' hε'0 (lt_of_le_of_lt (min_le_right _ _) (by norm_num)) W hCT
  obtain ⟨Cs, Qs, hCs0, hs⟩ := sum_sq_aSharp_le P
  obtain ⟨Cd, hCd0, hKd⟩ := 𝒦_diag_re_le P
  -- fixed-data quantities
  set lam := P.lam with hlam
  have hlam0 : 0 < lam := P.lam_pos
  set μ := (1 + P.ε₁) * lam with hμ
  have hμ0 : 0 < μ := by have := P.ε₁_pos; positivity
  set h₀ := Ecal * W.Iw / 2 with hh₀
  have hh₀0 : 0 < h₀ := by have := mul_pos Ecal_pos W.Iw_pos; positivity
  set ν := 6 * W.wtmax * W.η⁻¹ ^ 2 with hν
  have hν0 : 0 ≤ ν := by have := wtmax_nonneg W; positivity
  have hw0 := W.wmax_nonneg
  set bI := P.bInt with hbI
  have hbI0 : 0 ≤ bI := integral_nonneg fun s => sq_nonneg _
  set Cn := 2 * μ * (μ + 6) + 2 * (8 * (1 + μ) + Cs) + μ * (μ + 6) + (8 * (1 + μ) + Cs) with hCn
  have hCn0 : 0 ≤ Cn := by positivity
  set CK := 2 * Real.pi * bI * lam + 2 * Cd with hCK
  have hCK0 : 0 ≤ CK := by positivity
  set θ₀ := 1 - 2 * P.θ with hθ₀
  have hθ₀0 : 1 / 2 < θ₀ := by have := P.θ_lt; linarith
  set tgt := δ' / 4 * h₀ * lam ^ 2 with htgt
  have htgt0 : 0 < tgt := by positivity
  set C₁ := (1 + κ⁻¹) * 128 * W.wmax * C₀' * bI * lam * Cn with hC₁
  set C₂ := 8 * (1 + κ⁻¹) * (5 * ν * C₀') * CK * Cn with hC₂
  set C₃ := (8 * (1 + κ⁻¹) * (ν * CF ^ 2) + Cab) * lam ^ 2 * P.aInt ^ 2 with hC₃
  set C₄ := (1 + κ⁻¹) * ((8 * (CT + 1) + 4 * C₀') * W.wmax) * CK * (4 * μ ^ 3) with hC₄
  have hC₂0 : 0 ≤ C₂ := by positivity
  have hC₄0 : 0 ≤ C₄ := by positivity
  -- all the conditions on `Q`
  have hev : ∀ᶠ Q : ℝ in atTop,
      (Qab ≤ Q ∧ Qi ≤ Q ∧ Qii ≤ Q ∧ QF ≤ Q ∧ QS ≤ Q ∧ Qs ≤ Q ∧ Real.exp 1 ≤ Q) ∧
      (cS * ((W.Vw + W.wtmax * W.η⁻¹ ^ 2) / W.Iw * Q ^ (-ε' / 4) * Real.log Q ^ 3 +
        (Q ^ (-ε' / 2) + W.Vw / W.Iw * Q ^ (-(1 / 2 : ℝ))) * CT) ≤ d) ∧
      (1 / 2 * (Ecal * W.Iw * Q ^ 2) ≤ W.H Q) ∧ (1 < ε * Real.log Q) ∧ (2 ≤ Q ^ ε) ∧
      (4 * C₁ / (tgt * θ₀) ≤ Real.log Q ^ P.a0) ∧
      (Q ^ (-P.ε₁) * (1 + Real.log Q) ^ 0 ≤ tgt / (C₂ + 1)) ∧
      (C₃ ≤ tgt / 2 * Q ^ 2) ∧
      (Q ^ (-ε) * (1 + Real.log Q) ^ 1 ≤ tgt / (C₄ + 1)) := by
    refine ((((eventually_ge_atTop Qab).and (eventually_ge_atTop Qi)).and
      (eventually_ge_atTop Qii)).and (eventually_ge_atTop QF) |>.and (eventually_ge_atTop QS)
      |>.and (eventually_ge_atTop Qs) |>.and (eventually_ge_atTop (Real.exp 1))).mono ?_ |>.and ?_
    · rintro Q ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩
      exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
    refine ((sharpLS_err_tendsto W cS hε'0 CT).eventually (ge_mem_nhds hd0)).and ?_
    refine (H_lower_eventually hWH W (κ := 1 / 2) (by norm_num)).and ?_
    refine ((Real.tendsto_log_atTop.const_mul_atTop hε).eventually_gt_atTop 1).and ?_
    refine ((tendsto_rpow_atTop hε).eventually_ge_atTop 2).and ?_
    refine (eventually_le_log_rpow P.a0_pos).and ?_
    refine (eventually_rpow_neg_mul_le P.ε₁_pos 0 (by positivity)).and ?_
    refine (eventually_le_mul_sq (by positivity)).and ?_
    exact eventually_rpow_neg_mul_le hε 1 (by positivity)
  obtain ⟨Q₀, hQ₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨Q₀, fun Q hQ T hT => ?_⟩
  obtain ⟨⟨hQab, hQi, hQii, hQF, hQS, hQs, hQe⟩, hSerr, hHl, hεℓ, hQε, hE1, hE2, hE3, hE4⟩ :=
    hQ₀ Q hQ
  have hQ1 : 1 < Q :=
    lt_of_lt_of_le (by have := Real.add_one_lt_exp (x := 1) one_ne_zero; linarith) hQe
  have hQ0 : 0 < Q := by linarith
  have hT1 : 1 ≤ T := one_le_T P hQe hT
  have hT0 : 0 < T := by linarith
  set ℓ := Real.log Q with hℓdef
  have hℓ1 : 1 ≤ ℓ := by
    have := Real.log_le_log (Real.exp_pos _) hQe; rwa [Real.log_exp] at this
  have hℓ0 : 0 < ℓ := by linarith
  have hH : 0 ≤ W.H Q := W.H_nonneg Q
  have hHl' : h₀ * Q ^ 2 ≤ W.H Q := by rw [hh₀]; linarith
  have hHu : W.H Q ≤ W.wmax * Q ^ 2 := sum_omega_card_le W hQ1.le
  have hY2 : P.Y Q ≤ Q ^ 2 := Y_le_sq P hQ1.le
  have hYr : P.Y Q ≤ Q ^ (2 - P.ε₁) := Y_le_rpow P hQ1.le
  have hYfl : (⌊P.Y Q⌋₊ : ℝ) ≤ P.Y Q := Nat.floor_le (P.Y_nonneg Q)
  -- the objects
  set x := Q ^ (1 + ε) / 2 with hx
  set M := W.wmax * C₀' * (Q ^ 2 + ⌊P.Y Q⌋₊) with hM
  set A₁ := ν * C₀' * (⌊P.Y Q⌋₊ + (⌊2 * P.Y Q / Q⌋₊ : ℝ) ^ 2) with hA₁
  set A₂ := ν * CF ^ 2 with hA₂
  set ε₀ := Cab * Q ^ (-(3 : ℝ)) with hε₀
  set c₃ := CT + d with hc₃
  have hM0 : 0 ≤ M := by positivity
  have hA₁0 : 0 ≤ A₁ := by positivity
  have hA₂0 : 0 ≤ A₂ := by positivity
  have hε₀0 : 0 ≤ ε₀ := by positivity
  have hc₃0 : 0 ≤ c₃ := by linarith
  -- the hypotheses of `pointwise_bound`
  have h0 : ∀ u, famForm W Q (P.rangeZ Q) (P.xVec Q T (P.bVec Q T) u) ≤
      famForm W Q (P.rangeZ Q) (P.xVec Q T (P.aVec Q) u) + ε₀ := fun u => by
    have := (abs_le.mp (hab Q hQab T hT u)).1
    linarith
  have hvb := VanishBeyond.bVec P hQ1 T
  have h1 := fun u hu => hi Q hQi T (P.bVec Q T) hvb u hu
  have h2 := fun u hu => hii Q hQii T (P.bVec Q T) hvb u hu
  have hKY : (⌊P.Y Q⌋₊ : ℝ) ≤ Q ^ (2 - ε') :=
    hYfl.trans (hYr.trans (Real.rpow_le_rpow_of_exponent_le hQ1.le
      (by linarith [min_le_left P.ε₁ (1 / 2)])))
  have h3 : ∀ z : ℤ → ℂ, levelForm (levels Q) (aNat W Q) (P.rangeZ Q) z ≤
      c₃ * W.H Q * normSq (P.rangeZ Q) z := by
    intro z
    rw [rangeZ_eq_intervalZ]
    refine (hS Q hQS 1 ⌊P.Y Q⌋₊ hKY z).trans ?_
    apply mul_le_mul_of_nonneg_right _ (normSq_nonneg' _ _)
    exact mul_le_mul_of_nonneg_right (by linarith) hH
  have h4 : ∀ z : ℤ → ℂ, famForm W Q (P.rangeZ Q) z ≤ M * normSq (P.rangeZ Q) z := by
    intro z
    refine (famForm_rangeZ_le P hmult W hQ1.le z).trans ?_
    apply mul_le_mul_of_nonneg_right _ (normSq_nonneg' _ _)
    have : 0 ≤ W.wmax * (Q ^ 2 + (⌊P.Y Q⌋₊ : ℝ)) := by positivity
    calc W.wmax * C₀ * (Q ^ 2 + ⌊P.Y Q⌋₊) = W.wmax * (Q ^ 2 + ⌊P.Y Q⌋₊) * C₀ := by ring
      _ ≤ W.wmax * (Q ^ 2 + ⌊P.Y Q⌋₊) * C₀' := mul_le_mul_of_nonneg_left (le_max_left _ _) this
      _ = M := by rw [hM]; ring
  have h5 := fun u => hF Q hQF T hT u
  have h6 := fun u (hu : (1 + ε) * Real.log Q < u) => xs_aNR_eq_aPP P hQ1 T hu
  have hpt := pointwise_bound P W (c₁ := 1 + d) (c₂ := Cband + d) (c₃ := c₃) (M := M)
    (A₁ := A₁) (A₂ := A₂) (ε₀ := ε₀) (x := x) hQ1 hε.le hκ0 hκ1 hH (by linarith) (by linarith)
    hc₃0 hM0 hA₁0 hA₂0 hε₀0 h0 h1 h2 h3 h4 h5 h6
  set Cmax := (1 + d) + (Cband + d) + c₃ with hCmax
  have hcf : ∀ u, 0 ≤ cfun (Real.log Q) ε (1 + d) (Cband + d) c₃ u ∧
      cfun (Real.log Q) ε (1 + d) (Cband + d) c₃ u ≤ Cmax := by
    intro u; unfold cfun; split_ifs <;> constructor <;> linarith
  have hκi : 0 ≤ 1 + κ⁻¹ := by have := inv_pos.mpr hκ0; linarith
  have hint := integral_step P W hQ1 hT0 hκ0 hH hcf hpt (mul_nonneg hκi hM0)
    (mul_nonneg (by positivity) hA₁0) (mul_nonneg hκi (by positivity))
  refine hint.trans ?_
  clear hint hpt h0 h1 h2 h3 h4 h5 h6 hi hii hF hS hab
  -- the main term (Step 5)
  have hsup : ∀ n ∈ P.range Q,
      sSup (cfun ℓ ε (1 + d) (Cband + d) c₃ '' {u | |u - Real.log n| < 2 * δL}) ≤
        (1 + d) * Ct (Real.log n / ell Q) := fun n _ =>
    sSup_cfun_le hℓ0 hεℓ hd0.le hCband hCT1 hCt1 hCtband hCtCT (Real.log n)
  have hmainsum : ∑ n ∈ P.range Q, P.bVec Q T n ^ 2 * (P.𝒦 Q T n n).re *
      sSup (cfun ℓ ε (1 + d) (Cband + d) c₃ '' {u | |u - Real.log n| < 2 * δL}) ≤
      (1 + d) * ∑ n ∈ P.range Q, P.bVec Q T n ^ 2 * Ct (Real.log n / ell Q) * (P.𝒦 Q T n n).re := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have h𝒦 := 𝒦_diag_re_nonneg P hQ1 T n (Finset.mem_Icc.mp hn).1
    calc P.bVec Q T n ^ 2 * (P.𝒦 Q T n n).re *
          sSup (cfun ℓ ε (1 + d) (Cband + d) c₃ '' {u | |u - Real.log n| < 2 * δL})
        ≤ P.bVec Q T n ^ 2 * (P.𝒦 Q T n n).re * ((1 + d) * Ct (Real.log n / ell Q)) :=
          mul_le_mul_of_nonneg_left (hsup n hn) (mul_nonneg (sq_nonneg _) h𝒦)
      _ = _ := by ring
  have hS0 : 0 ≤ ∑ n ∈ P.range Q, P.bVec Q T n ^ 2 * Ct (Real.log n / ell Q) * (P.𝒦 Q T n n).re :=
    Finset.sum_nonneg fun n hn => mul_nonneg (mul_nonneg (sq_nonneg _)
      (le_trans zero_le_one (hCt1 _))) (𝒦_diag_re_nonneg P hQ1 T n (Finset.mem_Icc.mp hn).1)
  have hmain : (1 + κ) ^ 3 * W.H Q * ∑ n ∈ P.range Q, P.bVec Q T n ^ 2 * (P.𝒦 Q T n n).re *
      sSup (cfun ℓ ε (1 + d) (Cband + d) c₃ '' {u | |u - Real.log n| < 2 * δL}) ≤
      (1 + δ') * W.H Q *
        ∑ n ∈ P.range Q, P.bVec Q T n ^ 2 * Ct (Real.log n / ell Q) * (P.𝒦 Q T n n).re := by
    have hk3 : 0 ≤ (1 + κ) ^ 3 * W.H Q := by positivity
    calc _ ≤ (1 + κ) ^ 3 * W.H Q * ((1 + d) *
          ∑ n ∈ P.range Q, P.bVec Q T n ^ 2 * Ct (Real.log n / ell Q) * (P.𝒦 Q T n n).re) :=
          mul_le_mul_of_nonneg_left hmainsum hk3
      _ = ((1 + κ) ^ 3 * (1 + d)) * (W.H Q *
          ∑ n ∈ P.range Q, P.bVec Q T n ^ 2 * Ct (Real.log n / ell Q) * (P.𝒦 Q T n n).re) := by
          ring
      _ ≤ (1 + δ') * (W.H Q *
          ∑ n ∈ P.range Q, P.bVec Q T n ^ 2 * Ct (Real.log n / ell Q) * (P.𝒦 Q T n n).re) :=
          mul_le_mul_of_nonneg_right hfac (mul_nonneg hH hS0)
      _ = _ := by ring
  refine add_le_add hmain ?_
  clear hmain hmainsum hsup hS0
  -- the error terms
  set Jl := P.Jlen T with hJldef
  have hJl : θ₀ * ℓ ^ P.a0 ≤ Jl := by
    rw [hJldef]; unfold PrimeSetup.Jlen
    exact mul_le_mul_of_nonneg_left hT.1 (by linarith)
  obtain ⟨hJlh, hJlℓ⟩ : 1 / 2 ≤ Jl ∧ 1 / 2 ≤ Jl * ℓ := Jl_facts hθ₀0 hT1 hℓ1
  have hJl0 : 0 ≤ Jl := by linarith
  have hLdef : P.L Q = lam * ℓ := rfl
  have hell : ell Q = ℓ := rfl
  rw [hLdef, hell]
  have hlogY : Real.log (P.Y Q) = μ * ℓ := by rw [log_Y, hLdef, hμ]; ring
  have hSA := norm_a_le_ell P hQ1 hlogY hμ0.le hℓ1
  have hSS := norm_sharp_le_ell P hlogY hμ0.le hℓ1 rfl hCs0 (hs Q hQs T hT1)
  have hSB := sum_sq_bVec_le P Q T
  have hSA0 : 0 ≤ ∑ n ∈ P.range Q, P.aVec Q n ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hSB0 : 0 ≤ ∑ n ∈ P.range Q, P.bVec Q T n ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hSS0 : 0 ≤ ∑ n ∈ P.range Q, P.aSharp Q T n ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  obtain ⟨hSAB, hSSC⟩ := sab_le hSA hSS hSB hSA0 hSS0 hCn
  have hK : ∀ n ∈ P.range Q, (P.𝒦 Q T n n).re ≤ CK * Jl * ℓ := by
    intro n hn
    have h := hKd Q T hQ1 hT0 n (Finset.mem_Icc.mp hn).1
    rw [← hJldef, hLdef] at h
    rw [hCK]
    exact 𝒦_le_ell P h hCd0 hJlℓ
  have hSPP := sum_sq_aPP_le_ell P hQ1 hQε hlogY hμ0.le hℓ0.le
  have hM2 : M ≤ 2 * W.wmax * C₀' * Q ^ 2 := M_le_sq P W hQ1 hC₀'0
  have hA₁b : A₁ ≤ 5 * ν * C₀' * (Q ^ 2 * Q ^ (-P.ε₁)) := A₁_le P hQ1 hν0 hC₀'0
  have hQmε₁ : 0 ≤ Q ^ (-P.ε₁) := Real.rpow_nonneg hQ0.le _
  have hQmε : 0 ≤ Q ^ (-ε) := Real.rpow_nonneg hQ0.le _
  have hε₀b : ε₀ ≤ Cab := by
    have hQm3 : Q ^ (-(3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hQ1.le (by norm_num)
    rw [hε₀]
    calc Cab * Q ^ (-(3 : ℝ)) ≤ Cab * 1 := mul_le_mul_of_nonneg_left hQm3 hCab0
      _ = Cab := mul_one _
  have hC₁b : C₁ ≤ tgt * Jl / 4 := C1_le htgt0 (by linarith) hE1 hJl
  have hC₂b : C₂ * Q ^ (-P.ε₁) ≤ tgt := by
    rw [pow_zero, mul_one] at hE2
    exact C_le_of hC₂0 hQmε₁ hE2
  have hC₄b : C₄ * Q ^ (-ε) * ℓ ≤ tgt := by
    rw [pow_one] at hE4
    exact C_le_of' hC₄0 hQmε hℓ0.le hE4
  have hSs0 : 0 ≤ ∑ n ∈ P.range Q, P.aSharp Q T n ^ 2 * (P.𝒦 Q T n n).re :=
    Finset.sum_nonneg fun n hn => mul_nonneg (sq_nonneg _)
      (𝒦_diag_re_nonneg P hQ1 T n (Finset.mem_Icc.mp hn).1)
  have hSp0 : 0 ≤ ∑ n ∈ P.range Q, aPP P Q x n ^ 2 * (P.𝒦 Q T n n).re :=
    Finset.sum_nonneg fun n hn => mul_nonneg (sq_nonneg _)
      (𝒦_diag_re_nonneg P hQ1 T n (Finset.mem_Icc.mp hn).1)
  have T1 := err_tails hκ0 hM2 hbI0 hlam0 hℓ0 hSA0 hSB0 hSAB hC₁ hC₁b htgt0.le hJl0 hw0
    hC₀'0
  have T2 := err_sharp hκ0 hA₁b (sum_sq_mul_𝒦_le P (P.aSharp Q T) hK) hSs0 hSSC hCK0 hJl0
    hℓ0.le hC₂ hC₂b hν0 hC₀'0 hQmε₁
  have T3 := err_const (La := lam * ℓ) (aI := P.aInt) hε₀b hA₂ rfl hC₃ hE3 hJlℓ htgt0.le
  have T4 := err_pp hκ0 hc₃0 (by rw [hc₃]; linarith) hH hHu hM0 hM2
    (sum_sq_mul_𝒦_le P (aPP P Q x) hK) hSp0 hSPP hCK0 hJl0 hℓ0.le hC₄ hC₄b
    (by linarith) hC₀'0 hw0
  have htot := err_total hδ' hHl' htgt hJl0 hℓ0.le
  linarith only [T1, T2, T3, T4, htot]

end Families.Phase3.C
