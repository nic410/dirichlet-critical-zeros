/-
# The Fejér kernel and `k_ς`

* `fourier_k0` — `𝓕 k₀(w) = sinc²(πςw)` (`k₀(ξ) = ς⁻¹(1 − |ξ|/ς)_+`), by the fundamental theorem of
  calculus on `[−ς,0]` and `[0,ς]` (antiderivative `e^{αv}((A+Bv)/α − B/α²)` of `e^{αv}(A+Bv)`).
* `hasSum_fejer_kper` — Poisson summation (`Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable`):
  `k_ς(ξ) = ∑_{n∈ℤ} sinc²(πςn) e(nξ)`, absolutely convergent (`lemma-A.tex`, proof of `lem:dual`, Step 1,
  `eqA:Poisson-g`, with `g(y) = F(κ(y−c)/K)`, `F(y) = (sin πy/πy)²`, before normalising by `F(κ/2)`).
* `kper_neg`, `k0_eq_zero_of_le`, `continuous_k0`, `sinc_sq_ge` (`sinc² y ≥ 1 − y²/3` for `|y| ≤ 1`).
-/
import Families.LemmaA

noncomputable section

open scoped BigOperators FourierTransform
open MeasureTheory Filter Topology Asymptotics

namespace Families.Phase1.B

open Families

/-! ### Elementary facts about `k₀` and `k_ς` -/

lemma k0_eq_zero_of_le {ς ξ : ℝ} (hς : 0 < ς) (h : ς ≤ |ξ|) : k0 ς ξ = 0 := by
  unfold k0
  have : 1 - |ξ| / ς ≤ 0 := by rw [sub_nonpos, le_div_iff₀ hς]; linarith
  rw [max_eq_right this, mul_zero]

lemma k0_nonneg {ς : ℝ} (hς : 0 ≤ ς) (ξ : ℝ) : 0 ≤ k0 ς ξ :=
  mul_nonneg (inv_nonneg.mpr hς) (le_max_right _ _)

lemma k0_neg (ς ξ : ℝ) : k0 ς (-ξ) = k0 ς ξ := by
  unfold k0; rw [abs_neg]

lemma continuous_k0 (ς : ℝ) : Continuous (k0 ς) :=
  continuous_const.mul ((continuous_const.sub (continuous_abs.div_const _)).max continuous_const)

lemma k0_of_nonneg {ς v : ℝ} (hς : 0 < ς) (h0 : 0 ≤ v) (h1 : v ≤ ς) :
    k0 ς v = ς⁻¹ + (-ς⁻¹ ^ 2) * v := by
  unfold k0
  rw [abs_of_nonneg h0, max_eq_left (by rw [sub_nonneg, div_le_one hς]; exact h1)]
  field_simp
  ring

lemma k0_of_nonpos {ς v : ℝ} (hς : 0 < ς) (h0 : v ≤ 0) (h1 : -ς ≤ v) :
    k0 ς v = ς⁻¹ + ς⁻¹ ^ 2 * v := by
  unfold k0
  rw [abs_of_nonpos h0, max_eq_left (by rw [sub_nonneg, div_le_one hς]; linarith)]
  field_simp
  ring

/-- `k_ς ≥ 0`. -/
lemma kper_nonneg' {ς : ℝ} (hς : 0 < ς) (ξ : ℝ) : 0 ≤ kper ς ξ :=
  tsum_nonneg fun _ => k0_nonneg hς.le _

/-- `k_ς` is even. -/
lemma kper_neg (ς ξ : ℝ) : kper ς (-ξ) = kper ς ξ := by
  unfold kper
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun m => ?_
  rw [← k0_neg]
  congr 1
  simp only [Equiv.neg_apply, Int.cast_neg]
  ring

/-! ### `∫ e^{αv}(A + Bv) dv` -/

lemma hasDerivAt_exp_mul_linear (α A B : ℂ) (hα : α ≠ 0) (v : ℝ) :
    HasDerivAt (fun v : ℝ => Complex.exp (α * v) * ((A + B * v) / α - B / α ^ 2))
      (Complex.exp (α * v) * (A + B * v)) v := by
  have hlin : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 v := Complex.ofRealCLM.hasDerivAt
  have h1 : HasDerivAt (fun v : ℝ => Complex.exp (α * v)) (Complex.exp (α * v) * (α * 1)) v :=
    (hlin.const_mul α).cexp
  have h2 : HasDerivAt (fun v : ℝ => (A + B * v) / α - B / α ^ 2) (B * 1 / α) v :=
    (((hlin.const_mul B).const_add A).div_const α).sub_const _
  refine (h1.mul h2).congr_deriv ?_
  field_simp
  ring

lemma integral_exp_mul_linear (α A B : ℂ) (hα : α ≠ 0) (a b : ℝ) :
    ∫ v in a..b, Complex.exp (α * v) * (A + B * v) =
      Complex.exp (α * b) * ((A + B * b) / α - B / α ^ 2) -
        Complex.exp (α * a) * ((A + B * a) / α - B / α ^ 2) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v _ => hasDerivAt_exp_mul_linear α A B hα v) ?_
  refine Continuous.intervalIntegrable ?_ _ _
  fun_prop

lemma integral_linear (A B : ℂ) (a b : ℝ) :
    ∫ v in a..b, (A + B * ((v : ℝ) : ℂ)) = (A * b + B * b ^ 2 / 2) - (A * a + B * a ^ 2 / 2) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun v : ℝ => A * ((v : ℝ) : ℂ) + B * ((v : ℝ) : ℂ) ^ 2 / 2) (fun v _ => ?_) ?_
  · have hlin : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 v := Complex.ofRealCLM.hasDerivAt
    have := ((hlin.const_mul A).add ((hlin.pow 2).const_mul B |>.div_const 2))
    convert this using 1
    · ext v; simp
    · push_cast; ring
  · exact Continuous.intervalIntegrable (by fun_prop) _ _

/-! ### The Fourier transform of `k₀` -/

/-- `k₀` as a complex-valued function. -/
def k0C (ς : ℝ) : ℝ → ℂ := fun x => (k0 ς x : ℂ)

lemma continuous_k0C (ς : ℝ) : Continuous (k0C ς) :=
  Complex.continuous_ofReal.comp (continuous_k0 ς)

lemma k0C_eq_zero_of_le {ς ξ : ℝ} (hς : 0 < ς) (h : ς ≤ |ξ|) : k0C ς ξ = 0 := by
  simp [k0C, k0_eq_zero_of_le hς h]

/-- The trigonometric identity behind `𝓕 k₀ = sinc²`. -/
lemma sinc_sq_eq {ς w : ℝ} (hς : 0 < ς) (hw : w ≠ 0) :
    (Real.sinc (Real.pi * ς * w)) ^ 2 =
      ς⁻¹ ^ 2 * (2 - 2 * Real.cos (2 * Real.pi * w * ς)) / (2 * Real.pi * w) ^ 2 := by
  have hu : Real.pi * ς * w ≠ 0 := by
    have := Real.pi_pos
    positivity
  rw [Real.sinc_of_ne_zero hu]
  have hc : Real.cos (2 * Real.pi * w * ς) = 1 - 2 * Real.sin (Real.pi * ς * w) ^ 2 := by
    rw [show 2 * Real.pi * w * ς = 2 * (Real.pi * ς * w) by ring, Real.cos_two_mul]
    have := Real.sin_sq_add_cos_sq (Real.pi * ς * w)
    linarith
  rw [hc]
  have hπ := Real.pi_pos
  field_simp
  ring

/-- **`𝓕 k₀(w) = sinc²(πςw)`** (`lemma-A.tex`, `lem:dual` Step 1: `∫F(y)e(yξ)dy = (1−|ξ|)_+`, dual form). -/
theorem fourier_k0 {ς : ℝ} (hς : 0 < ς) (w : ℝ) :
    𝓕 (k0C ς) w = ((Real.sinc (Real.pi * ς * w)) ^ 2 : ℝ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  set α : ℂ := ((-2 * Real.pi * w : ℝ) : ℂ) * Complex.I with hα
  have hint : ∀ v : ℝ, Complex.exp (↑(-2 * Real.pi * v * w) * Complex.I) • k0C ς v =
      Complex.exp (α * v) * (k0 ς v : ℂ) := by
    intro v
    simp only [smul_eq_mul, k0C, hα]
    congr 2
    push_cast; ring
  simp_rw [hint]
  have hcont : Continuous fun v : ℝ => Complex.exp (α * v) * (k0 ς v : ℂ) :=
    (by fun_prop : Continuous fun v : ℝ => Complex.exp (α * v)).mul
      (Complex.continuous_ofReal.comp (continuous_k0 ς))
  -- restrict to `[−ς, ς]` and split at `0`
  have hsupp : ∫ v, Complex.exp (α * ((v : ℝ) : ℂ)) * (k0 ς v : ℂ) =
      ∫ v in (-ς)..ς, Complex.exp (α * ((v : ℝ) : ℂ)) * (k0 ς v : ℂ) := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv => ?_).symm
    rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hv
    have : ς ≤ |v| := by
      rcases hv with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    rw [k0_eq_zero_of_le hς this]; simp
  rw [hsupp, ← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  -- the two halves as integrals of `e^{αv}(A + Bv)`
  have hL : ∫ v in (-ς)..0, Complex.exp (α * ((v : ℝ) : ℂ)) * (k0 ς v : ℂ) =
      ∫ v in (-ς)..0, Complex.exp (α * ((v : ℝ) : ℂ)) * ((ς⁻¹ : ℂ) + (ς⁻¹ ^ 2 : ℂ) * ((v : ℝ) : ℂ)) := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [Set.uIcc_of_le (by linarith)] at hv
    rw [k0_of_nonpos hς hv.2 hv.1]
    push_cast; ring
  have hR : ∫ v in (0 : ℝ)..ς, Complex.exp (α * ((v : ℝ) : ℂ)) * (k0 ς v : ℂ) =
      ∫ v in (0 : ℝ)..ς, Complex.exp (α * ((v : ℝ) : ℂ)) * ((ς⁻¹ : ℂ) + (-ς⁻¹ ^ 2 : ℂ) * ((v : ℝ) : ℂ)) := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [Set.uIcc_of_le hς.le] at hv
    rw [k0_of_nonneg hς hv.1 hv.2]
    push_cast; ring
  rw [hL, hR]
  have hς0 : (ς : ℂ) ≠ 0 := by exact_mod_cast hς.ne'
  by_cases hw : w = 0
  · -- `w = 0`: `∫ k₀ = 1`
    have hα0 : α = 0 := by rw [hα, hw]; simp
    simp only [hα0, zero_mul, Complex.exp_zero, one_mul]
    rw [integral_linear, integral_linear, hw]
    simp only [mul_zero, Real.sinc_zero]
    push_cast
    field_simp
    ring
  · have hα0 : α ≠ 0 := by
      rw [hα]
      refine mul_ne_zero ?_ Complex.I_ne_zero
      have := Real.pi_pos
      exact_mod_cast (by positivity : (-2 * Real.pi * w) ≠ 0)
    rw [integral_exp_mul_linear α _ _ hα0, integral_exp_mul_linear α _ _ hα0, sinc_sq_eq hς hw]
    -- `e^{ας} + e^{−ας} = 2 cos(2πwς)`
    have hexp : Complex.exp (α * ς) + Complex.exp (α * (-ς : ℝ)) =
        2 * (Real.cos (2 * Real.pi * w * ς) : ℂ) := by
      have e1 : α * ς = ((-(2 * Real.pi * w * ς) : ℝ) : ℂ) * Complex.I := by
        rw [hα]; push_cast; ring
      have e2 : α * ((-ς : ℝ) : ℂ) = ((2 * Real.pi * w * ς : ℝ) : ℂ) * Complex.I := by
        rw [hα]; push_cast; ring
      rw [e1, e2, Complex.exp_mul_I, Complex.exp_mul_I, Complex.ofReal_neg, Complex.cos_neg,
        Complex.sin_neg, Complex.ofReal_cos]
      ring
    have hα2 : α ^ 2 = -((2 * Real.pi * w : ℝ) : ℂ) ^ 2 := by
      rw [hα]; push_cast; ring_nf; rw [Complex.I_sq]; ring
    have hπw : ((2 * Real.pi * w : ℝ) : ℂ) ≠ 0 := by
      have := Real.pi_pos
      exact_mod_cast (by positivity : (2 * Real.pi * w) ≠ 0)
    calc _ = (ς : ℂ)⁻¹ ^ 2 * (Complex.exp (α * ς) + Complex.exp (α * ((-ς : ℝ) : ℂ)) - 2) / α ^ 2 := by
          simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
          push_cast
          field_simp
          ring
      _ = _ := by
          rw [hexp, hα2]
          push_cast
          field_simp
          ring

/-! ### Poisson summation: `k_ς` as a Fejér series -/

/-- `e(x)` has modulus `1`. -/
lemma norm_eA' (x : ℝ) : ‖eA x‖ = 1 := by
  unfold eA
  rw [Complex.norm_exp]
  simp

/-- The Fejér coefficients `F(ςn) = sinc²(πςn)`, `F(y) = (sin πy/πy)²`. -/
def fejerCoeff (ς : ℝ) (n : ℤ) : ℝ := (Real.sinc (Real.pi * ς * n)) ^ 2

lemma fejerCoeff_nonneg (ς : ℝ) (n : ℤ) : 0 ≤ fejerCoeff ς n := sq_nonneg _

lemma fejerCoeff_le {ς : ℝ} (hς : 0 < ς) {n : ℤ} (hn : n ≠ 0) :
    fejerCoeff ς n ≤ (Real.pi * ς)⁻¹ ^ 2 * (1 / (n : ℝ) ^ 2) := by
  unfold fejerCoeff
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hπ := Real.pi_pos
  have hy : Real.pi * ς * n ≠ 0 := by positivity
  rw [Real.sinc_of_ne_zero hy, div_pow]
  have h1 := Real.sin_sq_le_one (Real.pi * ς * n)
  calc Real.sin (Real.pi * ς * n) ^ 2 / (Real.pi * ς * n) ^ 2 ≤ 1 / (Real.pi * ς * n) ^ 2 :=
        div_le_div_of_nonneg_right h1 (sq_nonneg _)
    _ = (Real.pi * ς)⁻¹ ^ 2 * (1 / (n : ℝ) ^ 2) := by field_simp

lemma summable_fejerCoeff {ς : ℝ} (hς : 0 < ς) : Summable (fejerCoeff ς) := by
  have h := (Real.summable_one_div_int_pow.mpr (by norm_num : 1 < 2)).mul_left
    ((Real.pi * ς)⁻¹ ^ 2)
  refine Summable.of_norm_bounded_eventually h ?_
  filter_upwards [(Set.finite_singleton (0 : ℤ)).compl_mem_cofinite] with n hn
  rw [Real.norm_of_nonneg (fejerCoeff_nonneg ς n)]
  exact fejerCoeff_le hς hn

/-- `k₀` has compact support, so it is `O(|x|^{-2})` at infinity. -/
lemma k0C_isBigO {ς : ℝ} (hς : 0 < ς) :
    k0C ς =O[cocompact ℝ] fun x : ℝ => |x| ^ (-(2 : ℝ)) := by
  have hev : k0C ς =ᶠ[cocompact ℝ] fun _ => (0 : ℂ) := by
    have hmem : {x : ℝ | ς ≤ |x|} ∈ cocompact ℝ := by
      refine mem_cocompact.mpr ⟨Set.Icc (-ς) ς, isCompact_Icc, fun x hx => ?_⟩
      simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
      show ς ≤ |x|
      rcases hx with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    filter_upwards [hmem] with x hx using k0C_eq_zero_of_le hς hx
  exact (isBigO_zero _ _).congr' hev.symm EventuallyEq.rfl

/-- **`k_ς` as a Fejér series** (`eqA:Poisson-g` up to the phase and the normalisation):
`k_ς(ξ) = ∑_{n∈ℤ} sinc²(πςn) e(nξ)`, the series converging absolutely. -/
theorem hasSum_fejer_kper {ς : ℝ} (hς : 0 < ς) (ξ : ℝ) :
    HasSum (fun n : ℤ => (fejerCoeff ς n : ℂ) * eA (n * ξ)) (kper ς ξ) := by
  have hsummF : Summable fun n : ℤ => 𝓕 (k0C ς) (n : ℝ) := by
    simp_rw [fourier_k0 hς]
    exact Complex.summable_ofReal.mpr (summable_fejerCoeff hς)
  have hP := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable (continuous_k0C ς)
    (by norm_num : (1 : ℝ) < 2) (k0C_isBigO hς) hsummF ξ
  have hterm : ∀ n : ℤ, 𝓕 (k0C ς) (n : ℝ) * fourier n (ξ : UnitAddCircle) =
      (fejerCoeff ς n : ℂ) * eA (n * ξ) := by
    intro n
    rw [fourier_k0 hς, fourier_coe_apply]
    unfold eA fejerCoeff
    congr 2
    push_cast
    ring
  have hsumm : Summable fun n : ℤ => (fejerCoeff ς n : ℂ) * eA (n * ξ) := by
    refine Summable.of_norm ?_
    simp_rw [norm_mul, norm_eA', mul_one, Complex.norm_real,
      Real.norm_of_nonneg (fejerCoeff_nonneg ς _)]
    exact summable_fejerCoeff hς
  have hval : (kper ς ξ : ℂ) = ∑' n : ℤ, (fejerCoeff ς n : ℂ) * eA (n * ξ) := by
    unfold kper
    rw [Complex.ofReal_tsum]
    simp only [k0C] at hP
    rw [hP]
    exact tsum_congr hterm
  rw [hval]
  exact hsumm.hasSum

/-! ### Lower bound for `sinc²` near `0` -/

/-- `sinc y ≥ 1 − y²/6` (from `sin y ≥ y − y³/6`, `y ≥ 0`, and evenness). -/
lemma one_sub_sq_div_six_le_sinc (y : ℝ) : 1 - y ^ 2 / 6 ≤ Real.sinc y := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [Real.sinc_zero]
  have key : ∀ z : ℝ, 0 < z → 1 - z ^ 2 / 6 ≤ Real.sinc z := fun z hz => by
    rw [Real.sinc_of_ne_zero hz.ne', le_div_iff₀ hz]
    have := Real.sin_ge_sub_cube hz.le
    nlinarith
  rcases lt_or_gt_of_ne hy with h | h
  · have := key (-y) (by linarith)
    rwa [Real.sinc_neg, neg_sq] at this
  · exact key y h

/-- `sinc² y ≥ 1 − y²/3` for `y² ≤ 6` (the TeX's `F(y) ≥ 1 − π²y²/3`, `F(y) = sinc²(πy)`). -/
lemma sinc_sq_ge {y : ℝ} (hy : y ^ 2 ≤ 6) : 1 - y ^ 2 / 3 ≤ Real.sinc y ^ 2 := by
  have h := one_sub_sq_div_six_le_sinc y
  have h0 : 0 ≤ 1 - y ^ 2 / 6 := by linarith
  have h2 : (1 - y ^ 2 / 6) ^ 2 ≤ Real.sinc y ^ 2 := pow_le_pow_left₀ h0 h 2
  nlinarith [sq_nonneg (y ^ 2)]

end Families.Phase1.B
