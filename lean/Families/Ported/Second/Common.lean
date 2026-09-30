/-
# Prime side (paper §5): shared lemmas

* `Φ` is real and even; `Φ(r)² = PhiSq(r) ≥ 0`, continuous, integrable, `≤ (aL)²`, `∫ Φ² ≪ L`;
  `∬_{J²} Φ(t−t')² = Re 𝒦(1,1) ≤ 2π|J| b L + O(1)`.
* `μ_χ` is continuous; on `J`, `μ_χ(t) = (1/2π)(log(q/π) + log T) + O(1)`; globally
  `|μ_χ(t)| ≤ (1/2π)(|log(q/π)| + C log(|t|+2))` (Stirling).
* crude sums of `a_n = Λ(n) n^{-1/2} Υ(n)` on `[1, Y]`.
* the large sieve in the forms used (`famLS`, `famLS_omega`, `bilinLS`) and `H ≫ Q²`.
-/
import Families.Ported.Second.Defs
import Families.M1Diag
import Families.Assembly
import Families.Phase3.C.B1

noncomputable section

open scoped BigOperators ComplexConjugate ContDiff
open ArithmeticFunction Finset MeasureTheory Filter Topology

namespace Families.Ported.Second

open Families

/-! ### `Φ` -/

section Phi

variable (P : PrimeSetup)

theorem Φ_conj (Q r : ℝ) : conj (P.Φ Q r) = P.Φ Q (-r) := by
  unfold PrimeSetup.Φ
  rw [← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [map_mul, map_pow, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I]
  congr 2
  push_cast; ring

theorem SC.ψL_neg (Q u : ℝ) : P.ψL Q (-u) = P.ψL Q u := by
  unfold PrimeSetup.ψL; rw [neg_div, P.ψ_even]

theorem Φ_neg (Q r : ℝ) : P.Φ Q (-r) = P.Φ Q r := by
  unfold PrimeSetup.Φ
  rw [← integral_neg_eq_self]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [SC.ψL_neg]
  congr 2
  push_cast; ring

theorem Φ_im (Q r : ℝ) : (P.Φ Q r).im = 0 := by
  have h : conj (P.Φ Q r) = P.Φ Q r := by rw [Φ_conj, Φ_neg]
  exact Complex.conj_eq_iff_im.mp h

theorem Φ_eq_re (Q r : ℝ) : P.Φ Q r = ((P.Φ Q r).re : ℂ) := by
  apply Complex.ext <;> simp [Φ_im]

theorem PhiSq_eq (Q r : ℝ) : PhiSq P Q r = (P.Φ Q r).re ^ 2 := by
  unfold PhiSq
  rw [Φ_eq_re P Q r]
  simp only [Complex.ofReal_re]
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

theorem Φ_sq_eq_PhiSq (Q r : ℝ) : P.Φ Q r ^ 2 = (PhiSq P Q r : ℂ) := by
  rw [PhiSq_eq, Complex.ofReal_pow, ← Φ_eq_re]

theorem PhiSq_nonneg (Q r : ℝ) : 0 ≤ PhiSq P Q r := by
  rw [PhiSq_eq]; exact sq_nonneg _

theorem PhiSq_neg (Q r : ℝ) : PhiSq P Q (-r) = PhiSq P Q r := by
  unfold PhiSq; rw [Φ_neg]

theorem PhiSq_continuous {Q : ℝ} (hQ : 1 < Q) : Continuous (PhiSq P Q) :=
  Complex.continuous_re.comp (P.Φ_sq_continuous hQ)

theorem PhiSq_integrable {Q : ℝ} (hQ : 1 < Q) : Integrable (PhiSq P Q) :=
  (P.Φ_sq_integrable hQ).re

lemma SC.integral_ψL_sq {Q : ℝ} (hQ : 1 < Q) : ∫ u, P.ψL Q u ^ 2 = P.L Q * P.aInt := by
  have hL := P.L_pos hQ
  have h : ∫ u, P.ψ (u / P.L Q) ^ 2 = |P.L Q| • ∫ y, P.ψ y ^ 2 :=
    Measure.integral_comp_div (fun s => P.ψ s ^ 2) (P.L Q)
  unfold PrimeSetup.ψL PrimeSetup.aInt PrimeSetup.vfun
  rw [h, abs_of_pos hL, smul_eq_mul]

lemma SC.integral_ψL_four {Q : ℝ} (hQ : 1 < Q) : ∫ u, P.ψL Q u ^ 4 = P.L Q * P.bInt := by
  have hL := P.L_pos hQ
  have h : ∫ u, P.ψ (u / P.L Q) ^ 4 = |P.L Q| • ∫ y, P.ψ y ^ 4 :=
    Measure.integral_comp_div (fun s => P.ψ s ^ 4) (P.L Q)
  unfold PrimeSetup.ψL PrimeSetup.bInt PrimeSetup.vfun
  rw [h, abs_of_pos hL, smul_eq_mul]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only; ring

theorem SC.norm_Φ_le {Q : ℝ} (hQ : 1 < Q) (r : ℝ) : ‖P.Φ Q r‖ ≤ P.aInt * P.L Q := by
  unfold PrimeSetup.Φ
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  rw [show P.aInt * P.L Q = P.L Q * P.aInt from mul_comm _ _, ← SC.integral_ψL_sq P hQ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [Complex.norm_exp]; simp

theorem PhiSq_le {Q : ℝ} (hQ : 1 < Q) (r : ℝ) : PhiSq P Q r ≤ (P.aInt * P.L Q) ^ 2 := by
  rw [PhiSq_eq]
  have h1 : |(P.Φ Q r).re| ≤ ‖P.Φ Q r‖ := Complex.abs_re_le_norm _
  have h2 := SC.norm_Φ_le P hQ r
  have h0 : 0 ≤ |(P.Φ Q r).re| := abs_nonneg _
  rw [← sq_abs]
  exact pow_le_pow_left₀ h0 (h1.trans h2) 2


open scoped FourierTransform in
lemma SC.Vhat_integrable : Integrable P.Vhat := by
  set VS := P.vC_hasCompactSupport.toSchwartzMap P.vC_contDiff
  have h1 : (VS : ℝ → ℂ) = P.vC := rfl
  have h2 := (𝓕 VS).integrable (μ := volume)
  rw [SchwartzMap.fourier_coe, h1] at h2
  have hR : -(1 / (2 * Real.pi)) ≠ 0 := by simp [Real.pi_ne_zero]
  have h3 := h2.comp_mul_left' hR
  refine h3.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [P.Vhat_eq_fourier]
  ring_nf

lemma SC.Φ_integrable {Q : ℝ} (hQ : 1 < Q) : Integrable (P.Φ Q) := by
  have hL := P.L_pos hQ
  have h := ((SC.Vhat_integrable P).comp_mul_left' hL.ne').const_mul (P.L Q : ℂ)
  refine h.congr (Filter.Eventually.of_forall fun r => ?_)
  simp only
  rw [P.Φ_eq_Vhat hQ]

lemma SC.integral_norm_Φ {Q : ℝ} (hQ : 1 < Q) : ∫ r, ‖P.Φ Q r‖ = ∫ x, ‖P.Vhat x‖ := by
  have hL := P.L_pos hQ
  have heq : (fun r => ‖P.Φ Q r‖) = fun r => P.L Q * ‖P.Vhat (P.L Q * r)‖ := by
    funext r
    rw [P.Φ_eq_Vhat hQ, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
  rw [heq, integral_const_mul, Measure.integral_comp_mul_left (fun x => ‖P.Vhat x‖) (P.L Q),
    abs_inv, abs_of_pos hL, smul_eq_mul]
  field_simp

/-- `∫ Φ² ≤ aL ∫|V| ≪ L`. -/
theorem integral_PhiSq_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ Q : ℝ, 1 < Q → ∫ r, PhiSq P Q r ≤ C * P.L Q := by
  have ha : 0 ≤ P.aInt := integral_nonneg fun s => sq_nonneg _
  refine ⟨P.aInt * ∫ x, ‖P.Vhat x‖, mul_nonneg ha (integral_nonneg fun _ => norm_nonneg _),
    fun Q hQ => ?_⟩
  have hL := P.L_pos hQ
  have hint : Integrable (fun r => P.aInt * P.L Q * ‖P.Φ Q r‖) :=
    ((SC.Φ_integrable P hQ).norm).const_mul _
  calc ∫ r, PhiSq P Q r ≤ ∫ r, P.aInt * P.L Q * ‖P.Φ Q r‖ := by
        refine integral_mono (PhiSq_integrable P hQ) hint fun r => ?_
        rw [PhiSq_eq]
        have h1 : |(P.Φ Q r).re| ≤ ‖P.Φ Q r‖ := Complex.abs_re_le_norm _
        have h2 := SC.norm_Φ_le P hQ r
        rw [← sq_abs, sq]
        have h0 : 0 ≤ |(P.Φ Q r).re| := abs_nonneg _
        calc |(P.Φ Q r).re| * |(P.Φ Q r).re| ≤ (P.aInt * P.L Q) * ‖P.Φ Q r‖ :=
              mul_le_mul (h1.trans h2) h1 h0 (by positivity)
          _ = _ := rfl
    _ = (P.aInt * ∫ x, ‖P.Vhat x‖) * P.L Q := by
        rw [integral_const_mul, SC.integral_norm_Φ P hQ]; ring

/-- `g(0) = ∫ ψ_L⁴ = L b`. -/
theorem g_zero {Q : ℝ} (hQ : 1 < Q) : P.g Q 0 = P.L Q * P.bInt := by
  rw [← SC.integral_ψL_four P hQ]
  unfold PrimeSetup.g
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only [zero_sub, SC.ψL_neg]; ring

theorem J2_PhiSq_eq {Q : ℝ} (hQ : 1 < Q) (T : ℝ) :
    ∫ t in P.J T, ∫ t' in P.J T, PhiSq P Q (t - t') = (P.𝒦 Q T 1 1).re := by
  have inner : ∀ t : ℝ, (∫ t' in P.J T, P.Φ Q (t - t') ^ 2 * ((1 : ℕ) : ℂ) ^ (-(Complex.I * t)) *
      ((1 : ℕ) : ℂ) ^ (Complex.I * t')) = ((∫ t' in P.J T, PhiSq P Q (t - t') : ℝ) : ℂ) := by
    intro t
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t' => ?_)
    simp only [Nat.cast_one, Complex.one_cpow, mul_one]
    rw [Φ_sq_eq_PhiSq]
  have h : P.𝒦 Q T 1 1 = ((∫ t in P.J T, ∫ t' in P.J T, PhiSq P Q (t - t') : ℝ) : ℂ) := by
    unfold PrimeSetup.𝒦
    simp_rw [inner]
    rw [integral_complex_ofReal]
  rw [h, Complex.ofReal_re]

/-- `∬_{J²} Φ(t−t')² ≤ 2π|J| b L + O(1)` (`eq:Kdiag` at `n = 1`). -/
theorem J2_PhiSq_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ Q T : ℝ, 1 < Q → 0 < T →
    ∫ t in P.J T, ∫ t' in P.J T, PhiSq P Q (t - t') ≤
      2 * Real.pi * P.Jlen T * P.bInt * P.L Q + C := by
  obtain ⟨C, hC⟩ := lemM1_diag P
  refine ⟨max C 0, le_max_right _ _, fun Q T hQ hT => ?_⟩
  have h := hC Q T hQ hT 1 le_rfl
  rw [J2_PhiSq_eq P hQ T]
  have hre : (P.𝒦 Q T 1 1).re - 2 * Real.pi * P.Jlen T * P.g Q (Real.log ((1 : ℕ) : ℝ)) ≤ C := by
    have := Complex.re_le_norm (P.𝒦 Q T 1 1 - 2 * Real.pi * P.Jlen T * P.g Q (Real.log ((1:ℕ):ℝ)))
    have e : (P.𝒦 Q T 1 1 - 2 * Real.pi * P.Jlen T * P.g Q (Real.log ((1:ℕ):ℝ))).re =
        (P.𝒦 Q T 1 1).re - 2 * Real.pi * P.Jlen T * P.g Q (Real.log ((1:ℕ):ℝ)) := by
      simp [Complex.sub_re, Complex.mul_re]
    rw [← e]; exact this.trans (by exact_mod_cast h)
  simp only [Nat.cast_one, Real.log_one, g_zero P hQ] at hre
  have := le_max_left C 0
  nlinarith

end Phi

/-! ### `μ_χ` -/

section Mu

lemma SC.digamma_continuousAt {z : ℂ} (hz : 0 < z.re) : ContinuousAt Complex.digamma z := by
  have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ Complex.Gamma {w : ℂ | 0 < w.re} := by
    intro w hw
    refine (Complex.differentiableAt_Gamma w fun m hm => ?_).differentiableWithinAt
    have : w.re = -(m : ℝ) := by rw [hm]; simp
    have hw' : 0 < w.re := hw
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have han : AnalyticAt ℂ Complex.Gamma z :=
    hdiff.analyticAt (hU.mem_nhds hz)
  have hderiv : ContinuousAt (deriv Complex.Gamma) z := han.deriv.continuousAt
  have hG : ContinuousAt Complex.Gamma z := han.continuousAt
  have hne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hz
  show ContinuousAt (fun w => deriv Complex.Gamma w / Complex.Gamma w) z
  exact hderiv.div hG hne

theorem digammaRe_continuous {a : ℝ} (ha : 0 ≤ a) : Continuous (digammaRe a) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hz : 0 < ((1 / 2 + a + Complex.I * t) / 2 : ℂ).re := by
    simp; linarith
  have h1 : ContinuousAt (fun t : ℝ => ((1 / 2 + a + Complex.I * t) / 2 : ℂ)) t := by
    fun_prop
  have h2 : ContinuousAt (fun s : ℝ => Complex.digamma ((1 / 2 + a + Complex.I * s) / 2)) t :=
    ContinuousAt.comp (f := fun s : ℝ => ((1 / 2 + a + Complex.I * s) / 2 : ℂ))
      (SC.digamma_continuousAt hz) h1
  exact Complex.continuous_re.continuousAt.comp h2


theorem aChi_cases {q : ℕ} (χ : DirichletCharacter ℂ q) : aChi χ = 0 ∨ aChi χ = 1 := by
  unfold aChi; split_ifs <;> simp

theorem SC.aChi_nonneg {q : ℕ} (χ : DirichletCharacter ℂ q) : 0 ≤ aChi χ := by
  rcases aChi_cases χ with h | h <;> rw [h] <;> norm_num

theorem muChi_continuous {q : ℕ} (χ : DirichletCharacter ℂ q) : Continuous (muChi χ) := by
  unfold muChi
  exact continuous_const.add (continuous_const.mul (digammaRe_continuous (SC.aChi_nonneg χ)))

/-- On `J`: `μ_χ(t) = (1/2π)(log(q/π) + log T) + O(1)` (Stirling (i)). -/
theorem muChi_near_J (hStir : StirlingDigamma) : ∃ R₀ : ℝ, 0 ≤ R₀ ∧
    ∀ (P : PrimeSetup) (T : ℝ), 1 ≤ T → ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), ∀ t ∈ P.J T,
      |muChi χ t - 1 / (2 * Real.pi) * (Real.log (q / Real.pi) + Real.log T)| ≤ R₀ := by
  obtain ⟨C, hC⟩ := hStir
  have hC0 : 0 ≤ C := by
    have := (hC 0 (Or.inl rfl)).1 1 le_rfl
    have h0 := abs_nonneg (digammaRe 0 1 - Real.log (1 / 2))
    linarith [show C / 1 = C from div_one C]
  have hpi := Real.pi_pos
  refine ⟨(C + Real.log 2) / (2 * Real.pi), by
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num); positivity, ?_⟩
  intro P T hT q χ t ht
  have hθ0 := P.θ_pos
  have hθ1 := P.θ_lt
  obtain ⟨ht1, ht2⟩ := ht
  have htT : T ≤ t := by nlinarith
  have ht1' : 1 ≤ t := le_trans hT htT
  have ht2T : t ≤ 2 * T := by nlinarith
  have htpos : 0 < t := by linarith
  have hTpos : 0 < T := by linarith
  have hi := (hC (aChi χ) (aChi_cases χ)).1 t ht1'
  have hCt : C / t ≤ C := div_le_self hC0 ht1'
  have hlog : |Real.log (t / 2) - Real.log T| ≤ Real.log 2 := by
    rw [← Real.log_div (by positivity) hTpos.ne']
    have h1 : t / 2 / T ≤ 1 := by rw [div_div, div_le_one (by positivity)]; linarith
    have h2 : 1 / 2 ≤ t / 2 / T := by
      rw [div_div, le_div_iff₀ (by positivity)]; linarith
    have hpos : 0 < t / 2 / T := by positivity
    rw [abs_le]
    constructor
    · have := Real.log_le_log (by norm_num) h2
      rw [one_div, Real.log_inv] at this
      linarith
    · have := Real.log_le_log hpos h1
      rw [Real.log_one] at this
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
      linarith
  have key : muChi χ t - 1 / (2 * Real.pi) * (Real.log (q / Real.pi) + Real.log T) =
      1 / (2 * Real.pi) * ((digammaRe (aChi χ) t - Real.log (t / 2)) +
        (Real.log (t / 2) - Real.log T)) := by
    unfold muChi; ring
  rw [key, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  have := abs_add_le (digammaRe (aChi χ) t - Real.log (t / 2)) (Real.log (t / 2) - Real.log T)
  rw [div_eq_mul_one_div (C + Real.log 2), mul_comm ((C + Real.log 2)) _]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith

/-- Globally: `|μ_χ(t)| ≤ (1/2π)(|log(q/π)| + C log(|t|+2))` (Stirling (ii)). -/
theorem muChi_abs_le (hStir : StirlingDigamma) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ),
      |muChi χ t| ≤ 1 / (2 * Real.pi) * (|Real.log (q / Real.pi)| + C * Real.log (|t| + 2)) := by
  obtain ⟨C, hC⟩ := hStir
  have hC0 : 0 ≤ C := by
    have := (hC 0 (Or.inl rfl)).2.1 0
    have h0 := abs_nonneg (digammaRe 0 0)
    have hl : 0 < Real.log (|(0 : ℝ)| + 2) := by
      rw [abs_zero, zero_add]; exact Real.log_pos (by norm_num)
    by_contra hneg
    push_neg at hneg
    have : C * Real.log (|(0 : ℝ)| + 2) < 0 := mul_neg_of_neg_of_pos hneg hl
    linarith
  refine ⟨C, hC0, fun q χ t => ?_⟩
  have hii := (hC (aChi χ) (aChi_cases χ)).2.1 t
  have hpi := Real.pi_pos
  unfold muChi
  rw [← mul_add]
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (abs_add_le _ _).trans (by linarith)

end Mu

/-! ### `a_n` and `S_χ[a]` -/

section Sums
variable (P : PrimeSetup)

theorem aVec_nonneg (Q : ℝ) (n : ℕ) : 0 ≤ P.aVec Q n := by
  unfold PrimeSetup.aVec PrimeSetup.Ups
  exact mul_nonneg (div_nonneg vonMangoldt_nonneg (Real.sqrt_nonneg _)) (P.Υ₀_range _).1

theorem aVec_zero (Q : ℝ) : P.aVec Q 0 = 0 := by
  simp [PrimeSetup.aVec]

theorem aVec_one (Q : ℝ) : P.aVec Q 1 = 0 := by
  simp [PrimeSetup.aVec]

theorem aVec_le (Q : ℝ) (n : ℕ) : P.aVec Q n ≤ Real.log n / Real.sqrt n := by
  unfold PrimeSetup.aVec PrimeSetup.Ups
  have h1 := (P.Υ₀_range (Real.log n / P.L Q))
  have h2 : Λ n / Real.sqrt n ≤ Real.log n / Real.sqrt n :=
    div_le_div_of_nonneg_right vonMangoldt_le_log (Real.sqrt_nonneg _)
  have h3 : 0 ≤ Λ n / Real.sqrt n := div_nonneg vonMangoldt_nonneg (Real.sqrt_nonneg _)
  calc Λ n / Real.sqrt n * P.Υ₀ (Real.log n / P.L Q) ≤ Λ n / Real.sqrt n * 1 :=
        mul_le_mul_of_nonneg_left h1.2 h3
    _ ≤ _ := by rw [mul_one]; exact h2

lemma SC.aVec_sq_le (Q : ℝ) (n : ℕ) : P.aVec Q n ^ 2 ≤ Real.log n ^ 2 / n := by
  have h0 := aVec_nonneg P Q n
  have h1 := aVec_le P Q n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [aVec_zero]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn'.le
  calc P.aVec Q n ^ 2 ≤ (Real.log n / Real.sqrt n) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ = Real.log n ^ 2 / n := by rw [div_pow, hs]

lemma SC.log_Y_le (Q : ℝ) : Real.log (P.Y Q) ≤ 3 * P.L Q ∨ P.L Q < 0 := by
  rcases le_or_gt 0 (P.L Q) with hL | hL
  · left
    rw [Families.Phase3.C.log_Y]
    have : P.ε₁ < 2 := by
      have := P.lam_ε₁; have := P.lam_pos; have := P.ε₁_pos; nlinarith
    nlinarith
  · right; exact hL

lemma SC.mem_range_le {Q : ℝ} {n : ℕ} (hn : n ∈ P.range Q) : 1 ≤ n ∧ (n : ℝ) ≤ P.Y Q := by
  unfold PrimeSetup.range at hn
  rw [Finset.mem_Icc] at hn
  exact ⟨hn.1, (Nat.le_floor_iff (Families.Phase3.C.Y_pos' P Q).le).mp hn.2⟩

lemma SC.log_le_of_mem_range {Q : ℝ} (hL : 0 ≤ P.L Q) {n : ℕ} (hn : n ∈ P.range Q) :
    0 ≤ Real.log n ∧ Real.log n ≤ 3 * P.L Q := by
  obtain ⟨h1, h2⟩ := SC.mem_range_le P hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast h1
  refine ⟨Real.log_nonneg (by exact_mod_cast h1), ?_⟩
  have := Real.log_le_log hn0 h2
  rcases SC.log_Y_le P Q with h | h
  · linarith
  · linarith

lemma SC.harmonic_range_le {Q : ℝ} (hL : 0 ≤ P.L Q) :
    ∑ n ∈ P.range Q, (1 : ℝ) / n ≤ 1 + 3 * P.L Q := by
  unfold PrimeSetup.range
  have h := harmonic_le_one_add_log ⌊P.Y Q⌋₊
  rw [harmonic_eq_sum_Icc] at h
  push_cast at h
  have e : ∑ n ∈ Finset.Icc 1 ⌊P.Y Q⌋₊, (1 : ℝ) / n = ∑ i ∈ Finset.Icc 1 ⌊P.Y Q⌋₊, ((i : ℝ))⁻¹ := by
    refine Finset.sum_congr rfl fun i _ => by rw [one_div]
  rw [e]
  refine h.trans ?_
  rcases Nat.eq_zero_or_pos ⌊P.Y Q⌋₊ with h0 | h0
  · rw [h0]; simp; linarith
  have hN : (1 : ℝ) ≤ ⌊P.Y Q⌋₊ := by exact_mod_cast h0
  have hNY : (⌊P.Y Q⌋₊ : ℝ) ≤ P.Y Q := Nat.floor_le (Families.Phase3.C.Y_pos' P Q).le
  have := Real.log_le_log (by linarith) hNY
  rcases SC.log_Y_le P Q with h' | h'
  · linarith
  · linarith

/-- Crude: `∑_{n ≤ Y} a_n² ≤ C L³`. -/
theorem sum_aVec_sq_le : ∃ C Q₀ : ℝ, 0 ≤ C ∧ ∀ Q : ℝ, Q₀ ≤ Q →
    ∑ n ∈ P.range Q, P.aVec Q n ^ 2 ≤ C * P.L Q ^ 3 := by
  refine ⟨36, Real.exp (1 / P.lam), by norm_num, fun Q hQ => ?_⟩
  have hL1 : 1 ≤ P.L Q := Families.Phase3.C.one_le_L P hQ
  have hL0 : 0 ≤ P.L Q := by linarith
  calc ∑ n ∈ P.range Q, P.aVec Q n ^ 2 ≤ ∑ n ∈ P.range Q, (3 * P.L Q) ^ 2 * ((1 : ℝ) / n) := by
        refine Finset.sum_le_sum fun n hn => ?_
        obtain ⟨hl0, hl⟩ := SC.log_le_of_mem_range P hL0 hn
        refine (SC.aVec_sq_le P Q n).trans ?_
        rw [div_eq_mul_one_div]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hl0 hl 2)
          (by have := (SC.mem_range_le P hn).1; positivity)
    _ = (3 * P.L Q) ^ 2 * ∑ n ∈ P.range Q, (1 : ℝ) / n := by rw [Finset.mul_sum]
    _ ≤ (3 * P.L Q) ^ 2 * (1 + 3 * P.L Q) :=
        mul_le_mul_of_nonneg_left (SC.harmonic_range_le P hL0) (by positivity)
    _ ≤ 36 * P.L Q ^ 3 := by nlinarith

/-- Crude: `∑_{n ≤ Y} a_n² / log n ≤ C L²`. -/
theorem sum_aVec_sq_div_log_le : ∃ C Q₀ : ℝ, 0 ≤ C ∧ ∀ Q : ℝ, Q₀ ≤ Q →
    ∑ n ∈ P.range Q, P.aVec Q n ^ 2 / Real.log n ≤ C * P.L Q ^ 2 := by
  refine ⟨12, Real.exp (1 / P.lam), by norm_num, fun Q hQ => ?_⟩
  have hL1 : 1 ≤ P.L Q := Families.Phase3.C.one_le_L P hQ
  have hL0 : 0 ≤ P.L Q := by linarith
  calc ∑ n ∈ P.range Q, P.aVec Q n ^ 2 / Real.log n ≤ ∑ n ∈ P.range Q, (3 * P.L Q) * ((1 : ℝ) / n) := by
        refine Finset.sum_le_sum fun n hn => ?_
        obtain ⟨hl0, hl⟩ := SC.log_le_of_mem_range P hL0 hn
        have hn1 := (SC.mem_range_le P hn).1
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
        rcases eq_or_lt_of_le hl0 with h | h
        · rw [← h, div_zero]; positivity
        · rw [div_le_iff₀ h]
          calc P.aVec Q n ^ 2 ≤ Real.log n ^ 2 / n := SC.aVec_sq_le P Q n
            _ = Real.log n * ((1 : ℝ) / n) * Real.log n := by ring
            _ ≤ 3 * P.L Q * ((1 : ℝ) / n) * Real.log n := by
                apply mul_le_mul_of_nonneg_right _ hl0
                exact mul_le_mul_of_nonneg_right hl (by positivity)
    _ = (3 * P.L Q) * ∑ n ∈ P.range Q, (1 : ℝ) / n := by rw [Finset.mul_sum]
    _ ≤ (3 * P.L Q) * (1 + 3 * P.L Q) :=
        mul_le_mul_of_nonneg_left (SC.harmonic_range_le P hL0) (by positivity)
    _ ≤ 12 * P.L Q ^ 2 := by nlinarith

/-- Crude: `∑_{n ≤ Y} a_n² / log² n ≤ C L`. -/
theorem sum_aVec_sq_div_log_sq_le : ∃ C Q₀ : ℝ, 0 ≤ C ∧ ∀ Q : ℝ, Q₀ ≤ Q →
    ∑ n ∈ P.range Q, P.aVec Q n ^ 2 / Real.log n ^ 2 ≤ C * P.L Q := by
  refine ⟨4, Real.exp (1 / P.lam), by norm_num, fun Q hQ => ?_⟩
  have hL1 : 1 ≤ P.L Q := Families.Phase3.C.one_le_L P hQ
  have hL0 : 0 ≤ P.L Q := by linarith
  calc ∑ n ∈ P.range Q, P.aVec Q n ^ 2 / Real.log n ^ 2 ≤ ∑ n ∈ P.range Q, (1 : ℝ) / n := by
        refine Finset.sum_le_sum fun n hn => ?_
        obtain ⟨hl0, -⟩ := SC.log_le_of_mem_range P hL0 hn
        have hn1 := (SC.mem_range_le P hn).1
        have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
        rcases eq_or_lt_of_le hl0 with h | h
        · rw [← h]; simp
        · rw [div_le_iff₀ (by positivity)]
          calc P.aVec Q n ^ 2 ≤ Real.log n ^ 2 / n := SC.aVec_sq_le P Q n
            _ = 1 / n * Real.log n ^ 2 := by ring
    _ ≤ 1 + 3 * P.L Q := SC.harmonic_range_le P hL0
    _ ≤ 4 * P.L Q := by linarith

theorem Schi_continuous {q : ℕ} (χ : DirichletCharacter ℂ q) (Q : ℝ) (x : ℕ → ℝ) :
    Continuous (P.Schi χ Q x) := by
  unfold PrimeSetup.Schi
  refine continuous_finsetSum _ fun n hn => ?_
  have hn1 := (SC.mem_range_le P hn).1
  have hn0 : 0 < ((n : ℂ)).re := by simp; exact_mod_cast hn1
  exact continuous_const.mul (continuous_const.cpow (by fun_prop) fun _ => Or.inl hn0)

theorem PChi_continuous (Q : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Continuous (PChi P Q χ) := by
  unfold PChi
  exact continuous_const.mul (Complex.continuous_re.comp (Schi_continuous P χ Q _))

end Sums

/-! ### The large sieve and the mass `H` -/

section LS

lemma SC.sum_intervalZ_one {M : Type*} [AddCommMonoid M] (K : ℕ) (f : ℤ → M) :
    ∑ n ∈ intervalZ 1 K, f n = ∑ n ∈ Finset.Icc 1 K, f (n : ℤ) := by
  symm
  refine Finset.sum_bij' (fun (k : ℕ) _ => (k : ℤ)) (fun (n : ℤ) _ => n.toNat) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    simp only [intervalZ, Finset.mem_Ico]
    omega
  · intro n hn
    simp only [intervalZ, Finset.mem_Ico] at hn
    simp only [Finset.mem_Icc]
    omega
  · intro k _; simp
  · intro n hn
    simp only [intervalZ, Finset.mem_Ico] at hn
    omega
  · intro k _; rfl

/-- The multiplicative large sieve on `[1, Y]` (`eq:MVLS`). -/
theorem famLS (hMV : MV_LargeSieve) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧
    ∀ (P : PrimeSetup) (Q : ℝ), 1 ≤ Q → ∀ x : ℕ → ℂ,
      ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (q : ℝ) / (Nat.totient q : ℝ) *
          ∑ χ ∈ primChars q, ‖∑ n ∈ P.range Q, x n * χ n‖ ^ 2
        ≤ C₀ * (Q ^ 2 + P.Y Q) * ∑ n ∈ P.range Q, ‖x n‖ ^ 2 := by
  obtain ⟨C₀, hmult, -⟩ := hMV
  refine ⟨max C₀ 0, le_max_right _ _, fun P Q hQ x => ?_⟩
  set K := ⌊P.Y Q⌋₊ with hK
  set x' : ℤ → ℂ := fun n => if 1 ≤ n then x n.toNat else 0 with hx'
  have h := hmult Q hQ 1 K x'
  have hS : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      ∑ n ∈ intervalZ 1 K, x' n * χ n = ∑ n ∈ P.range Q, x n * χ n := by
    intro q χ
    rw [SC.sum_intervalZ_one]
    unfold PrimeSetup.range
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    simp only [hx', show (1 : ℤ) ≤ (n : ℤ) by exact_mod_cast hn1, if_true, Int.toNat_natCast,
      Int.cast_natCast]
  have hN : normSq (intervalZ 1 K) x' = ∑ n ∈ P.range Q, ‖x n‖ ^ 2 := by
    unfold normSq
    rw [SC.sum_intervalZ_one]
    unfold PrimeSetup.range
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    simp only [hx', show (1 : ℤ) ≤ (n : ℤ) by exact_mod_cast hn1, if_true, Int.toNat_natCast]
  simp_rw [hS] at h
  rw [hN] at h
  have hKY : (K : ℝ) ≤ P.Y Q := Nat.floor_le (Families.Phase3.C.Y_pos' P Q).le
  have hsum0 : 0 ≤ ∑ n ∈ P.range Q, ‖x n‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  refine h.trans ?_
  have hQK : 0 ≤ Q ^ 2 + (K : ℝ) := by positivity
  calc C₀ * (Q ^ 2 + K) * ∑ n ∈ P.range Q, ‖x n‖ ^ 2
      ≤ max C₀ 0 * (Q ^ 2 + K) * ∑ n ∈ P.range Q, ‖x n‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hsum0
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) hQK
    _ ≤ max C₀ 0 * (Q ^ 2 + P.Y Q) * ∑ n ∈ P.range Q, ‖x n‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hsum0
        exact mul_le_mul_of_nonneg_left (by linarith) (le_max_right _ _)

/-- `ω(q) ≤ w_max q/φ(q)`. -/
theorem omega_le (W : Weight) (Q : ℝ) (q : ℕ) :
    W.omega Q q ≤ W.wmax * ((q : ℝ) / (Nat.totient q : ℝ)) := by
  unfold Weight.omega
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_right (W.le_wmax _) (by positivity)

/-- The large sieve with the family weights. -/
theorem famLS_omega (hMV : MV_LargeSieve) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧
    ∀ (P : PrimeSetup) (W : Weight) (Q : ℝ), 1 ≤ Q → ∀ x : ℕ → ℂ,
      ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ χ ∈ primChars q, ‖∑ n ∈ P.range Q, x n * χ n‖ ^ 2
        ≤ W.wmax * C₀ * (Q ^ 2 + P.Y Q) * ∑ n ∈ P.range Q, ‖x n‖ ^ 2 := by
  obtain ⟨C₀, hC₀, h⟩ := famLS hMV
  refine ⟨C₀, hC₀, fun P W Q hQ x => ?_⟩
  have hw := W.wmax_nonneg
  calc ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ χ ∈ primChars q, ‖∑ n ∈ P.range Q, x n * χ n‖ ^ 2
      ≤ ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.wmax * ((q : ℝ) / (Nat.totient q : ℝ) *
          ∑ χ ∈ primChars q, ‖∑ n ∈ P.range Q, x n * χ n‖ ^ 2) := by
        refine Finset.sum_le_sum fun q _ => ?_
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (omega_le W Q q)
          (Finset.sum_nonneg fun _ _ => by positivity)
    _ = W.wmax * ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ((q : ℝ) / (Nat.totient q : ℝ) *
          ∑ χ ∈ primChars q, ‖∑ n ∈ P.range Q, x n * χ n‖ ^ 2) := by rw [Finset.mul_sum]
    _ ≤ W.wmax * (C₀ * (Q ^ 2 + P.Y Q) * ∑ n ∈ P.range Q, ‖x n‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (h P Q hQ x) hw
    _ = _ := by ring

/-- Bilinear form of the large sieve. -/
theorem bilinLS (hMV : MV_LargeSieve) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧
    ∀ (P : PrimeSetup) (Q : ℝ), 1 ≤ Q →
    ∀ (b : (q : ℕ) → DirichletCharacter ℂ q → ℂ) (x : ℕ → ℂ),
      ‖∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ ∈ primChars q, b q χ * ∑ n ∈ P.range Q, x n * χ n‖ ^ 2
        ≤ (∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ ∈ primChars q, (Nat.totient q : ℝ) / q * ‖b q χ‖ ^ 2) *
          (C₀ * (Q ^ 2 + P.Y Q) * ∑ n ∈ P.range Q, ‖x n‖ ^ 2) := by
  obtain ⟨C₀, hC₀, h⟩ := famLS hMV
  refine ⟨C₀, hC₀, fun P Q hQ b x => ?_⟩
  set S : (q : ℕ) → DirichletCharacter ℂ q → ℂ := fun q χ => ∑ n ∈ P.range Q, x n * χ n with hSdef
  set A := Finset.Icc 1 ⌊Q⌋₊
  set I := A.sigma fun q => primChars q
  set f : (Σ q : ℕ, DirichletCharacter ℂ q) → ℝ := fun z =>
    Real.sqrt ((Nat.totient z.1 : ℝ) / z.1) * ‖b z.1 z.2‖ with hf
  set g : (Σ q : ℕ, DirichletCharacter ℂ q) → ℝ := fun z =>
    Real.sqrt ((z.1 : ℝ) / (Nat.totient z.1 : ℝ)) * ‖S z.1 z.2‖ with hg
  have hmemq : ∀ z ∈ I, 1 ≤ z.1 := by
    intro z hz
    have := (Finset.mem_sigma.mp hz).1
    exact (Finset.mem_Icc.mp this).1
  have hfg : ∀ z ∈ I, ‖b z.1 z.2‖ * ‖S z.1 z.2‖ = f z * g z := by
    intro z hz
    have hq := hmemq z hz
    have hq0 : (0 : ℝ) < z.1 := by exact_mod_cast hq
    have hφ : (0 : ℝ) < Nat.totient z.1 := by exact_mod_cast Nat.totient_pos.mpr hq
    simp only [hf, hg]
    have : Real.sqrt ((Nat.totient z.1 : ℝ) / z.1) * Real.sqrt ((z.1 : ℝ) / (Nat.totient z.1 : ℝ))
        = 1 := by
      rw [← Real.sqrt_mul (by positivity)]
      rw [show (Nat.totient z.1 : ℝ) / z.1 * (z.1 / Nat.totient z.1) = 1 by field_simp]
      simp
    calc ‖b z.1 z.2‖ * ‖S z.1 z.2‖ = (Real.sqrt ((Nat.totient z.1 : ℝ) / z.1) *
        Real.sqrt ((z.1 : ℝ) / (Nat.totient z.1 : ℝ))) * (‖b z.1 z.2‖ * ‖S z.1 z.2‖) := by
          rw [this, one_mul]
      _ = _ := by ring
  have hf2 : ∀ z ∈ I, f z ^ 2 = (Nat.totient z.1 : ℝ) / z.1 * ‖b z.1 z.2‖ ^ 2 := by
    intro z _
    simp only [hf, mul_pow]
    rw [Real.sq_sqrt (by positivity)]
  have hg2 : ∀ z ∈ I, g z ^ 2 = (z.1 : ℝ) / (Nat.totient z.1 : ℝ) * ‖S z.1 z.2‖ ^ 2 := by
    intro z _
    simp only [hg, mul_pow]
    rw [Real.sq_sqrt (by positivity)]
  have hnorm : ‖∑ q ∈ A, ∑ χ ∈ primChars q, b q χ * S q χ‖ ≤ ∑ z ∈ I, f z * g z := by
    rw [Finset.sum_sigma']
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [norm_mul, hfg z hz]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq I f g
  have hsumf : ∑ z ∈ I, f z ^ 2 =
      ∑ q ∈ A, ∑ χ ∈ primChars q, (Nat.totient q : ℝ) / q * ‖b q χ‖ ^ 2 := by
    rw [Finset.sum_congr rfl hf2]
    exact (Finset.sum_sigma' A (fun q => primChars q)
      (fun q χ => (Nat.totient q : ℝ) / q * ‖b q χ‖ ^ 2)).symm
  have hsumg : ∑ z ∈ I, g z ^ 2 =
      ∑ q ∈ A, (q : ℝ) / (Nat.totient q : ℝ) * ∑ χ ∈ primChars q, ‖S q χ‖ ^ 2 := by
    rw [Finset.sum_congr rfl hg2]
    rw [← (Finset.sum_sigma' A (fun q => primChars q)
      (fun q χ => (q : ℝ) / (Nat.totient q : ℝ) * ‖S q χ‖ ^ 2))]
    refine Finset.sum_congr rfl fun q _ => by rw [Finset.mul_sum]
  have hfg0 : 0 ≤ ∑ z ∈ I, f z * g z := Finset.sum_nonneg fun z _ => by
    simp only [hf, hg]; positivity
  calc ‖∑ q ∈ A, ∑ χ ∈ primChars q, b q χ * S q χ‖ ^ 2 ≤ (∑ z ∈ I, f z * g z) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ (∑ z ∈ I, f z ^ 2) * ∑ z ∈ I, g z ^ 2 := hCS
    _ ≤ _ := by
        rw [hsumf, hsumg]
        apply mul_le_mul_of_nonneg_left (h P Q hQ x)
        exact Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun _ _ => by positivity

/-- `H ≫ Q²` (from `lem:WH`). -/
theorem H_lower (hWH : lemWH_Statement) (W : Weight) :
    ∃ c Q₀ : ℝ, 0 < c ∧ ∀ Q : ℝ, Q₀ ≤ Q → c * Q ^ 2 ≤ W.H Q := by
  have h := H_lower_eventually hWH W (κ := 1 / 2) (by norm_num)
  obtain ⟨Q₀, hQ₀⟩ := Filter.eventually_atTop.mp h
  refine ⟨1 / 2 * (Ecal * W.Iw), Q₀, by have := Ecal_pos; have := W.Iw_pos; positivity,
    fun Q hQ => ?_⟩
  have := hQ₀ Q hQ
  linarith

end LS

end Families.Ported.Second
