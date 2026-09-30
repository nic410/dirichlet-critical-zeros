/-
# Zero side: Fourier-analytic facts about the window transform `\widehat{ψ_L}`

* `envelope` (paper `lem:envelope`): `|ψ̂_L(r − iδ)| ≤ C_A L e^{L|δ|/2} (1 + L|r|)^{−A}`, and its
  lattice-shifted form `envelope_pk`.
* `gabor_hasSum`, `bessel` (paper `lem:gabor`, diagonal): for real `t`,
  `∑_k |p_k(t)|² = a L²` (Parseval on the circle `ℝ/Lℤ`), hence `∑_{k∈S} |p_k(t)|² ≤ a L²`.
* `integrable_normSq_pk`, `integral_normSq_pk` (Plancherel): `∫_ℝ |p_k(t)|² dt = 2π a L`.
* `aInt_pos`, `integral_ψL_sq`: `a = ∫ψ² > 0` and `∫ ψ_L² = L a`.
-/
import Families.Ported.Zero.ExplicitFormula
import Zeta23.ExplicitFormula.Bridge

noncomputable section

open scoped BigOperators ComplexConjugate ContDiff
open Complex Set MeasureTheory

namespace Families.Ported.Zero

open Zeta23

variable (P : PrimeSetup)

/-! ### Support of `ψ`, `ψ_L` -/

lemma abs_le_half_of_ψ_ne {u : ℝ} (hu : P.ψ u ≠ 0) : |u| ≤ 1 / 2 := by
  obtain ⟨r, hr, h⟩ := P.ψ_supp
  by_contra hc
  push Not at hc
  exact hu (h u (by linarith))

lemma abs_lt_of_ψL_ne {Q : ℝ} (hQ : 1 < Q) {u : ℝ} (hu : P.ψL Q u ≠ 0) : |u| < P.L Q / 2 := by
  obtain ⟨r, hr, h⟩ := ψL_supp P
  have hL := L_pos P hQ
  have : |u| ≤ r * P.L Q := by
    by_contra hc
    push Not at hc
    exact hu (h Q hQ u hc)
  nlinarith

/-- Integrals of functions vanishing off `supp ψ_L` over `[−L/2, L/2]` are full-line integrals. -/
lemma intervalIntegral_eq_integral_of_ψL {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Q : ℝ} (hQ : 1 < Q) (g : ℝ → E) (hg : ∀ u, P.ψL Q u = 0 → g u = 0) :
    ∫ x in (-(P.L Q / 2))..(P.L Q / 2), g x = ∫ x, g x := by
  have hL := L_pos P hQ
  rw [intervalIntegral.integral_of_le (by linarith)]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => hg x ?_
  by_contra hne
  have := abs_lt.mp (abs_lt_of_ψL_ne P hQ hne)
  exact hx ⟨this.1, this.2.le⟩

/-! ### `a = ∫ ψ²` -/

theorem aInt_pos : 0 < P.aInt := by
  obtain ⟨x, hx⟩ := P.ψ_ne
  unfold PrimeSetup.aInt PrimeSetup.vfun
  have hc : Continuous P.ψ := P.ψ_smooth.continuous
  refine (hc.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero ?_
    (fun s => sq_nonneg (P.ψ s)) (x := x) (pow_ne_zero 2 hx)
  refine hasCompactSupport_of_support_subset_abs (Λ := 1 / 2) fun u hu => ?_
  exact abs_le_half_of_ψ_ne P fun h => hu (by simp [h])

theorem integral_ψL_sq {Q : ℝ} (hQ : 1 < Q) : ∫ u, P.ψL Q u ^ 2 = P.L Q * P.aInt := by
  have hL := L_pos P hQ
  have := Measure.integral_comp_div (fun s => P.ψ s ^ 2) (P.L Q)
  simp only [PrimeSetup.ψL, PrimeSetup.aInt, PrimeSetup.vfun]
  rw [this, abs_of_pos hL, smul_eq_mul]

/-! ### The envelope bound (`lem:envelope`) -/

/-- `ψ` as a complex-valued function. -/
def psiC : ℝ → ℂ := fun s => ((P.ψ s : ℝ) : ℂ)

lemma contDiff_psiC : ContDiff ℝ ∞ (psiC P) :=
  Complex.ofRealCLM.contDiff.comp P.ψ_smooth

lemma tsupport_psiC : tsupport (psiC P) ⊆ Icc (-(1 / 2)) (1 / 2) :=
  tsupport_subset_of_support_subset_abs fun u hu =>
    abs_le_half_of_ψ_ne P fun h => hu (by simp [psiC, h])

lemma tsupport_iter_deriv_psiC (n : ℕ) :
    tsupport (deriv^[n] (psiC P)) ⊆ Icc (-(1 / 2)) (1 / 2) := by
  induction n with
  | zero => exact tsupport_psiC P
  | succ n ih =>
    rw [Function.iterate_succ']
    exact tsupport_deriv_subset.trans ih

lemma hasCompactSupport_iter_deriv_psiC (n : ℕ) : HasCompactSupport (deriv^[n] (psiC P)) :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) (tsupport_iter_deriv_psiC P n)

lemma paperFT_iter_deriv_psiC (n : ℕ) (z : ℂ) :
    paperFT (deriv^[n] (psiC P)) z = (-(I * z)) ^ n * paperFT (psiC P) z := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', paperFT_deriv, ih, pow_succ]
    · ring
    · exact contDiff_infty.mp ((contDiff_psiC P).iterate_deriv n) 1
    · exact hasCompactSupport_iter_deriv_psiC P n

lemma norm_paperFT_psiC_le (n : ℕ) (z : ℂ) :
    ‖z‖ ^ n * ‖paperFT (psiC P) z‖ ≤
      Real.exp (|z.im| * (1 / 2)) * ∫ u, ‖deriv^[n] (psiC P) u‖ := by
  have hint : Integrable (deriv^[n] (psiC P)) :=
    ((contDiff_psiC P).iterate_deriv n).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_iter_deriv_psiC P n)
  have h := norm_paperFT_le (f := deriv^[n] (psiC P)) (Λ := 1 / 2) hint
    (fun u hu => abs_le.mpr (tsupport_iter_deriv_psiC P n (subset_tsupport _ hu))) z
  rw [paperFT_iter_deriv_psiC, norm_mul, norm_pow, norm_neg, norm_mul, Complex.norm_I,
    one_mul] at h
  exact h

/-- Rescaling: `\widehat{ψ_L}(w) = L · \hat ψ(L w)`. -/
lemma hatψL_eq_scale {Q : ℝ} (hQ : 1 < Q) (w : ℂ) :
    P.hatψL Q w = (P.L Q : ℂ) * paperFT (psiC P) ((P.L Q : ℂ) * w) := by
  have hL := L_pos P hQ
  have hL' : (P.L Q : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have := Measure.integral_comp_div
    (fun s : ℝ => ((P.ψ s : ℝ) : ℂ) * cexp (I * ((P.L Q : ℂ) * w) * s)) (P.L Q)
  rw [abs_of_pos hL, Complex.real_smul] at this
  unfold PrimeSetup.hatψL paperFT psiC PrimeSetup.ψL
  rw [← this]
  congr 1
  funext u
  congr 2
  push_cast
  field_simp

lemma one_add_pow_le_two_pow {x : ℝ} (hx : 0 ≤ x) (A : ℕ) : (1 + x) ^ A ≤ 2 ^ A * (1 + x ^ A) := by
  have hxA : 0 ≤ x ^ A := pow_nonneg hx A
  have h2 : (0 : ℝ) ≤ 2 ^ A := by positivity
  rcases le_total x 1 with h | h
  · have : (1 + x) ^ A ≤ 2 ^ A := pow_le_pow_left₀ (by linarith) (by linarith) A
    nlinarith
  · have : (1 + x) ^ A ≤ (2 * x) ^ A := pow_le_pow_left₀ (by linarith) (by linarith) A
    rw [mul_pow] at this
    nlinarith

/-- **`lem:envelope`**: `|\widehat{ψ_L}(w)| (1 + L|Re w|)^A ≪_A L e^{L|Im w|/2}`. -/
theorem envelope (A : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ Q : ℝ, 1 < Q → ∀ w : ℂ,
    ‖P.hatψL Q w‖ * (1 + P.L Q * |w.re|) ^ A ≤ C * P.L Q * Real.exp (P.L Q * |w.im| / 2) := by
  set C0 := ∫ u, ‖deriv^[0] (psiC P) u‖
  set CA := ∫ u, ‖deriv^[A] (psiC P) u‖
  have hC0 : 0 ≤ C0 := integral_nonneg fun _ => norm_nonneg _
  have hCA : 0 ≤ CA := integral_nonneg fun _ => norm_nonneg _
  refine ⟨2 ^ A * (C0 + CA), by positivity, fun Q hQ w => ?_⟩
  have hL := L_pos P hQ
  set z : ℂ := (P.L Q : ℂ) * w with hz
  have hzre : z.re = P.L Q * w.re := by simp [hz]
  have hzim : z.im = P.L Q * w.im := by simp [hz]
  have hE : Real.exp (|z.im| * (1 / 2)) = Real.exp (P.L Q * |w.im| / 2) := by
    rw [hzim, abs_mul, abs_of_pos hL]; ring_nf
  have h0 := norm_paperFT_psiC_le P 0 z
  have hA := norm_paperFT_psiC_le P A z
  rw [hE] at h0 hA
  rw [pow_zero, one_mul] at h0
  have hx : P.L Q * |w.re| ≤ ‖z‖ := by
    have := Complex.abs_re_le_norm z
    rwa [hzre, abs_mul, abs_of_pos hL] at this
  have hx0 : 0 ≤ P.L Q * |w.re| := by positivity
  have h3 : (1 + P.L Q * |w.re|) ^ A ≤ 2 ^ A * (1 + ‖z‖ ^ A) :=
    (one_add_pow_le_two_pow hx0 A).trans (by gcongr)
  rw [hatψL_eq_scale P hQ, norm_mul, Complex.norm_of_nonneg hL.le]
  set F := ‖paperFT (psiC P) z‖
  set E := Real.exp (P.L Q * |w.im| / 2)
  have hF : 0 ≤ F := norm_nonneg _
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  calc P.L Q * F * (1 + P.L Q * |w.re|) ^ A ≤ P.L Q * F * (2 ^ A * (1 + ‖z‖ ^ A)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = P.L Q * 2 ^ A * (F + ‖z‖ ^ A * F) := by ring
    _ ≤ P.L Q * 2 ^ A * (E * C0 + E * CA) := by gcongr
    _ = 2 ^ A * (C0 + CA) * P.L Q * E := by ring

/-- `lem:envelope` for the lattice translates `p_k(z) = \widehat{ψ_L}(z − τ_k)`. -/
theorem envelope_pk (A : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ Q : ℝ, 1 < Q → ∀ (τ₀ : ℝ) (k : ℤ) (z : ℂ),
    ‖P.pk Q τ₀ k z‖ * (1 + P.L Q * |z.re - tau P Q τ₀ k|) ^ A ≤
      C * P.L Q * Real.exp (P.L Q * |z.im| / 2) := by
  obtain ⟨C, hC, h⟩ := envelope P A
  refine ⟨C, hC, fun Q hQ τ₀ k z => ?_⟩
  have := h Q hQ (z - (tau P Q τ₀ k : ℂ))
  rw [← pk_eq] at this
  simpa using this

/-! ### Parseval on the lattice (`lem:gabor`, diagonal) -/

theorem gabor_hasSum {Q : ℝ} (hQ : 1 < Q) (τ₀ t : ℝ) :
    HasSum (fun k : ℤ => ‖P.pk Q τ₀ k t‖ ^ 2) (P.aInt * P.L Q ^ 2) := by
  have hL := L_pos P hQ
  have hL' : (P.L Q : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hab : -(P.L Q / 2) < P.L Q / 2 := by linarith
  have hba : P.L Q / 2 - -(P.L Q / 2) = P.L Q := by ring
  set g : ℝ → ℂ := fun u => ((P.ψL Q u : ℝ) : ℂ) * cexp (I * ((t - τ₀ : ℝ) : ℂ) * u) with hg
  have hgc : Continuous g := by
    have := (contDiff_ψL P Q).continuous
    fun_prop
  have hgs : HasCompactSupport g := by
    refine hasCompactSupport_of_support_subset_abs (Λ := P.L Q / 2) fun u hu => ?_
    refine (abs_lt_of_ψL_ne P hQ fun h => hu ?_).le
    simp [hg, h]
  have hmem : MemLp g 2 (volume.restrict (Ioc (-(P.L Q / 2)) (P.L Q / 2))) :=
    (hgc.memLp_of_hasCompactSupport hgs).restrict _
  have hS := hasSum_sq_fourierCoeffOn hab hmem
  have hnorm : ∀ u, ‖g u‖ ^ 2 = P.ψL Q u ^ 2 := by
    intro u
    rw [hg, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    simp
  have hval : (P.L Q / 2 - -(P.L Q / 2))⁻¹ • ∫ x in (-(P.L Q / 2))..(P.L Q / 2), ‖g x‖ ^ 2 =
      P.aInt := by
    rw [hba, intervalIntegral_eq_integral_of_ψL P hQ _ (fun u hu => by rw [hnorm, hu]; ring)]
    simp_rw [hnorm]
    rw [integral_ψL_sq P hQ, smul_eq_mul]
    field_simp
  rw [hval] at hS
  have hcoef : ∀ k : ℤ, fourierCoeffOn hab g k = (1 / (P.L Q : ℂ)) * P.pk Q τ₀ k t := by
    intro k
    rw [fourierCoeffOn_eq_integral]
    simp only [fourier_coe_apply]
    rw [intervalIntegral_eq_integral_of_ψL P hQ _ (fun u hu => by simp [hg, hu]), pk_eq,
      PrimeSetup.hatψL, Complex.real_smul, hba]
    push_cast
    congr 1
    congr 1
    funext x
    rw [smul_eq_mul, hg]
    simp only
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    simp only [tau]
    push_cast
    field_simp
    ring
  have hS' := hS.mul_left (P.L Q ^ 2)
  have hfun : (fun k : ℤ => ‖P.pk Q τ₀ k t‖ ^ 2) =
      fun i => P.L Q ^ 2 * ‖fourierCoeffOn hab g i‖ ^ 2 := by
    funext k
    rw [hcoef, norm_mul, mul_pow, norm_div, norm_one, Complex.norm_of_nonneg hL.le]
    field_simp
  rw [hfun, mul_comm]
  exact hS'

theorem bessel {Q : ℝ} (hQ : 1 < Q) (τ₀ : ℝ) (S : Finset ℤ) (t : ℝ) :
    ∑ k ∈ S, ‖P.pk Q τ₀ k t‖ ^ 2 ≤ P.aInt * P.L Q ^ 2 :=
  sum_le_hasSum S (fun _ _ => by positivity) (gabor_hasSum P hQ τ₀ t)

/-! ### Plancherel on the diagonal -/

lemma norm_fk (Q τ₀ : ℝ) (k : ℤ) (u : ℝ) : ‖fk P Q τ₀ k u‖ = |P.ψL Q u| := by
  unfold fk
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  simp

lemma hasCompactSupport_fk {Q : ℝ} (hQ : 1 < Q) (τ₀ : ℝ) (k : ℤ) :
    HasCompactSupport (fk P Q τ₀ k) :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) (tsupport_fk P hQ τ₀ k)

/-- `\hat k(t) = |p_k(t)|²` for the Weil test function `k = f_k ⋆ \tilde f_k`. -/
lemma paperFT_weilTest_fk {Q : ℝ} (hQ : 1 < Q) (τ₀ : ℝ) (k : ℤ) (t : ℝ) :
    paperFT (EF.weilTest (fk P Q τ₀ k) (fk P Q τ₀ k)) t = ((‖P.pk Q τ₀ k t‖ ^ 2 : ℝ) : ℂ) := by
  have hc := (contDiff_fk P Q τ₀ k).continuous
  have hs := hasCompactSupport_fk P hQ τ₀ k
  rw [EF.paperFT_weilTest hc hc hs hs, Complex.conj_ofReal, paperFT_fk, Complex.mul_conj']
  push_cast
  rfl

lemma weilTest_fk_zero {Q : ℝ} (hQ : 1 < Q) (τ₀ : ℝ) (k : ℤ) :
    EF.weilTest (fk P Q τ₀ k) (fk P Q τ₀ k) 0 = ((P.L Q * P.aInt : ℝ) : ℂ) := by
  simp only [EF.weilTest, convolution_def, ContinuousLinearMap.mul_apply', EF.tilde, zero_sub,
    neg_neg]
  simp_rw [Complex.mul_conj', norm_fk]
  rw [← integral_ψL_sq P hQ, ← integral_complex_ofReal]
  congr 1
  funext u
  rw [← Complex.ofReal_pow, sq_abs]

theorem integrable_normSq_pk {Q : ℝ} (hQ : 1 < Q) (τ₀ : ℝ) (k : ℤ) :
    Integrable (fun t : ℝ => ‖P.pk Q τ₀ k t‖ ^ 2) := by
  have hfc := contDiff_fk P Q τ₀ k
  have hfs := hasCompactSupport_fk P hQ τ₀ k
  have hKc := EF.weilTest_contDiff hfc hfc.continuous hfs
  have hKs := EF.weilTest_hasCompactSupport hfs hfs
  have hint := EF.integrable_paperFT_ofReal (EF.integrable_fourier_of_contDiff_two hKc hKs)
  refine hint.norm.congr (Filter.Eventually.of_forall fun t => ?_)
  simp only
  rw [paperFT_weilTest_fk P hQ, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

theorem integral_normSq_pk {Q : ℝ} (hQ : 1 < Q) (τ₀ : ℝ) (k : ℤ) :
    ∫ t : ℝ, ‖P.pk Q τ₀ k t‖ ^ 2 = 2 * Real.pi * P.aInt * P.L Q := by
  have hfc := contDiff_fk P Q τ₀ k
  have hfs := hasCompactSupport_fk P hQ τ₀ k
  have hKc := EF.weilTest_contDiff hfc hfc.continuous hfs
  have hKs := EF.weilTest_hasCompactSupport hfs hfs
  have hinv := EF.paper_inversion hKc.continuous
    (hKc.continuous.integrable_of_hasCompactSupport hKs)
    (EF.integrable_fourier_of_contDiff_two hKc hKs) 0
  have hI : (∫ r : ℝ, paperFT (EF.weilTest (fk P Q τ₀ k) (fk P Q τ₀ k)) r *
      cexp (-I * r * ((0 : ℝ) : ℂ))) = ((∫ t : ℝ, ‖P.pk Q τ₀ k t‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    funext r
    rw [paperFT_weilTest_fk P hQ]
    simp
  rw [hI, weilTest_fk_zero P hQ] at hinv
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2 : ((∫ t : ℝ, ‖P.pk Q τ₀ k t‖ ^ 2 : ℝ) : ℂ) =
      ((2 * Real.pi * P.aInt * P.L Q : ℝ) : ℂ) := by
    push_cast at hinv ⊢
    field_simp at hinv
    linear_combination -hinv
  exact_mod_cast h2

end Families.Ported.Zero
