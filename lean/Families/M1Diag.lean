/-
`lem:M1`, diagonal part (`lemma-B-majorant.tex` §5, `eq:Kdiag` of main.tex):
  `𝒦(n,n) = 2π|J| g(log n) + O_v(1)`, uniformly in `Q, T, n`.
Route: `𝒦(n,n) = ∫ Φ(r)² n^{−ir} (|J| − |r|)_+ dr` (change of variables on `J²`);
`∫ Φ(r)² n^{−ir} dr = 2π g(log n)` (Fourier inversion for the smooth compactly supported `g`,
via `HasCompactSupport.toSchwartzMap` and `Continuous.fourierInv_fourier_eq`);
`|(|J| − |r|)_+ − |J|| ≤ |r|` and `∫ |r| |Φ_Q(r)|² dr = ∫ |x| |V(x)|² dx` (scale invariance,
`Φ_Q(r) = L·V(Lr)`, `V = \widehat{ψ²}`), finite because `\widehat{ψ²}` is Schwartz.
-/
import Families.M1
open scoped BigOperators ComplexConjugate ContDiff FourierTransform
open MeasureTheory
noncomputable section
namespace Families
namespace PrimeSetup
variable (P : PrimeSetup)

lemma FR_contDiff {Q : ℝ} : ContDiff ℝ ∞ (P.FR Q) := by
  unfold FR ψL
  exact (P.ψ_smooth.comp (contDiff_id.div_const _)).pow 2

lemma g_contDiff {Q : ℝ} (hQ : 1 < Q) : ContDiff ℝ ∞ (P.g Q) := by
  have : P.g Q = convolution (P.FR Q) (P.FR Q) (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext u; exact P.g_eq_conv Q u
  rw [this]
  exact (P.FR_hasCompactSupport hQ).contDiff_convolution_right (n := ⊤) _
    (P.FR_integrable hQ).locallyIntegrable P.FR_contDiff

lemma g_hasCompactSupport {Q : ℝ} (hQ : 1 < Q) : HasCompactSupport (P.g Q) := by
  have : P.g Q = convolution (P.FR Q) (P.FR Q) (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext u; exact P.g_eq_conv Q u
  rw [this]
  exact (P.FR_hasCompactSupport hQ).convolution _ (P.FR_hasCompactSupport hQ)

/-- `g` as a complex function. -/
def gC (Q : ℝ) : ℝ → ℂ := fun u => (P.g Q u : ℂ)

lemma gC_hasCompactSupport {Q : ℝ} (hQ : 1 < Q) : HasCompactSupport (P.gC Q) :=
  (P.g_hasCompactSupport hQ).comp_left Complex.ofReal_zero

lemma gC_contDiff {Q : ℝ} (hQ : 1 < Q) : ContDiff ℝ ∞ (P.gC Q) :=
  Complex.ofRealCLM.contDiff.comp (P.g_contDiff hQ)

lemma fourier_gC_integrable {Q : ℝ} (hQ : 1 < Q) : Integrable (𝓕 (P.gC Q)) := by
  set GS := (P.gC_hasCompactSupport hQ).toSchwartzMap (P.gC_contDiff hQ)
  have h1 : (GS : ℝ → ℂ) = P.gC Q := rfl
  have h2 := (𝓕 GS).integrable (μ := volume)
  rw [SchwartzMap.fourier_coe, h1] at h2
  exact h2

lemma fourier_gC_continuous {Q : ℝ} (hQ : 1 < Q) : Continuous (𝓕 (P.gC Q)) := by
  set GS := (P.gC_hasCompactSupport hQ).toSchwartzMap (P.gC_contDiff hQ)
  have h1 : (GS : ℝ → ℂ) = P.gC Q := rfl
  have h2 := (𝓕 GS).continuous
  rw [SchwartzMap.fourier_coe, h1] at h2
  exact h2

/-- `Φ(r)² = 𝓕g(−r/2π)` (Mathlib's `𝓕 f(w) = ∫ e^{−2πivw} f(v) dv`). -/
lemma Φ_sq_eq_fourier {Q : ℝ} (hQ : 1 < Q) (r : ℝ) :
    P.Φ Q r ^ 2 = 𝓕 (P.gC Q) (-(r / (2 * Real.pi))) := by
  rw [P.Φ_sq_eq hQ, Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [gC, smul_eq_mul]
  rw [mul_comm]
  congr 2
  push_cast
  field_simp

lemma Φ_sq_integrable {Q : ℝ} (hQ : 1 < Q) : Integrable (fun r => P.Φ Q r ^ 2) := by
  have h := (P.fourier_gC_integrable hQ).comp_mul_left'
    (R := -(1 / (2 * Real.pi))) (by simp [Real.pi_ne_zero])
  refine h.congr (Filter.Eventually.of_forall fun r => ?_)
  simp only
  rw [P.Φ_sq_eq_fourier hQ, show -(1 / (2 * Real.pi)) * r = -(r / (2 * Real.pi)) by ring]

lemma Φ_sq_continuous {Q : ℝ} (hQ : 1 < Q) : Continuous (fun r => P.Φ Q r ^ 2) := by
  have : (fun r => P.Φ Q r ^ 2) = fun r => 𝓕 (P.gC Q) (-(r / (2 * Real.pi))) := by
    funext r; exact P.Φ_sq_eq_fourier hQ r
  rw [this]
  exact (P.fourier_gC_continuous hQ).comp (by fun_prop)

/-- Fourier inversion: `∫ Φ(r)² e^{−irℓ} dr = 2π g(ℓ)`. -/
lemma Φ_sq_inversion {Q : ℝ} (hQ : 1 < Q) (ℓ : ℝ) :
    ∫ r, P.Φ Q r ^ 2 * Complex.exp (-(Complex.I * r * ℓ)) = 2 * Real.pi * P.g Q ℓ := by
  have hinv := congrFun (Continuous.fourierInv_fourier_eq
    ((P.gC_contDiff hQ).continuous) ((P.g_integrable hQ).ofReal) (P.fourier_gC_integrable hQ)) ℓ
  rw [Real.fourierInv_eq'] at hinv
  set h : ℝ → ℂ := fun r => P.Φ Q r ^ 2 * Complex.exp (-(Complex.I * r * ℓ)) with hh
  have hsub := Measure.integral_comp_mul_left h (-(2 * Real.pi))
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [inv_neg, abs_neg, abs_inv, abs_of_pos hpi] at hsub
  have hrhs : ∫ x, h (-(2 * Real.pi) * x) = ∫ v, Complex.exp (↑(2 * Real.pi * inner ℝ v ℓ) * Complex.I) •
      𝓕 (P.gC Q) v := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [hh, smul_eq_mul]
    rw [P.Φ_sq_eq_fourier hQ]
    have : -(-(2 * Real.pi) * v / (2 * Real.pi)) = v := by field_simp
    rw [this, mul_comm]
    congr 2
    rw [RCLike.inner_apply, conj_trivial]
    push_cast; ring
  rw [hrhs, hinv] at hsub
  have : ∫ r, h r = 2 * Real.pi * (P.gC Q ℓ) := by
    have h2 : (2 * Real.pi)⁻¹ • ∫ r, h r = P.gC Q ℓ := hsub.symm
    rw [← h2, Complex.real_smul]
    push_cast
    field_simp
  simpa [gC] using this


/-- `∫_J ∫_J F(t − t') dt' dt = ∫ F(r) (|J| − |r|)_+ dr` for `J = [a,b]`. -/
lemma double_integral_Icc (F : ℝ → ℂ) (hF : Integrable F) (hFc : Continuous F) (a b : ℝ) :
    ∫ t in Set.Icc a b, ∫ t' in Set.Icc a b, F (t - t') =
      ∫ r, F r * ((max (b - a - |r|) 0 : ℝ) : ℂ) := by
  set S := Set.Icc a b with hS
  set ind : ℝ → ℂ := S.indicator (fun _ => (1 : ℂ)) with hind
  have hind_meas : Measurable ind := measurable_const.indicator measurableSet_Icc
  -- step i
  have h1 : ∀ t, ∫ t' in S, F (t - t') = ∫ r, ind (t - r) * F r := by
    intro t
    rw [← integral_indicator measurableSet_Icc]
    rw [← integral_sub_left_eq_self (S.indicator (fun t' => F (t - t'))) (μ := volume) t]
    refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    simp only [hind, Set.indicator]
    split_ifs <;> simp
  -- step ii
  have hint : Integrable (Function.uncurry fun t r => ind (t - r) * F r)
      ((volume.restrict S).prod volume) := by
    have : IsFiniteMeasure (volume.restrict S) := ⟨by
      rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
    have hbound : Integrable (fun p : ℝ × ℝ => (1 : ℝ) * ‖F p.2‖) ((volume.restrict S).prod volume) :=
      (integrable_const (1 : ℝ)).mul_prod hF.norm
    refine hbound.mono' ?_ (Filter.Eventually.of_forall ?_)
    · exact ((hind_meas.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable).mul
        (hFc.comp continuous_snd).aestronglyMeasurable
    · rintro ⟨t, r⟩
      simp only [Function.uncurry_apply_pair, norm_mul, one_mul]
      refine mul_le_of_le_one_left (norm_nonneg _) ?_
      simp only [hind, Set.indicator]; split_ifs <;> simp
  rw [integral_congr_ae (Filter.Eventually.of_forall h1), integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  simp only
  rw [integral_mul_const, mul_comm]
  congr 1
  -- step iii
  have h3 : ∀ t, ind (t - r) = (Set.Icc (a + r) (b + r)).indicator (fun _ => (1 : ℂ)) t := by
    intro t
    simp only [hind, hS, Set.indicator, Set.mem_Icc]
    congr 1
    apply propext; constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  simp_rw [h3]
  rw [setIntegral_indicator measurableSet_Icc, setIntegral_const, hS, Set.Icc_inter_Icc,
    Real.volume_real_Icc, Complex.real_smul, mul_one]
  congr 2
  rcases le_total 0 r with hr | hr
  · rw [abs_of_nonneg hr, max_eq_right (by linarith), min_eq_left (by linarith)]; ring
  · rw [abs_of_nonpos hr, max_eq_left (by linarith), min_eq_right (by linarith)]; ring

/-- `𝒦(n,n) = ∫ Φ(r)² n^{−ir} (|J| − |r|)_+ dr`. -/
lemma 𝒦_diag_eq {Q : ℝ} (hQ : 1 < Q) (T : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    P.𝒦 Q T n n = ∫ r, (P.Φ Q r ^ 2 * Complex.exp (-(Complex.I * r * Real.log n))) *
      ((max ((2 - P.θ) * T - (1 + P.θ) * T - |r|) 0 : ℝ) : ℂ) := by
  set F : ℝ → ℂ := fun r => P.Φ Q r ^ 2 * Complex.exp (-(Complex.I * r * Real.log n)) with hFdef
  have hFc : Continuous F := (P.Φ_sq_continuous hQ).mul (by fun_prop)
  have hFi : Integrable F := by
    refine (P.Φ_sq_integrable hQ).mul_bdd (c := 1) (by fun_prop) (Filter.Eventually.of_forall
      fun r => ?_)
    rw [Complex.norm_exp]; simp
    rw [← Complex.natCast_log, Complex.ofReal_im, mul_zero]
  rw [← double_integral_Icc F hFi hFc]
  unfold 𝒦 J
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun t' => ?_)
  simp only [hFdef]
  rw [natCast_cpow n hn, natCast_cpow n hn, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast; ring


/-- `v = ψ²` as a complex function. -/
def vC : ℝ → ℂ := fun s => ((P.ψ s ^ 2 : ℝ) : ℂ)

/-- `V(x) = ∫ ψ(s)² e^{ixs} ds` (so `Φ_Q(r) = L·V(Lr)`). -/
def Vhat (x : ℝ) : ℂ := ∫ s, P.vC s * Complex.exp (Complex.I * x * s)

lemma vC_hasCompactSupport : HasCompactSupport P.vC := by
  obtain ⟨r, -, hr⟩ := P.ψ_supp
  refine HasCompactSupport.intro (K := Set.Icc (-|r|) (|r|)) isCompact_Icc ?_
  intro x hx
  have hx' : r < |x| := by
    by_contra hcon
    exact hx (Set.mem_Icc.mpr (abs_le.mp ((not_lt.mp hcon).trans (le_abs_self r))))
  simp [vC, hr x hx']

lemma vC_contDiff : ContDiff ℝ ∞ P.vC :=
  Complex.ofRealCLM.contDiff.comp (P.ψ_smooth.pow 2)

lemma vC_integrable : Integrable P.vC :=
  P.vC_contDiff.continuous.integrable_of_hasCompactSupport P.vC_hasCompactSupport

lemma Vhat_eq_fourier (x : ℝ) : P.Vhat x = 𝓕 P.vC (-(x / (2 * Real.pi))) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 2
  push_cast
  field_simp

lemma Vhat_continuous : Continuous P.Vhat := by
  set VS := P.vC_hasCompactSupport.toSchwartzMap P.vC_contDiff
  have h1 : (VS : ℝ → ℂ) = P.vC := rfl
  have h2 := (𝓕 VS).continuous
  rw [SchwartzMap.fourier_coe, h1] at h2
  have : P.Vhat = fun x => 𝓕 P.vC (-(x / (2 * Real.pi))) := funext P.Vhat_eq_fourier
  rw [this]; exact h2.comp (by fun_prop)

lemma Vhat_norm_le (x : ℝ) : ‖P.Vhat x‖ ≤ ∫ s, ‖P.vC s‖ := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only [norm_mul]
  rw [Complex.norm_exp]; simp

/-- `h(x) = |x| ‖V(x)‖²`. -/
def hV (x : ℝ) : ℝ := |x| * ‖P.Vhat x‖ ^ 2

lemma hV_integrable : Integrable P.hV := by
  set VS := P.vC_hasCompactSupport.toSchwartzMap P.vC_contDiff
  have h1 : (VS : ℝ → ℂ) = P.vC := rfl
  have h2 := (𝓕 VS).integrable_pow_mul volume 1
  rw [SchwartzMap.fourier_coe, h1] at h2
  have hR : -(1 / (2 * Real.pi)) ≠ 0 := by simp [Real.pi_ne_zero]
  have h3 := (h2.comp_mul_left' hR).const_mul (2 * Real.pi)
  have h4 : Integrable (fun x => |x| * ‖P.Vhat x‖) := by
    refine h3.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [pow_one, Real.norm_eq_abs]
    rw [P.Vhat_eq_fourier, show -(x / (2 * Real.pi)) = -(1 / (2 * Real.pi)) * x by ring,
      abs_mul, abs_neg, abs_div, abs_one, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    field_simp
  refine (h4.mul_bdd (c := ∫ s, ‖P.vC s‖) (P.Vhat_continuous.norm).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)).congr (Filter.Eventually.of_forall fun x => ?_)
  · rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; exact P.Vhat_norm_le x
  · simp only [hV]; ring

lemma Φ_eq_Vhat {Q : ℝ} (hQ : 1 < Q) (r : ℝ) : P.Φ Q r = P.L Q * P.Vhat (P.L Q * r) := by
  have hL := P.L_pos hQ
  set k : ℝ → ℂ := fun s => P.vC s * Complex.exp (Complex.I * ↑(P.L Q * r) * s) with hk
  have := Measure.integral_comp_div k (P.L Q)
  rw [abs_of_pos hL, Complex.real_smul] at this
  unfold Φ Vhat
  rw [← this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have hL' : (P.L Q : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  simp only [hk, vC, ψL]
  push_cast
  congr 2
  field_simp

lemma integral_r_Φ_sq {Q : ℝ} (hQ : 1 < Q) :
    Integrable (fun r => |r| * ‖P.Φ Q r ^ 2‖) ∧ ∫ r, |r| * ‖P.Φ Q r ^ 2‖ = ∫ x, P.hV x := by
  have hL := P.L_pos hQ
  have heq : (fun r => |r| * ‖P.Φ Q r ^ 2‖) = fun r => P.L Q * P.hV (P.L Q * r) := by
    funext r
    rw [P.Φ_eq_Vhat hQ, norm_pow, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hL]
    simp only [hV, abs_mul, abs_of_pos hL]; ring
  rw [heq]
  refine ⟨(P.hV_integrable.comp_mul_left' hL.ne').const_mul _, ?_⟩
  rw [integral_const_mul, Measure.integral_comp_mul_left, abs_inv, abs_of_pos hL, smul_eq_mul]
  field_simp

end PrimeSetup

open PrimeSetup in
/-- **`lem:M1`, diagonal** (proved). `𝒦(n,n) = 2π|J| g(log n) + O_v(1)`, with the explicit
constant `C = ∫ |x| |V(x)|² dx`, `V(x) = ∫ ψ(s)² e^{ixs} ds`, independent of `Q, T, n`. -/
theorem lemM1_diag_proved : lemM1_diag_Statement := by
  intro P
  refine ⟨∫ x, P.hV x, fun Q T hQ hT n hn => ?_⟩
  set a := (1 + P.θ) * T
  set b := (2 - P.θ) * T
  have hJl : P.Jlen T = b - a := by simp only [Jlen, a, b]; ring
  have hJpos : 0 ≤ b - a := by
    have := P.θ_lt; simp only [a, b]; nlinarith
  set F : ℝ → ℂ := fun r => P.Φ Q r ^ 2 * Complex.exp (-(Complex.I * r * Real.log n)) with hFdef
  have hFi : Integrable F := by
    refine (P.Φ_sq_integrable hQ).mul_bdd (c := 1) (by fun_prop) (Filter.Eventually.of_forall
      fun r => ?_)
    rw [Complex.norm_exp]; simp
    rw [← Complex.natCast_log, Complex.ofReal_im, mul_zero]
  have hFn : ∀ r, ‖F r‖ = ‖P.Φ Q r ^ 2‖ := by
    intro r; simp only [hFdef, norm_mul]
    rw [Complex.norm_exp]; simp
    rw [← Complex.natCast_log, Complex.ofReal_im, mul_zero, Real.exp_zero, mul_one]
  have hm_int : Integrable (fun r => F r * ((max (b - a - |r|) 0 : ℝ) : ℂ)) := by
    refine hFi.mul_bdd (c := b - a) (by fun_prop) (Filter.Eventually.of_forall fun r => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith [abs_nonneg r]) hJpos
  have hK := P.𝒦_diag_eq hQ T n hn
  have hinv := P.Φ_sq_inversion hQ (Real.log n)
  have hdiff : P.𝒦 Q T n n - 2 * (Real.pi : ℂ) * (P.Jlen T : ℂ) * (P.g Q (Real.log n) : ℂ)
      = ∫ r, F r * (((max (b - a - |r|) 0 : ℝ) : ℂ) - ((b - a : ℝ) : ℂ)) := by
    rw [hK]
    have h2 : 2 * (Real.pi : ℂ) * (P.Jlen T : ℂ) * (P.g Q (Real.log n) : ℂ)
        = ∫ r, F r * ((b - a : ℝ) : ℂ) := by
      rw [integral_mul_const, hinv, hJl]; push_cast; ring
    rw [h2, ← integral_sub hm_int (hFi.mul_const _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    simp only [hFdef]; ring
  rw [hdiff]
  obtain ⟨hint, hval⟩ := P.integral_r_Φ_sq hQ
  rw [← hval]
  refine norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall fun r => ?_)
  rw [norm_mul, hFn, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rcases le_total (b - a - |r|) 0 with h | h
  · rw [max_eq_right h, zero_sub, abs_neg, abs_of_nonneg hJpos]; linarith
  · rw [max_eq_left h, show b - a - |r| - (b - a) = -|r| by ring, abs_neg, abs_abs]

end Families

namespace Families

/-- Alias under the name used in `STATEMENTS.md`. -/
theorem lemM1_diag : lemM1_diag_Statement := lemM1_diag_proved

end Families
