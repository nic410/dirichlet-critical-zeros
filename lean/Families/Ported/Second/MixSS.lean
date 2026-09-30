/-
# Prime side (paper §5): the mixed and the same-sign terms

* `Mmix_small` (`lem:muLambda`): `M_{μΛ} = o(H T L² ℓ)`.
* `SSC_small` (`lem:ss`): `∑_χ ω_χ ∬_{J²} Φ(t−t')² S_χ(t) S_χ(t') = o(H T L² ℓ)`.

Route.
* `MixSS.cov`: `∬_{[a,b]²} F(t−t') G(t,t') = ∫_r F(r) ∫_{[a,b]∩[a+r,b+r]} G(t,t−r) dt dr`.
* Mixed term, `μ_χ = β_q + r_χ` (`β_q = (1/2π)(log(q/π) + log T)`, `|r_χ| ≤ R₀` on `J`):
  the `r`-part is `≤ R₀ · sup_{t'} ∑_χ ω_χ|P_χ(t')| · ∬Φ²` (`MA_bound`; the sup via AM–GM and the
  large sieve, `sum_absP_le`); the `β`-part is `−(1/π) Re ∑_χ ω_χ β_q ∑_n a_n X(n) χ(n)`
  (`MB_eq`), `|X(n)| ≤ 2 ∫Φ² / log n` (`X_bound`, via `cov`), and `bilinLS` (`MB_small`).
* Same-sign term: `SSC = ∫_r Φ(r)² ∫_{J_r} ∑_χ ω_χ S_χ(t) S_χ(t−r) dt dr` (`SSC_eq`, `cov`); the inner
  integral is `i (E(β) − E(α))` with `E = ∑_χ ω_χ ∑_{n,m} x_n χ(n) y_m χ(m) / log(nm)` (`SS_key`), and
  `1/log(nm) = ∫_0^∞ (nm)^{−σ} dσ` plus the large sieve bound `|E| ≤ w_max C₀ (Q²+Y) ∑ a_n²/(2 log n)`
  (`laplace_LS`); hence `‖SSC‖ ≪ Q² L³` (`SSC_bound`).
-/
import Families.Ported.Second.Common

noncomputable section

set_option linter.unusedSectionVars false

open scoped BigOperators ComplexConjugate ContDiff
open ArithmeticFunction Finset MeasureTheory Filter Topology

namespace Families.Ported.Second

open Families

/-! Auxiliary lemmas live in the sub-namespace `MixSS` (to avoid name clashes). -/
namespace MixSS

/-! ### Double integrals over a square -/

section Double

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma D_cont (a b : ℝ) {f : ℝ → ℝ → E} (hf : Continuous (Function.uncurry f)) :
    Continuous (fun t => ∫ t' in Set.Icc a b, f t t') :=
  continuous_parametric_integral_of_continuous hf isCompact_Icc

lemma inner_integrableOn (a b t : ℝ) {f : ℝ → ℝ → E} (hf : Continuous (Function.uncurry f)) :
    IntegrableOn (fun t' => f t t') (Set.Icc a b) :=
  (hf.comp (Continuous.prodMk_right t)).integrableOn_Icc

lemma D_sum (a b : ℝ) {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ → E)
    (hf : ∀ i ∈ s, Continuous (Function.uncurry (f i))) :
    ∫ t in Set.Icc a b, ∫ t' in Set.Icc a b, ∑ i ∈ s, f i t t' =
      ∑ i ∈ s, ∫ t in Set.Icc a b, ∫ t' in Set.Icc a b, f i t t' := by
  have h1 : ∀ t, ∫ t' in Set.Icc a b, ∑ i ∈ s, f i t t' =
      ∑ i ∈ s, ∫ t' in Set.Icc a b, f i t t' := fun t =>
    integral_finsetSum s (fun i hi => inner_integrableOn a b t (hf i hi))
  simp_rw [h1]
  exact integral_finsetSum s (fun i hi => (D_cont a b (hf i hi)).integrableOn_Icc)

lemma D_add (a b : ℝ) (f g : ℝ → ℝ → E)
    (hf : Continuous (Function.uncurry f)) (hg : Continuous (Function.uncurry g)) :
    ∫ t in Set.Icc a b, ∫ t' in Set.Icc a b, (f t t' + g t t') =
      (∫ t in Set.Icc a b, ∫ t' in Set.Icc a b, f t t') +
        ∫ t in Set.Icc a b, ∫ t' in Set.Icc a b, g t t' := by
  have h1 : ∀ t, ∫ t' in Set.Icc a b, (f t t' + g t t') =
      (∫ t' in Set.Icc a b, f t t') + ∫ t' in Set.Icc a b, g t t' := fun t =>
    integral_add (inner_integrableOn a b t hf) (inner_integrableOn a b t hg)
  simp_rw [h1]
  exact integral_add (D_cont a b hf).integrableOn_Icc (D_cont a b hg).integrableOn_Icc

lemma D_mono (a b : ℝ) (f g : ℝ → ℝ → ℝ)
    (hf : Continuous (Function.uncurry f)) (hg : Continuous (Function.uncurry g))
    (h : ∀ t ∈ Set.Icc a b, ∀ t' ∈ Set.Icc a b, f t t' ≤ g t t') :
    ∫ t in Set.Icc a b, ∫ t' in Set.Icc a b, f t t' ≤
      ∫ t in Set.Icc a b, ∫ t' in Set.Icc a b, g t t' := by
  refine setIntegral_mono_on (D_cont a b hf).integrableOn_Icc (D_cont a b hg).integrableOn_Icc
    measurableSet_Icc fun t ht => ?_
  exact setIntegral_mono_on (inner_integrableOn a b t hf) (inner_integrableOn a b t hg)
    measurableSet_Icc fun t' ht' => h t ht t' ht'

lemma D_norm_le (a b : ℝ) (f : ℝ → ℝ → E) (g : ℝ → ℝ → ℝ)
    (hg : Continuous (Function.uncurry g))
    (h : ∀ t ∈ Set.Icc a b, ∀ t' ∈ Set.Icc a b, ‖f t t'‖ ≤ g t t') :
    ‖∫ t in Set.Icc a b, ∫ t' in Set.Icc a b, f t t'‖ ≤
      ∫ t in Set.Icc a b, ∫ t' in Set.Icc a b, g t t' := by
  refine norm_integral_le_of_norm_le (D_cont a b hg).integrableOn_Icc
    (ae_restrict_of_forall_mem measurableSet_Icc fun t ht => ?_)
  exact norm_integral_le_of_norm_le (inner_integrableOn a b t hg)
    (ae_restrict_of_forall_mem measurableSet_Icc fun t' ht' => h t ht t' ht')

lemma D_re (a b : ℝ) (f : ℝ → ℝ → ℂ) (hf : Continuous (Function.uncurry f)) :
    ∫ t in Set.Icc a b, ∫ t' in Set.Icc a b, (f t t').re =
      (∫ t in Set.Icc a b, ∫ t' in Set.Icc a b, f t t').re := by
  have h1 : ∀ t, ∫ t' in Set.Icc a b, (f t t').re = (∫ t' in Set.Icc a b, f t t').re := fun t =>
    integral_re (inner_integrableOn a b t hf)
  simp_rw [h1]
  exact integral_re (D_cont a b hf).integrableOn_Icc

/-- Change of variables `t' = t − r` on the square `[a,b]²`. -/
lemma cov (F : ℝ → ℝ) (hF : Integrable F) (hFc : Continuous F) (G : ℝ → ℝ → ℂ)
    (hG : Continuous (Function.uncurry G)) (M : ℝ) (hM : ∀ t t', ‖G t t'‖ ≤ M) (a b : ℝ) :
    ∫ t in Set.Icc a b, ∫ t' in Set.Icc a b, (F (t - t') : ℂ) * G t t' =
      ∫ r, (F r : ℂ) * ∫ t in Set.Icc (max a (a + r)) (min b (b + r)), G t (t - r) := by
  set S := Set.Icc a b with hS
  set ind : ℝ → ℂ := S.indicator (fun _ => (1 : ℂ)) with hind
  have hind_meas : Measurable ind := measurable_const.indicator measurableSet_Icc
  have h1 : ∀ t, ∫ t' in S, (F (t - t') : ℂ) * G t t' =
      ∫ r, ind (t - r) * ((F r : ℂ) * G t (t - r)) := by
    intro t
    rw [← integral_indicator measurableSet_Icc]
    rw [← integral_sub_left_eq_self (S.indicator (fun t' => (F (t - t') : ℂ) * G t t'))
      (μ := volume) t]
    refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    simp only [hind, Set.indicator]
    split_ifs <;> simp
  have hint : Integrable (Function.uncurry fun t r => ind (t - r) * ((F r : ℂ) * G t (t - r)))
      ((volume.restrict S).prod volume) := by
    have : IsFiniteMeasure (volume.restrict S) := ⟨by
      rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
    have hbound : Integrable (fun p : ℝ × ℝ => M * ‖F p.2‖) ((volume.restrict S).prod volume) :=
      (integrable_const M).mul_prod hF.norm
    refine hbound.mono' ?_ (Filter.Eventually.of_forall ?_)
    · refine ((hind_meas.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable).mul ?_
      refine Continuous.aestronglyMeasurable ?_
      have hG' : Continuous (fun p : ℝ × ℝ => G p.1 (p.1 - p.2)) :=
        hG.comp (continuous_fst.prodMk (continuous_fst.sub continuous_snd))
      exact ((Complex.continuous_ofReal.comp hFc).comp continuous_snd).mul hG'
    · rintro ⟨t, r⟩
      simp only [Function.uncurry_apply_pair, norm_mul, Complex.norm_real]
      have hi : ‖ind (t - r)‖ ≤ 1 := by
        simp only [hind, Set.indicator]; split_ifs <;> simp
      have hG1 := hM t (t - r)
      calc ‖ind (t - r)‖ * (‖F r‖ * ‖G t (t - r)‖) ≤ 1 * (‖F r‖ * M) := by
            gcongr
        _ = M * ‖F r‖ := by ring
  rw [integral_congr_ae (Filter.Eventually.of_forall h1), integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  simp only
  have h2 : ∀ t, ind (t - r) * ((F r : ℂ) * G t (t - r)) =
      (F r : ℂ) * (Set.Icc (a + r) (b + r)).indicator (fun t => G t (t - r)) t := by
    intro t
    simp only [hind, hS, Set.indicator, Set.mem_Icc]
    have : (a ≤ t - r ∧ t - r ≤ b) ↔ (a + r ≤ t ∧ t ≤ b + r) := by
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    by_cases h : a + r ≤ t ∧ t ≤ b + r
    · rw [if_pos (this.mpr h), if_pos h]; ring
    · rw [if_neg (fun h' => h (this.mp h')), if_neg h]; ring
  simp_rw [h2]
  rw [integral_const_mul, setIntegral_indicator measurableSet_Icc, hS, Set.Icc_inter_Icc]

lemma D_congr (a b : ℝ) (f g : ℝ → ℝ → E) (h : ∀ t t', f t t' = g t t') :
    ∫ t in Set.Icc a b, ∫ t' in Set.Icc a b, f t t' =
      ∫ t in Set.Icc a b, ∫ t' in Set.Icc a b, g t t' := by
  have : f = g := funext fun t => funext fun t' => h t t'
  rw [this]

lemma D_famsum {𝕜 : Type*} [RCLike 𝕜] (a b : ℝ) (s : Finset ℕ) (c : ℕ → 𝕜)
    (f : (q : ℕ) → DirichletCharacter ℂ q → ℝ → ℝ → 𝕜)
    (hf : ∀ q (χ : DirichletCharacter ℂ q), Continuous (Function.uncurry (f q χ))) :
    ∫ t in Set.Icc a b, ∫ t' in Set.Icc a b, ∑ q ∈ s, c q * ∑ χ ∈ primChars q, f q χ t t' =
      ∑ q ∈ s, c q * ∑ χ ∈ primChars q, ∫ t in Set.Icc a b, ∫ t' in Set.Icc a b, f q χ t t' := by
  rw [D_sum a b s (fun q t t' => c q * ∑ χ ∈ primChars q, f q χ t t') fun q _ =>
    continuous_const.mul (continuous_finsetSum _ fun χ _ => hf q χ)]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp_rw [integral_const_mul]
  rw [D_sum a b (primChars q) (f q) fun χ _ => hf q χ]

end Double

/-! ### Oscillatory integrals -/

section Osc

lemma integral_Icc_exp (c : ℝ) (hc : c ≠ 0) (d : ℂ) {α β : ℝ} (h : α ≤ β) :
    ∫ t in Set.Icc α β, Complex.exp (-(Complex.I * c * t) + d) =
      Complex.I / c * (Complex.exp (-(Complex.I * c * β) + d) -
        Complex.exp (-(Complex.I * c * α) + d)) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h]
  have hc' : (-(Complex.I * c)) ≠ 0 := by
    simp [Complex.I_ne_zero, hc]
  have e1 : ∀ t : ℝ, Complex.exp (-(Complex.I * c * t) + d) =
      Complex.exp (-(Complex.I * c) * t) * Complex.exp d := by
    intro t; rw [← Complex.exp_add]; ring_nf
  simp_rw [e1]
  rw [intervalIntegral.integral_mul_const, integral_exp_mul_complex hc']
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

lemma norm_integral_Icc_exp_le (c : ℝ) (hc : 0 < c) (d : ℝ) (α β : ℝ) :
    ‖∫ t in Set.Icc α β, Complex.exp (-(Complex.I * c * t) + Complex.I * d)‖ ≤ 2 / c := by
  rcases le_or_gt α β with h | h
  · rw [integral_Icc_exp c hc.ne' _ h]
    have hn : ∀ x : ℝ, ‖Complex.exp (-(Complex.I * c * x) + Complex.I * d)‖ = 1 := by
      intro x
      rw [Complex.norm_exp]
      simp
    rw [norm_mul, norm_div, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    calc 1 / c * ‖Complex.exp (-(Complex.I * c * β) + Complex.I * d) -
          Complex.exp (-(Complex.I * c * α) + Complex.I * d)‖
        ≤ 1 / c * (1 + 1) := by
          gcongr
          exact (norm_sub_le _ _).trans (by rw [hn, hn])
      _ = 2 / c := by ring
  · rw [Set.Icc_eq_empty (not_le.mpr h), Measure.restrict_empty, integral_zero_measure, norm_zero]
    positivity

lemma cpow_eq_exp (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    (n : ℂ) ^ (-(Complex.I * t)) = Complex.exp (-(Complex.I * Real.log n * t)) := by
  rw [PrimeSetup.natCast_cpow n hn]; congr 1; ring

lemma norm_cpow_eq_one (n : ℕ) (hn : 1 ≤ n) (t : ℝ) : ‖(n : ℂ) ^ (-(Complex.I * t))‖ = 1 := by
  rw [cpow_eq_exp n hn, Complex.norm_exp]
  have : (-(Complex.I * (Real.log n : ℂ) * (t : ℂ))).re = 0 := by
    rw [mul_assoc, ← Complex.ofReal_mul, Complex.neg_re, Complex.I_mul_re, Complex.ofReal_im,
      neg_neg]
  rw [this, Real.exp_zero]

lemma continuous_cpow (n : ℕ) (hn : 1 ≤ n) :
    Continuous (fun t : ℝ => (n : ℂ) ^ (-(Complex.I * t))) := by
  simp_rw [cpow_eq_exp n hn]
  fun_prop

/-- `|∬_{[a,b]²} F(t−t') n^{−it'}| ≤ 2 (∫ F) / log n` for `F ≥ 0`, `n ≥ 2`. -/
lemma X_bound (F : ℝ → ℝ) (hF : Integrable F) (hFc : Continuous F) (hF0 : ∀ r, 0 ≤ F r)
    (a b : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    ‖∫ t in Set.Icc a b, ∫ t' in Set.Icc a b, (F (t - t') : ℂ) * (n : ℂ) ^ (-(Complex.I * t'))‖
      ≤ 2 * (∫ r, F r) / Real.log n := by
  have hn1 : 1 ≤ n := by omega
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
  rw [cov F hF hFc (fun _ t' => (n : ℂ) ^ (-(Complex.I * t')))
    ((continuous_cpow n hn1).comp continuous_snd) 1
    (fun _ t' => (norm_cpow_eq_one n hn1 t').le) a b]
  refine (norm_integral_le_of_norm_le (hF.mul_const (2 / Real.log n))
    (Filter.Eventually.of_forall fun r => ?_)).trans (le_of_eq ?_)
  · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hF0 r)]
    refine mul_le_mul_of_nonneg_left ?_ (hF0 r)
    have e : ∀ t : ℝ, (n : ℂ) ^ (-(Complex.I * ((t - r : ℝ) : ℂ))) =
        Complex.exp (-(Complex.I * Real.log n * t) + Complex.I * (r * Real.log n : ℝ)) := by
      intro t; rw [cpow_eq_exp n hn1]; congr 1; push_cast; ring
    simp_rw [e]
    exact norm_integral_Icc_exp_le _ hlog _ _ _
  · rw [integral_mul_const]; ring

end Osc

/-! ### Linearity helpers for family sums -/

section Lin

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma integral_sum_sum (N M : Finset ℕ) (f : ℕ → ℕ → α → ℂ)
    (hf : ∀ n ∈ N, ∀ m ∈ M, Integrable (f n m) μ) :
    ∫ x, ∑ n ∈ N, ∑ m ∈ M, f n m x ∂μ = ∑ n ∈ N, ∑ m ∈ M, ∫ x, f n m x ∂μ := by
  rw [integral_finsetSum _ (fun n hn => integrable_finsetSum _ (fun m hm => hf n hn m hm))]
  exact Finset.sum_congr rfl (fun n hn => integral_finsetSum _ (fun m hm => hf n hn m hm))

lemma integrable_famsum (s : Finset ℕ) (c : ℕ → ℂ)
    (g : (q : ℕ) → DirichletCharacter ℂ q → α → ℂ)
    (hg : ∀ q ∈ s, ∀ χ ∈ primChars q, Integrable (g q χ) μ) :
    Integrable (fun x => ∑ q ∈ s, c q * ∑ χ ∈ primChars q, g q χ x) μ :=
  integrable_finsetSum _ fun q hq => (integrable_finsetSum _ fun χ hχ => hg q hq χ hχ).const_mul _

lemma integral_famsum (s : Finset ℕ) (c : ℕ → ℂ)
    (g : (q : ℕ) → DirichletCharacter ℂ q → α → ℂ)
    (hg : ∀ q ∈ s, ∀ χ ∈ primChars q, Integrable (g q χ) μ) :
    ∫ x, ∑ q ∈ s, c q * ∑ χ ∈ primChars q, g q χ x ∂μ =
      ∑ q ∈ s, c q * ∑ χ ∈ primChars q, ∫ x, g q χ x ∂μ := by
  rw [integral_finsetSum _ fun q hq =>
    (integrable_finsetSum _ fun χ hχ => hg q hq χ hχ).const_mul _]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [integral_const_mul, integral_finsetSum _ fun χ hχ => hg q hq χ hχ]

end Lin

/-! ### The Laplace transform and the large sieve -/

section Laplace

lemma laplace_exp (c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun σ : ℝ => Real.exp (-c * σ)) (Set.Ioi 0) ∧
      ∫ σ in Set.Ioi 0, Real.exp (-c * σ) = 1 / c := by
  refine ⟨integrableOn_exp_mul_Ioi (by linarith) 0, ?_⟩
  rw [integral_exp_mul_Ioi (by linarith) 0]
  simp only [mul_zero, Real.exp_zero]
  field_simp

/-- `1/log(nm) = ∫_0^∞ (nm)^{-σ} dσ`, combined with the large sieve: for vectors `x, y` on `[1,Y]`
with `|x_n|, |y_n| ≤ u_n`, `u_1 = 0`,
`|∑_χ ω_χ ∑_{n,m} x_n χ(n) y_m χ(m) / log(nm)| ≤ w_max C₀ (Q²+Y) ∑_n u_n²/(2 log n)`. -/
lemma laplace_LS (hMV : MV_LargeSieve) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧
    ∀ (P : PrimeSetup) (W : Weight) (Q : ℝ), 1 ≤ Q → ∀ (x y : ℕ → ℂ) (u : ℕ → ℝ),
      (∀ n, ‖x n‖ ≤ u n) → (∀ n, ‖y n‖ ≤ u n) → u 1 = 0 →
      ‖∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (W.omega Q q : ℂ) * ∑ χ ∈ primChars q,
          ∑ n ∈ P.range Q, ∑ m ∈ P.range Q,
            x n * χ n * (y m * χ m) / ((Real.log n + Real.log m : ℝ) : ℂ)‖
        ≤ W.wmax * C₀ * (Q ^ 2 + P.Y Q) * ∑ n ∈ P.range Q, u n ^ 2 / (2 * Real.log n) := by
  obtain ⟨C₀, hC₀, hLS⟩ := famLS_omega hMV
  refine ⟨C₀, hC₀, fun P W Q hQ x y u hx hy hu1 => ?_⟩
  have hx1 : x 1 = 0 := norm_le_zero_iff.mp (hu1 ▸ hx 1)
  have hy1 : y 1 = 0 := norm_le_zero_iff.mp (hu1 ▸ hy 1)
  have hu0 : ∀ n, 0 ≤ u n := fun n => (norm_nonneg _).trans (hx n)
  have hrange : ∀ n ∈ P.range Q, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  set K : ℝ := W.wmax * C₀ * (Q ^ 2 + P.Y Q) with hK
  have hK0 : 0 ≤ K := by
    have := W.wmax_nonneg
    have := PrimeSetup.Y_nonneg P Q
    positivity
  -- the Laplace weights
  set e : ℕ → ℝ → ℝ := fun n σ => Real.exp (-(σ * Real.log n)) with he
  -- termwise Laplace identity
  set f : (q : ℕ) → DirichletCharacter ℂ q → ℕ → ℕ → ℝ → ℂ := fun q χ n m σ =>
    (x n * (e n σ : ℂ) * χ n) * (y m * (e m σ : ℂ) * χ m) with hf
  have hterm : ∀ q (χ : DirichletCharacter ℂ q), ∀ n ∈ P.range Q, ∀ m ∈ P.range Q,
      IntegrableOn (f q χ n m) (Set.Ioi 0) ∧
      ∫ σ in Set.Ioi 0, f q χ n m σ =
        x n * χ n * (y m * χ m) / ((Real.log n + Real.log m : ℝ) : ℂ) := by
    intro q χ n hn m hm
    have hn1 := hrange n hn
    have hm1 := hrange m hm
    by_cases hn2 : n = 1
    · subst hn2; simp [hf, hx1]
    by_cases hm2 : m = 1
    · subst hm2; simp [hf, hy1]
    have hc : 0 < Real.log n + Real.log m := by
      have h1 : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
      have h2 : 0 < Real.log m := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
      linarith
    obtain ⟨hi, hv⟩ := laplace_exp _ hc
    have hfe : f q χ n m = fun σ => (x n * χ n * (y m * χ m)) *
        ((Real.exp (-(Real.log n + Real.log m) * σ) : ℝ) : ℂ) := by
      funext σ
      simp only [hf, he]
      have : Real.exp (-(Real.log n + Real.log m) * σ) =
          Real.exp (-(σ * Real.log n)) * Real.exp (-(σ * Real.log m)) := by
        rw [← Real.exp_add]; ring_nf
      rw [this]; push_cast; ring
    rw [hfe]
    refine ⟨hi.ofReal.const_mul _, ?_⟩
    rw [integral_const_mul, integral_complex_ofReal, hv]
    push_cast
    field_simp
  -- swap
  have hswap : ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (W.omega Q q : ℂ) * ∑ χ ∈ primChars q,
        ∑ n ∈ P.range Q, ∑ m ∈ P.range Q,
          x n * χ n * (y m * χ m) / ((Real.log n + Real.log m : ℝ) : ℂ) =
      ∫ σ in Set.Ioi 0, ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (W.omega Q q : ℂ) * ∑ χ ∈ primChars q,
        ∑ n ∈ P.range Q, ∑ m ∈ P.range Q, f q χ n m σ := by
    rw [integral_famsum _ _ _ fun q _ χ _ =>
      integrable_finsetSum _ fun n hn => integrable_finsetSum _ fun m hm => (hterm q χ n hn m hm).1]
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [integral_sum_sum _ _ _ fun n hn m hm => (hterm q χ n hn m hm).1]
    exact Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun m hm =>
      (hterm q χ n hn m hm).2.symm
  rw [hswap]
  -- the pointwise bound
  set g : ℝ → ℝ := fun σ => K * ∑ n ∈ P.range Q, u n ^ 2 * Real.exp (-(2 * Real.log n) * σ)
    with hg
  have hgi : IntegrableOn g (Set.Ioi 0) := by
    refine (integrable_finsetSum _ fun n hn => ?_).const_mul K
    by_cases hn2 : n = 1
    · subst hn2; simp [hu1]
    have h1 : 0 < 2 * Real.log n :=
      mul_pos two_pos (Real.log_pos (by exact_mod_cast (by have := hrange n hn; omega : 1 < n)))
    exact (laplace_exp _ h1).1.const_mul _
  have hgv : ∫ σ in Set.Ioi 0, g σ = K * ∑ n ∈ P.range Q, u n ^ 2 / (2 * Real.log n) := by
    rw [integral_const_mul]
    congr 1
    rw [integral_finsetSum _ fun n hn => ?_]
    · refine Finset.sum_congr rfl fun n hn => ?_
      by_cases hn2 : n = 1
      · subst hn2; simp [hu1]
      have h1 : 0 < 2 * Real.log n :=
        mul_pos two_pos (Real.log_pos (by exact_mod_cast (by have := hrange n hn; omega : 1 < n)))
      rw [integral_const_mul, (laplace_exp _ h1).2]
      ring
    · by_cases hn2 : n = 1
      · subst hn2; simp [hu1]
      have h1 : 0 < 2 * Real.log n :=
        mul_pos two_pos (Real.log_pos (by exact_mod_cast (by have := hrange n hn; omega : 1 < n)))
      exact (laplace_exp _ h1).1.const_mul _
  rw [← hgv]
  refine norm_integral_le_of_norm_le hgi (Filter.Eventually.of_forall fun σ => ?_)
  -- for fixed σ: factor and apply the large sieve
  set A : (q : ℕ) → DirichletCharacter ℂ q → ℂ := fun q χ =>
    ∑ n ∈ P.range Q, (x n * (e n σ : ℂ)) * χ n with hA
  set B : (q : ℕ) → DirichletCharacter ℂ q → ℂ := fun q χ =>
    ∑ n ∈ P.range Q, (y n * (e n σ : ℂ)) * χ n with hB
  have hfac : ∀ q (χ : DirichletCharacter ℂ q),
      ∑ n ∈ P.range Q, ∑ m ∈ P.range Q, f q χ n m σ = A q χ * B q χ := by
    intro q χ
    simp only [hA, hB, hf, Finset.sum_mul_sum]
  simp_rw [hfac]
  have hω := W.omega_nonneg Q
  have hLA := hLS P W Q hQ (fun n => x n * (e n σ : ℂ))
  have hLB := hLS P W Q hQ (fun n => y n * (e n σ : ℂ))
  have hnx : ∑ n ∈ P.range Q, ‖x n * (e n σ : ℂ)‖ ^ 2 ≤
      ∑ n ∈ P.range Q, u n ^ 2 * Real.exp (-(2 * Real.log n) * σ) := by
    refine Finset.sum_le_sum fun n _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow]
    have : Real.exp (-(σ * Real.log n)) ^ 2 = Real.exp (-(2 * Real.log n) * σ) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [this]
    gcongr
    exact hx n
  have hny : ∑ n ∈ P.range Q, ‖y n * (e n σ : ℂ)‖ ^ 2 ≤
      ∑ n ∈ P.range Q, u n ^ 2 * Real.exp (-(2 * Real.log n) * σ) := by
    refine Finset.sum_le_sum fun n _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow]
    have : Real.exp (-(σ * Real.log n)) ^ 2 = Real.exp (-(2 * Real.log n) * σ) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [this]
    gcongr
    exact hy n
  set U := ∑ n ∈ P.range Q, u n ^ 2 * Real.exp (-(2 * Real.log n) * σ)
  have hAB : ‖∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (W.omega Q q : ℂ) * ∑ χ ∈ primChars q, A q χ * B q χ‖ ≤
      ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ χ ∈ primChars q,
        (‖A q χ‖ ^ 2 + ‖B q χ‖ ^ 2) / 2 := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hω q)]
    refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => ?_))
      (hω q)
    rw [norm_mul]
    nlinarith [sq_nonneg (‖A q χ‖ - ‖B q χ‖)]
  refine hAB.trans ?_
  have hsplit : ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ χ ∈ primChars q,
        (‖A q χ‖ ^ 2 + ‖B q χ‖ ^ 2) / 2 =
      ((∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ χ ∈ primChars q, ‖A q χ‖ ^ 2) +
        ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ χ ∈ primChars q, ‖B q χ‖ ^ 2) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← mul_add, ← Finset.sum_add_distrib, mul_div_assoc, Finset.sum_div]
  rw [hsplit]
  simp only [hg]
  have h1 : ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ χ ∈ primChars q, ‖A q χ‖ ^ 2 ≤ K * U :=
    hLA.trans (mul_le_mul_of_nonneg_left hnx hK0)
  have h2 : ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ χ ∈ primChars q, ‖B q χ‖ ^ 2 ≤ K * U :=
    hLB.trans (mul_le_mul_of_nonneg_left hny hK0)
  linarith

end Laplace

/-! ### The same-sign term -/

section SS

lemma phase_prod (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (t r : ℝ) :
    (n : ℂ) ^ (-(Complex.I * t)) * (m : ℂ) ^ (-(Complex.I * ((t - r : ℝ) : ℂ))) =
      Complex.exp (-(Complex.I * ((Real.log n + Real.log m : ℝ) : ℂ) * t) +
        Complex.I * ((r * Real.log m : ℝ) : ℂ)) := by
  rw [cpow_eq_exp n hn, cpow_eq_exp m hm, ← Complex.exp_add]
  congr 1; push_cast; ring

lemma integral_phase (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (hnm : 2 ≤ n ∨ 2 ≤ m) (r : ℝ)
    {α β : ℝ} (h : α ≤ β) :
    ∫ t in Set.Icc α β, (n : ℂ) ^ (-(Complex.I * t)) *
        (m : ℂ) ^ (-(Complex.I * ((t - r : ℝ) : ℂ))) =
      Complex.I / ((Real.log n + Real.log m : ℝ) : ℂ) *
        ((n : ℂ) ^ (-(Complex.I * β)) * (m : ℂ) ^ (-(Complex.I * ((β - r : ℝ) : ℂ))) -
          (n : ℂ) ^ (-(Complex.I * α)) * (m : ℂ) ^ (-(Complex.I * ((α - r : ℝ) : ℂ)))) := by
  have hc : Real.log n + Real.log m ≠ 0 := by
    have h1 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    have h2 : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
    rcases hnm with h | h
    · have : 0 < Real.log n := Real.log_pos (by exact_mod_cast h)
      linarith
    · have : 0 < Real.log m := Real.log_pos (by exact_mod_cast h)
      linarith
  simp_rw [phase_prod n m hn hm]
  exact integral_Icc_exp _ hc _ h

variable (P : PrimeSetup)

/-- `G(t,t') = ∑_χ ω_χ S_χ(t) S_χ(t')`. -/
def Gss (W : Weight) (Q : ℝ) (t t' : ℝ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (W.omega Q q : ℂ) * ∑ χ ∈ primChars q,
    P.Schi χ Q (P.aVec Q) t * P.Schi χ Q (P.aVec Q) t'

lemma range_one_le {Q : ℝ} {n : ℕ} (hn : n ∈ P.range Q) : 1 ≤ n := (Finset.mem_Icc.mp hn).1

lemma Schi_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q) (Q t : ℝ) :
    ‖P.Schi χ Q (P.aVec Q) t‖ ≤ ∑ n ∈ P.range Q, P.aVec Q n := by
  unfold PrimeSetup.Schi
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (aVec_nonneg P Q n),
    norm_cpow_eq_one n (range_one_le P hn) t, mul_one]
  exact mul_le_of_le_one_right (aVec_nonneg P Q n) (DirichletCharacter.norm_le_one χ _)

lemma Gss_continuous (W : Weight) (Q : ℝ) : Continuous (Function.uncurry (Gss P W Q)) := by
  unfold Gss
  refine continuous_finsetSum _ fun q _ => continuous_const.mul
    (continuous_finsetSum _ fun χ _ => ?_)
  exact ((Schi_continuous P χ Q _).comp continuous_fst).mul
    ((Schi_continuous P χ Q _).comp continuous_snd)

lemma Gss_norm_le (W : Weight) (Q t t' : ℝ) :
    ‖Gss P W Q t t'‖ ≤ ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ _χ ∈ primChars q,
      (∑ n ∈ P.range Q, P.aVec Q n) ^ 2 := by
  unfold Gss
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (W.omega_nonneg Q q)]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => ?_))
    (W.omega_nonneg Q q)
  rw [norm_mul, sq]
  exact mul_le_mul (Schi_norm_le P χ Q t) (Schi_norm_le P χ Q t') (norm_nonneg _)
    (Finset.sum_nonneg fun n _ => aVec_nonneg P Q n)

lemma SS_key (hMV : MV_LargeSieve) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧
    ∀ (P : PrimeSetup) (W : Weight) (Q : ℝ), 1 ≤ Q → ∀ r α β : ℝ,
      ‖∫ t in Set.Icc α β, Gss P W Q t (t - r)‖ ≤
        2 * (W.wmax * C₀ * (Q ^ 2 + P.Y Q) *
          ∑ n ∈ P.range Q, P.aVec Q n ^ 2 / (2 * Real.log n)) := by
  obtain ⟨C₀, hC₀, hL⟩ := laplace_LS hMV
  refine ⟨C₀, hC₀, fun P W Q hQ r α β => ?_⟩
  set B := W.wmax * C₀ * (Q ^ 2 + P.Y Q) * ∑ n ∈ P.range Q, P.aVec Q n ^ 2 / (2 * Real.log n)
    with hBdef
  have hB0 : 0 ≤ B := by
    have := W.wmax_nonneg
    have := PrimeSetup.Y_nonneg P Q
    have : 0 ≤ ∑ n ∈ P.range Q, P.aVec Q n ^ 2 / (2 * Real.log n) :=
      Finset.sum_nonneg fun n hn => div_nonneg (sq_nonneg _)
        (mul_nonneg two_pos.le (Real.log_nonneg (by exact_mod_cast range_one_le P hn)))
    positivity
  rcases lt_or_ge β α with h | h
  · rw [Set.Icc_eq_empty (not_le.mpr h), Measure.restrict_empty, integral_zero_measure, norm_zero]
    positivity
  set a := P.aVec Q with ha
  set ph : ℕ → ℕ → ℝ → ℂ := fun n m t =>
    (n : ℂ) ^ (-(Complex.I * t)) * (m : ℂ) ^ (-(Complex.I * ((t - r : ℝ) : ℂ))) with hph
  have hexp : ∀ t, Gss P W Q t (t - r) = ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (W.omega Q q : ℂ) *
      ∑ χ ∈ primChars q, ∑ n ∈ P.range Q, ∑ m ∈ P.range Q,
        ((a n : ℂ) * χ n * ((a m : ℂ) * χ m)) * ph n m t := by
    intro t
    unfold Gss PrimeSetup.Schi
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    simp only [hph]; ring
  simp_rw [hexp]
  have hph_cont : ∀ n ∈ P.range Q, ∀ m ∈ P.range Q, Continuous (ph n m) := by
    intro n hn m hm
    have h2 : Continuous (fun t : ℝ => (m : ℂ) ^ (-(Complex.I * ((t - r : ℝ) : ℂ)))) :=
      (continuous_cpow m (range_one_le P hm)).comp (continuous_id.sub continuous_const)
    exact (continuous_cpow n (range_one_le P hn)).mul h2
  rw [integral_famsum (μ := volume.restrict (Set.Icc α β)) (Finset.Icc 1 ⌊Q⌋₊)
    (fun q => (W.omega Q q : ℂ))
    (fun q χ t => ∑ n ∈ P.range Q, ∑ m ∈ P.range Q, ((a n : ℂ) * χ n * ((a m : ℂ) * χ m)) * ph n m t)
    (fun q _ χ _ => integrable_finsetSum _ fun n hn => integrable_finsetSum _ fun m hm =>
      ((hph_cont n hn m hm).integrableOn_Icc).const_mul _)]
  have hint : ∀ q (χ : DirichletCharacter ℂ q),
      ∫ t in Set.Icc α β, ∑ n ∈ P.range Q, ∑ m ∈ P.range Q,
        ((a n : ℂ) * χ n * ((a m : ℂ) * χ m)) * ph n m t =
      ∑ n ∈ P.range Q, ∑ m ∈ P.range Q, ((a n : ℂ) * χ n * ((a m : ℂ) * χ m)) *
        (Complex.I / ((Real.log n + Real.log m : ℝ) : ℂ) * (ph n m β - ph n m α)) := by
    intro q χ
    rw [integral_sum_sum _ _ _ fun n hn m hm => ((hph_cont n hn m hm).integrableOn_Icc).const_mul _]
    refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun m hm => ?_
    rw [integral_const_mul]
    have hn1 := range_one_le P hn
    have hm1 := range_one_le P hm
    by_cases hn2 : n = 1
    · by_cases hm2 : m = 1
      · subst hn2; subst hm2; simp [ha, aVec_one]
      · congr 1
        exact integral_phase n m hn1 hm1 (Or.inr (by omega)) r h
    · congr 1
      exact integral_phase n m hn1 hm1 (Or.inl (by omega)) r h
  simp_rw [hint]
  set xγ : ℝ → ℕ → ℂ := fun γ n => (a n : ℂ) * (n : ℂ) ^ (-(Complex.I * γ)) with hxγ
  set yγ : ℝ → ℕ → ℂ := fun γ m => (a m : ℂ) * (m : ℂ) ^ (-(Complex.I * ((γ - r : ℝ) : ℂ)))
    with hyγ
  set Lf : ℝ → ℂ := fun γ => ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (W.omega Q q : ℂ) * ∑ χ ∈ primChars q,
    ∑ n ∈ P.range Q, ∑ m ∈ P.range Q,
      xγ γ n * χ n * (yγ γ m * χ m) / ((Real.log n + Real.log m : ℝ) : ℂ) with hLf
  have hform : ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (W.omega Q q : ℂ) * ∑ χ ∈ primChars q,
      ∑ n ∈ P.range Q, ∑ m ∈ P.range Q, ((a n : ℂ) * χ n * ((a m : ℂ) * χ m)) *
        (Complex.I / ((Real.log n + Real.log m : ℝ) : ℂ) * (ph n m β - ph n m α)) =
      Complex.I * (Lf β - Lf α) := by
    simp only [hLf, mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun χ _ =>
      Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    simp only [hxγ, hyγ, hph]
    ring
  rw [hform]
  have hnorm : ∀ γ : ℝ, ∀ n, ‖(a n : ℂ) * (n : ℂ) ^ (-(Complex.I * γ))‖ ≤ a n := by
    intro γ n
    by_cases hn : n = 0
    · subst hn; simp [ha, aVec_zero]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (aVec_nonneg P Q n),
      norm_cpow_eq_one n (by omega), mul_one]
  have hLb : ∀ γ, ‖Lf γ‖ ≤ B := fun γ =>
    hL P W Q hQ (xγ γ) (yγ γ) a (fun n => hnorm γ n) (fun n => hnorm (γ - r) n) (aVec_one P Q)
  calc ‖Complex.I * (Lf β - Lf α)‖ = ‖Lf β - Lf α‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    _ ≤ ‖Lf β‖ + ‖Lf α‖ := norm_sub_le _ _
    _ ≤ B + B := add_le_add (hLb β) (hLb α)
    _ = 2 * B := by ring

lemma SSC_eq (W : Weight) {Q : ℝ} (hQ : 1 < Q) (T : ℝ) :
    SSC P W Q T = ∫ t in P.J T, ∫ t' in P.J T, (PhiSq P Q (t - t') : ℂ) * Gss P W Q t t' := by
  have hpt : ∀ t t', (PhiSq P Q (t - t') : ℂ) * Gss P W Q t t' =
      ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (W.omega Q q : ℂ) * ∑ χ ∈ primChars q,
        (PhiSq P Q (t - t') : ℂ) * P.Schi χ Q (P.aVec Q) t * P.Schi χ Q (P.aVec Q) t' := by
    intro t t'
    unfold Gss
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun χ _ => ?_
    ring
  simp_rw [hpt]
  unfold SSC PrimeSetup.J
  rw [D_famsum]
  intro q χ
  have h1 : Continuous (fun p : ℝ × ℝ => (PhiSq P Q (p.1 - p.2) : ℂ)) :=
    Complex.continuous_ofReal.comp ((PhiSq_continuous P hQ).comp (continuous_fst.sub continuous_snd))
  exact (h1.mul ((Schi_continuous P χ Q _).comp continuous_fst)).mul
    ((Schi_continuous P χ Q _).comp continuous_snd)

/-- `‖SSC‖ ≤ 2 (∫Φ²) w_max C₀ (Q²+Y) ∑ a_n²/(2 log n)`. -/
lemma SSC_bound (hMV : MV_LargeSieve) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧
    ∀ (P : PrimeSetup) (W : Weight) (Q : ℝ), 1 < Q → ∀ T : ℝ,
      ‖SSC P W Q T‖ ≤ (∫ r, PhiSq P Q r) * (2 * (W.wmax * C₀ * (Q ^ 2 + P.Y Q) *
          ∑ n ∈ P.range Q, P.aVec Q n ^ 2 / (2 * Real.log n))) := by
  obtain ⟨C₀, hC₀, hK⟩ := SS_key hMV
  refine ⟨C₀, hC₀, fun P W Q hQ T => ?_⟩
  rw [SSC_eq P W hQ T]
  unfold PrimeSetup.J
  rw [cov (PhiSq P Q) (PhiSq_integrable P hQ) (PhiSq_continuous P hQ) (Gss P W Q)
    (Gss_continuous P W Q) _ (Gss_norm_le P W Q)]
  rw [← integral_mul_const]
  refine norm_integral_le_of_norm_le ((PhiSq_integrable P hQ).mul_const _)
    (Filter.Eventually.of_forall fun r => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (PhiSq_nonneg P Q r)]
  exact mul_le_mul_of_nonneg_left (hK P W Q hQ.le r _ _) (PhiSq_nonneg P Q r)

end SS

/-! ### Asymptotic bookkeeping -/

section Asymp

variable (P : PrimeSetup)

lemma ell_large (M : ℝ) : ∀ Q : ℝ, Real.exp M ≤ Q → M ≤ Real.log Q := by
  intro Q hQ
  have := Real.log_le_log (Real.exp_pos _) hQ
  rwa [Real.log_exp] at this

lemma T_large (M : ℝ) : ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ P.heights Q, M ≤ T := by
  set M' := max M 1 with hM'
  have hM'0 : 0 < M' := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨Real.exp (M' ^ P.a0⁻¹), fun Q hQ T hT => ?_⟩
  have hl := ell_large _ Q hQ
  have h0 : 0 ≤ M' ^ P.a0⁻¹ := Real.rpow_nonneg hM'0.le _
  have h1 : (M' ^ P.a0⁻¹) ^ P.a0 ≤ Real.log Q ^ P.a0 :=
    Real.rpow_le_rpow h0 hl P.a0_pos.le
  rw [Real.rpow_inv_rpow hM'0.le P.a0_pos.ne'] at h1
  exact (le_max_left _ _).trans (h1.trans hT.1)

lemma logT_le {Q T : ℝ} (hQ : Real.exp 1 ≤ Q) (hT : T ∈ P.heights Q) :
    0 ≤ Real.log T ∧ Real.log T ≤ P.A0 * Real.log Q := by
  have hT1 : 1 ≤ T := Families.Phase3.C.one_le_T P hQ hT
  have hl : 1 ≤ Real.log Q := ell_large 1 Q hQ
  refine ⟨Real.log_nonneg hT1, ?_⟩
  have h1 : Real.log T ≤ Real.log (Real.log Q ^ P.A0) :=
    Real.log_le_log (by linarith) hT.2
  rw [Real.log_rpow (by linarith)] at h1
  have h2 : Real.log (Real.log Q) ≤ Real.log Q := by
    have := Real.log_le_sub_one_of_pos (show 0 < Real.log Q by linarith)
    linarith
  have hA : 0 ≤ P.A0 := (P.a0_pos.trans P.a0_lt).le
  nlinarith

end Asymp

end MixSS

/-! ### `lem:ss` -/

open MixSS in
/-- **`lem:ss`**: the same-sign term is `o(H T L² ℓ)`, uniformly in `T`. -/
theorem SSC_small (hMV : MV_LargeSieve) (hWH : lemWH_Statement) :
    ∀ (P : PrimeSetup) (W : Weight) (δ : ℝ), 0 < δ → ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
      ∀ T ∈ P.heights Q,
      ‖SSC P W Q T‖ ≤ δ * (W.H Q * T * P.L Q ^ 2 * ell Q) := by
  intro P W δ hδ
  obtain ⟨C₀, hC₀, hB⟩ := SSC_bound hMV
  obtain ⟨CΦ, hCΦ, hΦ⟩ := integral_PhiSq_le P
  obtain ⟨C₁, Q₁, hC₁, h₁⟩ := sum_aVec_sq_div_log_le P
  obtain ⟨cH, QH, hcH, hH⟩ := H_lower hWH W
  set K : ℝ := 4 * W.wmax * C₀ * C₁ * CΦ / cH with hK
  have hw := W.wmax_nonneg
  have hK0 : 0 ≤ K := by positivity
  obtain ⟨QT, hQT⟩ := T_large P (K * P.lam / δ)
  refine ⟨max (max Q₁ QH) (max QT (Real.exp 1)), fun Q hQ T hT => ?_⟩
  have hQ1 : Q₁ ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hQ
  have hQH : QH ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hQ
  have hQT' : QT ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hQ
  have hQe : Real.exp 1 ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hQ
  have hℓ : 1 ≤ Real.log Q := ell_large 1 Q hQe
  have hQ1' : 1 < Q := lt_of_lt_of_le (by
    have := Real.add_one_le_exp (1 : ℝ); linarith) hQe
  have hL : 0 < P.L Q := mul_pos P.lam_pos (by linarith)
  have hT1 : 1 ≤ T := Families.Phase3.C.one_le_T P hQe hT
  have hTbig : K * P.lam / δ ≤ T := hQT Q hQT' T hT
  have hY : P.Y Q ≤ Q ^ 2 := Families.Phase3.C.Y_le_sq P hQ1'.le
  have hY0 := PrimeSetup.Y_nonneg P Q
  have hHc : cH * Q ^ 2 ≤ W.H Q := hH Q hQH
  have hH0 : 0 ≤ W.H Q := W.H_nonneg Q
  have hIΦ : ∫ r, PhiSq P Q r ≤ CΦ * P.L Q := hΦ Q hQ1'
  have hIΦ0 : 0 ≤ ∫ r, PhiSq P Q r := integral_nonneg fun r => PhiSq_nonneg P Q r
  have hS : ∑ n ∈ P.range Q, P.aVec Q n ^ 2 / (2 * Real.log n) ≤ C₁ * P.L Q ^ 2 := by
    refine le_trans (Finset.sum_le_sum fun n hn => ?_) (h₁ Q hQ1)
    have h0 : 0 ≤ P.aVec Q n ^ 2 / Real.log n :=
      div_nonneg (sq_nonneg _) (Real.log_nonneg (by exact_mod_cast range_one_le P hn))
    rw [mul_comm, ← div_div]
    exact half_le_self h0
  have hS0 : 0 ≤ ∑ n ∈ P.range Q, P.aVec Q n ^ 2 / (2 * Real.log n) :=
    Finset.sum_nonneg fun n hn => div_nonneg (sq_nonneg _)
      (mul_nonneg two_pos.le (Real.log_nonneg (by exact_mod_cast range_one_le P hn)))
  refine (hB P W Q hQ1' T).trans ?_
  -- `(∫Φ²) · 2 w C₀ (Q²+Y) ∑ ≤ CΦ L · 2 w C₀ (2Q²) C₁ L² ≤ K H L³`
  have hQ2 : Q ^ 2 ≤ W.H Q / cH := by rw [le_div_iff₀ hcH]; linarith
  have step1 : (∫ r, PhiSq P Q r) * (2 * (W.wmax * C₀ * (Q ^ 2 + P.Y Q) *
      ∑ n ∈ P.range Q, P.aVec Q n ^ 2 / (2 * Real.log n))) ≤
      (CΦ * P.L Q) * (2 * (W.wmax * C₀ * (2 * Q ^ 2) * (C₁ * P.L Q ^ 2))) := by
    gcongr
    linarith
  have step2 : (CΦ * P.L Q) * (2 * (W.wmax * C₀ * (2 * Q ^ 2) * (C₁ * P.L Q ^ 2))) ≤
      K * W.H Q * P.L Q ^ 3 := by
    have : (CΦ * P.L Q) * (2 * (W.wmax * C₀ * (2 * Q ^ 2) * (C₁ * P.L Q ^ 2))) =
        (4 * W.wmax * C₀ * C₁ * CΦ) * Q ^ 2 * P.L Q ^ 3 := by ring
    rw [this, hK]
    have h4 : 0 ≤ 4 * W.wmax * C₀ * C₁ * CΦ := by positivity
    calc 4 * W.wmax * C₀ * C₁ * CΦ * Q ^ 2 * P.L Q ^ 3
        ≤ 4 * W.wmax * C₀ * C₁ * CΦ * (W.H Q / cH) * P.L Q ^ 3 := by gcongr
      _ = 4 * W.wmax * C₀ * C₁ * CΦ / cH * W.H Q * P.L Q ^ 3 := by ring
  have step3 : K * W.H Q * P.L Q ^ 3 ≤ δ * (W.H Q * T * P.L Q ^ 2 * ell Q) := by
    have hKl : K * P.lam ≤ δ * T := by rwa [div_le_iff₀ hδ, mul_comm T] at hTbig
    have hLl : P.L Q = P.lam * ell Q := rfl
    have : K * W.H Q * P.L Q ^ 3 = (K * P.lam) * (W.H Q * P.L Q ^ 2 * ell Q) := by
      rw [hLl]; ring
    rw [this]
    have hpos : 0 ≤ W.H Q * P.L Q ^ 2 * ell Q := by
      unfold ell; positivity
    calc (K * P.lam) * (W.H Q * P.L Q ^ 2 * ell Q) ≤ (δ * T) * (W.H Q * P.L Q ^ 2 * ell Q) :=
          mul_le_mul_of_nonneg_right hKl hpos
      _ = δ * (W.H Q * T * P.L Q ^ 2 * ell Q) := by ring
  linarith

end Families.Ported.Second

/-! ### The mixed term -/

namespace Families.Ported.Second

open Families

namespace MixSS

section Mix

variable (P : PrimeSetup)

/-- `β_q = (1/2π)(log(q/π) + log T)`. -/
def beta (q : ℕ) (T : ℝ) : ℝ := 1 / (2 * Real.pi) * (Real.log (q / Real.pi) + Real.log T)

/-- The `r`-part `∑_χ ω_χ ∬ Φ(t−t')² (μ_χ(t) − β_q) P_χ(t')`. -/
def MA (W : Weight) (Q T : ℝ) : ℝ :=
  famSum W Q fun q χ => ∫ t in P.J T, ∫ t' in P.J T,
    PhiSq P Q (t - t') * (muChi χ t - beta q T) * PChi P Q χ t'

/-- The `β`-part `∑_χ ω_χ β_q ∬ Φ(t−t')² P_χ(t')`. -/
def MB (W : Weight) (Q T : ℝ) : ℝ :=
  famSum W Q fun q χ => ∫ t in P.J T, ∫ t' in P.J T,
    PhiSq P Q (t - t') * beta q T * PChi P Q χ t'

lemma PhiSq_cont2 {Q : ℝ} (hQ : 1 < Q) :
    Continuous (fun p : ℝ × ℝ => PhiSq P Q (p.1 - p.2)) :=
  (PhiSq_continuous P hQ).comp (continuous_fst.sub continuous_snd)

lemma Mmix_split (W : Weight) {Q : ℝ} (hQ : 1 < Q) (T : ℝ) :
    Mmix P W Q T = MA P W Q T + MB P W Q T := by
  unfold Mmix MA MB famSum PrimeSetup.J
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [← D_add]
  · exact D_congr _ _ _ _ fun t t' => by ring
  · exact ((PhiSq_cont2 P hQ).mul (((muChi_continuous χ).comp continuous_fst).sub
      continuous_const)).mul ((PChi_continuous P Q χ).comp continuous_snd)
  · exact ((PhiSq_cont2 P hQ).mul continuous_const).mul ((PChi_continuous P Q χ).comp continuous_snd)

lemma H_eq (W : Weight) (Q : ℝ) :
    W.H Q = ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ _χ ∈ primChars q, (1 : ℝ) := by
  unfold Weight.H phiStar
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]

/-- `∑_χ ω_χ |P_χ(t')| ≤ (1/π)(A H/2 + w_max C₀ (Q²+Y) ‖a‖²/(2A))` (large sieve and AM–GM). -/
lemma sum_absP_le (hMV : MV_LargeSieve) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧
    ∀ (P : PrimeSetup) (W : Weight) (Q : ℝ), 1 ≤ Q → ∀ A : ℝ, 0 < A → ∀ t' : ℝ,
      ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ χ ∈ primChars q, |PChi P Q χ t'| ≤
        1 / Real.pi * (A / 2 * W.H Q +
          W.wmax * C₀ * (Q ^ 2 + P.Y Q) * (∑ n ∈ P.range Q, P.aVec Q n ^ 2) / (2 * A)) := by
  obtain ⟨C₀, hC₀, hLS⟩ := famLS_omega hMV
  refine ⟨C₀, hC₀, fun P W Q hQ A hA t' => ?_⟩
  have hω := W.omega_nonneg Q
  have hpi : 0 < 1 / Real.pi := by positivity
  set x : ℕ → ℂ := fun n => (P.aVec Q n : ℂ) * (n : ℂ) ^ (-(Complex.I * t')) with hxdef
  have hS : ∀ q (χ : DirichletCharacter ℂ q),
      P.Schi χ Q (P.aVec Q) t' = ∑ n ∈ P.range Q, x n * χ n := by
    intro q χ; unfold PrimeSetup.Schi
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hxdef]; ring
  have hx : ∑ n ∈ P.range Q, ‖x n‖ ^ 2 = ∑ n ∈ P.range Q, P.aVec Q n ^ 2 := by
    refine Finset.sum_congr rfl fun n hn => ?_
    simp only [hxdef]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (aVec_nonneg P Q n),
      norm_cpow_eq_one n (range_one_le P hn), mul_one]
  have hL := hLS P W Q hQ x
  rw [hx] at hL
  set s : (q : ℕ) → DirichletCharacter ℂ q → ℝ := fun q χ => ‖∑ n ∈ P.range Q, x n * χ n‖ ^ 2
    with hsdef
  have hP : ∀ q (χ : DirichletCharacter ℂ q),
      |PChi P Q χ t'| ≤ 1 / Real.pi * (A / 2 + s q χ / (2 * A)) := by
    intro q χ
    unfold PChi
    rw [abs_mul, abs_neg, abs_of_pos hpi, hS q χ]
    refine mul_le_mul_of_nonneg_left ?_ hpi.le
    set z := ∑ n ∈ P.range Q, x n * χ n
    refine (Complex.abs_re_le_norm z).trans ?_
    have key : A / 2 + ‖z‖ ^ 2 / (2 * A) - ‖z‖ = (‖z‖ - A) ^ 2 / (2 * A) := by
      field_simp; ring
    have : 0 ≤ (‖z‖ - A) ^ 2 / (2 * A) := by positivity
    simp only [hsdef]
    linarith
  have e1 : ∀ q, ∑ χ ∈ primChars q, 1 / Real.pi * (A / 2 + s q χ / (2 * A)) =
      1 / Real.pi * (A / 2) * ∑ _χ ∈ primChars q, (1 : ℝ) +
        1 / Real.pi / (2 * A) * ∑ χ ∈ primChars q, s q χ := by
    intro q
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun χ _ => ?_
    field_simp
  calc ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ χ ∈ primChars q, |PChi P Q χ t'|
      ≤ ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ χ ∈ primChars q,
          1 / Real.pi * (A / 2 + s q χ / (2 * A)) :=
        Finset.sum_le_sum fun q _ =>
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun χ _ => hP q χ) (hω q)
    _ = 1 / Real.pi * (A / 2) * W.H Q + 1 / Real.pi / (2 * A) *
          ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ χ ∈ primChars q, s q χ := by
        rw [H_eq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [e1 q]; ring
    _ ≤ 1 / Real.pi * (A / 2) * W.H Q + 1 / Real.pi / (2 * A) *
          (W.wmax * C₀ * (Q ^ 2 + P.Y Q) * ∑ n ∈ P.range Q, P.aVec Q n ^ 2) := by
        gcongr
    _ = _ := by ring

/-- The `r`-part: `|M_A| ≤ R₀ · sup_{t'} ∑_χ ω_χ|P_χ(t')| · ∬_{J²}Φ²`. -/
lemma MA_bound (hStir : StirlingDigamma) (hMV : MV_LargeSieve) : ∃ R₀ C₀ : ℝ, 0 ≤ R₀ ∧ 0 ≤ C₀ ∧
    ∀ (P : PrimeSetup) (W : Weight) (Q : ℝ), 1 < Q → ∀ T : ℝ, 1 ≤ T → ∀ A : ℝ, 0 < A →
      |MA P W Q T| ≤ R₀ * (1 / Real.pi * (A / 2 * W.H Q +
          W.wmax * C₀ * (Q ^ 2 + P.Y Q) * (∑ n ∈ P.range Q, P.aVec Q n ^ 2) / (2 * A))) *
        ∫ t in P.J T, ∫ t' in P.J T, PhiSq P Q (t - t') := by
  obtain ⟨R₀, hR₀, hmu⟩ := muChi_near_J hStir
  obtain ⟨C₀, hC₀, hsum⟩ := sum_absP_le hMV
  refine ⟨R₀, C₀, hR₀, hC₀, fun P W Q hQ T hT A hA => ?_⟩
  set BP := 1 / Real.pi * (A / 2 * W.H Q +
    W.wmax * C₀ * (Q ^ 2 + P.Y Q) * (∑ n ∈ P.range Q, P.aVec Q n ^ 2) / (2 * A)) with hBP
  have hBP_ge : ∀ t', ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ χ ∈ primChars q,
      |PChi P Q χ t'| ≤ BP := hsum P W Q hQ.le A hA
  have hω := W.omega_nonneg Q
  have hmu' : ∀ q (χ : DirichletCharacter ℂ q), ∀ t ∈ P.J T, |muChi χ t - beta q T| ≤ R₀ :=
    fun q χ t ht => hmu P T hT q χ t ht
  unfold MA famSum
  unfold PrimeSetup.J at hmu' ⊢
  set a := (1 + P.θ) * T
  set b := (2 - P.θ) * T
  have hcP : ∀ q (χ : DirichletCharacter ℂ q), Continuous (Function.uncurry
      (fun t t' => PhiSq P Q (t - t') * (R₀ * |PChi P Q χ t'|))) := fun q χ =>
    (PhiSq_cont2 P hQ).mul (continuous_const.mul
      (((PChi_continuous P Q χ).comp continuous_snd).abs))
  have step1 : |∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ χ ∈ primChars q,
      ∫ t in Set.Icc a b, ∫ t' in Set.Icc a b,
        PhiSq P Q (t - t') * (muChi χ t - beta q T) * PChi P Q χ t'| ≤
      ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ χ ∈ primChars q,
        ∫ t in Set.Icc a b, ∫ t' in Set.Icc a b, PhiSq P Q (t - t') * (R₀ * |PChi P Q χ t'|) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q _ => ?_)
    rw [abs_mul, abs_of_nonneg (hω q)]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun χ _ => ?_)) (hω q)
    rw [← Real.norm_eq_abs]
    refine D_norm_le a b _ _ (hcP q χ) fun t ht t' _ => ?_
    have h0 := PhiSq_nonneg P Q (t - t')
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg h0]
    have := hmu' q χ t ht
    calc PhiSq P Q (t - t') * |muChi χ t - beta q T| * |PChi P Q χ t'|
        ≤ PhiSq P Q (t - t') * R₀ * |PChi P Q χ t'| := by gcongr
      _ = PhiSq P Q (t - t') * (R₀ * |PChi P Q χ t'|) := by ring
  rw [← D_famsum a b _ (fun q => W.omega Q q)
    (fun q χ t t' => PhiSq P Q (t - t') * (R₀ * |PChi P Q χ t'|)) hcP] at step1
  refine step1.trans ?_
  have hc1 : Continuous (Function.uncurry (fun t t' : ℝ =>
      ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ χ ∈ primChars q,
        PhiSq P Q (t - t') * (R₀ * |PChi P Q χ t'|))) :=
    continuous_finsetSum _ fun q _ => continuous_const.mul
      (continuous_finsetSum _ fun χ _ => hcP q χ)
  have hc2 : Continuous (Function.uncurry (fun t t' : ℝ => R₀ * BP * PhiSq P Q (t - t'))) :=
    continuous_const.mul (PhiSq_cont2 P hQ)
  refine (D_mono a b _ _ hc1 hc2 fun t _ t' _ => ?_).trans (le_of_eq ?_)
  · have e : ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ χ ∈ primChars q,
        PhiSq P Q (t - t') * (R₀ * |PChi P Q χ t'|) =
        PhiSq P Q (t - t') * R₀ * ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q *
          ∑ χ ∈ primChars q, |PChi P Q χ t'| := by
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun χ _ => ?_
      ring
    rw [e]
    have h0 := PhiSq_nonneg P Q (t - t')
    calc PhiSq P Q (t - t') * R₀ * ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q *
          ∑ χ ∈ primChars q, |PChi P Q χ t'| ≤ PhiSq P Q (t - t') * R₀ * BP := by
          gcongr
          exact hBP_ge t'
      _ = R₀ * BP * PhiSq P Q (t - t') := by ring
  · simp_rw [integral_const_mul]

/-- `X(n) = ∬_{J²} Φ(t−t')² n^{−it'}`. -/
def Xn (Q T : ℝ) (n : ℕ) : ℂ :=
  ∫ t in P.J T, ∫ t' in P.J T, (PhiSq P Q (t - t') : ℂ) * (n : ℂ) ^ (-(Complex.I * t'))

lemma MB_chi {Q : ℝ} (hQ : 1 < Q) (T β : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ∫ t in P.J T, ∫ t' in P.J T, PhiSq P Q (t - t') * β * PChi P Q χ t' =
      β * (-(1 / Real.pi)) * (∑ n ∈ P.range Q, ((P.aVec Q n : ℂ) * Xn P Q T n) * χ n).re := by
  unfold Xn PrimeSetup.J
  have hpt : ∀ t t', PhiSq P Q (t - t') * β * PChi P Q χ t' =
      β * (-(1 / Real.pi)) * ((PhiSq P Q (t - t') : ℂ) * P.Schi χ Q (P.aVec Q) t').re := by
    intro t t'; unfold PChi; rw [Complex.re_ofReal_mul]; ring
  rw [D_congr _ _ _ _ hpt]
  simp_rw [integral_const_mul]
  congr 1
  have hc : Continuous (Function.uncurry (fun t t' : ℝ =>
      (PhiSq P Q (t - t') : ℂ) * P.Schi χ Q (P.aVec Q) t')) :=
    (Complex.continuous_ofReal.comp (PhiSq_cont2 P hQ)).mul
      ((Schi_continuous P χ Q _).comp continuous_snd)
  rw [D_re _ _ _ hc]
  congr 1
  have hpt2 : ∀ t t', (PhiSq P Q (t - t') : ℂ) * P.Schi χ Q (P.aVec Q) t' =
      ∑ n ∈ P.range Q, ((P.aVec Q n : ℂ) * χ n) *
        ((PhiSq P Q (t - t') : ℂ) * (n : ℂ) ^ (-(Complex.I * t'))) := by
    intro t t'; unfold PrimeSetup.Schi; rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [D_congr _ _ _ _ hpt2, D_sum _ _ _ (fun n t t' => ((P.aVec Q n : ℂ) * χ n) *
    ((PhiSq P Q (t - t') : ℂ) * (n : ℂ) ^ (-(Complex.I * t')))) fun n hn => continuous_const.mul
    ((Complex.continuous_ofReal.comp (PhiSq_cont2 P hQ)).mul
      ((continuous_cpow n (range_one_le P hn)).comp continuous_snd))]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp_rw [integral_const_mul]
  ring

lemma MB_eq (W : Weight) {Q : ℝ} (hQ : 1 < Q) (T : ℝ) :
    MB P W Q T = -(1 / Real.pi) * (∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ ∈ primChars q,
      ((W.omega Q q * beta q T : ℝ) : ℂ) *
        ∑ n ∈ P.range Q, ((P.aVec Q n : ℂ) * Xn P Q T n) * χ n).re := by
  unfold MB famSum
  simp_rw [MB_chi P hQ T]
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Complex.re_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [Complex.re_ofReal_mul]
  ring

lemma beta_abs_le {Q T : ℝ} (hQ : Real.exp 1 ≤ Q) (hT : T ∈ P.heights Q) {q : ℕ}
    (hq : q ∈ Finset.Icc 1 ⌊Q⌋₊) :
    |beta q T| ≤ (4 + P.A0) / (2 * Real.pi) * Real.log Q := by
  have hℓ : 1 ≤ Real.log Q := ell_large 1 Q hQ
  have hQ0 : 0 < Q := lt_of_lt_of_le (Real.exp_pos 1) hQ
  obtain ⟨hq1, hqQ⟩ := Finset.mem_Icc.mp hq
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hqQ' : (q : ℝ) ≤ Q := (Nat.cast_le.mpr hqQ).trans (Nat.floor_le hQ0.le)
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hq1'
  have hlqQ : Real.log q ≤ Real.log Q := Real.log_le_log (by linarith) hqQ'
  have hpi0 : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  have hpi3 : Real.log Real.pi ≤ 3 := by
    have := Real.log_le_sub_one_of_pos Real.pi_pos
    linarith [Real.pi_le_four]
  obtain ⟨hT0, hTA⟩ := logT_le P hQ hT
  have hdiv : Real.log (q / Real.pi) = Real.log q - Real.log Real.pi :=
    Real.log_div (by positivity) Real.pi_ne_zero
  have hA0 : 0 ≤ P.A0 := (P.a0_pos.trans P.a0_lt).le
  unfold beta
  rw [hdiv, abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  have habs : |Real.log q - Real.log Real.pi + Real.log T| ≤ (4 + P.A0) * Real.log Q := by
    rw [abs_le]; constructor <;> nlinarith
  calc 1 / (2 * Real.pi) * |Real.log q - Real.log Real.pi + Real.log T|
      ≤ 1 / (2 * Real.pi) * ((4 + P.A0) * Real.log Q) := by gcongr
    _ = (4 + P.A0) / (2 * Real.pi) * Real.log Q := by ring

lemma Xn_bound {Q : ℝ} (hQ : 1 < Q) (T : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    ‖Xn P Q T n‖ ≤ 2 * (∫ r, PhiSq P Q r) / Real.log n := by
  unfold Xn PrimeSetup.J
  exact X_bound (PhiSq P Q) (PhiSq_integrable P hQ) (PhiSq_continuous P hQ) (PhiSq_nonneg P Q)
    _ _ n hn

end Mix

/-! ### `lem:muLambda` -/

theorem MB_small (hMV : MV_LargeSieve) (hWH : lemWH_Statement) :
    ∀ (P : PrimeSetup) (W : Weight) (δ : ℝ), 0 < δ → ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
      ∀ T ∈ P.heights Q, |MB P W Q T| ≤ δ * (W.H Q * T * P.L Q ^ 2 * ell Q) := by
  intro P W δ hδ
  obtain ⟨C₀, hC₀, hbil⟩ := bilinLS hMV
  obtain ⟨CΦ, hCΦ, hΦ⟩ := integral_PhiSq_le P
  obtain ⟨C₂, Q₂, hC₂, h₂⟩ := sum_aVec_sq_div_log_sq_le P
  obtain ⟨cH, QH, hcH, hH⟩ := H_lower hWH W
  have hw := W.wmax_nonneg
  set Kβ : ℝ := (4 + P.A0) / (2 * Real.pi) with hKβ
  set K₃ : ℝ := W.wmax * Kβ ^ 2 * (C₀ * (2 / cH) * (4 * CΦ ^ 2 * C₂)) with hK₃
  have hK₃0 : 0 ≤ K₃ := by positivity
  have hpδ : 0 < (Real.pi * δ) ^ 2 * P.lam := by
    have := P.lam_pos; have := Real.pi_pos; positivity
  refine ⟨max (max Q₂ QH) (max (Real.exp 1) (Real.exp (K₃ / ((Real.pi * δ) ^ 2 * P.lam)))),
    fun Q hQ T hT => ?_⟩
  have hQ2 : Q₂ ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hQ
  have hQH : QH ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hQ
  have hQe : Real.exp 1 ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hQ
  have hQb : Real.exp (K₃ / ((Real.pi * δ) ^ 2 * P.lam)) ≤ Q :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hQ
  have hℓ : 1 ≤ Real.log Q := ell_large 1 Q hQe
  have hℓb := ell_large _ Q hQb
  have hQ1' : 1 < Q := lt_of_lt_of_le (by
    have := Real.add_one_le_exp (1 : ℝ); linarith) hQe
  have hL : 0 < P.L Q := mul_pos P.lam_pos (by linarith)
  have hLdef : P.L Q = P.lam * Real.log Q := rfl
  have hT1 : 1 ≤ T := Families.Phase3.C.one_le_T P hQe hT
  have hY : P.Y Q ≤ Q ^ 2 := Families.Phase3.C.Y_le_sq P hQ1'.le
  have hY0 := PrimeSetup.Y_nonneg P Q
  have hHc : cH * Q ^ 2 ≤ W.H Q := hH Q hQH
  have hH0 : 0 ≤ W.H Q := W.H_nonneg Q
  have hQ2H : Q ^ 2 ≤ W.H Q / cH := by rw [le_div_iff₀ hcH]; linarith
  have hω := W.omega_nonneg Q
  have hLbig : K₃ ≤ (Real.pi * δ) ^ 2 * P.L Q := by
    rw [div_le_iff₀ hpδ] at hℓb
    rw [hLdef]; linarith
  rw [MB_eq P W hQ1' T]
  set Z := ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ ∈ primChars q,
      ((W.omega Q q * beta q T : ℝ) : ℂ) *
        ∑ n ∈ P.range Q, ((P.aVec Q n : ℂ) * Xn P Q T n) * χ n with hZ
  -- the `b`-sum
  have h1 : ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ ∈ primChars q, (Nat.totient q : ℝ) / q *
      ‖((W.omega Q q * beta q T : ℝ) : ℂ)‖ ^ 2 ≤
      W.wmax * (Kβ * Real.log Q) ^ 2 * W.H Q := by
    calc ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ ∈ primChars q, (Nat.totient q : ℝ) / q *
          ‖((W.omega Q q * beta q T : ℝ) : ℂ)‖ ^ 2
        ≤ ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ _χ ∈ primChars q,
            W.wmax * (Kβ * Real.log Q) ^ 2 * W.omega Q q := by
          refine Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun χ _ => ?_
          have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
          have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
          have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq1
          have hωle := omega_le W Q q
          have hφω : (Nat.totient q : ℝ) / q * W.omega Q q ≤ W.wmax := by
            calc (Nat.totient q : ℝ) / q * W.omega Q q
                ≤ (Nat.totient q : ℝ) / q * (W.wmax * ((q : ℝ) / (Nat.totient q : ℝ))) := by
                  gcongr
              _ = W.wmax := by field_simp
          have hβ := beta_abs_le P hQe hT hq
          have hβ2 : beta q T ^ 2 ≤ (Kβ * Real.log Q) ^ 2 := by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) hβ 2
          rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
          calc (Nat.totient q : ℝ) / q * (W.omega Q q * beta q T) ^ 2
              = ((Nat.totient q : ℝ) / q * W.omega Q q) * (W.omega Q q * beta q T ^ 2) := by ring
            _ ≤ W.wmax * (W.omega Q q * (Kβ * Real.log Q) ^ 2) := by
                refine mul_le_mul hφω ?_ (mul_nonneg (hω q) (sq_nonneg _)) hw
                exact mul_le_mul_of_nonneg_left hβ2 (hω q)
            _ = W.wmax * (Kβ * Real.log Q) ^ 2 * W.omega Q q := by ring
      _ = W.wmax * (Kβ * Real.log Q) ^ 2 * W.H Q := by
          rw [H_eq, Finset.mul_sum]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun χ _ => ?_
          ring
  -- the `x`-sum
  have hIΦ : ∫ r, PhiSq P Q r ≤ CΦ * P.L Q := hΦ Q hQ1'
  have hIΦ0 : 0 ≤ ∫ r, PhiSq P Q r := integral_nonneg fun r => PhiSq_nonneg P Q r
  have h2 : ∑ n ∈ P.range Q, ‖(P.aVec Q n : ℂ) * Xn P Q T n‖ ^ 2 ≤
      4 * CΦ ^ 2 * P.L Q ^ 2 * (C₂ * P.L Q) := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (h₂ Q hQ2) (by positivity))
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn1 := range_one_le P hn
    by_cases hn2 : n = 1
    · subst hn2; simp [aVec_one]
    have hn2' : 2 ≤ n := by omega
    have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hX := Xn_bound P hQ1' T n hn2'
    have hX' : ‖Xn P Q T n‖ ≤ 2 * (CΦ * P.L Q) / Real.log n :=
      hX.trans (by gcongr)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (aVec_nonneg P Q n), mul_pow]
    calc P.aVec Q n ^ 2 * ‖Xn P Q T n‖ ^ 2
        ≤ P.aVec Q n ^ 2 * (2 * (CΦ * P.L Q) / Real.log n) ^ 2 := by
          gcongr
      _ = 4 * CΦ ^ 2 * P.L Q ^ 2 * (P.aVec Q n ^ 2 / Real.log n ^ 2) := by
          field_simp
          ring
  have hZ2 : ‖Z‖ ^ 2 ≤ K₃ * Real.log Q ^ 2 * W.H Q ^ 2 * P.L Q ^ 3 := by
    have hb := hbil P Q hQ1'.le (fun q χ => ((W.omega Q q * beta q T : ℝ) : ℂ))
      (fun n => (P.aVec Q n : ℂ) * Xn P Q T n)
    refine hb.trans ?_
    have hS0 : 0 ≤ ∑ n ∈ P.range Q, ‖(P.aVec Q n : ℂ) * Xn P Q T n‖ ^ 2 :=
      Finset.sum_nonneg fun n _ => sq_nonneg _
    calc (∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ ∈ primChars q, (Nat.totient q : ℝ) / q *
          ‖((W.omega Q q * beta q T : ℝ) : ℂ)‖ ^ 2) *
          (C₀ * (Q ^ 2 + P.Y Q) * ∑ n ∈ P.range Q, ‖(P.aVec Q n : ℂ) * Xn P Q T n‖ ^ 2)
        ≤ (W.wmax * (Kβ * Real.log Q) ^ 2 * W.H Q) *
          (C₀ * (2 * (W.H Q / cH)) * (4 * CΦ ^ 2 * P.L Q ^ 2 * (C₂ * P.L Q))) := by
          refine mul_le_mul h1 ?_ (by positivity) (by positivity)
          refine mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hC₀) h2 hS0 (by positivity)
      _ = K₃ * Real.log Q ^ 2 * W.H Q ^ 2 * P.L Q ^ 3 := by
          rw [hK₃]; field_simp
  -- conclusion
  have hX0 : 0 ≤ Real.pi * δ * (W.H Q * T * P.L Q ^ 2 * Real.log Q) := by positivity
  have hZle : ‖Z‖ ≤ Real.pi * δ * (W.H Q * T * P.L Q ^ 2 * Real.log Q) := by
    have hsq : ‖Z‖ ^ 2 ≤ (Real.pi * δ * (W.H Q * T * P.L Q ^ 2 * Real.log Q)) ^ 2 := by
      refine hZ2.trans ?_
      have e : (Real.pi * δ * (W.H Q * T * P.L Q ^ 2 * Real.log Q)) ^ 2 =
          ((Real.pi * δ) ^ 2 * P.L Q) * T ^ 2 * (Real.log Q ^ 2 * W.H Q ^ 2 * P.L Q ^ 3) := by ring
      rw [e]
      have hT2 : 1 ≤ T ^ 2 := one_le_pow₀ hT1
      have hp : 0 ≤ Real.log Q ^ 2 * W.H Q ^ 2 * P.L Q ^ 3 := by positivity
      calc K₃ * Real.log Q ^ 2 * W.H Q ^ 2 * P.L Q ^ 3
          = K₃ * 1 * (Real.log Q ^ 2 * W.H Q ^ 2 * P.L Q ^ 3) := by ring
        _ ≤ ((Real.pi * δ) ^ 2 * P.L Q) * T ^ 2 * (Real.log Q ^ 2 * W.H Q ^ 2 * P.L Q ^ 3) := by
          gcongr
    have := abs_le_of_sq_le_sq hsq hX0
    rwa [abs_norm] at this
  unfold ell
  rw [abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 1 / Real.pi)]
  calc 1 / Real.pi * |Z.re| ≤ 1 / Real.pi * ‖Z‖ := by
        gcongr; exact Complex.abs_re_le_norm Z
    _ ≤ 1 / Real.pi * (Real.pi * δ * (W.H Q * T * P.L Q ^ 2 * Real.log Q)) := by gcongr
    _ = δ * (W.H Q * T * P.L Q ^ 2 * Real.log Q) := by
        field_simp

theorem MA_small (hStir : StirlingDigamma) (hMV : MV_LargeSieve) (hWH : lemWH_Statement) :
    ∀ (P : PrimeSetup) (W : Weight) (δ : ℝ), 0 < δ → ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
      ∀ T ∈ P.heights Q, |MA P W Q T| ≤ δ * (W.H Q * T * P.L Q ^ 2 * ell Q) := by
  intro P W δ hδ
  obtain ⟨R₀, C₀, hR₀, hC₀, hMA⟩ := MA_bound hStir hMV
  obtain ⟨CJ, hCJ, hJ⟩ := J2_PhiSq_le P
  obtain ⟨Ca, Qa, hCa, ha⟩ := sum_aVec_sq_le P
  obtain ⟨cH, QH, hcH, hH⟩ := H_lower hWH W
  have hw := W.wmax_nonneg
  have hpi := Real.pi_pos
  have hlam := P.lam_pos
  have hb : 0 ≤ P.bInt := integral_nonneg fun s => sq_nonneg _
  set K₁ : ℝ := W.wmax * C₀ * Ca * P.lam / cH with hK₁
  set K₂ : ℝ := R₀ * (2 * Real.pi * P.bInt + CJ) / Real.pi with hK₂
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hK₂0 : 0 ≤ K₂ := by positivity
  set η : ℝ := δ / (2 * (K₂ + 1)) with hη
  have hη0 : 0 < η := by positivity
  refine ⟨max (max Qa QH) (max (max (Real.exp 1) (Real.exp (1 / P.lam)))
    (Real.exp (4 * K₂ * K₁ / (η * δ)))), fun Q hQ T hT => ?_⟩
  have hQa : Qa ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hQ
  have hQH : QH ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hQ
  have hQe : Real.exp 1 ≤ Q := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_max_right _ _)) hQ
  have hQl : Real.exp (1 / P.lam) ≤ Q := le_trans (le_trans (le_trans (le_max_right _ _)
    (le_max_left _ _)) (le_max_right _ _)) hQ
  have hQb : Real.exp (4 * K₂ * K₁ / (η * δ)) ≤ Q :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hQ
  have hℓ : 1 ≤ Real.log Q := ell_large 1 Q hQe
  have hℓb := ell_large _ Q hQb
  have hQ1' : 1 < Q := lt_of_lt_of_le (by
    have := Real.add_one_le_exp (1 : ℝ); linarith) hQe
  have hL1 : 1 ≤ P.L Q := Families.Phase3.C.one_le_L P hQl
  have hL : 0 < P.L Q := by linarith
  have hLdef : P.L Q = P.lam * Real.log Q := rfl
  have hT1 : 1 ≤ T := Families.Phase3.C.one_le_T P hQe hT
  have hY : P.Y Q ≤ Q ^ 2 := Families.Phase3.C.Y_le_sq P hQ1'.le
  have hY0 := PrimeSetup.Y_nonneg P Q
  have hHc : cH * Q ^ 2 ≤ W.H Q := hH Q hQH
  have hH0 : 0 ≤ W.H Q := W.H_nonneg Q
  have hQ2H : Q ^ 2 ≤ W.H Q / cH := by rw [le_div_iff₀ hcH]; linarith
  set A : ℝ := η * Real.log Q * P.L Q with hA
  have hA0 : 0 < A := by positivity
  have hmain := hMA P W Q hQ1' T hT1 A hA0
  set Dphi := ∫ t in P.J T, ∫ t' in P.J T, PhiSq P Q (t - t') with hDphi
  have hD0 : 0 ≤ Dphi := integral_nonneg fun t => integral_nonneg fun t' => PhiSq_nonneg P Q _
  have hDle : Dphi ≤ (2 * Real.pi * P.bInt + CJ) * (T * P.L Q) := by
    refine (hJ Q T hQ1' (by linarith)).trans ?_
    have hJl : P.Jlen T ≤ T := by
      have : 0 ≤ P.θ * T := mul_nonneg P.θ_pos.le (by linarith)
      calc P.Jlen T = T - 2 * (P.θ * T) := by unfold PrimeSetup.Jlen; ring
        _ ≤ T := by linarith
    have hTL : 1 ≤ T * P.L Q := one_le_mul_of_one_le_of_one_le hT1 hL1
    calc 2 * Real.pi * P.Jlen T * P.bInt * P.L Q + CJ
        ≤ 2 * Real.pi * T * P.bInt * P.L Q + CJ * (T * P.L Q) := by
          gcongr
          · exact le_mul_of_one_le_right hCJ hTL
      _ = (2 * Real.pi * P.bInt + CJ) * (T * P.L Q) := by ring
  -- the large-sieve factor
  have hsa := ha Q hQa
  have hsa0 : 0 ≤ ∑ n ∈ P.range Q, P.aVec Q n ^ 2 := Finset.sum_nonneg fun n _ => sq_nonneg _
  have hBP : 1 / Real.pi * (A / 2 * W.H Q +
      W.wmax * C₀ * (Q ^ 2 + P.Y Q) * (∑ n ∈ P.range Q, P.aVec Q n ^ 2) / (2 * A)) ≤
      1 / Real.pi * (W.H Q * P.L Q * (η * Real.log Q / 2 + K₁ / η)) := by
    gcongr
    have h1 : W.wmax * C₀ * (Q ^ 2 + P.Y Q) * (∑ n ∈ P.range Q, P.aVec Q n ^ 2) ≤
        W.wmax * C₀ * (2 * (W.H Q / cH)) * (Ca * P.L Q ^ 3) := by
      gcongr
      linarith
    have h2 : W.wmax * C₀ * (2 * (W.H Q / cH)) * (Ca * P.L Q ^ 3) / (2 * A) =
        W.H Q * P.L Q * (K₁ / η) := by
      rw [hA, hK₁, hLdef]
      field_simp
    have h3 : W.wmax * C₀ * (Q ^ 2 + P.Y Q) * (∑ n ∈ P.range Q, P.aVec Q n ^ 2) / (2 * A) ≤
        W.H Q * P.L Q * (K₁ / η) := by
      rw [← h2]; gcongr
    have h4 : A / 2 * W.H Q = W.H Q * P.L Q * (η * Real.log Q / 2) := by rw [hA]; ring
    rw [h4, mul_add (W.H Q * P.L Q)]
    linarith
  have hstep : |MA P W Q T| ≤ K₂ * (W.H Q * T * P.L Q ^ 2) *
      (η * Real.log Q / 2 + K₁ / η) := by
    refine hmain.trans ?_
    have hBP0 : 0 ≤ 1 / Real.pi * (W.H Q * P.L Q * (η * Real.log Q / 2 + K₁ / η)) := by
      positivity
    calc R₀ * (1 / Real.pi * (A / 2 * W.H Q + W.wmax * C₀ * (Q ^ 2 + P.Y Q) *
          (∑ n ∈ P.range Q, P.aVec Q n ^ 2) / (2 * A))) * Dphi
        ≤ R₀ * (1 / Real.pi * (W.H Q * P.L Q * (η * Real.log Q / 2 + K₁ / η))) *
          ((2 * Real.pi * P.bInt + CJ) * (T * P.L Q)) := by
          gcongr
      _ = K₂ * (W.H Q * T * P.L Q ^ 2) * (η * Real.log Q / 2 + K₁ / η) := by
          rw [hK₂]; field_simp
  refine hstep.trans ?_
  -- `K₂ (η ℓ/2 + K₁/η) ≤ δ ℓ`
  have hc1 : K₂ * η ≤ δ / 2 := by
    have hK1 : 0 < K₂ + 1 := by linarith
    have e : K₂ * η = δ / 2 * (K₂ / (K₂ + 1)) := by
      rw [hη]; field_simp
    have hle : K₂ / (K₂ + 1) ≤ 1 := by
      rw [div_le_one hK1]; linarith
    rw [e]
    calc δ / 2 * (K₂ / (K₂ + 1)) ≤ δ / 2 * 1 := by gcongr
      _ = δ / 2 := by ring
  have hc2 : K₂ * (K₁ / η) ≤ δ / 4 * Real.log Q := by
    rw [div_le_iff₀ (by positivity : 0 < η * δ)] at hℓb
    have e : K₂ * (K₁ / η) = (4 * K₂ * K₁) / (4 * η) := by
      field_simp
    rw [e, div_le_iff₀ (by positivity)]
    calc 4 * K₂ * K₁ ≤ Real.log Q * (η * δ) := hℓb
      _ = δ / 4 * Real.log Q * (4 * η) := by ring
  have hc : K₂ * (η * Real.log Q / 2 + K₁ / η) ≤ δ * Real.log Q := by
    have e : K₂ * (η * Real.log Q / 2 + K₁ / η) = (K₂ * η) * Real.log Q / 2 + K₂ * (K₁ / η) := by
      ring
    have h5 : (K₂ * η) * Real.log Q / 2 ≤ δ / 2 * Real.log Q / 2 := by
      gcongr
    have h6 : 0 ≤ δ * Real.log Q := by positivity
    rw [e]
    linarith
  have hX0 : 0 ≤ W.H Q * T * P.L Q ^ 2 := by positivity
  unfold ell
  calc K₂ * (W.H Q * T * P.L Q ^ 2) * (η * Real.log Q / 2 + K₁ / η)
      = (W.H Q * T * P.L Q ^ 2) * (K₂ * (η * Real.log Q / 2 + K₁ / η)) := by ring
    _ ≤ (W.H Q * T * P.L Q ^ 2) * (δ * Real.log Q) := mul_le_mul_of_nonneg_left hc hX0
    _ = δ * (W.H Q * T * P.L Q ^ 2 * Real.log Q) := by ring

end MixSS

open MixSS in
/-- **`lem:muLambda`**: the mixed term is `o(H T L² ℓ)`, uniformly in `T`. -/
theorem Mmix_small (hMV : MV_LargeSieve) (hStir : StirlingDigamma) (hWH : lemWH_Statement) :
    ∀ (P : PrimeSetup) (W : Weight) (δ : ℝ), 0 < δ → ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
      ∀ T ∈ P.heights Q,
      |Mmix P W Q T| ≤ δ * (W.H Q * T * P.L Q ^ 2 * ell Q) := by
  intro P W δ hδ
  obtain ⟨QA, hA⟩ := MA_small hStir hMV hWH P W (δ / 2) (by positivity)
  obtain ⟨QB, hB⟩ := MB_small hMV hWH P W (δ / 2) (by positivity)
  refine ⟨max (max QA QB) 2, fun Q hQ T hT => ?_⟩
  have hQA : QA ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hQ
  have hQB : QB ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hQ
  have hQ2 : (2 : ℝ) ≤ Q := le_trans (le_max_right _ _) hQ
  rw [Mmix_split P W (by linarith) T]
  have h1 := hA Q hQA T hT
  have h2 := hB Q hQB T hT
  calc |MA P W Q T + MB P W Q T| ≤ |MA P W Q T| + |MB P W Q T| := abs_add_le _ _
    _ ≤ δ / 2 * (W.H Q * T * P.L Q ^ 2 * ell Q) + δ / 2 * (W.H Q * T * P.L Q ^ 2 * ell Q) :=
        add_le_add h1 h2
    _ = δ * (W.H Q * T * P.L Q ^ 2 * ell Q) := by ring

end Families.Ported.Second
