/-
# Montgomery 1969 density: Gallagher's inequality

For a finite exponential sum `F(v) = ∑_j a_j e^{−i v ℓ_j}` and `W > 0`,
`∫_{−W}^{W} |F(v)|² dv ≤ (3π/4) W² ∫_ℝ |∑_{ℓ_j ∈ [u, u+2/W)} a_j|² du`.

Proof: the Fejér kernel. `∫ sinc²(πςw) e(wξ) dw = k₀(ξ)` (Fourier inversion of the project's
`fourier_k0`), `k₀` is a normalised convolution of two boxes, and `sinc²(πςw) ≥ 2/3` for `|w| ≤ W`
when `ς = 1/(πW)`.
-/
import Families.Phase1.B.Fejer

noncomputable section

open scoped BigOperators FourierTransform ComplexConjugate
open MeasureTheory Real Complex Finset

namespace Families.Hyp.Montgomery

open Families Families.Phase1.B

/-! ### `sinc²` is integrable -/

lemma sinc_sq_le_two_div (y : ℝ) : Real.sinc y ^ 2 ≤ 2 * (1 + y ^ 2)⁻¹ := by
  have h1 : Real.sinc y ^ 2 ≤ 1 := by
    have := Real.abs_sinc_le_one y
    have h0 : 0 ≤ |Real.sinc y| := abs_nonneg _
    nlinarith [sq_abs (Real.sinc y)]
  rcases le_or_gt (y ^ 2) 1 with hy | hy
  · have : 1 ≤ 2 * (1 + y ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]; linarith
    linarith
  · have hy0 : y ≠ 0 := by rintro rfl; norm_num at hy
    rw [Real.sinc_of_ne_zero hy0, div_pow]
    have hs : Real.sin y ^ 2 ≤ 1 := Real.sin_sq_le_one y
    have hpos : 0 < y ^ 2 := by positivity
    rw [div_le_iff₀ hpos, ← div_eq_mul_inv, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith

lemma integrable_sinc_sq {ς : ℝ} (hς : 0 < ς) :
    Integrable (fun w : ℝ => Real.sinc (π * ς * w) ^ 2) := by
  have hg : Integrable (fun w : ℝ => 2 * (1 + (π * ς * w) ^ 2)⁻¹) := by
    have := (integrable_inv_one_add_sq.comp_mul_left' (R := π * ς) (by positivity)).const_mul 2
    simpa [mul_comm, mul_assoc, mul_left_comm] using this
  refine hg.mono' ?_ ?_
  · exact (Real.continuous_sinc.comp (continuous_const.mul continuous_id)).pow 2
      |>.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun w => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sinc_sq_le_two_div _

lemma integrable_sinc_sq_C {ς : ℝ} (hς : 0 < ς) :
    Integrable (fun w : ℝ => ((Real.sinc (π * ς * w) ^ 2 : ℝ) : ℂ)) :=
  (integrable_sinc_sq hς).ofReal

lemma k0C_hasCompactSupport {ς : ℝ} (hς : 0 < ς) : HasCompactSupport (k0C ς) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -ς) (b := ς)) fun x hx => ?_
  apply k0C_eq_zero_of_le hς
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  rcases hx with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

/-- **Fourier inversion for the Fejér kernel**: `∫ sinc²(πςw) e(wξ) dw = k₀(ξ)`. -/
theorem integral_sinc_sq_mul_exp {ς : ℝ} (hς : 0 < ς) (ξ : ℝ) :
    ∫ w : ℝ, Complex.exp (((2 * π * w * ξ : ℝ) : ℂ) * Complex.I) *
      ((Real.sinc (π * ς * w) ^ 2 : ℝ) : ℂ) = (k0 ς ξ : ℂ) := by
  have hF : 𝓕 (k0C ς) = fun w => ((Real.sinc (π * ς * w) ^ 2 : ℝ) : ℂ) := by
    funext w; exact fourier_k0 hς w
  have hint : Integrable (k0C ς) :=
    (continuous_k0C ς).integrable_of_hasCompactSupport (k0C_hasCompactSupport hς)
  have hint' : Integrable (𝓕 (k0C ς)) := by rw [hF]; exact integrable_sinc_sq_C hς
  have hinv := congrFun ((continuous_k0C ς).fourierInv_fourier_eq hint hint') ξ
  rw [hF, fourierInv_eq'] at hinv
  simp only [k0C] at hinv
  rw [← hinv]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  simp only [smul_eq_mul]
  congr 3
  simp [mul_comm]
  ring

/-! ### Boxes -/

/-- The window indicator `1[u ≤ x < u + h]`. -/
def win (h u x : ℝ) : ℝ := if u ≤ x ∧ x < u + h then 1 else 0

lemma win_nonneg (h u x : ℝ) : 0 ≤ win h u x := by unfold win; split_ifs <;> norm_num

lemma win_le_one (h u x : ℝ) : win h u x ≤ 1 := by unfold win; split_ifs <;> norm_num

lemma win_eq_indicator (h x : ℝ) :
    (fun u => win h u x) = (Set.Ioc (x - h) x).indicator 1 := by
  funext u
  unfold win
  by_cases hu : u ≤ x ∧ x < u + h
  · rw [if_pos hu, Set.indicator_of_mem]; · rfl
    exact ⟨by linarith [hu.2], hu.1⟩
  · rw [if_neg hu, Set.indicator_of_notMem]
    rintro ⟨h1, h2⟩; exact hu ⟨h2, by linarith⟩

lemma win_mul_win_eq_indicator (h x y : ℝ) :
    (fun u => win h u x * win h u y) =
      (Set.Ioc (x - h) x ∩ Set.Ioc (y - h) y).indicator 1 := by
  funext u
  have e1 : win h u x = _ := congrFun (win_eq_indicator h x) u
  have e2 : win h u y = _ := congrFun (win_eq_indicator h y) u
  rw [e1, e2, Set.inter_indicator_one]
  rfl

/-- `∫ 1[u ≤ x < u+h] 1[u ≤ y < u+h] du = (h − |x − y|)_+`. -/
lemma integral_win_mul_win (h x y : ℝ) :
    ∫ u, win h u x * win h u y = max (h - |x - y|) 0 := by
  rw [win_mul_win_eq_indicator, integral_indicator_one (measurableSet_Ioc.inter measurableSet_Ioc),
    Set.Ioc_inter_Ioc, Real.volume_real_Ioc]
  congr 1
  rcases le_total x y with hxy | hxy
  · rw [max_eq_right (by linarith), min_eq_left hxy, abs_of_nonpos (by linarith)]; ring
  · rw [max_eq_left (by linarith), min_eq_right hxy, abs_of_nonneg (by linarith)]; ring

lemma integrable_win_mul_win (h x y : ℝ) : Integrable (fun u => win h u x * win h u y) := by
  rw [win_mul_win_eq_indicator]
  apply (integrable_indicator_iff (measurableSet_Ioc.inter measurableSet_Ioc)).2
  refine IntegrableOn.mono_set ?_ Set.inter_subset_left
  exact integrableOn_const (by simp)

/-! ### The Fejér identity for exponential sums -/

/-- `e^{−i v ℓ}`. -/
def ex (v ℓ : ℝ) : ℂ := Complex.exp (((-(v * ℓ) : ℝ) : ℂ) * Complex.I)

lemma norm_ex (v ℓ : ℝ) : ‖ex v ℓ‖ = 1 := Complex.norm_exp_ofReal_mul_I _

lemma continuous_ex (ℓ : ℝ) : Continuous (fun v => ex v ℓ) := by unfold ex; fun_prop

lemma ex_mul_conj_ex (v ℓ ℓ' : ℝ) :
    ex v ℓ * conj (ex v ℓ') =
      Complex.exp (((2 * π * v * ((ℓ' - ℓ) / (2 * π)) : ℝ) : ℂ) * Complex.I) := by
  unfold ex
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  push_cast
  field_simp
  ring

lemma integral_sinc_sq_ex_conj {ς : ℝ} (hς : 0 < ς) (ℓ ℓ' : ℝ) :
    ∫ v : ℝ, ((Real.sinc (π * ς * v) ^ 2 : ℝ) : ℂ) * (ex v ℓ * conj (ex v ℓ')) =
      ((k0 ς ((ℓ' - ℓ) / (2 * π)) : ℝ) : ℂ) := by
  rw [← integral_sinc_sq_mul_exp hς]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only
  rw [ex_mul_conj_ex, mul_comm]

lemma k0_eq_integral_win {ς : ℝ} (hς : 0 < ς) (ℓ ℓ' : ℝ) :
    k0 ς ((ℓ' - ℓ) / (2 * π)) =
      (ς * (2 * π * ς))⁻¹ * ∫ u, win (2 * π * ς) u ℓ * win (2 * π * ς) u ℓ' := by
  rw [integral_win_mul_win]
  unfold k0
  have hπ : 0 < π := Real.pi_pos
  have h2 : |(ℓ' - ℓ) / (2 * π)| / ς = |ℓ - ℓ'| / (2 * π * ς) := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * π), abs_sub_comm]
    field_simp
  rw [h2]
  have hh : 0 < 2 * π * ς := by positivity
  have : max (2 * π * ς - |ℓ - ℓ'|) 0 = (2 * π * ς) * max (1 - |ℓ - ℓ'| / (2 * π * ς)) 0 := by
    rw [mul_max_of_nonneg _ _ hh.le, mul_zero, mul_sub, mul_one, mul_div_cancel₀ _ hh.ne']
  rw [this]
  field_simp

lemma integrable_sinc_sq_mul {ς : ℝ} (hς : 0 < ς) {g : ℝ → ℂ} (hg : Continuous g) {M : ℝ}
    (hM : ∀ v, ‖g v‖ ≤ M) :
    Integrable (fun v : ℝ => ((Real.sinc (π * ς * v) ^ 2 : ℝ) : ℂ) * g v) := by
  refine ((integrable_sinc_sq hς).const_mul M).mono' ?_ ?_
  · exact ((Complex.continuous_ofReal.comp ((Real.continuous_sinc.comp
      (continuous_const.mul continuous_id)).pow 2)).mul hg).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun v => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_comm]
    exact mul_le_mul_of_nonneg_right (hM v) (sq_nonneg _)

lemma ofReal_norm_sq_eq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- **The Fejér identity**: `∫ sinc²(πςv) |∑ a_j e^{−ivℓ_j}|² dv
= (ς·2πς)⁻¹ ∫ |∑_{ℓ_j ∈ [u, u+2πς)} a_j|² du`. -/
theorem integral_sinc_sq_norm_sq {ι : Type*} (J : Finset ι) (a : ι → ℂ) (ℓ : ι → ℝ) {ς : ℝ}
    (hς : 0 < ς) :
    ∫ v : ℝ, Real.sinc (π * ς * v) ^ 2 * ‖∑ j ∈ J, a j * ex v (ℓ j)‖ ^ 2 =
      (ς * (2 * π * ς))⁻¹ *
        ∫ u : ℝ, ‖∑ j ∈ J, (win (2 * π * ς) u (ℓ j) : ℂ) * a j‖ ^ 2 := by
  set h := 2 * π * ς with hh
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul, ← integral_complex_ofReal, ← integral_complex_ofReal]
  -- left side as a double sum
  have hL : ∀ v : ℝ, (((Real.sinc (π * ς * v) ^ 2 * ‖∑ j ∈ J, a j * ex v (ℓ j)‖ ^ 2 : ℝ)) : ℂ) =
      ∑ j ∈ J, ∑ k ∈ J, a j * conj (a k) *
        (((Real.sinc (π * ς * v) ^ 2 : ℝ) : ℂ) * (ex v (ℓ j) * conj (ex v (ℓ k)))) := by
    intro v
    rw [Complex.ofReal_mul, ofReal_norm_sq_eq, map_sum, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul]; ring
  have hR : ∀ u : ℝ, (((‖∑ j ∈ J, (win h u (ℓ j) : ℂ) * a j‖ ^ 2 : ℝ)) : ℂ) =
      ∑ j ∈ J, ∑ k ∈ J, a j * conj (a k) * ((win h u (ℓ j) * win h u (ℓ k) : ℝ) : ℂ) := by
    intro u
    rw [ofReal_norm_sq_eq, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, Complex.conj_ofReal]; push_cast; ring
  simp_rw [hL, hR]
  have hintL : ∀ j k, Integrable (fun v : ℝ => a j * conj (a k) *
      (((Real.sinc (π * ς * v) ^ 2 : ℝ) : ℂ) * (ex v (ℓ j) * conj (ex v (ℓ k))))) := by
    intro j k
    refine (integrable_sinc_sq_mul hς (M := 1)
      ((continuous_ex (ℓ j)).mul (Complex.continuous_conj.comp (continuous_ex (ℓ k)))) ?_).const_mul _
    intro v
    simp only [Pi.mul_apply, Function.comp_apply]
    rw [norm_mul, Complex.norm_conj, norm_ex, norm_ex, one_mul]
  have hintR : ∀ j k, Integrable (fun u : ℝ => a j * conj (a k) *
      ((win h u (ℓ j) * win h u (ℓ k) : ℝ) : ℂ)) :=
    fun j k => (integrable_win_mul_win h (ℓ j) (ℓ k)).ofReal.const_mul _
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun k _ => hintL j k),
    integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun k _ => hintR j k),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ (fun k _ => hintL j k),
    integral_finsetSum _ (fun k _ => hintR j k), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, integral_const_mul, integral_sinc_sq_ex_conj hς,
    k0_eq_integral_win hς, integral_complex_ofReal]
  simp only [hh]
  push_cast
  ring

/-- **Gallagher's inequality**: `∫_{−W}^{W} |∑ a_j e^{−ivℓ_j}|² dv
≤ (3π/4) W² ∫ |∑_{ℓ_j ∈ [u, u+2/W)} a_j|² du`. -/
theorem gallagher {ι : Type*} (J : Finset ι) (a : ι → ℂ) (ℓ : ι → ℝ) {W : ℝ} (hW : 0 < W) :
    ∫ v in (-W)..W, ‖∑ j ∈ J, a j * ex v (ℓ j)‖ ^ 2 ≤
      (3 * π / 4) * W ^ 2 * ∫ u : ℝ, ‖∑ j ∈ J, (win (2 / W) u (ℓ j) : ℂ) * a j‖ ^ 2 := by
  have hπ : 0 < π := Real.pi_pos
  set ς : ℝ := 1 / (π * W) with hςdef
  have hς : 0 < ς := by positivity
  have hid := integral_sinc_sq_norm_sq J a ℓ hς
  have h2 : 2 * π * ς = 2 / W := by rw [hςdef]; field_simp
  rw [h2] at hid
  have hconst : (ς * (2 / W))⁻¹ = π * W ^ 2 / 2 := by rw [hςdef]; field_simp
  rw [hconst] at hid
  set F : ℝ → ℝ := fun v => ‖∑ j ∈ J, a j * ex v (ℓ j)‖ ^ 2 with hF
  have hFc : Continuous F := by
    rw [hF]; exact (continuous_finsetSum _ fun j _ =>
      continuous_const.mul (continuous_ex (ℓ j))).norm.pow 2
  set M : ℝ := (∑ j ∈ J, ‖a j‖) ^ 2 with hM
  have hFb : ∀ v, F v ≤ M := by
    intro v
    rw [hF, hM]
    refine pow_le_pow_left₀ (norm_nonneg _) ((norm_sum_le _ _).trans (le_of_eq ?_)) 2
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [norm_mul, norm_ex, mul_one]
  have hG : Integrable (fun v : ℝ => Real.sinc (π * ς * v) ^ 2 * F v) := by
    refine ((integrable_sinc_sq hς).mul_const M).mono' ?_ ?_
    · exact (((Real.continuous_sinc.comp (continuous_const.mul continuous_id)).pow 2).mul
        hFc).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun v => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_left (hFb v) (sq_nonneg _)
  have hstep1 : ∫ v in (-W)..W, F v ≤ ∫ v in (-W)..W, (3 / 2) * (Real.sinc (π * ς * v) ^ 2 * F v) := by
    refine intervalIntegral.integral_mono_on (by linarith) (hFc.intervalIntegrable _ _)
      ((hG.const_mul (3 / 2)).intervalIntegrable) fun v hv => ?_
    have hy : (π * ς * v) ^ 2 ≤ 1 := by
      have : π * ς * v = v / W := by rw [hςdef]; field_simp
      rw [this, div_pow, div_le_one (by positivity)]
      exact sq_le_sq' (by linarith [hv.1]) hv.2
    have hs := sinc_sq_ge (y := π * ς * v) (by linarith)
    have hF0 : 0 ≤ F v := sq_nonneg _
    nlinarith
  have hstep2 : ∫ v in (-W)..W, (3 / 2) * (Real.sinc (π * ς * v) ^ 2 * F v) ≤
      ∫ v : ℝ, (3 / 2) * (Real.sinc (π * ς * v) ^ 2 * F v) := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact setIntegral_le_integral (hG.const_mul _) (Filter.Eventually.of_forall fun v =>
      mul_nonneg (by norm_num) (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  calc ∫ v in (-W)..W, F v ≤ ∫ v : ℝ, (3 / 2) * (Real.sinc (π * ς * v) ^ 2 * F v) :=
        hstep1.trans hstep2
    _ = (3 / 2) * ∫ v : ℝ, Real.sinc (π * ς * v) ^ 2 * F v := integral_const_mul _ _
    _ = _ := by rw [hid]; ring

end Families.Hyp.Montgomery
