/-
The auxiliary smooth cut-offs of `PrimeSetup` (`main.tex` §2.3), constructed
explicitly, so that `PrimeSetup` is inhabited for every admissible choice of the numerical data.

* `upsilon0 ε₁`: smooth, `[0,1]`-valued, `= 1` on `[0,1]`, `= 0` on `(1+ε₁, ∞)` (the cut-off `Υ₀`);
* `dyadic j`: a smooth dyadic partition of unity `ψ_j(y) = h(y/2^j)`, `h(t) = η₀(t) − η₀(2t)`,
  `η₀(t) = S(2 − t)` (`S` = `Real.smoothTransition`): `ψ_j ≥ 0`, `supp ψ_j ⊂ [2^j/2, 2·2^j]`,
  `∑_j ψ_j = 1` on `[1, ∞)` (telescoping), `|ψ_j^{(i)}| ≤ c_i 2^{−ij}`.
-/
import Mathlib

noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace Families.Phase4.A

/-! ### The prime cut-off `Υ₀` -/

/-- `Υ₀(y) = S((1 + ε₁ − y)/ε₁)`. -/
def upsilon0 (ε₁ y : ℝ) : ℝ := Real.smoothTransition ((1 + ε₁ - y) / ε₁)

lemma upsilon0_contDiff (ε₁ : ℝ) : ContDiff ℝ ∞ (upsilon0 ε₁) := by
  unfold upsilon0
  exact Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const _)

lemma upsilon0_range (ε₁ y : ℝ) : 0 ≤ upsilon0 ε₁ y ∧ upsilon0 ε₁ y ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

lemma upsilon0_one {ε₁ : ℝ} (hε₁ : 0 < ε₁) {y : ℝ} (hy : y ≤ 1) : upsilon0 ε₁ y = 1 := by
  unfold upsilon0
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ hε₁]; linarith

lemma upsilon0_zero {ε₁ : ℝ} (hε₁ : 0 < ε₁) {y : ℝ} (hy : 1 + ε₁ < y) : upsilon0 ε₁ y = 0 := by
  unfold upsilon0
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) hε₁.le

/-! ### The dyadic partition of unity `(ψ_j)` -/

/-- `η₀(t) = S(2 − t)`: `1` for `t ≤ 1`, `0` for `t ≥ 2`. -/
def eta0 (t : ℝ) : ℝ := Real.smoothTransition (2 - t)

/-- `h(t) = η₀(t) − η₀(2t)`, supported in `[1/2, 2]`. -/
def hbump (t : ℝ) : ℝ := eta0 t - eta0 (2 * t)

/-- `ψ_j(y) = h(2^{−j} y)`. -/
def dyadic (j : ℕ) (y : ℝ) : ℝ := hbump (((2 : ℝ) ^ j)⁻¹ * y)

lemma eta0_contDiff : ContDiff ℝ ∞ eta0 :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

lemma hbump_contDiff : ContDiff ℝ ∞ hbump :=
  eta0_contDiff.sub (eta0_contDiff.comp (contDiff_const.mul contDiff_id))

lemma dyadic_contDiff (j : ℕ) : ContDiff ℝ ∞ (dyadic j) :=
  hbump_contDiff.comp (contDiff_const.mul contDiff_id)

lemma eta0_of_le_one {t : ℝ} (ht : t ≤ 1) : eta0 t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma eta0_of_two_le {t : ℝ} (ht : 2 ≤ t) : eta0 t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma hbump_nonneg (t : ℝ) : 0 ≤ hbump t := by
  unfold hbump
  rcases le_or_gt 0 t with ht | ht
  · have : eta0 (2 * t) ≤ eta0 t := Real.smoothTransition.monotone (by linarith)
    linarith
  · rw [eta0_of_le_one (by linarith), eta0_of_le_one (by linarith)]; simp

lemma hbump_of_lt {t : ℝ} (ht : t < 1 / 2) : hbump t = 0 := by
  unfold hbump
  rw [eta0_of_le_one (by linarith), eta0_of_le_one (by linarith)]; simp

lemma hbump_of_gt {t : ℝ} (ht : 2 < t) : hbump t = 0 := by
  unfold hbump
  rw [eta0_of_two_le (by linarith), eta0_of_two_le (by linarith)]; simp

lemma hbump_hasCompactSupport : HasCompactSupport hbump := by
  refine HasCompactSupport.intro (isCompact_Icc (a := 1 / 2) (b := 2)) fun t ht => ?_
  simp only [Set.mem_Icc, not_and_or, not_le] at ht
  rcases ht with ht | ht
  · exact hbump_of_lt ht
  · exact hbump_of_gt ht

lemma dyadic_nonneg (j : ℕ) (y : ℝ) : 0 ≤ dyadic j y := hbump_nonneg _

lemma dyadic_supp (j : ℕ) (y : ℝ) (h : dyadic j y ≠ 0) :
    (2 : ℝ) ^ j / 2 ≤ y ∧ y ≤ 2 * 2 ^ j := by
  have hp : (0 : ℝ) < 2 ^ j := by positivity
  by_contra hc
  rw [not_and_or, not_le, not_le] at hc
  apply h
  rcases hc with hc | hc
  · apply hbump_of_lt
    rw [inv_mul_eq_div, div_lt_iff₀ hp]; linarith
  · apply hbump_of_gt
    rw [inv_mul_eq_div, lt_div_iff₀ hp]; linarith

/-- `ψ_j(y) = a(j+1) − a(j)` with `a(j) = η₀(2^{1−j} y)`. -/
lemma dyadic_eq_sub (j : ℕ) (y : ℝ) :
    dyadic j y = eta0 (2 * ((2 : ℝ) ^ (j + 1))⁻¹ * y) - eta0 (2 * ((2 : ℝ) ^ j)⁻¹ * y) := by
  unfold dyadic hbump
  have : 2 * ((2 : ℝ) ^ (j + 1))⁻¹ * y = ((2 : ℝ) ^ j)⁻¹ * y := by
    rw [pow_succ]; field_simp
  rw [this, mul_assoc]

lemma dyadic_sum {y : ℝ} (hy : 1 ≤ y) : ∑' j, dyadic j y = 1 := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (2 * y) (by norm_num : (1 : ℝ) < 2)
  have hvan : ∀ j ∉ Finset.range N, dyadic j y = 0 := by
    intro j hj
    rw [Finset.mem_range, not_lt] at hj
    apply hbump_of_lt
    have hp : (0 : ℝ) < 2 ^ j := by positivity
    have hNj : (2 : ℝ) ^ N ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
    rw [inv_mul_eq_div, div_lt_iff₀ hp]; linarith
  rw [tsum_eq_sum hvan]
  simp_rw [dyadic_eq_sub]
  rw [Finset.sum_range_sub (fun j => eta0 (2 * ((2 : ℝ) ^ j)⁻¹ * y)) N]
  have hp : (0 : ℝ) < 2 ^ N := by positivity
  rw [eta0_of_le_one, eta0_of_two_le]
  · simp
  · simp; linarith
  · rw [mul_assoc, inv_mul_eq_div, ← mul_div_assoc, div_le_one hp]; linarith

lemma hbump_iteratedDeriv_bounded (i : ℕ) : ∃ C : ℝ, ∀ t, |iteratedDeriv i hbump t| ≤ C := by
  have hc : Continuous (iteratedFDeriv ℝ i hbump) :=
    hbump_contDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support (hbump_hasCompactSupport.iteratedFDeriv i)
  refine ⟨C, fun t => ?_⟩
  rw [← Real.norm_eq_abs, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact hC t

lemma dyadic_deriv (i : ℕ) :
    ∃ C : ℝ, ∀ j y, |iteratedDeriv i (dyadic j) y| ≤ C * ((2 : ℝ) ^ j)⁻¹ ^ i := by
  obtain ⟨C, hC⟩ := hbump_iteratedDeriv_bounded i
  refine ⟨C, fun j y => ?_⟩
  have h := iteratedDeriv_comp_const_mul (n := i) (hbump_contDiff.of_le (by exact_mod_cast le_top))
    ((2 : ℝ) ^ j)⁻¹
  have e : dyadic j = fun y => hbump (((2 : ℝ) ^ j)⁻¹ * y) := rfl
  rw [e, h, abs_mul, abs_of_nonneg (by positivity)]
  have hp : (0 : ℝ) ≤ ((2 : ℝ) ^ j)⁻¹ ^ i := by positivity
  calc ((2 : ℝ) ^ j)⁻¹ ^ i * |iteratedDeriv i hbump (((2 : ℝ) ^ j)⁻¹ * y)|
      ≤ ((2 : ℝ) ^ j)⁻¹ ^ i * C := mul_le_mul_of_nonneg_left (hC _) hp
    _ = C * ((2 : ℝ) ^ j)⁻¹ ^ i := mul_comm _ _

end Families.Phase4.A
