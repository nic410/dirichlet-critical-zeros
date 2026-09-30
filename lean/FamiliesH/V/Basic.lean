/-
# Theorem 1.4(a), package V: basic facts about `p(β; F_C)` (no `sorry`)

* `FC_mono_arg`: `F_C` is nondecreasing on `[0, ∞)` for `C ≥ 1`;
* `admissibleB_mono`, `admissibleB_window`: the admissible classes are nested in `β`, and for `β ≤ 2`
  an admissible window at support `β` is a `Families.AdmissibleWindow`;
* `unitW = 1_{[−1/2,1/2]}`: admissible at every support `β ≥ 1`, with `𝒬_{F_C}(unitW) ≤ 2`;
* `pB_bddBelow`, `pB_ge_of_admissible`;
* the dilation `dil a f (x) = a⁻¹ f(x/a)` (`a > 0`): admissible at support `aβ` when `f` is admissible at
  support `β`, with `∫ (dil a f)² = a⁻¹ ∫ f²` and
  `∬ dil a f(x) dil a f(y) F(|x−y|) = ∬ f(u) f(v) F(a|u−v|)` (`Qf_dil`).
-/
import FamiliesH.Glue

noncomputable section

open MeasureTheory Filter Topology

namespace Families.Hybrid.V

open Families

/-! ### The kernel `F_C` -/

/-- `F_C` is nondecreasing on `[0, ∞)` when `C ≥ 1`. -/
lemma FC_mono_arg {C : ℝ} (hC : 1 ≤ C) {a b : ℝ} (hab : a ≤ b) : FC C a ≤ FC C b := by
  unfold FC
  split_ifs with h1 h2 h2 <;> linarith

lemma FC_abs_le {C : ℝ} (hC : 1 ≤ C) : ∀ α, 0 ≤ α → |FC C α| ≤ C := by
  intro α hα
  obtain ⟨h0, h1⟩ := Families.Phase4.A.FC_bounds hC α hα
  rw [abs_of_nonneg h0]
  exact h1

/-! ### Admissible classes -/

/-- The admissible classes are nested: support `β'` inside support `β ≥ β'`. -/
lemma admissibleB_mono {β' β : ℝ} (h : β' ≤ β) {f : ℝ → ℝ} (hf : AdmissibleWindowB β' f) :
    AdmissibleWindowB β f where
  nonneg := hf.nonneg
  even := hf.even
  supp x hx := by
    have hx' := hf.supp x hx
    exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  memL2 := hf.memL2
  integral_eq_one := hf.integral_eq_one

/-- For `β ≤ 2`, an admissible window at support `β` is admissible in the sense of `Families`. -/
lemma admissibleB_window {β : ℝ} (hβ : β ≤ 2) {f : ℝ → ℝ} (hf : AdmissibleWindowB β f) :
    AdmissibleWindow f where
  nonneg := hf.nonneg
  even := hf.even
  supp x hx := by
    have hx' := hf.supp x hx
    exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  memL2 := hf.memL2
  integral_eq_one := hf.integral_eq_one

lemma integrable_of_admissibleB {β : ℝ} {f : ℝ → ℝ} (hf : AdmissibleWindowB β f) : Integrable f := by
  by_contra h
  have := integral_undef h
  rw [hf.integral_eq_one] at this
  exact one_ne_zero this

lemma admissibleB_supp {β : ℝ} {f : ℝ → ℝ} (hf : AdmissibleWindowB β f) :
    ∀ x, β / 2 < |x| → f x = 0 := by
  intro x hx
  by_contra h
  have h1 : |x| ≤ β / 2 := abs_le.2 ⟨by linarith [(hf.supp x h).1], (hf.supp x h).2⟩
  linarith

/-! ### The unit window `1_{[−1/2, 1/2]}` -/

/-- `unitW = 1_{[−1/2, 1/2]}`. -/
def unitW : ℝ → ℝ := (Set.Icc (-(1 / 2) : ℝ) (1 / 2)).indicator (fun _ => (1 : ℝ))

lemma unitW_nonneg (x : ℝ) : 0 ≤ unitW x := Set.indicator_nonneg (fun _ _ => zero_le_one) x

lemma unitW_le_one (x : ℝ) : unitW x ≤ 1 := by
  unfold unitW
  by_cases hx : x ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2)
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx]; norm_num

lemma unitW_eq_zero {x : ℝ} (hx : x ∉ Set.Icc (-(1 / 2) : ℝ) (1 / 2)) : unitW x = 0 := by
  unfold unitW; exact Set.indicator_of_notMem hx _

lemma integrable_unitW : Integrable unitW :=
  (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc

lemma integral_unitW : ∫ x, unitW x = 1 := by
  rw [unitW, integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le (by norm_num)]
  norm_num

/-- `unitW` is admissible at every support `β ≥ 1`. -/
lemma unitW_admissible {β : ℝ} (hβ : 1 ≤ β) : AdmissibleWindowB β unitW where
  nonneg := unitW_nonneg
  even x := by
    have h : (-x ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2)) ↔ (x ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2)) := by
      simp only [Set.mem_Icc]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    simp only [unitW, Set.indicator_apply, h]
  supp x hx := by
    have hx' : x ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2) := Set.mem_of_indicator_ne_zero hx
    exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  memL2 := memLp_indicator_const 2 measurableSet_Icc _ (Or.inr measure_Icc_lt_top.ne)
  integral_eq_one := integral_unitW

/-- `𝒬_{F_C}(unitW) ≤ 2`: on `[−1/2, 1/2]²` one has `|x − y| ≤ 1`, so `F_C(|x−y|) = |x−y| ≤ 1`. -/
lemma Qf_unitW_le {C : ℝ} (hC : 1 ≤ C) : Qf (FC C) unitW ≤ 2 := by
  have hFm := Families.Phase4.A.measurable_FC C
  have hK := FC_abs_le hC
  have hsq : ∫ x, unitW x ^ 2 = 1 := by
    have e : (fun x => unitW x ^ 2) = unitW := by
      funext x
      unfold unitW
      by_cases hx : x ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2)
      · rw [Set.indicator_of_mem hx]; norm_num
      · rw [Set.indicator_of_notMem hx]; norm_num
    rw [e, integral_unitW]
  have hpt : ∀ x y, unitW x * unitW y * FC C |x - y| ≤ unitW x * unitW y := by
    intro x y
    by_cases hx : x ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2)
    · by_cases hy : y ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2)
      · have hxy : |x - y| ≤ 1 := by
          rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
        have hF : FC C |x - y| ≤ 1 := by
          unfold FC; rw [if_pos hxy]; exact hxy
        have h0 : 0 ≤ unitW x * unitW y := mul_nonneg (unitW_nonneg x) (unitW_nonneg y)
        calc unitW x * unitW y * FC C |x - y| ≤ unitW x * unitW y * 1 :=
              mul_le_mul_of_nonneg_left hF h0
          _ = unitW x * unitW y := mul_one _
      · rw [unitW_eq_zero hy]; simp
    · rw [unitW_eq_zero hx]; simp
  have hinner : ∀ x, ∫ y, unitW x * unitW y * FC C |x - y| ≤ unitW x := by
    intro x
    calc ∫ y, unitW x * unitW y * FC C |x - y| ≤ ∫ y, unitW x * unitW y :=
          integral_mono (Families.Phase4.A.inner_integrable integrable_unitW hFm hK x)
            (integrable_unitW.const_mul _) (hpt x)
      _ = unitW x := by rw [integral_const_mul, integral_unitW, mul_one]
  have hdbl : (∫ x, ∫ y, unitW x * unitW y * FC C |x - y|) ≤ 1 := by
    calc (∫ x, ∫ y, unitW x * unitW y * FC C |x - y|) ≤ ∫ x, unitW x :=
          integral_mono (Families.Phase4.A.outer_integrable integrable_unitW integrable_unitW hFm hK)
            integrable_unitW hinner
      _ = 1 := integral_unitW
  unfold Qf
  linarith

/-! ### `p(β; F_C)` -/

lemma Qf_FC_nonneg_of {C : ℝ} (hC : 0 ≤ C) {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ Qf (FC C) f :=
  Families.Qf_FC_nonneg hC hf

lemma pB_bddBelow (β : ℝ) {C : ℝ} (hC : 0 ≤ C) :
    BddBelow (Qf (FC C) '' {f | AdmissibleWindowB β f}) :=
  ⟨0, by rintro _ ⟨g, hg, rfl⟩; exact Qf_FC_nonneg_of hC hg.nonneg⟩

lemma pB_nonempty {β : ℝ} (hβ : 1 ≤ β) (C : ℝ) :
    (Qf (FC C) '' {f | AdmissibleWindowB β f}).Nonempty :=
  ⟨_, unitW, unitW_admissible hβ, rfl⟩

/-- Any admissible window at support `β` gives `p(β; F_C) ≥ 2 − 𝒬_{F_C}(f)`. -/
lemma pB_ge_of_admissible {β C : ℝ} (hC : 0 ≤ C) {f : ℝ → ℝ} (hf : AdmissibleWindowB β f) :
    2 - Qf (FC C) f ≤ pB β C := by
  unfold pB
  have := csInf_le (pB_bddBelow β hC) ⟨f, hf, rfl⟩
  linarith

/-- For `β ≥ 1`, `C ≥ 1`: the infimum in `p(β; F_C)` is at most `2`. -/
lemma sInf_le_two {β C : ℝ} (hβ : 1 ≤ β) (hC : 1 ≤ C) :
    sInf (Qf (FC C) '' {f | AdmissibleWindowB β f}) ≤ 2 :=
  (csInf_le (pB_bddBelow β (by linarith)) ⟨unitW, unitW_admissible hβ, rfl⟩).trans (Qf_unitW_le hC)

/-! ### Dilation -/

/-- `dil a f (x) = a⁻¹ f(x/a)`. -/
def dil (a : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ := a⁻¹ * f (x / a)

lemma integral_dil {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ) : ∫ x, dil a f x = ∫ x, f x := by
  have h := Measure.integral_comp_div (fun u => a⁻¹ * f u) a
  show ∫ x, a⁻¹ * f (x / a) = _
  rw [h, abs_of_pos ha, smul_eq_mul, integral_const_mul, ← mul_assoc, mul_inv_cancel₀ ha.ne',
    one_mul]

lemma integral_sq_dil {a : ℝ} (ha : 0 < a) (f : ℝ → ℝ) :
    ∫ x, dil a f x ^ 2 = a⁻¹ * ∫ x, f x ^ 2 := by
  have e : (fun x => dil a f x ^ 2) = fun x => a⁻¹ ^ 2 * f (x / a) ^ 2 := by
    funext x; simp only [dil, mul_pow]
  have h := Measure.integral_comp_div (fun u => a⁻¹ ^ 2 * f u ^ 2) a
  rw [e, h, abs_of_pos ha, smul_eq_mul, integral_const_mul, ← mul_assoc]
  congr 1
  field_simp

lemma double_dil {a : ℝ} (ha : 0 < a) (f F : ℝ → ℝ) :
    (∫ x, ∫ y, dil a f x * dil a f y * F |x - y|) =
      ∫ u, ∫ v, f u * f v * F (a * |u - v|) := by
  have hinner : ∀ x, (∫ y, dil a f x * dil a f y * F |x - y|) =
      a⁻¹ * f (x / a) * ∫ v, f v * F |x - a * v| := by
    intro x
    have e : (fun y => dil a f x * dil a f y * F |x - y|) =
        fun y => a⁻¹ * (a⁻¹ * f (x / a)) * (f (y / a) * F |x - a * (y / a)|) := by
      funext y
      simp only [dil]
      rw [mul_div_cancel₀ y ha.ne']
      ring
    have h := Measure.integral_comp_div
      (fun v => a⁻¹ * (a⁻¹ * f (x / a)) * (f v * F |x - a * v|)) a
    rw [e, h, abs_of_pos ha, smul_eq_mul, integral_const_mul, ← mul_assoc,
      ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
  simp_rw [hinner]
  have e2 : (fun x => a⁻¹ * f (x / a) * ∫ v, f v * F |x - a * v|) =
      fun x => a⁻¹ * (f (x / a) * ∫ v, f v * F |a * (x / a) - a * v|) := by
    funext x
    rw [mul_div_cancel₀ x ha.ne']
    ring
  have h := Measure.integral_comp_div
    (fun u => a⁻¹ * (f u * ∫ v, f v * F |a * u - a * v|)) a
  rw [e2, h, abs_of_pos ha, smul_eq_mul, integral_const_mul, ← mul_assoc,
    mul_inv_cancel₀ ha.ne', one_mul]
  congr 1
  funext u
  rw [← integral_const_mul]
  congr 1
  funext v
  rw [← mul_sub, abs_mul, abs_of_pos ha]
  ring

/-- `𝒬_F(dil a f) = a⁻¹ ∫ f² + ∬ f(u) f(v) F(a|u−v|)`. -/
lemma Qf_dil {a : ℝ} (ha : 0 < a) (f F : ℝ → ℝ) :
    Qf F (dil a f) = a⁻¹ * (∫ x, f x ^ 2) + ∫ u, ∫ v, f u * f v * F (a * |u - v|) := by
  unfold Qf
  rw [integral_sq_dil ha, double_dil ha]

/-- The dilation of an admissible window at support `β` is admissible at support `aβ`. -/
lemma dil_admissible {a β : ℝ} (ha : 0 < a) {f : ℝ → ℝ} (hf : AdmissibleWindowB β f) :
    AdmissibleWindowB (a * β) (dil a f) where
  nonneg x := mul_nonneg (inv_nonneg.2 ha.le) (hf.nonneg _)
  even x := by
    simp only [dil]
    rw [neg_div, hf.even]
  supp x hx := by
    have hfx : f (x / a) ≠ 0 := by
      intro h; apply hx; simp [dil, h]
    obtain ⟨h1, h2⟩ := hf.supp (x / a) hfx
    have hx1 : x = a * (x / a) := by rw [mul_div_cancel₀ x ha.ne']
    constructor
    · rw [hx1]; nlinarith
    · rw [hx1]; nlinarith
  memL2 := by
    have hfi := integrable_of_admissibleB hf
    have hf2 : Integrable (fun x => f x ^ 2) := hf.memL2.integrable_sq
    have hm : AEStronglyMeasurable (dil a f) :=
      ((hfi.comp_div ha.ne').const_mul a⁻¹).aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq hm]
    have e : (fun x => dil a f x ^ 2) = fun x => a⁻¹ ^ 2 * f (x / a) ^ 2 := by
      funext x; simp only [dil, mul_pow]
    rw [e]
    exact (hf2.comp_div (g := fun u => f u ^ 2) ha.ne').const_mul _
  integral_eq_one := by rw [integral_dil ha, hf.integral_eq_one]

end Families.Hybrid.V
