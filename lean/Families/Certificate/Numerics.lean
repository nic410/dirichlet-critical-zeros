/-
`prop:cert` (main.tex §7.2): the exact rational certificates
  `p(1) ≥ 0.932282` and `p(1.2688) ≥ 0.885912`
from the explicit even step functions of `paper/cert/certify.py` (n = 400 cells, heights at scale 1e9).

Structure of the proof (fully formal, no `sorry`, no `native_decide`):
* `pC_ge_of_admissible`: any admissible window `f` gives `p(C) ≥ 2 − 𝒬_{F_C}(f)`.
* `G1`, `Gfun`: explicit antiderivatives of `t ↦ F_C(|t|)` (`G₁' = F_C(|·|)` off `{-1,0,1}`,
  `G' = G₁` off `{-1,0,1}`); FTC with countably many exceptional points gives the exact cell-pair
  integral `∫_{I_i}∫_{I_j} F_C(|x−y|) = G(d+h) − 2G(d) + G(d−h)` (`outer_cell_integral`).
* `Qf_stepFn`: for any grid step function (closed cells), `𝒬_{F_C}(f) = h∑c_i² + ∑_{i,j} c_i c_j κ_{i−j}`.
* `window ms`: the certificate window (400 closed cells of width 1/200, heights `m_i/(h∑m)`);
  it is exactly even (`stepFn_neg`, from `ms.reverse = ms`), supported in `[-1,1]`, in `L²`, of mass 1.
* `Qf_window`, `Qf_window_le`: `𝒬` equals an explicit rational built from the integer data; the
  denominator-cleared inequality is `CertData.cert1` / `cert2`, checked by `decide +kernel`
  in `Families.Certificate.Data`.
-/
import Families.Variational
import Families.Certificate.Data

noncomputable section

open MeasureTheory Set

namespace Families

lemma FC_nonneg {C : ℝ} (hC : 0 ≤ C) {α : ℝ} (hα : 0 ≤ α) : 0 ≤ FC C α := by
  unfold FC; split_ifs <;> assumption

lemma Qf_FC_nonneg {C : ℝ} (hC : 0 ≤ C) {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ Qf (FC C) f := by
  unfold Qf
  refine add_nonneg (integral_nonneg fun x => sq_nonneg _) (integral_nonneg fun x => ?_)
  exact integral_nonneg fun y => mul_nonneg (mul_nonneg (hf x) (hf y)) (FC_nonneg hC (abs_nonneg _))

/-- Any admissible window gives a lower bound for `p(C)` (`C ≥ 0`). -/
theorem pC_ge_of_admissible {C : ℝ} (hC : 0 ≤ C) {f : ℝ → ℝ} (hf : AdmissibleWindow f) :
    2 - Qf (FC C) f ≤ pC C := by
  unfold pC
  have hbdd : BddBelow (Qf (FC C) '' {f | AdmissibleWindow f}) :=
    ⟨0, by rintro _ ⟨g, hg, rfl⟩; exact Qf_FC_nonneg hC hg.nonneg⟩
  have := csInf_le hbdd ⟨f, hf, rfl⟩
  linarith

/-! ### The antiderivatives `G₁ = G'` and `G` of `t ↦ F_C(|t|)` -/

/-- `G₁(t) = t|t|/2` for `|t| ≤ 1`, `sign(t)(1/2 + C(|t|-1))` for `|t| > 1` (written so that the
second branch is continuous everywhere). -/
def G1 (C t : ℝ) : ℝ := if |t| ≤ 1 then t * |t| / 2 else C * t - (C - 1 / 2) * t / max |t| 1

/-- `G(t) = |t|³/6` for `|t| ≤ 1`, `1/6 + (|t|-1)/2 + C(|t|-1)²/2` for `|t| > 1`. -/
def Gfun (C t : ℝ) : ℝ := if |t| ≤ 1 then |t| ^ 3 / 6 else 1 / 6 + (|t| - 1) / 2 + C * (|t| - 1) ^ 2 / 2

lemma continuous_G1 (C : ℝ) : Continuous (G1 C) := by
  unfold G1
  refine Continuous.if_le ?_ ?_ continuous_abs continuous_const ?_
  · fun_prop
  · refine Continuous.sub (by fun_prop) (Continuous.div (by fun_prop) (by fun_prop) ?_)
    intro x; exact (lt_of_lt_of_le one_pos (le_max_right _ _)).ne'
  · intro x hx
    rw [hx, max_eq_left le_rfl]; ring

lemma continuous_Gfun (C : ℝ) : Continuous (Gfun C) := by
  unfold Gfun
  refine Continuous.if_le (by fun_prop) (by fun_prop) continuous_abs continuous_const ?_
  intro x hx; rw [hx]; ring

lemma measurable_FC_abs (C : ℝ) : Measurable (fun t : ℝ => FC C |t|) := by
  unfold FC
  exact Measurable.ite (measurableSet_le measurable_abs measurable_const) measurable_abs
    measurable_const

lemma abs_le_of_mem_uIcc {t u v : ℝ} (ht : t ∈ uIcc u v) : |t| ≤ |u| + |v| := by
  rw [mem_uIcc] at ht
  have hu1 := neg_abs_le u; have hu2 := le_abs_self u
  have hv1 := neg_abs_le v; have hv2 := le_abs_self v
  have := abs_nonneg u; have := abs_nonneg v
  rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma abs_FC_abs_le (C t M : ℝ) (hM : |t| ≤ M) : abs (FC C |t|) ≤ M + |C| := by
  unfold FC
  split_ifs
  · rw [abs_abs]; linarith [abs_nonneg C]
  · linarith [abs_nonneg t]

lemma intervalIntegrable_FC_abs (C u v : ℝ) :
    IntervalIntegrable (fun t : ℝ => FC C |t|) volume u v := by
  rw [intervalIntegrable_iff]
  refine Measure.integrableOn_of_bounded (M := (|u| + |v|) + |C|) ?_
    (measurable_FC_abs C).aestronglyMeasurable ?_
  · exact ((measure_mono uIoc_subset_uIcc).trans_lt (by simp [uIcc])).ne
  · rw [ae_restrict_iff' measurableSet_uIoc]
    refine Filter.Eventually.of_forall fun t ht => ?_
    rw [Real.norm_eq_abs]
    exact abs_FC_abs_le C t _ (abs_le_of_mem_uIcc (uIoc_subset_uIcc ht))

/-- Local derivative lemma: equality with a function on an open set containing `t`. -/
lemma hasDerivAt_of_eqOn_open {f g : ℝ → ℝ} {g' : ℝ} {s : Set ℝ} {t : ℝ} (hs : IsOpen s)
    (ht : t ∈ s) (heq : EqOn f g s) (hg : HasDerivAt g g' t) : HasDerivAt f g' t :=
  hg.congr_of_eventuallyEq (Filter.eventually_of_mem (hs.mem_nhds ht) fun _ hx => heq hx)

lemma hd_quad (a b c t : ℝ) : HasDerivAt (fun s => a * s * s + b * s + c) (2 * a * t + b) t := by
  have h1 : HasDerivAt (fun s : ℝ => a * s) (a * 1) t := (hasDerivAt_id' t).const_mul a
  have h2 := ((h1.mul (hasDerivAt_id' t)).add ((hasDerivAt_id' t).const_mul b)).add_const c
  exact h2.congr_deriv (by ring)

lemma hd_cubic (a t : ℝ) : HasDerivAt (fun s => a * s * s * s) (3 * a * t * t) t := by
  have h1 : HasDerivAt (fun s : ℝ => a * s) (a * 1) t := (hasDerivAt_id' t).const_mul a
  have h2 : HasDerivAt (fun s : ℝ => a * s * s) (a * 1 * t + a * t * 1) t :=
    h1.mul (hasDerivAt_id' t)
  have h3 : HasDerivAt (fun s : ℝ => a * s * s * s) ((a * 1 * t + a * t * 1) * t + a * t * t * 1) t :=
    h2.mul (hasDerivAt_id' t)
  exact h3.congr_deriv (by ring)

lemma hasDerivAt_G1 (C t : ℝ) (h1 : t ≠ -1) (h0 : t ≠ 0) (h2 : t ≠ 1) :
    HasDerivAt (G1 C) (FC C |t|) t := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · rcases lt_or_gt_of_ne h1 with ht1 | ht1
    · -- t < -1
      have hF : FC C |t| = C := by
        unfold FC; rw [if_neg]; rw [abs_of_neg ht]; linarith
      rw [hF]
      refine (hasDerivAt_of_eqOn_open isOpen_Iio (show t ∈ Iio (-1) from ht1) ?_
        (hd_quad 0 C (C - 1 / 2) t)).congr_deriv (by ring)
      intro s hs
      simp only [mem_Iio] at hs
      have hs0 : s < 0 := by linarith
      unfold G1
      rw [if_neg (by rw [abs_of_neg hs0]; linarith), abs_of_neg hs0,
        max_eq_left (by linarith), div_neg, mul_div_assoc, div_self hs0.ne]
      ring
    · -- -1 < t < 0
      have hF : FC C |t| = -t := by
        unfold FC; rw [if_pos (by rw [abs_of_neg ht]; linarith), abs_of_neg ht]
      rw [hF]
      refine (hasDerivAt_of_eqOn_open isOpen_Ioo (show t ∈ Ioo (-1) 0 from ⟨ht1, ht⟩) ?_
        (hd_quad (-1 / 2) 0 0 t)).congr_deriv (by ring)
      intro s hs
      simp only [mem_Ioo] at hs
      unfold G1
      rw [if_pos (by rw [abs_of_neg hs.2]; linarith), abs_of_neg hs.2]
      ring
  · exact absurd ht h0
  · rcases lt_or_gt_of_ne h2 with ht1 | ht1
    · -- 0 < t < 1
      have hF : FC C |t| = t := by
        unfold FC; rw [if_pos (by rw [abs_of_pos ht]; linarith), abs_of_pos ht]
      rw [hF]
      refine (hasDerivAt_of_eqOn_open isOpen_Ioo (show t ∈ Ioo 0 1 from ⟨ht, ht1⟩) ?_
        (hd_quad (1 / 2) 0 0 t)).congr_deriv (by ring)
      intro s hs
      simp only [mem_Ioo] at hs
      unfold G1
      rw [if_pos (by rw [abs_of_pos hs.1]; linarith), abs_of_pos hs.1]
      ring
    · -- t > 1
      have hF : FC C |t| = C := by
        unfold FC; rw [if_neg]; rw [abs_of_pos ht]; linarith
      rw [hF]
      refine (hasDerivAt_of_eqOn_open isOpen_Ioi (show t ∈ Ioi 1 from ht1) ?_
        (hd_quad 0 C (-(C - 1 / 2)) t)).congr_deriv (by ring)
      intro s hs
      simp only [mem_Ioi] at hs
      have hs0 : 0 < s := by linarith
      unfold G1
      rw [if_neg (by rw [abs_of_pos hs0]; linarith), abs_of_pos hs0,
        max_eq_left (by linarith), mul_div_assoc, div_self hs0.ne']
      ring

lemma hasDerivAt_Gfun (C t : ℝ) (h1 : t ≠ -1) (h0 : t ≠ 0) (h2 : t ≠ 1) :
    HasDerivAt (Gfun C) (G1 C t) t := by
  rcases lt_trichotomy t 0 with ht | ht | ht
  · rcases lt_or_gt_of_ne h1 with ht1 | ht1
    · -- t < -1
      have hG : G1 C t = C * t + (C - 1 / 2) := by
        unfold G1
        rw [if_neg (by rw [abs_of_neg ht]; linarith), abs_of_neg ht, max_eq_left (by linarith),
          div_neg, mul_div_assoc, div_self ht.ne]
        ring
      rw [hG]
      refine (hasDerivAt_of_eqOn_open isOpen_Iio (show t ∈ Iio (-1) from ht1) ?_
        (hd_quad (C / 2) (C - 1 / 2) (C / 2 - 1 / 3) t)).congr_deriv (by ring)
      intro s hs
      simp only [mem_Iio] at hs
      have hs0 : s < 0 := by linarith
      unfold Gfun
      rw [if_neg (by rw [abs_of_neg hs0]; linarith), abs_of_neg hs0]
      ring
    · -- -1 < t < 0
      have hG : G1 C t = -(t ^ 2) / 2 := by
        unfold G1
        rw [if_pos (by rw [abs_of_neg ht]; linarith), abs_of_neg ht]; ring
      rw [hG]
      refine (hasDerivAt_of_eqOn_open isOpen_Ioo (show t ∈ Ioo (-1) 0 from ⟨ht1, ht⟩) ?_
        (hd_cubic (-1 / 6) t)).congr_deriv (by ring)
      intro s hs
      simp only [mem_Ioo] at hs
      unfold Gfun
      rw [if_pos (by rw [abs_of_neg hs.2]; linarith), abs_of_neg hs.2]
      ring
  · exact absurd ht h0
  · rcases lt_or_gt_of_ne h2 with ht1 | ht1
    · -- 0 < t < 1
      have hG : G1 C t = t ^ 2 / 2 := by
        unfold G1
        rw [if_pos (by rw [abs_of_pos ht]; linarith), abs_of_pos ht]; ring
      rw [hG]
      refine (hasDerivAt_of_eqOn_open isOpen_Ioo (show t ∈ Ioo 0 1 from ⟨ht, ht1⟩) ?_
        (hd_cubic (1 / 6) t)).congr_deriv (by ring)
      intro s hs
      simp only [mem_Ioo] at hs
      unfold Gfun
      rw [if_pos (by rw [abs_of_pos hs.1]; linarith), abs_of_pos hs.1]
      ring
    · -- t > 1
      have hG : G1 C t = C * t - (C - 1 / 2) := by
        unfold G1
        rw [if_neg (by rw [abs_of_pos ht]; linarith), abs_of_pos ht, max_eq_left (by linarith),
          mul_div_assoc, div_self ht.ne']
        ring
      rw [hG]
      refine (hasDerivAt_of_eqOn_open isOpen_Ioi (show t ∈ Ioi 1 from ht1) ?_
        (hd_quad (C / 2) (1 / 2 - C) (C / 2 - 1 / 3) t)).congr_deriv (by ring)
      intro s hs
      simp only [mem_Ioi] at hs
      have hs0 : 0 < s := by linarith
      unfold Gfun
      rw [if_neg (by rw [abs_of_pos hs0]; linarith), abs_of_pos hs0]
      ring

lemma countable_breaks : ({-1, 0, 1} : Set ℝ).Countable := by
  simp only [countable_insert, countable_singleton]

/-- FTC: `∫_u^v F_C(|t|) dt = G₁(v) - G₁(u)`. -/
lemma integral_FC_abs (C u v : ℝ) : ∫ t in u..v, FC C |t| = G1 C v - G1 C u := by
  refine integral_eq_of_hasDerivAt_off_countable (G1 C) (fun t => FC C |t|) countable_breaks
    (continuous_G1 C).continuousOn ?_ (intervalIntegrable_FC_abs C u v)
  intro t ht
  have hts : t ∉ ({-1, 0, 1} : Set ℝ) := ht.2
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hts
  exact hasDerivAt_G1 C t hts.1 hts.2.1 hts.2.2

/-- FTC: `∫_u^v G₁(t) dt = G(v) - G(u)`. -/
lemma integral_G1 (C u v : ℝ) : ∫ t in u..v, G1 C t = Gfun C v - Gfun C u := by
  refine integral_eq_of_hasDerivAt_off_countable (Gfun C) (G1 C) countable_breaks
    (continuous_Gfun C).continuousOn ?_ ((continuous_G1 C).intervalIntegrable u v)
  intro t ht
  have hts : t ∉ ({-1, 0, 1} : Set ℝ) := ht.2
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hts
  exact hasDerivAt_Gfun C t hts.1 hts.2.1 hts.2.2

/-- The inner integral: `∫_b^{b+h} F_C(|x-y|) dy = G₁(x-b) - G₁(x-b-h)`. -/
lemma inner_cell_integral (C x b h : ℝ) :
    ∫ y in b..b + h, FC C |x - y| = G1 C (x - b) - G1 C (x - (b + h)) := by
  rw [intervalIntegral.integral_comp_sub_left (fun t => FC C |t|) x, integral_FC_abs]

/-- The outer integral: `∫_a^{a+h} (G₁(x-b) - G₁(x-b-h)) dx = G(d+h) - 2G(d) + G(d-h)`, `d = a-b`. -/
lemma outer_cell_integral (C a b h : ℝ) :
    ∫ x in a..a + h, (G1 C (x - b) - G1 C (x - (b + h)))
      = Gfun C (a - b + h) - 2 * Gfun C (a - b) + Gfun C (a - b - h) := by
  have i1 : IntervalIntegrable (fun x => G1 C (x - b)) volume a (a + h) :=
    ((continuous_G1 C).comp (continuous_sub_right b)).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun x => G1 C (x - (b + h))) volume a (a + h) :=
    ((continuous_G1 C).comp (continuous_sub_right (b + h))).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub i1 i2]
  rw [intervalIntegral.integral_comp_sub_right (G1 C) b,
    intervalIntegral.integral_comp_sub_right (G1 C) (b + h), integral_G1, integral_G1]
  ring_nf

/-! ### Step functions on a grid -/

/-- The closed cell `[a + ih, a + ih + h]`. -/
def cell (a h : ℝ) (i : ℕ) : Set ℝ := Icc (a + i * h) (a + i * h + h)

/-- The step function `∑_{i<N} c_i 1_{cell i}` (closed cells; they overlap only at grid points). -/
def stepFn (a h : ℝ) (N : ℕ) (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range N, (cell a h i).indicator (fun _ => c i) x

lemma measurableSet_cell (a h : ℝ) (i : ℕ) : MeasurableSet (cell a h i) := by
  unfold cell; exact measurableSet_Icc

lemma volume_cell_ne_top (a h : ℝ) (i : ℕ) : volume (cell a h i) ≠ ⊤ := by
  unfold cell; rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top

lemma integrable_stepFn (a h : ℝ) (N : ℕ) (c : ℕ → ℝ) : Integrable (stepFn a h N c) := by
  unfold stepFn
  refine integrable_finsetSum _ fun i _ => ?_
  exact (integrableOn_const (volume_cell_ne_top a h i)).integrable_indicator (measurableSet_cell a h i)

lemma memLp_stepFn (a h : ℝ) (N : ℕ) (c : ℕ → ℝ) : MemLp (stepFn a h N c) 2 volume := by
  unfold stepFn
  refine memLp_finsetSum _ fun i _ => ?_
  exact memLp_indicator_const 2 (measurableSet_cell a h i) (c i) (Or.inr (volume_cell_ne_top a h i))

/-- `∫ (∑ c_i 1_{cell i}) g = ∑ c_i ∫_{cell i} g`. -/
lemma integral_stepFn_mul (a h : ℝ) (hh : 0 ≤ h) (N : ℕ) (c : ℕ → ℝ) (g : ℝ → ℝ)
    (hg : ∀ i, IntegrableOn g (cell a h i)) :
    ∫ x, stepFn a h N c x * g x = ∑ i ∈ Finset.range N, c i * ∫ x in (a + i * h)..(a + i * h + h), g x := by
  have hpt : ∀ x, stepFn a h N c x * g x =
      ∑ i ∈ Finset.range N, (cell a h i).indicator (fun x => c i * g x) x := by
    intro x
    unfold stepFn
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hx : x ∈ cell a h i
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  simp_rw [hpt]
  rw [integral_finsetSum _ fun i _ => IntegrableOn.integrable_indicator
    (show IntegrableOn (fun x => c i * g x) (cell a h i) volume from (hg i).const_mul (c i))
    (measurableSet_cell a h i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_indicator (measurableSet_cell a h i), integral_const_mul, cell,
    intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc]

/-- On the open cell `i` the step function equals `c_i`. -/
lemma stepFn_eq_of_mem_Ioo (a h : ℝ) (hh : 0 < h) (N : ℕ) (c : ℕ → ℝ) {i : ℕ} (hi : i < N)
    {x : ℝ} (hx : x ∈ Ioo (a + i * h) (a + i * h + h)) : stepFn a h N c x = c i := by
  unfold stepFn
  rw [Finset.sum_eq_single i]
  · rw [Set.indicator_of_mem (show x ∈ cell a h i from Ioo_subset_Icc_self hx)]
  · intro j _ hji
    rw [Set.indicator_of_notMem]
    intro hj
    simp only [cell, mem_Icc] at hj
    simp only [mem_Ioo] at hx
    have h1 : (j : ℝ) < i + 1 := by
      by_contra hc; have hc' := not_lt.mp hc; nlinarith
    have h2 : (i : ℝ) < j + 1 := by
      by_contra hc; have hc' := not_lt.mp hc; nlinarith
    have h1' : j < i + 1 := by exact_mod_cast h1
    have h2' : i < j + 1 := by exact_mod_cast h2
    omega
  · intro h; exact absurd (Finset.mem_range.mpr hi) h

lemma integral_cell_stepFn (a h : ℝ) (hh : 0 < h) (N : ℕ) (c : ℕ → ℝ) {i : ℕ} (hi : i < N) :
    ∫ x in (a + i * h)..(a + i * h + h), stepFn a h N c x = c i * h := by
  rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo,
    setIntegral_congr_fun measurableSet_Ioo (fun x hx => stepFn_eq_of_mem_Ioo a h hh N c hi hx)]
  simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply, univ_inter,
    Real.volume_real_Ioo_of_le (by linarith : a + i * h ≤ a + i * h + h), smul_eq_mul]
  ring

lemma integrableOn_FC_abs_sub (C x : ℝ) (s : Set ℝ) {s₀ s₁ : ℝ} (hs : s = Icc s₀ s₁) :
    IntegrableOn (fun y => FC C |x - y|) s := by
  subst hs
  refine Measure.integrableOn_of_bounded (M := (|x| + (|s₀| + |s₁|)) + |C|) (by simp)
    ((measurable_FC_abs C).comp (measurable_const.sub measurable_id)).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Icc]
  refine Filter.Eventually.of_forall fun y hy => ?_
  rw [Real.norm_eq_abs]
  refine abs_FC_abs_le C (x - y) _ ?_
  have := abs_le_of_mem_uIcc (Icc_subset_uIcc hy)
  have := abs_sub x y
  linarith

/-- **𝒬 of a grid step function.** -/
theorem Qf_stepFn (C a h : ℝ) (hh : 0 < h) (N : ℕ) (c : ℕ → ℝ) :
    Qf (FC C) (stepFn a h N c) =
      (∑ i ∈ Finset.range N, c i * (c i * h)) +
        ∑ i ∈ Finset.range N, c i * ∑ j ∈ Finset.range N, c j *
          (Gfun C (((i : ℝ) - j) * h + h) - 2 * Gfun C (((i : ℝ) - j) * h)
            + Gfun C (((i : ℝ) - j) * h - h)) := by
  set f := stepFn a h N c with hf
  have hint : ∀ i, IntegrableOn f (cell a h i) := fun i => (integrable_stepFn a h N c).integrableOn
  unfold Qf
  congr 1
  · -- ∫ f² = ∑ c_i (c_i h)
    have : (fun x => f x ^ 2) = fun x => f x * f x := by ext x; ring
    rw [this, integral_stepFn_mul a h hh.le N c f hint]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [integral_cell_stepFn a h hh N c (Finset.mem_range.mp hi)]
  · -- the double integral
    set P : ℝ → ℝ := fun x => ∑ j ∈ Finset.range N,
      c j * (G1 C (x - (a + j * h)) - G1 C (x - (a + j * h + h))) with hP
    have hinner : ∀ x, ∫ y, f x * f y * FC C |x - y| = f x * P x := by
      intro x
      have : (fun y => f x * f y * FC C |x - y|) = fun y => f x * (f y * FC C |x - y|) := by
        ext y; ring
      rw [this, integral_const_mul]
      congr 1
      rw [integral_stepFn_mul a h hh.le N c _ fun i => integrableOn_FC_abs_sub C x _ rfl]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [inner_cell_integral]
    simp_rw [hinner]
    have hPc : Continuous P := by
      rw [hP]
      refine continuous_finsetSum _ fun j _ => Continuous.mul continuous_const ?_
      exact ((continuous_G1 C).comp (continuous_sub_right _)).sub
        ((continuous_G1 C).comp (continuous_sub_right _))
    rw [integral_stepFn_mul a h hh.le N c P fun i => hPc.integrableOn_Icc]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [hP, intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [intervalIntegral.integral_const_mul, outer_cell_integral]
      congr 1
      have e : a + i * h - (a + j * h) = ((i : ℝ) - j) * h := by ring
      rw [e]
    · intro j _
      exact (continuous_const.mul (((continuous_G1 C).comp (continuous_sub_right _)).sub
        ((continuous_G1 C).comp (continuous_sub_right _)))).intervalIntegrable _ _


/-! ### Evenness, support and mass of a symmetric grid step function -/

lemma neg_mem_cell_iff (a h : ℝ) (N : ℕ) (hsym : a + N * h = -a) {i : ℕ} (hi : i < N) (x : ℝ) :
    -x ∈ cell a h i ↔ x ∈ cell a h (N - 1 - i) := by
  have hc : ((N - 1 - i : ℕ) : ℝ) = N - 1 - i := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
  simp only [cell, mem_Icc, hc]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith

lemma stepFn_neg (a h : ℝ) (N : ℕ) (c : ℕ → ℝ) (hsym : a + N * h = -a)
    (hc : ∀ i < N, c (N - 1 - i) = c i) (x : ℝ) : stepFn a h N c (-x) = stepFn a h N c x := by
  unfold stepFn
  calc ∑ i ∈ Finset.range N, (cell a h i).indicator (fun _ => c i) (-x)
      = ∑ i ∈ Finset.range N, (cell a h (N - 1 - i)).indicator (fun _ => c (N - 1 - (N - 1 - i))) x := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi' := Finset.mem_range.mp hi
        have e : N - 1 - (N - 1 - i) = i := by omega
        rw [e]
        by_cases hx : x ∈ cell a h (N - 1 - i)
        · rw [Set.indicator_of_mem hx,
            Set.indicator_of_mem ((neg_mem_cell_iff a h N hsym hi' x).mpr hx)]
        · rw [Set.indicator_of_notMem hx,
            Set.indicator_of_notMem (fun h' => hx ((neg_mem_cell_iff a h N hsym hi' x).mp h'))]
    _ = ∑ i ∈ Finset.range N, (cell a h i).indicator (fun _ => c (N - 1 - i)) x :=
        Finset.sum_range_reflect (fun j => (cell a h j).indicator (fun _ => c (N - 1 - j)) x) N
    _ = ∑ i ∈ Finset.range N, (cell a h i).indicator (fun _ => c i) x := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hc i (Finset.mem_range.mp hi)]

lemma stepFn_eq_zero_of_notMem (a h : ℝ) (hh : 0 ≤ h) (N : ℕ) (c : ℕ → ℝ) {x : ℝ}
    (hx : x ∉ Icc a (a + N * h)) : stepFn a h N c x = 0 := by
  unfold stepFn
  refine Finset.sum_eq_zero fun i hi => Set.indicator_of_notMem (fun hxi => hx ?_) _
  have hi' : (i : ℝ) + 1 ≤ N := by exact_mod_cast Finset.mem_range.mp hi
  simp only [cell, mem_Icc] at hxi ⊢
  constructor <;> nlinarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]

lemma integral_stepFn (a h : ℝ) (hh : 0 ≤ h) (N : ℕ) (c : ℕ → ℝ) :
    ∫ x, stepFn a h N c x = ∑ i ∈ Finset.range N, c i * h := by
  have := integral_stepFn_mul a h hh N c (fun _ => 1) fun i => integrableOn_const (volume_cell_ne_top a h i)
  simp only [mul_one, intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left] at this
  exact this

/-! ### The certificate windows -/

open Families.CertData

/-- Heights `c_i = m_i/(h ∑ m)` of the certificate window built from an integer list. -/
def cvec (ms : List ℤ) (i : ℕ) : ℝ := (ms.getD i 0 : ℝ) / ((1 / 200) * (ms.sum : ℝ))

/-- The certificate window: the step function on the 400 cells of `[-1,1]` with heights `cvec ms`. -/
def window (ms : List ℤ) : ℝ → ℝ := stepFn (-1) (1 / 200) 400 (cvec ms)

lemma getD_nonneg_of_check (l : List ℤ) (h : nonnegCheck l = true) (i : ℕ) : 0 ≤ l.getD i 0 := by
  unfold nonnegCheck at h
  rw [List.all_eq_true] at h
  rw [List.getD_eq_getElem?_getD]
  cases hx : l[i]? with
  | none => simp
  | some x => simpa using h x (List.mem_of_getElem? hx)

lemma getD_symm (l : List ℤ) (hl : l.reverse = l) {i : ℕ} (hi : i < l.length) :
    l.getD (l.length - 1 - i) 0 = l.getD i 0 := by
  conv_rhs => rw [← hl]
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_reverse hi]

lemma sum_range_getD (l : List ℤ) : ∑ i ∈ Finset.range l.length, l.getD i 0 = l.sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.sum_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero, ih]
    ring

lemma dot_eq_sum (l₁ l₂ : List ℤ) (h : l₁.length ≤ l₂.length) :
    dot l₁ l₂ = ∑ i ∈ Finset.range l₁.length, l₁.getD i 0 * l₂.getD i 0 := by
  induction l₁ generalizing l₂ with
  | nil => simp [dot]
  | cons a t ih =>
    cases l₂ with
    | nil => simp at h
    | cons b t₂ =>
      simp only [List.length_cons, Nat.add_le_add_iff_right] at h
      have : dot (a :: t) (b :: t₂) = a * b + dot t t₂ := by
        simp [dot, List.zipWith_cons_cons, List.sum_cons]
      rw [this, ih t₂ h, List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      ring

lemma getD_drop' (l : List ℤ) (i t : ℕ) : (l.drop i).getD t 0 = l.getD (i + t) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

lemma getD_map_range (f : ℕ → ℤ) {n i : ℕ} (hi : i < n) : ((List.range n).map f).getD i 0 = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

lemma kerList_length (cn cd : ℤ) : (kerList cn cd).length = 799 := by simp [kerList]

lemma kerList_getD (cn cd : ℤ) {k : ℕ} (hk : k < 799) :
    (kerList cn cd).getD k 0 = ks cn cd ((k : ℤ) - 399) := by
  rw [List.getD_eq_getElem?_getD, kerList, List.getElem?_map, List.getElem?_range hk]
  rfl

lemma inner_eq (ms : List ℤ) (hlen : ms.length = 400) (hl : ms.reverse = ms) (cn cd : ℤ)
    {i : ℕ} (hi : i < 400) :
    dot ms ((kerList cn cd).drop i) =
      ∑ j ∈ Finset.range 400, ms.getD j 0 * ks cn cd ((i : ℤ) - j) := by
  rw [dot_eq_sum _ _ (by simp [hlen, kerList_length]; omega), hlen]
  have hdrop : ∀ t ∈ Finset.range 400, ms.getD t 0 * ((kerList cn cd).drop i).getD t 0
      = ms.getD t 0 * ks cn cd (((i + t : ℕ) : ℤ) - 399) := by
    intro t ht
    have ht' := Finset.mem_range.mp ht
    rw [getD_drop', kerList_getD cn cd (by omega)]
  rw [Finset.sum_congr rfl hdrop]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  have hs := getD_symm ms hl (i := j) (by omega)
  rw [hlen] at hs
  rw [hs]
  congr 2
  push_cast [Nat.cast_sub (by omega : j ≤ 400 - 1)]
  ring

lemma quad_eq (ms : List ℤ) (hlen : ms.length = 400) (hl : ms.reverse = ms) (cn cd : ℤ) :
    quadL ms (kerList cn cd) = ∑ i ∈ Finset.range 400, ms.getD i 0 *
      ∑ j ∈ Finset.range 400, ms.getD j 0 * ks cn cd ((i : ℤ) - j) := by
  unfold quadL
  rw [dot_eq_sum _ _ (by simp [hlen]), hlen]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  rw [getD_map_range _ hi', inner_eq ms hlen hl cn cd hi']

lemma natAbs_cast_real (k : ℤ) : ((k.natAbs : ℤ) : ℝ) = |(k : ℝ)| := by push_cast; rfl

lemma Gfun_grid (cn cd : ℤ) (hcd : 0 < cd) (k : ℤ) :
    Gfun ((cn : ℝ) / cd) ((k : ℝ) / 200) = (Gs cn cd k : ℝ) / (6 * 200 ^ 3 * cd) := by
  have hcd' : (0 : ℝ) < cd := by exact_mod_cast hcd
  have habs : |(k : ℝ) / 200| = |(k : ℝ)| / 200 := by rw [abs_div]; norm_num
  unfold Gfun Gs
  by_cases hk : k.natAbs ≤ 200
  · have hk' : |(k : ℝ)| ≤ 200 := by
      rw [← natAbs_cast_real]; exact_mod_cast hk
    rw [if_pos (by rw [habs]; linarith), if_pos hk]
    push_cast
    rw [habs, ← natAbs_cast_real]
    field_simp
  · have hk' : ¬ |(k : ℝ)| ≤ 200 := by
      rw [← natAbs_cast_real]; exact_mod_cast hk
    rw [if_neg (by rw [habs]; intro h; exact hk' (by linarith)), if_neg hk]
    push_cast
    rw [habs, ← natAbs_cast_real]
    field_simp
    all_goals (try push_cast)
    all_goals (try ring)


/-! ### Admissibility and the exact value of `𝒬` on the certificate windows -/

lemma sum_getD_real (ms : List ℤ) (hlen : ms.length = 400) :
    ∑ i ∈ Finset.range 400, (ms.getD i 0 : ℝ) = (ms.sum : ℝ) := by
  rw [← sum_range_getD ms, hlen]; push_cast; rfl

lemma window_admissible (ms : List ℤ) (hlen : ms.length = 400) (hl : ms.reverse = ms)
    (hnn : nonnegCheck ms = true) (hS : 0 < ms.sum) : AdmissibleWindow (window ms) := by
  have hS' : (0 : ℝ) < ms.sum := by exact_mod_cast hS
  have hcnn : ∀ i, 0 ≤ cvec ms i := fun i => by
    unfold cvec
    exact div_nonneg (by exact_mod_cast getD_nonneg_of_check ms hnn i) (by positivity)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    unfold window stepFn
    exact Finset.sum_nonneg fun i _ => Set.indicator_nonneg (fun _ _ => hcnn i) x
  · intro x
    refine stepFn_neg (-1) (1 / 200) 400 (cvec ms) (by norm_num) (fun i hi => ?_) x
    unfold cvec
    have := getD_symm ms hl (i := i) (by omega)
    rw [hlen] at this
    rw [this]
  · intro x hx
    by_contra hx'
    have hset : Icc (-1 : ℝ) (-1 + ((400 : ℕ) : ℝ) * (1 / 200)) = Icc (-1) 1 := by norm_num
    exact hx (stepFn_eq_zero_of_notMem (-1) (1 / 200) (by norm_num) 400 (cvec ms)
      (by rw [hset]; exact hx'))
  · exact memLp_stepFn _ _ _ _
  · unfold window
    rw [integral_stepFn _ _ (by norm_num)]
    unfold cvec
    rw [← Finset.sum_mul, ← Finset.sum_div, sum_getD_real ms hlen]
    field_simp

lemma kappa_grid (cn cd : ℤ) (hcd : 0 < cd) (i j : ℕ) :
    Gfun ((cn : ℝ) / cd) (((i : ℝ) - j) * (1 / 200) + 1 / 200)
      - 2 * Gfun ((cn : ℝ) / cd) (((i : ℝ) - j) * (1 / 200))
      + Gfun ((cn : ℝ) / cd) (((i : ℝ) - j) * (1 / 200) - 1 / 200)
      = (ks cn cd ((i : ℤ) - j) : ℝ) / (6 * 200 ^ 3 * cd) := by
  have e1 : ((i : ℝ) - j) * (1 / 200) + 1 / 200 = (((i : ℤ) - j + 1 : ℤ) : ℝ) / 200 := by
    push_cast; ring
  have e2 : ((i : ℝ) - j) * (1 / 200) = (((i : ℤ) - j : ℤ) : ℝ) / 200 := by push_cast; ring
  have e3 : ((i : ℝ) - j) * (1 / 200) - 1 / 200 = (((i : ℤ) - j - 1 : ℤ) : ℝ) / 200 := by
    push_cast; ring
  rw [e1, e3, e2, Gfun_grid cn cd hcd, Gfun_grid cn cd hcd, Gfun_grid cn cd hcd]
  unfold ks
  push_cast
  ring

/-- The exact value: `𝒬_{F_C}(window) = (h X + Y/D) (h S)^{-2}` with `X = ∑ m_i²`,
`Y = ∑_{i,j} m_i m_j κ_{i-j}`, `S = ∑ m_i`, `h = 1/200`, `D = 6·200³·c_d`. -/
lemma Qf_window (ms : List ℤ) (hlen : ms.length = 400) (hl : ms.reverse = ms) (hS : 0 < ms.sum)
    (cn cd : ℤ) (hcd : 0 < cd) :
    Qf (FC ((cn : ℝ) / cd)) (window ms) =
      ((1 / 200) * (dot ms ms : ℝ) + (quadL ms (kerList cn cd) : ℝ) / (6 * 200 ^ 3 * cd))
        * (200 / (ms.sum : ℝ)) ^ 2 := by
  have hS' : (0 : ℝ) < ms.sum := by exact_mod_cast hS
  have hcd' : (0 : ℝ) < cd := by exact_mod_cast hcd
  have hc : ∀ i, cvec ms i = (ms.getD i 0 : ℝ) * (200 / (ms.sum : ℝ)) := by
    intro i; unfold cvec; field_simp
  have hX : (dot ms ms : ℝ) = ∑ i ∈ Finset.range 400, (ms.getD i 0 : ℝ) * (ms.getD i 0 : ℝ) := by
    rw [dot_eq_sum ms ms le_rfl, hlen]; push_cast; rfl
  have hY : (quadL ms (kerList cn cd) : ℝ) = ∑ i ∈ Finset.range 400, (ms.getD i 0 : ℝ) *
      ∑ j ∈ Finset.range 400, (ms.getD j 0 : ℝ) * (ks cn cd ((i : ℤ) - j) : ℝ) := by
    rw [quad_eq ms hlen hl cn cd]; push_cast; rfl
  unfold window
  rw [Qf_stepFn _ _ _ (by norm_num)]
  simp_rw [kappa_grid cn cd hcd, hc]
  rw [hX, hY]
  simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_div, add_mul]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_; ring
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_; ring

/-- From the kernel-checked integer inequality to `𝒬 ≤ B/10⁶`. -/
lemma Qf_window_le (ms : List ℤ) (hlen : ms.length = 400) (hl : ms.reverse = ms) (hS : 0 < ms.sum)
    (cn cd B : ℤ) (hcd : 0 < cd) (hcert : certCheck cd B ms (kerList cn cd) = true) :
    Qf (FC ((cn : ℝ) / cd)) (window ms) ≤ (B : ℝ) / 10 ^ 6 := by
  have hS' : (0 : ℝ) < ms.sum := by exact_mod_cast hS
  have hcd' : (0 : ℝ) < cd := by exact_mod_cast hcd
  unfold certCheck at hcert
  have hz := of_decide_eq_true hcert
  have hr : (6 * 200 ^ 3 * (cd : ℝ) * 200000000 * (dot ms ms : ℝ)
      + 40000000000 * (quadL ms (kerList cn cd) : ℝ)
      ≤ (B : ℝ) * (6 * 200 ^ 3 * cd) * (ms.sum : ℝ) ^ 2) := by exact_mod_cast hz
  rw [Qf_window ms hlen hl hS cn cd hcd]
  set X := (dot ms ms : ℝ)
  set Y := (quadL ms (kerList cn cd) : ℝ)
  set S := (ms.sum : ℝ)
  have key : ((1 / 200) * X + Y / (6 * 200 ^ 3 * cd)) * (200 / S) ^ 2
      = (6 * 200 ^ 3 * cd * 200000000 * X + 40000000000 * Y) / (10 ^ 6 * (6 * 200 ^ 3 * cd) * S ^ 2) := by
    field_simp
    ring
  rw [key, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hr]

/-- `prop:cert`, row `C = 1`: `p(1) ≥ 0.932282`. -/
theorem pC_one_ge : (0.932282 : ℝ) ≤ pC 1 := by
  have hadm := window_admissible ms1 ms1_length ms1_reverse ms1_nonneg ms1_sum_pos
  have h1 := pC_ge_of_admissible (C := 1) zero_le_one hadm
  have h2 := Qf_window_le ms1 ms1_length ms1_reverse ms1_sum_pos 1 1 1067718 one_pos cert1
  have e : ((1 : ℤ) : ℝ) / ((1 : ℤ) : ℝ) = 1 := by norm_num
  rw [e] at h2
  norm_num at h2 ⊢
  linarith

/-- `prop:cert`, row `C = 1.2688`: `p(1.2688) ≥ 0.885912`. -/
theorem pC_12688_ge : (0.885912 : ℝ) ≤ pC (12688 / 10000) := by
  have hadm := window_admissible ms2 ms2_length ms2_reverse ms2_nonneg ms2_sum_pos
  have h1 := pC_ge_of_admissible (C := 12688 / 10000) (by norm_num) hadm
  have h2 := Qf_window_le ms2 ms2_length ms2_reverse ms2_sum_pos 12688 10000 1114088
    (by norm_num) cert2
  have e : ((12688 : ℤ) : ℝ) / ((10000 : ℤ) : ℝ) = 12688 / 10000 := by norm_num
  rw [e] at h2
  norm_num at h2 ⊢
  linarith

end Families
