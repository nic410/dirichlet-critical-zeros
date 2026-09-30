/-
# Montgomery 1969 density: zero counting by Jensen's formula

`jensen_zero_count`: for entire `G, H` with `‖GH − 1‖ ≤ 1/2` on `Re s ≥ a := 1/2 + δ/2 + 2/δ`, the zeros of
`G` with `β ≥ 1/2 + δ`, `|γ| ≤ T` (counted with multiplicity) number at most
`(5/δ²) [ (2π)⁻¹ ∫_0^{2π} I(a + R cos θ) dθ + 2 I(a) ]`, where `R = 2/δ`, `W = T + 1 + R` and
`I(σ) = ∫_{−W}^{W} ‖G(σ+iv)H(σ+iv) − 1‖ dv`.

Proof: Mathlib's Jensen formula (`AnalyticOnNhd.circleAverage_log_norm`) for `F = GH` on the discs
`D(a + iu, R) ⊃ D(a + iu, r)`, `r² = (R − δ/2)² + 1/4` (so `log(R/r) ≥ δ²/5`), with
`log‖F‖ ≤ ‖F − 1‖` and `−log‖F(a+iu)‖ ≤ 2‖F(a+iu) − 1‖`; every zero with `β ≥ 1/2+δ`, `|γ − u| ≤ 1/2`
lies in `D(a + iu, r)`; integrate over `u ∈ [−T−1, T+1]` and swap the `u`- and `θ`-integrals.
-/
import Mathlib

noncomputable section

open scoped BigOperators
open MeasureTheory Real Complex

namespace Families.Hyp.Montgomery

/-- The divisor of an analytic function is its (natural-number) order of vanishing. -/
lemma jz_divisor_eq {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U) {z : ℂ} (hz : z ∈ U) :
    MeromorphicOn.divisor f U z = (analyticOrderNatAt f z : ℤ) := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hf hz]
  unfold analyticOrderNatAt
  cases analyticOrderAt f z with
  | top => simp
  | coe n => simp

/-- An entire function that is nonzero somewhere has finite order everywhere. -/
lemma jz_order_ne_top {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z₀ : ℂ} (h0 : f z₀ ≠ 0) (z : ℂ) :
    analyticOrderAt f z ≠ ⊤ := by
  have hA : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  refine hA.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (Set.mem_univ z₀)
    (Set.mem_univ z) ?_
  rw [(hf.analyticAt z₀).analyticOrderAt_eq_zero.mpr h0]
  simp

/-- `ord_ρ G ≤ ord_ρ (G H)` when `G H` is not identically zero. -/
lemma jz_order_le {G H : ℂ → ℂ} (hG : Differentiable ℂ G) (hH : Differentiable ℂ H) {z₀ : ℂ}
    (h0 : G z₀ * H z₀ ≠ 0) (ρ : ℂ) :
    analyticOrderNatAt G ρ ≤ analyticOrderNatAt (fun z => G z * H z) ρ := by
  have hF : Differentiable ℂ (fun z => G z * H z) := hG.mul hH
  have hne := jz_order_ne_top hF h0 ρ
  have hmul : analyticOrderAt (fun z => G z * H z) ρ =
      analyticOrderAt G ρ + analyticOrderAt H ρ :=
    analyticOrderAt_mul (hG.analyticAt ρ) (hH.analyticAt ρ)
  rw [hmul] at hne
  have hGt : analyticOrderAt G ρ ≠ ⊤ := fun h => hne (by simp [h])
  have hHt : analyticOrderAt H ρ ≠ ⊤ := fun h => hne (by simp [h])
  unfold analyticOrderNatAt
  rw [hmul, ENat.toNat_add hGt hHt]
  omega

/-- Jensen's inequality for a finite set of points in the smaller disc. -/
lemma jz_jensen_finset {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c : ℂ} {r R : ℝ} (hr : 0 < r)
    (hrR : r < R) (hc : f c ≠ 0) (S : Finset ℂ) (hS : ∀ ρ ∈ S, ‖ρ - c‖ ≤ r) :
    (∑ ρ ∈ S, (analyticOrderNatAt f ρ : ℝ)) * Real.log (R / r) ≤
      circleAverage (fun z => Real.log ‖f z‖) c R - Real.log ‖f c‖ := by
  have hR : 0 < R := hr.trans hrR
  have hA : AnalyticOnNhd ℂ f (Metric.closedBall c |R|) := fun z _ => hf.analyticAt z
  have jensen := hA.circleAverage_log_norm hR.ne' hc
  set D := MeromorphicOn.divisor f (Metric.closedBall c |R|) with hD
  have hfin := D.finiteSupport (isCompact_closedBall c |R|)
  set φ : ℂ → ℝ := fun u => (D u : ℝ) * Real.log (R * ‖c - u‖⁻¹) with hφ
  have hφnn : ∀ u, 0 ≤ φ u := by
    intro u
    by_cases hu : u ∈ Metric.closedBall c |R|
    · apply mul_nonneg
      · rw [hD, jz_divisor_eq hA hu]; positivity
      · by_cases h0 : ‖c - u‖ = 0
        · simp [h0]
        · apply Real.log_nonneg
          rw [Metric.mem_closedBall, dist_eq_norm, abs_of_pos hR, norm_sub_rev] at hu
          rw [← div_eq_mul_inv, le_div_iff₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0))]
          linarith
    · simp [φ, D, hu]
  have hsupp : Function.support φ ⊆ ((S ∪ hfin.toFinset : Finset ℂ) : Set ℂ) := by
    intro u hu
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Set.Finite.mem_toFinset]
    right
    intro h
    apply hu
    simp [φ, h]
  have hsum : ∑ᶠ u, φ u = ∑ u ∈ S ∪ hfin.toFinset, φ u :=
    finsum_eq_sum_of_support_subset φ hsupp
  have key : (∑ ρ ∈ S, (analyticOrderNatAt f ρ : ℝ)) * Real.log (R / r) ≤ ∑ ρ ∈ S, φ ρ := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro ρ hρ
    have hρc := hS ρ hρ
    have hmem : ρ ∈ Metric.closedBall c |R| := by
      rw [Metric.mem_closedBall, dist_eq_norm, abs_of_pos hR]; linarith
    simp only [φ, hD, jz_divisor_eq hA hmem, Int.cast_natCast]
    by_cases h0 : ρ = c
    · subst h0
      have : analyticOrderNatAt f ρ = 0 := by
        unfold analyticOrderNatAt
        rw [(hf.analyticAt ρ).analyticOrderAt_eq_zero.mpr hc]
        rfl
      simp [this]
    · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Real.log_le_log (div_pos hR hr)
      have hpos : 0 < ‖c - ρ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm h0))
      rw [← div_eq_mul_inv]
      exact div_le_div_of_nonneg_left hR.le hpos (by rwa [norm_sub_rev])
  have h2 : ∑ ρ ∈ S, φ ρ ≤ ∑ u ∈ S ∪ hfin.toFinset, φ u :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun u _ _ => hφnn u)
  have : ∑ᶠ u, φ u = ∑ᶠ u, (D u : ℝ) * Real.log (R * ‖c - u‖⁻¹) := rfl
  linarith [jensen]

/-- `log ‖F‖` is bounded by `‖F - 1‖` on circles. -/
lemma jz_circleAverage_log_le {F : ℂ → ℂ} (hF : Differentiable ℂ F) (c : ℂ) (R : ℝ) :
    circleAverage (fun z => Real.log ‖F z‖) c R ≤ circleAverage (fun z => ‖F z - 1‖) c R := by
  apply circleAverage_mono
  · exact MeromorphicOn.circleIntegrable_log_norm (fun z _ => (hF.analyticAt z).meromorphicAt)
  · exact ((hF.continuous.sub continuous_const).norm.continuousOn).circleIntegrable'
  · intro z _
    by_cases h : F z = 0
    · simp [h]
    · have h1 := Real.log_le_sub_one_of_pos (norm_pos_iff.mpr h)
      have h2 : ‖F z‖ - ‖(1 : ℂ)‖ ≤ ‖F z - 1‖ := norm_sub_norm_le _ _
      simp only [norm_one] at h2
      linarith

/-- `-log ‖w‖ ≤ 2 ‖w - 1‖` when `‖w - 1‖ ≤ 1/2`. -/
lemma jz_neg_log_le {w : ℂ} (hw : ‖w - 1‖ ≤ 1 / 2) : -Real.log ‖w‖ ≤ 2 * ‖w - 1‖ := by
  have h2 : ‖(1 : ℂ)‖ - ‖w‖ ≤ ‖w - 1‖ := by
    rw [norm_sub_rev]; exact norm_sub_norm_le _ _
  simp only [norm_one] at h2
  set y := ‖w‖
  set x := ‖w - 1‖
  have hy : 1 / 2 ≤ y := by linarith
  have hypos : 0 < y := by linarith
  have h3 := Real.log_le_sub_one_of_pos (inv_pos.mpr hypos)
  rw [Real.log_inv] at h3
  have h4 : y * y⁻¹ = 1 := mul_inv_cancel₀ hypos.ne'
  have h5 : 0 < y⁻¹ := inv_pos.mpr hypos
  have hx : 0 ≤ x := norm_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left h2 h5.le]


/-- Geometry: zeros with `β ≥ 1/2 + δ`, `|γ - u| ≤ 1/2` lie in the disc of radius
`2/δ - 2δ/5` about `a + iu`. -/
lemma jz_geom {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) {ρ : ℂ} (h1 : 1 / 2 + δ ≤ ρ.re)
    (h2 : ρ.re < 1) {u : ℝ} (h3 : |ρ.im - u| ≤ 1 / 2) :
    ‖ρ - (((1 / 2 + δ / 2 + 2 / δ : ℝ) : ℂ) + (u : ℂ) * Complex.I)‖ ≤ 2 / δ - 2 * δ / 5 := by
  have hRδ : 2 / δ * δ = 2 := by field_simp
  have hR4 : 4 ≤ 2 / δ := by rw [le_div_iff₀ hδ]; linarith
  set R := 2 / δ with hR
  have hre : (ρ - (((1 / 2 + δ / 2 + R : ℝ) : ℂ) + (u : ℂ) * Complex.I)).re =
      ρ.re - (1 / 2 + δ / 2 + R) := by simp
  have him : (ρ - (((1 / 2 + δ / 2 + R : ℝ) : ℂ) + (u : ℂ) * Complex.I)).im = ρ.im - u := by simp
  have hr0 : 0 ≤ R - 2 * δ / 5 := by linarith
  rw [← sq_le_sq₀ (norm_nonneg _) hr0, Complex.sq_norm, Complex.normSq_apply, hre, him]
  have habs := abs_le.mp h3
  set x := 1 / 2 + δ / 2 + R - ρ.re with hx
  have hx0 : 0 ≤ x := by linarith
  have hx1 : x ≤ R - δ / 2 := by linarith
  have hxx : x * x ≤ (R - δ / 2) ^ 2 := by nlinarith
  have hyy : (ρ.im - u) * (ρ.im - u) ≤ 1 / 4 := by nlinarith
  have hk : (R - δ / 2) ^ 2 + 1 / 4 ≤ (R - 2 * δ / 5) ^ 2 := by nlinarith
  have : (ρ.re - (1 / 2 + δ / 2 + R)) * (ρ.re - (1 / 2 + δ / 2 + R)) = x * x := by
    rw [hx]; ring
  linarith

/-- `log(R/r) ≥ δ²/5` for `R = 2/δ`, `r = 2/δ - 2δ/5`. -/
lemma jz_log_ratio {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    δ ^ 2 / 5 ≤ Real.log ((2 / δ) / (2 / δ - 2 * δ / 5)) := by
  have hR4 : 4 ≤ 2 / δ := by rw [le_div_iff₀ hδ]; linarith
  have hr : 0 < 2 / δ - 2 * δ / 5 := by linarith
  have hq : (2 / δ - 2 * δ / 5) / (2 / δ) = 1 - δ ^ 2 / 5 := by field_simp
  have hpos : 0 < (2 / δ - 2 * δ / 5) / (2 / δ) := div_pos hr (by positivity)
  have h := Real.log_le_sub_one_of_pos hpos
  have e : (2 / δ) / (2 / δ - 2 * δ / 5) = ((2 / δ - 2 * δ / 5) / (2 / δ))⁻¹ :=
    (inv_div _ _).symm
  rw [e, Real.log_inv]
  rw [hq] at h ⊢
  linarith

/-- The point `circleMap (a + iu) R θ` in coordinates. -/
lemma jz_circleMap (a u R θ : ℝ) :
    circleMap (((a : ℝ) : ℂ) + (u : ℂ) * Complex.I) R θ =
      ((a + R * Real.cos θ : ℝ) : ℂ) + ((u + R * Real.sin θ : ℝ) : ℂ) * Complex.I := by
  simp only [circleMap, Complex.exp_mul_I]
  push_cast
  ring

/-- Per-window bound from Jensen's formula. -/
lemma jz_window (G H : ℂ → ℂ) (hG : Differentiable ℂ G) (hH : Differentiable ℂ H)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (hre : ∀ ρ : ℂ, G ρ = 0 → ρ.re < 1)
    (hfar : ∀ s : ℂ, 1 / 2 + δ / 2 + 2 / δ ≤ s.re → ‖G s * H s - 1‖ ≤ 1 / 2)
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, G ρ = 0 ∧ 1 / 2 + δ ≤ ρ.re) (u : ℝ) :
    ∑ ρ ∈ S, (Set.Icc (ρ.im - 1 / 2) (ρ.im + 1 / 2)).indicator
        (fun _ => (analyticOrderNatAt G ρ : ℝ)) u ≤
      5 / δ ^ 2 * ((2 * π)⁻¹ * (∫ θ in (0 : ℝ)..(2 * π),
          ‖G (((1 / 2 + δ / 2 + 2 / δ + 2 / δ * Real.cos θ : ℝ) : ℂ) +
                ((u + 2 / δ * Real.sin θ : ℝ) : ℂ) * Complex.I) *
            H (((1 / 2 + δ / 2 + 2 / δ + 2 / δ * Real.cos θ : ℝ) : ℂ) +
                ((u + 2 / δ * Real.sin θ : ℝ) : ℂ) * Complex.I) - 1‖)
        + 2 * ‖G (((1 / 2 + δ / 2 + 2 / δ : ℝ) : ℂ) + (u : ℂ) * Complex.I) *
              H (((1 / 2 + δ / 2 + 2 / δ : ℝ) : ℂ) + (u : ℂ) * Complex.I) - 1‖) := by
  set s₀ : ℂ := ((1 / 2 + δ / 2 + 2 / δ : ℝ) : ℂ) + (u : ℂ) * Complex.I with hs₀def
  set F : ℂ → ℂ := fun z => G z * H z with hFdef
  have hFd : Differentiable ℂ F := hG.mul hH
  have hs₀ : ‖F s₀ - 1‖ ≤ 1 / 2 := hfar s₀ (by simp [s₀])
  have hFs₀ : F s₀ ≠ 0 := by
    intro h
    rw [h] at hs₀
    norm_num at hs₀
  set S' := S.filter (fun ρ => u ∈ Set.Icc (ρ.im - 1 / 2) (ρ.im + 1 / 2)) with hS'
  have h1 : ∑ ρ ∈ S, (Set.Icc (ρ.im - 1 / 2) (ρ.im + 1 / 2)).indicator
        (fun _ => (analyticOrderNatAt G ρ : ℝ)) u = ∑ ρ ∈ S', (analyticOrderNatAt G ρ : ℝ) := by
    rw [hS', Finset.sum_filter]
    simp only [Set.indicator_apply]
  have h2 : ∑ ρ ∈ S', (analyticOrderNatAt G ρ : ℝ) ≤ ∑ ρ ∈ S', (analyticOrderNatAt F ρ : ℝ) :=
    Finset.sum_le_sum (fun ρ _ => by exact_mod_cast jz_order_le hG hH hFs₀ ρ)
  have hball : ∀ ρ ∈ S', ‖ρ - s₀‖ ≤ 2 / δ - 2 * δ / 5 := by
    intro ρ hρ
    rw [hS', Finset.mem_filter] at hρ
    obtain ⟨hρS, hu⟩ := hρ
    obtain ⟨hG0, hβ⟩ := hS ρ hρS
    have h3 : |ρ.im - u| ≤ 1 / 2 := by
      rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
    exact jz_geom hδ hδ' hβ (hre ρ hG0) h3
  have hR4 : 4 ≤ 2 / δ := by rw [le_div_iff₀ hδ]; linarith
  have hr0 : 0 < 2 / δ - 2 * δ / 5 := by linarith
  have hrR : 2 / δ - 2 * δ / 5 < 2 / δ := by linarith
  have hJ := jz_jensen_finset hFd hr0 hrR hFs₀ S' hball
  have hlog := jz_log_ratio hδ hδ'
  have hcirc := jz_circleAverage_log_le hFd s₀ (2 / δ)
  have hneg := jz_neg_log_le hs₀
  have hcirc_eq : circleAverage (fun z => ‖F z - 1‖) s₀ (2 / δ) =
      (2 * π)⁻¹ * (∫ θ in (0 : ℝ)..(2 * π),
          ‖G (((1 / 2 + δ / 2 + 2 / δ + 2 / δ * Real.cos θ : ℝ) : ℂ) +
                ((u + 2 / δ * Real.sin θ : ℝ) : ℂ) * Complex.I) *
            H (((1 / 2 + δ / 2 + 2 / δ + 2 / δ * Real.cos θ : ℝ) : ℂ) +
                ((u + 2 / δ * Real.sin θ : ℝ) : ℂ) * Complex.I) - 1‖) := by
    rw [circleAverage_def, smul_eq_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [F, s₀, jz_circleMap]
  set X := ∑ ρ ∈ S', (analyticOrderNatAt F ρ : ℝ) with hX
  have hX0 : 0 ≤ X := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hXQ : X * (δ ^ 2 / 5) ≤ circleAverage (fun z => ‖F z - 1‖) s₀ (2 / δ) + 2 * ‖F s₀ - 1‖ := by
    have := mul_le_mul_of_nonneg_left hlog hX0
    linarith
  rw [h1, ← hcirc_eq]
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hXle : X ≤ 5 / δ ^ 2 *
      (circleAverage (fun z => ‖F z - 1‖) s₀ (2 / δ) + 2 * ‖F s₀ - 1‖) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hδ2]
    nlinarith
  exact h2.trans hXle

/-- Integral of the window-counting function. -/
lemma jz_integral_indicator_sum (S : Finset ℂ) (c : ℂ → ℝ) {T : ℝ}
    (hS : ∀ ρ ∈ S, |ρ.im| ≤ T) :
    ∫ u in (-(T + 1))..(T + 1), ∑ ρ ∈ S,
        (Set.Icc (ρ.im - 1 / 2) (ρ.im + 1 / 2)).indicator (fun _ => c ρ) u = ∑ ρ ∈ S, c ρ := by
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro ρ hρ
    have hb := abs_le.mp (hS ρ hρ)
    rw [intervalIntegral.integral_of_le (by linarith), integral_indicator_const _ measurableSet_Icc,
      measureReal_restrict_apply measurableSet_Icc,
      Set.inter_eq_left.mpr (Set.Icc_subset_Ioc (by linarith) (by linarith)),
      Real.volume_real_Icc_of_le (by linarith)]
    norm_num
  · intro ρ _
    have : IntervalIntegrable (fun _ : ℝ => c ρ) MeasureTheory.volume (-(T + 1)) (T + 1) :=
      intervalIntegrable_const
    rw [intervalIntegrable_iff] at this ⊢
    exact this.indicator measurableSet_Icc

/-- Fubini and shift. -/
lemma jz_fubini_shift (φ : ℝ → ℝ → ℝ) (hφ : Continuous (Function.uncurry φ))
    (hφ0 : ∀ θ v, 0 ≤ φ θ v) {A R : ℝ} (hA : 0 ≤ A) (hR : 0 ≤ R) :
    ∫ u in (-A)..A, ∫ θ in (0 : ℝ)..(2 * π), φ θ (u + R * Real.sin θ) ≤
      ∫ θ in (0 : ℝ)..(2 * π), ∫ v in (-(A + R))..(A + R), φ θ v := by
  have hc : Continuous (Function.uncurry fun (u θ : ℝ) => φ θ (u + R * Real.sin θ)) := by
    have : (Function.uncurry fun (u θ : ℝ) => φ θ (u + R * Real.sin θ)) =
        (Function.uncurry φ) ∘ (fun p : ℝ × ℝ => (p.2, p.1 + R * Real.sin p.2)) := by
      ext p; rfl
    rw [this]
    exact hφ.comp (by fun_prop)
  rw [intervalIntegral_intervalIntegral_swap]
  · apply intervalIntegral.integral_mono_on (by positivity)
    · apply Continuous.intervalIntegrable
      have hc' : Continuous (Function.uncurry fun (θ u : ℝ) => φ θ (u + R * Real.sin θ)) := by
        have : (Function.uncurry fun (θ u : ℝ) => φ θ (u + R * Real.sin θ)) =
            (Function.uncurry φ) ∘ (fun p : ℝ × ℝ => (p.1, p.2 + R * Real.sin p.1)) := by
          ext p; rfl
        rw [this]
        exact hφ.comp (by fun_prop)
      exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc' _ _
    · apply Continuous.intervalIntegrable
      exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hφ _ _
    · intro θ _
      rw [intervalIntegral.integral_comp_add_right (fun v => φ θ v)]
      have hs1 := Real.neg_one_le_sin θ
      have hs2 := Real.sin_le_one θ
      apply intervalIntegral.integral_mono_interval
      · nlinarith
      · linarith
      · nlinarith
      · exact Filter.Eventually.of_forall (fun v => hφ0 θ v)
      · apply Continuous.intervalIntegrable
        exact hφ.comp (by fun_prop : Continuous fun v : ℝ => (θ, v))
  · exact (hc.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)

/-- Enlarging a symmetric interval for a nonnegative continuous integrand. -/
lemma jz_interval_mono (ψ : ℝ → ℝ) (hψ : Continuous ψ) (hψ0 : ∀ v, 0 ≤ ψ v) {A W : ℝ}
    (hA : 0 ≤ A) (hAW : A ≤ W) :
    ∫ u in (-A)..A, ψ u ≤ ∫ v in (-W)..W, ψ v :=
  intervalIntegral.integral_mono_interval (by linarith) (by linarith) hAW
    (Filter.Eventually.of_forall hψ0) (hψ.intervalIntegrable _ _)


/-- Continuity of the shifted `θ`-integral in the centre `u`. -/
lemma jz_cont_shift (φ : ℝ → ℝ → ℝ) (hφ : Continuous (Function.uncurry φ)) (R : ℝ) :
    Continuous (fun u : ℝ => ∫ θ in (0 : ℝ)..(2 * π), φ θ (u + R * Real.sin θ)) := by
  have hc : Continuous (Function.uncurry fun (u θ : ℝ) => φ θ (u + R * Real.sin θ)) := by
    have : (Function.uncurry fun (u θ : ℝ) => φ θ (u + R * Real.sin θ)) =
        (Function.uncurry φ) ∘ (fun p : ℝ × ℝ => (p.2, p.1 + R * Real.sin p.2)) := by
      ext p; rfl
    rw [this]
    exact hφ.comp (by fun_prop)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hc _ _

/-- Assembly: integrate the per-window bound over `u ∈ [-T-1, T+1]`. The right-hand side is
written exactly as parsed in `jensen_zero_count` (the `2 * I(a)` term sits inside both
integrals). -/
lemma jz_assemble (φ : ℝ → ℝ → ℝ) (ψ : ℝ → ℝ) (J : ℝ → ℝ)
    (hφc : Continuous (Function.uncurry φ)) (hψc : Continuous ψ)
    (hφ0 : ∀ θ v, 0 ≤ φ θ v) (hψ0 : ∀ v, 0 ≤ ψ v) {δ T : ℝ} (hδ : 0 < δ) (hT : 0 ≤ T)
    (hJint : IntervalIntegrable J MeasureTheory.volume (-(T + 1)) (T + 1))
    (hK : ∀ u, J u ≤ 5 / δ ^ 2 * ((2 * π)⁻¹ *
      (∫ θ in (0 : ℝ)..(2 * π), φ θ (u + 2 / δ * Real.sin θ)) + 2 * ψ u)) :
    ∫ u in (-(T + 1))..(T + 1), J u ≤
      5 / δ ^ 2 * ((2 * π)⁻¹ * (∫ θ in (0 : ℝ)..(2 * π),
          ∫ v in (-(T + 1 + 2 / δ))..(T + 1 + 2 / δ), φ θ v)
        + 2 * ∫ v in (-(T + 1 + 2 / δ))..(T + 1 + 2 / δ), ψ v) := by
  have hR0 : 0 ≤ 2 / δ := by positivity
  have hI1c := jz_cont_shift φ hφc (2 / δ)
  have hKc : Continuous (fun u : ℝ => 5 / δ ^ 2 * ((2 * π)⁻¹ *
      (∫ θ in (0 : ℝ)..(2 * π), φ θ (u + 2 / δ * Real.sin θ)) + 2 * ψ u)) :=
    continuous_const.mul ((continuous_const.mul hI1c).add (continuous_const.mul hψc))
  calc _ ≤ ∫ u in (-(T + 1))..(T + 1), 5 / δ ^ 2 * ((2 * π)⁻¹ *
          (∫ θ in (0 : ℝ)..(2 * π), φ θ (u + 2 / δ * Real.sin θ)) + 2 * ψ u) :=
        intervalIntegral.integral_mono_on (by linarith) hJint (hKc.intervalIntegrable _ _)
          (fun u _ => hK u)
    _ = 5 / δ ^ 2 * ((2 * π)⁻¹ * (∫ u in (-(T + 1))..(T + 1),
          ∫ θ in (0 : ℝ)..(2 * π), φ θ (u + 2 / δ * Real.sin θ))
          + 2 * ∫ u in (-(T + 1))..(T + 1), ψ u) := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
        · exact (hI1c.intervalIntegrable _ _).const_mul _
        · exact (hψc.intervalIntegrable _ _).const_mul _
    _ ≤ 5 / δ ^ 2 * ((2 * π)⁻¹ * (∫ θ in (0 : ℝ)..(2 * π),
          ∫ v in (-(T + 1 + 2 / δ))..(T + 1 + 2 / δ), φ θ v)
          + 2 * ∫ v in (-(T + 1 + 2 / δ))..(T + 1 + 2 / δ), ψ v) := by
        have hC := jz_fubini_shift φ hφc hφ0 (A := T + 1) (R := 2 / δ) (by linarith) hR0
        have hD := jz_interval_mono ψ hψc hψ0 (A := T + 1) (W := T + 1 + 2 / δ) (by linarith)
          (by linarith)
        have h5 : 0 ≤ 5 / δ ^ 2 := by positivity
        have h2π : 0 ≤ (2 * π)⁻¹ := by positivity
        gcongr

theorem jensen_zero_count (G H : ℂ → ℂ) (hG : Differentiable ℂ G) (hH : Differentiable ℂ H)
    {δ T : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (hT : 0 ≤ T)
    (hZ : {ρ : ℂ | G ρ = 0 ∧ 1 / 2 + δ ≤ ρ.re ∧ |ρ.im| ≤ T}.Finite)
    (hre : ∀ ρ : ℂ, G ρ = 0 → ρ.re < 1)
    (hfar : ∀ s : ℂ, 1 / 2 + δ / 2 + 2 / δ ≤ s.re → ‖G s * H s - 1‖ ≤ 1 / 2) :
    ((∑ᶠ ρ ∈ {ρ : ℂ | G ρ = 0 ∧ 1 / 2 + δ ≤ ρ.re ∧ |ρ.im| ≤ T}, analyticOrderNatAt G ρ : ℕ) : ℝ) ≤
      5 / δ ^ 2 * ((2 * π)⁻¹ * (∫ θ in (0 : ℝ)..(2 * π),
          ∫ v in (-(T + 1 + 2 / δ))..(T + 1 + 2 / δ),
            ‖G (((1 / 2 + δ / 2 + 2 / δ + 2 / δ * Real.cos θ : ℝ) : ℂ) + (v : ℂ) * Complex.I) *
              H (((1 / 2 + δ / 2 + 2 / δ + 2 / δ * Real.cos θ : ℝ) : ℂ) + (v : ℂ) * Complex.I) - 1‖)
        + 2 * ∫ v in (-(T + 1 + 2 / δ))..(T + 1 + 2 / δ),
            ‖G (((1 / 2 + δ / 2 + 2 / δ : ℝ) : ℂ) + (v : ℂ) * Complex.I) *
              H (((1 / 2 + δ / 2 + 2 / δ : ℝ) : ℂ) + (v : ℂ) * Complex.I) - 1‖) := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hZ, Nat.cast_sum]
  have hSmem : ∀ ρ ∈ hZ.toFinset, G ρ = 0 ∧ 1 / 2 + δ ≤ ρ.re ∧ |ρ.im| ≤ T := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    exact hρ
  rw [← jz_integral_indicator_sum hZ.toFinset (fun ρ => (analyticOrderNatAt G ρ : ℝ))
    (fun ρ hρ => (hSmem ρ hρ).2.2)]
  have hGc := hG.continuous
  have hHc := hH.continuous
  refine jz_assemble _ _ _ ?_ ?_ (fun _ _ => norm_nonneg _) (fun _ => norm_nonneg _) hδ hT ?_
    (fun u => jz_window G H hG hH hδ hδ' hre hfar hZ.toFinset
      (fun ρ hρ => ⟨(hSmem ρ hρ).1, (hSmem ρ hρ).2.1⟩) u)
  · unfold Function.uncurry
    fun_prop
  · fun_prop
  · have := IntervalIntegrable.sum (μ := MeasureTheory.volume) (a := -(T + 1)) (b := T + 1)
      hZ.toFinset (f := fun ρ u => (Set.Icc (ρ.im - 1 / 2) (ρ.im + 1 / 2)).indicator
        (fun _ => (analyticOrderNatAt G ρ : ℝ)) u) (fun ρ _ => by
          have h' : IntervalIntegrable (fun _ : ℝ => (analyticOrderNatAt G ρ : ℝ))
              MeasureTheory.volume (-(T + 1)) (T + 1) := intervalIntegrable_const
          rw [intervalIntegrable_iff] at h' ⊢
          exact h'.indicator measurableSet_Icc)
    rw [Finset.sum_fn] at this
    exact this

end Families.Hyp.Montgomery
