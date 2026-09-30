/-
Analytic toolkit for `prop:count` and `lem:C`.

* The triangle kernel `k₀ = k0 ς` (`lemma-A.tex`, before `lem:WH`): nonnegativity, `k₀ ≤ ς⁻¹`,
  evenness, support `|ξ| < ς`, continuity, `∫ k₀ = 1`, `TV(k₀) ≤ 2/ς`.
* Bounded variation on `ℝ`: variation of sums, of constant multiples, of the positive part and of
  monotone reparametrisations; BV ⇒ measurable; `2|f| ≤ V_f` for compactly supported `f`;
  compactly supported BV functions are integrable.
* **`eqA:APTV`** (`lemma-A.tex`, proof of `prop:count`): for `f` of bounded variation with compact
  support, `|∑_{j∈ℤ} f(a+Dj) − D⁻¹∫f| ≤ TV(f)`.
-/
import Families.Weights

noncomputable section

open scoped BigOperators ENNReal
open Finset MeasureTheory Set

namespace Families.Phase1.A

open Families

/-! ### The triangle kernel `k₀` -/

section k0

variable {ς : ℝ}

lemma k0_nonneg (hς : 0 < ς) (ξ : ℝ) : 0 ≤ k0 ς ξ :=
  mul_nonneg (inv_nonneg.mpr hς.le) (le_max_right _ _)

lemma k0_le (hς : 0 < ς) (ξ : ℝ) : k0 ς ξ ≤ ς⁻¹ := by
  unfold k0
  have h0 : 0 ≤ |ξ| / ς := div_nonneg (abs_nonneg ξ) hς.le
  have h1 : max (1 - |ξ| / ς) 0 ≤ 1 := max_le (by linarith) zero_le_one
  calc ς⁻¹ * max (1 - |ξ| / ς) 0 ≤ ς⁻¹ * 1 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hς.le)
    _ = ς⁻¹ := mul_one _

lemma k0_neg (ς ξ : ℝ) : k0 ς (-ξ) = k0 ς ξ := by
  unfold k0; rw [abs_neg]

lemma k0_sub_comm (ς a b : ℝ) : k0 ς (a - b) = k0 ς (b - a) := by
  rw [← neg_sub, k0_neg]

lemma k0_eq_zero (hς : 0 < ς) {ξ : ℝ} (h : ς ≤ |ξ|) : k0 ς ξ = 0 := by
  unfold k0
  have : 1 - |ξ| / ς ≤ 0 := by
    rw [sub_nonpos, le_div_iff₀ hς]; linarith
  rw [max_eq_right this, mul_zero]

lemma abs_lt_of_k0_ne_zero (hς : 0 < ς) {ξ : ℝ} (h : k0 ς ξ ≠ 0) : |ξ| < ς := by
  by_contra h'
  exact h (k0_eq_zero hς (not_lt.mp h'))

lemma k0_zero : k0 ς 0 = ς⁻¹ := by
  unfold k0; simp

/-- `k₀` is a non-increasing function of `|ξ|`. -/
lemma k0_le_k0_of_abs_le (hς : 0 < ς) {x y : ℝ} (h : |y| ≤ |x|) : k0 ς x ≤ k0 ς y := by
  unfold k0
  refine mul_le_mul_of_nonneg_left (max_le_max ?_ le_rfl) (inv_nonneg.mpr hς.le)
  have : |y| / ς ≤ |x| / ς := div_le_div_of_nonneg_right h hς.le
  linarith

lemma continuous_k0 (ς : ℝ) : Continuous (k0 ς) := by
  unfold k0
  exact continuous_const.mul
    ((continuous_const.sub (continuous_abs.div_const ς)).max continuous_const)

lemma k0_eq_of_nonneg (hς : 0 < ς) {ξ : ℝ} (h0 : 0 ≤ ξ) (h1 : ξ ≤ ς) :
    k0 ς ξ = ς⁻¹ - ς⁻¹ ^ 2 * ξ := by
  unfold k0
  have : 0 ≤ 1 - ξ / ς := by rw [sub_nonneg, div_le_one hς]; exact h1
  rw [abs_of_nonneg h0, max_eq_left this]
  field_simp

lemma k0_eq_zero_of_not_mem (hς : 0 < ς) {ξ : ℝ} (h : ξ ∉ Icc (-ς) ς) : k0 ς ξ = 0 := by
  refine k0_eq_zero hς ?_
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at h
  rcases h with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

/-- `∫ k₀ = 1`. -/
lemma integral_k0 (hς : 0 < ς) : ∫ ξ, k0 ς ξ = 1 := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (fun ξ h => k0_eq_zero_of_not_mem hς h),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  have hc : Continuous (k0 ς) := continuous_k0 ς
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have h2 : ∫ ξ in (0 : ℝ)..ς, k0 ς ξ = ∫ ξ in (0 : ℝ)..ς, (ς⁻¹ - ς⁻¹ ^ 2 * ξ) := by
    refine intervalIntegral.integral_congr fun ξ hξ => ?_
    rw [uIcc_of_le hς.le] at hξ
    exact k0_eq_of_nonneg hς hξ.1 hξ.2
  have h1 : ∫ ξ in (-ς)..0, k0 ς ξ = ∫ ξ in (0 : ℝ)..ς, k0 ς ξ := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := ς) (k0 ς)
    simp only [k0_neg, neg_zero] at this
    exact this.symm
  have hi : IntervalIntegrable (fun ξ : ℝ => ς⁻¹ ^ 2 * ξ) volume 0 ς :=
    (continuous_const.mul continuous_id).intervalIntegrable _ _
  rw [h1, h2, intervalIntegral.integral_sub intervalIntegrable_const hi,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id]
  have hX : ς * ς⁻¹ = 1 := mul_inv_cancel₀ hς.ne'
  simp only [smul_eq_mul]
  linear_combination (1 - ς * ς⁻¹) * hX

/-- `∫ k₀(z − y) dz = 1`. -/
lemma integral_k0_sub (hς : 0 < ς) (y : ℝ) : ∫ z, k0 ς (z - y) = 1 := by
  rw [integral_sub_right_eq_self (fun z => k0 ς z) y, integral_k0 hς]

lemma integrable_k0_sub (hς : 0 < ς) (y : ℝ) : Integrable (fun z => k0 ς (z - y)) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_k0_sub hς y]; exact one_ne_zero

/-- `TV(k₀) ≤ 2/ς` (in fact `=`). -/
lemma eVariationOn_k0_le (hς : 0 < ς) : eVariationOn (k0 ς) univ ≤ ENNReal.ofReal (2 / ς) := by
  have hl : ∀ x ≤ -ς, k0 ς x = k0 ς (-ς) := fun x hx => by
    rw [k0_eq_zero hς (by rw [abs_of_neg (by linarith)]; linarith),
      k0_eq_zero hς (by rw [abs_neg, abs_of_pos hς])]
  have hr : ∀ x, ς ≤ x → k0 ς x = k0 ς ς := fun x hx => by
    rw [k0_eq_zero hς (by rw [abs_of_pos (by linarith)]; linarith),
      k0_eq_zero hς (by rw [abs_of_pos hς])]
  rw [eVariationOn_univ_eq_Icc (k0 ς) (a := -ς) (b := ς) (by linarith) hl hr]
  have e := eVariationOn.Icc_add_Icc (k0 ς) (s := univ) (a := -ς) (b := 0) (c := ς)
    (by linarith) hς.le (mem_univ _)
  simp only [univ_inter] at e
  rw [← e]
  have hm : MonotoneOn (k0 ς) (Icc (-ς) 0) := fun x hx y hy hxy =>
    k0_le_k0_of_abs_le hς (by rw [abs_of_nonpos hx.2, abs_of_nonpos hy.2]; linarith)
  have ha : AntitoneOn (k0 ς) (Icc 0 ς) := fun x hx y hy hxy =>
    k0_le_k0_of_abs_le hς (by rw [abs_of_nonneg hx.1, abs_of_nonneg hy.1]; linarith)
  have p1 := hm.eVariationOn_eq (Set.left_mem_Icc.mpr (by linarith)) (Set.right_mem_Icc.mpr (by linarith))
  rw [inter_self] at p1
  have p2 := antitoneOn_eVariationOn_eq ha (Set.left_mem_Icc.mpr hς.le) (Set.right_mem_Icc.mpr hς.le)
  rw [inter_self] at p2
  rw [p1, p2, k0_zero, k0_eq_zero hς (by rw [abs_neg, abs_of_pos hς]),
    k0_eq_zero hς (by rw [abs_of_pos hς]), sub_zero,
    ← ENNReal.ofReal_add (inv_nonneg.mpr hς.le) (inv_nonneg.mpr hς.le)]
  apply ENNReal.ofReal_le_ofReal
  rw [div_eq_mul_inv]; linarith

end k0

/-! ### Bounded variation helpers -/

section BV

variable {α : Type*} [LinearOrder α]

lemma eVariationOn_add_le (f g : α → ℝ) (s : Set α) :
    eVariationOn (fun x => f x + g x) s ≤ eVariationOn f s + eVariationOn g s := by
  apply iSup_le
  rintro ⟨n, u, hu, us⟩
  calc ∑ i ∈ Finset.range n, edist (f (u (i + 1)) + g (u (i + 1))) (f (u i) + g (u i))
      ≤ ∑ i ∈ Finset.range n, (edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i))) :=
        Finset.sum_le_sum fun i _ => edist_add_add_le _ _ _ _
    _ = ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) +
        ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) := Finset.sum_add_distrib
    _ ≤ eVariationOn f s + eVariationOn g s :=
        add_le_add (eVariationOn.sum_le hu us) (eVariationOn.sum_le hu us)

lemma eVariationOn_const (c : ℝ) (s : Set α) : eVariationOn (fun _ : α => c) s = 0 :=
  eVariationOn.constant_on (by
    refine (Set.subsingleton_singleton (a := c)).anti ?_
    rintro _ ⟨x, _, rfl⟩; rfl)

lemma eVariationOn_sum_le {ι : Type*} (t : Finset ι) (f : ι → α → ℝ) (s : Set α) :
    eVariationOn (fun x => ∑ i ∈ t, f i x) s ≤ ∑ i ∈ t, eVariationOn (f i) s := by
  classical
  induction t using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; rw [eVariationOn_const]
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    exact (eVariationOn_add_le _ _ s).trans (add_le_add le_rfl ih)

lemma eVariationOn_const_mul_le (c : ℝ) (f : α → ℝ) (s : Set α) :
    eVariationOn (fun x => c * f x) s ≤ ENNReal.ofReal |c| * eVariationOn f s := by
  apply iSup_le
  rintro ⟨n, u, hu, us⟩
  calc ∑ i ∈ Finset.range n, edist (c * f (u (i + 1))) (c * f (u i))
      = ∑ i ∈ Finset.range n, ENNReal.ofReal |c| * edist (f (u (i + 1))) (f (u i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul,
          ENNReal.ofReal_mul (abs_nonneg c)]
    _ = ENNReal.ofReal |c| * ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) := by
        rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal |c| * eVariationOn f s := by grw [eVariationOn.sum_le hu us]

lemma eVariationOn_neg' (f : α → ℝ) (s : Set α) :
    eVariationOn (fun x => -f x) s = eVariationOn f s := by
  unfold eVariationOn
  simp only [edist_neg_neg]

lemma eVariationOn_sub_le (f g : α → ℝ) (s : Set α) :
    eVariationOn (fun x => f x - g x) s ≤ eVariationOn f s + eVariationOn g s := by
  have := eVariationOn_add_le f (fun x => -g x) s
  rw [eVariationOn_neg'] at this
  simpa only [sub_eq_add_neg] using this

lemma eVariationOn_max_zero_le (f : α → ℝ) (s : Set α) :
    eVariationOn (fun x => max (f x) 0) s ≤ eVariationOn f s := by
  have h : LipschitzOnWith 1 (fun t : ℝ => max t 0) univ :=
    (LipschitzWith.id.max_const 0).lipschitzOnWith
  have := h.comp_eVariationOn_le (g := f) (s := s) (mapsTo_univ _ _)
  simpa [Function.comp_def] using this

end BV

/-- Monotone reparametrisation does not increase the variation on `ℝ`. -/
lemma eVariationOn_comp_monotone_le (f : ℝ → ℝ) {φ : ℝ → ℝ} (hφ : Monotone φ) :
    eVariationOn (fun x => f (φ x)) univ ≤ eVariationOn f univ :=
  eVariationOn.comp_le_of_monotoneOn f φ (hφ.monotoneOn _) (mapsTo_univ _ _)

lemma eVariationOn_comp_mul_le (f : ℝ → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    eVariationOn (fun x => f (c * x)) univ ≤ eVariationOn f univ :=
  eVariationOn_comp_monotone_le f fun _ _ hxy => mul_le_mul_of_nonneg_left hxy hc

lemma eVariationOn_comp_div_le (f : ℝ → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    eVariationOn (fun x => f (x / c)) univ ≤ eVariationOn f univ :=
  eVariationOn_comp_monotone_le f fun _ _ hxy => div_le_div_of_nonneg_right hxy hc

/-- Bounded variation on `ℝ` implies measurability (Jordan decomposition). -/
lemma measurable_of_bv {f : ℝ → ℝ} (hf : BoundedVariationOn f univ) : Measurable f := by
  obtain ⟨p, q, hp, hq, hpq⟩ := hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  rw [monotoneOn_univ] at hp hq
  rw [hpq]
  exact hp.measurable.sub hq.measurable

lemma intervalIntegrable_of_bv {f : ℝ → ℝ} (hf : BoundedVariationOn f univ) (a b : ℝ) :
    IntervalIntegrable f volume a b := by
  obtain ⟨p, q, hp, hq, hpq⟩ := hf.locallyBoundedVariationOn.exists_monotoneOn_sub_monotoneOn
  rw [monotoneOn_univ] at hp hq
  rw [hpq]
  exact hp.intervalIntegrable.sub hq.intervalIntegrable

/-- For `f` of bounded variation vanishing off `[A,B]`: `2|f(x)| ≤ V_f`. -/
lemma two_mul_abs_le_variation {f : ℝ → ℝ} (hf : BoundedVariationOn f univ) {A B : ℝ}
    (hsupp : ∀ x, f x ≠ 0 → x ∈ Icc A B) (x : ℝ) :
    2 * |f x| ≤ (eVariationOn f univ).toReal := by
  set a := min A x - 1 with ha
  set b := max B x + 1 with hb
  have fa : f a = 0 := by
    by_contra h
    have := (hsupp a h).1
    have := min_le_left A x
    linarith
  have fb : f b = 0 := by
    by_contra h
    have := (hsupp b h).2
    have := le_max_left B x
    linarith
  have hax : a ≤ x := by have := min_le_right A x; linarith
  have hxb : x ≤ b := by have := le_max_right B x; linarith
  have h1 := eVariationOn.edist_le f (s := Icc a x) (Set.left_mem_Icc.mpr hax) (Set.right_mem_Icc.mpr hax)
  have h2 := eVariationOn.edist_le f (s := Icc x b) (Set.left_mem_Icc.mpr hxb) (Set.right_mem_Icc.mpr hxb)
  have e := eVariationOn.Icc_add_Icc f (s := univ) hax hxb (mem_univ x)
  simp only [univ_inter] at e
  have hmono : eVariationOn f (Icc a b) ≤ eVariationOn f univ := eVariationOn.mono f (subset_univ _)
  rw [fa, edist_dist, Real.dist_eq, zero_sub, abs_neg] at h1
  rw [fb, edist_dist, Real.dist_eq, sub_zero] at h2
  have htot : ENNReal.ofReal (2 * |f x|) ≤ eVariationOn f univ := by
    rw [two_mul, ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    calc ENNReal.ofReal |f x| + ENNReal.ofReal |f x|
        ≤ eVariationOn f (Icc a x) + eVariationOn f (Icc x b) := add_le_add h1 h2
      _ = eVariationOn f (Icc a b) := e
      _ ≤ _ := hmono
  exact (ENNReal.ofReal_le_iff_le_toReal hf).mp htot

/-- A measurable function bounded by `M` and vanishing off `[A,B]` is integrable. -/
lemma integrable_of_bound_of_support {f : ℝ → ℝ} (hf : AEStronglyMeasurable f volume) (M : ℝ)
    (hM : ∀ x, |f x| ≤ M) {A B : ℝ} (hsupp : ∀ x, f x ≠ 0 → x ∈ Icc A B) : Integrable f := by
  have h1 : IntegrableOn f (Icc A B) volume :=
    Measure.integrableOn_of_bounded (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) hf
      (M := M) (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hM x)
  refine (integrableOn_iff_integrable_of_support_subset ?_).mp h1
  intro x hx
  exact hsupp x hx

lemma integrable_of_bv {f : ℝ → ℝ} (hf : BoundedVariationOn f univ) {A B : ℝ}
    (hsupp : ∀ x, f x ≠ 0 → x ∈ Icc A B) : Integrable f :=
  integrable_of_bound_of_support (measurable_of_bv hf).aestronglyMeasurable
    ((eVariationOn f univ).toReal / 2)
    (fun x => by have := two_mul_abs_le_variation hf hsupp x; linarith) hsupp

/-! ### `eqA:APTV` -/

/-- **`eqA:APTV`, `D = 1`.** For `F` of bounded variation on `ℝ` vanishing off `[A,B]`:
`|∑_{j∈ℤ} F(j) − ∫F| ≤ TV(F)`. -/
theorem aptv_one {F : ℝ → ℝ} (hF : BoundedVariationOn F univ) {A B : ℝ}
    (hsupp : ∀ x, F x ≠ 0 → x ∈ Icc A B) :
    Summable (fun j : ℤ => F j) ∧ |∑' j : ℤ, F j - ∫ x, F x| ≤ (eVariationOn F univ).toReal := by
  set j0 : ℤ := ⌊A⌋ - 1 with hj0
  set n : ℕ := (⌈B⌉ - j0 + 1).toNat with hn
  set t : ℕ → ℝ := fun i => (j0 : ℝ) + i with ht
  have hA : (j0 : ℝ) < A := by
    have := Int.floor_le A
    rw [hj0]; push_cast; linarith
  have hnB : B < (j0 : ℝ) + n := by
    have h1 : (⌈B⌉ - j0 + 1 : ℤ) ≤ n := by rw [hn]; exact Int.self_le_toNat _
    have h2 : ((⌈B⌉ - j0 + 1 : ℤ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1
    have := Int.le_ceil B
    push_cast at h2
    linarith
  -- the embedding `i ↦ j0 + i`
  let e : ℕ ↪ ℤ := ⟨fun i => j0 + (i : ℤ), fun a b h => by simpa using h⟩
  have he : ∀ i, e i = j0 + (i : ℤ) := fun i => rfl
  have hzero : ∀ j : ℤ, j ∉ (Finset.range n).map e → F j = 0 := by
    intro j hj
    by_contra hFj
    obtain ⟨h1, h2⟩ := hsupp j hFj
    apply hj
    rw [Finset.mem_map]
    refine ⟨(j - j0).toNat, ?_, ?_⟩
    · rw [Finset.mem_range]
      have hjj : j0 ≤ j := by
        have : (j0 : ℝ) < j := lt_of_lt_of_le hA h1
        exact_mod_cast this.le
      have : (j : ℝ) < (j0 : ℝ) + n := lt_of_le_of_lt h2 hnB
      have : j < j0 + n := by exact_mod_cast this
      omega
    · have hjj : j0 ≤ j := by
        have : (j0 : ℝ) < j := lt_of_lt_of_le hA h1
        exact_mod_cast this.le
      rw [he]
      omega
  have hsum : Summable (fun j : ℤ => F j) := summable_of_ne_finset_zero hzero
  refine ⟨hsum, ?_⟩
  rw [tsum_eq_sum hzero, Finset.sum_map]
  have hsum' : ∑ i ∈ Finset.range n, F (e i) = ∑ i ∈ Finset.range n, F (t i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [he]
    simp only [ht]
    push_cast; rfl
  rw [hsum']
  -- the integral as a sum over unit intervals
  have hint : ∫ x, F x = ∑ i ∈ Finset.range n, ∫ x in t i..t (i + 1), F x := by
    rw [intervalIntegral.sum_integral_adjacent_intervals
      (fun k _ => intervalIntegrable_of_bv hF _ _)]
    have ht0 : t 0 = j0 := by simp [ht]
    have htn : t n = j0 + n := by simp [ht]
    rw [ht0, htn, intervalIntegral.integral_of_le (by linarith),
      setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro x hx
    by_contra hFx
    obtain ⟨h1, h2⟩ := hsupp x hFx
    exact hx ⟨lt_of_lt_of_le hA h1, by linarith⟩
  rw [hint, ← Finset.sum_sub_distrib]
  have hstep : ∀ i ∈ Finset.range n,
      |F (t i) - ∫ x in t i..t (i + 1), F x|
        ≤ (eVariationOn F (Icc (t i) (t (i + 1)))).toReal := by
    intro i _
    have hti : t (i + 1) = t i + 1 := by simp only [ht]; push_cast; ring
    have hle : t i ≤ t (i + 1) := by rw [hti]; linarith
    have hfin : eVariationOn F (Icc (t i) (t (i + 1))) ≠ ⊤ :=
      ne_top_of_le_ne_top hF (eVariationOn.mono F (subset_univ _))
    have hconst : F (t i) = ∫ x in t i..t (i + 1), F (t i) := by
      rw [intervalIntegral.integral_const, hti]; simp
    rw [hconst, ← intervalIntegral.integral_sub intervalIntegrable_const
      (intervalIntegrable_of_bv hF _ _), ← Real.norm_eq_abs]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := t i) (b := t (i + 1))
      (f := fun x => F (t i) - F x) (C := (eVariationOn F (Icc (t i) (t (i + 1)))).toReal)
      (fun x hx => by
        rw [uIoc_of_le hle] at hx
        have hxI : x ∈ Icc (t i) (t (i + 1)) := ⟨hx.1.le, hx.2⟩
        have hed := eVariationOn.edist_le F (Set.left_mem_Icc.mpr hle) hxI
        rw [edist_dist] at hed
        rw [Real.norm_eq_abs, ← Real.dist_eq]
        exact (ENNReal.ofReal_le_iff_le_toReal hfin).mp hed)
    rw [hti, add_sub_cancel_left, abs_one, mul_one] at this
    rw [hti]
    exact this
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hstep).trans ?_)
  have hmono : Monotone t := fun a b hab => by
    simp only [ht]
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  have hfin : ∀ i ∈ Finset.range n, eVariationOn F (Icc (t i) (t (i + 1))) ≠ ⊤ := fun i _ =>
    ne_top_of_le_ne_top hF (eVariationOn.mono F (subset_univ _))
  rw [← ENNReal.toReal_sum hfin, eVariationOn.sum' F hmono]
  exact ENNReal.toReal_mono hF (eVariationOn.mono F (subset_univ _))

/-- **`eqA:APTV`.** For `f` of bounded variation on `ℝ` vanishing off `[A,B]`, `a ∈ ℝ`, `D > 0`:
`|∑_{j∈ℤ} f(a+Dj) − D⁻¹∫f| ≤ TV(f)` (and the sum has finite support). -/
theorem aptv {f : ℝ → ℝ} (hf : BoundedVariationOn f univ) {A B : ℝ}
    (hsupp : ∀ x, f x ≠ 0 → x ∈ Icc A B) (a D : ℝ) (hD : 0 < D) :
    Summable (fun j : ℤ => f (a + D * j)) ∧
      |∑' j : ℤ, f (a + D * j) - D⁻¹ * ∫ x, f x| ≤ (eVariationOn f univ).toReal := by
  set F : ℝ → ℝ := fun x => f (a + D * x) with hFdef
  have hFvar : eVariationOn F univ ≤ eVariationOn f univ :=
    eVariationOn_comp_monotone_le f fun x y hxy => by
      have := mul_le_mul_of_nonneg_left hxy hD.le; linarith
  have hF : BoundedVariationOn F univ := ne_top_of_le_ne_top hf hFvar
  have hFsupp : ∀ x, F x ≠ 0 → x ∈ Icc ((A - a) / D) ((B - a) / D) := by
    intro x hx
    obtain ⟨h1, h2⟩ := hsupp _ hx
    constructor
    · rw [div_le_iff₀ hD]; linarith
    · rw [le_div_iff₀ hD]; linarith
  have hint : ∫ x, F x = D⁻¹ * ∫ x, f x := by
    have h1 := Measure.integral_comp_mul_left (fun y => f (a + y)) D
    simp only [smul_eq_mul] at h1
    rw [hFdef]
    simp only at h1 ⊢
    rw [h1, integral_add_left_eq_self (fun y => f y) a, abs_of_pos (inv_pos.mpr hD)]
  obtain ⟨hs, hb⟩ := aptv_one hF hFsupp
  refine ⟨hs, ?_⟩
  rw [← hint]
  exact hb.trans (ENNReal.toReal_mono hf hFvar)

end Families.Phase1.A
