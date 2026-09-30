/-
The spoke weights `f_k(q) = 𝔴(q/Q) k₀(k/(qv) − y)` of `prop:count` /
`lem:C` and the evaluation of the main terms by the substitution `q = |k|/(v|z|)`
(`lemma-A.tex`, proof of `prop:count`, "Main term").

* `spokeF`: `f_k` (extended by `0` to `q ≤ 0`); support in `[0,Q]`, `|f_k| ≤ V_𝔴/(2ς)`,
  `TV(f_k) ≤ 2V_𝔴/ς`, and `f_k ≡ 0` for `|k|` beyond the spoke range.
* `rhoGen 𝔴 c Q v z = (vz)^{-2} ∑_{1≤k≤v|z|Q} k c(k) 𝔴(k/(v|z|Q))` (`c(k) = G_S(k,r)` gives `ρ_r` of
  `lem:C`; `c(k) = φ(k)/k` gives `ρ_{𝔴,v}` of `eqA:rho`).
* `main_term`: `∑_{1≤k≤K₀} (c(k)/v)(∫f_k + ∫f_{−k}) = ∫ k₀(z−y) rhoGen(z) dz`, with integrability.
-/
import Families.Phase1.A.Toolkit

noncomputable section

open scoped BigOperators ENNReal
open Finset MeasureTheory Set

namespace Families.Phase1.A

open Families

/-! ### Definitions -/

/-- The spoke weight `f_k(x) = 𝔴(x/Q) k₀(k/(xv) − y)` for `x > 0`, and `0` for `x ≤ 0`. -/
def spokeF (𝔴 : ℝ → ℝ) (Q ς y : ℝ) (v : ℕ) (k : ℤ) (x : ℝ) : ℝ :=
  𝔴 (x / Q) * (if 0 < x then k0 ς ((k : ℝ) / (x * v) - y) else 0)

/-- `(vz)^{-2} ∑_{1≤k≤v|z|Q} k c(k) 𝔴(k/(v|z|Q))`. -/
def rhoGen (𝔴 : ℝ → ℝ) (c : ℕ → ℝ) (Q : ℝ) (v : ℕ) (z : ℝ) : ℝ :=
  ((v : ℝ) * z)⁻¹ ^ 2 * ∑ k ∈ Finset.Icc 1 ⌊(v : ℝ) * |z| * Q⌋₊,
    (k : ℝ) * c k * 𝔴 (k / ((v : ℝ) * |z| * Q))

/-- The integrand of the `k`-th main term after the substitution, `c = k/v`:
`(c/z²) 𝔴(c/(|z|Q)) k₀(z − y)`. -/
def hfun (𝔴 : ℝ → ℝ) (Q ς y c : ℝ) (z : ℝ) : ℝ :=
  c / z ^ 2 * 𝔴 (c / (|z| * Q)) * k0 ς (z - y)

/-! ### Elementary facts -/

section facts

variable {𝔴 : ℝ → ℝ} (hbv : BoundedVariationOn 𝔴 univ) (hsupp : ∀ u, 𝔴 u ≠ 0 → 0 < u ∧ u ≤ 1)
include hbv hsupp

omit hbv in
lemma supp_Icc01 : ∀ u, 𝔴 u ≠ 0 → u ∈ Icc (0 : ℝ) 1 :=
  fun u hu => ⟨(hsupp u hu).1.le, (hsupp u hu).2⟩

omit hbv in
lemma w_eq_zero_of_nonpos {u : ℝ} (hu : u ≤ 0) : 𝔴 u = 0 := by
  by_contra h; linarith [(hsupp u h).1]

omit hbv in
lemma w_eq_zero_of_gt_one {u : ℝ} (hu : 1 < u) : 𝔴 u = 0 := by
  by_contra h; linarith [(hsupp u h).2]

lemma abs_w_le (u : ℝ) : |𝔴 u| ≤ (eVariationOn 𝔴 univ).toReal / 2 := by
  have := two_mul_abs_le_variation hbv (supp_Icc01 hsupp) u; linarith

omit hsupp in
lemma measurable_w : Measurable 𝔴 := measurable_of_bv hbv

end facts

section spokeF

variable {𝔴 : ℝ → ℝ} (hbv : BoundedVariationOn 𝔴 univ) (hsupp : ∀ u, 𝔴 u ≠ 0 → 0 < u ∧ u ≤ 1)
  {Q ς y : ℝ} {v : ℕ}
include hbv hsupp

omit hbv in
lemma spokeF_supp (hQ : 0 < Q) (k : ℤ) :
    ∀ x, spokeF 𝔴 Q ς y v k x ≠ 0 → x ∈ Icc 0 Q := by
  intro x hx
  have hw : 𝔴 (x / Q) ≠ 0 := left_ne_zero_of_mul hx
  obtain ⟨h1, h2⟩ := hsupp _ hw
  exact ⟨(div_pos_iff_of_pos_right hQ).mp h1 |>.le, (div_le_one hQ).mp h2⟩

omit hbv hsupp in
lemma spokeF_of_pos (k : ℤ) {x : ℝ} (hx : 0 < x) :
    spokeF 𝔴 Q ς y v k x = 𝔴 (x / Q) * k0 ς ((k : ℝ) / (x * v) - y) := by
  unfold spokeF; rw [if_pos hx]

lemma abs_spokeF_le (hς : 0 < ς) (k : ℤ) (x : ℝ) :
    |spokeF 𝔴 Q ς y v k x| ≤ (eVariationOn 𝔴 univ).toReal / 2 * ς⁻¹ := by
  unfold spokeF
  rw [abs_mul]
  refine mul_le_mul (abs_w_le hbv hsupp _) ?_ (abs_nonneg _) (by positivity)
  split_ifs
  · rw [abs_of_nonneg (k0_nonneg hς _)]; exact k0_le hς _
  · rw [abs_zero]; positivity

omit hbv in
/-- `f_k ≡ 0` once `|k| > K₀`, where `K₀` bounds `v|z|Q` on the support of `k₀(· − y)`. -/
lemma spokeF_eq_zero_of_lt (hQ : 0 < Q) (hς : 0 < ς) (hv : 1 ≤ v) (K0 : ℕ)
    (hK0 : ∀ z, |z - y| < ς → (v : ℝ) * |z| * Q < K0 + 1) {k : ℤ} (hk : (K0 : ℤ) < |k|) (x : ℝ) :
    spokeF 𝔴 Q ς y v k x = 0 := by
  by_contra hne
  obtain ⟨hx0, hxQ⟩ := spokeF_supp hsupp hQ k x hne
  have hx : 0 < x := by
    rcases eq_or_lt_of_le hx0 with h | h
    · exfalso; apply hne; unfold spokeF; rw [if_neg (by rw [← h]; exact lt_irrefl 0), mul_zero]
    · exact h
  rw [spokeF_of_pos k hx] at hne
  have hk0 : k0 ς ((k : ℝ) / (x * v) - y) ≠ 0 := right_ne_zero_of_mul hne
  have h1 := hK0 _ (abs_lt_of_k0_ne_zero hς hk0)
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have e : (v : ℝ) * |(k : ℝ) / (x * v)| * Q = |(k : ℝ)| * (Q / x) := by
    rw [abs_div, abs_of_pos (mul_pos hx hv')]; field_simp
  rw [e] at h1
  have hQx : 1 ≤ Q / x := by rw [le_div_iff₀ hx]; linarith
  have h2 : |(k : ℝ)| < K0 + 1 := by
    have : |(k : ℝ)| ≤ |(k : ℝ)| * (Q / x) := le_mul_of_one_le_right (abs_nonneg _) hQx
    linarith
  have h3 : ((K0 : ℤ) : ℝ) + 1 ≤ |(k : ℝ)| := by
    have : (K0 : ℤ) + 1 ≤ |k| := hk
    rw [← Int.cast_abs]; exact_mod_cast this
  push_cast at h3
  linarith

omit hbv hsupp in
/-- The `k₀`-factor of `f_k` vanishes near `0` and is a monotone reparametrisation of `k₀` away
from `0`, so its variation is at most `TV(k₀) ≤ 2/ς`. -/
lemma eVariationOn_spokeG_le (hς : 0 < ς) (hv : 1 ≤ v) {k : ℤ} (hk : k ≠ 0) :
    eVariationOn (fun x : ℝ => if 0 < x then k0 ς ((k : ℝ) / (x * v) - y) else 0) univ
      ≤ ENNReal.ofReal (2 / ς) := by
  set g := fun x : ℝ => if 0 < x then k0 ς ((k : ℝ) / (x * v) - y) else 0 with hg
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have hk' : 0 < |(k : ℝ)| := abs_pos.mpr (by exact_mod_cast hk)
  have hyς : 0 < |y| + ς := by positivity
  set x0 := |(k : ℝ)| / (v * (|y| + ς)) with hx0
  have hx0pos : 0 < x0 := by positivity
  have hzero : ∀ x ∈ Iic x0, g x = 0 := by
    intro x hx
    simp only [hg]
    split_ifs with hxpos
    · apply k0_eq_zero hς
      have h1 : |y| + ς ≤ |(k : ℝ) / (x * v)| := by
        rw [abs_div, abs_of_pos (mul_pos hxpos hv'), le_div_iff₀ (mul_pos hxpos hv')]
        have : x * v ≤ x0 * v := mul_le_mul_of_nonneg_right hx hv'.le
        have e : x0 * v * (|y| + ς) = |(k : ℝ)| := by rw [hx0]; field_simp
        nlinarith
      have h2 : |(k : ℝ) / (x * v)| - |y| ≤ |(k : ℝ) / (x * v) - y| := abs_sub_abs_le_abs_sub _ _
      linarith
    · rfl
  have hunion : (univ : Set ℝ) = Iic x0 ∪ Ici x0 := (Iic_union_Ici).symm
  rw [hunion, eVariationOn.union g isGreatest_Iic isLeast_Ici]
  have h1 : eVariationOn g (Iic x0) = 0 := eVariationOn.constant_on (by
    refine (Set.subsingleton_singleton (a := (0 : ℝ))).anti ?_
    rintro _ ⟨x, hx, rfl⟩; exact hzero x hx)
  set φ : ℝ → ℝ := fun x => (k : ℝ) / (x * v) - y with hφ
  have h2 : eVariationOn g (Ici x0) = eVariationOn (k0 ς ∘ φ) (Ici x0) :=
    eVariationOn.eq_of_eqOn fun x hx => by
      simp only [hg, Function.comp_apply, hφ]
      rw [if_pos (lt_of_lt_of_le hx0pos hx)]
  rw [h1, zero_add, h2]
  refine le_trans ?_ (eVariationOn_k0_le hς)
  rcases lt_or_gt_of_ne hk with hkneg | hkpos
  · refine eVariationOn.comp_le_of_monotoneOn (k0 ς) φ ?_ (mapsTo_univ _ _)
    intro a ha b hb hab
    have ha0 : 0 < a := lt_of_lt_of_le hx0pos ha
    have hkR : (k : ℝ) < 0 := by exact_mod_cast hkneg
    simp only [hφ]
    have : (k : ℝ) / (a * v) ≤ (k : ℝ) / (b * v) := by
      rw [div_le_div_iff₀ (mul_pos ha0 hv') (mul_pos (lt_of_lt_of_le ha0 hab) hv')]
      exact mul_le_mul_of_nonpos_left (mul_le_mul_of_nonneg_right hab hv'.le) hkR.le
    linarith
  · refine eVariationOn.comp_le_of_antitoneOn (k0 ς) φ ?_ (mapsTo_univ _ _)
    intro a ha b hb hab
    have ha0 : 0 < a := lt_of_lt_of_le hx0pos ha
    have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
    simp only [hφ]
    have : (k : ℝ) / (b * v) ≤ (k : ℝ) / (a * v) := by
      rw [div_le_div_iff₀ (mul_pos (lt_of_lt_of_le ha0 hab) hv') (mul_pos ha0 hv')]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hab hv'.le) hkR.le
    linarith

/-- `TV(f_k) ≤ 2 V_𝔴/ς` (`lemma-A.tex`: `TV(f_k) ≤ (2‖𝔴‖_∞ + V_𝔴)/ς ≤ 2V_𝔴/ς`). -/
lemma eVariationOn_spokeF_le (hQ : 0 < Q) (hς : 0 < ς) (hv : 1 ≤ v) {k : ℤ} (hk : k ≠ 0) :
    eVariationOn (spokeF 𝔴 Q ς y v k) univ
      ≤ ENNReal.ofReal (2 * (eVariationOn 𝔴 univ).toReal / ς) := by
  set V := (eVariationOn 𝔴 univ).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  set f1 : ℝ → ℝ := fun x => 𝔴 (x / Q)
  set g1 : ℝ → ℝ := fun x => if 0 < x then k0 ς ((k : ℝ) / (x * v) - y) else 0
  have hfg : spokeF 𝔴 Q ς y v k = f1 * g1 := rfl
  have hf1 : ∀ x ∈ (univ : Set ℝ), ‖f1 x‖ₑ ≤ ENNReal.ofReal (V / 2) := fun x _ => by
    rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (abs_w_le hbv hsupp _)
  have hg1 : ∀ x ∈ (univ : Set ℝ), ‖g1 x‖ₑ ≤ ENNReal.ofReal ς⁻¹ := fun x _ => by
    rw [Real.enorm_eq_ofReal_abs]
    refine ENNReal.ofReal_le_ofReal ?_
    simp only [g1]
    split_ifs
    · rw [abs_of_nonneg (k0_nonneg hς _)]; exact k0_le hς _
    · rw [abs_zero]; positivity
  have hTVf1 : eVariationOn f1 univ ≤ ENNReal.ofReal V := by
    rw [hV, ENNReal.ofReal_toReal hbv]
    exact eVariationOn_comp_div_le 𝔴 hQ.le
  have hTVg1 : eVariationOn g1 univ ≤ ENNReal.ofReal (2 / ς) :=
    eVariationOn_spokeG_le hς hv hk
  rw [hfg]
  refine (eVariation_mul_le hf1 hg1).trans ?_
  calc ENNReal.ofReal (V / 2) * eVariationOn g1 univ + ENNReal.ofReal ς⁻¹ * eVariationOn f1 univ
      ≤ ENNReal.ofReal (V / 2) * ENNReal.ofReal (2 / ς) + ENNReal.ofReal ς⁻¹ * ENNReal.ofReal V := by
        gcongr
    _ = ENNReal.ofReal (2 * V / ς) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        field_simp
        ring

lemma bv_spokeF (hQ : 0 < Q) (hς : 0 < ς) (hv : 1 ≤ v) {k : ℤ} (hk : k ≠ 0) :
    BoundedVariationOn (spokeF 𝔴 Q ς y v k) univ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (eVariationOn_spokeF_le hbv hsupp hQ hς hv hk)

end spokeF

/-! ### The substitution `x = c/z` -/

/-- `∫_{x>0} g(x) dx = ∫_{z>0} (c/z²) g(c/z) dz` for `c > 0`. -/
lemma integral_Ioi_inv_subst (g : ℝ → ℝ) {c : ℝ} (hc : 0 < c) :
    ∫ x in Ioi (0 : ℝ), g x = ∫ z in Ioi (0 : ℝ), c / z ^ 2 * g (c / z) := by
  have h1 := integral_comp_rpow_Ioi g (p := -1) (by norm_num)
  set h : ℝ → ℝ := fun x => (x ^ 2)⁻¹ * g x⁻¹ with hh
  have h2 : ∫ x in Ioi (0 : ℝ), (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • g (x ^ (-1 : ℝ)) =
      ∫ x in Ioi (0 : ℝ), h x := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    simp only [smul_eq_mul, hh]
    have hx0 : 0 ≤ x := le_of_lt hx
    rw [Real.rpow_neg_one, abs_neg, abs_one, one_mul, show (-1 : ℝ) - 1 = -2 by norm_num,
      Real.rpow_neg hx0, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [← h1, h2]
  have h3 := integral_comp_mul_left_Ioi h 0 (inv_pos.mpr hc)
  rw [mul_zero, inv_inv, smul_eq_mul] at h3
  have h4 : ∫ z in Ioi (0 : ℝ), c / z ^ 2 * g (c / z) = ∫ z in Ioi (0 : ℝ), c⁻¹ * h (c⁻¹ * z) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun z hz => ?_
    simp only [hh]
    have hz0 : z ≠ 0 := (ne_of_lt hz).symm
    have hc0 : c ≠ 0 := hc.ne'
    rw [mul_inv, inv_inv, show c / z = (c⁻¹)⁻¹ * z⁻¹ by rw [inv_inv, div_eq_mul_inv]]
    field_simp
  rw [h4, integral_const_mul, h3, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]

section mainterm

variable {𝔴 : ℝ → ℝ} (hbv : BoundedVariationOn 𝔴 univ) (hsupp : ∀ u, 𝔴 u ≠ 0 → 0 < u ∧ u ≤ 1)
  {Q ς : ℝ} {v : ℕ}
include hbv hsupp

omit hbv hsupp in
lemma integral_spokeF_eq_Ioi (y : ℝ) (k : ℤ) :
    ∫ x, spokeF 𝔴 Q ς y v k x = ∫ x in Ioi (0 : ℝ), spokeF 𝔴 Q ς y v k x := by
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
  unfold spokeF
  rw [if_neg (by simpa using hx), mul_zero]

omit hbv hsupp in
/-- Positive spokes: `∫ f_j = ∫_{z>0} hfun(j/v)`. -/
lemma integral_spokeF_pos (hv : 1 ≤ v) (y : ℝ) (j : ℕ) (hj : 1 ≤ j) :
    ∫ x, spokeF 𝔴 Q ς y v (j : ℤ) x = ∫ z in Ioi (0 : ℝ), hfun 𝔴 Q ς y ((j : ℝ) / v) z := by
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have hc : (0 : ℝ) < (j : ℝ) / v := div_pos (by exact_mod_cast hj) hv'
  rw [integral_spokeF_eq_Ioi,
    setIntegral_congr_fun measurableSet_Ioi (fun x hx => spokeF_of_pos (k := (j : ℤ)) hx),
    integral_Ioi_inv_subst _ hc]
  refine setIntegral_congr_fun measurableSet_Ioi fun z hz => ?_
  have hz0 : 0 < z := hz
  simp only [hfun]
  rw [abs_of_pos hz0]
  have e1 : (j : ℝ) / v / z / Q = (j : ℝ) / v / (z * Q) := by rw [div_div]
  have e2 : ((j : ℤ) : ℝ) / ((j : ℝ) / v / z * v) - y = z - y := by
    push_cast
    have : (j : ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
    field_simp
  rw [e1, e2]; ring

omit hbv hsupp in
/-- Negative spokes: `∫ f_{−j} = ∫_{z≤0} hfun(j/v)`. -/
lemma integral_spokeF_neg (hv : 1 ≤ v) (y : ℝ) (j : ℕ) (hj : 1 ≤ j) :
    ∫ x, spokeF 𝔴 Q ς y v (-(j : ℤ)) x = ∫ z in Iic (0 : ℝ), hfun 𝔴 Q ς y ((j : ℝ) / v) z := by
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have hc : (0 : ℝ) < (j : ℝ) / v := div_pos (by exact_mod_cast hj) hv'
  have hjne : (j : ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
  rw [integral_spokeF_eq_Ioi,
    setIntegral_congr_fun measurableSet_Ioi (fun x hx => spokeF_of_pos (k := -(j : ℤ)) hx),
    integral_Ioi_inv_subst _ hc]
  have hneg := integral_comp_neg_Ioi 0 (hfun 𝔴 Q ς y ((j : ℝ) / v))
  rw [neg_zero] at hneg
  rw [← hneg]
  refine setIntegral_congr_fun measurableSet_Ioi fun z hz => ?_
  have hz0 : 0 < z := hz
  simp only [hfun]
  rw [abs_neg, abs_of_pos hz0, neg_sq]
  have e1 : (j : ℝ) / v / z / Q = (j : ℝ) / v / (z * Q) := by rw [div_div]
  have e2 : ((-(j : ℤ) : ℤ) : ℝ) / ((j : ℝ) / v / z * v) - y = -(z + y) := by
    push_cast
    field_simp
    ring
  rw [e1, e2, k0_neg, show -z - y = -(z + y) by ring, k0_neg]
  ring

lemma integrable_hfun (hQ : 0 < Q) (hς : 0 < ς) (y : ℝ) {c : ℝ} (hc : 0 < c) :
    Integrable (hfun 𝔴 Q ς y c) := by
  set M := (eVariationOn 𝔴 univ).toReal / 2
  have hM : 0 ≤ M := by positivity
  refine integrable_of_bound_of_support (A := y - ς) (B := y + ς) ?_ (Q ^ 2 / c * M * ς⁻¹) ?_ ?_
  · have hw := measurable_w hbv
    have hk := (continuous_k0 ς).measurable
    unfold hfun
    fun_prop
  · intro z
    unfold hfun
    by_cases hw : 𝔴 (c / (|z| * Q)) = 0
    · rw [hw, mul_zero, zero_mul, abs_zero]; positivity
    · obtain ⟨h1, h2⟩ := hsupp _ hw
      have hz : 0 < |z| := by
        by_contra h
        have : |z| = 0 := le_antisymm (not_lt.mp h) (abs_nonneg z)
        rw [this, zero_mul, div_zero] at h1; exact lt_irrefl 0 h1
      have hzQ : c / Q ≤ |z| := by
        rw [div_le_one (mul_pos hz hQ)] at h2
        rw [div_le_iff₀ hQ]; linarith
      have hz2 : 0 < z ^ 2 := by rw [← sq_abs]; positivity
      have h3 : c ≤ Q * |z| := by rw [div_le_iff₀ hQ] at hzQ; linarith
      have h4 : c * c ≤ (Q * |z|) * (Q * |z|) := mul_self_le_mul_self hc.le h3
      have h5 : (Q * |z|) * (Q * |z|) = Q ^ 2 * z ^ 2 := by rw [← sq_abs z]; ring
      have hcz : c / z ^ 2 ≤ Q ^ 2 / c := by
        rw [div_le_div_iff₀ hz2 hc]; linarith
      rw [abs_mul, abs_mul, abs_of_pos (div_pos hc hz2), abs_of_nonneg (k0_nonneg hς _)]
      have hw := abs_w_le hbv hsupp (c / (|z| * Q))
      have hk1 := k0_le hς (z - y)
      have hk2 := k0_nonneg hς (z - y)
      have hwn := abs_nonneg (𝔴 (c / (|z| * Q)))
      exact mul_le_mul (mul_le_mul hcz hw hwn (by positivity)) hk1 hk2 (by positivity)
  · intro z hz
    have hk : k0 ς (z - y) ≠ 0 := right_ne_zero_of_mul hz
    have := abs_lt_of_k0_ne_zero hς hk
    rw [abs_lt] at this
    exact ⟨by linarith, by linarith⟩

omit hbv hsupp in
lemma sum_range_succ_eq_sum_Icc (f : ℕ → ℝ) (K : ℕ) :
    ∑ n ∈ Finset.range K, f (n + 1) = ∑ k ∈ Finset.Icc 1 K, f k := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1)]

/-- **Main term** (`lemma-A.tex`, proof of `prop:count`; `lem:C`, "The main terms are evaluated by
the substitution of Proposition `prop:count`"). If `v|z|Q < K₀ + 1` whenever `|z − y| < ς`, then
`∑_{1≤k≤K₀} (c(k)/v)(∫f_k + ∫f_{−k}) = ∫ k₀(z−y) rhoGen(z) dz`, and the integrand is integrable. -/
theorem main_term (hQ : 0 < Q) (hς : 0 < ς) (hv : 1 ≤ v) (y : ℝ) (c : ℕ → ℝ) (K0 : ℕ)
    (hK0 : ∀ z, |z - y| < ς → (v : ℝ) * |z| * Q < K0 + 1) :
    Integrable (fun z => k0 ς (z - y) * rhoGen 𝔴 c Q v z) ∧
    ∑ n ∈ Finset.range K0, c (n + 1) / v *
        ((∫ x, spokeF 𝔴 Q ς y v ((n + 1 : ℕ) : ℤ) x) +
          ∫ x, spokeF 𝔴 Q ς y v (-((n + 1 : ℕ) : ℤ)) x)
      = ∫ z, k0 ς (z - y) * rhoGen 𝔴 c Q v z := by
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have hcpos : ∀ n : ℕ, (0 : ℝ) < ((n + 1 : ℕ) : ℝ) / v := fun n =>
    div_pos (by exact_mod_cast Nat.succ_pos n) hv'
  -- pointwise identity
  have hpt : ∀ z, ∑ n ∈ Finset.range K0, c (n + 1) / v * hfun 𝔴 Q ς y (((n + 1 : ℕ) : ℝ) / v) z =
      k0 ς (z - y) * rhoGen 𝔴 c Q v z := by
    intro z
    by_cases hkz : k0 ς (z - y) = 0
    · rw [hkz, zero_mul]
      exact Finset.sum_eq_zero fun n _ => by simp [hfun, hkz]
    by_cases hz : z = 0
    · subst hz
      simp [hfun, rhoGen]
    have hzabs : 0 < |z| := abs_pos.mpr hz
    have hlt := hK0 z (abs_lt_of_k0_ne_zero hς hkz)
    have hfl : ⌊(v : ℝ) * |z| * Q⌋₊ ≤ K0 := by
      have := Nat.floor_lt (by positivity : (0 : ℝ) ≤ v * |z| * Q) |>.mpr
        (show (v : ℝ) * |z| * Q < ((K0 + 1 : ℕ) : ℝ) by push_cast; exact hlt)
      omega
    unfold rhoGen
    rw [sum_range_succ_eq_sum_Icc (fun k => c k / v * hfun 𝔴 Q ς y ((k : ℝ) / v) z) K0,
      Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_subset (Finset.Icc_subset_Icc_right hfl)]
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hfun]
      have e : (k : ℝ) / v / (|z| * Q) = k / (v * |z| * Q) := by
        field_simp
      rw [e]
      field_simp
    · intro k hk hk'
      rw [Finset.mem_Icc] at hk hk'
      have hk1 : ⌊(v : ℝ) * |z| * Q⌋₊ < k := by omega
      have : (v : ℝ) * |z| * Q < k := (Nat.floor_lt (by positivity)).mp hk1
      have hw : 𝔴 ((k : ℝ) / (v * |z| * Q)) = 0 :=
        w_eq_zero_of_gt_one hsupp (by rw [one_lt_div (by positivity)]; exact this)
      simp only [hfun]
      have e : (k : ℝ) / v / (|z| * Q) = k / (v * |z| * Q) := by field_simp
      rw [e, hw]; ring
  have hint : ∀ n ∈ Finset.range K0,
      Integrable (fun z => c (n + 1) / v * hfun 𝔴 Q ς y (((n + 1 : ℕ) : ℝ) / v) z) :=
    fun n _ => (integrable_hfun hbv hsupp hQ hς y (hcpos n)).const_mul _
  have hInt : Integrable (fun z => k0 ς (z - y) * rhoGen 𝔴 c Q v z) := by
    have := integrable_finsetSum (Finset.range K0) hint
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    exact hpt z
  refine ⟨hInt, ?_⟩
  have hsplit : ∀ n : ℕ, (∫ x, spokeF 𝔴 Q ς y v ((n + 1 : ℕ) : ℤ) x) +
      ∫ x, spokeF 𝔴 Q ς y v (-((n + 1 : ℕ) : ℤ)) x =
      ∫ z, hfun 𝔴 Q ς y (((n + 1 : ℕ) : ℝ) / v) z := by
    intro n
    rw [integral_spokeF_pos hv y (n + 1) (by omega),
      integral_spokeF_neg hv y (n + 1) (by omega), add_comm]
    exact intervalIntegral.integral_Iic_add_Ioi
      (integrable_hfun hbv hsupp hQ hς y (hcpos n)).integrableOn
      (integrable_hfun hbv hsupp hQ hς y (hcpos n)).integrableOn
  simp_rw [hsplit, ← integral_const_mul]
  rw [← integral_finsetSum _ hint]
  exact integral_congr_ae (Filter.Eventually.of_forall hpt)

end mainterm

end Families.Phase1.A
