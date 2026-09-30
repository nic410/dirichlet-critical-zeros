/-
The two log-wide weights of `eq:logwide` as bona fide `Weight`s (so that statements quantifying
over `W : Weight` with `W.w = wSharpFun η` / `wSmoothFun η` are not vacuous), their masses
`c_w`, the variation `V_w = 2η⁻²` of the sharp weight (`lem:A`), the bound `R_w ≤ w_max/c_w`
(`lemma-A.tex`, after `eqA:Rw`) and `m(u) = 0` for `u > 1/2` (`lem:Omega`(c), last clause).
-/
import Families.LemmaC
import Families.Schur

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius ENNReal
open ArithmeticFunction Finset MeasureTheory Set

namespace Families

/-! ### Variation helpers -/

lemma eVariationOn_neg (f : ℝ → ℝ) (s : Set ℝ) :
    eVariationOn (fun x => -f x) s = eVariationOn f s := by
  unfold eVariationOn
  simp only [edist_neg_neg]

lemma antitoneOn_eVariationOn_eq {f : ℝ → ℝ} {s : Set ℝ} (hf : AntitoneOn f s) {a b : ℝ}
    (as : a ∈ s) (bs : b ∈ s) : eVariationOn f (s ∩ Icc a b) = .ofReal (f a - f b) := by
  have hm : MonotoneOn (fun x => -f x) s := fun x hx y hy hxy => neg_le_neg (hf hx hy hxy)
  rw [← eVariationOn_neg, hm.eVariationOn_eq as bs]
  congr 1; ring

/-- A function that is constant on `(-∞, a]` and on `[b, ∞)` has the same variation on `ℝ` as on
`[a,b]`. -/
lemma eVariationOn_univ_eq_Icc (f : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (ha : ∀ x ≤ a, f x = f a) (hb : ∀ x, b ≤ x → f x = f b) :
    eVariationOn f univ = eVariationOn f (Icc a b) := by
  have h0a : eVariationOn f (Iic a) = 0 := by
    refine eVariationOn.constant_on ((Set.subsingleton_singleton (a := f a)).anti ?_)
    rintro _ ⟨x, hx, rfl⟩; exact ha x hx
  have h0b : eVariationOn f (Ici b) = 0 := by
    refine eVariationOn.constant_on ((Set.subsingleton_singleton (a := f b)).anti ?_)
    rintro _ ⟨x, hx, rfl⟩; exact hb x hx
  rw [← Set.Iic_union_Ici (a := a), eVariationOn.union f isGreatest_Iic isLeast_Ici, h0a, zero_add,
    ← Set.Icc_union_Ici_eq_Ici hab, eVariationOn.union f (isGreatest_Icc hab) isLeast_Ici, h0b,
    add_zero]

/-! ### Integral helper -/

lemma integral_indicator_Icc (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (w h : ℝ → ℝ)
    (hw : ∀ u, u * w u = Set.indicator (Icc η 1) h u) :
    ∫ u in (0 : ℝ)..1, u * w u = ∫ u in η..1, h u := by
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le hη1]
  simp_rw [hw]
  rw [integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
  have : Icc η 1 ∩ Ioc 0 1 = Icc η 1 := by
    ext u; simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ioc]; constructor
    · rintro ⟨h1, -⟩; exact h1
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2⟩, lt_of_lt_of_le hη h1, h2⟩
  rw [this, integral_Icc_eq_integral_Ioc]

/-! ### The sharp log-wide weight -/

lemma wSharpFun_nonneg (η u : ℝ) : 0 ≤ wSharpFun η u := by
  unfold wSharpFun; split_ifs <;> positivity

lemma wSharpFun_supp (η u : ℝ) (h : wSharpFun η u ≠ 0) : η ≤ u ∧ u ≤ 1 := by
  unfold wSharpFun at h; split_ifs at h with hc
  · exact hc
  · exact absurd rfl h

lemma wSharpFun_Iw (η : ℝ) (h0 : 0 < η) (h1 : η < 1 / 2) :
    ∫ u in (0 : ℝ)..1, u * wSharpFun η u = Real.log (1 / η) := by
  rw [integral_indicator_Icc η h0 (by linarith) (wSharpFun η) (fun u => u⁻¹)]
  · rw [integral_inv_of_pos h0 one_pos]
  · intro u
    unfold wSharpFun
    by_cases h : η ≤ u ∧ u ≤ 1
    · rw [if_pos h, Set.indicator_of_mem (show u ∈ Icc η 1 from h)]
      have : u ≠ 0 := (lt_of_lt_of_le h0 h.1).ne'
      field_simp
    · rw [if_neg h, Set.indicator_of_notMem (show u ∉ Icc η 1 from h), mul_zero]

lemma wSharpFun_eVariation (η : ℝ) (h0 : 0 < η) (h1 : η < 1 / 2) :
    eVariationOn (wSharpFun η) univ = ENNReal.ofReal (2 * η⁻¹ ^ 2) := by
  set f := wSharpFun η with hf
  have hη1 : η < 1 := by linarith
  have f_lt : ∀ x, x < η → f x = 0 := fun x hx => by
    simp only [hf, wSharpFun]; rw [if_neg (fun h => absurd h.1 (not_le.mpr hx))]
  have f_gt : ∀ x, 1 < x → f x = 0 := fun x hx => by
    simp only [hf, wSharpFun]; rw [if_neg (fun h => absurd h.2 (not_le.mpr hx))]
  have f_in : ∀ x, η ≤ x → x ≤ 1 → f x = x⁻¹ ^ 2 := fun x hx1 hx2 => by
    simp only [hf, wSharpFun]; rw [if_pos ⟨hx1, hx2⟩]
  rw [eVariationOn_univ_eq_Icc f (show (0 : ℝ) ≤ 2 by norm_num)
    (fun x hx => by rw [f_lt x (by linarith), f_lt 0 h0])
    (fun x hx => by rw [f_gt x (by linarith), f_gt 2 (by norm_num)])]
  have e1 : eVariationOn f (univ ∩ Icc 0 η) + eVariationOn f (univ ∩ Icc η 1) =
      eVariationOn f (univ ∩ Icc 0 1) := eVariationOn.Icc_add_Icc f h0.le hη1.le (mem_univ _)
  have e2 : eVariationOn f (univ ∩ Icc 0 1) + eVariationOn f (univ ∩ Icc 1 2) =
      eVariationOn f (univ ∩ Icc 0 2) :=
    eVariationOn.Icc_add_Icc f zero_le_one (by norm_num) (mem_univ _)
  simp only [univ_inter] at e1 e2
  -- piece 1: monotone on [0, η]
  have p1 : eVariationOn f (Icc 0 η) = ENNReal.ofReal (η⁻¹ ^ 2) := by
    have hm : MonotoneOn f (Icc 0 η) := by
      intro x hx y hy hxy
      rcases eq_or_lt_of_le hy.2 with rfl | hy'
      · rcases eq_or_lt_of_le hx.2 with rfl | hx'
        · exact le_rfl
        · rw [f_lt x hx', f_in _ le_rfl hη1.le]; positivity
      · rw [f_lt x (lt_of_le_of_lt hxy hy'), f_lt y hy']
    have := hm.eVariationOn_eq (Set.left_mem_Icc.mpr h0.le) (Set.right_mem_Icc.mpr h0.le)
    rw [Set.inter_self, f_in _ le_rfl hη1.le, f_lt 0 h0, sub_zero] at this
    exact this
  -- piece 2: antitone on [η, 1]
  have p2 : eVariationOn f (Icc η 1) = ENNReal.ofReal (η⁻¹ ^ 2 - 1) := by
    have ha : AntitoneOn f (Icc η 1) := by
      intro x hx y hy hxy
      rw [f_in x hx.1 hx.2, f_in y hy.1 hy.2]
      have hx0 : 0 < x := lt_of_lt_of_le h0 hx.1
      have : y⁻¹ ≤ x⁻¹ := inv_anti₀ hx0 hxy
      have : 0 ≤ y⁻¹ := inv_nonneg.mpr (hx0.le.trans hxy)
      nlinarith
    have := antitoneOn_eVariationOn_eq ha (Set.left_mem_Icc.mpr hη1.le) (Set.right_mem_Icc.mpr hη1.le)
    rw [Set.inter_self, f_in _ le_rfl hη1.le, f_in 1 hη1.le le_rfl] at this
    simpa using this
  -- piece 3: antitone on [1, 2]
  have p3 : eVariationOn f (Icc 1 2) = ENNReal.ofReal 1 := by
    have ha : AntitoneOn f (Icc 1 2) := by
      intro x hx y hy hxy
      rcases eq_or_lt_of_le hx.1 with rfl | hx'
      · rcases eq_or_lt_of_le hy.1 with rfl | hy'
        · exact le_rfl
        · rw [f_gt y hy', f_in 1 hη1.le le_rfl]; norm_num
      · rw [f_gt x hx', f_gt y (lt_of_lt_of_le hx' hxy)]
    have := antitoneOn_eVariationOn_eq ha (Set.left_mem_Icc.mpr (by norm_num : (1 : ℝ) ≤ 2))
      (Set.right_mem_Icc.mpr (by norm_num : (1 : ℝ) ≤ 2))
    rw [Set.inter_self, f_in 1 hη1.le le_rfl, f_gt 2 (by norm_num)] at this
    simpa using this
  have hge : 1 ≤ η⁻¹ ^ 2 := by
    have : 1 ≤ η⁻¹ := (one_le_inv₀ h0).mpr hη1.le
    nlinarith
  rw [← e2, ← e1, p1, p2, p3, ← ENNReal.ofReal_add (by positivity) (by linarith),
    ← ENNReal.ofReal_add (by linarith) zero_le_one]
  congr 1; ring

/-- The sharp log-wide weight `w_η = u^{-2} 1_{[η,1]}` as an admissible `Weight`. -/
def wSharpWeight (η : ℝ) (h0 : 0 < η) (h1 : η < 1 / 2) : Weight where
  w := wSharpFun η
  η := η
  η_pos := h0
  η_lt_half := h1
  nonneg := wSharpFun_nonneg η
  supp := wSharpFun_supp η
  bv := by
    unfold BoundedVariationOn
    rw [wSharpFun_eVariation η h0 h1]; exact ENNReal.ofReal_ne_top
  Iw_pos := by
    rw [wSharpFun_Iw η h0 h1]
    apply Real.log_pos
    rw [one_div]; exact (one_lt_inv₀ h0).mpr (by linarith)

@[simp] lemma wSharpWeight_w (η : ℝ) (h0 : 0 < η) (h1 : η < 1 / 2) :
    (wSharpWeight η h0 h1).w = wSharpFun η := rfl
@[simp] lemma wSharpWeight_η (η : ℝ) (h0 : 0 < η) (h1 : η < 1 / 2) :
    (wSharpWeight η h0 h1).η = η := rfl

/-- `lem:A` (sharp weight): `V_w = 2η⁻²` and `c_w = (6/π²) log(1/η)`, for *any* `Weight` whose
function is `wSharpFun η` (same statement as `Families.wSharp_Vw_cw` in `LemmaA.lean`). -/
theorem wSharp_Vw_cw_proof (W : Weight) (η : ℝ) (hη : 0 < η ∧ η < 1 / 2)
    (hW : W.w = wSharpFun η) :
    W.Vw = 2 * η⁻¹ ^ 2 ∧ W.cw = 6 / Real.pi ^ 2 * Real.log (1 / η) := by
  refine ⟨?_, ?_⟩
  · unfold Weight.Vw
    rw [hW, wSharpFun_eVariation η hη.1 hη.2, ENNReal.toReal_ofReal (by positivity)]
  · unfold Weight.cw Weight.Iw
    rw [hW, wSharpFun_Iw η hη.1 hη.2]

theorem wSharp_cw (η : ℝ) (h0 : 0 < η) (h1 : η < 1 / 2) :
    (wSharpWeight η h0 h1).cw = 6 / Real.pi ^ 2 * Real.log (1 / η) :=
  (wSharp_Vw_cw_proof _ η ⟨h0, h1⟩ rfl).2

theorem wSharp_Vw (η : ℝ) (h0 : 0 < η) (h1 : η < 1 / 2) :
    (wSharpWeight η h0 h1).Vw = 2 * η⁻¹ ^ 2 :=
  (wSharp_Vw_cw_proof _ η ⟨h0, h1⟩ rfl).1

/-! ### The log-smooth weight -/

/-- The smooth profile `h(u) = u^{-2} sin²(π log u / log η)` (valid formula on `(0,∞)`). -/
def smoothProfile (η u : ℝ) : ℝ := u⁻¹ ^ 2 * Real.sin (Real.pi * Real.log u / Real.log η) ^ 2

lemma wSmoothFun_nonneg (η u : ℝ) : 0 ≤ wSmoothFun η u := by
  unfold wSmoothFun; split_ifs <;> positivity

lemma wSmoothFun_supp (η u : ℝ) (h : wSmoothFun η u ≠ 0) : η ≤ u ∧ u ≤ 1 := by
  unfold wSmoothFun at h; split_ifs at h with hc
  · exact hc
  · exact absurd rfl h

lemma smoothProfile_contDiffOn (η : ℝ) (h0 : 0 < η) :
    ContDiffOn ℝ 1 (smoothProfile η) (Icc η 1) := by
  intro x hx
  have hx0 : x ≠ 0 := (lt_of_lt_of_le h0 hx.1).ne'
  apply ContDiffAt.contDiffWithinAt
  unfold smoothProfile
  fun_prop (disch := exact hx0)

lemma smoothProfile_pos (η : ℝ) (h0 : 0 < η) (h1 : η < 1 / 2) (x : ℝ) (hx : x ∈ Ioo η 1) :
    0 < smoothProfile η x := by
  have hx0 : 0 < x := lt_trans h0 hx.1
  have hlη : Real.log η < 0 := Real.log_neg h0 (by linarith)
  have hlx : Real.log x < 0 := Real.log_neg hx0 hx.2
  have hlηx : Real.log η < Real.log x := Real.log_lt_log h0 hx.1
  have hs0 : 0 < Real.log x / Real.log η := div_pos_of_neg_of_neg hlx hlη
  have hs1 : Real.log x / Real.log η < 1 := by
    rw [div_lt_one_of_neg hlη]; exact hlηx
  have hsin : 0 < Real.sin (Real.pi * Real.log x / Real.log η) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · rw [mul_div_assoc]; exact mul_pos Real.pi_pos hs0
    · rw [mul_div_assoc]; nlinarith [Real.pi_pos]
  unfold smoothProfile
  have : 0 < x⁻¹ ^ 2 := by positivity
  positivity

lemma wSmoothFun_eq_indicator (η : ℝ) (u : ℝ) :
    wSmoothFun η u = Set.indicator (Icc η 1) (smoothProfile η) u := by
  unfold wSmoothFun smoothProfile
  by_cases h : η ≤ u ∧ u ≤ 1
  · rw [if_pos h, Set.indicator_of_mem (show u ∈ Icc η 1 from h)]
  · rw [if_neg h, Set.indicator_of_notMem (show u ∉ Icc η 1 from h)]

lemma wSmoothFun_Iw_pos (η : ℝ) (h0 : 0 < η) (h1 : η < 1 / 2) :
    0 < ∫ u in (0 : ℝ)..1, u * wSmoothFun η u := by
  rw [integral_indicator_Icc η h0 (by linarith) (wSmoothFun η) (fun u => u * smoothProfile η u)]
  · refine intervalIntegral.intervalIntegral_pos_of_pos_on ?_ ?_ (by linarith)
    · apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le (by linarith)]
      exact continuousOn_id.mul (smoothProfile_contDiffOn η h0).continuousOn
    · intro x hx
      exact mul_pos (lt_trans h0 hx.1) (smoothProfile_pos η h0 h1 x hx)
  · intro u
    rw [wSmoothFun_eq_indicator η]
    by_cases h : u ∈ Icc η 1
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]

lemma wSmoothFun_bv (η : ℝ) (h0 : 0 < η) (h1 : η < 1 / 2) :
    BoundedVariationOn (wSmoothFun η) univ := by
  have hlη : Real.log η ≠ 0 := (Real.log_neg h0 (by linarith)).ne
  have fη : wSmoothFun η η = 0 := by
    rw [wSmoothFun_eq_indicator η, Set.indicator_of_mem (Set.left_mem_Icc.mpr (by linarith))]
    unfold smoothProfile
    rw [mul_div_assoc, div_self hlη, mul_one, Real.sin_pi]; ring
  have f1 : wSmoothFun η 1 = 0 := by
    rw [wSmoothFun_eq_indicator η, Set.indicator_of_mem (Set.right_mem_Icc.mpr (by linarith))]
    unfold smoothProfile
    simp
  have hlt : ∀ x, x < η → wSmoothFun η x = 0 := fun x hx => by
    rw [wSmoothFun_eq_indicator η, Set.indicator_of_notMem (fun h => absurd h.1 (not_le.mpr hx))]
  have hgt : ∀ x, 1 < x → wSmoothFun η x = 0 := fun x hx => by
    rw [wSmoothFun_eq_indicator η, Set.indicator_of_notMem (fun h => absurd h.2 (not_le.mpr hx))]
  unfold BoundedVariationOn
  rw [eVariationOn_univ_eq_Icc (wSmoothFun η) (a := η) (b := 1) (by linarith)
    (fun x hx => by
      rcases eq_or_lt_of_le hx with rfl | hx'
      · rfl
      · rw [hlt x hx', fη])
    (fun x hx => by
      rcases eq_or_lt_of_le hx with rfl | hx'
      · rfl
      · rw [hgt x hx', f1])]
  have heq : EqOn (wSmoothFun η) (smoothProfile η) (Icc η 1) := fun x hx => by
    rw [wSmoothFun_eq_indicator η, Set.indicator_of_mem hx]
  rw [eVariationOn.eq_of_eqOn heq]
  obtain ⟨K, hK⟩ := (smoothProfile_contDiffOn η h0).exists_lipschitzOnWith one_ne_zero
    (convex_Icc η 1) isCompact_Icc
  have := hK.locallyBoundedVariationOn η 1 (Set.left_mem_Icc.mpr (by linarith))
    (Set.right_mem_Icc.mpr (by linarith))
  rw [Set.inter_self] at this
  exact this

/-- The log-smooth weight `w^sm_η = u^{-2} sin²(π log u / log η) 1_{[η,1]}` as an admissible
`Weight`. -/
def wSmoothWeight (η : ℝ) (h0 : 0 < η) (h1 : η < 1 / 2) : Weight where
  w := wSmoothFun η
  η := η
  η_pos := h0
  η_lt_half := h1
  nonneg := wSmoothFun_nonneg η
  supp := wSmoothFun_supp η
  bv := wSmoothFun_bv η h0 h1
  Iw_pos := wSmoothFun_Iw_pos η h0 h1

@[simp] lemma wSmoothWeight_w (η : ℝ) (h0 : 0 < η) (h1 : η < 1 / 2) :
    (wSmoothWeight η h0 h1).w = wSmoothFun η := rfl
@[simp] lemma wSmoothWeight_η (η : ℝ) (h0 : 0 < η) (h1 : η < 1 / 2) :
    (wSmoothWeight η h0 h1).η = η := rfl

/-! ### `R_w ≤ w_max / c_w` -/

lemma Weight.cw_pos (W : Weight) : 0 < W.cw := by
  unfold Weight.cw Weight.Iw
  exact mul_pos (div_pos (by norm_num) (by positivity)) W.Iw_pos

lemma Weight.wmax_nonneg (W : Weight) : 0 ≤ W.wmax := (W.nonneg 0).trans (W.le_wmax 0)

lemma Pw_le (W : Weight) (t : ℝ) (ht : 0 < t) : Pw W t ≤ W.wmax / W.cw := by
  unfold Pw
  set N := ⌊1 / t⌋₊
  have hNt : (N : ℝ) * t ≤ 1 := by
    have := Nat.floor_le (show (0 : ℝ) ≤ 1 / t by positivity)
    rw [le_div_iff₀ ht] at this; exact this
  have hterm : ∀ k ∈ Finset.Icc 1 N,
      (Nat.totient k : ℝ) / (k : ℝ) ^ 2 * W.wt (k * t) ≤ (N : ℝ) * t ^ 2 * W.wmax := by
    intro k hk
    have hk' := Finset.mem_Icc.mp hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk'.1
    unfold Weight.wt
    have e : (Nat.totient k : ℝ) / (k : ℝ) ^ 2 * (((k : ℝ) * t) ^ 2 * W.w (k * t)) =
        (Nat.totient k : ℝ) * t ^ 2 * W.w (k * t) := by
      field_simp
    rw [e]
    have hφ : (Nat.totient k : ℝ) ≤ N := by
      exact_mod_cast (Nat.totient_le k).trans hk'.2
    have hw := W.le_wmax ((k : ℝ) * t)
    have hw0 := W.nonneg ((k : ℝ) * t)
    have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
    have hφ0 : (0 : ℝ) ≤ Nat.totient k := Nat.cast_nonneg _
    calc (Nat.totient k : ℝ) * t ^ 2 * W.w (k * t)
        ≤ (Nat.totient k : ℝ) * t ^ 2 * W.wmax :=
          mul_le_mul_of_nonneg_left hw (mul_nonneg hφ0 ht2)
      _ ≤ (N : ℝ) * t ^ 2 * W.wmax :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hφ ht2) W.wmax_nonneg
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul] at hsum
  have hb : (N : ℝ) * ((N : ℝ) * t ^ 2 * W.wmax) ≤ W.wmax := by
    have : (N : ℝ) * ((N : ℝ) * t ^ 2 * W.wmax) = ((N : ℝ) * t) ^ 2 * W.wmax := by ring
    rw [this]
    have h0 : 0 ≤ (N : ℝ) * t := by positivity
    have : ((N : ℝ) * t) ^ 2 ≤ 1 := by nlinarith
    nlinarith [W.wmax_nonneg]
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (hsum.trans hb) (inv_nonneg.mpr W.cw_pos.le)

/-- `R_w ≤ w_max / c_w` (same statement as `Families.Rw_le` in `LemmaA.lean`). -/
theorem Rw_le' (W : Weight) : Rw W ≤ ENNReal.ofReal (W.wmax / W.cw) := by
  unfold Rw
  refine essSup_le_of_ae_le _ ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
  exact ENNReal.ofReal_le_ofReal (Pw_le W t ht)

/-! ### `m(u) = 0` for `u > 1/2` -/

theorem mfun_eq_zero_of_gt_half (W : Weight) (u : ℝ) (hu : 1 / 2 < u) : mfun W u = 0 := by
  unfold mfun
  have hu0 : 0 < u := by linarith
  have hN : ⌊1 / u⌋₊ < 2 := by
    rw [Nat.floor_lt (by positivity)]
    rw [div_lt_iff₀ hu0]; push_cast; linarith
  have hsum : ∑ r ∈ (Finset.Icc 1 ⌊1 / u⌋₊).filter (fun r : ℕ => μ r = -1),
      W.w (u * r) / Nat.totient r = 0 := by
    refine Finset.sum_eq_zero fun r hr => ?_
    obtain ⟨hr1, hr2⟩ := Finset.mem_filter.mp hr
    have : r = 1 := by have := Finset.mem_Icc.mp hr1; omega
    subst this
    simp at hr2
  rw [hsum, zero_sub]
  exact max_eq_right (neg_nonpos.mpr (W.nonneg u))

/-- `lem:A` (sharp weight): `V_w = 2η⁻²`, `c_w = (6/π²) log(1/η)` (name used in STATEMENTS.md). -/
theorem wSharp_Vw_cw (W : Weight) (η : ℝ) (hη : 0 < η ∧ η < 1 / 2) (hW : W.w = wSharpFun η) :
    W.Vw = 2 * η⁻¹ ^ 2 ∧ W.cw = 6 / Real.pi ^ 2 * Real.log (1 / η) :=
  wSharp_Vw_cw_proof W η hη hW

/-- `R_w ≤ w_max/c_w < ∞` (`lemma-A.tex`, after `eqA:Rw`). -/
theorem Rw_le (W : Weight) : Rw W ≤ ENNReal.ofReal (W.wmax / W.cw) := Rw_le' W

end Families
