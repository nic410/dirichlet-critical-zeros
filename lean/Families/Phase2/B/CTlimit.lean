/-
# **`lem:CTlimit`** (Lemma 6.22)

`Families.Phase2.B.lemCTlimit_proof : lemCTlimit_Statement`.

* (1) `lemCTlimit_one` (`RSBound.lean`).
* (2), (3): the statement quantifies over `W` with `W.w = wSharpFun η` (resp. `wSmoothFun η`), but `W.η`
  may be smaller than `η`. Since `R_S`, `R^m`, `C_T^+` depend on `W` only through `W.w`
  (`CTp_congr`), we pass to `W' = wSharpWeight η` (resp. `wSmoothWeight η`), which has `W'.η = η`; the
  existence of `W` forces `η > 0` (`eta_pos_of_sharp`, `eta_pos_of_smooth`), and `L_η ≥ 3` gives
  `η < 1/2`.
  - sharp: `h = 1_{[0,L]}`, `I_w = L`, `m̃ = 0` on `[η,∞)` (`lem:Omega`(d)); so
    `C_T^+ ≤ 1 + (c_∅ + (4B + 3)/ℰ)/L ≤ 1 + 38.9/L`;
  - log-smooth: `h(y) = sin²(πy/L) 1_{[0,L]}(y)`, quasi-concave (`sin` concave on `[0,π]`),
    `(π/L)`-Lipschitz, `I_w = L/2` (from `∫ h = I_w` and `∫₀^π sin² = π/2`), and
    `m̃ ≤ (π/L)σ₁⁻` on `[η,∞)` (`lem:Omega`(e)); so
    `C_T^+ ≤ 1 + 2(c_∅ + (4B + 3 + (4/3)πσ₁⁻)/ℰ)/L ≤ 1 + 82.7/L`.
-/
import Families.Phase2.B.RmBound

noncomputable section

open scoped BigOperators ENNReal
open Finset MeasureTheory Filter

namespace Families.Phase2.B

open Families Families.Phase1.B

/-! ### `R_S`, `R^m`, `C_T^+` depend only on `W.w` -/

lemma RS_congr {W W' : Weight} (h : W.w = W'.w) (S : Finset ℕ) (t : ℝ) :
    RS W S t = RS W' S t := by
  unfold RS Weight.Iw Weight.wt; rw [h]

lemma Rm_congr {W W' : Weight} (h : W.w = W'.w) (t : ℝ) : Rm W t = Rm W' t := by
  unfold Rm mt mfun Weight.Iw; rw [h]

lemma CTp_congr {W W' : Weight} (h : W.w = W'.w) : CTp W = CTp W' := by
  unfold CTp; simp_rw [RS_congr h, Rm_congr h]

/-- `C_T^+ ≤ A + B` from pointwise bounds. -/
lemma CTp_le_of (W : Weight) (A B : ℝ) (hRS : ∀ S t, 0 < t → RS W S t ≤ A)
    (hRm : ∀ t, 0 < t → Rm W t ≤ B) : CTp W ≤ ENNReal.ofReal (A + B) := by
  refine iSup_le fun S => essSup_le_of_ae_le _ ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
  exact ENNReal.ofReal_le_ofReal (add_le_add (hRS S t ht) (hRm t ht))

/-- `‖w̃‖_∞ ≤ 1` when `w̃(u) = h(log(1/u))` with `h ≤ 1`. -/
lemma wtmax_le_one (W : Weight) (h : ℝ → ℝ) (h1 : ∀ y, h y ≤ 1)
    (hwt : ∀ u, 0 < u → W.wt u = h (Real.log (1 / u))) : W.wtmax ≤ 1 := by
  unfold Weight.wtmax
  refine csSup_le (Set.range_nonempty _) ?_
  rintro _ ⟨u, rfl⟩
  rcases le_or_gt u 0 with hu | hu
  · have : W.w u = 0 := by
      by_contra hne
      have := (W.supp u hne).1
      linarith [W.η_pos]
    unfold Weight.wt; rw [this, mul_zero]; norm_num
  · rw [hwt u hu]; exact h1 _

/-- `L_η ≥ 3` and `η > 0` give `η < 1/2`. -/
lemma eta_lt_half_of_Leta {η : ℝ} (h0 : 0 < η) (hL : 3 ≤ Leta η) : η < 1 / 2 := by
  unfold Leta at hL
  have h1 : Real.exp 3 ≤ 1 / η := by
    rw [← Real.exp_log (show 0 < 1 / η by positivity)]; exact Real.exp_le_exp.mpr hL
  have h2 : (2 : ℝ) < Real.exp 3 := by
    have := Real.add_one_le_exp 3; linarith
  rw [le_div_iff₀ h0] at h1
  nlinarith

/-! ### The sharp weight -/

lemma eta_pos_of_sharp (W : Weight) (η : ℝ) (hW : W.w = wSharpFun η) : 0 < η := by
  by_contra hη
  push Not at hη
  have hW0 := W.η_pos
  have hW1 := W.η_lt_half
  set u := W.η / 2
  have hne : W.w u ≠ 0 := by
    rw [hW]; unfold wSharpFun
    rw [if_pos ⟨by simp only [u]; linarith, by simp only [u]; linarith⟩]
    positivity
  have := (W.supp u hne).1
  simp only [u] at this
  linarith

/-- The profile of the sharp weight: `h = 1_{[0,L]}`. -/
def hSharp (L : ℝ) (y : ℝ) : ℝ := if 0 ≤ y ∧ y ≤ L then 1 else 0

lemma hSharp_mem (L y : ℝ) : 0 ≤ hSharp L y ∧ hSharp L y ≤ 1 := by
  unfold hSharp; split_ifs <;> norm_num

lemma hSharp_qc (L : ℝ) (lam : ℝ) : Set.OrdConnected {y | lam < hSharp L y} := by
  rcases lt_or_ge lam 0 with h | h
  · have : {y | lam < hSharp L y} = Set.univ := by
      ext y; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact lt_of_lt_of_le h (hSharp_mem L y).1
    rw [this]; exact Set.ordConnected_univ
  rcases lt_or_ge lam 1 with h1 | h1
  · have : {y | lam < hSharp L y} = Set.Icc 0 L := by
      ext y; simp only [Set.mem_ofPred_eq, Set.mem_Icc, hSharp]
      split_ifs with hy
      · simp [hy, h1]
      · simp only [hy, iff_false]; linarith
    rw [this]; exact Set.ordConnected_Icc
  · have : {y | lam < hSharp L y} = ∅ := by
      ext y; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact le_trans (hSharp_mem L y).2 h1
    rw [this]; exact Set.ordConnected_empty

/-- For `u > 0`: `u ∈ [η,1] ⟺ log(1/u) ∈ [0, L_η]`. -/
lemma mem_Icc_iff_log {η u : ℝ} (h0 : 0 < η) (hu : 0 < u) :
    (η ≤ u ∧ u ≤ 1) ↔ (0 ≤ Real.log (1 / u) ∧ Real.log (1 / u) ≤ Leta η) := by
  unfold Leta
  rw [one_div, one_div, Real.log_inv, Real.log_inv, neg_nonneg, neg_le_neg_iff,
    Real.log_nonpos_iff hu.le, Real.log_le_log_iff h0 hu]
  exact And.comm

lemma sharp_wt (η : ℝ) (h0 : 0 < η) (h1 : η < 1 / 2) (u : ℝ) (hu : 0 < u) :
    (wSharpWeight η h0 h1).wt u = hSharp (Leta η) (Real.log (1 / u)) := by
  unfold Weight.wt hSharp
  simp only [wSharpWeight_w, wSharpFun]
  by_cases h : η ≤ u ∧ u ≤ 1
  · rw [if_pos h, if_pos ((mem_Icc_iff_log h0 hu).mp h)]; field_simp
  · rw [if_neg h, if_neg (fun h' => h ((mem_Icc_iff_log h0 hu).mpr h')), mul_zero]

/-- **`lem:CTlimit` (2): `C_T^+(w_η) ≤ 1 + 42/L_η`.** -/
theorem lemCTlimit_sharp (W : Weight) (η : ℝ) (hW : W.w = wSharpFun η) (hL : 3 ≤ Leta η) :
    CTp W ≤ ENNReal.ofReal (1 + 42 / Leta η) := by
  have h0 := eta_pos_of_sharp W η hW
  have h1 := eta_lt_half_of_Leta h0 hL
  set W' := wSharpWeight η h0 h1 with hW'
  rw [CTp_congr (W' := W') (by rw [hW]; rfl)]
  set L := Leta η with hLdef
  have hLpos : 0 < L := by linarith
  have hwt := sharp_wt η h0 h1
  have hI : W'.Iw = L := wSharpFun_Iw η h0 h1
  have hw1 : W'.wtmax ≤ 1 := wtmax_le_one W' (hSharp L) (fun y => (hSharp_mem L y).2) hwt
  have hRS : ∀ S t, 0 < t → RS W' S t ≤ 1 + (cEmpty + 4 * Bconst / Ecal) / L := by
    intro S t ht
    rw [← hI]
    exact RS_le_of_quasiconcave W' (hSharp L) (hSharp_mem L)
      (fun y hy => by unfold hSharp; rw [if_neg (fun h => absurd h.1 (not_le.mpr hy))])
      (hSharp_qc L) hwt S t ht
  -- `m̃ = 0` on `[η, ∞)` (`lem:Omega`(d), `w̃ = 1` on `[η,1]`)
  have hd := (lemOmega_d_proof W' ⟨1, fun u hu1 hu2 => by
    rw [hwt u (lt_of_lt_of_le h0 hu1)]; unfold hSharp
    rw [if_pos ((mem_Icc_iff_log h0 (lt_of_lt_of_le h0 hu1)).mp ⟨hu1, hu2⟩)]⟩).1
  have hhigh : ∀ u, W'.η ≤ u → mt W' u ≤ 0 := fun u hu => by
    unfold mt; rw [hd u hu, mul_zero]
  have hRm : ∀ t, 0 < t → Rm W' t ≤ 3 / (Ecal * L) := by
    intro t ht
    have := Rm_le W' hw1 0 le_rfl hhigh t ht
    rw [hI, zero_mul, add_zero] at this
    exact this
  refine (CTp_le_of W' _ _ hRS hRm).trans (ENNReal.ofReal_le_ofReal ?_)
  -- numerics: `c_∅ + (4B + 3)/ℰ ≤ 42`
  have hc := cEmpty_le
  have hB := Bconst_lt
  have hE := Ecal_ge_047914
  have hE0 := Ecal_pos
  have key : cEmpty + 4 * Bconst / Ecal + 3 / Ecal ≤ 42 := by
    have : (4 * Bconst + 3) / Ecal ≤ 37.41 := by rw [div_le_iff₀ hE0]; nlinarith
    have e : 4 * Bconst / Ecal + 3 / Ecal = (4 * Bconst + 3) / Ecal := by ring
    linarith
  have e : 1 + (cEmpty + 4 * Bconst / Ecal) / L + 3 / (Ecal * L) =
      1 + (cEmpty + 4 * Bconst / Ecal + 3 / Ecal) / L := by
    field_simp
    ring
  rw [e]
  gcongr

/-! ### The log-smooth weight -/

lemma eta_pos_of_smooth (W : Weight) (η : ℝ) (hW : W.w = wSmoothFun η) (hL : 3 ≤ Leta η) :
    0 < η := by
  by_contra hη
  push Not at hη
  rcases eq_or_lt_of_le hη with h | h
  · subst h; unfold Leta at hL; simp at hL; linarith
  -- `η < 0`: find `u ∈ (0, W.η)` with `w(u) ≠ 0`
  set L := Leta η with hLdef
  have hLpos : 0 < L := by linarith
  have hlogη : Real.log η = -L := by rw [hLdef]; unfold Leta; rw [one_div, Real.log_inv, neg_neg]
  have hW0 := W.η_pos
  set k : ℕ := ⌈-Real.log W.η / L⌉₊ with hk
  set u := Real.exp (-(L * (k + 1 / 2))) with hu
  have hu0 : 0 < u := Real.exp_pos _
  have hkL : -Real.log W.η / L ≤ k := Nat.le_ceil _
  have hk' : -Real.log W.η < L * (k + 1 / 2) := by
    rw [div_le_iff₀ hLpos] at hkL; nlinarith
  have huW : u < W.η := by
    rw [hu, ← Real.exp_log hW0]; exact Real.exp_lt_exp.mpr (by linarith)
  have hu1 : u ≤ 1 := by
    rw [hu, Real.exp_le_one_iff]; have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; nlinarith
  have hne : W.w u ≠ 0 := by
    rw [hW]; unfold wSmoothFun
    rw [if_pos ⟨by linarith, hu1⟩, hu, Real.log_exp, hlogη]
    have e : Real.pi * -(L * (k + 1 / 2)) / -L = (k : ℝ) * Real.pi + Real.pi / 2 := by
      field_simp
    rw [e, Real.sin_add_pi_div_two, Real.cos_nat_mul_pi]
    have : ((-1 : ℝ) ^ k) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [this, mul_one]
    positivity
  have := (W.supp u hne).1
  linarith

/-- The profile of the log-smooth weight: `h(y) = sin²(πy/L) 1_{[0,L]}(y)`. -/
def hSmooth (L : ℝ) (y : ℝ) : ℝ := if 0 ≤ y ∧ y ≤ L then Real.sin (Real.pi * y / L) ^ 2 else 0

lemma hSmooth_mem (L y : ℝ) : 0 ≤ hSmooth L y ∧ hSmooth L y ≤ 1 := by
  unfold hSmooth; split_ifs
  · exact ⟨sq_nonneg _, by rw [sq_le_one_iff_abs_le_one]; exact Real.abs_sin_le_one _⟩
  · norm_num

/-- `h = g ∘ clamp` with `g(x) = sin²(πx/L)`, `clamp(y) = max(min(y, L), 0)`. -/
lemma hSmooth_eq_clamp {L : ℝ} (hL : 0 < L) (y : ℝ) :
    hSmooth L y = Real.sin (Real.pi * max (min y L) 0 / L) ^ 2 := by
  unfold hSmooth
  split_ifs with h
  · rw [min_eq_left h.2, max_eq_left h.1]
  · rcases not_and_or.mp h with h' | h'
    · push Not at h'
      rw [max_eq_right (le_trans (min_le_left _ _) h'.le)]; simp
    · push Not at h'
      rw [min_eq_right h'.le, max_eq_left hL.le, mul_div_assoc, div_self hL.ne', mul_one,
        Real.sin_pi]; norm_num

/-- `h` is `(π/L)`-Lipschitz. -/
lemma hSmooth_lipschitz {L : ℝ} (hL : 0 < L) :
    LipschitzWith (Real.toNNReal (Real.pi / L)) (hSmooth L) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq, Real.dist_eq, hSmooth_eq_clamp hL,
    hSmooth_eq_clamp hL]
  set a := Real.pi * max (min x L) 0 / L
  set b := Real.pi * max (min y L) 0 / L
  have hsq : ∀ z : ℝ, Real.sin z ^ 2 = 1 / 2 - Real.cos (2 * z) / 2 := fun z => by
    rw [Real.sin_sq, Real.cos_sq]; ring
  rw [hsq, hsq]
  have hcos := Real.abs_cos_sub_cos_le (2 * b) (2 * a)
  have hclamp : |max (min x L) 0 - max (min y L) 0| ≤ |x - y| := by
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
    simp
  have hab : a - b = Real.pi / L * (max (min x L) 0 - max (min y L) 0) := by
    simp only [a, b]; ring
  calc |1 / 2 - Real.cos (2 * a) / 2 - (1 / 2 - Real.cos (2 * b) / 2)|
      = |Real.cos (2 * b) - Real.cos (2 * a)| / 2 := by
        rw [show 1 / 2 - Real.cos (2 * a) / 2 - (1 / 2 - Real.cos (2 * b) / 2) =
          (Real.cos (2 * b) - Real.cos (2 * a)) / 2 by ring, abs_div, abs_two]
    _ ≤ |2 * b - 2 * a| / 2 := by gcongr
    _ = |a - b| := by
        rw [show 2 * b - 2 * a = -(2 * (a - b)) by ring, abs_neg, abs_mul, abs_two]; ring
    _ = Real.pi / L * |max (min x L) 0 - max (min y L) 0| := by
        rw [hab, abs_mul, abs_of_pos (by positivity)]
    _ ≤ Real.pi / L * |x - y| := by gcongr

/-- `h` is quasi-concave: `sin` is concave on `[0, π]`. -/
lemma hSmooth_qc {L : ℝ} (hL : 0 < L) (lam : ℝ) : Set.OrdConnected {y | lam < hSmooth L y} := by
  rcases lt_or_ge lam 0 with h | h
  · have : {y | lam < hSmooth L y} = Set.univ := by
      ext y; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact lt_of_lt_of_le h (hSmooth_mem L y).1
    rw [this]; exact Set.ordConnected_univ
  refine ⟨fun x hx y hy z hz => ?_⟩
  simp only [Set.mem_ofPred_eq] at hx hy ⊢
  have hin : ∀ v, lam < hSmooth L v → 0 ≤ v ∧ v ≤ L := fun v hv => by
    by_contra hc
    unfold hSmooth at hv; rw [if_neg hc] at hv; linarith
  obtain ⟨hx0, hxL⟩ := hin x hx
  obtain ⟨hy0, hyL⟩ := hin y hy
  have hz0 : 0 ≤ z := le_trans hx0 hz.1
  have hzL : z ≤ L := le_trans hz.2 hyL
  have hmemπ : ∀ v, 0 ≤ v → v ≤ L → Real.pi * v / L ∈ Set.Icc 0 Real.pi := fun v h0 h1 =>
    ⟨by positivity, by rw [div_le_iff₀ hL]; nlinarith [Real.pi_pos]⟩
  have hsin := strictConcaveOn_sin_Icc.concaveOn.min_le_of_mem_Icc (hmemπ x hx0 hxL)
    (hmemπ y hy0 hyL) (z := Real.pi * z / L)
    ⟨by gcongr; exact hz.1, by gcongr; exact hz.2⟩
  have hs0 : ∀ v, 0 ≤ v → v ≤ L → 0 ≤ Real.sin (Real.pi * v / L) := fun v h0 h1 =>
    Real.sin_nonneg_of_nonneg_of_le_pi (hmemπ v h0 h1).1 (hmemπ v h0 h1).2
  unfold hSmooth at hx hy ⊢
  rw [if_pos ⟨hx0, hxL⟩] at hx
  rw [if_pos ⟨hy0, hyL⟩] at hy
  rw [if_pos ⟨hz0, hzL⟩]
  rcases min_choice (Real.sin (Real.pi * x / L)) (Real.sin (Real.pi * y / L)) with hm | hm
  · rw [hm] at hsin
    exact lt_of_lt_of_le hx (pow_le_pow_left₀ (hs0 x hx0 hxL) hsin 2)
  · rw [hm] at hsin
    exact lt_of_lt_of_le hy (pow_le_pow_left₀ (hs0 y hy0 hyL) hsin 2)

lemma smooth_wt (η : ℝ) (h0 : 0 < η) (h1 : η < 1 / 2) (u : ℝ) (hu : 0 < u) :
    (wSmoothWeight η h0 h1).wt u = hSmooth (Leta η) (Real.log (1 / u)) := by
  unfold Weight.wt hSmooth
  simp only [wSmoothWeight_w, wSmoothFun]
  by_cases h : η ≤ u ∧ u ≤ 1
  · rw [if_pos h, if_pos ((mem_Icc_iff_log h0 hu).mp h)]
    have hlη : Real.log η ≠ 0 := (Real.log_neg h0 (by linarith)).ne
    have e : Real.pi * Real.log (1 / u) / Leta η = Real.pi * Real.log u / Real.log η := by
      unfold Leta
      rw [one_div, one_div, Real.log_inv, Real.log_inv, mul_neg, neg_div_neg_eq]
    rw [e]
    field_simp
  · rw [if_neg h, if_neg (fun h' => h ((mem_Icc_iff_log h0 hu).mpr h')), mul_zero]

/-- `∫₀^L sin²(πy/L) dy = L/2`. -/
lemma integral_sin_sq_scaled {L : ℝ} (hL : 0 < L) :
    ∫ y in (0 : ℝ)..L, Real.sin (Real.pi * y / L) ^ 2 = L / 2 := by
  have hc : Real.pi / L ≠ 0 := by positivity
  have e : (fun y : ℝ => Real.sin (Real.pi * y / L) ^ 2) =
      fun y => (fun x : ℝ => Real.sin x ^ 2) (Real.pi / L * y) := by
    funext y; congr 2; ring
  rw [e, intervalIntegral.integral_comp_mul_left (fun x : ℝ => Real.sin x ^ 2) hc, integral_sin_sq]
  simp only [mul_zero, Real.sin_zero, zero_mul, Real.cos_zero, smul_eq_mul]
  rw [show Real.pi / L * L = Real.pi by field_simp, Real.sin_pi]
  field_simp
  ring

/-- `I_w = L/2` for the log-smooth weight. -/
lemma smooth_Iw (η : ℝ) (h0 : 0 < η) (h1 : η < 1 / 2) (hL : 0 < Leta η) :
    (wSmoothWeight η h0 h1).Iw = Leta η / 2 := by
  set L := Leta η
  have hlint := lintegral_h_eq (wSmoothWeight η h0 h1) (hSmooth L)
    (fun y hy => by unfold hSmooth; rw [if_neg (fun h => absurd h.1 (not_le.mpr hy))])
    (smooth_wt η h0 h1)
  have hsupp : (fun y => ENNReal.ofReal (hSmooth L y)).support ⊆ Set.Icc 0 L := by
    intro y hy
    by_contra hy'
    exact hy (by simp only; unfold hSmooth; rw [if_neg (show ¬ (0 ≤ y ∧ y ≤ L) from fun h => hy' h)]; simp)
  rw [← setLIntegral_eq_of_support_subset hsupp] at hlint
  have hcongr : Set.EqOn (fun y => ENNReal.ofReal (hSmooth L y))
      (fun y => ENNReal.ofReal (Real.sin (Real.pi * y / L) ^ 2)) (Set.Icc 0 L) := fun y hy => by
    simp only; unfold hSmooth; rw [if_pos (show 0 ≤ y ∧ y ≤ L from hy)]
  rw [setLIntegral_congr_fun measurableSet_Icc hcongr,
    ← ofReal_integral_eq_lintegral_ofReal
      ((by fun_prop : Continuous fun y : ℝ => Real.sin (Real.pi * y / L) ^ 2).integrableOn_Icc)
      (Eventually.of_forall fun y => sq_nonneg _),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hL.le,
    integral_sin_sq_scaled hL] at hlint
  have hI := (wSmoothWeight η h0 h1).Iw_pos
  exact ((ENNReal.ofReal_eq_ofReal_iff hI.le (by positivity)).mp hlint.symm)

/-- **`lem:CTlimit` (3): `C_T^+(w^sm_η) ≤ 1 + 83/L_η`.** -/
theorem lemCTlimit_smooth (W : Weight) (η : ℝ) (hW : W.w = wSmoothFun η) (hL : 3 ≤ Leta η) :
    CTp W ≤ ENNReal.ofReal (1 + 83 / Leta η) := by
  have h0 := eta_pos_of_smooth W η hW hL
  have h1 := eta_lt_half_of_Leta h0 hL
  set W' := wSmoothWeight η h0 h1 with hW'
  rw [CTp_congr (W' := W') (by rw [hW]; rfl)]
  set L := Leta η with hLdef
  have hLpos : 0 < L := by linarith
  have hwt := smooth_wt η h0 h1
  have hI : W'.Iw = L / 2 := smooth_Iw η h0 h1 hLpos
  have hw1 : W'.wtmax ≤ 1 := wtmax_le_one W' (hSmooth L) (fun y => (hSmooth_mem L y).2) hwt
  have hRS : ∀ S t, 0 < t → RS W' S t ≤ 1 + (cEmpty + 4 * Bconst / Ecal) / (L / 2) := by
    intro S t ht
    rw [← hI]
    exact RS_le_of_quasiconcave W' (hSmooth L) (hSmooth_mem L)
      (fun y hy => by unfold hSmooth; rw [if_neg (fun h => absurd h.1 (not_le.mpr hy))])
      (hSmooth_qc hLpos) hwt S t ht
  -- `m̃ ≤ (π/L) σ₁⁻` on `[η, ∞)` (`lem:Omega`(e))
  have hσ0 := sigma1m_nonneg
  set K := Real.pi / L * sigma1m with hK
  have hK0 : 0 ≤ K := by positivity
  have hhigh : ∀ u, W'.η ≤ u → mt W' u ≤ K := fun u hu => by
    have := lemOmega_e_proof W' (hSmooth L) _ (hSmooth_lipschitz hLpos) hwt u hu
    rwa [Real.coe_toNNReal _ (by positivity)] at this
  have hlog : Real.log (1 / (2 * W'.η)) ≤ L := by
    rw [hLdef]; unfold Leta
    exact Real.log_le_log (by simp only [W', wSmoothWeight_η]; positivity)
      (by simp only [W', wSmoothWeight_η]; rw [one_div_le_one_div (by positivity) h0]; linarith)
  have hKL : K * (1 + Real.log (1 / (2 * W'.η))) ≤ 4 / 3 * Real.pi * sigma1m := by
    calc K * (1 + Real.log (1 / (2 * W'.η))) ≤ K * (1 + L) := by gcongr
      _ = Real.pi * sigma1m * (1 / L + 1) := by rw [hK]; field_simp
      _ ≤ Real.pi * sigma1m * (1 / 3 + 1) := by
          gcongr
      _ = 4 / 3 * Real.pi * sigma1m := by ring
  have hRm : ∀ t, 0 < t → Rm W' t ≤ (3 + 4 / 3 * Real.pi * sigma1m) / (Ecal * (L / 2)) := by
    intro t ht
    have := Rm_le W' hw1 K hK0 hhigh t ht
    rw [hI] at this
    refine this.trans (div_le_div_of_nonneg_right (by linarith) ?_)
    have := Ecal_pos
    positivity
  refine (CTp_le_of W' _ _ hRS hRm).trans (ENNReal.ofReal_le_ofReal ?_)
  -- numerics: `c_∅ + (4B + 3 + (4/3)πσ₁⁻)/ℰ ≤ 41.5`
  have hc := cEmpty_le
  have hB := Bconst_lt
  have hE := Ecal_ge_047914
  have hE0 := Ecal_pos
  have hs := sigma1m_le
  have hpi := Real.pi_lt_d4
  have key : cEmpty + 4 * Bconst / Ecal + (3 + 4 / 3 * Real.pi * sigma1m) / Ecal ≤ 41.5 := by
    have : (4 * Bconst + (3 + 4 / 3 * Real.pi * sigma1m)) / Ecal ≤ 40.02 := by
      rw [div_le_iff₀ hE0]
      have : Real.pi * sigma1m ≤ 3.1416 * 0.2809 := mul_le_mul hpi.le hs hσ0 (by norm_num)
      nlinarith
    have e : 4 * Bconst / Ecal + (3 + 4 / 3 * Real.pi * sigma1m) / Ecal =
        (4 * Bconst + (3 + 4 / 3 * Real.pi * sigma1m)) / Ecal := by ring
    linarith
  have e : 1 + (cEmpty + 4 * Bconst / Ecal) / (L / 2) +
      (3 + 4 / 3 * Real.pi * sigma1m) / (Ecal * (L / 2)) =
      1 + 2 * (cEmpty + 4 * Bconst / Ecal + (3 + 4 / 3 * Real.pi * sigma1m) / Ecal) / L := by
    field_simp
    ring
  rw [e]
  gcongr
  linarith

/-! ### `lem:CTlimit` -/

/-- **`lem:CTlimit`**, sorry-free. -/
theorem lemCTlimit_proof : lemCTlimit_Statement :=
  ⟨fun W h h01 hsupp hqc hwt => lemCTlimit_one W h h01 hsupp hqc hwt,
    lemCTlimit_sharp, lemCTlimit_smooth⟩

end Families.Phase2.B
