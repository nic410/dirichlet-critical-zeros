/-
# `lem:CTlimit`, the bound for `R_S` (proof of Lemma 6.22)

For `w̃(u) = h(log(1/u))` with `h : ℝ → [0,1]` quasi-concave (all superlevel sets `{h > λ}` are
intervals) and `h = 0` on `(−∞,0)`:
`R_S(t) ≤ 1 + (c_∅ + 4B/ℰ)/I_w` for every `S` and every `t > 0` (`RS_le_of_quasiconcave`).

Proof (as in the TeX, via the layer-cake formula):
* `sum_Icc_fS_le`: `∑_{α≤n≤β} f_S(n)/n ≤ ℰ log(β/α) + ℰ c_∅ + 4B` for integers `1 ≤ α ≤ β`, from
  `lem:fS`(iii) (`|E_S(s)| ≤ 2B e^{−s/2}`) at `log β` and at the left limit at `log α`, and
  `c_S ≤ c_∅` (`lem:fS`(iii)); for `α = 1` the sum is `F_S(log β)`.
* `lintegral_h_eq`: `∫_ℝ h = I_w` (change of variables `y = log(1/u)`,
  `lintegral_image_eq_lintegral_abs_deriv_mul`).
* `sum_mul_h_le`: with `a_n = f_S(n)/n ≥ 0`, `y_n = log(1/(nt))` (decreasing in `n`),
  `∑ a_n h(y_n) = ∫_0^∞ ∑_{h(y_n)>λ} a_n dλ`; for `0 < λ < 1` the `n` with `h(y_n) > λ` lie in
  `[n₁, n₂]` with `y_{n₁}, y_{n₂} ∈ {h > λ}`, so `log(n₂/n₁) = y_{n₁} − y_{n₂} ≤ |{h > λ}|`; and
  `∫_0^∞ |{h > λ}| dλ = ∫ h` (Mathlib's layer cake `lintegral_eq_lintegral_meas_lt`).
Everything is done in `ℝ≥0∞`, so no integrability side conditions arise.
-/
import Families.Phase2.B.CTNumerics

noncomputable section

open scoped BigOperators ENNReal Topology
open Finset MeasureTheory Filter

namespace Families.Phase2.B

open Families Families.Phase1.B

/-! ### Partial sums of `f_S(n)/n` -/

lemma floor_exp_log_nat {n : ℕ} (hn : 1 ≤ n) : ⌊Real.exp (Real.log n)⌋₊ = n := by
  rw [Real.exp_log (by exact_mod_cast hn)]; exact Nat.floor_natCast n

/-- `F_S(log n) ≤ ℰ(log n + c_S) + 2B`. -/
lemma FS_log_le (S : Finset ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 n, fS S k / k ≤ Ecal * (Real.log n + cS S) + 2 * Bconst := by
  have h := lemfS_iii_a S (Real.log n) (Real.log_natCast_nonneg n)
  unfold ES at h
  rw [floor_exp_log_nat hn] at h
  have hB : 0 ≤ Bconst := le_trans zero_le_one one_le_Bconst
  have he : Real.exp (-Real.log n / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have := Real.log_natCast_nonneg n; linarith
  have := (abs_le.mp h).2
  nlinarith

/-- `F_S(log n −) ≥ ℰ(log n + c_S) − 2B` (left limit at `log n`, `n ≥ 2`). -/
lemma FS_pred_ge (S : Finset ℕ) {n : ℕ} (hn : 2 ≤ n) :
    Ecal * (Real.log n + cS S) - 2 * Bconst ≤ ∑ k ∈ Finset.Icc 1 (n - 1), fS S k / k := by
  have hB : 0 ≤ Bconst := le_trans zero_le_one one_le_Bconst
  have hn1 : (1 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n - 1 by omega)
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by push_cast [show 1 ≤ n by omega]; ring
  have hlt : Real.log ((n - 1 : ℕ) : ℝ) < Real.log n :=
    Real.log_lt_log (by linarith) (by rw [hcast]; linarith)
  have hcont : Continuous fun s : ℝ => Ecal * (s + cS S) - 2 * Bconst := by fun_prop
  refine le_of_tendsto ((hcont.tendsto (Real.log n)).mono_left
    (nhdsWithin_le_nhds (s := Set.Iio (Real.log n)))) ?_
  filter_upwards [Ioo_mem_nhdsLT hlt] with s hs
  have hs0 : 0 ≤ s := le_trans (Real.log_nonneg hn1) hs.1.le
  have hfl : ⌊Real.exp s⌋₊ = n - 1 := by
    rw [Nat.floor_eq_iff (Real.exp_pos s).le]
    constructor
    · have := Real.exp_lt_exp.mpr hs.1
      rw [Real.exp_log (by linarith)] at this; exact this.le
    · have := Real.exp_lt_exp.mpr hs.2
      rw [Real.exp_log (by positivity)] at this; rw [hcast]; linarith
  have h := lemfS_iii_a S s hs0
  unfold ES at h
  rw [hfl] at h
  have he : Real.exp (-s / 2) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
  have := (abs_le.mp h).1
  nlinarith

/-- **Sums over integer intervals.** For `1 ≤ n₁ ≤ n₂`:
`∑_{n₁≤n≤n₂} f_S(n)/n ≤ ℰ log(n₂/n₁) + (ℰ c_∅ + 4B)`. -/
theorem sum_Icc_fS_le (S : Finset ℕ) {n₁ n₂ : ℕ} (h1 : 1 ≤ n₁) (h12 : n₁ ≤ n₂) :
    ∑ k ∈ Finset.Icc n₁ n₂, fS S k / k ≤
      Ecal * Real.log ((n₂ : ℝ) / n₁) + (Ecal * cEmpty + 4 * Bconst) := by
  have hB : 0 ≤ Bconst := le_trans zero_le_one one_le_Bconst
  have hE := Ecal_pos
  have hcS := (lemfS_iii_c S).1
  have hc0 := cEmpty_pos
  have hup := FS_log_le S (le_trans h1 h12)
  have hn1 : (0 : ℝ) < n₁ := by exact_mod_cast h1
  have hn2 : (0 : ℝ) < n₂ := by exact_mod_cast (le_trans h1 h12)
  rw [Real.log_div hn2.ne' hn1.ne']
  rcases eq_or_lt_of_le h1 with h | h
  · subst h
    simp only [Nat.cast_one, Real.log_one, sub_zero]
    nlinarith
  · have hlow := FS_pred_ge S (show 2 ≤ n₁ by omega)
    have hsplit : ∑ k ∈ Finset.Icc 1 n₂, fS S k / k =
        ∑ k ∈ Finset.Icc 1 (n₁ - 1), fS S k / k + ∑ k ∈ Finset.Icc n₁ n₂, fS S k / k := by
      have e1 : Finset.Icc 1 n₂ = Finset.Ioc 0 n₂ := rfl
      have e2 : Finset.Icc 1 (n₁ - 1) = Finset.Ioc 0 (n₁ - 1) := rfl
      have e3 : Finset.Icc n₁ n₂ = Finset.Ioc (n₁ - 1) n₂ := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
      rw [e1, e2, e3, Finset.sum_Ioc_consecutive _ (Nat.zero_le _) (by omega)]
    have hlog1 : 0 ≤ Real.log n₁ := Real.log_natCast_nonneg n₁
    nlinarith

/-! ### `∫ h = I_w` -/

/-- The integrability of `u w(u)` on `[0,1]` follows from `I_w > 0`. -/
lemma intervalIntegrable_Iw (W : Weight) :
    IntervalIntegrable (fun u => u * W.w u) MeasureTheory.volume 0 1 := by
  by_contra h
  have := W.Iw_pos
  rw [intervalIntegral.integral_undef h] at this
  exact lt_irrefl _ this

/-- **`∫_ℝ h = I_w`** for `w̃(u) = h(log(1/u))`, `h ≥ 0`, `h = 0` on `(−∞,0)`. -/
theorem lintegral_h_eq (W : Weight) (h : ℝ → ℝ) (hneg : ∀ y, y < 0 → h y = 0)
    (hwt : ∀ u, 0 < u → W.wt u = h (Real.log (1 / u))) :
    ∫⁻ y, ENNReal.ofReal (h y) = ENNReal.ofReal W.Iw := by
  -- restrict to `(0, ∞)`
  have hsupp : (fun y => ENNReal.ofReal (h y)).support ⊆ Set.Ici 0 := by
    intro y hy
    by_contra hy'
    exact hy (by simp [hneg y (not_le.mp hy')])
  rw [← setLIntegral_eq_of_support_subset hsupp, setLIntegral_congr Ioi_ae_eq_Ici.symm]
  -- change of variables `y = −log u`, `u ∈ (0,1)`
  have himg : (fun u : ℝ => -Real.log u) '' Set.Ioo 0 1 = Set.Ioi 0 := by
    ext y
    simp only [Set.mem_image, Set.mem_Ioo, Set.mem_Ioi]
    constructor
    · rintro ⟨u, ⟨hu0, hu1⟩, rfl⟩
      have := Real.log_neg hu0 hu1; linarith
    · intro hy
      refine ⟨Real.exp (-y), ⟨Real.exp_pos _, ?_⟩, by rw [Real.log_exp]; ring⟩
      rw [Real.exp_lt_one_iff]; linarith
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivWithinAt (fun u : ℝ => -Real.log u) (-x⁻¹) (Set.Ioo 0 1) x := fun x hx =>
    (Real.hasDerivAt_log hx.1.ne').neg.hasDerivWithinAt
  have hinj : Set.InjOn (fun u : ℝ => -Real.log u) (Set.Ioo 0 1) := by
    intro x hx y hy hxy
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr hx.1) (Set.mem_Ioi.mpr hy.1) (neg_inj.mp hxy)
  rw [← himg, lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hderiv hinj]
  have hcongr : Set.EqOn (fun x => ENNReal.ofReal |-x⁻¹| * ENNReal.ofReal (h (-Real.log x)))
      (fun u => ENNReal.ofReal (u * W.w u)) (Set.Ioo 0 1) := by
    intro x hx
    have hx0 := hx.1
    simp only
    rw [abs_neg, abs_of_pos (inv_pos.mpr hx0), ← ENNReal.ofReal_mul (inv_pos.mpr hx0).le]
    congr 1
    have := hwt x hx0
    rw [one_div, Real.log_inv] at this
    rw [← this]
    unfold Weight.wt
    field_simp
  rw [setLIntegral_congr_fun measurableSet_Ioo hcongr]
  -- back to the Bochner integral `I_w`
  have hint : MeasureTheory.IntegrableOn (fun u => u * W.w u) (Set.Ioo 0 1) := by
    have := (intervalIntegrable_Iw W).1
    exact this.mono_set Set.Ioo_subset_Ioc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun u hu =>
      mul_nonneg hu.1.le (W.nonneg u)))]
  congr 1
  unfold Weight.Iw
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]

/-! ### The layer-cake bound -/

/-- **Layer cake.** For `h : ℝ → [0,1]` quasi-concave, `t > 0`, and any `M`:
`∑_{1≤n≤M} (f_S(n)/n) h(log(1/(nt))) ≤ ℰ ∫h + (ℰ c_∅ + 4B)` (in `ℝ≥0∞`). -/
theorem sum_mul_h_le (S : Finset ℕ) (h : ℝ → ℝ) (h01 : ∀ y, 0 ≤ h y ∧ h y ≤ 1)
    (hqc : ∀ lam : ℝ, Set.OrdConnected {y | lam < h y}) (t : ℝ) (ht : 0 < t) (M : ℕ) :
    ENNReal.ofReal (∑ n ∈ Finset.Icc 1 M, fS S n / n * h (Real.log (1 / (n * t)))) ≤
      ENNReal.ofReal Ecal * (∫⁻ y, ENNReal.ofReal (h y)) +
        ENNReal.ofReal (Ecal * cEmpty + 4 * Bconst) := by
  set a : ℕ → ℝ := fun n => fS S n / n with ha
  set yv : ℕ → ℝ := fun n => Real.log (1 / (n * t)) with hyv
  set C : ℝ := Ecal * cEmpty + 4 * Bconst with hC
  have hE := Ecal_pos
  have hB : 0 ≤ Bconst := le_trans zero_le_one one_le_Bconst
  have hC0 : 0 ≤ C := by have := cEmpty_pos; positivity
  have ha0 : ∀ n, 0 ≤ a n := fun n => div_nonneg (fS_nonneg S n) (Nat.cast_nonneg n)
  -- measurability of `h`
  have hmeas : Measurable h := measurable_of_Ioi fun x => (hqc x).measurableSet
  -- (1) the left side as a layer-cake integral
  set G : ℝ → ℝ≥0∞ := fun lam => ∑ n ∈ Finset.Icc 1 M,
    ENNReal.ofReal (a n) * (Set.Iio (h (yv n))).indicator 1 lam with hG
  have hL : ENNReal.ofReal (∑ n ∈ Finset.Icc 1 M, a n * h (yv n)) = ∫⁻ lam in Set.Ioi 0, G lam := by
    rw [ENNReal.ofReal_sum_of_nonneg fun n _ => mul_nonneg (ha0 n) (h01 _).1]
    simp only [hG]
    rw [lintegral_finsetSum (Finset.Icc 1 M)
      (f := fun n lam => ENNReal.ofReal (a n) * (Set.Iio (h (yv n))).indicator 1 lam) fun n _ =>
        (measurable_const.indicator measurableSet_Iio).const_mul _]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [lintegral_const_mul _ (measurable_one.indicator measurableSet_Iio),
      lintegral_indicator_one measurableSet_Iio, Measure.restrict_apply measurableSet_Iio,
      Set.Iio_inter_Ioi, Real.volume_Ioo, sub_zero, ENNReal.ofReal_mul (ha0 n)]
  -- (2) the pointwise bound for `λ > 0`
  have hpt : ∀ lam ∈ Set.Ioi (0 : ℝ), G lam ≤
      ENNReal.ofReal Ecal * MeasureTheory.volume {y | lam < h y} +
        (Set.Iio 1).indicator (fun _ => ENNReal.ofReal C) lam := by
    intro lam hlam
    set N := (Finset.Icc 1 M).filter (fun n => lam < h (yv n)) with hN
    have hGN : G lam = ENNReal.ofReal (∑ n ∈ N, a n) := by
      rw [hG, ENNReal.ofReal_sum_of_nonneg fun n _ => ha0 n, hN, Finset.sum_filter]
      refine Finset.sum_congr rfl fun n _ => ?_
      by_cases hn : lam < h (yv n)
      · rw [if_pos hn, Set.indicator_of_mem (Set.mem_Iio.mpr hn), Pi.one_apply, mul_one]
      · rw [if_neg hn, Set.indicator_of_notMem (fun h' => hn (Set.mem_Iio.mp h')), mul_zero]
    rw [hGN]
    rcases N.eq_empty_or_nonempty with hNe | hNe
    · rw [hNe, Finset.sum_empty, ENNReal.ofReal_zero]; exact zero_le
    have hlam1 : lam < 1 := by
      obtain ⟨n, hn⟩ := hNe
      exact lt_of_lt_of_le (Finset.mem_filter.mp hn).2 (h01 _).2
    rw [Set.indicator_of_mem (Set.mem_Iio.mpr hlam1)]
    set n₁ := N.min' hNe
    set n₂ := N.max' hNe
    have hn₁N : n₁ ∈ N := N.min'_mem hNe
    have hn₂N : n₂ ∈ N := N.max'_mem hNe
    have hn₁ : 1 ≤ n₁ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hn₁N).1).1
    have h12 : n₁ ≤ n₂ := N.min'_le _ hn₂N
    have hsub : N ⊆ Finset.Icc n₁ n₂ := fun n hn =>
      Finset.mem_Icc.mpr ⟨N.min'_le n hn, N.le_max' n hn⟩
    have hsum : ∑ n ∈ N, a n ≤ Ecal * Real.log ((n₂ : ℝ) / n₁) + C :=
      (Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => ha0 n).trans
        (sum_Icc_fS_le S hn₁ h12)
    have hn1r : (0 : ℝ) < n₁ := by exact_mod_cast hn₁
    have hn2r : (0 : ℝ) < n₂ := by exact_mod_cast (le_trans hn₁ h12)
    have hlog0 : 0 ≤ Real.log ((n₂ : ℝ) / n₁) :=
      Real.log_nonneg (by rw [le_div_iff₀ hn1r, one_mul]; exact_mod_cast h12)
    -- `log(n₂/n₁) = y_{n₁} − y_{n₂} ≤ |{h > λ}|`
    have hvol : ENNReal.ofReal (Real.log ((n₂ : ℝ) / n₁)) ≤
        MeasureTheory.volume {y | lam < h y} := by
      have hIcc : Set.Icc (yv n₂) (yv n₁) ⊆ {y | lam < h y} :=
        (hqc lam).out (Finset.mem_filter.mp hn₂N).2 (Finset.mem_filter.mp hn₁N).2
      refine le_trans (le_of_eq ?_) (measure_mono hIcc)
      rw [Real.volume_Icc]
      congr 1
      simp only [hyv]
      rw [one_div, one_div, Real.log_inv, Real.log_inv, Real.log_mul hn1r.ne' ht.ne',
        Real.log_mul hn2r.ne' ht.ne', Real.log_div hn2r.ne' hn1r.ne']
      ring
    calc ENNReal.ofReal (∑ n ∈ N, a n)
        ≤ ENNReal.ofReal (Ecal * Real.log ((n₂ : ℝ) / n₁) + C) := ENNReal.ofReal_le_ofReal hsum
      _ = ENNReal.ofReal Ecal * ENNReal.ofReal (Real.log ((n₂ : ℝ) / n₁)) + ENNReal.ofReal C := by
          rw [ENNReal.ofReal_add (by positivity) hC0, ENNReal.ofReal_mul hE.le]
      _ ≤ ENNReal.ofReal Ecal * MeasureTheory.volume {y | lam < h y} + ENNReal.ofReal C := by
          gcongr
  -- (3) integrate
  have hmeasI : Measurable ((Set.Iio (1 : ℝ)).indicator fun _ => ENNReal.ofReal C) :=
    measurable_const.indicator measurableSet_Iio
  calc ENNReal.ofReal (∑ n ∈ Finset.Icc 1 M, fS S n / n * h (Real.log (1 / (n * t))))
      = ∫⁻ lam in Set.Ioi 0, G lam := hL
    _ ≤ ∫⁻ lam in Set.Ioi 0, (ENNReal.ofReal Ecal * MeasureTheory.volume {y | lam < h y} +
          (Set.Iio 1).indicator (fun _ => ENNReal.ofReal C) lam) :=
        setLIntegral_mono' measurableSet_Ioi hpt
    _ = ENNReal.ofReal Ecal * (∫⁻ lam in Set.Ioi 0, MeasureTheory.volume {y | lam < h y}) +
          ENNReal.ofReal C := by
        rw [lintegral_add_right _ hmeasI, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_indicator_const measurableSet_Iio, Measure.restrict_apply measurableSet_Iio,
          Set.Iio_inter_Ioi, Real.volume_Ioo, sub_zero, ENNReal.ofReal_one, mul_one]
    _ = ENNReal.ofReal Ecal * (∫⁻ y, ENNReal.ofReal (h y)) + ENNReal.ofReal C := by
        have hlc : ∫⁻ y, ENNReal.ofReal (h y) =
            ∫⁻ lam in Set.Ioi 0, MeasureTheory.volume {y | lam < h y} :=
          lintegral_eq_lintegral_meas_lt MeasureTheory.volume
            (Eventually.of_forall fun y => (h01 y).1) hmeas.aemeasurable
        rw [hlc]

/-! ### `R_S ≤ 1 + (c_∅ + 4B/ℰ)/I_w` -/

/-- **`lem:CTlimit`, the `R_S` bound.** -/
theorem RS_le_of_quasiconcave (W : Weight) (h : ℝ → ℝ) (h01 : ∀ y, 0 ≤ h y ∧ h y ≤ 1)
    (hneg : ∀ y, y < 0 → h y = 0) (hqc : ∀ lam : ℝ, Set.OrdConnected {y | lam < h y})
    (hwt : ∀ u, 0 < u → W.wt u = h (Real.log (1 / u))) (S : Finset ℕ) (t : ℝ) (ht : 0 < t) :
    RS W S t ≤ 1 + (cEmpty + 4 * Bconst / Ecal) / W.Iw := by
  have hE := Ecal_pos
  have hI : 0 < W.Iw := W.Iw_pos
  have hB : 0 ≤ Bconst := le_trans zero_le_one one_le_Bconst
  have hC0 : 0 ≤ Ecal * cEmpty + 4 * Bconst := by have := cEmpty_pos; positivity
  set X := ∑ n ∈ Finset.Icc 1 ⌊1 / t⌋₊, fS S n / n * h (Real.log (1 / (n * t))) with hX
  have hRS : RS W S t = (Ecal * W.Iw)⁻¹ * X := by
    unfold RS
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    rw [hwt _ (mul_pos hn ht)]
  have hbound := sum_mul_h_le S h h01 hqc t ht ⌊1 / t⌋₊
  rw [← hX, lintegral_h_eq W h hneg hwt, ← ENNReal.ofReal_mul hE.le,
    ← ENNReal.ofReal_add (by positivity) hC0,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at hbound
  rw [hRS]
  calc (Ecal * W.Iw)⁻¹ * X ≤ (Ecal * W.Iw)⁻¹ * (Ecal * W.Iw + (Ecal * cEmpty + 4 * Bconst)) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = 1 + (cEmpty + 4 * Bconst / Ecal) / W.Iw := by
        field_simp

/-- `c_∅ + 4B/ℰ ≤ 32.6` (`c_∅ ≤ 1.4608`, `B < 3.73`, `ℰ ≥ 0.47914`). -/
lemma cEmpty_add_le : cEmpty + 4 * Bconst / Ecal ≤ 32.6 := by
  have h1 := cEmpty_le
  have h2 := Bconst_lt
  have h3 := Ecal_ge_047914
  have hE := Ecal_pos
  have : 4 * Bconst / Ecal ≤ 31.1392 := by
    rw [div_le_iff₀ hE]; nlinarith
  linarith

/-- **`lem:CTlimit` (1).** -/
theorem lemCTlimit_one (W : Weight) (h : ℝ → ℝ) (h01 : ∀ y, 0 ≤ h y ∧ h y ≤ 1)
    (hsupp : ∀ y, (y < 0 ∨ Leta W.η < y) → h y = 0)
    (hqc : ∀ lam : ℝ, Set.OrdConnected {y | lam < h y})
    (hwt : ∀ u, 0 < u → W.wt u = h (Real.log (1 / u))) :
    CT W ≤ ENNReal.ofReal (1 + (cEmpty + 4 * Bconst / Ecal) / W.Iw) ∧
    CT W ≤ ENNReal.ofReal (1 + 32.6 / W.Iw) := by
  have hneg : ∀ y, y < 0 → h y = 0 := fun y hy => hsupp y (Or.inl hy)
  have hCT : CT W ≤ ENNReal.ofReal (1 + (cEmpty + 4 * Bconst / Ecal) / W.Iw) := by
    refine iSup_le fun S => essSup_le_of_ae_le _ ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
    exact ENNReal.ofReal_le_ofReal (RS_le_of_quasiconcave W h h01 hneg hqc hwt S t ht)
  refine ⟨hCT, hCT.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have := cEmpty_add_le
  have hI := W.Iw_pos
  gcongr

end Families.Phase2.B
