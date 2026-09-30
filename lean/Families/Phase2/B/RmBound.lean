/-
# `lem:CTlimit`, the bound for `R^m` (proof of Lemma 6.22)

`Rm_le`: if `‖w̃‖_∞ ≤ 1` and `m̃(u) ≤ K` for `u ≥ η` (`K ≥ 0`), then for every `t > 0`
`ℰ I_w R^m(t) ≤ ∑_k m̃(kt)/k ≤ 3 + K(1 + log(1/(2η)))`.
* `k t < η`: `m̃(kt) ≤ 3(kt/η)²` (`lem:Omega`(c)), so each term is `≤ 3t/η`, and there are at most
  `η/t` such `k` (the TeX sums `∑_{k<η/t} k`; the termwise bound gives the same `3`);
* `η ≤ kt ≤ 1/2`: `∑ 1/k ≤ 1 + log(b/a) ≤ 1 + log(1/(2η))` (Mathlib's harmonic bounds);
* `kt > 1/2`: `m̃(kt) = 0` (`lem:Omega`(c)).
The sharp weight has `K = 0` (`lem:Omega`(d)); the log-smooth weight `K = (π/L_η)σ₁⁻` (`lem:Omega`(e)).
-/
import Families.Phase2.B.RSBound
import Families.Weights

noncomputable section

open scoped BigOperators
open Finset

namespace Families.Phase2.B

open Families Families.Phase1.B

/-- `∑_{a≤k≤b} 1/k ≤ 1 + log(b/a)` for `1 ≤ a ≤ b`. -/
lemma sum_Icc_inv_le (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ k ∈ Finset.Icc a b, (1 : ℝ) / k ≤ 1 + Real.log ((b : ℝ) / a) := by
  have hH : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k = (harmonic n : ℝ) := by
    intro n
    rw [harmonic_eq_sum_Icc]; push_cast; simp [one_div]
  have hsplit : ∑ k ∈ Finset.Icc 1 b, (1 : ℝ) / k =
      ∑ k ∈ Finset.Icc 1 (a - 1), (1 : ℝ) / k + ∑ k ∈ Finset.Icc a b, (1 : ℝ) / k := by
    have e1 : Finset.Icc 1 b = Finset.Ioc 0 b := rfl
    have e2 : Finset.Icc 1 (a - 1) = Finset.Ioc 0 (a - 1) := rfl
    have e3 : Finset.Icc a b = Finset.Ioc (a - 1) b := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
    rw [e1, e2, e3, Finset.sum_Ioc_consecutive _ (Nat.zero_le _) (by omega)]
  have h1 := harmonic_le_one_add_log b
  have h2 := log_add_one_le_harmonic (a - 1)
  rw [show a - 1 + 1 = a by omega] at h2
  rw [← hH] at h1 h2
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (le_trans ha hab)
  rw [Real.log_div hb0.ne' ha0.ne']
  linarith

lemma mt_nonneg (W : Weight) (u : ℝ) : 0 ≤ mt W u := by
  unfold mt mfun; exact mul_nonneg (sq_nonneg u) (le_max_right _ _)

/-- `m̃(u) ≤ 3 ‖w̃‖_∞ (u/η)²` (`lem:Omega`(c)). -/
lemma mt_le_low (W : Weight) (hw1 : W.wtmax ≤ 1) {u : ℝ} (hu : 0 < u) :
    mt W u ≤ 3 * u ^ 2 / W.η ^ 2 := by
  have h := lemOmega_c W u hu
  have hw0 := wtmax_nonneg W
  have hmin : min (u⁻¹ ^ 2 / 4) (W.η⁻¹ ^ 2) ≤ W.η⁻¹ ^ 2 := min_le_right _ _
  have h' : mfun W u ≤ 3 * W.η⁻¹ ^ 2 := by
    calc mfun W u ≤ 3 * W.wtmax * min (u⁻¹ ^ 2 / 4) (W.η⁻¹ ^ 2) := h
      _ ≤ 3 * 1 * W.η⁻¹ ^ 2 := by
          apply mul_le_mul (by linarith) hmin (le_min (by positivity) (by positivity)) (by norm_num)
      _ = 3 * W.η⁻¹ ^ 2 := by ring
  unfold mt
  calc u ^ 2 * mfun W u ≤ u ^ 2 * (3 * W.η⁻¹ ^ 2) := mul_le_mul_of_nonneg_left h' (sq_nonneg u)
    _ = 3 * u ^ 2 / W.η ^ 2 := by rw [inv_pow]; ring

lemma mt_eq_zero_of_gt_half (W : Weight) {u : ℝ} (hu : 1 / 2 < u) : mt W u = 0 := by
  unfold mt; rw [mfun_eq_zero_of_gt_half W u hu, mul_zero]

/-- **The `R^m` bound.** -/
theorem Rm_le (W : Weight) (hw1 : W.wtmax ≤ 1) (K : ℝ) (hK : 0 ≤ K)
    (hhigh : ∀ u, W.η ≤ u → mt W u ≤ K) (t : ℝ) (ht : 0 < t) :
    Rm W t ≤ (3 + K * (1 + Real.log (1 / (2 * W.η)))) / (Ecal * W.Iw) := by
  have hE := Ecal_pos
  have hI : 0 < W.Iw := W.Iw_pos
  have hη := W.η_pos
  have hη2 := W.η_lt_half
  set M := ⌊1 / t⌋₊
  -- the `R^m` sum is bounded termwise by two indicator sums
  have hterm : ∀ k ∈ Finset.Icc 1 M, (Nat.totient k : ℝ) / (k : ℝ) ^ 2 * mt W (k * t) ≤
      (if (k : ℝ) * t < W.η then 3 * t / W.η else 0) +
        (if W.η ≤ (k : ℝ) * t ∧ (k : ℝ) * t ≤ 1 / 2 then K * (1 / (k : ℝ)) else 0) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    have hkt : 0 < (k : ℝ) * t := mul_pos hk0 ht
    have hφ : (Nat.totient k : ℝ) ≤ k := by exact_mod_cast Nat.totient_le k
    have hm0 := mt_nonneg W ((k : ℝ) * t)
    have h1 : (Nat.totient k : ℝ) / (k : ℝ) ^ 2 * mt W (k * t) ≤ mt W (k * t) / k := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hk0]
      nlinarith [mul_le_mul_of_nonneg_right hφ hm0]
    refine h1.trans ?_
    by_cases hlow : (k : ℝ) * t < W.η
    · rw [if_pos hlow, if_neg (fun h => absurd h.1 (not_le.mpr hlow)), add_zero]
      have := mt_le_low W hw1 hkt
      rw [div_le_iff₀ hk0]
      calc mt W (k * t) ≤ 3 * ((k : ℝ) * t) ^ 2 / W.η ^ 2 := this
        _ = 3 * t / W.η * ((k : ℝ) * t / W.η) * k := by field_simp
        _ ≤ 3 * t / W.η * 1 * k := by
            gcongr
            rw [div_le_one hη]; exact hlow.le
        _ = 3 * t / W.η * k := by ring
    · rw [if_neg hlow, zero_add]
      by_cases hhalf : (k : ℝ) * t ≤ 1 / 2
      · rw [if_pos ⟨not_lt.mp hlow, hhalf⟩, mul_one_div]
        exact div_le_div_of_nonneg_right (hhigh _ (not_lt.mp hlow)) hk0.le
      · rw [if_neg (fun h => hhalf h.2), mt_eq_zero_of_gt_half W (not_le.mp hhalf), zero_div]
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter] at hsum
  -- the low part: at most `η/t` terms, each `3t/η`
  set F₁ := (Finset.Icc 1 M).filter (fun k : ℕ => (k : ℝ) * t < W.η) with hF₁
  have hlow : ∑ k ∈ F₁, 3 * t / W.η ≤ 3 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hsub : F₁ ⊆ Finset.Icc 1 ⌊W.η / t⌋₊ := by
      intro k hk
      obtain ⟨hk1, hk2⟩ := Finset.mem_filter.mp hk
      refine Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk1).1, Nat.le_floor ?_⟩
      rw [le_div_iff₀ ht]; exact hk2.le
    have hcard : (F₁.card : ℝ) ≤ W.η / t := by
      have := Finset.card_le_card hsub
      rw [Nat.card_Icc, Nat.add_sub_cancel] at this
      exact le_trans (by exact_mod_cast this) (Nat.floor_le (by positivity))
    calc (F₁.card : ℝ) * (3 * t / W.η) ≤ W.η / t * (3 * t / W.η) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 3 := by field_simp
  -- the middle part: `∑ 1/k ≤ 1 + log(1/(2η))`
  set F₂ := (Finset.Icc 1 M).filter
    (fun k : ℕ => W.η ≤ (k : ℝ) * t ∧ (k : ℝ) * t ≤ 1 / 2) with hF₂
  have hlog0 : 0 ≤ Real.log (1 / (2 * W.η)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]; linarith
  have hmid : ∑ k ∈ F₂, K * (1 / (k : ℝ)) ≤ K * (1 + Real.log (1 / (2 * W.η))) := by
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hK
    rcases F₂.eq_empty_or_nonempty with hne | hne
    · rw [hne, Finset.sum_empty]; linarith
    set a := F₂.min' hne
    set b := F₂.max' hne
    have haF := F₂.min'_mem hne
    have hbF := F₂.max'_mem hne
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp (Finset.mem_filter.mp haF).1).1
    have hab : a ≤ b := F₂.min'_le _ hbF
    have hsub : F₂ ⊆ Finset.Icc a b := fun k hk =>
      Finset.mem_Icc.mpr ⟨F₂.min'_le k hk, F₂.le_max' k hk⟩
    have hs := (Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => by positivity).trans
      (sum_Icc_inv_le a b ha1 hab)
    have hat : W.η ≤ (a : ℝ) * t := (Finset.mem_filter.mp haF).2.1
    have hbt : (b : ℝ) * t ≤ 1 / 2 := (Finset.mem_filter.mp hbF).2.2
    have ha0 : (0 : ℝ) < a := by exact_mod_cast ha1
    have hb0 : (0 : ℝ) < b := by exact_mod_cast (le_trans ha1 hab)
    have hba : (b : ℝ) / a ≤ 1 / (2 * W.η) := by
      rw [div_le_div_iff₀ ha0 (by positivity)]
      nlinarith
    have := Real.log_le_log (by positivity) hba
    linarith
  -- assemble
  have hmain : ∑ k ∈ Finset.Icc 1 M, (Nat.totient k : ℝ) / (k : ℝ) ^ 2 * mt W (k * t) ≤
      3 + K * (1 + Real.log (1 / (2 * W.η))) := by linarith
  unfold Rm
  rw [inv_mul_eq_div]
  exact div_le_div_of_nonneg_right hmain (by positivity)

end Families.Phase2.B
