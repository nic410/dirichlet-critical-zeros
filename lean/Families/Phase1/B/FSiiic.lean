/-
# `lem:fS` (iii), the constants `c_∅ − c_S`  (Lemma 6.19)

`lemfS_iii_c : ∀ S, 0 ≤ c_∅ − c_S ∧ c_∅ − c_S < 0.168`.

`c_∅ − c_S = ∑_{p∈S} a_p`, `a_p = log p/(p³(p−1)(1−p⁻²−p⁻³)) ≥ 0`; the sum over all primes is `0.16722…`.
Rigorous bound: the primes `p ≤ 31` explicitly (upper bounds for `log p` from `log 2 < 0.6931471808`, the
Taylor bound `Real.abs_log_sub_add_sum_range_le` for `log(3/4)`, and `log x ≤ x − 1`), and for `n ≥ 37`
`a_n ≤ 1/(2.67 n²(n−1))` (`log n ≤ n/e`), with the telescoping bound `∑_{n≥37} 1/(n²(n−1)) ≤ 1/(2·36²)`.
Total `< 0.16723 + 0.00015 + 0.0001 < 0.168`.
-/
import Families.LemmaC

noncomputable section

open scoped BigOperators
open Finset

namespace Families.Phase1.B

open Families

/-- The summand of `c_∅ − c_S`. -/
def cdiff (p : ℕ) : ℝ :=
  Real.log p / ((p : ℝ) ^ 3 * (p - 1) * (1 - (p : ℝ) ^ (-2 : ℤ) - (p : ℝ) ^ (-3 : ℤ)))

lemma cEmpty_sub_cS (S : Finset ℕ) : cEmpty - cS S = ∑ p ∈ S.filter Nat.Prime, cdiff p := by
  unfold cS cdiff; ring

lemma cdiff_den_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < (n : ℝ) ^ 3 * (n - 1) * (1 - (n : ℝ) ^ (-2 : ℤ) - (n : ℝ) ^ (-3 : ℤ)) := by
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (n : ℝ) ^ (-2 : ℤ) ≤ 1 / 4 := by
    rw [zpow_neg, zpow_ofNat, inv_le_comm₀ (by positivity) (by norm_num)]; nlinarith
  have h3 : (n : ℝ) ^ (-3 : ℤ) ≤ 1 / 8 := by
    rw [zpow_neg, zpow_ofNat, inv_le_comm₀ (by positivity) (by norm_num)]
    have := pow_le_pow_left₀ (by norm_num) h2 3
    norm_num at this ⊢; linarith
  apply mul_pos (mul_pos (by positivity) (by linarith))
  linarith

lemma cdiff_nonneg {n : ℕ} (hn : 2 ≤ n) : 0 ≤ cdiff n :=
  div_nonneg (Real.log_natCast_nonneg n) (cdiff_den_pos hn).le

/-- `cdiff p ≤ L/(p³(p−1)(1−p⁻²−p⁻³))` from `log p ≤ L`. -/
lemma cdiff_le_of_log_le {n : ℕ} (hn : 2 ≤ n) {L : ℝ} (hL : Real.log n ≤ L) :
    cdiff n ≤ L / ((n : ℝ) ^ 3 * (n - 1) * (1 - (n : ℝ) ^ (-2 : ℤ) - (n : ℝ) ^ (-3 : ℤ))) :=
  div_le_div_of_nonneg_right hL (cdiff_den_pos hn).le

/-! ### Upper bounds for `log p`, `p ≤ 31` -/

lemma log_two_le : Real.log 2 ≤ 0.6931471808 := Real.log_two_lt_d9.le

/-- `log(2^k · x) ≤ k log 2 + (x − 1)`. -/
lemma log_le_of_pow_two {n k : ℕ} (hn : 0 < n) :
    Real.log n ≤ k * 0.6931471808 + ((n : ℝ) / 2 ^ k - 1) := by
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hsplit : Real.log n = k * Real.log 2 + Real.log ((n : ℝ) / 2 ^ k) := by
    rw [Real.log_div (by positivity) h2k.ne', Real.log_pow]; ring
  rw [hsplit]
  have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (n : ℝ) / 2 ^ k by positivity)
  have h2 : (k : ℝ) * Real.log 2 ≤ k * 0.6931471808 :=
    mul_le_mul_of_nonneg_left log_two_le (Nat.cast_nonneg _)
  linarith

/-- `log 3 ≤ 1.099` (from `log(3/4) ≤ −(x + x²/2 + … + x⁵/5) + x⁶/(1−x)`, `x = 1/4`). -/
lemma log_three_le : Real.log 3 ≤ 1.099 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := 1 / 4) (by norm_num) 5
  have hs : (∑ i ∈ Finset.range 5, (1 / 4 : ℝ) ^ (i + 1) / (i + 1)) = 1 / 4 + 1 / 32 + 1 / 192 +
      1 / 1024 + 1 / 5120 := by
    simp [Finset.sum_range_succ]; norm_num
  rw [hs] at h
  have h34 : Real.log (1 - 1 / 4) = Real.log 3 - 2 * Real.log 2 := by
    rw [show (1 : ℝ) - 1 / 4 = 3 / 2 ^ 2 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]; push_cast; ring
  rw [h34] at h
  have := (abs_le.mp h).2
  norm_num at this
  linarith [log_two_le]

/-! ### The tail `n ≥ 37` -/

/-- `log n ≤ n/e`. -/
lemma log_le_div_e {x : ℝ} (hx : 0 < x) : Real.log x ≤ x / Real.exp 1 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < x / Real.exp 1 by positivity)
  rw [Real.log_div hx.ne' (Real.exp_pos 1).ne', Real.log_exp] at h
  linarith

lemma cdiff_le_tail {n : ℕ} (hn : 37 ≤ n) :
    cdiff n ≤ 1 / 2.67 * (1 / ((n : ℝ) ^ 2 * (n - 1))) := by
  have h37 : (37 : ℝ) ≤ n := by exact_mod_cast hn
  have hL := log_le_div_e (show (0 : ℝ) < n by linarith)
  have he := Real.exp_one_gt_d9
  have hL' : Real.log n ≤ (n : ℝ) / 2.7182818283 :=
    hL.trans (div_le_div_of_nonneg_left (by linarith) (by norm_num) he.le)
  have hden : (n : ℝ) ^ 3 * (n - 1) * (1 - 1 / 1369 - 1 / 50653) ≤
      (n : ℝ) ^ 3 * (n - 1) * (1 - (n : ℝ) ^ (-2 : ℤ) - (n : ℝ) ^ (-3 : ℤ)) := by
    have h1 : (n : ℝ) ^ (-2 : ℤ) ≤ 1 / 1369 := by
      rw [zpow_neg, zpow_ofNat, inv_le_comm₀ (by positivity) (by norm_num)]; nlinarith
    have h3 : (n : ℝ) ^ (-3 : ℤ) ≤ 1 / 50653 := by
      rw [zpow_neg, zpow_ofNat, inv_le_comm₀ (by positivity) (by norm_num)]
      have : (37 : ℝ) ^ 3 ≤ (n : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) h37 3
      norm_num at this ⊢; linarith
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by positivity) (by linarith))
    linarith
  have hpos : 0 < (n : ℝ) ^ 3 * (n - 1) * (1 - 1 / 1369 - 1 / 50653) :=
    mul_pos (mul_pos (by positivity) (by linarith)) (by norm_num)
  calc cdiff n ≤ ((n : ℝ) / 2.7182818283) /
        ((n : ℝ) ^ 3 * (n - 1) * (1 - (n : ℝ) ^ (-2 : ℤ) - (n : ℝ) ^ (-3 : ℤ))) :=
        cdiff_le_of_log_le (by omega) hL'
    _ ≤ ((n : ℝ) / 2.7182818283) / ((n : ℝ) ^ 3 * (n - 1) * (1 - 1 / 1369 - 1 / 50653)) :=
        div_le_div_of_nonneg_left (by positivity) hpos hden
    _ ≤ 1 / 2.67 * (1 / ((n : ℝ) ^ 2 * (n - 1))) := by
        have hn0 : (n : ℝ) ≠ 0 := by positivity
        have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
        have e : ((n : ℝ) / 2.7182818283) / ((n : ℝ) ^ 3 * (n - 1) * (1 - 1 / 1369 - 1 / 50653)) =
            1 / (2.7182818283 * (1 - 1 / 1369 - 1 / 50653)) * (1 / ((n : ℝ) ^ 2 * (n - 1))) := by
          field_simp
        rw [e]
        refine mul_le_mul_of_nonneg_right (by norm_num) ?_
        exact div_nonneg zero_le_one (mul_nonneg (by positivity) (by linarith))

/-- `∑_{n ∈ s} 1/(n²(n−1)) ≤ 1/(2·(a−1)²)` for `s ⊆ [a, ∞)`, `a ≥ 2`. -/
lemma sum_inv_sq_mul_pred_le (a : ℕ) (ha : 2 ≤ a) (s : Finset ℕ) (hs : ∀ n ∈ s, a ≤ n) :
    ∑ n ∈ s, 1 / ((n : ℝ) ^ 2 * (n - 1)) ≤ 1 / (2 * ((a : ℝ) - 1) ^ 2) := by
  -- telescoping: `1/(n²(n−1)) ≤ 1/(2(n−1)²) − 1/(2n²)`
  have key : ∀ N : ℕ, a ≤ N → ∑ n ∈ Finset.Icc a N, 1 / ((n : ℝ) ^ 2 * (n - 1)) ≤
      1 / (2 * ((a : ℝ) - 1) ^ 2) - 1 / (2 * (N : ℝ) ^ 2) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      rw [Finset.Icc_self, Finset.sum_singleton]
      have h : (2 : ℝ) ≤ a := by exact_mod_cast ha
      have ha1 : (0 : ℝ) < a - 1 := by linarith
      have ha0 : (0 : ℝ) < a := by linarith
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀
        (by positivity) (by positivity)]
      nlinarith [mul_pos ha1 ha0, mul_pos (mul_pos ha1 ha0) ha0, mul_pos (mul_pos ha1 ha1) ha0]
    | succ N hN ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have h : (2 : ℝ) ≤ N := by exact_mod_cast (le_trans ha hN)
      push_cast
      have hN0 : (0 : ℝ) < N := by linarith
      have hstep : 1 / (((N : ℝ) + 1) ^ 2 * ((N : ℝ) + 1 - 1)) ≤
          1 / (2 * (N : ℝ) ^ 2) - 1 / (2 * ((N : ℝ) + 1) ^ 2) := by
        rw [show (N : ℝ) + 1 - 1 = N by ring, div_sub_div _ _ (by positivity) (by positivity),
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_pos hN0 hN0, mul_pos (mul_pos hN0 hN0) hN0,
          mul_pos (mul_pos (mul_pos hN0 hN0) hN0) hN0]
      linarith
  refine le_trans ?_ ((key (max a (s.sup id)) (le_max_left _ _)).trans ?_)
  · refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun n hn _ => ?_
    · rw [Finset.mem_Icc]
      exact ⟨hs n hn, le_trans (Finset.le_sup (f := id) hn) (le_max_right _ _)⟩
    · have := (Finset.mem_Icc.mp hn).1
      have h : (2 : ℝ) ≤ n := by exact_mod_cast (le_trans ha this)
      exact div_nonneg zero_le_one (mul_nonneg (by positivity) (by linarith))
  · have : 0 ≤ 1 / (2 * ((max a (s.sup id) : ℕ) : ℝ) ^ 2) := by positivity
    linarith

/-! ### `lem:fS`(iii), the constants -/

/-- The head: `∑_{p ≤ 31 prime} a_p ≤ 0.16731`. -/
lemma head_bound (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime ∧ p ≤ 31) : ∑ p ∈ T, cdiff p ≤ 0.16731 := by
  have hsub : T ⊆ {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} := by
    intro p hp
    obtain ⟨hpp, hp31⟩ := hT p hp
    interval_cases p <;> simp_all (config := { decide := true })
  have hnn : ∀ p ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} : Finset ℕ), 0 ≤ cdiff p := by
    intro p hp; simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    exact cdiff_nonneg (by omega)
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => hnn p hp).trans ?_
  have b2 := cdiff_le_of_log_le (n := 2) le_rfl (show Real.log (2 : ℕ) ≤ 0.6931471808 by
    push_cast; exact log_two_le)
  have b3 := cdiff_le_of_log_le (n := 3) (by norm_num) (show Real.log (3 : ℕ) ≤ 1.099 by
    push_cast; exact log_three_le)
  have b5 := cdiff_le_of_log_le (n := 5) (by norm_num) (log_le_of_pow_two (k := 2) (by norm_num))
  have b7 := cdiff_le_of_log_le (n := 7) (by norm_num) (log_le_of_pow_two (k := 3) (by norm_num))
  have b11 := cdiff_le_of_log_le (n := 11) (by norm_num) (log_le_of_pow_two (k := 3) (by norm_num))
  have b13 := cdiff_le_of_log_le (n := 13) (by norm_num) (log_le_of_pow_two (k := 4) (by norm_num))
  have b17 := cdiff_le_of_log_le (n := 17) (by norm_num) (log_le_of_pow_two (k := 4) (by norm_num))
  have b19 := cdiff_le_of_log_le (n := 19) (by norm_num) (log_le_of_pow_two (k := 4) (by norm_num))
  have b23 := cdiff_le_of_log_le (n := 23) (by norm_num) (log_le_of_pow_two (k := 5) (by norm_num))
  have b29 := cdiff_le_of_log_le (n := 29) (by norm_num) (log_le_of_pow_two (k := 5) (by norm_num))
  have b31 := cdiff_le_of_log_le (n := 31) (by norm_num) (log_le_of_pow_two (k := 5) (by norm_num))
  have hsum : ∑ p ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31} : Finset ℕ), cdiff p =
      cdiff 2 + cdiff 3 + cdiff 5 + cdiff 7 + cdiff 11 + cdiff 13 + cdiff 17 + cdiff 19 +
        cdiff 23 + cdiff 29 + cdiff 31 := by
    simp [Finset.sum_insert]; ring
  rw [hsum]
  norm_num at b2 b3 b5 b7 b11 b13 b17 b19 b23 b29 b31
  linarith

/-- **`lem:fS`(iii), constants:** `0 ≤ c_∅ − c_S < 0.168` for every `S`. -/
theorem lemfS_iii_c : ∀ S : Finset ℕ, 0 ≤ cEmpty - cS S ∧ cEmpty - cS S < 0.168 := by
  intro S
  rw [cEmpty_sub_cS]
  refine ⟨Finset.sum_nonneg fun p hp => cdiff_nonneg (Finset.mem_filter.mp hp).2.two_le, ?_⟩
  rw [← Finset.sum_filter_add_sum_filter_not (S.filter Nat.Prime) (fun p => p ≤ 31)]
  have h1 := head_bound ((S.filter Nat.Prime).filter (fun p => p ≤ 31)) fun p hp => by
    rw [Finset.mem_filter, Finset.mem_filter] at hp; exact ⟨hp.1.2, hp.2⟩
  have hge : ∀ p ∈ (S.filter Nat.Prime).filter (fun p => ¬ p ≤ 31), 37 ≤ p := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_filter] at hp
    obtain ⟨⟨-, hpp⟩, hp31⟩ := hp
    by_contra h
    interval_cases p <;> first | omega | (norm_num at hpp)
  have h2 : ∑ p ∈ (S.filter Nat.Prime).filter (fun p => ¬ p ≤ 31), cdiff p ≤
      1 / 2.67 * (1 / (2 * ((37 : ℕ) - 1 : ℝ) ^ 2)) := by
    calc ∑ p ∈ (S.filter Nat.Prime).filter (fun p => ¬ p ≤ 31), cdiff p
        ≤ ∑ p ∈ (S.filter Nat.Prime).filter (fun p => ¬ p ≤ 31),
            1 / 2.67 * (1 / ((p : ℝ) ^ 2 * (p - 1))) :=
          Finset.sum_le_sum fun p hp => cdiff_le_tail (hge p hp)
      _ = 1 / 2.67 * ∑ p ∈ (S.filter Nat.Prime).filter (fun p => ¬ p ≤ 31),
            1 / ((p : ℝ) ^ 2 * (p - 1)) := by rw [Finset.mul_sum]
      _ ≤ 1 / 2.67 * (1 / (2 * ((37 : ℕ) - 1 : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (sum_inv_sq_mul_pred_le 37 (by norm_num) _ hge) (by norm_num)
  have hc : (1 / 2.67 : ℝ) * (1 / (2 * ((37 : ℕ) - 1 : ℝ) ^ 2)) < 0.00015 := by norm_num
  linarith

end Families.Phase1.B
