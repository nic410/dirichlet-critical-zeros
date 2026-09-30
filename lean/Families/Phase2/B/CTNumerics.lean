/-
# Numerical constants for `lem:CTlimit` (Lemma 6.22)

* `gamma_le : γ ≤ 0.5851` — from Mathlib's `γ < H_n − log n` at `n = 64` (`log 64 = 6 log 2`);
  Mathlib's own `γ < 2/3` is too weak here.
* `cEmpty_le : c_∅ ≤ 1.4608` (true value `1.41070…`) — `c_∅ = γ + ∑_p a_p log p`,
  `a_p = (p⁻²+p⁻³)/(1−p⁻²−p⁻³)`; the primes `p ≤ 100` explicitly (upper bounds for `log p` from
  `log 2 < 0.6931471808`, `log 3 ≤ 1.099` and `log x ≤ x − 1`), the primes `p > 100` by Abel summation
  against Chebyshev's `θ(n) ≤ n log 4` (`abel_theta`, a version of `BconstCert.abel_invariant` for a
  general antitone weight): `∑_{p>100} log p/p² ≤ 2 log 4/101`, and `a_p ≤ 1.011/p²`.
  Total `≤ 0.5851 + 0.8321 + 0.0278 < 1.4608`.
* `cEmpty_pos : 0 < c_∅`.
* `sigma1m_le : σ₁⁻ ≤ 0.2809` (true value `0.2631…`; the TeX states `< 0.27`) — the head `r ≤ 31` with
  hand-evaluated Möbius values (`moebius_eval`, via Mathlib's `Nat.primeFactorsList` simproc; no
  `decide` on `μ`), the tail `r ≥ 32` by dyadic blocks `[2^j, 2^{j+1})` and the proved
  `∑_{r≥a} 1/(r²φ(r)) ≤ 3/a²`: `∑_{j≥5} 3(j+1) log 2/4^j = 3 log 2 · 76/(9·1024) < 0.01715`.

All checks are `norm_num`/`decide` (kernel); no `native_decide`.
-/
import Families.Phase1.B.All
import Families.Certificate.Ecal

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius
open Finset

namespace Families.Phase2.B

open Families Families.Phase1.B

/-! ### `γ` -/

/-- `γ ≤ 0.5851` (from `γ < H₆₄ − log 64`, `H₆₄ ≤ 4.7439`). -/
lemma gamma_le : Real.eulerMascheroniConstant ≤ 0.5851 := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 64
  rw [Real.eulerMascheroniSeq', if_neg (by norm_num)] at h
  have hH : (harmonic 64 : ℚ) ≤ 4.7439 := by
    unfold harmonic
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  have hH' : ((harmonic 64 : ℚ) : ℝ) ≤ ((4.7439 : ℚ) : ℝ) := Rat.cast_le.mpr hH
  have hl : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; norm_num
  have := Real.log_two_gt_d9
  push_cast at h hH'
  linarith

/-! ### Abel summation against `θ` for a general antitone weight -/

/-- The Abel-summation invariant for a weight `g ≥ 0` antitone on `[P+1, ∞)`: for `N ≥ P+1`,
`∑_{P<n≤N} [n prime] log n · g(n) + (cN − θ(N)) g(N) ≤ c (P+1) g(P+1) + c ∑_{P+1<n≤N} g(n)`,
`c = log 4`. -/
lemma abel_theta (g : ℕ → ℝ) (P : ℕ) (hg0 : ∀ n, P + 1 ≤ n → 0 ≤ g n)
    (hanti : ∀ n, P + 1 ≤ n → g (n + 1) ≤ g n) (N : ℕ) (hN : P + 1 ≤ N) :
    ∑ n ∈ Finset.Ioc P N, (if n.Prime then Real.log n else 0) * g n +
        (Real.log 4 * N - Ath N) * g N ≤
      Real.log 4 * (P + 1 : ℕ) * g (P + 1) + Real.log 4 * ∑ n ∈ Finset.Ioc (P + 1) N, g n := by
  have hc : 0 < Real.log 4 := Real.log_pos (by norm_num)
  induction N, hN using Nat.le_induction with
  | base =>
    rw [show Finset.Ioc P (P + 1) = {P + 1} by
        ext x; simp only [Finset.mem_Ioc, Finset.mem_singleton]; omega, Finset.sum_singleton,
      show Finset.Ioc (P + 1) (P + 1) = ∅ by simp, Finset.sum_empty, mul_zero, add_zero, Ath_succ]
    have := Ath_nonneg P
    have := hg0 (P + 1) le_rfl
    push_cast
    split_ifs <;> nlinarith
  | succ N hN ih =>
    rw [Finset.sum_Ioc_succ_top (by omega), Finset.sum_Ioc_succ_top (by omega)]
    have hA := Ath_le N
    have hg := hanti N hN
    have hg0' := hg0 (N + 1) (by omega)
    rw [Ath_succ]
    push_cast at ih ⊢
    have hmono : (Real.log 4 * N - Ath N) * g (N + 1) ≤ (Real.log 4 * N - Ath N) * g N :=
      mul_le_mul_of_nonneg_left hg (by linarith)
    split_ifs at ih ⊢ <;> nlinarith

/-- `∑_{a<n≤N} 1/n² ≤ 1/a` (`a ≥ 1`). -/
lemma sum_Ioc_inv_sq_le (a N : ℕ) (ha : 1 ≤ a) :
    ∑ n ∈ Finset.Ioc a N, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / (a : ℝ) := by
  have key : ∀ M : ℕ, ∑ n ∈ Finset.Ioc a (a + M), (1 : ℝ) / (n : ℝ) ^ 2 ≤
      1 / (a : ℝ) - 1 / ((a + M : ℕ) : ℝ) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [show a + (M + 1) = a + M + 1 by ring, Finset.sum_Ioc_succ_top (by omega)]
      have h1 : (1 : ℝ) ≤ ((a + M : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ a + M by omega)
      have hstep : (1 : ℝ) / ((a + M + 1 : ℕ) : ℝ) ^ 2 ≤
          1 / ((a + M : ℕ) : ℝ) - 1 / ((a + M + 1 : ℕ) : ℝ) := by
        push_cast at h1 ⊢
        rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
          (by positivity)]
        nlinarith
      linarith
  rcases le_or_gt N a with h | h
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]; positivity
  · have := key (N - a)
    rw [show a + (N - a) = N by omega] at this
    have : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
    linarith

/-- **Chebyshev tail:** `∑_{P<p≤N} log p/p² ≤ 2 log 4/(P+1)` (`P ≥ 1`). -/
theorem sum_prime_log_div_sq_le (P : ℕ) (hP : 1 ≤ P) (N : ℕ) :
    ∑ n ∈ Finset.Ioc P N, (if n.Prime then Real.log n else 0) * (1 / (n : ℝ) ^ 2) ≤
      2 * Real.log 4 / ((P + 1 : ℕ) : ℝ) := by
  have hc : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hP1 : (2 : ℝ) ≤ ((P + 1 : ℕ) : ℝ) := by push_cast; exact_mod_cast (by omega : 2 ≤ P + 1)
  rcases le_or_gt N P with h | h
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]; positivity
  have hinv := abel_theta (fun n => 1 / (n : ℝ) ^ 2) P (fun n _ => by positivity)
    (fun n hn => by
      have : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      push_cast
      exact one_div_le_one_div_of_le (by positivity) (by nlinarith)) N h
  have hAN : 0 ≤ (Real.log 4 * N - Ath N) * (1 / (N : ℝ) ^ 2) :=
    mul_nonneg (by linarith [Ath_le N]) (by positivity)
  have hgs := sum_Ioc_inv_sq_le (P + 1) N (by omega)
  have e : Real.log 4 * ((P + 1 : ℕ) : ℝ) * (1 / (((P + 1 : ℕ) : ℝ)) ^ 2) =
      Real.log 4 / ((P + 1 : ℕ) : ℝ) := by
    field_simp
  rw [e] at hinv
  have := mul_le_mul_of_nonneg_left hgs hc.le
  calc _ ≤ Real.log 4 / ((P + 1 : ℕ) : ℝ) + Real.log 4 * (1 / ((P + 1 : ℕ) : ℝ)) := by linarith
    _ = 2 * Real.log 4 / ((P + 1 : ℕ) : ℝ) := by ring

/-! ### `c_∅ ≤ 1.4608` -/

/-- The summand of `c_∅ − γ`. -/
def cterm (n : ℕ) : ℝ :=
  ((n : ℝ) ^ (-2 : ℤ) + (n : ℝ) ^ (-3 : ℤ)) * Real.log n / (1 - (n : ℝ) ^ (-2 : ℤ) - (n : ℝ) ^ (-3 : ℤ))

lemma cterm_den_pos {n : ℕ} (hn : 2 ≤ n) : 0 < 1 - (n : ℝ) ^ (-2 : ℤ) - (n : ℝ) ^ (-3 : ℤ) := by
  have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (n : ℝ) ^ (-2 : ℤ) ≤ 1 / 4 := by
    rw [zpow_neg, zpow_ofNat, inv_le_comm₀ (by positivity) (by norm_num)]; nlinarith
  have h3 : (n : ℝ) ^ (-3 : ℤ) ≤ 1 / 8 := by
    rw [zpow_neg, zpow_ofNat, inv_le_comm₀ (by positivity) (by norm_num)]
    have := pow_le_pow_left₀ (by norm_num) h2 3
    norm_num at this ⊢; linarith
  linarith

lemma cterm_nonneg {n : ℕ} (hn : 2 ≤ n) : 0 ≤ cterm n :=
  div_nonneg (mul_nonneg (by positivity) (Real.log_natCast_nonneg n)) (cterm_den_pos hn).le

lemma cterm_le_of_log_le {n : ℕ} (hn : 2 ≤ n) {L : ℝ} (hL : Real.log n ≤ L) :
    cterm n ≤ ((n : ℝ) ^ (-2 : ℤ) + (n : ℝ) ^ (-3 : ℤ)) * L /
      (1 - (n : ℝ) ^ (-2 : ℤ) - (n : ℝ) ^ (-3 : ℤ)) :=
  div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hL (by positivity)) (cterm_den_pos hn).le

/-- `a_p ≤ 1.011/p²` for `p ≥ 101`. -/
lemma cterm_le_tail {n : ℕ} (hn : 101 ≤ n) : cterm n ≤ 1.011 * (Real.log n * (1 / (n : ℝ) ^ 2)) := by
  have h : (101 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hden := cterm_den_pos (show 2 ≤ n by omega)
  unfold cterm
  rw [div_le_iff₀ hden]
  have hl := Real.log_natCast_nonneg n
  simp only [zpow_neg, zpow_ofNat]
  have e2 : ((n : ℝ) ^ 2)⁻¹ = 1 / (n : ℝ) ^ 2 := (one_div _).symm
  have e3 : ((n : ℝ) ^ 3)⁻¹ = 1 / (n : ℝ) * (1 / (n : ℝ) ^ 2) := by field_simp
  rw [e2, e3]
  set x := 1 / (n : ℝ) with hx
  set y := 1 / (n : ℝ) ^ 2 with hy
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 / 101 := by rw [hx]; exact one_div_le_one_div_of_le (by norm_num) h
  have hy0 : 0 ≤ y := by positivity
  have hyx : y ≤ x * (1 / 101) := by
    rw [hy, hx, show (1 : ℝ) / (n : ℝ) ^ 2 = 1 / (n : ℝ) * (1 / (n : ℝ)) by field_simp]
    exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by norm_num) h) (by positivity)
  -- `(y + x y) L ≤ 1.011 (L y) (1 − y − x y)`
  have hxy : x * y ≤ (1 / 101) * y := mul_le_mul_of_nonneg_right hx1 hy0
  have hyy : y ≤ 1 / 101 * (1 / 101) := hyx.trans (by nlinarith)
  have key : y + x * y ≤ 1.011 * y * (1 - y - x * y) := by
    have : 1 + x ≤ 1.011 * (1 - y - x * y) := by nlinarith
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left key hl]

/-- The head primes `p ≤ 100`. -/
def headC : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73,
  79, 83, 89, 97}

lemma mem_headC_of_prime {p : ℕ} (hp : p.Prime) (h : p ≤ 100) : p ∈ headC := by
  have : p ∈ (Finset.range 101).filter Nat.Prime := Finset.mem_filter.mpr ⟨by
    rw [Finset.mem_range]; omega, hp⟩
  have e : (Finset.range 101).filter Nat.Prime = headC := by decide
  rwa [e] at this

/-- The head: `∑_{p ≤ 100} a_p log p ≤ 0.8321`. -/
lemma cterm_head_le : ∑ p ∈ headC, cterm p ≤ 0.8321 := by
  have b2 := cterm_le_of_log_le (n := 2) le_rfl (show Real.log (2 : ℕ) ≤ 0.6931471808 by
    push_cast; exact log_two_le)
  have b3 := cterm_le_of_log_le (n := 3) (by norm_num) (show Real.log (3 : ℕ) ≤ 1.099 by
    push_cast; exact log_three_le)
  have b5 := cterm_le_of_log_le (n := 5) (by norm_num) (log_le_of_pow_two (k := 2) (by norm_num))
  have b7 := cterm_le_of_log_le (n := 7) (by norm_num) (log_le_of_pow_two (k := 3) (by norm_num))
  have b11 := cterm_le_of_log_le (n := 11) (by norm_num) (log_le_of_pow_two (k := 3) (by norm_num))
  have b13 := cterm_le_of_log_le (n := 13) (by norm_num) (log_le_of_pow_two (k := 4) (by norm_num))
  have b17 := cterm_le_of_log_le (n := 17) (by norm_num) (log_le_of_pow_two (k := 4) (by norm_num))
  have b19 := cterm_le_of_log_le (n := 19) (by norm_num) (log_le_of_pow_two (k := 4) (by norm_num))
  have b23 := cterm_le_of_log_le (n := 23) (by norm_num) (log_le_of_pow_two (k := 5) (by norm_num))
  have b29 := cterm_le_of_log_le (n := 29) (by norm_num) (log_le_of_pow_two (k := 5) (by norm_num))
  have b31 := cterm_le_of_log_le (n := 31) (by norm_num) (log_le_of_pow_two (k := 5) (by norm_num))
  have b37 := cterm_le_of_log_le (n := 37) (by norm_num) (log_le_of_pow_two (k := 5) (by norm_num))
  have b41 := cterm_le_of_log_le (n := 41) (by norm_num) (log_le_of_pow_two (k := 5) (by norm_num))
  have b43 := cterm_le_of_log_le (n := 43) (by norm_num) (log_le_of_pow_two (k := 5) (by norm_num))
  have b47 := cterm_le_of_log_le (n := 47) (by norm_num) (log_le_of_pow_two (k := 5) (by norm_num))
  have b53 := cterm_le_of_log_le (n := 53) (by norm_num) (log_le_of_pow_two (k := 5) (by norm_num))
  have b59 := cterm_le_of_log_le (n := 59) (by norm_num) (log_le_of_pow_two (k := 5) (by norm_num))
  have b61 := cterm_le_of_log_le (n := 61) (by norm_num) (log_le_of_pow_two (k := 5) (by norm_num))
  have b67 := cterm_le_of_log_le (n := 67) (by norm_num) (log_le_of_pow_two (k := 6) (by norm_num))
  have b71 := cterm_le_of_log_le (n := 71) (by norm_num) (log_le_of_pow_two (k := 6) (by norm_num))
  have b73 := cterm_le_of_log_le (n := 73) (by norm_num) (log_le_of_pow_two (k := 6) (by norm_num))
  have b79 := cterm_le_of_log_le (n := 79) (by norm_num) (log_le_of_pow_two (k := 6) (by norm_num))
  have b83 := cterm_le_of_log_le (n := 83) (by norm_num) (log_le_of_pow_two (k := 6) (by norm_num))
  have b89 := cterm_le_of_log_le (n := 89) (by norm_num) (log_le_of_pow_two (k := 6) (by norm_num))
  have b97 := cterm_le_of_log_le (n := 97) (by norm_num) (log_le_of_pow_two (k := 6) (by norm_num))
  have hsum : ∑ p ∈ headC, cterm p =
      cterm 2 + cterm 3 + cterm 5 + cterm 7 + cterm 11 + cterm 13 + cterm 17 + cterm 19 +
        cterm 23 + cterm 29 + cterm 31 + cterm 37 + cterm 41 + cterm 43 + cterm 47 + cterm 53 +
        cterm 59 + cterm 61 + cterm 67 + cterm 71 + cterm 73 + cterm 79 + cterm 83 + cterm 89 +
        cterm 97 := by
    simp [headC, Finset.sum_insert]; ring
  rw [hsum]
  norm_num at b2 b3 b5 b7 b11 b13 b17 b19 b23 b29 b31 b37 b41 b43
  norm_num at b47 b53 b59 b61 b67 b71 b73 b79 b83 b89 b97
  linarith

/-- The tail: for a finite set `U` of primes `> 100`, `∑_{p∈U} a_p log p ≤ 0.0278`. -/
lemma cterm_tail_le (U : Finset ℕ) (hU : ∀ p ∈ U, p.Prime ∧ 100 < p) :
    ∑ p ∈ U, cterm p ≤ 0.0278 := by
  set N := U.sup id
  have hsub : U ⊆ (Finset.Ioc 100 N).filter Nat.Prime := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨(hU p hp).2, Finset.le_sup (f := id) hp⟩, (hU p hp).1⟩
  have hT := sum_prime_log_div_sq_le 100 (by norm_num) N
  have hl4 : Real.log 4 ≤ 1.3863 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith [Real.log_two_lt_d9]
  calc ∑ p ∈ U, cterm p ≤ ∑ p ∈ U, 1.011 * (Real.log p * (1 / (p : ℝ) ^ 2)) :=
        Finset.sum_le_sum fun p hp => cterm_le_tail (hU p hp).2
    _ ≤ ∑ p ∈ (Finset.Ioc 100 N).filter Nat.Prime, 1.011 * (Real.log p * (1 / (p : ℝ) ^ 2)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ =>
          mul_nonneg (by norm_num) (mul_nonneg (Real.log_natCast_nonneg p) (by positivity))
    _ = 1.011 * ∑ n ∈ Finset.Ioc 100 N, (if n.Prime then Real.log n else 0) * (1 / (n : ℝ) ^ 2) := by
        rw [Finset.sum_filter, Finset.mul_sum]
        exact Finset.sum_congr rfl fun n _ => by split_ifs <;> simp
    _ ≤ 1.011 * (2 * Real.log 4 / ((100 + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hT (by norm_num)
    _ ≤ 0.0278 := by
        push_cast
        rw [mul_div_assoc']
        rw [div_le_iff₀ (by norm_num)]
        nlinarith

/-- The prime sum of `c_∅`: `∑_p a_p log p ≤ 0.8599`. -/
lemma tsum_cterm_le : ∑' p : Nat.Primes, cterm p ≤ 0.8599 := by
  refine Real.tsum_le_of_sum_le (fun p => cterm_nonneg p.2.two_le) fun U => ?_
  rw [← Finset.sum_filter_add_sum_filter_not U (fun p : Nat.Primes => (p : ℕ) ≤ 100)]
  have h1 : ∑ p ∈ U.filter (fun p : Nat.Primes => (p : ℕ) ≤ 100), cterm p ≤ ∑ p ∈ headC, cterm p := by
    rw [show ∑ p ∈ U.filter (fun p : Nat.Primes => (p : ℕ) ≤ 100), cterm p =
        ∑ n ∈ (U.filter (fun p : Nat.Primes => (p : ℕ) ≤ 100)).map primesEmb, cterm n by
      rw [Finset.sum_map]; rfl]
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun n hn _ => ?_
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hn
      exact mem_headC_of_prime p.2 (Finset.mem_filter.mp hp).2
    · simp only [headC, Finset.mem_insert, Finset.mem_singleton] at hn
      exact cterm_nonneg (by omega)
  have h2 : ∑ p ∈ U.filter (fun p : Nat.Primes => ¬ (p : ℕ) ≤ 100), cterm p ≤ 0.0278 := by
    rw [show ∑ p ∈ U.filter (fun p : Nat.Primes => ¬ (p : ℕ) ≤ 100), cterm p =
        ∑ n ∈ (U.filter (fun p : Nat.Primes => ¬ (p : ℕ) ≤ 100)).map primesEmb, cterm n by
      rw [Finset.sum_map]; rfl]
    refine cterm_tail_le _ fun n hn => ?_
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hn
    exact ⟨p.2, by have := (Finset.mem_filter.mp hp).2; show 100 < (p : ℕ); omega⟩
  have h3 := cterm_head_le
  linarith

lemma cEmpty_eq : cEmpty = Real.eulerMascheroniConstant + ∑' p : Nat.Primes, cterm p := rfl

/-- **`c_∅ ≤ 1.4608`** (certified; true value `1.41070…`). -/
theorem cEmpty_le : cEmpty ≤ 1.4608 := by
  rw [cEmpty_eq]; linarith [gamma_le, tsum_cterm_le]

/-- `c_∅ > 0`. -/
theorem cEmpty_pos : 0 < cEmpty := by
  rw [cEmpty_eq]
  have := Real.one_half_lt_eulerMascheroniConstant
  have : 0 ≤ ∑' p : Nat.Primes, cterm p := tsum_nonneg fun p => cterm_nonneg p.2.two_le
  linarith

/-! ### `σ₁⁻ ≤ 0.2809` -/

/-- Möbius values through `Nat.primeFactorsList` (evaluated by Mathlib's simproc). -/
lemma moebius_eval (n : ℕ) (hn : n ≠ 0) :
    μ n = if n.primeFactorsList.Nodup then (-1) ^ n.primeFactorsList.length else 0 := by
  split_ifs with h
  · rw [ArithmeticFunction.moebius_apply_of_squarefree
      ((Nat.squarefree_iff_nodup_primeFactorsList hn).2 h), ArithmeticFunction.cardFactors_apply]
  · exact ArithmeticFunction.moebius_eq_zero_of_not_squarefree
      (fun hs => h ((Nat.squarefree_iff_nodup_primeFactorsList hn).1 hs))

/-- The `r ≤ 31` with `μ(r) = −1`. -/
def headS : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 30, 31}

lemma mem_headS {r : ℕ} (hr : r < 32) (h : μ r = -1) : r ∈ headS := by
  rcases Nat.eq_zero_or_pos r with rfl | hr0
  · rw [ArithmeticFunction.map_zero] at h; norm_num at h
  interval_cases r <;> first
    | decide
    | (rw [moebius_eval _ (by norm_num)] at h; simp [Nat.primeFactorsList_ofNat] at h)

/-- The `σ₁⁻` summand. -/
def s1term (r : ℕ) : ℝ := if μ r = -1 then Real.log r / ((r : ℝ) ^ 2 * Nat.totient r) else 0

lemma s1term_le (r : ℕ) : s1term r ≤ Real.log r / ((r : ℝ) ^ 2 * Nat.totient r) := by
  unfold s1term; split_ifs
  · exact le_rfl
  · exact div_nonneg (Real.log_natCast_nonneg r) (by positivity)

lemma s1_bound {r : ℕ} (hr : 1 ≤ r) {L : ℝ} (hL : Real.log r ≤ L) (φ : ℕ) (hφ : Nat.totient r = φ) :
    Real.log r / ((r : ℝ) ^ 2 * Nat.totient r) ≤ L / ((r : ℝ) ^ 2 * φ) := by
  rw [← hφ]
  have : (0 : ℝ) < Nat.totient r := by exact_mod_cast Nat.totient_pos.mpr hr
  exact div_le_div_of_nonneg_right hL (by positivity)

/-- The head `r < 32`: `≤ 0.2637`. -/
lemma s1_head_le : ∑ r ∈ Finset.range 32, s1term r ≤ 0.2637 := by
  have h1 : ∑ r ∈ Finset.range 32, s1term r ≤
      ∑ r ∈ Finset.range 32, if r ∈ headS then Real.log r / ((r : ℝ) ^ 2 * Nat.totient r) else 0 := by
    refine Finset.sum_le_sum fun r hr => ?_
    split_ifs with h
    · exact s1term_le r
    · have : μ r ≠ -1 := fun h' => h (mem_headS (Finset.mem_range.mp hr) h')
      unfold s1term; rw [if_neg this]
  rw [Finset.sum_ite_mem, show Finset.range 32 ∩ headS = headS by decide] at h1
  refine h1.trans ?_
  have b2 := s1_bound (r := 2) (by norm_num) (show Real.log (2 : ℕ) ≤ 0.6931471808 by
    push_cast; exact log_two_le) 1 (by decide)
  have b3 := s1_bound (r := 3) (by norm_num) (show Real.log (3 : ℕ) ≤ 1.099 by
    push_cast; exact log_three_le) 2 (by decide)
  have b5 := s1_bound (r := 5) (by norm_num) (log_le_of_pow_two (k := 2) (by norm_num)) 4 (by decide)
  have b7 := s1_bound (r := 7) (by norm_num) (log_le_of_pow_two (k := 3) (by norm_num)) 6 (by decide)
  have b11 := s1_bound (r := 11) (by norm_num) (log_le_of_pow_two (k := 3) (by norm_num)) 10
    (by decide)
  have b13 := s1_bound (r := 13) (by norm_num) (log_le_of_pow_two (k := 4) (by norm_num)) 12
    (by decide)
  have b17 := s1_bound (r := 17) (by norm_num) (log_le_of_pow_two (k := 4) (by norm_num)) 16
    (by decide)
  have b19 := s1_bound (r := 19) (by norm_num) (log_le_of_pow_two (k := 4) (by norm_num)) 18
    (by decide)
  have b23 := s1_bound (r := 23) (by norm_num) (log_le_of_pow_two (k := 5) (by norm_num)) 22
    (by decide)
  have b29 := s1_bound (r := 29) (by norm_num) (log_le_of_pow_two (k := 5) (by norm_num)) 28
    (by decide)
  have b30 := s1_bound (r := 30) (by norm_num) (log_le_of_pow_two (k := 5) (by norm_num)) 8
    (by decide)
  have b31 := s1_bound (r := 31) (by norm_num) (log_le_of_pow_two (k := 5) (by norm_num)) 30
    (by decide)
  have hsum : ∑ r ∈ headS, Real.log r / ((r : ℝ) ^ 2 * Nat.totient r) =
      Real.log (2 : ℕ) / (((2 : ℕ) : ℝ) ^ 2 * Nat.totient 2) +
      Real.log (3 : ℕ) / (((3 : ℕ) : ℝ) ^ 2 * Nat.totient 3) +
      Real.log (5 : ℕ) / (((5 : ℕ) : ℝ) ^ 2 * Nat.totient 5) +
      Real.log (7 : ℕ) / (((7 : ℕ) : ℝ) ^ 2 * Nat.totient 7) +
      Real.log (11 : ℕ) / (((11 : ℕ) : ℝ) ^ 2 * Nat.totient 11) +
      Real.log (13 : ℕ) / (((13 : ℕ) : ℝ) ^ 2 * Nat.totient 13) +
      Real.log (17 : ℕ) / (((17 : ℕ) : ℝ) ^ 2 * Nat.totient 17) +
      Real.log (19 : ℕ) / (((19 : ℕ) : ℝ) ^ 2 * Nat.totient 19) +
      Real.log (23 : ℕ) / (((23 : ℕ) : ℝ) ^ 2 * Nat.totient 23) +
      Real.log (29 : ℕ) / (((29 : ℕ) : ℝ) ^ 2 * Nat.totient 29) +
      Real.log (30 : ℕ) / (((30 : ℕ) : ℝ) ^ 2 * Nat.totient 30) +
      Real.log (31 : ℕ) / (((31 : ℕ) : ℝ) ^ 2 * Nat.totient 31) := by
    simp only [headS]
    rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    ring
  rw [hsum]
  norm_num at b2 b3 b5 b7 b11 b13 b17 b19 b23 b29 b30 b31 ⊢
  linarith

/-- Dyadic block: `∑_{2^j ≤ r < 2^{j+1}} log r/(r²φ(r)) ≤ 3(j+1) log 2/4^j`. -/
lemma s1_block_le (j : ℕ) :
    ∑ r ∈ (Finset.Ico (2 ^ j) (2 ^ (j + 1)) : Finset ℕ), Real.log r / ((r : ℝ) ^ 2 * Nat.totient r) ≤
      (j + 1) * Real.log 2 * (3 / ((2 : ℝ) ^ j) ^ 2) := by
  have hge : ∀ r ∈ (Finset.Ico (2 ^ j) (2 ^ (j + 1)) : Finset ℕ), 2 ^ j ≤ r := fun r hr =>
    (Finset.mem_Ico.mp hr).1
  have h3 := sum_inv_sq_totient_le_of_ge (2 ^ j) (Nat.one_le_two_pow) _ hge
  push_cast at h3
  have hl : ∀ r ∈ (Finset.Ico (2 ^ j) (2 ^ (j + 1)) : Finset ℕ), Real.log r ≤ (j + 1) * Real.log 2 := by
    intro r hr
    have h1 : 1 ≤ r := le_trans Nat.one_le_two_pow (Finset.mem_Ico.mp hr).1
    have h2 : (r : ℝ) ≤ 2 ^ (j + 1) := by exact_mod_cast (Finset.mem_Ico.mp hr).2.le
    calc Real.log r ≤ Real.log ((2 : ℝ) ^ (j + 1)) :=
          Real.log_le_log (by exact_mod_cast h1) h2
      _ = (j + 1) * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
  have hl2 : 0 ≤ (j + 1 : ℝ) * Real.log 2 := by positivity
  calc ∑ r ∈ (Finset.Ico (2 ^ j) (2 ^ (j + 1)) : Finset ℕ), Real.log r / ((r : ℝ) ^ 2 * Nat.totient r)
      ≤ ∑ r ∈ (Finset.Ico (2 ^ j) (2 ^ (j + 1)) : Finset ℕ),
          (j + 1) * Real.log 2 * (1 / ((r : ℝ) ^ 2 * Nat.totient r)) := by
        refine Finset.sum_le_sum fun r hr => ?_
        rw [mul_one_div]
        exact div_le_div_of_nonneg_right (hl r hr) (by positivity)
    _ = (j + 1) * Real.log 2 *
          ∑ r ∈ (Finset.Ico (2 ^ j) (2 ^ (j + 1)) : Finset ℕ), 1 / ((r : ℝ) ^ 2 * Nat.totient r) := by
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 hl2

/-- `∑_{5 ≤ j < J} (j+1)/4^j = T(5) − T(J)`, `T(j) = (12j+16)/(9·4^j)`. -/
lemma sum_dyadic_eq (J : ℕ) (hJ : 5 ≤ J) :
    ∑ j ∈ Finset.Ico 5 J, ((j : ℝ) + 1) / 4 ^ j =
      (12 * 5 + 16) / (9 * 4 ^ 5) - (12 * (J : ℝ) + 16) / (9 * 4 ^ J) := by
  induction J, hJ using Nat.le_induction with
  | base => simp
  | succ J hJ ih =>
    rw [Finset.sum_Ico_succ_top hJ, ih]
    push_cast
    field_simp
    ring

/-- The tail `r ≥ 32` up to `2^J`: `≤ 0.01715`. -/
lemma s1_tail_pow_le (J : ℕ) (hJ : 5 ≤ J) :
    ∑ r ∈ (Finset.Ico 32 (2 ^ J) : Finset ℕ), Real.log r / ((r : ℝ) ^ 2 * Nat.totient r) ≤ 0.01715 := by
  have hsplit : ∀ J : ℕ, 5 ≤ J → ∑ r ∈ (Finset.Ico 32 (2 ^ J) : Finset ℕ), Real.log r / ((r : ℝ) ^ 2 * Nat.totient r) ≤
      ∑ j ∈ Finset.Ico 5 J, (j + 1) * Real.log 2 * (3 / ((2 : ℝ) ^ j) ^ 2) := by
    intro J hJ
    induction J, hJ using Nat.le_induction with
    | base => simp
    | succ J hJ ih =>
      rw [Finset.sum_Ico_succ_top hJ, ← Finset.sum_Ico_consecutive _
        (show 32 ≤ 2 ^ J from le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hJ))
        (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ J))]
      have := s1_block_le J
      linarith
  refine (hsplit J hJ).trans ?_
  have e : ∑ j ∈ Finset.Ico 5 J, ((j : ℝ) + 1) * Real.log 2 * (3 / ((2 : ℝ) ^ j) ^ 2) =
      3 * Real.log 2 * ∑ j ∈ Finset.Ico 5 J, ((j : ℝ) + 1) / 4 ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← pow_mul, show (2 : ℝ) ^ (j * 2) = 4 ^ j by rw [pow_mul']; norm_num]
    ring
  rw [e, sum_dyadic_eq J hJ]
  have h0 : 0 ≤ (12 * (J : ℝ) + 16) / (9 * 4 ^ J) := by positivity
  have hl := log_two_le
  have hl0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have : (12 * 5 + 16 : ℝ) / (9 * 4 ^ 5) - (12 * (J : ℝ) + 16) / (9 * 4 ^ J) ≤ 76 / 9216 := by
    norm_num; linarith
  have h1 : 0 ≤ (12 * 5 + 16 : ℝ) / (9 * 4 ^ 5) - (12 * (J : ℝ) + 16) / (9 * 4 ^ J) := by
    rw [← sum_dyadic_eq J hJ]; exact Finset.sum_nonneg fun j _ => by positivity
  calc 3 * Real.log 2 * ((12 * 5 + 16 : ℝ) / (9 * 4 ^ 5) - (12 * (J : ℝ) + 16) / (9 * 4 ^ J))
      ≤ 3 * 0.6931471808 * (76 / 9216) :=
        mul_le_mul (by linarith) this h1 (by norm_num)
    _ ≤ 0.01715 := by norm_num

/-- **`σ₁⁻ ≤ 0.2809`** (certified; true value `0.2631…`). -/
theorem sigma1m_le : sigma1m ≤ 0.2809 := by
  have hs : sigma1m = ∑' r, s1term r := rfl
  rw [hs]
  have hnn : ∀ r, 0 ≤ s1term r := sigma1m_term_nonneg
  refine Real.tsum_le_of_sum_range_le hnn fun n => ?_
  have hn : n ≤ 2 ^ (n + 5) :=
    le_trans (Nat.lt_two_pow_self).le (Nat.pow_le_pow_right (by norm_num) (by omega))
  calc ∑ r ∈ Finset.range n, s1term r ≤ ∑ r ∈ Finset.range (2 ^ (n + 5)), s1term r :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hn)
          fun r _ _ => hnn r
    _ = ∑ r ∈ Finset.range 32, s1term r + ∑ r ∈ Finset.Ico 32 (2 ^ (n + 5)), s1term r := by
        rw [Finset.range_eq_Ico, Finset.range_eq_Ico, Finset.sum_Ico_consecutive _ (by norm_num)
          (le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (show 5 ≤ n + 5 by omega)))]
    _ ≤ 0.2637 + 0.01715 := by
        refine add_le_add s1_head_le ?_
        exact (Finset.sum_le_sum fun r _ => s1term_le r).trans (s1_tail_pow_le (n + 5) (by omega))
    _ ≤ 0.2809 := by norm_num

end Families.Phase2.B
