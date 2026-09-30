/-
# Multiplicative functions given by local factors

`locProd F n = ∏_{p ∣ n} F p (v_p(n))` (the form of `fS`, `gS` in `Families.LemmaC`).

* `locProd_mul` (multiplicative on coprime arguments), `locProd_prime_pow`, `locProd_one`.
* `toAF`, `isMultiplicative_toAF_locProd`: as a Mathlib `ArithmeticFunction` (value `0` at `0`).
* `summable_of_euler_bound`: an Euler-product summability criterion — if `h ≥ 0` is multiplicative,
  `h 0 = 0`, `h 1 = 1`, each `∑_e h(p^e)` converges and `∏_{p<N} ∑_e h(p^e) ≤ C` for all `N`, then
  `h` is summable with `∑ h ≤ C` (via Mathlib's `summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum`).
* `prod_one_add_le_exp`, `sum_primesBelow_inv_sq_le`.
-/
import Families.LemmaC

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.zeta
open ArithmeticFunction Finset

namespace Families.Phase1.B

open Families

/-- The multiplicative function with local factors `F p k` at `p^k`. -/
def locProd (F : ℕ → ℕ → ℝ) (n : ℕ) : ℝ := ∏ p ∈ n.primeFactors, F p (n.factorization p)

@[simp] lemma locProd_zero (F : ℕ → ℕ → ℝ) : locProd F 0 = 1 := by simp [locProd]

@[simp] lemma locProd_one (F : ℕ → ℕ → ℝ) : locProd F 1 = 1 := by simp [locProd]

lemma not_dvd_of_mem_primeFactors_of_coprime {m n p : ℕ} (h : m.Coprime n)
    (hp : p ∈ m.primeFactors) : ¬ p ∣ n := by
  intro hpn
  have hpm := Nat.dvd_of_mem_primeFactors hp
  have := Nat.dvd_gcd hpm hpn
  rw [h] at this
  exact (Nat.prime_of_mem_primeFactors hp).one_lt.ne' (Nat.dvd_one.mp this)

lemma locProd_mul (F : ℕ → ℕ → ℝ) {m n : ℕ} (h : m.Coprime n) :
    locProd F (m * n) = locProd F m * locProd F n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Nat.coprime_zero_left] at h; subst h; simp
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.coprime_zero_right] at h; subst h; simp
  unfold locProd
  rw [Nat.primeFactors_mul hm.ne' hn.ne', Finset.prod_union h.disjoint_primeFactors]
  congr 1
  · refine Finset.prod_congr rfl fun p hp => ?_
    rw [Nat.factorization_mul hm.ne' hn.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (not_dvd_of_mem_primeFactors_of_coprime h hp), add_zero]
  · refine Finset.prod_congr rfl fun p hp => ?_
    rw [Nat.factorization_mul hm.ne' hn.ne', Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd
        (not_dvd_of_mem_primeFactors_of_coprime h.symm hp), zero_add]

lemma locProd_prime_pow (F : ℕ → ℕ → ℝ) {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    locProd F (p ^ k) = F p k := by
  unfold locProd
  rw [Nat.primeFactors_prime_pow hk hp, Finset.prod_singleton, hp.factorization_pow,
    Finsupp.single_eq_same]

lemma locProd_prime_pow' (F : ℕ → ℕ → ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    locProd F (p ^ k) = if k = 0 then 1 else F p k := by
  split_ifs with hk
  · rw [hk, pow_zero, locProd_one]
  · exact locProd_prime_pow F hp hk

/-! ### As an arithmetic function -/

/-- `f` as an arithmetic function (with the value `0` at `0`). -/
def toAF (f : ℕ → ℝ) : ArithmeticFunction ℝ := ⟨fun n => if n = 0 then 0 else f n, by simp⟩

lemma toAF_apply (f : ℕ → ℝ) {n : ℕ} (hn : n ≠ 0) : toAF f n = f n := by
  simp [toAF, hn]

lemma isMultiplicative_toAF (f : ℕ → ℝ) (h1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.Coprime n → f (m * n) = f m * f n) :
    (toAF f).IsMultiplicative := by
  refine ⟨by rw [toAF_apply f one_ne_zero, h1], fun {m n} hmn => ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [Nat.coprime_zero_left] at hmn; subst hmn; simp [toAF, h1]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Nat.coprime_zero_right] at hmn; subst hmn; simp [toAF, h1]
  rw [toAF_apply f (by positivity), toAF_apply f hm.ne', toAF_apply f hn.ne',
    hmul hm.ne' hn.ne' hmn]

lemma isMultiplicative_toAF_locProd (F : ℕ → ℕ → ℝ) : (toAF (locProd F)).IsMultiplicative :=
  isMultiplicative_toAF _ (locProd_one F) fun _ _ h => locProd_mul F h

/-- Divisor sums of `locProd`: `∑_{d ∣ p^i} locProd F d = 1 + ∑_{1 ≤ j ≤ i} F p j`. -/
lemma sum_divisors_prime_pow_locProd (F : ℕ → ℕ → ℝ) {p : ℕ} (hp : p.Prime) (i : ℕ) :
    ∑ d ∈ (p ^ i).divisors, locProd F d = 1 + ∑ j ∈ Finset.Icc 1 i, F p j := by
  rw [Nat.divisors_prime_pow hp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega),
      locProd_prime_pow F hp (by omega)]
    ring

/-! ### An Euler-product summability criterion -/

/-- If `h ≥ 0` is multiplicative with `h 0 = 0`, `h 1 = 1`, every local series converges and the
partial Euler products `∏_{p<N} ∑_e h(p^e)` are `≤ C`, then `h` is summable and `∑ h ≤ C`. -/
theorem summable_of_euler_bound {h : ℕ → ℝ} (h0 : h 0 = 0) (h1 : h 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → h (m * n) = h m * h n) (hnn : ∀ n, 0 ≤ h n)
    (hloc : ∀ {p : ℕ}, p.Prime → Summable fun e : ℕ => h (p ^ e)) {C : ℝ}
    (hC : ∀ N : ℕ, ∏ p ∈ N.primesBelow, ∑' e : ℕ, h (p ^ e) ≤ C) :
    Summable h ∧ ∑' n, h n ≤ C := by
  have hsum : ∀ N : ℕ, ∑ i ∈ Finset.range N, h i ≤ C := by
    intro N
    have hS := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum h1
      (fun hmn => hmul hmn) (fun hp => by
        simpa [Real.norm_of_nonneg (hnn _)] using hloc hp) N).2
    have hS' : HasSum (Set.indicator N.smoothNumbers h) _ := hasSum_subtype_iff_indicator.mp hS
    have hle := sum_le_hasSum (Finset.range N) (fun i _ => Set.indicator_nonneg
      (fun j _ => hnn j) i) hS'
    refine le_trans (le_of_eq ?_) (hle.trans (hC N))
    refine Finset.sum_congr rfl fun i hi => ?_
    by_cases hi0 : i = 0
    · subst hi0
      rw [h0]
      by_cases h0m : (0 : ℕ) ∈ N.smoothNumbers
      · rw [Set.indicator_of_mem h0m, h0]
      · rw [Set.indicator_of_notMem h0m]
    · have : i ∈ N.smoothNumbers := by
        rw [Nat.mem_smoothNumbers']
        intro p hp hpi
        exact lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hi0) hpi)
          (Finset.mem_range.mp hi)
      rw [Set.indicator_of_mem this]
  exact ⟨summable_of_sum_range_le hnn hsum, Real.tsum_le_of_sum_range_le hnn hsum⟩

/-- `∏ (1 + a_i) ≤ exp(∑ a_i)` for `a_i ≥ 0`. -/
lemma prod_one_add_le_exp {ι : Type*} (s : Finset ι) (a : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i) :
    ∏ i ∈ s, (1 + a i) ≤ Real.exp (∑ i ∈ s, a i) := by
  rw [Real.exp_sum]
  refine Finset.prod_le_prod (fun i hi => by linarith [ha i hi]) fun i _ => ?_
  linarith [Real.add_one_le_exp (a i)]

/-- `∑_{p < N} 1/p² ≤ 1`. -/
lemma sum_primesBelow_inv_sq_le (N : ℕ) : ∑ p ∈ N.primesBelow, (1 : ℝ) / (p : ℝ) ^ 2 ≤ 1 := by
  calc ∑ p ∈ N.primesBelow, (1 : ℝ) / (p : ℝ) ^ 2
      ≤ ∑ i ∈ Finset.Ioo 1 N, ((i : ℝ) ^ 2)⁻¹ := by
        simp_rw [one_div]
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun _ _ _ => by positivity
        have hpp := Nat.prime_of_mem_primesBelow hp
        rw [Finset.mem_Ioo]
        exact ⟨hpp.one_lt, Nat.lt_of_mem_primesBelow hp⟩
    _ ≤ 2 / ((1 : ℕ) + 1 : ℝ) := sum_Ioo_inv_sq_le 1 N
    _ = 1 := by norm_num

end Families.Phase1.B
