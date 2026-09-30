/-
# `lem:fS` (ii)  (Lemma 6.19 and its proof)

* `lemfS_ii_conv : ∀ S n, 1 ≤ n → fS S n = ∑_{d ∣ n} gS S d` (`f_S = 1 * g_S`), via
  `ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers`.
* `lemfS_ii_euler : ∀ S, HasSum (fun d => gS S d / d) Ecal` (`∑_d g_S(d)/d = ℰ`), via Mathlib's
  `EulerProduct.eulerProduct_hasProd`: the Euler factor is `1 − p^{-2} − p^{-3}` for every `S`.
* `gloc` (local factors of `g_S`), `gS_eq_locProd`, `summable_norm_gS_div`.
-/
import Families.Phase1.B.LocalMult

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.zeta
open ArithmeticFunction Finset

namespace Families.Phase1.B

open Families

/-- The local factors of `g_S`. -/
def gloc (S : Finset ℕ) (p k : ℕ) : ℝ :=
  if p ∈ S then
    (if k = 1 then -1 / ((p : ℝ) - 1) else if k = 2 then 1 / ((p : ℝ) * (p - 1)) else 0)
  else (if k = 1 then -1 / (p : ℝ) - 1 / (p : ℝ) ^ 2 else 0)

lemma gS_eq_locProd (S : Finset ℕ) : gS S = locProd (gloc S) := rfl

lemma fS_eq_locProd (S : Finset ℕ) : fS S = locProd (fSpp S) := rfl

lemma gloc_eq_zero (S : Finset ℕ) (p : ℕ) {k : ℕ} (hk : 3 ≤ k) : gloc S p k = 0 := by
  unfold gloc
  rw [if_neg (by omega : k ≠ 1), if_neg (by omega : k ≠ 2), if_neg (by omega : k ≠ 1)]
  split_ifs <;> rfl

/-- `∑_{1≤j≤i} g_S(p^j)` for `i ≥ 2`. -/
lemma sum_gloc_ge_two (S : Finset ℕ) (p : ℕ) {i : ℕ} (hi : 2 ≤ i) :
    ∑ j ∈ Finset.Icc 1 i, gloc S p j = gloc S p 1 + gloc S p 2 := by
  induction i, hi using Nat.le_induction with
  | base => rw [show Finset.Icc 1 2 = {1, 2} by decide, Finset.sum_pair (by norm_num)]
  | succ i hi ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, gloc_eq_zero S p (k := i + 1) (by omega), add_zero]

/-- The local identity `1 + ∑_{1≤j≤i} g_S(p^j) = f_S(p^i)`. -/
lemma one_add_sum_gloc (S : Finset ℕ) {p : ℕ} (hp : p.Prime) (i : ℕ) :
    1 + ∑ j ∈ Finset.Icc 1 i, gloc S p j = if i = 0 then 1 else fSpp S p i := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  rcases Nat.lt_trichotomy i 1 with h | h | h
  · have : i = 0 := by omega
    subst this; simp
  · subst h
    simp only [Finset.Icc_self, Finset.sum_singleton, one_ne_zero, if_false]
    by_cases hS : p ∈ S
    · simp only [gloc, fSpp, hS, if_true]
      field_simp; ring
    · simp only [gloc, fSpp, hS, if_true, if_false]
      field_simp; ring
  · rw [sum_gloc_ge_two S p (by omega), if_neg (by omega)]
    have hi1 : i ≠ 1 := by omega
    by_cases hS : p ∈ S
    · simp only [gloc, fSpp, hS, hi1, if_true, if_false, OfNat.ofNat_ne_one]
      field_simp; ring
    · simp only [gloc, fSpp, hS, if_true, if_false, OfNat.ofNat_ne_one]
      field_simp; ring

/-- **`lem:fS`(ii), convolution identity:** `f_S = 1 * g_S`. -/
theorem lemfS_ii_conv : ∀ (S : Finset ℕ) (n : ℕ), 1 ≤ n → fS S n = ∑ d ∈ n.divisors, gS S d := by
  intro S n hn
  have hZ : IsMultiplicative ((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) :=
    isMultiplicative_zeta.natCast
  have hG := isMultiplicative_toAF_locProd (gloc S)
  have hF := isMultiplicative_toAF_locProd (fSpp S)
  have key : toAF (locProd (fSpp S)) =
      ((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) * toAF (locProd (gloc S)) := by
    refine (IsMultiplicative.eq_iff_eq_on_prime_powers _ hF _ (hZ.mul hG)).mpr fun p i hp => ?_
    rw [coe_zeta_mul_apply, toAF_apply _ (pow_ne_zero _ hp.ne_zero),
      Finset.sum_congr rfl (fun d hd => toAF_apply _ (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd))),
      sum_divisors_prime_pow_locProd _ hp, locProd_prime_pow' _ hp, one_add_sum_gloc S hp]
  have h := congrArg (fun F : ArithmeticFunction ℝ => F n) key
  rw [toAF_apply _ (by omega), coe_zeta_mul_apply] at h
  rw [fS_eq_locProd, h, gS_eq_locProd]
  exact Finset.sum_congr rfl fun d hd => toAF_apply _ (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd))

/-! ### `∑ g_S(d)/d = ℰ` -/

/-- `d ↦ g_S(d)/d`. -/
def gdiv (S : Finset ℕ) (d : ℕ) : ℝ := gS S d / d

lemma gdiv_zero (S : Finset ℕ) : gdiv S 0 = 0 := by simp [gdiv]

lemma gdiv_one (S : Finset ℕ) : gdiv S 1 = 1 := by simp [gdiv, gS_eq_locProd]

lemma gdiv_mul (S : Finset ℕ) {m n : ℕ} (h : m.Coprime n) : gdiv S (m * n) = gdiv S m * gdiv S n := by
  unfold gdiv
  rw [gS_eq_locProd, locProd_mul _ h, Nat.cast_mul, mul_div_mul_comm]

lemma gdiv_prime_pow (S : Finset ℕ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    gdiv S (p ^ e) = (if e = 0 then 1 else gloc S p e) / (p : ℝ) ^ e := by
  unfold gdiv
  rw [gS_eq_locProd, locProd_prime_pow' _ hp, Nat.cast_pow]

lemma gdiv_prime_pow_eq_zero (S : Finset ℕ) {p : ℕ} (hp : p.Prime) {e : ℕ} (he : 3 ≤ e) :
    gdiv S (p ^ e) = 0 := by
  rw [gdiv_prime_pow S hp, if_neg (by omega), gloc_eq_zero S p he, zero_div]

/-- A local series supported on `e ≤ 2`. -/
lemma tsum_prime_pow_three {f : ℕ → ℝ} {p : ℕ} (h : ∀ e, 3 ≤ e → f (p ^ e) = 0) :
    ∑' e : ℕ, f (p ^ e) = f 1 + f p + f (p ^ 2) := by
  rw [tsum_eq_sum (s := Finset.range 3) (fun e he => h e (by simpa using he))]
  simp [Finset.sum_range_succ]

lemma summable_prime_pow_three {f : ℕ → ℝ} {p : ℕ} (h : ∀ e, 3 ≤ e → f (p ^ e) = 0) :
    Summable fun e : ℕ => f (p ^ e) :=
  summable_of_ne_finset_zero (s := Finset.range 3) fun e he => h e (by simpa using he)

lemma gdiv_prime (S : Finset ℕ) {p : ℕ} (hp : p.Prime) : gdiv S p = gloc S p 1 / p := by
  have := gdiv_prime_pow S hp 1
  simpa using this

lemma gdiv_prime_sq (S : Finset ℕ) {p : ℕ} (hp : p.Prime) :
    gdiv S (p ^ 2) = gloc S p 2 / (p : ℝ) ^ 2 := by
  have := gdiv_prime_pow S hp 2
  simpa using this

/-- The Euler factor of `g_S(d)/d`: `1 − p⁻² − p⁻³` for every `S`. -/
lemma euler_factor_gdiv (S : Finset ℕ) {p : ℕ} (hp : p.Prime) :
    ∑' e : ℕ, gdiv S (p ^ e) = 1 - (p : ℝ) ^ (-2 : ℤ) - (p : ℝ) ^ (-3 : ℤ) := by
  rw [tsum_prime_pow_three (fun e he => gdiv_prime_pow_eq_zero S hp he), gdiv_one,
    gdiv_prime S hp, gdiv_prime_sq S hp]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  simp only [zpow_neg, zpow_ofNat]
  by_cases hS : p ∈ S
  · simp only [gloc, hS, if_true, OfNat.ofNat_ne_one, if_false]
    field_simp; ring
  · simp only [gloc, hS, if_true, if_false, OfNat.ofNat_ne_one]
    field_simp; ring

/-- The local bound `∑_e |g_S(p^e)|/p^e ≤ 1 + 3/p²`. -/
lemma euler_factor_norm_gdiv_le (S : Finset ℕ) {p : ℕ} (hp : p.Prime) :
    ‖gdiv S 1‖ + ‖gdiv S p‖ + ‖gdiv S (p ^ 2)‖ ≤ 1 + 3 * (1 / (p : ℝ) ^ 2) := by
  rw [gdiv_one, gdiv_prime S hp, gdiv_prime_sq S hp, norm_one, Real.norm_eq_abs,
    Real.norm_eq_abs]
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  by_cases hS : p ∈ S
  · simp only [gloc, hS, if_true, OfNat.ofNat_ne_one, if_false]
    have e1 : |-1 / ((p : ℝ) - 1) / p| = 1 / ((p : ℝ) * (p - 1)) := by
      rw [abs_div, abs_div, abs_neg, abs_one, abs_of_pos hp1, abs_of_pos hp0]; field_simp
    have e2 : |1 / ((p : ℝ) * (p - 1)) / (p : ℝ) ^ 2| = 1 / ((p : ℝ) * (p - 1)) / (p : ℝ) ^ 2 :=
      abs_of_nonneg (by positivity)
    rw [e1, e2]
    have h1 : 1 / ((p : ℝ) * (p - 1)) ≤ 2 * (1 / (p : ℝ) ^ 2) := by
      rw [div_le_iff₀ (by positivity)]; field_simp; nlinarith
    have h2 : 1 / ((p : ℝ) * (p - 1)) / (p : ℝ) ^ 2 ≤ 1 / (p : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      rw [div_le_one (by positivity)]; nlinarith
    linarith
  · simp only [gloc, hS, if_true, if_false, OfNat.ofNat_ne_one, zero_div, abs_zero, add_zero]
    have e1 : |(-1 / (p : ℝ) - 1 / (p : ℝ) ^ 2) / p| = (1 / (p : ℝ) + 1 / (p : ℝ) ^ 2) / p := by
      rw [show -1 / (p : ℝ) - 1 / (p : ℝ) ^ 2 = -(1 / (p : ℝ) + 1 / (p : ℝ) ^ 2) by ring, neg_div,
        abs_neg, abs_of_nonneg (by positivity)]
    rw [e1]
    have h4 : (1 / (p : ℝ) + 1 / (p : ℝ) ^ 2) / p ≤ 2 * (1 / (p : ℝ) ^ 2) := by
      rw [div_le_iff₀ hp0]; field_simp; nlinarith
    have : (0 : ℝ) ≤ 1 / (p : ℝ) ^ 2 := by positivity
    linarith

/-- `|g_S(d)|/d` is summable (Euler factors `≤ 1 + 3/p²`). -/
theorem summable_norm_gdiv (S : Finset ℕ) : Summable fun d => ‖gdiv S d‖ := by
  have h0 : ‖gdiv S 0‖ = 0 := by rw [gdiv_zero, norm_zero]
  have h1 : ‖gdiv S 1‖ = 1 := by rw [gdiv_one, norm_one]
  have hmul : ∀ {m n : ℕ}, m.Coprime n → ‖gdiv S (m * n)‖ = ‖gdiv S m‖ * ‖gdiv S n‖ :=
    fun h => by rw [gdiv_mul S h, norm_mul]
  have hzero : ∀ {p : ℕ}, p.Prime → ∀ e, 3 ≤ e → ‖gdiv S (p ^ e)‖ = 0 := fun hp e he => by
    rw [gdiv_prime_pow_eq_zero S hp he, norm_zero]
  have hC : ∀ N : ℕ, ∏ p ∈ N.primesBelow, ∑' e : ℕ, ‖gdiv S (p ^ e)‖ ≤ Real.exp 3 := by
    intro N
    have hloc : ∀ p ∈ N.primesBelow, ∑' e : ℕ, ‖gdiv S (p ^ e)‖ ≤ 1 + 3 * (1 / (p : ℝ) ^ 2) := by
      intro p hpN
      have hp := Nat.prime_of_mem_primesBelow hpN
      calc ∑' e : ℕ, ‖gdiv S (p ^ e)‖ = ‖gdiv S 1‖ + ‖gdiv S p‖ + ‖gdiv S (p ^ 2)‖ :=
            tsum_prime_pow_three (f := fun d => ‖gdiv S d‖) (hzero hp)
        _ ≤ _ := euler_factor_norm_gdiv_le S hp
    calc ∏ p ∈ N.primesBelow, ∑' e : ℕ, ‖gdiv S (p ^ e)‖
        ≤ ∏ p ∈ N.primesBelow, (1 + 3 * (1 / (p : ℝ) ^ 2)) :=
          Finset.prod_le_prod (fun p _ => tsum_nonneg fun _ => norm_nonneg _) hloc
      _ ≤ Real.exp (∑ p ∈ N.primesBelow, 3 * (1 / (p : ℝ) ^ 2)) :=
          prod_one_add_le_exp _ _ fun p _ => by positivity
      _ ≤ Real.exp 3 := by
          rw [← Finset.mul_sum]
          exact Real.exp_le_exp.mpr (by linarith [sum_primesBelow_inv_sq_le N])
  exact (summable_of_euler_bound (h := fun d => ‖gdiv S d‖) h0 h1 hmul (fun _ => norm_nonneg _)
    (fun hp => summable_prime_pow_three (f := fun d => ‖gdiv S d‖) (hzero hp)) hC).1

/-- **`lem:fS`(ii), Euler product:** `∑_d g_S(d)/d = ℰ` for every `S`. -/
theorem lemfS_ii_euler : ∀ S : Finset ℕ, HasSum (fun d : ℕ => gS S d / d) Ecal := by
  intro S
  have hs := summable_norm_gdiv S
  have hP := EulerProduct.eulerProduct_hasProd (f := gdiv S) (gdiv_one S) (fun h => gdiv_mul S h)
    hs (gdiv_zero S)
  have hE : Ecal = ∑' n, gdiv S n := by
    rw [← hP.tprod_eq]
    unfold Ecal
    exact tprod_congr fun p => (euler_factor_gdiv S p.2).symm
  have : HasSum (gdiv S) Ecal := hE ▸ hs.of_norm.hasSum
  exact this

end Families.Phase1.B
