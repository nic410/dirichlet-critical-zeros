/-
# The constant `B` of `lem:fS`(iii)

`B = ∏_p (1 + p^{−1/2}/(p−1) + p^{−1}/(p(p−1)))` (`Families.Bconst`).

* `bfac`, `one_le_bfac`, `multipliable_bfac` (so `Bconst` is a genuine convergent product),
  `prod_bfac_le_Bconst` (finite partial products `≤ B`).
* `gabs S d = |g_S(d)| d^{−1/2}`: multiplicative, Euler factor `≤ bfac p`; `summable_gabs`,
  `tsum_gabs_le_Bconst : ∑_d |g_S(d)| d^{−1/2} ≤ B` (the input of `|E_S| ≤ 2B e^{−s/2}`).
-/
import Families.Phase1.B.FSii

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius
open ArithmeticFunction Finset

namespace Families.Phase1.B

open Families

/-- The Euler factor of `B`. -/
def bfac (p : ℕ) : ℝ :=
  1 + (p : ℝ) ^ (-(1 / 2 : ℝ)) / ((p : ℝ) - 1) + (p : ℝ)⁻¹ / ((p : ℝ) * ((p : ℝ) - 1))

lemma Bconst_eq : Bconst = ∏' p : Nat.Primes, bfac p := rfl

lemma bfac_sub_one_nonneg {p : ℕ} (hp : p.Prime) : 0 ≤ bfac p - 1 := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  unfold bfac
  have : 0 ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) / ((p : ℝ) - 1) :=
    div_nonneg (Real.rpow_nonneg (by linarith) _) (by linarith)
  have : 0 ≤ (p : ℝ)⁻¹ / ((p : ℝ) * ((p : ℝ) - 1)) :=
    div_nonneg (inv_nonneg.mpr (by linarith)) (mul_nonneg (by linarith) (by linarith))
  linarith

lemma one_le_bfac {p : ℕ} (hp : p.Prime) : 1 ≤ bfac p := by
  linarith [bfac_sub_one_nonneg hp]

/-- `bfac p − 1 ≤ 4 p^{−3/2}` for `p ≥ 2`. -/
lemma bfac_sub_one_le {p : ℕ} (hp : 2 ≤ p) :
    bfac p - 1 ≤ 4 * (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have hhalf : (p : ℝ) - 1 ≥ (p : ℝ) / 2 := by linarith
  have e32 : (p : ℝ) ^ (-(3 / 2 : ℝ)) = (p : ℝ) ^ (-(1 / 2 : ℝ)) / p := by
    rw [show -(3 / 2 : ℝ) = -(1 / 2) + (-1) by norm_num, Real.rpow_add hp0, Real.rpow_neg_one]
    ring
  have hs : 0 < (p : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hp0 _
  -- `p^{-1/2} ≥ p^{-1}` (`p ≥ 1`)
  have hs1 : (p : ℝ)⁻¹ ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  unfold bfac
  rw [e32]
  have t1 : (p : ℝ) ^ (-(1 / 2 : ℝ)) / ((p : ℝ) - 1) ≤ 2 * ((p : ℝ) ^ (-(1 / 2 : ℝ)) / p) := by
    rw [div_le_iff₀ hp1]; field_simp; nlinarith
  have t2 : (p : ℝ)⁻¹ / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 2 * ((p : ℝ) ^ (-(1 / 2 : ℝ)) / p) := by
    rw [div_le_iff₀ (by positivity)]
    have : (p : ℝ)⁻¹ ≤ 2 * ((p : ℝ) ^ (-(1 / 2 : ℝ)) / p) * (p * (p - 1)) := by
      have e : 2 * ((p : ℝ) ^ (-(1 / 2 : ℝ)) / p) * (p * (p - 1)) =
          2 * (p - 1) * (p : ℝ) ^ (-(1 / 2 : ℝ)) := by field_simp
      rw [e]; nlinarith
    exact this
  linarith

lemma summable_bfac_sub_one : Summable fun p : Nat.Primes => bfac p - 1 := by
  have hs : Summable fun n : ℕ => 4 * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
    have := (Real.summable_nat_rpow_inv.mpr (show (1 : ℝ) < 3 / 2 by norm_num)).mul_left 4
    refine this.congr fun n => ?_
    rw [Real.rpow_neg (Nat.cast_nonneg _)]
  exact Summable.of_nonneg_of_le (fun p => bfac_sub_one_nonneg p.2)
    (fun p => bfac_sub_one_le p.2.two_le) (hs.comp_injective Nat.Primes.coe_nat_injective)

lemma multipliable_bfac : Multipliable fun p : Nat.Primes => bfac p := by
  have := Real.multipliable_one_add_of_summable summable_bfac_sub_one
  simpa using this

lemma summable_log_bfac : Summable fun p : Nat.Primes => Real.log (bfac p) := by
  have := Real.summable_log_one_add_of_summable summable_bfac_sub_one
  simpa using this

/-- Finite partial products of `B` are `≤ B`. -/
lemma prod_bfac_le_Bconst (T : Finset Nat.Primes) : ∏ p ∈ T, bfac p ≤ Bconst := by
  have hpos : ∀ p : Nat.Primes, 0 < bfac p := fun p => lt_of_lt_of_le one_pos (one_le_bfac p.2)
  rw [Bconst_eq, ← Real.rexp_tsum_eq_tprod hpos summable_log_bfac, ← Real.exp_log
    (Finset.prod_pos fun p _ => hpos p), Real.log_prod (fun p _ => (hpos p).ne')]
  refine Real.exp_le_exp.mpr (summable_log_bfac.sum_le_tsum T fun p _ => ?_)
  exact Real.log_nonneg (one_le_bfac p.2)

lemma prod_primesBelow_bfac_le (N : ℕ) : ∏ p ∈ N.primesBelow, bfac p ≤ Bconst := by
  calc ∏ p ∈ N.primesBelow, bfac p = ∏ p ∈ (N.primesBelow).subtype Nat.Prime, bfac (p : ℕ) :=
        (Finset.prod_subtype_of_mem bfac fun p hp => Nat.prime_of_mem_primesBelow hp).symm
    _ ≤ Bconst := prod_bfac_le_Bconst ((N.primesBelow).subtype Nat.Prime)

lemma one_le_Bconst : 1 ≤ Bconst := by
  have := prod_bfac_le_Bconst ∅
  simpa using this

/-! ### `∑_d |g_S(d)| d^{−1/2} ≤ B` -/

/-- `|g_S(d)| d^{−1/2}`. -/
def gabs (S : Finset ℕ) (d : ℕ) : ℝ := |gS S d| * (d : ℝ) ^ (-(1 / 2 : ℝ))

lemma gabs_nonneg (S : Finset ℕ) (d : ℕ) : 0 ≤ gabs S d :=
  mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

lemma gabs_zero (S : Finset ℕ) : gabs S 0 = 0 := by
  simp [gabs]

lemma gabs_one (S : Finset ℕ) : gabs S 1 = 1 := by
  simp [gabs, gS_eq_locProd]

lemma gabs_mul (S : Finset ℕ) {m n : ℕ} (h : m.Coprime n) :
    gabs S (m * n) = gabs S m * gabs S n := by
  unfold gabs
  rw [gS_eq_locProd, locProd_mul _ h, abs_mul, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  ring

lemma gabs_prime_pow_eq_zero (S : Finset ℕ) {p : ℕ} (hp : p.Prime) {e : ℕ} (he : 3 ≤ e) :
    gabs S (p ^ e) = 0 := by
  unfold gabs
  rw [gS_eq_locProd, locProd_prime_pow _ hp (by omega), gloc_eq_zero S p he, abs_zero, zero_mul]

lemma gabs_euler_factor_le (S : Finset ℕ) {p : ℕ} (hp : p.Prime) :
    gabs S 1 + gabs S p + gabs S (p ^ 2) ≤ bfac p := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  have e1 : gabs S p = |gloc S p 1| * (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
    unfold gabs; rw [gS_eq_locProd, show (p : ℕ) = p ^ 1 by ring, locProd_prime_pow _ hp one_ne_zero,
      pow_one]
  have e2 : gabs S (p ^ 2) = |gloc S p 2| * (p : ℝ)⁻¹ := by
    unfold gabs
    rw [gS_eq_locProd, locProd_prime_pow _ hp two_ne_zero, Nat.cast_pow,
      show ((p : ℝ) ^ 2) ^ (-(1 / 2 : ℝ)) = (p : ℝ)⁻¹ by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; norm_num; exact Real.rpow_neg_one _]
  rw [gabs_one, e1, e2]
  unfold bfac
  have hs : 0 ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hp0.le _
  -- `|g(p)| ≤ 1/(p−1)`, `|g(p²)| ≤ 1/(p(p−1))`
  have g1 : |gloc S p 1| ≤ 1 / ((p : ℝ) - 1) := by
    by_cases hS : p ∈ S
    · simp only [gloc, hS, if_true]
      rw [abs_div, abs_neg, abs_one, abs_of_pos hp1]
    · simp only [gloc, hS, if_true, if_false]
      rw [show -1 / (p : ℝ) - 1 / (p : ℝ) ^ 2 = -(1 / (p : ℝ) + 1 / (p : ℝ) ^ 2) by ring, abs_neg,
        abs_of_pos (by positivity), div_add_div _ _ hp0.ne' (by positivity),
        div_le_div_iff₀ (by positivity) hp1]
      nlinarith
  have g2 : |gloc S p 2| ≤ 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    by_cases hS : p ∈ S
    · simp only [gloc, hS, if_true, OfNat.ofNat_ne_one, if_false]
      rw [abs_of_pos (by positivity)]
    · simp only [gloc, hS, if_false, OfNat.ofNat_ne_one, abs_zero]
      positivity
  have t1 := mul_le_mul_of_nonneg_right g1 hs
  have t2 := mul_le_mul_of_nonneg_right g2 (inv_nonneg.mpr hp0.le)
  have e3 : 1 / ((p : ℝ) - 1) * (p : ℝ) ^ (-(1 / 2 : ℝ)) =
      (p : ℝ) ^ (-(1 / 2 : ℝ)) / ((p : ℝ) - 1) := by ring
  have e4 : 1 / ((p : ℝ) * ((p : ℝ) - 1)) * (p : ℝ)⁻¹ =
      (p : ℝ)⁻¹ / ((p : ℝ) * ((p : ℝ) - 1)) := by ring
  linarith

theorem summable_gabs_and_le (S : Finset ℕ) :
    Summable (gabs S) ∧ ∑' d, gabs S d ≤ Bconst := by
  have hzero : ∀ {p : ℕ}, p.Prime → ∀ e, 3 ≤ e → gabs S (p ^ e) = 0 :=
    fun hp e he => gabs_prime_pow_eq_zero S hp he
  refine summable_of_euler_bound (h := gabs S) (gabs_zero S) (gabs_one S)
    (fun h => gabs_mul S h) (gabs_nonneg S)
    (fun hp => summable_prime_pow_three (f := gabs S) (hzero hp)) fun N => ?_
  refine le_trans (Finset.prod_le_prod (fun p _ => tsum_nonneg fun _ => gabs_nonneg S _)
    fun p hp => ?_) (prod_primesBelow_bfac_le N)
  have hpp := Nat.prime_of_mem_primesBelow hp
  calc ∑' e : ℕ, gabs S (p ^ e) = gabs S 1 + gabs S p + gabs S (p ^ 2) :=
        tsum_prime_pow_three (f := gabs S) (hzero hpp)
    _ ≤ bfac p := gabs_euler_factor_le S hpp

lemma summable_gabs (S : Finset ℕ) : Summable (gabs S) := (summable_gabs_and_le S).1

lemma tsum_gabs_le_Bconst (S : Finset ℕ) : ∑' d, gabs S d ≤ Bconst := (summable_gabs_and_le S).2

end Families.Phase1.B
