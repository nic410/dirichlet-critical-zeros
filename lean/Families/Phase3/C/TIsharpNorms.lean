/-
The norm bounds used in `prop:TIsharp` (`eqB:norms`, **no PNT**), the prime-power
bound of Step 4(c), and bounds for the diagonal `𝒦(n,n)`.

* `sum_sq_aVec_le`: `‖a‖² ≤ log Y (log Y + 6)` (Mertens' upper bound `∑_{n≤N} Λ(n)/n ≤ log N + log 4 + 4`
  from `∑_{n≤N} log n = ∑_d Λ(d)⌊N/d⌋` and Chebyshev's `ψ(N) ≤ (log 4 + 4)N`);
* `sum_sq_aSharp_le`: `‖a♯‖² ≤ 4(1 + log Q)(1 + log Y) + C` (convexity with the weights `ψ_j`, then
  step (4) of `lem:B2`, i.e. `∑ F Λ_R² = G(R) ∑ F + O(·)`, with `h ≡ 1`; `G(R_j) ≤ 4(1 + log Q)`);
* `sum_sq_aPP_le`: `∑_{n > x, n not Q-rough} a_n² ≤ 2√Y (log Y)³/x` for `x ≥ Q` (such `n` with
  `a_n ≠ 0` are proper prime powers; `card_pp_le`);
* `𝒦_diag_re_nonneg`, `𝒦_diag_re_le`: `0 ≤ 𝒦(n,n) ≤ 2π|J| b L + C` (`lem:M1`, `g ≤ bL`).
-/
import Families.Phase3.C.TIsharpBasic
import Families.Phase3.C.B2

noncomputable section

open scoped BigOperators ContDiff Nat ArithmeticFunction.Moebius
open Set MeasureTheory ArithmeticFunction

namespace Families.Phase3.C

open Families

/-! ### Mertens' first theorem (upper bound) -/

lemma sum_log_Ioc_le (N : ℕ) : ∑ n ∈ Finset.Ioc 0 N, Real.log n ≤ N * Real.log N := by
  calc ∑ n ∈ Finset.Ioc 0 N, Real.log n ≤ ∑ n ∈ Finset.Ioc 0 N, Real.log N := by
        refine Finset.sum_le_sum fun n hn => ?_
        have := Finset.mem_Ioc.mp hn
        exact Real.log_le_log (by exact_mod_cast this.1) (by exact_mod_cast this.2)
    _ = N * Real.log N := by rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]; simp

lemma sum_log_eq_sum_vonMangoldt (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, Real.log n = ∑ d ∈ Finset.Ioc 0 N, Λ d * ((N / d : ℕ) : ℝ) := by
  have h := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum (R := ℝ) Λ N
  rw [ArithmeticFunction.vonMangoldt_mul_zeta] at h
  simpa only [ArithmeticFunction.log_apply] using h

/-- `∑_{d ≤ N} Λ(d)/d ≤ log N + log 4 + 4`. -/
lemma sum_vonMangoldt_div_le (N : ℕ) :
    ∑ d ∈ Finset.Ioc 0 N, Λ d / d ≤ Real.log N + (Real.log 4 + 4) := by
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · subst h0
    simp only [Finset.Ioc_self, Finset.sum_empty, Nat.cast_zero, Real.log_zero, zero_add]
    have : 0 < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hkey : ∀ d ∈ Finset.Ioc 0 N, Λ d * (N : ℝ) / d ≤ Λ d * ((N / d : ℕ) : ℝ) + Λ d := by
    intro d hd
    have hd0 : 0 < d := (Finset.mem_Ioc.mp hd).1
    have hdr : (0 : ℝ) < d := by exact_mod_cast hd0
    have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := d)
    have hdiv : (N : ℝ) / d ≤ ((N / d : ℕ) : ℝ) + 1 := by
      rw [div_le_iff₀ hdr]
      have h1 := Nat.div_add_mod N d
      have h2 := Nat.mod_lt N hd0
      have e : (N : ℝ) = d * ((N / d : ℕ) : ℝ) + ((N % d : ℕ) : ℝ) := by exact_mod_cast h1.symm
      have h3 : ((N % d : ℕ) : ℝ) < d := by exact_mod_cast h2
      nlinarith
    calc Λ d * (N : ℝ) / d = Λ d * ((N : ℝ) / d) := by ring
      _ ≤ Λ d * (((N / d : ℕ) : ℝ) + 1) := mul_le_mul_of_nonneg_left hdiv hΛ
      _ = _ := by ring
  have hsum := Finset.sum_le_sum hkey
  rw [Finset.sum_add_distrib, ← sum_log_eq_sum_vonMangoldt] at hsum
  have hψ : ∑ d ∈ Finset.Ioc 0 N, Λ d ≤ (Real.log 4 + 4) * N := by
    have := Chebyshev.psi_le_const_mul_self (x := (N : ℝ)) hN0.le
    unfold Chebyshev.psi at this
    rwa [Nat.floor_natCast] at this
  have hlog := sum_log_Ioc_le N
  have e2 : ∑ d ∈ Finset.Ioc 0 N, Λ d * (N : ℝ) / d = N * ∑ d ∈ Finset.Ioc 0 N, Λ d / d := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun d _ => by ring
  rw [e2] at hsum
  have : (N : ℝ) * ∑ d ∈ Finset.Ioc 0 N, Λ d / d ≤ N * (Real.log N + (Real.log 4 + 4)) := by
    nlinarith
  exact le_of_mul_le_mul_left this hN0

lemma log_four_lt_two : Real.log 4 < 2 := by
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [this]; linarith [log_two_bounds.2]

lemma Icc_one_eq_Ioc (N : ℕ) : Finset.Icc 1 N = Finset.Ioc 0 N := by
  ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega

variable (P : PrimeSetup)

/-! ### `‖a‖² ≪ L²` -/

lemma one_le_Y {Q : ℝ} (hQ : 1 < Q) : 1 ≤ P.Y Q := by
  have h := log_Y P (Q := Q)
  have hL := L_pos' P hQ
  have : 0 ≤ Real.log (P.Y Q) := by rw [h]; have := P.ε₁_pos; positivity
  have hY := Y_pos' P Q
  by_contra hc
  have := Real.log_neg hY (not_le.mp hc)
  linarith

lemma aVec_sq_le (Q : ℝ) (n : ℕ) (hn : 1 ≤ n) : P.aVec Q n ^ 2 ≤ Real.log n * (Λ n / n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  have hΛl : Λ n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
  have hU := P.Υ₀_range (Real.log n / P.L Q)
  unfold PrimeSetup.aVec PrimeSetup.Ups
  have hs : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hn0.le
  have hs0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  rw [div_mul_eq_mul_div, div_pow, hs, mul_pow]
  rw [div_le_iff₀ hn0]
  have hU2 : P.Υ₀ (Real.log n / P.L Q) ^ 2 ≤ 1 := by nlinarith [hU.1, hU.2]
  have e : Real.log n * (Λ n / n) * n = Real.log n * Λ n := by field_simp
  rw [e]
  calc Λ n ^ 2 * P.Υ₀ (Real.log n / P.L Q) ^ 2 ≤ Λ n ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hU2 (sq_nonneg _)
    _ ≤ Real.log n * Λ n := by nlinarith

/-- **`eqB:norms`, first half**: `‖a‖² ≤ log Y (log Y + 6)`. -/
theorem sum_sq_aVec_le {Q : ℝ} (hQ : 1 < Q) :
    ∑ n ∈ P.range Q, P.aVec Q n ^ 2 ≤ Real.log (P.Y Q) * (Real.log (P.Y Q) + 6) := by
  set N : ℕ := ⌊P.Y Q⌋₊ with hN
  have hY1 := one_le_Y P hQ
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hY1)
  have hlogN : Real.log N ≤ Real.log (P.Y Q) :=
    Real.log_le_log (by exact_mod_cast hN1) (Nat.floor_le (by linarith))
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  have hterm : ∀ n ∈ P.range Q, P.aVec Q n ^ 2 ≤ Real.log N * (Λ n / n) := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
    refine (aVec_sq_le P Q n hn1).trans ?_
    have : 0 ≤ Λ n / n := div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
    exact mul_le_mul_of_nonneg_right
      (Real.log_le_log (by exact_mod_cast hn1) (by exact_mod_cast hnN)) this
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hS : ∑ n ∈ P.range Q, Λ n / n ≤ Real.log N + (Real.log 4 + 4) := by
    unfold PrimeSetup.range; rw [← hN, Icc_one_eq_Ioc]; exact sum_vonMangoldt_div_le N
  have h4 := log_four_lt_two
  have hS0 : 0 ≤ ∑ n ∈ P.range Q, Λ n / n :=
    Finset.sum_nonneg fun n _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
  calc Real.log N * ∑ n ∈ P.range Q, Λ n / n ≤ Real.log N * (Real.log N + 6) :=
        mul_le_mul_of_nonneg_left (by linarith) hlogN0
    _ ≤ Real.log (P.Y Q) * (Real.log (P.Y Q) + 6) := by
        apply mul_le_mul hlogN (by linarith) (by linarith) (by linarith)

/-! ### `‖a♯‖² ≪ (1 + ℓ)(1 + L)` -/

lemma aSharp_eq_blocks {Q T : ℝ} (n : ℕ) :
    P.aSharp Q T n = ∑ j ∈ P.blocks Q,
      P.ψj j n * (P.Ups Q n / Real.sqrt n * PrimeSetup.LamR (P.Rj Q T j) n) := by
  unfold PrimeSetup.aSharp
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · ring
  · have : P.Rj Q T j = 0 := by omega
    rw [this, LamR_zero]; ring

lemma aSharp_sq_le {Q T : ℝ} {n : ℕ} (hn : n ∈ P.range Q) :
    P.aSharp Q T n ^ 2 ≤
      ∑ j ∈ P.blocks Q, Fh P Q (fun _ => 1) j n * PrimeSetup.LamR (P.Rj Q T j) n ^ 2 := by
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnY : (n : ℝ) ≤ ⌊P.Y Q⌋₊ := by exact_mod_cast (Finset.mem_Icc.mp hn).2
  have hsum := sum_psi_blocks P (Q := Q) (y := n) (by exact_mod_cast hn1) hnY
  rw [aSharp_eq_blocks P n]
  set v : ℕ → ℝ := fun j => P.Ups Q n / Real.sqrt n * PrimeSetup.LamR (P.Rj Q T j) n
  have hCS : (∑ j ∈ P.blocks Q, P.ψj j n * v j) ^ 2 ≤ ∑ j ∈ P.blocks Q, P.ψj j n * v j ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq (P.blocks Q) (fun j => Real.sqrt (P.ψj j n))
      (fun j => Real.sqrt (P.ψj j n) * v j)
    have e1 : ∀ j, Real.sqrt (P.ψj j n) * (Real.sqrt (P.ψj j n) * v j) = P.ψj j n * v j := by
      intro j; rw [← mul_assoc, Real.mul_self_sqrt (P.ψj_nonneg j n)]
    have e2 : ∀ j, Real.sqrt (P.ψj j n) ^ 2 = P.ψj j n := fun j => Real.sq_sqrt (P.ψj_nonneg j n)
    have e3 : ∀ j, (Real.sqrt (P.ψj j n) * v j) ^ 2 = P.ψj j n * v j ^ 2 := by
      intro j; rw [mul_pow, e2]
    simp only [e1, e2, e3] at this
    rw [hsum, one_mul] at this
    exact this
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  refine hCS.trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fh_nat P Q _ j n hn1]
  simp only [v]
  have hs : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hn0.le
  have hs0 : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
  field_simp
  rw [hs]; ring

lemma sum_Fh1_le {Q : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    ∑ j ∈ P.blocks Q, Fh P Q (fun _ => 1) j n ≤ 1 / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  simp_rw [Fh_nat P Q _ _ n hn]
  have hU := P.Υ₀_range (Real.log n / P.L Q)
  have hU2 : P.Ups Q n ^ 2 ≤ 1 := by unfold PrimeSetup.Ups; nlinarith [hU.1, hU.2]
  have hψ := sum_psi_blocks_le P (Q := Q) (y := n) (by exact_mod_cast hn)
  have : ∑ j ∈ P.blocks Q, P.ψj j n * P.Ups Q n ^ 2 * 1 / n =
      (∑ j ∈ P.blocks Q, P.ψj j n) * (P.Ups Q n ^ 2 / n) := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [this]
  have h0 : 0 ≤ ∑ j ∈ P.blocks Q, P.ψj j n := Finset.sum_nonneg fun j _ => P.ψj_nonneg j n
  calc (∑ j ∈ P.blocks Q, P.ψj j n) * (P.Ups Q n ^ 2 / n) ≤ 1 * (1 / n) := by
        apply mul_le_mul hψ (div_le_div_of_nonneg_right hU2 hn0.le) (by positivity) zero_le_one
    _ = 1 / n := one_mul _

lemma Fh1_nonneg (Q : ℝ) (j : ℕ) (y : ℝ) : 0 ≤ Fh P Q (fun _ => 1) j y :=
  Fh_nonneg P Q (fun _ => zero_le_one) j y

/-- Step (4) of `lem:B2` with `h ≡ 1`, per block. -/
lemma block_LamR_sq_le :
    ∃ Ce : ℝ, 0 ≤ Ce ∧ ∀ Q T : ℝ, 4 < Q → 1 ≤ T → 2 * P.Y Q ≤ Q ^ 2 → 1 ≤ P.L Q →
      ∀ j ∈ P.blocks Q,
        ∑ n ∈ P.range Q, Fh P Q (fun _ => 1) j n * PrimeSetup.LamR (P.Rj Q T j) n ^ 2 ≤
          4 * (1 + Real.log Q) * ∑ n ∈ P.range Q, Fh P Q (fun _ => 1) j n + Ce / ((j : ℝ) + 1) ^ 2 := by
  set K : ℕ := ⌈1 / P.ε₃⌉₊ + 1 with hKdef
  have hK1 : 1 ≤ K := by omega
  have hKε : 1 ≤ K * P.ε₃ := by
    have h1 : 1 / P.ε₃ ≤ ⌈1 / P.ε₃⌉₊ := Nat.le_ceil _
    have h2 : (⌈1 / P.ε₃⌉₊ : ℝ) ≤ K := by rw [hKdef]; push_cast; linarith
    have := P.ε₃_pos
    rw [div_le_iff₀ this] at h1
    nlinarith
  obtain ⟨CF, hCF0, hCF⟩ := Fh_deriv_bound P K hK1 (fun _ => 1)
  obtain ⟨Cde, hCde0, hCde⟩ := exp_decay 0 (by linarith [log_two_bounds.1] : 0 < Real.log 2)
  refine ⟨(K + 3) * K ^ K * CF * Cde * 1, by positivity, ?_⟩
  intro Q T hQ hT hY2 hL j hj
  have hQ1 : 1 < Q := by linarith
  have hsum0 : 0 ≤ ∑ n ∈ P.range Q, Fh P Q (fun _ => 1) j n :=
    Finset.sum_nonneg fun n _ => Fh1_nonneg P Q j n
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ1.le
  have hCe : 0 ≤ (K + 3) * K ^ K * CF * Cde * 1 / ((j : ℝ) + 1) ^ 2 := by positivity
  rcases le_or_gt j 2 with hj2 | hj3
  · -- `R_j = 0`
    have hN4 : (2 : ℝ) ^ j ≤ 4 := by
      calc (2 : ℝ) ^ j ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) hj2
        _ = 4 := by norm_num
    have hR0 : P.Rj Q T j = 0 := by
      unfold PrimeSetup.Rj
      rw [Nat.floor_eq_zero, div_lt_one (by positivity)]
      have h1 : ((2 : ℝ) ^ j) ^ (1 - P.ε₃) ≤ 2 ^ j := by
        have := Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num) : (1 : ℝ) ≤ 2 ^ j)
          (show 1 - P.ε₃ ≤ 1 by linarith [P.ε₃_pos])
        simpa using this
      nlinarith
    rw [hR0]
    simp only [LamR_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      Finset.sum_const_zero]
    positivity
  · have hj3' : 3 ≤ j := hj3
    have hNQ := two_pow_le_sq_of_block P (by linarith) hY2 hj
    obtain ⟨hRle, -, hG⟩ := Rj_block_facts P hQ1 hT hj3' hNQ
    have hFK : ∀ y, |iteratedDeriv K (Fh P Q (fun _ => 1) j) y| ≤
        CF * 1 / 2 ^ j * (2 * K / 2 ^ j) ^ K := by
      intro y
      have := hCF Q hL (fun _ => 1) 1 contDiff_const (fun _ => zero_le_one) (fun _ => le_rfl)
        (fun i y => by
          rw [iteratedDeriv_const]; split_ifs <;> norm_num) j K le_rfl y
      rwa [Real.norm_eq_abs] at this
    have hpe := piece_e hK1 (Fh_contDiff P Q contDiff_const j K) hCF0 zero_le_one hj3'
      P.ε₃_pos hKε hFK (Fh_supp P Q _ j) (P.range Q) (by
        intro n hn
        have hs := Fh_supp P Q _ j n hn
        have hnY : (n : ℝ) ≤ P.Y Q := by
          by_contra hc
          exact hn (Fh_eq_zero_of_gt P hQ1 _ j (not_le.mp hc))
        simp only [PrimeSetup.range, Finset.mem_Icc]
        refine ⟨?_, Nat.le_floor hnY⟩
        have : (1 : ℝ) / 2 ≤ n := le_trans (by
          have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
          linarith) hs.1
        have : (0 : ℝ) < n := by linarith
        exact_mod_cast this) hRle hCde
    have h1 := (abs_le.mp hpe).2
    have h2 : Gsum (P.Rj Q T j) * ∑ n ∈ P.range Q, Fh P Q (fun _ => 1) j n ≤
        4 * (1 + Real.log Q) * ∑ n ∈ P.range Q, Fh P Q (fun _ => 1) j n :=
      mul_le_mul_of_nonneg_right hG hsum0
    have h3 : (K + 3) * K ^ K * CF * Cde * 1 / ((j : ℝ) + 1) ^ 2 =
        ((K : ℝ) + 3) * (K : ℝ) ^ K * CF * Cde * 1 / ((j : ℝ) + 1) ^ 2 := rfl
    linarith

/-- **`eqB:norms`, second half** (no PNT): `‖a♯‖² ≤ 4(1 + log Q)(1 + log Y) + C`. -/
theorem sum_sq_aSharp_le :
    ∃ C Q₀ : ℝ, 0 ≤ C ∧ ∀ Q : ℝ, Q₀ ≤ Q → ∀ T : ℝ, 1 ≤ T →
      ∑ n ∈ P.range Q, P.aSharp Q T n ^ 2 ≤ 4 * (1 + Real.log Q) * (1 + Real.log (P.Y Q)) + C := by
  obtain ⟨Ce, hCe0, hCe⟩ := block_LamR_sq_le P
  refine ⟨2 * Ce, max (max 5 (Real.exp (1 / P.lam))) (2 ^ (1 / P.ε₁)), by positivity, ?_⟩
  intro Q hQ T hT
  have hQ5 : 5 ≤ Q := le_trans (le_max_left _ _) (le_of_max_le_left hQ)
  have hQL : Real.exp (1 / P.lam) ≤ Q := le_trans (le_max_right _ _) (le_of_max_le_left hQ)
  have hQε : 2 ^ (1 / P.ε₁) ≤ Q := le_of_max_le_right hQ
  have hQ1 : 1 < Q := by linarith
  have hL := one_le_L P hQL
  have hQε' : 2 ≤ Q ^ P.ε₁ := by
    have := Real.rpow_le_rpow (by positivity) hQε P.ε₁_pos.le
    rwa [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ P.ε₁_pos.ne', Real.rpow_one]
      at this
  have hY2 := two_Y_le P hQ1.le hQε'
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ1.le
  -- convexity
  have hconv : ∑ n ∈ P.range Q, P.aSharp Q T n ^ 2 ≤
      ∑ j ∈ P.blocks Q, ∑ n ∈ P.range Q,
        Fh P Q (fun _ => 1) j n * PrimeSetup.LamR (P.Rj Q T j) n ^ 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun n hn => aSharp_sq_le P hn
  refine hconv.trans ?_
  refine (Finset.sum_le_sum fun j hj => hCe Q T (by linarith) hT hY2 hL j hj).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
  have hharm : ∑ n ∈ P.range Q, ∑ j ∈ P.blocks Q, Fh P Q (fun _ => 1) j n ≤
      1 + Real.log (P.Y Q) := by
    refine (Finset.sum_le_sum fun n hn => sum_Fh1_le P (Q := Q)
      (Finset.mem_Icc.mp hn).1).trans ?_
    have hY1 := one_le_Y P hQ1
    have hN1 : 1 ≤ ⌊P.Y Q⌋₊ := Nat.le_floor (by exact_mod_cast hY1)
    have h1 := harmonic_le_one_add_log ⌊P.Y Q⌋₊
    rw [harmonic_eq_sum_Icc] at h1
    push_cast at h1
    have h2 : Real.log ⌊P.Y Q⌋₊ ≤ Real.log (P.Y Q) :=
      Real.log_le_log (by exact_mod_cast hN1) (Nat.floor_le (by linarith))
    simp only [one_div]
    linarith
  have hsq : ∑ j ∈ P.blocks Q, Ce / ((j : ℝ) + 1) ^ 2 ≤ 2 * Ce := by
    have := sum_inv_sq_le_two (Nat.log 2 ⌊P.Y Q⌋₊ + 2)
    unfold PrimeSetup.blocks
    calc ∑ j ∈ Finset.range (Nat.log 2 ⌊P.Y Q⌋₊ + 2), Ce / ((j : ℝ) + 1) ^ 2
        = Ce * ∑ j ∈ Finset.range (Nat.log 2 ⌊P.Y Q⌋₊ + 2), 1 / ((j : ℝ) + 1) ^ 2 := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ Ce * 2 := mul_le_mul_of_nonneg_left this hCe0
      _ = 2 * Ce := by ring
  have h4 : 0 ≤ 4 * (1 + Real.log Q) := by positivity
  nlinarith

/-! ### Prime powers (Step 4(c)) -/

open Classical in
/-- `a` on the `Q`-rough integers. -/
def aR (Q : ℝ) : ℕ → ℝ := fun n => if IsRough Q (n : ℤ) then P.aVec Q n else 0

open Classical in
/-- `a` on the non-`Q`-rough integers. -/
def aNR (Q : ℝ) : ℕ → ℝ := fun n => if IsRough Q (n : ℤ) then 0 else P.aVec Q n

open Classical in
/-- `a` on the non-`Q`-rough integers `n > x`. -/
def aPP (Q x : ℝ) : ℕ → ℝ := fun n => if x < n ∧ ¬ IsRough Q (n : ℤ) then P.aVec Q n else 0

lemma aR_add_aNR (Q : ℝ) : aR P Q + aNR P Q = P.aVec Q := by
  funext n; simp only [aR, aNR, Pi.add_apply]; split_ifs <;> simp

lemma aVec_ne_zero {Q : ℝ} {n : ℕ} (h : P.aVec Q n ≠ 0) : Λ n ≠ 0 := by
  intro h0; apply h; simp [PrimeSetup.aVec, h0]

/-- A non-`Q`-rough `n > Q` with `Λ(n) ≠ 0` is not prime. -/
lemma not_prime_of_not_rough {Q : ℝ} {n : ℕ} (hn : Q < n) (h1 : 1 ≤ n)
    (hr : ¬ IsRough Q (n : ℤ)) : ¬ n.Prime := by
  intro hp
  apply hr
  refine ⟨by exact_mod_cast h1, fun p hpp hdvd => ?_⟩
  have hdvd' : p ∣ n := by exact_mod_cast hdvd
  have : p = n := ((Nat.Prime.eq_one_or_self_of_dvd hp p hdvd').resolve_left hpp.one_lt.ne')
  rw [this]; exact hn

lemma aPP_sq_le {Q x : ℝ} {n : ℕ} (hn : n ∈ P.range Q) (hx : 0 < x) :
    aPP P Q x n ^ 2 ≤ Real.log (P.Y Q) ^ 2 / x := by
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnN : n ≤ ⌊P.Y Q⌋₊ := (Finset.mem_Icc.mp hn).2
  unfold aPP
  split_ifs with h
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have h1 := aVec_sq_le P Q n hn1
    have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have hΛl : Λ n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
    have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
    have hlogY : Real.log n ≤ Real.log (P.Y Q) :=
      Real.log_le_log hn0 ((Nat.cast_le.mpr hnN).trans (Nat.floor_le (P.Y_nonneg Q)))
    have h2 : Real.log n * (Λ n / n) ≤ Real.log (P.Y Q) * (Real.log (P.Y Q) / x) := by
      apply mul_le_mul hlogY _ (by positivity) (hlog0.trans hlogY)
      calc Λ n / n ≤ Real.log n / n := div_le_div_of_nonneg_right hΛl hn0.le
        _ ≤ Real.log (P.Y Q) / n := div_le_div_of_nonneg_right hlogY hn0.le
        _ ≤ Real.log (P.Y Q) / x := div_le_div_of_nonneg_left (hlog0.trans hlogY) hx h.1.le
    calc P.aVec Q n ^ 2 ≤ _ := h1
      _ ≤ _ := h2
      _ = Real.log (P.Y Q) ^ 2 / x := by ring
  · have : 0 ≤ Real.log (P.Y Q) ^ 2 / x := by positivity
    simpa using this

lemma natLog_le_two_log {N : ℕ} (hN : 1 ≤ N) : (Nat.log 2 N : ℝ) ≤ 2 * Real.log N := by
  have h1 : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 (by omega)
  have h2 : ((2 : ℝ) ^ Nat.log 2 N) ≤ N := by exact_mod_cast h1
  have h3 : Real.log ((2 : ℝ) ^ Nat.log 2 N) ≤ Real.log N := Real.log_le_log (by positivity) h2
  rw [Real.log_pow] at h3
  have := log_two_bounds.1
  have h0 : (0 : ℝ) ≤ Nat.log 2 N := Nat.cast_nonneg _
  nlinarith

/-- **Step 4(c)**: `∑_{n > x, n not Q-rough} a_n² ≤ 2√Y (log Y)³/x` for `x ≥ Q`. -/
theorem sum_sq_aPP_le {Q x : ℝ} (hQ : 1 < Q) (hx : Q ≤ x) :
    ∑ n ∈ P.range Q, aPP P Q x n ^ 2 ≤ 2 * Real.sqrt (P.Y Q) * Real.log (P.Y Q) ^ 3 / x := by
  have hx0 : 0 < x := by linarith
  set N : ℕ := ⌊P.Y Q⌋₊ with hN
  have hY1 := one_le_Y P hQ
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hY1)
  set PP := (Finset.Icc 1 N).filter (fun n => Λ n ≠ 0 ∧ ¬ n.Prime) with hPP
  have hsupp : ∀ n ∈ P.range Q, n ∉ PP → aPP P Q x n ^ 2 = 0 := by
    intro n hn hnPP
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    unfold aPP
    split_ifs with h
    · by_cases ha : P.aVec Q n = 0
      · simp [ha]
      · exfalso; apply hnPP
        rw [hPP, Finset.mem_filter]
        exact ⟨hn, aVec_ne_zero P ha, not_prime_of_not_rough (lt_of_le_of_lt hx h.1) hn1 h.2⟩
    · simp
  have hsub : PP ⊆ P.range Q := Finset.filter_subset _ _
  rw [← Finset.sum_subset hsub hsupp]
  have hcard : (PP.card : ℝ) ≤ (Nat.sqrt N * Nat.log 2 N : ℕ) := by exact_mod_cast card_pp_le N
  have hlogN : Real.log N ≤ Real.log (P.Y Q) :=
    Real.log_le_log (by exact_mod_cast hN1) (Nat.floor_le (by linarith))
  have hlogY0 : 0 ≤ Real.log (P.Y Q) := Real.log_nonneg hY1
  have hsq : (Nat.sqrt N : ℝ) ≤ Real.sqrt (P.Y Q) :=
    Real.nat_sqrt_le_real_sqrt.trans (Real.sqrt_le_sqrt (Nat.floor_le (by linarith)))
  have hlg : (Nat.log 2 N : ℝ) ≤ 2 * Real.log (P.Y Q) :=
    (natLog_le_two_log hN1).trans (by linarith)
  calc ∑ n ∈ PP, aPP P Q x n ^ 2 ≤ ∑ n ∈ PP, Real.log (P.Y Q) ^ 2 / x :=
        Finset.sum_le_sum fun n hn => aPP_sq_le P (hsub hn) hx0
    _ = PP.card * (Real.log (P.Y Q) ^ 2 / x) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Nat.sqrt N * Nat.log 2 N : ℕ) * (Real.log (P.Y Q) ^ 2 / x) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ (Real.sqrt (P.Y Q) * (2 * Real.log (P.Y Q))) * (Real.log (P.Y Q) ^ 2 / x) := by
        push_cast
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul hsq hlg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt (P.Y Q) * Real.log (P.Y Q) ^ 3 / x := by ring

/-! ### The diagonal `𝒦(n,n)` -/

lemma 𝒦_diag_re_nonneg {Q : ℝ} (hQ : 1 < Q) (T : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ (P.𝒦 Q T n n).re := by
  rw [P.𝒦_diag_re hQ T n hn]
  exact integral_nonneg fun u => mul_nonneg (P.g_nonneg Q u) (sq_nonneg _)

lemma Jlen_nonneg {T : ℝ} (hT : 0 ≤ T) : 0 ≤ P.Jlen T := by
  unfold PrimeSetup.Jlen; have := P.θ_lt; nlinarith

/-- `𝒦(n,n) ≤ 2π|J| b L + C` (`lem:M1`, diagonal, and `g ≤ bL`). -/
lemma 𝒦_diag_re_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ Q T : ℝ, 1 < Q → 0 < T → ∀ n : ℕ, 1 ≤ n →
    (P.𝒦 Q T n n).re ≤ 2 * Real.pi * P.Jlen T * (P.bInt * P.L Q) + C := by
  obtain ⟨C, hC⟩ := lemM1_diag P
  refine ⟨|C|, abs_nonneg _, fun Q T hQ hT n hn => ?_⟩
  have h1 := hC Q T hQ hT n hn
  have h2 : (P.𝒦 Q T n n).re - 2 * Real.pi * P.Jlen T * P.g Q (Real.log n) ≤ C := by
    have := Complex.re_le_norm (P.𝒦 Q T n n - ((2 * Real.pi * P.Jlen T * P.g Q (Real.log n) : ℝ) : ℂ))
    rw [Complex.sub_re, Complex.ofReal_re] at this
    have e : ((2 * Real.pi * P.Jlen T * P.g Q (Real.log n) : ℝ) : ℂ) =
        2 * Real.pi * P.Jlen T * P.g Q (Real.log n) := by push_cast; ring
    rw [e] at this
    linarith
  have hJ := Jlen_nonneg P hT.le
  have hg := P.g_le hQ (Real.log n)
  have h3 : 2 * Real.pi * P.Jlen T * P.g Q (Real.log n) ≤ 2 * Real.pi * P.Jlen T * (P.bInt * P.L Q) :=
    mul_le_mul_of_nonneg_left hg (by positivity)
  have := le_abs_self C
  linarith

end Families.Phase3.C
