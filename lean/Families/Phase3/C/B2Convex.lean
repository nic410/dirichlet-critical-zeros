/-
Step (1) of `lem:B2` — reduction to blocks by convexity.

For `1 ≤ n ≤ Y`: `∑_{j ∈ blocks} ψ_j(n) = 1`, so
`b_n = ∑_j ψ_j(n) Υ(n) n^{−1/2} (Λ(n) − Λ_{R_j}(n))` (`Λ_0 = 0`), and by Cauchy–Schwarz
`b_n² h(log n) ≤ ∑_j F_j(n) (Λ(n) − Λ_{R_j}(n))²` (`bVec_sq_le`).
-/
import Families.Phase3.C.B2BlockEst

noncomputable section

open scoped ContDiff Nat ArithmeticFunction.Moebius
open Set ArithmeticFunction MeasureTheory

namespace Families.Phase3.C

open Families

variable (P : PrimeSetup)

lemma psi_zero_of_not_block {Q y : ℝ} (hy : y ≤ ⌊P.Y Q⌋₊) {j : ℕ} (hj : j ∉ P.blocks Q) :
    P.ψj j y = 0 := by
  by_contra hne
  have hs := (P.ψj_supp j y hne).1
  unfold PrimeSetup.blocks at hj
  rw [Finset.mem_range, not_lt] at hj
  set m := ⌊P.Y Q⌋₊
  have hm : (m : ℝ) < 2 ^ (Nat.log 2 m + 1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num) m
  have h2 : (2 : ℝ) ^ (Nat.log 2 m + 2) ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
  have h3 : (2 : ℝ) ^ (Nat.log 2 m + 2) = 2 * 2 ^ (Nat.log 2 m + 1) := by ring
  linarith

lemma summable_psi {y : ℝ} (hy : 1 ≤ y) : Summable (fun j => P.ψj j y) := by
  by_contra h
  have := P.ψj_sum y hy
  rw [tsum_eq_zero_of_not_summable h] at this
  norm_num at this

/-- `∑_{j ∈ blocks} ψ_j(y) = 1` for `1 ≤ y ≤ ⌊Y⌋`. -/
lemma sum_psi_blocks {Q y : ℝ} (hy1 : 1 ≤ y) (hy : y ≤ ⌊P.Y Q⌋₊) :
    ∑ j ∈ P.blocks Q, P.ψj j y = 1 := by
  rw [← P.ψj_sum y hy1, tsum_eq_sum]
  intro j hj
  exact psi_zero_of_not_block P hy hj

/-- `∑_{j ∈ blocks} ψ_j(y) ≤ 1` for `y ≥ 1`. -/
lemma sum_psi_blocks_le {Q y : ℝ} (hy1 : 1 ≤ y) : ∑ j ∈ P.blocks Q, P.ψj j y ≤ 1 := by
  rw [← P.ψj_sum y hy1]
  exact Summable.sum_le_tsum _ (fun j _ => P.ψj_nonneg j y) (summable_psi P hy1)

lemma LamR_zero (n : ℕ) : PrimeSetup.LamR 0 n = 0 := by simp [PrimeSetup.LamR]

/-- `b_n = ∑_{j ∈ blocks} ψ_j(n) Υ(n) n^{−1/2} (Λ(n) − Λ_{R_j}(n))` for `1 ≤ n ≤ Y`. -/
lemma bVec_eq_blocks {Q T : ℝ} {n : ℕ} (hn : n ∈ P.range Q) :
    P.bVec Q T n = ∑ j ∈ P.blocks Q,
      P.ψj j n * (P.Ups Q n / Real.sqrt n * (Λ n - PrimeSetup.LamR (P.Rj Q T j) n)) := by
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnY : (n : ℝ) ≤ ⌊P.Y Q⌋₊ := by exact_mod_cast (Finset.mem_Icc.mp hn).2
  have hsum := sum_psi_blocks P (Q := Q) (y := n) (by exact_mod_cast hn1) hnY
  unfold PrimeSetup.bVec PrimeSetup.aVec PrimeSetup.aSharp
  have ha : Λ n / Real.sqrt n * P.Ups Q n =
      ∑ j ∈ P.blocks Q, P.ψj j n * (P.Ups Q n / Real.sqrt n * Λ n) := by
    rw [← Finset.sum_mul, hsum]; ring
  have hs : ∑ j ∈ (P.blocks Q).filter (fun j => 1 ≤ P.Rj Q T j),
      P.ψj j n * P.Ups Q n / Real.sqrt n * PrimeSetup.LamR (P.Rj Q T j) n =
      ∑ j ∈ P.blocks Q, P.ψj j n * (P.Ups Q n / Real.sqrt n * PrimeSetup.LamR (P.Rj Q T j) n) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · ring
    · have : P.Rj Q T j = 0 := by omega
      rw [this, LamR_zero]; ring
  rw [ha, hs, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Step (1) of `lem:B2`** (convexity). -/
theorem bVec_sq_le {Q T : ℝ} {h : ℝ → ℝ} (hh : ∀ y, 0 ≤ h y) {n : ℕ} (hn : n ∈ P.range Q) :
    P.bVec Q T n ^ 2 * h (Real.log n) ≤
      ∑ j ∈ P.blocks Q, Fh P Q h j n * (Λ n - PrimeSetup.LamR (P.Rj Q T j) n) ^ 2 := by
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnY : (n : ℝ) ≤ ⌊P.Y Q⌋₊ := by exact_mod_cast (Finset.mem_Icc.mp hn).2
  have hsum := sum_psi_blocks P (Q := Q) (y := n) (by exact_mod_cast hn1) hnY
  rw [bVec_eq_blocks P hn]
  set v : ℕ → ℝ := fun j => P.Ups Q n / Real.sqrt n * (Λ n - PrimeSetup.LamR (P.Rj Q T j) n)
  -- Cauchy–Schwarz with weights `ψ_j(n)`, `∑ ψ_j(n) = 1`
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
  calc (∑ j ∈ P.blocks Q, P.ψj j n * v j) ^ 2 * h (Real.log n)
      ≤ (∑ j ∈ P.blocks Q, P.ψj j n * v j ^ 2) * h (Real.log n) :=
        mul_le_mul_of_nonneg_right hCS (hh _)
    _ = ∑ j ∈ P.blocks Q, Fh P Q h j n * (Λ n - PrimeSetup.LamR (P.Rj Q T j) n) ^ 2 := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Fh_nat P Q h j n hn1]
        simp only [v]
        have hs : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt hn0.le
        have hs0 : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
        field_simp
        rw [hs]; ring

end Families.Phase3.C
