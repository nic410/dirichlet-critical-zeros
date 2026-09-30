/-
The per-block estimate of `lem:B2` (steps (2)–(5)).

For a block `j ≥ 3` (`N = 2^j ≤ Q²`), with `F = F_j`, `R = R_j`,
`Σ_j = ∑_n F(n)(Λ(n) − Λ_R(n))²` and `M_j = ∫ F(y)(log y − G(R)) dy`:
`Σ_j − M_j = (∑_p F(p)log²p − ∫F log) + PP₁ − 2G(R)(∑_p F(p) log p − ∫F) − 2PP₂
            + (∑ F Λ_R² − G(R)∑F) + G(R)(∑F − ∫F)` (`block_decomp`),
and each piece is `≪ h_max (1 + log Q)/(j+1)²` (`block_estimate`).
-/
import Families.Phase3.C.B2Step4

noncomputable section

open scoped ContDiff Nat ArithmeticFunction.Moebius
open Set ArithmeticFunction MeasureTheory

namespace Families.Phase3.C

open Families

/-- The prime indicator weight `c(n) = 1_{prime} log n`. -/
def cPrime (n : ℕ) : ℝ := if n.Prime then Real.log n else 0

/-- `Λ(n)` on proper prime powers only. -/
def LamPP (n : ℕ) : ℝ := if n.Prime then 0 else Λ n

lemma vonMangoldt_split (n : ℕ) : Λ n = cPrime n + LamPP n := by
  unfold cPrime LamPP
  split_ifs with hp
  · rw [vonMangoldt_apply_prime hp]; ring
  · ring

/-- The algebraic decomposition of `Σ_j` (steps (2)–(4)). -/
lemma block_decomp (S : Finset ℕ) (F L : ℕ → ℝ) (g : ℝ)
    (hL : ∀ n ∈ S, n.Prime → F n ≠ 0 → L n = g) :
    ∑ n ∈ S, F n * (Λ n - L n) ^ 2 =
      (∑ n ∈ S, (F n * Real.log n) * cPrime n + ∑ n ∈ S, F n * (LamPP n * Λ n)) -
        2 * (g * ∑ n ∈ S, F n * cPrime n + ∑ n ∈ S, F n * (LamPP n * L n)) +
        ∑ n ∈ S, F n * L n ^ 2 := by
  have hpt : ∀ n ∈ S, F n * (Λ n - L n) ^ 2 =
      ((F n * Real.log n) * cPrime n + F n * (LamPP n * Λ n)) -
        2 * (g * (F n * cPrime n) + F n * (LamPP n * L n)) + F n * L n ^ 2 := by
    intro n hn
    by_cases hp : n.Prime
    · have hc : cPrime n = Real.log n := if_pos hp
      have hpp : LamPP n = 0 := if_pos hp
      have hΛ : Λ n = Real.log n := vonMangoldt_apply_prime hp
      rw [hc, hpp, hΛ]
      by_cases hF : F n = 0
      · rw [hF]; ring
      · rw [hL n hn hp hF]; ring
    · have hc : cPrime n = 0 := if_neg hp
      have hpp : LamPP n = Λ n := if_neg hp
      rw [hc, hpp]; ring
  rw [Finset.sum_congr rfl hpt]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

/-! ### Prime powers -/

/-- `|∑_n F(n) Λ_{pp}(n) g(n)| ≤ #pp(M) · B · log M · G₀` when `|F| ≤ B`, `F = 0` off `[1, M]`,
and `|g| ≤ G₀` on `[1, M]`. -/
lemma pp_sum_le (S : Finset ℕ) {F g : ℕ → ℝ} {M : ℕ} {B G₀ : ℝ} (hB : ∀ n, |F n| ≤ B)
    (hF : ∀ n, M < n → F n = 0) (hg : ∀ n, 1 ≤ n → n ≤ M → |g n| ≤ G₀) (_hG₀ : 0 ≤ G₀) :
    |∑ n ∈ S, F n * (LamPP n * g n)| ≤
      ((Finset.Icc 1 M).filter (fun n => Λ n ≠ 0 ∧ ¬ n.Prime)).card * (B * Real.log M * G₀) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  set PP := (Finset.Icc 1 M).filter (fun n => Λ n ≠ 0 ∧ ¬ n.Prime) with hPP
  have hzero : ∀ n ∈ S, n ∉ PP → F n * (LamPP n * g n) = 0 := by
    intro n _ hn
    by_contra hne
    apply hn
    have hF0 : F n ≠ 0 := left_ne_zero_of_mul hne
    have hL0 : LamPP n ≠ 0 := left_ne_zero_of_mul (right_ne_zero_of_mul hne)
    have hnp : ¬ n.Prime := by intro hp; exact hL0 (if_pos hp)
    have hΛ : Λ n ≠ 0 := by intro h; exact hL0 (by simp [LamPP, hnp, h])
    have hn0 : n ≠ 0 := by intro h; subst h; exact hΛ (by simp)
    have hnM : n ≤ M := by by_contra h; exact hF0 (hF n (not_le.mp h))
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hn0, hnM⟩, hΛ, hnp⟩
  rw [← Finset.sum_filter_of_ne (p := (· ∈ PP)) (fun n hn hne => by
    by_contra h; exact hne (hzero n hn h))]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ n ∈ S.filter (· ∈ PP), |F n * (LamPP n * g n)|
      ≤ ∑ n ∈ PP, |F n * (LamPP n * g n)| :=
        Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => (Finset.mem_filter.mp hn).2)
          (fun _ _ _ => abs_nonneg _)
    _ ≤ ∑ n ∈ PP, B * Real.log M * G₀ := by
        refine Finset.sum_le_sum fun n hn => ?_
        obtain ⟨hnI, -, hnp⟩ := Finset.mem_filter.mp hn
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hnI).1
        have hnM : n ≤ M := (Finset.mem_Icc.mp hnI).2
        have hΛ := ArithmeticFunction.vonMangoldt_le_log (n := n)
        have hΛ0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
        have hlog : Real.log n ≤ Real.log M :=
          Real.log_le_log (by exact_mod_cast hn1) (by exact_mod_cast hnM)
        rw [abs_mul, abs_mul, show LamPP n = Λ n from if_neg hnp, abs_of_nonneg hΛ0]
        calc |F n| * (Λ n * |g n|) ≤ B * (Real.log M * G₀) :=
              mul_le_mul (hB n) (mul_le_mul (hΛ.trans hlog) (hg n hn1 hnM) (abs_nonneg _)
                ((Real.log_nonneg (by exact_mod_cast hn1)).trans hlog)) (by positivity) hB0
          _ = B * Real.log M * G₀ := by ring
    _ = PP.card * (B * Real.log M * G₀) := by rw [Finset.sum_const, nsmul_eq_mul]

/-! ### Decay in `j` -/

lemma exp_decay (m : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, ((j : ℝ) + 1) ^ m * Real.exp (-(c * j)) ≤ C / ((j : ℝ) + 1) ^ 2 := by
  obtain ⟨C, hC1, hC⟩ := pow_le_exp_mul (m + 2) hc
  refine ⟨C, by linarith, fun j => ?_⟩
  have hj := hC j (Nat.cast_nonneg j)
  have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  rw [le_div_iff₀ (by positivity), Real.exp_neg]
  have hexp : 0 < Real.exp (c * j) := Real.exp_pos _
  rw [pow_add] at hj
  calc ((j : ℝ) + 1) ^ m * (Real.exp (c * j))⁻¹ * ((j : ℝ) + 1) ^ 2
      = ((j : ℝ) + 1) ^ m * ((j : ℝ) + 1) ^ 2 / Real.exp (c * j) := by field_simp
    _ ≤ C * Real.exp (c * j) / Real.exp (c * j) := by gcongr
    _ = C := by field_simp

lemma two_pow_eq_exp (j : ℕ) : (2 : ℝ) ^ j = Real.exp (Real.log 2 * j) := by
  rw [← Real.exp_log (by positivity : (0 : ℝ) < 2 ^ j), Real.log_pow]; ring_nf

lemma log_two_bounds : 1 / 2 < Real.log 2 ∧ Real.log 2 < 1 := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  constructor <;> linarith

lemma decay_a {j : ℕ} (hj : 3 ≤ j) :
    (1 + Real.log (2 * 2 ^ j)) / Real.log ((2 : ℝ) ^ j / 2) ^ 3 ≤ 128 / ((j : ℝ) + 1) ^ 2 := by
  obtain ⟨hl1, hl2⟩ := log_two_bounds
  have hj' : (3 : ℝ) ≤ j := by exact_mod_cast hj
  have e1 : Real.log (2 * 2 ^ j) = (j + 1) * Real.log 2 := by
    rw [show (2 : ℝ) * 2 ^ j = 2 ^ (j + 1) by ring, Real.log_pow]; push_cast; ring
  have e2 : Real.log ((2 : ℝ) ^ j / 2) = (j - 1) * Real.log 2 := by
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow]; ring
  rw [e1, e2]
  have hden : ((j : ℝ) + 1) ^ 3 / 64 ≤ ((j - 1) * Real.log 2) ^ 3 := by
    have : ((j : ℝ) + 1) / 4 ≤ (j - 1) * Real.log 2 := by nlinarith
    have h0 : 0 ≤ ((j : ℝ) + 1) / 4 := by positivity
    calc ((j : ℝ) + 1) ^ 3 / 64 = (((j : ℝ) + 1) / 4) ^ 3 := by ring
      _ ≤ _ := pow_le_pow_left₀ h0 this 3
  have hpos : 0 < ((j - 1) * Real.log 2) ^ 3 := by
    have : 0 < (j : ℝ) - 1 := by linarith
    positivity
  rw [div_le_div_iff₀ hpos (by positivity)]
  have hnum : 1 + ((j : ℝ) + 1) * Real.log 2 ≤ 2 * ((j : ℝ) + 1) := by nlinarith
  calc (1 + ((j : ℝ) + 1) * Real.log 2) * ((j : ℝ) + 1) ^ 2
      ≤ 2 * ((j : ℝ) + 1) * ((j : ℝ) + 1) ^ 2 := by gcongr
    _ = 128 * (((j : ℝ) + 1) ^ 3 / 64) := by ring
    _ ≤ 128 * ((j - 1) * Real.log 2) ^ 3 := by gcongr

lemma decay_c {j : ℕ} (hj : 3 ≤ j) :
    1 / Real.log ((2 : ℝ) ^ j / 2) ^ 3 ≤ 64 / ((j : ℝ) + 1) ^ 2 := by
  have h := decay_a hj
  have hl : 0 ≤ Real.log (2 * 2 ^ j) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num); linarith)
  have hj' : (3 : ℝ) ≤ j := by exact_mod_cast hj
  have hpos : 0 < Real.log ((2 : ℝ) ^ j / 2) ^ 3 := by
    have : (1 : ℝ) < 2 ^ j / 2 := by
      have : (8 : ℝ) ≤ 2 ^ j := by
        calc (8 : ℝ) = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
      linarith
    have := Real.log_pos this; positivity
  -- `1/log³ ≤ (1 + log 2N)/log³ ≤ 128/(j+1)²`; sharpen by `2 ≤ 1 + log 2N`
  have h2 : 2 ≤ 1 + Real.log (2 * 2 ^ j) := by
    have : Real.log 16 ≤ Real.log (2 * 2 ^ j) := by
      apply Real.log_le_log (by norm_num)
      have : (8 : ℝ) ≤ 2 ^ j := by
        calc (8 : ℝ) = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
      linarith
    have h16 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    have := log_two_bounds.1
    linarith
  calc 1 / Real.log ((2 : ℝ) ^ j / 2) ^ 3
      = (1 / 2) * (2 / Real.log ((2 : ℝ) ^ j / 2) ^ 3) := by ring
    _ ≤ (1 / 2) * ((1 + Real.log (2 * 2 ^ j)) / Real.log ((2 : ℝ) ^ j / 2) ^ 3) := by gcongr
    _ ≤ (1 / 2) * (128 / ((j : ℝ) + 1) ^ 2) := by gcongr
    _ = 64 / ((j : ℝ) + 1) ^ 2 := by ring

end Families.Phase3.C
