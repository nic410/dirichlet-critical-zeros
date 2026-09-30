/-
**the per-block estimate of `lem:B2`** (steps (2)–(5)), from `PNT_dlVP`.

`block_estimate`: for `j ≥ 3` with `2^j ≤ Q²`,
`|∑_n F_j(n)(Λ(n) − Λ_{R_j}(n))² − (∫ F_j log − G(R_j) ∫ F_j)| ≤ C_b h_max (1 + log Q)/(j+1)²`,
uniformly in `T ≥ 1` and in `h` (subject to `|h^{(i)}| ≤ C_i h_max`).
-/
import Families.Phase3.C.B2Block

noncomputable section

open scoped ContDiff Nat ArithmeticFunction.Moebius
open Set ArithmeticFunction MeasureTheory

namespace Families.Phase3.C

open Families

variable (P : PrimeSetup)

/-- Facts about `R = R_j` when `N = 2^j ≤ Q²`, `T ≥ 1`: `R ≤ N^{1/2−ε₃}`, `R < N/2` (`N ≥ 8`) and
`G(R) ≤ 4(1 + log Q)`. -/
lemma Rj_block_facts {Q T : ℝ} (hQ : 1 < Q) (hT : 1 ≤ T) {j : ℕ} (hj : 3 ≤ j)
    (hNQ : (2 : ℝ) ^ j ≤ Q ^ 2) :
    (P.Rj Q T j : ℝ) ≤ ((2 : ℝ) ^ j) ^ ((1 : ℝ) / 2 - P.ε₃) ∧
      (P.Rj Q T j : ℝ) < (2 : ℝ) ^ j / 2 ∧ Gsum (P.Rj Q T j) ≤ 4 * (1 + Real.log Q) := by
  set N : ℝ := 2 ^ j with hN
  set R : ℕ := P.Rj Q T j with hR
  have hN8 : 8 ≤ N := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
  have hN0 : 0 < N := by linarith
  have hQ0 : 0 < Q := by linarith
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ.le
  have hsqrt : N ^ ((1 : ℝ) / 2) ≤ Q := by
    rw [← Real.sqrt_eq_rpow]
    calc Real.sqrt N ≤ Real.sqrt (Q ^ 2) := Real.sqrt_le_sqrt hNQ
      _ = Q := Real.sqrt_sq hQ0.le
  have hR1 : (R : ℝ) ≤ N ^ ((1 : ℝ) / 2 - P.ε₃) := by
    have hfl : (R : ℝ) ≤ N ^ (1 - P.ε₃) / (Q * T) := by
      rw [hR]; unfold PrimeSetup.Rj; exact Nat.floor_le (by positivity)
    have h2 : N ^ (1 - P.ε₃) / (Q * T) ≤ N ^ (1 - P.ε₃) / Q :=
      div_le_div_of_nonneg_left (by positivity) hQ0 (by nlinarith)
    have h3 : N ^ (1 - P.ε₃) / Q ≤ N ^ (1 - P.ε₃) / N ^ ((1 : ℝ) / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hsqrt
    have h4 : N ^ (1 - P.ε₃) / N ^ ((1 : ℝ) / 2) = N ^ ((1 : ℝ) / 2 - P.ε₃) := by
      rw [← Real.rpow_sub hN0]; congr 1; ring
    linarith
  have hR2 : (R : ℝ) < N / 2 := by
    have h1 : N ^ ((1 : ℝ) / 2 - P.ε₃) ≤ N ^ ((1 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [P.ε₃_pos])
    have h2 : N ^ ((1 : ℝ) / 2) < N / 2 := by
      rw [← Real.sqrt_eq_rpow]
      have hs : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
      have hs0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg N
      nlinarith
    linarith
  refine ⟨hR1, hR2, ?_⟩
  rcases Nat.eq_zero_or_pos R with h0 | hpos
  · rw [h0, Gsum_zero]; positivity
  · have := Gsum_le R hpos
    have hRN : (R : ℝ) ≤ Q ^ 2 := by
      have : N ^ ((1 : ℝ) / 2 - P.ε₃) ≤ N ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith [P.ε₃_pos])
      rw [Real.rpow_one] at this; linarith
    have hlogR : Real.log R ≤ 2 * Real.log Q := by
      have hR0 : (0 : ℝ) < R := by exact_mod_cast hpos
      calc Real.log R ≤ Real.log (Q ^ 2) := Real.log_le_log hR0 hRN
        _ = 2 * Real.log Q := by rw [Real.log_pow]; norm_num
    linarith

/-- The number of proper prime powers `≤ 2N = 2^{j+1}` is `≤ √(2N) (j+1)`. -/
lemma card_pp_two_pow (j : ℕ) :
    (((Finset.Icc 1 (2 ^ (j + 1))).filter (fun n => Λ n ≠ 0 ∧ ¬ n.Prime)).card : ℝ) ≤
      Real.sqrt 2 * Real.sqrt (2 ^ j) * ((j : ℝ) + 1) := by
  have h := card_pp_le (2 ^ (j + 1))
  have hlog : Nat.log 2 (2 ^ (j + 1)) = j + 1 := Nat.log_pow (by norm_num) _
  rw [hlog] at h
  have hs : (Nat.sqrt (2 ^ (j + 1)) : ℝ) ≤ Real.sqrt 2 * Real.sqrt (2 ^ j) := by
    have := Real.nat_sqrt_le_real_sqrt (a := 2 ^ (j + 1))
    rw [← Real.sqrt_mul (by norm_num)]
    push_cast at this
    calc (Nat.sqrt (2 ^ (j + 1)) : ℝ) ≤ Real.sqrt (2 ^ (j + 1)) := this
      _ = Real.sqrt (2 * 2 ^ j) := by rw [pow_succ]; ring_nf
  calc (((Finset.Icc 1 (2 ^ (j + 1))).filter (fun n => Λ n ≠ 0 ∧ ¬ n.Prime)).card : ℝ)
      ≤ (Nat.sqrt (2 ^ (j + 1)) * (j + 1) : ℕ) := by exact_mod_cast h
    _ = (Nat.sqrt (2 ^ (j + 1)) : ℝ) * ((j : ℝ) + 1) := by push_cast; ring
    _ ≤ Real.sqrt 2 * Real.sqrt (2 ^ j) * ((j : ℝ) + 1) := by gcongr

/-! ### The six pieces -/

/-- (a) `|∑_p G(p) log p − ∫ G| ≤ 2048 C_G C₀ h_max/(j+1)²`, `G = F_j log`. -/
lemma piece_a {C₀ : ℝ} (hPNT : ∀ x : ℝ, 2 ≤ x → |Chebyshev.theta x - x| ≤ C₀ * x / Real.log x ^ 3)
    (hC₀ : 0 ≤ C₀) {G : ℝ → ℝ} (hG : ContDiff ℝ 1 G) {CG hmax : ℝ} (hCG : 0 ≤ CG) (hmax0 : 0 ≤ hmax)
    {j : ℕ} (hj : 3 ≤ j)
    (hG1 : ∀ y, |deriv G y| ≤ CG * hmax * (1 + Real.log (2 * 2 ^ j)) / 2 ^ j * (2 / 2 ^ j))
    (hsupp : ∀ y, G y ≠ 0 → (2 : ℝ) ^ j / 2 ≤ y ∧ y ≤ 2 * 2 ^ j) (S : Finset ℕ)
    (hS : ∀ n : ℕ, G n ≠ 0 → n ∈ S) :
    |∑ n ∈ S, G n * cPrime n - ∫ y, G y| ≤ 16 * CG * C₀ * 128 * hmax / ((j : ℝ) + 1) ^ 2 := by
  set N : ℝ := 2 ^ j with hN
  have hN8 : 8 ≤ N := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
  have hN0 : 0 < N := by linarith
  refine (prime_sum_sub_integral_le hPNT hG hG1 hN8 hsupp S hS).trans ?_
  have hdec := decay_a hj
  rw [← hN] at hdec
  have hl : 0 < Real.log (N / 2) := Real.log_pos (by linarith)
  calc 4 * N * (CG * hmax * (1 + Real.log (2 * N)) / N * (2 / N) *
        (C₀ * (2 * N) / Real.log (N / 2) ^ 3))
      = 16 * CG * C₀ * hmax * ((1 + Real.log (2 * N)) / Real.log (N / 2) ^ 3) := by
        field_simp; ring
    _ ≤ 16 * CG * C₀ * hmax * (128 / ((j : ℝ) + 1) ^ 2) := by gcongr
    _ = 16 * CG * C₀ * 128 * hmax / ((j : ℝ) + 1) ^ 2 := by ring

/-- (c) `|∑_p F(p) log p − ∫ F| ≤ 1024 K C_F C₀ h_max/(j+1)²`. -/
lemma piece_c {C₀ : ℝ} (hPNT : ∀ x : ℝ, 2 ≤ x → |Chebyshev.theta x - x| ≤ C₀ * x / Real.log x ^ 3)
    (hC₀ : 0 ≤ C₀) {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) {CF hmax : ℝ} {K : ℕ} (hCF : 0 ≤ CF)
    (hmax0 : 0 ≤ hmax) {j : ℕ} (hj : 3 ≤ j)
    (hF1 : ∀ y, |deriv F y| ≤ CF * hmax / 2 ^ j * (2 * K / 2 ^ j))
    (hsupp : ∀ y, F y ≠ 0 → (2 : ℝ) ^ j / 2 ≤ y ∧ y ≤ 2 * 2 ^ j) (S : Finset ℕ)
    (hS : ∀ n : ℕ, F n ≠ 0 → n ∈ S) :
    |∑ n ∈ S, F n * cPrime n - ∫ y, F y| ≤ 16 * K * CF * C₀ * 64 * hmax / ((j : ℝ) + 1) ^ 2 := by
  set N : ℝ := 2 ^ j with hN
  have hN8 : 8 ≤ N := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
  have hN0 : 0 < N := by linarith
  refine (prime_sum_sub_integral_le hPNT hF hF1 hN8 hsupp S hS).trans ?_
  have hdec := decay_c hj
  rw [← hN] at hdec
  have hl : 0 < Real.log (N / 2) := Real.log_pos (by linarith)
  calc 4 * N * (CF * hmax / N * (2 * K / N) * (C₀ * (2 * N) / Real.log (N / 2) ^ 3))
      = 16 * K * CF * C₀ * hmax * (1 / Real.log (N / 2) ^ 3) := by field_simp; ring
    _ ≤ 16 * K * CF * C₀ * hmax * (64 / ((j : ℝ) + 1) ^ 2) := by gcongr
    _ = 16 * K * CF * C₀ * 64 * hmax / ((j : ℝ) + 1) ^ 2 := by ring

lemma log_two_pow_succ_le (j : ℕ) : Real.log ((2 ^ (j + 1) : ℕ) : ℝ) ≤ (j : ℝ) + 1 := by
  push_cast; rw [Real.log_pow]; push_cast
  have := log_two_bounds.2
  nlinarith [Nat.cast_nonneg (α := ℝ) j]

/-- (b), (d): the proper prime powers. `|∑ F(n) Λ_{pp}(n) g(n)| ≤ √2 C_F h_max (j+1)² N^{−1/2} G₀`
when `|g| ≤ G₀` on `[1, 2N]` and `G₀ ≤ (j+1)` or `G₀ ≤ N^{1/2−ε₃}`. -/
lemma pp_block_le (S : Finset ℕ) {F : ℝ → ℝ} {CF hmax : ℝ} {j : ℕ}
    (hF0 : ∀ y, |F y| ≤ CF * hmax / 2 ^ j) (hbig : ∀ n : ℕ, 2 ^ (j + 1) < n → F n = 0)
    {g : ℕ → ℝ} {G₀ : ℝ} (hg : ∀ n, 1 ≤ n → n ≤ 2 ^ (j + 1) → |g n| ≤ G₀) (hG₀ : 0 ≤ G₀)
    (hCF : 0 ≤ CF) (hmax0 : 0 ≤ hmax) :
    |∑ n ∈ S, F n * (LamPP n * g n)| ≤
      Real.sqrt 2 * CF * hmax * ((j : ℝ) + 1) ^ 2 * (Real.sqrt (2 ^ j) / 2 ^ j) * G₀ := by
  have hpp := pp_sum_le S (F := fun n : ℕ => F n) (g := g) (M := 2 ^ (j + 1))
    (B := CF * hmax / 2 ^ j) (G₀ := G₀) (fun n => hF0 n) (fun n hn => hbig n hn) hg hG₀
  refine hpp.trans ?_
  have hcard := card_pp_two_pow j
  have hlogM := log_two_pow_succ_le j
  have hlogM0 : 0 ≤ Real.log ((2 ^ (j + 1) : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.one_le_two_pow)
  calc (((Finset.Icc 1 (2 ^ (j + 1))).filter (fun n => Λ n ≠ 0 ∧ ¬ n.Prime)).card : ℝ) *
        (CF * hmax / 2 ^ j * Real.log ((2 ^ (j + 1) : ℕ) : ℝ) * G₀)
      ≤ (Real.sqrt 2 * Real.sqrt (2 ^ j) * ((j : ℝ) + 1)) *
          (CF * hmax / 2 ^ j * ((j : ℝ) + 1) * G₀) := by
        gcongr
    _ = Real.sqrt 2 * CF * hmax * ((j : ℝ) + 1) ^ 2 * (Real.sqrt (2 ^ j) / 2 ^ j) * G₀ := by ring

lemma sqrt_two_pow_div (j : ℕ) :
    Real.sqrt ((2 : ℝ) ^ j) / 2 ^ j = Real.exp (-(Real.log 2 / 2 * j)) := by
  rw [two_pow_eq_exp, Real.sqrt_eq_rpow, ← Real.exp_mul, ← Real.exp_sub]
  congr 1; ring

/-- (e) the `Λ_R²` term. -/
lemma piece_e {F : ℝ → ℝ} {K : ℕ} (hK1 : 1 ≤ K) (hF : ContDiff ℝ K F) {CF hmax : ℝ}
    (hCF : 0 ≤ CF) (hmax0 : 0 ≤ hmax) {j : ℕ} (hj : 3 ≤ j) {ε : ℝ} (hε : 0 < ε)
    (hKε : 1 ≤ K * ε)
    (hFK : ∀ y, |iteratedDeriv K F y| ≤ CF * hmax / 2 ^ j * (2 * K / 2 ^ j) ^ K)
    (hsupp : ∀ y, F y ≠ 0 → (2 : ℝ) ^ j / 2 ≤ y ∧ y ≤ 2 * 2 ^ j) (S : Finset ℕ)
    (hS : ∀ n : ℕ, F n ≠ 0 → n ∈ S) {R : ℕ} (hRle : (R : ℝ) ≤ ((2 : ℝ) ^ j) ^ ((1 : ℝ) / 2 - ε))
    {Cde : ℝ} (hCde : ∀ j : ℕ, ((j : ℝ) + 1) ^ 0 * Real.exp (-(Real.log 2 * j)) ≤
      Cde / ((j : ℝ) + 1) ^ 2) :
    |∑ n ∈ S, F n * PrimeSetup.LamR R n ^ 2 - Gsum R * ∑ n ∈ S, F n| ≤
      (K + 3) * K ^ K * CF * Cde * hmax / ((j : ℝ) + 1) ^ 2 := by
  set N : ℝ := 2 ^ j with hN
  have hN8 : 8 ≤ N := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
  have hN0 : 0 < N := by linarith
  refine (sum_F_LamR_sq hF hFK (a := N / 2) (b := 2 * N) (by positivity) (by linarith) hsupp S
    hS R).trans ?_
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hK1' : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  set ν : ℝ := N ^ (-ε) with hν
  have hν0 : 0 ≤ ν := by positivity
  have hR2 : ((R : ℝ)) ^ 2 ≤ N * ν ^ 2 := by
    have h1 : ((R : ℝ)) ^ 2 ≤ (N ^ ((1 : ℝ) / 2 - ε)) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hRle 2
    have h2 : (N ^ ((1 : ℝ) / 2 - ε)) ^ 2 = N * ν ^ 2 := by
      rw [hν, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le,
        ← Real.rpow_mul hN0.le]
      rw [show N * N ^ (-ε * ((2 : ℕ) : ℝ)) = N ^ (1 : ℝ) * N ^ (-ε * ((2 : ℕ) : ℝ)) by
        rw [Real.rpow_one], ← Real.rpow_add hN0]
      congr 1; push_cast; ring
    linarith
  have hlen : 2 * N - N / 2 + K + 1 ≤ (K + 3) * N := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ K + 3 / 2) (by linarith : (0 : ℝ) ≤ N - 1)]
  have hfreq : (2 * K / N) ^ K * (((R : ℝ) ^ 2) / 4) ^ K ≤ K ^ K * ν ^ (2 * K) := by
    rw [← mul_pow, pow_mul, ← mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    calc 2 * K / N * (((R : ℝ) ^ 2) / 4) ≤ 2 * K / N * (N * ν ^ 2 / 4) := by gcongr
      _ = K * ν ^ 2 / 2 := by field_simp; ring
      _ ≤ K * ν ^ 2 := by
          have : 0 ≤ K * ν ^ 2 := by positivity
          linarith
  have hNν : N * ν ^ (2 * K + 2) ≤ Real.exp (-(Real.log 2 * j)) := by
    have h1 : N * ν ^ (2 * K + 2) = N ^ (1 - (2 * K + 2) * ε) := by
      rw [hν, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le,
        show N * N ^ (-ε * ((2 * K + 2 : ℕ) : ℝ)) =
          N ^ (1 : ℝ) * N ^ (-ε * ((2 * K + 2 : ℕ) : ℝ)) by rw [Real.rpow_one],
        ← Real.rpow_add hN0]
      congr 1; push_cast; ring
    have h2 : N ^ (1 - (2 * K + 2) * ε) ≤ N ^ (-1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith)
    have h3 : N ^ (-1 : ℝ) = Real.exp (-(Real.log 2 * j)) := by
      rw [Real.rpow_neg_one, hN, two_pow_eq_exp, ← Real.exp_neg]
    linarith
  have hdec := hCde j
  simp only [pow_zero, one_mul] at hdec
  calc (R : ℝ) ^ 2 * ((2 * N - N / 2 + K + 1) * (CF * hmax / N * (2 * K / N) ^ K) *
        (((R : ℝ) ^ 2) / 4) ^ K)
      = (R : ℝ) ^ 2 * (2 * N - N / 2 + K + 1) * (CF * hmax / N) *
          ((2 * K / N) ^ K * (((R : ℝ) ^ 2) / 4) ^ K) := by ring
    _ ≤ (N * ν ^ 2) * ((K + 3) * N) * (CF * hmax / N) * (K ^ K * ν ^ (2 * K)) := by
        have : 0 ≤ 2 * N - N / 2 + K + 1 := by linarith
        gcongr
    _ = (K + 3) * K ^ K * CF * hmax * (N * ν ^ (2 * K + 2)) := by
        rw [pow_add ν (2 * K) 2]; field_simp
    _ ≤ (K + 3) * K ^ K * CF * hmax * Real.exp (-(Real.log 2 * j)) := by gcongr
    _ ≤ (K + 3) * K ^ K * CF * hmax * (Cde / ((j : ℝ) + 1) ^ 2) := by gcongr
    _ = (K + 3) * K ^ K * CF * Cde * hmax / ((j : ℝ) + 1) ^ 2 := by ring

/-- (f) `|∑ F − ∫ F| ≤ 4K C_F h_max/N`. -/
lemma piece_f {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) {CF hmax : ℝ} {K : ℕ} (hCF : 0 ≤ CF)
    (hmax0 : 0 ≤ hmax) {j : ℕ} (hj : 3 ≤ j)
    (hF1 : ∀ y, |deriv F y| ≤ CF * hmax / 2 ^ j * (2 * K / 2 ^ j))
    (hsupp : ∀ y, F y ≠ 0 → (2 : ℝ) ^ j / 2 ≤ y ∧ y ≤ 2 * 2 ^ j) (S : Finset ℕ)
    (hS : ∀ n : ℕ, F n ≠ 0 → n ∈ S) {Cde : ℝ}
    (hCde : ∀ j : ℕ, ((j : ℝ) + 1) ^ 0 * Real.exp (-(Real.log 2 * j)) ≤ Cde / ((j : ℝ) + 1) ^ 2) :
    |∑ n ∈ S, F n - ∫ y, F y| ≤ 4 * K * CF * Cde * hmax / ((j : ℝ) + 1) ^ 2 := by
  set N : ℝ := 2 ^ j with hN
  have hN8 : 8 ≤ N := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
  have hN0 : 0 < N := by linarith
  refine (abs_sum_sub_integral_le hF hF1 (a := N / 2) (b := 2 * N) (by linarith) (by linarith)
    hsupp S hS).trans ?_
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hdec := hCde j
  simp only [pow_zero, one_mul] at hdec
  have h1 : (2 * N - N / 2 + 2) * (CF * hmax / N * (2 * K / N)) ≤ 4 * K * CF * hmax / N := by
    rw [le_div_iff₀ hN0]
    have e : (2 * N - N / 2 + 2) * (CF * hmax / N * (2 * K / N)) * N =
        (3 * K + 4 * K / N) * (CF * hmax) := by field_simp; ring
    rw [e]
    have : 4 * K / N ≤ K := by rw [div_le_iff₀ hN0]; nlinarith
    have : 0 ≤ CF * hmax := by positivity
    nlinarith
  have h2 : 1 / N = Real.exp (-(Real.log 2 * j)) := by
    rw [hN, two_pow_eq_exp, one_div, ← Real.exp_neg]
  have hX : 0 ≤ 4 * K * CF * hmax := by positivity
  calc (2 * N - N / 2 + 2) * (CF * hmax / N * (2 * K / N)) ≤ 4 * K * CF * hmax / N := h1
    _ = 4 * K * CF * hmax * (1 / N) := by ring
    _ ≤ 4 * K * CF * hmax * (Cde / ((j : ℝ) + 1) ^ 2) := by
        rw [h2]; exact mul_le_mul_of_nonneg_left hdec hX
    _ = 4 * K * CF * Cde * hmax / ((j : ℝ) + 1) ^ 2 := by ring

/-- The combination of the six pieces (pure inequality). -/
lemma combine_six {a b c d e f g ℓ w A B Cc D E Fc : ℝ} (hg0 : 0 ≤ g) (hg : g ≤ 4 * (1 + ℓ))
    (hℓ : 0 ≤ ℓ) (hw : 0 ≤ w)
    (ha : |a| ≤ A * w) (hb : |b| ≤ B * w) (hc : |c| ≤ Cc * w) (hd : |d| ≤ D * w)
    (he : |e| ≤ E * w) (hf : |f| ≤ Fc * w) (hA : 0 ≤ A) (hB : 0 ≤ B) (_hC : 0 ≤ Cc) (hD : 0 ≤ D)
    (hE : 0 ≤ E) (_hF : 0 ≤ Fc) :
    |a + b - 2 * g * c - 2 * d + e + g * f| ≤
      (A + B + 2 * 4 * Cc + 2 * D + E + 4 * Fc) * w * (1 + ℓ) := by
  have h1 : |a + b - 2 * g * c - 2 * d + e + g * f| ≤
      |a| + |b| + 2 * g * |c| + 2 * |d| + |e| + g * |f| := by
    have e6 : |2 * g * c| = 2 * g * |c| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * g)]
    have e7 : |2 * d| = 2 * |d| := by rw [abs_mul, abs_two]
    have e8 : |g * f| = g * |f| := by rw [abs_mul, abs_of_nonneg hg0]
    calc |a + b - 2 * g * c - 2 * d + e + g * f|
        ≤ |a + b - 2 * g * c - 2 * d + e| + |g * f| := abs_add_le _ _
      _ ≤ |a + b - 2 * g * c - 2 * d| + |e| + |g * f| := by gcongr; exact abs_add_le _ _
      _ ≤ |a + b - 2 * g * c| + |2 * d| + |e| + |g * f| := by gcongr; exact abs_sub _ _
      _ ≤ |a + b| + |2 * g * c| + |2 * d| + |e| + |g * f| := by gcongr; exact abs_sub _ _
      _ ≤ |a| + |b| + |2 * g * c| + |2 * d| + |e| + |g * f| := by gcongr; exact abs_add_le _ _
      _ = _ := by rw [e6, e7, e8]
  refine h1.trans ?_
  have hℓ1 : w ≤ w * (1 + ℓ) := le_mul_of_one_le_right hw (by linarith)
  have hgc : g * |c| ≤ 4 * (1 + ℓ) * (Cc * w) := mul_le_mul hg hc (abs_nonneg _) (by positivity)
  have hgf : g * |f| ≤ 4 * (1 + ℓ) * (Fc * w) := mul_le_mul hg hf (abs_nonneg _) (by positivity)
  have t1 : A * w ≤ A * (w * (1 + ℓ)) := mul_le_mul_of_nonneg_left hℓ1 hA
  have t2 : B * w ≤ B * (w * (1 + ℓ)) := mul_le_mul_of_nonneg_left hℓ1 hB
  have t4 : D * w ≤ D * (w * (1 + ℓ)) := mul_le_mul_of_nonneg_left hℓ1 hD
  have t5 : E * w ≤ E * (w * (1 + ℓ)) := mul_le_mul_of_nonneg_left hℓ1 hE
  nlinarith

/-- **Per-block estimate** (steps (2)–(5) of `lem:B2`). -/
theorem block_estimate {C₀ : ℝ}
    (hPNT : ∀ x : ℝ, 2 ≤ x → |Chebyshev.theta x - x| ≤ C₀ * x / Real.log x ^ 3) (Cs : ℕ → ℝ) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ Q T : ℝ, 1 < Q → 1 ≤ P.L Q → 1 ≤ T →
      ∀ (h : ℝ → ℝ) (hmax : ℝ), ContDiff ℝ ∞ h → (∀ y, 0 ≤ h y) → (∀ y, h y ≤ hmax) →
      (∀ i y, |iteratedDeriv i h y| ≤ Cs i * hmax) →
      ∀ j : ℕ, 3 ≤ j → (2 : ℝ) ^ j ≤ Q ^ 2 →
        |∑ n ∈ P.range Q, Fh P Q h j n * (Λ n - PrimeSetup.LamR (P.Rj Q T j) n) ^ 2 -
          ((∫ y, Gh P Q h j y) - Gsum (P.Rj Q T j) * ∫ y, Fh P Q h j y)| ≤
            Cb * hmax * (1 + Real.log Q) / ((j : ℝ) + 1) ^ 2 := by
  have hC₀ : 0 ≤ C₀ := by
    have h := hPNT 2 le_rfl
    have : 0 ≤ C₀ * 2 / Real.log 2 ^ 3 := (abs_nonneg _).trans h
    have hl : 0 < Real.log 2 ^ 3 := by have := Real.log_pos one_lt_two; positivity
    rw [div_nonneg_iff] at this
    rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
    · linarith
    · linarith
  set K : ℕ := ⌈1 / P.ε₃⌉₊ with hKdef
  have hε := P.ε₃_pos
  have hK1 : 1 ≤ K := by
    rw [hKdef, Nat.one_le_ceil_iff]; positivity
  have hKε : 1 ≤ K * P.ε₃ := by
    have := Nat.le_ceil (1 / P.ε₃)
    rw [← hKdef, div_le_iff₀ hε] at this; linarith
  obtain ⟨CF, hCF0, hCF⟩ := Fh_deriv_bound P K hK1 Cs
  obtain ⟨CG, hCG0, hCG⟩ := Gh_deriv_bound P Cs
  have hl2 := log_two_bounds.1
  obtain ⟨Cdb, hCdb0, hCdb⟩ := exp_decay 3 (c := Real.log 2 / 2) (by linarith)
  obtain ⟨Cdd, hCdd0, hCdd⟩ := exp_decay 2 (c := P.ε₃ * Real.log 2) (by positivity)
  obtain ⟨Cde, hCde0, hCde⟩ := exp_decay 0 (c := Real.log 2) (by linarith)
  refine ⟨16 * CG * C₀ * 128 + Real.sqrt 2 * CF * Cdb + 2 * 4 * (16 * K * CF * C₀ * 64) +
    2 * (Real.sqrt 2 * CF * Cdd) + (K + 3) * K ^ K * CF * Cde + 4 * (4 * K * CF * Cde),
    by positivity, ?_⟩
  intro Q T hQ hL hT h hmax hh hh0 hhmax hhd j hj hNQ
  have hmax0 : 0 ≤ hmax := (hh0 0).trans (hhmax 0)
  have hj1 : 1 ≤ j := by omega
  obtain ⟨hRle, hRlt, hGR⟩ := Rj_block_facts P hQ hT hj hNQ
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ.le
  -- derivative bounds for `F = F_j`
  have hFk := hCF Q hL h hmax hh hh0 hhmax hhd j
  have hF0 : ∀ y, |Fh P Q h j y| ≤ CF * hmax / 2 ^ j := fun y => by
    have := hFk 0 (Nat.zero_le _) y
    simpa [Real.norm_eq_abs] using this
  have hF1 : ∀ y, |deriv (Fh P Q h j) y| ≤ CF * hmax / 2 ^ j * (2 * K / 2 ^ j) := fun y => by
    have := hFk 1 hK1 y
    simpa [Real.norm_eq_abs, iteratedDeriv_one] using this
  have hFK : ∀ y, |iteratedDeriv K (Fh P Q h j) y| ≤ CF * hmax / 2 ^ j * (2 * K / 2 ^ j) ^ K :=
    fun y => by
      have := hFk K le_rfl y
      rwa [Real.norm_eq_abs] at this
  have hG1 := hCG Q hL h hmax hh hh0 hhmax hhd j hj1
  have hFS : ∀ n : ℕ, Fh P Q h j n ≠ 0 → n ∈ P.range Q := by
    intro n hn
    have hs := Fh_supp P Q h j n hn
    have hnY : (n : ℝ) ≤ P.Y Q := by
      by_contra hc; exact hn (Fh_eq_zero_of_gt P hQ h j (not_le.mp hc))
    simp only [PrimeSetup.range, Finset.mem_Icc]
    refine ⟨?_, Nat.le_floor hnY⟩
    have : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hs.1
    exact_mod_cast this
  have hGS : ∀ n : ℕ, Gh P Q h j n ≠ 0 → n ∈ P.range Q := by
    intro n hn
    apply hFS
    intro hF; apply hn; rw [Gh_eq, hF, zero_mul]
  have hFbig : ∀ n : ℕ, 2 ^ (j + 1) < n → Fh P Q h j n = 0 := by
    intro n hn
    by_contra hne
    have h1 := (Fh_supp P Q h j n hne).2
    have h2 : ((2 ^ (j + 1) : ℕ) : ℝ) < n := by exact_mod_cast hn
    push_cast at h2
    rw [pow_succ] at h2
    linarith
  -- the decomposition
  have hLp : ∀ n ∈ P.range Q, n.Prime → Fh P Q h j n ≠ 0 →
      PrimeSetup.LamR (P.Rj Q T j) n = Gsum (P.Rj Q T j) := by
    intro n _ hp hF
    have hn := (Fh_supp P Q h j n hF).1
    exact LamR_prime hp (by
      have : (P.Rj Q T j : ℝ) < n := lt_of_lt_of_le hRlt hn
      exact_mod_cast this)
  rw [block_decomp (P.range Q) (fun n : ℕ => Fh P Q h j n) (fun n => PrimeSetup.LamR (P.Rj Q T j) n)
    (Gsum (P.Rj Q T j)) hLp]
  have hA1 : ∑ n ∈ P.range Q, (Fh P Q h j n * Real.log n) * cPrime n =
      ∑ n ∈ P.range Q, Gh P Q h j n * cPrime n :=
    Finset.sum_congr rfl fun n _ => by rw [Gh_eq]
  rw [hA1]
  have key : ∀ (A1 B1 C1 D1 E1 F1 I1 I2 g : ℝ),
      A1 + B1 - 2 * (g * C1 + D1) + E1 - (I1 - g * I2) =
        (A1 - I1) + B1 - 2 * g * (C1 - I2) - 2 * D1 + (E1 - g * F1) + g * (F1 - I2) := by
    intros; ring
  rw [key _ _ _ _ _ (∑ n ∈ P.range Q, Fh P Q h j n)]
  have hw0 : 0 ≤ hmax / ((j : ℝ) + 1) ^ 2 := by positivity
  have ha := piece_a hPNT hC₀ (Gh_contDiff P Q hh j 1) hCG0 hmax0 hj hG1 (Gh_supp P Q h j)
    (P.range Q) hGS
  have hb := pp_block_le (P.range Q) hF0 hFbig (g := fun n => Λ n)
    (G₀ := (j : ℝ) + 1) (fun n hn1 hnM => by
      rw [abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      exact ArithmeticFunction.vonMangoldt_le_log.trans
        ((Real.log_le_log (by exact_mod_cast hn1) (by exact_mod_cast hnM)).trans
          (log_two_pow_succ_le j))) (by positivity) hCF0 hmax0
  have hb' : |∑ n ∈ P.range Q, Fh P Q h j n * (LamPP n * Λ n)| ≤
      Real.sqrt 2 * CF * Cdb * (hmax / ((j : ℝ) + 1) ^ 2) := by
    refine hb.trans ?_
    rw [sqrt_two_pow_div]
    have := hCdb j
    calc Real.sqrt 2 * CF * hmax * ((j : ℝ) + 1) ^ 2 * Real.exp (-(Real.log 2 / 2 * j)) *
          ((j : ℝ) + 1)
        = Real.sqrt 2 * CF * hmax * (((j : ℝ) + 1) ^ 3 * Real.exp (-(Real.log 2 / 2 * j))) := by
          ring
      _ ≤ Real.sqrt 2 * CF * hmax * (Cdb / ((j : ℝ) + 1) ^ 2) := by gcongr
      _ = _ := by ring
  have hc := piece_c hPNT hC₀ (Fh_contDiff P Q hh j 1) hCF0 hmax0 hj hF1 (Fh_supp P Q h j)
    (P.range Q) hFS
  have hd := pp_block_le (P.range Q) hF0 hFbig (g := fun n => PrimeSetup.LamR (P.Rj Q T j) n)
    (G₀ := ((2 : ℝ) ^ j) ^ ((1 : ℝ) / 2 - P.ε₃))
    (fun n _ _ => (abs_LamR_le _ n).trans hRle) (by positivity) hCF0 hmax0
  have hd' : |∑ n ∈ P.range Q, Fh P Q h j n * (LamPP n * PrimeSetup.LamR (P.Rj Q T j) n)| ≤
      Real.sqrt 2 * CF * Cdd * (hmax / ((j : ℝ) + 1) ^ 2) := by
    refine hd.trans ?_
    have hN0 : (0 : ℝ) < 2 ^ j := by positivity
    have hpow : Real.sqrt ((2 : ℝ) ^ j) / 2 ^ j * ((2 : ℝ) ^ j) ^ ((1 : ℝ) / 2 - P.ε₃) =
        Real.exp (-(P.ε₃ * Real.log 2 * j)) := by
      rw [Real.sqrt_eq_rpow, show ((2 : ℝ) ^ j) ^ ((1 : ℝ) / 2) / 2 ^ j =
        ((2 : ℝ) ^ j) ^ ((1 : ℝ) / 2) / ((2 : ℝ) ^ j) ^ (1 : ℝ) by rw [Real.rpow_one],
        ← Real.rpow_sub hN0, ← Real.rpow_add hN0, two_pow_eq_exp,
        Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      congr 1; ring
    have := hCdd j
    calc Real.sqrt 2 * CF * hmax * ((j : ℝ) + 1) ^ 2 * (Real.sqrt (2 ^ j) / 2 ^ j) *
          ((2 : ℝ) ^ j) ^ ((1 : ℝ) / 2 - P.ε₃)
        = Real.sqrt 2 * CF * hmax * (((j : ℝ) + 1) ^ 2 *
            (Real.sqrt ((2 : ℝ) ^ j) / 2 ^ j * ((2 : ℝ) ^ j) ^ ((1 : ℝ) / 2 - P.ε₃))) := by ring
      _ = Real.sqrt 2 * CF * hmax * (((j : ℝ) + 1) ^ 2 * Real.exp (-(P.ε₃ * Real.log 2 * j))) := by
          rw [hpow]
      _ ≤ Real.sqrt 2 * CF * hmax * (Cdd / ((j : ℝ) + 1) ^ 2) := by gcongr
      _ = _ := by ring
  have he := piece_e hK1 (Fh_contDiff P Q hh j K) hCF0 hmax0 hj hε hKε hFK (Fh_supp P Q h j)
    (P.range Q) hFS hRle hCde
  have hf := piece_f (Fh_contDiff P Q hh j 1) hCF0 hmax0 hj hF1 (Fh_supp P Q h j) (P.range Q) hFS
    hCde
  have hcomb := combine_six (Gsum_nonneg (P.Rj Q T j)) hGR hlogQ hw0
    (A := 16 * CG * C₀ * 128) (B := Real.sqrt 2 * CF * Cdb) (Cc := 16 * K * CF * C₀ * 64)
    (D := Real.sqrt 2 * CF * Cdd) (E := (K + 3) * K ^ K * CF * Cde) (Fc := 4 * K * CF * Cde)
    (by rw [mul_div_assoc] at ha; exact ha) hb' (by rw [mul_div_assoc] at hc; exact hc) hd'
    (by rw [mul_div_assoc] at he; exact he) (by rw [mul_div_assoc] at hf; exact hf)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
  refine hcomb.trans (le_of_eq ?_)
  ring

end Families.Phase3.C
