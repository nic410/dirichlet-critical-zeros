/-
**`lem:B1`** (invisibility), Lemma 5.6.

`S_χ[a♯](t) = ∑_{j : R_j ≥ 1} ∑_{r ≤ R_j} (μ(r)/φ(r)) ∑_n F_{j,t}(n) c_r(n) χ(n)` (`Schi_aSharp_eq`), and
each inner sum is `≤ φ(r) √q (3N_j/2 + K + 1) C N_j^{−1/2} (2(1+|t|)K/N_j)^K (rq/4)^K`
(`sum_F_ramanujan_char_le`, `Fjt_deriv_bound`); with `rq(1+|t|) ≤ 4 Q R_j T ≤ 4 N_j^{1−ε₃}` this is
`≪ φ(r) √Q N_j^{1/2 − Kε₃}`, and summing over `r ≤ R_j ≤ N_j` and the `≤ 3Q²` blocks (`N_j ≥ QT ≥ Q`)
gives `≪ Q^{4 − Kε₃} ≤ Q^{−A}` for `Kε₃ ≥ A + 4`.
-/
import Families.Phase3.C.Weights

noncomputable section

open scoped ContDiff Nat ArithmeticFunction.Moebius
open Set ArithmeticFunction

namespace Families.Phase3.C

open Families

variable (P : PrimeSetup)

/-! ### Elementary facts about the fixed data -/

lemma L_pos' {Q : ℝ} (hQ : 1 < Q) : 0 < P.L Q := mul_pos P.lam_pos (Real.log_pos hQ)

lemma log_Y {Q : ℝ} : Real.log (P.Y Q) = P.L Q * (1 + P.ε₁) := by
  unfold PrimeSetup.Y PrimeSetup.X
  rw [Real.log_rpow (Real.exp_pos _), Real.log_exp]; ring

lemma Y_pos' (Q : ℝ) : 0 < P.Y Q := Real.rpow_pos_of_pos (Real.exp_pos _) _

/-- `Y = Q^{λ(1+ε₁)} ≤ Q^{2−ε₁}`. -/
lemma Y_le_rpow {Q : ℝ} (hQ : 1 ≤ Q) : P.Y Q ≤ Q ^ (2 - P.ε₁) := by
  rcases eq_or_lt_of_le hQ with h | h
  · subst h; unfold PrimeSetup.Y PrimeSetup.X PrimeSetup.L; simp
  have hQ0 : 0 < Q := by linarith
  have hY : P.Y Q = Q ^ (P.lam * (1 + P.ε₁)) := by
    rw [Real.rpow_def_of_pos hQ0]
    unfold PrimeSetup.Y PrimeSetup.X PrimeSetup.L
    rw [← Real.exp_mul]; ring_nf
  rw [hY]
  exact Real.rpow_le_rpow_of_exponent_le hQ P.lam_ε₁

lemma Y_le_sq {Q : ℝ} (hQ : 1 ≤ Q) : P.Y Q ≤ Q ^ 2 := by
  refine (Y_le_rpow P hQ).trans ?_
  have : Q ^ (2 - P.ε₁) ≤ Q ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hQ (by linarith [P.ε₁_pos])
  simpa using this

lemma one_le_L {Q : ℝ} (hQ : Real.exp (1 / P.lam) ≤ Q) : 1 ≤ P.L Q := by
  have hQ0 : 0 < Q := lt_of_lt_of_le (Real.exp_pos _) hQ
  have := Real.log_le_log (Real.exp_pos _) hQ
  rw [Real.log_exp] at this
  unfold PrimeSetup.L
  have hl := P.lam_pos
  rw [div_le_iff₀ hl] at this
  linarith

lemma one_le_T {Q T : ℝ} (hQ : Real.exp 1 ≤ Q) (hT : T ∈ P.heights Q) : 1 ≤ T := by
  have hl : 1 ≤ Real.log Q := by
    have := Real.log_le_log (Real.exp_pos _) hQ; rwa [Real.log_exp] at this
  exact le_trans (Real.one_le_rpow hl P.a0_pos.le) hT.1

lemma card_blocks_le {Q : ℝ} (hQ : 1 ≤ Q) : ((P.blocks Q).card : ℝ) ≤ 3 * Q ^ 2 := by
  unfold PrimeSetup.blocks
  rw [Finset.card_range]
  have h1 : Nat.log 2 ⌊P.Y Q⌋₊ ≤ ⌊P.Y Q⌋₊ := Nat.log_le_self 2 _
  have h2 : (⌊P.Y Q⌋₊ : ℝ) ≤ P.Y Q := Nat.floor_le (Y_pos' P Q).le
  have h3 := Y_le_sq P hQ
  push_cast
  have : ((Nat.log 2 ⌊P.Y Q⌋₊ : ℕ) : ℝ) ≤ Q ^ 2 := by
    calc ((Nat.log 2 ⌊P.Y Q⌋₊ : ℕ) : ℝ) ≤ (⌊P.Y Q⌋₊ : ℝ) := by exact_mod_cast h1
      _ ≤ Q ^ 2 := h2.trans h3
  have hQ2 : 1 ≤ Q ^ 2 := one_le_pow₀ hQ
  linarith

/-! ### The decomposition of `S_χ[a♯]` -/

lemma natCast_cpow' (n : ℕ) (hn : 1 ≤ n) (z : ℂ) :
    (n : ℂ) ^ z = Complex.exp ((Real.log n : ℂ) * z) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [Complex.cpow_def_of_ne_zero hn0, Complex.natCast_log]

lemma Et_nat (t : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    Et t n = ((Real.sqrt n)⁻¹ : ℝ) * (n : ℂ) ^ (-(Complex.I * t)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [natCast_cpow' n hn, Et]
  have hs : ((Real.sqrt n)⁻¹ : ℝ) = Real.exp (-(1 / 2) * Real.log n) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hn0.le, Real.rpow_def_of_pos hn0]; ring_nf
  rw [hs, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1; push_cast; ring

lemma Fjt_nat (Q : ℝ) (j : ℕ) (t : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    Fjt P Q j t n = ((P.ψj j n * P.Ups Q n / Real.sqrt n : ℝ) : ℂ) * (n : ℂ) ^ (-(Complex.I * t)) := by
  rw [Fjt, Et_nat t n hn]
  simp only [UpsL, PrimeSetup.Ups]
  push_cast; ring

lemma Schi_aSharp_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (Q T t : ℝ) :
    P.Schi χ Q (P.aSharp Q T) t =
      ∑ j ∈ (P.blocks Q).filter (fun j => 1 ≤ P.Rj Q T j), ∑ r ∈ Finset.Icc 1 (P.Rj Q T j),
        (((μ r : ℝ) / Nat.totient r : ℝ) : ℂ) *
          ∑ n ∈ P.range Q, Fjt P Q j t n * ramanujan r n * χ n := by
  unfold PrimeSetup.Schi
  have hpt : ∀ n ∈ P.range Q, (P.aSharp Q T n : ℂ) * χ n * (n : ℂ) ^ (-(Complex.I * t)) =
      ∑ j ∈ (P.blocks Q).filter (fun j => 1 ≤ P.Rj Q T j), ∑ r ∈ Finset.Icc 1 (P.Rj Q T j),
        (((μ r : ℝ) / Nat.totient r : ℝ) : ℂ) * (Fjt P Q j t n * ramanujan r n * χ n) := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    unfold PrimeSetup.aSharp PrimeSetup.LamR
    push_cast
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Fjt_nat P Q j t n hn1]
    conv_rhs => rw [← ramanujan_re_coe r n]
    push_cast; ring
  rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]

/-! ### The block estimate -/

/-- `R_j ≥ 1` forces `N_j ≥ QT`; `Q T R_j ≤ N_j^{1−ε₃}`; and `R_j ≤ N_j` when `QT ≥ 1`. -/
lemma Rj_facts {Q T : ℝ} (hQT1 : 1 ≤ Q * T) {j : ℕ} (hR : 1 ≤ P.Rj Q T j) :
    Q * T ≤ (2 : ℝ) ^ j ∧ Q * T * P.Rj Q T j ≤ ((2 : ℝ) ^ j) ^ (1 - P.ε₃) ∧
      (P.Rj Q T j : ℝ) ≤ (2 : ℝ) ^ j := by
  have hQT : 0 < Q * T := by linarith
  set N : ℝ := (2 : ℝ) ^ j with hN
  have hN1 : 1 ≤ N := one_le_pow₀ (by norm_num)
  have hfl : (P.Rj Q T j : ℝ) ≤ N ^ (1 - P.ε₃) / (Q * T) := by
    unfold PrimeSetup.Rj
    exact Nat.floor_le (by positivity)
  have h2 : Q * T * P.Rj Q T j ≤ N ^ (1 - P.ε₃) := by
    rw [le_div_iff₀ hQT] at hfl; linarith
  have h3 : N ^ (1 - P.ε₃) ≤ N := by
    have := Real.rpow_le_rpow_of_exponent_le hN1 (show 1 - P.ε₃ ≤ 1 by linarith [P.ε₃_pos])
    simpa using this
  have hR' : (1 : ℝ) ≤ P.Rj Q T j := by exact_mod_cast hR
  refine ⟨?_, h2, ?_⟩
  · nlinarith
  · have h4 : N ^ (1 - P.ε₃) / (Q * T) ≤ N ^ (1 - P.ε₃) :=
      div_le_self (by positivity) hQT1
    linarith

/-- The arithmetic of one `(j, r)` term. -/
lemma block_arith {N T Q R CF : ℝ} {K : ℕ} {ε t rq : ℝ} (hN1 : 1 ≤ N) (hT : 0 ≤ T)
    (ht : 1 + |t| ≤ 4 * T) (hK1 : 1 ≤ K) (hCF : 0 ≤ CF) (hrq0 : 0 ≤ rq) (hrq : rq ≤ R * Q)
    (hQTR : Q * T * R ≤ N ^ (1 - ε)) :
    (2 * N - N / 2 + K + 1) * (CF * Real.sqrt (2 / N) * (2 * (1 + |t|) * K / N) ^ K) *
        (rq / 4) ^ K ≤
      ((K + 3) * CF * Real.sqrt 2 * (2 * K) ^ K) * N ^ ((1 : ℝ) / 2 - K * ε) := by
  have hN0 : 0 < N := by linarith
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hK1' : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hlen : 2 * N - N / 2 + K + 1 ≤ (K + 3) * N := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ K + 3 / 2) (by linarith : (0 : ℝ) ≤ N - 1)]
  have hNε : N ^ (1 - ε) = N * N ^ (-ε) := by
    rw [Real.rpow_sub hN0, Real.rpow_one, Real.rpow_neg hN0.le]; ring
  have hfreq : 2 * (1 + |t|) * K / N * (rq / 4) ≤ 2 * K * N ^ (-ε) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hN0]
    calc 2 * (1 + |t|) * K * (rq / 4) ≤ 2 * (4 * T) * K * ((R * Q) / 4) := by
          gcongr
      _ = 2 * K * (Q * T * R) := by ring
      _ ≤ 2 * K * (N * N ^ (-ε)) := by rw [← hNε]; gcongr
      _ = 2 * K * N ^ (-ε) * N := by ring
  have hpow : (2 * (1 + |t|) * K / N) ^ K * (rq / 4) ^ K ≤ (2 * K) ^ K * N ^ (-(K * ε)) := by
    rw [← mul_pow]
    calc (2 * (1 + |t|) * K / N * (rq / 4)) ^ K ≤ (2 * K * N ^ (-ε)) ^ K :=
          pow_le_pow_left₀ (by positivity) hfreq K
      _ = (2 * K) ^ K * N ^ (-(K * ε)) := by
          rw [mul_pow, ← Real.rpow_natCast (N ^ (-ε)), ← Real.rpow_mul hN0.le]
          ring_nf
  have hsq : Real.sqrt (2 / N) = Real.sqrt 2 * N ^ (-(1 / 2 : ℝ)) := by
    rw [Real.sqrt_div' 2 hN0.le, Real.sqrt_eq_rpow N, div_eq_mul_inv, ← Real.rpow_neg hN0.le]
  have hNpow : N * (N ^ (-(1 / 2 : ℝ)) * N ^ (-(K * ε))) = N ^ ((1 : ℝ) / 2 - K * ε) := by
    rw [← Real.rpow_add hN0,
      show N * N ^ (-(1 / 2 : ℝ) + -(K * ε)) = N ^ (1 : ℝ) * N ^ (-(1 / 2 : ℝ) + -(K * ε)) by
        rw [Real.rpow_one], ← Real.rpow_add hN0]
    congr 1; ring
  have hA0 : 0 ≤ CF * Real.sqrt (2 / N) := by positivity
  calc (2 * N - N / 2 + K + 1) * (CF * Real.sqrt (2 / N) * (2 * (1 + |t|) * K / N) ^ K) *
        (rq / 4) ^ K
      = (2 * N - N / 2 + K + 1) * (CF * Real.sqrt (2 / N)) *
          ((2 * (1 + |t|) * K / N) ^ K * (rq / 4) ^ K) := by ring
    _ ≤ ((K + 3) * N) * (CF * Real.sqrt (2 / N)) * ((2 * K) ^ K * N ^ (-(K * ε))) := by
        gcongr
    _ = ((K + 3) * CF * Real.sqrt 2 * (2 * K) ^ K) *
          (N * (N ^ (-(1 / 2 : ℝ)) * N ^ (-(K * ε)))) := by rw [hsq]; ring
    _ = _ := by rw [hNpow]

/-- One block: `‖∑_{r ≤ R_j} (μ(r)/φ(r)) ∑_n F_{j,t}(n) c_r(n) χ(n)‖ ≤ √Q C₁ N_j^{3/2 − Kε₃}`. -/
lemma block_bound {K : ℕ} (hK1 : 1 ≤ K) {CF : ℝ} (hCF0 : 0 ≤ CF)
    (hCF : ∀ Q : ℝ, 1 ≤ P.L Q → ∀ (j : ℕ) (t : ℝ), ∀ k ≤ K, ∀ y : ℝ,
      ‖iteratedDeriv k (Fjt P Q j t) y‖ ≤ CF * Real.sqrt (2 / 2 ^ j) * (2 * (1 + |t|) * K / 2 ^ j) ^ k)
    {Q T t : ℝ} (hQ1 : 1 < Q) (hL : 1 ≤ P.L Q) (hT1 : 1 ≤ T) (ht : |t| ≤ 3 * T)
    {q : ℕ} [NeZero q] (hq2 : 2 ≤ q) (hqQ : (q : ℝ) ≤ Q) (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) {j : ℕ} (hRj : 1 ≤ P.Rj Q T j) :
    ‖∑ r ∈ Finset.Icc 1 (P.Rj Q T j), (((μ r : ℝ) / Nat.totient r : ℝ) : ℂ) *
        ∑ n ∈ P.range Q, Fjt P Q j t n * ramanujan r n * χ n‖ ≤
      Real.sqrt Q * ((K + 3) * CF * Real.sqrt 2 * (2 * K) ^ K) *
        ((2 : ℝ) ^ j) ^ ((3 : ℝ) / 2 - K * P.ε₃) := by
  set C₁ : ℝ := (K + 3) * CF * Real.sqrt 2 * (2 * K) ^ K with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hQ0 : 0 < Q := by linarith
  have hQT1 : 1 ≤ Q * T := by nlinarith
  obtain ⟨-, hQTR, hRN⟩ := Rj_facts P hQT1 hRj
  set N : ℝ := (2 : ℝ) ^ j with hN
  set R : ℕ := P.Rj Q T j with hR
  have hN1 : 1 ≤ N := one_le_pow₀ (by norm_num)
  have hN0 : 0 < N := by linarith
  have hinner : ∀ r ∈ Finset.Icc 1 R,
      ‖∑ n ∈ P.range Q, Fjt P Q j t n * ramanujan r n * χ n‖ ≤
        Nat.totient r * (Real.sqrt Q * (C₁ * N ^ ((1 : ℝ) / 2 - K * P.ε₃))) := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hrR : r ≤ R := (Finset.mem_Icc.mp hr).2
    have hbound := sum_F_ramanujan_char_le hq2 χ hprim hr1 (Fjt_contDiff P Q j t K)
      (fun y => hCF Q hL j t K le_rfl y) (a := N / 2) (b := 2 * N) (by positivity)
      (by linarith) (fun y hy => Fjt_supp P Q j t y hy) (P.range Q) (by
        intro n hn
        have hs := Fjt_supp P Q j t n hn
        have hnY : (n : ℝ) ≤ P.Y Q := by
          by_contra hc
          exact hn (Fjt_eq_zero_of_gt P hQ1 j t (not_le.mp hc))
        simp only [PrimeSetup.range, Finset.mem_Icc]
        refine ⟨?_, Nat.le_floor hnY⟩
        have : (1 : ℝ) / 2 ≤ n := le_trans (by linarith) hs.1
        have : (0 : ℝ) < n := by linarith
        exact_mod_cast this)
    refine hbound.trans ?_
    have hφ : (0 : ℝ) ≤ Nat.totient r := Nat.cast_nonneg _
    have hrq : ((r * q : ℕ) : ℝ) ≤ R * Q := by
      push_cast
      exact mul_le_mul (by exact_mod_cast hrR) hqQ (Nat.cast_nonneg _) (by positivity)
    have hX := block_arith (t := t) (T := T) hN1 (by linarith) (by linarith) hK1 hCF0
      (Nat.cast_nonneg _) hrq hQTR
    have hX0 : 0 ≤ (2 * N - N / 2 + K + 1) *
        (CF * Real.sqrt (2 / N) * (2 * (1 + |t|) * K / N) ^ K) * (((r * q : ℕ) : ℝ) / 4) ^ K := by
      have : 0 ≤ 2 * N - N / 2 + K + 1 := by linarith
      positivity
    calc (Nat.totient r : ℝ) * Real.sqrt q * ((2 * N - N / 2 + K + 1) *
          (CF * Real.sqrt (2 / N) * (2 * (1 + |t|) * K / N) ^ K) * (((r * q : ℕ) : ℝ) / 4) ^ K)
        ≤ (Nat.totient r * Real.sqrt Q) * (C₁ * N ^ ((1 : ℝ) / 2 - K * P.ε₃)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hqQ) hφ) hX hX0
            (by positivity)
      _ = _ := by ring
  -- sum over `r`
  have hterm : ∀ r ∈ Finset.Icc 1 R, ‖(((μ r : ℝ) / Nat.totient r : ℝ) : ℂ) *
      ∑ n ∈ P.range Q, Fjt P Q j t n * ramanujan r n * χ n‖ ≤
        Real.sqrt Q * (C₁ * N ^ ((1 : ℝ) / 2 - K * P.ε₃)) := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hφ : (0 : ℝ) < Nat.totient r := by exact_mod_cast Nat.totient_pos.mpr hr1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, Nat.abs_cast]
    have hμ : |(μ r : ℝ)| ≤ 1 := by
      have := ArithmeticFunction.abs_moebius_le_one (n := r)
      exact_mod_cast this
    calc |(μ r : ℝ)| / Nat.totient r * ‖∑ n ∈ P.range Q, Fjt P Q j t n * ramanujan r n * χ n‖
        ≤ 1 / Nat.totient r *
            (Nat.totient r * (Real.sqrt Q * (C₁ * N ^ ((1 : ℝ) / 2 - K * P.ε₃)))) := by
          gcongr
          exact hinner r hr
      _ = _ := by field_simp
  have hsumr := (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at hsumr
  simp only [add_tsub_cancel_right] at hsumr
  refine hsumr.trans ?_
  have h1 : N * N ^ ((1 : ℝ) / 2 - K * P.ε₃) = N ^ ((3 : ℝ) / 2 - K * P.ε₃) := by
    rw [show N * N ^ ((1 : ℝ) / 2 - K * P.ε₃) = N ^ (1 : ℝ) * N ^ ((1 : ℝ) / 2 - K * P.ε₃) by
      rw [Real.rpow_one], ← Real.rpow_add hN0]
    congr 1; ring
  calc (R : ℝ) * (Real.sqrt Q * (C₁ * N ^ ((1 : ℝ) / 2 - K * P.ε₃)))
      ≤ N * (Real.sqrt Q * (C₁ * N ^ ((1 : ℝ) / 2 - K * P.ε₃))) := by gcongr
    _ = Real.sqrt Q * C₁ * (N * N ^ ((1 : ℝ) / 2 - K * P.ε₃)) := by ring
    _ = Real.sqrt Q * C₁ * N ^ ((3 : ℝ) / 2 - K * P.ε₃) := by rw [h1]

/-- The modulus of a family character: `2 ≤ q ≤ Q` for `Q ≥ 2/η`. -/
lemma family_modulus {W : Weight} {Q : ℝ} (hQη : 2 / W.η ≤ Q) {q : ℕ}
    {χ : DirichletCharacter ℂ q} (hχ : InFamily W Q q χ) : 2 ≤ q ∧ (q : ℝ) ≤ Q := by
  have hη := W.η_pos
  have hQ0 : 0 < Q := lt_of_lt_of_le (by positivity) hQη
  have hqsupp := W.supp (q / Q) hχ.2.ne'
  constructor
  · have h1 : W.η * Q ≤ q := by
      have := hqsupp.1; rw [le_div_iff₀ hQ0] at this; linarith
    have h2 : 2 ≤ W.η * Q := by
      rw [div_le_iff₀ hη] at hQη; linarith
    have : (2 : ℝ) ≤ q := by linarith
    exact_mod_cast this
  · have := hqsupp.2; rwa [div_le_one hQ0] at this

/-- **`lem:B1`** (invisibility), proved. -/
theorem lemB1_proof : lemB1_Statement := by
  intro P W A hA
  set K : ℕ := ⌈(A + 4) / P.ε₃⌉₊ + 1 with hKdef
  have hK1 : 1 ≤ K := by omega
  have hKε : A + 4 ≤ K * P.ε₃ := by
    have h1 : (A + 4) / P.ε₃ ≤ ⌈(A + 4) / P.ε₃⌉₊ := Nat.le_ceil _
    have h2 : (⌈(A + 4) / P.ε₃⌉₊ : ℝ) ≤ K := by rw [hKdef]; push_cast; linarith
    have := P.ε₃_pos
    rw [div_le_iff₀ this] at h1
    nlinarith
  obtain ⟨CF, hCF0, hCF⟩ := Fjt_deriv_bound P K hK1
  set C₁ : ℝ := (K + 3) * CF * Real.sqrt 2 * (2 * K) ^ K with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  refine ⟨3 * C₁, max (Real.exp (1 / P.lam)) (max (Real.exp 1) (2 / W.η)), ?_⟩
  intro Q hQ T hT q χ hχ t ht
  have hQL : Real.exp (1 / P.lam) ≤ Q := le_of_max_le_left hQ
  have hQe : Real.exp 1 ≤ Q := le_of_max_le_left (le_of_max_le_right hQ)
  have hQη : 2 / W.η ≤ Q := le_of_max_le_right (le_of_max_le_right hQ)
  have hQ1 : 1 < Q :=
    lt_of_lt_of_le (by have := Real.add_one_lt_exp (x := 1) one_ne_zero; linarith) hQe
  have hQ0 : 0 < Q := by linarith
  have hL := one_le_L P hQL
  have hT1 := one_le_T P hQe hT
  obtain ⟨hq2, hqQ⟩ := family_modulus hQη hχ
  have : NeZero q := ⟨by omega⟩
  have hexp : (3 : ℝ) / 2 - K * P.ε₃ ≤ 0 := by linarith
  have hblock : ∀ j ∈ (P.blocks Q).filter (fun j => 1 ≤ P.Rj Q T j),
      ‖∑ r ∈ Finset.Icc 1 (P.Rj Q T j), (((μ r : ℝ) / Nat.totient r : ℝ) : ℂ) *
          ∑ n ∈ P.range Q, Fjt P Q j t n * ramanujan r n * χ n‖ ≤
        Real.sqrt Q * C₁ * Q ^ ((3 : ℝ) / 2 - K * P.ε₃) := by
    intro j hj
    have hRj := (Finset.mem_filter.mp hj).2
    refine (block_bound P hK1 hCF0 hCF hQ1 hL hT1 ht hq2 hqQ χ hχ.1 hRj).trans ?_
    have hQT1 : 1 ≤ Q * T := by nlinarith
    have hNQ : Q ≤ (2 : ℝ) ^ j := le_trans (by nlinarith) (Rj_facts P hQT1 hRj).1
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hQ0 hNQ hexp) (by positivity)
  rw [Schi_aSharp_eq]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum hblock).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (((P.blocks Q).filter (fun j => 1 ≤ P.Rj Q T j)).card : ℝ) ≤ 3 * Q ^ 2 :=
    le_trans (by exact_mod_cast Finset.card_filter_le _ _) (card_blocks_le P hQ1.le)
  have hsqQ : Real.sqrt Q = Q ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow Q
  have hfin : Q ^ 2 * Real.sqrt Q * Q ^ ((3 : ℝ) / 2 - K * P.ε₃) ≤ Q ^ (-A) := by
    rw [hsqQ, ← Real.rpow_natCast Q 2, ← Real.rpow_add hQ0, ← Real.rpow_add hQ0]
    apply Real.rpow_le_rpow_of_exponent_le hQ1.le
    push_cast; linarith
  calc (((P.blocks Q).filter (fun j => 1 ≤ P.Rj Q T j)).card : ℝ) *
        (Real.sqrt Q * C₁ * Q ^ ((3 : ℝ) / 2 - K * P.ε₃))
      ≤ (3 * Q ^ 2) * (Real.sqrt Q * C₁ * Q ^ ((3 : ℝ) / 2 - K * P.ε₃)) := by gcongr
    _ = 3 * C₁ * (Q ^ 2 * Real.sqrt Q * Q ^ ((3 : ℝ) / 2 - K * P.ε₃)) := by ring
    _ ≤ 3 * C₁ * Q ^ (-A) := by gcongr

end Families.Phase3.C
