/-
**`lem:B2`** (flattened norm), Lemma 5.7, from `PNT_dlVP`.

`∑_n b_n² h(log n) ≤ ∑_j Σ_j` (convexity, `bVec_sq_le`); `Σ_j = M_j + O(h_max(1+ℓ)/(j+1)²)` for `j ≥ 3`
(`block_estimate`, the only place where PNT enters) and `Σ_j ≤ M_j + O(h_max)` for `j ≤ 2`
(`small_block_le`); `∑_j M_j ≤ (1 + (2 log T + 2)/ℓ) ∫ ℓ F_b(s/ℓ) h(s) ds` (`sum_M_le`); and
`(2 log T + 2)/ℓ ≤ δ` for `T ≤ ℓ^{A₀}`, `Q` large.
-/
import Families.Phase3.C.B2Sum
import Families.Phase3.C.B1

noncomputable section

open scoped ContDiff Nat ArithmeticFunction.Moebius
open Set ArithmeticFunction MeasureTheory

namespace Families.Phase3.C

open Families

variable (P : PrimeSetup)

/-- Blocks with `j ≤ 2`: `R_j = 0` and `Σ_j ≤ M_j + 96 C h_max`. -/
lemma small_block_le {Q T : ℝ} (hQ : 4 < Q) (hT : 1 ≤ T) {h : ℝ → ℝ} (hh0 : ∀ y, 0 ≤ h y)
    {CF hmax : ℝ} (hCF : 0 ≤ CF) (hmax0 : 0 ≤ hmax) {j : ℕ} (hj : j ≤ 2)
    (hFj : ∀ y, |Fh P Q h j y| ≤ CF * hmax) :
    ∑ n ∈ P.range Q, Fh P Q h j n * (Λ n - PrimeSetup.LamR (P.Rj Q T j) n) ^ 2 ≤
      ((∫ y, Gh P Q h j y) - Gsum (P.Rj Q T j) * ∫ y, Fh P Q h j y) + 96 * CF * hmax := by
  have hN4 : (2 : ℝ) ^ j ≤ 4 := by
    calc (2 : ℝ) ^ j ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) hj
      _ = 4 := by norm_num
  have hR0 : P.Rj Q T j = 0 := by
    unfold PrimeSetup.Rj
    rw [Nat.floor_eq_zero, div_lt_one (by positivity)]
    have h1 : ((2 : ℝ) ^ j) ^ (1 - P.ε₃) ≤ 2 ^ j := by
      have := Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num) : (1 : ℝ) ≤ 2 ^ j)
        (show 1 - P.ε₃ ≤ 1 by linarith [P.ε₃_pos])
      simpa using this
    nlinarith
  rw [hR0, Gsum_zero, zero_mul, sub_zero]
  simp only [LamR_zero, sub_zero]
  have hlog8 : Real.log 8 < 3 := by
    have : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    rw [this]; linarith [log_two_bounds.2]
  have hX : 0 ≤ CF * hmax := by positivity
  -- `Σ_j ≤ 72 C h_max`
  have hsum : ∑ n ∈ P.range Q, Fh P Q h j n * Λ n ^ 2 ≤ 72 * CF * hmax := by
    have hterm : ∀ n ∈ P.range Q, Fh P Q h j n * Λ n ^ 2 ≤
        (if n ≤ 8 then 9 * CF * hmax else 0) := by
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      by_cases hF : Fh P Q h j n = 0
      · rw [hF, zero_mul]; split_ifs <;> positivity
      · have hs := Fh_supp P Q h j n hF
        have hn8 : n ≤ 8 := by
          have : (n : ℝ) ≤ 8 := by linarith [hs.2]
          exact_mod_cast this
        rw [if_pos hn8]
        have hΛ : Λ n ≤ 3 := ArithmeticFunction.vonMangoldt_le_log.trans
          ((Real.log_le_log (by exact_mod_cast hn1) (by exact_mod_cast hn8)).trans hlog8.le)
        have hΛ0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
        have hF1 : Fh P Q h j n ≤ CF * hmax := (le_abs_self _).trans (hFj n)
        have hF2 : 0 ≤ Fh P Q h j n := Fh_nonneg P Q hh0 j n
        calc Fh P Q h j n * Λ n ^ 2 ≤ (CF * hmax) * 3 ^ 2 := by gcongr
          _ = 9 * CF * hmax := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_filter]
    calc ∑ n ∈ (P.range Q).filter (· ≤ 8), 9 * CF * hmax
        ≤ ∑ n ∈ Finset.Icc 1 8, 9 * CF * hmax :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => by
            obtain ⟨hn1, hn2⟩ := Finset.mem_filter.mp hn
            exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn1).1, hn2⟩)
            (fun _ _ _ => by positivity)
      _ = 72 * CF * hmax := by simp; ring
  -- `M_j = ∫ F_j log ≥ −18 C h_max`
  have hM : -(18 * CF * hmax) ≤ ∫ y, Gh P Q h j y := by
    set N : ℝ := 2 ^ j with hN
    have hN1 : 1 ≤ N := one_le_pow₀ (by norm_num)
    have hint : ∫ y in Icc (N / 2) (2 * N), Gh P Q h j y = ∫ y, Gh P Q h j y :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
        by_contra hne; exact hy (Gh_supp P Q h j y hne)
    have hbd : ∀ y ∈ Icc (N / 2) (2 * N), ‖Gh P Q h j y‖ ≤ CF * hmax * 3 := by
      intro y hy
      have hy0 : 0 < y := lt_of_lt_of_le (by linarith) hy.1
      rw [Gh_eq, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hlog : |Real.log y| ≤ 3 := by
        rw [abs_le]
        constructor
        · have : Real.log (1 / 2) ≤ Real.log y := Real.log_le_log (by norm_num) (by linarith [hy.1])
          have h2 : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
          linarith [log_two_bounds.2]
        · have : Real.log y ≤ Real.log 8 := Real.log_le_log hy0 (by linarith [hy.2])
          linarith
      exact mul_le_mul (hFj y) hlog (abs_nonneg _) hX
    have : ‖∫ y in Icc (N / 2) (2 * N), Gh P Q h j y‖ ≤
        CF * hmax * 3 * volume.real (Icc (N / 2) (2 * N)) :=
      norm_setIntegral_le_of_norm_le_const measure_Icc_lt_top hbd
    rw [hint, Real.norm_eq_abs, Real.volume_real_Icc] at this
    have hlen : max (2 * N - N / 2) 0 ≤ 6 := by
      apply max_le _ (by norm_num); linarith
    have := (abs_le.mp (this.trans (mul_le_mul_of_nonneg_left hlen (by positivity)))).1
    linarith
  linarith

lemma two_pow_le_sq_of_block {Q : ℝ} (hQ : 2 ≤ Q) (hY2 : 2 * P.Y Q ≤ Q ^ 2) {j : ℕ}
    (hj : j ∈ P.blocks Q) : (2 : ℝ) ^ j ≤ Q ^ 2 := by
  unfold PrimeSetup.blocks at hj
  have hjl : j ≤ Nat.log 2 ⌊P.Y Q⌋₊ + 1 := by
    have := Finset.mem_range.mp hj; omega
  calc (2 : ℝ) ^ j ≤ 2 ^ (Nat.log 2 ⌊P.Y Q⌋₊ + 1) := pow_le_pow_right₀ (by norm_num) hjl
    _ = 2 * 2 ^ (Nat.log 2 ⌊P.Y Q⌋₊) := by ring
    _ ≤ Q ^ 2 := by
        rcases Nat.eq_zero_or_pos ⌊P.Y Q⌋₊ with h0 | hpos
        · rw [h0, Nat.log_zero_right, pow_zero]; nlinarith
        · have := Nat.pow_log_le_self 2 (show ⌊P.Y Q⌋₊ ≠ 0 by omega)
          have h1 : (2 : ℝ) ^ (Nat.log 2 ⌊P.Y Q⌋₊) ≤ P.Y Q :=
            (by exact_mod_cast this : ((2 ^ (Nat.log 2 ⌊P.Y Q⌋₊ : ℕ) : ℕ) : ℝ) ≤ ⌊P.Y Q⌋₊).trans
              (Nat.floor_le (Y_pos' P Q).le) |>.trans' (by push_cast; rfl)
          linarith

/-- `2Y ≤ Q²` once `Q^{ε₁} ≥ 2`. -/
lemma two_Y_le {Q : ℝ} (hQ : 1 ≤ Q) (hQε : 2 ≤ Q ^ P.ε₁) : 2 * P.Y Q ≤ Q ^ 2 := by
  have h1 := Y_le_rpow P hQ
  have hQ0 : 0 < Q := by linarith
  have h2 : Q ^ (2 - P.ε₁) * Q ^ P.ε₁ = Q ^ 2 := by
    rw [← Real.rpow_add hQ0]; norm_num
  nlinarith [Real.rpow_nonneg hQ0.le (2 - P.ε₁)]

/-- `(2 log T + 2)/ℓ ≤ δ` for `T ≤ ℓ^{A₀}`, `ℓ ≥ max(1, ((4A₀ + 2)/δ)²)`. -/
lemma slack_le {Q T δ : ℝ} (hδ : 0 < δ) (hT : 1 ≤ T) (hT' : T ≤ Real.log Q ^ P.A0)
    (hℓ : max 1 (((4 * P.A0 + 2) / δ) ^ 2) ≤ Real.log Q) :
    (2 * Real.log T + 2) / Real.log Q ≤ δ := by
  set ℓ := Real.log Q with hℓdef
  have hA0 : 0 < P.A0 := lt_trans P.a0_pos P.a0_lt
  have hℓ1 : 1 ≤ ℓ := le_trans (le_max_left _ _) hℓ
  have hℓ0 : 0 < ℓ := by linarith
  have hlogT : Real.log T ≤ P.A0 * Real.log ℓ := by
    calc Real.log T ≤ Real.log (ℓ ^ P.A0) := Real.log_le_log (by linarith) hT'
      _ = P.A0 * Real.log ℓ := Real.log_rpow hℓ0 _
  have hlogℓ : Real.log ℓ ≤ 2 * Real.sqrt ℓ := by
    have := Real.log_le_rpow_div hℓ0.le (by norm_num : (0 : ℝ) < 1 / 2)
    rw [Real.sqrt_eq_rpow]; linarith
  have hs1 : 1 ≤ Real.sqrt ℓ := by rw [Real.one_le_sqrt]; exact hℓ1
  have hsq : (4 * P.A0 + 2) / δ ≤ Real.sqrt ℓ := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ (4 * P.A0 + 2) / δ)]
    exact Real.sqrt_le_sqrt (le_trans (le_max_right _ _) hℓ)
  have hsl : Real.sqrt ℓ * Real.sqrt ℓ = ℓ := Real.mul_self_sqrt hℓ0.le
  rw [div_le_iff₀ hℓ0]
  have h1 : 2 * Real.log T + 2 ≤ (4 * P.A0 + 2) * Real.sqrt ℓ := by nlinarith
  have h2 : (4 * P.A0 + 2) ≤ δ * Real.sqrt ℓ := by rwa [div_le_iff₀' hδ] at hsq
  have h3 : (4 * P.A0 + 2) * Real.sqrt ℓ ≤ δ * Real.sqrt ℓ * Real.sqrt ℓ :=
    mul_le_mul_of_nonneg_right h2 (by positivity)
  nlinarith

/-- **Why `lemB2_Statement` is parenthesised.** Without parentheses the right-hand side
`(1 + δ) * ∫ s, ell Q * Fb P.ε₃ (s / ell Q) * h s + C * hmax * ell Q` parses as
`(1 + δ) * ∫ s, (ell Q * Fb P.ε₃ (s / ell Q) * h s + C * hmax * ell Q)` (the body of `∫` is parsed at
precedence 60, so it swallows `+`; `∑` does not). For `C · hmax · ell Q ≠ 0` that integrand is not
integrable and the Bochner integral is `0` (`lemB2_rhs_collapse`), so the statement would assert
`∑ b_n² h(log n) ≤ 0`, which is false (e.g. `h(log 2) > 0`, `b_2 = a_2 = log 2/√2`); with `C = 0` it is the
bound without the `O(‖h‖_∞ ℓ)` term, false for `h` a narrow bump at `log 2`. The intended statement is
`lemB2_Statement_fixed` (the same text with the integral parenthesised), proved below. -/
def lemB2_Statement_fixed : Prop :=
  ∀ (P : PrimeSetup) (Cs : ℕ → ℝ) (δ : ℝ), 0 < δ → ∃ C Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
    ∀ T ∈ P.heights Q, ∀ (h : ℝ → ℝ) (hmax : ℝ), ContDiff ℝ ∞ h → (∀ y, 0 ≤ h y) →
      Integrable h → (∀ y, h y ≤ hmax) → (∀ i y, |iteratedDeriv i h y| ≤ Cs i * hmax) →
      ∑ n ∈ P.range Q, P.bVec Q T n ^ 2 * h (Real.log n)
        ≤ (1 + δ) * (∫ s, ell Q * Fb P.ε₃ (s / ell Q) * h s) + C * hmax * ell Q

/-- The right-hand side of `lemB2_Statement` as written collapses: `∫ s, (f s + c) = 0` for `c ≠ 0`,
`f` integrable. -/
lemma lemB2_rhs_collapse {f : ℝ → ℝ} (hf : Integrable f) {c : ℝ} (hc : c ≠ 0) :
    ∫ s, (f s + c) = 0 := by
  apply integral_undef
  intro h
  have hconst : Integrable (fun _ : ℝ => c) :=
    (h.sub hf).congr (Filter.Eventually.of_forall fun s => by simp)
  rw [integrable_const_iff] at hconst
  rcases hconst with h0 | hfin
  · exact hc h0
  · have := hfin.measure_univ_lt_top
    rw [Real.volume_univ] at this
    exact absurd this (lt_irrefl _)

/-- **`lem:B2`** (flattened norm, statement with the integral parenthesised), proved from `PNT_dlVP`. -/
theorem lemB2_proof_fixed (hPNT : PNT_dlVP) : lemB2_Statement_fixed := by
  intro P Cs δ hδ
  obtain ⟨C₀, hC₀⟩ := hPNT
  obtain ⟨Cb, hCb0, hCb⟩ := block_estimate P hC₀ Cs
  obtain ⟨CF, hCF0, hCF⟩ := Fh_deriv_bound P 1 le_rfl Cs
  refine ⟨4 * Cb + 3 * (96 * CF),
    max (max 5 (Real.exp 1)) (max (Real.exp (1 / P.lam))
      (max (2 ^ (1 / P.ε₁)) (Real.exp (max 1 (((4 * P.A0 + 2) / δ) ^ 2))))), ?_⟩
  intro Q hQ T hT h hmax hh hh0 hint hhmax hhd
  have hQ5 : 5 ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hQ
  have hQe : Real.exp 1 ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hQ
  have hQL : Real.exp (1 / P.lam) ≤ Q :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hQ
  have hQε : (2 : ℝ) ^ (1 / P.ε₁) ≤ Q :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hQ
  have hQδ : Real.exp (max 1 (((4 * P.A0 + 2) / δ) ^ 2)) ≤ Q :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hQ
  have hQ1 : 1 < Q := by linarith
  have hQ0 : 0 < Q := by linarith
  have hL := one_le_L P hQL
  have hT1 := one_le_T P hQe hT
  have hmax0 : 0 ≤ hmax := (hh0 0).trans (hhmax 0)
  have hℓ1 : 1 ≤ Real.log Q := by
    have := Real.log_le_log (Real.exp_pos _) hQe; rwa [Real.log_exp] at this
  have hQεpow : 2 ≤ Q ^ P.ε₁ := by
    have := Real.rpow_le_rpow (by positivity) hQε P.ε₁_pos.le
    rwa [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ P.ε₁_pos.ne', Real.rpow_one]
      at this
  have hY2 := two_Y_le P hQ1.le hQεpow
  have hslack : (2 * Real.log T + 2) / Real.log Q ≤ δ := by
    refine slack_le P hδ hT1 hT.2 ?_
    have := Real.log_le_log (Real.exp_pos _) hQδ; rwa [Real.log_exp] at this
  -- convexity
  have hconv : ∑ n ∈ P.range Q, P.bVec Q T n ^ 2 * h (Real.log n) ≤
      ∑ j ∈ P.blocks Q, ∑ n ∈ P.range Q,
        Fh P Q h j n * (Λ n - PrimeSetup.LamR (P.Rj Q T j) n) ^ 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun n hn => bVec_sq_le P hh0 hn
  -- per block
  set Mj : ℕ → ℝ := fun j => (∫ y, Gh P Q h j y) - Gsum (P.Rj Q T j) * ∫ y, Fh P Q h j y
  set Ej : ℕ → ℝ := fun j => Cb * hmax * (1 + Real.log Q) / ((j : ℝ) + 1) ^ 2 +
    (if j ≤ 2 then 96 * CF * hmax else 0)
  have hblock : ∀ j ∈ P.blocks Q, ∑ n ∈ P.range Q,
      Fh P Q h j n * (Λ n - PrimeSetup.LamR (P.Rj Q T j) n) ^ 2 ≤ Mj j + Ej j := by
    intro j hj
    have hE0 : 0 ≤ Cb * hmax * (1 + Real.log Q) / ((j : ℝ) + 1) ^ 2 := by positivity
    by_cases hj3 : 3 ≤ j
    · have := hCb Q T hQ1 hL hT1 h hmax hh hh0 hhmax hhd j hj3
        (two_pow_le_sq_of_block P (by linarith) hY2 hj)
      have h2 : ¬ j ≤ 2 := by omega
      simp only [Mj, Ej, if_neg h2, add_zero]
      linarith [(abs_le.mp this).2]
    · have h2 : j ≤ 2 := by omega
      have hFj : ∀ y, |Fh P Q h j y| ≤ CF * hmax := by
        intro y
        have := hCF Q hL h hmax hh hh0 hhmax hhd j 0 (Nat.zero_le _) y
        simp only [pow_zero, mul_one, Real.norm_eq_abs, iteratedDeriv_zero] at this
        refine this.trans ?_
        rw [div_le_iff₀ (by positivity)]
        have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
        nlinarith [mul_nonneg hCF0 hmax0]
      have := small_block_le P (by linarith) hT1 hh0 hCF0 hmax0 h2 hFj
      simp only [Mj, Ej, if_pos h2]
      linarith
  have hsumM := sum_M_le P hQ1 hT1 hY2 hh hh0 hint
  -- the errors
  have hsumE : ∑ j ∈ P.blocks Q, Ej j ≤ 2 * Cb * hmax * (1 + Real.log Q) + 3 * (96 * CF * hmax) := by
    simp only [Ej, Finset.sum_add_distrib]
    have e1 : ∑ j ∈ P.blocks Q, Cb * hmax * (1 + Real.log Q) / ((j : ℝ) + 1) ^ 2 ≤
        2 * Cb * hmax * (1 + Real.log Q) := by
      have : ∑ j ∈ P.blocks Q, Cb * hmax * (1 + Real.log Q) / ((j : ℝ) + 1) ^ 2 =
          Cb * hmax * (1 + Real.log Q) * ∑ j ∈ P.blocks Q, 1 / ((j : ℝ) + 1) ^ 2 := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
      rw [this]
      have h2 := sum_inv_sq_le_two (Nat.log 2 ⌊P.Y Q⌋₊ + 2)
      unfold PrimeSetup.blocks
      have hX : 0 ≤ Cb * hmax * (1 + Real.log Q) := by positivity
      nlinarith
    have e2 : ∑ j ∈ P.blocks Q, (if j ≤ 2 then 96 * CF * hmax else 0) ≤ 3 * (96 * CF * hmax) := by
      rw [← Finset.sum_filter]
      calc ∑ j ∈ (P.blocks Q).filter (· ≤ 2), 96 * CF * hmax
          ≤ ∑ j ∈ Finset.range 3, 96 * CF * hmax :=
            Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => by
              have := (Finset.mem_filter.mp hj).2
              exact Finset.mem_range.mpr (by omega)) (fun _ _ _ => by positivity)
        _ = 3 * (96 * CF * hmax) := by simp
    linarith
  -- assemble
  have hint0 : 0 ≤ ∫ s, Real.log Q * Fb P.ε₃ (s / Real.log Q) * h s :=
    integral_nonneg fun s => mul_nonneg (mul_nonneg (by linarith)
      (Fb_nonneg _ _ P.ε₃_pos.le)) (hh0 s)
  unfold ell
  calc ∑ n ∈ P.range Q, P.bVec Q T n ^ 2 * h (Real.log n)
      ≤ ∑ j ∈ P.blocks Q, (Mj j + Ej j) := hconv.trans (Finset.sum_le_sum hblock)
    _ = ∑ j ∈ P.blocks Q, Mj j + ∑ j ∈ P.blocks Q, Ej j := Finset.sum_add_distrib
    _ ≤ (1 + (2 * Real.log T + 2) / Real.log Q) *
          (∫ s, Real.log Q * Fb P.ε₃ (s / Real.log Q) * h s) +
        (2 * Cb * hmax * (1 + Real.log Q) + 3 * (96 * CF * hmax)) := add_le_add hsumM hsumE
    _ ≤ (1 + δ) * (∫ s, Real.log Q * Fb P.ε₃ (s / Real.log Q) * h s) +
          (4 * Cb + 3 * (96 * CF)) * hmax * Real.log Q := by
        have h1 : (1 + (2 * Real.log T + 2) / Real.log Q) *
            (∫ s, Real.log Q * Fb P.ε₃ (s / Real.log Q) * h s) ≤
            (1 + δ) * (∫ s, Real.log Q * Fb P.ε₃ (s / Real.log Q) * h s) := by gcongr
        have h2 : 2 * Cb * hmax * (1 + Real.log Q) ≤ 4 * Cb * hmax * Real.log Q := by
          have : 0 ≤ Cb * hmax := by positivity
          nlinarith
        have h3 : 3 * (96 * CF * hmax) ≤ 3 * (96 * CF) * hmax * Real.log Q := by
          have : 0 ≤ CF * hmax := by positivity
          nlinarith
        nlinarith

end Families.Phase3.C
