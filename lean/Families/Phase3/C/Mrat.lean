/-
**`eqB:Mrat`** (display (5.7)) and Step 0 of `prop:TIsharp`
(`lemma-toeplitz-C.tex` `eqC:step0`).

By `lem:M1`, `∑ y_n y_m Δ 𝒦 = ∫ g(u) x_y(u)^*Δ x_y(u) du`. With `a = b + a♯` and
`∑_n x_{a♯}(u)_n χ(n) = ∫_J e^{itu} S_χ[a♯](t) dt` (`sum_xVec_char`), `lem:B1` makes the `a♯`-part
`O(Q^{-A})` for every `χ ∈ 𝓕` and every `u` (`famForm_ab_close`); crude polynomial bounds handle the
rest. Integrating against `g` gives `eqB:Mrat`.
-/
import Families.Phase3.C.B1
import Families.Phase3.C.B2Arith
import Families.M3
import Families.Glue
import Families.Weights

noncomputable section

open scoped ContDiff Nat ArithmeticFunction.Moebius
open Set ArithmeticFunction MeasureTheory

namespace Families.Phase3.C

open Families

variable (P : PrimeSetup)

/-! ### Reindexing `[1, Y] ⊂ ℤ` ↔ `[1, Y] ⊂ ℕ` -/

lemma sum_rangeZ' {M : Type*} [AddCommMonoid M] (Q : ℝ) (F : ℕ → M) :
    ∑ n ∈ P.rangeZ Q, F n.toNat = ∑ k ∈ P.range Q, F k := by
  have hY := (Y_pos' P Q).le
  have hmem : ∀ k : ℕ, k ∈ P.range Q ↔ (k : ℤ) ∈ P.rangeZ Q := by
    intro k
    simp only [PrimeSetup.range, PrimeSetup.rangeZ, Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by exact_mod_cast h1, ?_⟩
      rw [Int.le_floor]; push_cast
      exact (Nat.le_floor_iff hY).mp h2
    · rintro ⟨h1, h2⟩
      refine ⟨by exact_mod_cast h1, ?_⟩
      rw [Nat.le_floor_iff hY]
      rw [Int.le_floor] at h2; push_cast at h2; exact h2
  symm
  refine Finset.sum_bij' (fun (k : ℕ) _ => (k : ℤ)) (fun (n : ℤ) _ => n.toNat) ?_ ?_ ?_ ?_ ?_
  · intro k hk; exact (hmem k).mp hk
  · intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    rw [hmem, Int.toNat_of_nonneg (by omega)]; exact hn
  · intro k _; simp
  · intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    exact Int.toNat_of_nonneg (by omega)
  · intro k _; simp

/-! ### `∑_n x_y(u)_n χ(n) = ∫_J e^{itu} S_χ[y](t) dt` -/

lemma exp_hatJ_split (t u : ℝ) (k : ℕ) (hk : 1 ≤ k) :
    Complex.exp (Complex.I * t * ((u - Real.log k : ℝ) : ℂ)) =
      Complex.exp (Complex.I * t * u) * (k : ℂ) ^ (-(Complex.I * t)) := by
  rw [natCast_cpow' k hk, ← Complex.exp_add]
  congr 1; push_cast; ring

lemma sum_xVec_char {q : ℕ} (χ : DirichletCharacter ℂ q) (Q T : ℝ) (y : ℕ → ℝ) (u : ℝ) :
    ∑ n ∈ P.rangeZ Q, P.xVec Q T y u n * χ n =
      ∫ t in P.J T, Complex.exp (Complex.I * t * u) * P.Schi χ Q y t := by
  have h1 : ∑ n ∈ P.rangeZ Q, P.xVec Q T y u n * χ n =
      ∑ k ∈ P.range Q, ((y k : ℂ) * χ k) * P.hatJ T (u - Real.log k) := by
    rw [← sum_rangeZ' P Q (fun k => ((y k : ℂ) * χ k) * P.hatJ T (u - Real.log k))]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    rw [PrimeSetup.xVec_of_pos P Q T y u hn1]
    have : ((n.toNat : ℕ) : ZMod q) = ((n : ℤ) : ZMod q) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    rw [this]; ring
  rw [h1]
  unfold PrimeSetup.hatJ PrimeSetup.Schi
  have hint : ∀ k ∈ P.range Q, IntegrableOn
      (fun t : ℝ => ((y k : ℂ) * χ k) * Complex.exp (Complex.I * t * ((u - Real.log k : ℝ) : ℂ)))
      (P.J T) := by
    intro k _
    unfold PrimeSetup.J
    exact (by fun_prop : Continuous _).integrableOn_Icc
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ hint]
  refine setIntegral_congr_fun (by unfold PrimeSetup.J; exact measurableSet_Icc) fun t _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  rw [exp_hatJ_split t u k hk1]; ring

lemma volume_J_le {T : ℝ} (hT : 0 ≤ T) : volume.real (P.J T) ≤ T := by
  unfold PrimeSetup.J
  rw [Real.volume_real_Icc]
  apply max_le _ hT
  nlinarith [P.θ_pos]

lemma norm_sum_xVec_char_le_of_Schi {q : ℕ} (χ : DirichletCharacter ℂ q) {Q T : ℝ} (hT : 0 ≤ T)
    (y : ℕ → ℝ) (u : ℝ) {B : ℝ} (hB : ∀ t ∈ P.J T, ‖P.Schi χ Q y t‖ ≤ B) :
    ‖∑ n ∈ P.rangeZ Q, P.xVec Q T y u n * χ n‖ ≤ B * T := by
  rw [sum_xVec_char]
  have hB0 : 0 ≤ B ∨ P.J T = ∅ := by
    by_cases h : (P.J T).Nonempty
    · obtain ⟨t, ht⟩ := h; exact Or.inl ((norm_nonneg _).trans (hB t ht))
    · exact Or.inr (Set.not_nonempty_iff_eq_empty.mp h)
  rcases hB0 with hB0 | hJ
  · have : ‖∫ t in P.J T, Complex.exp (Complex.I * t * u) * P.Schi χ Q y t‖ ≤
        B * volume.real (P.J T) := norm_setIntegral_le_of_norm_le_const
      (by unfold PrimeSetup.J; exact measure_Icc_lt_top) (fun t ht => by
        rw [norm_mul]
        have : ‖Complex.exp (Complex.I * t * u)‖ = 1 := by
          rw [Complex.norm_exp]; simp
        rw [this, one_mul]; exact hB t ht)
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_left (volume_J_le P hT) hB0
  · rw [hJ, Measure.restrict_empty, integral_zero_measure, norm_zero]
    by_cases hB0 : 0 ≤ B
    · positivity
    · exfalso
      -- `J = ∅` only if `T < 0` or `θ ≥ 1/2`; neither happens here
      have : ((1 + P.θ) * T) ∈ P.J T := by
        unfold PrimeSetup.J
        refine ⟨le_rfl, ?_⟩
        nlinarith [P.θ_lt, P.θ_pos]
      rw [hJ] at this; exact this

lemma norm_sum_xVec_char_le {q : ℕ} (χ : DirichletCharacter ℂ q) {Q T : ℝ} (hT : 0 ≤ T)
    (y : ℕ → ℝ) (u : ℝ) :
    ‖∑ n ∈ P.rangeZ Q, P.xVec Q T y u n * χ n‖ ≤ (∑ k ∈ P.range Q, |y k|) * T := by
  refine norm_sum_xVec_char_le_of_Schi P χ hT y u fun t _ => ?_
  unfold PrimeSetup.Schi
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 : ‖χ k‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
  have h2 : ‖(k : ℂ) ^ (-(Complex.I * t))‖ = 1 := by
    rw [natCast_cpow' k hk1, Complex.norm_exp, Complex.re_ofReal_mul]
    simp
  rw [h2, mul_one]
  exact mul_le_of_le_one_right (abs_nonneg _) h1

/-! ### The difference of two family forms -/

lemma norm_add_sq_sub_le (α β : ℂ) :
    |‖α + β‖ ^ 2 - ‖α‖ ^ 2| ≤ ‖β‖ * (2 * ‖α‖ + ‖β‖) := by
  have h1 : ‖α + β‖ ≤ ‖α‖ + ‖β‖ := norm_add_le _ _
  have h2 : ‖α‖ ≤ ‖α + β‖ + ‖β‖ := by
    have := norm_sub_le (α + β) β; simpa using this
  have hα := norm_nonneg α
  have hβ := norm_nonneg β
  have hab := norm_nonneg (α + β)
  rw [abs_le]
  constructor <;> nlinarith

lemma card_primChars_le (q : ℕ) [NeZero q] : ((primChars q).card : ℝ) ≤ Nat.totient q := by
  have h1 : (primChars q).card ≤ Fintype.card (DirichletCharacter ℂ q) :=
    Finset.card_le_univ _
  have h2 : Fintype.card (DirichletCharacter ℂ q) = Nat.totient q := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  exact_mod_cast h1.trans h2.le

/-- `∑_q ω(q) φ*(q) ≤ w_max Q²`, crude. -/
lemma sum_omega_card_le (W : Weight) {Q : ℝ} (hQ : 1 ≤ Q) :
    ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ((primChars q).card : ℝ) ≤ W.wmax * Q ^ 2 := by
  have hterm : ∀ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ((primChars q).card : ℝ) ≤ W.wmax * Q := by
    intro q hq
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hqQ : (q : ℝ) ≤ Q := by
      have := (Finset.mem_Icc.mp hq).2
      exact (Nat.cast_le.mpr this).trans (Nat.floor_le (by linarith))
    have : NeZero q := ⟨by omega⟩
    have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq1
    unfold Weight.omega
    have hwq : 0 ≤ W.wmax * q / Nat.totient q := by
      have := W.wmax_nonneg; positivity
    calc W.w (q / Q) * q / Nat.totient q * ((primChars q).card : ℝ)
        ≤ W.wmax * q / Nat.totient q * ((primChars q).card : ℝ) := by
          gcongr; exact W.le_wmax _
      _ ≤ W.wmax * q / Nat.totient q * Nat.totient q :=
          mul_le_mul_of_nonneg_left (card_primChars_le q) hwq
      _ = W.wmax * q := by field_simp
      _ ≤ W.wmax * Q := mul_le_mul_of_nonneg_left hqQ W.wmax_nonneg
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  simp only [add_tsub_cancel_right]
  have hfl : (⌊Q⌋₊ : ℝ) ≤ Q := Nat.floor_le (by linarith)
  have hw := W.wmax_nonneg
  calc (⌊Q⌋₊ : ℝ) * (W.wmax * Q) ≤ Q * (W.wmax * Q) :=
        mul_le_mul_of_nonneg_right hfl (by positivity)
    _ = W.wmax * Q ^ 2 := by ring

/-- `|x_a^*Δx_a − x_b^*Δx_b| ≤ ∑_q ω(q) ∑_χ |β_χ|(2|α_χ| + |β_χ|)` for `x_a = x_b + x_s`. -/
lemma famForm_sub_abs_le (W : Weight) (Q : ℝ) (I : Finset ℤ) (xb xs : ℤ → ℂ) :
    |famForm W Q I (xb + xs) - famForm W Q I xb| ≤
      ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ χ ∈ primChars q,
        ‖∑ n ∈ I, xs n * χ n‖ * (2 * ‖∑ n ∈ I, xb n * χ n‖ + ‖∑ n ∈ I, xs n * χ n‖) := by
  unfold famForm
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  have hω : 0 ≤ W.omega Q q := by
    unfold Weight.omega
    exact div_nonneg (mul_nonneg (W.nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  rw [← mul_sub, abs_mul, abs_of_nonneg hω, ← Finset.sum_sub_distrib]
  refine mul_le_mul_of_nonneg_left ?_ hω
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun χ _ => ?_)
  have : ∑ n ∈ I, (xb + xs) n * χ n = ∑ n ∈ I, xb n * χ n + ∑ n ∈ I, xs n * χ n := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun n _ => by simp [add_mul]
  rw [this]
  exact norm_add_sq_sub_le _ _

/-! ### Crude polynomial bounds -/

lemma abs_aVec_le (Q : ℝ) (n : ℕ) (hn : 1 ≤ n) : |P.aVec Q n| ≤ Real.log n := by
  unfold PrimeSetup.aVec PrimeSetup.Ups
  have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
  have hΛl := ArithmeticFunction.vonMangoldt_le_log (n := n)
  have hs : 1 ≤ Real.sqrt n := by
    rw [Real.one_le_sqrt]; exact_mod_cast hn
  have hU := P.Υ₀_range (Real.log n / P.L Q)
  rw [abs_mul, abs_div, abs_of_nonneg hΛ, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg hU.1]
  calc Λ n / Real.sqrt n * P.Υ₀ (Real.log n / P.L Q) ≤ Λ n / Real.sqrt n :=
        mul_le_of_le_one_right (div_nonneg hΛ (Real.sqrt_nonneg _)) hU.2
    _ ≤ Λ n := div_le_self hΛ hs
    _ ≤ Real.log n := hΛl

lemma Rj_le_sq {Q T : ℝ} (hQ : 1 ≤ Q) (hQT : 1 ≤ Q * T) {j : ℕ} (hj : j ∈ P.blocks Q) :
    (P.Rj Q T j : ℝ) ≤ 2 * Q ^ 2 := by
  have hN1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have h1 : (P.Rj Q T j : ℝ) ≤ ((2 : ℝ) ^ j) ^ (1 - P.ε₃) / (Q * T) := by
    unfold PrimeSetup.Rj; exact Nat.floor_le (by positivity)
  have h2 : ((2 : ℝ) ^ j) ^ (1 - P.ε₃) / (Q * T) ≤ (2 : ℝ) ^ j := by
    refine (div_le_self (by positivity) hQT).trans ?_
    have := Real.rpow_le_rpow_of_exponent_le hN1 (show 1 - P.ε₃ ≤ 1 by linarith [P.ε₃_pos])
    simpa using this
  have h3 : (2 : ℝ) ^ j ≤ 2 * Q ^ 2 := by
    unfold PrimeSetup.blocks at hj
    have hjl : j ≤ Nat.log 2 ⌊P.Y Q⌋₊ + 1 := by
      have := Finset.mem_range.mp hj; omega
    have hY1 : 1 ≤ ⌊P.Y Q⌋₊ ∨ ⌊P.Y Q⌋₊ = 0 := by omega
    calc (2 : ℝ) ^ j ≤ 2 ^ (Nat.log 2 ⌊P.Y Q⌋₊ + 1) := pow_le_pow_right₀ (by norm_num) hjl
      _ = 2 * 2 ^ (Nat.log 2 ⌊P.Y Q⌋₊) := by ring
      _ ≤ 2 * Q ^ 2 := by
          gcongr
          rcases hY1 with h | h
          · have := Nat.pow_log_le_self 2 (show ⌊P.Y Q⌋₊ ≠ 0 by omega)
            calc (2 : ℝ) ^ (Nat.log 2 ⌊P.Y Q⌋₊) ≤ (⌊P.Y Q⌋₊ : ℝ) := by exact_mod_cast this
              _ ≤ P.Y Q := Nat.floor_le (Y_pos' P Q).le
              _ ≤ Q ^ 2 := Y_le_sq P hQ
          · rw [h, Nat.log_zero_right, pow_zero]; nlinarith
  linarith

/-- `|a♯_n| ≤ 6 C₀ Q⁴` (`C₀ = sup|ψ_j|`), crude. -/
lemma abs_aSharp_le {C₀ : ℝ} (hC₀ : ∀ j y, |P.ψj j y| ≤ C₀) {Q T : ℝ} (hQ : 1 < Q)
    (hQT : 1 ≤ Q * T) (n : ℕ) (hn : 1 ≤ n) : |P.aSharp Q T n| ≤ 6 * C₀ * Q ^ 4 := by
  have hC0 : 0 ≤ C₀ := (abs_nonneg _).trans (hC₀ 0 0)
  unfold PrimeSetup.aSharp
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ j ∈ (P.blocks Q).filter (fun j => 1 ≤ P.Rj Q T j),
      |P.ψj j n * P.Ups Q n / Real.sqrt n * PrimeSetup.LamR (P.Rj Q T j) n| ≤ C₀ * (2 * Q ^ 2) := by
    intro j hj
    have hjb := (Finset.mem_filter.mp hj).1
    have hs : 1 ≤ Real.sqrt n := by rw [Real.one_le_sqrt]; exact_mod_cast hn
    have hU := P.Υ₀_range (Real.log n / P.L Q)
    rw [abs_mul, abs_div, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    unfold PrimeSetup.Ups
    rw [abs_of_nonneg hU.1]
    have e1 : |P.ψj j n| * P.Υ₀ (Real.log n / P.L Q) ≤ C₀ :=
      (mul_le_of_le_one_right (abs_nonneg _) hU.2).trans (hC₀ j n)
    have e2 : |P.ψj j n| * P.Υ₀ (Real.log n / P.L Q) / Real.sqrt n ≤ C₀ :=
      (div_le_self (mul_nonneg (abs_nonneg _) hU.1) hs).trans e1
    have e3 := abs_LamR_le (P.Rj Q T j) n
    calc |P.ψj j n| * P.Υ₀ (Real.log n / P.L Q) / Real.sqrt n * |PrimeSetup.LamR (P.Rj Q T j) n|
        ≤ C₀ * (P.Rj Q T j : ℝ) :=
          mul_le_mul e2 e3 (abs_nonneg _) hC0
      _ ≤ C₀ * (2 * Q ^ 2) := mul_le_mul_of_nonneg_left (Rj_le_sq P hQ.le hQT hjb) hC0
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (((P.blocks Q).filter (fun j => 1 ≤ P.Rj Q T j)).card : ℝ) ≤ 3 * Q ^ 2 :=
    le_trans (by exact_mod_cast Finset.card_filter_le _ _) (card_blocks_le P hQ.le)
  calc (((P.blocks Q).filter (fun j => 1 ≤ P.Rj Q T j)).card : ℝ) * (C₀ * (2 * Q ^ 2))
      ≤ (3 * Q ^ 2) * (C₀ * (2 * Q ^ 2)) := by gcongr
    _ = 6 * C₀ * Q ^ 4 := by ring

lemma sum_abs_range_le {Q : ℝ} (hQ : 1 ≤ Q) {f : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ n ∈ P.range Q, |f n| ≤ B) : ∑ n ∈ P.range Q, |f n| ≤ Q ^ 2 * B := by
  refine (Finset.sum_le_sum hf).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  unfold PrimeSetup.range
  rw [Nat.card_Icc]
  simp only [add_tsub_cancel_right]
  have : (⌊P.Y Q⌋₊ : ℝ) ≤ Q ^ 2 := (Nat.floor_le (Y_pos' P Q).le).trans (Y_le_sq P hQ)
  exact mul_le_mul_of_nonneg_right this hB

/-- `‖b‖₁ ≤ c Q⁶` (crude). -/
lemma sum_abs_bVec_le : ∃ c : ℝ, 0 ≤ c ∧ ∀ Q T : ℝ, 1 < Q → 1 ≤ Q * T →
    ∑ n ∈ P.range Q, |P.bVec Q T n| ≤ c * Q ^ 6 := by
  obtain ⟨C₀, hC₀⟩ := P.ψj_deriv 0
  have hC : ∀ j y, |P.ψj j y| ≤ |C₀| := fun j y => by
    have := hC₀ j y; simp at this; exact this.trans (le_abs_self _)
  refine ⟨1 + 6 * |C₀|, by positivity, fun Q T hQ hQT => ?_⟩
  refine (sum_abs_range_le P hQ.le (B := (1 + 6 * |C₀|) * Q ^ 4) (by positivity)
    fun n hn => ?_).trans
    (le_of_eq (by ring))
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnY : (n : ℝ) ≤ Q ^ 2 := by
    have := (Finset.mem_Icc.mp hn).2
    exact (Nat.cast_le.mpr this).trans ((Nat.floor_le (Y_pos' P Q).le).trans (Y_le_sq P hQ.le))
  unfold PrimeSetup.bVec
  have h1 := abs_aVec_le P Q n hn1
  have h2 := abs_aSharp_le P hC hQ hQT n hn1
  have hlog : Real.log n ≤ Q ^ 4 := by
    have : Real.log n ≤ n := (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
    have hQ4 : Q ^ 2 ≤ Q ^ 4 := pow_le_pow_right₀ hQ.le (by norm_num)
    linarith
  calc |P.aVec Q n - P.aSharp Q T n| ≤ |P.aVec Q n| + |P.aSharp Q T n| := abs_sub _ _
    _ ≤ Q ^ 4 + 6 * |C₀| * Q ^ 4 := by linarith
    _ = (1 + 6 * |C₀|) * Q ^ 4 := by ring

/-- `T ≤ A₀^{A₀} Q` on the admissible heights. -/
lemma T_le_Q {Q T : ℝ} (hQ : 1 ≤ Q) (hT : T ∈ P.heights Q) : T ≤ P.A0 ^ P.A0 * Q := by
  have hA0 : 0 < P.A0 := lt_trans P.a0_pos P.a0_lt
  have hQ0 : 0 < Q := by linarith
  have hlog0 : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have h1 : Real.log Q ≤ Q ^ (1 / P.A0) / (1 / P.A0) :=
    Real.log_le_rpow_div hQ0.le (by positivity)
  have h2 : Real.log Q ^ P.A0 ≤ (Q ^ (1 / P.A0) / (1 / P.A0)) ^ P.A0 :=
    Real.rpow_le_rpow hlog0 h1 hA0.le
  have h3 : (Q ^ (1 / P.A0) / (1 / P.A0)) ^ P.A0 = P.A0 ^ P.A0 * Q := by
    rw [div_eq_mul_inv, one_div, inv_inv, Real.mul_rpow (by positivity) hA0.le,
      ← Real.rpow_mul hQ0.le, inv_mul_cancel₀ hA0.ne', Real.rpow_one]
    ring
  linarith [hT.2]

lemma final_arith {Q T A w cb c' CB' x : ℝ} (hQ1 : 1 ≤ Q) (hT0 : 0 ≤ T) (hTc : T ≤ c' * Q)
    (hw : 0 ≤ w) (hcb : 0 ≤ cb) (hc' : 0 ≤ c') (hCB : 0 ≤ CB') (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hxQ : x * Q ^ 20 ≤ Q ^ (-A)) :
    w * Q ^ 2 * (CB' * x * T * (2 * (cb * Q ^ 6 * T) + CB' * x * T)) ≤
      w * (c' * CB') * (2 * cb * c' + c' * CB') * Q ^ (-A) := by
  have hQ0 : 0 ≤ Q := by linarith
  have hQ7 : Q ≤ Q ^ 7 := by
    calc Q = Q ^ 1 := (pow_one Q).symm
      _ ≤ Q ^ 7 := pow_le_pow_right₀ hQ1 (by norm_num)
  have hQ10 : Q ^ 10 ≤ Q ^ 20 := pow_le_pow_right₀ hQ1 (by norm_num)
  have hK : 0 ≤ w * (c' * CB') * (2 * cb * c' + c' * CB') := by positivity
  calc w * Q ^ 2 * (CB' * x * T * (2 * (cb * Q ^ 6 * T) + CB' * x * T))
      ≤ w * Q ^ 2 * (CB' * x * (c' * Q) * (2 * (cb * Q ^ 6 * (c' * Q)) + CB' * 1 * (c' * Q))) := by
        gcongr
    _ = w * (c' * CB') * x * Q ^ 3 * (2 * cb * c' * Q ^ 7 + c' * CB' * Q) := by ring
    _ ≤ w * (c' * CB') * x * Q ^ 3 * (2 * cb * c' * Q ^ 7 + c' * CB' * Q ^ 7) := by gcongr
    _ = w * (c' * CB') * (2 * cb * c' + c' * CB') * (x * Q ^ 10) := by ring
    _ ≤ w * (c' * CB') * (2 * cb * c' + c' * CB') * (x * Q ^ 20) := by gcongr
    _ ≤ w * (c' * CB') * (2 * cb * c' + c' * CB') * Q ^ (-A) :=
        mul_le_mul_of_nonneg_left hxQ hK

/-! ### Step 0: `x_a^*Δx_a` and `x_b^*Δx_b` agree up to `O(Q^{-A})`, for every `u` -/

theorem famForm_ab_close (W : Weight) (A : ℝ) (hA : 0 < A) :
    ∃ C Q₀ : ℝ, 0 ≤ C ∧ ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ P.heights Q, ∀ u : ℝ,
      |famForm W Q (P.rangeZ Q) (P.xVec Q T (P.aVec Q) u) -
        famForm W Q (P.rangeZ Q) (P.xVec Q T (P.bVec Q T) u)| ≤ C * Q ^ (-A) := by
  obtain ⟨CB, QB, hB1⟩ := lemB1_proof P W (A + 20) (by linarith)
  obtain ⟨cb, hcb0, hcb⟩ := sum_abs_bVec_le P
  set c' : ℝ := P.A0 ^ P.A0 with hc'
  have hc'0 : 0 ≤ c' := Real.rpow_nonneg (lt_trans P.a0_pos P.a0_lt).le _
  set CB' : ℝ := max CB 1 with hCB'
  refine ⟨W.wmax * (c' * CB') * (2 * cb * c' + c' * CB'), max QB (Real.exp 1), by
    have := W.wmax_nonneg; positivity, ?_⟩
  intro Q hQ T hT u
  have hQB : QB ≤ Q := le_of_max_le_left hQ
  have hQe : Real.exp 1 ≤ Q := le_of_max_le_right hQ
  have hQ1 : 1 < Q :=
    lt_of_lt_of_le (by have := Real.add_one_lt_exp (x := 1) one_ne_zero; linarith) hQe
  have hQ0 : 0 < Q := by linarith
  have hT1 := one_le_T P hQe hT
  have hT0 : 0 ≤ T := by linarith
  have hQT : 1 ≤ Q * T := by nlinarith
  have hTQ := T_le_Q P hQ1.le hT
  -- `x_a = x_b + x_♯`
  have hsplit : P.xVec Q T (P.aVec Q) u = P.xVec Q T (P.bVec Q T) u + P.xVec Q T (P.aSharp Q T) u := by
    funext n
    simp only [PrimeSetup.xVec, Pi.add_apply, PrimeSetup.bVec]
    split_ifs
    · push_cast; ring
    · simp
  rw [hsplit]
  refine (famForm_sub_abs_le W Q _ _ _).trans ?_
  -- bounds for the two character sums
  have hQA : Q ^ (-(A + 20)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hQ1.le (by linarith)
  have hβ : ∀ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∀ χ ∈ primChars q, W.omega Q q ≠ 0 →
      ‖∑ n ∈ P.rangeZ Q, P.xVec Q T (P.aSharp Q T) u n * χ n‖ ≤ CB' * Q ^ (-(A + 20)) * T := by
    intro q _ χ hχ hω
    have hw : 0 < W.w (q / Q) := by
      have := W.nonneg (q / Q)
      rcases this.lt_or_eq with h | h
      · exact h
      · exfalso; apply hω; unfold Weight.omega; rw [← h]; simp
    have hfam : InFamily W Q q χ := ⟨mem_primChars.mp hχ, hw⟩
    refine norm_sum_xVec_char_le_of_Schi P χ hT0 _ u fun t ht => ?_
    have htT : |t| ≤ 3 * T := by
      unfold PrimeSetup.J at ht
      rw [abs_le]
      constructor <;> nlinarith [ht.1, ht.2, P.θ_pos, P.θ_lt]
    exact (hB1 Q hQB T hT q χ hfam t htT).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  have hα : ∀ q (χ : DirichletCharacter ℂ q),
      ‖∑ n ∈ P.rangeZ Q, P.xVec Q T (P.bVec Q T) u n * χ n‖ ≤ cb * Q ^ 6 * T := by
    intro q χ
    exact (norm_sum_xVec_char_le P χ hT0 _ u).trans
      (mul_le_mul_of_nonneg_right (hcb Q T hQ1 hQT) hT0)
  have hCB'1 : 1 ≤ CB' := le_max_right _ _
  -- the bracket, uniformly
  set E : ℝ := CB' * Q ^ (-(A + 20)) * T * (2 * (cb * Q ^ 6 * T) + CB' * Q ^ (-(A + 20)) * T) with hE
  have hterm : ∀ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ χ ∈ primChars q,
        ‖∑ n ∈ P.rangeZ Q, P.xVec Q T (P.aSharp Q T) u n * χ n‖ *
          (2 * ‖∑ n ∈ P.rangeZ Q, P.xVec Q T (P.bVec Q T) u n * χ n‖ +
            ‖∑ n ∈ P.rangeZ Q, P.xVec Q T (P.aSharp Q T) u n * χ n‖) ≤
      W.omega Q q * ((primChars q).card : ℝ) * E := by
    intro q hq
    have hω : 0 ≤ W.omega Q q := by
      unfold Weight.omega
      exact div_nonneg (mul_nonneg (W.nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    rcases hω.lt_or_eq with hω | hω
    · rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hω.le
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum fun χ hχ => ?_
      have hb := hβ q hq χ hχ hω.ne'
      have ha := hα q χ
      have h0 : 0 ≤ ‖∑ n ∈ P.rangeZ Q, P.xVec Q T (P.aSharp Q T) u n * χ n‖ := norm_nonneg _
      rw [hE]
      gcongr
    · rw [← hω]; simp
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  refine (mul_le_mul_of_nonneg_right (sum_omega_card_le W hQ1.le) hE0).trans ?_
  -- final arithmetic: `w_max Q² · E ≤ C Q^{-A}`
  have hQpow : Q ^ (-(A + 20)) * Q ^ 20 ≤ Q ^ (-A) := by
    rw [← Real.rpow_natCast Q 20, ← Real.rpow_add hQ0]; push_cast
    exact Real.rpow_le_rpow_of_exponent_le hQ1.le (by linarith)
  exact final_arith hQ1.le hT0 hTQ W.wmax_nonneg hcb0 hc'0 (by linarith)
    (Real.rpow_nonneg hQ0.le _) hQA hQpow

/-! ### Integrability and `eqB:Mrat` -/

lemma continuous_famForm_xVec (W : Weight) (Q T : ℝ) (I : Finset ℤ) (y : ℕ → ℝ) :
    Continuous (fun u => famForm W Q I (P.xVec Q T y u)) := by
  unfold famForm
  refine continuous_finsetSum _ fun q _ => continuous_const.mul
    (continuous_finsetSum _ fun χ _ => ?_)
  refine (continuous_norm.comp (continuous_finsetSum _ fun n _ => ?_)).pow 2
  refine Continuous.mul ?_ continuous_const
  unfold PrimeSetup.xVec
  split_ifs
  · exact continuous_const.mul ((P.hatJ_continuous T).comp (continuous_id.sub continuous_const))
  · exact continuous_const

lemma famForm_xVec_le (W : Weight) (Q T : ℝ) (I : Finset ℤ) (y : ℕ → ℝ) (u : ℝ) :
    famForm W Q I (P.xVec Q T y u) ≤
      ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ _χ ∈ primChars q,
        (∑ n ∈ I, |y n.toNat| * volume.real (P.J T)) ^ 2 := by
  unfold famForm
  refine Finset.sum_le_sum fun q _ => ?_
  have hω : 0 ≤ W.omega Q q := by
    unfold Weight.omega
    exact div_nonneg (mul_nonneg (W.nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun χ _ => ?_) hω
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [norm_mul]
  have h1 : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
  have h2 : ‖P.xVec Q T y u n‖ ≤ |y n.toNat| * volume.real (P.J T) := by
    unfold PrimeSetup.xVec
    split_ifs
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (P.hatJ_norm_le T _) (abs_nonneg _)
    · rw [norm_zero]; exact mul_nonneg (abs_nonneg _) measureReal_nonneg
  calc ‖P.xVec Q T y u n‖ * ‖χ n‖ ≤ ‖P.xVec Q T y u n‖ * 1 :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ ≤ _ := by rw [mul_one]; exact h2

lemma famForm_nonneg' (W : Weight) (Q : ℝ) (I : Finset ℤ) (x : ℤ → ℂ) : 0 ≤ famForm W Q I x := by
  unfold famForm
  refine Finset.sum_nonneg fun q _ => mul_nonneg ?_ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  unfold Weight.omega
  exact div_nonneg (mul_nonneg (W.nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

lemma integrable_g_famForm {Q : ℝ} (hQ : 1 < Q) (W : Weight) (T : ℝ) (y : ℕ → ℝ) :
    Integrable (fun u => P.g Q u * famForm W Q (P.rangeZ Q) (P.xVec Q T y u)) := by
  refine (P.g_integrable hQ).mul_bdd (c := ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q *
      ∑ χ ∈ primChars q, (∑ n ∈ P.rangeZ Q, |y n.toNat| * volume.real (P.J T)) ^ 2)
    (continuous_famForm_xVec P W Q T _ y).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (famForm_nonneg' W Q _ _)]
  exact famForm_xVec_le P W Q T _ y u

/-- `Re ∑ y_n y_m Δ 𝒦 = ∫ g(u) x_y(u)^*Δ x_y(u) du` (real form of `lem:M1`). -/
lemma ratioForm_re_eq {Q : ℝ} (hQ : 1 < Q) (W : Weight) (T : ℝ) (y : ℕ → ℝ) :
    (P.ratioForm W Q T y).re = ∫ u, P.g Q u * famForm W Q (P.rangeZ Q) (P.xVec Q T y u) := by
  rw [P.ratioForm_factorisation hQ W y]
  have : (fun u => (P.g Q u : ℂ) * (famForm W Q (P.rangeZ Q) (P.xVec Q T y u) : ℂ)) =
      fun u => ((P.g Q u * famForm W Q (P.rangeZ Q) (P.xVec Q T y u) : ℝ) : ℂ) := by
    funext u; push_cast; ring
  rw [this, integral_complex_ofReal, Complex.ofReal_re]

lemma ratioForm_eq_ofReal {Q : ℝ} (hQ : 1 < Q) (W : Weight) (T : ℝ) (y : ℕ → ℝ) :
    P.ratioForm W Q T y = ((∫ u, P.g Q u * famForm W Q (P.rangeZ Q) (P.xVec Q T y u) : ℝ) : ℂ) := by
  rw [P.ratioForm_factorisation hQ W y, ← integral_complex_ofReal]
  congr 1; funext u; push_cast; ring

/-- `∫ g = (L ∫ψ²)²`. -/
lemma integral_g {Q : ℝ} (hQ : 1 < Q) : ∫ u, P.g Q u = (P.L Q * P.aInt) ^ 2 := by
  have hconv : P.g Q = convolution (P.FR Q) (P.FR Q) (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext u; exact P.g_eq_conv Q u
  rw [hconv, integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) (P.FR_integrable hQ)
    (P.FR_integrable hQ)]
  have hFR : ∫ u, P.FR Q u = P.L Q * P.aInt := by
    have hL := L_pos' P hQ
    have := Measure.integral_comp_div (fun t => P.vfun t) (P.L Q)
    simp only [smul_eq_mul, abs_of_pos hL] at this
    rw [PrimeSetup.aInt, ← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [PrimeSetup.FR, PrimeSetup.vfun, PrimeSetup.ψL]
  rw [hFR]
  simp [sq]

/-- **`eqB:Mrat`**, proved (from `lem:B1` and `lem:M1`). -/
theorem eqBMrat_proof : eqBMrat_Statement := by
  intro P W A hA
  obtain ⟨C, Q₀, hC0, hclose⟩ := famForm_ab_close P W (A + 2) (by linarith)
  refine ⟨C * (P.lam * P.aInt) ^ 2, max Q₀ (Real.exp 1), ?_⟩
  intro Q hQ T hT
  have hQ₀ : Q₀ ≤ Q := le_of_max_le_left hQ
  have hQe : Real.exp 1 ≤ Q := le_of_max_le_right hQ
  have hQ1 : 1 < Q :=
    lt_of_lt_of_le (by have := Real.add_one_lt_exp (x := 1) one_ne_zero; linarith) hQe
  have hQ0 : 0 < Q := by linarith
  rw [ratioForm_eq_ofReal P hQ1 W T, ratioForm_eq_ofReal P hQ1 W T, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs,
    ← integral_sub (integrable_g_famForm P hQ1 W T _) (integrable_g_famForm P hQ1 W T _)]
  have hbound : ∀ u, ‖P.g Q u * famForm W Q (P.rangeZ Q) (P.xVec Q T (P.aVec Q) u) -
      P.g Q u * famForm W Q (P.rangeZ Q) (P.xVec Q T (P.bVec Q T) u)‖ ≤
        P.g Q u * (C * Q ^ (-(A + 2))) := by
    intro u
    rw [← mul_sub, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (P.g_nonneg Q u)]
    exact mul_le_mul_of_nonneg_left (hclose Q hQ₀ T hT u) (P.g_nonneg Q u)
  have hint : Integrable (fun u => P.g Q u * (C * Q ^ (-(A + 2)))) :=
    (P.g_integrable hQ1).mul_const _
  refine (norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hbound)).trans ?_
  rw [integral_mul_const, integral_g P hQ1]
  -- `(L a)² · C Q^{-(A+2)} ≤ C (λ a)² Q^{-A}` since `L = λ log Q ≤ λ Q`
  have hlog : Real.log Q ≤ Q := (Real.log_le_sub_one_of_pos hQ0).trans (by linarith)
  have hlog0 : 0 ≤ Real.log Q := Real.log_nonneg hQ1.le
  have ha0 : 0 ≤ P.aInt := integral_nonneg fun s => sq_nonneg _
  have hLQ : P.L Q * P.aInt ≤ P.lam * P.aInt * Q := by
    unfold PrimeSetup.L
    have := P.lam_pos
    calc P.lam * Real.log Q * P.aInt ≤ P.lam * Q * P.aInt := by gcongr
      _ = P.lam * P.aInt * Q := by ring
  have hL0 : 0 ≤ P.L Q * P.aInt := mul_nonneg (L_pos' P hQ1).le ha0
  have hpow : Q ^ 2 * Q ^ (-(A + 2)) = Q ^ (-A) := by
    rw [← Real.rpow_natCast Q 2, ← Real.rpow_add hQ0]; congr 1; push_cast; ring
  calc (P.L Q * P.aInt) ^ 2 * (C * Q ^ (-(A + 2)))
      ≤ (P.lam * P.aInt * Q) ^ 2 * (C * Q ^ (-(A + 2))) := by
        gcongr
    _ = C * (P.lam * P.aInt) ^ 2 * (Q ^ 2 * Q ^ (-(A + 2))) := by ring
    _ = C * (P.lam * P.aInt) ^ 2 * Q ^ (-A) := by rw [hpow]

end Families.Phase3.C
