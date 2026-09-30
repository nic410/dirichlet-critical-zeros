/-
# Zero side: the family first moment (`lem:firstmoment`) and the prime part of the trace

* `norm_sum_primChars_le`: `|∑*_{χ mod q} χ(n)| ≤ ∑_{d | q, d | n−1} φ(d)` (IK (3.9), in the repo as
  `Families.sum_primChars_eq`).
* `first_moment`: `|∑_{q ≤ Q} ω(q) ∑*_χ χ(n)| ≤ 2 w_max Q τ(n−1)` for `n ≥ 2` (`lem:firstmoment`).
* `sum_divisors_div_sqrt_le`: `∑_{2 ≤ n ≤ N} τ(n−1)/√n ≤ 2√N (1 + log N)`.
* `Pch`: the sharp prime part `P_χ(t) = −(1/π) Re ∑_{n ≤ X} Λ(n) χ(n) n^{−1/2−it}` (`zeta23`'s `PXc`),
  and `abs_famSum_Pch_le`: `|∑_χ ω_χ P_χ(t)| ≤ (4/π) w_max Q √X log X (1 + log X)` for all `t`.
-/
import Families.Ported.Zero.Bridge
import Families.Toeplitz
import Families.Schur
import Families.Weights

noncomputable section

open scoped BigOperators ComplexConjugate ArithmeticFunction.Moebius
open Complex Set Finset

namespace Families.Ported.Zero

open Zeta23 Zeta23.ThmE

/-- `|∑*_{χ mod q} χ(n)| ≤ ∑_{d | q, d | n−1} φ(d)` for `n ≥ 1`. -/
lemma norm_sum_primChars_le (q : ℕ) (hq : 0 < q) (n : ℕ) (hn : 1 ≤ n) :
    ‖∑ χ ∈ primChars q, χ (n : ZMod q)‖ ≤
      ∑ d ∈ q.divisors.filter (fun d => d ∣ n - 1), (Nat.totient d : ℝ) := by
  by_cases hcop : IsCoprime (n : ℤ) q
  · have h := sum_primChars_eq q hq (n : ℤ) 1 hcop isCoprime_one_left
    simp only [Int.cast_one, map_one, mul_one, Int.cast_natCast] at h
    rw [h]
    refine (norm_sum_le _ _).trans ?_
    have hfilt : q.divisors.filter (fun d : ℕ => ((d : ℕ) : ℤ) ∣ (n : ℤ) - 1) =
        q.divisors.filter (fun d => d ∣ n - 1) := by
      refine Finset.filter_congr fun d _ => ?_
      rw [show ((n : ℤ) - 1) = ((n - 1 : ℕ) : ℤ) by push_cast [Nat.cast_sub hn]; ring]
      exact Int.natCast_dvd_natCast
    rw [hfilt]
    refine Finset.sum_le_sum fun d _ => ?_
    rw [norm_mul]
    have hμ : ‖((μ (q / d) : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have : ‖((Nat.totient d : ℕ) : ℂ)‖ = (Nat.totient d : ℝ) := by
      rw [Complex.norm_natCast]
    rw [this]
    nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.totient d), norm_nonneg ((μ (q / d) : ℤ) : ℂ)]
  · have h := sum_primChars_eq_zero_of_not_coprime q (n : ℤ) 1 (by simpa using hcop)
    simp only [Int.cast_one, map_one, mul_one, Int.cast_natCast] at h
    rw [h, norm_zero]
    exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

/-- **`lem:firstmoment`**: `|∑_{q ≤ Q} ω(q) ∑*_{χ mod q} χ(n)| ≤ 2 w_max Q τ(n−1)` for `n ≥ 2`. -/
theorem first_moment (W : Weight) {Q : ℝ} (hQ : 1 ≤ Q) (n : ℕ) (hn : 2 ≤ n) :
    ‖∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (W.omega Q q : ℂ) * ∑ χ ∈ primChars q, χ (n : ZMod q)‖ ≤
      2 * W.wmax * Q * ((n - 1).divisors.card : ℝ) := by
  set N := ⌊Q⌋₊
  have hNQ : (N : ℝ) ≤ Q := Nat.floor_le (by linarith)
  have hwm := W.wmax_nonneg
  have hω : ∀ q, W.omega Q q ≤ W.wmax * ((q : ℝ) / Nat.totient q) := by
    intro q
    unfold Weight.omega
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (W.le_wmax _) (by positivity)
  have hω0 : ∀ q, 0 ≤ W.omega Q q := by
    intro q; unfold Weight.omega
    exact div_nonneg (mul_nonneg (W.nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  calc ‖∑ q ∈ Finset.Icc 1 N, (W.omega Q q : ℂ) * ∑ χ ∈ primChars q, χ (n : ZMod q)‖
      ≤ ∑ q ∈ Finset.Icc 1 N, W.omega Q q *
          ∑ d ∈ q.divisors.filter (fun d => d ∣ n - 1), (Nat.totient d : ℝ) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q hq => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hω0 q)]
        exact mul_le_mul_of_nonneg_left
          (norm_sum_primChars_le q (Finset.mem_Icc.mp hq).1 n (by omega)) (hω0 q)
    _ ≤ ∑ q ∈ Finset.Icc 1 N, W.wmax * ((q : ℝ) / Nat.totient q) *
          ∑ d ∈ q.divisors.filter (fun d => d ∣ n - 1), (Nat.totient d : ℝ) :=
        Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_right (hω q)
          (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
    _ = W.wmax * ∑ d ∈ (n - 1).divisors, (Nat.totient d : ℝ) *
          ∑ q ∈ (Finset.Icc 1 N).filter (fun q => d ∣ q), (q : ℝ) / Nat.totient q := by
        rw [Finset.mul_sum]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm' (t' := (n - 1).divisors)
          (s' := fun d => (Finset.Icc 1 N).filter (fun q => d ∣ q))]
        · refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun q _ => ?_
          ring
        · intro q d
          simp only [Finset.mem_Icc, Finset.mem_filter, Nat.mem_divisors]
          constructor
          · rintro ⟨⟨h1, h2⟩, ⟨hdq, hq0⟩, hdn⟩
            exact ⟨⟨⟨h1, h2⟩, hdq⟩, hdn, by omega⟩
          · rintro ⟨⟨⟨h1, h2⟩, hdq⟩, hdn, _⟩
            exact ⟨⟨h1, h2⟩, ⟨hdq, by omega⟩, hdn⟩
    _ ≤ W.wmax * ∑ d ∈ (n - 1).divisors, 2 * Q := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun d hd => ?_) hwm
        have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
        exact (sum_multiples_div_totient_le N d hd0).trans (by linarith)
    _ = 2 * W.wmax * Q * ((n - 1).divisors.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- `∑_{j ≤ M} 1/√j ≤ 2√M`. -/
lemma sum_inv_sqrt_le (M : ℕ) : ∑ j ∈ Finset.Icc 1 M, 1 / Real.sqrt j ≤ 2 * Real.sqrt M := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.cast_succ]
    have h1 : 1 / Real.sqrt (M + 1) ≤ 2 * (Real.sqrt (M + 1) - Real.sqrt M) := by
      have hs : 0 < Real.sqrt (M + 1) := Real.sqrt_pos.mpr (by positivity)
      have hs0 : 0 ≤ Real.sqrt M := Real.sqrt_nonneg _
      have hle : Real.sqrt M ≤ Real.sqrt (M + 1) := Real.sqrt_le_sqrt (by linarith)
      have hsq : Real.sqrt (M + 1) ^ 2 = M + 1 := Real.sq_sqrt (by positivity)
      have hsq0 : Real.sqrt M ^ 2 = M := Real.sq_sqrt (by positivity)
      rw [div_le_iff₀ hs]
      nlinarith
    linarith

/-- `∑_{m ≤ N} τ(m)/√m ≤ 2√N (1 + log N)`. -/
lemma sum_card_divisors_div_sqrt_le (N : ℕ) :
    ∑ m ∈ Finset.Icc 1 N, ((m.divisors.card : ℕ) : ℝ) / Real.sqrt m ≤
      2 * Real.sqrt N * (1 + Real.log N) := by
  -- swap: ∑_{m ≤ N} ∑_{d | m} 1/√m = ∑_{d ≤ N} ∑_{j ≤ N/d} 1/√(dj)
  have hswap : ∑ m ∈ Finset.Icc 1 N, ((m.divisors.card : ℕ) : ℝ) / Real.sqrt m =
      ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ (Finset.Icc 1 N).filter (fun m => d ∣ m), 1 / Real.sqrt m := by
    have h1 : ∀ m : ℕ, ((m.divisors.card : ℕ) : ℝ) / Real.sqrt m = ∑ d ∈ m.divisors, 1 / Real.sqrt m := by
      intro m; rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
    simp_rw [h1]
    rw [Finset.sum_comm' (t' := Finset.Icc 1 N)
      (s' := fun d => (Finset.Icc 1 N).filter (fun m => d ∣ m))]
    intro m d
    simp only [Finset.mem_Icc, Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, h2⟩, hdm, hm0⟩
      exact ⟨⟨⟨h1, h2⟩, hdm⟩, Nat.pos_of_dvd_of_pos hdm (by omega),
        (Nat.le_of_dvd (by omega) hdm).trans h2⟩
    · rintro ⟨⟨⟨h1, h2⟩, hdm⟩, _, _⟩
      exact ⟨⟨h1, h2⟩, hdm, by omega⟩
  rw [hswap]
  have hinner : ∀ d ∈ Finset.Icc 1 N,
      ∑ m ∈ (Finset.Icc 1 N).filter (fun m => d ∣ m), 1 / Real.sqrt m ≤ 2 * Real.sqrt N / d := by
    intro d hd
    have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
    have hbij : ∑ m ∈ (Finset.Icc 1 N).filter (fun m => d ∣ m), 1 / Real.sqrt m
        = ∑ j ∈ Finset.Icc 1 (N / d), 1 / Real.sqrt ((d * j : ℕ) : ℝ) := by
      symm
      refine Finset.sum_bij' (fun j _ => d * j) (fun m _ => m / d) ?_ ?_ ?_ ?_ ?_
      · intro j hj
        have hj' := Finset.mem_Icc.mp hj
        rw [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩,
          Nat.dvd_mul_right d j⟩
        exact (Nat.le_div_iff_mul_le hd0).mp hj'.2 |>.trans' (by rw [mul_comm])
      · intro m hm
        obtain ⟨hm1, hdm⟩ := Finset.mem_filter.mp hm
        have hm1' := Finset.mem_Icc.mp hm1
        rw [Finset.mem_Icc]
        refine ⟨?_, Nat.div_le_div_right hm1'.2⟩
        obtain ⟨k, rfl⟩ := hdm
        rw [Nat.mul_div_cancel_left k hd0]
        rcases Nat.eq_zero_or_pos k with h | h
        · subst h; simp at hm1'
        · exact h
      · intro j _; exact Nat.mul_div_cancel_left j hd0
      · intro m hm; exact Nat.mul_div_cancel' (Finset.mem_filter.mp hm).2
      · intro j _; rfl
    rw [hbij]
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
    have hsplit : ∀ j : ℕ, 1 / Real.sqrt ((d * j : ℕ) : ℝ) = 1 / Real.sqrt d * (1 / Real.sqrt j) := by
      intro j
      rw [Nat.cast_mul, Real.sqrt_mul hdR.le, one_div_mul_one_div]
    simp_rw [hsplit]
    rw [← Finset.mul_sum]
    have h2 := sum_inv_sqrt_le (N / d)
    have h3 : Real.sqrt ((N / d : ℕ) : ℝ) ≤ Real.sqrt N / Real.sqrt d := by
      rw [← Real.sqrt_div' _ hdR.le]
      apply Real.sqrt_le_sqrt
      rw [le_div_iff₀ hdR]
      exact_mod_cast Nat.div_mul_le_self N d
    have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdR
    calc 1 / Real.sqrt d * ∑ j ∈ Finset.Icc 1 (N / d), 1 / Real.sqrt j
        ≤ 1 / Real.sqrt d * (2 * (Real.sqrt N / Real.sqrt d)) := by
          apply mul_le_mul_of_nonneg_left (h2.trans (by linarith)) (by positivity)
      _ = 2 * Real.sqrt N / (Real.sqrt d * Real.sqrt d) := by field_simp
      _ = 2 * Real.sqrt N / d := by rw [Real.mul_self_sqrt hdR.le]
  calc ∑ d ∈ Finset.Icc 1 N, ∑ m ∈ (Finset.Icc 1 N).filter (fun m => d ∣ m), 1 / Real.sqrt m
      ≤ ∑ d ∈ Finset.Icc 1 N, 2 * Real.sqrt N / d := Finset.sum_le_sum hinner
    _ = 2 * Real.sqrt N * ∑ d ∈ Finset.Icc 1 N, 1 / (d : ℝ) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun d _ => by ring
    _ ≤ 2 * Real.sqrt N * (1 + Real.log N) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hh := harmonic_le_one_add_log N
        have : ((harmonic N : ℚ) : ℝ) = ∑ d ∈ Finset.Icc 1 N, 1 / (d : ℝ) := by
          rw [harmonic_eq_sum_Icc]
          push_cast
          simp
        rw [← this]
        exact hh

/-- `∑_{2 ≤ n ≤ N} τ(n−1)/√n ≤ 2√N (1 + log N)`. -/
lemma sum_divisors_div_sqrt_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 2 N, (((n - 1).divisors.card : ℕ) : ℝ) / Real.sqrt n ≤
      2 * Real.sqrt N * (1 + Real.log N) := by
  calc ∑ n ∈ Finset.Icc 2 N, (((n - 1).divisors.card : ℕ) : ℝ) / Real.sqrt n
      ≤ ∑ n ∈ Finset.Icc 2 N, (((n - 1).divisors.card : ℕ) : ℝ) / Real.sqrt ((n - 1 : ℕ) : ℝ) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn2 := (Finset.mem_Icc.mp hn).1
        have h1 : (1 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ n - 1)
        apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (Real.sqrt_pos.mpr (by linarith))
        exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.sub_le n 1)
    _ = ∑ m ∈ (Finset.Icc 2 N).image (fun n : ℕ => n - 1),
          ((m.divisors.card : ℕ) : ℝ) / Real.sqrt (m : ℝ) := by
        rw [Finset.sum_image]
        intro a ha b hb h
        have := (Finset.mem_Icc.mp ha).1; have := (Finset.mem_Icc.mp hb).1
        simp only at h; omega
    _ ≤ ∑ m ∈ Finset.Icc 1 N, ((m.divisors.card : ℕ) : ℝ) / Real.sqrt m := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
        intro m hm
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
        have := Finset.mem_Icc.mp hn
        exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    _ ≤ 2 * Real.sqrt N * (1 + Real.log N) := sum_card_divisors_div_sqrt_le N

/-! ### The sharp prime part -/

/-- `P_χ(t) = −(1/π) Re ∑_{n ≤ X} Λ(n) χ(n) n^{−1/2−it}` (= `zeta23`'s `PXc (coeff χ) X t`). -/
def Pch (X : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) : ℝ :=
  -(1 / Real.pi) * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
    ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q) * (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * t)).re

lemma PXc_eq_Pch {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (X t : ℝ) :
    PXc (coeff χ) X t = Pch X χ t := rfl

lemma norm_natCast_cpow (n : ℕ) (hn : 0 < n) (t : ℝ) :
    ‖(n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * t)‖ = 1 / Real.sqrt n := by
  rw [Complex.norm_natCast_cpow_of_pos hn]
  have : (-(1 / 2 : ℂ) - Complex.I * t).re = -(1 / 2) := by simp
  rw [this, Real.rpow_neg (Nat.cast_nonneg n), ← Real.sqrt_eq_rpow, one_div]

/-- `|∑_χ ω_χ P_χ(t)| ≤ (4/π) w_max Q √X log X (1 + log X)` uniformly in `t` (via
`lem:firstmoment`). -/
theorem abs_famSum_Pch_le (W : Weight) {Q X : ℝ} (hQ : 1 ≤ Q) (hX : 1 ≤ X) (t : ℝ) :
    |famSum W Q (fun _ χ => Pch X χ t)| ≤
      4 / Real.pi * W.wmax * Q * Real.sqrt X * Real.log X * (1 + Real.log X) := by
  set a : ℕ → ℂ := fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
    (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * t) with ha
  set F : ℕ → ℂ := fun n => ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (W.omega Q q : ℂ) *
    ∑ χ ∈ primChars q, χ (n : ZMod q) with hF
  have hrep : famSum W Q (fun _ χ => Pch X χ t) =
      -(1 / Real.pi) * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, a n * F n).re := by
    have e1 : ∀ q (χ : DirichletCharacter ℂ q), (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q) *
          (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * t)) = ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, a n * χ (n : ZMod q) := by
      intro q χ
      refine Finset.sum_congr rfl fun n _ => ?_
      simp only [ha]; ring
    have e2 : (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, a n * F n) = ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊,
        ∑ χ ∈ primChars q, (W.omega Q q : ℂ) * ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, a n * χ (n : ZMod q) := by
      simp only [hF, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun χ _ => Finset.sum_congr rfl fun n _ => ?_
      ring
    rw [e2]
    unfold famSum Pch
    rw [Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Complex.re_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [Complex.re_ofReal_mul]
    dsimp only
    rw [e1 q χ]
    ring
  rw [hrep, abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 1 / Real.pi)]
  set M := ⌊X⌋₊ with hM
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hMX : (M : ℝ) ≤ X := Nat.floor_le (by linarith)
  have hwm := W.wmax_nonneg
  -- bound the sum
  have hterm : ∀ n ∈ Finset.Ioc 0 ⌊X⌋₊, ‖a n * F n‖ ≤
      Real.log X * (2 * W.wmax * Q) * ((((n - 1).divisors.card : ℕ) : ℝ) / Real.sqrt n) *
        (if 2 ≤ n then 1 else 0) := by
    intro n hn
    have hn0 : 0 < n := (Finset.mem_Ioc.mp hn).1
    have hnM : n ≤ M := (Finset.mem_Ioc.mp hn).2
    by_cases h2 : 2 ≤ n
    · rw [if_pos h2, mul_one, norm_mul]
      have ha' : ‖a n‖ = ArithmeticFunction.vonMangoldt n / Real.sqrt n := by
        simp only [ha, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, norm_natCast_cpow n hn0 t]
        ring
      rw [ha']
      have hΛ : ArithmeticFunction.vonMangoldt n ≤ Real.log X := by
        refine ArithmeticFunction.vonMangoldt_le_log.trans ?_
        exact Real.log_le_log (by exact_mod_cast hn0) ((Nat.cast_le.mpr hnM).trans hMX)
      have hFn := first_moment W hQ n h2
      have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn0)
      calc ArithmeticFunction.vonMangoldt n / Real.sqrt n * ‖F n‖
          ≤ Real.log X / Real.sqrt n * (2 * W.wmax * Q * ((n - 1).divisors.card : ℝ)) := by
            apply mul_le_mul (div_le_div_of_nonneg_right hΛ hsq.le) hFn (norm_nonneg _)
              (div_nonneg hlogX hsq.le)
        _ = _ := by ring
    · have hn1 : n = 1 := by omega
      subst hn1
      simp [ha]
  have hsum := Finset.sum_le_sum hterm
  have hsplit : ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, Real.log X * (2 * W.wmax * Q) *
      ((((n - 1).divisors.card : ℕ) : ℝ) / Real.sqrt n) * (if 2 ≤ n then 1 else 0) =
      Real.log X * (2 * W.wmax * Q) * ∑ n ∈ Finset.Icc 2 M,
        ((((n - 1).divisors.card : ℕ) : ℝ) / Real.sqrt n) := by
    rw [Finset.mul_sum]
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ioc 0 ⌊X⌋₊) (fun n => 2 ≤ n)]
    have hz : ∑ n ∈ (Finset.Ioc 0 ⌊X⌋₊).filter (fun n => ¬ 2 ≤ n), Real.log X * (2 * W.wmax * Q) *
        ((((n - 1).divisors.card : ℕ) : ℝ) / Real.sqrt n) * (if 2 ≤ n then 1 else 0) = 0 :=
      Finset.sum_eq_zero fun n hn => by
        rw [if_neg (Finset.mem_filter.mp hn).2, mul_zero]
    rw [hz, add_zero]
    have hset : (Finset.Ioc 0 ⌊X⌋₊).filter (fun n => 2 ≤ n) = Finset.Icc 2 M := by
      ext n; simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]; omega
    rw [hset]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [if_pos (Finset.mem_Icc.mp hn).1, mul_one]
  have hdiv := sum_divisors_div_sqrt_le M
  have hsqrtM : Real.sqrt M ≤ Real.sqrt X := Real.sqrt_le_sqrt hMX
  have hlogM : Real.log M ≤ Real.log X := by
    rcases Nat.eq_zero_or_pos M with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]; exact hlogX
    · exact Real.log_le_log (by exact_mod_cast hpos) hMX
  have hfin : ∑ n ∈ Finset.Icc 2 M, ((((n - 1).divisors.card : ℕ) : ℝ) / Real.sqrt n) ≤
      2 * Real.sqrt X * (1 + Real.log X) := by
    refine hdiv.trans ?_
    have : 0 ≤ 1 + Real.log (M : ℝ) := by
      rcases Nat.eq_zero_or_pos M with h0 | hpos
      · rw [h0, Nat.cast_zero, Real.log_zero]; norm_num
      · have := Real.log_nonneg (by exact_mod_cast hpos : (1 : ℝ) ≤ M); linarith
    have := mul_le_mul (mul_le_mul_of_nonneg_left hsqrtM (by norm_num : (0:ℝ) ≤ 2))
      (by linarith : 1 + Real.log (M : ℝ) ≤ 1 + Real.log X) this (by positivity)
    linarith
  calc 1 / Real.pi * |(∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, a n * F n).re|
      ≤ 1 / Real.pi * ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ‖a n * F n‖ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (Complex.abs_re_le_norm _).trans (norm_sum_le _ _)
    _ ≤ 1 / Real.pi * (Real.log X * (2 * W.wmax * Q) * (2 * Real.sqrt X * (1 + Real.log X))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        refine hsum.trans ?_
        rw [hsplit]
        exact mul_le_mul_of_nonneg_left hfin (by positivity)
    _ = 4 / Real.pi * W.wmax * Q * Real.sqrt X * Real.log X * (1 + Real.log X) := by ring

end Families.Ported.Zero
