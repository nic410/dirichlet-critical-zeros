/-
# `lem:fS` (iii), the error term `|E_S(s)| ≤ 2B e^{−s/2}`

`lemfS_iii_a : ∀ S s, 0 ≤ s → |E_S(s)| ≤ 2 B e^{−s/2}` (Lemma 6.19 and its proof;
"word for word that of `lem:harm`").

With `x = e^s`, `X = ⌊x⌋`, `G(d) = g_S(d)/d`, `H(y) = ∑_{m ≤ y} 1/m`:
* `F_S(s) = ∑_{d ≤ X} G(d) H(x/d)` (`f_S = 1 * g_S`, `FS_eq`);
* `H(y) = log y + γ + θ(y)`, `|θ(y)| ≤ 2/y` for `y ≥ 1` (`abs_Hs_sub_le`, from Mathlib's
  `H_n − log(n+1) < γ < H_n − log n`);
* `ℰ = ∑_d G(d)` and `∑_d G(d) log d = −ℰ(c_S − γ)` (`lemfS_ii_euler`, `Lam_eq`), so
  `E_S(s) = ∑_{d ≤ X} G(d) θ(x/d) − ∑_{d > X} G(d)(log(x/d) + γ)`;
* each term is `≤ 2 x^{−1/2} |g_S(d)| d^{−1/2}` in absolute value, and `∑_d |g_S(d)| d^{−1/2} ≤ B`
  (`tsum_gabs_le_Bconst`).
-/
import Families.Phase1.B.FSlogderiv

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius
open ArithmeticFunction Finset

namespace Families.Phase1.B

open Families

/-! ### The harmonic sum -/

/-- `H(y) = ∑_{1 ≤ m ≤ y} 1/m`. -/
def Hs (y : ℝ) : ℝ := ∑ m ∈ Finset.Icc 1 ⌊y⌋₊, (1 : ℝ) / m

lemma Hs_eq_harmonic (y : ℝ) : Hs y = (harmonic ⌊y⌋₊ : ℝ) := by
  unfold Hs
  rw [harmonic_eq_sum_Icc]
  push_cast
  simp [one_div]

/-- `|H(y) − log y − γ| ≤ 2/y` for `y ≥ 1`. -/
lemma abs_Hs_sub_le {y : ℝ} (hy : 1 ≤ y) :
    |Hs y - Real.log y - Real.eulerMascheroniConstant| ≤ 2 / y := by
  set n := ⌊y⌋₊ with hn
  have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast hy)
  have hny : (n : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hyn : y < n + 1 := Nat.lt_floor_add_one y
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have h1 := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
  have h2 := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  unfold Real.eulerMascheroniSeq at h1
  unfold Real.eulerMascheroniSeq' at h2
  rw [if_neg (by omega)] at h2
  rw [Hs_eq_harmonic, ← hn]
  have hl1 : Real.log n ≤ Real.log y := Real.log_le_log hn0 hny
  have hl2 : Real.log y < Real.log (n + 1) := Real.log_lt_log (by linarith) hyn
  have hdiff : Real.log ((n : ℝ) + 1) - Real.log n ≤ 1 / n := by
    rw [← Real.log_div (by positivity) hn0.ne']
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((n : ℝ) + 1) / n by positivity)
    have e : ((n : ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
    linarith
  have h2n : 1 / (n : ℝ) ≤ 2 / y := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    rw [div_le_div_iff₀ hn0 (by linarith)]; linarith
  rw [abs_le]
  constructor <;> linarith

/-! ### `F_S(s) = ∑_{d ≤ x} G(d) H(x/d)` -/

/-- `∑_{n ≤ X} ∑_{d ∣ n} K(d,n) = ∑_{d ≤ X} ∑_{m ≤ X/d} K(d, dm)`. -/
lemma sum_Icc_divisors (X : ℕ) (K : ℕ → ℕ → ℝ) :
    ∑ n ∈ Finset.Icc 1 X, ∑ d ∈ n.divisors, K d n =
      ∑ d ∈ Finset.Icc 1 X, ∑ m ∈ Finset.Icc 1 (X / d), K d (d * m) := by
  have h1 : ∀ n ∈ Finset.Icc 1 X, n.divisors = (Finset.Icc 1 X).filter (fun d => d ∣ n) := by
    intro n hn
    obtain ⟨hn1, hnX⟩ := Finset.mem_Icc.mp hn
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hd, -⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega), (Nat.le_of_dvd (by omega) hd).trans hnX⟩, hd⟩
    · rintro ⟨-, hd⟩; exact ⟨hd, by omega⟩
  rw [Finset.sum_congr rfl fun n hn => by rw [h1 n hn]]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [← Finset.sum_filter]
  have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
  refine Finset.sum_nbij' (fun n => n / d) (fun m => d * m) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨hnI, hdvd⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1, hnX⟩ := Finset.mem_Icc.mp hnI
    rw [Finset.mem_Icc]
    exact ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hd0, Nat.div_le_div_right hnX⟩
  · intro m hm
    obtain ⟨hm1, hmX⟩ := Finset.mem_Icc.mp hm
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (by positivity), ?_⟩, dvd_mul_right _ _⟩
    exact (Nat.le_div_iff_mul_le hd0).mp hmX |>.trans_eq' (mul_comm _ _)
  · intro n hn; exact Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2
  · intro m _; exact Nat.mul_div_cancel_left m hd0
  · intro n hn; rw [Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2]

/-- `F_S(s) = ∑_{d ≤ x} G(d) H(x/d)`. -/
lemma FS_eq (S : Finset ℕ) (x : ℝ) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, fS S n / n = ∑ d ∈ Finset.Icc 1 ⌊x⌋₊, gdiv S d * Hs (x / d) := by
  have h1 : ∀ n ∈ Finset.Icc 1 ⌊x⌋₊, fS S n / n = ∑ d ∈ n.divisors, gS S d / n := by
    intro n hn
    rw [lemfS_ii_conv S n (Finset.mem_Icc.mp hn).1, Finset.sum_div]
  rw [Finset.sum_congr rfl h1, sum_Icc_divisors ⌊x⌋₊ (fun d n => gS S d / n)]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
  unfold Hs gdiv
  rw [Nat.floor_div_natCast, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  push_cast
  field_simp

/-! ### The assembly -/

/-- `|γ − log z| ≤ 2√z` for `z ≥ 1`. -/
lemma abs_gamma_sub_log_le {z : ℝ} (hz : 1 ≤ z) :
    |Real.eulerMascheroniConstant - Real.log z| ≤ 2 * z ^ (1 / 2 : ℝ) := by
  have hγ0 : 0 < Real.eulerMascheroniConstant := by
    linarith [Real.one_half_lt_eulerMascheroniConstant]
  have hγ1 := Real.eulerMascheroniConstant_lt_two_thirds
  have hl : 0 ≤ Real.log z := Real.log_nonneg hz
  have hsq : 1 ≤ z ^ (1 / 2 : ℝ) := Real.one_le_rpow hz (by norm_num)
  have hlog : Real.log z ≤ 2 * z ^ (1 / 2 : ℝ) := by
    have := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ z) (show (0 : ℝ) < 1 / 2 by norm_num)
    linarith
  rw [abs_le]; constructor <;> linarith

/-- **`lem:fS`(iii), error term:** `|E_S(s)| ≤ 2 B e^{−s/2}` for `s ≥ 0`, uniformly in `S`. -/
theorem lemfS_iii_a : ∀ (S : Finset ℕ) (s : ℝ), 0 ≤ s →
    |ES S s| ≤ 2 * Bconst * Real.exp (-s / 2) := by
  intro S s hs
  set x := Real.exp s with hxdef
  have hx1 : 1 ≤ x := Real.one_le_exp hs
  have hx0 : 0 < x := by linarith
  set X := ⌊x⌋₊ with hX
  set γ := Real.eulerMascheroniConstant with hγ
  have hlogx : Real.log x = s := Real.log_exp s
  -- `x^{-1/2} = e^{−s/2}`
  have hxhalf : x ^ (-(1 / 2 : ℝ)) = Real.exp (-s / 2) := by
    rw [hxdef, ← Real.exp_mul]; congr 1; ring
  -- the terms `e(d)`
  let θ : ℕ → ℝ := fun d => Hs (x / d) - Real.log (x / d) - γ
  let e : ℕ → ℝ := fun d => if d ∈ Finset.Icc 1 X then gdiv S d * θ d
    else -(gdiv S d * (Real.log x + γ - Real.log d))
  -- `|e(d)| ≤ 2 x^{−1/2} |g(d)| d^{−1/2}`
  have hxs : 0 < x ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hx0 _
  have he : ∀ d, ‖e d‖ ≤ 2 * x ^ (-(1 / 2 : ℝ)) * gabs S d := by
    intro d
    simp only [e, Real.norm_eq_abs]
    rcases Nat.eq_zero_or_pos d with rfl | hdpos
    · simp [gdiv, gabs_zero]
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hdpos
    have hsd : 0 < (d : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hd0 _
    unfold gabs gdiv
    split_ifs with hd
    · -- `d ≤ X`: `|θ(x/d)| ≤ 2d/x`
      have hdX : (d : ℝ) ≤ x := le_trans (by exact_mod_cast (Finset.mem_Icc.mp hd).2)
        (Nat.floor_le hx0.le)
      have hθ := abs_Hs_sub_le (show 1 ≤ x / d by rw [le_div_iff₀ hd0]; linarith)
      rw [abs_mul, abs_div, abs_of_pos hd0]
      have h1 : |gS S d| / d * |θ d| ≤ |gS S d| / d * (2 / (x / d)) :=
        mul_le_mul_of_nonneg_left hθ (by positivity)
      have h2 : |gS S d| / d * (2 / (x / d)) = 2 * |gS S d| * x⁻¹ := by field_simp
      -- `x⁻¹ ≤ x^{-1/2} d^{-1/2}`
      have h3 : x⁻¹ ≤ x ^ (-(1 / 2 : ℝ)) * (d : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [← Real.mul_rpow hx0.le hd0.le, show x⁻¹ = x ^ (-(1 / 2 : ℝ)) * x ^ (-(1 / 2 : ℝ)) by
          rw [← Real.rpow_add hx0]; norm_num; exact (Real.rpow_neg_one x).symm]
        rw [Real.mul_rpow hx0.le hd0.le]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hd0 hdX (by norm_num))
          hxs.le
      calc |gS S d| / d * |θ d| ≤ 2 * |gS S d| * x⁻¹ := h1.trans_eq h2
        _ ≤ 2 * |gS S d| * (x ^ (-(1 / 2 : ℝ)) * (d : ℝ) ^ (-(1 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = 2 * x ^ (-(1 / 2 : ℝ)) * (|gS S d| * (d : ℝ) ^ (-(1 / 2 : ℝ))) := by ring
    · -- `d > X ≥ x`: `|log(x/d) + γ| ≤ 2 (d/x)^{1/2}`
      have hdX : X < d := by
        by_contra h; exact hd (Finset.mem_Icc.mpr ⟨hdpos, by omega⟩)
      have hxd : x < d := lt_of_lt_of_le (Nat.lt_floor_add_one x) (by exact_mod_cast hdX)
      have hz : 1 ≤ (d : ℝ) / x := by rw [le_div_iff₀ hx0]; linarith
      have hγl := abs_gamma_sub_log_le hz
      have elog : Real.log x + γ - Real.log d = γ - Real.log ((d : ℝ) / x) := by
        rw [Real.log_div hd0.ne' hx0.ne']; ring
      rw [abs_neg, elog, abs_mul, abs_div, abs_of_pos hd0]
      have hsplit : ((d : ℝ) / x) ^ (1 / 2 : ℝ) = (d : ℝ) ^ (1 / 2 : ℝ) * x ^ (-(1 / 2 : ℝ)) := by
        rw [Real.div_rpow hd0.le hx0.le, Real.rpow_neg hx0.le, div_eq_mul_inv]
      have hdhalf : (d : ℝ) ^ (1 / 2 : ℝ) / d = (d : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [show -(1 / 2 : ℝ) = 1 / 2 - 1 by norm_num, Real.rpow_sub_one hd0.ne']
      calc |gS S d| / d * |γ - Real.log ((d : ℝ) / x)|
          ≤ |gS S d| / d * (2 * ((d : ℝ) / x) ^ (1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left hγl (by positivity)
        _ = 2 * x ^ (-(1 / 2 : ℝ)) * (|gS S d| * ((d : ℝ) ^ (1 / 2 : ℝ) / d)) := by
            rw [hsplit]; ring
        _ = 2 * x ^ (-(1 / 2 : ℝ)) * (|gS S d| * (d : ℝ) ^ (-(1 / 2 : ℝ))) := by rw [hdhalf]
  have hsum_e : Summable e :=
    Summable.of_norm_bounded ((summable_gabs S).mul_left (2 * x ^ (-(1 / 2 : ℝ)))) he
  -- `E_S(s) = ∑ e(d)`
  have hE : ES S s = ∑' d, e d := by
    -- the two infinite series
    have hEc : ∑' d, gdiv S d = Ecal := (lemfS_ii_euler S).tsum_eq
    have hL := Lam_eq S
    -- split `∑' e` into the finite part and the tail
    have hfinsupp : ∀ f : ℕ → ℝ, Summable f →
        ∑' d, f d = ∑ d ∈ Finset.Icc 1 X, f d + ∑' d, (if d ∈ Finset.Icc 1 X then 0 else f d) := by
      intro f hf
      have hind : Summable fun d => if d ∈ Finset.Icc 1 X then f d else 0 :=
        summable_of_ne_finset_zero (s := Finset.Icc 1 X) fun d hd => by simp [hd]
      have hrest : Summable fun d => if d ∈ Finset.Icc 1 X then 0 else f d :=
        (hf.sub hind).congr fun d => by split_ifs <;> ring
      have hsp : ∀ d, f d = (if d ∈ Finset.Icc 1 X then f d else 0) +
          (if d ∈ Finset.Icc 1 X then 0 else f d) := fun d => by split_ifs <;> ring
      rw [tsum_congr hsp, Summable.tsum_add hind hrest,
        tsum_eq_sum (s := Finset.Icc 1 X) (fun d hd => if_neg hd)]
      congr 1
      exact Finset.sum_congr rfl fun d hd => if_pos hd
    have hA : Summable fun d => gdiv S d * (Real.log x + γ - Real.log d) := by
      have := ((summable_gdiv S).mul_right (Real.log x + γ)).sub (summable_gdiv_mul_log S)
      refine this.congr fun d => by ring
    have hsplitA := hfinsupp _ hA
    have htot : ∑' d, gdiv S d * (Real.log x + γ - Real.log d) =
        (Real.log x + γ) * Ecal + Ecal * (cS S - γ) := by
      have e1 : ∀ d, gdiv S d * (Real.log x + γ - Real.log d) =
          (Real.log x + γ) * gdiv S d - gdiv S d * Real.log d := fun d => by ring
      rw [tsum_congr e1, Summable.tsum_sub ((summable_gdiv S).mul_left _) (summable_gdiv_mul_log S),
        tsum_mul_left, hEc, hL]
      ring
    have htail : ∑' d, e d = ∑ d ∈ Finset.Icc 1 X, gdiv S d * θ d -
        ∑' d, (if d ∈ Finset.Icc 1 X then 0 else gdiv S d * (Real.log x + γ - Real.log d)) := by
      rw [hfinsupp e hsum_e]
      have e2 : ∑ d ∈ Finset.Icc 1 X, e d = ∑ d ∈ Finset.Icc 1 X, gdiv S d * θ d :=
        Finset.sum_congr rfl fun d hd => by simp only [e, if_pos hd]
      have e3 : ∑' d, (if d ∈ Finset.Icc 1 X then 0 else e d) =
          -∑' d, (if d ∈ Finset.Icc 1 X then 0 else gdiv S d * (Real.log x + γ - Real.log d)) := by
        rw [← tsum_neg]; refine tsum_congr fun d => ?_
        simp only [e]; split_ifs <;> simp
      rw [e2, e3]; ring
    rw [htail]
    have htail' : ∑' d, (if d ∈ Finset.Icc 1 X then 0 else gdiv S d * (Real.log x + γ - Real.log d))
        = (Real.log x + γ) * Ecal + Ecal * (cS S - γ) -
          ∑ d ∈ Finset.Icc 1 X, gdiv S d * (Real.log x + γ - Real.log d) := by
      rw [← htot, hsplitA]; ring
    rw [htail']
    unfold ES
    rw [FS_eq S x, ← hX]
    have e4 : ∀ d ∈ Finset.Icc 1 X, gdiv S d * Hs (x / d) =
        gdiv S d * θ d + gdiv S d * (Real.log x + γ - Real.log d) := by
      intro d hd
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
      simp only [θ]
      rw [Real.log_div hx0.ne' hd0.ne']; ring
    rw [Finset.sum_congr rfl e4, Finset.sum_add_distrib, hlogx]
    ring
  -- conclude
  rw [hE]
  calc |∑' d, e d| ≤ ∑' d, ‖e d‖ := by
        rw [← Real.norm_eq_abs]; exact norm_tsum_le_tsum_norm hsum_e.norm
    _ ≤ ∑' d, 2 * x ^ (-(1 / 2 : ℝ)) * gabs S d :=
        Summable.tsum_le_tsum he hsum_e.norm ((summable_gabs S).mul_left _)
    _ = 2 * x ^ (-(1 / 2 : ℝ)) * ∑' d, gabs S d := tsum_mul_left
    _ ≤ 2 * x ^ (-(1 / 2 : ℝ)) * Bconst :=
        mul_le_mul_of_nonneg_left (tsum_gabs_le_Bconst S) (by positivity)
    _ = 2 * Bconst * Real.exp (-s / 2) := by rw [hxhalf]; ring

end Families.Phase1.B
