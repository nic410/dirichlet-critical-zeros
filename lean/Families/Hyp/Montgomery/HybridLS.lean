/-
# Montgomery 1969 density: the hybrid large sieve

`∑_{q ≤ Q} ∑*_χ ∫_{−W}^{W} |∑_{n∈S} x_n χ(n) n^{−iv}|² dv ≤ 100 ∑_{n∈S} |x_n|² (W(Q²+1) + n)`
for `W ≥ 2`, from Gallagher's inequality (`gallagher`) and the multiplicative large sieve
`Families.Hyp.MV_LargeSieve_proof` (`C₀ = 17/4`).
-/
import Families.Hyp.Montgomery.Gallagher
import Families.Hyp.MVLargeSieve

noncomputable section

open scoped BigOperators ComplexConjugate
open MeasureTheory Real Finset

namespace Families.Hyp.Montgomery

open Families

/-! ### Window integrals -/

lemma measurable_win (h x : ℝ) : Measurable (fun u => win h u x) := by
  rw [win_eq_indicator]; exact measurable_one.indicator measurableSet_Ioc

lemma integrable_win (h x : ℝ) : Integrable (fun u => win h u x) := by
  rw [win_eq_indicator]
  apply (integrable_indicator_iff measurableSet_Ioc).2
  exact integrableOn_const (by simp)

lemma integral_win {h : ℝ} (hh : 0 ≤ h) (x : ℝ) : ∫ u, win h u x = h := by
  rw [win_eq_indicator, integral_indicator_one measurableSet_Ioc, Real.volume_real_Ioc]
  rw [max_eq_left (by linarith)]; ring

lemma win_mem (h u x : ℝ) : win h u x = 0 ∨ win h u x = 1 := by
  unfold win; split_ifs <;> simp

lemma win_sq (h u x : ℝ) : win h u x ^ 2 = win h u x := by
  rcases win_mem h u x with e | e <;> rw [e] <;> norm_num

/-- `‖∑ win_n a_n‖² ≤ (∑ ‖a_n‖)² ∑ win_n`. -/
lemma norm_winSum_sq_le (h u : ℝ) {ι : Type*} (S : Finset ι) (a : ι → ℂ) (ℓ : ι → ℝ) :
    ‖∑ n ∈ S, (win h u (ℓ n) : ℂ) * a n‖ ^ 2 ≤
      (∑ n ∈ S, ‖a n‖) ^ 2 * ∑ n ∈ S, win h u (ℓ n) := by
  by_cases hall : ∀ n ∈ S, win h u (ℓ n) = 0
  · rw [Finset.sum_eq_zero fun n hn => by rw [hall n hn]; simp]
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun n _ => win_nonneg h u _)
  · push Not at hall
    obtain ⟨n₀, hn₀, hne⟩ := hall
    have h1 : 1 ≤ ∑ n ∈ S, win h u (ℓ n) := by
      have : win h u (ℓ n₀) = 1 := (win_mem h u _).resolve_left hne
      rw [← this]
      exact Finset.single_le_sum (fun n _ => win_nonneg h u _) hn₀
    have h2 : ‖∑ n ∈ S, (win h u (ℓ n) : ℂ) * a n‖ ≤ ∑ n ∈ S, ‖a n‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (win_nonneg h u _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (win_le_one h u _)
    have h3 : 0 ≤ ∑ n ∈ S, ‖a n‖ := Finset.sum_nonneg fun n _ => norm_nonneg _
    calc ‖∑ n ∈ S, (win h u (ℓ n) : ℂ) * a n‖ ^ 2 ≤ (∑ n ∈ S, ‖a n‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h2 2
      _ ≤ (∑ n ∈ S, ‖a n‖) ^ 2 * ∑ n ∈ S, win h u (ℓ n) :=
          le_mul_of_one_le_right (sq_nonneg _) h1

lemma measurable_winSum (h : ℝ) {ι : Type*} (S : Finset ι) (a : ι → ℂ) (ℓ : ι → ℝ) :
    Measurable (fun u => ∑ n ∈ S, (win h u (ℓ n) : ℂ) * a n) := by
  refine Finset.measurable_sum _ fun n _ => ?_
  exact (Complex.measurable_ofReal.comp (measurable_win h (ℓ n))).mul_const _

lemma integrable_winSum_sq (h : ℝ) {ι : Type*} (S : Finset ι) (a : ι → ℂ) (ℓ : ι → ℝ) :
    Integrable (fun u => ‖∑ n ∈ S, (win h u (ℓ n) : ℂ) * a n‖ ^ 2) := by
  refine (((integrable_finsetSum S fun n _ => integrable_win h (ℓ n))).const_mul
    ((∑ n ∈ S, ‖a n‖) ^ 2)).mono' ?_ ?_
  · exact ((measurable_winSum h S a ℓ).norm.pow_const 2).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun u => ?_
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    simpa using norm_winSum_sq_le h u S a ℓ

/-! ### The large sieve on a natural interval -/

lemma sum_intervalZ_eq {M : Type*} [AddCommMonoid M] (A B : ℕ) (hAB : A ≤ B) (f : ℤ → M) :
    ∑ m ∈ intervalZ (A : ℤ) (B - A), f m = ∑ n ∈ Finset.Ico A B, f (n : ℤ) := by
  unfold intervalZ
  have e : ((A : ℤ) + ((B - A : ℕ) : ℤ)) = (B : ℤ) := by push_cast [Nat.cast_sub hAB]; ring
  rw [e]
  symm
  refine Finset.sum_nbij' (fun n => (n : ℤ)) (fun m => m.toNat) ?_ ?_ ?_ ?_ ?_
  · intro n hn; simp only [Finset.mem_coe, Finset.mem_Ico] at hn ⊢; omega
  · intro m hm; simp only [Finset.mem_coe, Finset.mem_Ico] at hm ⊢; omega
  · intro n _; simp
  · intro m hm; simp only [Finset.mem_coe, Finset.mem_Ico] at hm; omega
  · intro n _; rfl

/-- The multiplicative large sieve on `[A, B)`, for coefficients on the naturals. -/
theorem ls_Ico (Q : ℝ) (hQ : 1 ≤ Q) (A B : ℕ) (hAB : A ≤ B) (y : ℕ → ℂ) :
    ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ ∈ primChars q, ‖∑ n ∈ Finset.Ico A B, y n * χ (n : ZMod q)‖ ^ 2
      ≤ (17 / 4) * (Q ^ 2 + (B - A : ℕ)) * ∑ n ∈ Finset.Ico A B, ‖y n‖ ^ 2 := by
  have hLS := mvMult_of_add (by norm_num) Hyp.mvAdd_proof Q hQ (A : ℤ) (B - A)
    (fun m => y m.toNat)
  have hsum : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      ∑ n ∈ intervalZ (A : ℤ) (B - A), y n.toNat * χ n =
        ∑ n ∈ Finset.Ico A B, y n * χ (n : ZMod q) := by
    intro q χ
    rw [sum_intervalZ_eq A B hAB]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp
  have hnorm : normSq (intervalZ (A : ℤ) (B - A)) (fun m => y m.toNat) =
      ∑ n ∈ Finset.Ico A B, ‖y n‖ ^ 2 := by
    unfold normSq
    rw [sum_intervalZ_eq A B hAB (fun m => ‖y m.toNat‖ ^ 2)]
    simp
  simp_rw [hsum, hnorm] at hLS
  refine le_trans (Finset.sum_le_sum fun q hq => ?_) hLS
  have hq0 : 0 < q := (Finset.mem_Icc.mp hq).1
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq0
  have h1 : (1 : ℝ) ≤ (q : ℝ) / Nat.totient q := by
    rw [le_div_iff₀ hφ, one_mul]; exact_mod_cast Nat.totient_le q
  exact le_mul_of_one_le_left (Finset.sum_nonneg fun _ _ => sq_nonneg _) h1

/-! ### Windows in `log n` are natural intervals -/

lemma win_log_eq (h u : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    win h u (Real.log n) =
      if ⌈Real.exp u⌉₊ ≤ n ∧ n < ⌈Real.exp (u + h)⌉₊ then 1 else 0 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold win
  congr 1
  apply propext
  rw [Real.le_log_iff_exp_le hn0, Real.log_lt_iff_lt_exp hn0, Nat.ceil_le, Nat.lt_ceil]

lemma ceil_exp_mono (u h : ℝ) (hh : 0 ≤ h) : ⌈Real.exp u⌉₊ ≤ ⌈Real.exp (u + h)⌉₊ :=
  Nat.ceil_mono (Real.exp_le_exp.mpr (by linarith))

/-- The number of integers in `[e^u, e^{u+h})` is at most `n(e^h − 1) + 1` for any `n ≥ e^u`. -/
lemma card_window_le (u h : ℝ) (hh : 0 ≤ h) {n : ℕ} (hn : Real.exp u ≤ n) :
    ((⌈Real.exp (u + h)⌉₊ - ⌈Real.exp u⌉₊ : ℕ) : ℝ) ≤ n * (Real.exp h - 1) + 1 := by
  rw [Nat.cast_sub (ceil_exp_mono u h hh)]
  have h1 : (⌈Real.exp (u + h)⌉₊ : ℝ) < Real.exp u * Real.exp h + 1 := by
    rw [← Real.exp_add]; exact Nat.ceil_lt_add_one (by positivity)
  have h2 : Real.exp u ≤ (⌈Real.exp u⌉₊ : ℝ) := Nat.le_ceil _
  have h3 : Real.exp u * (Real.exp h - 1) ≤ n * (Real.exp h - 1) :=
    mul_le_mul_of_nonneg_right hn (by linarith [Real.add_one_le_exp h])
  nlinarith

/-- Pointwise large sieve for a window sum. -/
theorem ls_window (Q : ℝ) (hQ : 1 ≤ Q) {h : ℝ} (hh : 0 ≤ h) (u : ℝ) (S : Finset ℕ)
    (hS : ∀ n ∈ S, 1 ≤ n) (x : ℕ → ℂ) :
    ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ ∈ primChars q,
        ‖∑ n ∈ S, (win h u (Real.log n) : ℂ) * (x n * χ (n : ZMod q))‖ ^ 2
      ≤ (17 / 4) * ∑ n ∈ S, win h u (Real.log n) * ‖x n‖ ^ 2 *
          (Q ^ 2 + 1 + n * (Real.exp h - 1)) := by
  set A := ⌈Real.exp u⌉₊ with hA
  set B := ⌈Real.exp (u + h)⌉₊ with hB
  have hAB : A ≤ B := ceil_exp_mono u h hh
  set y : ℕ → ℂ := fun n => if n ∈ S then x n else 0 with hy
  have hwin : ∀ n ∈ S, win h u (Real.log n) = if n ∈ Finset.Ico A B then 1 else 0 := by
    intro n hn
    rw [win_log_eq h u (hS n hn)]
    simp only [Finset.mem_Ico, hA, hB]
  have hrewrite : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      ∑ n ∈ S, (win h u (Real.log n) : ℂ) * (x n * χ (n : ZMod q)) =
        ∑ n ∈ Finset.Ico A B, y n * χ (n : ZMod q) := by
    intro q χ
    rw [← Finset.sum_filter_add_sum_filter_not S (fun n => n ∈ Finset.Ico A B)]
    rw [Finset.sum_eq_zero (s := S.filter (fun n => n ∉ Finset.Ico A B)) (fun n hn => by
      rw [Finset.mem_filter] at hn
      rw [hwin n hn.1, if_neg hn.2]; simp), add_zero]
    rw [← Finset.sum_subset (Finset.filter_subset (fun n => n ∈ S) (Finset.Ico A B)) (fun n _ hn => by
      simp only [Finset.mem_filter, not_and] at hn
      simp only [hy]
      rw [if_neg (fun h' => hn (by assumption) h')]; simp)]
    refine Finset.sum_congr (by ext n; simp [and_comm]) fun n hn => ?_
    simp only [Finset.mem_filter] at hn
    rw [hwin n hn.2, if_pos hn.1, hy]
    simp [hn.2]
  simp_rw [hrewrite]
  refine (ls_Ico Q hQ A B hAB y).trans ?_
  -- rewrite the right side as a sum over `S ∩ [A, B)`
  have hR : ∑ n ∈ S, win h u (Real.log n) * ‖x n‖ ^ 2 * (Q ^ 2 + 1 + n * (Real.exp h - 1)) =
      ∑ n ∈ Finset.Ico A B, (if n ∈ S then ‖x n‖ ^ 2 * (Q ^ 2 + 1 + n * (Real.exp h - 1)) else 0) := by
    rw [← Finset.sum_filter, ← Finset.sum_filter_add_sum_filter_not S (fun n => n ∈ Finset.Ico A B)]
    rw [Finset.sum_eq_zero (s := S.filter (fun n => n ∉ Finset.Ico A B)) (fun n hn => by
      rw [Finset.mem_filter] at hn
      rw [hwin n hn.1, if_neg hn.2]; simp), add_zero]
    refine Finset.sum_congr (by ext n; simp [and_comm]) fun n hn => ?_
    simp only [Finset.mem_filter] at hn
    rw [hwin n hn.2, if_pos hn.1]; ring
  rw [hR, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  have hnA := (Finset.mem_Ico.mp hn).1
  simp only [hy]
  split_ifs with hnS
  · have hcard := card_window_le u h hh (n := n) ((Nat.le_ceil _).trans (by exact_mod_cast hnA))
    have hQ2 : 0 ≤ Q ^ 2 := sq_nonneg _
    have hx : 0 ≤ ‖x n‖ ^ 2 := sq_nonneg _
    have : (17 / 4 : ℝ) * (Q ^ 2 + ((B - A : ℕ) : ℝ)) * ‖x n‖ ^ 2 ≤
        17 / 4 * (‖x n‖ ^ 2 * (Q ^ 2 + 1 + n * (Real.exp h - 1))) := by nlinarith
    simpa using this
  · simp

/-! ### The hybrid large sieve -/

/-- **Hybrid large sieve**: for `W ≥ 2` and `S ⊂ [1, ∞)`,
`∑_{q ≤ Q} ∑*_χ ∫_{−W}^{W} |∑_{n∈S} x_n χ(n) n^{−iv}|² dv ≤ 100 ∑_{n∈S} |x_n|² (W(Q²+1) + n)`. -/
theorem hybrid_large_sieve (Q : ℝ) (hQ : 1 ≤ Q) {W : ℝ} (hW : 2 ≤ W) (S : Finset ℕ)
    (hS : ∀ n ∈ S, 1 ≤ n) (x : ℕ → ℂ) :
    ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ ∈ primChars q,
        ∫ v in (-W)..W, ‖∑ n ∈ S, x n * χ (n : ZMod q) * ex v (Real.log n)‖ ^ 2
      ≤ 100 * ∑ n ∈ S, ‖x n‖ ^ 2 * (W * (Q ^ 2 + 1) + n) := by
  have hW0 : 0 < W := by linarith
  set h : ℝ := 2 / W with hh
  have hh0 : 0 ≤ h := by positivity
  have hG : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      ∫ v in (-W)..W, ‖∑ n ∈ S, x n * χ (n : ZMod q) * ex v (Real.log n)‖ ^ 2 ≤
        (3 * π / 4) * W ^ 2 *
          ∫ u : ℝ, ‖∑ n ∈ S, (win h u (Real.log n) : ℂ) * (x n * χ (n : ZMod q))‖ ^ 2 :=
    fun q χ => gallagher S (fun n => x n * χ (n : ZMod q)) (fun n => Real.log n) hW0
  refine (Finset.sum_le_sum fun q _ => Finset.sum_le_sum fun χ _ => hG q χ).trans ?_
  simp_rw [← Finset.mul_sum]
  have hint : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), Integrable (fun u : ℝ =>
      ‖∑ n ∈ S, (win h u (Real.log n) : ℂ) * (x n * χ (n : ZMod q))‖ ^ 2) :=
    fun q χ => integrable_winSum_sq h S _ _
  have hinner : ∀ q : ℕ, ∑ χ ∈ primChars q, ∫ u : ℝ,
      ‖∑ n ∈ S, (win h u (Real.log n) : ℂ) * (x n * χ (n : ZMod q))‖ ^ 2 =
      ∫ u : ℝ, ∑ χ ∈ primChars q,
        ‖∑ n ∈ S, (win h u (Real.log n) : ℂ) * (x n * χ (n : ZMod q))‖ ^ 2 :=
    fun q => (integral_finsetSum _ fun χ _ => hint q χ).symm
  rw [Finset.sum_congr rfl fun q _ => hinner q,
    ← integral_finsetSum _ fun q _ => integrable_finsetSum _ fun χ _ => hint q χ]
  -- pointwise large sieve, then integrate the windows
  have hpt : ∀ u : ℝ, ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ ∈ primChars q,
      ‖∑ n ∈ S, (win h u (Real.log n) : ℂ) * (x n * χ (n : ZMod q))‖ ^ 2 ≤
      (17 / 4) * ∑ n ∈ S, win h u (Real.log n) * (‖x n‖ ^ 2 *
          (Q ^ 2 + 1 + n * (Real.exp h - 1))) := by
    intro u
    refine (ls_window Q hQ hh0 u S hS x).trans (le_of_eq ?_)
    congr 1; refine Finset.sum_congr rfl fun n _ => by ring
  have hintR : Integrable (fun u : ℝ => (17 / 4 : ℝ) * ∑ n ∈ S, win h u (Real.log n) *
      (‖x n‖ ^ 2 * (Q ^ 2 + 1 + n * (Real.exp h - 1)))) :=
    (integrable_finsetSum _ fun n _ => (integrable_win h _).mul_const _).const_mul _
  have hmono := integral_mono (integrable_finsetSum _ fun q _ => integrable_finsetSum _
    fun χ _ => hint q χ) hintR hpt
  have hval : ∫ u : ℝ, (17 / 4 : ℝ) * ∑ n ∈ S, win h u (Real.log n) *
      (‖x n‖ ^ 2 * (Q ^ 2 + 1 + n * (Real.exp h - 1))) =
      (17 / 4) * ∑ n ∈ S, h * (‖x n‖ ^ 2 * (Q ^ 2 + 1 + n * (Real.exp h - 1))) := by
    rw [integral_const_mul, integral_finsetSum _ fun n _ => (integrable_win h _).mul_const _]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_mul_const, integral_win hh0]
  rw [hval] at hmono
  have hexp : Real.exp h - 1 ≤ 2 * h := by
    have h1 : |h| ≤ 1 := by
      rw [abs_of_nonneg hh0, hh, div_le_one hW0]; linarith
    have := Real.abs_exp_sub_one_le h1
    rw [abs_of_nonneg hh0] at this
    exact (le_abs_self _).trans this
  have hπ : π < 4 := Real.pi_lt_four
  calc (3 * π / 4) * W ^ 2 * ∫ u : ℝ, ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ ∈ primChars q,
        ‖∑ n ∈ S, (win h u (Real.log n) : ℂ) * (x n * χ (n : ZMod q))‖ ^ 2
      ≤ (3 * π / 4) * W ^ 2 * ((17 / 4) * ∑ n ∈ S, h * (‖x n‖ ^ 2 *
          (Q ^ 2 + 1 + n * (Real.exp h - 1)))) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ ≤ 100 * ∑ n ∈ S, ‖x n‖ ^ 2 * (W * (Q ^ 2 + 1) + n) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_le_sum fun n _ => ?_
        have hx : 0 ≤ ‖x n‖ ^ 2 := sq_nonneg _
        have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have e1 : W ^ 2 * h = 2 * W := by rw [hh]; field_simp
        have hle : W ^ 2 * h * (Q ^ 2 + 1 + n * (Real.exp h - 1)) ≤
            2 * (W * (Q ^ 2 + 1) + 4 * n) := by
          rw [e1]
          have : W * (n * (Real.exp h - 1)) ≤ W * (n * (2 * h)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hn0) hW0.le
          have e2 : W * (n * (2 * h)) = 4 * n := by rw [hh]; field_simp; ring
          nlinarith
        have hQ1 : 0 ≤ W * (Q ^ 2 + 1) := by positivity
        calc 3 * π / 4 * W ^ 2 * (17 / 4 * (h * (‖x n‖ ^ 2 * (Q ^ 2 + 1 + n * (Real.exp h - 1)))))
            = (51 * π / 16) * ‖x n‖ ^ 2 * (W ^ 2 * h * (Q ^ 2 + 1 + n * (Real.exp h - 1))) := by
              ring
          _ ≤ (51 * π / 16) * ‖x n‖ ^ 2 * (2 * (W * (Q ^ 2 + 1) + 4 * n)) :=
              mul_le_mul_of_nonneg_left hle (by positivity)
          _ ≤ 100 * (‖x n‖ ^ 2 * (W * (Q ^ 2 + 1) + n)) := by
              have hπ' : π < 3.15 := Real.pi_lt_d2
              have hA : 0 ≤ ‖x n‖ ^ 2 * (W * (Q ^ 2 + 1) + 4 * n) := by positivity
              have e : 51 * π / 16 * ‖x n‖ ^ 2 * (2 * (W * (Q ^ 2 + 1) + 4 * n)) =
                  (51 * π / 8) * (‖x n‖ ^ 2 * (W * (Q ^ 2 + 1) + 4 * n)) := by ring
              rw [e]
              have h1 : (51 * π / 8) * (‖x n‖ ^ 2 * (W * (Q ^ 2 + 1) + 4 * n)) ≤
                  25 * (‖x n‖ ^ 2 * (W * (Q ^ 2 + 1) + 4 * n)) :=
                mul_le_mul_of_nonneg_right (by linarith) hA
              nlinarith

end Families.Hyp.Montgomery
