/-
Sums against counting functions, for `lem:B2` steps (2)–(4).

`abel_sub_integral`: for `f` smooth, vanishing at `a`, `b` and outside `(a, b)`,
`∑_{a<k≤b} f(k) c(k) − ∫ f = −∫_a^b f'(t) (A(t) − t) dt`, `A(t) = ∑_{k≤t} c(k)` (Mathlib's Abel summation
plus one integration by parts). Specialisations:
* `abs_sum_sub_integral_le` (`c ≡ 1`, `|A(t) − t| ≤ 1`): `|∑ f(n) − ∫ f| ≤ (b − a + 2) sup|f'|`
  (`lem:poisson`(c) at first order);
* `prime_sum_sub_integral_le` (`c(k) = 1_{prime} log k`, `A = θ`, **with the hypothesis `PNT_dlVP`**):
  `|∑_p f(p) log p − ∫ f| ≤ 4N sup|f'| · C₀ 2N/log³(N/2)` for `f` supported in `[N/2, 2N]`, `N ≥ 8`.
  This is the "Stieltjes integration by parts against `dθ`" of steps (2), (3).
-/
import Families.Phase3.C.B2Arith

noncomputable section

open MeasureTheory Set
open scoped Interval

namespace Families.Phase3.C

lemma sum_eq_sum_of_supp {g : ℕ → ℝ} {s₁ s₂ : Finset ℕ}
    (h : ∀ n, g n ≠ 0 → n ∈ s₁ ∧ n ∈ s₂) : ∑ n ∈ s₁, g n = ∑ n ∈ s₂, g n := by
  have h1 : ∑ n ∈ s₁ ∩ s₂, g n = ∑ n ∈ s₁, g n :=
    Finset.sum_subset Finset.inter_subset_left fun n hn hn' => by
      by_contra hne
      exact hn' (Finset.mem_inter.mpr ⟨hn, (h n hne).2⟩)
  have h2 : ∑ n ∈ s₁ ∩ s₂, g n = ∑ n ∈ s₂, g n :=
    Finset.sum_subset Finset.inter_subset_right fun n hn hn' => by
      by_contra hne
      exact hn' (Finset.mem_inter.mpr ⟨(h n hne).1, hn⟩)
  rw [← h1, h2]

lemma deriv_eq_zero_of_supp {f : ℝ → ℝ} {a b : ℝ} (hsupp : ∀ y, f y ≠ 0 → a ≤ y ∧ y ≤ b)
    {t : ℝ} (ht : t < a ∨ b < t) : deriv f t = 0 := by
  have hz : f =ᶠ[nhds t] fun _ => 0 := by
    rcases ht with ht | ht
    · filter_upwards [Iio_mem_nhds ht] with z hz
      by_contra h; exact absurd (hsupp z h).1 (not_le.mpr hz)
    · filter_upwards [Ioi_mem_nhds ht] with z hz
      by_contra h; exact absurd (hsupp z h).2 (not_le.mpr hz)
  rw [hz.deriv_eq, deriv_const]

/-- Abel summation relative to the model `A(t) ≈ t`. -/
theorem abel_sub_integral (c : ℕ → ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hfa : f a = 0) (hfb : f b = 0) (hsupp : ∀ y, f y ≠ 0 → a < y ∧ y < b) :
    ∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f k * c k - ∫ y, f y =
      -∫ t in a..b, deriv f t * ((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) - t) := by
  have hderc : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have habel := sum_mul_eq_sub_sub_integral_mul c ha hab
    (fun t _ => (hf.differentiable one_ne_zero) t) hderc.integrableOn_Icc
  simp only [hfa, hfb, zero_mul, sub_zero, zero_sub] at habel
  rw [← intervalIntegral.integral_of_le hab] at habel
  -- `∫ f = ∫_a^b f = −∫_a^b f'(t) t dt`
  have hint : ∫ y, f y = ∫ y in a..b, f y := by
    rw [intervalIntegral.integral_of_le hab]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_).symm
    by_contra h
    exact hy ⟨(hsupp y h).1, (hsupp y h).2.le⟩
  have hparts : ∫ y in a..b, f y = -∫ t in a..b, deriv f t * t := by
    have := intervalIntegral.integral_mul_deriv_eq_deriv_mul (u := f) (u' := deriv f)
      (v := fun t => t) (v' := fun _ => (1 : ℝ)) (a := a) (b := b)
      (fun x _ => ((hf.differentiable one_ne_zero) x).hasDerivAt) (fun x _ => hasDerivAt_id x)
      (hderc.intervalIntegrable a b) intervalIntegrable_const
    simp only [mul_one] at this
    rw [this, hfa, hfb]; ring
  have hi1 : IntervalIntegrable (fun t => deriv f t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact integrableOn_mul_sum_Icc c ha hderc.integrableOn_Icc
  have hi2 : IntervalIntegrable (fun t => deriv f t * t) volume a b :=
    (hderc.mul continuous_id).intervalIntegrable _ _
  rw [hint, hparts, habel]
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_sub hi1 hi2]
  ring

/-- **`lem:poisson`(c), first order.** `|∑_n f(n) − ∫ f| ≤ (b − a + 2) sup|f'|` for `f` smooth supported in
`[a, b]`, `a ≥ 1`. -/
theorem abs_sum_sub_integral_le {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {M : ℝ}
    (hM : ∀ y, |deriv f y| ≤ M) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
    (hsupp : ∀ y, f y ≠ 0 → a ≤ y ∧ y ≤ b) (S : Finset ℕ) (hS : ∀ n : ℕ, f n ≠ 0 → n ∈ S) :
    |∑ n ∈ S, f n - ∫ y, f y| ≤ (b - a + 2) * M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hsupp' : ∀ y, f y ≠ 0 → a - 1 < y ∧ y < b + 1 := fun y hy =>
    ⟨by linarith [(hsupp y hy).1], by linarith [(hsupp y hy).2]⟩
  have hfa : f (a - 1) = 0 := by by_contra h; linarith [(hsupp _ h).1]
  have hfb : f (b + 1) = 0 := by by_contra h; linarith [(hsupp _ h).2]
  have key := abel_sub_integral (fun _ => (1 : ℝ)) hf (by linarith) (by linarith) hfa hfb hsupp'
  simp only [mul_one] at key
  have hsum : ∑ n ∈ S, f n = ∑ k ∈ Finset.Ioc ⌊a - 1⌋₊ ⌊b + 1⌋₊, f k := by
    apply sum_eq_sum_of_supp
    intro n hn
    refine ⟨hS n hn, Finset.mem_Ioc.mpr ⟨?_, ?_⟩⟩
    · rw [Nat.floor_lt (by linarith)]; exact (hsupp' n hn).1
    · exact Nat.le_floor (hsupp' n hn).2.le
  rw [hsum, key, abs_neg]
  have hbd : ∀ t ∈ Ι (a - 1) (b + 1),
      ‖deriv f t * ((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, (1 : ℝ)) - t)‖ ≤ M := by
    intro t ht
    rw [Set.uIoc_of_le (by linarith)] at ht
    have ht0 : 0 ≤ t := by linarith [ht.1]
    simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one, tsub_zero]
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 : |((⌊t⌋₊ + 1 : ℕ) : ℝ) - t| ≤ 1 := by
      push_cast
      rw [abs_le]
      constructor
      · linarith [Nat.floor_le ht0, Nat.lt_floor_add_one t]
      · linarith [Nat.floor_le ht0, Nat.lt_floor_add_one t]
    calc |deriv f t| * |((⌊t⌋₊ + 1 : ℕ) : ℝ) - t| ≤ M * 1 :=
          mul_le_mul (hM t) h1 (abs_nonneg _) hM0
      _ = M := mul_one M
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  rw [Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < b + 1 - (a - 1))] at this
  linarith

/-- **Steps (2)–(3) of `lem:B2`**: `∑_p f(p) log p = ∫ f + O(N sup|f'| · C₀ 2N/log³(N/2))`, from `PNT_dlVP`. -/
theorem prime_sum_sub_integral_le {C₀ : ℝ}
    (hPNT : ∀ x : ℝ, 2 ≤ x → |Chebyshev.theta x - x| ≤ C₀ * x / Real.log x ^ 3)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) {M : ℝ} (hM : ∀ y, |deriv f y| ≤ M) {N : ℝ} (hN : 8 ≤ N)
    (hsupp : ∀ y, f y ≠ 0 → N / 2 ≤ y ∧ y ≤ 2 * N) (S : Finset ℕ)
    (hS : ∀ n : ℕ, f n ≠ 0 → n ∈ S) :
    |∑ n ∈ S, f n * (if n.Prime then Real.log n else 0) - ∫ y, f y| ≤
      4 * N * (M * (C₀ * (2 * N) / Real.log (N / 2) ^ 3)) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hlogpos : 0 < Real.log (N / 2) := Real.log_pos (by linarith)
  have hC₀ : 0 ≤ C₀ := by
    have h := hPNT 2 le_rfl
    have hl : 0 < Real.log 2 ^ 3 := by positivity
    have : 0 ≤ C₀ * 2 / Real.log 2 ^ 3 := (abs_nonneg _).trans h
    rw [div_nonneg_iff] at this
    rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
    · linarith
    · linarith
  set a : ℝ := N / 4 with ha'
  set b : ℝ := 4 * N with hb'
  have hsupp' : ∀ y, f y ≠ 0 → a < y ∧ y < b := fun y hy =>
    ⟨by linarith [(hsupp y hy).1], by linarith [(hsupp y hy).2]⟩
  have hfa : f a = 0 := by by_contra h; linarith [(hsupp _ h).1]
  have hfb : f b = 0 := by by_contra h; linarith [(hsupp _ h).2]
  set c : ℕ → ℝ := fun k => if k.Prime then Real.log k else 0 with hc
  have key := abel_sub_integral c hf (by positivity) (by linarith) hfa hfb hsupp'
  have hsum : ∑ n ∈ S, f n * (if n.Prime then Real.log n else 0) =
      ∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f k * c k := by
    apply sum_eq_sum_of_supp
    intro n hn
    have hfn : f n ≠ 0 := left_ne_zero_of_mul hn
    refine ⟨hS n hfn, Finset.mem_Ioc.mpr ⟨?_, ?_⟩⟩
    · rw [Nat.floor_lt (by positivity)]; exact (hsupp' n hfn).1
    · exact Nat.le_floor (hsupp' n hfn).2.le
  rw [hsum, key, abs_neg]
  have htheta : ∀ t : ℝ, ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k = Chebyshev.theta t := by
    intro t
    rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  have hbd : ∀ t ∈ Ι a b,
      ‖deriv f t * ((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) - t)‖ ≤ M * (C₀ * (2 * N) / Real.log (N / 2) ^ 3) := by
    intro t _
    rw [htheta, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    by_cases ht : N / 2 ≤ t ∧ t ≤ 2 * N
    · have ht2 : 2 ≤ t := by linarith [ht.1]
      have hlt : Real.log (N / 2) ≤ Real.log t := Real.log_le_log (by linarith) ht.1
      have hp := hPNT t ht2
      have h1 : C₀ * t / Real.log t ^ 3 ≤ C₀ * (2 * N) / Real.log (N / 2) ^ 3 := by
        apply div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left ht.2 hC₀) (by positivity)
        exact pow_le_pow_left₀ hlogpos.le hlt 3
      exact mul_le_mul (hM t) (hp.trans h1) (abs_nonneg _) hM0
    · have ht' : t < N / 2 ∨ 2 * N < t := by
        simp only [not_and_or, not_le] at ht; exact ht
      rw [deriv_eq_zero_of_supp hsupp ht', abs_zero, zero_mul]
      positivity
  have := intervalIntegral.norm_integral_le_of_norm_le_const hbd
  rw [Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < b - a)] at this
  have hba : b - a ≤ 4 * N := by simp only [a, b]; linarith
  have hX : 0 ≤ M * (C₀ * (2 * N) / Real.log (N / 2) ^ 3) := by positivity
  calc |∫ t in a..b, deriv f t * ((∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) - t)|
      ≤ M * (C₀ * (2 * N) / Real.log (N / 2) ^ 3) * (b - a) := this
    _ ≤ M * (C₀ * (2 * N) / Real.log (N / 2) ^ 3) * (4 * N) := mul_le_mul_of_nonneg_left hba hX
    _ = _ := by ring

end Families.Phase3.C
