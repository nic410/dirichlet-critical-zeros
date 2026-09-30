/-
Smooth sums (`lemma-B-majorant.tex`, `lem:poisson`).

We prove `lem:poisson`(a) in the equivalent "summation by parts" form: for `F` smooth, supported in
`[a, b]`, and any frequency `β`,
`|1 − e(β)|^K · |∑_n F(n) e(nβ)| ≤ (b − a + K + 1) sup|F^{(K)}|`
(`sum_smooth_eA_le`), via the discrete identity `∑ ∇F(n) e(nβ) = (1 − e(β)) ∑ F(n) e(nβ)` and
`|∇^K F| ≤ sup|F^{(K)}|`. With `|1 − e(m/M)| ≥ 4/M` for `M ∤ m` (`norm_one_sub_eA_ge`) this is the
TeX's bound `B₀ N^{1/2} (Θ/(N‖β‖))^i` up to the constant (no Poisson summation is needed). Part (c)
(sum versus integral) is proved at first order (`abs_sum_sub_integral_le`), which is all that the
applications need.
-/
import Families.Phase3.C.Deriv

noncomputable section

open scoped ContDiff
open Set MeasureTheory

namespace Families.Phase3.C

lemma eA_add' (x y : ℝ) : eA (x + y) = eA x * eA y := by
  unfold eA; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma norm_eA' (x : ℝ) : ‖eA x‖ = 1 := by
  unfold eA
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma eA_int (m : ℤ) : eA m = 1 := by
  unfold eA
  rw [show (2 * (Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ)) = m * (2 * Real.pi * Complex.I) by
    push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I m

/-! ### Backward differences -/

/-- Backward difference `∇F(x) = F(x) − F(x − 1)`. -/
def bd (F : ℝ → ℂ) : ℝ → ℂ := fun x => F x - F (x - 1)

lemma bd_iter_supp {F : ℝ → ℂ} {a b : ℝ} (h : ∀ y, F y ≠ 0 → a ≤ y ∧ y ≤ b) (k : ℕ) :
    ∀ y, (bd^[k] F) y ≠ 0 → a ≤ y ∧ y ≤ b + k := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    intro y hy
    rw [Function.iterate_succ_apply'] at hy
    by_contra hcon
    apply hy
    simp only [not_and_or, not_le] at hcon
    have e1 : (bd^[k] F) y = 0 := by
      by_contra hne
      have := ih y hne
      rcases hcon with h1 | h1
      · linarith [this.1]
      · push_cast at h1; linarith [this.2]
    have e2 : (bd^[k] F) (y - 1) = 0 := by
      by_contra hne
      have := ih _ hne
      rcases hcon with h1 | h1
      · linarith [this.1]
      · push_cast at h1; linarith [this.2]
    show (bd^[k] F) y - (bd^[k] F) (y - 1) = 0
    rw [e1, e2, sub_zero]

/-- `|∇^k F| ≤ sup |F^{(k)}|`. -/
lemma bd_iter_bound : ∀ (k : ℕ) (F : ℝ → ℂ), ContDiff ℝ k F → ∀ M : ℝ,
    (∀ y, ‖iteratedDeriv k F y‖ ≤ M) → ∀ x, ‖(bd^[k] F) x‖ ≤ M := by
  intro k
  induction k with
  | zero => intro F _ M hM x; simpa using hM x
  | succ k ih =>
    intro F hF M hM x
    rw [Function.iterate_succ_apply]
    have hFk : ContDiff ℝ k F := hF.of_le (by exact_mod_cast Nat.le_succ k)
    have hshift : ContDiff ℝ k (fun z => F (z - 1)) := hFk.comp (contDiff_id.sub contDiff_const)
    refine ih (bd F) (hFk.sub hshift) M ?_ x
    intro y
    have hsub : iteratedDeriv k (bd F) y = iteratedDeriv k F y - iteratedDeriv k F (y - 1) := by
      have hbd : bd F = F - (fun z => F (z - 1)) := rfl
      rw [hbd, iteratedDeriv_sub (hFk.contDiffAt) (hshift.contDiffAt),
        iteratedDeriv_comp_sub_const]
    rw [hsub]
    set G := iteratedDeriv k F with hG
    have hGd : Differentiable ℝ G :=
      hF.differentiable_iteratedDeriv k (by exact_mod_cast Nat.lt_succ_self k)
    have hderiv : ∀ z, deriv G z = iteratedDeriv (k + 1) F z := by
      intro z; rw [hG, iteratedDeriv_succ]
    have := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (s := univ)
      (fun z _ => hGd z) (fun z _ => by rw [hderiv]; exact hM z) convex_univ
      (mem_univ (y - 1)) (mem_univ y)
    simpa using this

/-! ### The summation-by-parts identity -/

lemma sum_range_bd (G : ℝ → ℂ) (β : ℝ) (A : ℤ) (L : ℕ) :
    ∑ i ∈ Finset.range L, bd G ((A : ℝ) + i) * eA (((A : ℝ) + i) * β)
      = (1 - eA β) * ∑ i ∈ Finset.range L, G ((A : ℝ) + i) * eA (((A : ℝ) + i) * β)
        - eA β * G ((A : ℝ) - 1) * eA (((A : ℝ) - 1) * β)
        + eA β * G ((A : ℝ) + L - 1) * eA (((A : ℝ) + L - 1) * β) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have h1 : eA β * eA (((A : ℝ) + L - 1) * β) = eA (((A : ℝ) + L) * β) := by
      rw [← eA_add']; congr 1; ring
    have h2 : ((A : ℝ) + ((L + 1 : ℕ) : ℝ) - 1) = (A : ℝ) + L := by push_cast; ring
    rw [h2]
    unfold bd
    rw [show ((A : ℝ) + (L : ℝ) - 1) = (A : ℝ) + L - 1 from rfl]
    linear_combination (G ((A : ℝ) + L - 1)) * h1

/-- Iterated summation by parts on a window `[A, A + L)`. -/
lemma sum_range_bd_iter {F : ℝ → ℂ} {a b : ℝ} (hsupp : ∀ y, F y ≠ 0 → a ≤ y ∧ y ≤ b) (β : ℝ)
    (K : ℕ) (A : ℤ) (L : ℕ) (hA : (A : ℝ) - 1 < a) (hL : b + K < (A : ℝ) + L) :
    ∀ k ≤ K, (1 - eA β) ^ k * ∑ i ∈ Finset.range L, F ((A : ℝ) + i) * eA (((A : ℝ) + i) * β)
      = ∑ i ∈ Finset.range L, (bd^[k] F) ((A : ℝ) + i) * eA (((A : ℝ) + i) * β) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hk' : k ≤ K := Nat.le_of_succ_le hk
    have hsk := bd_iter_supp hsupp k
    have hz1 : (bd^[k] F) ((A : ℝ) - 1) = 0 := by
      by_contra h; linarith [(hsk _ h).1]
    have hz2 : (bd^[k] F) ((A : ℝ) + L - 1) = 0 := by
      by_contra h
      have := (hsk _ h).2
      have hkK : (k : ℝ) + 1 ≤ K := by exact_mod_cast hk
      linarith
    rw [pow_succ, mul_comm _ (1 - eA β), mul_assoc, ih hk', Function.iterate_succ_apply',
      sum_range_bd, hz1, hz2]
    ring

/-- **`lem:poisson`(a), summation-by-parts form.** -/
theorem sum_smooth_eA_le {F : ℝ → ℂ} {K : ℕ} (hF : ContDiff ℝ K F) {M : ℝ}
    (hM : ∀ y, ‖iteratedDeriv K F y‖ ≤ M) {a b : ℝ} (hab : a ≤ b)
    (hsupp : ∀ y, F y ≠ 0 → a ≤ y ∧ y ≤ b) (S : Finset ℤ) (hS : ∀ n : ℤ, F n ≠ 0 → n ∈ S)
    (β : ℝ) :
    ‖1 - eA β‖ ^ K * ‖∑ n ∈ S, F n * eA (n * β)‖ ≤ (b - a + K + 1) * M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set A : ℤ := ⌈a⌉ with hAdef
  set L : ℕ := (⌊b⌋ - ⌈a⌉ + 1 + K).toNat with hLdef
  have hA1 : (A : ℝ) - 1 < a := by have := Int.ceil_lt_add_one a; rw [hAdef]; linarith
  have hAa : a ≤ (A : ℝ) := Int.le_ceil a
  have hfl : b < (⌊b⌋ : ℝ) + 1 := Int.lt_floor_add_one b
  have hLnn : 0 ≤ ⌊b⌋ - ⌈a⌉ + 1 + (K : ℤ) := by
    have : ⌈a⌉ ≤ ⌊b⌋ + 1 := by
      have h1 : (⌈a⌉ : ℝ) < b + 1 := by have := Int.ceil_lt_add_one a; linarith
      have h2 : ⌈a⌉ < ⌊b⌋ + 1 + 1 := by
        have : (⌈a⌉ : ℝ) < (⌊b⌋ : ℝ) + 1 + 1 := by linarith
        exact_mod_cast this
      omega
    omega
  have hLcast : (L : ℝ) = (⌊b⌋ : ℝ) - A + 1 + K := by
    rw [hLdef]
    have : ((⌊b⌋ - ⌈a⌉ + 1 + K).toNat : ℤ) = ⌊b⌋ - ⌈a⌉ + 1 + K := Int.toNat_of_nonneg hLnn
    have h' : (((⌊b⌋ - ⌈a⌉ + 1 + K).toNat : ℤ) : ℝ) = ((⌊b⌋ - ⌈a⌉ + 1 + K : ℤ) : ℝ) := by
      rw [this]
    push_cast at h'
    rw [← h']
  have hL : b + K < (A : ℝ) + L := by rw [hLcast]; linarith
  -- rewrite the sum over `S` as a sum over the window
  have hwin : ∑ n ∈ S, F n * eA (n * β)
      = ∑ i ∈ Finset.range L, F ((A : ℝ) + i) * eA (((A : ℝ) + i) * β) := by
    set W : Finset ℤ := (Finset.range L).image (fun i : ℕ => A + (i : ℤ))
    have hW : ∑ i ∈ Finset.range L, F ((A : ℝ) + i) * eA (((A : ℝ) + i) * β)
        = ∑ n ∈ W, F n * eA (n * β) := by
      rw [Finset.sum_image (fun i _ j _ h => by simpa using h)]; push_cast; rfl
    rw [hW]
    have hsub1 : ∀ n ∈ S, n ∉ S ∩ W → F n * eA (n * β) = 0 := by
      intro n hn hnW
      by_contra hne
      have hF0 : F n ≠ 0 := left_ne_zero_of_mul hne
      apply hnW
      refine Finset.mem_inter.mpr ⟨hn, ?_⟩
      have hs := hsupp _ hF0
      simp only [W, Finset.mem_image, Finset.mem_range]
      refine ⟨(n - A).toNat, ?_, ?_⟩
      · have h1 : A ≤ n := by
          have : (A : ℝ) < (n : ℝ) + 1 := by linarith [hs.1]
          have : A < n + 1 := by exact_mod_cast this
          omega
        have h2 : (n : ℝ) < A + L := by linarith [hs.2]
        have h2' : n < A + L := by exact_mod_cast h2
        omega
      · have h1 : A ≤ n := by
          have : (A : ℝ) < (n : ℝ) + 1 := by linarith [hs.1]
          have : A < n + 1 := by exact_mod_cast this
          omega
        show A + (((n - A).toNat : ℕ) : ℤ) = n
        omega
    have hsub2 : ∀ n ∈ W, n ∉ S ∩ W → F n * eA (n * β) = 0 := by
      intro n hn hnS
      have : n ∉ S := fun h => hnS (Finset.mem_inter.mpr ⟨h, hn⟩)
      have hF0 : F n = 0 := by by_contra h; exact this (hS n h)
      rw [hF0, zero_mul]
    rw [← Finset.sum_subset (Finset.inter_subset_left) hsub1,
      ← Finset.sum_subset (Finset.inter_subset_right) hsub2]
  rw [hwin, ← norm_pow, ← norm_mul, sum_range_bd_iter hsupp β K A L hA1 hL K le_rfl]
  have hbd := bd_iter_bound K F hF M hM
  calc ‖∑ i ∈ Finset.range L, (bd^[K] F) ((A : ℝ) + i) * eA (((A : ℝ) + i) * β)‖
      ≤ ∑ i ∈ Finset.range L, ‖(bd^[K] F) ((A : ℝ) + i) * eA (((A : ℝ) + i) * β)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range L, M := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul, norm_eA', mul_one]; exact hbd _
    _ = L * M := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (b - a + K + 1) * M := by
        apply mul_le_mul_of_nonneg_right _ hM0
        rw [hLcast]; linarith [Int.floor_le b]

/-- The same for sums over natural numbers (all `y` with `F y ≠ 0` are `≥ a ≥ 0`). -/
theorem sum_smooth_eA_le_nat {F : ℝ → ℂ} {K : ℕ} (hF : ContDiff ℝ K F) {M : ℝ}
    (hM : ∀ y, ‖iteratedDeriv K F y‖ ≤ M) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hsupp : ∀ y, F y ≠ 0 → a ≤ y ∧ y ≤ b) (S : Finset ℕ) (hS : ∀ n : ℕ, F n ≠ 0 → n ∈ S)
    (β : ℝ) :
    ‖1 - eA β‖ ^ K * ‖∑ n ∈ S, F n * eA (n * β)‖ ≤ (b - a + K + 1) * M := by
  have h := sum_smooth_eA_le hF hM hab hsupp (S.map Nat.castEmbedding) ?_ β
  · rw [Finset.sum_map] at h
    simpa using h
  · intro n hn
    have hn0 : (0 : ℤ) ≤ n := by
      have := (hsupp _ hn).1
      have : (0 : ℝ) ≤ n := le_trans ha this
      exact_mod_cast this
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn0
    refine Finset.mem_map.mpr ⟨m, hS m (by simpa using hn), rfl⟩

/-! ### The frequency lower bound `|1 − e(m/M)| ≥ 4/M` -/

lemma norm_one_sub_eA (β : ℝ) : ‖1 - eA β‖ = 2 * |Real.sin (Real.pi * β)| := by
  rw [norm_sub_rev]
  unfold eA
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (β : ℂ)) = Complex.I * ((2 * Real.pi * β : ℝ) : ℂ) by
    push_cast; ring, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show 2 * Real.pi * β / 2 = Real.pi * β by ring, Real.norm_eq_abs, abs_mul, abs_two]

lemma abs_sin_ge {m : ℤ} {M : ℕ} (hM : 0 < M) (hm : ¬ (M : ℤ) ∣ m) :
    2 / (M : ℝ) ≤ |Real.sin (Real.pi * (m / M))| := by
  set r : ℤ := m % M with hr
  have hMz : (0 : ℤ) < M := by exact_mod_cast hM
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (ne_of_gt hMz)
  have hrM : r < M := Int.emod_lt_of_pos _ hMz
  have hrne : r ≠ 0 := by
    intro h; exact hm (Int.dvd_of_emod_eq_zero h)
  have hdecomp : m = M * (m / M) + r := by rw [hr]; linarith [Int.mul_ediv_add_emod m M]
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hsin : |Real.sin (Real.pi * (m / M))| = |Real.sin (Real.pi * (r / M))| := by
    have : Real.pi * ((m : ℝ) / M) = Real.pi * ((r : ℝ) / M) + ((m / M : ℤ) : ℝ) * Real.pi := by
      have hm' : (m : ℝ) = M * ((m / M : ℤ) : ℝ) + r := by exact_mod_cast hdecomp
      rw [hm']; field_simp; ring
    rw [this, Real.sin_add_int_mul_pi, abs_mul, abs_neg_one_zpow, one_mul]
  rw [hsin]
  -- `s = min(r, M − r)`
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (show (1 : ℤ) ≤ r by omega)
  have hrM' : (r : ℝ) ≤ M - 1 := by
    have : r ≤ (M : ℤ) - 1 := by omega
    exact_mod_cast this
  have key : ∀ s : ℝ, 1 ≤ s → s ≤ M / 2 → 2 / (M : ℝ) ≤ Real.sin (Real.pi * (s / M)) := by
    intro s hs1 hs2
    have h0 : 0 ≤ Real.pi * (s / M) := by positivity
    have h1 : Real.pi * (s / M) ≤ Real.pi / 2 := by
      rw [mul_div_assoc']
      rw [div_le_div_iff₀ hMr (by norm_num)]
      nlinarith [Real.pi_pos]
    have := Real.mul_le_sin h0 h1
    have h3 : 2 / Real.pi * (Real.pi * (s / M)) = 2 * s / M := by
      field_simp
    rw [h3] at this
    calc 2 / (M : ℝ) ≤ 2 * s / M := by
          apply div_le_div_of_nonneg_right _ hMr.le; linarith
      _ ≤ _ := this
  rcases le_or_gt (r : ℝ) (M / 2) with hle | hgt
  · have := key r hr1 hle
    exact this.trans (le_abs_self _)
  · have h2 := key ((M : ℝ) - r) (by linarith) (by linarith)
    have : Real.sin (Real.pi * (((M : ℝ) - r) / M)) = Real.sin (Real.pi * (r / M)) := by
      rw [show Real.pi * (((M : ℝ) - r) / M) = Real.pi - Real.pi * (r / M) by field_simp,
        Real.sin_pi_sub]
    rw [this] at h2
    exact h2.trans (le_abs_self _)

/-- `|1 − e(m/M)| ≥ 4/M` when `M ∤ m`. -/
theorem norm_one_sub_eA_ge {m : ℤ} {M : ℕ} (hM : 0 < M) (hm : ¬ (M : ℤ) ∣ m) :
    4 / (M : ℝ) ≤ ‖1 - eA (m / M)‖ := by
  rw [norm_one_sub_eA]
  have := abs_sin_ge hM hm
  have h : 4 / (M : ℝ) = 2 * (2 / M) := by ring
  rw [h]; linarith

/-- Combined: for `M ∤ m`, `|∑ F(n) e(nm/M)| ≤ (b − a + K + 1) sup|F^{(K)}| (M/4)^K`. -/
theorem sum_smooth_eA_rat_le {F : ℝ → ℂ} {K : ℕ} (hF : ContDiff ℝ K F) {Mb : ℝ}
    (hM : ∀ y, ‖iteratedDeriv K F y‖ ≤ Mb) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hsupp : ∀ y, F y ≠ 0 → a ≤ y ∧ y ≤ b) (S : Finset ℕ) (hS : ∀ n : ℕ, F n ≠ 0 → n ∈ S)
    {m : ℤ} {M : ℕ} (hMpos : 0 < M) (hm : ¬ (M : ℤ) ∣ m) :
    ‖∑ n ∈ S, F n * eA (n * (m / M))‖ ≤ (b - a + K + 1) * Mb * ((M : ℝ) / 4) ^ K := by
  have h := sum_smooth_eA_le_nat hF hM ha hab hsupp S hS (m / M)
  have hlow := norm_one_sub_eA_ge hMpos hm
  have hMr : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hpos : 0 < (4 / (M : ℝ)) ^ K := by positivity
  have hle : (4 / (M : ℝ)) ^ K ≤ ‖1 - eA (m / M)‖ ^ K :=
    pow_le_pow_left₀ (by positivity) hlow K
  have h2 : (4 / (M : ℝ)) ^ K * ‖∑ n ∈ S, F n * eA (n * (m / M))‖ ≤ (b - a + K + 1) * Mb :=
    le_trans (mul_le_mul_of_nonneg_right hle (norm_nonneg _)) h
  have h3 : ((M : ℝ) / 4) ^ K * (4 / (M : ℝ)) ^ K = 1 := by
    rw [← mul_pow]; field_simp; simp
  calc ‖∑ n ∈ S, F n * eA (n * (m / M))‖
      = ((M : ℝ) / 4) ^ K * ((4 / (M : ℝ)) ^ K * ‖∑ n ∈ S, F n * eA (n * (m / M))‖) := by
        rw [← mul_assoc, h3, one_mul]
    _ ≤ ((M : ℝ) / 4) ^ K * ((b - a + K + 1) * Mb) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

end Families.Phase3.C
