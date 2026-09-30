/-
A small derivative-bound ("symbol") toolkit.

All weights used in the Poisson / summation-by-parts steps of `lem:B1`, `lem:B2` and `prop:TIsharp`
(`lemma-B-majorant.tex` `eqB:Fjt`, `eqB:derivs`) are products of a dyadic bump `ψ_j` with factors of
the form `g(c · log y)`, `g` smooth, `c ≥ 1`. On `y ∈ [N/2, 2N]` such a factor satisfies
`‖d^k/dy^k g(c log y)‖ ≤ K! C (2cK/N)^k` (Faà di Bruno bound `norm_iteratedFDerivWithin_comp_le`),
and products multiply the amplitudes (`norm_iteratedFDerivWithin_mul_le`).

`SymB f s K A σ` : `‖f^{(k)}(y)‖ ≤ A σ^k` for `k ≤ K`, `y ∈ s`.
-/
import Families.Basic

noncomputable section

open scoped ContDiff Nat
open Set

namespace Families.Phase3.C

/-- Symbol bound on `s`: `‖f^{(k)}(y)‖ ≤ A σ^k` for all `k ≤ K` and `y ∈ s`. -/
def SymB {𝔸 : Type*} [NormedAddCommGroup 𝔸] [NormedSpace ℝ 𝔸] (f : ℝ → 𝔸) (s : Set ℝ) (K : ℕ)
    (A σ : ℝ) : Prop :=
  ∀ k ≤ K, ∀ y ∈ s, ‖iteratedDeriv k f y‖ ≤ A * σ ^ k

section general

variable {𝔸 : Type*} [NormedAddCommGroup 𝔸] [NormedSpace ℝ 𝔸]

lemma norm_iteratedDeriv_eq_within (f : ℝ → 𝔸) {U : Set ℝ} (hU : IsOpen U) {y : ℝ} (hy : y ∈ U)
    (k : ℕ) : ‖iteratedDeriv k f y‖ = ‖iteratedFDerivWithin ℝ k f U y‖ := by
  rw [iteratedFDerivWithin_of_isOpen k hU hy, norm_iteratedFDeriv_eq_norm_iteratedDeriv]

lemma SymB.amp_nonneg {f : ℝ → 𝔸} {s : Set ℝ} {K : ℕ} {A σ : ℝ} (h : SymB f s K A σ) {y : ℝ}
    (hy : y ∈ s) : 0 ≤ A := by
  have := h 0 (Nat.zero_le _) y hy
  simp only [pow_zero, mul_one] at this
  exact (norm_nonneg _).trans this

lemma SymB.mono {f : ℝ → 𝔸} {s : Set ℝ} {K : ℕ} {A A' σ σ' : ℝ} (h : SymB f s K A σ)
    (hA : A ≤ A') (hσ0 : 0 ≤ σ) (hσ : σ ≤ σ') : SymB f s K A' σ' := by
  intro k hk y hy
  have hA0 := h.amp_nonneg hy
  calc ‖iteratedDeriv k f y‖ ≤ A * σ ^ k := h k hk y hy
    _ ≤ A' * σ ^ k := mul_le_mul_of_nonneg_right hA (pow_nonneg hσ0 _)
    _ ≤ A' * σ' ^ k := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hσ0 hσ _) (hA0.trans hA)

lemma SymB.subset {f : ℝ → 𝔸} {s s' : Set ℝ} {K : ℕ} {A σ : ℝ} (h : SymB f s K A σ)
    (hs : s' ⊆ s) : SymB f s' K A σ := fun k hk y hy => h k hk y (hs hy)

lemma SymB.of_le {f : ℝ → 𝔸} {s : Set ℝ} {K K' : ℕ} {A σ : ℝ} (h : SymB f s K A σ)
    (hK : K' ≤ K) : SymB f s K' A σ := fun k hk y hy => h k (hk.trans hK) y hy

end general

/-! ### Products -/

theorem SymB.mul {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] {f g : ℝ → 𝔸} {U s : Set ℝ}
    (hU : IsOpen U) (hs : s ⊆ U) {K : ℕ} {A B σ : ℝ}
    (hf : ContDiffOn ℝ K f U) (hg : ContDiffOn ℝ K g U) (hσ : 0 ≤ σ)
    (hfb : SymB f s K A σ) (hgb : SymB g s K B σ) :
    SymB (fun y => f y * g y) s K (2 ^ K * A * B) σ := by
  intro k hk y hy
  have hyU := hs hy
  have hA := hfb.amp_nonneg hy
  have hB := hgb.amp_nonneg hy
  rw [norm_iteratedDeriv_eq_within _ hU hyU]
  have hkK : ((k : ℕ) : WithTop ℕ∞) ≤ (K : WithTop ℕ∞) := by exact_mod_cast hk
  refine (norm_iteratedFDerivWithin_mul_le hf hg hU.uniqueDiffOn hyU hkK).trans ?_
  have hterm : ∀ i ∈ Finset.range (k + 1),
      (k.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i f U y‖ * ‖iteratedFDerivWithin ℝ (k - i) g U y‖
        ≤ (k.choose i : ℝ) * (A * B * σ ^ k) := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [← norm_iteratedDeriv_eq_within _ hU hyU, ← norm_iteratedDeriv_eq_within _ hU hyU]
    have h1 := hfb i (hik.trans hk) y hy
    have h2 := hgb (k - i) ((Nat.sub_le _ _).trans hk) y hy
    have hσk : σ ^ i * σ ^ (k - i) = σ ^ k := by rw [← pow_add, Nat.add_sub_cancel' hik]
    have hc : (0 : ℝ) ≤ k.choose i := Nat.cast_nonneg _
    calc (k.choose i : ℝ) * ‖iteratedDeriv i f y‖ * ‖iteratedDeriv (k - i) g y‖
        ≤ (k.choose i : ℝ) * (A * σ ^ i) * (B * σ ^ (k - i)) := by
          gcongr
      _ = (k.choose i : ℝ) * (A * B * σ ^ k) := by rw [← hσk]; ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  have hsum : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) = 2 ^ k := by
    exact_mod_cast Nat.sum_range_choose k
  rw [hsum]
  have h2k : (2 : ℝ) ^ k ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) hk
  have := mul_nonneg (mul_nonneg hA hB) (pow_nonneg hσ k)
  nlinarith

/-! ### Real-valued functions viewed in `ℂ` -/

theorem SymB.ofReal {f : ℝ → ℝ} {U s : Set ℝ} (hU : IsOpen U) (hs : s ⊆ U) {K : ℕ} {A σ : ℝ}
    (hf : ContDiffOn ℝ K f U) (h : SymB f s K A σ) :
    SymB (fun y => (f y : ℂ)) s K A σ := by
  intro k hk y hy
  have hyU := hs hy
  rw [norm_iteratedDeriv_eq_within _ hU hyU]
  have hkK : ((k : ℕ) : WithTop ℕ∞) ≤ (K : WithTop ℕ∞) := by exact_mod_cast hk
  have := LinearIsometry.norm_iteratedFDerivWithin_comp_left (𝕜 := ℝ) Complex.ofRealLI
    ((hf y hyU)) hU.uniqueDiffOn hyU hkK
  have hcomp : (fun y => (f y : ℂ)) = (Complex.ofRealLI ∘ f) := rfl
  rw [hcomp, this, ← norm_iteratedDeriv_eq_within _ hU hyU]
  exact h k hk y hy

/-! ### Composition with `c · log` -/

lemma iteratedDeriv_log_succ {y : ℝ} (m : ℕ) :
    iteratedDeriv (m + 1) Real.log y = (-1) ^ m * (m ! : ℝ) * y ^ (-1 - (m : ℤ)) := by
  rw [iteratedDeriv_succ', Real.deriv_log', iteratedDeriv_eq_iterate, iter_deriv_inv]

lemma norm_iteratedDeriv_log_succ {y : ℝ} (hy : 0 < y) (m : ℕ) :
    ‖iteratedDeriv (m + 1) Real.log y‖ = (m ! : ℝ) / y ^ (m + 1) := by
  rw [iteratedDeriv_log_succ, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Real.norm_natCast, Real.norm_eq_abs, abs_of_pos (zpow_pos hy _)]
  rw [show (-1 - (m : ℤ)) = -((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
    div_eq_mul_inv]

theorem SymB.comp_log {𝔸 : Type*} [NormedAddCommGroup 𝔸] [NormedSpace ℝ 𝔸] {g : ℝ → 𝔸} {K : ℕ}
    (hg : ContDiff ℝ K g) {c N C : ℝ} (hc : 1 ≤ c) (hN : 0 < N)
    (hgb : ∀ y ∈ Icc (N / 2) (2 * N), ∀ i ≤ K, ‖iteratedDeriv i g (c * Real.log y)‖ ≤ C) :
    SymB (fun y => g (c * Real.log y)) (Icc (N / 2) (2 * N)) K (K ! * C) (2 * c * K / N) := by
  intro k hk y hy
  have hy0 : 0 < y := lt_of_lt_of_le (by linarith) hy.1
  have hyU : y ∈ Ioi (0 : ℝ) := hy0
  have hC : 0 ≤ C := by
    have := hgb y hy 0 (Nat.zero_le _)
    simp only [iteratedDeriv_zero] at this
    exact (norm_nonneg _).trans this
  set f : ℝ → ℝ := fun y => c * Real.log y with hf
  have hfC : ContDiffOn ℝ K f (Ioi 0) := by
    refine contDiffOn_const.mul (Real.contDiffOn_log.mono ?_)
    intro x hx; exact ne_of_gt hx
  have hcomp : (fun y => g (c * Real.log y)) = g ∘ f := rfl
  rw [hcomp, norm_iteratedDeriv_eq_within _ isOpen_Ioi hyU]
  have hkK : ((k : ℕ) : WithTop ℕ∞) ≤ (K : WithTop ℕ∞) := by exact_mod_cast hk
  set D : ℝ := 2 * c * K / N with hD
  have hD0 : 0 ≤ D := by positivity
  have hCg : ∀ i ≤ k, ‖iteratedFDerivWithin ℝ i g univ (f y)‖ ≤ C := by
    intro i hi
    rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hgb y hy i (hi.trans hk)
  have hDf : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDerivWithin ℝ i f (Ioi 0) y‖ ≤ D ^ i := by
    intro i hi1 hik
    rw [← norm_iteratedDeriv_eq_within _ isOpen_Ioi hyU]
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    have hlog : ContDiffAt ℝ (↑(m + 1)) Real.log y :=
      Real.contDiffAt_log.mpr (ne_of_gt hy0)
    rw [hf, iteratedDeriv_const_mul c hlog, norm_mul, Real.norm_eq_abs, abs_of_pos (by linarith),
      norm_iteratedDeriv_log_succ hy0]
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
    have hmK : (m ! : ℝ) ≤ (K : ℝ) ^ (m + 1) := by
      have h1 : (m ! : ℝ) ≤ (m : ℝ) ^ m := by exact_mod_cast Nat.factorial_le_pow m
      have h2 : (m : ℝ) ^ m ≤ (K : ℝ) ^ m :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast (show m ≤ K by omega)) m
      have h3 : (K : ℝ) ^ m ≤ (K : ℝ) ^ (m + 1) := pow_le_pow_right₀ hK1 (Nat.le_succ m)
      linarith
    have hcpow : c ≤ c ^ (m + 1) := by
      calc c = c ^ 1 := (pow_one c).symm
        _ ≤ c ^ (m + 1) := pow_le_pow_right₀ hc (by omega)
    have hy2 : (2 / N) ^ (m + 1) * y ^ (m + 1) ≥ 1 := by
      rw [← mul_pow]
      have : 1 ≤ 2 / N * y := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hN]; linarith [hy.1]
      exact one_le_pow₀ this
    have hypos : 0 < y ^ (m + 1) := pow_pos hy0 _
    rw [show D = c * (K : ℝ) * (2 / N) by rw [hD]; ring]
    rw [mul_pow, mul_pow]
    have hfact : (m ! : ℝ) * y⁻¹ ^ (m + 1) ≤ (K : ℝ) ^ (m + 1) * (2 / N) ^ (m + 1) := by
      have hyinv : y⁻¹ ^ (m + 1) ≤ (2 / N) ^ (m + 1) := by
        rw [inv_pow]
        rw [inv_le_iff_one_le_mul₀ hypos]; linarith
      exact mul_le_mul hmK hyinv (by positivity) (by positivity)
    calc c * ((m ! : ℝ) * (y ^ (m + 1))⁻¹)
        = c * ((m ! : ℝ) * y⁻¹ ^ (m + 1)) := by rw [inv_pow]
      _ ≤ c ^ (m + 1) * ((K : ℝ) ^ (m + 1) * (2 / N) ^ (m + 1)) :=
          mul_le_mul hcpow hfact (by positivity) (by positivity)
      _ = _ := by ring
  have hmain := norm_iteratedFDerivWithin_comp_le (g := g) (f := f) (hg.contDiffOn) hfC hkK
    uniqueDiffOn_univ isOpen_Ioi.uniqueDiffOn (mapsTo_univ _ _) hyU hCg hDf
  refine hmain.trans ?_
  have hkf : (k ! : ℝ) ≤ K ! := by exact_mod_cast Nat.factorial_le hk
  have : 0 ≤ C * D ^ k := mul_nonneg hC (pow_nonneg hD0 k)
  calc (k ! : ℝ) * C * D ^ k = (k ! : ℝ) * (C * D ^ k) := by ring
    _ ≤ (K ! : ℝ) * (C * D ^ k) := mul_le_mul_of_nonneg_right hkf this
    _ = (K ! : ℝ) * C * D ^ k := by ring

/-! ### Globalisation through a bump supported in `[a, b] ⊂ (0, ∞)` -/

lemma eventually_zero_of_bump {ψ : ℝ → ℝ} {a b : ℝ} (hsupp : ∀ y, ψ y ≠ 0 → a ≤ y ∧ y ≤ b)
    (G : ℝ → ℂ) {y : ℝ} (hy : y < a ∨ b < y) :
    (fun z => (ψ z : ℂ) * G z) =ᶠ[nhds y] fun _ => 0 := by
  rcases hy with hy | hy
  · filter_upwards [Iio_mem_nhds hy] with z hz
    have : ψ z = 0 := by
      by_contra h; exact absurd (hsupp z h).1 (not_le.mpr hz)
    simp [this]
  · filter_upwards [Ioi_mem_nhds hy] with z hz
    have : ψ z = 0 := by
      by_contra h; exact absurd (hsupp z h).2 (not_le.mpr hz)
    simp [this]

theorem contDiff_bump_mul {ψ : ℝ → ℝ} {K : ℕ} (hψ : ContDiff ℝ K ψ) {a b : ℝ} (ha : 0 < a)
    (hsupp : ∀ y, ψ y ≠ 0 → a ≤ y ∧ y ≤ b) {G : ℝ → ℂ} (hG : ContDiffOn ℝ K G (Ioi 0)) :
    ContDiff ℝ K (fun y => (ψ y : ℂ) * G y) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  rcases lt_or_ge 0 y with hy | hy
  · have h1 : ContDiffOn ℝ K (fun y => (ψ y : ℂ) * G y) (Ioi 0) :=
      (Complex.ofRealCLM.contDiff.comp hψ).contDiffOn.mul hG
    exact h1.contDiffAt (Ioi_mem_nhds hy)
  · exact contDiffAt_const.congr_of_eventuallyEq
      (eventually_zero_of_bump hsupp G (Or.inl (lt_of_le_of_lt hy ha)))

theorem iteratedDeriv_bump_mul_eq_zero {ψ : ℝ → ℝ} {a b : ℝ}
    (hsupp : ∀ y, ψ y ≠ 0 → a ≤ y ∧ y ≤ b) (G : ℝ → ℂ) (k : ℕ) {y : ℝ} (hy : y < a ∨ b < y) :
    iteratedDeriv k (fun z => (ψ z : ℂ) * G z) y = 0 := by
  rw [(eventually_zero_of_bump hsupp G hy).iteratedDeriv_eq, iteratedDeriv_const]
  split_ifs <;> rfl

/-- Global bound: if `F = ψ · G` with `ψ` supported in `[a, b] ⊂ (0,∞)` and `F` satisfies a symbol
bound on `[a, b]`, then the bound holds on all of `ℝ` (the derivatives vanish off `[a, b]`). -/
theorem global_of_bump {ψ : ℝ → ℝ} {a b : ℝ} (hsupp : ∀ y, ψ y ≠ 0 → a ≤ y ∧ y ≤ b)
    {G : ℝ → ℂ} {K : ℕ} {A σ : ℝ} (hA : 0 ≤ A) (hσ : 0 ≤ σ)
    (h : SymB (fun z => (ψ z : ℂ) * G z) (Icc a b) K A σ) :
    ∀ k ≤ K, ∀ y, ‖iteratedDeriv k (fun z => (ψ z : ℂ) * G z) y‖ ≤ A * σ ^ k := by
  intro k hk y
  by_cases hy : y ∈ Icc a b
  · exact h k hk y hy
  · have hy' : y < a ∨ b < y := by
      simp only [mem_Icc, not_and_or, not_le] at hy; exact hy
    rw [iteratedDeriv_bump_mul_eq_zero hsupp G k hy', norm_zero]
    positivity

end Families.Phase3.C
