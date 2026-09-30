/-
Step (4) of `lem:B2` (the term `Λ_R²`), and small analytic helpers.

`sum_F_LamR_sq`: for `F` smooth, supported in `[a, b] ⊂ [0, ∞)`, with `|F^{(K)}| ≤ M_K`,
`|∑_n F(n) Λ_R(n)² − G(R) ∑_n F(n)| ≤ R² (b − a + K + 1) M_K (R²/4)^K`
(orthogonality of Ramanujan sums, `sum_F_ramanujan_mul_le`). This is also the input of
`eqB:norms` (`‖a♯‖² ≪ Lℓ`) in `prop:TIsharp`.
-/
import Families.Phase3.C.B2Weights

noncomputable section

open scoped ContDiff Nat ArithmeticFunction.Moebius
open Set ArithmeticFunction

namespace Families.Phase3.C

open Families

/-! ### Helpers -/

/-- Polynomials are dominated by exponentials: `(x+1)^m ≤ C e^{cx}` for `x ≥ 0`. -/
lemma pow_le_exp_mul (m : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x : ℝ, 0 ≤ x → (x + 1) ^ m ≤ C * Real.exp (c * x) := by
  have hcm : 0 < c ^ m := pow_pos hc m
  refine ⟨2 ^ m * (1 + (m ! : ℝ) / c ^ m), ?_, fun x hx => ?_⟩
  · have : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
    have : 0 ≤ (m ! : ℝ) / c ^ m := by positivity
    nlinarith
  have hexp1 : 1 ≤ Real.exp (c * x) := Real.one_le_exp (by positivity)
  have hxm : x ^ m ≤ (m ! : ℝ) / c ^ m * Real.exp (c * x) := by
    have h := Real.pow_div_factorial_le_exp (c * x) (by positivity) m
    rw [mul_pow, div_le_iff₀ (by positivity)] at h
    rw [div_mul_eq_mul_div, le_div_iff₀ hcm]
    nlinarith
  have hmax : (x + 1) ^ m ≤ 2 ^ m * (1 + x ^ m) := by
    rcases le_or_gt x 1 with h1 | h1
    · have : (x + 1) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      have : (0 : ℝ) ≤ 2 ^ m * x ^ m := by positivity
      nlinarith
    · have : (x + 1) ^ m ≤ (2 * x) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
      rw [mul_pow] at this
      have : (0 : ℝ) ≤ 2 ^ m := by positivity
      nlinarith
  calc (x + 1) ^ m ≤ 2 ^ m * (1 + x ^ m) := hmax
    _ ≤ 2 ^ m * (Real.exp (c * x) + (m ! : ℝ) / c ^ m * Real.exp (c * x)) := by gcongr
    _ = 2 ^ m * (1 + (m ! : ℝ) / c ^ m) * Real.exp (c * x) := by ring

/-- `∑_{j < B} 1/(j+1)² ≤ 2`. -/
lemma sum_inv_sq_le_two (B : ℕ) : ∑ j ∈ Finset.range B, 1 / ((j : ℝ) + 1) ^ 2 ≤ 2 := by
  suffices h : ∀ B : ℕ, 1 ≤ B → ∑ j ∈ Finset.range B, 1 / ((j : ℝ) + 1) ^ 2 ≤ 2 - 1 / (B : ℝ) by
    rcases Nat.eq_zero_or_pos B with hB | hB
    · subst hB; simp
    · have h1 := h B hB
      have h2 : (0 : ℝ) ≤ 1 / (B : ℝ) := by positivity
      linarith
  intro B hB
  induction B, hB using Nat.le_induction with
  | base => norm_num
  | succ B hB ih =>
    rw [Finset.sum_range_succ]
    have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
    have key : 1 / ((B : ℝ) + 1) ^ 2 ≤ 1 / (B : ℝ) - 1 / ((B : ℝ) + 1) := by
      rw [div_sub_div _ _ hB0.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    push_cast
    linarith

/-- The iterated derivatives of `ofReal ∘ f` have the same norms as those of `f`. -/
lemma norm_iteratedDeriv_ofReal {f : ℝ → ℝ} {K : ℕ} (hf : ContDiff ℝ K f) {k : ℕ} (hk : k ≤ K)
    (y : ℝ) : ‖iteratedDeriv k (fun y => (f y : ℂ)) y‖ = ‖iteratedDeriv k f y‖ := by
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have : (fun y => (f y : ℂ)) = Complex.ofRealLI ∘ f := rfl
  rw [this]
  exact LinearIsometry.norm_iteratedFDeriv_comp_left Complex.ofRealLI hf.contDiffAt
    (by exact_mod_cast hk)

/-! ### Step (4): `∑ F Λ_R² = G(R) ∑ F + O(·)` -/

lemma LamR_sq_expand (R n : ℕ) :
    ((PrimeSetup.LamR R n : ℝ) : ℂ) ^ 2 =
      ∑ r ∈ Finset.Icc 1 R, ∑ r' ∈ Finset.Icc 1 R,
        (((μ r : ℝ) / Nat.totient r * ((μ r' : ℝ) / Nat.totient r') : ℝ) : ℂ) *
          (ramanujan r n * ramanujan r' n) := by
  unfold PrimeSetup.LamR
  push_cast
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r' _ => ?_
  conv_rhs => rw [← ramanujan_re_coe r n, ← ramanujan_re_coe r' n]
  ring

theorem sum_F_LamR_sq {F : ℝ → ℝ} {K : ℕ} (hF : ContDiff ℝ K F) {Mb : ℝ}
    (hM : ∀ y, |iteratedDeriv K F y| ≤ Mb) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hsupp : ∀ y, F y ≠ 0 → a ≤ y ∧ y ≤ b) (S : Finset ℕ) (hS : ∀ n : ℕ, F n ≠ 0 → n ∈ S)
    (R : ℕ) :
    |∑ n ∈ S, F n * PrimeSetup.LamR R n ^ 2 - Gsum R * ∑ n ∈ S, F n| ≤
      (R : ℝ) ^ 2 * ((b - a + K + 1) * Mb * (((R : ℝ) ^ 2) / 4) ^ K) := by
  have hM0 : 0 ≤ Mb := (abs_nonneg _).trans (hM 0)
  set FC : ℝ → ℂ := fun y => (F y : ℂ) with hFC
  have hFCc : ContDiff ℝ K FC := Complex.ofRealCLM.contDiff.comp hF
  have hMC : ∀ y, ‖iteratedDeriv K FC y‖ ≤ Mb := fun y => by
    rw [hFC, norm_iteratedDeriv_ofReal hF le_rfl, Real.norm_eq_abs]; exact hM y
  have hsuppC : ∀ y, FC y ≠ 0 → a ≤ y ∧ y ≤ b := fun y hy =>
    hsupp y (fun h => hy (by simp [hFC, h]))
  have hSC : ∀ n : ℕ, FC n ≠ 0 → n ∈ S := fun n hn => hS n (fun h => hn (by simp [hFC, h]))
  set Bd : ℝ := (b - a + K + 1) * Mb * (((R : ℝ) ^ 2) / 4) ^ K with hBd
  have hBd0 : 0 ≤ Bd := by
    have : 0 ≤ b - a + K + 1 := by linarith
    positivity
  -- complexify
  set w : ℕ → ℕ → ℝ := fun r r' => (μ r : ℝ) / Nat.totient r * ((μ r' : ℝ) / Nat.totient r')
  have hkey : ((∑ n ∈ S, F n * PrimeSetup.LamR R n ^ 2 - Gsum R * ∑ n ∈ S, F n : ℝ) : ℂ) =
      ∑ r ∈ Finset.Icc 1 R, ∑ r' ∈ Finset.Icc 1 R, ((w r r' : ℝ) : ℂ) *
        (∑ n ∈ S, FC n * (ramanujan r n * ramanujan r' n) -
          (if r = r' then (Nat.totient r : ℂ) * ∑ n ∈ S, FC n else 0)) := by
    have h1 : ((∑ n ∈ S, F n * PrimeSetup.LamR R n ^ 2 : ℝ) : ℂ) =
        ∑ r ∈ Finset.Icc 1 R, ∑ r' ∈ Finset.Icc 1 R, ((w r r' : ℝ) : ℂ) *
          ∑ n ∈ S, FC n * (ramanujan r n * ramanujan r' n) := by
      push_cast
      simp_rw [LamR_sq_expand, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r' _ => ?_
      refine Finset.sum_congr rfl fun n _ => ?_
      simp only [hFC, w]; push_cast; ring
    have h2 : ((Gsum R * ∑ n ∈ S, F n : ℝ) : ℂ) =
        ∑ r ∈ Finset.Icc 1 R, ∑ r' ∈ Finset.Icc 1 R, ((w r r' : ℝ) : ℂ) *
          (if r = r' then (Nat.totient r : ℂ) * ∑ n ∈ S, FC n else 0) := by
      have : ∀ r ∈ Finset.Icc 1 R, ∑ r' ∈ Finset.Icc 1 R, ((w r r' : ℝ) : ℂ) *
          (if r = r' then (Nat.totient r : ℂ) * ∑ n ∈ S, FC n else 0) =
            (((μ r : ℝ) ^ 2 / Nat.totient r : ℝ) : ℂ) * ∑ n ∈ S, FC n := by
        intro r hr
        have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
        have hφ : (Nat.totient r : ℂ) ≠ 0 := by
          exact_mod_cast (Nat.totient_pos.mpr hr1).ne'
        simp_rw [mul_ite, mul_zero]
        rw [Finset.sum_ite_eq (Finset.Icc 1 R) r, if_pos hr]
        simp only [w]; push_cast
        field_simp
      rw [Finset.sum_congr rfl this, ← Finset.sum_mul, Gsum]
      push_cast; simp only [hFC]
    rw [Complex.ofReal_sub, h1, h2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r' _ => ?_
    ring
  have hterm : ∀ r ∈ Finset.Icc 1 R, ∀ r' ∈ Finset.Icc 1 R,
      ‖((w r r' : ℝ) : ℂ) * (∑ n ∈ S, FC n * (ramanujan r n * ramanujan r' n) -
          (if r = r' then (Nat.totient r : ℂ) * ∑ n ∈ S, FC n else 0))‖ ≤ Bd := by
    intro r hr r' hr'
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hr1' : 1 ≤ r' := (Finset.mem_Icc.mp hr').1
    have hφ : (0 : ℝ) < Nat.totient r := by exact_mod_cast Nat.totient_pos.mpr hr1
    have hφ' : (0 : ℝ) < Nat.totient r' := by exact_mod_cast Nat.totient_pos.mpr hr1'
    have hb := sum_F_ramanujan_mul_le hr1 hr1' hFCc hMC ha hab hsuppC S hSC
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hw : |w r r'| ≤ 1 / Nat.totient r * (1 / Nat.totient r') := by
      simp only [w]
      rw [abs_mul, abs_div, abs_div, Nat.abs_cast, Nat.abs_cast]
      have hμ : |(μ r : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := r)
      have hμ' : |(μ r' : ℝ)| ≤ 1 := by
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := r')
      gcongr
    have hrr : ((r * r' : ℕ) : ℝ) / 4 ≤ ((R : ℝ) ^ 2) / 4 := by
      have h1 : (r : ℝ) ≤ R := by exact_mod_cast (Finset.mem_Icc.mp hr).2
      have h2 : (r' : ℝ) ≤ R := by exact_mod_cast (Finset.mem_Icc.mp hr').2
      push_cast
      gcongr
      nlinarith [Nat.cast_nonneg (α := ℝ) r, Nat.cast_nonneg (α := ℝ) r']
    have hb' : ‖∑ n ∈ S, FC n * (ramanujan r n * ramanujan r' n) -
        (if r = r' then (Nat.totient r : ℂ) * ∑ n ∈ S, FC n else 0)‖ ≤
          Nat.totient r * Nat.totient r' * Bd := by
      refine hb.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      rw [hBd]
      have : 0 ≤ b - a + K + 1 := by linarith
      gcongr
    calc |w r r'| * ‖∑ n ∈ S, FC n * (ramanujan r n * ramanujan r' n) -
          (if r = r' then (Nat.totient r : ℂ) * ∑ n ∈ S, FC n else 0)‖
        ≤ (1 / Nat.totient r * (1 / Nat.totient r')) * (Nat.totient r * Nat.totient r' * Bd) :=
          mul_le_mul hw hb' (norm_nonneg _) (by positivity)
      _ = Bd := by field_simp
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hkey]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ r ∈ Finset.Icc 1 R, ‖∑ r' ∈ Finset.Icc 1 R, ((w r r' : ℝ) : ℂ) *
          (∑ n ∈ S, FC n * (ramanujan r n * ramanujan r' n) -
            (if r = r' then (Nat.totient r : ℂ) * ∑ n ∈ S, FC n else 0))‖
      ≤ ∑ r ∈ Finset.Icc 1 R, ∑ r' ∈ Finset.Icc 1 R, Bd := by
        refine Finset.sum_le_sum fun r hr => (norm_sum_le _ _).trans ?_
        exact Finset.sum_le_sum fun r' hr' => hterm r hr r' hr'
    _ = (R : ℝ) ^ 2 * Bd := by
        simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, add_tsub_cancel_right]; ring

end Families.Phase3.C
