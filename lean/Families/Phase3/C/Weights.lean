/-
The smooth block weights of `lemma-B-majorant.tex` (`eqB:Fjt`, `eqB:derivs`).

`F_{j,t}(y) = ψ_j(y) Υ₀(log y/L) y^{−1/2−it}` and its derivative bounds
`|F_{j,t}^{(k)}(y)| ≤ C N_j^{−1/2} (2(1+|t|)K/N_j)^k` (`k ≤ K`, all `y`, `L ≥ 1`), with `C` depending only on
`K` and the fixed data (the derivative bounds of `ψ_j` and `Υ₀`).
-/
import Families.Phase3.C.Freq
import Families.PrimeSide

noncomputable section

open scoped ContDiff Nat
open Set

namespace Families.Phase3.C

open Families

/-! ### Generic helpers -/

lemma iteratedDeriv_cexp_real (a : ℂ) (n : ℕ) :
    iteratedDeriv n (fun w : ℝ => Complex.exp (a * w)) =
      fun w : ℝ => a ^ n * Complex.exp (a * (w : ℂ)) := by
  induction n with
  | zero => funext w; simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext w
    have : HasDerivAt (fun w : ℝ => a ^ n * Complex.exp (a * w))
        (a ^ n * (Complex.exp (a * w) * (a * 1))) w :=
      ((((hasDerivAt_id w).ofReal_comp).const_mul a).cexp).const_mul (a ^ n)
    rw [this.deriv]; ring

/-- A finite family of bounds can be replaced by one bound. -/
lemma uniform_bound_of_forall {P : ℕ → ℝ → Prop} (hmono : ∀ i C C', C ≤ C' → P i C → P i C')
    (h : ∀ i, ∃ C, P i C) (K : ℕ) : ∃ C, 0 ≤ C ∧ ∀ i ≤ K, P i C := by
  choose C hC using h
  refine ⟨∑ i ∈ Finset.range (K + 1), |C i|, Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  intro i hi
  refine hmono i _ _ ?_ (hC i)
  calc C i ≤ |C i| := le_abs_self _
    _ ≤ _ := Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))

variable (P : PrimeSetup)

/-! ### Fixed-data bounds -/

/-- Derivatives of `Υ₀` are bounded on `[-1, ∞)`. -/
lemma Ups0_deriv_bound (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ K, ∀ w : ℝ, -1 ≤ w → ‖iteratedDeriv i P.Υ₀ w‖ ≤ C := by
  refine uniform_bound_of_forall (P := fun i C => ∀ w : ℝ, -1 ≤ w → ‖iteratedDeriv i P.Υ₀ w‖ ≤ C)
    (fun i C C' hCC' h w hw => (h w hw).trans hCC') (fun i => ?_) K
  have hcont : Continuous (iteratedDeriv i P.Υ₀) :=
    P.Υ₀_smooth.continuous_iteratedDeriv i (by exact_mod_cast le_top)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 2 + P.ε₁)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨C, fun w hw => ?_⟩
  by_cases hw2 : w ≤ 2 + P.ε₁
  · exact hC w ⟨hw, hw2⟩
  · have hz : P.Υ₀ =ᶠ[nhds w] fun _ => 0 := by
      filter_upwards [Ioi_mem_nhds (show 1 + P.ε₁ < w by linarith)] with z hz
      exact P.Υ₀_zero z hz
    rw [hz.iteratedDeriv_eq, iteratedDeriv_const]
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (-1) ⟨le_rfl, by linarith [P.ε₁_pos]⟩)
    split_ifs <;> simpa using hC0

/-- Derivatives of the `ψ_j`, uniformly in `j`, up to order `K`. -/
lemma ψj_deriv_uniform (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ K, ∀ j y, ‖iteratedDeriv i (P.ψj j) y‖ ≤ C * ((2 : ℝ) ^ j)⁻¹ ^ i := by
  refine uniform_bound_of_forall
    (P := fun i C => ∀ j y, ‖iteratedDeriv i (P.ψj j) y‖ ≤ C * ((2 : ℝ) ^ j)⁻¹ ^ i)
    (fun i C C' hCC' h j y => (h j y).trans
      (mul_le_mul_of_nonneg_right hCC' (by positivity))) (fun i => ?_) K
  obtain ⟨C, hC⟩ := P.ψj_deriv i
  exact ⟨C, fun j y => by rw [Real.norm_eq_abs]; exact hC j y⟩

/-! ### The weights -/

/-- `E_t(y) = exp(−(1/2 + it) log y)` (`= y^{−1/2−it}` for `y > 0`). -/
def Et (t y : ℝ) : ℂ := Complex.exp (-(1 / 2 + Complex.I * t) * (Real.log y : ℂ))

/-- `Υ(y) = Υ₀(log y / L)`. -/
def UpsL (Q y : ℝ) : ℝ := P.Υ₀ (Real.log y / P.L Q)

/-- `F_{j,t}(y) = ψ_j(y) Υ₀(log y/L) y^{−1/2−it}` (`eqB:Fjt`). -/
def Fjt (Q : ℝ) (j : ℕ) (t y : ℝ) : ℂ := (P.ψj j y : ℂ) * ((UpsL P Q y : ℂ) * Et t y)

lemma Et_contDiffOn (t : ℝ) : ContDiffOn ℝ ∞ (Et t) (Ioi 0) := by
  unfold Et
  refine Complex.contDiff_exp.comp_contDiffOn ?_
  refine contDiffOn_const.mul ?_
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn
    (Real.contDiffOn_log.mono fun x hx => ne_of_gt hx)

lemma UpsL_contDiffOn (Q : ℝ) : ContDiffOn ℝ ∞ (UpsL P Q) (Ioi 0) := by
  unfold UpsL
  exact P.Υ₀_smooth.comp_contDiffOn
    ((Real.contDiffOn_log.mono fun x hx => ne_of_gt hx).div_const _)

lemma Fjt_contDiff (Q : ℝ) (j : ℕ) (t : ℝ) (K : ℕ) : ContDiff ℝ K (Fjt P Q j t) := by
  have hpos : (0 : ℝ) < (2 : ℝ) ^ j / 2 := by positivity
  exact contDiff_bump_mul ((P.ψj_smooth j).of_le (by exact_mod_cast le_top)) hpos
    (fun y hy => P.ψj_supp j y hy)
    (((Complex.ofRealCLM.contDiff.comp_contDiffOn (UpsL_contDiffOn P Q)).mul
      (Et_contDiffOn t)).of_le (by exact_mod_cast le_top))

lemma Fjt_supp (Q : ℝ) (j : ℕ) (t y : ℝ) (h : Fjt P Q j t y ≠ 0) :
    (2 : ℝ) ^ j / 2 ≤ y ∧ y ≤ 2 * 2 ^ j := by
  apply P.ψj_supp j y
  intro h0; apply h; simp [Fjt, h0]

/-- `Υ(y) = 0` for `y > Y`. -/
lemma UpsL_eq_zero {Q y : ℝ} (hQ : 1 < Q) (hy : P.Y Q < y) : UpsL P Q y = 0 := by
  unfold UpsL
  apply P.Υ₀_zero
  have hL : 0 < P.L Q := mul_pos P.lam_pos (Real.log_pos hQ)
  have hY : Real.log (P.Y Q) = P.L Q * (1 + P.ε₁) := by
    unfold PrimeSetup.Y PrimeSetup.X
    rw [Real.log_rpow (Real.exp_pos _), Real.log_exp]; ring
  have hYpos : 0 < P.Y Q := Real.rpow_pos_of_pos (Real.exp_pos _) _
  have : Real.log (P.Y Q) < Real.log y := Real.log_lt_log hYpos hy
  rw [lt_div_iff₀ hL]; linarith

lemma Fjt_eq_zero_of_gt {Q y : ℝ} (hQ : 1 < Q) (j : ℕ) (t : ℝ) (hy : P.Y Q < y) :
    Fjt P Q j t y = 0 := by
  simp [Fjt, UpsL_eq_zero P hQ hy]

/-! ### Symbol bounds -/

lemma Et_symb (t : ℝ) (K : ℕ) {N : ℝ} (hN : 0 < N) :
    SymB (Et t) (Icc (N / 2) (2 * N)) K (K ! * Real.sqrt (2 / N)) (2 * (1 + |t|) * K / N) := by
  set c : ℝ := 1 + |t| with hc
  have hc1 : 1 ≤ c := by rw [hc]; linarith [abs_nonneg t]
  have hc0 : 0 < c := by linarith
  set a : ℂ := -(1 / 2 + Complex.I * t) / c with ha
  have hEt : Et t = fun y => (fun w : ℝ => Complex.exp (a * w)) (c * Real.log y) := by
    funext y
    simp only [Et, ha]
    congr 1
    have hc0' : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
    push_cast
    field_simp
  rw [hEt]
  have hanorm : ‖a‖ ≤ 1 := by
    rw [ha, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0, div_le_one hc0]
    calc ‖-(1 / 2 + Complex.I * t)‖ = ‖(1 / 2 : ℂ) + Complex.I * t‖ := norm_neg _
      _ ≤ ‖(1 / 2 : ℂ)‖ + ‖Complex.I * t‖ := norm_add_le _ _
      _ = 1 / 2 + |t| := by
          rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
          norm_num
      _ ≤ c := by rw [hc]; linarith
  have hare : a.re = -(1 / 2) / c := by
    rw [ha, Complex.div_ofReal_re]
    simp
  refine SymB.comp_log (g := fun w : ℝ => Complex.exp (a * w))
    (Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)) hc1 hN ?_
  intro y hy i _
  have hy0 : 0 < y := lt_of_lt_of_le (by linarith) hy.1
  rw [iteratedDeriv_cexp_real, norm_mul, norm_pow]
  have h1 : ‖a‖ ^ i ≤ 1 := pow_le_one₀ (norm_nonneg _) hanorm
  have h2 : ‖Complex.exp (a * ((c * Real.log y : ℝ) : ℂ))‖ ≤ Real.sqrt (2 / N) := by
    rw [Complex.norm_exp]
    have hre : (a * ((c * Real.log y : ℝ) : ℂ)).re = -(Real.log y) / 2 := by
      rw [Complex.re_mul_ofReal, hare]; field_simp
    rw [hre]
    have hexp : Real.exp (-(Real.log y) / 2) = (Real.sqrt y)⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hy0.le, Real.rpow_def_of_pos hy0]; ring_nf
    rw [hexp]
    have hsq : Real.sqrt (N / 2) ≤ Real.sqrt y := Real.sqrt_le_sqrt hy.1
    have hsqpos : 0 < Real.sqrt (N / 2) := Real.sqrt_pos.mpr (by positivity)
    calc (Real.sqrt y)⁻¹ ≤ (Real.sqrt (N / 2))⁻¹ := inv_anti₀ hsqpos hsq
      _ = Real.sqrt (2 / N) := by
          rw [← Real.sqrt_inv, inv_div]
  calc ‖a‖ ^ i * ‖Complex.exp (a * ((c * Real.log y : ℝ) : ℂ))‖ ≤ 1 * Real.sqrt (2 / N) :=
        mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = Real.sqrt (2 / N) := one_mul _

lemma UpsL_symb {Q : ℝ} (hL : 1 ≤ P.L Q) (K : ℕ) {C : ℝ}
    (hC : ∀ i ≤ K, ∀ w : ℝ, -1 ≤ w → ‖iteratedDeriv i P.Υ₀ w‖ ≤ C) {N : ℝ} (hN : 1 ≤ N) :
    SymB (UpsL P Q) (Icc (N / 2) (2 * N)) K (K ! * C) (2 * 1 * K / N) := by
  have hL0 : 0 < P.L Q := by linarith
  have hUps : UpsL P Q = fun y => (fun z => P.Υ₀ ((P.L Q)⁻¹ * z)) (1 * Real.log y) := by
    funext y; simp [UpsL, div_eq_inv_mul]
  rw [hUps]
  refine SymB.comp_log (g := fun z => P.Υ₀ ((P.L Q)⁻¹ * z))
    ((P.Υ₀_smooth.of_le (by exact_mod_cast le_top)).comp (contDiff_const.mul contDiff_id))
    le_rfl (by linarith) ?_
  intro y hy i hi
  have hy0 : 0 < y := lt_of_lt_of_le (by linarith) hy.1
  rw [iteratedDeriv_comp_const_mul ((P.Υ₀_smooth).of_le (by exact_mod_cast le_top)) _]
  simp only [one_mul]
  rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_inv, abs_of_pos hL0]
  have h1 : ((P.L Q)⁻¹) ^ i ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hL)
  have hw : -1 ≤ (P.L Q)⁻¹ * Real.log y := by
    have hlog : -1 ≤ Real.log y := by
      have : Real.log (1 / 2) ≤ Real.log y :=
        Real.log_le_log (by norm_num) (le_trans (by linarith) hy.1)
      have h2 : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
      have h3 : Real.log 2 < 1 := by
        have := Real.log_two_lt_d9; linarith
      linarith
    rcases le_or_gt 0 (Real.log y) with h | h
    · have : 0 ≤ (P.L Q)⁻¹ * Real.log y := mul_nonneg (by positivity) h
      linarith
    · have : (P.L Q)⁻¹ * Real.log y ≥ Real.log y := by
        have hinv : (P.L Q)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL
        nlinarith
      linarith
  have h2 := hC i hi _ hw
  have hC0 : 0 ≤ C := (norm_nonneg _).trans h2
  calc ((P.L Q)⁻¹) ^ i * ‖iteratedDeriv i P.Υ₀ ((P.L Q)⁻¹ * Real.log y)‖ ≤ 1 * C :=
        mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = C := one_mul _

lemma ψj_symb (K : ℕ) {C : ℝ} (hC : ∀ i ≤ K, ∀ j y, ‖iteratedDeriv i (P.ψj j) y‖ ≤ C * ((2 : ℝ) ^ j)⁻¹ ^ i)
    (j : ℕ) (s : Set ℝ) : SymB (P.ψj j) s K C ((2 : ℝ) ^ j)⁻¹ := by
  intro k hk y _
  exact hC k hk j y

/-- **`eqB:derivs`** for `F_{j,t}`: an explicit symbol bound, uniform in `j`, `t`, `Q` (with `L ≥ 1`). -/
theorem Fjt_deriv_bound (K : ℕ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Q : ℝ, 1 ≤ P.L Q → ∀ (j : ℕ) (t : ℝ), ∀ k ≤ K, ∀ y : ℝ,
      ‖iteratedDeriv k (Fjt P Q j t) y‖ ≤
        C * Real.sqrt (2 / 2 ^ j) * (2 * (1 + |t|) * K / 2 ^ j) ^ k := by
  obtain ⟨Cu, hCu0, hCu⟩ := Ups0_deriv_bound P K
  obtain ⟨Cp, hCp0, hCp⟩ := ψj_deriv_uniform P K
  refine ⟨2 ^ K * Cp * (2 ^ K * (K ! * Cu) * K !), by positivity, ?_⟩
  intro Q hL j t k hk y
  set N : ℝ := 2 ^ j with hN
  have hN1 : 1 ≤ N := one_le_pow₀ (by norm_num)
  have hN0 : 0 < N := by linarith
  set σ : ℝ := 2 * (1 + |t|) * K / N with hσ
  have hσ0 : 0 ≤ σ := by positivity
  have hs : Icc (N / 2) (2 * N) ⊆ Ioi (0 : ℝ) := fun y hy => lt_of_lt_of_le (by linarith) hy.1
  -- the two `(0,∞)`-factors
  have hU := UpsL_symb P hL K hCu hN1
  have hU' : SymB (fun y => (UpsL P Q y : ℂ)) (Icc (N / 2) (2 * N)) K (K ! * Cu) σ := by
    refine (SymB.ofReal isOpen_Ioi hs ((UpsL_contDiffOn P Q).of_le
      (by exact_mod_cast le_top)) hU).mono le_rfl (by positivity) ?_
    rw [hσ]
    apply div_le_div_of_nonneg_right _ hN0.le
    have : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    nlinarith
  have hE := Et_symb t K hN0
  have hG := SymB.mul (U := Ioi 0) isOpen_Ioi hs
    ((Complex.ofRealCLM.contDiff.comp_contDiffOn (UpsL_contDiffOn P Q)).of_le
      (by exact_mod_cast le_top))
    ((Et_contDiffOn t).of_le (by exact_mod_cast le_top)) hσ0 hU' hE
  -- the bump
  have hψ : SymB (fun y => (P.ψj j y : ℂ)) (Icc (N / 2) (2 * N)) K Cp σ := by
    refine (SymB.ofReal isOpen_Ioi hs ((P.ψj_smooth j).contDiffOn.of_le
      (by exact_mod_cast le_top)) (ψj_symb P K hCp j _)).mono le_rfl (by positivity) ?_
    rw [hσ, ← hN, inv_eq_one_div]
    apply div_le_div_of_nonneg_right _ hN0.le
    have : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
    nlinarith
  have hF := SymB.mul (U := Ioi 0) isOpen_Ioi hs
    ((Complex.ofRealCLM.contDiff.comp (P.ψj_smooth j)).contDiffOn.of_le
      (by exact_mod_cast le_top))
    (((Complex.ofRealCLM.contDiff.comp_contDiffOn (UpsL_contDiffOn P Q)).mul
      (Et_contDiffOn t)).of_le (by exact_mod_cast le_top)) hσ0 hψ hG
  have hglob := global_of_bump (ψ := P.ψj j) (a := N / 2) (b := 2 * N)
    (fun y hy => by have := P.ψj_supp j y hy; rw [← hN] at this; exact this)
    (G := fun y => (UpsL P Q y : ℂ) * Et t y) (by positivity) hσ0 hF k hk y
  have hFeq : Fjt P Q j t = fun z => (P.ψj j z : ℂ) * ((UpsL P Q z : ℂ) * Et t z) := rfl
  rw [hFeq]
  refine hglob.trans (le_of_eq ?_)
  ring

end Families.Phase3.C
