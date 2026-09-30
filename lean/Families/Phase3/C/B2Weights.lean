/-
The real block weights of `lem:B2`, step (1):
`F_j(y) = ψ_j(y) Υ(y)² h(log y)/y` and `F_j(y) log y`, with symbol bounds
`|F_j^{(k)}| ≤ C h_max N^{-1} (2K/N)^k` (`Fh_deriv_bound`) and
`|(F_j log)'| ≤ C h_max (1 + log 2N) N^{-1} (2/N)` (`Gh_deriv_bound`), uniformly in `j`, `Q` (with `L ≥ 1`),
and in `h` subject to `|h^{(i)}| ≤ C_i h_max`.
-/
import Families.Phase3.C.B2Sums
import Families.Phase3.C.Weights

noncomputable section

open scoped ContDiff Nat
open Set

namespace Families.Phase3.C

open Families

/-! ### Real-valued globalisation through a bump -/

lemma eventually_zero_of_bump_real {ψ : ℝ → ℝ} {a b : ℝ} (hsupp : ∀ y, ψ y ≠ 0 → a ≤ y ∧ y ≤ b)
    (G : ℝ → ℝ) {y : ℝ} (hy : y < a ∨ b < y) :
    (fun z => ψ z * G z) =ᶠ[nhds y] fun _ => 0 := by
  rcases hy with hy | hy
  · filter_upwards [Iio_mem_nhds hy] with z hz
    have : ψ z = 0 := by
      by_contra h; exact absurd (hsupp z h).1 (not_le.mpr hz)
    simp [this]
  · filter_upwards [Ioi_mem_nhds hy] with z hz
    have : ψ z = 0 := by
      by_contra h; exact absurd (hsupp z h).2 (not_le.mpr hz)
    simp [this]

theorem contDiff_bump_mul_real {ψ : ℝ → ℝ} {K : ℕ} (hψ : ContDiff ℝ K ψ) {a b : ℝ} (ha : 0 < a)
    (hsupp : ∀ y, ψ y ≠ 0 → a ≤ y ∧ y ≤ b) {G : ℝ → ℝ} (hG : ContDiffOn ℝ K G (Ioi 0)) :
    ContDiff ℝ K (fun y => ψ y * G y) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  rcases lt_or_ge 0 y with hy | hy
  · exact (hψ.contDiffOn.mul hG).contDiffAt (Ioi_mem_nhds hy)
  · exact contDiffAt_const.congr_of_eventuallyEq
      (eventually_zero_of_bump_real hsupp G (Or.inl (lt_of_le_of_lt hy ha)))

theorem global_of_bump_real {ψ : ℝ → ℝ} {a b : ℝ} (hsupp : ∀ y, ψ y ≠ 0 → a ≤ y ∧ y ≤ b)
    {G : ℝ → ℝ} {K : ℕ} {A σ : ℝ} (hA : 0 ≤ A) (hσ : 0 ≤ σ)
    (h : SymB (fun z => ψ z * G z) (Icc a b) K A σ) :
    ∀ k ≤ K, ∀ y, ‖iteratedDeriv k (fun z => ψ z * G z) y‖ ≤ A * σ ^ k := by
  intro k hk y
  by_cases hy : y ∈ Icc a b
  · exact h k hk y hy
  · have hy' : y < a ∨ b < y := by
      simp only [mem_Icc, not_and_or, not_le] at hy; exact hy
    rw [(eventually_zero_of_bump_real hsupp G hy').iteratedDeriv_eq, iteratedDeriv_const]
    split_ifs
    · simp only [norm_zero]; positivity
    · simp only [norm_zero]; positivity

/-! ### The weights -/

variable (P : PrimeSetup)

/-- The `(0,∞)`-part of `F_j`: `Υ(y)² h(log y) e^{−log y}`. -/
def Gcore (Q : ℝ) (h : ℝ → ℝ) (y : ℝ) : ℝ :=
  UpsL P Q y ^ 2 * h (Real.log y) * Real.exp (-Real.log y)

/-- `F_j(y) = ψ_j(y) Υ(y)² h(log y)/y` (`lemma-B-majorant.tex`, step (1) of `lem:B2`). -/
def Fh (Q : ℝ) (h : ℝ → ℝ) (j : ℕ) (y : ℝ) : ℝ := P.ψj j y * Gcore P Q h y

/-- `F_j(y) log y`. -/
def Gh (Q : ℝ) (h : ℝ → ℝ) (j : ℕ) (y : ℝ) : ℝ := P.ψj j y * (Gcore P Q h y * Real.log y)

lemma Gh_eq (Q : ℝ) (h : ℝ → ℝ) (j : ℕ) (y : ℝ) : Gh P Q h j y = Fh P Q h j y * Real.log y := by
  unfold Gh Fh; ring

lemma Gcore_contDiffOn (Q : ℝ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiffOn ℝ ∞ (Gcore P Q h) (Ioi 0) := by
  unfold Gcore
  have hlog : ContDiffOn ℝ ∞ Real.log (Ioi 0) :=
    Real.contDiffOn_log.mono fun x hx => ne_of_gt hx
  exact (((UpsL_contDiffOn P Q).pow 2).mul (hh.comp_contDiffOn hlog)).mul
    (Real.contDiff_exp.comp_contDiffOn hlog.neg)

lemma Gcore_log_contDiffOn (Q : ℝ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiffOn ℝ ∞ (fun y => Gcore P Q h y * Real.log y) (Ioi 0) :=
  (Gcore_contDiffOn P Q hh).mul (Real.contDiffOn_log.mono fun _ hx => ne_of_gt hx)

lemma Fh_contDiff (Q : ℝ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (j : ℕ) (K : ℕ) :
    ContDiff ℝ K (Fh P Q h j) :=
  contDiff_bump_mul_real ((P.ψj_smooth j).of_le (by exact_mod_cast le_top))
    (by positivity : (0 : ℝ) < (2 : ℝ) ^ j / 2) (fun y hy => P.ψj_supp j y hy)
    ((Gcore_contDiffOn P Q hh).of_le (by exact_mod_cast le_top))

lemma Gh_contDiff (Q : ℝ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (j : ℕ) (K : ℕ) :
    ContDiff ℝ K (Gh P Q h j) :=
  contDiff_bump_mul_real ((P.ψj_smooth j).of_le (by exact_mod_cast le_top))
    (by positivity : (0 : ℝ) < (2 : ℝ) ^ j / 2) (fun y hy => P.ψj_supp j y hy)
    ((Gcore_log_contDiffOn P Q hh).of_le (by exact_mod_cast le_top))

lemma Fh_supp (Q : ℝ) (h : ℝ → ℝ) (j : ℕ) (y : ℝ) (hy : Fh P Q h j y ≠ 0) :
    (2 : ℝ) ^ j / 2 ≤ y ∧ y ≤ 2 * 2 ^ j :=
  P.ψj_supp j y (fun h0 => hy (by simp [Fh, h0]))

lemma Gh_supp (Q : ℝ) (h : ℝ → ℝ) (j : ℕ) (y : ℝ) (hy : Gh P Q h j y ≠ 0) :
    (2 : ℝ) ^ j / 2 ≤ y ∧ y ≤ 2 * 2 ^ j :=
  P.ψj_supp j y (fun h0 => hy (by simp [Gh, h0]))

lemma Fh_eq_zero_of_gt {Q y : ℝ} (hQ : 1 < Q) (h : ℝ → ℝ) (j : ℕ) (hy : P.Y Q < y) :
    Fh P Q h j y = 0 := by
  simp [Fh, Gcore, UpsL_eq_zero P hQ hy]

lemma Fh_nonneg (Q : ℝ) {h : ℝ → ℝ} (hh : ∀ y, 0 ≤ h y) (j : ℕ) (y : ℝ) : 0 ≤ Fh P Q h j y := by
  unfold Fh Gcore
  exact mul_nonneg (P.ψj_nonneg j y)
    (mul_nonneg (mul_nonneg (sq_nonneg _) (hh _)) (Real.exp_pos _).le)

/-- `F_j(n) = ψ_j(n) Υ(n)² h(log n)/n`. -/
lemma Fh_nat (Q : ℝ) (h : ℝ → ℝ) (j : ℕ) (n : ℕ) (hn : 1 ≤ n) :
    Fh P Q h j n = P.ψj j n * P.Ups Q n ^ 2 * h (Real.log n) / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold Fh Gcore UpsL
  rw [Real.exp_neg, Real.exp_log hn0]
  simp only [PrimeSetup.Ups]
  field_simp

/-! ### Symbol bounds -/

lemma exp_neg_log_symb (K : ℕ) {N : ℝ} (hN : 0 < N) :
    SymB (fun y => Real.exp (-Real.log y)) (Icc (N / 2) (2 * N)) K (K ! * (2 / N))
      (2 * 1 * K / N) := by
  have heq : (fun y => Real.exp (-Real.log y)) =
      fun y => (fun z : ℝ => Real.exp ((-1) * z)) (1 * Real.log y) := by
    funext y; congr 1; ring
  rw [heq]
  refine SymB.comp_log (g := fun z : ℝ => Real.exp ((-1) * z))
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)) le_rfl hN ?_
  intro y hy i _
  have hy0 : 0 < y := lt_of_lt_of_le (by linarith) hy.1
  rw [iteratedDeriv_exp_const_mul, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    one_mul, abs_of_pos (Real.exp_pos _)]
  rw [show (-1 : ℝ) * (1 * Real.log y) = -Real.log y by ring, Real.exp_neg, Real.exp_log hy0]
  rw [inv_le_comm₀ hy0 (by positivity), inv_div]
  exact hy.1

lemma h_log_symb (K : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) {B : ℝ}
    (hB : ∀ i ≤ K, ∀ y, |iteratedDeriv i h y| ≤ B) {N : ℝ} (hN : 0 < N) :
    SymB (fun y => h (Real.log y)) (Icc (N / 2) (2 * N)) K (K ! * B) (2 * 1 * K / N) := by
  have heq : (fun y => h (Real.log y)) = fun y => h (1 * Real.log y) := by
    funext y; rw [one_mul]
  rw [heq]
  exact SymB.comp_log (hh.of_le (by exact_mod_cast le_top)) le_rfl hN
    (fun y _ i hi => by rw [Real.norm_eq_abs]; exact hB i hi _)

lemma iteratedDeriv_id_succ_succ (i : ℕ) (z : ℝ) :
    iteratedDeriv (i + 2) (fun z : ℝ => z) z = 0 := by
  rw [iteratedDeriv_succ']
  have : deriv (fun z : ℝ => z) = fun _ => 1 := deriv_id''
  rw [this, iteratedDeriv_const]
  simp

lemma log_symb (K : ℕ) {N : ℝ} (hN : 2 ≤ N) :
    SymB Real.log (Icc (N / 2) (2 * N)) K (K ! * (1 + Real.log (2 * N))) (2 * 1 * K / N) := by
  have key : SymB (fun y => (fun z : ℝ => z) (1 * Real.log y)) (Icc (N / 2) (2 * N)) K
      (K ! * (1 + Real.log (2 * N))) (2 * 1 * K / N) := by
    refine SymB.comp_log (g := fun z : ℝ => z) contDiff_id le_rfl (by linarith) ?_
    intro y hy i _
    have hy1 : 1 ≤ y := le_trans (by linarith) hy.1
    have hlog0 : 0 ≤ Real.log y := Real.log_nonneg hy1
    have hlog : Real.log y ≤ Real.log (2 * N) := Real.log_le_log (by linarith) hy.2
    have hlog2 : 0 ≤ Real.log (2 * N) := hlog0.trans hlog
    rcases i with _ | _ | i
    · rw [iteratedDeriv_zero, one_mul, Real.norm_eq_abs, abs_of_nonneg hlog0]; linarith
    · rw [zero_add, iteratedDeriv_one, deriv_id'']; simp only [norm_one]; linarith
    · rw [iteratedDeriv_id_succ_succ, norm_zero]; linarith
  have heq' : (fun y => (fun z : ℝ => z) (1 * Real.log y)) = Real.log := by
    funext y; simp
  rw [heq'] at key
  exact key

/-- **Symbol bound for `F_j`**, uniform in `j`, `Q` (`L ≥ 1`) and in `h` with `|h^{(i)}| ≤ C_i h_max`. -/
theorem Fh_deriv_bound (K : ℕ) (hK : 1 ≤ K) (Cs : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Q : ℝ, 1 ≤ P.L Q → ∀ (h : ℝ → ℝ) (hmax : ℝ), ContDiff ℝ ∞ h →
      (∀ y, 0 ≤ h y) → (∀ y, h y ≤ hmax) → (∀ i y, |iteratedDeriv i h y| ≤ Cs i * hmax) →
      ∀ (j : ℕ), ∀ k ≤ K, ∀ y : ℝ,
        ‖iteratedDeriv k (Fh P Q h j) y‖ ≤ C * hmax / 2 ^ j * (2 * K / 2 ^ j) ^ k := by
  obtain ⟨Cu, hCu0, hCu⟩ := Ups0_deriv_bound P K
  obtain ⟨Cp, hCp0, hCp⟩ := ψj_deriv_uniform P K
  set Ch : ℝ := ∑ i ∈ Finset.range (K + 1), |Cs i| with hCh
  have hCh0 : 0 ≤ Ch := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨2 ^ K * Cp * (2 ^ K * (2 ^ K * (2 ^ K * (K ! * Cu) * (K ! * Cu)) * (K ! * Ch)) * (K ! * 2)),
    by positivity, ?_⟩
  intro Q hL h hmax hh hh0 hhmax hhd j k hk y
  have hmax0 : 0 ≤ hmax := (hh0 0).trans (hhmax 0)
  set N : ℝ := 2 ^ j with hN
  have hN1 : 1 ≤ N := one_le_pow₀ (by norm_num)
  have hN0 : 0 < N := by linarith
  set σ : ℝ := 2 * 1 * K / N with hσ
  have hσ0 : 0 ≤ σ := by positivity
  have hs : Icc (N / 2) (2 * N) ⊆ Ioi (0 : ℝ) := fun y hy => lt_of_lt_of_le (by linarith) hy.1
  have hlog : ContDiffOn ℝ ∞ Real.log (Ioi 0) := Real.contDiffOn_log.mono fun x hx => ne_of_gt hx
  have hU := UpsL_symb P hL K hCu hN1
  have hUc : ContDiffOn ℝ K (UpsL P Q) (Ioi 0) := (UpsL_contDiffOn P Q).of_le (by exact_mod_cast le_top)
  have hU2 := SymB.mul isOpen_Ioi hs hUc hUc hσ0 hU hU
  have hhb : ∀ i ≤ K, ∀ y, |iteratedDeriv i h y| ≤ Ch * hmax := by
    intro i hi y
    refine (hhd i y).trans (mul_le_mul_of_nonneg_right ?_ hmax0)
    calc Cs i ≤ |Cs i| := le_abs_self _
      _ ≤ Ch := Finset.single_le_sum (f := fun i => |Cs i|) (fun _ _ => abs_nonneg _)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  have hH := h_log_symb K hh hhb hN0
  have hHc : ContDiffOn ℝ K (fun y => h (Real.log y)) (Ioi 0) :=
    (hh.comp_contDiffOn hlog).of_le (by exact_mod_cast le_top)
  have hUH := SymB.mul isOpen_Ioi hs ((hUc.pow 2).congr fun y _ => by ring) hHc hσ0 hU2 hH
  have hE := exp_neg_log_symb K hN0
  have hEc : ContDiffOn ℝ K (fun y => Real.exp (-Real.log y)) (Ioi 0) :=
    (Real.contDiff_exp.comp_contDiffOn hlog.neg).of_le (by exact_mod_cast le_top)
  have hG := SymB.mul isOpen_Ioi hs
    ((((hUc.pow 2).congr fun y _ => by ring).mul hHc)) hEc hσ0 hUH hE
  have hψ : SymB (P.ψj j) (Icc (N / 2) (2 * N)) K Cp σ := by
    refine (ψj_symb P K hCp j _).mono le_rfl (by positivity) ?_
    rw [hσ, ← hN, inv_eq_one_div]
    apply div_le_div_of_nonneg_right _ hN0.le
    have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  have hGc : ContDiffOn ℝ K (Gcore P Q h) (Ioi 0) :=
    (Gcore_contDiffOn P Q hh).of_le (by exact_mod_cast le_top)
  have hF := SymB.mul isOpen_Ioi hs ((P.ψj_smooth j).contDiffOn.of_le (by exact_mod_cast le_top))
    (hGc.congr fun y _ => by unfold Gcore; ring) hσ0 hψ hG
  have hglob := global_of_bump_real (ψ := P.ψj j) (a := N / 2) (b := 2 * N)
    (fun y hy => by have := P.ψj_supp j y hy; rw [← hN] at this; exact this)
    (G := fun y => UpsL P Q y * UpsL P Q y * h (Real.log y) * Real.exp (-Real.log y))
    (by positivity) hσ0 hF k hk y
  have hFeq : Fh P Q h j = fun z => P.ψj j z *
      (UpsL P Q z * UpsL P Q z * h (Real.log z) * Real.exp (-Real.log z)) := by
    funext z; unfold Fh Gcore; ring
  rw [hFeq]
  refine hglob.trans (le_of_eq ?_)
  rw [hσ]; ring

/-- **Symbol bound for `F_j log`** at first order. -/
theorem Gh_deriv_bound (Cs : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Q : ℝ, 1 ≤ P.L Q → ∀ (h : ℝ → ℝ) (hmax : ℝ), ContDiff ℝ ∞ h →
      (∀ y, 0 ≤ h y) → (∀ y, h y ≤ hmax) → (∀ i y, |iteratedDeriv i h y| ≤ Cs i * hmax) →
      ∀ (j : ℕ), 1 ≤ j → ∀ y : ℝ,
        |deriv (Gh P Q h j) y| ≤ C * hmax * (1 + Real.log (2 * 2 ^ j)) / 2 ^ j * (2 / 2 ^ j) := by
  set K : ℕ := 1
  obtain ⟨Cu, hCu0, hCu⟩ := Ups0_deriv_bound P K
  obtain ⟨Cp, hCp0, hCp⟩ := ψj_deriv_uniform P K
  set Ch : ℝ := ∑ i ∈ Finset.range (K + 1), |Cs i| with hCh
  have hCh0 : 0 ≤ Ch := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨2 * Cp * (2 * (2 * (2 * (2 * Cu * Cu) * Ch) * 2) * 1), by positivity, ?_⟩
  intro Q hL h hmax hh hh0 hhmax hhd j hj y
  have hmax0 : 0 ≤ hmax := (hh0 0).trans (hhmax 0)
  set N : ℝ := 2 ^ j with hN
  have hN2 : 2 ≤ N := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hj
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  set σ : ℝ := 2 * 1 * K / N with hσ
  have hσ0 : 0 ≤ σ := by positivity
  have hs : Icc (N / 2) (2 * N) ⊆ Ioi (0 : ℝ) := fun y hy => lt_of_lt_of_le (by linarith) hy.1
  have hlog : ContDiffOn ℝ ∞ Real.log (Ioi 0) := Real.contDiffOn_log.mono fun x hx => ne_of_gt hx
  have hU := UpsL_symb P hL K hCu hN1
  have hUc : ContDiffOn ℝ K (UpsL P Q) (Ioi 0) := (UpsL_contDiffOn P Q).of_le (by exact_mod_cast le_top)
  have hU2 := SymB.mul isOpen_Ioi hs hUc hUc hσ0 hU hU
  have hhb : ∀ i ≤ K, ∀ y, |iteratedDeriv i h y| ≤ Ch * hmax := by
    intro i hi y
    refine (hhd i y).trans (mul_le_mul_of_nonneg_right ?_ hmax0)
    calc Cs i ≤ |Cs i| := le_abs_self _
      _ ≤ Ch := Finset.single_le_sum (f := fun i => |Cs i|) (fun _ _ => abs_nonneg _)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  have hH := h_log_symb K hh hhb hN0
  have hHc : ContDiffOn ℝ K (fun y => h (Real.log y)) (Ioi 0) :=
    (hh.comp_contDiffOn hlog).of_le (by exact_mod_cast le_top)
  have hUH := SymB.mul isOpen_Ioi hs ((hUc.pow 2).congr fun y _ => by ring) hHc hσ0 hU2 hH
  have hE := exp_neg_log_symb K hN0
  have hEc : ContDiffOn ℝ K (fun y => Real.exp (-Real.log y)) (Ioi 0) :=
    (Real.contDiff_exp.comp_contDiffOn hlog.neg).of_le (by exact_mod_cast le_top)
  have hG := SymB.mul isOpen_Ioi hs
    ((((hUc.pow 2).congr fun y _ => by ring).mul hHc)) hEc hσ0 hUH hE
  have hL' := log_symb K hN2
  have hlogc : ContDiffOn ℝ K Real.log (Ioi 0) := hlog.of_le (by exact_mod_cast le_top)
  have hGL := SymB.mul isOpen_Ioi hs
    (((((hUc.pow 2).congr fun y _ => by ring).mul hHc)).mul hEc) hlogc hσ0 hG hL'
  have hψ : SymB (P.ψj j) (Icc (N / 2) (2 * N)) K Cp σ := by
    refine (ψj_symb P K hCp j _).mono le_rfl (by positivity) ?_
    rw [hσ, ← hN, inv_eq_one_div]
    apply div_le_div_of_nonneg_right _ hN0.le
    norm_num
  have hF := SymB.mul isOpen_Ioi hs ((P.ψj_smooth j).contDiffOn.of_le (by exact_mod_cast le_top))
    ((Gcore_log_contDiffOn P Q hh).of_le (by exact_mod_cast le_top) |>.congr
      fun y _ => by unfold Gcore; ring) hσ0 hψ hGL
  have hglob := global_of_bump_real (ψ := P.ψj j) (a := N / 2) (b := 2 * N)
    (fun y hy => by have := P.ψj_supp j y hy; rw [← hN] at this; exact this)
    (G := fun y => UpsL P Q y * UpsL P Q y * h (Real.log y) * Real.exp (-Real.log y) * Real.log y)
    (hF.amp_nonneg (y := N) ⟨by linarith, by linarith⟩) hσ0 hF 1 le_rfl y
  have hGeq : Gh P Q h j = fun z => P.ψj j z *
      (UpsL P Q z * UpsL P Q z * h (Real.log z) * Real.exp (-Real.log z) * Real.log z) := by
    funext z; unfold Gh Gcore; ring
  rw [hGeq, ← iteratedDeriv_one, ← Real.norm_eq_abs]
  refine hglob.trans (le_of_eq ?_)
  rw [hσ]
  simp only [K, Nat.factorial_one, Nat.cast_one, pow_one]
  field_simp

end Families.Phase3.C
