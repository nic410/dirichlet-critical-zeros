/-
Step (7) of `lem:B2` — summing the block main terms.

`sum_M_le`: `∑_{j∈blocks} (∫ F_j log − G(R_j) ∫ F_j) ≤ (1 + c/ℓ) ∫ ℓ F_b(s/ℓ) h(s) ds`, `c = 2 log T + 2`
(`∑_j ψ_j ≤ 1`, `Υ ≤ 1`, substitution `y = e^s`).
-/
import Families.Phase3.C.B2Density

noncomputable section

open scoped ContDiff Nat ArithmeticFunction.Moebius
open Set ArithmeticFunction MeasureTheory

namespace Families.Phase3.C

open Families

variable (P : PrimeSetup)

lemma Fh_hasCompactSupport (Q : ℝ) (h : ℝ → ℝ) (j : ℕ) : HasCompactSupport (Fh P Q h j) :=
  HasCompactSupport.intro (K := Icc ((2 : ℝ) ^ j / 2) (2 * 2 ^ j)) isCompact_Icc fun y hy => by
    by_contra hne; exact hy (Fh_supp P Q h j y hne)

lemma Gh_hasCompactSupport (Q : ℝ) (h : ℝ → ℝ) (j : ℕ) : HasCompactSupport (Gh P Q h j) :=
  HasCompactSupport.intro (K := Icc ((2 : ℝ) ^ j / 2) (2 * 2 ^ j)) isCompact_Icc fun y hy => by
    by_contra hne; exact hy (Gh_supp P Q h j y hne)

lemma Fh_integrable (Q : ℝ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (j : ℕ) : Integrable (Fh P Q h j) :=
  (Fh_contDiff P Q hh j 0).continuous.integrable_of_hasCompactSupport (Fh_hasCompactSupport P Q h j)

lemma Gh_integrable (Q : ℝ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (j : ℕ) : Integrable (Gh P Q h j) :=
  (Gh_contDiff P Q hh j 0).continuous.integrable_of_hasCompactSupport (Gh_hasCompactSupport P Q h j)

lemma Fh_mul_Phi_integrable (Q : ℝ) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (j : ℕ) {ℓ c ε : ℝ}
    (hℓ : 0 < ℓ) (hc : 0 ≤ c) (hε : 0 ≤ ε) :
    Integrable (fun y => Fh P Q h j y * Phi ℓ c ε y) :=
  (Fh_integrable P Q hh j).mul_bdd (c := (1 + c / ℓ) * (ℓ * (1 + 2 * ε)))
    (measurable_Phi ℓ c ε).aestronglyMeasurable (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Phi_nonneg hℓ hc hε y)]; exact Phi_le hℓ hc y)

/-- `Ψ(y) = h(log y) Φ(y)/y` on `(0, ∞)`. -/
def Psi (h : ℝ → ℝ) (ℓ c ε : ℝ) (y : ℝ) : ℝ := if 0 < y then h (Real.log y) * Phi ℓ c ε y / y else 0

lemma Psi_comp_exp (h : ℝ → ℝ) (ℓ c ε s : ℝ) (hℓ : ℓ ≠ 0) :
    |Real.exp s| • Psi h ℓ c ε (Real.exp s) = (1 + c / ℓ) * (ℓ * Fb ε (s / ℓ) * h s) := by
  unfold Psi Phi
  rw [if_pos (Real.exp_pos s), Real.log_exp, abs_of_pos (Real.exp_pos s), smul_eq_mul]
  field_simp

lemma Psi_integral {h : ℝ → ℝ} (hint : Integrable h) {ℓ c ε : ℝ} (hℓ : 0 < ℓ) (_hc : 0 ≤ c)
    (hε : 0 ≤ ε) :
    Integrable (Psi h ℓ c ε) ∧
      ∫ y, Psi h ℓ c ε y = (1 + c / ℓ) * ∫ s, ℓ * Fb ε (s / ℓ) * h s := by
  have himg : Real.exp '' univ = Ioi 0 := by rw [image_univ, Real.range_exp]
  have hderiv : ∀ x ∈ (univ : Set ℝ), HasDerivWithinAt Real.exp (Real.exp x) univ x :=
    fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt
  have hinj : InjOn Real.exp univ := Real.exp_injective.injOn
  have hg : Integrable (fun s => (1 + c / ℓ) * (ℓ * Fb ε (s / ℓ) * h s)) := by
    have : Integrable (fun s => ℓ * Fb ε (s / ℓ) * h s) := by
      have hb : Integrable (fun s => h s * (ℓ * Fb ε (s / ℓ))) :=
        hint.mul_bdd (c := ℓ * (1 + 2 * ε))
          (by unfold Fb; fun_prop) (Filter.Eventually.of_forall fun s => by
            rw [Real.norm_eq_abs, abs_of_nonneg (by have := Fb_nonneg ε (s / ℓ) hε; positivity)]
            exact mul_le_mul_of_nonneg_left (Fb_le ε _) hℓ.le)
      exact hb.congr (Filter.Eventually.of_forall fun s => by ring)
    exact this.const_mul _
  have hInt : IntegrableOn (Psi h ℓ c ε) (Ioi 0) := by
    rw [← himg, integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hderiv hinj]
    rw [integrableOn_univ]
    exact hg.congr (Filter.Eventually.of_forall fun s => (Psi_comp_exp h ℓ c ε s hℓ.ne').symm)
  have hzero : ∀ y ∉ Ioi (0 : ℝ), Psi h ℓ c ε y = 0 := by
    intro y hy; unfold Psi; rw [if_neg (by simpa using hy)]
  have hInt' : Integrable (Psi h ℓ c ε) := by
    rw [← integrableOn_univ]
    have : univ = Ioi (0 : ℝ) ∪ (Ioi 0)ᶜ := (union_compl_self _).symm
    rw [this]
    refine hInt.union ?_
    exact (integrableOn_zero).congr_fun (fun y hy => (hzero y hy).symm) measurableSet_Ioi.compl
  refine ⟨hInt', ?_⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero, ← himg,
    integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hderiv hinj,
    setIntegral_univ]
  simp_rw [Psi_comp_exp h ℓ c ε _ hℓ.ne']
  rw [integral_const_mul]

/-- **Step (7) of `lem:B2`.** -/
theorem sum_M_le {Q T : ℝ} (hQ : 1 < Q) (hT : 1 ≤ T) (hY2 : 2 * P.Y Q ≤ Q ^ 2) {h : ℝ → ℝ}
    (hh : ContDiff ℝ ∞ h) (hh0 : ∀ y, 0 ≤ h y) (hint : Integrable h) :
    ∑ j ∈ P.blocks Q, ((∫ y, Gh P Q h j y) - Gsum (P.Rj Q T j) * ∫ y, Fh P Q h j y) ≤
      (1 + (2 * Real.log T + 2) / Real.log Q) *
        ∫ s, Real.log Q * Fb P.ε₃ (s / Real.log Q) * h s := by
  set ℓ := Real.log Q with hℓ
  set c := 2 * Real.log T + 2 with hc
  have hℓ0 : 0 < ℓ := Real.log_pos hQ
  have hc0 : 0 ≤ c := by have := Real.log_nonneg hT; positivity
  have hε0 : 0 ≤ P.ε₃ := P.ε₃_pos.le
  set Φ := Phi ℓ c P.ε₃ with hΦ
  -- each block
  have hblock : ∀ j ∈ P.blocks Q, (∫ y, Gh P Q h j y) - Gsum (P.Rj Q T j) * ∫ y, Fh P Q h j y ≤
      ∫ y, Fh P Q h j y * Φ y := by
    intro j _
    rw [← integral_const_mul, ← integral_sub (Gh_integrable P Q hh j)
      ((Fh_integrable P Q hh j).const_mul _)]
    refine integral_mono ((Gh_integrable P Q hh j).sub ((Fh_integrable P Q hh j).const_mul _))
      (Fh_mul_Phi_integrable P Q hh j hℓ0 hc0 hε0) fun y => ?_
    simp only
    rw [Gh_eq]
    rw [show Fh P Q h j y * Real.log y - Gsum (P.Rj Q T j) * Fh P Q h j y =
      Fh P Q h j y * (Real.log y - Gsum (P.Rj Q T j)) by ring]
    by_cases hF : Fh P Q h j y = 0
    · rw [hF]; simp
    · have hs := Fh_supp P Q h j y hF
      have hyY : y ≤ P.Y Q := by
        by_contra hc'; exact hF (Fh_eq_zero_of_gt P hQ h j (not_le.mp hc'))
      exact mul_le_mul_of_nonneg_left (density_le_Phi P hQ hT hY2 hs hyY)
        (Fh_nonneg P Q hh0 j y)
  refine (Finset.sum_le_sum hblock).trans ?_
  rw [← integral_finsetSum _ (fun j _ => Fh_mul_Phi_integrable P Q hh j hℓ0 hc0 hε0)]
  obtain ⟨hΨint, hΨ⟩ := Psi_integral hint hℓ0 hc0 hε0 (ε := P.ε₃)
  rw [← hΨ]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => ?_) hΨint
    (Filter.Eventually.of_forall fun y => ?_)
  · exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (Fh_nonneg P Q hh0 j y) (Phi_nonneg hℓ0 hc0 hε0 y)
  · simp only
    unfold Psi
    rcases le_or_gt y 0 with hy | hy
    · rw [if_neg (not_lt.mpr hy)]
      refine le_of_eq (Finset.sum_eq_zero fun j _ => ?_)
      have : Fh P Q h j y = 0 := by
        by_contra hne
        have := (Fh_supp P Q h j y hne).1
        have : (0 : ℝ) < 2 ^ j / 2 := by positivity
        linarith
      rw [this, zero_mul]
    · rw [if_pos hy]
      rcases lt_or_ge y 1 with hy1 | hy1
      · -- `Φ(y) = 0` for `y < 1`
        have hΦ0 : Phi ℓ c P.ε₃ y = 0 := by
          unfold Phi Fb
          have : Real.log y / ℓ < 0 := div_neg_of_neg_of_pos (Real.log_neg hy hy1) hℓ0
          rw [max_eq_right this.le,
            min_eq_left (by linarith [P.ε₃_pos] : (0 : ℝ) ≤ 1 + 2 * P.ε₃)]
          ring
        simp [hΦ, hΦ0]
      · have hψ := sum_psi_blocks_le P (Q := Q) hy1
        have hG : 0 ≤ Gcore P Q h y := by
          unfold Gcore; exact mul_nonneg (mul_nonneg (sq_nonneg _) (hh0 _)) (Real.exp_pos _).le
        have hGle : Gcore P Q h y ≤ h (Real.log y) / y := by
          unfold Gcore
          rw [Real.exp_neg, Real.exp_log hy, div_eq_mul_inv]
          have hU := P.Υ₀_range (Real.log y / P.L Q)
          have hU2 : UpsL P Q y ^ 2 ≤ 1 := by
            unfold UpsL; nlinarith [hU.1, hU.2]
          have h1 := hh0 (Real.log y)
          have h2 : 0 ≤ y⁻¹ := by positivity
          calc UpsL P Q y ^ 2 * h (Real.log y) * y⁻¹ ≤ 1 * h (Real.log y) * y⁻¹ := by gcongr
            _ = h (Real.log y) * y⁻¹ := by ring
        have hΦnn := Phi_nonneg hℓ0 hc0 hε0 y
        calc ∑ j ∈ P.blocks Q, Fh P Q h j y * Φ y
            = (∑ j ∈ P.blocks Q, P.ψj j y) * Gcore P Q h y * Φ y := by
              rw [Finset.sum_mul, Finset.sum_mul]; rfl
          _ ≤ 1 * (h (Real.log y) / y) * Φ y := by gcongr
          _ = h (Real.log y) * Φ y / y := by ring

end Families.Phase3.C
