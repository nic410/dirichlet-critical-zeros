/-
# Theorem 1.4(a), package V: `lem:Mbeta` (Lemma 9.21) — proved, no `sorry`

For `C ≥ 1` and `1 ≤ β' ≤ β ≤ 2`: `p(β'; F_C) ≤ p(β; F_C) ≤ p(β'; F_C) + 2(β/β' − 1)`.

* The first inequality: the admissible class at `β'` is contained in the class at `β`
  (`admissibleB_mono`), and both infima exist (`pB_bddBelow`, `pB_nonempty`).
* The second: for `f` admissible at `β` and `a = β'/β ∈ (0,1]`, the dilation `dil a f = a⁻¹ f(·/a)` is
  admissible at `β'` (`dil_admissible`) and, since `F_C` is nondecreasing on `[0,∞)` (`FC_mono_arg`),
  `𝒬(dil a f) = a⁻¹∫f² + ∬ f f F_C(a|u−v|) ≤ 𝒬(f) + (a⁻¹ − 1)∫ f²` (`Qf_dil`). As `F_C ≥ 0`,
  `∫ f² ≤ 𝒬(f)`, and near-optimal `f` have `𝒬(f) ≤ inf + δ ≤ 2 + δ` (`sInf_le_two`). Let `δ → 0`.
-/
import FamiliesH.V.Basic

noncomputable section

open MeasureTheory

namespace Families.Hybrid.V

open Families

/-- `∫ f² ≤ 𝒬_{F_C}(f)` for `f ≥ 0` and `C ≥ 0`. -/
lemma integral_sq_le_Qf {C : ℝ} (hC : 0 ≤ C) {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∫ x, f x ^ 2 ≤ Qf (FC C) f := by
  unfold Qf
  have : 0 ≤ ∫ x, ∫ y, f x * f y * FC C |x - y| :=
    integral_nonneg fun x => integral_nonneg fun y =>
      mul_nonneg (mul_nonneg (hf x) (hf y)) (Families.FC_nonneg hC (abs_nonneg _))
  linarith

/-- The dilation estimate: `𝒬_{F_C}(dil a f) ≤ 𝒬_{F_C}(f) + (a⁻¹ − 1) ∫ f²` for `0 < a ≤ 1`. -/
lemma Qf_dil_le {C : ℝ} (hC : 1 ≤ C) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {β : ℝ} {f : ℝ → ℝ}
    (hf : AdmissibleWindowB β f) :
    Qf (FC C) (dil a f) ≤ Qf (FC C) f + (a⁻¹ - 1) * ∫ x, f x ^ 2 := by
  have hi := integrable_of_admissibleB hf
  have hFm := Families.Phase4.A.measurable_FC C
  have hFK := FC_abs_le hC
  have hF'm : Measurable (fun α => FC C (a * α)) := hFm.comp (measurable_const.mul measurable_id)
  have hF'K : ∀ α, 0 ≤ α → |(fun α => FC C (a * α)) α| ≤ C := fun α hα =>
    FC_abs_le hC (a * α) (mul_nonneg ha.le hα)
  have hmono : (∫ u, ∫ v, f u * f v * FC C (a * |u - v|)) ≤ ∫ u, ∫ v, f u * f v * FC C |u - v| := by
    refine integral_mono (Families.Phase4.A.outer_integrable hi hi hF'm hF'K)
      (Families.Phase4.A.outer_integrable hi hi hFm hFK) fun u => ?_
    refine integral_mono (Families.Phase4.A.inner_integrable hi hF'm hF'K u)
      (Families.Phase4.A.inner_integrable hi hFm hFK u) fun v => ?_
    have hle : a * |u - v| ≤ |u - v| := mul_le_of_le_one_left (abs_nonneg _) ha1
    exact mul_le_mul_of_nonneg_left (FC_mono_arg hC hle) (mul_nonneg (hf.nonneg u) (hf.nonneg v))
  rw [Qf_dil ha]
  unfold Qf
  have : a⁻¹ * ∫ x, f x ^ 2 = (∫ x, f x ^ 2) + (a⁻¹ - 1) * ∫ x, f x ^ 2 := by ring
  linarith

/-- **`lem:Mbeta`** (Lemma 9.21). -/
theorem lemMbeta_proof : lemMbeta_Statement := by
  intro C hC β' β hβ' hβ'β hβ2
  have hβ1 : 1 ≤ β := hβ'.trans hβ'β
  have hβ'pos : 0 < β' := by linarith
  have hβpos : 0 < β := by linarith
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have hbddβ := pB_bddBelow β hC0
  have hbddβ' := pB_bddBelow β' hC0
  have hneβ := pB_nonempty hβ1 C
  have hneβ' := pB_nonempty hβ' C
  constructor
  · -- nested classes
    unfold pB
    have : sInf (Qf (FC C) '' {f | AdmissibleWindowB β f}) ≤
        sInf (Qf (FC C) '' {f | AdmissibleWindowB β' f}) := by
      apply csInf_le_csInf hbddβ hneβ'
      rintro _ ⟨f, hf, rfl⟩
      exact ⟨f, admissibleB_mono hβ'β hf, rfl⟩
    linarith
  · -- dilation
    unfold pB
    obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = β' / β := ⟨_, rfl⟩
    have ha : 0 < a := by rw [ha_def]; exact div_pos hβ'pos hβpos
    have ha1 : a ≤ 1 := by rw [ha_def]; exact (div_le_one hβpos).2 hβ'β
    have hainv : a⁻¹ = β / β' := by rw [ha_def, inv_div]
    have haβ : a * β = β' := by rw [ha_def]; field_simp
    have hainv1 : 1 ≤ a⁻¹ := by rw [hainv]; exact (one_le_div hβ'pos).2 hβ'β
    set I := sInf (Qf (FC C) '' {f | AdmissibleWindowB β f}) with hI
    set I' := sInf (Qf (FC C) '' {f | AdmissibleWindowB β' f}) with hI'
    have hI2 : I ≤ 2 := sInf_le_two hβ1 hC
    have hkey : ∀ δ : ℝ, 0 < δ → I' ≤ I + 2 * (a⁻¹ - 1) + a⁻¹ * δ := by
      intro δ hδ
      obtain ⟨_, ⟨f, hf, rfl⟩, hfQ⟩ := exists_lt_of_csInf_lt hneβ (lt_add_of_pos_right I hδ)
      have hd : AdmissibleWindowB β' (dil a f) := by
        have := dil_admissible ha hf
        rwa [haβ] at this
      have h1 : I' ≤ Qf (FC C) (dil a f) := csInf_le hbddβ' ⟨dil a f, hd, rfl⟩
      have h2 := Qf_dil_le hC ha ha1 hf
      have h3 : ∫ x, f x ^ 2 ≤ Qf (FC C) f := integral_sq_le_Qf hC0 hf.nonneg
      have h4 : (a⁻¹ - 1) * ∫ x, f x ^ 2 ≤ (a⁻¹ - 1) * (2 + δ) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        linarith
      nlinarith
    have hfinal : I' ≤ I + 2 * (a⁻¹ - 1) := by
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have := hkey (a * ε) (mul_pos ha hε)
      rwa [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul] at this
    rw [hainv] at hfinal
    linarith

end Families.Hybrid.V
