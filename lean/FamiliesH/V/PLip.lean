/-
# Theorem 1.4(a), package V: `lem:pLipH` (Lemma 9.22) — proved, no `sorry`

For `1 ≤ C ≤ C'`: `p(β; F_{C'}) ≤ p(β; F_C)` and `p(β; F_{C'}) ≥ p(β; F_C) − (C' − C)`.
A port of `Families.pC_antitone_lip` (whose helper lemmas are `private`) to the admissible class at
support `β`; the support plays no role in the argument.
-/
import FamiliesH.V.Basic

noncomputable section

open MeasureTheory

namespace Families.Hybrid.V

open Families

private lemma FC_mono_C {C C' : ℝ} (hCC' : C ≤ C') (α : ℝ) : FC C α ≤ FC C' α := by
  unfold FC; split_ifs <;> linarith

private lemma FC_lip_C {C C' : ℝ} (hCC' : C ≤ C') (α : ℝ) : FC C' α ≤ FC C α + (C' - C) := by
  unfold FC; split_ifs <;> linarith

/-- `𝒬_{F_C}(f) ≤ 𝒬_{F_{C'}}(f) ≤ 𝒬_{F_C}(f) + (C' − C)` for `f` admissible at any support. -/
lemma Qf_boundsB {β : ℝ} {f : ℝ → ℝ} (hf : AdmissibleWindowB β f) {C C' : ℝ} (hC : 1 ≤ C)
    (hCC' : C ≤ C') :
    Qf (FC C) f ≤ Qf (FC C') f ∧ Qf (FC C') f ≤ Qf (FC C) f + (C' - C) := by
  have hC' : 1 ≤ C' := hC.trans hCC'
  have hi := integrable_of_admissibleB hf
  have hin : ∀ C0 : ℝ, 1 ≤ C0 → ∀ x, Integrable (fun y => f x * f y * FC C0 |x - y|) :=
    fun C0 h0 x =>
      Families.Phase4.A.inner_integrable hi (Families.Phase4.A.measurable_FC C0) (FC_abs_le h0) x
  have hout : ∀ C0 : ℝ, 1 ≤ C0 → Integrable (fun x => ∫ y, f x * f y * FC C0 |x - y|) :=
    fun C0 h0 =>
      Families.Phase4.A.outer_integrable hi hi (Families.Phase4.A.measurable_FC C0) (FC_abs_le h0)
  unfold Qf
  constructor
  · have : (∫ x, ∫ y, f x * f y * FC C |x - y|) ≤ ∫ x, ∫ y, f x * f y * FC C' |x - y| := by
      refine integral_mono (hout C hC) (hout C' hC') fun x => ?_
      refine integral_mono (hin C hC x) (hin C' hC' x) fun y => ?_
      exact mul_le_mul_of_nonneg_left (FC_mono_C hCC' _) (mul_nonneg (hf.nonneg x) (hf.nonneg y))
    linarith
  · have hpt : ∀ x, (∫ y, f x * f y * FC C' |x - y|)
        ≤ (∫ y, f x * f y * FC C |x - y|) + (C' - C) * f x := by
      intro x
      have hB : Integrable (fun y => f x * f y * FC C |x - y| + (C' - C) * f x * f y) :=
        (hin C hC x).add (hi.const_mul _)
      calc (∫ y, f x * f y * FC C' |x - y|)
          ≤ ∫ y, (f x * f y * FC C |x - y| + (C' - C) * f x * f y) := by
            refine integral_mono (hin C' hC' x) hB fun y => ?_
            have h1 := FC_lip_C hCC' |x - y|
            have h2 : 0 ≤ f x * f y := mul_nonneg (hf.nonneg x) (hf.nonneg y)
            nlinarith
        _ = (∫ y, f x * f y * FC C |x - y|) + (C' - C) * f x := by
            rw [integral_add (hin C hC x) (hi.const_mul _), integral_const_mul,
              hf.integral_eq_one, mul_one]
    have hB : Integrable (fun x => (∫ y, f x * f y * FC C |x - y|) + (C' - C) * f x) :=
      (hout C hC).add (hi.const_mul _)
    have : (∫ x, ∫ y, f x * f y * FC C' |x - y|)
        ≤ (∫ x, ∫ y, f x * f y * FC C |x - y|) + (C' - C) := by
      calc (∫ x, ∫ y, f x * f y * FC C' |x - y|)
          ≤ ∫ x, ((∫ y, f x * f y * FC C |x - y|) + (C' - C) * f x) :=
            integral_mono (hout C' hC') hB hpt
        _ = (∫ x, ∫ y, f x * f y * FC C |x - y|) + (C' - C) := by
            rw [integral_add (hout C hC) (hi.const_mul _), integral_const_mul,
              hf.integral_eq_one, mul_one]
    linarith

/-- **`lem:pLipH`** (Lemma 9.22). -/
theorem lemPLipH_proof : lemPLipH_Statement := by
  intro β _hβ1 _hβ2 C C' hC hCC'
  have hC' : 1 ≤ C' := hC.trans hCC'
  set A := {f | AdmissibleWindowB β f}
  unfold pB
  rcases Set.eq_empty_or_nonempty A with hA | hA
  · have hA' : {f | AdmissibleWindowB β f} = (∅ : Set (ℝ → ℝ)) := hA
    rw [hA', Set.image_empty, Set.image_empty, Real.sInf_empty]
    constructor <;> linarith
  have hne : ∀ C0 : ℝ, (Qf (FC C0) '' A).Nonempty := fun C0 => hA.image _
  have hbdd : ∀ C0 : ℝ, 0 ≤ C0 → BddBelow (Qf (FC C0) '' A) := fun C0 hC0 => pB_bddBelow β hC0
  have h1 : sInf (Qf (FC C) '' A) ≤ sInf (Qf (FC C') '' A) := by
    refine le_csInf (hne C') ?_
    rintro _ ⟨f, hf, rfl⟩
    exact (csInf_le (hbdd C (by linarith)) ⟨f, hf, rfl⟩).trans (Qf_boundsB hf hC hCC').1
  have h2 : sInf (Qf (FC C') '' A) - (C' - C) ≤ sInf (Qf (FC C) '' A) := by
    refine le_csInf (hne C) ?_
    rintro _ ⟨f, hf, rfl⟩
    have := (csInf_le (hbdd C' (by linarith)) ⟨f, hf, rfl⟩).trans (Qf_boundsB hf hC hCC').2
    linarith
  constructor <;> linarith

end Families.Hybrid.V
