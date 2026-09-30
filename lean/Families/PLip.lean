/-
`lem:pLip` (main.tex §7.1): `p` is nonincreasing and `p(C') ≥ p(C) − (C' − C)` for `C' ≥ C ≥ 1`.
-/
import Families.Variational

noncomputable section

open MeasureTheory

namespace Families

private lemma measurable_FC (C : ℝ) : Measurable (FC C) := by
  unfold FC
  exact Measurable.ite measurableSet_Iic measurable_id measurable_const

private lemma FC_nonneg {C : ℝ} (hC : 0 ≤ C) {α : ℝ} (hα : 0 ≤ α) : 0 ≤ FC C α := by
  unfold FC; split_ifs <;> assumption

private lemma FC_le {C : ℝ} (hC : 1 ≤ C) (α : ℝ) : FC C α ≤ C := by
  unfold FC; split_ifs with h <;> linarith

private lemma FC_mono {C C' : ℝ} (hCC' : C ≤ C') (α : ℝ) : FC C α ≤ FC C' α := by
  unfold FC; split_ifs <;> linarith

private lemma FC_lip {C C' : ℝ} (hCC' : C ≤ C') (α : ℝ) : FC C' α ≤ FC C α + (C' - C) := by
  unfold FC; split_ifs <;> linarith

private lemma integrable_of_admissible {f : ℝ → ℝ} (hf : AdmissibleWindow f) : Integrable f := by
  by_contra h
  have := integral_undef h
  rw [hf.integral_eq_one] at this
  exact one_ne_zero this

/-- For admissible `f` and `1 ≤ C`: the inner integrands are integrable for every `x`. -/
private lemma inner_integrable {f : ℝ → ℝ} (hf : AdmissibleWindow f) {C : ℝ} (hC : 1 ≤ C) (x : ℝ) :
    Integrable (fun y => f x * f y * FC C |x - y|) := by
  have hi := (integrable_of_admissible hf).const_mul (f x)
  refine hi.mul_bdd (c := C) ?_ (Filter.Eventually.of_forall fun y => ?_)
  · exact ((measurable_FC C).comp (measurable_const.sub measurable_id).abs).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (FC_nonneg (by linarith) (abs_nonneg _))]
    exact FC_le hC _

/-- For admissible `f` and `1 ≤ C`: the outer integrand is integrable. -/
private lemma outer_integrable {f : ℝ → ℝ} (hf : AdmissibleWindow f) {C : ℝ} (hC : 1 ≤ C) :
    Integrable (fun x => ∫ y, f x * f y * FC C |x - y|) := by
  have hi := integrable_of_admissible hf
  have hprod : Integrable (fun z : ℝ × ℝ => f z.1 * f z.2) (volume.prod volume) := hi.mul_prod hi
  have hmeas : AEStronglyMeasurable (fun z : ℝ × ℝ => FC C |z.1 - z.2|) (volume.prod volume) :=
    ((measurable_FC C).comp (measurable_fst.sub measurable_snd).abs).aestronglyMeasurable
  have h2 : Integrable (fun z : ℝ × ℝ => f z.1 * f z.2 * FC C |z.1 - z.2|) (volume.prod volume) := by
    refine hprod.mul_bdd (c := C) hmeas (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (FC_nonneg (by linarith) (abs_nonneg _))]
    exact FC_le hC _
  exact h2.integral_prod_left

/-- `𝒬_{F_C}(f) ≤ 𝒬_{F_{C'}}(f) ≤ 𝒬_{F_C}(f) + (C' − C)` for admissible `f`. -/
private lemma Qf_bounds {f : ℝ → ℝ} (hf : AdmissibleWindow f) {C C' : ℝ} (hC : 1 ≤ C)
    (hCC' : C ≤ C') :
    Qf (FC C) f ≤ Qf (FC C') f ∧ Qf (FC C') f ≤ Qf (FC C) f + (C' - C) := by
  have hC' : 1 ≤ C' := hC.trans hCC'
  have hi := integrable_of_admissible hf
  unfold Qf
  constructor
  · have : (∫ x, ∫ y, f x * f y * FC C |x - y|) ≤ ∫ x, ∫ y, f x * f y * FC C' |x - y| := by
      refine integral_mono (outer_integrable hf hC) (outer_integrable hf hC') fun x => ?_
      refine integral_mono (inner_integrable hf hC x) (inner_integrable hf hC' x) fun y => ?_
      exact mul_le_mul_of_nonneg_left (FC_mono hCC' _) (mul_nonneg (hf.nonneg x) (hf.nonneg y))
    linarith
  · have hpt : ∀ x, (∫ y, f x * f y * FC C' |x - y|)
        ≤ (∫ y, f x * f y * FC C |x - y|) + (C' - C) * f x := by
      intro x
      have hB : Integrable (fun y => f x * f y * FC C |x - y| + (C' - C) * f x * f y) :=
        (inner_integrable hf hC x).add (hi.const_mul _)
      calc (∫ y, f x * f y * FC C' |x - y|)
          ≤ ∫ y, (f x * f y * FC C |x - y| + (C' - C) * f x * f y) := by
            refine integral_mono (inner_integrable hf hC' x) hB fun y => ?_
            have h1 := FC_lip hCC' |x - y|
            have h2 : 0 ≤ f x * f y := mul_nonneg (hf.nonneg x) (hf.nonneg y)
            nlinarith
        _ = (∫ y, f x * f y * FC C |x - y|) + (C' - C) * f x := by
            rw [integral_add (inner_integrable hf hC x) (hi.const_mul _), integral_const_mul,
              hf.integral_eq_one, mul_one]
    have hB : Integrable (fun x => (∫ y, f x * f y * FC C |x - y|) + (C' - C) * f x) :=
      (outer_integrable hf hC).add (hi.const_mul _)
    have : (∫ x, ∫ y, f x * f y * FC C' |x - y|)
        ≤ (∫ x, ∫ y, f x * f y * FC C |x - y|) + (C' - C) := by
      calc (∫ x, ∫ y, f x * f y * FC C' |x - y|)
          ≤ ∫ x, ((∫ y, f x * f y * FC C |x - y|) + (C' - C) * f x) :=
            integral_mono (outer_integrable hf hC') hB hpt
        _ = (∫ x, ∫ y, f x * f y * FC C |x - y|) + (C' - C) := by
            rw [integral_add (outer_integrable hf hC) (hi.const_mul _), integral_const_mul,
              hf.integral_eq_one, mul_one]
    linarith

/-- `𝒬_{F_C}(f) ≥ 0` for admissible `f` and `C ≥ 0`. -/
private lemma Qf_nonneg {f : ℝ → ℝ} (hf : AdmissibleWindow f) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ Qf (FC C) f := by
  unfold Qf
  refine add_nonneg (integral_nonneg fun x => sq_nonneg _) (integral_nonneg fun x => ?_)
  refine integral_nonneg fun y => ?_
  exact mul_nonneg (mul_nonneg (hf.nonneg x) (hf.nonneg y)) (FC_nonneg hC (abs_nonneg _))

/-- **`lem:pLip`.** For `1 ≤ C ≤ C'`: `p(C') ≤ p(C)` and `p(C) − (C' − C) ≤ p(C')`. -/
theorem pC_antitone_lip (C C' : ℝ) (hC : 1 ≤ C) (hCC' : C ≤ C') :
    pC C' ≤ pC C ∧ pC C - (C' - C) ≤ pC C' := by
  have hC' : 1 ≤ C' := hC.trans hCC'
  set A := {f | AdmissibleWindow f}
  unfold pC
  rcases Set.eq_empty_or_nonempty A with hA | hA
  · have hA' : {f | AdmissibleWindow f} = (∅ : Set (ℝ → ℝ)) := hA
    rw [hA', Set.image_empty, Set.image_empty, Real.sInf_empty]
    constructor <;> linarith
  have hne : ∀ C0 : ℝ, (Qf (FC C0) '' A).Nonempty := fun C0 => hA.image _
  have hbdd : ∀ C0 : ℝ, 0 ≤ C0 → BddBelow (Qf (FC C0) '' A) := by
    intro C0 hC0
    refine ⟨0, ?_⟩
    rintro _ ⟨f, hf, rfl⟩
    exact Qf_nonneg hf hC0
  have h1 : sInf (Qf (FC C) '' A) ≤ sInf (Qf (FC C') '' A) := by
    refine le_csInf (hne C') ?_
    rintro _ ⟨f, hf, rfl⟩
    exact (csInf_le (hbdd C (by linarith)) ⟨f, hf, rfl⟩).trans (Qf_bounds hf hC hCC').1
  have h2 : sInf (Qf (FC C') '' A) - (C' - C) ≤ sInf (Qf (FC C) '' A) := by
    refine le_csInf (hne C) ?_
    rintro _ ⟨f, hf, rfl⟩
    have := (csInf_le (hbdd C' (by linarith)) ⟨f, hf, rfl⟩).trans (Qf_bounds hf hC hCC').2
    linarith
  constructor <;> linarith

end Families
