/-
# Package TS: Step 5 of Proposition 9.18 — integration in `u`

* `integral_stepH`: integrate the pointwise bound (needed only for `u < L`, since `g(u) = 0` for
  `|u| ≥ L`) against `g`, with `lem:M1H` (`HSetup.ratioForm_eq_ofRealH`) and `lem:M3H`(iii)
  (`F.lemM3H_iii_proof`, at the scale `δ`); the two tail integrals are kept as they are (they are
  bounded by `cor:tails`);
* `sSup_window_le`: the window `|u − log n| < 2δ` of `lem:M3H`(iii) lies inside the window
  `|u − log n| < 1/2` of the families four-case comparison `sSup_cfun_le`.
-/
import FamiliesH.TS.Pointwise

noncomputable section

open scoped BigOperators ContDiff
open Set MeasureTheory Filter Topology

namespace Families.Hybrid

open Families Families.Phase3.C

namespace TS

/-- For `δ ≤ 1/4` the sup of `c` over `|u − t| < 2δ` is at most its sup over `|u − t| < 1/2`. -/
lemma sSup_window_le {cf : ℝ → ℝ} {Cmax : ℝ} (hcf : ∀ u, cf u ≤ Cmax) {δ : ℝ} (hδ : 0 < δ)
    (hδ4 : δ ≤ 1 / 4) (t : ℝ) :
    sSup (cf '' {u | |u - t| < 2 * δ}) ≤ sSup (cf '' {u | |u - t| < 2 * δL}) := by
  apply csSup_le_csSup
  · exact ⟨Cmax, by rintro _ ⟨u, _, rfl⟩; exact hcf u⟩
  · exact ⟨cf t, t, by simp only [Set.mem_ofPred_eq, sub_self, abs_zero]; linarith, rfl⟩
  · apply Set.image_mono
    intro u hu
    simp only [Set.mem_ofPred_eq] at hu ⊢
    unfold δL
    linarith

variable (P : HSetup)

lemma g_nonnegH (Q T u : ℝ) : 0 ≤ P.g Q T u := P.toPS.g_nonneg (Q * T) u

/-- `lem:M3H`(iii) with `c ≡ 1`. -/
lemma M3H_iii_one {Q T δ : ℝ} (hQ : 1 < Q) (hT : 0 < T) (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4)
    (y : ℕ → ℝ) :
    ∫ u, P.g Q T u * normSq (P.rangeZ Q T) (xsH P Q T δ y u) * 1 ≤
      ∑ n ∈ P.range Q T, y n ^ 2 * (P.𝒦 Q T n n).re := by
  refine (F.lemM3H_iii_proof P rhoLoc isLocCutoff_rhoLoc Q T δ hQ hT hδ hδ4 y (fun _ => 1) 1
    (fun _ => ⟨zero_le_one, le_rfl⟩)).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun n _ => ?_
  have hne : ({u | |u - Real.log n| < 2 * δ} : Set ℝ).Nonempty :=
    ⟨Real.log n, by simp only [Set.mem_ofPred_eq, sub_self, abs_zero]; linarith⟩
  rw [hne.image_const, csSup_singleton, mul_one]

/-- **Step 5**: integrate the pointwise bound against `g`. -/
theorem integral_stepH (W : Weight) {Q T δ ε κ c₁ c₂ c₃ M A₁ A₂ ε₀ x Cmax : ℝ} (hQ : 1 < Q)
    (hT : 0 < T) (hQT : 1 < Q * T) (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4)
    (hcf : ∀ u, 0 ≤ cfun (ellS Q T) ε c₁ c₂ c₃ u ∧ cfun (ellS Q T) ε c₁ c₂ c₃ u ≤ Cmax)
    (hpt : ∀ u, u < P.L Q T → famForm W Q (P.rangeZ Q T) (P.xVec Q T (P.bVec Q T) u) ≤
      (1 + κ) ^ 3 * (cfun (ellS Q T) ε c₁ c₂ c₃ u * W.H Q) *
          normSq (P.rangeZ Q T) (xsH P Q T δ (P.bVec Q T) u) +
        ((1 + κ⁻¹) * (famForm W Q (P.rangeZ Q T) (xtH P Q T δ (P.aVec Q T) u) +
            famForm W Q (P.rangeZ Q T) (xtH P Q T δ (P.bVec Q T) u)) +
          8 * (1 + κ⁻¹) * (A₁ * normSq (P.rangeZ Q T) (xsH P Q T δ (P.aSharp Q T) u) + A₂) +
          (1 + κ⁻¹) * (8 * (c₃ * W.H Q) + 2 * M) *
            normSq (P.rangeZ Q T) (xsH P Q T δ (aPPH P Q T x) u) + ε₀))
    (hK1 : 0 ≤ (1 + κ) ^ 3 * W.H Q) (hK4 : 0 ≤ 8 * (1 + κ⁻¹) * A₁)
    (hK5 : 0 ≤ (1 + κ⁻¹) * (8 * (c₃ * W.H Q) + 2 * M)) :
    (P.ratioForm W Q T (P.bVec Q T)).re ≤
      (1 + κ) ^ 3 * W.H Q * ∑ n ∈ P.range Q T, P.bVec Q T n ^ 2 * (P.𝒦 Q T n n).re *
          sSup (cfun (ellS Q T) ε c₁ c₂ c₃ '' {u | |u - Real.log n| < 2 * δ}) +
        ((1 + κ⁻¹) * (∫ u, P.g Q T u * famForm W Q (P.rangeZ Q T) (xtH P Q T δ (P.aVec Q T) u)) +
          (1 + κ⁻¹) * (∫ u, P.g Q T u * famForm W Q (P.rangeZ Q T) (xtH P Q T δ (P.bVec Q T) u)) +
          8 * (1 + κ⁻¹) * A₁ * ∑ n ∈ P.range Q T, P.aSharp Q T n ^ 2 * (P.𝒦 Q T n n).re +
          (8 * (1 + κ⁻¹) * A₂ + ε₀) * (P.L Q T * P.aInt) ^ 2 +
          (1 + κ⁻¹) * (8 * (c₃ * W.H Q) + 2 * M) *
            ∑ n ∈ P.range Q T, aPPH P Q T x n ^ 2 * (P.𝒦 Q T n n).re) := by
  set cf := cfun (ellS Q T) ε c₁ c₂ c₃ with hcfdef
  set g := P.g Q T with hg
  set I := P.rangeZ Q T with hI
  set f₁ : ℝ → ℝ := fun u => g u * normSq I (xsH P Q T δ (P.bVec Q T) u) * cf u with hf₁
  set f₂ : ℝ → ℝ := fun u => g u * famForm W Q I (xtH P Q T δ (P.aVec Q T) u) with hf₂
  set f₃ : ℝ → ℝ := fun u => g u * famForm W Q I (xtH P Q T δ (P.bVec Q T) u) with hf₃
  set f₄ : ℝ → ℝ := fun u => g u * normSq I (xsH P Q T δ (P.aSharp Q T) u) * 1 with hf₄
  set f₅ : ℝ → ℝ := fun u => g u * normSq I (xsH P Q T δ (aPPH P Q T x) u) with hf₅
  set X₁ := (1 + κ) ^ 3 * W.H Q
  set X₂ := 1 + κ⁻¹
  set X₄ := 8 * (1 + κ⁻¹) * A₁
  set X₀ := 8 * (1 + κ⁻¹) * A₂ + ε₀
  set X₅ := (1 + κ⁻¹) * (8 * (c₃ * W.H Q) + 2 * M)
  have i₁ : Integrable f₁ :=
    (integrable_gH_mul P hQT (continuous_normSq_of I (continuous_xsH_apply P Q T δ _))).mul_bdd
      (c := Cmax) (cfun_measurable _ _ _ _ _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hcf u).1]; exact (hcf u).2)
  have i₂ : Integrable f₂ :=
    integrable_gH_mul P hQT (continuous_famForm_of W Q I (continuous_xtH_apply P Q T δ _))
  have i₃ : Integrable f₃ :=
    integrable_gH_mul P hQT (continuous_famForm_of W Q I (continuous_xtH_apply P Q T δ _))
  have i₄ : Integrable f₄ :=
    (integrable_gH_mul P hQT (continuous_normSq_of I (continuous_xsH_apply P Q T δ _))).mul_const 1
  have i₀ : Integrable g := P.toPS.g_integrable hQT
  have i₅ : Integrable f₅ :=
    integrable_gH_mul P hQT (continuous_normSq_of I (continuous_xsH_apply P Q T δ _))
  set R : ℝ → ℝ := fun u => X₁ * f₁ u + X₂ * f₂ u + X₂ * f₃ u + X₄ * f₄ u + X₀ * g u + X₅ * f₅ u
    with hR
  have iR : Integrable R :=
    (((((i₁.const_mul X₁).add (i₂.const_mul X₂)).add (i₃.const_mul X₂)).add
      (i₄.const_mul X₄)).add (i₀.const_mul X₀)).add (i₅.const_mul X₅)
  have hptR : ∀ u, g u * famForm W Q I (P.xVec Q T (P.bVec Q T) u) ≤ R u := by
    intro u
    by_cases hu : u < P.L Q T
    · have hg0 : 0 ≤ g u := g_nonnegH P Q T u
      refine (mul_le_mul_of_nonneg_left (hpt u hu) hg0).trans (le_of_eq ?_)
      simp only [hR, hf₁, hf₂, hf₃, hf₄, hf₅]
      ring
    · have hg0 : g u = 0 := g_eq_zero_of_le P hQT ((not_lt.mp hu).trans (le_abs_self u))
      simp only [hR, hf₁, hf₂, hf₃, hf₄, hf₅, hg0]
      ring_nf
      exact le_refl _
  have j1 : Integrable (fun u => X₁ * f₁ u + X₂ * f₂ u) := (i₁.const_mul X₁).add (i₂.const_mul X₂)
  have j2 : Integrable (fun u => X₁ * f₁ u + X₂ * f₂ u + X₂ * f₃ u) := j1.add (i₃.const_mul X₂)
  have j3 : Integrable (fun u => X₁ * f₁ u + X₂ * f₂ u + X₂ * f₃ u + X₄ * f₄ u) :=
    j2.add (i₄.const_mul X₄)
  have j4 : Integrable (fun u => X₁ * f₁ u + X₂ * f₂ u + X₂ * f₃ u + X₄ * f₄ u + X₀ * g u) :=
    j3.add (i₀.const_mul X₀)
  have hint : ∫ u, R u = X₁ * (∫ u, f₁ u) + X₂ * (∫ u, f₂ u) + X₂ * (∫ u, f₃ u) +
      X₄ * (∫ u, f₄ u) + X₀ * (∫ u, g u) + X₅ * (∫ u, f₅ u) := by
    simp only [hR]
    rw [integral_add j4 (i₅.const_mul X₅), integral_add j3 (i₀.const_mul X₀),
      integral_add j2 (i₄.const_mul X₄), integral_add j1 (i₃.const_mul X₂),
      integral_add (i₁.const_mul X₁) (i₂.const_mul X₂)]
    simp only [integral_const_mul]
  have hmain : (P.ratioForm W Q T (P.bVec Q T)).re ≤ ∫ u, R u := by
    rw [P.ratioForm_eq_ofRealH hQ hT W (P.bVec Q T), Complex.ofReal_re]
    have hia : Integrable (fun u => g u * famForm W Q I (P.xVec Q T (P.bVec Q T) u)) :=
      F.integrable_g_famForm_gen P.toPS hQT W Q T _
    exact integral_mono hia iR hptR
  -- the integrals
  have I₁ : ∫ u, f₁ u ≤ ∑ n ∈ P.range Q T, P.bVec Q T n ^ 2 * (P.𝒦 Q T n n).re *
      sSup (cf '' {u | |u - Real.log n| < 2 * δ}) :=
    F.lemM3H_iii_proof P rhoLoc isLocCutoff_rhoLoc Q T δ hQ hT hδ hδ4 _ cf Cmax hcf
  have I₄ : ∫ u, f₄ u ≤ ∑ n ∈ P.range Q T, P.aSharp Q T n ^ 2 * (P.𝒦 Q T n n).re :=
    M3H_iii_one P hQ hT hδ hδ4 (P.aSharp Q T)
  have I₀ : ∫ u, g u = (P.L Q T * P.aInt) ^ 2 := integral_g P.toPS hQT
  have I₅ : ∫ u, f₅ u ≤ ∑ n ∈ P.range Q T, aPPH P Q T x n ^ 2 * (P.𝒦 Q T n n).re := by
    have := M3H_iii_one P hQ hT hδ hδ4 (aPPH P Q T x)
    simpa only [mul_one] using this
  refine hmain.trans ?_
  rw [hint, I₀]
  have e1 := mul_le_mul_of_nonneg_left I₁ hK1
  have e4 := mul_le_mul_of_nonneg_left I₄ hK4
  have e5 := mul_le_mul_of_nonneg_left I₅ hK5
  linarith

end TS

end Families.Hybrid
