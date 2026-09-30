/-
**Step 5 of `prop:TIsharp`** — integration in `u` (proof of
Proposition 6.24).

* `sSup_cfun_le`: for `εℓ > 1` (so `2δ = 1/2 < εℓ/2`), `sup{c(u) : |u − log n| < 2δ} ≤ (1 + d) C̃_ε(log n/ℓ)`
  (the four cases of the TeX), with `c₁ = 1 + d`, `c₂ = C_band + d`, `c₃ = C_T^+ + d`;
* `integral_step`: integrating the pointwise bound of `pointwise_bound` against `g` with `lem:M1`
  (`ratioForm_re_eq`) and `lem:M3`(iii),(iv).
-/
import Families.Phase3.C.TIsharpLevels

noncomputable section

open scoped BigOperators ContDiff
open Set MeasureTheory Filter Topology

namespace Families.Phase3.C

open Families

variable (P : PrimeSetup)

/-! ### `lem:M3` for our `ρ` and `δ` -/

lemma M3_iii {Q T : ℝ} (hQ : 1 < Q) (hT : 0 < T) (y : ℕ → ℝ) (c : ℝ → ℝ) (Cmax : ℝ)
    (hc : ∀ u, 0 ≤ c u ∧ c u ≤ Cmax) :
    ∫ u, P.g Q u * normSq (P.rangeZ Q) (xs P Q T y u) * c u ≤
      ∑ n ∈ P.range Q, y n ^ 2 * (P.𝒦 Q T n n).re * sSup (c '' {u | |u - Real.log n| < 2 * δL}) :=
  (lemM3_iii_iv P rhoLoc rhoLoc_contDiff (fun ξ => ⟨rhoLoc_nonneg ξ, rhoLoc_le_one ξ⟩)
    (fun _ h => rhoLoc_one h) (fun _ h => rhoLoc_zero h) Q T δL hQ hT δL_pos
    (by norm_num [δL]) y).1 c Cmax hc

lemma M3_iv {Q T : ℝ} (hQ : 1 < Q) (hT : 0 < T) (y : ℕ → ℝ) :
    ∫ u, P.g Q u * normSq (P.rangeZ Q) (xt P Q T y u) ≤
      8 * P.bInt * P.L Q * (∑ n ∈ P.range Q, y n ^ 2) / δL :=
  (lemM3_iii_iv P rhoLoc rhoLoc_contDiff (fun ξ => ⟨rhoLoc_nonneg ξ, rhoLoc_le_one ξ⟩)
    (fun _ h => rhoLoc_one h) (fun _ h => rhoLoc_zero h) Q T δL hQ hT δL_pos
    (by norm_num [δL]) y).2

/-- `lem:M3`(iii) with `c ≡ 1`. -/
lemma M3_iii_one {Q T : ℝ} (hQ : 1 < Q) (hT : 0 < T) (y : ℕ → ℝ) :
    ∫ u, P.g Q u * normSq (P.rangeZ Q) (xs P Q T y u) * 1 ≤
      ∑ n ∈ P.range Q, y n ^ 2 * (P.𝒦 Q T n n).re := by
  refine (M3_iii P hQ hT y (fun _ => 1) 1 (fun _ => ⟨zero_le_one, le_rfl⟩)).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun n _ => ?_
  have hne : ({u | |u - Real.log n| < 2 * δL} : Set ℝ).Nonempty :=
    ⟨Real.log n, by simp only [Set.mem_ofPred_eq, sub_self, abs_zero]; unfold δL; norm_num⟩
  rw [hne.image_const, csSup_singleton, mul_one]

/-! ### The profile comparison -/

lemma cfun_measurable (ℓ ε c₁ c₂ c₃ : ℝ) : Measurable (cfun ℓ ε c₁ c₂ c₃) := by
  unfold cfun
  exact Measurable.ite measurableSet_Iic measurable_const
    (Measurable.ite measurableSet_Iic measurable_const measurable_const)

/-- **Step 5, the four cases**: `sup{c(u) : |u − t| < 1/2} ≤ (1 + d) C̃_ε(t/ℓ)` for `εℓ > 1`. -/
lemma sSup_cfun_le {ℓ ε d Cband CT : ℝ} (hℓ : 0 < ℓ) (hεℓ : 1 < ε * ℓ) (hd : 0 ≤ d)
    (hCband : 1 ≤ Cband) (hCT : 1 ≤ CT) {Ct : ℝ → ℝ} (hCt1 : ∀ α, 1 ≤ Ct α)
    (hband : ∀ α, 1 - 3 / 2 * ε ≤ α → α ≤ 1 + 3 / 2 * ε → Cband ≤ Ct α)
    (hCTge : ∀ α, 1 + ε / 2 ≤ α → CT ≤ Ct α) (t : ℝ) :
    sSup (cfun ℓ ε (1 + d) (Cband + d) (CT + d) '' {u | |u - t| < 2 * δL}) ≤ (1 + d) * Ct (t / ℓ) := by
  have hne : ((cfun ℓ ε (1 + d) (Cband + d) (CT + d)) '' {u | |u - t| < 2 * δL}).Nonempty :=
    ⟨_, ⟨t, by simp only [Set.mem_ofPred_eq, sub_self, abs_zero]; unfold δL; norm_num, rfl⟩⟩
  refine csSup_le hne ?_
  rintro _ ⟨u, hu, rfl⟩
  simp only [Set.mem_ofPred_eq] at hu
  unfold δL at hu
  rw [abs_lt] at hu
  have hα : ∀ a : ℝ, a * ℓ ≤ t → a ≤ t / ℓ := fun a h => by rw [le_div_iff₀ hℓ]; exact h
  have hα' : ∀ a : ℝ, t ≤ a * ℓ → t / ℓ ≤ a := fun a h => by rw [div_le_iff₀ hℓ]; exact h
  unfold cfun
  split_ifs with h1 h2
  · have := hCt1 (t / ℓ); nlinarith
  · have hlo : 1 - 3 / 2 * ε ≤ t / ℓ := hα _ (by nlinarith)
    have hhi : t / ℓ ≤ 1 + 3 / 2 * ε := hα' _ (by nlinarith)
    have := hband _ hlo hhi
    nlinarith
  · have hlo : 1 + ε / 2 ≤ t / ℓ := hα _ (by nlinarith)
    have := hCTge _ hlo
    nlinarith

/-! ### Integration -/

lemma integrable_g_normSq_xs {Q : ℝ} (hQ : 1 < Q) (T : ℝ) (y : ℕ → ℝ) :
    Integrable (fun u => P.g Q u * normSq (P.rangeZ Q) (xs P Q T y u)) :=
  integrable_g_mul P hQ (continuous_normSq_xs P Q T _ y)

lemma integrable_g_normSq_xt {Q : ℝ} (hQ : 1 < Q) (T : ℝ) (y : ℕ → ℝ) :
    Integrable (fun u => P.g Q u * normSq (P.rangeZ Q) (xt P Q T y u)) :=
  integrable_g_mul P hQ (continuous_normSq_xt P Q T _ y)

/-- **Step 5**: integrate the pointwise bound against `g`. -/
theorem integral_step (W : Weight) {Q T ε κ c₁ c₂ c₃ M A₁ A₂ ε₀ x Cmax : ℝ} (hQ : 1 < Q)
    (hT : 0 < T) (hκ : 0 < κ) (hH : 0 ≤ W.H Q)
    (hcf : ∀ u, 0 ≤ cfun (Real.log Q) ε c₁ c₂ c₃ u ∧ cfun (Real.log Q) ε c₁ c₂ c₃ u ≤ Cmax)
    (hpt : ∀ u, famForm W Q (P.rangeZ Q) (P.xVec Q T (P.bVec Q T) u) ≤
      (1 + κ) ^ 3 * (cfun (Real.log Q) ε c₁ c₂ c₃ u * W.H Q) *
          normSq (P.rangeZ Q) (xs P Q T (P.bVec Q T) u) +
        ((1 + κ⁻¹) * M * (normSq (P.rangeZ Q) (xt P Q T (P.aVec Q) u) +
            normSq (P.rangeZ Q) (xt P Q T (P.bVec Q T) u)) +
          8 * (1 + κ⁻¹) * (A₁ * normSq (P.rangeZ Q) (xs P Q T (P.aSharp Q T) u) + A₂) +
          (1 + κ⁻¹) * (8 * (c₃ * W.H Q) + 2 * M) *
            normSq (P.rangeZ Q) (xs P Q T (aPP P Q x) u) + ε₀))
    (hK2 : 0 ≤ (1 + κ⁻¹) * M) (hK4 : 0 ≤ 8 * (1 + κ⁻¹) * A₁)
    (hK5 : 0 ≤ (1 + κ⁻¹) * (8 * (c₃ * W.H Q) + 2 * M)) :
    (P.ratioForm W Q T (P.bVec Q T)).re ≤
      (1 + κ) ^ 3 * W.H Q * ∑ n ∈ P.range Q, P.bVec Q T n ^ 2 * (P.𝒦 Q T n n).re *
          sSup (cfun (Real.log Q) ε c₁ c₂ c₃ '' {u | |u - Real.log n| < 2 * δL}) +
        ((1 + κ⁻¹) * M * (8 * P.bInt * P.L Q * (∑ n ∈ P.range Q, P.aVec Q n ^ 2) / δL) +
          (1 + κ⁻¹) * M * (8 * P.bInt * P.L Q * (∑ n ∈ P.range Q, P.bVec Q T n ^ 2) / δL) +
          8 * (1 + κ⁻¹) * A₁ * ∑ n ∈ P.range Q, P.aSharp Q T n ^ 2 * (P.𝒦 Q T n n).re +
          (8 * (1 + κ⁻¹) * A₂ + ε₀) * (P.L Q * P.aInt) ^ 2 +
          (1 + κ⁻¹) * (8 * (c₃ * W.H Q) + 2 * M) *
            ∑ n ∈ P.range Q, aPP P Q x n ^ 2 * (P.𝒦 Q T n n).re) := by
  set cf := cfun (Real.log Q) ε c₁ c₂ c₃ with hcfdef
  set g := P.g Q with hg
  set f₁ : ℝ → ℝ := fun u => g u * normSq (P.rangeZ Q) (xs P Q T (P.bVec Q T) u) * cf u with hf₁
  set f₂ : ℝ → ℝ := fun u => g u * normSq (P.rangeZ Q) (xt P Q T (P.aVec Q) u) with hf₂
  set f₃ : ℝ → ℝ := fun u => g u * normSq (P.rangeZ Q) (xt P Q T (P.bVec Q T) u) with hf₃
  set f₄ : ℝ → ℝ := fun u => g u * normSq (P.rangeZ Q) (xs P Q T (P.aSharp Q T) u) * 1 with hf₄
  set f₅ : ℝ → ℝ := fun u => g u * normSq (P.rangeZ Q) (xs P Q T (aPP P Q x) u) with hf₅
  set X₁ := (1 + κ) ^ 3 * W.H Q
  set X₂ := (1 + κ⁻¹) * M
  set X₄ := 8 * (1 + κ⁻¹) * A₁
  set X₀ := 8 * (1 + κ⁻¹) * A₂ + ε₀
  set X₅ := (1 + κ⁻¹) * (8 * (c₃ * W.H Q) + 2 * M)
  have i₁ : Integrable f₁ :=
    (integrable_g_normSq_xs P hQ T _).mul_bdd (c := Cmax) (cfun_measurable _ _ _ _ _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hcf u).1]; exact (hcf u).2)
  have i₂ : Integrable f₂ := integrable_g_normSq_xt P hQ T _
  have i₃ : Integrable f₃ := integrable_g_normSq_xt P hQ T _
  have i₄ : Integrable f₄ := (integrable_g_normSq_xs P hQ T _).mul_const 1
  have i₀ : Integrable g := P.g_integrable hQ
  have i₅ : Integrable f₅ := integrable_g_normSq_xs P hQ T _
  set R : ℝ → ℝ := fun u => X₁ * f₁ u + X₂ * f₂ u + X₂ * f₃ u + X₄ * f₄ u + X₀ * g u + X₅ * f₅ u
    with hR
  have iR : Integrable R :=
    (((((i₁.const_mul X₁).add (i₂.const_mul X₂)).add (i₃.const_mul X₂)).add
      (i₄.const_mul X₄)).add (i₀.const_mul X₀)).add (i₅.const_mul X₅)
  have hptR : ∀ u, g u * famForm W Q (P.rangeZ Q) (P.xVec Q T (P.bVec Q T) u) ≤ R u := by
    intro u
    have hg0 : 0 ≤ g u := P.g_nonneg Q u
    refine (mul_le_mul_of_nonneg_left (hpt u) hg0).trans (le_of_eq ?_)
    simp only [hR, hf₁, hf₂, hf₃, hf₄, hf₅]
    ring
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
    rw [ratioForm_re_eq P hQ W T (P.bVec Q T)]
    exact integral_mono (integrable_g_famForm P hQ W T _) iR hptR
  -- the six integrals
  have I₁ : ∫ u, f₁ u ≤ ∑ n ∈ P.range Q, P.bVec Q T n ^ 2 * (P.𝒦 Q T n n).re *
      sSup (cf '' {u | |u - Real.log n| < 2 * δL}) := M3_iii P hQ hT _ cf Cmax hcf
  have I₂ := M3_iv P hQ hT (P.aVec Q)
  have I₃ := M3_iv P hQ hT (P.bVec Q T)
  have I₄ := M3_iii_one P hQ hT (P.aSharp Q T)
  have I₀ : ∫ u, g u = (P.L Q * P.aInt) ^ 2 := integral_g P hQ
  have I₅ : ∫ u, f₅ u ≤ ∑ n ∈ P.range Q, aPP P Q x n ^ 2 * (P.𝒦 Q T n n).re := by
    have := M3_iii_one P hQ hT (aPP P Q x)
    simpa only [mul_one] using this
  have hX₁ : 0 ≤ X₁ := by positivity
  refine hmain.trans ?_
  rw [hint, I₀]
  have e1 := mul_le_mul_of_nonneg_left I₁ hX₁
  have e2 := mul_le_mul_of_nonneg_left I₂ hK2
  have e3 := mul_le_mul_of_nonneg_left I₃ hK2
  have e4 := mul_le_mul_of_nonneg_left I₄ hK4
  have e5 := mul_le_mul_of_nonneg_left I₅ hK5
  linarith

end Families.Phase3.C
