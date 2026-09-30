/-
# `prop:second` from its two halves

`propSecond_of_parts`: the finite-centre replacement (`FC2_Statement`, `𝔐 ≤ 𝓜/(aL)² + o(HTℓ)`), the
prime-side bound for `𝓜` (`McalBound_Statement`) and the lower half of `lem:RvM` give `prop:second`
(proof of Proposition 5.13: "divide by `a²L²` and use `L = λℓ`, `|J| = (1−2θ)T` and `N = (1+o(1))HTℓ/2π`").
-/
import Families.Ported.Second.Defs
import Families.Phase4.A.QfBasic
import Families.Phase3.C.B1
import Families.Assembly

noncomputable section

open scoped BigOperators ContDiff
open MeasureTheory Filter Topology

namespace Families.Ported.Second

open Families

lemma aInt_pos (P : PrimeSetup) : 0 < P.aInt := by
  obtain ⟨x₀, hx₀⟩ := P.ψ_ne
  have hc : Continuous P.vfun := (P.ψ_smooth.continuous).pow 2
  have hcs : HasCompactSupport P.vfun := by
    obtain ⟨r, -, hr⟩ := P.ψ_supp
    refine HasCompactSupport.intro (K := Set.Icc (-|r|) (|r|)) isCompact_Icc ?_
    intro x hx
    have hx' : r < |x| := by
      by_contra hcon
      exact hx (Set.mem_Icc.mpr (abs_le.mp ((not_lt.mp hcon).trans (le_abs_self r))))
    simp [PrimeSetup.vfun, hr x hx']
  have hv : P.vfun x₀ ≠ 0 := by simp only [PrimeSetup.vfun]; exact pow_ne_zero 2 hx₀
  exact hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs (fun x => sq_nonneg _) hv

/-- `𝒬_F(f_v) ≥ 0` for `F(α) = c(α) min(α, 1+ε₄)`, `c ≥ 1`. -/
lemma Qf_fv_nonneg (P : PrimeSetup) (c : ℝ → ℝ) (hc1 : ∀ α, 1 ≤ c α) :
    0 ≤ Qf (fun α => c α * min α (1 + 2 * P.ε₃))
      (fun x => P.vfun (x / P.lam) / (P.lam * P.aInt)) := by
  refine Families.Phase4.A.Qf_nonneg_of (fun α hα => ?_) (fun x => ?_)
  · exact mul_nonneg (le_trans zero_le_one (hc1 α))
      (le_min hα (by linarith [P.ε₃_pos]))
  · exact div_nonneg (sq_nonneg _) (mul_pos P.lam_pos (aInt_pos P)).le

/-- The arithmetic of the final step, with `Y = HTℓ/2π`. -/
lemma final_arith {Mf A Y N Qv s δ δ₃ : ℝ} (hY : 0 ≤ Y) (hQv : 0 ≤ Qv) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) (hδ : 0 < δ) (hδ₃h : δ₃ ≤ 1 / 2) (hδ₃0 : 0 ≤ δ₃)
    (hδ₃Q : δ₃ * (Qv + 1) ≤ δ / 6)
    (h1 : Mf ≤ A + δ / 6 * Y) (h2 : A ≤ s * Y * Qv + δ / 6 * Y) (h3 : (1 - δ₃) * Y ≤ N) :
    Mf ≤ s * Qv * N + δ * N := by
  have hY2 : Y ≤ 2 * N := by nlinarith
  have hN : 0 ≤ N := by linarith
  have e1 : s * Y * Qv = s * Qv * ((1 - δ₃) * Y) + δ₃ * (s * Qv * Y) := by ring
  have t1 : s * Qv * ((1 - δ₃) * Y) ≤ s * Qv * N :=
    mul_le_mul_of_nonneg_left h3 (mul_nonneg hs0 hQv)
  have t2 : s * Qv * Y ≤ Qv * (2 * N) := by
    have : s * Qv ≤ Qv := by nlinarith
    calc s * Qv * Y ≤ Qv * Y := mul_le_mul_of_nonneg_right this hY
      _ ≤ Qv * (2 * N) := mul_le_mul_of_nonneg_left hY2 hQv
  have t3 : δ₃ * (s * Qv * Y) ≤ δ₃ * (Qv * (2 * N)) := mul_le_mul_of_nonneg_left t2 hδ₃0
  have t4 : δ₃ * (Qv * (2 * N)) ≤ δ / 3 * N := by
    have : δ₃ * Qv ≤ δ / 6 := by nlinarith
    nlinarith
  have t5 : δ / 6 * Y ≤ δ / 3 * N := by nlinarith
  linarith

/-- **`prop:second` from its halves** (proof of Proposition 5.13). -/
theorem propSecond_of_parts (hFC2 : FC2_Statement) (hM : McalBound_Statement)
    (hRvM : lemRvM_lower_Statement) : propSecond_Statement := by
  intro P W τ₀ c hc hc1 hprof δ hδ
  set Qv := Qf (fun α => c α * min α (1 + 2 * P.ε₃))
    (fun x => P.vfun (x / P.lam) / (P.lam * P.aInt)) with hQv
  have hQv0 : 0 ≤ Qv := Qf_fv_nonneg P c hc1
  have ha := aInt_pos P
  have hpi := Real.pi_pos
  set δ₁ : ℝ := δ / 6 / (2 * Real.pi) with hδ₁
  set δ₂ : ℝ := P.aInt ^ 2 * (δ / 6) / (2 * Real.pi) with hδ₂
  set δ₃ : ℝ := min (1 / 2) (δ / 6 / (Qv + 1)) with hδ₃
  have hδ₁0 : 0 < δ₁ := by positivity
  have hδ₂0 : 0 < δ₂ := by positivity
  have hδ₃0 : 0 < δ₃ := lt_min (by norm_num) (by positivity)
  have hδ₃h : δ₃ ≤ 1 / 2 := min_le_left _ _
  have hδ₃Q : δ₃ * (Qv + 1) ≤ δ / 6 := by
    have := min_le_right (1 / 2 : ℝ) (δ / 6 / (Qv + 1))
    rw [← hδ₃, le_div_iff₀ (by positivity)] at this
    exact this
  obtain ⟨Q₁, hQ₁⟩ := hFC2 P W τ₀ δ₁ hδ₁0
  obtain ⟨Q₂, hQ₂⟩ := hM P W c hc hc1 hprof δ₂ hδ₂0
  obtain ⟨Q₃, hQ₃⟩ := hRvM W P.a0 P.A0 P.a0_pos P.a0_lt δ₃ hδ₃0
  refine ⟨max (max Q₁ Q₂) (max Q₃ (Real.exp 1)), fun Q hQ T hT => ?_⟩
  have hQ1 : Q₁ ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hQ
  have hQ2 : Q₂ ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hQ
  have hQ3 : Q₃ ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hQ
  have hQe : Real.exp 1 ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hQ
  have hT1 : 1 ≤ T := Families.Phase3.C.one_le_T P hQe hT
  have hℓ : 1 ≤ Real.log Q := by
    have := Real.log_le_log (Real.exp_pos _) hQe; rwa [Real.log_exp] at this
  have hL : 0 < P.L Q := mul_pos P.lam_pos (by linarith)
  have hH : 0 ≤ W.H Q := Families.Weight.H_nonneg W Q
  have h1 := hQ₁ Q hQ1 T hT
  have h2 := hQ₂ Q hQ2 T hT
  have h3 := hQ₃ Q hQ3 T hT
  unfold ell at h1 h2
  rw [← hQv] at h2
  set Y : ℝ := W.H Q * T * Real.log Q / (2 * Real.pi) with hY
  have hY0 : 0 ≤ Y := by positivity
  have haL : 0 < (P.aInt * P.L Q) ^ 2 := by positivity
  have h1' : P.Mfrak W Q T τ₀ ≤ Mcal P W Q T / (P.aInt * P.L Q) ^ 2 + δ / 6 * Y := by
    have : δ₁ * (W.H Q * T * Real.log Q) = δ / 6 * Y := by
      rw [hδ₁, hY]; field_simp
    linarith
  have h2' : Mcal P W Q T / (P.aInt * P.L Q) ^ 2 ≤ (1 - 2 * P.θ) * Y * Qv + δ / 6 * Y := by
    rw [div_le_iff₀ haL]
    refine h2.trans (le_of_eq ?_)
    have hJ : P.Jlen T = (1 - 2 * P.θ) * T := rfl
    rw [hJ, hY, hδ₂]
    field_simp
  exact final_arith hY0 hQv0 (by linarith [P.θ_lt]) (by linarith [P.θ_pos]) hδ hδ₃h hδ₃0.le hδ₃Q
    h1' h2' h3

end Families.Ported.Second
