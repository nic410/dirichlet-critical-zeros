/-
# Theorem 1.4(a): statement checks (proved, no `sorry`)

Faithfulness pins for `thmH_Statement` (cf. `STATEMENTS-H.md` §3):
* `pB_two` — at support `β = 2` the hybrid variational constant is the audited `Families.pC`;
* `kappaT_rpow`, `betaK_zero`, `betaK` bounds — `κ_T` and `β(κ)` mean what the TeX says;
* `Iff.rfl` / `rfl` pins for the parsing of the target `p(κ_T) − ε`, of `ProportionsAtLeastH`, of `Qf`,
  and of the real powers `Q ^ κ₁`.
-/
import FamiliesH.Glue

noncomputable section

open MeasureTheory

namespace Families.Hybrid

open Families

/-- At `β = 2` the admissible class of `pB` is exactly `Families.AdmissibleWindow`. -/
theorem admissibleB_two_iff (f : ℝ → ℝ) : AdmissibleWindowB 2 f ↔ AdmissibleWindow f := by
  have hI : Set.Icc (-(2 : ℝ) / 2) (2 / 2) = Set.Icc (-1) 1 := by norm_num
  constructor
  · intro h
    refine ⟨h.nonneg, h.even, fun x hx => ?_, h.memL2, h.integral_eq_one⟩
    have := h.supp x hx
    rwa [hI] at this
  · intro h
    refine ⟨h.nonneg, h.even, fun x hx => ?_, h.memL2, h.integral_eq_one⟩
    rw [hI]
    exact h.supp x hx

/-- **`p(2; F_C) = p(C)`**: the hybrid constant at support `2` is the audited `Families.pC`. -/
theorem pB_two (C : ℝ) : pB 2 C = pC C := by
  have hS : {f | AdmissibleWindowB 2 f} = {f | AdmissibleWindow f} :=
    Set.ext fun f => admissibleB_two_iff f
  unfold pB pC
  rw [hS]

/-- `κ_T` of `T = Q^κ` is `κ` (for `Q > 1`). -/
theorem kappaT_rpow {Q κ : ℝ} (hQ : 1 < Q) : kappaT Q (Q ^ κ) = κ := by
  unfold kappaT
  rw [Real.log_rpow (by linarith)]
  exact mul_div_cancel_right₀ κ (Real.log_pos hQ).ne'

theorem betaK_zero : betaK 0 = 2 := by norm_num [betaK]

theorem betaK_one : betaK 1 = 3 / 2 := by norm_num [betaK]

theorem betaK_ten : betaK 10 = 12 / 11 := by norm_num [betaK]

/-- `β(κ) ∈ (1, 2]` for `κ ≥ 0`. -/
theorem betaK_mem {κ : ℝ} (h : 0 ≤ κ) : 1 < betaK κ ∧ betaK κ ≤ 2 :=
  ⟨one_lt_betaK h, betaK_le_two h⟩

/-! ### Parsing pins -/

/-- The target of `thmH_Statement` is `p(β(κ)) − ε`, **not** `p(β(κ) − ε)` or `pB (betaK κ) (1 − ε)`. -/
example (ε : ℝ) : (fun κ : ℝ => pB (betaK κ) 1 - ε) = (fun κ => (pB (betaK κ) 1) - ε) := rfl

/-- `ProportionsAtLeastH` unfolds to the intended `ε`–`Q₀` statement, with the target inside the
`T`-quantifier and `Q₀` before `T` (uniformity). -/
example (W : Weight) (a0 κ1 : ℝ) (p : ℝ → ℝ) :
    ProportionsAtLeastH W a0 κ1 p ↔
      ∀ ε : ℝ, 0 < ε → ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
        ∀ T ∈ Set.Icc (Real.log Q ^ a0) (Q ^ κ1),
          ((p (kappaT Q T)) - ε) * Nfam W Q T ≤ Ns0 W Q T ∧
          ((p (kappaT Q T)) - ε) * Nfam W Q T ≤ Nstar0 W Q T ∧
          (((1 + p (kappaT Q T)) / 2) - ε) * Nfam W Q T ≤ Nd W Q T :=
  Iff.rfl

/-- `Qf` (reused from `Families`): the square integral is added **outside** the double integral. -/
example (C : ℝ) (f : ℝ → ℝ) :
    Qf (FC C) f = (∫ x, f x ^ 2) + ∫ x, ∫ y, f x * f y * FC C |x - y| := rfl

/-- The heights use the real power `Q ^ κ₁` (`Real.rpow`). -/
example (Q κ : ℝ) : Q ^ κ = Real.rpow Q κ := rfl

/-- The cell heights are the closed interval `[ℓ^{a₀}, Q^{κc}]`. -/
example (a0 kc Q : ℝ) : cellHeights a0 kc Q = Set.Icc (Real.log Q ^ a0) (Q ^ kc) := rfl

/-! ### The hybrid headline generalises the audited one -/

/-- **`thmH ⇒ thmMain`** (statement-faithfulness check, proved): together with `lem:Mbeta`, the hybrid
headline implies the audited families headline `Families.thmMain_Statement`. On the polylogarithmic range
`ℓ^{a₀} ≤ T ≤ ℓ^{A₀}` one has `T ≤ Q` and `κ_T ≤ A₀ log log Q / log Q → 0`, and
`p(2) ≤ p(β(κ_T)) + 2(2/β(κ_T) − 1) ≤ p(β(κ_T)) + κ_T` by `lem:Mbeta`, with `p(2) = pC 1` (`pB_two`);
the certificate `0.932282 ≤ pC 1` is `Families.thmMain_constant`. -/
theorem thmMain_of_thmH (hM : lemMbeta_Statement) (hH : thmH_Statement) : thmMain_Statement := by
  refine ⟨fun a0 A0 ε ha0 hA0 hε => ?_, thmMain_constant⟩
  obtain ⟨η₀, hη₀, hHε⟩ := hH.1 (ε / 2) (by positivity)
  refine ⟨η₀, hη₀, fun η hη hηη₀ W hW => ?_⟩
  have hP := hHε a0 1 ha0 one_pos η hη hηη₀ W hW
  intro ε' hε'
  obtain ⟨Q₁, hQ₁⟩ := hP ε' hε'
  have hA0pos : 0 < A0 := lt_trans ha0 hA0
  set c : ℝ := min 1 (ε / 2) / A0 with hc
  have hc0 : 0 < c := div_pos (lt_min one_pos (by positivity)) hA0pos
  have hlo := (Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop).bound hc0
  obtain ⟨Q₂, hQ₂⟩ := Filter.eventually_atTop.1 hlo
  refine ⟨max Q₁ (max (Real.exp 1) Q₂), fun Q hQ T hT => ?_⟩
  have hQ1' : Q₁ ≤ Q := le_trans (le_max_left _ _) hQ
  have hQe : Real.exp 1 ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hQ
  have hQ2' : Q₂ ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hQ
  have he1 : (1 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (one_ne_zero (α := ℝ)); linarith
  have hQ1 : 1 < Q := lt_of_lt_of_le he1 hQe
  have hlogQ : 1 ≤ Real.log Q := by
    have := Real.log_le_log (Real.exp_pos 1) hQe
    rwa [Real.log_exp] at this
  have hlogpos : 0 < Real.log Q := by linarith
  have hT1 : 1 ≤ T := le_trans (Real.one_le_rpow hlogQ ha0.le) hT.1
  have hTpos : 0 < T := by linarith
  -- `A₀ log log Q ≤ min(1, ε/2) log Q`
  have hbound : A0 * Real.log (Real.log Q) ≤ min 1 (ε / 2) * Real.log Q := by
    have h := hQ₂ Q hQ2'
    simp only [Function.comp_apply, id, Real.norm_eq_abs] at h
    rw [abs_of_pos hlogpos] at h
    have h' : Real.log (Real.log Q) ≤ c * Real.log Q := le_trans (le_abs_self _) h
    have h'' := mul_le_mul_of_nonneg_left h' hA0pos.le
    have hcA : A0 * (c * Real.log Q) = min 1 (ε / 2) * Real.log Q := by
      rw [hc]; field_simp
    linarith
  -- `log T ≤ A₀ log log Q`
  have hlogT : Real.log T ≤ A0 * Real.log (Real.log Q) := by
    have := Real.log_le_log hTpos hT.2
    rwa [Real.log_rpow hlogpos] at this
  have hmin1 : min 1 (ε / 2) * Real.log Q ≤ Real.log Q := by
    have := mul_le_mul_of_nonneg_right (min_le_left 1 (ε / 2)) hlogpos.le
    linarith
  have hmin2 : min 1 (ε / 2) * Real.log Q ≤ ε / 2 * Real.log Q :=
    mul_le_mul_of_nonneg_right (min_le_right 1 (ε / 2)) hlogpos.le
  -- `T ≤ Q = Q^1`
  have hTQ : T ∈ Set.Icc (Real.log Q ^ a0) (Q ^ (1 : ℝ)) := by
    refine ⟨hT.1, ?_⟩
    rw [Real.rpow_one]
    have h1 : Real.log T ≤ Real.log Q := by linarith
    exact (Real.log_le_log_iff hTpos (by linarith)).mp h1
  -- `0 ≤ κ_T ≤ ε/2`
  have hκ0 : 0 ≤ kappaT Q T := kappaT_nonneg hQ1 hT1
  have hκε : kappaT Q T ≤ ε / 2 := by
    unfold kappaT
    rw [div_le_iff₀ hlogpos]
    linarith
  -- `p(1) ≤ p(β(κ_T)) + ε/2`
  have hMb := (hM 1 le_rfl (betaK (kappaT Q T)) 2 (one_lt_betaK hκ0).le (betaK_le_two hκ0)
    le_rfl).2
  rw [pB_two] at hMb
  have hr := betaK_ratio_le (le_refl (0 : ℝ)) hκ0
  rw [betaK_zero] at hr
  have hp : pC 1 ≤ pB (betaK (kappaT Q T)) 1 + ε / 2 := by linarith
  obtain ⟨h1, h2, h3⟩ := hQ₁ Q hQ1' T hTQ
  beta_reduce at h1 h2 h3
  have hN0 := Nfam_nonneg W Q T
  refine ⟨?_, ?_, ?_⟩
  · exact le_trans (mul_le_mul_of_nonneg_right (by linarith) hN0) h1
  · exact le_trans (mul_le_mul_of_nonneg_right (by linarith) hN0) h2
  · exact le_trans (mul_le_mul_of_nonneg_right (by linarith) hN0) h3

end Families.Hybrid
