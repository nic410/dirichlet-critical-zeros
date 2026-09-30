/-
# Package TS: Step 4(b), the `T^♮`-form of `x♯^s(u)` at polynomial height

`‖x♯^s‖²_{T^♮} = ∑_{e ≤ Q} ν(e) ∑*_c |S_{x♯^s}(c/e)|²`, split at `E₀ = ⌊2Y/(QT)⌋ ≥ R_max`:
* levels `e ≤ E₀`: `ν(e) ≤ 6‖w̃‖_∞η^{−2}` and the additive large sieve **on the localisation interval**
  (`K(u)` integers; the families proof uses all of `[1, Y]`, which is too long once `Y ≫ Q²`),
  `≤ ν_max C₀ (K(u) + E₀²) ‖x♯^s‖²`;
* levels `e > E₀`: `|S_{x♯^s}(c/e)| ≤ C_F Q^{−1}` (`farey_sharpH`), so they contribute `≤ ν_max C_F²`.
-/
import FamiliesH.TS.Farey

noncomputable section

open scoped BigOperators ContDiff
open Set MeasureTheory Filter Topology

namespace Families.Hybrid

open Families Families.Phase3.C

namespace TS

variable (P : HSetup)

/-- `R_j ≤ E₀ = ⌊2Y/(QT)⌋` for every block (the families `Rj_le_E0` at `(QT, 1)`). -/
lemma Rj_le_E0H {Q T : ℝ} (hQT : 1 < Q * T) {j : ℕ} (hj : j ∈ P.blocks Q T) :
    P.Rj Q T j ≤ ⌊2 * P.Y Q T / (Q * T)⌋₊ := by
  rw [P.Rj_eq_one]
  exact Rj_le_E0 P.toPS hQT le_rfl hj

/-- **Step 4(b)** at polynomial height: for `δ ∈ [T^{−1}, 1]`,
`‖x♯^s(u)‖²_{T^♮} ≤ ν_max C₀ (K(u) + E₀²) ‖x♯^s(u)‖² + ν_max C_F²`. -/
theorem levelForm_xsSharpH {C₀ : ℝ} (hadd : MVLargeSieveAdd C₀) (W : Weight) :
    ∃ CF Q₀ : ℝ, 0 ≤ CF ∧ ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ P.heights Q, ∀ δ : ℝ, 0 < δ → 1 ≤ δ⁻¹ →
      δ⁻¹ ≤ T → ∀ u : ℝ,
      levelForm (levels Q) (aNat W Q) (P.rangeZ Q T) (xsH P Q T δ (P.aSharp Q T) u) ≤
        6 * W.wtmax * W.η⁻¹ ^ 2 * max C₀ 0 *
            (KlocH δ u + (⌊2 * P.Y Q T / (Q * T)⌋₊ : ℝ) ^ 2) *
            normSq (P.rangeZ Q T) (xsH P Q T δ (P.aSharp Q T) u) +
          6 * W.wtmax * W.η⁻¹ ^ 2 * CF ^ 2 := by
  obtain ⟨CF, QF, hCF0, hF⟩ := farey_sharpH P 1
  refine ⟨CF, max QF (Real.exp 1), hCF0, ?_⟩
  intro Q hQ T hT δ hδ hδ1 hδT u
  have hQF : QF ≤ Q := le_of_max_le_left hQ
  have hQe : Real.exp 1 ≤ Q := le_of_max_le_right hQ
  have hQ1 : 1 < Q :=
    lt_of_lt_of_le (by have := Real.add_one_lt_exp (x := 1) one_ne_zero; linarith) hQe
  have hQ0 : 0 < Q := by linarith
  have hT1 := one_le_T_of_mem P hQe hT
  have hQT1 : 1 < Q * T := by nlinarith
  set ν : ℝ := 6 * W.wtmax * W.η⁻¹ ^ 2 with hν
  have hν0 : 0 ≤ ν := by have := wtmax_nonneg W; positivity
  set E₀ : ℕ := ⌊2 * P.Y Q T / (Q * T)⌋₊ with hE₀
  set x := xsH P Q T δ (P.aSharp Q T) u with hx
  have hsupp : ∀ n, x n ≠ 0 → (n ∈ P.rangeZ Q T ↔ n ∈ intervalZ (N0H δ u) (KlocH δ u)) :=
    supp_iff_of_xsH P hδ (vanish_aSharpH P hQT1) u
  set Se : ℕ → ℝ := fun e => ∑ c ∈ reduced e, ‖S (P.rangeZ Q T) x ((c : ℝ) / e)‖ ^ 2 with hSe
  have hSe0 : ∀ e, 0 ≤ Se e := fun e => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have haN : ∀ e ∈ levels Q, 0 ≤ aNat W Q e ∧ aNat W Q e ≤ ν := fun e he =>
    ⟨aNat_nonneg W Q hQ0 e he, aNat_le W hQ0 (Finset.mem_Icc.mp he).1⟩
  have hLF : levelForm (levels Q) (aNat W Q) (P.rangeZ Q T) x =
      ∑ e ∈ levels Q, aNat W Q e * Se e := rfl
  rw [hLF, ← Finset.sum_filter_add_sum_filter_not (levels Q) (fun e => e ≤ E₀)]
  -- low levels: the additive large sieve on the localisation interval
  have hlow : ∑ e ∈ (levels Q).filter (fun e => e ≤ E₀), aNat W Q e * Se e ≤
      ν * max C₀ 0 * (KlocH δ u + (E₀ : ℝ) ^ 2) * normSq (P.rangeZ Q T) x := by
    calc ∑ e ∈ (levels Q).filter (fun e => e ≤ E₀), aNat W Q e * Se e
        ≤ ∑ e ∈ (levels Q).filter (fun e => e ≤ E₀), ν * Se e :=
          Finset.sum_le_sum fun e he =>
            mul_le_mul_of_nonneg_right (haN e (Finset.mem_filter.mp he).1).2 (hSe0 e)
      _ ≤ ∑ e ∈ Finset.Icc 1 E₀, ν * Se e := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (fun e he => ?_)
            (fun e _ _ => mul_nonneg hν0 (hSe0 e))
          obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
          exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp he1).1, he2⟩
      _ = ν * ∑ e ∈ Finset.Icc 1 E₀, Se e := by rw [Finset.mul_sum]
      _ ≤ ν * (max C₀ 0 * (KlocH δ u + (E₀ : ℝ) ^ 2) * normSq (P.rangeZ Q T) x) := by
          apply mul_le_mul_of_nonneg_left _ hν0
          have h := hadd E₀ (N0H δ u) (KlocH δ u) x
          simp only [hSe]
          simp_rw [S_congr_supp hsupp]
          rw [normSq_congr_supp hsupp]
          refine h.trans ?_
          apply mul_le_mul_of_nonneg_right _ (normSq_nonneg' _ _)
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ = _ := by ring
  -- high levels: `|S| ≤ C_F Q^{−1}`
  have hhigh : ∑ e ∈ (levels Q).filter (fun e => ¬ e ≤ E₀), aNat W Q e * Se e ≤ ν * CF ^ 2 := by
    have hB : ∀ e ∈ (levels Q).filter (fun e => ¬ e ≤ E₀),
        Se e ≤ Nat.totient e * (CF * Q ^ (-(1 : ℝ))) ^ 2 := by
      intro e he
      obtain ⟨he1, he2⟩ := Finset.mem_filter.mp he
      have heQ : (e : ℝ) ≤ Q :=
        (Nat.cast_le.mpr (Finset.mem_Icc.mp he1).2).trans (Nat.floor_le hQ0.le)
      have hRe : ∀ j ∈ P.blocks Q T, P.Rj Q T j < e := fun j hj =>
        lt_of_le_of_lt (Rj_le_E0H P hQT1 hj) (not_le.mp he2)
      calc Se e ≤ ∑ c ∈ reduced e, (CF * Q ^ (-(1 : ℝ))) ^ 2 := by
            refine Finset.sum_le_sum fun c hc => ?_
            exact pow_le_pow_left₀ (norm_nonneg _) (hF Q hQF T hT δ hδ1 hδT u e c heQ hRe hc) 2
        _ = Nat.totient e * (CF * Q ^ (-(1 : ℝ))) ^ 2 := by
            rw [Finset.sum_const, card_reduced, nsmul_eq_mul]
    calc ∑ e ∈ (levels Q).filter (fun e => ¬ e ≤ E₀), aNat W Q e * Se e
        ≤ ∑ e ∈ (levels Q).filter (fun e => ¬ e ≤ E₀),
            ν * (Nat.totient e * (CF * Q ^ (-(1 : ℝ))) ^ 2) :=
          Finset.sum_le_sum fun e he => mul_le_mul (haN e (Finset.mem_filter.mp he).1).2
            (hB e he) (hSe0 e) hν0
      _ ≤ ∑ e ∈ levels Q, ν * (Nat.totient e * (CF * Q ^ (-(1 : ℝ))) ^ 2) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun e _ _ => by positivity)
      _ = ν * (CF * Q ^ (-(1 : ℝ))) ^ 2 * ∑ e ∈ levels Q, (Nat.totient e : ℝ) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun e _ => by ring
      _ ≤ ν * (CF * Q ^ (-(1 : ℝ))) ^ 2 * Q ^ 2 :=
          mul_le_mul_of_nonneg_left (sum_totient_levels_le hQ1.le) (by positivity)
      _ = ν * CF ^ 2 := by
          rw [Real.rpow_neg_one, mul_pow, inv_pow]
          field_simp
  linarith

end TS

end Families.Hybrid
