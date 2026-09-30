/-
**Step 4(b) of `prop:TIsharp`** — the `T^♮`-form of the subtracted part `x♯^s(u)`
(proof of Proposition 6.24).

`‖x♯^s‖²_{T^♮} = ∑_{e ≤ Q} ν(e) ∑*_c |S_{x♯^s}(c/e)|²`, split at `E₀ = ⌊2Y/Q⌋ ≥ R_max`:
* levels `e ≤ E₀`: `ν(e) ≤ 6‖w̃‖_∞η^{−2}` (`aNat_le`) and the additive large sieve on `[1, Y]`,
  `≤ ν_max C₀ (⌊Y⌋ + E₀²) ‖x♯^s‖²`;
* levels `e > E₀`: `|S_{x♯^s}(c/e)| ≤ C_F Q^{−1}` (`farey_sharp_le`), so these contribute
  `≤ ν_max ∑_{e ≤ Q} φ(e) C_F² Q^{−2} ≤ ν_max C_F²`.
-/
import Families.Phase3.C.TIsharpFarey
import Families.Phase3.C.TIsharpLocal

noncomputable section

open scoped BigOperators ContDiff
open Set MeasureTheory Filter Topology

namespace Families.Phase3.C

open Families

variable (P : PrimeSetup)

/-- `R_j ≤ ⌊2Y/Q⌋` for every block (`T ≥ 1`). -/
lemma Rj_le_E0 {Q T : ℝ} (hQ : 1 < Q) (hT : 1 ≤ T) {j : ℕ} (hj : j ∈ P.blocks Q) :
    P.Rj Q T j ≤ ⌊2 * P.Y Q / Q⌋₊ := by
  have hQ0 : 0 < Q := by linarith
  have hN1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hQT : Q ≤ Q * T := by nlinarith
  have h1 : (P.Rj Q T j : ℝ) ≤ ((2 : ℝ) ^ j) ^ (1 - P.ε₃) / (Q * T) := by
    unfold PrimeSetup.Rj; exact Nat.floor_le (by positivity)
  have h2 : ((2 : ℝ) ^ j) ^ (1 - P.ε₃) ≤ (2 : ℝ) ^ j := by
    have := Real.rpow_le_rpow_of_exponent_le hN1 (show 1 - P.ε₃ ≤ 1 by linarith [P.ε₃_pos])
    simpa using this
  have h3 : (2 : ℝ) ^ j ≤ 2 * P.Y Q := by
    unfold PrimeSetup.blocks at hj
    have hjl : j ≤ Nat.log 2 ⌊P.Y Q⌋₊ + 1 := by
      have := Finset.mem_range.mp hj; omega
    have hY1 := one_le_Y P hQ
    have hN : ⌊P.Y Q⌋₊ ≠ 0 := by
      have : 1 ≤ ⌊P.Y Q⌋₊ := Nat.le_floor (by exact_mod_cast hY1)
      omega
    have := Nat.pow_log_le_self 2 hN
    calc (2 : ℝ) ^ j ≤ 2 ^ (Nat.log 2 ⌊P.Y Q⌋₊ + 1) := pow_le_pow_right₀ (by norm_num) hjl
      _ = 2 * 2 ^ (Nat.log 2 ⌊P.Y Q⌋₊) := by ring
      _ ≤ 2 * P.Y Q := by
          gcongr
          calc (2 : ℝ) ^ (Nat.log 2 ⌊P.Y Q⌋₊) ≤ (⌊P.Y Q⌋₊ : ℝ) := by exact_mod_cast this
            _ ≤ P.Y Q := Nat.floor_le (by linarith)
  apply Nat.le_floor
  calc (P.Rj Q T j : ℝ) ≤ ((2 : ℝ) ^ j) ^ (1 - P.ε₃) / (Q * T) := h1
    _ ≤ (2 : ℝ) ^ j / Q := by
        rw [div_le_div_iff₀ (by positivity) hQ0]
        calc ((2 : ℝ) ^ j) ^ (1 - P.ε₃) * Q ≤ (2 : ℝ) ^ j * (Q * T) :=
              mul_le_mul h2 hQT hQ0.le (by positivity)
          _ = _ := by ring
    _ ≤ 2 * P.Y Q / Q := div_le_div_of_nonneg_right h3 hQ0.le

lemma sum_totient_levels_le {Q : ℝ} (hQ : 1 ≤ Q) :
    ∑ e ∈ levels Q, (Nat.totient e : ℝ) ≤ Q ^ 2 := by
  have hfl : (⌊Q⌋₊ : ℝ) ≤ Q := Nat.floor_le (by linarith)
  calc ∑ e ∈ levels Q, (Nat.totient e : ℝ) ≤ ∑ e ∈ levels Q, Q := by
        refine Finset.sum_le_sum fun e he => ?_
        have he2 := (Finset.mem_Icc.mp he).2
        calc (Nat.totient e : ℝ) ≤ e := by exact_mod_cast Nat.totient_le e
          _ ≤ ⌊Q⌋₊ := by exact_mod_cast he2
          _ ≤ Q := hfl
    _ = ⌊Q⌋₊ * Q := by
        rw [Finset.sum_const, levels, Nat.card_Icc, nsmul_eq_mul]; simp
    _ ≤ Q * Q := mul_le_mul_of_nonneg_right hfl (by linarith)
    _ = Q ^ 2 := by ring

/-- **Step 4(b)**: `‖x♯^s(u)‖²_{T^♮} ≤ ν_max C₀ (⌊Y⌋ + E₀²) ‖x♯^s(u)‖² + ν_max C_F²`. -/
theorem levelForm_xsSharp_le {C₀ : ℝ} (hadd : MVLargeSieveAdd C₀) (W : Weight) :
    ∃ CF Q₀ : ℝ, 0 ≤ CF ∧ ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ P.heights Q, ∀ u : ℝ,
      levelForm (levels Q) (aNat W Q) (P.rangeZ Q) (xs P Q T (P.aSharp Q T) u) ≤
        6 * W.wtmax * W.η⁻¹ ^ 2 * max C₀ 0 * (⌊P.Y Q⌋₊ + (⌊2 * P.Y Q / Q⌋₊ : ℝ) ^ 2) *
            normSq (P.rangeZ Q) (xs P Q T (P.aSharp Q T) u) +
          6 * W.wtmax * W.η⁻¹ ^ 2 * CF ^ 2 := by
  obtain ⟨CF, QF, hCF0, hF⟩ := farey_sharp_le P 1
  refine ⟨CF, max QF (Real.exp 1), hCF0, ?_⟩
  intro Q hQ T hT u
  have hQF : QF ≤ Q := le_of_max_le_left hQ
  have hQe : Real.exp 1 ≤ Q := le_of_max_le_right hQ
  have hQ1 : 1 < Q :=
    lt_of_lt_of_le (by have := Real.add_one_lt_exp (x := 1) one_ne_zero; linarith) hQe
  have hQ0 : 0 < Q := by linarith
  have hT1 := one_le_T P hQe hT
  set ν : ℝ := 6 * W.wtmax * W.η⁻¹ ^ 2 with hν
  have hν0 : 0 ≤ ν := by have := wtmax_nonneg W; positivity
  set E₀ : ℕ := ⌊2 * P.Y Q / Q⌋₊ with hE₀
  set x := xs P Q T (P.aSharp Q T) u with hx
  set Se : ℕ → ℝ := fun e => ∑ c ∈ reduced e, ‖S (P.rangeZ Q) x ((c : ℝ) / e)‖ ^ 2 with hSe
  have hSe0 : ∀ e, 0 ≤ Se e := fun e => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have haN : ∀ e ∈ levels Q, 0 ≤ aNat W Q e ∧ aNat W Q e ≤ ν := fun e he =>
    ⟨aNat_nonneg W Q hQ0 e he, aNat_le W hQ0 (Finset.mem_Icc.mp he).1⟩
  have hLF : levelForm (levels Q) (aNat W Q) (P.rangeZ Q) x =
      ∑ e ∈ levels Q, aNat W Q e * Se e := rfl
  rw [hLF, ← Finset.sum_filter_add_sum_filter_not (levels Q) (fun e => e ≤ E₀)]
  -- low levels: the additive large sieve
  have hlow : ∑ e ∈ (levels Q).filter (fun e => e ≤ E₀), aNat W Q e * Se e ≤
      ν * max C₀ 0 * (⌊P.Y Q⌋₊ + (E₀ : ℝ) ^ 2) * normSq (P.rangeZ Q) x := by
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
      _ ≤ ν * (max C₀ 0 * (⌊P.Y Q⌋₊ + (E₀ : ℝ) ^ 2) * normSq (P.rangeZ Q) x) := by
          apply mul_le_mul_of_nonneg_left _ hν0
          have h := hadd E₀ 1 ⌊P.Y Q⌋₊ x
          simp only [hSe]
          rw [rangeZ_eq_intervalZ]
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
      have hRe : ∀ j ∈ P.blocks Q, P.Rj Q T j < e := fun j hj =>
        lt_of_le_of_lt (Rj_le_E0 P hQ1 hT1 hj) (not_le.mp he2)
      calc Se e ≤ ∑ c ∈ reduced e, (CF * Q ^ (-(1 : ℝ))) ^ 2 := by
            refine Finset.sum_le_sum fun c hc => ?_
            exact pow_le_pow_left₀ (norm_nonneg _) (hF Q hQF T hT u e c heQ hRe hc) 2
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

end Families.Phase3.C
