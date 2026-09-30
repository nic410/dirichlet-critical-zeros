/-
Steps (6)–(7) of `lem:B2` — the density comparison.

`density_le`: on the support of `F_j`, `log y − G(R_j) ≤ min(log⁺ y, ℓ(1+2ε₃) + 2 log T + 2)`, using
`G(R) ≥ log(R+1)` (`log_le_Gsum`; an *upper* bound for the density `log y − G(R_j)` only).
`sum_M_le`: `∑_j ∫ F_j(y)(log y − G(R_j)) dy ≤ (1 + (2 log T + 2)/ℓ) ∫ ℓ F_b(s/ℓ) h(s) ds`
(substitution `y = e^s`, `∑ ψ_j ≤ 1`, `Υ ≤ 1`).
-/
import Families.Phase3.C.B2Convex

noncomputable section

open scoped ContDiff Nat ArithmeticFunction.Moebius
open Set ArithmeticFunction MeasureTheory

namespace Families.Phase3.C

open Families

variable (P : PrimeSetup)

/-- The pointwise density bound (step (6)). -/
lemma density_le {Q T : ℝ} (hQ : 1 < Q) (hT : 1 ≤ T) (hY2 : 2 * P.Y Q ≤ Q ^ 2) {j : ℕ}
    {y : ℝ} (hy1 : 1 ≤ y) (hyN : (2 : ℝ) ^ j / 2 ≤ y ∧ y ≤ 2 * 2 ^ j) (hyY : y ≤ P.Y Q) :
    Real.log y - Gsum (P.Rj Q T j) ≤ Real.log Q * (1 + 2 * P.ε₃) + (2 * Real.log T + 2) := by
  set N : ℝ := 2 ^ j with hN
  set ℓ := Real.log Q with hℓ
  have hN1 : 1 ≤ N := one_le_pow₀ (by norm_num)
  have hN0 : 0 < N := by linarith
  have hQ0 : 0 < Q := by linarith
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg hQ.le
  have hlT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hε := P.ε₃_pos
  have hε' := P.ε₃_lt
  obtain ⟨hl1, hl2⟩ := log_two_bounds
  have hlogy : Real.log y ≤ Real.log 2 + Real.log N := by
    rw [← Real.log_mul (by norm_num) hN0.ne']
    exact Real.log_le_log (by linarith) hyN.2
  have hQT : Real.log (Q * T) = ℓ + Real.log T := Real.log_mul hQ0.ne' (by linarith)
  have hNε : Real.log (N ^ (1 - P.ε₃)) = (1 - P.ε₃) * Real.log N := Real.log_rpow hN0 _
  set x : ℝ := N ^ (1 - P.ε₃) / (Q * T) with hx
  have hxpos : 0 < x := by positivity
  rcases Nat.eq_zero_or_pos (P.Rj Q T j) with h0 | hpos
  · -- `R_j = 0`: `N^{1−ε₃} < QT`
    rw [h0, Gsum_zero, sub_zero]
    have hx1 : x < 1 := by
      have : ⌊x⌋₊ = 0 := h0
      exact Nat.floor_eq_zero.mp this
    have h1 : (1 - P.ε₃) * Real.log N < ℓ + Real.log T := by
      rw [← hNε, ← hQT]
      apply Real.log_lt_log (by positivity)
      rw [hx, div_lt_one (by positivity)] at hx1; exact hx1
    have h2 : Real.log N < (1 + 2 * P.ε₃) * (ℓ + Real.log T) := by
      have hpos' : 0 < 1 - P.ε₃ := by linarith
      have h3 : Real.log N < (ℓ + Real.log T) / (1 - P.ε₃) := by
        rw [lt_div_iff₀ hpos']; linarith
      have h4 : (ℓ + Real.log T) / (1 - P.ε₃) ≤ (1 + 2 * P.ε₃) * (ℓ + Real.log T) := by
        rw [div_le_iff₀ hpos']
        have h0' : 0 ≤ ℓ + Real.log T := by linarith
        nlinarith [mul_nonneg (mul_nonneg hε.le (by linarith : (0 : ℝ) ≤ 1 - 2 * P.ε₃)) h0']
      linarith
    nlinarith
  · -- `R_j ≥ 1`: `G(R) ≥ log R ≥ log(x/2)`
    have hx1 : 1 ≤ x := by
      have : 1 ≤ ⌊x⌋₊ := hpos
      exact_mod_cast (Nat.one_le_floor_iff x).mp this
    have hR : x / 2 ≤ (P.Rj Q T j : ℝ) := by
      have hlt := Nat.lt_floor_add_one x
      have : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hpos
      show x / 2 ≤ (⌊x⌋₊ : ℝ)
      linarith
    have hG : Real.log (x / 2) ≤ Gsum (P.Rj Q T j) := by
      refine le_trans ?_ (log_le_Gsum _)
      exact Real.log_le_log (by positivity) (by linarith)
    have hlogx : Real.log (x / 2) = (1 - P.ε₃) * Real.log N - (ℓ + Real.log T) - Real.log 2 := by
      rw [Real.log_div (by positivity) (by norm_num), hx, Real.log_div (by positivity)
        (by positivity), hNε, hQT]
    have hNQ : Real.log N ≤ 2 * ℓ := by
      have : N ≤ Q ^ 2 := by linarith [hyN.1]
      calc Real.log N ≤ Real.log (Q ^ 2) := Real.log_le_log hN0 this
        _ = 2 * ℓ := by rw [Real.log_pow, hℓ]; norm_num
    rw [hlogx] at hG
    nlinarith

/-- `ℓ F_b(log y/ℓ) = min(log⁺ y, ℓ(1+2ε₃))`. -/
lemma ell_Fb {ℓ ε t : ℝ} (hℓ : 0 < ℓ) : ℓ * Fb ε (t / ℓ) = min (max t 0) (ℓ * (1 + 2 * ε)) := by
  unfold Fb
  rw [mul_min_of_nonneg _ _ hℓ.le, mul_max_of_nonneg _ _ hℓ.le, mul_div_cancel₀ _ hℓ.ne', mul_zero]

/-- The density function `Φ(y) = (1 + c/ℓ) ℓ F_b(log y/ℓ)`. -/
def Phi (ℓ c ε : ℝ) (y : ℝ) : ℝ := (1 + c / ℓ) * (ℓ * Fb ε (Real.log y / ℓ))

lemma Fb_nonneg (ε α : ℝ) (hε : 0 ≤ ε) : 0 ≤ Fb ε α := by
  unfold Fb; exact le_min (le_max_right _ _) (by linarith)

lemma Fb_le (ε α : ℝ) : Fb ε α ≤ 1 + 2 * ε := min_le_right _ _

lemma Phi_nonneg {ℓ c ε : ℝ} (hℓ : 0 < ℓ) (hc : 0 ≤ c) (hε : 0 ≤ ε) (y : ℝ) : 0 ≤ Phi ℓ c ε y := by
  unfold Phi
  have := Fb_nonneg ε (Real.log y / ℓ) hε
  positivity

lemma Phi_le {ℓ c ε : ℝ} (hℓ : 0 < ℓ) (hc : 0 ≤ c) (y : ℝ) :
    Phi ℓ c ε y ≤ (1 + c / ℓ) * (ℓ * (1 + 2 * ε)) := by
  unfold Phi
  have := Fb_le ε (Real.log y / ℓ)
  gcongr

lemma measurable_Phi (ℓ c ε : ℝ) : Measurable (Phi ℓ c ε) := by
  unfold Phi Fb
  fun_prop

/-- `log y − G(R_j) ≤ Φ(y)` on the support of `F_j`, when `c/ℓ` is the relative slack. -/
lemma density_le_Phi {Q T : ℝ} (hQ : 1 < Q) (hT : 1 ≤ T) (hY2 : 2 * P.Y Q ≤ Q ^ 2) {j : ℕ}
    {y : ℝ} (hyN : (2 : ℝ) ^ j / 2 ≤ y ∧ y ≤ 2 * 2 ^ j) (hyY : y ≤ P.Y Q) :
    Real.log y - Gsum (P.Rj Q T j) ≤
      Phi (Real.log Q) (2 * Real.log T + 2) P.ε₃ y := by
  set ℓ := Real.log Q with hℓ
  have hℓ0 : 0 < ℓ := Real.log_pos hQ
  have hlT : 0 ≤ Real.log T := Real.log_nonneg hT
  set c := 2 * Real.log T + 2 with hc
  have hc0 : 0 ≤ c := by positivity
  have hG0 := Gsum_nonneg (P.Rj Q T j)
  have hPhi0 := Phi_nonneg hℓ0 hc0 P.ε₃_pos.le y
  rcases lt_or_ge y 1 with hy1 | hy1
  · -- `log y < 0 ≤ Φ`
    have hlog : Real.log y ≤ 0 := by
      have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hyN.1
      exact (Real.log_neg hy0 hy1).le
    linarith
  · have h1 := density_le P hQ hT hY2 hy1 hyN hyY
    have hlog0 : 0 ≤ Real.log y := Real.log_nonneg hy1
    unfold Phi
    rw [ell_Fb hℓ0, max_eq_left hlog0]
    set B := ℓ * (1 + 2 * P.ε₃) with hB
    have hBℓ : ℓ ≤ B := by rw [hB]; nlinarith [P.ε₃_pos]
    have hmin : min (Real.log y) (B + c) ≤ (1 + c / ℓ) * min (Real.log y) B := by
      rcases le_total (Real.log y) B with hle | hle
      · rw [min_eq_left hle]
        calc min (Real.log y) (B + c) ≤ Real.log y := min_le_left _ _
          _ ≤ (1 + c / ℓ) * Real.log y := by
              have : 0 ≤ c / ℓ * Real.log y := by positivity
              linarith
      · rw [min_eq_right hle]
        calc min (Real.log y) (B + c) ≤ B + c := min_le_right _ _
          _ ≤ B + c / ℓ * B := by
              have : c ≤ c / ℓ * B := by
                rw [div_mul_eq_mul_div, le_div_iff₀ hℓ0]; nlinarith
              linarith
          _ = (1 + c / ℓ) * B := by ring
    have h2 : Real.log y - Gsum (P.Rj Q T j) ≤ min (Real.log y) (B + c) := by
      refine le_min (by linarith) ?_
      rw [hB, hc]; linarith
    exact h2.trans hmin

end Families.Phase3.C
