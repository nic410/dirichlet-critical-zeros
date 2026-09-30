/-
# Montgomery 1969 density: the full statement from a `t`-aspect input

`Families.Montgomery69_Density` is uniform in all heights `T' ≥ 2`. The q-aspect range `T' ≤ Q` is
proved (`Montgomery69_Density_upTo_proof`). The range `T' > Q` follows from a **per-character**
zero-density estimate in the `t`-aspect, `TAspectDensity` (for `T ≥ q`:
`N(1/2+δ, T, χ) ≤ C T^{1−c₁δ} (log T)^B`), a classical consequence of the approximate functional
equation (Selberg; Montgomery, *Topics*, Ch. 12), which is **not** proved here.

`Montgomery69_Density_of_tAspect : TAspectDensity → Montgomery69_Density`.
-/
import Families.Hyp.Montgomery.Main

noncomputable section

open scoped BigOperators
open Real Finset

namespace Families.Hyp.Montgomery

open Families

/-- Sanity check: `Montgomery69_Density_upTo A` is `Families.Montgomery69_Density` restricted to
`T' ≤ Q^A` (so it is implied by the full statement). -/
theorem Montgomery69_Density_upTo_of_full (A : ℝ) (h : Montgomery69_Density) :
    Montgomery69_Density_upTo A := by
  obtain ⟨C, c, C₁, hc, hb⟩ := h
  exact ⟨C, c, C₁, hc, fun Q hQ T hT _ δ hδ0 hδ1 => hb Q hQ T hT δ hδ0 hδ1⟩

/-- **Per-character zero density in the `t`-aspect** (`T ≥ q`); not proved here. -/
def TAspectDensity : Prop :=
  ∃ C c₁ B : ℝ, 0 < c₁ ∧ 0 ≤ B ∧ ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), 1 ≤ q →
    χ.IsPrimitive → ∀ T : ℝ, 2 ≤ T → (q : ℝ) ≤ T → ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / 2 →
      (Ndens χ (1 / 2 + δ) T : ℝ) ≤ C * T ^ (1 - c₁ * δ) * Real.log T ^ B

/-- `ℓ^a ≤ 2^{b−a} ℓ^b` for `ℓ ≥ 1/2` and `a ≤ b`. -/
lemma rpow_le_two_rpow_mul {ℓ a b : ℝ} (hℓ : 1 / 2 ≤ ℓ) (hab : a ≤ b) :
    ℓ ^ a ≤ 2 ^ (b - a) * ℓ ^ b := by
  have hℓ0 : 0 < ℓ := by linarith
  have h1 : (1 : ℝ) ≤ 2 * ℓ := by linarith
  have key : (2 * ℓ) ^ a ≤ (2 * ℓ) ^ b := Real.rpow_le_rpow_of_exponent_le h1 hab
  rw [Real.mul_rpow (by norm_num) hℓ0.le, Real.mul_rpow (by norm_num) hℓ0.le] at key
  have h2a : (0 : ℝ) < 2 ^ a := by positivity
  have e : (2 : ℝ) ^ (b - a) = 2 ^ b / 2 ^ a := Real.rpow_sub (by norm_num) b a
  rw [e, div_mul_eq_mul_div, le_div_iff₀ h2a]
  linarith

/-- **`Families.Montgomery69_Density` from the `t`-aspect input.** -/
theorem Montgomery69_Density_of_tAspect (h : TAspectDensity) : Montgomery69_Density := by
  obtain ⟨C₀, c₀, C₁₀, hc₀, hq⟩ := Montgomery69_Density_upTo_proof 1 one_pos
  obtain ⟨C, c₁, B, hc₁, hB, ht⟩ := h
  set c : ℝ := min c₀ (c₁ / 3) with hc
  have hc0 : 0 < c := lt_min hc₀ (by linarith)
  set D : ℝ := max C₁₀ B with hD
  refine ⟨|C₀| * 2 ^ (D - C₁₀) + |C| * 2 ^ (D - B), c, D, hc0, ?_⟩
  intro Q hQ T hT δ hδ0 hδ1
  have hQ0 : 0 < Q := by linarith
  have hT0 : 0 < T := by linarith
  have hQT : 1 ≤ Q ^ 2 * T := by nlinarith
  set ℓ := Real.log (Q * T) with hℓ
  have hℓ2 : 1 / 2 ≤ ℓ := half_le_log_QT hQ hT
  have hℓ0 : 0 < ℓ := by linarith
  have hP0 : 0 ≤ (Q ^ 2 * T) ^ (1 - c * δ) := by positivity
  have hlogD : 0 ≤ ℓ ^ D := by positivity
  have htwo1 : (0 : ℝ) ≤ 2 ^ (D - C₁₀) := by positivity
  have htwo2 : (0 : ℝ) ≤ 2 ^ (D - B) := by positivity
  have hLHS0 : 0 ≤ ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ ∈ primChars q, (Ndens χ (1 / 2 + δ) T : ℝ) :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hX : 0 ≤ |C₀| * 2 ^ (D - C₁₀) * ((Q ^ 2 * T) ^ (1 - c * δ) * ℓ ^ D) := by positivity
  have hY : 0 ≤ |C| * 2 ^ (D - B) * ((Q ^ 2 * T) ^ (1 - c * δ) * ℓ ^ D) := by positivity
  suffices hs : ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ ∈ primChars q, (Ndens χ (1 / 2 + δ) T : ℝ) ≤
      |C₀| * 2 ^ (D - C₁₀) * ((Q ^ 2 * T) ^ (1 - c * δ) * ℓ ^ D) ∨
      ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ ∈ primChars q, (Ndens χ (1 / 2 + δ) T : ℝ) ≤
      |C| * 2 ^ (D - B) * ((Q ^ 2 * T) ^ (1 - c * δ) * ℓ ^ D) by
    rcases hs with hs | hs <;> nlinarith
  rcases le_or_gt T Q with hTQ | hTQ
  · -- the q-aspect
    left
    have hb := hq Q hQ T hT (by rwa [Real.rpow_one]) δ hδ0 hδ1
    have hcδ : c * δ ≤ c₀ * δ := mul_le_mul_of_nonneg_right (min_le_left _ _) hδ0
    have hP : (Q ^ 2 * T) ^ (1 - c₀ * δ) ≤ (Q ^ 2 * T) ^ (1 - c * δ) :=
      Real.rpow_le_rpow_of_exponent_le hQT (by linarith)
    have hl : ℓ ^ C₁₀ ≤ 2 ^ (D - C₁₀) * ℓ ^ D := rpow_le_two_rpow_mul hℓ2 (le_max_left _ _)
    have hP1 : 0 ≤ (Q ^ 2 * T) ^ (1 - c₀ * δ) := by positivity
    have hl1 : 0 ≤ ℓ ^ C₁₀ := by positivity
    calc _ ≤ C₀ * (Q ^ 2 * T) ^ (1 - c₀ * δ) * ℓ ^ C₁₀ := hb
      _ ≤ |C₀| * (Q ^ 2 * T) ^ (1 - c₀ * δ) * ℓ ^ C₁₀ := by
          gcongr; exact le_abs_self _
      _ ≤ |C₀| * (Q ^ 2 * T) ^ (1 - c * δ) * (2 ^ (D - C₁₀) * ℓ ^ D) := by
          gcongr
      _ = _ := by ring
  · -- the t-aspect
    right
    have hTq : ∀ q ∈ Finset.Icc 1 ⌊Q⌋₊, (q : ℝ) ≤ T := fun q hq =>
      ((Nat.cast_le.mpr (Finset.mem_Icc.mp hq).2).trans (Nat.floor_le hQ0.le)).trans hTQ.le
    have hlogT : Real.log T ^ B ≤ 2 ^ (D - B) * ℓ ^ D := by
      have h1 : Real.log T ≤ ℓ := Real.log_le_log hT0 (le_mul_of_one_le_left hT0.le hQ)
      have h0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
      calc Real.log T ^ B ≤ ℓ ^ B := Real.rpow_le_rpow h0 h1 hB
        _ ≤ 2 ^ (D - B) * ℓ ^ D := rpow_le_two_rpow_mul hℓ2 (le_max_right _ _)
    have hTexp : T ^ (1 - c₁ * δ) ≤ T * (Q ^ 2 * T) ^ (-(c * δ)) := by
      have hQ2 : Q ^ 2 * T ≤ T ^ (3 : ℝ) := by
        have : Q ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hQ0.le hTQ.le 2
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; nlinarith
      have hcδ : 3 * (c * δ) ≤ c₁ * δ := by
        have : c ≤ c₁ / 3 := min_le_right _ _
        nlinarith
      rw [sub_eq_add_neg, Real.rpow_add hT0, Real.rpow_one]
      refine mul_le_mul_of_nonneg_left ?_ hT0.le
      calc T ^ (-(c₁ * δ)) ≤ T ^ (3 * -(c * δ)) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ = (T ^ (3 : ℝ)) ^ (-(c * δ)) := by rw [Real.rpow_mul hT0.le]
        _ ≤ (Q ^ 2 * T) ^ (-(c * δ)) :=
            Real.rpow_le_rpow_of_nonpos (by positivity) hQ2
              (by have := mul_nonneg hc0.le hδ0; linarith)
    have hsplit : (Q ^ 2 * T) ^ (1 - c * δ) = Q ^ 2 * T * (Q ^ 2 * T) ^ (-(c * δ)) := by
      rw [sub_eq_add_neg, Real.rpow_add (by positivity), Real.rpow_one]
    have hper : ∀ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∀ χ ∈ primChars q, (Ndens χ (1 / 2 + δ) T : ℝ) ≤
        |C| * (T * (Q ^ 2 * T) ^ (-(c * δ))) * (2 ^ (D - B) * ℓ ^ D) := by
      intro q hq χ hχ
      have hb := ht q χ (Finset.mem_Icc.mp hq).1 (mem_primChars.mp hχ) T hT (hTq q hq) δ hδ0 hδ1
      have h1 : 0 ≤ T ^ (1 - c₁ * δ) := by positivity
      have h2 : 0 ≤ Real.log T ^ B := by
        have : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
        positivity
      calc _ ≤ C * T ^ (1 - c₁ * δ) * Real.log T ^ B := hb
        _ ≤ |C| * T ^ (1 - c₁ * δ) * Real.log T ^ B := by gcongr; exact le_abs_self _
        _ ≤ |C| * (T * (Q ^ 2 * T) ^ (-(c * δ))) * (2 ^ (D - B) * ℓ ^ D) := by gcongr
    have hZ : 0 ≤ |C| * (T * (Q ^ 2 * T) ^ (-(c * δ))) * (2 ^ (D - B) * ℓ ^ D) := by positivity
    calc _ ≤ ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ((primChars q).card : ℝ) *
          (|C| * (T * (Q ^ 2 * T) ^ (-(c * δ))) * (2 ^ (D - B) * ℓ ^ D)) := by
          refine Finset.sum_le_sum fun q hq => ?_
          rw [← nsmul_eq_mul, ← Finset.sum_const]
          exact Finset.sum_le_sum fun χ hχ => hper q hq χ hχ
      _ = (∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ((primChars q).card : ℝ)) *
          (|C| * (T * (Q ^ 2 * T) ^ (-(c * δ))) * (2 ^ (D - B) * ℓ ^ D)) := by rw [Finset.sum_mul]
      _ ≤ Q ^ 2 * (|C| * (T * (Q ^ 2 * T) ^ (-(c * δ))) * (2 ^ (D - B) * ℓ ^ D)) :=
          mul_le_mul_of_nonneg_right (sum_card_primChars_le_one hQ) hZ
      _ = |C| * 2 ^ (D - B) * ((Q ^ 2 * T) ^ (1 - c * δ) * ℓ ^ D) := by rw [hsplit]; ring

end Families.Hyp.Montgomery
