/-
# Package F: `lem:B2H` (flattened norm at height `T = Q^κ`), Lemma 9.12

Through the bridge, `b = a − a♯` is the families flattened vector at `Q' = QT` with `T' = 1`
(`R_j = ⌊N_j^{1−ε₃}/(QT)⌋`, `bVec_eq`), and `ℓ_* = log(QT) = ell (QT)`. The families proof
(`Phase3.C.lemB2_proof_fixed`) only uses `T ≥ 1` (through `block_estimate`, `small_block_le`,
`sum_M_le`), never `T ∈ heights`, so it runs verbatim at `(Q', T') = (QT, 1)`; the slack
`(2 log T' + 2)/log Q'` becomes `2/ℓ_*`. The prime number theorem enters through
`Families.Hyp.PNT_dlVP_proof` (a theorem of the families package), so no hypothesis is needed.
(S3) — `R_j ≤ N_j^{1/2−ε₃}` — is automatic: `N_j ≤ Y ≤ (QT)²` (`two_Y_le` at `Q'`).
-/
import FamiliesH.F.Bridge
import Families.Phase3.C.B2
import Families.Hyp.PNT

noncomputable section

open scoped ContDiff Nat ArithmeticFunction.Moebius
open Set ArithmeticFunction MeasureTheory

namespace Families.Hybrid

open Families Families.Phase3.C

namespace F

/-- **`lem:B2H`** (flattened norm at height `T = Q^κ`), proved (PNT from `Families.Hyp`). -/
theorem lemB2H_proof : lemB2H_Statement := by
  intro P Cs δ hδ
  set P' : PrimeSetup := P.toPS with hP'
  obtain ⟨C₀, hC₀⟩ := Families.Hyp.PNT_dlVP_proof
  obtain ⟨Cb, hCb0, hCb⟩ := block_estimate P' hC₀ Cs
  obtain ⟨CF, hCF0, hCF⟩ := Fh_deriv_bound P' 1 le_rfl Cs
  refine ⟨4 * Cb + 3 * (96 * CF),
    max (max 5 (Real.exp 1)) (max (Real.exp (1 / P.lam))
      (max (2 ^ (1 / P.ε₁)) (Real.exp (2 / δ)))), ?_⟩
  intro Q hQ T hT h hmax hh hh0 hint hhmax hhd
  have hQ5 : 5 ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hQ
  have hQe : Real.exp 1 ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hQ
  have hQL : Real.exp (1 / P.lam) ≤ Q :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hQ
  have hQε : (2 : ℝ) ^ (1 / P.ε₁) ≤ Q :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hQ
  have hQδ : Real.exp (2 / δ) ≤ Q :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hQ
  have hT1 : 1 ≤ T := by
    have hl : 1 ≤ Real.log Q := by
      have := Real.log_le_log (Real.exp_pos _) hQe; rwa [Real.log_exp] at this
    exact le_trans (Real.one_le_rpow hl P.a0_pos.le) hT.1
  -- everything happens at `Q' = QT`
  set Q' : ℝ := Q * T with hQ'def
  have hQQ' : Q ≤ Q' := by rw [hQ'def]; nlinarith
  have hQ'5 : 5 ≤ Q' := le_trans hQ5 hQQ'
  have hQ'1 : 1 < Q' := by linarith
  have hQ'0 : 0 < Q' := by linarith
  have hL : 1 ≤ P'.L Q' := one_le_L P' (le_trans hQL hQQ')
  have hT1' : (1 : ℝ) ≤ 1 := le_rfl
  have hmax0 : 0 ≤ hmax := (hh0 0).trans (hhmax 0)
  have hℓ1 : 1 ≤ Real.log Q' := by
    have := Real.log_le_log (Real.exp_pos _) (le_trans hQe hQQ'); rwa [Real.log_exp] at this
  have hε₁ : P'.ε₁ = P.ε₁ := rfl
  have hQεpow : 2 ≤ Q' ^ P'.ε₁ := by
    rw [hε₁]
    have := Real.rpow_le_rpow (by positivity) (le_trans hQε hQQ') P.ε₁_pos.le
    rwa [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ P.ε₁_pos.ne', Real.rpow_one]
      at this
  have hY2 := two_Y_le P' hQ'1.le hQεpow
  have hslack : (2 * Real.log 1 + 2) / Real.log Q' ≤ δ := by
    rw [Real.log_one, mul_zero, zero_add, div_le_iff₀ (by linarith)]
    have h1 : 2 / δ ≤ Real.log Q' := by
      have := Real.log_le_log (Real.exp_pos _) (le_trans hQδ hQQ'); rwa [Real.log_exp] at this
    rw [div_le_iff₀ hδ] at h1
    linarith
  -- the hybrid objects are the families objects at `(Q', 1)`
  have hLHS : ∑ n ∈ P.range Q T, P.bVec Q T n ^ 2 * h (Real.log n) =
      ∑ n ∈ P'.range Q', P'.bVec Q' 1 n ^ 2 * h (Real.log n) := by
    rw [P.bVec_eq]; rfl
  have hℓs : ellS Q T = Real.log Q' := rfl
  have hε₃ : P'.ε₃ = P.ε₃ := rfl
  rw [hLHS, hℓs, ← hε₃]
  -- convexity
  have hconv : ∑ n ∈ P'.range Q', P'.bVec Q' 1 n ^ 2 * h (Real.log n) ≤
      ∑ j ∈ P'.blocks Q', ∑ n ∈ P'.range Q',
        Fh P' Q' h j n * (Λ n - PrimeSetup.LamR (P'.Rj Q' 1 j) n) ^ 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun n hn => bVec_sq_le P' hh0 hn
  -- per block
  set Mj : ℕ → ℝ := fun j => (∫ y, Gh P' Q' h j y) - Gsum (P'.Rj Q' 1 j) * ∫ y, Fh P' Q' h j y
  set Ej : ℕ → ℝ := fun j => Cb * hmax * (1 + Real.log Q') / ((j : ℝ) + 1) ^ 2 +
    (if j ≤ 2 then 96 * CF * hmax else 0)
  have hblock : ∀ j ∈ P'.blocks Q', ∑ n ∈ P'.range Q',
      Fh P' Q' h j n * (Λ n - PrimeSetup.LamR (P'.Rj Q' 1 j) n) ^ 2 ≤ Mj j + Ej j := by
    intro j hj
    have hE0 : 0 ≤ Cb * hmax * (1 + Real.log Q') / ((j : ℝ) + 1) ^ 2 := by positivity
    by_cases hj3 : 3 ≤ j
    · have := hCb Q' 1 hQ'1 hL hT1' h hmax hh hh0 hhmax hhd j hj3
        (two_pow_le_sq_of_block P' (by linarith) hY2 hj)
      have h2 : ¬ j ≤ 2 := by omega
      simp only [Mj, Ej, if_neg h2, add_zero]
      linarith [(abs_le.mp this).2]
    · have h2 : j ≤ 2 := by omega
      have hFj : ∀ y, |Fh P' Q' h j y| ≤ CF * hmax := by
        intro y
        have := hCF Q' hL h hmax hh hh0 hhmax hhd j 0 (Nat.zero_le _) y
        simp only [pow_zero, mul_one, Real.norm_eq_abs, iteratedDeriv_zero] at this
        refine this.trans ?_
        rw [div_le_iff₀ (by positivity)]
        have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
        nlinarith [mul_nonneg hCF0 hmax0]
      have := small_block_le P' (by linarith) hT1' hh0 hCF0 hmax0 h2 hFj
      simp only [Mj, Ej, if_pos h2]
      linarith
  have hsumM := sum_M_le P' hQ'1 hT1' hY2 hh hh0 hint
  -- the errors
  have hsumE : ∑ j ∈ P'.blocks Q', Ej j ≤
      2 * Cb * hmax * (1 + Real.log Q') + 3 * (96 * CF * hmax) := by
    simp only [Ej, Finset.sum_add_distrib]
    have e1 : ∑ j ∈ P'.blocks Q', Cb * hmax * (1 + Real.log Q') / ((j : ℝ) + 1) ^ 2 ≤
        2 * Cb * hmax * (1 + Real.log Q') := by
      have : ∑ j ∈ P'.blocks Q', Cb * hmax * (1 + Real.log Q') / ((j : ℝ) + 1) ^ 2 =
          Cb * hmax * (1 + Real.log Q') * ∑ j ∈ P'.blocks Q', 1 / ((j : ℝ) + 1) ^ 2 := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring
      rw [this]
      have h2 := sum_inv_sq_le_two (Nat.log 2 ⌊P'.Y Q'⌋₊ + 2)
      unfold PrimeSetup.blocks
      have hX : 0 ≤ Cb * hmax * (1 + Real.log Q') := by positivity
      nlinarith
    have e2 : ∑ j ∈ P'.blocks Q', (if j ≤ 2 then 96 * CF * hmax else 0) ≤ 3 * (96 * CF * hmax) := by
      rw [← Finset.sum_filter]
      calc ∑ j ∈ (P'.blocks Q').filter (· ≤ 2), 96 * CF * hmax
          ≤ ∑ j ∈ Finset.range 3, 96 * CF * hmax :=
            Finset.sum_le_sum_of_subset_of_nonneg (fun j hj => by
              have := (Finset.mem_filter.mp hj).2
              exact Finset.mem_range.mpr (by omega)) (fun _ _ _ => by positivity)
        _ = 3 * (96 * CF * hmax) := by simp
    linarith
  -- assemble
  have hint0 : 0 ≤ ∫ s, Real.log Q' * Fb P'.ε₃ (s / Real.log Q') * h s :=
    integral_nonneg fun s => mul_nonneg (mul_nonneg (by linarith)
      (Fb_nonneg _ _ P'.ε₃_pos.le)) (hh0 s)
  calc ∑ n ∈ P'.range Q', P'.bVec Q' 1 n ^ 2 * h (Real.log n)
      ≤ ∑ j ∈ P'.blocks Q', (Mj j + Ej j) := hconv.trans (Finset.sum_le_sum hblock)
    _ = ∑ j ∈ P'.blocks Q', Mj j + ∑ j ∈ P'.blocks Q', Ej j := Finset.sum_add_distrib
    _ ≤ (1 + (2 * Real.log 1 + 2) / Real.log Q') *
          (∫ s, Real.log Q' * Fb P'.ε₃ (s / Real.log Q') * h s) +
        (2 * Cb * hmax * (1 + Real.log Q') + 3 * (96 * CF * hmax)) := add_le_add hsumM hsumE
    _ ≤ (1 + δ) * (∫ s, Real.log Q' * Fb P'.ε₃ (s / Real.log Q') * h s) +
          (4 * Cb + 3 * (96 * CF)) * hmax * Real.log Q' := by
        have h1 : (1 + (2 * Real.log 1 + 2) / Real.log Q') *
            (∫ s, Real.log Q' * Fb P'.ε₃ (s / Real.log Q') * h s) ≤
            (1 + δ) * (∫ s, Real.log Q' * Fb P'.ε₃ (s / Real.log Q') * h s) := by gcongr
        have h2 : 2 * Cb * hmax * (1 + Real.log Q') ≤ 4 * Cb * hmax * Real.log Q' := by
          have : 0 ≤ Cb * hmax := by positivity
          nlinarith
        have h3 : 3 * (96 * CF * hmax) ≤ 3 * (96 * CF) * hmax * Real.log Q' := by
          have : 0 ≤ CF * hmax := by positivity
          nlinarith
        nlinarith

end F

end Families.Hybrid
