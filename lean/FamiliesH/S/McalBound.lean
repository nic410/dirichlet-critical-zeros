/-
# Package S: the prime-side bound for `𝓜` at polynomial height

`mcalBound_ofH`: under the profile bound,
`𝓜 ≤ (aL)² (H|J|ℓ_*/2π) 𝒬_F(f_v) + o(H T L² ℓ_*)`, uniformly on the cell
(the families `McalBound_Statement` with `ℓ → ℓ_*`, family at `Q`, prime side at `QT`).

`𝓜 = M_{μμ} + 2(M_A + M_B) + ∑ω K₂(P,P)` (`Mcal2_split`, `Mmix2_split`), where
* `M_{μμ} ≤ H|J|bLℓ_*²/2π + o(HTL²ℓ_*)` (`Mmumu_boundH`);
* `M_B = o(HTL²ℓ_*)` (`MB_smallH`, bilinear large sieve);
* `∑ω K₂(P,P) = (1/2π²)(Re ∑a a Δ𝒦 + Re SSC) ≤ H|J|L²ℓ_* I_F/π + o(HTL²ℓ_*)` (`ratio_boundH`,
  `SSC_smallH`);
* **the `r`-part `M_A`** is bounded by positivity of `K₂` (`MA2_abs_le`):
  `2|M_A| ≤ s ∑ω K₂(r,r) + s⁻¹ ∑ω K₂(P,P)` with `∑ω K₂(r,r) ≤ R₀² H ∬Φ² ≪ H T L` and a fixed large
  `s`; this uses the upper bound for `∑ω K₂(P,P)` just obtained, so it needs the profile bound, which
  is a hypothesis of `prop:secondH` anyway. (The families proof bounded `M_A` with the pointwise
  large sieve, which loses `(1 + Y/Q²)^{1/2}`; that loss is not `o(1)` at polynomial height.)
-/
import FamiliesH.S.Mumu
import FamiliesH.S.SS
import FamiliesH.S.Ratio

noncomputable section

set_option linter.unusedSectionVars false

open scoped BigOperators ContDiff
open Finset MeasureTheory Filter Topology

namespace Families.Hybrid.S

open Families Families.Ported.Second

set_option maxHeartbeats 800000 in
/-- **The bound for `𝓜`** at polynomial height. -/
theorem mcalBound_ofH (hMV : MV_LargeSieve) (hStir : StirlingDigamma) (hWH : lemWH_Statement)
    (hB2 : lemB2H_Statement) (hMrat : eqBMratH_Statement) (P : HSetup) (W : Weight)
    (c : ℝ → ℝ) (hc : ContDiff ℝ ∞ c) (hc1 : ∀ α, 1 ≤ c α) (hprof : P.ProfileBoundH W c)
    (δ : ℝ) (hδ : 0 < δ) : ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ P.heights Q,
      Mcal2 P.toPS W Q (Q * T) T ≤
        (P.aInt * P.L Q T) ^ 2 * (W.H Q * P.Jlen T * ellS Q T / (2 * Real.pi)) *
          Qf (fun α => c α * min α (1 + 2 * P.ε₃))
            (fun x => P.vfun (x / P.lam) / (P.lam * P.aInt)) +
        δ * (W.H Q * T * P.L Q T ^ 2 * ellS Q T) := by
  have hpi := Real.pi_pos
  have hl := P.lam_pos
  have hb : 0 ≤ P.bInt := integral_nonneg fun s => sq_nonneg _
  have hIF := IF_nonneg (P := P.toPS) hc1
  set IFv := IF P.toPS c with hIFv
  set δ' : ℝ := δ / 7 with hδ'
  have hδ'0 : 0 < δ' := by positivity
  set s : ℝ := (IFv / Real.pi + 2 * δ' + 1) / δ' with hs
  have hs0 : 0 < s := by positivity
  have hsinv : s⁻¹ * (IFv / Real.pi + 2 * δ') ≤ δ' := by
    rw [hs, inv_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨R₀, hR₀, hRR⟩ := RR2_le hStir
  obtain ⟨CJ, hCJ, hJ2⟩ := J2_PhiSq_le P.toPS
  obtain ⟨Q₁, h₁⟩ := Mmumu_boundH hStir P W δ' hδ'0
  obtain ⟨Q₂, h₂⟩ := MB_smallH hMV hWH P W δ' hδ'0
  obtain ⟨Q₃, h₃⟩ := ratio_boundH hB2 hMrat hWH P W c hc hc1 hprof δ' hδ'0
  obtain ⟨Q₄, h₄⟩ := SSC_smallH hMV hWH P W δ' hδ'0
  set KR : ℝ := s * R₀ ^ 2 * (2 * Real.pi * P.bInt + CJ) with hKR
  have hKR0 : 0 ≤ KR := by positivity
  obtain ⟨QL, hQL⟩ := L_large P (KR / δ' + 1)
  refine ⟨max (max (max Q₁ Q₂) (max Q₃ Q₄)) (max QL (Real.exp 1)), fun Q hQ T hT => ?_⟩
  have hQa := le_trans (le_max_left _ _) hQ
  have hQb := le_trans (le_max_right _ _) hQ
  have hQ1' : Q₁ ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hQa
  have hQ2' : Q₂ ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hQa
  have hQ3' : Q₃ ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hQa
  have hQ4' : Q₄ ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hQa
  have hQL' : QL ≤ Q := le_trans (le_max_left _ _) hQb
  have hQe : Real.exp 1 ≤ Q := le_trans (le_max_right _ _) hQb
  obtain ⟨hT1, hℓ1, hℓs, hQQT, hQT, -⟩ := cell_facts P hQe hT
  have hTpos : 0 < T := by linarith
  have hLbig := (hQL Q hQL' T hT).1
  have hℓs1 : 1 ≤ ellS Q T := le_trans hℓ1 hℓs
  have hL1 : 1 ≤ P.L Q T := by
    have : 0 ≤ KR / δ' := by positivity
    linarith
  have hH0 : 0 ≤ W.H Q := W.H_nonneg Q
  have hJlen : P.Jlen T ≤ T := by
    unfold HSetup.Jlen
    have : 0 ≤ 2 * P.θ * T := by have := P.θ_pos; positivity
    linarith
  have hJlen0 : 0 ≤ P.Jlen T := by
    unfold HSetup.Jlen
    exact mul_nonneg (by linarith [P.θ_lt]) (by linarith)
  set L := P.L Q T with hLL
  set ℓs := ellS Q T with hℓℓ
  have hL0 : 0 ≤ L := by linarith
  have hℓs0 : 0 ≤ ℓs := by linarith
  set X := W.H Q * T * L ^ 2 * ℓs with hX
  have hX0 : 0 ≤ X := by positivity
  -- the pieces
  have e1 := h₁ Q hQ1' T hT
  have e2 := h₂ Q hQ2' T hT
  have e3 := h₃ Q hQ3' T hT
  have e4 := h₄ Q hQ4' T hT
  have hPP : PP2 P.toPS W Q (Q * T) T = 1 / (2 * Real.pi ^ 2) *
      ((P.ratioForm W Q T (P.aVec Q T)).re + (SSC2 P.toPS W Q (Q * T) T).re) :=
    PP2_eq P.toPS W hQT Q T
  have hss : 1 / (2 * Real.pi ^ 2) * (SSC2 P.toPS W Q (Q * T) T).re ≤ δ' * X := by
    have hre : (SSC2 P.toPS W Q (Q * T) T).re ≤ δ' * X := (Complex.re_le_norm _).trans e4
    have hpi2 : 1 ≤ 2 * Real.pi ^ 2 := by
      have : (3 : ℝ) ^ 2 ≤ Real.pi ^ 2 := pow_le_pow_left₀ (by norm_num) Real.pi_gt_three.le 2
      linarith
    have hc0 : 0 ≤ 1 / (2 * Real.pi ^ 2) := by positivity
    have hc1' : 1 / (2 * Real.pi ^ 2) ≤ 1 := by rw [div_le_one (by positivity)]; exact hpi2
    have h0 : 0 ≤ δ' * X := by positivity
    calc 1 / (2 * Real.pi ^ 2) * (SSC2 P.toPS W Q (Q * T) T).re
        ≤ 1 / (2 * Real.pi ^ 2) * (δ' * X) := mul_le_mul_of_nonneg_left hre hc0
      _ ≤ 1 * (δ' * X) := mul_le_mul_of_nonneg_right hc1' h0
      _ = δ' * X := one_mul _
  -- `∑ω K₂(P,P) ≤ H|J|L²ℓ_* I_F/π + 2δ'X ≤ (I_F/π + 2δ') X`
  set Main2 := W.H Q * P.Jlen T * L ^ 2 * ℓs * IFv / Real.pi with hMain2
  have hPPle : PP2 P.toPS W Q (Q * T) T ≤ Main2 + 2 * δ' * X := by
    rw [hPP, mul_add]; linarith
  have hMain2X : Main2 ≤ IFv / Real.pi * X := by
    rw [hMain2, hX]
    have : W.H Q * P.Jlen T * L ^ 2 * ℓs ≤ W.H Q * T * L ^ 2 * ℓs := by gcongr
    have e : W.H Q * P.Jlen T * L ^ 2 * ℓs * IFv / Real.pi =
        IFv / Real.pi * (W.H Q * P.Jlen T * L ^ 2 * ℓs) := by ring
    rw [e]; exact mul_le_mul_of_nonneg_left this (by positivity)
  -- the `r`-part
  have hRR' : RR2 P.toPS W Q (Q * T) T ≤ R₀ ^ 2 * W.H Q * (2 * Real.pi * P.bInt + CJ) * (T * L) := by
    refine (hRR P.toPS W Q (Q * T) T hQT hT1).trans ?_
    have hJ := hJ2 (Q * T) T hQT hTpos
    have hTL : 1 ≤ T * L := one_le_mul_of_one_le_of_one_le hT1 hL1
    have hJ' : ∫ t in P.toPS.J T, ∫ t' in P.toPS.J T, PhiSq P.toPS (Q * T) (t - t') ≤
        (2 * Real.pi * P.bInt + CJ) * (T * L) := by
      refine hJ.trans ?_
      have h1 : 2 * Real.pi * P.Jlen T * P.bInt * L ≤ 2 * Real.pi * T * P.bInt * L := by gcongr
      have h2 : CJ ≤ CJ * (T * L) := le_mul_of_one_le_right hCJ hTL
      have e : (2 * Real.pi * P.bInt + CJ) * (T * L) = 2 * Real.pi * T * P.bInt * L + CJ * (T * L) := by
        ring
      have hPSJ : P.toPS.Jlen T = P.Jlen T := rfl
      have hPSb : P.toPS.bInt = P.bInt := rfl
      have hPSL : P.toPS.L (Q * T) = L := rfl
      rw [hPSJ, hPSb, hPSL, e]
      linarith
    calc R₀ ^ 2 * W.H Q * ∫ t in P.toPS.J T, ∫ t' in P.toPS.J T, PhiSq P.toPS (Q * T) (t - t')
        ≤ R₀ ^ 2 * W.H Q * ((2 * Real.pi * P.bInt + CJ) * (T * L)) :=
          mul_le_mul_of_nonneg_left hJ' (by positivity)
      _ = R₀ ^ 2 * W.H Q * (2 * Real.pi * P.bInt + CJ) * (T * L) := by ring
  have hsRR : s * RR2 P.toPS W Q (Q * T) T ≤ δ' * X := by
    have hKRL : KR ≤ δ' * L := by
      have h : KR / δ' ≤ L := by linarith
      rw [div_le_iff₀ hδ'0] at h; linarith
    calc s * RR2 P.toPS W Q (Q * T) T
        ≤ s * (R₀ ^ 2 * W.H Q * (2 * Real.pi * P.bInt + CJ) * (T * L)) :=
          mul_le_mul_of_nonneg_left hRR' hs0.le
      _ = KR * (W.H Q * T * L) := by rw [hKR]; ring
      _ ≤ δ' * L * (W.H Q * T * L) := mul_le_mul_of_nonneg_right hKRL (by positivity)
      _ = δ' * (W.H Q * T * L ^ 2) * 1 := by ring
      _ ≤ δ' * (W.H Q * T * L ^ 2) * ℓs :=
          mul_le_mul_of_nonneg_left hℓs1 (by positivity)
      _ = δ' * X := by rw [hX]; ring
  have hMA := MA2_abs_le P.toPS W hQT Q T hs0
  have hsPP : s⁻¹ * PP2 P.toPS W Q (Q * T) T ≤ δ' * X := by
    calc s⁻¹ * PP2 P.toPS W Q (Q * T) T ≤ s⁻¹ * ((IFv / Real.pi + 2 * δ') * X) := by
          apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hs0.le)
          have : (IFv / Real.pi + 2 * δ') * X = IFv / Real.pi * X + 2 * δ' * X := by ring
          rw [this]; linarith
      _ = (s⁻¹ * (IFv / Real.pi + 2 * δ')) * X := by ring
      _ ≤ δ' * X := mul_le_mul_of_nonneg_right hsinv hX0
  -- `eq:split`
  have hsplit := Mcal2_split P.toPS W hQT Q T
  have hmix := Mmix2_split P.toPS W hQT Q T
  -- the main term
  have ha := aInt_pos P.toPS
  have ha' : 0 < P.aInt := ha
  have hQf : Qf (fun α => c α * min α (1 + 2 * P.ε₃))
      (fun x => P.vfun (x / P.lam) / (P.lam * P.aInt)) =
      (P.bInt / P.lam + 2 * IFv) / P.aInt ^ 2 := Qf_fv_eq (P := P.toPS) hc.continuous
  have hLdef : L = P.lam * ℓs := rfl
  have hmain : (P.aInt * L) ^ 2 * (W.H Q * P.Jlen T * ℓs / (2 * Real.pi)) *
      Qf (fun α => c α * min α (1 + 2 * P.ε₃))
        (fun x => P.vfun (x / P.lam) / (P.lam * P.aInt)) =
      W.H Q * P.Jlen T * P.bInt * L * ℓs ^ 2 / (2 * Real.pi) + Main2 := by
    rw [hQf, hMain2, hLdef]
    field_simp
  rw [hmain, hsplit, hmix]
  have hMB := (le_abs_self (MB2 P.toPS W Q (Q * T) T)).trans e2
  have hMA' : 2 * MA2 P.toPS W Q (Q * T) T ≤
      s * RR2 P.toPS W Q (Q * T) T + s⁻¹ * PP2 P.toPS W Q (Q * T) T :=
    (by linarith [le_abs_self (MA2 P.toPS W Q (Q * T) T)] : 2 * MA2 P.toPS W Q (Q * T) T ≤
      2 * |MA2 P.toPS W Q (Q * T) T|).trans hMA
  have hsum6 : δ' * X + 2 * (δ' * X) + δ' * X + δ' * X + 2 * δ' * X ≤ δ * X := by
    rw [hδ']; ring_nf; exact le_refl _
  have e1' : Mmumu2 P.toPS W Q (Q * T) T ≤
      W.H Q * P.Jlen T * P.bInt * L * ℓs ^ 2 / (2 * Real.pi) + δ' * X := e1
  linarith

end Families.Hybrid.S
