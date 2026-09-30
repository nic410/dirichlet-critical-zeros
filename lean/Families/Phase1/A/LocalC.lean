/-
**`lem:C`** (`lemma-toeplitz-C.tex`), the local count for the positive
part, from `lem:Omega`(a),(c) and `lem:fS`(i).

* `ae_pullback_inv`: null sets of `t > 0` pull back to null sets under `z ↦ 1/(c|z|)`
  ("as `z ↦ t = 1/(v|z|Q)` is a diffeomorphism of each half-line onto `(0,∞)`").
* `lemC_fixed`: the bound at fixed data `(Q, ς, V, θ, u/v)` with `k_* ≤ Q`:
  `(μ^♮*k_ς)(θ) ≤ ℰ I_w Q² C_T^+ + 6‖w̃‖_∞η^{-2}ς^{-1} + (4(1+log Q)² + 3(1+log Q))·4V_wς^{-1}k_*(1+log⁺k_*)`.
* `lemC_of : lemOmega_ac_Statement → lemfS_i_Statement → lemC_Statement`, with `Q₁(ε) = 4^{4/ε}`.
-/
import Families.Phase1.A.LocalCPrep

noncomputable section

open scoped BigOperators ENNReal ArithmeticFunction.Moebius
open Finset MeasureTheory Set

namespace Families.Phase1.A

open Families ArithmeticFunction

/-! ### The null-set step -/

/-- If `P` holds for a.e. `t > 0`, then `P(1/(c|z|))` holds for a.e. `z ≠ 0` (`c > 0`). -/
lemma ae_pullback_inv {P : ℝ → Prop} (hP : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), P t) {c : ℝ}
    (hc : 0 < c) : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ 0 → P (1 / (c * |z|)) := by
  rw [ae_restrict_iff' measurableSet_Ioi] at hP
  set N : Set ℝ := {t | 0 < t ∧ ¬ P t} with hN
  have hN0 : volume N = 0 := by
    rw [ae_iff] at hP
    refine measure_mono_null (fun t ht => ?_) hP
    simp only [hN, Set.mem_ofPred_eq] at ht ⊢
    exact fun h => ht.2 (h ht.1)
  set h1 : ℝ → ℝ := fun t => 1 / (c * t) with hh1
  set h2 : ℝ → ℝ := fun t => -(1 / (c * t)) with hh2
  have hd1 : DifferentiableOn ℝ h1 N := by
    intro t ht
    have : c * t ≠ 0 := (mul_pos hc ht.1).ne'
    exact ((differentiableAt_const _).div ((differentiableAt_const c).mul differentiableAt_id)
      this).differentiableWithinAt
  have hd2 : DifferentiableOn ℝ h2 N := hd1.neg
  have hI1 := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hd1 hN0
  have hI2 := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hd2 hN0
  have hU := measure_union_null hI1 hI2
  refine (measure_eq_zero_iff_ae_notMem.mp hU).mono fun z hz hz0 => ?_
  by_contra hPz
  apply hz
  have hzabs : 0 < |z| := abs_pos.mpr hz0
  have hpos : 0 < 1 / (c * |z|) := by positivity
  rcases lt_or_gt_of_ne hz0 with hneg | hpos'
  · right
    refine ⟨1 / (c * |z|), ⟨hpos, hPz⟩, ?_⟩
    simp only [hh2]
    rw [abs_of_neg hneg]
    field_simp
  · left
    refine ⟨1 / (c * |z|), ⟨hpos, hPz⟩, ?_⟩
    simp only [hh1]
    rw [abs_of_pos hpos']
    field_simp

lemma rhoTwist_zero (𝔴 : ℝ → ℝ) (S : Finset ℕ) (r : ℕ) (Q : ℝ) (v : ℕ) :
    rhoTwist 𝔴 S r Q v 0 = 0 := by
  unfold rhoTwist; simp

lemma wtmax_nonneg (W : Weight) : 0 ≤ W.wtmax :=
  Real.sSup_nonneg (by rintro _ ⟨u, rfl⟩; unfold Weight.wt; exact mul_nonneg (sq_nonneg u) (W.nonneg u))

/-! ### `lem:C` at fixed data -/

/-- **`lem:C` at fixed data.** Hypotheses: `Q ≥ 1`, `ς > 0`, a Dirichlet approximation `u/v`
(`1 ≤ v ≤ V`, `(u,v) = 1`, `|θ − u/v| ≤ 1/(vV)`) and `k_* = Q/V + QVς ≤ Q`. -/
theorem lemC_fixed (hΩ : lemOmega_ac_Statement) (hfS : lemfS_i_Statement) (W : Weight)
    {Q ς V θ : ℝ} {u : ℤ} {v : ℕ} (hQ : 1 ≤ Q) (hς : 0 < ς) (hV : 1 ≤ V) (hv : 1 ≤ v)
    (hvV : (v : ℝ) ≤ V) (huv : IsCoprime u (v : ℤ)) (hθ : |θ - u / v| ≤ 1 / (v * V))
    (hks : Q / V + Q * V * ς ≤ Q) :
    ENNReal.ofReal (natConv W Q ς θ) ≤
      ENNReal.ofReal (Ecal * W.Iw * Q ^ 2) * CTp W +
      ENNReal.ofReal (6 * W.wtmax * W.η⁻¹ ^ 2 * ς⁻¹ +
        (4 * (1 + Real.log Q) ^ 2 + 3 * (1 + Real.log Q)) *
          (4 * W.Vw * ς⁻¹ * (Q / V + Q * V * ς) * (1 + Real.posLog (Q / V + Q * V * ς)))) := by
  have hQ0 : 0 < Q := by linarith
  have hV0 : 0 < V := by linarith
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  set y := θ - u / v with hy
  set ks := Q / V + Q * V * ς with hks_def
  have hks0 : 0 ≤ ks := by positivity
  set E0 := 4 * W.Vw * ς⁻¹ * ks * (1 + Real.posLog ks) with hE0
  have hE0nn : 0 ≤ E0 := by
    have := Vw_nonneg W; have := Real.posLog_nonneg (x := ks); positivity
  set R := (Finset.Icc 1 ⌊Q⌋₊).filter Squarefree with hR
  set S := v.primeFactors with hS
  set L := 1 + Real.log Q with hL
  have hL1 : 1 ≤ L := by have := Real.log_nonneg hQ; linarith
  -- the twisted counts
  have hRmem : ∀ r ∈ R, 1 ≤ r ∧ Squarefree r := fun r hr =>
    ⟨(Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1, (Finset.mem_filter.mp hr).2⟩
  set ρr : ℕ → ℝ → ℝ := fun r z => rhoTwist (fun u => W.w (r * u)) S r Q v z with hρr
  set ρm : ℝ → ℝ := fun z => rhoTwist (mQ W Q) S 1 Q v z with hρm
  set tcr : ℕ → ℝ := fun r => twistedConv (fun u => W.w (r * u)) r Q ς θ with htcr
  set isor : ℕ → ℝ := fun r => (if Nat.Coprime v r then W.w (r * (v / Q)) else 0) * k0 ς y
    with hisor
  have hcr : ∀ r ∈ R, Integrable (fun z => k0 ς (z - y) * ρr r z) ∧
      |tcr r - isor r - ∫ z, k0 ς (z - y) * ρr r z| ≤ (r.divisors.card : ℝ) * E0 := by
    intro r hr
    obtain ⟨hI, hB⟩ := twistedCount (w_dil_bv W r) (w_dil_supp W (hRmem r hr).1) hQ hς hV hv hvV
      huv hθ (hRmem r hr).2
    rw [← hks_def] at hB
    refine ⟨hI, hB.trans ?_⟩
    have hVr := w_dil_Vw_le W r
    have := Real.posLog_nonneg (x := ks)
    rw [hE0]
    gcongr
  obtain ⟨hIm, hBm⟩ := twistedCount (mQ_bv W Q) (mQ_supp W Q) hQ hς hV hv hvV huv hθ
    (r := 1) squarefree_one
  rw [Nat.divisors_one, Finset.card_singleton, Nat.cast_one, one_mul,
    if_pos (Nat.coprime_one_right v)] at hBm
  have hBm' : |twistedConv (mQ W Q) 1 Q ς θ - mQ W Q (v / Q) * k0 ς y -
      ∫ z, k0 ς (z - y) * ρm z| ≤ 3 * L * E0 := by
    refine hBm.trans ?_
    have hVm := Vw_mQ_le W hQ
    have := Real.posLog_nonneg (x := ks)
    have h1 : 4 * (eVariationOn (mQ W Q) univ).toReal * ς⁻¹ * ks * (1 + Real.posLog ks) ≤
        4 * (3 * W.Vw * L) * ς⁻¹ * ks * (1 + Real.posLog ks) := by gcongr
    calc _ ≤ 4 * (3 * W.Vw * L) * ς⁻¹ * ks * (1 + Real.posLog ks) := h1
      _ = 3 * L * E0 := by rw [hE0]; ring
  -- the three parts
  set ISO := ∑ r ∈ R, (μ r : ℝ) / Nat.totient r * isor r + mQ W Q (v / Q) * k0 ς y with hISO
  set G : ℝ → ℝ := fun z => ∑ r ∈ R, (μ r : ℝ) / Nat.totient r * ρr r z + ρm z with hG
  set MAIN := ∑ r ∈ R, (μ r : ℝ) / Nat.totient r * (∫ z, k0 ς (z - y) * ρr r z) +
    ∫ z, k0 ς (z - y) * ρm z with hMAIN
  have hdecomp : natConv W Q ς θ = ∑ r ∈ R, (μ r : ℝ) / Nat.totient r * tcr r +
      twistedConv (mQ W Q) 1 Q ς θ := natConv_decomp W hQ0 ς θ
  -- error part
  have herr : |natConv W Q ς θ - ISO - MAIN| ≤ (4 * L ^ 2 + 3 * L) * E0 := by
    have e : natConv W Q ς θ - ISO - MAIN =
        ∑ r ∈ R, (μ r : ℝ) / Nat.totient r * (tcr r - isor r - ∫ z, k0 ς (z - y) * ρr r z) +
        (twistedConv (mQ W Q) 1 Q ς θ - mQ W Q (v / Q) * k0 ς y - ∫ z, k0 ς (z - y) * ρm z) := by
      have hsum : ∑ r ∈ R, (μ r : ℝ) / Nat.totient r * (tcr r - isor r -
            ∫ z, k0 ς (z - y) * ρr r z) =
          ∑ r ∈ R, (μ r : ℝ) / Nat.totient r * tcr r - ∑ r ∈ R, (μ r : ℝ) / Nat.totient r * isor r -
            ∑ r ∈ R, (μ r : ℝ) / Nat.totient r * (∫ z, k0 ς (z - y) * ρr r z) := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun r _ => by ring
      rw [hdecomp, hISO, hMAIN, hsum]
      ring
    rw [e]
    have hsumτ : ∑ r ∈ R, ((r.divisors.card : ℕ) : ℝ) / Nat.totient r ≤ 4 * L ^ 2 := by
      refine (sum_sqfree_card_divisors_div_totient_le' ⌊Q⌋₊).trans ?_
      have hN : (1 : ℝ) ≤ ⌊Q⌋₊ := by exact_mod_cast (Nat.floor_pos.mpr hQ : 0 < ⌊Q⌋₊)
      have hlog : Real.log ⌊Q⌋₊ ≤ Real.log Q :=
        Real.log_le_log (by linarith) (Nat.floor_le hQ0.le)
      have h0 : 0 ≤ 1 + Real.log ⌊Q⌋₊ := by have := Real.log_nonneg hN; linarith
      have : (1 + Real.log ⌊Q⌋₊) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ h0 (by linarith) 2
      linarith
    have h1 : |∑ r ∈ R, (μ r : ℝ) / Nat.totient r * (tcr r - isor r -
        ∫ z, k0 ς (z - y) * ρr r z)| ≤ 4 * L ^ 2 * E0 := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ r ∈ R, |(μ r : ℝ) / Nat.totient r * (tcr r - isor r - ∫ z, k0 ς (z - y) * ρr r z)|
          ≤ ∑ r ∈ R, ((r.divisors.card : ℕ) : ℝ) / Nat.totient r * E0 := by
            refine Finset.sum_le_sum fun r hr => ?_
            rw [abs_mul]
            have hφ : (0 : ℝ) < Nat.totient r :=
              by exact_mod_cast Nat.totient_pos.mpr (hRmem r hr).1
            have hμ : |(μ r : ℝ) / Nat.totient r| ≤ 1 / Nat.totient r := by
              rw [abs_div, abs_of_pos hφ]
              gcongr
              exact_mod_cast ArithmeticFunction.abs_moebius_le_one
            calc |(μ r : ℝ) / Nat.totient r| * |tcr r - isor r - ∫ z, k0 ς (z - y) * ρr r z|
                ≤ 1 / Nat.totient r * ((r.divisors.card : ℝ) * E0) :=
                  mul_le_mul hμ (hcr r hr).2 (abs_nonneg _) (by positivity)
              _ = _ := by ring
        _ = (∑ r ∈ R, ((r.divisors.card : ℕ) : ℝ) / Nat.totient r) * E0 := by
            rw [Finset.sum_mul]
        _ ≤ 4 * L ^ 2 * E0 := by gcongr
    calc _ ≤ |∑ r ∈ R, (μ r : ℝ) / Nat.totient r * (tcr r - isor r -
          ∫ z, k0 ς (z - y) * ρr r z)| +
          |twistedConv (mQ W Q) 1 Q ς θ - mQ W Q (v / Q) * k0 ς y -
            ∫ z, k0 ς (z - y) * ρm z| := abs_add_le _ _
      _ ≤ 4 * L ^ 2 * E0 + 3 * L * E0 := add_le_add h1 hBm'
      _ = _ := by ring
  -- isolated point
  have hiso : ISO ≤ 6 * W.wtmax * W.η⁻¹ ^ 2 * ς⁻¹ := by
    have hΩv : ∑ r ∈ R, (μ r : ℝ) / Nat.totient r * (if Nat.Coprime v r then W.w (r * (v / Q))
        else 0) = Ωlev W Q v := by
      rw [Ωlev_eq_second_form W Q v hv, hR, Finset.sum_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun r _ => ?_
      by_cases hsq : Squarefree r
      · by_cases hc : Nat.Coprime v r
        · rw [if_pos hsq, if_pos hc, if_pos ⟨hsq, hc.symm⟩]
          push_cast
          rw [show (v : ℝ) * r / Q = r * (v / Q) by ring]
        · rw [if_pos hsq, if_neg hc, if_neg (fun h => hc h.2.symm), mul_zero]
      · rw [if_neg hsq, if_neg (fun h => hsq h.1)]
    have hmv : mQ W Q (v / Q) = mfun W (v / Q) :=
      mQ_eq_mfun W (by positivity) (by
        rw [one_div_div, div_le_iff₀ hv']
        have : (1 : ℝ) ≤ v := by exact_mod_cast hv
        nlinarith)
    have hISO' : ISO = (Ωlev W Q v + mfun W (v / Q)) * k0 ς y := by
      rw [hISO, ← hmv, ← hΩv, add_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun r _ => ?_
      simp only [hisor]; ring
    obtain ⟨ha, hc, -⟩ := hΩ W Q hQ0
    have h1 : |Ωlev W Q v| ≤ 3 * W.wtmax * W.η⁻¹ ^ 2 :=
      (ha v hv).trans (mul_le_mul_of_nonneg_left (min_le_right _ _)
        (by have := wtmax_nonneg W; positivity))
    have h2 : mfun W (v / Q) ≤ 3 * W.wtmax * W.η⁻¹ ^ 2 :=
      (hc (v / Q) (by positivity)).trans (mul_le_mul_of_nonneg_left (min_le_right _ _)
        (by have := wtmax_nonneg W; positivity))
    have hk := k0_le hς y
    have hk0 := k0_nonneg hς y
    have hm0 := mfun_nonneg W (v / Q)
    rw [hISO']
    calc (Ωlev W Q v + mfun W (v / Q)) * k0 ς y ≤ (|Ωlev W Q v| + mfun W (v / Q)) * ς⁻¹ := by
          have : Ωlev W Q v + mfun W (v / Q) ≤ |Ωlev W Q v| + mfun W (v / Q) := by
            linarith [le_abs_self (Ωlev W Q v)]
          calc (Ωlev W Q v + mfun W (v / Q)) * k0 ς y ≤ (|Ωlev W Q v| + mfun W (v / Q)) * k0 ς y :=
                mul_le_mul_of_nonneg_right this hk0
            _ ≤ _ := mul_le_mul_of_nonneg_left hk (by positivity)
      _ ≤ (3 * W.wtmax * W.η⁻¹ ^ 2 + 3 * W.wtmax * W.η⁻¹ ^ 2) * ς⁻¹ := by
          gcongr
      _ = 6 * W.wtmax * W.η⁻¹ ^ 2 * ς⁻¹ := by ring
  -- main part: as one integral
  have hIntr : ∀ r ∈ R, Integrable (fun z => (μ r : ℝ) / Nat.totient r * (k0 ς (z - y) * ρr r z)) :=
    fun r hr => (hcr r hr).1.const_mul _
  have hGfun : (fun z => k0 ς (z - y) * G z) = fun z =>
      (∑ r ∈ R, (μ r : ℝ) / Nat.totient r * (k0 ς (z - y) * ρr r z)) + k0 ς (z - y) * ρm z := by
    funext z
    simp only [hG, mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  have hIntG : Integrable (fun z => k0 ς (z - y) * G z) := by
    rw [hGfun]; exact (integrable_finsetSum _ hIntr).add hIm
  have hMAIN_eq : MAIN = ∫ z, k0 ς (z - y) * G z := by
    rw [hGfun, integral_add (integrable_finsetSum _ hIntr) hIm, integral_finsetSum _ hIntr, hMAIN]
    have hs : ∑ r ∈ R, (μ r : ℝ) / Nat.totient r * (∫ z, k0 ς (z - y) * ρr r z) =
        ∑ r ∈ R, ∫ z, (μ r : ℝ) / Nat.totient r * (k0 ς (z - y) * ρr r z) :=
      Finset.sum_congr rfl fun r _ => (integral_const_mul _ _).symm
    rw [hs]
  -- the ess sup
  set c := Ecal * W.Iw * Q ^ 2 with hc_def
  have hc0 : 0 < c := by have := Ecal_Iw_pos W; positivity
  set Ess := essSup (fun t => ENNReal.ofReal (RS W S t + Rm W t)) (volume.restrict (Ioi (0 : ℝ)))
    with hEss_def
  have hEss : Ess ≤ CTp W := by
    unfold CTp
    exact le_iSup (fun S : Finset ℕ => essSup (fun t => ENNReal.ofReal (RS W S t + Rm W t))
      (volume.restrict (Ioi (0 : ℝ)))) S
  set ERR := 6 * W.wtmax * W.η⁻¹ ^ 2 * ς⁻¹ + (4 * L ^ 2 + 3 * L) * E0 with hERR
  by_cases hE : Ess = ⊤
  · have hC : CTp W = ⊤ := top_le_iff.mp (hE ▸ hEss)
    rw [hC, ENNReal.mul_top (by simpa using hc0), top_add]
    exact le_top
  -- a.e. bound on the density
  have hae : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), RS W S t + Rm W t ≤ Ess.toReal :=
    (ENNReal.ae_le_essSup _).mono fun t ht => (ENNReal.ofReal_le_iff_le_toReal hE).mp ht
  have hae' := ae_pullback_inv hae (c := (v : ℝ) * Q) (by positivity)
  have hmain_le : MAIN ≤ c * Ess.toReal := by
    rw [hMAIN_eq]
    have hIntc : Integrable (fun z => k0 ς (z - y) * (c * Ess.toReal)) :=
      (integrable_k0_sub hς y).mul_const _
    calc ∫ z, k0 ς (z - y) * G z ≤ ∫ z, k0 ς (z - y) * (c * Ess.toReal) := by
          refine integral_mono_ae hIntG hIntc (hae'.mono fun z hz => ?_)
          have hk0 := k0_nonneg hς (z - y)
          have hcE : 0 ≤ c * Ess.toReal := by positivity
          by_cases hkz : k0 ς (z - y) = 0
          · simp [hkz]
          by_cases hz0 : z = 0
          · subst hz0
            simp only [hG, hρr, hρm, rhoTwist_zero, mul_zero, Finset.sum_const_zero, add_zero]
            exact mul_nonneg hk0 hcE
          refine mul_le_mul_of_nonneg_left ?_ hk0
          have hlt := vzQ_lt_kstar hQ0 hς hV0 hv hvV hθ z (abs_lt_of_k0_ne_zero hς hkz)
          have hM : ⌊(v : ℝ) * |z| * Q⌋₊ ≤ ⌊Q⌋₊ := Nat.floor_le_floor (by linarith)
          have e1 := sum_rhoTwist_eq hfS W hQ0 hv S hz0 hM
          have e2 := rhoTwist_mQ_le W hQ0 hv S hz0
          have ht : 1 / ((v : ℝ) * |z| * Q) = 1 / ((v : ℝ) * Q * |z|) := by ring_nf
          have hR := hz hz0
          rw [← ht] at hR
          simp only [hG]
          calc ∑ r ∈ R, (μ r : ℝ) / Nat.totient r * ρr r z + ρm z
              ≤ Q ^ 2 * (Ecal * W.Iw) * RS W S (1 / ((v : ℝ) * |z| * Q)) +
                Q ^ 2 * (Ecal * W.Iw) * Rm W (1 / ((v : ℝ) * |z| * Q)) := by
                rw [← e1]; exact add_le_add le_rfl e2
            _ = c * (RS W S (1 / ((v : ℝ) * |z| * Q)) + Rm W (1 / ((v : ℝ) * |z| * Q))) := by
                rw [hc_def]; ring
            _ ≤ c * Ess.toReal := mul_le_mul_of_nonneg_left hR hc0.le
      _ = c * Ess.toReal := by
          rw [integral_mul_const, integral_k0_sub hς y, one_mul]
  -- conclusion
  have hnat : natConv W Q ς θ ≤ c * Ess.toReal + ERR := by
    have := neg_abs_le (natConv W Q ς θ - ISO - MAIN)
    have := le_abs_self (natConv W Q ς θ - ISO - MAIN)
    rw [hERR]
    linarith
  calc ENNReal.ofReal (natConv W Q ς θ) ≤ ENNReal.ofReal (c * Ess.toReal + ERR) :=
        ENNReal.ofReal_le_ofReal hnat
    _ ≤ ENNReal.ofReal (c * Ess.toReal) + ENNReal.ofReal ERR := ENNReal.ofReal_add_le
    _ = ENNReal.ofReal c * Ess + ENNReal.ofReal ERR := by
        rw [ENNReal.ofReal_mul hc0.le, ENNReal.ofReal_toReal hE]
    _ ≤ ENNReal.ofReal c * CTp W + ENNReal.ofReal ERR := by gcongr
    _ = _ := by rw [hERR, hE0, hL]

/-! ### Exponent bookkeeping and `Q₁(ε)` -/

/-- For `Q ≥ 4^{4/ε}`, `Q ≤ K ≤ Q^{2−ε}`, `κ = Q^{−ε/4}`, `ς = κ/K`, `V = Q^{1−ε/2}`:
`Q ≥ 1`, `ς > 0`, `V ≥ 1`, `ς⁻¹ ≤ Q^{2−3ε/4}`, `k_* = Q/V + QVς ≤ Q` and `ς⁻¹k_* ≤ 2Q^{2−ε/4}`
(`lem:C`, first paragraph of the proof; `Q₁(ε) = 4^{4/ε}` makes `κ ≤ 1/4` and `k_* < Q`). -/
lemma lemC_exponents {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) {Q : ℝ} (hQ : (4 : ℝ) ^ (4 / ε) ≤ Q)
    {K : ℕ} (hK1 : Q ≤ K) (hK2 : (K : ℝ) ≤ Q ^ (2 - ε)) :
    1 ≤ Q ∧ 0 < Q ^ (-ε / 4) / K ∧ 1 ≤ Q ^ (1 - ε / 2) ∧
      (Q ^ (-ε / 4) / K)⁻¹ ≤ Q ^ (2 - 3 * ε / 4) ∧
      Q / Q ^ (1 - ε / 2) + Q * Q ^ (1 - ε / 2) * (Q ^ (-ε / 4) / K) ≤ Q ∧
      (Q ^ (-ε / 4) / K)⁻¹ * (Q / Q ^ (1 - ε / 2) + Q * Q ^ (1 - ε / 2) * (Q ^ (-ε / 4) / K))
        ≤ 2 * Q ^ (2 - ε / 4) := by
  have h4 : (1 : ℝ) ≤ (4 : ℝ) ^ (4 / ε) := Real.one_le_rpow (by norm_num) (by positivity)
  have hQ1 : 1 ≤ Q := h4.trans hQ
  have hQ0 : 0 < Q := by linarith
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le hQ0 hK1
  set a := Q ^ (ε / 4) with ha
  have ha4 : 4 ≤ a := by
    have h1 : ((4 : ℝ) ^ (4 / ε)) ^ (ε / 4) ≤ a :=
      Real.rpow_le_rpow (by positivity) hQ (by positivity)
    rwa [← Real.rpow_mul (by norm_num), show 4 / ε * (ε / 4) = 1 by field_simp,
      Real.rpow_one] at h1
  have ha0 : 0 < a := by linarith
  have hpow : ∀ n : ℕ, Q ^ ((ε / 4) * n) = a ^ n := fun n => Real.rpow_mul_natCast hQ0.le _ n
  have hQ2 : Q ^ (2 : ℝ) = Q ^ 2 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have e1 : Q ^ (-ε / 4) = a⁻¹ := by rw [neg_div, Real.rpow_neg hQ0.le]
  have e2 : Q ^ (1 - ε / 2) = Q / a ^ 2 := by
    rw [Real.rpow_sub hQ0, Real.rpow_one, ← hpow 2]; congr 2; push_cast; ring
  have e3 : Q ^ (2 - ε) = Q ^ 2 / a ^ 4 := by
    rw [Real.rpow_sub hQ0, hQ2, ← hpow 4]; congr 2; push_cast; ring
  have e4 : Q ^ (2 - 3 * ε / 4) = Q ^ 2 / a ^ 3 := by
    rw [Real.rpow_sub hQ0, hQ2, ← hpow 3]; congr 2; push_cast; ring
  have e5 : Q ^ (2 - ε / 4) = Q ^ 2 / a := by
    rw [Real.rpow_sub hQ0, hQ2]
  have ha4Q : a ^ 4 ≤ Q := by
    rw [← hpow 4]
    calc Q ^ ((ε / 4) * ((4 : ℕ) : ℝ)) ≤ Q ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hQ1 (by push_cast; linarith)
      _ = Q := Real.rpow_one Q
  rw [e1, e2, e4, e5]
  rw [e3] at hK2
  have hKa : (K : ℝ) * a ^ 4 ≤ Q ^ 2 := by
    rw [le_div_iff₀ (by positivity)] at hK2; linarith
  have ha2 : 16 ≤ a ^ 2 := by nlinarith
  have ha3 : 64 ≤ a ^ 3 := by nlinarith
  refine ⟨hQ1, by positivity, ?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity), one_mul]; nlinarith
  · -- `ς⁻¹ = aK ≤ Q²/a³`
    rw [inv_div, div_inv_eq_mul, le_div_iff₀ (by positivity)]
    nlinarith
  · -- `k_* = a² + Q²/(a³K) ≤ Q/16 + Q/64`
    have t1 : Q / (Q / a ^ 2) = a ^ 2 := by field_simp
    have t2 : Q * (Q / a ^ 2) * (a⁻¹ / K) ≤ Q / a ^ 3 := by
      rw [show Q * (Q / a ^ 2) * (a⁻¹ / K) = Q ^ 2 / (a ^ 3 * K) by field_simp]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_left hK1 (by positivity : (0 : ℝ) ≤ Q * a ^ 3)
      nlinarith
    have t3 : Q / a ^ 3 ≤ Q / 64 := div_le_div_of_nonneg_left hQ0.le (by norm_num) ha3
    have t4 : a ^ 2 ≤ Q / 16 := by rw [le_div_iff₀ (by norm_num)]; nlinarith
    rw [t1]; linarith
  · -- `ς⁻¹ k_* = a³K + Q²/a² ≤ 2Q²/a`
    have t1 : (a⁻¹ / K)⁻¹ * (Q / (Q / a ^ 2) + Q * (Q / a ^ 2) * (a⁻¹ / K)) =
        a ^ 3 * K + Q ^ 2 / a ^ 2 := by field_simp
    rw [t1]
    have t2 : a ^ 3 * K ≤ Q ^ 2 / a := by
      rw [le_div_iff₀ ha0]; nlinarith
    have t3 : Q ^ 2 / a ^ 2 ≤ Q ^ 2 / a :=
      div_le_div_of_nonneg_left (by positivity) ha0 (by nlinarith)
    linarith

/-- **`lem:C`** from `lem:Omega`(a),(c) and `lem:fS`(i), with `Q₁(ε) = 4^{4/ε}`. -/
theorem lemC_of (hΩ : lemOmega_ac_Statement) (hfS : lemfS_i_Statement) : lemC_Statement := by
  intro ε hε hε1
  refine ⟨(4 : ℝ) ^ (4 / ε), fun W Q hQ K hK1 hK2 θ => ?_⟩
  obtain ⟨hQ1, hς, hV, hςinv, hks, hςks⟩ := lemC_exponents hε hε1 hQ hK1 hK2
  set ς := Q ^ (-ε / 4) / K with hς_def
  set V := Q ^ (1 - ε / 2) with hV_def
  have hQ0 : 0 < Q := by linarith
  -- Dirichlet approximation `u/v`, `1 ≤ v ≤ V`, `|θ − u/v| ≤ 1/(vV)`
  obtain ⟨q, hq1, hq2⟩ := Real.exists_rat_abs_sub_le_and_den_le θ (n := ⌊V⌋₊)
    (Nat.floor_pos.mpr hV)
  have hv : 1 ≤ q.den := q.den_pos
  have hvV : (q.den : ℝ) ≤ V := (Nat.cast_le.mpr hq2).trans (Nat.floor_le (by linarith))
  have huv : IsCoprime q.num (q.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs, Int.natAbs_natCast]
    exact q.reduced
  have hθ : |θ - q.num / q.den| ≤ 1 / (q.den * V) := by
    rw [← Rat.cast_def]
    refine hq1.trans (one_div_le_one_div_of_le (by positivity) ?_)
    have : V < ⌊V⌋₊ + 1 := Nat.lt_floor_add_one V
    have hd : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
    nlinarith
  have hmain := lemC_fixed hΩ hfS W hQ1 hς hV hv hvV huv hθ hks
  refine hmain.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal ?_))
  -- the error terms
  set ks := Q / V + Q * V * ς with hks_def
  set L := 1 + Real.log Q with hL
  have hL1 : 1 ≤ L := by have := Real.log_nonneg hQ1; linarith
  have hks0 : 0 ≤ ks := by
    have : 0 < V := by linarith
    positivity
  have hpl : 1 + Real.posLog ks ≤ L := by
    have h1 := Real.posLog_le_posLog hks0 hks
    rw [Real.posLog_eq_log (x := Q) (by rw [abs_of_pos hQ0]; exact hQ1)] at h1
    linarith
  have hpl0 : 0 ≤ 1 + Real.posLog ks := by have := Real.posLog_nonneg (x := ks); linarith
  have hVw := Vw_nonneg W
  have hwt := wtmax_nonneg W
  set P := Q ^ (2 - ε / 4) with hP
  have hP0 : 0 ≤ P := by positivity
  have hLeta : 0 ≤ Leta W.η + 1 := by
    unfold Leta
    have : 1 < 1 / W.η := by rw [lt_one_div (by norm_num) W.η_pos]; linarith [W.η_lt_half]
    have := Real.log_pos this
    linarith
  have hiso : 6 * W.wtmax * W.η⁻¹ ^ 2 * ς⁻¹ ≤ 6 * W.wtmax * W.η⁻¹ ^ 2 * Q ^ (2 - 3 * ε / 4) := by
    gcongr
  have hspk : (4 * L ^ 2 + 3 * L) * (4 * W.Vw * ς⁻¹ * ks * (1 + Real.posLog ks)) ≤
      120 * W.Vw * P * L ^ 3 := by
    have hA : ς⁻¹ * ks ≤ 2 * P := hςks
    have hA0 : 0 ≤ ς⁻¹ * ks := by positivity
    calc (4 * L ^ 2 + 3 * L) * (4 * W.Vw * ς⁻¹ * ks * (1 + Real.posLog ks))
        = (4 * L ^ 2 + 3 * L) * (4 * W.Vw) * (ς⁻¹ * ks) * (1 + Real.posLog ks) := by ring
      _ ≤ (4 * L ^ 2 + 3 * L) * (4 * W.Vw) * (2 * P) * L := by gcongr
      _ = W.Vw * P * (32 * L ^ 3 + 24 * L ^ 2) := by ring
      _ ≤ W.Vw * P * (120 * L ^ 3) := by
          gcongr
          nlinarith
      _ = 120 * W.Vw * P * L ^ 3 := by ring
  have h3 : 0 ≤ 3 * W.wtmax * (Leta W.η + 1) := by positivity
  linarith

/-- **`lem:C`** from the full `lem:fS` statement (only part (i) is used). -/
theorem lemC_of_lemfS (hΩ : lemOmega_ac_Statement) (hfS : lemfS_Statement) : lemC_Statement :=
  lemC_of hΩ (lemfS_i_of_lemfS hfS)

end Families.Phase1.A
