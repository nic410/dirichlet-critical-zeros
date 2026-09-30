/-
# Theorem 1.4(a): the glue (all proved, no `sorry`)

* `bandLSH_of_MV` — the band constant at polynomial height from the multiplicative large sieve and
  `lem:WH` (port of `Families.bandLS_of_MV`; the intervals may lie anywhere).
* `assembly_fixedH` — `prop:zeroH` + `prop:secondH` + the lower half of `lem:RvMH` at fixed data
  (port of `Families.assembly_fixed`, with `ℓ_*` in `lem:RvMH`).
* `thmHcell_of_parts` — the one-cell theorem from the component statements (port of
  `Families.thmMain_of_parts`; §9.4, proof of Theorem 9.20).
* `thmH_of_cells` — the κ-cells argument (§9.4, (9.16)–(9.17)): the one-cell theorem and
  `lem:Mbeta` give the height-dependent target `p(β(κ_T))`.
* `thmH_of_parts` — the headline from the component statements.
-/
import FamiliesH.Main

noncomputable section

open scoped BigOperators ComplexConjugate ArithmeticFunction.Moebius ENNReal ContDiff
open ArithmeticFunction Finset MeasureTheory Filter Topology

namespace Families.Hybrid

open Families

/-! ### Arithmetic of `β(κ)` and `κ_T` -/

lemma betaK_le_two {κ : ℝ} (h : 0 ≤ κ) : betaK κ ≤ 2 := by
  unfold betaK
  rw [div_le_iff₀ (by linarith)]
  linarith

lemma one_lt_betaK {κ : ℝ} (h : 0 ≤ κ) : 1 < betaK κ := by
  unfold betaK
  rw [lt_div_iff₀ (by linarith)]
  linarith

lemma betaK_anti {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : betaK b ≤ betaK a := by
  unfold betaK
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- `β(a)/β(b) − 1 = (b−a)/((1+a)(2+b)) ≤ (b−a)/2` for `0 ≤ a ≤ b`. -/
lemma betaK_ratio_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    betaK a / betaK b - 1 ≤ (b - a) / 2 := by
  have h1 : (1 : ℝ) + a ≠ 0 := by linarith
  have h2 : (1 : ℝ) + b ≠ 0 := by linarith
  have h3 : (2 : ℝ) + b ≠ 0 := by linarith
  have hkey : betaK a / betaK b - 1 = (b - a) / ((1 + a) * (2 + b)) := by
    unfold betaK
    field_simp
    ring
  rw [hkey]
  apply div_le_div_of_nonneg_left (by linarith) (by norm_num)
  nlinarith

lemma kappaT_nonneg {Q T : ℝ} (hQ : 1 < Q) (hT : 1 ≤ T) : 0 ≤ kappaT Q T :=
  div_nonneg (Real.log_nonneg hT) (Real.log_pos hQ).le

lemma kappaT_le {Q T κ : ℝ} (hQ : 1 < Q) (hT : 0 < T) (h : T ≤ Q ^ κ) : kappaT Q T ≤ κ := by
  unfold kappaT
  rw [div_le_iff₀ (Real.log_pos hQ)]
  have := Real.log_le_log hT h
  rwa [Real.log_rpow (by linarith)] at this

lemma le_rpow_of_kappaT_le {Q T κ : ℝ} (hQ : 1 < Q) (hT : 0 < T) (h : kappaT Q T ≤ κ) :
    T ≤ Q ^ κ := by
  unfold kappaT at h
  rw [div_le_iff₀ (Real.log_pos hQ)] at h
  have hQκ : 0 < Q ^ κ := Real.rpow_pos_of_pos (by linarith) κ
  rw [← Real.log_rpow (by linarith)] at h
  exact (Real.log_le_log_iff hT hQκ).mp h

/-! ### The band constant at polynomial height -/

/-- **The band constant** (port of `Families.bandLS_of_MV`). From the multiplicative large sieve (with
constant `C₀`, no restriction on the position of the interval) and `lem:WH`: for intervals of
`K ≤ Q^{5/4} ≤ Q²` integers **anywhere**, `Λ_mult(K) ≤ w_max C₀ (Q² + K) ≤ 2 C₀ w_max Q²`, and
`H ≥ (1 − o(1)) ℰ I_w Q²`. -/
theorem bandLSH_of_MV (hMV : MV_LargeSieve) (hWH : lemWH_Statement) (W : Weight) :
    ∃ Cband : ℝ, 1 ≤ Cband ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → BandLSH W ε Cband := by
  obtain ⟨C₀, hmult, -⟩ := hMV
  have hE : 0 < Ecal * W.Iw := mul_pos Ecal_pos W.Iw_pos
  set C₁ := max C₀ 0 with hC₁
  have hC₁0 : 0 ≤ C₁ := le_max_right _ _
  set A := 2 * C₁ * W.wmax / (Ecal * W.Iw) with hA
  have hA0 : 0 ≤ A := div_nonneg (by have := W.wmax_nonneg; positivity) hE.le
  refine ⟨A + 1, by linarith, fun ε _ _ δ hδ => ?_⟩
  have hκ : A / (A + 1) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  obtain ⟨Q₁, hQ₁⟩ := Filter.eventually_atTop.1 (H_lower_eventually hWH W hκ)
  refine ⟨max Q₁ 1, fun Q hQ K hK N₀ _ x => ?_⟩
  have hQ1 : 1 ≤ Q := le_of_max_le_right hQ
  have hHl := hQ₁ Q (le_of_max_le_left hQ)
  have hx : 0 ≤ normSq (intervalZ N₀ K) x := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hK2 : (K : ℝ) ≤ Q ^ 2 := by
    calc (K : ℝ) ≤ Q ^ (5 / 4 : ℝ) := hK
      _ ≤ Q ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
      _ = Q ^ 2 := by norm_cast
  have hmv := hmult Q hQ1 N₀ K x
  have hC : C₀ * (Q ^ 2 + K) * normSq (intervalZ N₀ K) x ≤
      C₁ * (2 * Q ^ 2) * normSq (intervalZ N₀ K) x := by
    apply mul_le_mul_of_nonneg_right _ hx
    calc C₀ * (Q ^ 2 + K) ≤ C₁ * (Q ^ 2 + K) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ C₁ * (2 * Q ^ 2) := mul_le_mul_of_nonneg_left (by linarith) hC₁0
  have hAA : (A + 1) * (A / (A + 1)) = A := by field_simp
  have hAE : A * (Ecal * W.Iw) = 2 * C₁ * W.wmax := by
    rw [hA, div_mul_cancel₀ _ hE.ne']
  have hH0 : 0 ≤ W.H Q := W.H_nonneg Q
  calc famForm W Q (intervalZ N₀ K) x
      ≤ W.wmax * (C₁ * (2 * Q ^ 2) * normSq (intervalZ N₀ K) x) :=
        (famForm_le_mult W Q _ x).trans
          (mul_le_mul_of_nonneg_left (hmv.trans hC) W.wmax_nonneg)
    _ = (A + 1) * (A / (A + 1) * (Ecal * W.Iw * Q ^ 2)) * normSq (intervalZ N₀ K) x := by
        rw [← mul_assoc (A + 1), hAA]
        calc W.wmax * (C₁ * (2 * Q ^ 2) * normSq (intervalZ N₀ K) x)
            = 2 * C₁ * W.wmax * Q ^ 2 * normSq (intervalZ N₀ K) x := by ring
          _ = A * (Ecal * W.Iw) * Q ^ 2 * normSq (intervalZ N₀ K) x := by rw [hAE]
          _ = _ := by ring
    _ ≤ (A + 1) * W.H Q * normSq (intervalZ N₀ K) x := by
        apply mul_le_mul_of_nonneg_right _ hx
        exact mul_le_mul_of_nonneg_left hHl (by linarith)
    _ ≤ (A + 1 + δ) * W.H Q * normSq (intervalZ N₀ K) x := by
        apply mul_le_mul_of_nonneg_right _ hx
        exact mul_le_mul_of_nonneg_right (by linarith) hH0

/-! ### The fixed-data assembly -/

lemma MfrakH_nonneg (P : HSetup) (W : Weight) (Q T τ₀ : ℝ) : 0 ≤ P.Mfrak W Q T τ₀ :=
  famSum_nonneg W Q _ fun _ _ =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **Fixed-data assembly** (port of `Families.assembly_fixed`). For fixed cell data `P` and a smooth
profile `c ≥ 1` satisfying the profile bound, `prop:zeroH` + `prop:secondH` + the lower half of
`lem:RvMH` give, for every `δ > 0` and all large `Q`, uniformly in the cell:
`N^s_0, N^*_0 ≥ (X − δ) N` and `N_d ≥ ((1+X)/2 − δ) N`, `X = P.certValue c`. -/
theorem assembly_fixedH (hZ : propZeroH_Statement) (hRvM : lemRvMH_lower_Statement)
    (hS : propSecondH_Statement) (P : HSetup) (W : Weight) (c : ℝ → ℝ)
    (hc : ContDiff ℝ ∞ c) (hc1 : ∀ α, 1 ≤ c α) (hprof : P.ProfileBoundH W c) :
    ∀ δ : ℝ, 0 < δ → ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ P.heights Q,
      (P.certValue c - δ) * Nfam W Q T ≤ Ns0 W Q T ∧
      (P.certValue c - δ) * Nfam W Q T ≤ Nstar0 W Q T ∧
      ((1 + P.certValue c) / 2 - δ) * Nfam W Q T ≤ Nd W Q T := by
  intro δ hδ
  set Y := (1 - 2 * P.θ) *
    Qf (fun α => c α * min α (1 + 2 * P.ε₃)) (fun x => P.vfun (x / P.lam) / (P.lam * P.aInt))
    with hY
  have hX : P.certValue c = 2 - 8 * P.θ - Y := rfl
  have hδ3 : 0 < δ / 3 := by positivity
  obtain ⟨Q₁, hQ₁⟩ := hS P W 0 c hc hc1 hprof (δ / 3) hδ3
  obtain ⟨Cz, Q₂, hQ₂⟩ := hZ P W 0 1 (δ / 3) one_pos hδ3
  obtain ⟨Q₃, hQ₃⟩ := hRvM W P.a0 P.kc P.a0_pos P.kc_pos (1 / 2) (by norm_num)
  set s := max Y 0 + δ / 3 with hs
  have hs0 : 0 ≤ s := by have := le_max_right Y 0; linarith
  set K := |Cz| * Real.sqrt s with hK
  have hK0 : 0 ≤ K := mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  set L₀ := max (max (3 * K / δ) (4 * Real.pi)) 1 with hL₀
  refine ⟨max (max Q₁ Q₂) (max Q₃ (Real.exp L₀)), fun Q hQ T hT => ?_⟩
  have hQ1 : Q₁ ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hQ
  have hQ2 : Q₂ ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hQ
  have hQ3 : Q₃ ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hQ
  have hQ4 : Real.exp L₀ ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hQ
  have hQpos : 0 < Q := lt_of_lt_of_le (Real.exp_pos _) hQ4
  have hlog : L₀ ≤ Real.log Q := by
    rw [← Real.log_exp L₀]; exact Real.log_le_log (Real.exp_pos _) hQ4
  have hlog1 : 1 ≤ Real.log Q := le_trans (le_max_right _ _) hlog
  have hlog4π : 4 * Real.pi ≤ Real.log Q :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hlog
  have hlogK : 3 * K / δ ≤ Real.log Q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hlog
  have hlogpos : 0 < Real.log Q := by linarith
  -- the three inputs at `(Q, T)`
  have hM := hQ₁ Q hQ1 T hT
  have hZQ := hQ₂ Q hQ2 T hT
  simp only at hZQ
  have hR := hQ₃ Q hQ3 T hT
  set N := Nfam W Q T with hN
  set M := P.Mfrak W Q T 0 with hMdef
  set H := W.H Q with hH
  have hN0 : 0 ≤ N := Nfam_nonneg W Q T
  have hM0 : 0 ≤ M := MfrakH_nonneg P W Q T 0
  have hH0 : 0 ≤ H := W.H_nonneg Q
  -- `T ≥ 1`, `ℓ_* ≥ ℓ`
  have hT1 : 1 ≤ T := le_trans (Real.one_le_rpow hlog1 P.a0_pos.le) hT.1
  have hellS : Real.log Q ≤ ellS Q T := by
    unfold ellS
    exact Real.log_le_log hQpos (le_mul_of_one_le_right hQpos.le hT1)
  -- `H ≤ N` (lower half of `lem:RvMH`)
  have hHN : H ≤ N := by
    have hellS0 : 0 ≤ ellS Q T := by linarith
    have hTL : 4 * Real.pi ≤ T * ellS Q T :=
      calc 4 * Real.pi ≤ Real.log Q := hlog4π
        _ ≤ ellS Q T := hellS
        _ = 1 * ellS Q T := (one_mul _).symm
        _ ≤ T * ellS Q T := mul_le_mul_of_nonneg_right hT1 hellS0
    have hpi : 0 < Real.pi := Real.pi_pos
    have h1 : H ≤ (1 - 1 / 2) * (H * T * ellS Q T / (2 * Real.pi)) := by
      rw [show (1 - 1 / 2 : ℝ) * (H * T * ellS Q T / (2 * Real.pi)) =
        H * (T * ellS Q T / (4 * Real.pi)) by field_simp; ring]
      have : 1 ≤ T * ellS Q T / (4 * Real.pi) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      exact le_mul_of_one_le_right hH0 this
    linarith
  -- `𝔐 ≤ s N`
  have hMs : M ≤ s * N := by
    have h1 : Y * N ≤ max Y 0 * N := mul_le_mul_of_nonneg_right (le_max_left Y 0) hN0
    have h2 : s * N = max Y 0 * N + δ / 3 * N := by rw [hs]; ring
    rw [h2]
    linarith
  -- `√(H𝔐) ≤ √s N`
  have hsqrt : Real.sqrt (H * M) ≤ Real.sqrt s * N := by
    have hHM : H * M ≤ N ^ 2 * s :=
      calc H * M ≤ N * M := mul_le_mul_of_nonneg_right hHN hM0
        _ ≤ N * (s * N) := mul_le_mul_of_nonneg_left hMs hN0
        _ = N ^ 2 * s := by ring
    calc Real.sqrt (H * M) ≤ Real.sqrt (N ^ 2 * s) := Real.sqrt_le_sqrt hHM
      _ = Real.sqrt (N ^ 2) * Real.sqrt s := Real.sqrt_mul (sq_nonneg N) s
      _ = Real.sqrt s * N := by rw [Real.sqrt_sq hN0, mul_comm]
  -- the error term of `prop:zeroH`
  have herr : Cz * Real.log Q ^ (-(1 : ℝ)) * Real.sqrt (H * M) ≤ δ / 3 * N := by
    rw [Real.rpow_neg_one]
    have hinv : 0 ≤ (Real.log Q)⁻¹ := inv_nonneg.mpr hlogpos.le
    have hKδ : K * (Real.log Q)⁻¹ ≤ δ / 3 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hlogpos]
      rw [div_le_iff₀ hδ] at hlogK
      linarith
    calc Cz * (Real.log Q)⁻¹ * Real.sqrt (H * M)
        ≤ |Cz| * (Real.log Q)⁻¹ * Real.sqrt (H * M) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hinv)
            (Real.sqrt_nonneg _)
      _ ≤ |Cz| * (Real.log Q)⁻¹ * (Real.sqrt s * N) :=
          mul_le_mul_of_nonneg_left hsqrt (mul_nonneg (abs_nonneg _) hinv)
      _ = K * (Real.log Q)⁻¹ * N := by rw [hK]; ring
      _ ≤ δ / 3 * N := mul_le_mul_of_nonneg_right hKδ hN0
  obtain ⟨hz1, hz2, hz3⟩ := hZQ
  have hδN : 0 ≤ δ * N := mul_nonneg hδ.le hN0
  rw [hX]
  refine ⟨?_, ?_, ?_⟩
  · linarith only [hz1, hM, herr, hδN]
  · linarith only [hz2, hM, herr, hδN]
  · linarith only [hz3, hM, herr, hδN]

/-! ### The one-cell theorem -/

/-- **Glue theorem for one cell** (port of `Families.thmMain_of_parts`; §9.4, proof of Theorem 9.20):
`lem:CTlimit` gives `C_T^+(w) ≤ 1 + ε/3` for `η ≤ η₀(ε)` (the choice of `η₀` involves neither `T` nor
the cell); `prop:sharpLS` gives `C_T^+ ≥ 1`; the band constant comes from the large sieve
(`bandLSH_of_MV`); `prop:TIsharpH` gives the profile bound; `prop:secondH` (via
`SecondMomentAssemblyH`) and `prop:zeroH` give `N^s_0 ≥ (P.certValue C̃ − o(1)) N`;
`assemblyLimitH` gives `P.certValue C̃ ≥ p(β(κc); F_{C_T^+}) − ε/3`; `lem:pLipH` gives
`p(β(κc); F_{C_T^+}) ≥ p(β(κc)) − ε/3`. -/
theorem thmHcell_of_parts
    (hCT : lemCTlimit_Statement) (hSharp : propSharpLS_Statement)
    (hTI : propTIsharpH_Statement) (hB2 : lemB2H_Statement) (hMrat : eqBMratH_Statement)
    (hLim : assemblyLimitH_Statement) (hLip : lemPLipH_Statement) (hMV : MV_LargeSieve)
    (hStir : StirlingDigamma) (hWH : lemWH_Statement)
    (hZero : propZeroH_Statement ∧ lemRvMH_lower_Statement) (hSec : SecondMomentAssemblyH) :
    thmHcell_Statement := by
  obtain ⟨hZ, hRvM⟩ := hZero
  have hS : propSecondH_Statement := hSec hMV hStir hWH hRvM hB2 hMrat
  intro ε hε
  -- the choice of `η₀(ε)`: `L_η = log(1/η) ≥ max(3, 249/ε)` (independent of `a₀` and the cell)
  set M : ℝ := max 3 (249 / ε) with hMdef
  have hM3 : 3 ≤ M := le_max_left _ _
  have hMε : 249 / ε ≤ M := le_max_right _ _
  refine ⟨Real.exp (-M), Real.exp_pos _, fun a0 kc ha0 hkc η hη hηη₀ W hW => ?_⟩
  have hL : M ≤ Leta η := by
    unfold Leta
    rw [one_div, Real.log_inv]
    have := Real.log_le_log hη hηη₀
    rw [Real.log_exp] at this
    linarith
  have hLpos : 0 < Leta η := by linarith
  have hkey : ∀ k : ℝ, k ≤ 83 → k / Leta η ≤ ε / 3 := by
    intro k hk
    rw [div_le_iff₀ hLpos]
    have h83 : ε / 3 * (249 / ε) = 83 := by field_simp; ring
    have h249 : 249 / ε ≤ Leta η := hMε.trans hL
    calc k ≤ 83 := hk
      _ = ε / 3 * (249 / ε) := h83.symm
      _ ≤ ε / 3 * Leta η := mul_le_mul_of_nonneg_left h249 (by positivity)
  -- `C_T^+(w) ≤ 1 + ε/3` (`lem:CTlimit`)
  have hCTle : CTp W ≤ ENNReal.ofReal (1 + ε / 3) := by
    rcases hW with hW | hW
    · refine (hCT.2.1 W η hW (by linarith)).trans (ENNReal.ofReal_le_ofReal ?_)
      linarith [hkey 42 (by norm_num)]
    · refine (hCT.2.2 W η hW (by linarith)).trans (ENNReal.ofReal_le_ofReal ?_)
      linarith [hkey 83 le_rfl]
  have hCTne : CTp W ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hCTle
  set C := (CTp W).toReal with hCdef
  have hCle : C ≤ 1 + ε / 3 := ENNReal.toReal_le_of_le_ofReal (by positivity) hCTle
  -- `C_T^+(w) ≥ 1` (remark after `prop:sharpLS`)
  have hC1 : 1 ≤ C := CTp_ge_one hSharp hWH W hCTne
  -- the band constant (intervals anywhere) and the fixed data of the cell (`assemblyLimitH`)
  obtain ⟨Cband, hCband1, hband⟩ := bandLSH_of_MV hMV hWH W
  set Cmax := max Cband C with hCmax
  obtain ⟨P, ε', hPa0, hPkc, hε'0, hε'3, hε'1, hε'8, hlim⟩ :=
    hLim a0 kc ha0 hkc C Cmax hC1 (le_max_right _ _) (ε / 3) (by positivity)
  -- the profile `C̃_ε'` and the profile bound (`prop:TIsharpH`)
  obtain ⟨hrange, hbelow, hbandv, habove, hfar⟩ :=
    bandProfile_spec (Cmax := Cmax) hε'0 hC1 (le_max_right _ _)
  have hsmooth : ContDiff ℝ ∞ (bandProfile Cmax C ε') := bandProfile_contDiff _ _ _
  have hε'8' : ε' ≤ 1 / (8 * (1 + P.kc)) := by rw [hPkc]; exact hε'8
  have hprof : P.ProfileBoundH W (bandProfile Cmax C ε') :=
    hTI P W hCTne ε' hε'0 hε'3 hε'1 hε'8' Cband hCband1 (hband ε' hε'0 (by linarith))
      (bandProfile Cmax C ε') hsmooth hrange hbelow
      (fun α h1 h2 => by rw [hbandv α h1 h2]; exact le_max_left _ _) habove hfar
  -- the certified value and `lem:pLipH` at `β = β(κc)`
  have hcert : pB (betaK kc) C - ε / 3 ≤ P.certValue (bandProfile Cmax C ε') :=
    hlim _ hsmooth.continuous hrange hbelow hfar
  have hβ1 : 1 ≤ betaK kc := (one_lt_betaK hkc.le).le
  have hβ2 : betaK kc ≤ 2 := betaK_le_two hkc.le
  have hLip' := (hLip (betaK kc) hβ1 hβ2 1 C le_rfl hC1).2
  have hX : pB (betaK kc) 1 - 2 * (ε / 3) ≤ P.certValue (bandProfile Cmax C ε') := by linarith
  -- `prop:zeroH` + `prop:secondH` at the fixed data
  have hfix := assembly_fixedH hZ hRvM hS P W (bandProfile Cmax C ε') hsmooth
    (fun α => (hrange α).1) hprof
  intro ε'' hε''
  obtain ⟨Q₀, hQ₀⟩ := hfix ε'' hε''
  refine ⟨Q₀, fun Q hQ T hT => ?_⟩
  have hT' : T ∈ P.heights Q := by
    unfold HSetup.heights; rw [hPa0, hPkc]; exact hT
  obtain ⟨h1, h2, h3⟩ := hQ₀ Q hQ T hT'
  have hN0 := Nfam_nonneg W Q T
  refine ⟨?_, ?_, ?_⟩
  · exact le_trans (mul_le_mul_of_nonneg_right (by linarith) hN0) h1
  · exact le_trans (mul_le_mul_of_nonneg_right (by linarith) hN0) h2
  · exact le_trans (mul_le_mul_of_nonneg_right (by linarith) hN0) h3

/-! ### The κ-cells (§9.4) -/

/-- **The κ-cells argument** ((9.16)–(9.17)). From the one-cell theorem (at accuracy `ε/2`) for the
cell tops `κ^{(j)} = jκ₁/m` (`m > 4κ₁/ε`) and `lem:Mbeta`: if `κ_T ∈ [κ^{(j-1)}, κ^{(j)}]` then
`p(β(κ_T)) ≤ p(β(κ^{(j)})) + 2(β(κ_T)/β(κ^{(j)}) − 1) ≤ p(β(κ^{(j)})) + ε/4`, and `T ≤ Q^{κ^{(j)}}`.
Finitely many cells, so one `Q₀` works for all `T ∈ [ℓ^{a₀}, Q^{κ₁}]`. -/
theorem thmH_of_cells (hcell : thmHcell_Statement) (hM : lemMbeta_Statement) :
    ∀ ε : ℝ, 0 < ε → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ (a0 κ1 : ℝ), 0 < a0 → 0 < κ1 →
      ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ W : Weight, (W.w = wSharpFun η ∨ W.w = wSmoothFun η) →
        ProportionsAtLeastH W a0 κ1 (fun κ => pB (betaK κ) 1 - ε) := by
  intro ε hε
  obtain ⟨η₀, hη₀, hc⟩ := hcell (ε / 2) (by positivity)
  refine ⟨η₀, hη₀, fun a0 κ1 ha0 hκ1 η hη hηη₀ W hW => ?_⟩
  -- the mesh `h = κ₁/m ≤ ε/4`
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 4 * κ1 / ε < m := exists_nat_gt _
  have hm0 : 0 < (m : ℝ) := lt_of_le_of_lt (by positivity) hm
  set h := κ1 / (m : ℝ) with hh
  have hh0 : 0 < h := div_pos hκ1 hm0
  have hhε : h ≤ ε / 4 := by
    rw [hh, div_le_iff₀ hm0]
    rw [div_lt_iff₀ hε] at hm
    nlinarith
  intro ε' hε'
  -- one `Q₀` per cell top `j h`, `1 ≤ j`
  have hQj : ∀ j : ℕ, ∃ Q₀ : ℝ, 1 ≤ j → ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ cellHeights a0 ((j : ℝ) * h) Q,
      (pB (betaK ((j : ℝ) * h)) 1 - ε / 2 - ε') * Nfam W Q T ≤ Ns0 W Q T ∧
      (pB (betaK ((j : ℝ) * h)) 1 - ε / 2 - ε') * Nfam W Q T ≤ Nstar0 W Q T ∧
      ((1 + (pB (betaK ((j : ℝ) * h)) 1 - ε / 2)) / 2 - ε') * Nfam W Q T ≤ Nd W Q T := by
    intro j
    by_cases hj : 1 ≤ j
    · have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
      have hjh : 0 < (j : ℝ) * h := mul_pos (by linarith) hh0
      obtain ⟨Q₀, hQ₀⟩ := hc a0 ((j : ℝ) * h) ha0 hjh η hη hηη₀ W hW ε' hε'
      exact ⟨Q₀, fun _ => hQ₀⟩
    · exact ⟨0, fun h1 => absurd h1 hj⟩
  choose Q0f hQ0f using hQj
  refine ⟨max (Real.exp 1) (∑ j ∈ Finset.range (m + 1), |Q0f j|), fun Q hQ T hT => ?_⟩
  -- `Q ≥ e`, so `log Q ≥ 1`, `T ≥ 1`, `0 ≤ κ_T ≤ κ₁`
  have hQe : Real.exp 1 ≤ Q := le_trans (le_max_left _ _) hQ
  have he1 : (1 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (one_ne_zero (α := ℝ)); linarith
  have hQ1 : 1 < Q := lt_of_lt_of_le he1 hQe
  have hlogQ : 1 ≤ Real.log Q := by
    have := Real.log_le_log (Real.exp_pos 1) hQe
    rwa [Real.log_exp] at this
  have hT1 : 1 ≤ T := le_trans (Real.one_le_rpow hlogQ ha0.le) hT.1
  have hTpos : 0 < T := by linarith
  set κ := kappaT Q T with hκdef
  have hκ0 : 0 ≤ κ := kappaT_nonneg hQ1 hT1
  have hκ1' : κ ≤ κ1 := kappaT_le hQ1 hTpos hT.2
  -- the cell `j = max 1 ⌈κ/h⌉₊`
  set j : ℕ := max 1 ⌈κ / h⌉₊ with hjdef
  have hj1 : 1 ≤ j := le_max_left _ _
  have hκh0 : 0 ≤ κ / h := div_nonneg hκ0 hh0.le
  have hjle : (j : ℝ) ≤ κ / h + 1 := by
    rcases le_total 1 ⌈κ / h⌉₊ with hc1 | hc1
    · have : j = ⌈κ / h⌉₊ := max_eq_right hc1
      rw [this]
      exact (Nat.ceil_lt_add_one hκh0).le
    · have : j = 1 := max_eq_left hc1
      rw [this]; push_cast; linarith
  have hκj : κ ≤ (j : ℝ) * h := by
    have h1 : κ / h ≤ (⌈κ / h⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈κ / h⌉₊ : ℝ) ≤ j := by exact_mod_cast le_max_right _ _
    have := h1.trans h2
    rwa [div_le_iff₀ hh0] at this
  have hjκ : (j : ℝ) * h - κ ≤ h := by
    have := mul_le_mul_of_nonneg_right hjle hh0.le
    rw [add_mul, div_mul_cancel₀ _ hh0.ne', one_mul] at this
    linarith
  have hjm : j ≤ m := by
    apply max_le (by exact_mod_cast (show (1 : ℝ) ≤ m by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0] at hm0; simp at hm0
      · exact_mod_cast h0))
    apply Nat.ceil_le.mpr
    rw [div_le_iff₀ hh0, hh]
    have hmh : (m : ℝ) * (κ1 / m) = κ1 := by field_simp
    rw [hmh]
    exact hκ1'
  -- `T` lies in the cell `j`
  have hTj : T ∈ cellHeights a0 ((j : ℝ) * h) Q := ⟨hT.1, le_rpow_of_kappaT_le hQ1 hTpos hκj⟩
  have hQj : Q0f j ≤ Q := by
    have hmem : j ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hjm)
    have h1 : Q0f j ≤ |Q0f j| := le_abs_self _
    have h2 : |Q0f j| ≤ ∑ i ∈ Finset.range (m + 1), |Q0f i| :=
      Finset.single_le_sum (f := fun i => |Q0f i|) (fun i _ => abs_nonneg _) hmem
    exact h1.trans (h2.trans (le_trans (le_max_right _ _) hQ))
  obtain ⟨h1, h2, h3⟩ := hQ0f j hj1 Q hQj T hTj
  -- `lem:Mbeta`: `p(β(κ_T)) ≤ p(β(jh)) + ε/4`
  have hjh0 : 0 ≤ (j : ℝ) * h := le_trans hκ0 hκj
  have hMb := (hM 1 le_rfl (betaK ((j : ℝ) * h)) (betaK κ) (one_lt_betaK hjh0).le
    (betaK_anti hκ0 hκj) (betaK_le_two hκ0)).2
  have hratio := betaK_ratio_le hκ0 hκj
  have hp : pB (betaK κ) 1 ≤ pB (betaK ((j : ℝ) * h)) 1 + ε / 4 := by
    have : 2 * (betaK κ / betaK ((j : ℝ) * h) - 1) ≤ ε / 4 := by nlinarith
    linarith
  have hN0 := Nfam_nonneg W Q T
  show ((pB (betaK κ) 1 - ε) - ε') * Nfam W Q T ≤ Ns0 W Q T ∧
    ((pB (betaK κ) 1 - ε) - ε') * Nfam W Q T ≤ Nstar0 W Q T ∧
    ((1 + (pB (betaK κ) 1 - ε)) / 2 - ε') * Nfam W Q T ≤ Nd W Q T
  refine ⟨?_, ?_, ?_⟩
  · exact le_trans (mul_le_mul_of_nonneg_right (by linarith) hN0) h1
  · exact le_trans (mul_le_mul_of_nonneg_right (by linarith) hN0) h2
  · exact le_trans (mul_le_mul_of_nonneg_right (by linarith) hN0) h3

/-! ### The headline from its parts -/

/-- **Glue theorem for Theorem 1.4(a)** (proved; standard axioms only): the component statements imply
`thmH_Statement`. -/
theorem thmH_of_parts
    (hCT : lemCTlimit_Statement) (hSharp : propSharpLS_Statement)
    (hTI : propTIsharpH_Statement) (hB2 : lemB2H_Statement) (hMrat : eqBMratH_Statement)
    (hLim : assemblyLimitH_Statement) (hLip : lemPLipH_Statement) (hMb : lemMbeta_Statement)
    (hCert : certH_Statement) (hMV : MV_LargeSieve) (hStir : StirlingDigamma)
    (hWH : lemWH_Statement) (hZero : propZeroH_Statement ∧ lemRvMH_lower_Statement)
    (hSec : SecondMomentAssemblyH) : thmH_Statement :=
  ⟨thmH_of_cells (thmHcell_of_parts hCT hSharp hTI hB2 hMrat hLim hLip hMV hStir hWH hZero hSec) hMb,
    hCert⟩

end Families.Hybrid
