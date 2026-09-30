/-
# Package TS: Proposition 9.18 (`prop:TIsharpH`), the band device at polynomial height

`TS.propTIsharpH54_proof : TS.propTIsharpH54_Statement` — the statement `propTIsharpH_Statement` with
the band hypothesis at the length `Q^{5/4}` of Lemma 9.1 (S2) (`TS.BandLSH54`; see `STATEMENTS-H.md` §5). No hypotheses beyond the statement's: the large sieve
(`Families.Hyp.MV_LargeSieve_proof`) and `lem:WH` (`Families.lemWH`) are theorems.

Route (§9.3, Steps 0–5; the families proof `Families.Phase3.C.propTIsharp_proof` with the changes
listed here):
* localisation at `δ = T^{−1+ε₅}`, `ε₅ = min(ε, ε₁)/(4(1+κc))` (so `δ ≤ 1/4` and `T^{−1} ≤ δ` once
  `T ≥ ℓ^{a₀}` is large), with a fixed splitting parameter `κ = η/10` (`η = min(δ', 1)`) in
  `eqC:seminorm`, and `κ_loc = T^{−ε₅/2} ≤ κ` so that `cor:tails` controls `(1+κ^{−1}) ∫ g x^{t*}Δx^t`;
* the pointwise bound is proved for `u < L` only (`g = 0` on `|u| ≥ L`), where (S2) gives the
  lengths `K(u) ≤ 5δe^u + 1 ≤ Q^{1−ε/2}, Q^{5/4}, Q^{2−ε₁/2}` in the three regimes, measured in units
  of `ℓ_* = log(QT)`;
* regime (iii) applies the sharp large sieve, the multiplicative large sieve (`M = 2w_max C₀Q²`) and
  the additive large sieve on the **localisation interval** (never on `[1, Y]`, which has
  `Y ≤ Q^{2−ε₁}T^{1−ε₁}` integers); the families bound `M_le_sq` is not used;
* `R_max ≤ E₀ = ⌊2Y/(QT)⌋` (`Rj_le_E0H`) and `E₀ ≤ 2Q^{1−ε₁}` from (S1), so the low levels cost
  `≪ Q^{2−ε₁/2}`; the high levels are the Farey bound `farey_sharpH`;
* the prime powers of regime (iii) lie on `n > (QT)^{1+ε}/2`, so `∑ a_pp² ≤ 4μ³ℓ_*³Q^{−ε}`;
* error target `δ' H|J|L²ℓ_*`: tails `2 · δ'/4` (`cor:tails`), the other three terms `≤ 3 tgt Q²|J|ℓ_*³`
  with `4 tgt Q²|J|ℓ_*³ ≤ δ'/2 · H|J|L²ℓ_*` (`err_total`).
-/
import FamiliesH.TS.Step5

noncomputable section

open scoped BigOperators ContDiff ENNReal
open Set MeasureTheory Filter Topology

namespace Families.Hybrid

open Families Families.Phase3.C

namespace TS

/-- For `T ≥ B`: `4 ≤ T^{1−ε₅}` (i.e. `δ ≤ 1/4`) and `κ^{−1} ≤ T^{ε₅/2}` (i.e. `κ_loc ≤ κ`). -/
lemma exists_T_threshold {ε₅ κ : ℝ} (hε₅ : 0 < ε₅) (hε₅1 : ε₅ < 1) (_hκ : 0 < κ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ T : ℝ, B ≤ T → 4 ≤ T ^ (1 - ε₅) ∧ κ⁻¹ ≤ T ^ (ε₅ / 2) := by
  have h1 := (tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 - ε₅)).eventually_ge_atTop (4 : ℝ)
  have h2 := (tendsto_rpow_atTop (by positivity : (0 : ℝ) < ε₅ / 2)).eventually_ge_atTop κ⁻¹
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.1 (h1.and h2)
  exact ⟨max B 1, le_max_right _ _, fun T hT => hB T (le_of_max_le_left hT)⟩

set_option maxHeartbeats 400000 in
/-- **Proposition 9.18** (`prop:TIsharpH`, the band device at polynomial height), with the band
hypothesis `Λ_mult(Q^{5/4}) ≤ (C_band + o(1))H` of the TeX. -/
theorem propTIsharpH54_proof : propTIsharpH54_Statement := by
  classical
  intro P W hCT ε hε hε3 _hεε₁ hε8 Cband hCband hband Ct _ hCtr _ hCtband hCtCT _ δ' hδ'
  have hkc := P.kc_pos
  have hε₁0 := P.ε₁_pos
  have hWH : lemWH_Statement := lemWH
  obtain ⟨C₀, hmult, hadd⟩ := Hyp.MV_LargeSieve_proof
  set C₀' := max C₀ 0 with hC₀'
  have hC₀'0 : 0 ≤ C₀' := le_max_right _ _
  -- the parameters `η`, `d`, `κ`
  set η := min δ' 1 with hη
  have hη0 : 0 < η := lt_min hδ' one_pos
  have hη1 : η ≤ 1 := min_le_right _ _
  have hηδ : η ≤ δ' := min_le_left _ _
  set d := η / 4 with hd
  set κ := η / 10 with hκ
  have hd0 : 0 < d := by positivity
  have hκ0 : 0 < κ := by positivity
  have hκ1 : κ ≤ 1 := by linarith
  have hfac : (1 + κ) ^ 3 * (1 + d) ≤ 1 + δ' := by
    have : (1 + κ) ^ 3 * (1 + d) ≤ 1 + η := by
      rw [hκ, hd]; nlinarith [sq_nonneg η, mul_pos hη0 hη0, pow_pos hη0 3, pow_pos hη0 4]
    linarith
  set CT := (CTp W).toReal with hCTdef
  have hSharpAll := propSharpLS hWH
  have hCT1 : 1 ≤ CT := CTp_ge_one hSharpAll hWH W hCT
  have hCt1 : ∀ α, 1 ≤ Ct α := fun α => (hCtr α).1
  -- the localisation exponent `ε₅` and the threshold for `T`
  set ε₅ := min ε P.ε₁ / (4 * (1 + P.kc)) with hε₅
  have hmin0 : 0 < min ε P.ε₁ := lt_min hε hε₁0
  have hε₅0 : 0 < ε₅ := by positivity
  have hε₅1 : ε₅ < 1 := by
    have : min ε P.ε₁ ≤ ε := min_le_left _ _
    rw [hε₅, div_lt_one (by positivity)]; linarith only [this, hε3, hkc]
  obtain ⟨B, hB1, hB⟩ := exists_T_threshold hε₅0 hε₅1 hκ0
  -- the components
  obtain ⟨Qsz, hsz⟩ := F.lemSizesH_proof P ε hε hε8
  obtain ⟨Cab, Qab, hCab0, hab⟩ := P.famForm_ab_closeH W 3 (by norm_num)
  obtain ⟨Qi, hi⟩ := short_interval_le hWH W (r := ε / 2) (by positivity) hd0
  obtain ⟨Qb, hb⟩ := hband d hd0
  obtain ⟨CF, QF, hCF0, hF⟩ := levelForm_xsSharpH P hadd W
  obtain ⟨cS, hcS⟩ := hSharpAll
  set ε' := min (P.ε₁ / 2) (1 / 2) with hε'
  have hε'0 : 0 < ε' := lt_min (by positivity) (by norm_num)
  have hε'1 : ε' ≤ P.ε₁ / 2 := min_le_left _ _
  obtain ⟨QS, hS⟩ := hcS ε' hε'0 (lt_of_le_of_lt (min_le_right _ _) (by norm_num)) W hCT
  obtain ⟨Cs, Qs, hCs0, hs⟩ := sum_sq_aSharp_le P.toPS
  obtain ⟨Cd, hCd0, hKd⟩ := 𝒦_diag_re_le P.toPS
  obtain ⟨Qt, htails⟩ := F.corTailsH_proof P W rhoLoc isLocCutoff_rhoLoc ε hε hε8 (δ' / 4)
    (by positivity)
  -- fixed-data quantities
  set lam := P.lam with hlam
  have hlam0 : 0 < lam := P.lam_pos
  set μ := (1 + P.ε₁) * lam with hμ
  have hμ0 : 0 < μ := by positivity
  set h₀ := Ecal * W.Iw / 2 with hh₀
  have hh₀0 : 0 < h₀ := by have := mul_pos Ecal_pos W.Iw_pos; positivity
  set ν := 6 * W.wtmax * W.η⁻¹ ^ 2 with hν
  have hν0 : 0 ≤ ν := by have := wtmax_nonneg W; positivity
  have hw0 := W.wmax_nonneg
  set bI := P.bInt with hbI
  have hbI0 : 0 ≤ bI := P.bInt_nonneg
  set Cn := 8 * (1 + μ) + Cs with hCn
  have hCn0 : 0 ≤ Cn := by positivity
  set CK := 2 * Real.pi * bI * lam + 2 * Cd with hCK
  have hCK0 : 0 ≤ CK := by positivity
  set θ₀ := 1 - 2 * P.θ with hθ₀
  have hθ₀0 : 1 / 2 < θ₀ := by have := P.θ_lt; linarith only [this, hθ₀]
  set tgt := δ' / 2 / 4 * h₀ * lam ^ 2 with htgt
  have htgt0 : 0 < tgt := by positivity
  set C₂ := 8 * (1 + κ⁻¹) * (5 * ν * C₀') * CK * Cn with hC₂
  set C₃ := (8 * (1 + κ⁻¹) * (ν * CF ^ 2) + Cab) * lam ^ 2 * P.aInt ^ 2 with hC₃
  set C₄ := (1 + κ⁻¹) * ((8 * (CT + 1) + 4 * C₀') * W.wmax) * CK * (4 * μ ^ 3) with hC₄
  set C₄' := C₄ * (1 + P.kc) with hC₄'
  have hC₂0 : 0 ≤ C₂ := by positivity
  have hC₄0 : 0 ≤ C₄ := by positivity
  have hC₄'0 : 0 ≤ C₄' := by positivity
  -- all the conditions on `Q`
  have hev : ∀ᶠ Q : ℝ in atTop,
      (Qsz ≤ Q ∧ Qab ≤ Q ∧ Qi ≤ Q ∧ Qb ≤ Q ∧ QF ≤ Q ∧ QS ≤ Q ∧ Qs ≤ Q ∧ Qt ≤ Q ∧
        Real.exp 1 ≤ Q) ∧
      (cS * ((W.Vw + W.wtmax * W.η⁻¹ ^ 2) / W.Iw * Q ^ (-ε' / 4) * Real.log Q ^ 3 +
        (Q ^ (-ε' / 2) + W.Vw / W.Iw * Q ^ (-(1 / 2 : ℝ))) * CT) ≤ d) ∧
      (1 / 2 * (Ecal * W.Iw * Q ^ 2) ≤ W.H Q) ∧ (1 < ε * Real.log Q) ∧ (2 ≤ Q ^ ε) ∧
      (B ≤ Real.log Q ^ P.a0) ∧
      (Q ^ (-(P.ε₁ / 2)) * (1 + Real.log Q) ^ 0 ≤ tgt / (C₂ + 1)) ∧
      (C₃ ≤ tgt / 2 * Q ^ 2) ∧
      (Q ^ (-ε) * (1 + Real.log Q) ^ 1 ≤ tgt / (C₄' + 1)) := by
    refine ((((eventually_ge_atTop Qsz).and (eventually_ge_atTop Qab)).and
      (eventually_ge_atTop Qi)).and (eventually_ge_atTop Qb) |>.and (eventually_ge_atTop QF)
      |>.and (eventually_ge_atTop QS) |>.and (eventually_ge_atTop Qs)
      |>.and (eventually_ge_atTop Qt) |>.and (eventually_ge_atTop (Real.exp 1))).mono ?_ |>.and ?_
    · rintro Q ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩
      exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    refine ((sharpLS_err_tendsto W cS hε'0 CT).eventually (ge_mem_nhds hd0)).and ?_
    refine (H_lower_eventually hWH W (κ := 1 / 2) (by norm_num)).and ?_
    refine ((Real.tendsto_log_atTop.const_mul_atTop hε).eventually_gt_atTop 1).and ?_
    refine ((tendsto_rpow_atTop hε).eventually_ge_atTop 2).and ?_
    refine (eventually_le_log_rpow P.a0_pos).and ?_
    refine (eventually_rpow_neg_mul_le (by positivity : 0 < P.ε₁ / 2) 0 (by positivity)).and ?_
    refine (eventually_le_mul_sq (by positivity)).and ?_
    exact eventually_rpow_neg_mul_le hε 1 (by positivity)
  obtain ⟨Q₀, hQ₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨Q₀, fun Q hQ T hT => ?_⟩
  obtain ⟨⟨hQsz, hQab, hQi, hQb, hQF, hQS, hQs, hQt, hQe⟩, hSerr, hHl, hεℓ, hQε, hBQ, hE2, hE3,
    hE4⟩ := hQ₀ Q hQ
  -- basic facts on `Q`, `T`, `ℓ_*`
  have hQ1 : 1 < Q :=
    lt_of_lt_of_le (by have := Real.add_one_lt_exp (x := 1) one_ne_zero; linarith only [this]) hQe
  have hQ0 : 0 < Q := lt_trans one_pos hQ1
  have hlogQ1 : 1 ≤ Real.log Q := by
    have := Real.log_le_log (Real.exp_pos _) hQe; rwa [Real.log_exp] at this
  have hT1 : 1 ≤ T := one_le_T_of_mem P hQe hT
  have hT0 : 0 < T := lt_of_lt_of_le one_pos hT1
  obtain ⟨hT4, hTκ⟩ := hB T (hBQ.trans hT.1)
  have hQT : Q ≤ Q * T := le_mul_of_one_le_right hQ0.le hT1
  have hQT1 : 1 < Q * T := lt_of_lt_of_le hQ1 hQT
  have hQT0 : 0 < Q * T := lt_trans one_pos hQT1
  obtain ⟨-, -, -, hQTM⟩ := P.cell_bounds hQ1.le hT1 hT
  set ℓ := ellS Q T with hℓdef
  have hℓQ : Real.log Q ≤ ℓ := Real.log_le_log hQ0 hQT
  have hℓ1 : 1 ≤ ℓ := hlogQ1.trans hℓQ
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le one_pos hℓ1
  have hℓup : ℓ ≤ (1 + P.kc) * Real.log Q := by
    have := Real.log_le_log hQT0 hQTM
    rwa [Real.log_rpow hQ0] at this
  have hεℓ' : 1 < ε * ℓ := lt_of_lt_of_le hεℓ (mul_le_mul_of_nonneg_left hℓQ hε.le)
  have hH : 0 ≤ W.H Q := W.H_nonneg Q
  have hHl' : h₀ * Q ^ 2 ≤ W.H Q := by rw [hh₀]; linarith only [hHl]
  have hHu : W.H Q ≤ W.wmax * Q ^ 2 := sum_omega_card_le W hQ1.le
  -- the localisation scale `δ = T^{−1+ε₅}`
  set δ := T ^ (-1 + ε₅) with hδdef
  have hδ0 : 0 < δ := Real.rpow_pos_of_pos hT0 _
  have hδinv : δ⁻¹ = T ^ (1 - ε₅) := by
    rw [hδdef, ← Real.rpow_neg hT0.le]; congr 1; ring
  have hδ4 : δ ≤ 1 / 4 := by
    have h4 : (4 : ℝ) ≤ δ⁻¹ := by rw [hδinv]; exact hT4
    have := mul_le_mul_of_nonneg_left h4 hδ0.le
    rw [mul_inv_cancel₀ hδ0.ne'] at this
    linarith only [this]
  have hδ1 : 1 ≤ δ⁻¹ := by rw [hδinv]; exact Real.one_le_rpow hT1 (by linarith only [hε₅1])
  have hδT : δ⁻¹ ≤ T := by
    rw [hδinv]
    calc T ^ (1 - ε₅) ≤ T ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hT1 (by linarith only [hε₅0])
      _ = T := Real.rpow_one T
  have hκloc : 1 + κ⁻¹ ≤ 1 + (T ^ (-(ε₅ / 2)))⁻¹ := by
    rw [Real.rpow_neg hT0.le, inv_inv]; linarith only [hTκ]
  -- the size facts
  obtain ⟨⟨hS1a, -⟩, hS2, -, -⟩ := hsz Q hQsz T hT
  have hQsplit : Q ^ (2 - P.ε₁ / 2) = Q ^ 2 * Q ^ (-(P.ε₁ / 2)) := by
    rw [show (2 : ℝ) - P.ε₁ / 2 = ((2 : ℕ) : ℝ) + (-(P.ε₁ / 2)) by push_cast; ring,
      Real.rpow_add hQ0, Real.rpow_natCast]
  have hQ2 : Q ^ (2 - P.ε₁ / 2) ≤ Q ^ 2 := by
    calc Q ^ (2 - P.ε₁ / 2) ≤ Q ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hQ1.le (by linarith only [hε₁0])
      _ = Q ^ 2 := by norm_cast
  have hQε' : Q ^ (2 - P.ε₁ / 2) ≤ Q ^ (2 - ε') :=
    Real.rpow_le_rpow_of_exponent_le hQ1.le (by linarith only [hε'1])
  have hQmε₁ : 0 ≤ Q ^ (-(P.ε₁ / 2)) := Real.rpow_nonneg hQ0.le _
  have hQmε : 0 ≤ Q ^ (-ε) := Real.rpow_nonneg hQ0.le _
  -- `E₀ = ⌊2Y/(QT)⌋ ≤ 2Q^{1−ε₁}` from (S1), hence `E₀² ≤ 4Q^{2−ε₁/2}`
  have hE0 : (⌊2 * P.Y Q T / (Q * T)⌋₊ : ℝ) ≤ 2 * Q ^ (1 - P.ε₁) := by
    have hY0 : 0 ≤ P.Y Q T := Real.rpow_nonneg (Real.exp_pos _).le _
    refine (Nat.floor_le (by positivity)).trans ?_
    rw [div_le_iff₀ hQT0]
    have hTe : T ^ (1 - P.ε₁) ≤ T := by
      calc T ^ (1 - P.ε₁) ≤ T ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hT1 (by linarith only [hε₁0])
        _ = T := Real.rpow_one T
    have hQs2 : Q ^ (2 - P.ε₁) = Q * Q ^ (1 - P.ε₁) := by
      rw [show (2 : ℝ) - P.ε₁ = 1 + (1 - P.ε₁) by ring, Real.rpow_add hQ0, Real.rpow_one]
    have h0 : 0 ≤ Q ^ (2 - P.ε₁) := by positivity
    calc 2 * P.Y Q T ≤ 2 * (Q ^ (2 - P.ε₁) * T ^ (1 - P.ε₁)) := by linarith only [hS1a]
      _ ≤ 2 * (Q ^ (2 - P.ε₁) * T) := by gcongr
      _ = 2 * Q ^ (1 - P.ε₁) * (Q * T) := by rw [hQs2]; ring
  have hE0sq : (⌊2 * P.Y Q T / (Q * T)⌋₊ : ℝ) ^ 2 ≤ 4 * (Q ^ 2 * Q ^ (-(P.ε₁ / 2))) := by
    have h0 : (0 : ℝ) ≤ ⌊2 * P.Y Q T / (Q * T)⌋₊ := Nat.cast_nonneg _
    have hsq : (Q ^ (1 - P.ε₁)) ^ 2 ≤ Q ^ 2 * Q ^ (-(P.ε₁ / 2)) := by
      rw [← hQsplit, ← Real.rpow_natCast (Q ^ (1 - P.ε₁)) 2, ← Real.rpow_mul hQ0.le]
      apply Real.rpow_le_rpow_of_exponent_le hQ1.le
      push_cast; linarith only [hε₁0]
    have := mul_le_mul hE0 hE0 h0 (by positivity)
    nlinarith only [this, hsq]
  -- the objects of the pointwise bound
  set x := (Q * T) ^ (1 + ε) / 2 with hx
  set M := 2 * W.wmax * C₀' * Q ^ 2 with hM
  set A₁ := 5 * ν * C₀' * (Q ^ 2 * Q ^ (-(P.ε₁ / 2))) with hA₁
  set A₂ := ν * CF ^ 2 with hA₂
  set ε₀ := Cab * Q ^ (-(3 : ℝ)) with hε₀
  set c₃ := CT + d with hc₃
  have hM0 : 0 ≤ M := by positivity
  have hA₁0 : 0 ≤ A₁ := by positivity
  have hA₂0 : 0 ≤ A₂ := by positivity
  have hε₀0 : 0 ≤ ε₀ := by positivity
  have hc₃0 : 0 ≤ c₃ := by linarith only [hc₃, hCT1, hd0]
  have hvb := vanish_bVecH P hQT1
  have hvS := vanish_aSharpH P hQT1
  have hvPP := vanish_aPPH P hQT1 x
  have hvR := vanish_aRH P hQT1
  -- Steps 0–4 for `u < L`
  have hpt : ∀ u, u < P.L Q T → famForm W Q (P.rangeZ Q T) (P.xVec Q T (P.bVec Q T) u) ≤
      (1 + κ) ^ 3 * (cfun ℓ ε (1 + d) (Cband + d) c₃ u * W.H Q) *
          normSq (P.rangeZ Q T) (xsH P Q T δ (P.bVec Q T) u) +
        ((1 + κ⁻¹) * (famForm W Q (P.rangeZ Q T) (xtH P Q T δ (P.aVec Q T) u) +
            famForm W Q (P.rangeZ Q T) (xtH P Q T δ (P.bVec Q T) u)) +
          8 * (1 + κ⁻¹) * (A₁ * normSq (P.rangeZ Q T) (xsH P Q T δ (P.aSharp Q T) u) + A₂) +
          (1 + κ⁻¹) * (8 * (c₃ * W.H Q) + 2 * M) *
            normSq (P.rangeZ Q T) (xsH P Q T δ (aPPH P Q T x) u) + ε₀) := by
    intro u hu
    obtain ⟨hS2i, hS2ii, hS2iii⟩ := hS2 u hu
    have hK := KlocH_le hδ0 hδ4 u
    have hKiii : (KlocH δ u : ℝ) ≤ Q ^ (2 - P.ε₁ / 2) := hK.trans hS2iii
    have hKQ2 : (KlocH δ u : ℝ) ≤ Q ^ 2 := hKiii.trans hQ2
    have hKε' : (KlocH δ u : ℝ) ≤ Q ^ (2 - ε') := hKiii.trans hQε'
    have hsuppb := supp_iff_of_xsH P hδ0 hvb u
    have hsuppPP := supp_iff_of_xsH P hδ0 hvPP u
    -- Step 0
    have h0 : famForm W Q (P.rangeZ Q T) (P.xVec Q T (P.bVec Q T) u) ≤
        famForm W Q (P.rangeZ Q T) (P.xVec Q T (P.aVec Q T) u) + ε₀ := by
      have := (abs_le.mp (hab Q hQab T hT u)).1
      linarith only [this, hε₀]
    -- regime (i): `lem:M2`
    have h1 : u ≤ (1 - ε) * ℓ → famForm W Q (P.rangeZ Q T) (xsH P Q T δ (P.bVec Q T) u) ≤
        (1 + d) * W.H Q * normSq (P.rangeZ Q T) (xsH P Q T δ (P.bVec Q T) u) := by
      intro h
      rw [famForm_congr_supp W Q hsuppb, normSq_congr_supp hsuppb]
      exact hi Q hQi (N0H δ u) (KlocH δ u) (hK.trans (hS2i h)) _
    -- regime (ii): the band hypothesis
    have h2 : u ≤ (1 + ε) * ℓ → famForm W Q (P.rangeZ Q T) (xsH P Q T δ (P.bVec Q T) u) ≤
        (Cband + d) * W.H Q * normSq (P.rangeZ Q T) (xsH P Q T δ (P.bVec Q T) u) := by
      intro h
      rw [famForm_congr_supp W Q hsuppb, normSq_congr_supp hsuppb]
      exact hb Q hQb (KlocH δ u) (hK.trans (hS2ii h)) (N0H δ u) (one_le_N0H δ u) _
    -- regime (iii): the sharp large sieve on the localisation interval
    have hsharp : ∀ z : ℤ → ℂ, (∀ n, z n ≠ 0 →
        (n ∈ P.rangeZ Q T ↔ n ∈ intervalZ (N0H δ u) (KlocH δ u))) →
        levelForm (levels Q) (aNat W Q) (P.rangeZ Q T) z ≤ c₃ * W.H Q * normSq (P.rangeZ Q T) z := by
      intro z hz
      rw [levelForm_congr_supp _ _ hz, normSq_congr_supp hz]
      refine (hS Q hQS (N0H δ u) (KlocH δ u) hKε' z).trans ?_
      apply mul_le_mul_of_nonneg_right _ (normSq_nonneg' _ _)
      exact mul_le_mul_of_nonneg_right (by linarith only [hSerr, hc₃]) hH
    have h3 : (1 + ε) * ℓ < u → levelForm (levels Q) (aNat W Q) (P.rangeZ Q T)
        (xsH P Q T δ (P.bVec Q T) u) ≤
        c₃ * W.H Q * normSq (P.rangeZ Q T) (xsH P Q T δ (P.bVec Q T) u) :=
      fun _ => hsharp _ hsuppb
    have h3' : (1 + ε) * ℓ < u → levelForm (levels Q) (aNat W Q) (P.rangeZ Q T)
        (xsH P Q T δ (aPPH P Q T x) u) ≤
        c₃ * W.H Q * normSq (P.rangeZ Q T) (xsH P Q T δ (aPPH P Q T x) u) :=
      fun _ => hsharp _ hsuppPP
    -- regime (iii): the large sieve for the prime powers
    have h4 : (1 + ε) * ℓ < u → famForm W Q (P.rangeZ Q T) (xsH P Q T δ (aPPH P Q T x) u) ≤
        M * normSq (P.rangeZ Q T) (xsH P Q T δ (aPPH P Q T x) u) := by
      intro _
      rw [famForm_congr_supp W Q hsuppPP, normSq_congr_supp hsuppPP]
      refine (famForm_interval_le hmult W hQ1.le (N0H δ u) (KlocH δ u) _).trans ?_
      apply mul_le_mul_of_nonneg_right _ (normSq_nonneg' _ _)
      have : 0 ≤ W.wmax * C₀' := mul_nonneg hw0 hC₀'0
      have := mul_le_mul_of_nonneg_left hKQ2 this
      rw [hM]; linarith only [this]
    -- Step 4(b)
    have h5 : levelForm (levels Q) (aNat W Q) (P.rangeZ Q T) (xsH P Q T δ (P.aSharp Q T) u) ≤
        A₁ * normSq (P.rangeZ Q T) (xsH P Q T δ (P.aSharp Q T) u) + A₂ := by
      refine (hF Q hQF T hT δ hδ0 hδ1 hδT u).trans ?_
      refine add_le_add (mul_le_mul_of_nonneg_right ?_ (normSq_nonneg' _ _)) le_rfl
      have hKA : (KlocH δ u : ℝ) ≤ Q ^ 2 * Q ^ (-(P.ε₁ / 2)) := hQsplit ▸ hKiii
      have : 0 ≤ ν * C₀' := mul_nonneg hν0 hC₀'0
      have := mul_le_mul_of_nonneg_left (add_le_add hKA hE0sq) this
      rw [hA₁]; linarith only [this]
    -- the rough part and the non-rough part in regime (iii)
    have h6 : (1 + ε) * ℓ < u → xsH P Q T δ (aNRH P Q T) u = xsH P Q T δ (aPPH P Q T x) u :=
      fun h => xsH_aNRH_eq_aPPH P hQT1 hδ0 hδ4 h
    have hR : famForm W Q (P.rangeZ Q T) (xsH P Q T δ (aRH P Q T) u) ≤
        levelForm (levels Q) (aNat W Q) (P.rangeZ Q T) (xsH P Q T δ (aRH P Q T) u) := by
      set IR := (P.rangeZ Q T).filter (fun n => IsRough Q n) with hIR
      have hsuppR : ∀ n, xsH P Q T δ (aRH P Q T) u n ≠ 0 → (n ∈ P.rangeZ Q T ↔ n ∈ IR) := by
        intro n hn
        have h1 := mem_rangeZ_of_xsH P hvR hn
        have h2 := rough_of_xsH_aRH P hδ0 hn
        simp only [hIR, Finset.mem_filter]
        exact ⟨fun h => ⟨h, h2⟩, fun h => h.1⟩
      rw [famForm_congr_supp W Q hsuppR, levelForm_congr_supp _ _ hsuppR]
      exact (lemmaS_rough W Q hQ0 IR (fun n hn => (Finset.mem_filter.mp hn).2) _).2
    exact pointwise_core W hQ0 (P.rangeZ Q T) hε.le hℓ0 hκ0 hκ1 hH (by linarith only [hd0])
      (by linarith only [hd0, hCband]) hc₃0 hM0 hA₁0 hA₂0 hε₀0
      (P.xVec Q T (P.bVec Q T) u) (P.xVec Q T (P.aVec Q T) u) (xsH P Q T δ (P.bVec Q T) u)
      (xtH P Q T δ (P.bVec Q T) u) (xsH P Q T δ (P.aVec Q T) u) (xtH P Q T δ (P.aVec Q T) u)
      (xsH P Q T δ (aRH P Q T) u) (xsH P Q T δ (aNRH P Q T) u) (xsH P Q T δ (P.aSharp Q T) u)
      (xsH P Q T δ (aPPH P Q T x) u)
      (xVec_eq_xsH_add_xtH P Q T δ _ u) (xVec_eq_xsH_add_xtH P Q T δ _ u)
      (by rw [← xsH_add, aRH_add_aNRH]) (by rw [aRH_eq P Q T, xsH_sub, xsH_add, add_sub_assoc])
      h0 h1 h2 h3 h3' h4 h5 h6 hR
  -- Step 5
  set Cmax := (1 + d) + (Cband + d) + c₃ with hCmax
  have hcf : ∀ u, 0 ≤ cfun ℓ ε (1 + d) (Cband + d) c₃ u ∧
      cfun ℓ ε (1 + d) (Cband + d) c₃ u ≤ Cmax := by
    intro u; unfold cfun; split_ifs <;> constructor <;> linarith only [hd0, hCband, hc₃0, hCmax]
  have hκi : 0 ≤ 1 + κ⁻¹ := by have := inv_pos.mpr hκ0; linarith only [this]
  have hint := integral_stepH P W hQ1 hT0 hQT1 hδ0 hδ4 hcf hpt (by positivity)
    (mul_nonneg (by positivity) hA₁0) (mul_nonneg hκi (by positivity))
  refine hint.trans ?_
  clear hint hpt hi hb hF hS hab
  -- the main term
  have hsup : ∀ n ∈ P.range Q T,
      sSup (cfun ℓ ε (1 + d) (Cband + d) c₃ '' {u | |u - Real.log n| < 2 * δ}) ≤
        (1 + d) * Ct (Real.log n / ℓ) := fun n _ =>
    (sSup_window_le (fun u => (hcf u).2) hδ0 hδ4 _).trans
      (sSup_cfun_le hℓ0 hεℓ' hd0.le hCband hCT1 hCt1 hCtband hCtCT (Real.log n))
  have h𝒦0 : ∀ n ∈ P.range Q T, 0 ≤ (P.𝒦 Q T n n).re := fun n hn =>
    𝒦_diag_re_nonneg P.toPS hQT1 T n (Finset.mem_Icc.mp hn).1
  have hmainsum : ∑ n ∈ P.range Q T, P.bVec Q T n ^ 2 * (P.𝒦 Q T n n).re *
      sSup (cfun ℓ ε (1 + d) (Cband + d) c₃ '' {u | |u - Real.log n| < 2 * δ}) ≤
      (1 + d) * ∑ n ∈ P.range Q T, P.bVec Q T n ^ 2 * Ct (Real.log n / ℓ) * (P.𝒦 Q T n n).re := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    calc P.bVec Q T n ^ 2 * (P.𝒦 Q T n n).re *
          sSup (cfun ℓ ε (1 + d) (Cband + d) c₃ '' {u | |u - Real.log n| < 2 * δ})
        ≤ P.bVec Q T n ^ 2 * (P.𝒦 Q T n n).re * ((1 + d) * Ct (Real.log n / ℓ)) :=
          mul_le_mul_of_nonneg_left (hsup n hn) (mul_nonneg (sq_nonneg _) (h𝒦0 n hn))
      _ = _ := by ring
  have hS0 : 0 ≤ ∑ n ∈ P.range Q T, P.bVec Q T n ^ 2 * Ct (Real.log n / ℓ) * (P.𝒦 Q T n n).re :=
    Finset.sum_nonneg fun n hn => mul_nonneg (mul_nonneg (sq_nonneg _)
      (le_trans zero_le_one (hCt1 _))) (h𝒦0 n hn)
  have hmain : (1 + κ) ^ 3 * W.H Q * ∑ n ∈ P.range Q T, P.bVec Q T n ^ 2 * (P.𝒦 Q T n n).re *
      sSup (cfun ℓ ε (1 + d) (Cband + d) c₃ '' {u | |u - Real.log n| < 2 * δ}) ≤
      (1 + δ') * W.H Q *
        ∑ n ∈ P.range Q T, P.bVec Q T n ^ 2 * Ct (Real.log n / ℓ) * (P.𝒦 Q T n n).re := by
    have hk3 : 0 ≤ (1 + κ) ^ 3 * W.H Q := by positivity
    calc _ ≤ (1 + κ) ^ 3 * W.H Q * ((1 + d) *
          ∑ n ∈ P.range Q T, P.bVec Q T n ^ 2 * Ct (Real.log n / ℓ) * (P.𝒦 Q T n n).re) :=
          mul_le_mul_of_nonneg_left hmainsum hk3
      _ = ((1 + κ) ^ 3 * (1 + d)) * (W.H Q *
          ∑ n ∈ P.range Q T, P.bVec Q T n ^ 2 * Ct (Real.log n / ℓ) * (P.𝒦 Q T n n).re) := by
          ring
      _ ≤ (1 + δ') * (W.H Q *
          ∑ n ∈ P.range Q T, P.bVec Q T n ^ 2 * Ct (Real.log n / ℓ) * (P.𝒦 Q T n n).re) :=
          mul_le_mul_of_nonneg_right hfac (mul_nonneg hH hS0)
      _ = _ := by ring
  refine add_le_add hmain ?_
  clear hmain hmainsum hsup hS0
  -- the tails (`cor:tails`)
  have hta : (1 + (T ^ (-(ε₅ / 2)))⁻¹) *
      (∫ u, P.g Q T u * famForm W Q (P.rangeZ Q T) (xtH P Q T δ (P.aVec Q T) u)) ≤
      δ' / 4 * W.H Q * P.Jlen T * P.L Q T ^ 2 * ℓ :=
    htails Q hQt T hT (P.aVec Q T) (by simp)
  have htb : (1 + (T ^ (-(ε₅ / 2)))⁻¹) *
      (∫ u, P.g Q T u * famForm W Q (P.rangeZ Q T) (xtH P Q T δ (P.bVec Q T) u)) ≤
      δ' / 4 * W.H Q * P.Jlen T * P.L Q T ^ 2 * ℓ :=
    htails Q hQt T hT (P.bVec Q T) (by simp)
  have hIa0 : 0 ≤ ∫ u, P.g Q T u * famForm W Q (P.rangeZ Q T) (xtH P Q T δ (P.aVec Q T) u) :=
    integral_nonneg fun u => mul_nonneg (g_nonnegH P Q T u) (famForm_nonneg' W Q _ _)
  have hIb0 : 0 ≤ ∫ u, P.g Q T u * famForm W Q (P.rangeZ Q T) (xtH P Q T δ (P.bVec Q T) u) :=
    integral_nonneg fun u => mul_nonneg (g_nonnegH P Q T u) (famForm_nonneg' W Q _ _)
  have T1a := (mul_le_mul_of_nonneg_right hκloc hIa0).trans hta
  have T1b := (mul_le_mul_of_nonneg_right hκloc hIb0).trans htb
  -- the remaining error terms
  set Jl := P.Jlen T with hJldef
  have hJl : θ₀ * T ≤ Jl := le_rfl
  obtain ⟨-, hJlℓ'⟩ := Jl_facts hθ₀0 hT1 hℓ1
  have hJlℓ : 1 / 2 ≤ Jl * ℓ := hJlℓ'
  have hJl0 : 0 ≤ Jl := by
    have : 0 ≤ θ₀ * T := by positivity
    exact le_trans this hJl
  have hLdef : P.L Q T = lam * ℓ := rfl
  have hlogY : Real.log (P.Y Q T) = μ * ℓ := by
    have e : Real.log (P.toPS.Y (Q * T)) = P.toPS.L (Q * T) * (1 + P.ε₁) := log_Y P.toPS
    have e2 : P.toPS.L (Q * T) = lam * ℓ := rfl
    rw [e2] at e
    rw [show P.Y Q T = P.toPS.Y (Q * T) from rfl, e, hμ]; ring
  have hSS : ∑ n ∈ P.range Q T, P.aSharp Q T n ^ 2 ≤ Cn * ℓ ^ 2 := by
    have h := hs (Q * T) (le_trans hQs hQT) 1 le_rfl
    rw [P.aSharp_eq]
    exact norm_sharp_le_ell P.toPS (Q := Q * T) (T := 1) hlogY hμ0.le hℓ1 rfl hCs0 h
  have hK : ∀ n ∈ P.range Q T, (P.𝒦 Q T n n).re ≤ CK * Jl * ℓ := by
    intro n hn
    have h : (P.𝒦 Q T n n).re ≤ 2 * Real.pi * Jl * (bI * (lam * ℓ)) + Cd :=
      hKd (Q * T) T hQT1 hT0 n (Finset.mem_Icc.mp hn).1
    exact 𝒦_le_ell P.toPS (Q := Q * T) (T := T) h hCd0 hJlℓ
  have hSPP := sum_sq_aPPH_le_ell P hQ1 hT1 hε.le hQε hlogY hμ0.le hℓ0.le
  have hε₀b : ε₀ ≤ Cab := by
    have hQm3 : Q ^ (-(3 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hQ1.le (by norm_num)
    calc Cab * Q ^ (-(3 : ℝ)) ≤ Cab * 1 := mul_le_mul_of_nonneg_left hQm3 hCab0
      _ = Cab := mul_one _
  have hC₂b : C₂ * Q ^ (-(P.ε₁ / 2)) ≤ tgt := by
    rw [pow_zero, mul_one] at hE2
    exact C_le_of hC₂0 hQmε₁ hE2
  have hC₄b : C₄ * Q ^ (-ε) * ℓ ≤ tgt := by
    rw [pow_one] at hE4
    have h1 := C_le_of' hC₄'0 hQmε (by linarith only [hlogQ1]) hE4
    have h2 : C₄ * Q ^ (-ε) * ℓ ≤ C₄ * Q ^ (-ε) * ((1 + P.kc) * Real.log Q) :=
      mul_le_mul_of_nonneg_left hℓup (mul_nonneg hC₄0 hQmε)
    have e : C₄ * Q ^ (-ε) * ((1 + P.kc) * Real.log Q) = C₄' * Q ^ (-ε) * Real.log Q := by
      rw [hC₄']; ring
    linarith only [h1, h2, e]
  have hSs0 : 0 ≤ ∑ n ∈ P.range Q T, P.aSharp Q T n ^ 2 * (P.𝒦 Q T n n).re :=
    Finset.sum_nonneg fun n hn => mul_nonneg (sq_nonneg _) (h𝒦0 n hn)
  have hSp0 : 0 ≤ ∑ n ∈ P.range Q T, aPPH P Q T x n ^ 2 * (P.𝒦 Q T n n).re :=
    Finset.sum_nonneg fun n hn => mul_nonneg (sq_nonneg _) (h𝒦0 n hn)
  have T2 : 8 * (1 + κ⁻¹) * A₁ * ∑ n ∈ P.range Q T, P.aSharp Q T n ^ 2 * (P.𝒦 Q T n n).re ≤
      tgt * (Q ^ 2 * Jl * ℓ ^ 3) := err_sharp (Q := Q) hκ0 hA₁.le
    (sum_sq_mul_𝒦_le P.toPS (Q := Q * T) (T := T) (P.aSharp Q T) hK) hSs0 hSS hCK0 hJl0
    hℓ0.le hC₂ hC₂b hν0 hC₀'0 hQmε₁
  have T3 := err_const (La := P.L Q T) (aI := P.aInt) (ℓ := ℓ) (Q := Q) (Jl := Jl) hε₀b hA₂
    hLdef hC₃ hE3 hJlℓ htgt0.le
  have T4 : (1 + κ⁻¹) * (8 * (c₃ * W.H Q) + 2 * M) *
      ∑ n ∈ P.range Q T, aPPH P Q T x n ^ 2 * (P.𝒦 Q T n n).re ≤
      tgt * (Q ^ 2 * Jl * ℓ ^ 3) := err_pp (Q := Q) hκ0 hc₃0 (by rw [hc₃]; linarith only [hd, hη1]) hH hHu hM0 hM.le
    (sum_sq_mul_𝒦_le P.toPS (Q := Q * T) (T := T) (aPPH P Q T x) hK) hSp0 hSPP hCK0 hJl0
    hℓ0.le hC₄ hC₄b (by linarith only [hCT1]) hC₀'0 hw0
  have htot := err_total (δ' := δ' / 2) (by positivity) hHl' htgt hJl0 hℓ0.le
  have hY0 : 0 ≤ tgt * (Q ^ 2 * Jl * ℓ ^ 3) := by positivity
  have hU0 : 0 ≤ δ' * W.H Q * Jl * (lam * ℓ) ^ 2 * ℓ := by positivity
  rw [hLdef] at T1a T1b T3 ⊢
  linarith only [T1a, T1b, T2, T3, T4, htot, hY0, hU0]

end TS

end Families.Hybrid
