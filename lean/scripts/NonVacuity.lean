/-
Non-vacuity checks for the two headlines, `Families.thmMain` (Theorem 1.1) and `Families.Hybrid.thmH`
(Theorem 1.4(a)). Run (after `lake build`, from the project directory):  lake env lean scripts/NonVacuity.lean
(`scripts/audit.sh` runs it and checks its output).

The headlines are written without division, as `(p − ε) N ≤ N^s_0` etc. Such a statement would hold trivially
if the weighted zero count `N` were `0`, if the height range were empty, or if no weight satisfied the hypotheses.
This file proves, from the headlines and the zero-counting lower bounds of the project, that none of this
happens:

(a) `N > 0` eventually, uniformly for `T` in the height range of each headline
    (`Nfam_pos_main`: `ℓ^{a₀} ≤ T ≤ ℓ^{A₀}`; `Nfam_pos_hybrid`: `ℓ^{a₀} ≤ T ≤ Q^{κ₁}`);
(b) each headline implies the paper's displayed ratio statement, with real division by `N > 0`
    (`thmMain_ratio`, `thmMain_ratio_numeric`, `thmH_ratio`): for every `ε > 0` there is `η₀ > 0` such that
    for `η ≤ η₀` and both weights there is `Q₀` with `N^s_0/N ≥ p − ε`, `N^*_0/N ≥ p − ε` and
    `N_d/N ≥ (1 + p)/2 − ε` for all `Q ≥ Q₀` and all `T` in the range (`p = p(1)` resp. `p = p(β(κ_T))`);
    the `δ`-forms `thmMain_ratio_delta`, `thmH_ratio_delta` are the `liminf` statements verbatim;
(c) the height ranges are eventually nonempty (`heights_main_nonempty`, `heights_hybrid_eventually_nonempty`),
    and both weights exist for every `0 < η < 1/2` (`weights_exist`), so the hypotheses on `W` are inhabited.
Also: the constants are not junk values of `sInf` (`pB_class_bddBelow`, `pB_le_two`), the supports of the
table (`betaK_table`, `betaK_kappaT`, `kappaT_at_pow`), and a concrete specialisation (`concrete_kappa2`:
sharp weight, `T = Q²`, `N^s_0 ≥ (0.824355 − ε − δ) N` with `N > 0`).

Every theorem here must depend only on `propext`, `Classical.choice` and `Quot.sound`; the `#print axioms`
lines at the end are checked by `scripts/audit.sh`.
-/
import Families
import FamiliesH

open Filter Families Families.Hybrid

namespace Families.NonVacuity

/-! ### (c) the hypotheses are inhabited -/

/-- Both log-wide weights exist as `Weight`s for every `0 < η < 1/2`. -/
theorem weights_exist (η : ℝ) (h0 : 0 < η) (h1 : η < 1 / 2) :
    (∃ W : Weight, W.w = wSharpFun η) ∧ (∃ W : Weight, W.w = wSmoothFun η) :=
  ⟨⟨wSharpWeight η h0 h1, rfl⟩, ⟨wSmoothWeight η h0 h1, rfl⟩⟩

/-- The polylogarithmic height range `[ℓ^{a₀}, ℓ^{A₀}]` of Theorem 1.1 is nonempty (and contains `ℓ^{a₀} ≥ 1`)
for every `Q ≥ 3`. -/
theorem heights_main_nonempty {a0 A0 : ℝ} (ha : 0 < a0) (hA : a0 < A0) {Q : ℝ} (hQ : 3 ≤ Q) :
    Real.log Q ^ a0 ∈ Set.Icc (Real.log Q ^ a0) (Real.log Q ^ A0) ∧ 1 ≤ Real.log Q ^ a0 := by
  have hlog1 : 1 ≤ Real.log Q := by
    rw [Real.le_log_iff_exp_le (by linarith)]; linarith [Real.exp_one_lt_d9]
  exact ⟨⟨le_rfl, Real.rpow_le_rpow_of_exponent_le hlog1 hA.le⟩, Real.one_le_rpow hlog1 ha.le⟩

/-- The height range `[ℓ^{a₀}, Q^{κ₁}]` of Theorem 1.4(a) is eventually nonempty, for all `a₀, κ₁ > 0`. -/
theorem heights_hybrid_eventually_nonempty {a0 κ1 : ℝ} (ha : 0 < a0) (hk : 0 < κ1) :
    ∀ᶠ Q in atTop, Real.log Q ^ a0 ≤ Q ^ κ1 := by
  have ho := (isLittleO_log_rpow_atTop (div_pos hk ha)).bound one_pos
  filter_upwards [ho, eventually_ge_atTop (1 : ℝ)] with Q hQ hQ1
  have hl0 : 0 ≤ Real.log Q := Real.log_nonneg hQ1
  rw [Real.norm_of_nonneg hl0, one_mul,
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hQ
  calc Real.log Q ^ a0 ≤ (Q ^ (κ1 / a0)) ^ a0 := Real.rpow_le_rpow hl0 hQ ha.le
    _ = Q ^ κ1 := by
      rw [← Real.rpow_mul (by linarith), div_mul_cancel₀ _ ha.ne']

/-! ### (a) the denominator is eventually positive, uniformly in `T` -/

/-- `N > 0` for all large `Q`, uniformly for `ℓ^{a₀} ≤ T ≤ ℓ^{A₀}` (Theorem 1.1's range), for every weight. -/
theorem Nfam_pos_main (W : Weight) {a0 A0 : ℝ} (ha : 0 < a0) (hA : a0 < A0) :
    ∃ Q0 : ℝ, ∀ Q : ℝ, Q0 ≤ Q → ∀ T ∈ Set.Icc (Real.log Q ^ a0) (Real.log Q ^ A0), 0 < Nfam W Q T := by
  obtain ⟨Q₂, h2⟩ := Ported.Zero.lemRvM_lower W a0 A0 ha hA (1 / 2) (by norm_num)
  obtain ⟨Q₃, h3⟩ := Filter.eventually_atTop.1 (H_pos_eventually lemWH W)
  refine ⟨max Q₂ (max Q₃ 3), fun Q hQ T hT => ?_⟩
  have hQ2 : Q₂ ≤ Q := le_trans (le_max_left _ _) hQ
  have hQ3 : Q₃ ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hQ
  have hQ4 : (3 : ℝ) ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hQ
  have hlog : 0 < Real.log Q := Real.log_pos (by linarith)
  have hTpos : 0 < T := lt_of_lt_of_le (Real.rpow_pos_of_pos hlog a0) hT.1
  have hH : 0 < W.H Q := h3 Q hQ3
  have hpos : 0 < (1 - 1 / 2 : ℝ) * (W.H Q * T * Real.log Q / (2 * Real.pi)) := by
    apply mul_pos (by norm_num); positivity
  exact lt_of_lt_of_le hpos (h2 Q hQ2 T hT)

/-- `N > 0` for all large `Q`, uniformly for `ℓ^{a₀} ≤ T ≤ Q^{κ₁}` (Theorem 1.4(a)'s range), for every weight. -/
theorem Nfam_pos_hybrid (W : Weight) {a0 κ1 : ℝ} (ha : 0 < a0) (hk : 0 < κ1) :
    ∃ Q0 : ℝ, ∀ Q : ℝ, Q0 ≤ Q → ∀ T ∈ Set.Icc (Real.log Q ^ a0) (Q ^ κ1), 0 < Nfam W Q T := by
  obtain ⟨Qr, hr⟩ := Z.lemRvMH_lower_proof W a0 κ1 ha hk (1 / 2) (by norm_num)
  obtain ⟨Qh, hh⟩ := Filter.eventually_atTop.mp (H_pos_eventually lemWH W)
  refine ⟨max Qr (max Qh 3), fun Q hQ T hT => ?_⟩
  have hH : 0 < W.H Q := hh Q (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hQ)
  have hQ3 : (3 : ℝ) ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hQ
  have hlog1 : 1 ≤ Real.log Q := by
    rw [Real.le_log_iff_exp_le (by linarith)]; linarith [Real.exp_one_lt_d9]
  have hT1 : 1 ≤ T := le_trans (Real.one_le_rpow hlog1 ha.le) hT.1
  have hell : 0 < ellS Q T := by
    unfold ellS; exact Real.log_pos (by nlinarith)
  have hmain : 0 < (1 - (1 / 2 : ℝ)) * (W.H Q * T * ellS Q T / (2 * Real.pi)) := by
    have : 0 < T := by linarith
    apply mul_pos (by norm_num); positivity
  exact hmain.trans_le (hr Q (le_trans (le_max_left _ _) hQ) T hT)

/-! ### (b) the ratio form of the headlines -/

/-- Theorem 1.1 in the paper's ratio form, `δ`-version (this is `liminf_Q inf_T N^s_0/N ≥ p(1) − ε` etc.
verbatim), with `N > 0`. -/
theorem thmMain_ratio_delta (a0 A0 ε : ℝ) (ha0 : 0 < a0) (hA : a0 < A0) (hε : 0 < ε) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ W : Weight,
      (W.w = wSharpFun η ∨ W.w = wSmoothFun η) →
      ∀ δ : ℝ, 0 < δ → ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
        ∀ T ∈ Set.Icc (Real.log Q ^ a0) (Real.log Q ^ A0),
          0 < Nfam W Q T ∧ pC 1 - ε - δ ≤ Ns0 W Q T / Nfam W Q T ∧
          pC 1 - ε - δ ≤ Nstar0 W Q T / Nfam W Q T ∧
          (1 + pC 1) / 2 - ε - δ ≤ Nd W Q T / Nfam W Q T := by
  obtain ⟨η₀, hη₀, h⟩ := thmMain.1 a0 A0 ε ha0 hA hε
  refine ⟨η₀, hη₀, fun η hη hηle W hW δ hδ => ?_⟩
  obtain ⟨Q₁, h1⟩ := h η hη hηle W hW δ hδ
  obtain ⟨Q₂, h2⟩ := Nfam_pos_main W ha0 hA
  refine ⟨max Q₁ Q₂, fun Q hQ T hT => ?_⟩
  have hN : 0 < Nfam W Q T := h2 Q (le_trans (le_max_right _ _) hQ) T hT
  obtain ⟨e1, e2, e3⟩ := h1 Q (le_trans (le_max_left _ _) hQ) T hT
  refine ⟨hN, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hN]; exact e1
  · rw [le_div_iff₀ hN]; exact e2
  · rw [le_div_iff₀ hN]; nlinarith

/-- **Theorem 1.1, ratio form.** For every `ε > 0` there is `η₀ > 0` such that for `η ≤ η₀` and
`w ∈ {w_η, w^sm_η}` there is `Q₀` with `N > 0`, `N^s_0/N ≥ p(1) − ε`, `N^*_0/N ≥ p(1) − ε` and
`N_d/N ≥ (1 + p(1))/2 − ε` for all `Q ≥ Q₀` and all `ℓ^{a₀} ≤ T ≤ ℓ^{A₀}`. -/
theorem thmMain_ratio (a0 A0 ε : ℝ) (ha0 : 0 < a0) (hA : a0 < A0) (hε : 0 < ε) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ W : Weight,
      (W.w = wSharpFun η ∨ W.w = wSmoothFun η) →
      ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ Set.Icc (Real.log Q ^ a0) (Real.log Q ^ A0),
          0 < Nfam W Q T ∧ pC 1 - ε ≤ Ns0 W Q T / Nfam W Q T ∧
          pC 1 - ε ≤ Nstar0 W Q T / Nfam W Q T ∧
          (1 + pC 1) / 2 - ε ≤ Nd W Q T / Nfam W Q T := by
  obtain ⟨η₀, hη₀, h⟩ := thmMain_ratio_delta a0 A0 (ε / 2) ha0 hA (half_pos hε)
  refine ⟨η₀, hη₀, fun η hη hηle W hW => ?_⟩
  obtain ⟨Q₀, hQ₀⟩ := h η hη hηle W hW (ε / 2) (half_pos hε)
  refine ⟨Q₀, fun Q hQ T hT => ?_⟩
  obtain ⟨hN, e1, e2, e3⟩ := hQ₀ Q hQ T hT
  exact ⟨hN, by linarith, by linarith, by linarith⟩

/-- **Theorem 1.1, ratio form with the certified constant**: `N^s_0/N, N^*_0/N ≥ 0.9322 − ε` and
`N_d/N ≥ 0.9661 − ε` (from `p(1) ≥ 0.932282`, the second conjunct of `thmMain_Statement`). -/
theorem thmMain_ratio_numeric (a0 A0 ε : ℝ) (ha0 : 0 < a0) (hA : a0 < A0) (hε : 0 < ε) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ W : Weight,
      (W.w = wSharpFun η ∨ W.w = wSmoothFun η) →
      ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ Set.Icc (Real.log Q ^ a0) (Real.log Q ^ A0),
          0 < Nfam W Q T ∧ 0.9322 - ε ≤ Ns0 W Q T / Nfam W Q T ∧
          0.9322 - ε ≤ Nstar0 W Q T / Nfam W Q T ∧
          0.9661 - ε ≤ Nd W Q T / Nfam W Q T := by
  obtain ⟨η₀, hη₀, h⟩ := thmMain_ratio a0 A0 ε ha0 hA hε
  have hc : (0.932282 : ℝ) ≤ pC 1 := thmMain.2
  refine ⟨η₀, hη₀, fun η hη hηle W hW => ?_⟩
  obtain ⟨Q₀, hQ₀⟩ := h η hη hηle W hW
  refine ⟨Q₀, fun Q hQ T hT => ?_⟩
  obtain ⟨hN, e1, e2, e3⟩ := hQ₀ Q hQ T hT
  refine ⟨hN, ?_, ?_, ?_⟩ <;> norm_num at hc ⊢ <;> linarith

/-- Theorem 1.4(a) in the paper's ratio form, `δ`-version (`liminf_Q inf_T (N^s_0/N − p(β_T)) ≥ −ε`
verbatim), with `N > 0`, for all `ℓ^{a₀} ≤ T ≤ Q^{κ₁}`. -/
theorem thmH_ratio_delta (ε : ℝ) (hε : 0 < ε) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ (a0 κ1 : ℝ), 0 < a0 → 0 < κ1 → ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ W : Weight,
      (W.w = wSharpFun η ∨ W.w = wSmoothFun η) →
      ∀ δ : ℝ, 0 < δ → ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
        ∀ T ∈ Set.Icc (Real.log Q ^ a0) (Q ^ κ1),
          0 < Nfam W Q T ∧
          pB (betaK (kappaT Q T)) 1 - ε - δ ≤ Ns0 W Q T / Nfam W Q T ∧
          pB (betaK (kappaT Q T)) 1 - ε - δ ≤ Nstar0 W Q T / Nfam W Q T ∧
          (1 + pB (betaK (kappaT Q T)) 1) / 2 - ε - δ ≤ Nd W Q T / Nfam W Q T := by
  obtain ⟨η₀, hη₀, h⟩ := thmH.1 ε hε
  refine ⟨η₀, hη₀, fun a0 κ1 ha0 hκ1 η hη hηle W hW δ hδ => ?_⟩
  obtain ⟨Q₁, h1⟩ := h a0 κ1 ha0 hκ1 η hη hηle W hW δ hδ
  obtain ⟨Q₂, h2⟩ := Nfam_pos_hybrid W ha0 hκ1
  refine ⟨max Q₁ Q₂, fun Q hQ T hT => ?_⟩
  have hN : 0 < Nfam W Q T := h2 Q (le_trans (le_max_right _ _) hQ) T hT
  obtain ⟨e1, e2, e3⟩ := h1 Q (le_trans (le_max_left _ _) hQ) T hT
  refine ⟨hN, ?_, ?_, ?_⟩
  · rw [le_div_iff₀ hN]; exact e1
  · rw [le_div_iff₀ hN]; exact e2
  · rw [le_div_iff₀ hN]; nlinarith

/-- **Theorem 1.4(a), ratio form.** For every `ε > 0` there is `η₀ > 0`, independent of `a₀, κ₁`, such that
for `η ≤ η₀` and `w ∈ {w_η, w^sm_η}` there is `Q₀` with `N > 0`, `N^s_0/N ≥ p(β_T) − ε`,
`N^*_0/N ≥ p(β_T) − ε` and `N_d/N ≥ (1 + p(β_T))/2 − ε` for all `Q ≥ Q₀` and all `ℓ^{a₀} ≤ T ≤ Q^{κ₁}`,
where `β_T = β(κ_T)` (`betaK_kappaT`: `β_T = log(Q²T)/log(QT)`). -/
theorem thmH_ratio (ε : ℝ) (hε : 0 < ε) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ (a0 κ1 : ℝ), 0 < a0 → 0 < κ1 → ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ W : Weight,
      (W.w = wSharpFun η ∨ W.w = wSmoothFun η) →
      ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ Set.Icc (Real.log Q ^ a0) (Q ^ κ1),
          0 < Nfam W Q T ∧
          pB (betaK (kappaT Q T)) 1 - ε ≤ Ns0 W Q T / Nfam W Q T ∧
          pB (betaK (kappaT Q T)) 1 - ε ≤ Nstar0 W Q T / Nfam W Q T ∧
          (1 + pB (betaK (kappaT Q T)) 1) / 2 - ε ≤ Nd W Q T / Nfam W Q T := by
  obtain ⟨η₀, hη₀, h⟩ := thmH_ratio_delta (ε / 2) (half_pos hε)
  refine ⟨η₀, hη₀, fun a0 κ1 ha0 hκ1 η hη hηle W hW => ?_⟩
  obtain ⟨Q₀, hQ₀⟩ := h a0 κ1 ha0 hκ1 η hη hηle W hW (ε / 2) (half_pos hε)
  refine ⟨Q₀, fun Q hQ T hT => ?_⟩
  obtain ⟨hN, e1, e2, e3⟩ := hQ₀ Q hQ T hT
  exact ⟨hN, by linarith, by linarith, by linarith⟩

/-! ### The constants and supports -/

/-- The variational functional is nonnegative on the admissible class. -/
theorem Qf_FC1_nonneg {β : ℝ} {f : ℝ → ℝ} (hf : AdmissibleWindowB β f) : 0 ≤ Qf (FC 1) f := by
  unfold Qf
  refine add_nonneg (MeasureTheory.integral_nonneg fun x => sq_nonneg _)
    (MeasureTheory.integral_nonneg fun x => MeasureTheory.integral_nonneg fun y => ?_)
  refine mul_nonneg (mul_nonneg (hf.nonneg x) (hf.nonneg y)) ?_
  unfold FC; split_ifs <;> first | exact abs_nonneg _ | norm_num

/-- The set whose `sInf` defines `p(β)` is bounded below, so `sInf` is not a junk value from unboundedness. -/
theorem pB_class_bddBelow (β : ℝ) : BddBelow (Qf (FC 1) '' {f | AdmissibleWindowB β f}) :=
  ⟨0, by rintro _ ⟨f, hf, rfl⟩; exact Qf_FC1_nonneg hf⟩

/-- `p(β) ≤ 2` for every `β`. -/
theorem pB_le_two (β : ℝ) : pB β 1 ≤ 2 := by
  unfold pB
  have : 0 ≤ sInf (Qf (FC 1) '' {f | AdmissibleWindowB β f}) :=
    Real.sInf_nonneg (by rintro _ ⟨f, hf, rfl⟩; exact Qf_FC1_nonneg hf)
  linarith

/-- The supports of the table after Theorem 1.4: `β(κ)` at `κ = 1, 2, 3, 5, 10`. -/
theorem betaK_table :
    betaK 1 = 3 / 2 ∧ betaK 2 = 4 / 3 ∧ betaK 3 = 5 / 4 ∧ betaK 5 = 7 / 6 ∧ betaK 10 = 12 / 11 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [betaK]

/-- The target is evaluated at `β_T = log(Q²T)/log(QT)`, as in the definition of `β_T` in §1 of the paper. -/
theorem betaK_kappaT {Q T : ℝ} (hQ : 1 < Q) (hT : 1 ≤ T) :
    betaK (kappaT Q T) = Real.log (Q ^ 2 * T) / Real.log (Q * T) := by
  have hQ0 : 0 < Q := by linarith
  have hT0 : 0 < T := by linarith
  have hl : 0 < Real.log Q := Real.log_pos hQ
  have hlT : 0 ≤ Real.log T := Real.log_nonneg hT
  unfold betaK kappaT
  rw [Real.log_mul (by positivity) hT0.ne', Real.log_mul hQ0.ne' hT0.ne', Real.log_pow]
  have h1 : (1 : ℝ) + Real.log T / Real.log Q ≠ 0 := by positivity
  field_simp
  ring

/-- `κ_T = κ` at `T = Q^κ`. -/
theorem kappaT_at_pow {Q κ : ℝ} (hQ : 1 < Q) : kappaT Q (Q ^ κ) = κ := by
  unfold kappaT
  rw [Real.log_rpow (by linarith)]
  field_simp [(Real.log_pos hQ).ne']

/-- A concrete specialisation of Theorem 1.4(a): sharp weight, `T = Q²` (so `κ_T = 2`), with the certified
`p(4/3) ≥ 0.824355`: `N^s_0 ≥ (0.824355 − ε − δ) N` and `N > 0` for all large `Q`. -/
theorem concrete_kappa2 (ε : ℝ) (hε : 0 < ε) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ W : Weight, W.w = wSharpFun η →
      ∀ δ : ℝ, 0 < δ → ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
        (0.824355 - ε - δ) * Nfam W Q (Q ^ (2 : ℝ)) ≤ Ns0 W Q (Q ^ (2 : ℝ)) ∧
        0 < Nfam W Q (Q ^ (2 : ℝ)) := by
  obtain ⟨η₀, hη₀, h⟩ := thmH.1 ε hε
  refine ⟨η₀, hη₀, fun η hη hηη W hW δ hδ => ?_⟩
  obtain ⟨Q₁, hQ₁⟩ := h 1 2 one_pos two_pos η hη hηη W (Or.inl hW) δ hδ
  obtain ⟨Q₂, hQ₂⟩ :=
    Filter.eventually_atTop.mp (heights_hybrid_eventually_nonempty (a0 := 1) (κ1 := 2) one_pos two_pos)
  obtain ⟨Q₃, hQ₃⟩ := Nfam_pos_hybrid W (a0 := 1) (κ1 := 2) one_pos two_pos
  refine ⟨max (max Q₁ Q₂) (max Q₃ 2), fun Q hQ => ?_⟩
  have hQ1 : Q₁ ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hQ
  have hQ2 : Q₂ ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hQ
  have hQ3 : Q₃ ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hQ
  have hQ4 : 2 ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hQ
  have hT : Q ^ (2 : ℝ) ∈ Set.Icc (Real.log Q ^ (1 : ℝ)) (Q ^ (2 : ℝ)) := ⟨hQ₂ Q hQ2, le_rfl⟩
  have hN := hQ₃ Q hQ3 _ hT
  obtain ⟨h1, -, -⟩ := hQ₁ Q hQ1 _ hT
  rw [kappaT_at_pow (by linarith)] at h1
  beta_reduce at h1
  have hc := thmH.2.2.1
  rw [show betaK 2 = 4 / 3 by norm_num [betaK]] at h1
  refine ⟨le_trans (mul_le_mul_of_nonneg_right (by linarith) hN.le) h1, hN⟩

end Families.NonVacuity

#print axioms Families.NonVacuity.weights_exist
#print axioms Families.NonVacuity.heights_main_nonempty
#print axioms Families.NonVacuity.heights_hybrid_eventually_nonempty
#print axioms Families.NonVacuity.Nfam_pos_main
#print axioms Families.NonVacuity.Nfam_pos_hybrid
#print axioms Families.NonVacuity.thmMain_ratio_delta
#print axioms Families.NonVacuity.thmMain_ratio
#print axioms Families.NonVacuity.thmMain_ratio_numeric
#print axioms Families.NonVacuity.thmH_ratio_delta
#print axioms Families.NonVacuity.thmH_ratio
#print axioms Families.NonVacuity.Qf_FC1_nonneg
#print axioms Families.NonVacuity.pB_class_bddBelow
#print axioms Families.NonVacuity.pB_le_two
#print axioms Families.NonVacuity.betaK_table
#print axioms Families.NonVacuity.betaK_kappaT
#print axioms Families.NonVacuity.kappaT_at_pow
#print axioms Families.NonVacuity.concrete_kappa2
