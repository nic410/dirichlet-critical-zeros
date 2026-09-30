/-
# Theorem 1.4(a), package Z: deletion and assembly at polynomial height (Proposition 9.9, `prop:zeroH`)

`propZeroH_proof : propZeroH_Statement`, **unconditionally** (standard axioms only).

The proof is the families assembly (`Families.Ported.Zero.propZero_of_upTo`) with:
* the Gabor objects at the bandwidth argument `QT` (`toPS P`, `Q' = Q * T`), the family sums at `Q`;
* the bad set `Bad a B₁ Q` of the **family** parameter `Q` (`T`-independent), so `lem:bad`
  (`bad_weight_unconditional`, Montgomery only at heights `≤ Q`) is reused verbatim;
  `perchar_uniformH` is `perchar_uniform` with the bad predicate decoupled from the bandwidth;
* `trace_lowerH` (`Z/Trace.lean`), `exterior_tailH` (`Z/Exterior.lean`), `rvm_familyH` (`Z/RvM.lean`);
* the budgets in units of `ℓ_* = log(QT)` where the main terms live (`budget_bad_arithH`: the factor
  `ℓ_*` in `|K_J|` cancels against `N ≍ H T ℓ_*`), and in units of `ℓ = log Q ≤ ℓ_*` elsewhere
  (the families `budget_ext_arith`, `budget_sqrt_arith`, `zero_final_arith` and `half_arith`).
-/
import FamiliesH.Z.Trace
import FamiliesH.Z.Exterior

noncomputable section

open scoped BigOperators ComplexConjugate
open Complex Set Matrix Finset RHLinalg Filter Topology

namespace Families.Hybrid.Z

open Families Families.Hybrid Families.Ported.Zero Zeta23 Zeta23.ThmE

open Classical in
/-- The per-character inequalities, uniform over good and bad characters, with an arbitrary bad
predicate (at polynomial height: `Bad a B₁ Q χ` at the family parameter, bandwidth argument `QT`). -/
lemma perchar_uniformH (P : PrimeSetup) {Q' : ℝ} (hQ' : 1 < Q') (τ₀ : ℝ) {q : ℕ} (hq : 1 < q)
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) {T : ℝ} (hT : 0 < T)
    (bad : Prop) {η₀ : ℝ} (hη₀ : 0 ≤ η₀)
    (hgood : ¬ bad → ∑ k, ∑ l, ‖Ghat P Q' T τ₀ χ k l - Ahat P Q' T τ₀ χ k l‖ ≤ η₀) :
    let Y := 4 * rtrace (Ghat P Q' T τ₀ χ) - frobSq (Ghat P Q' T τ₀ χ)
    let X := 4 * η₀ + 2 * Real.sqrt (frobSq (Ghat P Q' T τ₀ χ)) * η₀ + η₀ ^ 2
    let bd : ℝ := if bad then 1 else 0
    let d : ℝ := (P.KJ Q' T τ₀).card
    Y - 2 * (Nchi χ T : ℝ) - 4 * d * bd - X ≤ Ns0chi χ T ∧
      Y - 2 * (Nchi χ T : ℝ) - 4 * d * bd - X ≤ Nstar0chi χ T ∧
      (Y - Nchi χ T - 4 * d * bd - X) / 2 ≤ Ndchi χ T := by
  intro Y X bd d
  have : NeZero q := ⟨by omega⟩
  have hX0 : 0 ≤ X := by positivity
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  by_cases hbad : bad
  · have hbd : bd = 1 := if_pos hbad
    have hY : Y ≤ 4 * d := by
      have := diag_bound (Ghat P Q' T τ₀ χ)
      rw [card_KJ_fintype] at this
      exact this
    have hN := Nat.cast_nonneg (α := ℝ) (Nchi χ T)
    have h1 := Nat.cast_nonneg (α := ℝ) (Ns0chi χ T)
    have h2 := Nat.cast_nonneg (α := ℝ) (Nstar0chi χ T)
    have h3 := Nat.cast_nonneg (α := ℝ) (Ndchi χ T)
    rw [hbd]
    refine ⟨by linarith, by linarith, by linarith⟩
  · have hbd : bd = 0 := if_neg hbad
    obtain ⟨h1, h2, h3⟩ := perchi_ext P hQ' τ₀ hq hprim hT (hgood hbad)
    rw [hbd]
    simp only [mul_zero, sub_zero]
    exact ⟨h1, h2, h3⟩

/-- Budget for the bad characters at polynomial height: `|K_J| ≤ 2Tλℓ_*` and `N ≥ H T ℓ_*/4π`
(the `ℓ_*` cancel), `∑_{bad} ω ≤ |C_b| Q² ℓ^{−2}` with `ℓ = log Q`. -/
lemma budget_bad_arithH {d T lam ℓ ℓs Cb Q δ κ₀ H N S : ℝ} (hlam : 0 < lam) (hℓ1 : 1 ≤ ℓ)
    (hℓs : 0 ≤ ℓs) (hT0 : 0 < T) (hQ0 : 0 < Q) (hδ : 0 < δ) (hκ₀ : 0 < κ₀)
    (hd : d ≤ 2 * T * (lam * ℓs)) (hS0 : 0 ≤ S) (hS : S ≤ |Cb| * Q ^ 2 * (1 / ℓ ^ 2))
    (hbadℓ : 96 * Real.pi * lam * |Cb| / (δ * κ₀) ≤ ℓ) (hH : κ₀ * Q ^ 2 ≤ H)
    (hN : H * T * ℓs / (4 * Real.pi) ≤ N) : 4 * d * S ≤ δ / 3 * N := by
  have hℓ0 : 0 < ℓ := by linarith
  have hX : 0 ≤ Q ^ 2 * T * ℓs := by positivity
  have h1 : 4 * d * S ≤ 4 * (2 * T * (lam * ℓs)) * (|Cb| * Q ^ 2 * (1 / ℓ ^ 2)) :=
    mul_le_mul (by linarith) hS hS0 (by positivity)
  have e1 : 4 * (2 * T * (lam * ℓs)) * (|Cb| * Q ^ 2 * (1 / ℓ ^ 2)) =
      (96 * Real.pi * lam * |Cb|) * (Q ^ 2 * T * ℓs) / (12 * Real.pi * ℓ ^ 2) := by
    field_simp; ring
  rw [div_le_iff₀ (by positivity)] at hbadℓ
  have h3 : (96 * Real.pi * lam * |Cb|) * (Q ^ 2 * T * ℓs) ≤
      ℓ ^ 2 * (δ * κ₀ * (Q ^ 2 * T * ℓs)) := by
    have h4 := mul_le_mul_of_nonneg_right hbadℓ hX
    have hℓℓ : ℓ ≤ ℓ ^ 2 := by nlinarith
    have h5 := mul_le_mul_of_nonneg_right hℓℓ (by positivity : (0:ℝ) ≤ δ * κ₀ * (Q ^ 2 * T * ℓs))
    have e : ℓ * (δ * κ₀) * (Q ^ 2 * T * ℓs) = ℓ * (δ * κ₀ * (Q ^ 2 * T * ℓs)) := by ring
    linarith
  have h2 : (96 * Real.pi * lam * |Cb|) * (Q ^ 2 * T * ℓs) / (12 * Real.pi * ℓ ^ 2) ≤
      δ * κ₀ * (Q ^ 2 * T * ℓs) / (12 * Real.pi) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h6 := mul_le_mul_of_nonneg_right h3 (by positivity : (0:ℝ) ≤ 12 * Real.pi)
    have e : ℓ ^ 2 * (δ * κ₀ * (Q ^ 2 * T * ℓs)) * (12 * Real.pi) =
        δ * κ₀ * (Q ^ 2 * T * ℓs) * (12 * Real.pi * ℓ ^ 2) := by ring
    linarith
  have h5 : δ * κ₀ * (Q ^ 2 * T * ℓs) / (12 * Real.pi) ≤ δ / 3 * N := by
    have h6 : κ₀ * Q ^ 2 * T * ℓs ≤ H * T * ℓs := by
      have := mul_le_mul_of_nonneg_right hH (by positivity : (0:ℝ) ≤ T * ℓs)
      linarith
    have e : δ * κ₀ * (Q ^ 2 * T * ℓs) / (12 * Real.pi) =
        δ / 3 * (κ₀ * Q ^ 2 * T * ℓs / (4 * Real.pi)) := by
      field_simp; ring
    rw [e]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact le_trans (div_le_div_of_nonneg_right h6 (by positivity)) hN
  rw [e1] at h1
  linarith

set_option maxHeartbeats 1000000 in
open Classical in
/-- **`prop:zeroH`** (Proposition 9.9), unconditionally. -/
theorem propZeroH_proof : propZeroH_Statement := by
  intro P W τ₀ B δ hB hδ
  set P' := toPS P with hP'
  obtain ⟨a, ha, hbadK⟩ := bad_weight_unconditional
  obtain ⟨B₁, hB₁, hbadW⟩ := hbadK 2
  obtain ⟨Cb, Qb, hbad⟩ := hbadW W
  obtain ⟨Cx, Qx, hext⟩ := exterior_tailH P τ₀ a B₁ ha hB₁ B
  obtain ⟨Qt, htr⟩ := trace_lowerH P W τ₀ (δ := δ / 12) (by positivity)
  obtain ⟨Qr, hrvm⟩ := rvm_familyH W P.a0_pos (δ := 1 / 2) (by norm_num)
  set κ₀ := 1 / 2 * (Ecal * W.Iw) with hκ₀
  have hκ₀0 : 0 < κ₀ := by have := Ecal_pos; have := W.Iw_pos; positivity
  have hHev := H_lower_eventually lemWH W (κ := 1 / 2) (by norm_num)
  have hlam := P'.lam_pos
  have ha0 := aInt_pos P'
  have hη := W.η_pos
  set Cz := 2 * |Cx| / (P'.aInt * P'.lam ^ 2) with hCz
  set M₁ := 1 + |Cx| / (P'.aInt * P'.lam ^ 2) + 60 * Real.pi * |Cx| / (δ * P'.aInt * P'.lam ^ 2)
    with hM₁
  have hev := hHev.and ((ev_log_ge 1).and ((ev_log_ge (1 / P'.lam)).and ((ev_log_ge M₁).and
    ((ev_log_ge (96 * Real.pi * P'.lam * |Cb| / (δ * κ₀))).and ((ev_log_rpow_ge 2 P.a0_pos).and
    (eventually_ge_atTop (2 / W.η + 2)))))))
  obtain ⟨Q₂, hQ₂⟩ := Filter.eventually_atTop.mp hev
  refine ⟨Cz, max (max (max Qb Qx) (max Qt Qr)) Q₂, fun Q hQ T hT => ?_⟩
  dsimp only
  have hQb : Qb ≤ Q :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans (le_max_left _ _) hQ)
  have hQx : Qx ≤ Q :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans (le_max_left _ _) hQ)
  have hQt : Qt ≤ Q :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans (le_max_left _ _) hQ)
  have hQr : Qr ≤ Q :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_trans (le_max_left _ _) hQ)
  obtain ⟨hHQ, hℓ1, hℓlam, hℓM, hℓbad, hℓa0, hQη⟩ := hQ₂ Q (le_trans (le_max_right _ _) hQ)
  set ℓ := Real.log Q with hℓ
  have hQ1 : 1 < Q := by linarith [div_pos (by norm_num : (0:ℝ) < 2) hη]
  have hQ0 : 0 < Q := by linarith
  have hT2 : 2 ≤ T := hℓa0.trans hT.1
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hQT : 1 < Q * T := one_lt_QT hQ1 hT1
  have hQη' : 2 ≤ W.η * Q := by
    have : 2 / W.η ≤ Q := by linarith
    rw [div_le_iff₀ hη] at this; linarith
  set ℓs := Real.log (Q * T) with hℓs
  have hℓsℓ : ℓ ≤ ℓs := by
    rw [hℓs, hℓ, Real.log_mul hQ0.ne' hT0.ne']; linarith [Real.log_nonneg hT1]
  have hℓs1 : 1 ≤ ℓs := by linarith
  have hellS : ellS Q T = ℓs := rfl
  have hL : 0 < P'.L (Q * T) := L_pos P' hQT
  have hLdef : P'.L (Q * T) = P'.lam * ℓs := rfl
  have hL1 : 1 ≤ P'.L (Q * T) := by
    rw [hLdef]
    rw [div_le_iff₀ hlam] at hℓlam
    have := mul_le_mul_of_nonneg_left hℓsℓ hlam.le
    linarith
  have hc0 : 0 < P'.aInt * P'.L (Q * T) ^ 2 := by positivity
  -- η₀
  set η₀ := |Cx| * ℓ ^ (-B) / (P'.aInt * P'.L (Q * T) ^ 2) with hη₀
  have hℓB : ℓ ^ (-B) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hℓ1 (by linarith)
  have hℓB0 : 0 ≤ ℓ ^ (-B) := Real.rpow_nonneg (by linarith) _
  have hη₀0 : 0 ≤ η₀ := by positivity
  have hη₀le : η₀ ≤ |Cx| / (P'.aInt * P'.lam ^ 2 * ℓ ^ 2) := by
    rw [hη₀, hLdef]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : |Cx| * ℓ ^ (-B) ≤ |Cx| := mul_le_of_le_one_right (abs_nonneg _) hℓB
    have h2 : P'.aInt * P'.lam ^ 2 * ℓ ^ 2 ≤ P'.aInt * (P'.lam * ℓs) ^ 2 := by
      rw [mul_pow, ← mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (by linarith) hℓsℓ 2
    exact mul_le_mul h1 h2 (by positivity) (abs_nonneg _)
  -- good characters
  have hgood : ∀ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.w (q / Q) ≠ 0 → ∀ χ ∈ primChars q,
      ¬ Bad a B₁ Q χ →
        ∑ k, ∑ l, ‖Ghat P' (Q * T) T τ₀ χ k l - Ahat P' (Q * T) T τ₀ χ k l‖ ≤ η₀ := by
    intro q hq hw χ hχ hgd
    have hq1 : 1 < q := one_lt_of_w_ne W hQη' hw
    have : NeZero q := ⟨by omega⟩
    have hqQ : (q : ℝ) ≤ Q :=
      (Nat.cast_le.mpr (Finset.mem_Icc.mp hq).2).trans (Nat.floor_le hQ0.le)
    obtain ⟨hsum, hle⟩ := hext Q hQx T hT q χ hq1 hqQ (Families.Ported.Zero.mem_primChars hχ) hgd
    have h1 := ext_entry_bound P' hQT τ₀ hq1 (Families.Ported.Zero.mem_primChars hχ) hT0 hsum
    refine h1.trans ?_
    rw [hη₀]
    apply div_le_div_of_nonneg_right _ hc0.le
    exact hle.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hℓB0)
  -- the family sums
  set d : ℝ := ((P'.KJ (Q * T) T τ₀).card : ℝ) with hd
  set bd : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ := fun _ χ => if Bad a B₁ Q χ then 1 else 0
  set F : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ := fun _ χ => frobSq (Ghat P' (Q * T) T τ₀ χ)
  set R : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ := fun _ χ => rtrace (Ghat P' (Q * T) T τ₀ χ)
  have hF0 : ∀ q χ, 0 ≤ F q χ := fun q χ => by
    simp only [F]; rw [frobSq_eq_sum]; positivity
  have hMfrak : P.Mfrak W Q T τ₀ = famSum W Q F := Mfrak_eqH P W Q T τ₀
  have hTr : (1 - 2 * P.θ - δ / 12) * Nfam W Q T ≤ famSum W Q R := by
    have := htr Q hQt T hT
    simpa only [R, rtrace_Ghat] using this
  have hBad : famSum W Q bd ≤ Cb * Q ^ 2 * ℓ ^ (-(2 : ℝ)) := hbad Q hQb
  have hSq : famSum W Q (fun q χ => Real.sqrt (F q χ)) ≤ Real.sqrt (W.H Q * famSum W Q F) :=
    famSum_sqrt_le W Q F hF0
  have hNr := hrvm Q hQr T hT.1
  rw [hellS] at hNr
  have hH : κ₀ * Q ^ 2 ≤ W.H Q := by rw [hκ₀]; linarith
  have hH0 : 0 ≤ W.H Q := le_trans (by positivity) hH
  have hN0 : 0 ≤ Nfam W Q T := by
    unfold Nfam famSum
    exact Finset.sum_nonneg fun q _ => mul_nonneg (omega_nonneg W Q q)
      (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
  have hNlows : W.H Q * T * ℓs / (4 * Real.pi) ≤ Nfam W Q T := by
    have := hNr.1
    have e : (1 - 1 / 2) * (W.H Q * T * ℓs / (2 * Real.pi)) = W.H Q * T * ℓs / (4 * Real.pi) := by
      field_simp; ring
    linarith
  have hNlow : W.H Q * T * ℓ / (4 * Real.pi) ≤ Nfam W Q T := by
    refine le_trans ?_ hNlows
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hℓsℓ (by positivity)
  -- budget: bad characters
  have hbd0 : 0 ≤ famSum W Q bd := by
    unfold famSum
    exact Finset.sum_nonneg fun q _ => mul_nonneg (omega_nonneg W Q q)
      (Finset.sum_nonneg fun χ _ => by simp only [bd]; split <;> norm_num)
  have hbudget_bad : 4 * d * famSum W Q bd ≤ δ / 3 * Nfam W Q T := by
    have hD := card_KJ_le P' hQT hT0.le τ₀
    have hTL : 1 ≤ T * P'.L (Q * T) := one_le_mul_of_one_le_of_one_le (by linarith) hL1
    have hd2 : d ≤ 2 * T * (P'.lam * ℓs) := by rw [hd, ← hLdef]; linarith
    have hbd1 : famSum W Q bd ≤ |Cb| * Q ^ 2 * (1 / ℓ ^ 2) := by
      have hℓ2 : ℓ ^ (-(2 : ℝ)) = 1 / ℓ ^ 2 := by
        rw [Real.rpow_neg (by linarith), one_div]; norm_cast
      rw [← hℓ2]
      exact hBad.trans (by gcongr; exact le_abs_self _)
    exact budget_bad_arithH hlam hℓ1 (by linarith) hT0 hQ0 hδ hκ₀0 hd2 hbd0 hbd1 hℓbad hH
      hNlows
  have hbudget_ext : (4 * η₀ + η₀ ^ 2) * W.H Q ≤ δ / 3 * Nfam W Q T :=
    budget_ext_arith hη₀0 hη₀le hℓM hT1 hH0 hNlow ha0 hlam hδ
  have hSq' : famSum W Q (fun q χ => Real.sqrt (F q χ)) ≤
      Real.sqrt (W.H Q * P.Mfrak W Q T τ₀) := by rw [hMfrak]; exact hSq
  have hSq0 : 0 ≤ famSum W Q (fun q χ => Real.sqrt (F q χ)) := by
    unfold famSum
    exact Finset.sum_nonneg fun q _ => mul_nonneg (omega_nonneg W Q q)
      (Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _)
  have h2η : 2 * η₀ ≤ Cz * ℓ ^ (-B) := by
    rw [hη₀, hCz, hLdef]
    exact budget_sqrt_arith hℓs1 hℓB0 ha0 hlam
  have hsq : 2 * η₀ * famSum W Q (fun q χ => Real.sqrt (F q χ)) ≤
      Cz * ℓ ^ (-B) * Real.sqrt (W.H Q * P.Mfrak W Q T τ₀) :=
    mul_le_mul h2η hSq' hSq0 (by positivity)
  -- per-character bounds, summed
  have hper := fun q (hq : q ∈ Finset.Icc 1 ⌊Q⌋₊) (hw : W.w (q / Q) ≠ 0) χ
      (hχ : χ ∈ primChars q) =>
    perchar_uniformH P' hQT τ₀ (one_lt_of_w_ne W hQη' hw)
      (Families.Ported.Zero.mem_primChars hχ) hT0 (Bad a B₁ Q χ) hη₀0 (hgood q hq hw χ hχ)
  have hsumc : ∀ (c : ℝ) (G : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
      (∀ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.w (q / Q) ≠ 0 → ∀ χ ∈ primChars q,
        4 * R q χ - F q χ - c * (Nchi χ T : ℝ) - 4 * d * bd q χ -
          (4 * η₀ + 2 * Real.sqrt (F q χ) * η₀ + η₀ ^ 2) ≤ G q χ) →
      4 * famSum W Q R - famSum W Q F - c * Nfam W Q T - 4 * d * famSum W Q bd -
        ((4 * η₀ + η₀ ^ 2) * W.H Q + 2 * η₀ * famSum W Q (fun q χ => Real.sqrt (F q χ))) ≤
        famSum W Q G := by
    intro c G hG
    have hNf : Nfam W Q T = famSum W Q (fun _ χ => (Nchi χ T : ℝ)) := rfl
    rw [hNf, ← famSum_lin W Q R F (fun _ χ => (Nchi χ T : ℝ)) bd c d η₀]
    refine famSum_mono_family W Q fun q hq hw χ hχ => ?_
    refine le_trans (le_of_eq ?_) (hG q hq hw χ hχ)
    ring
  have hNs := hsumc 2 (fun _ χ => (Ns0chi χ T : ℝ)) fun q hq hw χ hχ => by
    have := (hper q hq hw χ hχ).1
    simp only [R, F, bd] at this ⊢
    linarith
  have hNst := hsumc 2 (fun _ χ => (Nstar0chi χ T : ℝ)) fun q hq hw χ hχ => by
    have := (hper q hq hw χ hχ).2.1
    simp only [R, F, bd] at this ⊢
    linarith
  have hNd := hsumc 1 (fun _ χ => 2 * (Ndchi χ T : ℝ)) fun q hq hw χ hχ => by
    have := (hper q hq hw χ hχ).2.2
    simp only [R, F, bd] at this ⊢
    linarith
  have hNd' : famSum W Q (fun _ χ => 2 * (Ndchi χ T : ℝ)) = 2 * Nd W Q T := by
    rw [famSum_smul]; rfl
  rw [hNd'] at hNd
  rw [← hMfrak] at hNs hNst hNd
  have hθeq : P'.θ = P.θ := rfl
  have hTr' : (1 - 2 * P'.θ - δ / 12) * Nfam W Q T ≤ famSum W Q R := by rw [hθeq]; exact hTr
  have hfin := fun (c : ℝ) (Rhs : ℝ) (h : 4 * famSum W Q R - P.Mfrak W Q T τ₀ - c * Nfam W Q T -
      4 * d * famSum W Q bd - ((4 * η₀ + η₀ ^ 2) * W.H Q +
        2 * η₀ * famSum W Q (fun q χ => Real.sqrt (F q χ))) ≤ Rhs) =>
    zero_final_arith P' hN0 hδ hTr' hbudget_bad hbudget_ext hsq h (c := c)
  rw [hθeq] at hfin
  refine ⟨?_, ?_, ?_⟩
  · have := hfin 2 _ hNs
    have e : (4 - 8 * P.θ - 2) = 2 - 8 * P.θ := by ring
    rw [e] at this
    exact this
  · have := hfin 2 _ hNst
    have e : (4 - 8 * P.θ - 2) = 2 - 8 * P.θ := by ring
    rw [e] at this
    exact this
  · have := hfin 1 _ hNd
    have hCz0 : 0 ≤ Cz := by rw [hCz]; positivity
    have hsq0 : 0 ≤ Cz * ℓ ^ (-B) * Real.sqrt (W.H Q * P.Mfrak W Q T τ₀) :=
      mul_nonneg (mul_nonneg hCz0 hℓB0) (Real.sqrt_nonneg _)
    exact half_arith (mul_nonneg hδ.le hN0) hsq0 this

end Families.Hybrid.Z
