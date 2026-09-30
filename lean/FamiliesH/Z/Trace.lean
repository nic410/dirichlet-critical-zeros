/-
# Theorem 1.4(a), package Z: the family trace at polynomial height (Proposition 9.6, `prop:traceH`)

`trace_lowerH`: uniformly for `ℓ^{a₀} ≤ T ≤ Q^{κc}`, `∑_χ ω_χ tr Ĝ_χ ≥ (1 − 2θ − δ) N`.

* Gamma part (`main_norm_lowerH`, `main_family_lowerH`): as in `Families.Ported.Zero.main_norm_lower`,
  but with `μ_χ(t) ≥ (ℓ_* − c₂)/2π` near the lattice points (`log t ≥ log T`), so the terms `log T`
  enter the main term `(1−2θ) T ℓ_*/2π` (they had to be `o(ℓ)` in §4).
* Prime part: `trace_prime_bound` (cancellation over the lattice, `Z/TracePrime.lean`),
  `≪ Q √X log X` uniformly in `T`, which is `o(N)` because `X = (QT)^λ` with `λ < 2` and
  `N ≍ Q² T ℓ_*` (`prime_smallH`).
* No finite-centre replacement (Proposition 9.5) is used: the decomposition is per lattice point,
  `gabor_diag_re` (the explicit formula), as in the `Families` Lean proof.
-/
import FamiliesH.Z.RvM
import FamiliesH.Z.TracePrime

noncomputable section

open scoped BigOperators ComplexConjugate
open Complex Set MeasureTheory Filter Topology

namespace Families.Hybrid.Z

open Families Families.Hybrid Families.Ported.Zero Zeta23 Zeta23.ThmE

/-- The per-character main term at polynomial height (`ℓ_s = log(QT)`, `L = λℓ_s`). -/
lemma main_norm_lowerH (P : PrimeSetup) {Q T : ℝ} (hQT : 1 < Q * T) (hT : 2 ≤ T)
    (hθT : 1 ≤ P.θ * T) (τ₀ : ℝ) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 1 < q) (hprim : χ.IsPrimitive)
    {C Cg η : ℝ} (hC : ∀ w : ℝ, ‖P.hatψL (Q * T) w‖ * (1 + P.L (Q * T) * |w|) ^ 2 ≤ C * P.L (Q * T))
    (hCg : 0 ≤ Cg) (hη : 0 < η) (hη1 : η ≤ 1)
    (hμ1 : ∀ t : ℝ, -1 ≤ muChi χ t)
    (hμ2 : ∀ t : ℝ, 1 ≤ t → 1 / (2 * Real.pi) * (Real.log q + Real.log t - Real.log (2 * Real.pi)) - Cg ≤
      muChi χ t)
    (hqη : Real.log Q + Real.log η ≤ Real.log q) (hQ0 : 0 < Q)
    (hℓ1 : 2 ≤ Real.log (Q * T))
    (hℓ2 : -Real.log η + Real.log (2 * Real.pi) + 2 * Real.pi * Cg + 1 ≤ Real.log (Q * T))
    (hℓ3 : 2 * Real.pi * C ^ 2 ≤ P.aInt * P.lam ^ 3 * Real.log (Q * T) ^ 2) :
    (1 - 2 * P.θ) * T * Real.log (Q * T) / (2 * Real.pi) -
        ((-Real.log η + Real.log (2 * Real.pi) + 2 * Real.pi * Cg + 1) / (2 * Real.pi) + 1 / P.lam) * T ≤
      (∑ k ∈ P.KJ (Q * T) T τ₀, ∫ t : ℝ, ‖P.pk (Q * T) τ₀ k t‖ ^ 2 * muChi χ t) /
        (P.aInt * P.L (Q * T) ^ 2) := by
  set ℓ := Real.log (Q * T) with hℓ
  set c₂ := -Real.log η + Real.log (2 * Real.pi) + 2 * Real.pi * Cg with hc₂
  set m₁ := (ℓ - c₂) / (2 * Real.pi) with hm₁
  have hπ : 0 < 2 * Real.pi := by positivity
  have hL : 0 < P.L (Q * T) := L_pos P hQT
  have hLdef : P.L (Q * T) = P.lam * ℓ := rfl
  have ha := aInt_pos P
  have hlam := P.lam_pos
  have hθ1 : 0 < 1 - 2 * P.θ := by linarith [P.θ_lt]
  have hT0 : 0 < T := by linarith
  have hℓs : ℓ = Real.log Q + Real.log T := by rw [hℓ, Real.log_mul hQ0.ne' hT0.ne']
  have hc₂0 : 0 ≤ c₂ := by
    rw [hc₂]
    have := Real.log_nonpos hη.le hη1
    have hl2π : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
    nlinarith [Real.pi_gt_three]
  -- per k
  have hk : ∀ k ∈ P.KJ (Q * T) T τ₀, P.aInt * P.L (Q * T) * (ℓ - c₂ - 1) ≤
      ∫ t : ℝ, ‖P.pk (Q * T) τ₀ k t‖ ^ 2 * muChi χ t := by
    intro k hkK
    obtain ⟨hk1, hk2⟩ := tau_mem_J P hQT T τ₀ hkK
    have hm : ∀ t : ℝ, |t - tau P (Q * T) τ₀ k| ≤ 1 → m₁ ≤ muChi χ t := by
      intro t ht
      have htT : T ≤ t := by
        have := (abs_le.mp ht).1
        nlinarith [P.θ_pos]
      have ht1 : 1 ≤ t := by linarith
      have h := hμ2 t ht1
      have hlt : Real.log T ≤ Real.log t := Real.log_le_log hT0 htT
      have : m₁ ≤ 1 / (2 * Real.pi) * (Real.log q + Real.log t - Real.log (2 * Real.pi)) - Cg := by
        rw [hm₁, hc₂]
        have e : 1 / (2 * Real.pi) * (Real.log q + Real.log t - Real.log (2 * Real.pi)) - Cg =
            (Real.log q + Real.log t - Real.log (2 * Real.pi) - 2 * Real.pi * Cg) / (2 * Real.pi) := by
          field_simp
        rw [e]
        apply div_le_div_of_nonneg_right _ hπ.le
        rw [hℓs]
        linarith
      linarith
    have hm1 : 0 ≤ m₁ + 1 := by
      rw [hm₁]; have : 0 ≤ (ℓ - c₂) / (2 * Real.pi) := div_nonneg (by linarith) hπ.le
      linarith
    have hmain := main_term_lower P hQT τ₀ χ k hC hm hm1 hμ1
      (integrable_normSq_mul_mu P hQT τ₀ hq hprim k)
    have hm1ℓ : m₁ + 1 ≤ ℓ := by
      rw [hm₁]
      have : (ℓ - c₂) / (2 * Real.pi) ≤ ℓ / 2 := by
        rw [div_le_iff₀ hπ]
        nlinarith [Real.pi_gt_three]
      linarith
    have herr : (m₁ + 1) * (2 * C ^ 2 / P.L (Q * T) ^ 2 * Real.pi) ≤ P.aInt * P.L (Q * T) := by
      have hC2 : 0 ≤ 2 * C ^ 2 / P.L (Q * T) ^ 2 * Real.pi := by positivity
      calc (m₁ + 1) * (2 * C ^ 2 / P.L (Q * T) ^ 2 * Real.pi)
          ≤ ℓ * (2 * C ^ 2 / P.L (Q * T) ^ 2 * Real.pi) := mul_le_mul_of_nonneg_right hm1ℓ hC2
        _ = 2 * Real.pi * C ^ 2 / (P.lam ^ 2 * ℓ) := by
            rw [hLdef]; field_simp
        _ ≤ P.aInt * P.L (Q * T) := by
            rw [div_le_iff₀ (by positivity), hLdef]
            nlinarith
    have e1 : m₁ * (2 * Real.pi * P.aInt * P.L (Q * T)) = P.aInt * P.L (Q * T) * (ℓ - c₂) := by
      rw [hm₁]; field_simp
    linarith
  have hsum : ((P.KJ (Q * T) T τ₀).card : ℝ) * (P.aInt * P.L (Q * T) * (ℓ - c₂ - 1)) ≤
      ∑ k ∈ P.KJ (Q * T) T τ₀, ∫ t : ℝ, ‖P.pk (Q * T) τ₀ k t‖ ^ 2 * muChi χ t := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum hk
  have hD := card_KJ_ge P hQT T τ₀
  rw [hLdef] at hsum hD ⊢
  exact trace_algebra hπ ha hlam (by linarith) (by linarith) P.θ_pos hθ1 hc₂0 (by linarith) hD hsum

/-- The main part, family-summed and normalised, from below. -/
lemma main_family_lowerH (P : PrimeSetup) {Q T : ℝ} (hQ1 : 1 < Q) (hT : 2 ≤ T) (hθT : 1 ≤ P.θ * T)
    (τ₀ : ℝ) (W : Weight)
    {Ce Cg : ℝ} (hC : ∀ w : ℝ, ‖P.hatψL (Q * T) w‖ * (1 + P.L (Q * T) * |w|) ^ 2 ≤ Ce * P.L (Q * T))
    (hCg0 : 0 ≤ Cg)
    (hmu : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), 1 ≤ q → (∀ t : ℝ, -1 ≤ muChi χ t) ∧
      (∀ t : ℝ, 1 ≤ t → 1 / (2 * Real.pi) * (Real.log q + Real.log t - Real.log (2 * Real.pi)) - Cg ≤
        muChi χ t))
    (hQη : 2 ≤ W.η * Q) (hℓ1 : 2 ≤ Real.log (Q * T))
    (hℓc : -Real.log W.η + Real.log (2 * Real.pi) + 2 * Real.pi * Cg + 1 ≤ Real.log (Q * T))
    (hℓ3 : 2 * Real.pi * Ce ^ 2 ≤ P.aInt * P.lam ^ 3 * Real.log (Q * T) ^ 2) :
    ((1 - 2 * P.θ) * T * Real.log (Q * T) / (2 * Real.pi) -
        ((-Real.log W.η + Real.log (2 * Real.pi) + 2 * Real.pi * Cg + 1) / (2 * Real.pi) +
          1 / P.lam) * T) * W.H Q ≤
      famSum W Q (fun _ χ => (∑ k ∈ P.KJ (Q * T) T τ₀,
        ∫ t : ℝ, ‖P.pk (Q * T) τ₀ k t‖ ^ 2 * muChi χ t) / (P.aInt * P.L (Q * T) ^ 2)) := by
  have hQ0 : 0 < Q := by linarith
  have hQT : 1 < Q * T := by nlinarith
  have hη := W.η_pos
  have hη1 : W.η ≤ 1 := by linarith [W.η_lt_half]
  rw [← famSum_const]
  refine famSum_mono_family W Q fun q hq hw χ hχ => ?_
  have hq1 : 1 < q := one_lt_of_w_ne W hQη hw
  have : NeZero q := ⟨by omega⟩
  have hqη : W.η * Q ≤ q := le_of_w_ne W hQ0 hw
  have hlq : Real.log Q + Real.log W.η ≤ Real.log q := by
    have := Real.log_le_log (by positivity) hqη
    rw [Real.log_mul hη.ne' hQ0.ne'] at this
    linarith
  obtain ⟨hμ1, hμ2⟩ := hmu q χ hq1.le
  exact main_norm_lowerH P hQT hT hθT τ₀ hq1 (Families.Ported.Zero.mem_primChars hχ) hC hCg0 hη hη1
    hμ1 hμ2 hlq hQ0 hℓ1 hℓc hℓ3

/-- `√X = (QT)^{λ/2}` and `log X = λ log(QT)` at the bandwidth argument `QT`. -/
lemma sqrt_X_eq (P : PrimeSetup) {Q' : ℝ} (hQ' : 0 < Q') :
    Real.sqrt (P.X Q') = Q' ^ (P.lam / 2) := by
  rw [PrimeSetup.X, ← Real.exp_half, Real.rpow_def_of_pos hQ']
  unfold PrimeSetup.L
  congr 1; ring

lemma log_X_eq (P : PrimeSetup) (Q' : ℝ) : Real.log (P.X Q') = P.lam * Real.log Q' := by
  rw [PrimeSetup.X, Real.log_exp]; rfl

/-- The prime part is `o(N)`: `(2w_max Q/(1−2r))·2√X(1+log X) ≤ (δ/6) H T ℓ_*/2π`,
given `H ≥ κ₀Q²`, `QT ≥ Q`, `ℓ_* ≥ 1` and `Q^s ≥ K`, `s = 1 − λ/2`. -/
lemma prime_smallH (P : PrimeSetup) {Q T δ κ₀ H r wm : ℝ} (hQ1 : 1 < Q) (hT1 : 1 ≤ T)
    (hδ : 0 < δ) (hκ₀ : 0 < κ₀) (hr : r < 1 / 2) (hwm : 0 ≤ wm) (hH : κ₀ * Q ^ 2 ≤ H)
    (hℓs : 1 ≤ Real.log (Q * T))
    (hQs : 48 * Real.pi * wm * (1 + P.lam) / (δ * κ₀ * (1 - 2 * r)) ≤ Q ^ (1 - P.lam / 2)) :
    2 * wm * Q / (1 - 2 * r) * (2 * Real.sqrt (P.X (Q * T)) * (1 + Real.log (P.X (Q * T)))) ≤
      δ / 6 * (H * T * Real.log (Q * T) / (2 * Real.pi)) := by
  set ℓ := Real.log (Q * T) with hℓ
  set s := 1 - P.lam / 2 with hs
  have hlam := P.lam_pos
  have hlam2 := P.lam_lt
  have hs0 : 0 < s := by rw [hs]; linarith
  have hQ0 : 0 < Q := by linarith
  have hQT0 : 0 < Q * T := by positivity
  have hQTQ : Q ≤ Q * T := le_mul_of_one_le_right hQ0.le hT1
  have hr12 : 0 < 1 - 2 * r := by linarith
  rw [sqrt_X_eq P hQT0, log_X_eq P]
  -- (QT)^{λ/2} (QT)^s = QT
  have hsplit : (Q * T) ^ (P.lam / 2) * (Q * T) ^ s = Q * T := by
    rw [← Real.rpow_add hQT0]
    have : P.lam / 2 + s = 1 := by rw [hs]; ring
    rw [this, Real.rpow_one]
  have hQTs : Q ^ s ≤ (Q * T) ^ s := Real.rpow_le_rpow hQ0.le hQTQ hs0.le
  have hpos1 : 0 < (Q * T) ^ (P.lam / 2) := Real.rpow_pos_of_pos hQT0 _
  have hpos2 : 0 < (Q * T) ^ s := Real.rpow_pos_of_pos hQT0 _
  -- 1 + λℓ ≤ (1+λ)ℓ
  have hlin : 1 + P.lam * ℓ ≤ (1 + P.lam) * ℓ := by nlinarith
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity) hH
  have hK : 48 * Real.pi * wm * (1 + P.lam) ≤ δ * κ₀ * (1 - 2 * r) * (Q * T) ^ s := by
    have h1 := hQs.trans hQTs
    rw [div_le_iff₀ (by positivity)] at h1
    linarith
  -- LHS ≤ 4 wm Q (QT)^{λ/2} (1+λ) ℓ/(1−2r)
  calc 2 * wm * Q / (1 - 2 * r) * (2 * (Q * T) ^ (P.lam / 2) * (1 + P.lam * ℓ))
      ≤ 2 * wm * Q / (1 - 2 * r) * (2 * (Q * T) ^ (P.lam / 2) * ((1 + P.lam) * ℓ)) := by
        gcongr
    _ = (48 * Real.pi * wm * (1 + P.lam)) * ((Q * T) ^ (P.lam / 2) * Q * ℓ) /
          (12 * Real.pi * (1 - 2 * r)) := by
        field_simp; ring
    _ ≤ (δ * κ₀ * (1 - 2 * r) * (Q * T) ^ s) * ((Q * T) ^ (P.lam / 2) * Q * ℓ) /
          (12 * Real.pi * (1 - 2 * r)) := by
        gcongr
    _ = δ * κ₀ * ((Q * T) ^ (P.lam / 2) * (Q * T) ^ s) * Q * ℓ / (12 * Real.pi) := by
        rw [div_eq_div_iff (mul_pos (by positivity) hr12).ne' (by positivity)]
        ring
    _ = δ * κ₀ * (Q * T) * Q * ℓ / (12 * Real.pi) := by rw [hsplit]
    _ ≤ δ / 6 * (H * T * ℓ / (2 * Real.pi)) := by
        rw [div_le_iff₀ (by positivity)]
        have : δ / 6 * (H * T * ℓ / (2 * Real.pi)) * (12 * Real.pi) = δ * H * T * ℓ := by
          field_simp; ring
        rw [this]
        have h3 : δ * κ₀ * Q ^ 2 * T * ℓ ≤ δ * H * T * ℓ := by
          have := mul_le_mul_of_nonneg_right hH (by positivity : (0:ℝ) ≤ δ * T * ℓ)
          nlinarith
        nlinarith

set_option maxHeartbeats 800000 in
/-- **`prop:traceH`, lower bound**: `∑_χ ω_χ tr Ĝ_χ ≥ (1 − 2θ − δ) N`, uniformly in the cell. -/
theorem trace_lowerH (P : HSetup) (W : Weight) (τ₀ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ P.heights Q,
      (1 - 2 * P.θ - δ) * Nfam W Q T ≤
        famSum W Q (fun _ χ => (∑ k ∈ (toPS P).KJ (Q * T) T τ₀,
          (∑' ρ : PrimeSetup.strip χ, gaborTerm (toPS P) (Q * T) τ₀ χ k k ρ).re) /
            ((toPS P).aInt * (toPS P).L (Q * T) ^ 2)) := by
  set P' := toPS P with hP'
  obtain ⟨Cg, hCg0, hmu⟩ := mu_facts
  obtain ⟨Ce, hCe0, henv⟩ := envelope P' 2
  obtain ⟨r₀, hr₀, hrψ₀⟩ := ψL_supp P'
  have hη := W.η_pos
  set c₂ := -Real.log W.η + Real.log (2 * Real.pi) + 2 * Real.pi * Cg with hc₂
  set c₅ := (c₂ + 1) / (2 * Real.pi) + 1 / P'.lam with hc₅
  set δ₁ := min (δ / 6) (1 / 2) with hδ₁
  have hδ₁0 : 0 < δ₁ := lt_min (by positivity) (by norm_num)
  obtain ⟨Q₁, hRvM⟩ := rvm_familyH W P.a0_pos hδ₁0
  set κ₀ := 1 / 2 * (Ecal * W.Iw) with hκ₀
  have hκ₀0 : 0 < κ₀ := by have := Ecal_pos; have := W.Iw_pos; positivity
  have hHev := H_lower_eventually lemWH W (κ := 1 / 2) (by norm_num)
  have hlam := P'.lam_pos
  have hlam2 := P'.lam_lt
  have hs0 : 0 < 1 - P'.lam / 2 := by linarith
  have ha := aInt_pos P'
  have hθpos := P.θ_pos
  have hwm := W.wmax_nonneg
  have hr12 : 0 < 1 - 2 * r₀ := by linarith
  have hev := hHev.and ((ev_log_ge 2).and ((ev_log_ge (c₂ + 1)).and
    ((ev_log_ge (12 * Real.pi * c₅ / δ)).and ((ev_log_ge (1 / P'.lam)).and
    ((ev_log_rpow_ge (2 + 1 / P.θ) P.a0_pos).and (((tendsto_rpow_atTop hs0).eventually_ge_atTop
      (48 * Real.pi * W.wmax * (1 + P'.lam) / (δ * κ₀ * (1 - 2 * r₀)))).and
    ((eventually_ge_atTop (2 / W.η + 2)).and
    (((Real.tendsto_log_atTop.atTop_mul_atTop₀ Real.tendsto_log_atTop).eventually_ge_atTop
      (2 * Real.pi * Ce ^ 2 / (P'.aInt * P'.lam ^ 3)))))))))))
  obtain ⟨Q₂, hQ₂⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max Q₁ Q₂, fun Q hQ T hT => ?_⟩
  obtain ⟨hHQ, hℓ2, hℓc, hℓδ, hℓlam, hℓa0, hQs, hQη, hℓℓ⟩ := hQ₂ Q ((le_max_right _ _).trans hQ)
  have hQ1 : 1 < Q := by linarith [div_pos (by norm_num : (0:ℝ) < 2) hη]
  have hQ0 : 0 < Q := by linarith
  have hT2' : 2 + 1 / P.θ ≤ T := hℓa0.trans hT.1
  have hT2 : 2 ≤ T := by have : 0 < 1 / P.θ := by positivity
                         linarith
  have hT0 : 0 < T := by linarith
  have hT1 : 1 ≤ T := by linarith
  have hθT : 1 ≤ P'.θ * T := by
    have h1 : 1 / P.θ ≤ T := by linarith
    rw [div_le_iff₀ hθpos] at h1
    show 1 ≤ P.θ * T
    linarith
  obtain ⟨hN1, hN2⟩ := hRvM Q ((le_max_left _ _).trans hQ) T hT.1
  have hQT : 1 < Q * T := one_lt_QT hQ1 hT1
  have hQη' : 2 ≤ W.η * Q := by
    have : 2 / W.η ≤ Q := by linarith
    rw [div_le_iff₀ hη] at this; linarith
  set ℓs := Real.log (Q * T) with hℓs
  have hℓsℓ : Real.log Q ≤ ℓs := by
    rw [hℓs, Real.log_mul hQ0.ne' hT0.ne']; linarith [Real.log_nonneg hT1]
  have hellS : ellS Q T = ℓs := rfl
  have hC : ∀ w : ℝ, ‖P'.hatψL (Q * T) w‖ * (1 + P'.L (Q * T) * |w|) ^ 2 ≤ Ce * P'.L (Q * T) := by
    intro w
    have := henv (Q * T) hQT (w : ℂ)
    simpa using this
  have hℓ3 : 2 * Real.pi * Ce ^ 2 ≤ P'.aInt * P'.lam ^ 3 * ℓs ^ 2 := by
    have := hℓℓ
    rw [div_le_iff₀ (by positivity)] at this
    have hsq : Real.log Q ^ 2 ≤ ℓs ^ 2 := by
      have : 0 ≤ Real.log Q := by linarith
      nlinarith
    have h2 : Real.log Q * Real.log Q * (P'.aInt * P'.lam ^ 3) ≤ P'.aInt * P'.lam ^ 3 * ℓs ^ 2 := by
      rw [show Real.log Q * Real.log Q * (P'.aInt * P'.lam ^ 3) =
        P'.aInt * P'.lam ^ 3 * Real.log Q ^ 2 by ring]
      exact mul_le_mul_of_nonneg_left hsq (by positivity)
    linarith
  have hL1 : 1 ≤ P'.L (Q * T) := by
    show 1 ≤ P'.lam * Real.log (Q * T)
    rw [div_le_iff₀ hlam] at hℓlam
    nlinarith
  -- decomposition
  have hdecomp : famSum W Q (fun _ χ => (∑ k ∈ P'.KJ (Q * T) T τ₀,
      (∑' ρ : PrimeSetup.strip χ, gaborTerm P' (Q * T) τ₀ χ k k ρ).re) /
        (P'.aInt * P'.L (Q * T) ^ 2)) =
      famSum W Q (fun _ χ => (∑ k ∈ P'.KJ (Q * T) T τ₀,
        ∫ t : ℝ, ‖P'.pk (Q * T) τ₀ k t‖ ^ 2 * muChi χ t) / (P'.aInt * P'.L (Q * T) ^ 2)) +
      famSum W Q (fun _ χ => ∑ k ∈ P'.KJ (Q * T) T τ₀,
        ∫ t : ℝ, ‖P'.pk (Q * T) τ₀ k t‖ ^ 2 * Pch (P'.X (Q * T)) χ t) /
          (P'.aInt * P'.L (Q * T) ^ 2) := by
    rw [← famSum_div, ← famSum_add]
    refine famSum_congr_family W Q fun q hq hw χ hχ => ?_
    have hq1 : 1 < q := one_lt_of_w_ne W hQη' hw
    have : NeZero q := ⟨by omega⟩
    rw [← add_div, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    exact gabor_diag_re P' hQT τ₀ hq1 (Families.Ported.Zero.mem_primChars hχ) k
  rw [hdecomp]
  have hMn := main_family_lowerH P' hQ1 hT2 hθT τ₀ W hC hCg0 hmu hQη' (by linarith) (by linarith) hℓ3
  -- prime part
  have hPrB := trace_prime_bound P' hQT W hQ1.le T τ₀ hr₀ (hrψ₀ (Q * T) hQT)
  set E : ℝ := 2 * W.wmax * Q / (1 - 2 * r₀) *
    (2 * Real.sqrt (P'.X (Q * T)) * (1 + Real.log (P'.X (Q * T)))) with hE
  have hc0 : 0 < P'.aInt * P'.L (Q * T) ^ 2 := by positivity
  have hPr : -E ≤ famSum W Q (fun _ χ => ∑ k ∈ P'.KJ (Q * T) T τ₀,
      ∫ t : ℝ, ‖P'.pk (Q * T) τ₀ k t‖ ^ 2 * Pch (P'.X (Q * T)) χ t) /
        (P'.aInt * P'.L (Q * T) ^ 2) := by
    rw [le_div_iff₀ hc0]
    have h := (abs_le.mp hPrB).1
    have e : -E * (P'.aInt * P'.L (Q * T) ^ 2) = -(P'.aInt * P'.L (Q * T) ^ 2 *
        (2 * W.wmax * Q / (1 - 2 * r₀)) *
          (2 * Real.sqrt (P'.X (Q * T)) * (1 + Real.log (P'.X (Q * T))))) := by
      rw [hE]; ring
    rw [e]; exact h
  have hHQ' : κ₀ * Q ^ 2 ≤ W.H Q := by rw [hκ₀]; linarith
  have hEsmall := prime_smallH P' hQ1 hT1 hδ hκ₀0 hr₀ hwm hHQ' (by linarith) hQs
  have hH0 : 0 ≤ W.H Q := le_trans (by positivity) hHQ'
  have hc5 : c₅ * T * W.H Q ≤ δ / 6 * (W.H Q * T * ℓs / (2 * Real.pi)) := by
    rw [div_le_iff₀ hδ] at hℓδ
    have : c₅ ≤ δ / 6 * (ℓs / (2 * Real.pi)) := by
      rw [show δ / 6 * (ℓs / (2 * Real.pi)) = δ * ℓs / (12 * Real.pi) by ring,
        le_div_iff₀ (by positivity)]
      nlinarith
    have := mul_le_mul_of_nonneg_right this (mul_nonneg hT0.le hH0)
    have e : δ / 6 * (ℓs / (2 * Real.pi)) * (T * W.H Q) =
        δ / 6 * (W.H Q * T * ℓs / (2 * Real.pi)) := by ring
    linarith
  have hM : 0 ≤ W.H Q * T * ℓs / (2 * Real.pi) := by
    have : 0 ≤ ℓs := by linarith
    positivity
  have hMn' : (1 - 2 * P'.θ) * (W.H Q * T * ℓs / (2 * Real.pi)) - c₅ * T * W.H Q ≤
      famSum W Q (fun _ χ => (∑ k ∈ P'.KJ (Q * T) T τ₀,
        ∫ t : ℝ, ‖P'.pk (Q * T) τ₀ k t‖ ^ 2 * muChi χ t) / (P'.aInt * P'.L (Q * T) ^ 2)) := by
    refine le_trans (le_of_eq ?_) hMn
    rw [hc₅, hc₂]; ring
  rw [hellS] at hN1 hN2
  have hθ1 : 0 < 1 - 2 * P'.θ := by have := P'.θ_lt; linarith
  exact trace_final_arith hM P'.θ_pos.le hθ1 (min_le_left _ _)
    (min_le_right _ _) hδ hN1 hN2 hMn' hPr hc5 hEsmall

end Families.Hybrid.Z
