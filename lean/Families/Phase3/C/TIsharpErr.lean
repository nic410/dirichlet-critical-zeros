/-
**the error term `𝓔_TI` of `prop:TIsharp`** (Proposition 6.24,
its statement and Step 5 of its proof), bounded term by term by `δ'/4 · H |J| L² ℓ` (via `tgt Q² |J| ℓ³` with `tgt = δ' h₀ λ²/4`,
`H ≥ h₀ Q²`):
* `err_tails`   — the tails (Step 2), `≪ κ^{−1} Q² L ‖y‖² = o(Q²|J|L²ℓ)` since `|J| ≥ (1−2θ)ℓ^{a₀}`;
* `err_sharp`   — `x♯^s` at the levels `e ≤ E₀` (Step 4(b)), `≪ κ^{−1} Q^{2−ε₁}|J|ℓ³`;
* `err_const`   — `x♯^s` at the levels `e > E₀` and Step 0, `≪ κ^{−1} L²`;
* `err_pp`      — the prime powers (Step 4(c)), `≪ κ^{−1} Q^{2−ε}|J|ℓ⁴`.
Pure real-number lemmas (small contexts, so that `nlinarith` is cheap), plus the concrete bounds on
`M`, `A₁`, `‖a‖²`, `‖a♯‖²`, `‖a_pp‖²`, `𝒦(n,n)` in terms of `ℓ = log Q`.
-/
import Families.Phase3.C.TIsharpStep5

noncomputable section

open scoped BigOperators ContDiff
open Set MeasureTheory Filter Topology

namespace Families.Phase3.C

open Families

/-! ### Pure inequalities -/

lemma err_tails {κ M bI lam ℓ SA SB wmax C₀' Q Cn C₁ tgt Jl : ℝ} (hκ : 0 < κ)
    (hM2 : M ≤ 2 * wmax * C₀' * Q ^ 2) (hbI : 0 ≤ bI) (hlam : 0 < lam) (hℓ : 0 < ℓ)
    (hSA0 : 0 ≤ SA) (hSB0 : 0 ≤ SB) (hSAB : SA + SB ≤ Cn * ℓ ^ 2)
    (hC₁ : C₁ = (1 + κ⁻¹) * 128 * wmax * C₀' * bI * lam * Cn) (hC₁b : C₁ ≤ tgt * Jl / 4)
    (htgt : 0 ≤ tgt) (hJl : 0 ≤ Jl) (hw : 0 ≤ wmax) (hC₀' : 0 ≤ C₀') :
    (1 + κ⁻¹) * M * (8 * bI * (lam * ℓ) * SA / δL) +
        (1 + κ⁻¹) * M * (8 * bI * (lam * ℓ) * SB / δL) ≤ tgt * (Q ^ 2 * Jl * ℓ ^ 3) := by
  have hκi : 0 ≤ 1 + κ⁻¹ := by have := inv_pos.mpr hκ; linarith
  have e : (1 + κ⁻¹) * M * (8 * bI * (lam * ℓ) * SA / δL) +
      (1 + κ⁻¹) * M * (8 * bI * (lam * ℓ) * SB / δL) =
      (1 + κ⁻¹) * M * (32 * bI * lam * ℓ) * (SA + SB) := by unfold δL; ring
  rw [e]
  calc (1 + κ⁻¹) * M * (32 * bI * lam * ℓ) * (SA + SB)
      ≤ (1 + κ⁻¹) * (2 * wmax * C₀' * Q ^ 2) * (32 * bI * lam * ℓ) * (Cn * ℓ ^ 2) := by
        gcongr
    _ = C₁ / 2 * (Q ^ 2 * ℓ ^ 3) := by rw [hC₁]; ring
    _ ≤ tgt * Jl / 4 / 2 * (Q ^ 2 * ℓ ^ 3) := by gcongr
    _ ≤ tgt * (Q ^ 2 * Jl * ℓ ^ 3) := by
        have : 0 ≤ tgt * (Q ^ 2 * Jl * ℓ ^ 3) := by positivity
        nlinarith

lemma err_sharp {κ A₁ ν C₀' Q Qε₁ Ss CK Jl ℓ SS Cn C₂ tgt : ℝ} (hκ : 0 < κ)
    (hA₁ : A₁ ≤ 5 * ν * C₀' * (Q ^ 2 * Qε₁)) (hSs : Ss ≤ CK * Jl * ℓ * SS) (hSs0 : 0 ≤ Ss)
    (hSS : SS ≤ Cn * ℓ ^ 2) (hCK : 0 ≤ CK) (hJl : 0 ≤ Jl) (hℓ : 0 ≤ ℓ)
    (hC₂ : C₂ = 8 * (1 + κ⁻¹) * (5 * ν * C₀') * CK * Cn) (hC₂b : C₂ * Qε₁ ≤ tgt)
    (hν : 0 ≤ ν) (hC₀' : 0 ≤ C₀') (hQε₁ : 0 ≤ Qε₁) :
    8 * (1 + κ⁻¹) * A₁ * Ss ≤ tgt * (Q ^ 2 * Jl * ℓ ^ 3) := by
  have hκi : 0 ≤ 1 + κ⁻¹ := by have := inv_pos.mpr hκ; linarith
  have h2 : Ss ≤ CK * Jl * ℓ * (Cn * ℓ ^ 2) :=
    hSs.trans (mul_le_mul_of_nonneg_left hSS (by positivity))
  calc 8 * (1 + κ⁻¹) * A₁ * Ss
      ≤ 8 * (1 + κ⁻¹) * (5 * ν * C₀' * (Q ^ 2 * Qε₁)) * (CK * Jl * ℓ * (Cn * ℓ ^ 2)) := by
        gcongr
    _ = (C₂ * Qε₁) * (Q ^ 2 * Jl * ℓ ^ 3) := by rw [hC₂]; ring
    _ ≤ tgt * (Q ^ 2 * Jl * ℓ ^ 3) := mul_le_mul_of_nonneg_right hC₂b (by positivity)

lemma err_const {κ A₂ ε₀ Cab La aI ℓ lam ν CF C₃ tgt Q Jl : ℝ} (hε₀ : ε₀ ≤ Cab)
    (hA₂ : A₂ = ν * CF ^ 2) (hLa : La = lam * ℓ)
    (hC₃ : C₃ = (8 * (1 + κ⁻¹) * (ν * CF ^ 2) + Cab) * lam ^ 2 * aI ^ 2)
    (hC₃b : C₃ ≤ tgt / 2 * Q ^ 2) (hJlℓ : 1 / 2 ≤ Jl * ℓ) (htgt : 0 ≤ tgt) :
    (8 * (1 + κ⁻¹) * A₂ + ε₀) * (La * aI) ^ 2 ≤ tgt * (Q ^ 2 * Jl * ℓ ^ 3) := by
  calc (8 * (1 + κ⁻¹) * A₂ + ε₀) * (La * aI) ^ 2
      ≤ (8 * (1 + κ⁻¹) * A₂ + Cab) * (La * aI) ^ 2 := by gcongr
    _ = C₃ * ℓ ^ 2 := by rw [hC₃, hA₂, hLa]; ring
    _ ≤ tgt / 2 * Q ^ 2 * ℓ ^ 2 := by gcongr
    _ ≤ tgt * (Q ^ 2 * Jl * ℓ ^ 3) := by
        have h0 : 0 ≤ tgt * Q ^ 2 * ℓ ^ 2 := by positivity
        have : tgt * Q ^ 2 * ℓ ^ 2 * (1 / 2) ≤ tgt * Q ^ 2 * ℓ ^ 2 * (Jl * ℓ) :=
          mul_le_mul_of_nonneg_left hJlℓ h0
        nlinarith

lemma err_pp {κ c₃ H M CT C₀' wmax Q Sp CK Jl ℓ μ Qε C₄ tgt SPP : ℝ} (hκ : 0 < κ)
    (hc₃0 : 0 ≤ c₃) (hc₃ : c₃ ≤ CT + 1) (hH : 0 ≤ H) (hHu : H ≤ wmax * Q ^ 2) (hM0 : 0 ≤ M)
    (hM2 : M ≤ 2 * wmax * C₀' * Q ^ 2) (hSp : Sp ≤ CK * Jl * ℓ * SPP) (hSp0 : 0 ≤ Sp)
    (hSPP : SPP ≤ 4 * μ ^ 3 * ℓ ^ 3 * Qε) (hCK : 0 ≤ CK) (hJl : 0 ≤ Jl) (hℓ : 0 ≤ ℓ)
    (hC₄ : C₄ = (1 + κ⁻¹) * ((8 * (CT + 1) + 4 * C₀') * wmax) * CK * (4 * μ ^ 3))
    (hC₄b : C₄ * Qε * ℓ ≤ tgt) (hCT : 0 ≤ CT) (hC₀' : 0 ≤ C₀') (hw : 0 ≤ wmax) :
    (1 + κ⁻¹) * (8 * (c₃ * H) + 2 * M) * Sp ≤ tgt * (Q ^ 2 * Jl * ℓ ^ 3) := by
  have hκi : 0 ≤ 1 + κ⁻¹ := by have := inv_pos.mpr hκ; linarith
  have hX : 8 * (c₃ * H) + 2 * M ≤ (8 * (CT + 1) + 4 * C₀') * wmax * Q ^ 2 := by
    have : c₃ * H ≤ (CT + 1) * (wmax * Q ^ 2) := mul_le_mul hc₃ hHu hH (by linarith)
    nlinarith
  have h2 : Sp ≤ CK * Jl * ℓ * (4 * μ ^ 3 * ℓ ^ 3 * Qε) :=
    hSp.trans (mul_le_mul_of_nonneg_left hSPP (by positivity))
  have h3 : 0 ≤ 8 * (c₃ * H) + 2 * M := by positivity
  calc (1 + κ⁻¹) * (8 * (c₃ * H) + 2 * M) * Sp
      ≤ (1 + κ⁻¹) * ((8 * (CT + 1) + 4 * C₀') * wmax * Q ^ 2) *
          (CK * Jl * ℓ * (4 * μ ^ 3 * ℓ ^ 3 * Qε)) := by gcongr
    _ = (C₄ * Qε * ℓ) * (Q ^ 2 * Jl * ℓ ^ 3) := by rw [hC₄]; ring
    _ ≤ tgt * (Q ^ 2 * Jl * ℓ ^ 3) := mul_le_mul_of_nonneg_right hC₄b (by positivity)

lemma err_total {δ' H h₀ Q Jl lam ℓ tgt : ℝ} (hδ' : 0 < δ') (hHl : h₀ * Q ^ 2 ≤ H)
    (htgt : tgt = δ' / 4 * h₀ * lam ^ 2) (hJl : 0 ≤ Jl) (hℓ : 0 ≤ ℓ) :
    4 * (tgt * (Q ^ 2 * Jl * ℓ ^ 3)) ≤ δ' * H * Jl * (lam * ℓ) ^ 2 * ℓ := by
  have e : 4 * (tgt * (Q ^ 2 * Jl * ℓ ^ 3)) = (h₀ * Q ^ 2) * (δ' * Jl * (lam * ℓ) ^ 2 * ℓ) := by
    rw [htgt]; ring
  rw [e]
  have h0 : 0 ≤ δ' * Jl * (lam * ℓ) ^ 2 * ℓ := by positivity
  calc (h₀ * Q ^ 2) * (δ' * Jl * (lam * ℓ) ^ 2 * ℓ) ≤ H * (δ' * Jl * (lam * ℓ) ^ 2 * ℓ) :=
        mul_le_mul_of_nonneg_right hHl h0
    _ = δ' * H * Jl * (lam * ℓ) ^ 2 * ℓ := by ring

/-! ### Concrete bounds in terms of `ℓ = log Q` -/

variable (P : PrimeSetup)

lemma norm_a_le_ell {Q μ ℓ : ℝ} (hQ : 1 < Q) (hlogY : Real.log (P.Y Q) = μ * ℓ) (hμ : 0 ≤ μ)
    (hℓ : 1 ≤ ℓ) : ∑ n ∈ P.range Q, P.aVec Q n ^ 2 ≤ μ * (μ + 6) * ℓ ^ 2 := by
  have h := sum_sq_aVec_le P hQ
  rw [hlogY] at h
  have hℓℓ : ℓ ≤ ℓ ^ 2 := by nlinarith
  have : μ * ℓ * (μ * ℓ + 6) ≤ μ * (μ + 6) * ℓ ^ 2 := by
    have := mul_le_mul_of_nonneg_left hℓℓ hμ
    nlinarith
  linarith

lemma norm_sharp_le_ell {Q T μ ℓ Cs : ℝ} (hlogY : Real.log (P.Y Q) = μ * ℓ) (hμ : 0 ≤ μ)
    (hℓ : 1 ≤ ℓ) (hℓQ : ℓ = Real.log Q) (hCs : 0 ≤ Cs)
    (h : ∑ n ∈ P.range Q, P.aSharp Q T n ^ 2 ≤ 4 * (1 + Real.log Q) * (1 + Real.log (P.Y Q)) + Cs) :
    ∑ n ∈ P.range Q, P.aSharp Q T n ^ 2 ≤ (8 * (1 + μ) + Cs) * ℓ ^ 2 := by
  rw [hlogY, ← hℓQ] at h
  have hℓℓ : ℓ ≤ ℓ ^ 2 := by nlinarith
  have hℓ2 : 1 ≤ ℓ ^ 2 := by nlinarith
  have hμℓ := mul_le_mul_of_nonneg_left hℓℓ hμ
  have e1 : 4 * (1 + ℓ) * (1 + μ * ℓ) ≤ 8 * (1 + μ) * ℓ ^ 2 := by nlinarith
  have e2 : Cs ≤ Cs * ℓ ^ 2 := by
    have := mul_le_mul_of_nonneg_left hℓ2 hCs; linarith
  linarith

lemma sum_sq_aPP_le_ell {Q ε μ ℓ : ℝ} (hQ : 1 < Q) (hQε : 2 ≤ Q ^ ε)
    (hlogY : Real.log (P.Y Q) = μ * ℓ) (hμ : 0 ≤ μ) (hℓ : 0 ≤ ℓ) :
    ∑ n ∈ P.range Q, aPP P Q (Q ^ (1 + ε) / 2) n ^ 2 ≤ 4 * μ ^ 3 * ℓ ^ 3 * Q ^ (-ε) := by
  have hQ0 : 0 < Q := by linarith
  have hx : Q ^ (1 + ε) = Q * Q ^ ε := by rw [Real.rpow_add hQ0, Real.rpow_one]
  have hQεx : Q ≤ Q ^ (1 + ε) / 2 := by rw [hx]; nlinarith
  refine (sum_sq_aPP_le P hQ hQεx).trans ?_
  rw [hlogY]
  have hsY : Real.sqrt (P.Y Q) ≤ Q :=
    (Real.sqrt_le_sqrt (Y_le_sq P hQ.le)).trans (le_of_eq (Real.sqrt_sq hQ0.le))
  have hx0 : 0 < Q ^ (1 + ε) / 2 := by positivity
  have hQe : Q ^ (-ε) * Q ^ (1 + ε) = Q := by
    rw [← Real.rpow_add hQ0]; norm_num
  rw [div_le_iff₀ hx0]
  have h3 : 0 ≤ (μ * ℓ) ^ 3 := by positivity
  have h4 : 0 ≤ Q ^ (-ε) := Real.rpow_nonneg hQ0.le _
  calc 2 * Real.sqrt (P.Y Q) * (μ * ℓ) ^ 3 ≤ 2 * Q * (μ * ℓ) ^ 3 := by gcongr
    _ = 4 * μ ^ 3 * ℓ ^ 3 * Q ^ (-ε) * (Q ^ (1 + ε) / 2) := by
        rw [show 4 * μ ^ 3 * ℓ ^ 3 * Q ^ (-ε) * (Q ^ (1 + ε) / 2) =
          2 * (μ * ℓ) ^ 3 * (Q ^ (-ε) * Q ^ (1 + ε)) by ring, hQe]
        ring

lemma M_le_sq (W : Weight) {Q C₀' : ℝ} (hQ : 1 < Q) (hC₀' : 0 ≤ C₀') :
    W.wmax * C₀' * (Q ^ 2 + ⌊P.Y Q⌋₊) ≤ 2 * W.wmax * C₀' * Q ^ 2 := by
  have h1 : (⌊P.Y Q⌋₊ : ℝ) ≤ Q ^ 2 := (Nat.floor_le (P.Y_nonneg Q)).trans (Y_le_sq P hQ.le)
  have : 0 ≤ W.wmax * C₀' := mul_nonneg W.wmax_nonneg hC₀'
  nlinarith

lemma A₁_le {Q ν C₀' : ℝ} (hQ : 1 < Q) (hν : 0 ≤ ν) (hC₀' : 0 ≤ C₀') :
    ν * C₀' * (⌊P.Y Q⌋₊ + (⌊2 * P.Y Q / Q⌋₊ : ℝ) ^ 2) ≤ 5 * ν * C₀' * (Q ^ 2 * Q ^ (-P.ε₁)) := by
  have hQ0 : 0 < Q := by linarith
  have hQε₁ : Q ^ (2 - P.ε₁) = Q ^ 2 * Q ^ (-P.ε₁) := by
    rw [show (2 : ℝ) - P.ε₁ = ((2 : ℕ) : ℝ) + (-P.ε₁) by push_cast; ring, Real.rpow_add hQ0,
      Real.rpow_natCast]
  rw [← hQε₁]
  have hYr := Y_le_rpow P hQ.le
  have hE : (⌊2 * P.Y Q / Q⌋₊ : ℝ) ≤ 2 * Q ^ (1 - P.ε₁) := by
    refine (Nat.floor_le (by have := P.Y_nonneg Q; positivity)).trans ?_
    rw [div_le_iff₀ hQ0]
    have : Q ^ (1 - P.ε₁) * Q = Q ^ (2 - P.ε₁) := by
      rw [← Real.rpow_add_one hQ0.ne']; ring_nf
    linarith
  have hE2 : (⌊2 * P.Y Q / Q⌋₊ : ℝ) ^ 2 ≤ 4 * Q ^ (2 - P.ε₁) := by
    have h0 : (0 : ℝ) ≤ ⌊2 * P.Y Q / Q⌋₊ := Nat.cast_nonneg _
    have hsq : (Q ^ (1 - P.ε₁)) ^ 2 ≤ Q ^ (2 - P.ε₁) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]
      exact Real.rpow_le_rpow_of_exponent_le hQ.le (by push_cast; linarith [P.ε₁_pos])
    nlinarith
  have hY' : (⌊P.Y Q⌋₊ : ℝ) ≤ Q ^ (2 - P.ε₁) := (Nat.floor_le (P.Y_nonneg Q)).trans hYr
  have : 0 ≤ ν * C₀' := mul_nonneg hν hC₀'
  nlinarith

lemma 𝒦_le_ell {Q T Cd bI lam ℓ Jl : ℝ} {n : ℕ} (hK : (P.𝒦 Q T n n).re ≤ 2 * Real.pi * Jl * (bI * (lam * ℓ)) + Cd)
    (hCd : 0 ≤ Cd) (hJlℓ : 1 / 2 ≤ Jl * ℓ) :
    (P.𝒦 Q T n n).re ≤ (2 * Real.pi * bI * lam + 2 * Cd) * Jl * ℓ := by
  have : Cd ≤ 2 * Cd * (Jl * ℓ) := by nlinarith
  nlinarith

/-! ### Small helpers for the final assembly -/

lemma sab_le {SA SB SS μ Cs ℓ Cn : ℝ} (hSA : SA ≤ μ * (μ + 6) * ℓ ^ 2)
    (hSS : SS ≤ (8 * (1 + μ) + Cs) * ℓ ^ 2) (hSB : SB ≤ 2 * SA + 2 * SS) (hSA0 : 0 ≤ SA)
    (hSS0 : 0 ≤ SS)
    (hCn : Cn = 2 * μ * (μ + 6) + 2 * (8 * (1 + μ) + Cs) + μ * (μ + 6) + (8 * (1 + μ) + Cs)) :
    SA + SB ≤ Cn * ℓ ^ 2 ∧ SS ≤ Cn * ℓ ^ 2 := by
  rw [hCn]
  constructor <;> nlinarith

lemma C1_le {C₁ tgt θ₀ la Jl : ℝ} (htgt : 0 < tgt) (hθ₀ : 0 < θ₀) (hE1 : 4 * C₁ / (tgt * θ₀) ≤ la)
    (hJl : θ₀ * la ≤ Jl) : C₁ ≤ tgt * Jl / 4 := by
  rw [div_le_iff₀ (by positivity)] at hE1
  have := mul_le_mul_of_nonneg_left hJl htgt.le
  nlinarith

lemma C_le_of {C q t : ℝ} (hC : 0 ≤ C) (hq : 0 ≤ q) (h : q ≤ t / (C + 1)) :
    C * q ≤ t := by
  rw [le_div_iff₀ (by linarith)] at h
  nlinarith

lemma C_le_of' {C q ℓ t : ℝ} (hC : 0 ≤ C) (hq : 0 ≤ q) (hℓ : 0 ≤ ℓ)
    (h : q * (1 + ℓ) ≤ t / (C + 1)) : C * q * ℓ ≤ t := by
  have h1 := C_le_of hC (by positivity) h
  have : C * q * ℓ ≤ C * (q * (1 + ℓ)) := by nlinarith [mul_nonneg hC hq]
  linarith

lemma Jl_facts {θ₀ T ℓ : ℝ} (hθ₀ : 1 / 2 < θ₀) (hT : 1 ≤ T) (hℓ : 1 ≤ ℓ) :
    1 / 2 ≤ θ₀ * T ∧ 1 / 2 ≤ θ₀ * T * ℓ := by
  have h1 : θ₀ * 1 ≤ θ₀ * T := mul_le_mul_of_nonneg_left hT (by linarith)
  have h2 : 1 / 2 ≤ θ₀ * T := by linarith
  refine ⟨h2, ?_⟩
  have := mul_le_mul h2 hℓ (by norm_num) (by linarith)
  linarith

end Families.Phase3.C
