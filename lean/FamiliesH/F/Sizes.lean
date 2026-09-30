/-
# Package F: the size facts `lem:sizes` (Lemma 9.1, (S1)–(S4))

Everything is reduced to linear inequalities between the exponents `ℓ = log Q` and `t = log T`
(`0 ≤ t ≤ κc ℓ` on the cell) and monotonicity of `exp`.
-/
import FamiliesH.F.Bridge

noncomputable section

open Real

namespace Families.Hybrid

open Families


namespace HSetup

open Families.Hybrid.F

variable (P : HSetup)

/-- `Y = exp(λ(1+ε₁)(log Q + log T))`. -/
lemma Y_exp {Q T : ℝ} (hQ : 0 < Q) (hT : 0 < T) :
    P.Y Q T = Real.exp (P.lam * (1 + P.ε₁) * (Real.log Q + Real.log T)) := by
  unfold HSetup.Y HSetup.X HSetup.L ellS
  rw [← Real.exp_mul, Real.log_mul hQ.ne' hT.ne']
  congr 1; ring

/-- `β(κc)(ℓ + t) ≤ 2ℓ + t` for `t ≤ κc ℓ`. -/
lemma betaK_mul_le {ℓ t : ℝ} (ht : t ≤ P.kc * ℓ) : betaK P.kc * (ℓ + t) ≤ 2 * ℓ + t := by
  have hkc := P.kc_pos
  unfold betaK
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  linarith

/-- (S1) in logarithmic form: `λ(1+ε₁)(ℓ+t) ≤ (2−ε₁)ℓ + (1−ε₁)t` for `0 ≤ ℓ`, `0 ≤ t ≤ κc ℓ`. -/
lemma S1_log {ℓ t : ℝ} (hℓ : 0 ≤ ℓ) (ht0 : 0 ≤ t) (ht : t ≤ P.kc * ℓ) :
    P.lam * (1 + P.ε₁) * (ℓ + t) ≤ (2 - P.ε₁) * ℓ + (1 - P.ε₁) * t := by
  have hβ := P.betaK_mul_le ht
  have h1 : P.lam * (1 + P.ε₁) * (ℓ + t) ≤ (betaK P.kc - P.ε₁) * (ℓ + t) :=
    mul_le_mul_of_nonneg_right P.lam_ε₁ (by linarith)
  linarith

end HSetup

namespace F

lemma le_log_of_exp_le {c Q : ℝ} (h : Real.exp c ≤ Q) : c ≤ Real.log Q := by
  have := Real.log_le_log (Real.exp_pos c) h
  rwa [Real.log_exp] at this

/-- `6 ≤ exp(x)` as soon as `log 6 ≤ x`. -/
lemma six_le_exp {x : ℝ} (h : Real.log 6 ≤ x) : (6 : ℝ) ≤ Real.exp x := by
  have := Real.exp_le_exp.mpr h
  rwa [Real.exp_log (by norm_num)] at this

/-- `5 e^a + 1 ≤ e^{b + a}` when `6 ≤ e^b` and `0 ≤ a`. -/
lemma five_exp_add_one_le {a b : ℝ} (ha : 0 ≤ a) (hb : (6 : ℝ) ≤ Real.exp b) :
    5 * Real.exp a + 1 ≤ Real.exp (b + a) := by
  have h1 : (1 : ℝ) ≤ Real.exp a := Real.one_le_exp ha
  rw [Real.exp_add]
  have h2 := mul_le_mul_of_nonneg_right hb (Real.exp_pos a).le
  linarith

/-- `2 exp(A) < exp(2(ℓ+t))` when `A ≤ 2(ℓ+t) − ε₁ℓ` and `6 ≤ exp(ε₁ℓ/2)`. -/
lemma two_exp_lt {A B c : ℝ} (hA : A ≤ B - c) (h6 : (6 : ℝ) ≤ Real.exp (c / 2)) :
    2 * Real.exp A < Real.exp B := by
  have h36 : (2 : ℝ) < Real.exp c := by
    have : Real.exp c = Real.exp (c / 2) * Real.exp (c / 2) := by
      rw [← Real.exp_add]; ring_nf
    rw [this]
    have h := mul_le_mul h6 h6 (by norm_num) (Real.exp_pos _).le
    linarith
  have hsplit : Real.exp B = Real.exp c * Real.exp (B - c) := by
    rw [← Real.exp_add]; ring_nf
  rw [hsplit]
  have h1 := Real.exp_le_exp.mpr hA
  have hpos := Real.exp_pos (B - c)
  have h2 := mul_lt_mul_of_pos_right h36 hpos
  linarith

/-- **`lem:sizes`** (Lemma 9.1). -/
theorem lemSizesH_proof : lemSizesH_Statement := by
  intro P ε hε hεmax ε₅
  have hε₅def : ε₅ = min ε P.ε₁ / (4 * (1 + P.kc)) := rfl
  have hkc := P.kc_pos
  have hε₁ := P.ε₁_pos
  have hlam := P.lam_pos
  have h4 : 0 < 4 * (1 + P.kc) := by linarith
  set m := min ε P.ε₁ with hm
  have hm_le_ε : m ≤ ε := min_le_left _ _
  have hm_le_ε₁ : m ≤ P.ε₁ := min_le_right _ _
  have hm_pos : 0 < m := lt_min hε hε₁
  have hε₅pos : 0 < ε₅ := by rw [hε₅def]; positivity
  have hε₅m : ε₅ * (4 * (1 + P.kc)) = m := by rw [hε₅def]; field_simp
  have hε₅kc : 0 < ε₅ * P.kc := mul_pos hε₅pos hkc
  have hε₅_le_ε : ε₅ ≤ ε / 4 := by linarith
  have hε₅_le_ε₁ : ε₅ ≤ P.ε₁ / 4 := by linarith
  have hkcε₅ : P.kc * ε₅ ≤ m / 4 := by linarith
  have hkcε₅_ε : P.kc * ε₅ ≤ ε / 4 := by linarith
  have hkcε₅_ε₁ : P.kc * ε₅ ≤ P.ε₁ / 4 := by linarith
  have hε1kc : ε * (1 + P.kc) ≤ 1 / 8 := by
    rw [le_div_iff₀ (by positivity)] at hεmax
    linarith
  have hε8 : ε ≤ 1 / 8 := by linarith [mul_pos hε hkc]
  refine ⟨max (Real.exp 1) (max (Real.exp (2 * Real.log 6 / ε))
    (max (Real.exp (32 / 3 * Real.log 6)) (Real.exp (2 * Real.log 6 / P.ε₁)))), ?_⟩
  intro Q hQ T hT
  -- the thresholds
  have hQe : Real.exp 1 ≤ Q := le_trans (le_max_left _ _) hQ
  have hQa : Real.exp (2 * Real.log 6 / ε) ≤ Q :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hQ
  have hQb : Real.exp (32 / 3 * Real.log 6) ≤ Q :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hQ
  have hQc : Real.exp (2 * Real.log 6 / P.ε₁) ≤ Q :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hQ
  have hQ0 : 0 < Q := lt_of_lt_of_le (Real.exp_pos _) hQe
  set ℓ := Real.log Q with hℓ
  have hℓ1 : 1 ≤ ℓ := le_log_of_exp_le hQe
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hℓa : 2 * Real.log 6 / ε ≤ ℓ := le_log_of_exp_le hQa
  have hℓb : 32 / 3 * Real.log 6 ≤ ℓ := le_log_of_exp_le hQb
  have hℓc : 2 * Real.log 6 / P.ε₁ ≤ ℓ := le_log_of_exp_le hQc
  have h6a : (6 : ℝ) ≤ Real.exp (ε / 2 * ℓ) := by
    apply six_le_exp
    rw [div_le_iff₀ hε] at hℓa; linarith
  have h6b : (6 : ℝ) ≤ Real.exp (3 / 32 * ℓ) := six_le_exp (by linarith)
  have h6c : (6 : ℝ) ≤ Real.exp (P.ε₁ / 2 * ℓ) := by
    apply six_le_exp
    rw [div_le_iff₀ hε₁] at hℓc; linarith
  have h6c' : (6 : ℝ) ≤ Real.exp (P.ε₁ * ℓ / 2) := by
    rw [show P.ε₁ * ℓ / 2 = P.ε₁ / 2 * ℓ by ring]; exact h6c
  -- the height
  obtain ⟨hTlo, hThi⟩ := hT
  have hT1 : 1 ≤ T := le_trans (Real.one_le_rpow hℓ1 P.a0_pos.le) hTlo
  have hT0 : 0 < T := by linarith
  set t := Real.log T with htdef
  have ht0 : 0 ≤ t := Real.log_nonneg hT1
  have htk : t ≤ P.kc * ℓ := by
    have := Real.log_le_log hT0 hThi
    rwa [Real.log_rpow hQ0] at this
  have hQT0 : 0 < Q * T := mul_pos hQ0 hT0
  have hlogQT : Real.log (Q * T) = ℓ + t := Real.log_mul hQ0.ne' hT0.ne'
  have hS1 := P.S1_log hℓ0 ht0 htk
  have hY : P.Y Q T = Real.exp (P.lam * (1 + P.ε₁) * (ℓ + t)) := P.Y_exp hQ0 hT0
  have hQr : ∀ a : ℝ, Q ^ a = Real.exp (ℓ * a) := fun a => Real.rpow_def_of_pos hQ0 a
  have hTr : ∀ a : ℝ, T ^ a = Real.exp (t * a) := fun a => Real.rpow_def_of_pos hT0 a
  have hQTsq : (Q * T) ^ 2 = Real.exp (2 * (ℓ + t)) := by
    have : Q * T = Real.exp (ℓ + t) := by rw [← hlogQT, Real.exp_log hQT0]
    rw [this, ← Real.exp_nat_mul]; norm_num
  have hA : P.lam * (1 + P.ε₁) * (ℓ + t) ≤ 2 * (ℓ + t) - P.ε₁ * ℓ := by
    linarith [mul_nonneg hε₁.le ht0]
  have hY2 : 2 * P.Y Q T < (Q * T) ^ 2 := by
    rw [hY, hQTsq]; exact two_exp_lt hA h6c'
  refine ⟨⟨?_, hY2⟩, ?_, ?_, ?_⟩
  · -- (S1a)
    rw [hY, hQr, hTr, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  · -- (S2)
    intro u hu
    have hexpT : 5 * T ^ (-1 + ε₅) * Real.exp u + 1 =
        5 * Real.exp (t * (-1 + ε₅) + u) + 1 := by
      rw [hTr, Real.exp_add]; ring
    have hL : P.L Q T = P.lam * (ℓ + t) := by
      unfold HSetup.L ellS; rw [hlogQT]
    refine ⟨?_, ?_, ?_⟩
    · intro hu1
      rw [hexpT, hQr]
      unfold ellS at hu1; rw [hlogQT] at hu1
      have hexp : t * (-1 + ε₅) + u ≤ (1 - ε) * ℓ := by
        linarith [mul_nonneg ht0 (by linarith : (0:ℝ) ≤ ε - ε₅)]
      have hmono := Real.exp_le_exp.mpr hexp
      have hkey := five_exp_add_one_le (a := (1 - ε) * ℓ) (mul_nonneg (by linarith) hℓ0) h6a
      have : ε / 2 * ℓ + (1 - ε) * ℓ = ℓ * (1 - ε / 2) := by ring
      rw [this] at hkey
      linarith
    · intro hu2
      rw [hexpT, hQr]
      unfold ellS at hu2; rw [hlogQT] at hu2
      have hte : t * (ε + ε₅) ≤ P.kc * ℓ * (ε + ε₅) :=
        mul_le_mul_of_nonneg_right htk (by linarith)
      have hexp : t * (-1 + ε₅) + u ≤ 37 / 32 * ℓ := by
        linarith [mul_le_mul_of_nonneg_left hε1kc hℓ0, mul_le_mul_of_nonneg_left hkcε₅_ε hℓ0,
          mul_le_mul_of_nonneg_left hε8 hℓ0]
      have hmono := Real.exp_le_exp.mpr hexp
      have hkey := five_exp_add_one_le (a := 37 / 32 * ℓ) (by linarith) h6b
      have : 3 / 32 * ℓ + 37 / 32 * ℓ = ℓ * (5 / 4) := by ring
      rw [this] at hkey
      linarith
    · rw [hexpT, hQr]
      rw [hL] at hu
      have hlamle : P.lam * (ℓ + t) ≤ P.lam * (1 + P.ε₁) * (ℓ + t) := by
        linarith [mul_nonneg (mul_nonneg hlam.le hε₁.le) (by linarith : (0:ℝ) ≤ ℓ + t)]
      have hexp : t * (-1 + ε₅) + u ≤ (2 - P.ε₁) * ℓ := by
        linarith [mul_nonneg ht0 (by linarith : (0:ℝ) ≤ P.ε₁ - ε₅)]
      have hmono := Real.exp_le_exp.mpr hexp
      have hkey := five_exp_add_one_le (a := (2 - P.ε₁) * ℓ)
        (mul_nonneg (by linarith [P.ε₁_lt]) hℓ0) h6c
      have : P.ε₁ / 2 * ℓ + (2 - P.ε₁) * ℓ = ℓ * (2 - P.ε₁ / 2) := by ring
      rw [this] at hkey
      linarith
  · -- (S3)
    intro j hj
    set N : ℝ := (2 : ℝ) ^ j with hN
    have hN1 : 1 ≤ N := one_le_pow₀ (by norm_num)
    have hN0 : 0 < N := by linarith
    have hfl : (P.Rj Q T j : ℝ) ≤ N ^ (1 - P.ε₃) / (Q * T) := by
      unfold HSetup.Rj; exact Nat.floor_le (by positivity)
    have hNε : N ^ (1 - P.ε₃) ≤ N := by
      have := Real.rpow_le_rpow_of_exponent_le hN1 (show 1 - P.ε₃ ≤ 1 by linarith [P.ε₃_pos])
      simpa using this
    refine ⟨?_, ?_⟩
    · calc (P.Rj Q T j : ℝ) ≤ N ^ (1 - P.ε₃) / (Q * T) := hfl
        _ ≤ N / (Q * T) := div_le_div_of_nonneg_right hNε hQT0.le
        _ ≤ 2 * P.Y Q T / (Q * T) := div_le_div_of_nonneg_right hj hQT0.le
    · have hsq : N ^ ((1 : ℝ) / 2) ≤ Q * T := by
        rw [← Real.sqrt_eq_rpow]
        calc Real.sqrt N ≤ Real.sqrt ((Q * T) ^ 2) := Real.sqrt_le_sqrt (by linarith)
          _ = Q * T := Real.sqrt_sq hQT0.le
      have hsplitN : N ^ (1 - P.ε₃) = N ^ ((1 : ℝ) / 2) * N ^ ((1 : ℝ) / 2 - P.ε₃) := by
        rw [← Real.rpow_add hN0]; ring_nf
      calc (P.Rj Q T j : ℝ) ≤ N ^ (1 - P.ε₃) / (Q * T) := hfl
        _ = N ^ ((1 : ℝ) / 2) * N ^ ((1 : ℝ) / 2 - P.ε₃) / (Q * T) := by rw [hsplitN]
        _ ≤ Q * T * N ^ ((1 : ℝ) / 2 - P.ε₃) / (Q * T) := by
            apply div_le_div_of_nonneg_right _ hQT0.le
            exact mul_le_mul_of_nonneg_right hsq (by positivity)
        _ = N ^ ((1 : ℝ) / 2 - P.ε₃) := by field_simp
  · -- (S4)
    have hinv : (T ^ (-(ε₅ / 2)))⁻¹ = T ^ (ε₅ / 2) := by
      rw [Real.rpow_neg hT0.le, inv_inv]
    rw [hinv, hTr, hQr]
    have h1 : t * (ε₅ / 2) ≤ ℓ * (P.ε₁ / 8) := by
      have : t * (ε₅ / 2) ≤ P.kc * ℓ * (ε₅ / 2) := mul_le_mul_of_nonneg_right htk (by linarith)
      linarith [mul_le_mul_of_nonneg_left hkcε₅_ε₁ hℓ0]
    have h2 := Real.exp_le_exp.mpr h1
    have h3 : (1 : ℝ) ≤ Real.exp (ℓ * (P.ε₁ / 8)) := Real.one_le_exp (by positivity)
    linarith

end F

end Families.Hybrid
