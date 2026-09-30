/-
# Package F: `cor:tails` (Corollary 9.14)

The tails at the localisation scale `δ = T^{−1+ε₅}` are negligible. We apply `lem:M3′`
(`lemM3primeH_proof`) with `g₁ = g ≤ g_∞ = bL` (`PrimeSetup.g_le` at `Q' = QT`), the multiplicative
large sieve with `C₀ = 17/4` (`Families.Hyp.mvMult_of_add`), the norm bounds `‖a‖², ‖b‖² ≪ ℓ_*²`
(`eqB:norms`, (5.10), at `Q' = QT`, no PNT) and `H ≥ ½ ℰ I_w Q²` (`lem:WH`). With `t = log T`,
`ℓ = log Q`, `k = k₀ + 4 ≤ 2t + 5`:

  `(1 + κ_loc⁻¹) · RHS(M3′) ≤ 2 K C_y L ℓ_*² Q² T · k² (2 e^{−ε₅t/2} + e^{−ε₁ℓ})`,

and `t² e^{−ε₅t/2} ≤ 48/(ε₅³ t)`, `t² e^{−ε₁ℓ} ≤ κc² ℓ² e^{−ε₁ℓ} ≤ 6κc²/(ε₁³ℓ)`, while
`t ≥ a₀ log ℓ → ∞` in the cell. This is exactly the paper's argument (with the cruder but sufficient
`Y ≤ Q² T Q^{−ε₁}` from (S1)).
-/
import FamiliesH.F.M3prime
import Families.Phase3.C.TIsharpNorms
import Families.Assembly
import Families.Wired.Phase2
import Families.Hyp.MVLargeSieve

noncomputable section

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace Families.Hybrid

open Families

namespace F

/-! ### Elementary real estimates -/

/-- `x² e^{−ax} ≤ 6/(a³x)` for `a, x > 0` (from `e^{ax} ≥ (ax)³/6`). -/
lemma sq_mul_exp_neg_le {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    x ^ 2 * Real.exp (-(a * x)) ≤ 6 / (a ^ 3 * x) := by
  have h := Real.pow_div_factorial_le_exp (a * x) (mul_pos ha hx).le 3
  have hfac : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [hfac] at h
  have he := Real.exp_pos (a * x)
  have hax : 0 < a ^ 3 * x := by positivity
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ he hax]
  have e : (a * x) ^ 3 = x ^ 2 * (a ^ 3 * x) := by ring
  rw [e] at h
  linarith

/-- `k₀ = ⌈log₂(1/δ)⌉ ≤ 2 log T + 1` for `δ = T^{−1+ε₅}`, `T ≥ 1`, `0 < ε₅ < 1`. -/
lemma k0_le {T ε₅ : ℝ} (hT : 1 ≤ T) (hε₅ : 0 < ε₅) (hε₅1 : ε₅ < 1) :
    (⌈Real.logb 2 (1 / T ^ (-1 + ε₅))⌉₊ : ℝ) ≤ 2 * Real.log T + 1 := by
  have hT0 : 0 < T := by linarith
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hl2 : 1 / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hx : Real.logb 2 (1 / T ^ (-1 + ε₅)) = (1 - ε₅) * Real.log T / Real.log 2 := by
    rw [one_div, Real.logb, Real.log_inv, Real.log_rpow hT0]; ring
  have hx0 : 0 ≤ Real.logb 2 (1 / T ^ (-1 + ε₅)) := by
    rw [hx]; apply div_nonneg _ (by linarith); nlinarith
  have hc := Nat.ceil_lt_add_one hx0
  have h2 : (1 - ε₅) * Real.log T / Real.log 2 ≤ 2 * Real.log T := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg hlogT (by linarith : (0 : ℝ) ≤ 2 * Real.log 2 - 1),
      mul_nonneg hε₅.le hlogT]
  rw [hx] at hc ⊢
  linarith

/-- `e^{−2} ≤ 1/4`. -/
lemma exp_neg_two_le : Real.exp (-2) ≤ 1 / 4 := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num), e]
  nlinarith

end F

namespace HSetup

open Families.Hybrid.F

variable (P : HSetup)

lemma bInt_nonneg : 0 ≤ P.bInt := by
  rw [P.bInt_eq]; unfold PrimeSetup.bInt; exact integral_nonneg fun _ => sq_nonneg _

/-- **`eqB:norms`** at `Q' = QT` (no PNT): `‖a‖², ‖b‖² ≤ C ℓ_*²` once `ℓ_* ≥ 1`. -/
lemma sum_sq_y_le : ∃ C Q₀ : ℝ, 0 ≤ C ∧ ∀ Q T : ℝ, Q₀ ≤ Q → 1 ≤ T → 1 ≤ ellS Q T →
    ∀ y ∈ ({P.aVec Q T, P.bVec Q T} : Set (ℕ → ℝ)),
      ∑ n ∈ P.range Q T, y n ^ 2 ≤ C * ellS Q T ^ 2 := by
  obtain ⟨Cs, Qs, hCs0, hs⟩ := Families.Phase3.C.sum_sq_aSharp_le P.toPS
  refine ⟨100 + 2 * Cs, max Qs 1, by linarith, ?_⟩
  intro Q T hQ hT hℓ y hy
  have hQ1 : 1 ≤ Q := le_of_max_le_right hQ
  have hQT : Q ≤ Q * T := by nlinarith
  have hQTs : Qs ≤ Q * T := le_trans (le_of_max_le_left hQ) hQT
  have hQT1 : 1 < Q * T := by
    by_contra hc
    replace hc := not_lt.mp hc
    have h1 : Q * T = 1 := le_antisymm hc (by nlinarith)
    have : ellS Q T = 0 := by unfold ellS; rw [h1, Real.log_one]
    linarith
  set ℓ := ellS Q T with hℓdef
  have hlogY : Real.log (P.toPS.Y (Q * T)) = P.lam * (1 + P.ε₁) * ℓ := by
    rw [Families.Phase3.C.log_Y P.toPS]
    unfold PrimeSetup.L; rw [hℓdef]; unfold ellS; simp only [toPS]; ring
  have hc : P.lam * (1 + P.ε₁) ≤ 5 / 2 := by
    have h1 := P.lam_lt
    have h2 := betaK_le_two P.kc_pos.le
    have h3 := P.ε₁_lt
    have h4 := P.ε₁_pos
    nlinarith [P.lam_pos]
  have hc0 : 0 ≤ P.lam * (1 + P.ε₁) := by have := P.lam_pos; have := P.ε₁_pos; positivity
  -- `‖a‖² ≤ 22 ℓ²`
  have ha : ∑ n ∈ P.range Q T, P.aVec Q T n ^ 2 ≤ 22 * ℓ ^ 2 := by
    have h := Families.Phase3.C.sum_sq_aVec_le P.toPS hQT1
    rw [hlogY] at h
    have e1 : ∑ n ∈ P.range Q T, P.aVec Q T n ^ 2 =
        ∑ n ∈ P.toPS.range (Q * T), P.toPS.aVec (Q * T) n ^ 2 := rfl
    rw [e1]
    refine h.trans ?_
    set c := P.lam * (1 + P.ε₁)
    have hcl : c * ℓ ≤ 5 / 2 * ℓ := mul_le_mul_of_nonneg_right hc (by linarith)
    have hcl0 : 0 ≤ c * ℓ := mul_nonneg hc0 (by linarith)
    nlinarith
  -- `‖a♯‖² ≤ (28 + C) ℓ²`
  have hs' : ∑ n ∈ P.range Q T, P.aSharp Q T n ^ 2 ≤ (28 + Cs) * ℓ ^ 2 := by
    have h := hs (Q * T) hQTs 1 le_rfl
    rw [hlogY] at h
    have e1 : ∑ n ∈ P.range Q T, P.aSharp Q T n ^ 2 =
        ∑ n ∈ P.toPS.range (Q * T), P.toPS.aSharp (Q * T) 1 n ^ 2 := by
      rw [P.aSharp_eq]; rfl
    rw [e1]
    refine h.trans ?_
    have hlQ : Real.log (Q * T) = ℓ := rfl
    rw [hlQ]
    set c := P.lam * (1 + P.ε₁)
    have hcl : c * ℓ ≤ 5 / 2 * ℓ := mul_le_mul_of_nonneg_right hc (by linarith)
    have hcl0 : 0 ≤ c * ℓ := mul_nonneg hc0 (by linarith)
    have hℓ2 : 1 ≤ ℓ ^ 2 := by nlinarith
    nlinarith
  rcases hy with rfl | rfl
  · nlinarith [sq_nonneg ℓ]
  · have hb : ∀ n, P.bVec Q T n ^ 2 ≤ 2 * P.aVec Q T n ^ 2 + 2 * P.aSharp Q T n ^ 2 := by
      intro n
      unfold HSetup.bVec
      nlinarith [sq_nonneg (P.aVec Q T n + P.aSharp Q T n)]
    refine (Finset.sum_le_sum fun n _ => hb n).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    nlinarith

end HSetup

namespace F

/-! ### `cor:tails` -/

set_option maxHeartbeats 1600000 in
/-- **`cor:tails`** (Corollary 9.14). -/
theorem corTailsH_proof : corTailsH_Statement := by
  intro P W ρ hρ ε hε hε8 ε₅ η hη
  have hkc := P.kc_pos
  have hε₁ := P.ε₁_pos
  have hε₁4 := P.ε₁_lt
  have ha0 := P.a0_pos
  have hlam := P.lam_pos
  have hθ := P.θ_lt
  have hε₅def : ε₅ = min ε P.ε₁ / (4 * (1 + P.kc)) := rfl
  have hmin0 : 0 < min ε P.ε₁ := lt_min hε hε₁
  have hmin1 : min ε P.ε₁ ≤ P.ε₁ := min_le_right _ _
  have hε₅0 : 0 < ε₅ := by rw [hε₅def]; positivity
  have hε₅1 : ε₅ ≤ P.ε₁ / 4 := by
    rw [hε₅def, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hε₅2 : ε₅ < 1 / 16 := by linarith
  -- the constants
  set C₀ : ℝ := 17 / 4 with hC₀def
  have hC₀ : 0 ≤ C₀ := by norm_num
  have hMV : MVLargeSieveMult C₀ :=
    Families.Hyp.mvMult_of_add (by norm_num) Families.Hyp.mvAdd_proof
  obtain ⟨Cy, Qy, hCy0, hy⟩ := P.sum_sq_y_le
  obtain ⟨QH, hQH⟩ := Filter.eventually_atTop.1
    (Families.H_lower_eventually Families.lemWH W (κ := 1 / 2) (by norm_num))
  set cH := Ecal * W.Iw with hcH
  have hcH0 : 0 < cH := mul_pos Ecal_pos W.Iw_pos
  have hb0 := P.bInt_nonneg
  have hw0 := W.wmax_nonneg
  set K' := 48 * C₀ * P.bInt * W.wmax with hK'
  have hK'0 : 0 ≤ K' := by positivity
  set B := 98 * K' * Cy with hB
  have hB0 : 0 ≤ B := by positivity
  set D := η * P.lam * cH / 4 with hD
  have hD0 : 0 < D := by positivity
  set t₁ := 192 * B / (ε₅ ^ 3 * D) + 4 with ht₁
  have ht₁3 : 4 ≤ t₁ := by have : 0 ≤ 192 * B / (ε₅ ^ 3 * D) := by positivity
                           linarith
  set ℓ₁ := 12 * B * P.kc ^ 2 / (P.ε₁ ^ 3 * D) + 1 with hℓ₁
  have hℓ₁1 : 1 ≤ ℓ₁ := by have : 0 ≤ 12 * B * P.kc ^ 2 / (P.ε₁ ^ 3 * D) := by positivity
                           linarith
  refine ⟨max (max (max Qy QH) 1) (max (Real.exp ℓ₁) (Real.exp (Real.exp (t₁ / P.a0)))), ?_⟩
  intro Q hQ T hT y hyab δ xt
  -- the sizes of `Q` and `T`
  have hQy : Qy ≤ Q := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_of_max_le_left hQ))
  have hQH' : QH ≤ Q :=
    le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_of_max_le_left hQ))
  have hQ1 : 1 ≤ Q := le_trans (le_max_right _ _) (le_of_max_le_left hQ)
  have hQℓ₁ : Real.exp ℓ₁ ≤ Q := le_trans (le_max_left _ _) (le_of_max_le_right hQ)
  have hQt₁ : Real.exp (Real.exp (t₁ / P.a0)) ≤ Q := le_trans (le_max_right _ _) (le_of_max_le_right hQ)
  have hQ0 : 0 < Q := by linarith
  set ℓ := Real.log Q with hℓdef
  have hℓℓ₁ : ℓ₁ ≤ ℓ := le_log_of_exp_le hQℓ₁
  have hℓ1 : 1 ≤ ℓ := le_trans hℓ₁1 hℓℓ₁
  have hℓt₁ : Real.exp (t₁ / P.a0) ≤ ℓ := le_log_of_exp_le hQt₁
  have hℓ0 : 0 < ℓ := by linarith
  simp only [HSetup.heights, cellHeights, Set.mem_Icc] at hT
  obtain ⟨hTlo, hThi⟩ := hT
  have hT0 : 0 < T := lt_of_lt_of_le (Real.rpow_pos_of_pos hℓ0 _) hTlo
  set t := Real.log T with htdef
  have htℓ : t ≤ P.kc * ℓ := by
    have := Real.log_le_log hT0 hThi
    rwa [Real.log_rpow hQ0] at this
  have ht₁t : t₁ ≤ t := by
    have h1 := Real.log_le_log (Real.rpow_pos_of_pos hℓ0 _) hTlo
    rw [Real.log_rpow hℓ0] at h1
    have h2 : t₁ / P.a0 ≤ Real.log ℓ := le_log_of_exp_le hℓt₁
    have h3 : t₁ ≤ P.a0 * Real.log ℓ := by
      rw [div_le_iff₀ ha0] at h2; linarith
    linarith
  have ht3 : 4 ≤ t := le_trans ht₁3 ht₁t
  have hT1' : 1 < T := (Real.log_pos_iff hT0.le).mp (by linarith)
  have hT1 : 1 ≤ T := hT1'.le
  have hQT1 : 1 < Q * T := by nlinarith [mul_pos hQ0 (by linarith : (0 : ℝ) < T - 1)]
  set ℓs := ellS Q T with hℓsdef
  have hℓs : ℓs = ℓ + t := by
    rw [hℓsdef]; unfold ellS; rw [Real.log_mul hQ0.ne' hT0.ne']
  have hℓs1 : 1 ≤ ℓs := by rw [hℓs]; linarith
  have hℓs0 : 0 < ℓs := by linarith
  -- `δ` and the M3′ bound
  have hδdef : δ = T ^ (-1 + ε₅) := rfl
  have hδexp : δ = Real.exp (t * (-1 + ε₅)) := by rw [hδdef, Real.rpow_def_of_pos hT0]
  have hδ0 : 0 < δ := by rw [hδexp]; exact Real.exp_pos _
  have hδ4 : δ ≤ 1 / 4 := by
    rw [hδexp]
    refine le_trans (Real.exp_le_exp.mpr ?_) exp_neg_two_le
    have h := mul_le_mul ht3 (by linarith : (15 / 16 : ℝ) ≤ 1 - ε₅) (by norm_num) (by linarith)
    linarith only [h]
  have hLpos : 0 < P.L Q T := by
    unfold HSetup.L; rw [← hℓsdef]; positivity
  have hgmeas : Measurable (P.g Q T) := by
    have : P.g Q T = P.toPS.g (Q * T) := rfl
    rw [this]; exact (P.toPS.g_continuous hQT1).measurable
  have hgbd : ∀ u, 0 ≤ P.g Q T u ∧ P.g Q T u ≤ P.bInt * P.L Q T := fun u =>
    ⟨P.toPS.g_nonneg (Q * T) u, P.toPS.g_le hQT1 u⟩
  have hM3 := lemM3primeH_proof C₀ hMV hC₀ P W ρ hρ Q T δ hQ1 hT0 hδ0 hδ4 y (P.g Q T)
    (P.bInt * P.L Q T) hgmeas hgbd
  dsimp only at hM3
  set S := ∑ n ∈ P.range Q T, y n ^ 2 with hSdef
  have hS : S ≤ Cy * ℓs ^ 2 := hy Q T hQy hT1 hℓs1 y hyab
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- exponential forms
  have hQexp : Q = Real.exp ℓ := by rw [hℓdef, Real.exp_log hQ0]
  have hTexp : T = Real.exp t := by rw [htdef, Real.exp_log hT0]
  have ht0 : 0 ≤ t := by linarith
  have hA : 1 + (T ^ (-(ε₅ / 2)))⁻¹ ≤ 2 * Real.exp (ε₅ / 2 * t) := by
    rw [Real.rpow_def_of_pos hT0, ← Real.exp_neg, ← htdef]
    have e : -(t * -(ε₅ / 2)) = ε₅ / 2 * t := by ring
    rw [e]
    have : 1 ≤ Real.exp (ε₅ / 2 * t) := Real.one_le_exp (by positivity)
    linarith only [this]
  have hAnn : 0 ≤ 1 + (T ^ (-(ε₅ / 2)))⁻¹ := by
    have := Real.rpow_pos_of_pos hT0 (-(ε₅ / 2)); positivity
  have hk0 : (⌈Real.logb 2 (1 / δ)⌉₊ : ℝ) ≤ 2 * t + 1 := k0_le hT1 hε₅0 (by linarith)
  have hk00 : (0 : ℝ) ≤ (⌈Real.logb 2 (1 / δ)⌉₊ : ℝ) := Nat.cast_nonneg _
  set k : ℝ := (⌈Real.logb 2 (1 / δ)⌉₊ : ℝ) + 4 with hkdef
  have hk1 : 1 ≤ k := by linarith only [hk00, hkdef]
  have hk7 : k ≤ 7 * t := by linarith only [hk0, hkdef, ht3]
  set Y := P.Y Q T with hYdef
  have hY0 : 0 ≤ Y := by rw [hYdef, P.Y_exp hQ0 hT0]; exact (Real.exp_pos _).le
  -- `R₀ ≤ K' L k (k (2Q²/δ + Y)) (C_y ℓ_*²)`
  have hR₀ : 48 * C₀ * (P.bInt * P.L Q T) * W.wmax * k *
      ((Q ^ 2 + 1) / δ + ((⌈Real.logb 2 (1 / δ)⌉₊ : ℝ) + 3) * Y) * S ≤
      K' * P.L Q T * k * (k * (2 * Q ^ 2 / δ + Y)) * (Cy * ℓs ^ 2) := by
    have e : 48 * C₀ * (P.bInt * P.L Q T) * W.wmax * k *
        ((Q ^ 2 + 1) / δ + ((⌈Real.logb 2 (1 / δ)⌉₊ : ℝ) + 3) * Y) * S =
        K' * P.L Q T * k * ((Q ^ 2 + 1) / δ + ((⌈Real.logb 2 (1 / δ)⌉₊ : ℝ) + 3) * Y) * S := by
      rw [hK']; ring
    rw [e]
    have hQ2 : 1 ≤ Q ^ 2 := by nlinarith only [hQ1]
    have h1 : (Q ^ 2 + 1) / δ ≤ 2 * Q ^ 2 / δ := by
      apply div_le_div_of_nonneg_right _ hδ0.le; linarith only [hQ2]
    have h2 : 2 * Q ^ 2 / δ ≤ k * (2 * Q ^ 2 / δ) :=
      le_mul_of_one_le_left (by positivity) hk1
    have h3 : ((⌈Real.logb 2 (1 / δ)⌉₊ : ℝ) + 3) * Y ≤ k * Y :=
      mul_le_mul_of_nonneg_right (by linarith only [hkdef]) hY0
    have h4 : (Q ^ 2 + 1) / δ + ((⌈Real.logb 2 (1 / δ)⌉₊ : ℝ) + 3) * Y ≤ k * (2 * Q ^ 2 / δ + Y) := by
      rw [mul_add]; linarith only [h1, h2, h3]
    have h5 : 0 ≤ (Q ^ 2 + 1) / δ + ((⌈Real.logb 2 (1 / δ)⌉₊ : ℝ) + 3) * Y := by positivity
    have hKLk : 0 ≤ K' * P.L Q T * k := by
      have := hLpos.le; have : (0 : ℝ) ≤ k := by linarith only [hk1]
      positivity
    apply mul_le_mul (mul_le_mul_of_nonneg_left h4 hKLk) hS hS0
    have : 0 ≤ k * (2 * Q ^ 2 / δ + Y) := by
      have : (0 : ℝ) ≤ k := by linarith only [hk1]
      positivity
    exact mul_nonneg hKLk this
  -- `E (2Q²/δ + Y) ≤ Q²T (2e₁ + e₂)`
  have hEQ : Real.exp (ε₅ / 2 * t) * (2 * Q ^ 2 / δ) =
      Q ^ 2 * T * (2 * Real.exp (-(ε₅ / 2 * t))) := by
    rw [mul_div_assoc', div_eq_iff hδ0.ne', hQexp, hTexp, hδexp]
    have h : Real.exp t * Real.exp (-(ε₅ / 2 * t)) * Real.exp (t * (-1 + ε₅)) =
        Real.exp (ε₅ / 2 * t) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have e : Real.exp ℓ ^ 2 * Real.exp t * (2 * Real.exp (-(ε₅ / 2 * t))) * Real.exp (t * (-1 + ε₅)) =
        2 * Real.exp ℓ ^ 2 * (Real.exp t * Real.exp (-(ε₅ / 2 * t)) * Real.exp (t * (-1 + ε₅))) := by
      ring
    rw [e, h]; ring
  have hEY : Real.exp (ε₅ / 2 * t) * Y ≤ Q ^ 2 * T * Real.exp (-(P.ε₁ * ℓ)) := by
    rw [hYdef, P.Y_exp hQ0 hT0, ← hℓdef, ← htdef, hQexp, hTexp]
    have hS1 := P.S1_log hℓ0.le ht0 htℓ
    have e1 : Real.exp ℓ ^ 2 * Real.exp t * Real.exp (-(P.ε₁ * ℓ)) =
        Real.exp (ℓ + ℓ + t + -(P.ε₁ * ℓ)) := by
      simp only [Real.exp_add]; ring
    rw [e1, ← Real.exp_add, Real.exp_le_exp]
    have : ε₅ / 2 * t ≤ P.ε₁ * t := by nlinarith only [hε₅1, ht0, hε₁]
    nlinarith only [hS1, this, ht0]
  -- the numerical factor
  have he₁ : t ^ 2 * Real.exp (-(ε₅ / 2 * t)) ≤ 48 / (ε₅ ^ 3 * t) := by
    have h := sq_mul_exp_neg_le (a := ε₅ / 2) (x := t) (by positivity) (by linarith only [ht3])
    have e : 6 / ((ε₅ / 2) ^ 3 * t) = 48 / (ε₅ ^ 3 * t) := by
      field_simp; ring
    rwa [e] at h
  have he₂ : t ^ 2 * Real.exp (-(P.ε₁ * ℓ)) ≤ P.kc ^ 2 * (6 / (P.ε₁ ^ 3 * ℓ)) := by
    have h := sq_mul_exp_neg_le (a := P.ε₁) (x := ℓ) hε₁ hℓ0
    have ht2 : t ^ 2 ≤ P.kc ^ 2 * ℓ ^ 2 := by
      have : t ^ 2 ≤ (P.kc * ℓ) ^ 2 := pow_le_pow_left₀ ht0 htℓ 2
      linarith only [this, show (P.kc * ℓ) ^ 2 = P.kc ^ 2 * ℓ ^ 2 by ring]
    calc t ^ 2 * Real.exp (-(P.ε₁ * ℓ)) ≤ P.kc ^ 2 * ℓ ^ 2 * Real.exp (-(P.ε₁ * ℓ)) :=
          mul_le_mul_of_nonneg_right ht2 (Real.exp_pos _).le
      _ = P.kc ^ 2 * (ℓ ^ 2 * Real.exp (-(P.ε₁ * ℓ))) := by ring
      _ ≤ P.kc ^ 2 * (6 / (P.ε₁ ^ 3 * ℓ)) := mul_le_mul_of_nonneg_left h (sq_nonneg _)
  have hnum : 2 * K' * Cy * (k ^ 2 * (2 * Real.exp (-(ε₅ / 2 * t)) + Real.exp (-(P.ε₁ * ℓ)))) ≤ D := by
    have hk2 : k ^ 2 ≤ 49 * t ^ 2 := by nlinarith only [hk1, hk7]
    have he0 : 0 ≤ 2 * Real.exp (-(ε₅ / 2 * t)) + Real.exp (-(P.ε₁ * ℓ)) := by positivity
    have h1 : k ^ 2 * (2 * Real.exp (-(ε₅ / 2 * t)) + Real.exp (-(P.ε₁ * ℓ))) ≤
        49 * (2 * (t ^ 2 * Real.exp (-(ε₅ / 2 * t))) + t ^ 2 * Real.exp (-(P.ε₁ * ℓ))) := by
      have := mul_le_mul_of_nonneg_right hk2 he0
      linarith only [this]
    have h2 : k ^ 2 * (2 * Real.exp (-(ε₅ / 2 * t)) + Real.exp (-(P.ε₁ * ℓ))) ≤
        49 * (2 * (48 / (ε₅ ^ 3 * t)) + P.kc ^ 2 * (6 / (P.ε₁ ^ 3 * ℓ))) := by
      linarith only [h1, he₁, he₂]
    have h2KC : 0 ≤ 2 * K' * Cy := by positivity
    have h3 := mul_le_mul_of_nonneg_left h2 h2KC
    -- the two thresholds
    have ht' : 192 * B / (ε₅ ^ 3 * D) ≤ t := by linarith only [ht₁t, ht₁]
    have hℓ' : 12 * B * P.kc ^ 2 / (P.ε₁ ^ 3 * D) ≤ ℓ := by linarith only [hℓℓ₁, hℓ₁]
    rw [div_le_iff₀ (by positivity)] at ht' hℓ'
    have ht0' : 0 < t := by linarith only [ht3]
    have i1 : 2 * K' * Cy * (49 * (2 * (48 / (ε₅ ^ 3 * t)))) ≤ D / 2 := by
      rw [show 2 * K' * Cy * (49 * (2 * (48 / (ε₅ ^ 3 * t)))) = 96 * B / (ε₅ ^ 3 * t) by
        rw [hB]; field_simp; ring]
      rw [div_le_iff₀ (by positivity)]
      nlinarith only [ht', hD0, hε₅0]
    have i2 : 2 * K' * Cy * (49 * (P.kc ^ 2 * (6 / (P.ε₁ ^ 3 * ℓ)))) ≤ D / 2 := by
      rw [show 2 * K' * Cy * (49 * (P.kc ^ 2 * (6 / (P.ε₁ ^ 3 * ℓ)))) =
          6 * B * P.kc ^ 2 / (P.ε₁ ^ 3 * ℓ) by rw [hB]; field_simp; ring]
      rw [div_le_iff₀ (by positivity)]
      nlinarith only [hℓ', hD0, hε₁]
    have e : 2 * K' * Cy * (49 * (2 * (48 / (ε₅ ^ 3 * t)) + P.kc ^ 2 * (6 / (P.ε₁ ^ 3 * ℓ)))) =
        2 * K' * Cy * (49 * (2 * (48 / (ε₅ ^ 3 * t)))) +
          2 * K' * Cy * (49 * (P.kc ^ 2 * (6 / (P.ε₁ ^ 3 * ℓ)))) := by ring
    linarith only [h3, e, i1, i2]
  -- the right-hand side
  have hHQ : 1 / 2 * (cH * Q ^ 2) ≤ W.H Q := hQH Q hQH'
  have hJ : T / 2 ≤ P.Jlen T := by unfold HSetup.Jlen; nlinarith only [hθ, hT0]
  have hLdef : P.L Q T = P.lam * ℓs := rfl
  have hcQ : 0 ≤ 1 / 2 * (cH * Q ^ 2) := by have := hcH0.le; positivity
  have hH0 : 0 ≤ W.H Q := le_trans hcQ hHQ
  have hHJ : 1 / 2 * (cH * Q ^ 2) * (T / 2) ≤ W.H Q * P.Jlen T :=
    mul_le_mul hHQ hJ (by linarith only [hT0]) hH0
  have hηL : 0 ≤ η * P.L Q T ^ 2 * ℓs := by have := hLpos.le; have := hη.le; positivity
  have hRHS : P.L Q T * ℓs ^ 2 * (Q ^ 2 * T) * D ≤ η * W.H Q * P.Jlen T * P.L Q T ^ 2 * ℓs := by
    have e : P.L Q T * ℓs ^ 2 * (Q ^ 2 * T) * D =
        (η * P.L Q T ^ 2 * ℓs) * ((1 / 2 * (cH * Q ^ 2)) * (T / 2)) := by
      rw [hD, hLdef]; ring
    have e' : η * W.H Q * P.Jlen T * P.L Q T ^ 2 * ℓs = (η * P.L Q T ^ 2 * ℓs) * (W.H Q * P.Jlen T) := by
      ring
    rw [e, e']
    exact mul_le_mul_of_nonneg_left hHJ hηL
  -- assemble
  have hE0 : 0 ≤ Real.exp (ε₅ / 2 * t) := (Real.exp_pos _).le
  have hLl : 0 ≤ P.L Q T * ℓs ^ 2 := by have := hLpos.le; positivity
  calc (1 + (T ^ (-(ε₅ / 2)))⁻¹) * ∫ u, P.g Q T u * famForm W Q (P.rangeZ Q T) (xt u)
      ≤ (1 + (T ^ (-(ε₅ / 2)))⁻¹) * (48 * C₀ * (P.bInt * P.L Q T) * W.wmax * k *
          ((Q ^ 2 + 1) / δ + ((⌈Real.logb 2 (1 / δ)⌉₊ : ℝ) + 3) * Y) * S) :=
        mul_le_mul_of_nonneg_left hM3 hAnn
    _ ≤ (2 * Real.exp (ε₅ / 2 * t)) * (K' * P.L Q T * k * (k * (2 * Q ^ 2 / δ + Y)) * (Cy * ℓs ^ 2)) := by
        apply mul_le_mul hA hR₀ _ (by positivity)
        have : 0 ≤ ((Q ^ 2 + 1) / δ + ((⌈Real.logb 2 (1 / δ)⌉₊ : ℝ) + 3) * Y) := by positivity
        have : (0 : ℝ) ≤ k := by linarith only [hk1]
        have := hLpos.le
        positivity
    _ = 2 * K' * Cy * (P.L Q T * ℓs ^ 2) * k ^ 2 *
          (Real.exp (ε₅ / 2 * t) * (2 * Q ^ 2 / δ) + Real.exp (ε₅ / 2 * t) * Y) := by ring
    _ ≤ 2 * K' * Cy * (P.L Q T * ℓs ^ 2) * k ^ 2 *
          (Q ^ 2 * T * (2 * Real.exp (-(ε₅ / 2 * t))) + Q ^ 2 * T * Real.exp (-(P.ε₁ * ℓ))) := by
        rw [hEQ]
        apply mul_le_mul_of_nonneg_left (by linarith only [hEY])
        positivity
    _ = P.L Q T * ℓs ^ 2 * (Q ^ 2 * T) *
          (2 * K' * Cy * (k ^ 2 * (2 * Real.exp (-(ε₅ / 2 * t)) + Real.exp (-(P.ε₁ * ℓ))))) := by ring
    _ ≤ P.L Q T * ℓs ^ 2 * (Q ^ 2 * T) * D := by
        apply mul_le_mul_of_nonneg_left hnum
        have := hT0.le
        positivity
    _ ≤ η * W.H Q * P.Jlen T * P.L Q T ^ 2 * ℓs := hRHS

end F

end Families.Hybrid
