/-
# Package TS: localisation at the scale `δ = T^{−1+ε₅}` (§9.3, Steps 1–3)

The objects of Proposition 9.18 at a **variable** localisation scale `δ ∈ (0, 1/4]` (the families
proof fixes `δ = 1/4`, which is too coarse at polynomial height):
* `xsH`, `xtH`: the localised and tail vectors, literally those of `lemM3H_iii_Statement` and
  `corTailsH_Statement` (with `ρ = rhoLoc`);
* the localisation interval `[N₀(u), N₀(u) + K(u))`, `N₀ = ⌈e^{u−2δ}⌉`, `K(u) ≤ 5δe^u + 1`
  (`KlocH_le`, via `lem:M3`(ii)), which is where (S2) of `lemSizesH_Statement` is applied;
* `g(u) = 0` for `|u| ≥ L` (so the pointwise bound is only needed for `u < L`, the range of (S2));
* the short-interval bound (regime (i), `lem:M2`) and the large sieve on an interval;
* the rough / non-rough split of `a` at the **family** modulus `Q` (with `a` at `Q' = QT`), and in
  regime (iii) the non-rough part lives on `n > (QT)^{1+ε}/2`.
-/
import FamiliesH.TS.Statement
import FamiliesH.F.All
import Families.Phase3.C.TIsharp

noncomputable section

open scoped BigOperators ContDiff
open Set MeasureTheory Filter Topology

namespace Families.Hybrid

open Families Families.Phase3.C

namespace TS

/-- `ρ = rhoLoc` is a localisation cut-off. -/
lemma isLocCutoff_rhoLoc : IsLocCutoff rhoLoc :=
  ⟨rhoLoc_contDiff, fun ξ => ⟨rhoLoc_nonneg ξ, rhoLoc_le_one ξ⟩, fun _ h => rhoLoc_one h,
    fun _ h => rhoLoc_zero h⟩

variable (P : HSetup)

/-! ### Localised and tail vectors -/

/-- `x^s_y(u)_n = x_y(u)_n ρ((log n − u)/δ)` (the vector of `lemM3H_iii_Statement`). -/
def xsH (Q T δ : ℝ) (y : ℕ → ℝ) (u : ℝ) : ℤ → ℂ :=
  fun n => P.xVec Q T y u n * rhoLoc ((Real.log n.toNat - u) / δ)

/-- `x^t_y(u)_n = x_y(u)_n (1 − ρ((log n − u)/δ))` (the vector of `corTailsH_Statement`). -/
def xtH (Q T δ : ℝ) (y : ℕ → ℝ) (u : ℝ) : ℤ → ℂ :=
  fun n => P.xVec Q T y u n * (1 - rhoLoc ((Real.log n.toNat - u) / δ))

lemma xVec_eq_xsH_add_xtH (Q T δ : ℝ) (y : ℕ → ℝ) (u : ℝ) :
    P.xVec Q T y u = xsH P Q T δ y u + xtH P Q T δ y u := by
  funext n; simp only [xsH, xtH, Pi.add_apply]; ring

lemma xVecH_add (Q T : ℝ) (y₁ y₂ : ℕ → ℝ) (u : ℝ) :
    P.xVec Q T (y₁ + y₂) u = P.xVec Q T y₁ u + P.xVec Q T y₂ u := by
  funext n
  simp only [HSetup.xVec, Pi.add_apply]
  split_ifs <;> push_cast <;> ring

lemma xVecH_sub (Q T : ℝ) (y₁ y₂ : ℕ → ℝ) (u : ℝ) :
    P.xVec Q T (y₁ - y₂) u = P.xVec Q T y₁ u - P.xVec Q T y₂ u := by
  funext n
  simp only [HSetup.xVec, Pi.sub_apply]
  split_ifs <;> push_cast <;> ring

lemma xsH_add (Q T δ : ℝ) (y₁ y₂ : ℕ → ℝ) (u : ℝ) :
    xsH P Q T δ (y₁ + y₂) u = xsH P Q T δ y₁ u + xsH P Q T δ y₂ u := by
  funext n
  simp only [xsH, xVecH_add, Pi.add_apply]
  ring

lemma xsH_sub (Q T δ : ℝ) (y₁ y₂ : ℕ → ℝ) (u : ℝ) :
    xsH P Q T δ (y₁ - y₂) u = xsH P Q T δ y₁ u - xsH P Q T δ y₂ u := by
  funext n
  simp only [xsH, xVecH_sub, Pi.sub_apply]
  ring

lemma xsH_congr {Q T δ : ℝ} (hδ : 0 < δ) {y₁ y₂ : ℕ → ℝ} {u : ℝ}
    (h : ∀ k : ℕ, 1 ≤ k → |Real.log k - u| < 2 * δ → y₁ k = y₂ k) :
    xsH P Q T δ y₁ u = xsH P Q T δ y₂ u := by
  funext n
  simp only [xsH, HSetup.xVec]
  split_ifs with hn
  · by_cases hr : rhoLoc ((Real.log n.toNat - u) / δ) = 0
    · simp [hr]
    · have hlt := rhoLoc_lt_of_ne_zero hr
      rw [abs_div, abs_of_pos hδ, div_lt_iff₀ hδ] at hlt
      have hk : 1 ≤ n.toNat := by omega
      rw [h n.toNat hk (by linarith)]
  · simp

/-! ### Supports -/

lemma xVecH_ne_zero {Q T : ℝ} {y : ℕ → ℝ} {u : ℝ} {n : ℤ} (h : P.xVec Q T y u n ≠ 0) :
    1 ≤ n ∧ y n.toNat ≠ 0 :=
  xVec_ne_zero P.toPS (Q := Q * T) (T := T) h

lemma xsH_ne_zero {Q T δ : ℝ} (hδ : 0 < δ) {y : ℕ → ℝ} {u : ℝ} {n : ℤ}
    (h : xsH P Q T δ y u n ≠ 0) :
    1 ≤ n ∧ y n.toNat ≠ 0 ∧ |Real.log n.toNat - u| < 2 * δ := by
  have h1 : P.xVec Q T y u n ≠ 0 := left_ne_zero_of_mul h
  have h2 : rhoLoc ((Real.log n.toNat - u) / δ) ≠ 0 := by
    intro h0; apply h; simp [xsH, h0]
  obtain ⟨hn, hy⟩ := xVecH_ne_zero P h1
  refine ⟨hn, hy, ?_⟩
  have hlt := rhoLoc_lt_of_ne_zero h2
  rw [abs_div, abs_of_pos hδ, div_lt_iff₀ hδ] at hlt
  linarith

lemma mem_rangeZ_of_xVecH {Q T : ℝ} {y : ℕ → ℝ} (hy : VanishBeyond P.toPS (Q * T) y) {u : ℝ}
    {n : ℤ} (h : P.xVec Q T y u n ≠ 0) : n ∈ P.rangeZ Q T :=
  mem_rangeZ_of_xVec P.toPS (Q := Q * T) (T := T) hy h

lemma mem_rangeZ_of_xsH {Q T δ : ℝ} {y : ℕ → ℝ} (hy : VanishBeyond P.toPS (Q * T) y) {u : ℝ}
    {n : ℤ} (h : xsH P Q T δ y u n ≠ 0) : n ∈ P.rangeZ Q T :=
  mem_rangeZ_of_xVecH P hy (left_ne_zero_of_mul h)

lemma mem_rangeZ_of_xtH {Q T δ : ℝ} {y : ℕ → ℝ} (hy : VanishBeyond P.toPS (Q * T) y) {u : ℝ}
    {n : ℤ} (h : xtH P Q T δ y u n ≠ 0) : n ∈ P.rangeZ Q T :=
  mem_rangeZ_of_xVecH P hy (left_ne_zero_of_mul h)

lemma vanish_aVecH {Q T : ℝ} (hQT : 1 < Q * T) : VanishBeyond P.toPS (Q * T) (P.aVec Q T) :=
  VanishBeyond.aVec P.toPS hQT

lemma vanish_aSharpH {Q T : ℝ} (hQT : 1 < Q * T) : VanishBeyond P.toPS (Q * T) (P.aSharp Q T) := by
  rw [P.aSharp_eq]; exact VanishBeyond.aSharp P.toPS hQT 1

lemma vanish_bVecH {Q T : ℝ} (hQT : 1 < Q * T) : VanishBeyond P.toPS (Q * T) (P.bVec Q T) := by
  rw [P.bVec_eq]; exact VanishBeyond.bVec P.toPS hQT 1

/-! ### The localisation interval -/

/-- `N₀(u) = ⌈e^{u−2δ}⌉`. -/
def N0H (δ u : ℝ) : ℤ := ⌈Real.exp (u - 2 * δ)⌉

/-- `K(u) = ⌊e^{u+2δ}⌋ − N₀(u) + 1` (`0` if this is negative). -/
def KlocH (δ u : ℝ) : ℕ := (⌊Real.exp (u + 2 * δ)⌋ - N0H δ u + 1).toNat

lemma one_le_N0H (δ u : ℝ) : 1 ≤ N0H δ u := Int.one_le_ceil_iff.mpr (Real.exp_pos _)

/-- `K(u) ≤ e^{u+2δ} − e^{u−2δ} + 1 ≤ 5δe^u + 1` for `δ ∈ (0, 1/4]` (`lem:M3`(ii)). -/
lemma KlocH_le {δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) (u : ℝ) :
    (KlocH δ u : ℝ) ≤ 5 * δ * Real.exp u + 1 := by
  unfold KlocH
  set m : ℤ := ⌊Real.exp (u + 2 * δ)⌋ - N0H δ u + 1 with hm
  have h5 : 0 ≤ 5 * δ * Real.exp u := by positivity
  rcases le_or_gt 0 m with hm0 | hm0
  · have hc : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hm0]
    rw [hc, hm]
    have h1 : ((⌊Real.exp (u + 2 * δ)⌋ : ℤ) : ℝ) ≤ Real.exp (u + 2 * δ) := Int.floor_le _
    have h2 : Real.exp (u - 2 * δ) ≤ (N0H δ u : ℝ) := Int.le_ceil _
    have h3 := lemM3_ii δ hδ hδ4
    have e1 : Real.exp (u + 2 * δ) = Real.exp u * Real.exp (2 * δ) := Real.exp_add _ _
    have e2 : Real.exp (u - 2 * δ) = Real.exp u * Real.exp (-(2 * δ)) := by
      rw [sub_eq_add_neg, Real.exp_add]
    have h4 := mul_le_mul_of_nonneg_left h3 (Real.exp_pos u).le
    push_cast
    nlinarith
  · rw [Int.toNat_of_nonpos hm0.le]
    push_cast
    linarith

lemma mem_interval_of_nearH {δ u : ℝ} {n : ℤ} (hn : 1 ≤ n)
    (h : |Real.log n.toNat - u| < 2 * δ) : n ∈ intervalZ (N0H δ u) (KlocH δ u) := by
  have hcast : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
  rw [hcast] at h
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show (0 : ℤ) < n by omega)
  rw [abs_lt] at h
  have hlo : Real.exp (u - 2 * δ) < n := by
    rw [← Real.exp_log hn0]; exact Real.exp_lt_exp.mpr (by linarith)
  have hhi : (n : ℝ) < Real.exp (u + 2 * δ) := by
    rw [← Real.exp_log hn0]; exact Real.exp_lt_exp.mpr (by linarith)
  have h1 : N0H δ u ≤ n := by unfold N0H; rw [Int.ceil_le]; exact hlo.le
  have h2 : n ≤ ⌊Real.exp (u + 2 * δ)⌋ := by rw [Int.le_floor]; exact hhi.le
  have h3 : (KlocH δ u : ℤ) = ⌊Real.exp (u + 2 * δ)⌋ - N0H δ u + 1 := by
    unfold KlocH; rw [Int.toNat_of_nonneg (by omega)]
  simp only [intervalZ, Finset.mem_Ico]
  omega

lemma mem_interval_of_xsH {Q T δ : ℝ} (hδ : 0 < δ) {y : ℕ → ℝ} {u : ℝ} {n : ℤ}
    (h : xsH P Q T δ y u n ≠ 0) : n ∈ intervalZ (N0H δ u) (KlocH δ u) := by
  obtain ⟨hn, -, hlt⟩ := xsH_ne_zero P hδ h
  exact mem_interval_of_nearH hn hlt

/-- On `[1, Y]` and on the localisation interval the forms of `x^s_y(u)` agree. -/
lemma supp_iff_of_xsH {Q T δ : ℝ} (hδ : 0 < δ) {y : ℕ → ℝ} (hy : VanishBeyond P.toPS (Q * T) y)
    (u : ℝ) : ∀ n, xsH P Q T δ y u n ≠ 0 →
      (n ∈ P.rangeZ Q T ↔ n ∈ intervalZ (N0H δ u) (KlocH δ u)) := fun _ hn =>
  ⟨fun _ => mem_interval_of_xsH P hδ hn, fun _ => mem_rangeZ_of_xsH P hy hn⟩

/-! ### Continuity in `u` -/

lemma continuous_famForm_of (W : Weight) (Q : ℝ) (I : Finset ℤ) {x : ℝ → ℤ → ℂ}
    (hx : ∀ n, Continuous fun u => x u n) : Continuous fun u => famForm W Q I (x u) := by
  unfold famForm
  refine continuous_finsetSum _ fun q _ => continuous_const.mul
    (continuous_finsetSum _ fun χ _ => ?_)
  exact (continuous_norm.comp
    (continuous_finsetSum _ fun n _ => (hx n).mul continuous_const)).pow 2

lemma continuous_normSq_of (I : Finset ℤ) {x : ℝ → ℤ → ℂ} (hx : ∀ n, Continuous fun u => x u n) :
    Continuous fun u => normSq I (x u) := by
  unfold normSq
  exact continuous_finsetSum _ fun n _ => ((hx n).norm.pow 2)

lemma continuous_xVecH_apply (Q T : ℝ) (y : ℕ → ℝ) (n : ℤ) :
    Continuous fun u => P.xVec Q T y u n :=
  continuous_xVec_apply P.toPS (Q * T) T y n

lemma continuous_rho_apply (δ : ℝ) (n : ℤ) :
    Continuous fun u : ℝ => ((rhoLoc ((Real.log n.toNat - u) / δ) : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp
    (rhoLoc_continuous.comp ((continuous_const.sub continuous_id).div_const _))

lemma continuous_xsH_apply (Q T δ : ℝ) (y : ℕ → ℝ) (n : ℤ) :
    Continuous fun u => xsH P Q T δ y u n :=
  (continuous_xVecH_apply P Q T y n).mul (continuous_rho_apply δ n)

lemma continuous_xtH_apply (Q T δ : ℝ) (y : ℕ → ℝ) (n : ℤ) :
    Continuous fun u => xtH P Q T δ y u n :=
  (continuous_xVecH_apply P Q T y n).mul (continuous_const.sub (continuous_rho_apply δ n))

/-- `g · f` is integrable for continuous `f` (`g` is continuous with compact support). -/
lemma integrable_gH_mul {Q T : ℝ} (hQT : 1 < Q * T) {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable (fun u => P.g Q T u * f u) :=
  integrable_g_mul P.toPS hQT hf

/-! ### `g(u) = 0` for `|u| ≥ L` -/

lemma g_eq_zero_of_le {Q T : ℝ} (hQT : 1 < Q * T) {u : ℝ} (hu : P.L Q T ≤ |u|) :
    P.g Q T u = 0 := by
  have hL : 0 < P.L Q T := L_pos' P.toPS hQT
  obtain ⟨r, hr, hr0⟩ := P.ψ_supp
  have hrL : r * P.L Q T < P.L Q T / 2 := by nlinarith
  have hz : ∀ s, P.ψL Q T s ^ 2 * P.ψL Q T (u - s) ^ 2 = 0 := by
    intro s
    by_cases hs : P.L Q T / 2 ≤ |s|
    · have : P.ψL Q T s = 0 := by
        unfold HSetup.ψL; apply hr0
        rw [abs_div, abs_of_pos hL, lt_div_iff₀ hL]; linarith
      simp [this]
    · have : P.ψL Q T (u - s) = 0 := by
        unfold HSetup.ψL; apply hr0
        rw [abs_div, abs_of_pos hL, lt_div_iff₀ hL]
        have := abs_sub_abs_le_abs_sub u s
        have hs' := not_le.mp hs
        linarith
      simp [this]
  unfold HSetup.g
  simp [hz]

/-! ### Short intervals (regime (i), `lem:M2`) and the large sieve on an interval -/

lemma famForm_intervalZ_zero (W : Weight) (Q : ℝ) (N₀ : ℤ) (x : ℤ → ℂ) :
    famForm W Q (intervalZ N₀ 0) x = 0 := by
  simp [intervalZ, famForm]

lemma normSq_intervalZ_zero (N₀ : ℤ) (x : ℤ → ℂ) : normSq (intervalZ N₀ 0) x = 0 := by
  simp [intervalZ, normSq]

/-- **Regime (i)**: `lem:M2` on intervals of `K ≤ Q^{1−r}` integers gives `(1 + d)H` for large `Q`. -/
theorem short_interval_le (hWH : lemWH_Statement) (W : Weight) {r d : ℝ} (hr : 0 < r) (hd : 0 < d) :
    ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ (N₀ : ℤ) (K : ℕ), (K : ℝ) ≤ Q ^ (1 - r) → ∀ x : ℤ → ℂ,
      famForm W Q (intervalZ N₀ K) x ≤ (1 + d) * W.H Q * normSq (intervalZ N₀ K) x := by
  have hE : 0 < Ecal * W.Iw := mul_pos Ecal_pos W.Iw_pos
  have hw := W.wmax_nonneg
  have hc : 0 < d * (Ecal * W.Iw) / (8 * (W.wmax + 1)) := by positivity
  have hev := (H_lower_eventually hWH W (κ := 1 / 2) (by norm_num)).and
    ((eventually_rpow_neg_mul_le hr 1 hc).and (eventually_ge_atTop (1 : ℝ)))
  obtain ⟨Q₀, hQ₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨Q₀, fun Q hQ N₀ K hK x => ?_⟩
  obtain ⟨hHl, hsmall, hQ1⟩ := hQ₀ Q hQ
  have hQ0 : 0 < Q := by linarith
  rcases Nat.eq_zero_or_pos K with hK0 | hK1
  · subst hK0
    rw [famForm_intervalZ_zero, normSq_intervalZ_zero, mul_zero]
  have hM2 := lemM2 W Q hQ0 N₀ K hK1 x
  refine hM2.trans (mul_le_mul_of_nonneg_right ?_ (normSq_nonneg' _ _))
  have hK1r : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hQr : Q ^ (1 - r) ≤ Q := by
    have := Real.rpow_le_rpow_of_exponent_le hQ1 (show 1 - r ≤ 1 by linarith)
    simpa using this
  have hlogK : 1 + Real.log K ≤ 1 + Real.log Q := by
    have := Real.log_le_log (by linarith) (hK.trans hQr); linarith
  have hlogK0 : 0 ≤ 1 + Real.log K := by have := Real.log_nonneg hK1r; linarith
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ1
  have hsplit : Q ^ (1 - r) = Q * Q ^ (-r) := by
    rw [Real.rpow_sub hQ0, Real.rpow_one, Real.rpow_neg hQ0.le]; ring
  have hsm : Q ^ (-r) * (1 + Real.log Q) ≤ d * (Ecal * W.Iw) / (8 * (W.wmax + 1)) := by
    have : Q ^ (-r) * (1 + Real.log Q) ^ 1 ≤ d * (Ecal * W.Iw) / (8 * (W.wmax + 1)) := hsmall
    rwa [pow_one] at this
  have hkey : 4 * W.wmax * Q * K * (1 + Real.log K) ≤ d * W.H Q := by
    calc 4 * W.wmax * Q * K * (1 + Real.log K)
        ≤ 4 * W.wmax * Q * Q ^ (1 - r) * (1 + Real.log Q) := by gcongr
      _ = 4 * W.wmax * Q ^ 2 * (Q ^ (-r) * (1 + Real.log Q)) := by rw [hsplit]; ring
      _ ≤ 4 * W.wmax * Q ^ 2 * (d * (Ecal * W.Iw) / (8 * (W.wmax + 1))) := by gcongr
      _ = d * (1 / 2 * (Ecal * W.Iw * Q ^ 2)) * (W.wmax / (W.wmax + 1)) := by
          field_simp; ring
      _ ≤ d * (1 / 2 * (Ecal * W.Iw * Q ^ 2)) * 1 := by
          gcongr
          rw [div_le_iff₀ (by linarith)]; linarith
      _ ≤ d * W.H Q := by rw [mul_one]; gcongr
  linarith

/-- The multiplicative large sieve on an interval anywhere: `x^*Δx ≤ w_max C₀ (Q² + K) ‖x‖²`. -/
lemma famForm_interval_le {C₀ : ℝ} (hmult : MVLargeSieveMult C₀) (W : Weight) {Q : ℝ} (hQ : 1 ≤ Q)
    (N₀ : ℤ) (K : ℕ) (x : ℤ → ℂ) :
    famForm W Q (intervalZ N₀ K) x ≤
      W.wmax * max C₀ 0 * (Q ^ 2 + K) * normSq (intervalZ N₀ K) x := by
  refine (famForm_le_mult W Q _ x).trans ?_
  have h1 := mul_le_mul_of_nonneg_left (hmult Q hQ N₀ K x) W.wmax_nonneg
  have hx : 0 ≤ normSq (intervalZ N₀ K) x := normSq_nonneg' _ _
  have h2 : W.wmax * (C₀ * (Q ^ 2 + K) * normSq (intervalZ N₀ K) x) ≤
      W.wmax * max C₀ 0 * (Q ^ 2 + K) * normSq (intervalZ N₀ K) x := by
    have := W.wmax_nonneg
    have h3 : C₀ * ((Q ^ 2 + K) * normSq (intervalZ N₀ K) x) ≤
        max C₀ 0 * ((Q ^ 2 + K) * normSq (intervalZ N₀ K) x) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    calc W.wmax * (C₀ * (Q ^ 2 + K) * normSq (intervalZ N₀ K) x)
        = W.wmax * (C₀ * ((Q ^ 2 + K) * normSq (intervalZ N₀ K) x)) := by ring
      _ ≤ W.wmax * (max C₀ 0 * ((Q ^ 2 + K) * normSq (intervalZ N₀ K) x)) :=
          mul_le_mul_of_nonneg_left h3 this
      _ = _ := by ring
  exact h1.trans h2

/-! ### The rough / non-rough split (at the family modulus `Q`) -/

open Classical in
/-- `a` on the `Q`-rough integers. -/
def aRH (Q T : ℝ) : ℕ → ℝ := fun n => if IsRough Q (n : ℤ) then P.aVec Q T n else 0

open Classical in
/-- `a` on the non-`Q`-rough integers. -/
def aNRH (Q T : ℝ) : ℕ → ℝ := fun n => if IsRough Q (n : ℤ) then 0 else P.aVec Q T n

open Classical in
/-- `a` on the non-`Q`-rough integers `n > x`. -/
def aPPH (Q T x : ℝ) : ℕ → ℝ :=
  fun n => if x < n ∧ ¬ IsRough Q (n : ℤ) then P.aVec Q T n else 0

lemma aRH_add_aNRH (Q T : ℝ) : aRH P Q T + aNRH P Q T = P.aVec Q T := by
  funext n; simp only [aRH, aNRH, Pi.add_apply]; split_ifs <;> simp

lemma aRH_eq (Q T : ℝ) : aRH P Q T = P.bVec Q T + P.aSharp Q T - aNRH P Q T := by
  funext n
  have := congrFun (aRH_add_aNRH P Q T) n
  simp only [Pi.add_apply] at this
  simp only [Pi.sub_apply, Pi.add_apply, HSetup.bVec]
  linarith

lemma vanish_aRH {Q T : ℝ} (hQT : 1 < Q * T) : VanishBeyond P.toPS (Q * T) (aRH P Q T) :=
  VanishBeyond.of_le P.toPS (vanish_aVecH P hQT) fun k hk => by simp [aRH, hk]

lemma vanish_aNRH {Q T : ℝ} (hQT : 1 < Q * T) : VanishBeyond P.toPS (Q * T) (aNRH P Q T) :=
  VanishBeyond.of_le P.toPS (vanish_aVecH P hQT) fun k hk => by simp [aNRH, hk]

lemma vanish_aPPH {Q T : ℝ} (hQT : 1 < Q * T) (x : ℝ) :
    VanishBeyond P.toPS (Q * T) (aPPH P Q T x) :=
  VanishBeyond.of_le P.toPS (vanish_aVecH P hQT) fun k hk => by simp [aPPH, hk]

lemma rough_of_xsH_aRH {Q T δ u : ℝ} (hδ : 0 < δ) {n : ℤ}
    (h : xsH P Q T δ (aRH P Q T) u n ≠ 0) : IsRough Q n := by
  obtain ⟨hn, hy, -⟩ := xsH_ne_zero P hδ h
  unfold aRH at hy
  split_ifs at hy with hr
  · rwa [Int.toNat_of_nonneg (by omega)] at hr
  · exact absurd rfl hy

/-- In regime (iii) (`u > (1+ε)ℓ_*`) the non-rough part of `x_a^s(u)` lives on `n > (QT)^{1+ε}/2`. -/
lemma xsH_aNRH_eq_aPPH {Q T δ ε u : ℝ} (hQT : 1 < Q * T) (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4)
    (hu : (1 + ε) * ellS Q T < u) :
    xsH P Q T δ (aNRH P Q T) u = xsH P Q T δ (aPPH P Q T ((Q * T) ^ (1 + ε) / 2)) u := by
  apply xsH_congr P hδ
  intro k hk hlt
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hbig : (Q * T) ^ (1 + ε) / 2 < k := by
    rw [abs_lt] at hlt
    have h1 : Real.exp (u - 2 * δ) < k := by
      rw [← Real.exp_log hk0]; exact Real.exp_lt_exp.mpr (by linarith)
    have h2 : (Q * T) ^ (1 + ε) * Real.exp (-(1 / 2)) < Real.exp (u - 2 * δ) := by
      rw [Real.rpow_def_of_pos (by linarith), ← Real.exp_add]
      apply Real.exp_lt_exp.mpr
      unfold ellS at hu
      nlinarith
    have h3 := half_le_exp_neg_half
    have h4 : 0 < (Q * T) ^ (1 + ε) := Real.rpow_pos_of_pos (by linarith) _
    nlinarith
  unfold aNRH aPPH
  split_ifs with h1 h2 h2 <;> simp_all

end TS

end Families.Hybrid
