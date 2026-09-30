/-
**Steps 1–4 of `prop:TIsharp`, pointwise in `u`** (proof of Proposition 6.24).

* the localisation interval: `x^s_y(u)` lives on `[⌈e^{u−1/2}⌉, ⌊e^{u+1/2}⌋ + 1]`, an interval of
  `K(u) ≤ 2e^u + 2` integers (`mem_interval_of_xs`, `Kloc_le`);
* regime (i), `u ≤ (1−ε)ℓ`: `lem:M2` gives `x_b^{s*}Δx_b^s ≤ (1 + d) H ‖x_b^s‖²` for `Q ≥ Q₀(d)`
  (`regime_i_bound`); regime (ii), `u ≤ (1+ε)ℓ`: the band hypothesis gives `(C_band + d) H`
  (`regime_ii_bound`);
* regime (iii), `u > (1+ε)ℓ`: the non-rough part of `x_a^s(u)` lives on `n > Q^{1+ε}/2`
  (`xs_aNR_eq_aPP`), the rough part is `Q`-rough (`rough_of_xs_aR`);
* `pointwise_bound`: the combination of Step 0 and Steps 1–4 for every `u`,
  `x_b^*Δx_b ≤ (1+κ)³ c(u) H ‖x_b^s‖² + E(u)`, with the step function `c(u) = cfun` and the error
  `E(u)` (tails, `x♯^s`, prime powers, Step 0) written out.
-/
import Families.Phase3.C.TIsharpNorms

noncomputable section

open scoped BigOperators ContDiff
open Set MeasureTheory Filter Topology

namespace Families.Phase3.C

open Families

/-! ### Elementary exponential bounds -/

lemma exp_half_lt_two : Real.exp (1 / 2) < 2 := by
  have h1 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by
    rw [sq, ← Real.exp_add]; norm_num
  have h2 := Real.exp_one_lt_d9
  have h3 := Real.exp_pos (1 / 2)
  nlinarith

lemma half_le_exp_neg_half : 1 / 2 ≤ Real.exp (-(1 / 2)) := by
  rw [Real.exp_neg]
  have := exp_half_lt_two
  have h3 := Real.exp_pos (1 / 2)
  rw [le_inv_comm₀ (by norm_num) h3]
  linarith

/-! ### The localisation interval -/

/-- `N₀(u) = ⌈e^{u−1/2}⌉`. -/
def N0 (u : ℝ) : ℤ := ⌈Real.exp (u - 1 / 2)⌉

/-- `K(u) = ⌊e^{u+1/2}⌋ − N₀(u) + 2`. -/
def Kloc (u : ℝ) : ℕ := (⌊Real.exp (u + 1 / 2)⌋ - N0 u + 2).toNat

lemma one_le_N0 (u : ℝ) : 1 ≤ N0 u := Int.one_le_ceil_iff.mpr (Real.exp_pos _)

lemma N0_sub_one_le (u : ℝ) : N0 u - 1 ≤ ⌊Real.exp (u + 1 / 2)⌋ := by
  rw [Int.le_floor]
  have h1 := Int.ceil_lt_add_one (Real.exp (u - 1 / 2))
  have h2 : Real.exp (u - 1 / 2) ≤ Real.exp (u + 1 / 2) := Real.exp_le_exp.mpr (by linarith)
  unfold N0; push_cast; linarith

lemma Kloc_eq (u : ℝ) : (Kloc u : ℤ) = ⌊Real.exp (u + 1 / 2)⌋ - N0 u + 2 := by
  unfold Kloc
  have := N0_sub_one_le u
  rw [Int.toNat_of_nonneg (by omega)]

lemma one_le_Kloc (u : ℝ) : 1 ≤ Kloc u := by
  have h := Kloc_eq u
  have := N0_sub_one_le u
  omega

lemma Kloc_le (u : ℝ) : (Kloc u : ℝ) ≤ 2 * Real.exp u + 2 := by
  have h := Kloc_eq u
  have h1 : ((⌊Real.exp (u + 1 / 2)⌋ : ℤ) : ℝ) ≤ Real.exp (u + 1 / 2) := Int.floor_le _
  have h2 : Real.exp (u - 1 / 2) ≤ (N0 u : ℝ) := Int.le_ceil _
  have h3 : Real.exp (u + 1 / 2) = Real.exp u * Real.exp (1 / 2) := Real.exp_add _ _
  have h4 := exp_half_lt_two
  have h5 := Real.exp_pos u
  have h6 := (Real.exp_pos (u - 1 / 2)).le
  have hK : (Kloc u : ℝ) = ((⌊Real.exp (u + 1 / 2)⌋ - N0 u + 2 : ℤ) : ℝ) := by
    rw [← h]; push_cast; rfl
  rw [hK]; push_cast
  nlinarith

lemma top_le (u : ℝ) : ((N0 u + Kloc u - 1 : ℤ) : ℝ) ≤ 2 * Real.exp u + 1 := by
  have h := Kloc_eq u
  have h1 : ((⌊Real.exp (u + 1 / 2)⌋ : ℤ) : ℝ) ≤ Real.exp (u + 1 / 2) := Int.floor_le _
  have h3 : Real.exp (u + 1 / 2) = Real.exp u * Real.exp (1 / 2) := Real.exp_add _ _
  have h4 := exp_half_lt_two
  have h5 := Real.exp_pos u
  have e : N0 u + (Kloc u : ℤ) - 1 = ⌊Real.exp (u + 1 / 2)⌋ + 1 := by rw [h]; ring
  rw [e]; push_cast
  nlinarith

lemma mem_interval_of_near {u : ℝ} {n : ℤ} (hn : 1 ≤ n) (h : |Real.log n.toNat - u| < 1 / 2) :
    n ∈ intervalZ (N0 u) (Kloc u) := by
  have hcast : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
  rw [hcast] at h
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show (0 : ℤ) < n by omega)
  rw [abs_lt] at h
  have hlo : Real.exp (u - 1 / 2) < n := by
    rw [← Real.exp_log hn0]; exact Real.exp_lt_exp.mpr (by linarith)
  have hhi : (n : ℝ) < Real.exp (u + 1 / 2) := by
    rw [← Real.exp_log hn0]; exact Real.exp_lt_exp.mpr (by linarith)
  have h1 : N0 u ≤ n := by unfold N0; rw [Int.ceil_le]; exact hlo.le
  have h2 : n ≤ ⌊Real.exp (u + 1 / 2)⌋ := by rw [Int.le_floor]; exact hhi.le
  have h3 := Kloc_eq u
  simp only [intervalZ, Finset.mem_Ico]
  omega

variable (P : PrimeSetup)

lemma mem_interval_of_xs {Q T : ℝ} {y : ℕ → ℝ} {u : ℝ} {n : ℤ} (h : xs P Q T y u n ≠ 0) :
    n ∈ intervalZ (N0 u) (Kloc u) := by
  obtain ⟨hn, -, hlt⟩ := xs_ne_zero P h
  exact mem_interval_of_near hn hlt

/-- On `[1, Y]` and on the localisation interval the forms of `x^s_y(u)` agree. -/
lemma supp_iff_of_xs {Q T : ℝ} {y : ℕ → ℝ} (hy : VanishBeyond P Q y) (u : ℝ) :
    ∀ n, xs P Q T y u n ≠ 0 → (n ∈ P.rangeZ Q ↔ n ∈ intervalZ (N0 u) (Kloc u)) := by
  intro n hn
  exact ⟨fun _ => mem_interval_of_xs P hn, fun _ => mem_rangeZ_of_xs P hy hn⟩

/-! ### Asymptotic helpers -/

lemma tendsto_rpow_neg_mul_one_add_log_pow {r : ℝ} (hr : 0 < r) (k : ℕ) :
    Tendsto (fun Q : ℝ => Q ^ (-r) * (1 + Real.log Q) ^ k) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_mul_log_pow hr k).const_mul ((2 : ℝ) ^ k)
  rw [mul_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with Q hQ
    have := Real.log_nonneg hQ
    positivity
  · filter_upwards [eventually_ge_atTop (Real.exp 1)] with Q hQ
    have hQ0 : 0 < Q := lt_of_lt_of_le (Real.exp_pos _) hQ
    have hl : 1 ≤ Real.log Q := by
      have := Real.log_le_log (Real.exp_pos _) hQ; rwa [Real.log_exp] at this
    have h1 : (1 + Real.log Q) ^ k ≤ (2 * Real.log Q) ^ k :=
      pow_le_pow_left₀ (by linarith) (by linarith) k
    have h2 : 0 ≤ Q ^ (-r) := Real.rpow_nonneg hQ0.le _
    calc Q ^ (-r) * (1 + Real.log Q) ^ k ≤ Q ^ (-r) * (2 * Real.log Q) ^ k :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = 2 ^ k * (Q ^ (-r) * Real.log Q ^ k) := by rw [mul_pow]; ring

lemma eventually_rpow_neg_mul_le {r : ℝ} (hr : 0 < r) (k : ℕ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ Q : ℝ in atTop, Q ^ (-r) * (1 + Real.log Q) ^ k ≤ c :=
  (tendsto_rpow_neg_mul_one_add_log_pow hr k).eventually (ge_mem_nhds hc)

lemma rpow_le_of_log_le {Q u a : ℝ} (hQ : 0 < Q) (hu : u ≤ a * Real.log Q) :
    Real.exp u ≤ Q ^ a := by
  rw [Real.rpow_def_of_pos hQ]
  exact Real.exp_le_exp.mpr (by linarith)

/-! ### Regime (i) (`lem:M2`) -/

theorem regime_i_bound (hWH : lemWH_Statement) (W : Weight) {ε d : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hd : 0 < d) :
    ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ (T : ℝ) (y : ℕ → ℝ), VanishBeyond P Q y →
      ∀ u : ℝ, u ≤ (1 - ε) * Real.log Q →
        famForm W Q (P.rangeZ Q) (xs P Q T y u) ≤ (1 + d) * W.H Q * normSq (P.rangeZ Q) (xs P Q T y u) := by
  have hE : 0 < Ecal * W.Iw := mul_pos Ecal_pos W.Iw_pos
  have hw := W.wmax_nonneg
  have hc : 0 < d * (Ecal * W.Iw) / (96 * (W.wmax + 1)) := by positivity
  have hev := (H_lower_eventually hWH W (κ := 1 / 2) (by norm_num)).and
    ((eventually_rpow_neg_mul_le hε 1 hc).and (eventually_ge_atTop (1 : ℝ)))
  obtain ⟨Q₀, hQ₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨Q₀, fun Q hQ T y hy u hu => ?_⟩
  obtain ⟨hHl, hsmall, hQ1⟩ := hQ₀ Q hQ
  have hQ0 : 0 < Q := by linarith
  rw [famForm_congr_supp W Q (supp_iff_of_xs P hy u), normSq_congr_supp (supp_iff_of_xs P hy u)]
  set K := Kloc u
  have hK1 := one_le_Kloc u
  have hM2 := lemM2 W Q hQ0 (N0 u) K hK1 (xs P Q T y u)
  refine hM2.trans (mul_le_mul_of_nonneg_right ?_ (normSq_nonneg' _ _))
  -- `4 w_max Q K (1 + log K) ≤ d H`
  have hKr : (K : ℝ) ≤ 4 * Q ^ (1 - ε) := by
    have h1 := Kloc_le u
    have h2 := rpow_le_of_log_le hQ0 hu
    have h3 : 1 ≤ Q ^ (1 - ε) := Real.one_le_rpow hQ1 (by linarith)
    linarith
  have hK1r : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hQε : Q ^ (1 - ε) ≤ Q := by
    have := Real.rpow_le_rpow_of_exponent_le hQ1 (show 1 - ε ≤ 1 by linarith)
    simpa using this
  have hlogK : 1 + Real.log K ≤ 3 + Real.log Q := by
    have h1 : Real.log K ≤ Real.log (4 * Q) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) hQ0.ne'] at h1
    have := log_four_lt_two
    linarith
  have hlogK0 : 0 ≤ 1 + Real.log K := by have := Real.log_nonneg hK1r; linarith
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ1
  have hsplit : Q ^ (1 - ε) = Q * Q ^ (-ε) := by
    rw [Real.rpow_sub hQ0, Real.rpow_one, Real.rpow_neg hQ0.le]; ring
  have hsm : Q ^ (-ε) * (3 + Real.log Q) ≤ 3 * (d * (Ecal * W.Iw) / (96 * (W.wmax + 1))) := by
    have : Q ^ (-ε) * (1 + Real.log Q) ^ 1 ≤ d * (Ecal * W.Iw) / (96 * (W.wmax + 1)) := hsmall
    rw [pow_one] at this
    have h0 : 0 ≤ Q ^ (-ε) := Real.rpow_nonneg hQ0.le _
    nlinarith
  have hkey : 4 * W.wmax * Q * K * (1 + Real.log K) ≤ d * W.H Q := by
    calc 4 * W.wmax * Q * K * (1 + Real.log K)
        ≤ 4 * W.wmax * Q * (4 * Q ^ (1 - ε)) * (3 + Real.log Q) := by gcongr
      _ = 16 * W.wmax * Q ^ 2 * (Q ^ (-ε) * (3 + Real.log Q)) := by rw [hsplit]; ring
      _ ≤ 16 * W.wmax * Q ^ 2 * (3 * (d * (Ecal * W.Iw) / (96 * (W.wmax + 1)))) := by gcongr
      _ = d * (1 / 2 * (Ecal * W.Iw * Q ^ 2)) * (W.wmax / (W.wmax + 1)) := by
          field_simp; ring
      _ ≤ d * (1 / 2 * (Ecal * W.Iw * Q ^ 2)) * 1 := by
          gcongr
          rw [div_le_iff₀ (by linarith)]; linarith
      _ ≤ d * W.H Q := by rw [mul_one]; gcongr
  linarith

/-! ### Regime (ii) (the band) -/

theorem regime_ii_bound (W : Weight) {ε Cband d : ℝ} (hε : 0 < ε) (hε3 : ε < 1 / 3)
    (hband : BandLS W ε Cband) (hd : 0 < d) :
    ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ (T : ℝ) (y : ℕ → ℝ), VanishBeyond P Q y →
      ∀ u : ℝ, u ≤ (1 + ε) * Real.log Q →
        famForm W Q (P.rangeZ Q) (xs P Q T y u) ≤
          (Cband + d) * W.H Q * normSq (P.rangeZ Q) (xs P Q T y u) := by
  obtain ⟨Q₁, hQ₁⟩ := hband d hd
  have hev : ∀ᶠ Q : ℝ in atTop, Q₁ ≤ Q ∧ 4 ≤ Q ^ ε ∧ 3 ≤ Q ^ (1 - ε) ∧ 1 ≤ Q :=
    (eventually_ge_atTop Q₁).and (((tendsto_rpow_atTop hε).eventually_ge_atTop 4).and
      (((tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 - ε)).eventually_ge_atTop 3).and
        (eventually_ge_atTop 1)))
  obtain ⟨Q₀, hQ₀⟩ := Filter.eventually_atTop.1 hev
  refine ⟨Q₀, fun Q hQ T y hy u hu => ?_⟩
  obtain ⟨hQQ₁, hQε, hQε', hQ1⟩ := hQ₀ Q hQ
  have hQ0 : 0 < Q := by linarith
  rw [famForm_congr_supp W Q (supp_iff_of_xs P hy u), normSq_congr_supp (supp_iff_of_xs P hy u)]
  have heu := rpow_le_of_log_le hQ0 hu
  have h1 : 1 ≤ Q ^ (1 + ε) := Real.one_le_rpow hQ1 (by linarith)
  have hK : (Kloc u : ℝ) ≤ Q ^ (1 + 2 * ε) := by
    have e : Q ^ (1 + 2 * ε) = Q ^ ε * Q ^ (1 + ε) := by
      rw [← Real.rpow_add hQ0]; ring_nf
    have := Kloc_le u
    rw [e]; nlinarith
  have htop : ((N0 u + Kloc u - 1 : ℤ) : ℝ) ≤ Q ^ 2 := by
    have e : Q ^ 2 = Q ^ (1 - ε) * Q ^ (1 + ε) := by
      rw [← Real.rpow_add hQ0, show (1 - ε) + (1 + ε) = ((2 : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
    have := top_le u
    rw [e]; nlinarith
  exact hQ₁ Q hQQ₁ (Kloc u) hK (N0 u) (one_le_N0 u) htop _

/-! ### Regime (iii): supports -/

lemma vanish_aR {Q : ℝ} (hQ : 1 < Q) : VanishBeyond P Q (aR P Q) := by
  intro k hk; simp [aR, VanishBeyond.aVec P hQ k hk]

lemma vanish_aNR {Q : ℝ} (hQ : 1 < Q) : VanishBeyond P Q (aNR P Q) := by
  intro k hk; simp [aNR, VanishBeyond.aVec P hQ k hk]

lemma vanish_aPP {Q : ℝ} (hQ : 1 < Q) (x : ℝ) : VanishBeyond P Q (aPP P Q x) := by
  intro k hk; simp [aPP, VanishBeyond.aVec P hQ k hk]

lemma rough_of_xs_aR {Q T u : ℝ} {n : ℤ} (h : xs P Q T (aR P Q) u n ≠ 0) : IsRough Q n := by
  obtain ⟨hn, hy, -⟩ := xs_ne_zero P h
  unfold aR at hy
  split_ifs at hy with hr
  · rwa [Int.toNat_of_nonneg (by omega)] at hr
  · exact absurd rfl hy

lemma aR_eq (Q T : ℝ) : aR P Q = P.bVec Q T + P.aSharp Q T - aNR P Q := by
  funext n
  have := congrFun (aR_add_aNR P Q) n
  simp only [Pi.add_apply] at this
  simp only [Pi.sub_apply, Pi.add_apply, PrimeSetup.bVec]
  linarith

/-- In regime (iii) the non-rough part of `x_a^s(u)` lives on `n > Q^{1+ε}/2`. -/
lemma xs_aNR_eq_aPP {Q : ℝ} (hQ : 1 < Q) {ε : ℝ} (T : ℝ) {u : ℝ}
    (hu : (1 + ε) * Real.log Q < u) :
    xs P Q T (aNR P Q) u = xs P Q T (aPP P Q (Q ^ (1 + ε) / 2)) u := by
  apply xs_congr
  intro k hk hlt
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hbig : Q ^ (1 + ε) / 2 < k := by
    rw [abs_lt] at hlt
    have h1 : Real.exp (u - 1 / 2) < k := by
      rw [← Real.exp_log hk0]; exact Real.exp_lt_exp.mpr (by linarith)
    have h2 : Q ^ (1 + ε) * Real.exp (-(1 / 2)) < Real.exp (u - 1 / 2) := by
      rw [Real.rpow_def_of_pos (by linarith), ← Real.exp_add]
      exact Real.exp_lt_exp.mpr (by linarith)
    have h3 := half_le_exp_neg_half
    have h4 : 0 < Q ^ (1 + ε) := Real.rpow_pos_of_pos (by linarith) _
    nlinarith
  unfold aNR aPP
  split_ifs with h1 h2 h2 <;> simp_all

/-! ### The pointwise bound (Steps 0–4) -/

/-- The step function `c(u)`: `c₁` on `u ≤ (1−ε)ℓ`, `c₂` on `(1−ε)ℓ < u ≤ (1+ε)ℓ`, `c₃` beyond. -/
def cfun (ℓ ε c₁ c₂ c₃ u : ℝ) : ℝ :=
  if u ≤ (1 - ε) * ℓ then c₁ else if u ≤ (1 + ε) * ℓ then c₂ else c₃

lemma cfun_nonneg {ℓ ε c₁ c₂ c₃ : ℝ} (h₁ : 0 ≤ c₁) (h₂ : 0 ≤ c₂) (h₃ : 0 ≤ c₃) (u : ℝ) :
    0 ≤ cfun ℓ ε c₁ c₂ c₃ u := by
  unfold cfun; split_ifs <;> assumption

/-- The algebra of Step 4 (pure inequalities). -/
lemma chain_iii {κ ε₀ M A₁ A₂ cH Fb Fa Fsa Fta FR FNR LR Lb Ls LNR Nb Nta Ns Npp : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hM : 0 ≤ M) (hcH : 0 ≤ cH) (hNpp : 0 ≤ Npp) (hLs0 : 0 ≤ Ls)
    (h0 : Fb ≤ Fa + ε₀) (h1 : Fa ≤ (1 + κ) * Fsa + (1 + κ⁻¹) * Fta) (h2 : Fta ≤ M * Nta)
    (h3 : Fsa ≤ (1 + κ) * FR + (1 + κ⁻¹) * FNR) (h4 : FNR ≤ M * Npp) (h5 : FR ≤ LR)
    (h6 : LR ≤ (1 + κ) * Lb + (1 + κ⁻¹) * (2 * Ls + 2 * LNR)) (h7 : Lb ≤ cH * Nb)
    (h8 : LNR ≤ cH * Npp) (h9 : Ls ≤ A₁ * Ns + A₂) :
    Fb ≤ (1 + κ) ^ 3 * cH * Nb + ((1 + κ⁻¹) * M * Nta + 8 * (1 + κ⁻¹) * (A₁ * Ns + A₂) +
      (1 + κ⁻¹) * (8 * cH + 2 * M) * Npp + ε₀) := by
  set a := 1 + κ with ha
  set b := 1 + κ⁻¹ with hb
  set X := A₁ * Ns + A₂ with hX
  set Y := cH * Npp with hY
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by have := inv_pos.mpr hκ; linarith
  have ha2 : a ≤ 2 := by linarith
  have haa : a * a ≤ 4 := by nlinarith
  have hX0 : 0 ≤ X := hLs0.trans h9
  have hY0 : 0 ≤ Y := mul_nonneg hcH hNpp
  have hMN : 0 ≤ M * Npp := mul_nonneg hM hNpp
  have e1 : LR ≤ a * (cH * Nb) + b * (2 * X + 2 * Y) :=
    h6.trans (add_le_add (mul_le_mul_of_nonneg_left h7 ha0)
      (mul_le_mul_of_nonneg_left (by linarith) hb0))
  have e2 : Fsa ≤ a * (a * (cH * Nb) + b * (2 * X + 2 * Y)) + b * (M * Npp) :=
    h3.trans (add_le_add (mul_le_mul_of_nonneg_left (h5.trans e1) ha0)
      (mul_le_mul_of_nonneg_left h4 hb0))
  have e3 : Fb ≤ a * (a * (a * (cH * Nb) + b * (2 * X + 2 * Y)) + b * (M * Npp)) +
      b * (M * Nta) + ε₀ := by
    have := h1.trans (add_le_add (mul_le_mul_of_nonneg_left e2 ha0)
      (mul_le_mul_of_nonneg_left h2 hb0))
    linarith
  have f2 : (a * a) * (b * (2 * X + 2 * Y)) ≤ 4 * (b * (2 * X + 2 * Y)) :=
    mul_le_mul_of_nonneg_right haa (by positivity)
  have f3 : a * (b * (M * Npp)) ≤ 2 * (b * (M * Npp)) :=
    mul_le_mul_of_nonneg_right ha2 (by positivity)
  calc Fb ≤ a * (a * (a * (cH * Nb) + b * (2 * X + 2 * Y)) + b * (M * Npp)) +
        b * (M * Nta) + ε₀ := e3
    _ = a ^ 3 * cH * Nb + (a * a) * (b * (2 * X + 2 * Y)) + a * (b * (M * Npp)) +
        b * (M * Nta) + ε₀ := by ring
    _ ≤ a ^ 3 * cH * Nb + 4 * (b * (2 * X + 2 * Y)) + 2 * (b * (M * Npp)) +
        b * (M * Nta) + ε₀ := by linarith
    _ = _ := by ring

/-- **Steps 0–4, pointwise in `u`.** -/
theorem pointwise_bound (W : Weight) {Q T ε κ c₁ c₂ c₃ M A₁ A₂ ε₀ x : ℝ} (hQ : 1 < Q)
    (hε : 0 ≤ ε) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hH : 0 ≤ W.H Q) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (hc₃ : 0 ≤ c₃) (hM : 0 ≤ M) (hA₁ : 0 ≤ A₁) (hA₂ : 0 ≤ A₂) (hε₀ : 0 ≤ ε₀)
    (h0 : ∀ u, famForm W Q (P.rangeZ Q) (P.xVec Q T (P.bVec Q T) u) ≤
      famForm W Q (P.rangeZ Q) (P.xVec Q T (P.aVec Q) u) + ε₀)
    (h1 : ∀ u, u ≤ (1 - ε) * Real.log Q → famForm W Q (P.rangeZ Q) (xs P Q T (P.bVec Q T) u) ≤
      c₁ * W.H Q * normSq (P.rangeZ Q) (xs P Q T (P.bVec Q T) u))
    (h2 : ∀ u, u ≤ (1 + ε) * Real.log Q → famForm W Q (P.rangeZ Q) (xs P Q T (P.bVec Q T) u) ≤
      c₂ * W.H Q * normSq (P.rangeZ Q) (xs P Q T (P.bVec Q T) u))
    (h3 : ∀ z : ℤ → ℂ, levelForm (levels Q) (aNat W Q) (P.rangeZ Q) z ≤
      c₃ * W.H Q * normSq (P.rangeZ Q) z)
    (h4 : ∀ z : ℤ → ℂ, famForm W Q (P.rangeZ Q) z ≤ M * normSq (P.rangeZ Q) z)
    (h5 : ∀ u, levelForm (levels Q) (aNat W Q) (P.rangeZ Q) (xs P Q T (P.aSharp Q T) u) ≤
      A₁ * normSq (P.rangeZ Q) (xs P Q T (P.aSharp Q T) u) + A₂)
    (h6 : ∀ u, (1 + ε) * Real.log Q < u → xs P Q T (aNR P Q) u = xs P Q T (aPP P Q x) u)
    (u : ℝ) :
    famForm W Q (P.rangeZ Q) (P.xVec Q T (P.bVec Q T) u) ≤
      (1 + κ) ^ 3 * (cfun (Real.log Q) ε c₁ c₂ c₃ u * W.H Q) *
          normSq (P.rangeZ Q) (xs P Q T (P.bVec Q T) u) +
        ((1 + κ⁻¹) * M * (normSq (P.rangeZ Q) (xt P Q T (P.aVec Q) u) +
            normSq (P.rangeZ Q) (xt P Q T (P.bVec Q T) u)) +
          8 * (1 + κ⁻¹) * (A₁ * normSq (P.rangeZ Q) (xs P Q T (P.aSharp Q T) u) + A₂) +
          (1 + κ⁻¹) * (8 * (c₃ * W.H Q) + 2 * M) *
            normSq (P.rangeZ Q) (xs P Q T (aPP P Q x) u) + ε₀) := by
  classical
  have hQ0 : 0 < Q := by linarith
  have hℓ : 0 < Real.log Q := Real.log_pos hQ
  set I := P.rangeZ Q with hI
  set F := famForm W Q I with hF
  set LF := levelForm (levels Q) (aNat W Q) I with hLF
  set N := normSq I with hN
  have hb0 : 0 ≤ 1 + κ⁻¹ := by have := inv_pos.mpr hκ; linarith
  have ha1 : 1 ≤ 1 + κ := by linarith
  have hNn : ∀ z, 0 ≤ N z := fun z => normSq_nonneg' _ _
  have hFn : ∀ z, 0 ≤ F z := fun z => famForm_nonneg' W Q _ _
  have hLFn : ∀ z, 0 ≤ LF z := fun z => levelForm_nonneg (fun e he => aNat_nonneg W Q hQ0 e he) _ _
  set E := (1 + κ⁻¹) * M * (N (xt P Q T (P.aVec Q) u) + N (xt P Q T (P.bVec Q T) u)) +
      8 * (1 + κ⁻¹) * (A₁ * N (xs P Q T (P.aSharp Q T) u) + A₂) +
      (1 + κ⁻¹) * (8 * (c₃ * W.H Q) + 2 * M) * N (xs P Q T (aPP P Q x) u) + ε₀ with hE
  have hEb : (1 + κ⁻¹) * (M * N (xt P Q T (P.bVec Q T) u)) ≤ E := by
    have t1 : 0 ≤ (1 + κ⁻¹) * M * N (xt P Q T (P.aVec Q) u) := by
      have := hNn (xt P Q T (P.aVec Q) u); positivity
    have t2 : 0 ≤ 8 * (1 + κ⁻¹) * (A₁ * N (xs P Q T (P.aSharp Q T) u) + A₂) := by
      have := hNn (xs P Q T (P.aSharp Q T) u); positivity
    have t3 : 0 ≤ (1 + κ⁻¹) * (8 * (c₃ * W.H Q) + 2 * M) * N (xs P Q T (aPP P Q x) u) := by
      have := hNn (xs P Q T (aPP P Q x) u); positivity
    rw [hE]; nlinarith
  by_cases hreg : u ≤ (1 + ε) * Real.log Q
  · -- regimes (i), (ii)
    set c := cfun (Real.log Q) ε c₁ c₂ c₃ u with hc
    have hc0 : 0 ≤ c := cfun_nonneg hc₁ hc₂ hc₃ u
    have hbound : F (xs P Q T (P.bVec Q T) u) ≤ c * W.H Q * N (xs P Q T (P.bVec Q T) u) := by
      rw [hc]; unfold cfun
      split_ifs with h
      · exact h1 u h
      · exact h2 u hreg
    have hsplit := lemM3_i W Q I (xs P Q T (P.bVec Q T) u) (xt P Q T (P.bVec Q T) u) κ hκ
    rw [← xVec_eq_xs_add_xt] at hsplit
    have hcHN : 0 ≤ c * W.H Q * N (xs P Q T (P.bVec Q T) u) := by
      have := hNn (xs P Q T (P.bVec Q T) u); positivity
    have ha3 : (1 + κ) ≤ (1 + κ) ^ 3 := le_self_pow₀ ha1 (by norm_num)
    calc F (P.xVec Q T (P.bVec Q T) u)
        ≤ (1 + κ) * F (xs P Q T (P.bVec Q T) u) + (1 + κ⁻¹) * F (xt P Q T (P.bVec Q T) u) := hsplit
      _ ≤ (1 + κ) * (c * W.H Q * N (xs P Q T (P.bVec Q T) u)) +
            (1 + κ⁻¹) * (M * N (xt P Q T (P.bVec Q T) u)) :=
          add_le_add (mul_le_mul_of_nonneg_left hbound (by linarith))
            (mul_le_mul_of_nonneg_left (h4 _) hb0)
      _ ≤ (1 + κ) ^ 3 * (c * W.H Q * N (xs P Q T (P.bVec Q T) u)) + E :=
          add_le_add (mul_le_mul_of_nonneg_right ha3 hcHN) hEb
      _ = _ := by ring
  · -- regime (iii)
    replace hreg := not_le.mp hreg
    have hcf : cfun (Real.log Q) ε c₁ c₂ c₃ u = c₃ := by
      unfold cfun
      rw [if_neg (by nlinarith), if_neg (by linarith)]
    rw [hcf]
    have hvR := vanish_aR P hQ
    -- the rough index set
    set IR := I.filter (fun n => IsRough Q n) with hIR
    have hsuppR : ∀ n, xs P Q T (aR P Q) u n ≠ 0 → (n ∈ I ↔ n ∈ IR) := by
      intro n hn
      have h1 := mem_rangeZ_of_xs P hvR hn
      have h2 := rough_of_xs_aR P hn
      simp only [hIR, Finset.mem_filter]
      exact ⟨fun h => ⟨h, h2⟩, fun h => h.1⟩
    have hR : F (xs P Q T (aR P Q) u) ≤ LF (xs P Q T (aR P Q) u) := by
      rw [hF, hLF, famForm_congr_supp W Q hsuppR, levelForm_congr_supp _ _ hsuppR]
      exact (lemmaS_rough W Q hQ0 IR (fun n hn => (Finset.mem_filter.mp hn).2) _).2
    have hxa : xs P Q T (P.aVec Q) u = xs P Q T (aR P Q) u + xs P Q T (aNR P Q) u := by
      rw [← xs_add, aR_add_aNR]
    have hxR : xs P Q T (aR P Q) u =
        xs P Q T (P.bVec Q T) u + (xs P Q T (P.aSharp Q T) u - xs P Q T (aNR P Q) u) := by
      rw [aR_eq P Q T, xs_sub, xs_add, add_sub_assoc]
    have hPP := h6 u hreg
    have e1 := lemM3_i W Q I (xs P Q T (P.aVec Q) u) (xt P Q T (P.aVec Q) u) κ hκ
    rw [← xVec_eq_xs_add_xt] at e1
    have e3 := lemM3_i W Q I (xs P Q T (aR P Q) u) (xs P Q T (aNR P Q) u) κ hκ
    rw [← hxa] at e3
    have e6 := levelForm_add_le (fun e he => aNat_nonneg W Q hQ0 e he) I
      (xs P Q T (P.bVec Q T) u) (xs P Q T (P.aSharp Q T) u - xs P Q T (aNR P Q) u) hκ
    rw [← hxR] at e6
    have e6' := levelForm_sub_le (fun e he => aNat_nonneg W Q hQ0 e he) I
      (xs P Q T (P.aSharp Q T) u) (xs P Q T (aNR P Q) u)
    have e6'' : LF (xs P Q T (aR P Q) u) ≤ (1 + κ) * LF (xs P Q T (P.bVec Q T) u) +
        (1 + κ⁻¹) * (2 * LF (xs P Q T (P.aSharp Q T) u) + 2 * LF (xs P Q T (aNR P Q) u)) :=
      e6.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left e6' hb0))
    have h4' : F (xs P Q T (aNR P Q) u) ≤ M * N (xs P Q T (aPP P Q x) u) := by
      rw [← hPP]; exact h4 _
    have h8' : LF (xs P Q T (aNR P Q) u) ≤ c₃ * W.H Q * N (xs P Q T (aPP P Q x) u) := by
      rw [← hPP]; exact h3 _
    have key := chain_iii hκ hκ1 hM (mul_nonneg hc₃ hH) (hNn _) (hLFn _) (h0 u) e1 (h4 _) e3 h4'
      hR e6'' (h3 _) h8' (h5 u)
    have hb' : 0 ≤ (1 + κ⁻¹) * M * N (xt P Q T (P.bVec Q T) u) := by
      have := hNn (xt P Q T (P.bVec Q T) u); positivity
    calc F (P.xVec Q T (P.bVec Q T) u) ≤ _ := key
      _ ≤ (1 + κ) ^ 3 * (c₃ * W.H Q) * N (xs P Q T (P.bVec Q T) u) + E := by
          rw [hE]; nlinarith

end Families.Phase3.C
