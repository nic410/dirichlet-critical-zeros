/-
# `prop:sharpLS` from `lem:dual`, `lem:C` and `lem:WH`
(Proposition 6.21)

`propSharpLS_of (hd : lemDual_Statement) (hC : lemC_Statement) (hWH : lemWH_Statement) :
propSharpLS_Statement`.

The TeX proof: "Enlarge `I` so that `Q ≤ K ≤ Q^{2−ε}`; combine Lemmas S and C with `1+κ² = 1+Q^{−ε/2}` and
`H = ℰI_wQ²(1+O(V_wI_w⁻¹Q^{−1/2}))` (Lemma WH)." Here:
* the interval `[N₀,N₀+K)` is enlarged to `[N₀,N₀+K')`, `K' = max(K,⌈Q⌉)` (so `Q ≤ K' ≤ Q^{2−ε}` once
  `Q^{1−ε} ≥ 2`), and `y` is extended by `0` (`levelForm_extend`, `normSq_extend`);
* `lem:S` is the proved `lemmaS_lambda_of_dual` (from `lem:dual`), with `κ = Q^{−ε/4} ≤ 1/4`
  (`Q ≥ 4^{4/ε}`), and `M = ℰI_wQ²C_T^+ + 𝔈` from `lem:C` (in `ℝ≥0∞`; `C_T^+ < ∞` converts it);
* `lem:WH` gives `ℰI_wQ² ≤ H + |c₀|V_wQ^{3/2}` and, for `Q ≥ (2|c₀|V_w/(ℰI_w))² + 2`, `ℰI_wQ² ≤ 2H`;
* `𝔈 ≤ 960(V_w + ‖w̃‖_∞η⁻²)Q^{2−ε/4}(log Q)³` for `Q ≥ e` (using `L_η + 1 ≤ η⁻²`).
The absolute constant is `c = 3840/ℰ + 2 + 2|c₀|/ℰ`, `c₀` the constant of `lem:WH`.
-/
import Families.Glue
import Families.Phase1.B.Omega
import Families.Phase1.B.Dual

noncomputable section

open scoped BigOperators
open Finset

namespace Families.Phase1.B

open Families

/-! ### Extending a vector by zero to a larger interval -/

lemma S_extend {I I' : Finset ℤ} (h : I ⊆ I') (y : ℤ → ℂ) (θ : ℝ) :
    S I' (fun n => if n ∈ I then y n else 0) θ = S I y θ := by
  unfold S
  calc ∑ n ∈ I', (if n ∈ I then y n else 0) * eA (n * θ)
      = ∑ n ∈ I, (if n ∈ I then y n else 0) * eA (n * θ) :=
        (Finset.sum_subset h fun n _ hn => by rw [if_neg hn, zero_mul]).symm
    _ = ∑ n ∈ I, y n * eA (n * θ) := Finset.sum_congr rfl fun n hn => by rw [if_pos hn]

lemma normSq_extend {I I' : Finset ℤ} (h : I ⊆ I') (y : ℤ → ℂ) :
    normSq I' (fun n => if n ∈ I then y n else 0) = normSq I y := by
  unfold normSq
  calc ∑ n ∈ I', ‖(if n ∈ I then y n else 0)‖ ^ 2
      = ∑ n ∈ I, ‖(if n ∈ I then y n else 0)‖ ^ 2 :=
        (Finset.sum_subset h fun n _ hn => by rw [if_neg hn]; simp).symm
    _ = ∑ n ∈ I, ‖y n‖ ^ 2 := Finset.sum_congr rfl fun n hn => by rw [if_pos hn]

lemma levelForm_extend {I I' : Finset ℤ} (h : I ⊆ I') (E : Finset ℕ) (a : ℕ → ℝ) (y : ℤ → ℂ) :
    levelForm E a I' (fun n => if n ∈ I then y n else 0) = levelForm E a I y := by
  unfold levelForm
  simp_rw [S_extend h]

lemma normSq_nonneg' (I : Finset ℤ) (y : ℤ → ℂ) : 0 ≤ normSq I y :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-! ### Elementary bounds -/

/-- `L_η + 1 ≤ η⁻²`. -/
lemma Leta_add_one_le (W : Weight) : Leta W.η + 1 ≤ W.η⁻¹ ^ 2 := by
  have hη := W.η_pos
  have hη1 : W.η < 1 := by linarith [W.η_lt_half]
  have h1 : Leta W.η ≤ W.η⁻¹ - 1 := by
    unfold Leta
    rw [one_div]
    exact Real.log_le_sub_one_of_pos (inv_pos.mpr hη)
  have h2 : 1 ≤ W.η⁻¹ := one_le_inv₀ hη |>.mpr hη1.le
  nlinarith

lemma Leta_add_one_nonneg (W : Weight) : 0 ≤ Leta W.η + 1 := by
  have hη := W.η_pos
  have hη1 : W.η < 1 := by linarith [W.η_lt_half]
  unfold Leta
  have : 0 ≤ Real.log (1 / W.η) := Real.log_nonneg (by rw [le_div_iff₀ hη]; linarith)
  linarith

/-- The final real inequality of `prop:sharpLS`, over abstract reals (`d = ℰ⁻¹`, `c0 = |c₀|`). -/
lemma sharpLS_key {E C Err H a1 a2 a3 P R c0 d : ℝ}
    (hd : 0 ≤ d) (hc0 : 0 ≤ c0) (hC0 : 0 ≤ C) (ha1 : 0 ≤ a1) (ha2 : 0 ≤ a2) (ha2le : a2 ≤ 1)
    (ha3 : 0 ≤ a3) (hP : 0 ≤ P) (hR : 0 ≤ R) (hErr0 : 0 ≤ Err) (hH : 0 ≤ H)
    (hEH1 : E * C ≤ H * C + c0 * d * R * a3 * E * C) (hEH2 : E ≤ 2 * H)
    (hErr : Err ≤ 960 * d * P * a1 * E) :
    (1 + a2) * (E * C + Err) ≤
      (C + (3840 * d + 2 + 2 * c0 * d) * (P * a1 + (a2 + R * a3) * C)) * H := by
  have k0 : (1 + a2) * Err ≤ 2 * Err := by
    have : 0 ≤ (1 - a2) * Err := mul_nonneg (by linarith) hErr0
    linarith
  have k1 : Err ≤ 960 * d * P * a1 * (2 * H) :=
    hErr.trans (mul_le_mul_of_nonneg_left hEH2 (by positivity))
  have k2 : a2 * C * E ≤ a2 * C * (2 * H) := mul_le_mul_of_nonneg_left hEH2 (by positivity)
  have k3 : c0 * d * R * a3 * C * E ≤ c0 * d * R * a3 * C * (2 * H) :=
    mul_le_mul_of_nonneg_left hEH2 (by positivity)
  have k4 : 0 ≤ H * ((2 + 2 * c0 * d) * (P * a1)) := by positivity
  have k5 : 0 ≤ H * ((3840 * d + 2 * c0 * d) * (a2 * C)) := by positivity
  have k6 : 0 ≤ H * ((3840 * d + 2) * (R * a3 * C)) := by positivity
  have hEC : E * C ≤ H * C + c0 * d * R * a3 * C * (2 * H) := by
    have e : c0 * d * R * a3 * E * C = c0 * d * R * a3 * C * E := by ring
    linarith
  calc (1 + a2) * (E * C + Err) = E * C + a2 * C * E + (1 + a2) * Err := by ring
    _ ≤ (H * C + c0 * d * R * a3 * C * (2 * H)) + a2 * C * (2 * H) +
          2 * (960 * d * P * a1 * (2 * H)) := by linarith
    _ ≤ _ := by linarith

/-- The error term of `lem:C` is `≤ 960 ℰ⁻¹ P a₁ ℰI_wQ²` with `P = (V_w + ‖w̃‖_∞η⁻²)/I_w`,
`a₁ = Q^{−ε/4}(log Q)³` (for `Q ≥ e`). -/
lemma lemC_err_le (W : Weight) {Q ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (hQe : Real.exp 1 ≤ Q) :
    6 * W.wtmax * W.η⁻¹ ^ 2 * Q ^ (2 - 3 * ε / 4) +
        120 * W.Vw * Q ^ (2 - ε / 4) * (1 + Real.log Q) ^ 3 + 3 * W.wtmax * (Leta W.η + 1)
      ≤ 960 * Ecal⁻¹ * ((W.Vw + W.wtmax * W.η⁻¹ ^ 2) / W.Iw) * (Q ^ (-ε / 4) * Real.log Q ^ 3) *
          (Ecal * W.Iw * Q ^ 2) := by
  have hEc := Ecal_pos
  have hIw : 0 < W.Iw := W.Iw_pos
  have hVw : 0 ≤ W.Vw := ENNReal.toReal_nonneg
  have hwt := wtmax_nonneg W
  have hQge1 : 1 ≤ Q := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hQe
  have hQpos : 0 < Q := by linarith
  have hlog : 1 ≤ Real.log Q := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hQe
  set a1 : ℝ := Q ^ (-ε / 4) * Real.log Q ^ 3 with ha1
  have hlog3 : 1 ≤ Real.log Q ^ 3 := one_le_pow₀ hlog
  have hQeps : Q ^ (-ε / 4) ≤ a1 := le_mul_of_one_le_right (by positivity) hlog3
  have hsplit : ∀ r : ℝ, Q ^ (2 + r) = Q ^ 2 * Q ^ r := fun r => by
    rw [Real.rpow_add hQpos, Real.rpow_two]
  have e1 : Q ^ (2 - 3 * ε / 4) ≤ Q ^ 2 * a1 := by
    rw [show (2 : ℝ) - 3 * ε / 4 = 2 + (-(3 * ε / 4)) by ring, hsplit]
    refine mul_le_mul_of_nonneg_left (le_trans ?_ hQeps) (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le hQge1 (by linarith)
  have h8 : (1 + Real.log Q) ^ 3 ≤ 8 * Real.log Q ^ 3 := by
    have : 1 + Real.log Q ≤ 2 * Real.log Q := by linarith
    calc (1 + Real.log Q) ^ 3 ≤ (2 * Real.log Q) ^ 3 := pow_le_pow_left₀ (by linarith) this 3
      _ = 8 * Real.log Q ^ 3 := by ring
  have e2 : Q ^ (2 - ε / 4) * (1 + Real.log Q) ^ 3 ≤ 8 * (Q ^ 2 * a1) := by
    rw [show (2 : ℝ) - ε / 4 = 2 + (-ε / 4) by ring, hsplit, ha1]
    have hq : 0 ≤ Q ^ 2 * Q ^ (-ε / 4) := by positivity
    calc Q ^ 2 * Q ^ (-ε / 4) * (1 + Real.log Q) ^ 3
        ≤ Q ^ 2 * Q ^ (-ε / 4) * (8 * Real.log Q ^ 3) := mul_le_mul_of_nonneg_left h8 hq
      _ = 8 * (Q ^ 2 * (Q ^ (-ε / 4) * Real.log Q ^ 3)) := by ring
  have e3 : 1 ≤ Q ^ 2 * a1 := by
    have h1 : 1 ≤ Q ^ (2 + (-ε / 4)) := Real.one_le_rpow hQge1 (by linarith)
    rw [hsplit] at h1
    calc (1 : ℝ) ≤ Q ^ 2 * Q ^ (-ε / 4) := h1
      _ ≤ Q ^ 2 * Q ^ (-ε / 4) * Real.log Q ^ 3 := le_mul_of_one_le_right (by positivity) hlog3
      _ = Q ^ 2 * a1 := by rw [ha1]; ring
  have e4 := Leta_add_one_le W
  have hwη : 0 ≤ W.wtmax * W.η⁻¹ ^ 2 := by positivity
  have hRHS : 960 * Ecal⁻¹ * ((W.Vw + W.wtmax * W.η⁻¹ ^ 2) / W.Iw) * a1 * (Ecal * W.Iw * Q ^ 2) =
      960 * W.Vw * (Q ^ 2 * a1) + 960 * (W.wtmax * W.η⁻¹ ^ 2) * (Q ^ 2 * a1) := by
    field_simp
  rw [hRHS]
  have t1 : 6 * W.wtmax * W.η⁻¹ ^ 2 * Q ^ (2 - 3 * ε / 4) ≤
      6 * (W.wtmax * W.η⁻¹ ^ 2) * (Q ^ 2 * a1) := by
    rw [show 6 * W.wtmax * W.η⁻¹ ^ 2 * Q ^ (2 - 3 * ε / 4) =
      6 * (W.wtmax * W.η⁻¹ ^ 2) * Q ^ (2 - 3 * ε / 4) by ring]
    exact mul_le_mul_of_nonneg_left e1 (by positivity)
  have t2 : 120 * W.Vw * Q ^ (2 - ε / 4) * (1 + Real.log Q) ^ 3 ≤ 960 * W.Vw * (Q ^ 2 * a1) := by
    rw [show 120 * W.Vw * Q ^ (2 - ε / 4) * (1 + Real.log Q) ^ 3 =
      120 * W.Vw * (Q ^ (2 - ε / 4) * (1 + Real.log Q) ^ 3) by ring]
    calc 120 * W.Vw * (Q ^ (2 - ε / 4) * (1 + Real.log Q) ^ 3)
        ≤ 120 * W.Vw * (8 * (Q ^ 2 * a1)) := mul_le_mul_of_nonneg_left e2 (by positivity)
      _ = 960 * W.Vw * (Q ^ 2 * a1) := by ring
  have t3 : 3 * W.wtmax * (Leta W.η + 1) ≤ 3 * (W.wtmax * W.η⁻¹ ^ 2) * (Q ^ 2 * a1) := by
    have : W.wtmax * (Leta W.η + 1) ≤ W.wtmax * W.η⁻¹ ^ 2 * (Q ^ 2 * a1) :=
      calc W.wtmax * (Leta W.η + 1) ≤ W.wtmax * W.η⁻¹ ^ 2 := mul_le_mul_of_nonneg_left e4 hwt
        _ ≤ W.wtmax * W.η⁻¹ ^ 2 * (Q ^ 2 * a1) := le_mul_of_one_le_right hwη e3
    linarith
  have hQa1 : 0 ≤ (W.wtmax * W.η⁻¹ ^ 2) * (Q ^ 2 * a1) := by positivity
  linarith

/-- `lem:WH` at a fixed large `Q`: `ℰI_wQ² ≤ H + |c₀|V_wQ^{3/2}` and, if `Q ≥ t² + 2` with
`t = 2|c₀|V_w/(ℰI_w)`, `ℰI_wQ² ≤ 2H`. -/
lemma wh_bounds (W : Weight) {c₀ Q : ℝ}
    (hWHQ : |W.H Q - Ecal * W.Iw * Q ^ 2| ≤ c₀ * W.Vw * Q ^ (3 / 2 : ℝ))
    (hQ : (2 * |c₀| * W.Vw / (Ecal * W.Iw)) ^ 2 + 2 ≤ Q) :
    Ecal * W.Iw * Q ^ 2 ≤ W.H Q + |c₀| * W.Vw * Q ^ (3 / 2 : ℝ) ∧
      Ecal * W.Iw * Q ^ 2 ≤ 2 * W.H Q := by
  have hEc := Ecal_pos
  have hIw : 0 < W.Iw := W.Iw_pos
  have hVw : 0 ≤ W.Vw := ENNReal.toReal_nonneg
  set t : ℝ := 2 * |c₀| * W.Vw / (Ecal * W.Iw) with ht
  have ht0 : 0 ≤ t := by positivity
  have hQpos : 0 < Q := by nlinarith [sq_nonneg t]
  have hX : 0 ≤ W.Vw * Q ^ (3 / 2 : ℝ) := by positivity
  have hEH1 : Ecal * W.Iw * Q ^ 2 ≤ W.H Q + |c₀| * W.Vw * Q ^ (3 / 2 : ℝ) := by
    have h1 := (abs_le.mp hWHQ).1
    have h2 : c₀ * W.Vw * Q ^ (3 / 2 : ℝ) ≤ |c₀| * W.Vw * Q ^ (3 / 2 : ℝ) := by
      rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self c₀) hX
    linarith
  refine ⟨hEH1, ?_⟩
  have hsq : t ≤ Q ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_sq ht0]
    exact Real.sqrt_le_sqrt (by linarith)
  have h12 : Q ^ (1 / 2 : ℝ) * Q ^ (3 / 2 : ℝ) = Q ^ 2 := by
    rw [← Real.rpow_add hQpos, ← Real.rpow_two]; norm_num
  have hQ320 : 0 ≤ Q ^ (3 / 2 : ℝ) := by positivity
  have h3 : t * Q ^ (3 / 2 : ℝ) ≤ Q ^ 2 := by
    rw [← h12]; exact mul_le_mul_of_nonneg_right hsq hQ320
  have hEI : 0 < Ecal * W.Iw := by positivity
  have h4 : 2 * (|c₀| * W.Vw * Q ^ (3 / 2 : ℝ)) ≤ Ecal * W.Iw * Q ^ 2 := by
    have e : 2 * (|c₀| * W.Vw * Q ^ (3 / 2 : ℝ)) = (Ecal * W.Iw) * (t * Q ^ (3 / 2 : ℝ)) := by
      rw [ht]; field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left h3 hEI.le
  linarith

/-! ### `prop:sharpLS` -/

/-- **`prop:sharpLS`** from `lem:dual`, `lem:C` and `lem:WH` (Proposition 6.21). -/
theorem propSharpLS_of (hd : lemDual_Statement) (hC : lemC_Statement) (hWH : lemWH_Statement) :
    propSharpLS_Statement := by
  obtain ⟨c₀, hc₀⟩ := hWH
  have hEc := Ecal_pos
  refine ⟨3840 * Ecal⁻¹ + 2 + 2 * |c₀| * Ecal⁻¹, fun ε hε hε1 W hW => ?_⟩
  obtain ⟨Q₁, hQ₁⟩ := hC ε hε hε1
  have hC0 : 0 ≤ (CTp W).toReal := ENNReal.toReal_nonneg
  have hIw : 0 < W.Iw := W.Iw_pos
  have hVw : 0 ≤ W.Vw := ENNReal.toReal_nonneg
  have hwt := wtmax_nonneg W
  refine ⟨max (max Q₁ ((4 : ℝ) ^ (4 / ε))) (max ((2 : ℝ) ^ (1 / (1 - ε)))
    (max (Real.exp 1) ((2 * |c₀| * W.Vw / (Ecal * W.Iw)) ^ 2 + 2))), fun Q hQ N₀ K hK y => ?_⟩
  have hQ1' : Q₁ ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hQ
  have hQ4 : (4 : ℝ) ^ (4 / ε) ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hQ
  have hQ2 : (2 : ℝ) ^ (1 / (1 - ε)) ≤ Q :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hQ
  have hQe : Real.exp 1 ≤ Q := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _)) hQ
  have hQ3 : (2 * |c₀| * W.Vw / (Ecal * W.Iw)) ^ 2 + 2 ≤ Q :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hQ
  have hQge1 : 1 ≤ Q := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hQe
  have hQpos : 0 < Q := by linarith
  -- `κ = Q^{−ε/4} ≤ 1/4`
  have hκpos : 0 < Q ^ (-ε / 4) := Real.rpow_pos_of_pos hQpos _
  have hκle : Q ^ (-ε / 4) ≤ 1 / 4 := by
    have h4 : (4 : ℝ) ≤ Q ^ (ε / 4) := by
      have := Real.rpow_le_rpow (by positivity) hQ4 (by positivity : (0 : ℝ) ≤ ε / 4)
      rwa [← Real.rpow_mul (by norm_num), show 4 / ε * (ε / 4) = (1 : ℝ) by field_simp,
        Real.rpow_one] at this
    rw [show -ε / 4 = -(ε / 4) by ring, Real.rpow_neg hQpos.le]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    linarith
  have hκsq : (Q ^ (-ε / 4)) ^ 2 = Q ^ (-ε / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQpos.le]
    norm_num
    ring_nf
  have ha2le : Q ^ (-ε / 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hQge1 (by linarith)
  -- the enlarged interval `[N₀, N₀ + K')`, `K' = max(K, ⌈Q⌉)`
  have hK'1 : 1 ≤ max K ⌈Q⌉₊ :=
    le_trans (Nat.one_le_iff_ne_zero.mpr (by positivity)) (le_max_right _ _)
  have hQK' : Q ≤ ((max K ⌈Q⌉₊ : ℕ) : ℝ) :=
    (Nat.le_ceil Q).trans (by exact_mod_cast le_max_right K ⌈Q⌉₊)
  have hK'le : ((max K ⌈Q⌉₊ : ℕ) : ℝ) ≤ Q ^ (2 - ε) := by
    rcases le_total K ⌈Q⌉₊ with h | h
    · rw [max_eq_right h]
      have hQ1e : (2 : ℝ) ≤ Q ^ (1 - ε) := by
        have := Real.rpow_le_rpow (by positivity) hQ2 (by linarith : (0 : ℝ) ≤ 1 - ε)
        rwa [← Real.rpow_mul (by norm_num), show 1 / (1 - ε) * (1 - ε) = (1 : ℝ) by
          field_simp [(by linarith : (1 : ℝ) - ε ≠ 0)], Real.rpow_one] at this
      have hsplit : Q ^ (2 - ε) = Q * Q ^ (1 - ε) := by
        rw [show (2 : ℝ) - ε = 1 + (1 - ε) by ring, Real.rpow_add hQpos, Real.rpow_one]
      rw [hsplit]
      have := (Nat.ceil_lt_add_one hQpos.le).le
      nlinarith
    · rw [max_eq_left h]; exact hK
  have hsub : intervalZ N₀ K ⊆ intervalZ N₀ (max K ⌈Q⌉₊) := by
    refine Finset.Ico_subset_Ico_right ?_
    have : K ≤ max K ⌈Q⌉₊ := le_max_left _ _
    omega
  -- `M` from `lem:C`
  have hE0 : 0 < Ecal * W.Iw * Q ^ 2 := by positivity
  have hErr0 : 0 ≤ 6 * W.wtmax * W.η⁻¹ ^ 2 * Q ^ (2 - 3 * ε / 4) +
      120 * W.Vw * Q ^ (2 - ε / 4) * (1 + Real.log Q) ^ 3 + 3 * W.wtmax * (Leta W.η + 1) := by
    have := Leta_add_one_nonneg W
    have : 0 ≤ 1 + Real.log Q := by linarith [Real.log_nonneg hQge1]
    positivity
  have hM : ∀ θ, natConv W Q (Q ^ (-ε / 4) / ((max K ⌈Q⌉₊ : ℕ) : ℝ)) θ ≤
      Ecal * W.Iw * Q ^ 2 * (CTp W).toReal +
        (6 * W.wtmax * W.η⁻¹ ^ 2 * Q ^ (2 - 3 * ε / 4) +
          120 * W.Vw * Q ^ (2 - ε / 4) * (1 + Real.log Q) ^ 3 + 3 * W.wtmax * (Leta W.η + 1)) := by
    intro θ
    have h := hQ₁ W Q hQ1' (max K ⌈Q⌉₊) hQK' hK'le θ
    rw [← ENNReal.ofReal_toReal hW, ← ENNReal.ofReal_mul hE0.le,
      ← ENNReal.ofReal_add (by positivity) hErr0] at h
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
  -- `lem:S` (via `lem:dual`) on the enlarged interval
  have hS := lemmaS_lambda_of_dual hd W Q hQpos N₀ (max K ⌈Q⌉₊) hK'1 (Q ^ (-ε / 4)) hκpos hκle _ hM
    (fun n => if n ∈ intervalZ N₀ K then y n else 0)
  rw [levelForm_extend hsub, normSq_extend hsub] at hS
  refine hS.trans (mul_le_mul_of_nonneg_right ?_ (normSq_nonneg' _ _))
  -- the key inequality
  rw [hκsq]
  have hQ2' : (2 : ℝ) ≤ Q := by
    have := sq_nonneg (2 * |c₀| * W.Vw / (Ecal * W.Iw))
    linarith
  obtain ⟨hEH1, hEH2⟩ := wh_bounds W (hc₀ W Q hQ2').2 hQ3
  have hH0 : 0 ≤ W.H Q := by linarith
  have hQ32 : Q ^ (3 / 2 : ℝ) = Q ^ (-(1 / 2 : ℝ)) * Q ^ 2 := by
    rw [← Real.rpow_two, ← Real.rpow_add hQpos]; norm_num
  have hEH1' : Ecal * W.Iw * Q ^ 2 * (CTp W).toReal ≤ W.H Q * (CTp W).toReal +
      |c₀| * Ecal⁻¹ * (W.Vw / W.Iw) * Q ^ (-(1 / 2 : ℝ)) * (Ecal * W.Iw * Q ^ 2) *
        (CTp W).toReal := by
    have e : |c₀| * W.Vw * Q ^ (3 / 2 : ℝ) =
        |c₀| * Ecal⁻¹ * (W.Vw / W.Iw) * Q ^ (-(1 / 2 : ℝ)) * (Ecal * W.Iw * Q ^ 2) := by
      rw [hQ32]; field_simp
    have := mul_le_mul_of_nonneg_right hEH1 hC0
    rw [e] at this
    linarith
  have key := sharpLS_key (inv_nonneg.mpr hEc.le) (abs_nonneg c₀) hC0
    (mul_nonneg (Real.rpow_nonneg hQpos.le _) (pow_nonneg (Real.log_nonneg hQge1) 3))
    (by positivity : 0 ≤ Q ^ (-ε / 2)) ha2le
    (by positivity : 0 ≤ Q ^ (-(1 / 2 : ℝ)))
    (by positivity : 0 ≤ (W.Vw + W.wtmax * W.η⁻¹ ^ 2) / W.Iw)
    (by positivity : 0 ≤ W.Vw / W.Iw) hErr0 hH0 hEH1' hEH2 (lemC_err_le W hε hε1 hQe)
  refine key.trans (le_of_eq ?_)
  ring

/-- **`prop:sharpLS`** with `lem:dual` discharged (`lemDual_proof`): only `lem:C` and the named
hypothesis `lem:WH` remain. -/
theorem propSharpLS_of_lemC (hC : lemC_Statement) (hWH : lemWH_Statement) : propSharpLS_Statement :=
  propSharpLS_of lemDual_proof hC hWH

end Families.Phase1.B
