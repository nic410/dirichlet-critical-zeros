/-
# Montgomery 1969 density: assembly

* `family_line_bound`: `∑_{2≤q≤Q} ∑*_χ ∫_{−W}^{W} |L M_X − 1|(σ+iv) dv ≤ Φ(Q,W,δ)` for `σ ≥ 1/2+δ/2`
  (from `family_mean_square` and `|g| ≤ ε/2 + |g|²/(2ε)`).
* `family_count`: `∑_{2≤q≤Q} ∑*_χ N(1/2+δ, T, χ) ≤ (15/δ²) Φ(Q, T+1+2/δ, δ)` (Jensen, `jensen_zero_count`).
* `Montgomery69_Density_upTo_proof`: `Montgomery69_Density` in the range `T' ≤ Q^A`, for every `A > 0`.
-/
import Families.Hyp.Montgomery.MeanSquare
import Families.Hyp.Montgomery.Jensen

noncomputable section

open scoped BigOperators ComplexConjugate
open MeasureTheory Real Finset

namespace Families.Hyp.Montgomery

open Families

/-- `Φ(Q, W, δ) = 68 (1+2/δ)² (1 + log Q) Q² W Q^{−δ/8}`. -/
def Phi (Q W δ : ℝ) : ℝ := 68 * ((1 + 2 / δ) ^ 2 * (1 + Real.log Q)) * (Q ^ 2 * W) * Q ^ (-(δ / 8))

/-- `g_χ(σ + iv) = L(σ+iv, χ) M_X(σ+iv, χ) − 1` with `X = ⌊√Q⌋`. -/
def gfun (Q : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  Lfun χ s * Mol ⌊Real.sqrt Q⌋₊ χ s - 1

/-- **The family line bound** (AM–GM from the mean square). -/
theorem family_line_bound {Q W δ σ : ℝ} (hQ : 1 ≤ Q) (hW : 2 ≤ W) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (hσ : 1 / 2 + δ / 2 ≤ σ) :
    ∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, ∑ χ ∈ primChars q, ∫ v in (-W)..W,
        ‖gfun Q χ ((σ : ℂ) + (v : ℂ) * Complex.I)‖ ≤ Phi Q W δ := by
  have hQ0 : 0 < Q := by linarith
  have hW0 : 0 < W := by linarith
  have hMS := family_mean_square hQ hW hδ hδ' hσ
  set B : ℝ := (1 + 2 / δ) ^ 2 * (1 + Real.log Q) with hB
  set u : ℝ := Q ^ (-(δ / 8)) with hu
  have hB0 : 0 < B := by
    have : 0 < 1 + Real.log Q := by linarith [Real.log_nonneg hQ]
    positivity
  have hu0 : 0 < u := Real.rpow_pos_of_pos hQ0 _
  have hu2 : Q ^ (-(δ / 4)) = u ^ 2 := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hQ0.le]; congr 1; push_cast; ring
  have hMS' : ∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, ∑ χ ∈ primChars q, ∫ v in (-W)..W,
      ‖gfun Q χ ((σ : ℂ) + (v : ℂ) * Complex.I)‖ ^ 2 ≤ 2000 * B ^ 2 * (Q ^ 2 * W) * u ^ 2 := by
    refine hMS.trans (le_of_eq ?_)
    rw [hu2, hB]; ring
  set ε : ℝ := 45 * B * u with hε
  have hε0 : 0 < ε := by positivity
  -- pointwise AM–GM
  have hpt : ∀ (z : ℂ), ‖z‖ ≤ ε / 2 + ‖z‖ ^ 2 / (2 * ε) := by
    intro z
    have h := sq_nonneg (‖z‖ - ε)
    rw [div_add_div _ _ (by norm_num) (by positivity), le_div_iff₀ (by positivity)]
    nlinarith
  have hchar : ∀ q ∈ Finset.Icc 2 ⌊Q⌋₊, ∀ χ ∈ primChars q, ∫ v in (-W)..W,
      ‖gfun Q χ ((σ : ℂ) + (v : ℂ) * Complex.I)‖ ≤
      ε * W + (1 / (2 * ε)) * ∫ v in (-W)..W, ‖gfun Q χ ((σ : ℂ) + (v : ℂ) * Complex.I)‖ ^ 2 := by
    intro q hq χ _
    have hq2 : 2 ≤ q := (Finset.mem_Icc.mp hq).1
    haveI : NeZero q := ⟨by omega⟩
    have hχ1 : χ ≠ 1 := Zeta23.ThmE.ne_one_of_primitive (by omega) (mem_primChars.mp ‹_›)
    have hcont : Continuous (fun v : ℝ => gfun Q χ ((σ : ℂ) + (v : ℂ) * Complex.I)) := by
      have h1 : Continuous (fun v : ℝ => (σ : ℂ) + (v : ℂ) * Complex.I) := by fun_prop
      unfold gfun
      rw [Lfun_eq_LFunction]
      exact (((DirichletCharacter.differentiable_LFunction hχ1).continuous.comp h1).mul
        ((differentiable_Mol _ χ).continuous.comp h1)).sub continuous_const
    have hi1 : IntervalIntegrable (fun v : ℝ => ε / 2 + ‖gfun Q χ ((σ : ℂ) + (v : ℂ) * Complex.I)‖ ^ 2 /
        (2 * ε)) volume (-W) W :=
      (continuous_const.add ((hcont.norm.pow 2).div_const _)).intervalIntegrable _ _
    refine (intervalIntegral.integral_mono_on (by linarith) (hcont.norm.intervalIntegrable _ _) hi1
      (fun v _ => hpt _)).trans (le_of_eq ?_)
    have hsq : Continuous (fun v : ℝ => ‖gfun Q χ ((σ : ℂ) + (v : ℂ) * Complex.I)‖ ^ 2 / (2 * ε)) :=
      (hcont.norm.pow 2).div_const _
    have e1 : ∫ v in (-W)..W, (ε / 2 + ‖gfun Q χ ((σ : ℂ) + (v : ℂ) * Complex.I)‖ ^ 2 / (2 * ε)) =
        (∫ _ in (-W)..W, ε / 2) +
          ∫ v in (-W)..W, ‖gfun Q χ ((σ : ℂ) + (v : ℂ) * Complex.I)‖ ^ 2 / (2 * ε) :=
      intervalIntegral.integral_add intervalIntegrable_const (hsq.intervalIntegrable _ _)
    have e2 : ∫ v in (-W)..W, ‖gfun Q χ ((σ : ℂ) + (v : ℂ) * Complex.I)‖ ^ 2 / (2 * ε) =
        (∫ v in (-W)..W, ‖gfun Q χ ((σ : ℂ) + (v : ℂ) * Complex.I)‖ ^ 2) / (2 * ε) :=
      intervalIntegral.integral_div _ _
    rw [e1, e2, intervalIntegral.integral_const, smul_eq_mul]
    ring
  calc ∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, ∑ χ ∈ primChars q, ∫ v in (-W)..W,
        ‖gfun Q χ ((σ : ℂ) + (v : ℂ) * Complex.I)‖
      ≤ ∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, ∑ χ ∈ primChars q, (ε * W + (1 / (2 * ε)) *
          ∫ v in (-W)..W, ‖gfun Q χ ((σ : ℂ) + (v : ℂ) * Complex.I)‖ ^ 2) :=
        Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun χ hχ => hchar q hq χ hχ
    _ = (∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, ((primChars q).card : ℝ)) * (ε * W) + (1 / (2 * ε)) *
          ∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, ∑ χ ∈ primChars q,
            ∫ v in (-W)..W, ‖gfun Q χ ((σ : ℂ) + (v : ℂ) * Complex.I)‖ ^ 2 := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.mul_sum,
          Finset.sum_mul]
    _ ≤ Q ^ 2 * (ε * W) + (1 / (2 * ε)) * (2000 * B ^ 2 * (Q ^ 2 * W) * u ^ 2) := by
        gcongr
        · exact sum_card_primChars_le hQ
    _ ≤ Phi Q W δ := by
        rw [hε]
        unfold Phi
        rw [← hB, ← hu]
        have hP : 0 < Q ^ 2 * W := by positivity
        field_simp
        nlinarith [mul_pos (mul_pos hB0 hu0) hP]

lemma differentiable_Lfun {q : ℕ} (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) :
    Differentiable ℂ (Lfun χ) := by
  haveI : NeZero q := ⟨by omega⟩
  rw [Lfun_eq_LFunction]
  exact DirichletCharacter.differentiable_LFunction (Zeta23.ThmE.ne_one_of_primitive (by omega) hχ)

lemma continuous_gfun (Q : ℝ) {q : ℕ} (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) : Continuous (gfun Q χ) := by
  unfold gfun
  exact ((differentiable_Lfun hq hχ).continuous.mul (differentiable_Mol _ χ).continuous).sub
    continuous_const

/-- **Jensen for one character.** -/
lemma char_count (Q : ℝ) (hQ : 1 ≤ Q) {q : ℕ} (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) {T δ : ℝ} (hT : 0 ≤ T) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    (Ndens χ (1 / 2 + δ) T : ℝ) ≤
      5 / δ ^ 2 * ((2 * π)⁻¹ * (∫ θ in (0 : ℝ)..(2 * π),
          ∫ v in (-(T + 1 + 2 / δ))..(T + 1 + 2 / δ),
            ‖gfun Q χ (((1 / 2 + δ / 2 + 2 / δ + 2 / δ * Real.cos θ : ℝ) : ℂ) + (v : ℂ) * Complex.I)‖)
        + 2 * ∫ v in (-(T + 1 + 2 / δ))..(T + 1 + 2 / δ),
            ‖gfun Q χ (((1 / 2 + δ / 2 + 2 / δ : ℝ) : ℂ) + (v : ℂ) * Complex.I)‖) := by
  haveI : NeZero q := ⟨by omega⟩
  have hX1 : 1 ≤ ⌊Real.sqrt Q⌋₊ := Nat.le_floor (by
    have : (1 : ℝ) ≤ Real.sqrt Q := by rw [Real.one_le_sqrt]; exact hQ
    exact_mod_cast this)
  have hfar : ∀ s : ℂ, 1 / 2 + δ / 2 + 2 / δ ≤ s.re →
      ‖Lfun χ s * Mol ⌊Real.sqrt Q⌋₊ χ s - 1‖ ≤ 1 / 2 := by
    intro s hs
    have h4 : (4 : ℝ) ≤ 2 / δ := by rw [le_div_iff₀ hδ]; linarith
    rw [Lfun_eq_LFunction]
    exact norm_LMol_sub_one_le hX1 χ (by linarith)
  exact jensen_zero_count (Lfun χ) (Mol ⌊Real.sqrt Q⌋₊ χ) (differentiable_Lfun hq hχ)
    (differentiable_Mol _ χ) hδ hδ' hT (Ndens_set_finite χ (by omega) hχ (by linarith) T)
    (fun ρ h => mont_re_lt_one χ (by omega) hχ h) hfar

/-- `I_χ(σ) = ∫_{−W}^{W} |g_χ(σ+iv)| dv`. -/
def Iline (Q W : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (σ : ℝ) : ℝ :=
  ∫ v in (-W)..W, ‖gfun Q χ ((σ : ℂ) + (v : ℂ) * Complex.I)‖

/-- **The family count** for `q ≥ 2`. -/
theorem family_count {Q T δ : ℝ} (hQ : 1 ≤ Q) (hT : 2 ≤ T) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) :
    ∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, ∑ χ ∈ primChars q, (Ndens χ (1 / 2 + δ) T : ℝ) ≤
      15 / δ ^ 2 * Phi Q (T + 1 + 2 / δ) δ := by
  set W : ℝ := T + 1 + 2 / δ with hWdef
  have hW : 2 ≤ W := by have : 0 < 2 / δ := by positivity
                        linarith
  set a : ℝ := 1 / 2 + δ / 2 + 2 / δ with ha
  have hcontI : ∀ q ∈ Finset.Icc 2 ⌊Q⌋₊, ∀ χ ∈ primChars q,
      Continuous (fun θ : ℝ => Iline Q W χ (a + 2 / δ * Real.cos θ)) := by
    intro q hq χ hχ
    have hq2 : 2 ≤ q := (Finset.mem_Icc.mp hq).1
    have hg := continuous_gfun Q hq2 (mem_primChars.mp hχ)
    have : Continuous (Function.uncurry (fun (θ v : ℝ) =>
        ‖gfun Q χ (((a + 2 / δ * Real.cos θ : ℝ) : ℂ) + (v : ℂ) * Complex.I)‖)) := by
      unfold Function.uncurry
      exact (hg.comp (by fun_prop)).norm
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' this _ _
  -- per character
  have hchar : ∀ q ∈ Finset.Icc 2 ⌊Q⌋₊, ∀ χ ∈ primChars q, (Ndens χ (1 / 2 + δ) T : ℝ) ≤
      5 / δ ^ 2 * ((2 * π)⁻¹ * (∫ θ in (0 : ℝ)..(2 * π), Iline Q W χ (a + 2 / δ * Real.cos θ)) +
        2 * Iline Q W χ a) := by
    intro q hq χ hχ
    exact char_count Q hQ (Finset.mem_Icc.mp hq).1 (mem_primChars.mp hχ) (by linarith) hδ hδ'
  refine (Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun χ hχ => hchar q hq χ hχ).trans ?_
  simp_rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  -- the θ-integral of the family sum
  have hswap : ∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, ∑ χ ∈ primChars q,
      (∫ θ in (0 : ℝ)..(2 * π), Iline Q W χ (a + 2 / δ * Real.cos θ)) =
      ∫ θ in (0 : ℝ)..(2 * π), ∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, ∑ χ ∈ primChars q,
        Iline Q W χ (a + 2 / δ * Real.cos θ) := by
    rw [intervalIntegral.integral_finsetSum fun q hq =>
      (continuous_finsetSum _ fun χ hχ => hcontI q hq χ hχ).intervalIntegrable _ _]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [intervalIntegral.integral_finsetSum fun χ hχ => (hcontI q hq χ hχ).intervalIntegrable _ _]
  have hθ : ∀ θ : ℝ, ∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, ∑ χ ∈ primChars q,
      Iline Q W χ (a + 2 / δ * Real.cos θ) ≤ Phi Q W δ := by
    intro θ
    refine family_line_bound hQ hW hδ hδ' ?_
    have := Real.neg_one_le_cos θ
    have h2 : 0 < 2 / δ := by positivity
    nlinarith
  have hθint : ∫ θ in (0 : ℝ)..(2 * π), ∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, ∑ χ ∈ primChars q,
      Iline Q W χ (a + 2 / δ * Real.cos θ) ≤ 2 * π * Phi Q W δ := by
    have hπ : 0 ≤ 2 * π := by positivity
    refine (intervalIntegral.integral_mono_on hπ
      ((continuous_finsetSum _ fun q hq => continuous_finsetSum _ fun χ hχ =>
        hcontI q hq χ hχ).intervalIntegrable _ _) intervalIntegrable_const
      (fun θ _ => hθ θ)).trans (le_of_eq ?_)
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  have ha' : ∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, ∑ χ ∈ primChars q, Iline Q W χ a ≤ Phi Q W δ :=
    family_line_bound hQ hW hδ hδ' (by have : 0 < 2 / δ := by positivity
                                       linarith)
  rw [hswap]
  have hPhi : 0 ≤ Phi Q W δ := le_trans (by
    refine Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun χ _ => ?_
    exact intervalIntegral.integral_nonneg (by linarith) fun _ _ => norm_nonneg _) ha'
  have hπ0 : 0 < 2 * π := by positivity
  have h5 : 0 ≤ 5 / δ ^ 2 := by positivity
  calc 5 / δ ^ 2 * (((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), ∑ q ∈ Finset.Icc 2 ⌊Q⌋₊,
        ∑ χ ∈ primChars q, Iline Q W χ (a + 2 / δ * Real.cos θ)) +
        2 * ∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, ∑ χ ∈ primChars q, Iline Q W χ a)
      ≤ 5 / δ ^ 2 * ((2 * π)⁻¹ * (2 * π * Phi Q W δ) + 2 * Phi Q W δ) := by
        gcongr
    _ = 15 / δ ^ 2 * Phi Q W δ := by
        field_simp
        ring

/-! ### Assembly -/

lemma sum_card_primChars_le_one {Q : ℝ} (hQ : 1 ≤ Q) :
    ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ((primChars q).card : ℝ) ≤ Q ^ 2 := by
  have hM : ((⌊Q⌋₊ : ℕ) : ℝ) ≤ Q := Nat.floor_le (by linarith)
  calc ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ((primChars q).card : ℝ)
      ≤ ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (⌊Q⌋₊ : ℝ) := by
        refine Finset.sum_le_sum fun q hq => ?_
        have hq' := Finset.mem_Icc.mp hq
        haveI : NeZero q := ⟨by omega⟩
        exact (card_primChars_le' q).trans (by exact_mod_cast hq'.2)
    _ ≤ (⌊Q⌋₊ : ℝ) * ⌊Q⌋₊ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
        have : (Finset.Icc 1 ⌊Q⌋₊).card ≤ ⌊Q⌋₊ := by simp
        exact_mod_cast this
    _ ≤ Q ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) ⌊Q⌋₊]

lemma half_le_log_QT {Q T : ℝ} (hQ : 1 ≤ Q) (hT : 2 ≤ T) : 1 / 2 ≤ Real.log (Q * T) := by
  have h1 : Real.log 2 ≤ Real.log (Q * T) := Real.log_le_log (by norm_num) (by nlinarith)
  have := Real.log_two_gt_d9; linarith

/-- The trivial count per character, in terms of `log(QT)`. -/
lemma Ndens_le_family_trivial {K : ℝ} (hK : 0 < K)
    (hKb : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), 1 ≤ q → χ.IsPrimitive → ∀ σ T : ℝ, 0 < σ →
      0 ≤ T → (Ndens χ σ T : ℝ) ≤ K * (T + 1) * Real.log (q * (T + 3)))
    {Q T σ : ℝ} (hQ : 1 ≤ Q) (hT : 2 ≤ T) (hσ : 0 < σ) {q : ℕ} (hq : q ∈ Finset.Icc 1 ⌊Q⌋₊)
    {χ : DirichletCharacter ℂ q} (hχ : χ ∈ primChars q) :
    (Ndens χ σ T : ℝ) ≤ 5 * K * T * Real.log (Q * T) := by
  have hq' := Finset.mem_Icc.mp hq
  have hqQ : (q : ℝ) ≤ Q := (Nat.cast_le.mpr hq'.2).trans (Nat.floor_le (by linarith))
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq'.1
  have h := hKb q χ hq'.1 (mem_primChars.mp hχ) σ T hσ (by linarith)
  have hℓ := half_le_log_QT hQ hT
  have hlog : Real.log (q * (T + 3)) ≤ 3 * Real.log (Q * T) := by
    have h1 : Real.log (q * (T + 3)) ≤ Real.log (Q * T * (5 / 2)) :=
      Real.log_le_log (by positivity) (by nlinarith)
    have h2 : Real.log (Q * T * (5 / 2)) = Real.log (Q * T) + Real.log (5 / 2) :=
      Real.log_mul (by positivity) (by norm_num)
    have h3 : Real.log (5 / 2) ≤ 1 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have := Real.exp_one_gt_d9; linarith
    linarith
  have hlog0 : 0 ≤ Real.log (q * (T + 3)) := Real.log_nonneg (by nlinarith)
  calc (Ndens χ σ T : ℝ) ≤ K * (T + 1) * Real.log (q * (T + 3)) := h
    _ ≤ K * (3 / 2 * T) * (3 * Real.log (Q * T)) := by
        gcongr
        · linarith
    _ ≤ 5 * K * T * Real.log (Q * T) := by
        have : 0 ≤ K * T * Real.log (Q * T) := by
          have : 0 ≤ Real.log (Q * T) := by linarith
          positivity
        nlinarith

set_option maxHeartbeats 1600000 in
/-- **`Families.Montgomery69_Density` in the q-aspect range `T' ≤ Q^A`** (every `A > 0`), with
`c = 1/(16(2+A))` and `C₁ = 6`. -/
theorem Montgomery69_Density_upTo_proof (A : ℝ) (hA : 0 < A) : Montgomery69_Density_upTo A := by
  obtain ⟨K, hK, hKb⟩ := Ndens_le_trivial
  set c : ℝ := 1 / (16 * (2 + A)) with hc
  have hc0 : 0 < c := by positivity
  have hc1 : c ≤ 1 / 32 := by
    rw [hc, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hcA : (2 + A) * c = 1 / 16 := by rw [hc]; field_simp
  refine ⟨1400000 + 1000 * K, c, 6, hc0, ?_⟩
  intro Q hQ T hT2 hTQ δ hδ0 hδ1
  have hQ0 : 0 < Q := by linarith
  have hT0 : 0 < T := by linarith
  set ℓ := Real.log (Q * T) with hℓdef
  have hℓ : 1 / 2 ≤ ℓ := half_le_log_QT hQ hT2
  have hQT : 0 < Q ^ 2 * T := by positivity
  have hQT1 : 1 ≤ Q ^ 2 * T := by nlinarith
  set L := Real.log (Q ^ 2 * T) with hLdef
  have hL2 : L ≤ 2 * ℓ := by
    rw [hLdef, hℓdef, ← Real.log_rpow (by positivity)]
    refine Real.log_le_log hQT ?_
    rw [Real.rpow_two]; nlinarith
  -- the right side
  have hrpow6 : Real.log (Q * T) ^ (6 : ℝ) = ℓ ^ 6 := by
    rw [hℓdef]; exact Real.rpow_ofNat _ 6
  rw [hrpow6]
  set P := (Q ^ 2 * T) ^ (1 - c * δ) with hPdef
  have hPsplit : P = Q ^ 2 * T * (Q ^ 2 * T) ^ (-(c * δ)) := by
    rw [hPdef, sub_eq_add_neg, Real.rpow_add hQT, Real.rpow_one]
  have hℓ6 : ℓ ≤ 32 * ℓ ^ 6 := by
    have h5 : (1 / 2 : ℝ) ^ 5 ≤ ℓ ^ 5 := pow_le_pow_left₀ (by norm_num) hℓ 5
    nlinarith
  have hQA : Q ^ 2 * T ≤ Q ^ (2 + A) := by
    rw [Real.rpow_add hQ0, Real.rpow_two]
    exact mul_le_mul_of_nonneg_left hTQ (by positivity)
  -- `(Q²T)^{cδ} ≤ Q²`
  have hE2 : (Q ^ 2 * T) ^ (c * δ) ≤ Q ^ 2 := by
    calc (Q ^ 2 * T) ^ (c * δ) ≤ (Q ^ (2 + A)) ^ (c * δ) :=
          Real.rpow_le_rpow hQT.le hQA (by positivity)
      _ = Q ^ ((2 + A) * (c * δ)) := by rw [← Real.rpow_mul hQ0.le]
      _ ≤ Q ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hQ (by
          rw [show (2 + A) * (c * δ) = (2 + A) * c * δ by ring, hcA]; linarith)
      _ = Q ^ 2 := Real.rpow_two Q
  have hTP : T ≤ P := by
    rw [hPsplit, Real.rpow_neg hQT.le, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    calc T * (Q ^ 2 * T) ^ (c * δ) ≤ T * Q ^ 2 := mul_le_mul_of_nonneg_left hE2 hT0.le
      _ = Q ^ 2 * T := by ring
  have hP0 : 0 < P := by rw [hPdef]; positivity
  -- the trivial per-character bound
  have htriv : ∀ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∀ χ ∈ primChars q,
      (Ndens χ (1 / 2 + δ) T : ℝ) ≤ 5 * K * T * ℓ := fun q hq χ hχ =>
    Ndens_le_family_trivial hK hKb hQ hT2 (by linarith) hq hχ
  have hC : 0 ≤ ℓ ^ 6 := by positivity
  by_cases hcase : δ * L ≤ 1
  · -- small δ: the trivial bound
    have hlow : 1 / 3 ≤ (Q ^ 2 * T) ^ (-(c * δ)) := by
      rw [Real.rpow_def_of_pos hQT, ← hLdef]
      have h1 : -1 ≤ L * -(c * δ) := by
        have hL0 : 0 ≤ L := Real.log_nonneg hQT1
        nlinarith
      have h2 : Real.exp (-1) ≤ Real.exp (L * -(c * δ)) := Real.exp_le_exp.mpr h1
      have h3 : 1 / 3 ≤ Real.exp (-1) := by
        rw [Real.exp_neg, one_div, inv_le_inv₀ (by norm_num) (Real.exp_pos 1)]
        have := Real.exp_one_lt_d9; linarith
      linarith
    have hQ2T : Q ^ 2 * T ≤ 3 * P := by rw [hPsplit]; nlinarith
    calc ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ ∈ primChars q, (Ndens χ (1 / 2 + δ) T : ℝ)
        ≤ ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ((primChars q).card : ℝ) * (5 * K * T * ℓ) := by
          refine Finset.sum_le_sum fun q hq => ?_
          rw [← nsmul_eq_mul, ← Finset.sum_const]
          exact Finset.sum_le_sum fun χ hχ => htriv q hq χ hχ
      _ = (∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ((primChars q).card : ℝ)) * (5 * K * T * ℓ) := by
          rw [Finset.sum_mul]
      _ ≤ Q ^ 2 * (5 * K * T * ℓ) :=
          mul_le_mul_of_nonneg_right (sum_card_primChars_le_one hQ) (by
            have : 0 ≤ ℓ := by linarith
            positivity)
      _ = 5 * K * ℓ * (Q ^ 2 * T) := by ring
      _ ≤ 5 * K * (32 * ℓ ^ 6) * (3 * P) := by
          gcongr
      _ ≤ (1400000 + 1000 * K) * P * ℓ ^ 6 := by nlinarith [mul_nonneg hP0.le hC]
  · -- large δ: Jensen for `q ≥ 2`, trivial for `q = 1`
    push Not at hcase
    have hδpos : 0 < δ := by
      rcases hδ0.lt_or_eq with h | h
      · exact h
      · rw [← h] at hcase; simp at hcase; linarith
    have hX : 1 ≤ ⌊Q⌋₊ := Nat.le_floor (by exact_mod_cast hQ)
    rw [sum_Icc_one_eq _ hX]
    -- `q = 1`
    have hone : ∑ χ ∈ primChars 1, (Ndens χ (1 / 2 + δ) T : ℝ) ≤ 5 * K * P * ℓ := by
      calc ∑ χ ∈ primChars 1, (Ndens χ (1 / 2 + δ) T : ℝ)
          ≤ ∑ χ ∈ primChars 1, (5 * K * T * ℓ) :=
            Finset.sum_le_sum fun χ hχ => htriv 1 (by simp [hX]) χ hχ
        _ = ((primChars 1).card : ℝ) * (5 * K * T * ℓ) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 1 * (5 * K * T * ℓ) := by
            refine mul_le_mul_of_nonneg_right ?_ (by
              have : 0 ≤ ℓ := by linarith
              positivity)
            have := card_primChars_le' 1; simpa using this
        _ ≤ 5 * K * P * ℓ := by
            have : 0 ≤ 5 * K * ℓ := by
              have : 0 ≤ ℓ := by linarith
              positivity
            nlinarith
    -- `q ≥ 2`
    have hfam := family_count hQ hT2 hδpos hδ1
    have hW : T + 1 + 2 / δ ≤ 2 * T / δ := by
      rw [le_div_iff₀ hδpos]
      have : 2 / δ * δ = 2 := by field_simp
      nlinarith
    have hB : (1 + 2 / δ) ^ 2 ≤ 7 / δ ^ 2 := by
      have h1 : 1 + 2 / δ ≤ 5 / 2 / δ := by
        rw [div_div, le_div_iff₀ (by positivity)]
        have : 2 / δ * δ = 2 := by field_simp
        nlinarith
      have h2 : (1 + 2 / δ) ^ 2 ≤ (5 / 2 / δ) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h1 2
      calc (1 + 2 / δ) ^ 2 ≤ (5 / 2 / δ) ^ 2 := h2
        _ = 25 / 4 / δ ^ 2 := by ring
        _ ≤ 7 / δ ^ 2 := by gcongr; norm_num
    have hlogQ : 1 + Real.log Q ≤ 3 * ℓ := by
      have : Real.log Q ≤ ℓ := Real.log_le_log hQ0 (le_mul_of_one_le_right hQ0.le (by linarith))
      linarith
    have hQd : Q ^ (-(δ / 8)) ≤ (Q ^ 2 * T) ^ (-(c * δ)) := by
      have e : (2 + A) * -(c * δ) = -(δ / 16) := by
        rw [show (2 + A) * -(c * δ) = -((2 + A) * c * δ) by ring, hcA]; ring
      have hcδ : 0 ≤ c * δ := mul_nonneg hc0.le hδ0
      calc Q ^ (-(δ / 8)) ≤ Q ^ ((2 + A) * -(c * δ)) :=
            Real.rpow_le_rpow_of_exponent_le hQ (by rw [e]; linarith)
        _ = (Q ^ (2 + A)) ^ (-(c * δ)) := by rw [Real.rpow_mul hQ0.le]
        _ ≤ (Q ^ 2 * T) ^ (-(c * δ)) :=
            Real.rpow_le_rpow_of_nonpos hQT hQA (by linarith)
    have hδL : 1 / δ ≤ 2 * ℓ := by
      rw [div_le_iff₀ hδpos]
      have := mul_le_mul_of_nonneg_left hL2 hδpos.le
      linarith
    have hδ5 : (1 / δ) ^ 5 ≤ 32 * ℓ ^ 5 := by
      calc (1 / δ) ^ 5 ≤ (2 * ℓ) ^ 5 := pow_le_pow_left₀ (by positivity) hδL 5
        _ = 32 * ℓ ^ 5 := by ring
    have hPhi : 15 / δ ^ 2 * Phi Q (T + 1 + 2 / δ) δ ≤ 1400000 * P * ℓ ^ 6 := by
      unfold Phi
      have hu : 0 ≤ Q ^ (-(δ / 8)) := by positivity
      have hlog0 : 0 ≤ 1 + Real.log Q := by linarith [Real.log_nonneg hQ]
      have hWpos : 0 ≤ T + 1 + 2 / δ := by positivity
      calc 15 / δ ^ 2 * (68 * ((1 + 2 / δ) ^ 2 * (1 + Real.log Q)) * (Q ^ 2 * (T + 1 + 2 / δ)) *
            Q ^ (-(δ / 8)))
          ≤ 15 / δ ^ 2 * (68 * (7 / δ ^ 2 * (3 * ℓ)) * (Q ^ 2 * (2 * T / δ)) *
              (Q ^ 2 * T) ^ (-(c * δ))) := by
            gcongr
        _ = 42840 * (1 / δ) ^ 5 * ℓ * (Q ^ 2 * T * (Q ^ 2 * T) ^ (-(c * δ))) := by
            field_simp
            norm_num
        _ ≤ 42840 * (32 * ℓ ^ 5) * ℓ * (Q ^ 2 * T * (Q ^ 2 * T) ^ (-(c * δ))) := by
            gcongr
        _ = 1370880 * (Q ^ 2 * T * (Q ^ 2 * T) ^ (-(c * δ))) * ℓ ^ 6 := by ring
        _ ≤ 1400000 * P * ℓ ^ 6 := by
            rw [← hPsplit, mul_assoc, mul_assoc]
            have h := mul_nonneg hP0.le hC
            linarith
    have hPl : 5 * K * P * ℓ ≤ 160 * K * P * ℓ ^ 6 := by
      have h0 : 0 ≤ 5 * K * P := by positivity
      calc 5 * K * P * ℓ ≤ (5 * K * P) * (32 * ℓ ^ 6) := mul_le_mul_of_nonneg_left hℓ6 h0
        _ = 160 * K * P * ℓ ^ 6 := by ring
    have h := mul_nonneg hP0.le hC
    calc ∑ χ ∈ primChars 1, (Ndens χ (1 / 2 + δ) T : ℝ) +
          ∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, ∑ χ ∈ primChars q, (Ndens χ (1 / 2 + δ) T : ℝ)
        ≤ 5 * K * P * ℓ + 15 / δ ^ 2 * Phi Q (T + 1 + 2 / δ) δ := add_le_add hone hfam
      _ ≤ 160 * K * P * ℓ ^ 6 + 1400000 * P * ℓ ^ 6 := add_le_add hPl hPhi
      _ = (160 * K + 1400000) * (P * ℓ ^ 6) := by ring
      _ ≤ (1400000 + 1000 * K) * (P * ℓ ^ 6) := mul_le_mul_of_nonneg_right (by linarith) h
      _ = (1400000 + 1000 * K) * P * ℓ ^ 6 := by ring

end Families.Hyp.Montgomery
