/-
# Prime side (paper §5): asymptotic helpers and the archimedean term `lem:mumu`

`Mmumu_bound`: `M_{μμ} ≤ H|J| b L ℓ²/2π + o(H T L² ℓ)` (upper half of `lem:mumu`, Lemma 5.1).
-/
import Families.Ported.Second.Expand

noncomputable section

open scoped BigOperators ContDiff
open Finset MeasureTheory Filter Topology

namespace Families.Ported.Second

open Families

/-! ### Asymptotic helpers (`Q → ∞`) -/

section Asymp

/-- `K (log ℓ + 1) ≤ ε ℓ` for all large `Q` (`ℓ = log Q`). -/
lemma eventually_loglog_le (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Q in atTop, K * (Real.log (Real.log Q) + 1) ≤ ε * Real.log Q := by
  have hK : 0 ≤ |K| := abs_nonneg K
  have h1 : ∀ᶠ y : ℝ in atTop, |Real.log y| ≤ ε / (2 * (|K| + 1)) * |y| :=
    (Real.isLittleO_log_id_atTop.bound (by positivity))
  have h2 : ∀ᶠ y : ℝ in atTop, 2 * (|K| + 1) / ε ≤ y := eventually_ge_atTop _
  have h3 : ∀ᶠ y : ℝ in atTop, (1 : ℝ) ≤ y := eventually_ge_atTop _
  have h := (h1.and (h2.and h3))
  filter_upwards [Real.tendsto_log_atTop.eventually h] with Q hQ
  obtain ⟨ha, hb, hc⟩ := hQ
  set y := Real.log Q
  have hy0 : 0 ≤ y := by linarith
  rw [abs_of_nonneg hy0] at ha
  have hl : Real.log y ≤ ε / (2 * (|K| + 1)) * y := (le_abs_self _).trans ha
  have hKK : K ≤ |K| := le_abs_self K
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hc
  have e1 : |K| * Real.log y ≤ ε / 2 * y := by
    have : |K| * Real.log y ≤ (|K| + 1) * (ε / (2 * (|K| + 1)) * y) :=
      mul_le_mul (by linarith) hl hlogy (by positivity)
    have e : (|K| + 1) * (ε / (2 * (|K| + 1)) * y) = ε / 2 * y := by field_simp
    linarith
  have e2 : |K| ≤ ε / 2 * y := by
    have := (div_le_iff₀ hε).mp hb
    nlinarith
  calc K * (Real.log y + 1) ≤ |K| * (Real.log y + 1) :=
        mul_le_mul_of_nonneg_right hKK (by linarith)
    _ = |K| * Real.log y + |K| := by ring
    _ ≤ ε / 2 * y + ε / 2 * y := add_le_add e1 e2
    _ = ε * y := by ring

/-- `K ≤ ε ℓ` for all large `Q`. -/
lemma eventually_const_le_ell (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Q in atTop, K ≤ ε * Real.log Q := by
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (K / ε))] with Q hQ
  rw [div_le_iff₀ hε] at hQ; linarith

lemma heights_facts (P : PrimeSetup) {Q T : ℝ} (hQ : Real.exp 1 ≤ Q) (hT : T ∈ P.heights Q) :
    1 ≤ T ∧ Real.log T ≤ P.A0 * Real.log (Real.log Q) := by
  have hT1 := Families.Phase3.C.one_le_T P hQ hT
  have hℓ : 1 ≤ Real.log Q := by
    have := Real.log_le_log (Real.exp_pos _) hQ; rwa [Real.log_exp] at this
  refine ⟨hT1, ?_⟩
  have h2 := hT.2
  have := Real.log_le_log (by linarith) h2
  rwa [Real.log_rpow (by linarith)] at this

end Asymp

/-! ### `lem:mumu` -/

/-- **`lem:mumu`, upper half.** For every `δ > 0` and large `Q`, uniformly in `T`:
`M_{μμ} ≤ H |J| b L ℓ²/(2π) + δ H T L² ℓ`. -/
theorem Mmumu_bound (hStir : StirlingDigamma) (hWH : lemWH_Statement) (P : PrimeSetup)
    (W : Weight) (δ : ℝ) (hδ : 0 < δ) : ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ P.heights Q,
      Mmumu P W Q T ≤ W.H Q * P.Jlen T * P.bInt * P.L Q * ell Q ^ 2 / (2 * Real.pi) +
        δ * (W.H Q * T * P.L Q ^ 2 * ell Q) := by
  obtain ⟨R₀, hR₀, hnear⟩ := muChi_near_J hStir
  obtain ⟨CJ, hCJ, hJ2⟩ := J2_PhiSq_le P
  have hpi := Real.pi_pos
  have hb : 0 ≤ P.bInt := integral_nonneg fun s => sq_nonneg _
  have hl := P.lam_pos
  -- the constants
  set x0 : ℝ := 2 * Real.pi * R₀ with hx0
  -- eventualities
  have e1 := eventually_loglog_le (3 * P.bInt / (2 * Real.pi) * (P.A0 + x0 + 1))
    (ε := δ / 2 * P.lam) (by positivity)
  have e2 := eventually_loglog_le (P.A0 + x0) (ε := 1) one_pos
  have e3 := eventually_const_le_ell (CJ + 1) (ε := δ / 2 * P.lam ^ 2) (by positivity)
  have e4 := eventually_const_le_ell (Real.log Real.pi) (ε := 1) one_pos
  have e5 : ∀ᶠ Q : ℝ in atTop, Real.exp 1 ≤ Q := eventually_ge_atTop _
  have e6 : ∀ᶠ Q : ℝ in atTop, Real.exp (1 / P.lam) ≤ Q := eventually_ge_atTop _
  obtain ⟨Q₀, hQ₀⟩ := Filter.eventually_atTop.mp (e1.and (e2.and (e3.and (e4.and (e5.and e6)))))
  refine ⟨Q₀, fun Q hQ T hT => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hQ₀ Q hQ
  have hQ1 : 1 < Q := lt_of_lt_of_le (by have := Real.add_one_le_exp (1 : ℝ); linarith) h5
  obtain ⟨hT1, hlogT⟩ := heights_facts P h5 hT
  set ℓ := Real.log Q with hℓdef
  have hℓ1 : 1 ≤ ℓ := by
    have := Real.log_le_log (Real.exp_pos _) h5; rwa [Real.log_exp] at this
  have hL1 : 1 ≤ P.L Q := Families.Phase3.C.one_le_L P h6
  have hLdef : P.L Q = P.lam * ℓ := rfl
  have hH0 : 0 ≤ W.H Q := Families.Weight.H_nonneg W Q
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hloglog : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ1
  -- `x = log T + 2πR₀ ≤ (A₀ + x₀)(log ℓ + 1)`
  set x : ℝ := Real.log T + x0 with hxdef
  have hA0 : 0 ≤ P.A0 := le_trans P.a0_pos.le P.a0_lt.le
  have hx0' : 0 ≤ x0 := by positivity
  have hx : x ≤ (P.A0 + x0) * (Real.log ℓ + 1) := by
    have : Real.log T ≤ P.A0 * Real.log ℓ := hlogT
    have e : (P.A0 + x0) * (Real.log ℓ + 1) = P.A0 * Real.log ℓ + P.A0 + x0 * Real.log ℓ + x0 := by
      ring
    rw [e, hxdef]
    linarith [mul_nonneg hx0' hloglog]
  have hx0l : 0 ≤ x := by positivity
  have hxℓ : x ≤ ℓ := hx.trans (by linarith)
  -- `U = (ℓ + x)/2π` bounds `|μ_χ|` on `J`
  set U : ℝ := (ℓ + x) / (2 * Real.pi) with hU
  have hU0 : 0 ≤ U := by positivity
  have hμU : ∀ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∀ χ : DirichletCharacter ℂ q, ∀ t ∈ P.J T,
      |muChi χ t| ≤ U := by
    intro q hq χ t ht
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hqQ : (q : ℝ) ≤ Q := by
      have := (Finset.mem_Icc.mp hq).2
      exact (Nat.le_floor_iff (by linarith)).mp this
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
    have hlogq : |Real.log (q / Real.pi)| ≤ ℓ := by
      rw [Real.log_div hq0.ne' hpi.ne', abs_le]
      have hlq := Real.log_le_log hq0 hqQ
      have hlq0 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq1)
      have hlpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
      constructor <;> linarith
    have h := hnear P T hT1 q χ t ht
    have hβ : |1 / (2 * Real.pi) * (Real.log (q / Real.pi) + Real.log T)| ≤
        (ℓ + Real.log T) / (2 * Real.pi) := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
      rw [one_div_mul_eq_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      calc |Real.log (q / Real.pi) + Real.log T| ≤ |Real.log (q / Real.pi)| + |Real.log T| :=
            abs_add_le _ _
        _ ≤ ℓ + Real.log T := by rw [abs_of_nonneg hlogT0]; linarith
    have := abs_sub_abs_le_abs_sub (muChi χ t)
      (1 / (2 * Real.pi) * (Real.log (q / Real.pi) + Real.log T))
    have e : (ℓ + Real.log T) / (2 * Real.pi) + R₀ = U := by
      rw [hU, hxdef, hx0]; field_simp; ring
    linarith
  -- pointwise: `K₂(μ, μ) ≤ U² ∬ Φ²`
  have hK2 : ∀ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∀ χ : DirichletCharacter ℂ q,
      ∫ t in P.J T, ∫ t' in P.J T, PhiSq P Q (t - t') * muChi χ t * muChi χ t' ≤
        U ^ 2 * ∫ t in P.J T, ∫ t' in P.J T, PhiSq P Q (t - t') := by
    intro q hq χ
    have hμc := muChi_continuous χ
    have hcont := K2_cont (P := P) hQ1 hμc hμc
    have hcont1 : Continuous (Function.uncurry fun t t' : ℝ => U ^ 2 * PhiSq P Q (t - t')) :=
      continuous_const.mul ((PhiSq_continuous P hQ1).comp (continuous_fst.sub continuous_snd))
    rw [← integral_const_mul]
    have hin : ∀ t, U ^ 2 * ∫ t' in P.J T, PhiSq P Q (t - t') =
        ∫ t' in P.J T, U ^ 2 * PhiSq P Q (t - t') := fun t => (integral_const_mul _ _).symm
    simp_rw [hin]
    refine setIntegral_mono_on (intOn_Icc_outer hcont _ _) (intOn_Icc_outer hcont1 _ _)
      measurableSet_Icc fun t ht => ?_
    refine setIntegral_mono_on (intOn_Icc_inner hcont _ _ t) (intOn_Icc_inner hcont1 _ _ t)
      measurableSet_Icc fun t' ht' => ?_
    have hK0 := PhiSq_nonneg P Q (t - t')
    have ha := hμU q hq χ t ht
    have hb := hμU q hq χ t' ht'
    have hprod : muChi χ t * muChi χ t' ≤ U ^ 2 := by
      have := abs_mul (muChi χ t) (muChi χ t')
      have h' : |muChi χ t * muChi χ t'| ≤ U * U :=
        this ▸ mul_le_mul ha hb (abs_nonneg _) hU0
      nlinarith [le_abs_self (muChi χ t * muChi χ t')]
    calc PhiSq P Q (t - t') * muChi χ t * muChi χ t'
        = PhiSq P Q (t - t') * (muChi χ t * muChi χ t') := by ring
      _ ≤ PhiSq P Q (t - t') * U ^ 2 := mul_le_mul_of_nonneg_left hprod hK0
      _ = U ^ 2 * PhiSq P Q (t - t') := by ring
  -- family sum
  set J2 := ∫ t in P.J T, ∫ t' in P.J T, PhiSq P Q (t - t') with hJ2def
  have hfam : Mmumu P W Q T ≤ W.H Q * (U ^ 2 * J2) := by
    unfold Mmumu famSum Weight.H
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun q hq => ?_
    have hω := Families.Weight.omega_nonneg W Q q
    calc W.omega Q q * ∑ χ ∈ primChars q,
          ∫ t in P.J T, ∫ t' in P.J T, PhiSq P Q (t - t') * muChi χ t * muChi χ t'
        ≤ W.omega Q q * ∑ χ ∈ primChars q, U ^ 2 * J2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun χ _ => hK2 q hq χ) hω
      _ = W.omega Q q * phiStar q * (U ^ 2 * J2) := by
          rw [Finset.sum_const, nsmul_eq_mul]; unfold phiStar; ring
  have hTpos : 0 < T := by linarith
  have hJ2 : J2 ≤ 2 * Real.pi * P.Jlen T * P.bInt * P.L Q + CJ := hJ2 Q T hQ1 hTpos
  have hJlen : P.Jlen T ≤ T := by
    unfold PrimeSetup.Jlen
    have : 0 ≤ 2 * P.θ * T := by have := P.θ_pos; positivity
    linarith
  have hJlen0 : 0 ≤ P.Jlen T := by
    unfold PrimeSetup.Jlen
    exact mul_nonneg (by linarith [P.θ_lt]) (by linarith)
  -- final estimate
  refine hfam.trans ?_
  have hUJ : U ^ 2 * J2 ≤ U ^ 2 * (2 * Real.pi * P.Jlen T * P.bInt * P.L Q + CJ) :=
    mul_le_mul_of_nonneg_left hJ2 (sq_nonneg _)
  have hmain : U ^ 2 * (2 * Real.pi * P.Jlen T * P.bInt * P.L Q) =
      P.Jlen T * P.bInt * P.L Q * (ℓ + x) ^ 2 / (2 * Real.pi) := by
    rw [hU]; field_simp
  -- `(ℓ + x)² ≤ ℓ² + 3ℓx`
  have hsq : (ℓ + x) ^ 2 ≤ ℓ ^ 2 + 3 * ℓ * x := by
    have e : (ℓ + x) ^ 2 = ℓ ^ 2 + 3 * ℓ * x - x * (ℓ - x) := by ring
    rw [e]; linarith [mul_nonneg hx0l (sub_nonneg.mpr hxℓ)]
  -- `3 b x/(2π) ≤ (δ/2) L`
  have hx3 : 3 * P.bInt / (2 * Real.pi) * x ≤ δ / 2 * P.L Q := by
    have h1' : 3 * P.bInt / (2 * Real.pi) * (P.A0 + x0 + 1) * (Real.log ℓ + 1) ≤
        δ / 2 * P.lam * ℓ := h1
    have hxx : x ≤ (P.A0 + x0 + 1) * (Real.log ℓ + 1) :=
      hx.trans (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
    have hc0 : 0 ≤ 3 * P.bInt / (2 * Real.pi) := by positivity
    calc 3 * P.bInt / (2 * Real.pi) * x ≤ 3 * P.bInt / (2 * Real.pi) *
          ((P.A0 + x0 + 1) * (Real.log ℓ + 1)) := mul_le_mul_of_nonneg_left hxx hc0
      _ ≤ δ / 2 * P.lam * ℓ := by linarith
      _ = δ / 2 * P.L Q := by rw [hLdef]; ring
  have hU1 : U ≤ ℓ := by
    rw [hU, div_le_iff₀ (by positivity)]
    have : 0 ≤ 2 * ℓ * (Real.pi - 1) := mul_nonneg (by linarith) (by linarith [Real.pi_gt_three])
    linarith
  have hCJ' : U ^ 2 * CJ ≤ δ / 2 * (T * P.L Q ^ 2 * ℓ) := by
    have h3' : CJ + 1 ≤ δ / 2 * P.lam ^ 2 * ℓ := h3
    have hU2 : U ^ 2 ≤ ℓ ^ 2 := pow_le_pow_left₀ hU0 hU1 2
    have e : δ / 2 * (T * P.L Q ^ 2 * ℓ) = δ / 2 * P.lam ^ 2 * ℓ * (T * ℓ ^ 2) := by
      rw [hLdef]; ring
    rw [e]
    calc U ^ 2 * CJ ≤ ℓ ^ 2 * CJ := mul_le_mul_of_nonneg_right hU2 hCJ
      _ ≤ ℓ ^ 2 * (δ / 2 * P.lam ^ 2 * ℓ) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _); linarith
      _ ≤ δ / 2 * P.lam ^ 2 * ℓ * (T * ℓ ^ 2) := by
          have h0 : 0 ≤ δ / 2 * P.lam ^ 2 * ℓ * ℓ ^ 2 := by positivity
          have := mul_le_mul_of_nonneg_left hT1 h0
          linarith
  have hmain2 : P.Jlen T * P.bInt * P.L Q * (ℓ + x) ^ 2 / (2 * Real.pi) ≤
      P.Jlen T * P.bInt * P.L Q * ℓ ^ 2 / (2 * Real.pi) + δ / 2 * (T * P.L Q ^ 2 * ℓ) := by
    have hJbL : 0 ≤ P.Jlen T * P.bInt * P.L Q := by positivity
    have step1 : P.Jlen T * P.bInt * P.L Q * (ℓ + x) ^ 2 / (2 * Real.pi) ≤
        P.Jlen T * P.bInt * P.L Q * (ℓ ^ 2 + 3 * ℓ * x) / (2 * Real.pi) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hsq hJbL
    have step2 : P.Jlen T * P.bInt * P.L Q * (3 * ℓ * x) / (2 * Real.pi) ≤
        δ / 2 * (T * P.L Q ^ 2 * ℓ) := by
      have e : P.Jlen T * P.bInt * P.L Q * (3 * ℓ * x) / (2 * Real.pi) =
          P.Jlen T * P.L Q * ℓ * (3 * P.bInt / (2 * Real.pi) * x) := by ring
      rw [e]
      have hJLl : 0 ≤ P.Jlen T * P.L Q * ℓ := by positivity
      calc P.Jlen T * P.L Q * ℓ * (3 * P.bInt / (2 * Real.pi) * x)
          ≤ P.Jlen T * P.L Q * ℓ * (δ / 2 * P.L Q) := mul_le_mul_of_nonneg_left hx3 hJLl
        _ ≤ T * P.L Q * ℓ * (δ / 2 * P.L Q) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_right hJlen (by positivity)
        _ = δ / 2 * (T * P.L Q ^ 2 * ℓ) := by ring
    have e : P.Jlen T * P.bInt * P.L Q * (ℓ ^ 2 + 3 * ℓ * x) / (2 * Real.pi) =
        P.Jlen T * P.bInt * P.L Q * ℓ ^ 2 / (2 * Real.pi) +
          P.Jlen T * P.bInt * P.L Q * (3 * ℓ * x) / (2 * Real.pi) := by ring
    linarith
  calc W.H Q * (U ^ 2 * J2) ≤ W.H Q * (U ^ 2 * (2 * Real.pi * P.Jlen T * P.bInt * P.L Q + CJ)) :=
        mul_le_mul_of_nonneg_left hUJ hH0
    _ = W.H Q * (U ^ 2 * (2 * Real.pi * P.Jlen T * P.bInt * P.L Q)) + W.H Q * (U ^ 2 * CJ) := by
        ring
    _ ≤ W.H Q * (P.Jlen T * P.bInt * P.L Q * ℓ ^ 2 / (2 * Real.pi) +
          δ / 2 * (T * P.L Q ^ 2 * ℓ)) + W.H Q * (δ / 2 * (T * P.L Q ^ 2 * ℓ)) := by
        rw [hmain]
        exact add_le_add (mul_le_mul_of_nonneg_left hmain2 hH0)
          (mul_le_mul_of_nonneg_left hCJ' hH0)
    _ = W.H Q * P.Jlen T * P.bInt * P.L Q * ell Q ^ 2 / (2 * Real.pi) +
          δ * (W.H Q * T * P.L Q ^ 2 * ell Q) := by
        simp only [ell, hℓdef]; ring

end Families.Ported.Second
