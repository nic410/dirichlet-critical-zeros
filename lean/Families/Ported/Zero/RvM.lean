/-
# Zero side: weighted Riemann–von Mangoldt (`lem:RvM`, paper §4.1)

* `rvm_chi`: the q-uniform count `|N_χ − (T/2π) ℓ_{1,χ}| ≤ A log(q(T+2))` for every primitive `χ`
  mod `q > 1` and `T ≥ T₀` (`zeta23` `Zeta23.ThmE.mainChi_uniform_aux`, absolute constants).
* `rvm_family`: `(1−δ) H T ℓ/2π ≤ N ≤ (1+δ) H T ℓ/2π` uniformly for `ℓ^{a₀} ≤ T ≤ ℓ^{A₀}`.
* `lemRvM_lower`: `lemRvM_lower_Statement`.

The paper's proof symmetrises over `χ ↦ χ̄`; `zeta23`'s count is one-sided (`T < γ ≤ 2T`) directly,
so no symmetrisation is needed.
-/
import Families.Ported.Zero.Bridge
import Families.Classical.Reductions

noncomputable section

open scoped BigOperators ComplexConjugate
open Complex Set Filter Topology

namespace Families.Ported.Zero

open Zeta23 Zeta23.ThmE

/-- **q-uniform Riemann–von Mangoldt** (`zeta23`, absolute constants). -/
theorem rvm_chi : ∃ A T₀ : ℝ, 0 < A ∧ 2 ≤ T₀ ∧ ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), 1 < q →
    χ.IsPrimitive → ∀ T : ℝ, T₀ ≤ T →
      |(Nchi χ T : ℝ) - T / (2 * Real.pi) * ell1q q T| ≤ A * Real.log (q * (T + 2)) := by
  obtain ⟨A, T₀, hA, h⟩ :=
    mainChi_uniform_aux backlund_horizontalChi_uniform GammaChi.gammaFactsChi_uniform
  refine ⟨A, max T₀ 2, hA, le_max_right _ _, fun q χ hq hprim T hT => ?_⟩
  have : NeZero q := ⟨by omega⟩
  have hT2 : (2 : ℝ) ≤ T := (le_max_right _ _).trans hT
  rw [Nchi_eq hq hprim (by linarith)]
  exact h q χ hq hprim T ((le_max_left _ _).trans hT)

/-- Real-arithmetic core of the family count: if `log q ∈ [ℓ + log η, ℓ]`, `1 ≤ ℓ`, `2 ≤ T`,
`log T ≤ A₀ log ℓ` and the error budget is small, the per-character count is within
`δ T ℓ/2π` of `T ℓ/2π`. -/
lemma rvm_chi_bounds {A η A0 δ ℓ T Nχ : ℝ} {q : ℕ} (hA : 0 < A) (hη : 0 < η) (hη1 : η ≤ 1)
    (hℓ : 1 ≤ ℓ) (hT : 2 ≤ T) (hq : (0 : ℝ) < q) (hq1 : Real.log q ≤ ℓ)
    (hq2 : ℓ + Real.log η ≤ Real.log q) (hTlog0 : 0 ≤ Real.log T)
    (hTlog : Real.log T ≤ A0 * Real.log ℓ)
    (hbudget : T * (-Real.log η + Real.log (2 * Real.pi) + 1 + A0 * Real.log ℓ)
        + 2 * Real.pi * A * (ℓ + T + 1) ≤ δ * T * ℓ)
    (hN : |Nχ - T / (2 * Real.pi) * ell1q q T| ≤ A * Real.log (q * (T + 2))) :
    (1 - δ) * (T * ℓ / (2 * Real.pi)) ≤ Nχ ∧ Nχ ≤ (1 + δ) * (T * ℓ / (2 * Real.pi)) := by
  have hπ : 0 < 2 * Real.pi := by positivity
  have hT0 : 0 < T := by linarith
  have hell : ell1q q T = Real.log q + Real.log T - Real.log (2 * Real.pi) + 2 * Real.log 2 - 1 := by
    unfold ell1q
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul hq.ne' hT0.ne']
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2' : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9; linarith
  have hlogπ : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have hlogπ' : 2 * Real.log 2 - 1 ≤ Real.log (2 * Real.pi) := by
    have : Real.log 2 ≤ Real.log (2 * Real.pi) :=
      Real.log_le_log (by norm_num) (by nlinarith [Real.pi_gt_three])
    linarith
  have hlogη : Real.log η ≤ 0 := Real.log_nonpos hη.le hη1
  have hlogℓ : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ
  -- error term
  have herr : A * Real.log (q * (T + 2)) ≤ A * (ℓ + T + 1) := by
    apply mul_le_mul_of_nonneg_left _ hA.le
    rw [Real.log_mul hq.ne' (by linarith)]
    have : Real.log (T + 2) ≤ T + 2 - 1 := Real.log_le_sub_one_of_pos (by linarith)
    linarith
  obtain ⟨hl, hr⟩ := abs_le.mp hN
  -- the main term vs Tℓ/2π
  have hmain_lo : T / (2 * Real.pi) * ell1q q T ≥
      T * ℓ / (2 * Real.pi) - T * (-Real.log η + Real.log (2 * Real.pi) + 1) / (2 * Real.pi) := by
    rw [hell, ge_iff_le, ← sub_nonneg]
    have : 0 ≤ T / (2 * Real.pi) * (Real.log q + Real.log T - Real.log (2 * Real.pi) + 2 * Real.log 2 - 1)
        - (T * ℓ / (2 * Real.pi) - T * (-Real.log η + Real.log (2 * Real.pi) + 1) / (2 * Real.pi)) := by
      have e : T / (2 * Real.pi) * (Real.log q + Real.log T - Real.log (2 * Real.pi) + 2 * Real.log 2 - 1)
          - (T * ℓ / (2 * Real.pi) - T * (-Real.log η + Real.log (2 * Real.pi) + 1) / (2 * Real.pi)) =
          T / (2 * Real.pi) * ((Real.log q - ℓ - Real.log η) + Real.log T + 2 * Real.log 2) := by
        field_simp; ring
      rw [e]
      apply mul_nonneg (by positivity)
      linarith
    linarith
  have hmain_hi : T / (2 * Real.pi) * ell1q q T ≤
      T * ℓ / (2 * Real.pi) + T * (A0 * Real.log ℓ) / (2 * Real.pi) := by
    rw [hell]
    have e : T * ℓ / (2 * Real.pi) + T * (A0 * Real.log ℓ) / (2 * Real.pi) -
        T / (2 * Real.pi) * (Real.log q + Real.log T - Real.log (2 * Real.pi) + 2 * Real.log 2 - 1) =
        T / (2 * Real.pi) * ((ℓ - Real.log q) + (A0 * Real.log ℓ - Real.log T) +
          (Real.log (2 * Real.pi) - (2 * Real.log 2 - 1))) := by
      field_simp; ring
    have : 0 ≤ T / (2 * Real.pi) * ((ℓ - Real.log q) + (A0 * Real.log ℓ - Real.log T) +
          (Real.log (2 * Real.pi) - (2 * Real.log 2 - 1))) := by
      apply mul_nonneg (by positivity); linarith
    linarith
  have hbud' : T * (-Real.log η + Real.log (2 * Real.pi) + 1) / (2 * Real.pi) + A * (ℓ + T + 1)
      ≤ δ * (T * ℓ / (2 * Real.pi)) := by
    have hA0 : 0 ≤ T * (A0 * Real.log ℓ) := by
      have : 0 ≤ A0 * Real.log ℓ := hTlog0.trans hTlog
      positivity
    rw [div_add' _ _ _ hπ.ne', div_le_iff₀ hπ]
    have : δ * (T * ℓ / (2 * Real.pi)) * (2 * Real.pi) = δ * T * ℓ := by field_simp
    rw [this]; nlinarith
  have hbud'' : T * (A0 * Real.log ℓ) / (2 * Real.pi) + A * (ℓ + T + 1)
      ≤ δ * (T * ℓ / (2 * Real.pi)) := by
    have hc : 0 ≤ T * (-Real.log η + Real.log (2 * Real.pi) + 1) := by
      apply mul_nonneg hT0.le; linarith
    rw [div_add' _ _ _ hπ.ne', div_le_iff₀ hπ]
    have : δ * (T * ℓ / (2 * Real.pi)) * (2 * Real.pi) = δ * T * ℓ := by field_simp
    rw [this]; nlinarith
  constructor
  · nlinarith
  · nlinarith

/-! ### Eventual smallness in `ℓ = log Q` -/

lemma ev_log_ge (M : ℝ) : ∀ᶠ Q : ℝ in atTop, M ≤ Real.log Q :=
  Real.tendsto_log_atTop.eventually_ge_atTop M

lemma ev_const_div_log_le (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Q : ℝ in atTop, c / Real.log Q ≤ ε := by
  have : Tendsto (fun Q => c / Real.log Q) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  filter_upwards [this.eventually_lt_const hε] with Q hQ using hQ.le

lemma ev_loglog_div_log_le (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Q : ℝ in atTop, c * Real.log (Real.log Q) / Real.log Q ≤ ε := by
  have h1 := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp Real.tendsto_log_atTop
  have h2 : Tendsto (fun Q : ℝ => c * Real.log (Real.log Q) / Real.log Q) atTop (𝓝 0) := by
    have := h1.const_mul c
    simp only [mul_zero] at this
    refine this.congr fun Q => ?_
    simp [Function.comp, mul_div_assoc]
  filter_upwards [h2.eventually_lt_const hε] with Q hQ using hQ.le

lemma ev_const_div_log_rpow_le (c : ℝ) {a0 : ℝ} (ha0 : 0 < a0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Q : ℝ in atTop, c / Real.log Q ^ a0 ≤ ε := by
  have : Tendsto (fun Q => c / Real.log Q ^ a0) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_rpow_atTop ha0).comp Real.tendsto_log_atTop)
  filter_upwards [this.eventually_lt_const hε] with Q hQ using hQ.le

lemma ev_log_rpow_ge (M : ℝ) {a0 : ℝ} (ha0 : 0 < a0) :
    ∀ᶠ Q : ℝ in atTop, M ≤ Real.log Q ^ a0 :=
  ((tendsto_rpow_atTop ha0).comp Real.tendsto_log_atTop).eventually_ge_atTop M

/-! ### The family count -/

/-- **`lem:RvM`** (both halves): `(1−δ) H T ℓ/2π ≤ N ≤ (1+δ) H T ℓ/2π`, uniformly for
`ℓ^{a₀} ≤ T ≤ ℓ^{A₀}`. -/
theorem rvm_family (W : Weight) {a0 A0 : ℝ} (ha0 : 0 < a0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ Set.Icc (Real.log Q ^ a0) (Real.log Q ^ A0),
      (1 - δ) * (W.H Q * T * Real.log Q / (2 * Real.pi)) ≤ Nfam W Q T ∧
      Nfam W Q T ≤ (1 + δ) * (W.H Q * T * Real.log Q / (2 * Real.pi)) := by
  obtain ⟨A, T₀, hA, hT₀, hrvm⟩ := rvm_chi
  set c : ℝ := -Real.log W.η + Real.log (2 * Real.pi) + 1 with hc
  have hε : 0 < δ / 4 := by positivity
  have hev := (ev_log_ge 1).and ((ev_const_div_log_le c hε).and
    ((ev_loglog_div_log_le |A0| hε).and ((ev_const_div_log_rpow_le (2 * Real.pi * A) ha0 hε).and
    ((ev_const_div_log_le (2 * Real.pi * A * 2) hε).and (ev_log_rpow_ge T₀ ha0)))))
  obtain ⟨Q₁, hQ₁⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max Q₁ (2 / W.η + 1), fun Q hQ T hT => ?_⟩
  obtain ⟨hℓ1, hc', hA0', hAT, hAℓ, hT0'⟩ := hQ₁ Q ((le_max_left _ _).trans hQ)
  have hη := W.η_pos
  have hQη : 2 ≤ W.η * Q := by
    have h1 : 2 / W.η + 1 ≤ Q := (le_max_right _ _).trans hQ
    have : 2 / W.η ≤ Q := by linarith
    rw [div_le_iff₀ hη] at this; linarith
  have hQ0 : 0 < Q := by nlinarith
  set ℓ := Real.log Q with hℓ
  have hT1 : Real.log Q ^ a0 ≤ T := hT.1
  have hTT₀ : T₀ ≤ T := hT0'.trans hT1
  have hT2 : 2 ≤ T := hT₀.trans hTT₀
  have hTpos : 0 < T := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  -- log T ≤ A0 log ℓ
  have hTlog : Real.log T ≤ A0 * Real.log ℓ := by
    have := Real.log_le_log hTpos hT.2
    rwa [Real.log_rpow hℓ0] at this
  have hTlog0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  -- the budget
  have hbudget : T * (-Real.log W.η + Real.log (2 * Real.pi) + 1 + A0 * Real.log ℓ)
      + 2 * Real.pi * A * (ℓ + T + 1) ≤ δ * T * ℓ := by
    have hlogℓ : 0 ≤ Real.log ℓ := Real.log_nonneg hℓ1
    have e1 : c ≤ δ / 4 * ℓ := by rwa [div_le_iff₀ hℓ0] at hc'
    have e2 : A0 * Real.log ℓ ≤ δ / 4 * ℓ := by
      have := hA0'
      rw [div_le_iff₀ hℓ0] at this
      have : A0 * Real.log ℓ ≤ |A0| * Real.log ℓ :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hlogℓ
      linarith
    have e3 : 2 * Real.pi * A ≤ δ / 4 * T := by
      have hr : 0 < Real.log Q ^ a0 := Real.rpow_pos_of_pos hℓ0 _
      have := hAT
      rw [div_le_iff₀ hr] at this
      nlinarith
    have e4 : 2 * Real.pi * A * 2 ≤ δ / 4 * ℓ := by rwa [div_le_iff₀ hℓ0] at hAℓ
    have hπA : 0 < 2 * Real.pi * A := by positivity
    -- 2πA(ℓ+T+1) ≤ 2πA·ℓ + 2πA·T + 2πA ≤ (δ/4)Tℓ + (δ/4)Tℓ·… (using T ≥ 2, ℓ ≥ 1)
    have f1 : 2 * Real.pi * A * ℓ ≤ δ / 4 * T * ℓ := by nlinarith
    have f2 : 2 * Real.pi * A * (T + 1) ≤ δ / 4 * T * ℓ := by nlinarith
    have hcT : T * c ≤ δ / 4 * T * ℓ := by nlinarith
    have hAT' : T * (A0 * Real.log ℓ) ≤ δ / 4 * T * ℓ := by nlinarith
    nlinarith
  -- termwise bounds
  have key : ∀ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∀ χ ∈ primChars q,
      W.omega Q q * ((1 - δ) * (T * ℓ / (2 * Real.pi))) ≤ W.omega Q q * (Nchi χ T : ℝ) ∧
      W.omega Q q * (Nchi χ T : ℝ) ≤ W.omega Q q * ((1 + δ) * (T * ℓ / (2 * Real.pi))) := by
    intro q hq χ hχ
    by_cases hw : W.w (q / Q) = 0
    · simp [Weight.omega, hw]
    have hq1 : 1 < q := one_lt_of_w_ne W hQη hw
    have hqQ : (q : ℝ) ≤ Q := by
      have := (Finset.mem_Icc.mp hq).2
      exact (Nat.cast_le.mpr this).trans (Nat.floor_le hQ0.le)
    have hqη : W.η * Q ≤ q := le_of_w_ne W hQ0 hw
    have hq0 : (0 : ℝ) < q := by positivity
    have hω : 0 ≤ W.omega Q q := by
      unfold Weight.omega
      exact div_nonneg (mul_nonneg (W.nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    have hlq1 : Real.log q ≤ ℓ := Real.log_le_log hq0 hqQ
    have hlq2 : ℓ + Real.log W.η ≤ Real.log q := by
      have := Real.log_le_log (by positivity) hqη
      rw [Real.log_mul hη.ne' hQ0.ne'] at this
      linarith
    obtain ⟨h1, h2⟩ := rvm_chi_bounds hA hη (by linarith [W.η_lt_half]) hℓ1 hT2 hq0 hlq1 hlq2
      hTlog0 hTlog hbudget (hrvm q χ hq1 (mem_primChars hχ) T hTT₀)
    exact ⟨mul_le_mul_of_nonneg_left h1 hω, mul_le_mul_of_nonneg_left h2 hω⟩
  have hH : ∀ c : ℝ, c * W.H Q = ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ ∈ primChars q, W.omega Q q * c := by
    intro c
    unfold Weight.H phiStar
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  have hN : Nfam W Q T = ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ ∈ primChars q, W.omega Q q * (Nchi χ T : ℝ) := by
    unfold Nfam famSum
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum]
  have e1 : (1 - δ) * (W.H Q * T * ℓ / (2 * Real.pi)) = ((1 - δ) * (T * ℓ / (2 * Real.pi))) * W.H Q := by
    ring
  have e2 : (1 + δ) * (W.H Q * T * ℓ / (2 * Real.pi)) = ((1 + δ) * (T * ℓ / (2 * Real.pi))) * W.H Q := by
    ring
  rw [e1, e2, hH, hH, hN]
  constructor
  · exact Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun χ hχ => (key q hq χ hχ).1
  · exact Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun χ hχ => (key q hq χ hχ).2

/-- **`lem:RvM`, lower half** — `lemRvM_lower_Statement`. -/
theorem lemRvM_lower : lemRvM_lower_Statement := by
  intro W a0 A0 ha0 _ δ hδ
  obtain ⟨Q₀, h⟩ := rvm_family W ha0 hδ (A0 := A0)
  exact ⟨Q₀, fun Q hQ T hT => (h Q hQ T hT).1⟩

end Families.Ported.Zero
