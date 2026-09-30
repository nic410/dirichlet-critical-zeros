/-
# Theorem 1.4(a), package Z: weighted Riemann–von Mangoldt at polynomial height (Lemma 9.2)

* `rvm_chi_boundsH`: the per-character arithmetic with `ℓ_* = log Q + log T` (the terms `log T` now
  belong to the main term, instead of being `o(ℓ)` as in `Families.Ported.Zero.rvm_chi_bounds`).
* `rvm_familyH`: `(1−δ) H T ℓ_*/2π ≤ N ≤ (1+δ) H T ℓ_*/2π`, uniformly for all `T ≥ ℓ^{a₀}` (no upper
  height bound is needed: the q-uniform count `Families.Ported.Zero.rvm_chi` has absolute constants).
* `lemRvMH_lower_proof : lemRvMH_lower_Statement`.
-/
import FamiliesH.Z.Basic

noncomputable section

open scoped BigOperators ComplexConjugate
open Complex Set Filter Topology

namespace Families.Hybrid.Z

open Families Families.Hybrid Families.Ported.Zero Zeta23 Zeta23.ThmE

/-- Real-arithmetic core of the family count at polynomial height. -/
lemma rvm_chi_boundsH {A η δ ℓ ℓs T Nχ : ℝ} {q : ℕ} (hA : 0 < A) (hη : 0 < η) (hη1 : η ≤ 1)
    (hT : 2 ≤ T) (hq : (0 : ℝ) < q) (hq1 : Real.log q ≤ ℓ)
    (hq2 : ℓ + Real.log η ≤ Real.log q) (hℓs : ℓs = ℓ + Real.log T)
    (hbudget : T * (-Real.log η + Real.log (2 * Real.pi) + 1) + 2 * Real.pi * A * (ℓs + 1) ≤
      δ * T * ℓs)
    (hN : |Nχ - T / (2 * Real.pi) * ell1q q T| ≤ A * Real.log (q * (T + 2))) :
    (1 - δ) * (T * ℓs / (2 * Real.pi)) ≤ Nχ ∧ Nχ ≤ (1 + δ) * (T * ℓs / (2 * Real.pi)) := by
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
  -- error term
  have herr : A * Real.log (q * (T + 2)) ≤ A * (ℓs + 1) := by
    apply mul_le_mul_of_nonneg_left _ hA.le
    rw [Real.log_mul hq.ne' (by linarith)]
    have h2T : Real.log (T + 2) ≤ Real.log T + 1 := by
      have h1 : Real.log (T + 2) ≤ Real.log (2 * T) := Real.log_le_log (by linarith) (by linarith)
      rw [Real.log_mul (by norm_num) hT0.ne'] at h1
      linarith
    rw [hℓs]; linarith
  obtain ⟨hl, hr⟩ := abs_le.mp hN
  have hmain_lo : T * ℓs / (2 * Real.pi) - T * (-Real.log η + Real.log (2 * Real.pi) + 1) / (2 * Real.pi)
      ≤ T / (2 * Real.pi) * ell1q q T := by
    rw [hell, hℓs]
    have e : T / (2 * Real.pi) * (Real.log q + Real.log T - Real.log (2 * Real.pi) + 2 * Real.log 2 - 1)
        - (T * (ℓ + Real.log T) / (2 * Real.pi) -
          T * (-Real.log η + Real.log (2 * Real.pi) + 1) / (2 * Real.pi)) =
        T / (2 * Real.pi) * ((Real.log q - ℓ - Real.log η) + 2 * Real.log 2) := by
      field_simp; ring
    have : 0 ≤ T / (2 * Real.pi) * ((Real.log q - ℓ - Real.log η) + 2 * Real.log 2) :=
      mul_nonneg (by positivity) (by linarith)
    linarith
  have hmain_hi : T / (2 * Real.pi) * ell1q q T ≤ T * ℓs / (2 * Real.pi) := by
    rw [hell, hℓs]
    have e : T * (ℓ + Real.log T) / (2 * Real.pi) -
        T / (2 * Real.pi) * (Real.log q + Real.log T - Real.log (2 * Real.pi) + 2 * Real.log 2 - 1) =
        T / (2 * Real.pi) * ((ℓ - Real.log q) + (Real.log (2 * Real.pi) - (2 * Real.log 2 - 1))) := by
      field_simp; ring
    have : 0 ≤ T / (2 * Real.pi) * ((ℓ - Real.log q) +
        (Real.log (2 * Real.pi) - (2 * Real.log 2 - 1))) :=
      mul_nonneg (by positivity) (by linarith)
    linarith
  have hc0 : 0 ≤ -Real.log η + Real.log (2 * Real.pi) + 1 := by linarith
  have hbud : T * (-Real.log η + Real.log (2 * Real.pi) + 1) / (2 * Real.pi) + A * (ℓs + 1)
      ≤ δ * (T * ℓs / (2 * Real.pi)) := by
    rw [div_add' _ _ _ hπ.ne', div_le_iff₀ hπ]
    have : δ * (T * ℓs / (2 * Real.pi)) * (2 * Real.pi) = δ * T * ℓs := by field_simp
    rw [this]; nlinarith
  have hbud' : A * (ℓs + 1) ≤ δ * (T * ℓs / (2 * Real.pi)) := by
    have : 0 ≤ T * (-Real.log η + Real.log (2 * Real.pi) + 1) / (2 * Real.pi) := by positivity
    linarith
  constructor
  · nlinarith
  · nlinarith

/-- **`lem:RvMH`** (both halves): `(1−δ) H T ℓ_*/2π ≤ N ≤ (1+δ) H T ℓ_*/2π` for all `T ≥ ℓ^{a₀}`. -/
theorem rvm_familyH (W : Weight) {a0 : ℝ} (ha0 : 0 < a0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ T : ℝ, Real.log Q ^ a0 ≤ T →
      (1 - δ) * (W.H Q * T * ellS Q T / (2 * Real.pi)) ≤ Nfam W Q T ∧
      Nfam W Q T ≤ (1 + δ) * (W.H Q * T * ellS Q T / (2 * Real.pi)) := by
  obtain ⟨A, T₀, hA, hT₀, hrvm⟩ := rvm_chi
  set c : ℝ := -Real.log W.η + Real.log (2 * Real.pi) + 1 with hc
  have hev := (ev_log_ge 1).and ((ev_log_ge (2 * c / δ)).and
    ((ev_log_rpow_ge T₀ ha0).and (ev_log_rpow_ge (8 * Real.pi * A / δ) ha0)))
  obtain ⟨Q₁, hQ₁⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max Q₁ (2 / W.η + 1), fun Q hQ T hT => ?_⟩
  obtain ⟨hℓ1, hℓc, hT0', hTA⟩ := hQ₁ Q ((le_max_left _ _).trans hQ)
  have hη := W.η_pos
  have hη1 : W.η ≤ 1 := by linarith [W.η_lt_half]
  have hQη : 2 ≤ W.η * Q := by
    have h1 : 2 / W.η + 1 ≤ Q := (le_max_right _ _).trans hQ
    have : 2 / W.η ≤ Q := by linarith
    rw [div_le_iff₀ hη] at this; linarith
  have hQ0 : 0 < Q := by nlinarith
  set ℓ := Real.log Q with hℓ
  have hTT₀ : T₀ ≤ T := hT0'.trans hT
  have hT2 : 2 ≤ T := hT₀.trans hTT₀
  have hTpos : 0 < T := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  set ℓs := ellS Q T with hℓs_def
  have hℓs : ℓs = ℓ + Real.log T := ellS_eq hQ0 hTpos
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hℓsℓ : ℓ ≤ ℓs := by rw [hℓs]; linarith
  -- the budget
  have hc0 : 0 ≤ c := by
    have : Real.log W.η ≤ 0 := Real.log_nonpos hη.le hη1
    have : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
    rw [hc]; linarith
  have hbudget : T * c + 2 * Real.pi * A * (ℓs + 1) ≤ δ * T * ℓs := by
    have e1 : c ≤ δ / 2 * ℓ := by
      rw [div_le_iff₀ hδ] at hℓc; nlinarith
    have e2 : 8 * Real.pi * A ≤ δ * T := by
      rw [div_le_iff₀ hδ] at hTA; nlinarith
    have hℓs1 : 1 ≤ ℓs := by linarith
    have f1 : T * c ≤ δ / 2 * T * ℓs := by
      have : c ≤ δ / 2 * ℓs := e1.trans (by nlinarith)
      have := mul_le_mul_of_nonneg_left this hTpos.le
      linarith
    have f2 : 2 * Real.pi * A * (ℓs + 1) ≤ δ / 2 * T * ℓs := by
      have hπA : 0 ≤ 2 * Real.pi * A := by positivity
      have g1 : 2 * Real.pi * A * (ℓs + 1) ≤ 2 * Real.pi * A * (2 * ℓs) :=
        mul_le_mul_of_nonneg_left (by linarith) hπA
      have g2 : 4 * Real.pi * A ≤ δ / 2 * T := by linarith
      have g3 := mul_le_mul_of_nonneg_right g2 (by linarith : (0:ℝ) ≤ ℓs)
      nlinarith
    linarith
  -- termwise bounds
  have key : ∀ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∀ χ ∈ primChars q,
      W.omega Q q * ((1 - δ) * (T * ℓs / (2 * Real.pi))) ≤ W.omega Q q * (Nchi χ T : ℝ) ∧
      W.omega Q q * (Nchi χ T : ℝ) ≤ W.omega Q q * ((1 + δ) * (T * ℓs / (2 * Real.pi))) := by
    intro q hq χ hχ
    by_cases hw : W.w (q / Q) = 0
    · simp [Weight.omega, hw]
    have hq1 : 1 < q := one_lt_of_w_ne W hQη hw
    have hqQ : (q : ℝ) ≤ Q := by
      have := (Finset.mem_Icc.mp hq).2
      exact (Nat.cast_le.mpr this).trans (Nat.floor_le hQ0.le)
    have hqη : W.η * Q ≤ q := le_of_w_ne W hQ0 hw
    have hq0 : (0 : ℝ) < q := by positivity
    have hω : 0 ≤ W.omega Q q := omega_nonneg W Q q
    have hlq1 : Real.log q ≤ ℓ := Real.log_le_log hq0 hqQ
    have hlq2 : ℓ + Real.log W.η ≤ Real.log q := by
      have := Real.log_le_log (by positivity) hqη
      rw [Real.log_mul hη.ne' hQ0.ne'] at this
      linarith
    obtain ⟨h1, h2⟩ := rvm_chi_boundsH hA hη hη1 hT2 hq0 hlq1 hlq2 hℓs hbudget
      (hrvm q χ hq1 (Families.Ported.Zero.mem_primChars hχ) T hTT₀)
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
  have e1 : (1 - δ) * (W.H Q * T * ℓs / (2 * Real.pi)) =
      ((1 - δ) * (T * ℓs / (2 * Real.pi))) * W.H Q := by ring
  have e2 : (1 + δ) * (W.H Q * T * ℓs / (2 * Real.pi)) =
      ((1 + δ) * (T * ℓs / (2 * Real.pi))) * W.H Q := by ring
  rw [e1, e2, hH, hH, hN]
  constructor
  · exact Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun χ hχ => (key q hq χ hχ).1
  · exact Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun χ hχ => (key q hq χ hχ).2

/-- **`lem:RvMH`, lower half** — `lemRvMH_lower_Statement`. -/
theorem lemRvMH_lower_proof : lemRvMH_lower_Statement := by
  intro W a0 kc ha0 _ δ hδ
  obtain ⟨Q₀, h⟩ := rvm_familyH W ha0 hδ
  exact ⟨Q₀, fun Q hQ T hT => (h Q hQ T hT.1).1⟩

end Families.Hybrid.Z
