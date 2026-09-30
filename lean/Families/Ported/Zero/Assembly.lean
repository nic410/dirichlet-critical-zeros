/-
# Zero side: deletion and assembly (paper §4.5) — `prop:zero` and `ZeroSideReduction`

`propZero_of_upTo : Montgomery69_Density_upTo 1 → lemWH_Statement → propZero_Statement` (Montgomery
only in the q-aspect range `T' ≤ Q`, via `lem:bad`), its corollary
`propZero_proof : Montgomery69_Density → lemWH_Statement → propZero_Statement`, and
`Families.Ported.zeroSide_proof : ZeroSideReduction`. The unconditional form is
`Families.Ported.Zero.propZero_unconditional` (`Families/Ported/Zero/Unconditional.lean`).

Proof of `prop:zero` (Proposition 3.6; proof in §4.5): for every family character,
`N^s_{0,χ} ≥ Y_χ − 2N_χ − 4|K_J| 1_{bad} − X_χ` (`perchar_uniform`), where
`Y_χ = 4 tr Ĝ_χ − ‖Ĝ_χ‖²` and `X_χ = 4η₀ + 2‖Ĝ_χ‖_F η₀ + η₀²`, `η₀ = |C_x| ℓ^{−B}/(aL²)` bounding the
exterior part of good characters (`prop:tail`); sum with the weights `ω_χ` and use
`∑ ω tr Ĝ ≥ (1 − 2θ − δ/12) N` (`prop:trace`), `∑_{bad} ω ≪ Q² ℓ^{−2}` (`lem:bad`), `N ≍ H T ℓ`
(`lem:RvM`), `H ≍ Q²` (`lem:WH`) and Cauchy–Schwarz `∑ ω ‖Ĝ‖_F ≤ (H 𝔐)^{1/2}`.
-/
import Families.Ported.Zero.DeletionChar
import Families.Ported.Zero.Trace
import Families.Ported.Zero.Bad

noncomputable section

open scoped BigOperators ComplexConjugate
open Complex Set Matrix Finset RHLinalg Filter Topology

namespace Families.Ported.Zero

open Zeta23 Zeta23.ThmE

/-! ### `famSum` linearity and Cauchy–Schwarz -/

lemma famSum_smul (W : Weight) (Q c : ℝ) (f : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) :
    famSum W Q (fun q χ => c * f q χ) = c * famSum W Q f := by
  unfold famSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← Finset.mul_sum]; ring

lemma famSum_sqrt_le (W : Weight) (Q : ℝ) (f : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ)
    (hf : ∀ q χ, 0 ≤ f q χ) :
    famSum W Q (fun q χ => Real.sqrt (f q χ)) ≤ Real.sqrt (W.H Q * famSum W Q f) := by
  unfold famSum
  have hH : W.H Q = ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ χ ∈ primChars q, (1 : ℝ) := by
    unfold Weight.H phiStar
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hH]
  -- flatten to a sum over the sigma type
  set S := (Finset.Icc 1 ⌊Q⌋₊).sigma (fun q => primChars q)
  have flat : ∀ g : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ,
      ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ χ ∈ primChars q, g q χ =
        ∑ x ∈ S, W.omega Q x.1 * g x.1 x.2 := by
    intro g
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum]
  rw [flat, flat, flat]
  apply Real.le_sqrt_of_sq_le
  have hω : ∀ x ∈ S, 0 ≤ W.omega Q x.1 := fun x _ => omega_nonneg W Q x.1
  have := Finset.sum_mul_sq_le_sq_mul_sq S (fun x => Real.sqrt (W.omega Q x.1))
    (fun x => Real.sqrt (W.omega Q x.1) * Real.sqrt (f x.1 x.2))
  have e1 : ∀ x ∈ S, Real.sqrt (W.omega Q x.1) * (Real.sqrt (W.omega Q x.1) *
      Real.sqrt (f x.1 x.2)) = W.omega Q x.1 * Real.sqrt (f x.1 x.2) := by
    intro x hx
    rw [← mul_assoc, Real.mul_self_sqrt (hω x hx)]
  have e2 : ∀ x ∈ S, Real.sqrt (W.omega Q x.1) ^ 2 = W.omega Q x.1 * 1 := by
    intro x hx; rw [Real.sq_sqrt (hω x hx), mul_one]
  have e3 : ∀ x ∈ S, (Real.sqrt (W.omega Q x.1) * Real.sqrt (f x.1 x.2)) ^ 2 =
      W.omega Q x.1 * f x.1 x.2 := by
    intro x hx; rw [mul_pow, Real.sq_sqrt (hω x hx), Real.sq_sqrt (hf _ _)]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3] at this
  exact this

variable (P : PrimeSetup)

lemma rtrace_Ghat (Q T τ₀ : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    rtrace (Ghat P Q T τ₀ χ) = (∑ k ∈ P.KJ Q T τ₀,
      (∑' ρ : PrimeSetup.strip χ, gaborTerm P Q τ₀ χ k k ρ).re) / (P.aInt * P.L Q ^ 2) := by
  rw [rtrace_eq_sum, Finset.sum_div, ← Finset.sum_coe_sort (P.KJ Q T τ₀)]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Ghat, gabor_apply]
  rw [show ((P.aInt : ℂ) * (P.L Q : ℂ) ^ 2) = ((P.aInt * P.L Q ^ 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.div_ofReal_re]

lemma card_KJ_fintype (Q T τ₀ : ℝ) :
    (Fintype.card (P.KJ Q T τ₀) : ℝ) = ((P.KJ Q T τ₀).card : ℝ) := by
  rw [Fintype.card_coe]

open Classical in
/-- The per-character inequalities in a form uniform over good and bad characters. -/
lemma perchar_uniform {Q : ℝ} (hQ : 1 < Q) (τ₀ : ℝ) {q : ℕ} (hq : 1 < q)
    {χ : DirichletCharacter ℂ q} (hprim : χ.IsPrimitive) {T : ℝ} (hT : 0 < T)
    {a B₁ η₀ : ℝ} (hη₀ : 0 ≤ η₀)
    (hgood : ¬ Bad a B₁ Q χ →
      ∑ k, ∑ l, ‖Ghat P Q T τ₀ χ k l - Ahat P Q T τ₀ χ k l‖ ≤ η₀) :
    let Y := 4 * rtrace (Ghat P Q T τ₀ χ) - frobSq (Ghat P Q T τ₀ χ)
    let X := 4 * η₀ + 2 * Real.sqrt (frobSq (Ghat P Q T τ₀ χ)) * η₀ + η₀ ^ 2
    let bd : ℝ := if Bad a B₁ Q χ then 1 else 0
    let d : ℝ := (P.KJ Q T τ₀).card
    Y - 2 * (Nchi χ T : ℝ) - 4 * d * bd - X ≤ Ns0chi χ T ∧
      Y - 2 * (Nchi χ T : ℝ) - 4 * d * bd - X ≤ Nstar0chi χ T ∧
      (Y - Nchi χ T - 4 * d * bd - X) / 2 ≤ Ndchi χ T := by
  intro Y X bd d
  have : NeZero q := ⟨by omega⟩
  have hX0 : 0 ≤ X := by positivity
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  by_cases hbad : Bad a B₁ Q χ
  · have hbd : bd = 1 := if_pos hbad
    have hY : Y ≤ 4 * d := by
      have := diag_bound (Ghat P Q T τ₀ χ)
      rw [card_KJ_fintype] at this
      exact this
    have hN := Nat.cast_nonneg (α := ℝ) (Nchi χ T)
    have h1 := Nat.cast_nonneg (α := ℝ) (Ns0chi χ T)
    have h2 := Nat.cast_nonneg (α := ℝ) (Nstar0chi χ T)
    have h3 := Nat.cast_nonneg (α := ℝ) (Ndchi χ T)
    rw [hbd]
    refine ⟨by linarith, by linarith, by linarith⟩
  · have hbd : bd = 0 := if_neg hbad
    obtain ⟨h1, h2, h3⟩ := perchi_ext P hQ τ₀ hq hprim hT (hgood hbad)
    rw [hbd]
    simp only [mul_zero, sub_zero]
    exact ⟨h1, h2, h3⟩

/-- Budget for the bad characters. -/
lemma budget_bad_arith {d T lam ℓ Cb Q δ κ₀ H N S : ℝ} (hlam : 0 < lam) (hℓ1 : 1 ≤ ℓ)
    (hT0 : 0 < T) (hQ0 : 0 < Q) (hδ : 0 < δ) (hκ₀ : 0 < κ₀) (hd0 : 0 ≤ d)
    (hd : d ≤ 2 * T * (lam * ℓ)) (hS0 : 0 ≤ S) (hS : S ≤ |Cb| * Q ^ 2 * (1 / ℓ ^ 2))
    (hbadℓ : 96 * Real.pi * lam * |Cb| / (δ * κ₀) ≤ ℓ) (hH : κ₀ * Q ^ 2 ≤ H)
    (hN : H * T * ℓ / (4 * Real.pi) ≤ N) : 4 * d * S ≤ δ / 3 * N := by
  have hℓ0 : 0 < ℓ := by linarith
  have h1 : 4 * d * S ≤ 4 * (2 * T * (lam * ℓ)) * (|Cb| * Q ^ 2 * (1 / ℓ ^ 2)) :=
    mul_le_mul (by linarith) hS hS0 (by positivity)
  have e1 : 4 * (2 * T * (lam * ℓ)) * (|Cb| * Q ^ 2 * (1 / ℓ ^ 2)) =
      8 * lam * |Cb| * Q ^ 2 * T / ℓ := by field_simp; ring
  have h2 : 8 * lam * |Cb| * Q ^ 2 * T / ℓ ≤ δ / 3 * (κ₀ * Q ^ 2 * T * ℓ / (4 * Real.pi)) := by
    rw [div_le_iff₀ (by positivity)] at hbadℓ
    rw [div_le_iff₀ hℓ0]
    have hQT : 0 ≤ Q ^ 2 * T := by positivity
    have h3 := mul_le_mul_of_nonneg_right hbadℓ hQT
    have h4 : 0 ≤ ℓ * (δ * κ₀) * (Q ^ 2 * T) := by positivity
    have e : δ / 3 * (κ₀ * Q ^ 2 * T * ℓ / (4 * Real.pi)) * ℓ =
        ℓ * (δ * κ₀) * (Q ^ 2 * T) * ℓ / (12 * Real.pi) := by field_simp; ring
    rw [e, le_div_iff₀ (by positivity)]
    have hℓℓ : ℓ * (δ * κ₀) * (Q ^ 2 * T) ≤ ℓ * (δ * κ₀) * (Q ^ 2 * T) * ℓ :=
      le_mul_of_one_le_right h4 hℓ1
    nlinarith [Real.pi_pos]
  have h5 : δ / 3 * (κ₀ * Q ^ 2 * T * ℓ / (4 * Real.pi)) ≤ δ / 3 * N := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine le_trans ?_ hN
    apply div_le_div_of_nonneg_right _ (by positivity)
    have := mul_le_mul_of_nonneg_right hH (by positivity : (0:ℝ) ≤ T * ℓ)
    nlinarith
  linarith

/-- Budget for the exterior part (the `H` terms). -/
lemma budget_ext_arith {η₀ H N T ℓ δ Cx a lam : ℝ} (hη₀0 : 0 ≤ η₀)
    (hη₀le : η₀ ≤ |Cx| / (a * lam ^ 2 * ℓ ^ 2))
    (hM₁ : 1 + |Cx| / (a * lam ^ 2) + 60 * Real.pi * |Cx| / (δ * a * lam ^ 2) ≤ ℓ)
    (hT1 : 1 ≤ T) (hH0 : 0 ≤ H) (hN : H * T * ℓ / (4 * Real.pi) ≤ N) (ha : 0 < a)
    (hlam : 0 < lam) (hδ : 0 < δ) : (4 * η₀ + η₀ ^ 2) * H ≤ δ / 3 * N := by
  have hA : 0 ≤ |Cx| / (a * lam ^ 2) := by positivity
  have hB : 0 ≤ 60 * Real.pi * |Cx| / (δ * a * lam ^ 2) := by positivity
  have hℓ1 : 1 ≤ ℓ := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hη₀1 : η₀ ≤ 1 := by
    refine hη₀le.trans ?_
    rw [div_le_one (by positivity)]
    have h1 : |Cx| / (a * lam ^ 2) ≤ ℓ := by linarith
    rw [div_le_iff₀ (by positivity)] at h1
    have : ℓ ≤ ℓ ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ a * lam ^ 2)]
  have hη₀δ : 5 * η₀ ≤ δ * ℓ / (12 * Real.pi) := by
    refine le_trans (mul_le_mul_of_nonneg_left hη₀le (by norm_num)) ?_
    have h60 : 60 * Real.pi * |Cx| / (δ * a * lam ^ 2) ≤ ℓ := by linarith
    rw [div_le_iff₀ (by positivity)] at h60
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    have hℓ3 : ℓ ≤ ℓ ^ 3 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hℓ3 (by positivity : (0:ℝ) ≤ δ * a * lam ^ 2),
      Real.pi_pos]
  have h1 : (4 * η₀ + η₀ ^ 2) * H ≤ 5 * η₀ * H := by
    have : η₀ ^ 2 ≤ η₀ := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right this hH0]
  refine h1.trans ?_
  have h2 : 5 * η₀ * H ≤ δ * ℓ / (12 * Real.pi) * H := mul_le_mul_of_nonneg_right hη₀δ hH0
  have e : δ / 3 * (H * T * ℓ / (4 * Real.pi)) = δ * ℓ / (12 * Real.pi) * H * T := by
    field_simp; ring
  have h3 : δ * ℓ / (12 * Real.pi) * H ≤ δ * ℓ / (12 * Real.pi) * H * T := by
    have : 0 ≤ δ * ℓ / (12 * Real.pi) * H := by positivity
    nlinarith
  have h4 : δ / 3 * (H * T * ℓ / (4 * Real.pi)) ≤ δ / 3 * N :=
    mul_le_mul_of_nonneg_left hN (by positivity)
  linarith

/-- `2η₀ ≤ C_z ℓ^{−B}`. -/
lemma budget_sqrt_arith {Cx ℓ ℓB a lam : ℝ} (hℓ1 : 1 ≤ ℓ) (hℓB : 0 ≤ ℓB) (ha : 0 < a)
    (hlam : 0 < lam) :
    2 * (|Cx| * ℓB / (a * (lam * ℓ) ^ 2)) ≤ 2 * |Cx| / (a * lam ^ 2) * ℓB := by
  rw [div_mul_eq_mul_div, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
  have hℓ2 : 1 ≤ ℓ ^ 2 := by nlinarith
  have : 0 ≤ 2 * (|Cx| * ℓB) * (a * lam ^ 2) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hℓ2 this]

/-- Linear expansion of the summed per-character bound. -/
lemma famSum_lin (W : Weight) (Q : ℝ) (R F Nc bd : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ)
    (c d η₀ : ℝ) :
    famSum W Q (fun q χ => 4 * R q χ + (-1) * F q χ + (-c) * Nc q χ + (-(4 * d)) * bd q χ +
      (-(2 * η₀)) * Real.sqrt (F q χ) + (-(4 * η₀ + η₀ ^ 2)) * 1) =
      4 * famSum W Q R - famSum W Q F - c * famSum W Q Nc - 4 * d * famSum W Q bd -
        ((4 * η₀ + η₀ ^ 2) * W.H Q + 2 * η₀ * famSum W Q (fun q χ => Real.sqrt (F q χ))) := by
  rw [famSum_add, famSum_add, famSum_add, famSum_add, famSum_add, famSum_smul, famSum_smul,
    famSum_smul, famSum_smul, famSum_smul, famSum_smul, famSum_const]
  ring

/-- Final arithmetic of `prop:zero` (one of the three conclusions; `c = 2` for `N^s_0, N^*_0` and
`c = 1` for `2 N_d`). -/
lemma zero_final_arith {N M H tr bdS sqS d η₀ δ Cz ℓB c Rhs : ℝ}
    (hN0 : 0 ≤ N) (hδ : 0 < δ)
    (htr : (1 - 2 * P.θ - δ / 12) * N ≤ tr)
    (hbad : 4 * d * bdS ≤ δ / 3 * N)
    (hext : (4 * η₀ + η₀ ^ 2) * H ≤ δ / 3 * N)
    (hsq : 2 * η₀ * sqS ≤ Cz * ℓB * Real.sqrt (H * M))
    (hRhs : 4 * tr - M - c * N - 4 * d * bdS - ((4 * η₀ + η₀ ^ 2) * H + 2 * η₀ * sqS) ≤ Rhs) :
    (4 - 8 * P.θ - c) * N - M - (δ * N + Cz * ℓB * Real.sqrt (H * M)) ≤ Rhs := by
  linarith

lemma half_arith {θ N M δN E Nd : ℝ} (hδN : 0 ≤ δN) (hE : 0 ≤ E)
    (h : (4 - 8 * θ - 1) * N - M - (δN + E) ≤ 2 * Nd) :
    ((3 - 8 * θ) * N - M) / 2 - (δN + E) ≤ Nd := by
  linarith

open Classical in
/-- **`prop:zero`** (paper §4), from Montgomery's density theorem in the q-aspect range
(`Montgomery69_Density_upTo 1`: heights `T' ≤ Q` only, the only ones `lem:bad` uses) and `lem:WH`. -/
theorem propZero_of_upTo (hM : Hyp.Montgomery.Montgomery69_Density_upTo 1)
    (hWH : lemWH_Statement) : propZero_Statement := by
  intro P W τ₀ B δ hB hδ
  obtain ⟨a, ha, hbadK⟩ := bad_weight_of_upTo hM
  obtain ⟨B₁, hB₁, hbadW⟩ := hbadK 2
  obtain ⟨Cb, Qb, hbad⟩ := hbadW W
  obtain ⟨Cx, Qx, hext⟩ := exterior_tail P τ₀ a B₁ ha hB₁ (envelope P) B
  obtain ⟨Qt, htr⟩ := trace_lower P hWH W τ₀ (δ := δ / 12) (by positivity)
  obtain ⟨Qr, hrvm⟩ := rvm_family W P.a0_pos (δ := 1 / 2) (by norm_num) (A0 := P.A0)
  set κ₀ := 1 / 2 * (Ecal * W.Iw) with hκ₀
  have hκ₀0 : 0 < κ₀ := by have := Ecal_pos; have := W.Iw_pos; positivity
  have hHev := H_lower_eventually hWH W (κ := 1 / 2) (by norm_num)
  have hlam := P.lam_pos
  have ha0 := aInt_pos P
  have hη := W.η_pos
  set Cz := 2 * |Cx| / (P.aInt * P.lam ^ 2) with hCz
  set M₁ := 1 + |Cx| / (P.aInt * P.lam ^ 2) + 60 * Real.pi * |Cx| / (δ * P.aInt * P.lam ^ 2)
    with hM₁
  have hev := hHev.and ((ev_log_ge 1).and ((ev_log_ge (1 / P.lam)).and ((ev_log_ge M₁).and
    ((ev_log_ge (96 * Real.pi * P.lam * |Cb| / (δ * κ₀))).and ((ev_log_rpow_ge 2 P.a0_pos).and
    (eventually_ge_atTop (2 / W.η + 2)))))))
  obtain ⟨Q₂, hQ₂⟩ := Filter.eventually_atTop.mp hev
  refine ⟨Cz, max (max (max Qb Qx) (max Qt Qr)) Q₂, fun Q hQ T hT => ?_⟩
  dsimp only
  have hQb : Qb ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans (le_max_left _ _) hQ)
  have hQx : Qx ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans (le_max_left _ _) hQ)
  have hQt : Qt ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_trans (le_max_left _ _) hQ)
  have hQr : Qr ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_trans (le_max_left _ _) hQ)
  obtain ⟨hHQ, hℓ1, hℓlam, hℓM, hℓbad, hℓa0, hQη⟩ := hQ₂ Q (le_trans (le_max_right _ _) hQ)
  set ℓ := Real.log Q with hℓ
  have hQ1 : 1 < Q := by linarith [div_pos (by norm_num : (0:ℝ) < 2) hη]
  have hQ0 : 0 < Q := by linarith
  have hT2 : 2 ≤ T := hℓa0.trans hT.1
  have hT0 : 0 < T := by linarith
  have hQη' : 2 ≤ W.η * Q := by
    have : 2 / W.η ≤ Q := by linarith
    rw [div_le_iff₀ hη] at this; linarith
  have hL : 0 < P.L Q := L_pos P hQ1
  have hLdef : P.L Q = P.lam * ℓ := rfl
  have hL1 : 1 ≤ P.L Q := by rw [hLdef]; rw [div_le_iff₀ hlam] at hℓlam; linarith
  have hc0 : 0 < P.aInt * P.L Q ^ 2 := by positivity
  -- η₀
  set η₀ := |Cx| * ℓ ^ (-B) / (P.aInt * P.L Q ^ 2) with hη₀
  have hℓB : ℓ ^ (-B) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hℓ1 (by linarith)
  have hℓB0 : 0 ≤ ℓ ^ (-B) := Real.rpow_nonneg (by linarith) _
  have hη₀0 : 0 ≤ η₀ := by positivity
  have hη₀le : η₀ ≤ |Cx| / (P.aInt * P.lam ^ 2 * ℓ ^ 2) := by
    rw [hη₀, hLdef]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : |Cx| * ℓ ^ (-B) ≤ |Cx| := mul_le_of_le_one_right (abs_nonneg _) hℓB
    nlinarith [mul_le_mul_of_nonneg_right this (by positivity : (0:ℝ) ≤ P.aInt * P.lam ^ 2 * ℓ ^ 2)]
  -- good characters
  have hgood : ∀ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.w (q / Q) ≠ 0 → ∀ χ ∈ primChars q,
      ¬ Bad a B₁ Q χ → ∑ k, ∑ l, ‖Ghat P Q T τ₀ χ k l - Ahat P Q T τ₀ χ k l‖ ≤ η₀ := by
    intro q hq hw χ hχ hgd
    have hq1 : 1 < q := one_lt_of_w_ne W hQη' hw
    have : NeZero q := ⟨by omega⟩
    have hqQ : (q : ℝ) ≤ Q :=
      (Nat.cast_le.mpr (Finset.mem_Icc.mp hq).2).trans (Nat.floor_le hQ0.le)
    obtain ⟨hsum, hle⟩ := hext Q hQx T hT q χ hq1 hqQ (mem_primChars hχ) hgd
    have h1 := ext_entry_bound P hQ1 τ₀ hq1 (mem_primChars hχ) hT0 hsum
    refine h1.trans ?_
    rw [hη₀]
    apply div_le_div_of_nonneg_right _ hc0.le
    exact hle.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hℓB0)
  -- the family sums
  set d : ℝ := ((P.KJ Q T τ₀).card : ℝ) with hd
  set bd : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ := fun _ χ => if Bad a B₁ Q χ then 1 else 0
  set F : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ := fun _ χ => frobSq (Ghat P Q T τ₀ χ)
  set R : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ := fun _ χ => rtrace (Ghat P Q T τ₀ χ)
  have hF0 : ∀ q χ, 0 ≤ F q χ := fun q χ => by
    simp only [F]; rw [frobSq_eq_sum]; positivity
  have hMfrak : P.Mfrak W Q T τ₀ = famSum W Q F := Mfrak_eq P W Q T τ₀
  have hTr : (1 - 2 * P.θ - δ / 12) * Nfam W Q T ≤ famSum W Q R := by
    have := htr Q hQt T hT
    simpa only [R, rtrace_Ghat] using this
  have hBad : famSum W Q bd ≤ Cb * Q ^ 2 * ℓ ^ (-(2 : ℝ)) := hbad Q hQb
  have hSq : famSum W Q (fun q χ => Real.sqrt (F q χ)) ≤ Real.sqrt (W.H Q * famSum W Q F) :=
    famSum_sqrt_le W Q F hF0
  have hNr := hrvm Q hQr T hT
  have hH : κ₀ * Q ^ 2 ≤ W.H Q := by rw [hκ₀]; linarith
  have hH0 : 0 ≤ W.H Q := le_trans (by positivity) hH
  have hN0 : 0 ≤ Nfam W Q T := by
    unfold Nfam famSum
    exact Finset.sum_nonneg fun q _ => mul_nonneg (omega_nonneg W Q q)
      (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
  have hNlow : W.H Q * T * ℓ / (4 * Real.pi) ≤ Nfam W Q T := by
    have := hNr.1
    have e : (1 - 1 / 2) * (W.H Q * T * ℓ / (2 * Real.pi)) = W.H Q * T * ℓ / (4 * Real.pi) := by
      field_simp; ring
    linarith
  -- budget: bad characters
  have hbd0 : 0 ≤ famSum W Q bd := by
    unfold famSum
    exact Finset.sum_nonneg fun q _ => mul_nonneg (omega_nonneg W Q q)
      (Finset.sum_nonneg fun χ _ => by simp only [bd]; split <;> norm_num)
  have hbudget_bad : 4 * d * famSum W Q bd ≤ δ / 3 * Nfam W Q T := by
    have hD := card_KJ_le P hQ1 hT0.le τ₀
    have hTL : 1 ≤ T * P.L Q := one_le_mul_of_one_le_of_one_le (by linarith) hL1
    have hd2 : d ≤ 2 * T * (P.lam * ℓ) := by rw [hd, ← hLdef]; linarith
    have hbd1 : famSum W Q bd ≤ |Cb| * Q ^ 2 * (1 / ℓ ^ 2) := by
      have hℓ2 : ℓ ^ (-(2 : ℝ)) = 1 / ℓ ^ 2 := by
        rw [Real.rpow_neg (by linarith), one_div]; norm_cast
      rw [← hℓ2]
      exact hBad.trans (by gcongr; exact le_abs_self _)
    exact budget_bad_arith hlam hℓ1 hT0 hQ0 hδ hκ₀0 (Nat.cast_nonneg _) hd2 hbd0 hbd1 hℓbad hH
      hNlow
  have hbudget_ext : (4 * η₀ + η₀ ^ 2) * W.H Q ≤ δ / 3 * Nfam W Q T :=
    budget_ext_arith hη₀0 hη₀le hℓM (by linarith) hH0 hNlow ha0 hlam hδ
  have hSq' : famSum W Q (fun q χ => Real.sqrt (F q χ)) ≤
      Real.sqrt (W.H Q * P.Mfrak W Q T τ₀) := by rw [hMfrak]; exact hSq
  have hSq0 : 0 ≤ famSum W Q (fun q χ => Real.sqrt (F q χ)) := by
    unfold famSum
    exact Finset.sum_nonneg fun q _ => mul_nonneg (omega_nonneg W Q q)
      (Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _)
  have h2η : 2 * η₀ ≤ Cz * ℓ ^ (-B) := by
    rw [hη₀, hCz, hLdef]
    exact budget_sqrt_arith hℓ1 hℓB0 ha0 hlam
  have hsq : 2 * η₀ * famSum W Q (fun q χ => Real.sqrt (F q χ)) ≤
      Cz * ℓ ^ (-B) * Real.sqrt (W.H Q * P.Mfrak W Q T τ₀) :=
    mul_le_mul h2η hSq' hSq0 (by positivity)
  -- per-character bounds, summed
  have hper := fun q (hq : q ∈ Finset.Icc 1 ⌊Q⌋₊) (hw : W.w (q / Q) ≠ 0) χ (hχ : χ ∈ primChars q) =>
    perchar_uniform P hQ1 τ₀ (one_lt_of_w_ne W hQη' hw) (mem_primChars hχ) hT0 hη₀0
      (hgood q hq hw χ hχ)
  have hsumc : ∀ (c : ℝ) (G : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ),
      (∀ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.w (q / Q) ≠ 0 → ∀ χ ∈ primChars q,
        4 * R q χ - F q χ - c * (Nchi χ T : ℝ) - 4 * d * bd q χ -
          (4 * η₀ + 2 * Real.sqrt (F q χ) * η₀ + η₀ ^ 2) ≤ G q χ) →
      4 * famSum W Q R - famSum W Q F - c * Nfam W Q T - 4 * d * famSum W Q bd -
        ((4 * η₀ + η₀ ^ 2) * W.H Q + 2 * η₀ * famSum W Q (fun q χ => Real.sqrt (F q χ))) ≤
        famSum W Q G := by
    intro c G hG
    have hNf : Nfam W Q T = famSum W Q (fun _ χ => (Nchi χ T : ℝ)) := rfl
    rw [hNf, ← famSum_lin W Q R F (fun _ χ => (Nchi χ T : ℝ)) bd c d η₀]
    refine famSum_mono_family W Q fun q hq hw χ hχ => ?_
    refine le_trans (le_of_eq ?_) (hG q hq hw χ hχ)
    ring
  have hNs := hsumc 2 (fun _ χ => (Ns0chi χ T : ℝ)) fun q hq hw χ hχ => by
    have := (hper q hq hw χ hχ).1
    simp only [R, F, bd] at this ⊢
    linarith
  have hNst := hsumc 2 (fun _ χ => (Nstar0chi χ T : ℝ)) fun q hq hw χ hχ => by
    have := (hper q hq hw χ hχ).2.1
    simp only [R, F, bd] at this ⊢
    linarith
  have hNd := hsumc 1 (fun _ χ => 2 * (Ndchi χ T : ℝ)) fun q hq hw χ hχ => by
    have := (hper q hq hw χ hχ).2.2
    simp only [R, F, bd] at this ⊢
    linarith
  have hNd' : famSum W Q (fun _ χ => 2 * (Ndchi χ T : ℝ)) = 2 * Nd W Q T := by
    rw [famSum_smul]; rfl
  rw [hNd'] at hNd
  rw [← hMfrak] at hNs hNst hNd
  have hfin := fun (c : ℝ) (Rhs : ℝ) (h : 4 * famSum W Q R - P.Mfrak W Q T τ₀ - c * Nfam W Q T -
      4 * d * famSum W Q bd - ((4 * η₀ + η₀ ^ 2) * W.H Q +
        2 * η₀ * famSum W Q (fun q χ => Real.sqrt (F q χ))) ≤ Rhs) =>
    zero_final_arith P hN0 hδ hTr hbudget_bad hbudget_ext hsq h (c := c)
  refine ⟨?_, ?_, ?_⟩
  · have := hfin 2 _ hNs
    have e : (4 - 8 * P.θ - 2) = 2 - 8 * P.θ := by ring
    rw [e] at this
    exact this
  · have := hfin 2 _ hNst
    have e : (4 - 8 * P.θ - 2) = 2 - 8 * P.θ := by ring
    rw [e] at this
    exact this
  · have := hfin 1 _ hNd
    have hCz0 : 0 ≤ Cz := by rw [hCz]; positivity
    have hsq0 : 0 ≤ Cz * ℓ ^ (-B) * Real.sqrt (W.H Q * P.Mfrak W Q T τ₀) :=
      mul_nonneg (mul_nonneg hCz0 hℓB0) (Real.sqrt_nonneg _)
    exact half_arith (mul_nonneg hδ.le hN0) hsq0 this

/-- **`prop:zero`** (paper §4), from the full `Montgomery69_Density` (all heights) and `lem:WH`: the
original form, kept for the record (via `propZero_of_upTo`; only the heights `T' ≤ Q` are used). -/
theorem propZero_proof (hM : Montgomery69_Density) (hWH : lemWH_Statement) :
    propZero_Statement :=
  propZero_of_upTo (Hyp.Montgomery.Montgomery69_Density_upTo_of_full 1 hM) hWH

/-- **The zero-side reduction** (paper §4 and Appendix B): `ZeroSideReduction`. -/
theorem zeroSide_proof' : ZeroSideReduction := fun _ hM _ hWH =>
  ⟨propZero_proof hM hWH, lemRvM_lower⟩

end Families.Ported.Zero

namespace Families.Ported

/-- **`ZeroSideReduction` is a theorem**. -/
theorem zeroSide_proof : ZeroSideReduction := Families.Ported.Zero.zeroSide_proof'

end Families.Ported
