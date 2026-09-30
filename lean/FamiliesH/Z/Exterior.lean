/-
# Theorem 1.4(a), package Z: the exterior tail at polynomial height (Proposition 9.7, `prop:tailH`)

For a primitive `χ` mod `q ∈ (1, Q]` that is **not** `Bad a B₁ Q χ` (the bad set of the family
parameter `Q`: it does not depend on `T`) and `T` in the cell, the zeros with `γ ∉ (T, 2T]` contribute
`∑_ρ m_ρ (∑_{k ∈ K_J} ‖p_k(z_ρ)‖)² ≪_B ℓ^{-B}` at bandwidth `L = λ ℓ_*` (`exterior_tailH`).

Changes from `Families.Ported.Zero.exterior_tail`:
* `exp_le_goodH`: `e^{L|δ|} = e^{λℓ|δ|} · T^{λ|δ|} ≤ ℓ^{2B₁} (1 + |γ|)^{n₀} · T` (the first factor is the
  families `exp_le_good` at `Q`; the second uses `λ|δ| ≤ 1`), so `E² ≤ G D^{n₀+1}` with `D = T + |γ|`;
* `final_arithH`: the powers of `L` are bounded through `L ≥ λℓ` (`L^{4−2A} ≤ (λℓ)^{4−2A}`).
The zero count (`count_sum_le`) is over conductors `q ≤ Q` and is unchanged.
-/
import FamiliesH.Z.Basic

noncomputable section

open scoped BigOperators
open Complex Set

namespace Families.Hybrid.Z

open Families Families.Hybrid Families.Ported.Zero Zeta23 Zeta23.ThmE

/-- Good characters at polynomial height: `e^{L(QT)|δ|} ≤ ℓ^{2B₁}(1 + |γ|)^{n₀} T`. -/
lemma exp_le_goodH (P : PrimeSetup) {a B₁ Q T : ℝ} (hB₁ : 0 ≤ B₁) (hQ : 1 < Q) (hT : 1 ≤ T)
    (hℓ : 1 ≤ Real.log Q) {n₀ : ℕ} (hn₀ : 2 ≤ a * n₀) {q : ℕ} {χ : DirichletCharacter ℂ q}
    (hgood : ¬ Bad a B₁ Q χ) {ρ : ℂ} (hρ : ρ ∈ PrimeSetup.strip χ) :
    Real.exp (P.L (Q * T) * |ρ.re - 1 / 2|) ≤
      Real.log Q ^ (2 * B₁) * (1 + |ρ.im|) ^ n₀ * T := by
  have hQ0 : 0 < Q := by linarith
  have hT0 : 0 < T := by linarith
  have hlam := P.lam_pos
  have hlam2 := P.lam_lt
  have h1 := exp_le_good P hB₁ hQ hℓ hn₀ hgood hρ
  -- |δ| < 1/2 in the strip
  have hδ : |ρ.re - 1 / 2| ≤ 1 / 2 := by
    have hr0 := hρ.2.1
    have hr1 := hρ.2.2
    rw [abs_le]; constructor <;> linarith
  have hsplit : P.L (Q * T) * |ρ.re - 1 / 2| =
      P.L Q * |ρ.re - 1 / 2| + P.lam * |ρ.re - 1 / 2| * Real.log T := by
    unfold PrimeSetup.L
    rw [Real.log_mul hQ0.ne' hT0.ne']; ring
  have h2 : Real.exp (P.lam * |ρ.re - 1 / 2| * Real.log T) ≤ T := by
    have hlT : 0 ≤ Real.log T := Real.log_nonneg hT
    have hc : P.lam * |ρ.re - 1 / 2| ≤ 1 := by
      have : P.lam * |ρ.re - 1 / 2| ≤ P.lam * (1 / 2) :=
        mul_le_mul_of_nonneg_left hδ hlam.le
      linarith
    calc Real.exp (P.lam * |ρ.re - 1 / 2| * Real.log T) ≤ Real.exp (Real.log T) := by
          apply Real.exp_le_exp.mpr
          have := mul_le_mul_of_nonneg_right hc hlT
          linarith
      _ = T := Real.exp_log hT0
  rw [hsplit, Real.exp_add]
  exact mul_le_mul h1 h2 (Real.exp_pos _).le
    (mul_nonneg (Real.rpow_nonneg (by linarith) _) (by positivity))

/-- The final bound in `ℓ` at bandwidth `L ≥ λℓ`. -/
lemma final_arithH {lam θ M A₀ S ℓ L B B₁ : ℝ} {A : ℕ} (hlam : 0 < lam) (hθ : 0 < θ)
    (hA₀ : 0 ≤ A₀) (hS : 0 ≤ S) (hℓ : 1 ≤ ℓ) (hL1 : 1 ≤ lam * ℓ) (hL : lam * ℓ ≤ L)
    (hA4 : 4 ≤ 2 * A) (hA : 5 + 2 * B₁ + B ≤ 2 * (A : ℝ)) :
    (L + 1) ^ 2 * M ^ 2 * L ^ 2 * ℓ ^ (2 * B₁) * (4 / (L * θ)) ^ (2 * A) *
        (16 * A₀ * (ℓ + 3) * S) ≤
      (4 * M ^ 2 * (4 / θ) ^ (2 * A) * (lam ^ (2 * A - 4))⁻¹ * 64 * A₀ * S) * ℓ ^ (-B) := by
  have hℓ0 : 0 < ℓ := by linarith
  have hlℓ : 0 < lam * ℓ := by positivity
  have hL0 : 0 < L := by linarith
  have hL1' : 1 ≤ L := by linarith
  set m := 2 * A - 4 with hm
  have hmA : 2 * A = m + 4 := by omega
  have hmR : (2 * A : ℝ) = (m : ℝ) + 4 := by exact_mod_cast hmA
  have e1 : (4 / (L * θ)) ^ (2 * A) = (4 / θ) ^ (2 * A) * ((L ^ m)⁻¹ * (L ^ 4)⁻¹) := by
    rw [← mul_inv, ← pow_add, ← hmA, ← div_eq_mul_inv, ← div_pow]
    congr 1
    rw [div_div, mul_comm θ L]
  rw [e1]
  have h1 : L + 1 ≤ 2 * L := by linarith
  have h2 : ℓ + 3 ≤ 4 * ℓ := by linarith
  have hG : 0 ≤ ℓ ^ (2 * B₁) := Real.rpow_nonneg hℓ0.le _
  have hLm : (L ^ m)⁻¹ ≤ ((lam * ℓ) ^ m)⁻¹ :=
    inv_anti₀ (pow_pos hlℓ m) (pow_le_pow_left₀ hlℓ.le hL m)
  have hpow : ℓ ^ (2 * B₁) * ℓ ^ (1 : ℕ) * (ℓ ^ m)⁻¹ ≤ ℓ ^ (-B) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_neg hℓ0.le,
      ← Real.rpow_add hℓ0, ← Real.rpow_add hℓ0]
    apply Real.rpow_le_rpow_of_exponent_le hℓ
    push_cast
    linarith
  have hK : 0 ≤ 4 * M ^ 2 * (4 / θ) ^ (2 * A) * (lam ^ m)⁻¹ * 64 * A₀ * S := by positivity
  calc (L + 1) ^ 2 * M ^ 2 * L ^ 2 * ℓ ^ (2 * B₁) *
        ((4 / θ) ^ (2 * A) * ((L ^ m)⁻¹ * (L ^ 4)⁻¹)) * (16 * A₀ * (ℓ + 3) * S)
      ≤ (2 * L) ^ 2 * M ^ 2 * L ^ 2 * ℓ ^ (2 * B₁) *
        ((4 / θ) ^ (2 * A) * ((L ^ m)⁻¹ * (L ^ 4)⁻¹)) * (16 * A₀ * (4 * ℓ) * S) := by
        gcongr
    _ = (4 * M ^ 2 * (4 / θ) ^ (2 * A) * 64 * A₀ * S) * (ℓ ^ (2 * B₁) * ℓ * (L ^ m)⁻¹) *
          (L ^ 4 * (L ^ 4)⁻¹) := by ring
    _ = (4 * M ^ 2 * (4 / θ) ^ (2 * A) * 64 * A₀ * S) * (ℓ ^ (2 * B₁) * ℓ * (L ^ m)⁻¹) := by
        rw [mul_inv_cancel₀ (pow_ne_zero 4 hL0.ne'), mul_one]
    _ ≤ (4 * M ^ 2 * (4 / θ) ^ (2 * A) * 64 * A₀ * S) * (ℓ ^ (2 * B₁) * ℓ * ((lam * ℓ) ^ m)⁻¹) := by
        gcongr
    _ = (4 * M ^ 2 * (4 / θ) ^ (2 * A) * (lam ^ m)⁻¹ * 64 * A₀ * S) *
          (ℓ ^ (2 * B₁) * ℓ ^ (1 : ℕ) * (ℓ ^ m)⁻¹) := by
        simp only [mul_pow, mul_inv, pow_one]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow hK

/-- **`prop:tailH`**: the exterior tail of a good character at polynomial height, uniformly in the
cell (`Bad` is the `T`-independent bad set at the family parameter `Q`). -/
theorem exterior_tailH (P : HSetup) (τ₀ a B₁ : ℝ) (ha : 0 < a) (hB₁ : 0 < B₁) (B : ℝ) :
    ∃ C Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ P.heights Q, ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      1 < q → (q : ℝ) ≤ Q → χ.IsPrimitive → ¬ Bad a B₁ Q χ →
      Summable (extTerm (toPS P) (Q * T) T τ₀ χ) ∧
        ∑' ρ, extTerm (toPS P) (Q * T) T τ₀ χ ρ ≤ C * Real.log Q ^ (-B) := by
  set P' := toPS P with hP'
  obtain ⟨A₀, hA₀1, hloc⟩ := localCountChi_uniform_proof
  set n₀ : ℕ := ⌈2 / a⌉₊ with hn₀_def
  have hn₀ : 2 ≤ a * n₀ := by
    have := Nat.le_ceil (2 / a)
    rw [div_le_iff₀ ha] at this
    linarith
  set A : ℕ := n₀ + 7 + ⌈B + 2 * B₁⌉₊ with hA_def
  have hA1 : n₀ + 1 + 6 ≤ 2 * A := by omega
  have hA4 : 4 ≤ 2 * A := by omega
  have hA2 : 5 + 2 * B₁ + B ≤ 2 * (A : ℝ) := by
    have h1 := Nat.le_ceil (B + 2 * B₁)
    have h2 : (A : ℝ) = n₀ + 7 + ⌈B + 2 * B₁⌉₊ := by simp [hA_def]
    have h3 : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
    have h4 : (0 : ℝ) ≤ ⌈B + 2 * B₁⌉₊ := Nat.cast_nonneg _
    linarith
  obtain ⟨M, hM0, hM⟩ := envelope P' A
  set S := ∑' j : ℤ, ((1 + |(j : ℝ)|) ^ 3)⁻¹ with hS_def
  have hS : 0 ≤ S := tsum_nonneg fun _ => by positivity
  have hlam := P'.lam_pos
  refine ⟨4 * M ^ 2 * (4 / P'.θ) ^ (2 * A) * (P'.lam ^ (2 * A - 4))⁻¹ * 64 * A₀ * S,
    Real.exp (1 + 1 / P'.lam), ?_⟩
  intro Q hQ T hT q χ hq hqQ hprim hgood
  have : NeZero q := ⟨by omega⟩
  have hℓ' : 1 + 1 / P'.lam ≤ Real.log Q := by
    rw [← Real.log_exp (1 + 1 / P'.lam)]
    exact Real.log_le_log (Real.exp_pos _) hQ
  have hl0 : 0 < 1 / P'.lam := by positivity
  have hℓ : 1 ≤ Real.log Q := by linarith
  have hQ1 : 1 < Q := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr (by positivity)) hQ
  have hQ0 : 0 < Q := by linarith
  have hT1 : 1 ≤ T := le_trans (Real.one_le_rpow hℓ P.a0_pos.le) hT.1
  have hT0 : 0 < T := by linarith
  have hQT : 1 < Q * T := one_lt_QT hQ1 hT1
  have hL : 0 < P'.L (Q * T) := L_pos P' hQT
  have hθ := P'.θ_pos
  have hG : 0 ≤ Real.log Q ^ (2 * B₁) := Real.rpow_nonneg (by linarith) _
  set K₁ := (P'.L (Q * T) + 1) ^ 2 * M ^ 2 * P'.L (Q * T) ^ 2 * Real.log Q ^ (2 * B₁) *
    (4 / (P'.L (Q * T) * P'.θ)) ^ (2 * A) with hK₁_def
  have hK₁ : 0 ≤ K₁ := mul_nonneg (mul_nonneg (by positivity) hG) (by positivity)
  -- the per-zero bound
  have hterm : ∀ ρ, extTerm P' (Q * T) T τ₀ χ ρ ≤
      K₁ * ((mult χ ρ : ℝ) * ((T + |(ρ : ℂ).im|) ^ 4)⁻¹) := by
    rintro ⟨ρ, hρs, hρI⟩
    show (mult χ ρ : ℝ) * (∑ k ∈ P'.KJ (Q * T) T τ₀, ‖P'.pk (Q * T) τ₀ k (zOf ρ)‖) ^ 2 ≤
      K₁ * ((mult χ ρ : ℝ) * ((T + |ρ.im|) ^ 4)⁻¹)
    set D := T + |ρ.im| with hD_def
    have hD : T ≤ D := le_add_of_nonneg_right (abs_nonneg _)
    have hD0 : 0 < D := by linarith
    have hD1 : 1 + |ρ.im| ≤ D := by linarith
    set E := Real.exp (P'.L (Q * T) * |ρ.re - 1 / 2| / 2) with hE_def
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    have hE2 : E ^ 2 ≤ Real.log Q ^ (2 * B₁) * D ^ (n₀ + 1) := by
      have h1 : E ^ 2 = Real.exp (P'.L (Q * T) * |ρ.re - 1 / 2|) := by
        rw [hE_def, sq, ← Real.exp_add]
        ring_nf
      rw [h1]
      refine (exp_le_goodH P' hB₁.le hQ1 hT1 hℓ hn₀ hgood hρs).trans ?_
      rw [pow_succ, ← mul_assoc]
      apply mul_le_mul _ hD hT0.le (by positivity)
      apply mul_le_mul_of_nonneg_left _ hG
      exact pow_le_pow_left₀ (by positivity) hD1 n₀
    have hk : ∀ k ∈ P'.KJ (Q * T) T τ₀, ‖P'.pk (Q * T) τ₀ k (zOf ρ)‖ ≤
        M * P'.L (Q * T) * E / (P'.L (Q * T) * P'.θ * D / 4) ^ A := by
      intro k hk
      obtain ⟨h1, h2⟩ := tau_mem_J P' hQT T τ₀ hk
      have hdist := dist_ge P'.θ_pos P'.θ_lt (by linarith) h1 h2 hρI
      have hdist' : P'.L (Q * T) * P'.θ * D / 4 ≤
          P'.L (Q * T) * |(zOf ρ).re - tau P' (Q * T) τ₀ k| := by
        rw [zOf_re]
        calc P'.L (Q * T) * P'.θ * D / 4 = P'.L (Q * T) * (P'.θ * (T + |ρ.im|) / 4) := by
              rw [hD_def]; ring
          _ ≤ P'.L (Q * T) * |ρ.im - tau P' (Q * T) τ₀ k| :=
              mul_le_mul_of_nonneg_left hdist hL.le
      have := norm_pk_le P' hM hQT τ₀ k (zOf ρ) (by positivity) hdist'
      rwa [zOf_im, abs_neg] at this
    have hsum : ∑ k ∈ P'.KJ (Q * T) T τ₀, ‖P'.pk (Q * T) τ₀ k (zOf ρ)‖ ≤
        (T * P'.L (Q * T) + 1) * (M * P'.L (Q * T) * E / (P'.L (Q * T) * P'.θ * D / 4) ^ A) := by
      calc ∑ k ∈ P'.KJ (Q * T) T τ₀, ‖P'.pk (Q * T) τ₀ k (zOf ρ)‖
          ≤ ∑ k ∈ P'.KJ (Q * T) T τ₀, M * P'.L (Q * T) * E / (P'.L (Q * T) * P'.θ * D / 4) ^ A :=
            Finset.sum_le_sum hk
        _ = ((P'.KJ (Q * T) T τ₀).card : ℝ) *
              (M * P'.L (Q * T) * E / (P'.L (Q * T) * P'.θ * D / 4) ^ A) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right (card_KJ_le P' hQT hT0.le τ₀) (by positivity)
    have hsq := pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => norm_nonneg _) hsum 2
    have harith := term_arith (M := M) hT1 hD hL hθ hG hE2 hA1
    calc (mult χ ρ : ℝ) * (∑ k ∈ P'.KJ (Q * T) T τ₀, ‖P'.pk (Q * T) τ₀ k (zOf ρ)‖) ^ 2
        ≤ (mult χ ρ : ℝ) * (K₁ * (D ^ 4)⁻¹) :=
          mul_le_mul_of_nonneg_left (hsq.trans harith) (Nat.cast_nonneg _)
      _ = K₁ * ((mult χ ρ : ℝ) * (D ^ 4)⁻¹) := by ring
  have hnn : ∀ ρ, 0 ≤ extTerm P' (Q * T) T τ₀ χ ρ := fun ρ => by unfold extTerm; positivity
  have hpart : ∀ F : Finset {ρ : ℂ // ρ ∈ PrimeSetup.strip χ ∧ ρ.im ∉ Set.Ioc T (2 * T)},
      ∑ ρ ∈ F, extTerm P' (Q * T) T τ₀ χ ρ ≤ K₁ * (16 * A₀ * (Real.log Q + 3) * S) := by
    intro F
    have hcount := count_sum_le hq hprim (by linarith) (fun t => hloc q χ hq hprim t) hqQ hT1
      (by linarith) (F.map (Function.Embedding.subtype _)) (by
        intro ρ hρ
        rw [Finset.mem_map] at hρ
        obtain ⟨x, _, rfl⟩ := hρ
        exact x.2.1)
    rw [Finset.sum_map] at hcount
    calc ∑ ρ ∈ F, extTerm P' (Q * T) T τ₀ χ ρ
        ≤ ∑ ρ ∈ F, K₁ * ((mult χ ρ : ℝ) * ((T + |(ρ : ℂ).im|) ^ 4)⁻¹) :=
          Finset.sum_le_sum fun ρ _ => hterm ρ
      _ = K₁ * ∑ ρ ∈ F, (mult χ ρ : ℝ) * ((T + |(ρ : ℂ).im|) ^ 4)⁻¹ := by
          rw [Finset.mul_sum]
      _ ≤ K₁ * (16 * A₀ * (Real.log Q + 3) * S) := mul_le_mul_of_nonneg_left hcount hK₁
  have hsumm : Summable (extTerm P' (Q * T) T τ₀ χ) := summable_of_sum_le hnn hpart
  refine ⟨hsumm, (hsumm.tsum_le_of_sum_le hpart).trans ?_⟩
  have hLl : P'.lam * Real.log Q ≤ P'.L (Q * T) := by
    show P'.lam * Real.log Q ≤ P'.lam * Real.log (Q * T)
    apply mul_le_mul_of_nonneg_left _ hlam.le
    exact Real.log_le_log hQ0 (le_mul_of_one_le_right hQ0.le hT1)
  have hL1 : 1 ≤ P'.lam * Real.log Q := by
    have h1 : P'.lam * (1 + 1 / P'.lam) ≤ P'.lam * Real.log Q :=
      mul_le_mul_of_nonneg_left hℓ' hlam.le
    have e : P'.lam * (1 + 1 / P'.lam) = P'.lam + 1 := by field_simp
    linarith
  have hfin := final_arithH (M := M) (A₀ := A₀) (S := S) (B := B) (B₁ := B₁) (A := A)
    hlam P'.θ_pos (by linarith) hS hℓ hL1 hLl hA4 hA2
  rw [hK₁_def]
  exact hfin

end Families.Hybrid.Z
