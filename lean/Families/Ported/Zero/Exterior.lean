/-
# Zero side: the exterior tail for good characters (paper `prop:tail`, Proposition 4.8)

For a primitive `χ` mod `q ∈ (1, Q]` that is not `Bad a B₁ Q` and `T ∈ [ℓ^{a₀}, ℓ^{A₀}]`, the zeros
with ordinate `γ ∉ (T, 2T]` contribute `∑_ρ m_ρ (∑_{k ∈ K_J} ‖p_k(z_ρ)‖)² ≪_B ℓ^{-B}`
(`exterior_tail`). The envelope bound for `\widehat{ψ_L}` is taken as the hypothesis `henv`.

Proof: `|γ − τ_k| ≥ θ(T + |γ|)/4` for `τ_k ∈ J` (`dist_ge`); the envelope with exponent `A` gives
`‖p_k(z_ρ)‖ ≤ C_A L e^{L|δ|/2} (LθD/4)^{-A}`, `D = T + |γ|` (`norm_pk_le`); for good `χ`,
`e^{L|δ|} ≤ ℓ^{2B₁}(1 + |γ|)^{n₀}` with `a n₀ ≥ 2` (`exp_le_good`); `|K_J| ≤ TL + 1`
(`card_KJ_le`); so each term is `≤ K₁ m_ρ D^{-4}` with `K₁ ≪ ℓ^{4 + 2B₁ − 2A}` (`term_arith`), and
the zero count `N_χ(j, j+1] ≤ A₀ log(q(|j|+3))` (`zeta23` `localCountChi_uniform_proof`) gives
`∑_ρ m_ρ D^{-4} ≪ ℓ` on every finite set (`count_sum_le`).
-/
import Families.Ported.Zero.ExplicitFormula

noncomputable section

open scoped BigOperators
open Complex Set

namespace Families.Ported.Zero

open Zeta23 Zeta23.ThmE

/-- the exterior ℓ¹-mass: ∑_{ρ ∈ strip, γ ∉ (T,2T]} m_ρ (∑_{k ∈ K_J} ‖p_k(z_ρ)‖)² -/
def extTerm (P : PrimeSetup) (Q T τ₀ : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (ρ : {ρ : ℂ // ρ ∈ PrimeSetup.strip χ ∧ ρ.im ∉ Set.Ioc T (2 * T)}) : ℝ :=
  (mult χ ρ : ℝ) * (∑ k ∈ P.KJ Q T τ₀, ‖P.pk Q τ₀ k (zOf ρ)‖) ^ 2

/-! ### The lattice `τ_k`, `k ∈ K_J` -/

lemma tau_mem_J (P : PrimeSetup) {Q : ℝ} (hQ : 1 < Q) (T τ₀ : ℝ) {k : ℤ} (hk : k ∈ P.KJ Q T τ₀) :
    (1 + P.θ) * T ≤ tau P Q τ₀ k ∧ tau P Q τ₀ k ≤ (2 - P.θ) * T := by
  have hL := L_pos P hQ
  have hπ := Real.pi_pos
  unfold PrimeSetup.KJ at hk
  rw [Finset.mem_Icc, Int.ceil_le, Int.le_floor] at hk
  obtain ⟨h1, h2⟩ := hk
  rw [div_le_iff₀ (by positivity)] at h1
  rw [le_div_iff₀ (by positivity)] at h2
  unfold tau
  constructor
  · have : (1 + P.θ) * T - τ₀ ≤ 2 * Real.pi * k / P.L Q := by
      rw [le_div_iff₀ hL]; linarith
    linarith
  · have : 2 * Real.pi * k / P.L Q ≤ (2 - P.θ) * T - τ₀ := by
      rw [div_le_iff₀ hL]; linarith
    linarith

/-- `|γ − τ| ≥ θ(T + |γ|)/4` for `τ ∈ J` and `γ ∉ (T, 2T]`. -/
lemma dist_ge {θ T τ γ : ℝ} (hθ : 0 < θ) (hθ' : θ < 1 / 4) (hT : 0 ≤ T)
    (hτ1 : (1 + θ) * T ≤ τ) (hτ2 : τ ≤ (2 - θ) * T) (hγ : γ ∉ Set.Ioc T (2 * T)) :
    θ * (T + |γ|) / 4 ≤ |γ - τ| := by
  rw [Set.mem_Ioc, not_and_or, not_lt, not_le] at hγ
  rcases hγ with hγ | hγ
  · rw [abs_sub_comm]
    refine le_trans ?_ (le_abs_self _)
    rcases le_or_gt 0 γ with h0 | h0
    · rw [abs_of_nonneg h0]
      nlinarith [mul_le_mul_of_nonneg_left hγ hθ.le]
    · rw [abs_of_neg h0]
      nlinarith [mul_le_mul_of_nonneg_left (show (0:ℝ) ≤ T - γ by linarith) hθ.le]
  · have h0 : 0 ≤ γ := by linarith
    rw [abs_of_nonneg h0]
    refine le_trans ?_ (le_abs_self _)
    nlinarith [mul_le_mul_of_nonneg_right (show 0 ≤ γ - 2 * T by linarith)
      (show (0:ℝ) ≤ 1 - θ / 4 by linarith), mul_nonneg hθ.le hT]

/-- `|K_J| ≤ TL + 1`. -/
lemma card_KJ_le (P : PrimeSetup) {Q : ℝ} (hQ : 1 < Q) {T : ℝ} (hT : 0 ≤ T) (τ₀ : ℝ) :
    ((P.KJ Q T τ₀).card : ℝ) ≤ T * P.L Q + 1 := by
  have hL := L_pos P hQ
  have hπ := Real.pi_pos
  have hθ := P.θ_pos
  have hθ' := P.θ_lt
  unfold PrimeSetup.KJ
  rw [Int.card_Icc]
  set x₁ := ((1 + P.θ) * T - τ₀) * P.L Q / (2 * Real.pi)
  set x₂ := ((2 - P.θ) * T - τ₀) * P.L Q / (2 * Real.pi)
  have hTL : 0 ≤ T * P.L Q := by positivity
  by_cases h : 0 ≤ ⌊x₂⌋ + 1 - ⌈x₁⌉
  · have hcast : (((⌊x₂⌋ + 1 - ⌈x₁⌉).toNat : ℕ) : ℝ) = ((⌊x₂⌋ + 1 - ⌈x₁⌉ : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h]
    rw [hcast]
    push_cast
    have hf := Int.floor_le x₂
    have hc := Int.le_ceil x₁
    have hx : x₂ - x₁ ≤ T * P.L Q := by
      have : x₂ - x₁ = (1 - 2 * P.θ) / (2 * Real.pi) * (T * P.L Q) := by
        simp only [x₁, x₂]; field_simp; ring
      rw [this]
      have : (1 - 2 * P.θ) / (2 * Real.pi) ≤ 1 := by
        rw [div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
      nlinarith
    linarith
  · push Not at h
    rw [Int.toNat_eq_zero.mpr h.le]
    simp only [Nat.cast_zero]
    linarith

/-! ### The envelope bound for `p_k` -/

lemma norm_pk_le (P : PrimeSetup) {A : ℕ} {M : ℝ}
    (hM : ∀ Q : ℝ, 1 < Q → ∀ w : ℂ,
      ‖P.hatψL Q w‖ * (1 + P.L Q * |w.re|) ^ A ≤ M * P.L Q * Real.exp (P.L Q * |w.im| / 2))
    {Q : ℝ} (hQ : 1 < Q) (τ₀ : ℝ) (k : ℤ) (z : ℂ) {D : ℝ} (hD : 0 < D)
    (hdist : D ≤ P.L Q * |z.re - tau P Q τ₀ k|) :
    ‖P.pk Q τ₀ k z‖ ≤ M * P.L Q * Real.exp (P.L Q * |z.im| / 2) / D ^ A := by
  rw [pk_eq]
  have h := hM Q hQ (z - (tau P Q τ₀ k : ℂ))
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero] at h
  rw [le_div_iff₀ (pow_pos hD A)]
  refine le_trans ?_ h
  gcongr
  linarith

/-! ### Good characters: `e^{L|δ|} ≤ ℓ^{2B₁} (1 + |γ|)^{n₀}` -/

/-- For `χ` not bad and a zero `ρ = 1/2 + δ + iγ` in the strip: `e^{L|δ|} ≤ ℓ^{2B₁}(1 + |γ|)^{n₀}`
whenever `a n₀ ≥ 2` (if `|δ| < δ₀`: `e^{L|δ|} ≤ e^{λℓδ₀} = ℓ^{λB₁}`; if `|δ| ≥ δ₀`:
`|γ| > Q^{a|δ|}`, so `e^{L|δ|} ≤ (Q^{a|δ|})^{n₀} ≤ |γ|^{n₀}`). -/
lemma exp_le_good (P : PrimeSetup) {a B₁ Q : ℝ} (hB₁ : 0 ≤ B₁) (hQ : 1 < Q)
    (hℓ : 1 ≤ Real.log Q) {n₀ : ℕ} (hn₀ : 2 ≤ a * n₀) {q : ℕ} {χ : DirichletCharacter ℂ q}
    (hgood : ¬ Bad a B₁ Q χ) {ρ : ℂ} (hρ : ρ ∈ PrimeSetup.strip χ) :
    Real.exp (P.L Q * |ρ.re - 1 / 2|) ≤ Real.log Q ^ (2 * B₁) * (1 + |ρ.im|) ^ n₀ := by
  have hQ0 : 0 < Q := by linarith
  have hℓ0 : 0 < Real.log Q := by linarith
  have hlam := P.lam_pos
  have hlam2 := P.lam_lt
  have hG : 1 ≤ Real.log Q ^ (2 * B₁) := Real.one_le_rpow hℓ (by linarith)
  have hH : 1 ≤ (1 + |ρ.im|) ^ n₀ := one_le_pow₀ (by linarith [abs_nonneg ρ.im])
  set δ := |ρ.re - 1 / 2| with hδ
  have hδ0 : 0 ≤ δ := abs_nonneg _
  by_cases h : delta0 B₁ Q ≤ δ
  · have hlt : Q ^ (a * δ) < |ρ.im| := by
      by_contra hc
      push Not at hc
      exact hgood ⟨ρ, hρ.1, hρ.2.1, hρ.2.2, h, hc⟩
    have h1 : Real.exp (P.L Q * δ) ≤ (Q ^ (a * δ)) ^ n₀ := by
      rw [Real.rpow_def_of_pos hQ0, ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      unfold PrimeSetup.L
      have : P.lam * (Real.log Q * δ) ≤ (a * n₀) * (Real.log Q * δ) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      nlinarith
    have h2 : (Q ^ (a * δ)) ^ n₀ ≤ (1 + |ρ.im|) ^ n₀ :=
      pow_le_pow_left₀ (Real.rpow_pos_of_pos hQ0 _).le (by linarith) n₀
    calc Real.exp (P.L Q * δ) ≤ (1 + |ρ.im|) ^ n₀ := h1.trans h2
      _ ≤ Real.log Q ^ (2 * B₁) * (1 + |ρ.im|) ^ n₀ := by
        nlinarith
  · push Not at h
    have h1 : Real.exp (P.L Q * δ) ≤ Real.log Q ^ (2 * B₁) := by
      rw [Real.rpow_def_of_pos hℓ0]
      apply Real.exp_le_exp.mpr
      have hd : Real.log Q * delta0 B₁ Q = B₁ * Real.log (Real.log Q) := by
        unfold delta0; field_simp
      have hll : 0 ≤ Real.log (Real.log Q) := Real.log_nonneg hℓ
      unfold PrimeSetup.L
      have : Real.log Q * δ ≤ Real.log Q * delta0 B₁ Q :=
        mul_le_mul_of_nonneg_left h.le hℓ0.le
      rw [hd] at this
      have h3 : P.lam * (Real.log Q * δ) ≤ P.lam * (B₁ * Real.log (Real.log Q)) :=
        mul_le_mul_of_nonneg_left this hlam.le
      have h4 : P.lam * (B₁ * Real.log (Real.log Q)) ≤ 2 * (B₁ * Real.log (Real.log Q)) :=
        mul_le_mul_of_nonneg_right hlam2.le (by positivity)
      nlinarith
    nlinarith

/-! ### Real arithmetic -/

/-- The per-zero bound, as pure real arithmetic. -/
lemma term_arith {T L M E G D θ : ℝ} {n₀ A : ℕ} (hT : 1 ≤ T) (hD : T ≤ D) (hL : 0 < L)
    (hθ : 0 < θ) (hG : 0 ≤ G) (hE2 : E ^ 2 ≤ G * D ^ n₀)
    (hA : n₀ + 6 ≤ 2 * A) :
    ((T * L + 1) * (M * L * E / (L * θ * D / 4) ^ A)) ^ 2 ≤
      (L + 1) ^ 2 * M ^ 2 * L ^ 2 * G * (4 / (L * θ)) ^ (2 * A) * (D ^ 4)⁻¹ := by
  have hD0 : 0 < D := by linarith
  have hD1 : 1 ≤ D := by linarith
  have e1 : ((T * L + 1) * (M * L * E / (L * θ * D / 4) ^ A)) ^ 2 =
      (T * L + 1) ^ 2 * M ^ 2 * L ^ 2 * E ^ 2 * (4 / (L * θ)) ^ (2 * A) * (D ^ (2 * A))⁻¹ := by
    have h4 : L * θ * D / 4 = (4 / (L * θ))⁻¹ * D := by field_simp
    have h5 : M * L * E / (L * θ * D / 4) ^ A = M * L * E * (4 / (L * θ)) ^ A * (D ^ A)⁻¹ := by
      rw [div_eq_mul_inv, h4, mul_pow, mul_inv, inv_pow, inv_inv]
      ring
    rw [h5]
    generalize (4 / (L * θ)) = u
    ring
  rw [e1]
  have hTL : T * L + 1 ≤ D * (L + 1) := by nlinarith
  have hpow : D ^ (n₀ + 6) ≤ D ^ (2 * A) := pow_le_pow_right₀ hD1 hA
  have hkey : (T * L + 1) ^ 2 * E ^ 2 * (D ^ (2 * A))⁻¹ ≤ (L + 1) ^ 2 * G * (D ^ 4)⁻¹ := by
    rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    calc (T * L + 1) ^ 2 * E ^ 2 ≤ (D * (L + 1)) ^ 2 * (G * D ^ n₀) := by
          gcongr
      _ = (L + 1) ^ 2 * G * (D ^ 4)⁻¹ * D ^ (n₀ + 6) := by
          field_simp
          ring
      _ ≤ (L + 1) ^ 2 * G * (D ^ 4)⁻¹ * D ^ (2 * A) := by gcongr
  calc (T * L + 1) ^ 2 * M ^ 2 * L ^ 2 * E ^ 2 * (4 / (L * θ)) ^ (2 * A) * (D ^ (2 * A))⁻¹
      = M ^ 2 * L ^ 2 * (4 / (L * θ)) ^ (2 * A) *
          ((T * L + 1) ^ 2 * E ^ 2 * (D ^ (2 * A))⁻¹) := by ring
    _ ≤ M ^ 2 * L ^ 2 * (4 / (L * θ)) ^ (2 * A) * ((L + 1) ^ 2 * G * (D ^ 4)⁻¹) := by
        gcongr
    _ = _ := by ring

/-- The final bound in `ℓ`. -/
lemma final_arith {lam θ M A₀ S ℓ B B₁ : ℝ} {A : ℕ} (hlam : 0 < lam) (hθ : 0 < θ)
    (hA₀ : 0 ≤ A₀) (hS : 0 ≤ S) (hℓ : 1 ≤ ℓ) (hA : 5 + 2 * B₁ + B ≤ 2 * (A : ℝ)) :
    (lam * ℓ + 1) ^ 2 * M ^ 2 * (lam * ℓ) ^ 2 * ℓ ^ (2 * B₁) * (4 / (lam * ℓ * θ)) ^ (2 * A) *
        (16 * A₀ * (ℓ + 3) * S) ≤
      ((lam + 1) ^ 2 * M ^ 2 * lam ^ 2 * (4 / (lam * θ)) ^ (2 * A) * 64 * A₀ * S) * ℓ ^ (-B) := by
  have hℓ0 : 0 < ℓ := by linarith
  have e1 : (4 / (lam * ℓ * θ)) ^ (2 * A) = (4 / (lam * θ)) ^ (2 * A) * (ℓ ^ (2 * A))⁻¹ := by
    rw [← inv_pow, ← mul_pow]
    congr 1
    field_simp
  rw [e1]
  have h1 : lam * ℓ + 1 ≤ (lam + 1) * ℓ := by nlinarith
  have h2 : ℓ + 3 ≤ 4 * ℓ := by linarith
  have hpow : ℓ ^ (5 : ℕ) * ℓ ^ (2 * B₁) * (ℓ ^ (2 * A))⁻¹ ≤ ℓ ^ (-B) := by
    rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_neg hℓ0.le,
      ← Real.rpow_add hℓ0, ← Real.rpow_add hℓ0]
    apply Real.rpow_le_rpow_of_exponent_le hℓ
    push_cast
    linarith
  calc (lam * ℓ + 1) ^ 2 * M ^ 2 * (lam * ℓ) ^ 2 * ℓ ^ (2 * B₁) *
        ((4 / (lam * θ)) ^ (2 * A) * (ℓ ^ (2 * A))⁻¹) * (16 * A₀ * (ℓ + 3) * S)
      ≤ ((lam + 1) * ℓ) ^ 2 * M ^ 2 * (lam * ℓ) ^ 2 * ℓ ^ (2 * B₁) *
        ((4 / (lam * θ)) ^ (2 * A) * (ℓ ^ (2 * A))⁻¹) * (16 * A₀ * (4 * ℓ) * S) := by
        gcongr
    _ = ((lam + 1) ^ 2 * M ^ 2 * lam ^ 2 * (4 / (lam * θ)) ^ (2 * A) * 64 * A₀ * S) *
          (ℓ ^ (5 : ℕ) * ℓ ^ (2 * B₁) * (ℓ ^ (2 * A))⁻¹) := by ring
    _ ≤ _ := by gcongr

/-! ### Counting the zeros -/

/-- `∑_{j ∈ ℤ} (1 + |j|)^{-3} < ∞`. -/
lemma summable_weight : Summable (fun j : ℤ => ((1 + |(j : ℝ)|) ^ 3)⁻¹) := by
  have h := (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ 3)⁻¹) 1).mpr
    (Real.summable_nat_pow_inv.mpr (by norm_num))
  apply Summable.of_nat_of_neg
  · refine h.congr fun n => ?_
    simp only [Int.cast_natCast, Nat.cast_add, Nat.cast_one]
    rw [abs_of_nonneg (Nat.cast_nonneg n), add_comm]
  · refine h.congr fun n => ?_
    simp only [Int.cast_neg, Int.cast_natCast, abs_neg, Nat.cast_add, Nat.cast_one]
    rw [abs_of_nonneg (Nat.cast_nonneg n), add_comm]

/-- For `j < γ ≤ j + 1` and `T ≥ 1`: `(T + |γ|)^{-4} ≤ 16 (1 + |j|)^{-4}`. -/
lemma weight_le {T γ : ℝ} {j : ℤ} (hT : 1 ≤ T) (h1 : (j : ℝ) < γ) (h2 : γ ≤ j + 1) :
    ((T + |γ|) ^ 4)⁻¹ ≤ 16 * ((1 + |(j : ℝ)|) ^ 4)⁻¹ := by
  have hD : (1 + |(j : ℝ)|) / 2 ≤ T + |γ| := by
    rcases le_or_gt 0 j with hj | hj
    · have : (0 : ℝ) ≤ j := by exact_mod_cast hj
      rw [abs_of_nonneg this, abs_of_pos (by linarith)]
      linarith
    · have : (j : ℝ) ≤ -1 := by exact_mod_cast (show j ≤ -1 by omega)
      rw [abs_of_neg (by linarith), abs_of_nonpos (by linarith)]
      linarith
  have hpos : 0 < (1 + |(j : ℝ)|) / 2 := by positivity
  calc ((T + |γ|) ^ 4)⁻¹ ≤ (((1 + |(j : ℝ)|) / 2) ^ 4)⁻¹ :=
        inv_anti₀ (by positivity) (pow_le_pow_left₀ hpos.le hD 4)
    _ = 16 * ((1 + |(j : ℝ)|) ^ 4)⁻¹ := by
        rw [div_pow, inv_div]
        field_simp
        norm_num

/-- The zero count: for a finite set `F` of nontrivial zeros of `L(s,χ)`,
`∑_{ρ ∈ F} m_ρ (T + |γ|)^{-4} ≤ 16 A₀ (ℓ + 3) ∑_{j ∈ ℤ} (1 + |j|)^{-3}` (group the zeros by
`j = ⌈γ⌉ − 1`, i.e. `γ ∈ (j, j+1]`, and use the local count `N_χ(j, j+1] ≤ A₀ log(q(|j|+3))`). -/
lemma count_sum_le {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hq : 1 < q)
    (hprim : χ.IsPrimitive) {A₀ : ℝ} (hA₀ : 0 ≤ A₀)
    (hloc : ∀ t : ℝ, (NcountL χ t (t + 1) : ℝ) ≤ A₀ * Real.log (q * (|t| + 3)))
    {Q T : ℝ} (hqQ : (q : ℝ) ≤ Q) (hT : 1 ≤ T) (hℓ : 0 ≤ Real.log Q) (F : Finset ℂ)
    (hF : ∀ ρ ∈ F, ρ ∈ PrimeSetup.strip χ) :
    ∑ ρ ∈ F, (mult χ ρ : ℝ) * ((T + |ρ.im|) ^ 4)⁻¹ ≤
      16 * A₀ * (Real.log Q + 3) * ∑' j : ℤ, ((1 + |(j : ℝ)|) ^ 3)⁻¹ := by
  classical
  set key : ℂ → ℤ := fun ρ => ⌈ρ.im⌉ - 1 with hkey_def
  have hkey : ∀ ρ : ℂ, ((key ρ : ℤ) : ℝ) < ρ.im ∧ ρ.im ≤ (key ρ : ℝ) + 1 := by
    intro ρ
    simp only [hkey_def]
    push_cast
    exact ⟨by linarith [Int.ceil_lt_add_one ρ.im], by linarith [Int.le_ceil ρ.im]⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  -- the local count on each unit window
  have hwin : ∀ j : ℤ, ∑ ρ ∈ F with key ρ = j, (mult χ ρ : ℝ) ≤
      A₀ * (Real.log Q + 3) * (1 + |(j : ℝ)|) := by
    intro j
    have hfin : (zerosInL χ j (j + 1)).Finite :=
      ((LSeam_of hq hprim).finite_window j (j + 1)).subset fun ρ hρ => ⟨hρ.1, hρ.2.1, hρ.2.2⟩
    have h1 : ∑ ρ ∈ F with key ρ = j, mult χ ρ ≤ NcountL χ j (j + 1) := by
      unfold NcountL
      rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
      simp_rw [mult_eq]
      apply Finset.sum_le_sum_of_subset
      intro ρ hρ
      rw [Finset.mem_filter] at hρ
      rw [Set.Finite.mem_toFinset]
      obtain ⟨hρF, hρj⟩ := hρ
      have hk := hkey ρ
      rw [hρj] at hk
      have hs := hF ρ hρF
      rw [strip_eq] at hs
      exact ⟨hs, hk.1, hk.2⟩
    have h1' : ∑ ρ ∈ F with key ρ = j, (mult χ ρ : ℝ) ≤ (NcountL χ j (j + 1) : ℝ) := by
      exact_mod_cast h1
    have h2 := hloc j
    have h3 : Real.log (q * (|(j : ℝ)| + 3)) ≤ (Real.log Q + 3) * (1 + |(j : ℝ)|) := by
      have hj0 := abs_nonneg (j : ℝ)
      rw [Real.log_mul hq0.ne' (by positivity)]
      have h4 : Real.log q ≤ Real.log Q := Real.log_le_log hq0 hqQ
      have h5 := Real.log_le_sub_one_of_pos (show 0 < |(j : ℝ)| + 3 by positivity)
      nlinarith
    calc ∑ ρ ∈ F with key ρ = j, (mult χ ρ : ℝ) ≤ A₀ * Real.log (q * (|(j : ℝ)| + 3)) :=
          h1'.trans h2
      _ ≤ A₀ * ((Real.log Q + 3) * (1 + |(j : ℝ)|)) := mul_le_mul_of_nonneg_left h3 hA₀
      _ = _ := by ring
  calc ∑ ρ ∈ F, (mult χ ρ : ℝ) * ((T + |ρ.im|) ^ 4)⁻¹
      = ∑ j ∈ F.image key, ∑ ρ ∈ F with key ρ = j, (mult χ ρ : ℝ) * ((T + |ρ.im|) ^ 4)⁻¹ :=
        (Finset.sum_fiberwise_of_maps_to (fun ρ hρ => Finset.mem_image_of_mem key hρ) _).symm
    _ ≤ ∑ j ∈ F.image key, 16 * A₀ * (Real.log Q + 3) * ((1 + |(j : ℝ)|) ^ 3)⁻¹ := by
        apply Finset.sum_le_sum
        intro j _
        calc ∑ ρ ∈ F with key ρ = j, (mult χ ρ : ℝ) * ((T + |ρ.im|) ^ 4)⁻¹
            ≤ ∑ ρ ∈ F with key ρ = j, (mult χ ρ : ℝ) * (16 * ((1 + |(j : ℝ)|) ^ 4)⁻¹) := by
              apply Finset.sum_le_sum
              intro ρ hρ
              rw [Finset.mem_filter] at hρ
              apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
              have hk := hkey ρ
              rw [hρ.2] at hk
              exact weight_le hT hk.1 hk.2
          _ = (∑ ρ ∈ F with key ρ = j, (mult χ ρ : ℝ)) * (16 * ((1 + |(j : ℝ)|) ^ 4)⁻¹) :=
              (Finset.sum_mul _ _ _).symm
          _ ≤ (A₀ * (Real.log Q + 3) * (1 + |(j : ℝ)|)) * (16 * ((1 + |(j : ℝ)|) ^ 4)⁻¹) :=
              mul_le_mul_of_nonneg_right (hwin j) (by positivity)
          _ = 16 * A₀ * (Real.log Q + 3) * ((1 + |(j : ℝ)|) ^ 3)⁻¹ := by
              have : (0 : ℝ) < 1 + |(j : ℝ)| := by positivity
              field_simp
    _ = 16 * A₀ * (Real.log Q + 3) * ∑ j ∈ F.image key, ((1 + |(j : ℝ)|) ^ 3)⁻¹ :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact summable_weight.sum_le_tsum _ (fun _ _ => by positivity)

theorem exterior_tail (P : PrimeSetup) (τ₀ a B₁ : ℝ) (ha : 0 < a) (hB₁ : 0 < B₁)
    (henv : ∀ A : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ Q : ℝ, 1 < Q → ∀ w : ℂ,
      ‖P.hatψL Q w‖ * (1 + P.L Q * |w.re|) ^ A ≤ C * P.L Q * Real.exp (P.L Q * |w.im| / 2))
    (B : ℝ) : ∃ C Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ P.heights Q, ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      1 < q → (q : ℝ) ≤ Q → χ.IsPrimitive → ¬ Bad a B₁ Q χ →
      Summable (extTerm P Q T τ₀ χ) ∧ ∑' ρ, extTerm P Q T τ₀ χ ρ ≤ C * Real.log Q ^ (-B) := by
  obtain ⟨A₀, hA₀1, hloc⟩ := localCountChi_uniform_proof
  set n₀ : ℕ := ⌈2 / a⌉₊ with hn₀_def
  have hn₀ : 2 ≤ a * n₀ := by
    have := Nat.le_ceil (2 / a)
    rw [div_le_iff₀ ha] at this
    linarith
  set A : ℕ := n₀ + 6 + ⌈B + 2 * B₁⌉₊ with hA_def
  have hA1 : n₀ + 6 ≤ 2 * A := by omega
  have hA2 : 5 + 2 * B₁ + B ≤ 2 * (A : ℝ) := by
    have h1 := Nat.le_ceil (B + 2 * B₁)
    have h2 : (A : ℝ) = n₀ + 6 + ⌈B + 2 * B₁⌉₊ := by simp [hA_def]
    have h3 : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg _
    linarith
  obtain ⟨M, hM0, hM⟩ := henv A
  set S := ∑' j : ℤ, ((1 + |(j : ℝ)|) ^ 3)⁻¹ with hS_def
  have hS : 0 ≤ S := tsum_nonneg fun _ => by positivity
  refine ⟨(P.lam + 1) ^ 2 * M ^ 2 * P.lam ^ 2 * (4 / (P.lam * P.θ)) ^ (2 * A) * 64 * A₀ * S,
    Real.exp 1, ?_⟩
  intro Q hQ T hT q χ hq hqQ hprim hgood
  have : NeZero q := ⟨by omega⟩
  have hQ1 : 1 < Q := by
    have := Real.add_one_lt_exp (one_ne_zero (α := ℝ))
    linarith
  have hℓ : 1 ≤ Real.log Q := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hQ
  have hT1 : 1 ≤ T := le_trans (Real.one_le_rpow hℓ P.a0_pos.le) hT.1
  have hL : 0 < P.L Q := L_pos P hQ1
  have hθ := P.θ_pos
  have hG : 0 ≤ Real.log Q ^ (2 * B₁) := Real.rpow_nonneg (by linarith) _
  set K₁ := (P.L Q + 1) ^ 2 * M ^ 2 * P.L Q ^ 2 * Real.log Q ^ (2 * B₁) *
    (4 / (P.L Q * P.θ)) ^ (2 * A) with hK₁_def
  have hK₁ : 0 ≤ K₁ := mul_nonneg (mul_nonneg (by positivity) hG) (by positivity)
  -- the per-zero bound
  have hterm : ∀ ρ, extTerm P Q T τ₀ χ ρ ≤
      K₁ * ((mult χ ρ : ℝ) * ((T + |(ρ : ℂ).im|) ^ 4)⁻¹) := by
    rintro ⟨ρ, hρs, hρI⟩
    show (mult χ ρ : ℝ) * (∑ k ∈ P.KJ Q T τ₀, ‖P.pk Q τ₀ k (zOf ρ)‖) ^ 2 ≤
      K₁ * ((mult χ ρ : ℝ) * ((T + |ρ.im|) ^ 4)⁻¹)
    set D := T + |ρ.im| with hD_def
    have hD : T ≤ D := le_add_of_nonneg_right (abs_nonneg _)
    have hD0 : 0 < D := by linarith
    set E := Real.exp (P.L Q * |ρ.re - 1 / 2| / 2) with hE_def
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    have hE2 : E ^ 2 ≤ Real.log Q ^ (2 * B₁) * D ^ n₀ := by
      have h1 : E ^ 2 = Real.exp (P.L Q * |ρ.re - 1 / 2|) := by
        rw [hE_def, sq, ← Real.exp_add]
        ring_nf
      rw [h1]
      refine (exp_le_good P hB₁.le hQ1 hℓ hn₀ hgood hρs).trans ?_
      apply mul_le_mul_of_nonneg_left _ hG
      exact pow_le_pow_left₀ (by positivity) (by linarith) n₀
    have hk : ∀ k ∈ P.KJ Q T τ₀,
        ‖P.pk Q τ₀ k (zOf ρ)‖ ≤ M * P.L Q * E / (P.L Q * P.θ * D / 4) ^ A := by
      intro k hk
      obtain ⟨h1, h2⟩ := tau_mem_J P hQ1 T τ₀ hk
      have hdist := dist_ge P.θ_pos P.θ_lt (by linarith) h1 h2 hρI
      have hdist' : P.L Q * P.θ * D / 4 ≤ P.L Q * |(zOf ρ).re - tau P Q τ₀ k| := by
        rw [zOf_re]
        calc P.L Q * P.θ * D / 4 = P.L Q * (P.θ * (T + |ρ.im|) / 4) := by rw [hD_def]; ring
          _ ≤ P.L Q * |ρ.im - tau P Q τ₀ k| := mul_le_mul_of_nonneg_left hdist hL.le
      have := norm_pk_le P hM hQ1 τ₀ k (zOf ρ) (by positivity) hdist'
      rwa [zOf_im, abs_neg] at this
    have hsum : ∑ k ∈ P.KJ Q T τ₀, ‖P.pk Q τ₀ k (zOf ρ)‖ ≤
        (T * P.L Q + 1) * (M * P.L Q * E / (P.L Q * P.θ * D / 4) ^ A) := by
      calc ∑ k ∈ P.KJ Q T τ₀, ‖P.pk Q τ₀ k (zOf ρ)‖
          ≤ ∑ k ∈ P.KJ Q T τ₀, M * P.L Q * E / (P.L Q * P.θ * D / 4) ^ A := Finset.sum_le_sum hk
        _ = ((P.KJ Q T τ₀).card : ℝ) * (M * P.L Q * E / (P.L Q * P.θ * D / 4) ^ A) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right (card_KJ_le P hQ1 (by linarith) τ₀) (by positivity)
    have hsq := pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => norm_nonneg _) hsum 2
    have harith := term_arith (M := M) hT1 hD hL hθ hG hE2 hA1
    calc (mult χ ρ : ℝ) * (∑ k ∈ P.KJ Q T τ₀, ‖P.pk Q τ₀ k (zOf ρ)‖) ^ 2
        ≤ (mult χ ρ : ℝ) * (K₁ * (D ^ 4)⁻¹) :=
          mul_le_mul_of_nonneg_left (hsq.trans harith) (Nat.cast_nonneg _)
      _ = K₁ * ((mult χ ρ : ℝ) * (D ^ 4)⁻¹) := by ring
  have hnn : ∀ ρ, 0 ≤ extTerm P Q T τ₀ χ ρ := fun ρ => by unfold extTerm; positivity
  have hpart : ∀ F : Finset {ρ : ℂ // ρ ∈ PrimeSetup.strip χ ∧ ρ.im ∉ Set.Ioc T (2 * T)},
      ∑ ρ ∈ F, extTerm P Q T τ₀ χ ρ ≤ K₁ * (16 * A₀ * (Real.log Q + 3) * S) := by
    intro F
    have hcount := count_sum_le hq hprim (by linarith) (fun t => hloc q χ hq hprim t) hqQ hT1
      (by linarith) (F.map (Function.Embedding.subtype _)) (by
        intro ρ hρ
        rw [Finset.mem_map] at hρ
        obtain ⟨x, _, rfl⟩ := hρ
        exact x.2.1)
    rw [Finset.sum_map] at hcount
    calc ∑ ρ ∈ F, extTerm P Q T τ₀ χ ρ
        ≤ ∑ ρ ∈ F, K₁ * ((mult χ ρ : ℝ) * ((T + |(ρ : ℂ).im|) ^ 4)⁻¹) :=
          Finset.sum_le_sum fun ρ _ => hterm ρ
      _ = K₁ * ∑ ρ ∈ F, (mult χ ρ : ℝ) * ((T + |(ρ : ℂ).im|) ^ 4)⁻¹ := by
          rw [Finset.mul_sum]
      _ ≤ K₁ * (16 * A₀ * (Real.log Q + 3) * S) := mul_le_mul_of_nonneg_left hcount hK₁
  have hsumm : Summable (extTerm P Q T τ₀ χ) := summable_of_sum_le hnn hpart
  refine ⟨hsumm, (hsumm.tsum_le_of_sum_le hpart).trans ?_⟩
  have hfin := final_arith (lam := P.lam) (θ := P.θ) (M := M) (A₀ := A₀) (S := S)
    (ℓ := Real.log Q) (B := B) (B₁ := B₁) (A := A) P.lam_pos P.θ_pos (by linarith) hS hℓ hA2
  rw [hK₁_def]
  simp only [PrimeSetup.L]
  exact hfin

end Families.Ported.Zero
