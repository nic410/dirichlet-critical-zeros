/-
# Zero side: the trace, per character (`prop:trace`, lower bound)

For primitive `χ` mod `q > 1` and a lattice point `τ_k`:

* `gabor_diag_re`: `Re G_{χ,kk} = ∫ ‖p_k‖² μ_χ + ∫ ‖p_k‖² P_χ` (explicit formula, `ν = μ + P`);
* `main_term_lower`: `∫ ‖p_k‖² μ_χ ≥ m₁ · 2π a L − (m₁+1) · 2πC²/L²` whenever `μ_χ ≥ m₁` on
  `[τ_k − 1, τ_k + 1]`, `μ_χ ≥ −1` everywhere and `C` is the envelope constant (`A = 2`).

The paper computes the trace through `lem:gabor` and `eq:fc1`; for the lower bound needed in
`prop:zero` it suffices to use, for each `k`, `∫ p_k² = 2π a L` (`integral_normSq_pk`) and that `μ_χ`
is `≈ ℓ/2π` near `τ_k` and `≥ −1` everywhere.
-/
import Families.Ported.Zero.Envelope
import Families.Ported.Zero.FirstMoment

noncomputable section

open scoped BigOperators ComplexConjugate
open Complex Set MeasureTheory Filter Topology

namespace Families.Ported.Zero

open Zeta23 Zeta23.ThmE

/-- `μ_χ(t) = (1/2π)(log(q/π) + Re ψ(1/4 + 𝔞/2 + it/2))` (paper `eq:mu`; `zeta23`'s `muq`). -/
def muChi {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) : ℝ := muq (parity χ) q t

lemma nuChi_eq (P : PrimeSetup) (Q : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) :
    nuChi P Q χ t = muChi χ t + Pch (P.X Q) χ t := rfl

lemma continuous_Pch (X : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) : Continuous (Pch X χ) := by
  unfold Pch
  refine continuous_const.mul (Complex.continuous_re.comp ?_)
  refine continuous_finsetSum _ fun n hn => ?_
  refine continuous_const.mul ?_
  have hn0 : (n : ℂ) ≠ 0 := by
    have := (Finset.mem_Ioc.mp hn).1
    exact_mod_cast this.ne'
  exact Continuous.const_cpow (by fun_prop) (Or.inl hn0)

lemma abs_Pch_le (X : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) :
    |Pch X χ t| ≤ 1 / Real.pi * ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
      ArithmeticFunction.vonMangoldt n / Real.sqrt n := by
  unfold Pch
  rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 1 / Real.pi)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_))
  have hn0 : 0 < n := (Finset.mem_Ioc.mp hn).1
  rw [norm_mul, norm_mul, norm_natCast_cpow n hn0 t, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  have := χ.norm_le_one (n : ZMod q)
  have h1 : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
  calc ArithmeticFunction.vonMangoldt n * ‖χ (n : ZMod q)‖ * (1 / Real.sqrt n)
      ≤ ArithmeticFunction.vonMangoldt n * 1 * (1 / Real.sqrt n) := by gcongr
    _ = _ := by ring

variable (P : PrimeSetup)

lemma pk_mul_self (Q τ₀ : ℝ) (k : ℤ) (t : ℝ) :
    P.pk Q τ₀ k t * P.pk Q τ₀ k t = ((‖P.pk Q τ₀ k t‖ ^ 2 : ℝ) : ℂ) := by
  have him := pk_ofReal_im P Q τ₀ k t
  set z := P.pk Q τ₀ k t
  have hz : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [him])
  rw [hz, ← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs, sq]

lemma integrable_normSq_mul_Pch {Q : ℝ} (hQ : 1 < Q) (τ₀ : ℝ) (k : ℤ) (X : ℝ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    Integrable (fun t : ℝ => ‖P.pk Q τ₀ k t‖ ^ 2 * Pch X χ t) := by
  have h := (integrable_normSq_pk P hQ τ₀ k).mul_bdd (c := 1 / Real.pi * ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
      ArithmeticFunction.vonMangoldt n / Real.sqrt n)
    (continuous_Pch X χ).aestronglyMeasurable
    (Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact abs_Pch_le X χ t)
  exact h

lemma integrable_normSq_mul_mu {Q : ℝ} (hQ : 1 < Q) (τ₀ : ℝ) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 1 < q) (hprim : χ.IsPrimitive) (k : ℤ) :
    Integrable (fun t : ℝ => ‖P.pk Q τ₀ k t‖ ^ 2 * muChi χ t) := by
  obtain ⟨-, hint, -⟩ := gabor_eq_integral P hQ τ₀ hq hprim k k
  have hfun : (fun t : ℝ => P.pk Q τ₀ k t * P.pk Q τ₀ k t * (nuChi P Q χ t : ℂ)) =
      fun t : ℝ => ((‖P.pk Q τ₀ k t‖ ^ 2 * nuChi P Q χ t : ℝ) : ℂ) := by
    funext t; rw [pk_mul_self, Complex.ofReal_mul]
  rw [hfun] at hint
  have hintR : Integrable (fun t : ℝ => ‖P.pk Q τ₀ k t‖ ^ 2 * nuChi P Q χ t) :=
    hint.re.congr (Eventually.of_forall fun t => Complex.ofReal_re _)
  have hP := integrable_normSq_mul_Pch P hQ τ₀ k (P.X Q) χ
  refine (hintR.sub hP).congr (Eventually.of_forall fun t => ?_)
  simp only [Pi.sub_apply, nuChi_eq]; ring

/-- `Re G_{χ,kk} = ∫ ‖p_k‖² μ_χ + ∫ ‖p_k‖² P_χ`. -/
lemma gabor_diag_re {Q : ℝ} (hQ : 1 < Q) (τ₀ : ℝ) {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : 1 < q) (hprim : χ.IsPrimitive) (k : ℤ) :
    (∑' ρ : PrimeSetup.strip χ, gaborTerm P Q τ₀ χ k k ρ).re =
      (∫ t : ℝ, ‖P.pk Q τ₀ k t‖ ^ 2 * muChi χ t) +
        ∫ t : ℝ, ‖P.pk Q τ₀ k t‖ ^ 2 * Pch (P.X Q) χ t := by
  obtain ⟨-, hint, heq⟩ := gabor_eq_integral P hQ τ₀ hq hprim k k
  have hfun : (fun t : ℝ => P.pk Q τ₀ k t * P.pk Q τ₀ k t * (nuChi P Q χ t : ℂ)) =
      fun t : ℝ => ((‖P.pk Q τ₀ k t‖ ^ 2 * nuChi P Q χ t : ℝ) : ℂ) := by
    funext t; rw [pk_mul_self, Complex.ofReal_mul]
  rw [heq, hfun, integral_complex_ofReal, Complex.ofReal_re]
  rw [hfun] at hint
  have hintR : Integrable (fun t : ℝ => ‖P.pk Q τ₀ k t‖ ^ 2 * nuChi P Q χ t) := by
    exact hint.re.congr (Eventually.of_forall fun t => Complex.ofReal_re _)
  have hP := integrable_normSq_mul_Pch P hQ τ₀ k (P.X Q) χ
  have hμ : Integrable (fun t : ℝ => ‖P.pk Q τ₀ k t‖ ^ 2 * muChi χ t) := by
    refine (hintR.sub hP).congr (Eventually.of_forall fun t => ?_)
    simp only [Pi.sub_apply, nuChi_eq]; ring
  rw [← integral_add hμ hP]
  congr 1; funext t; rw [nuChi_eq]; ring

/-- The main term, per lattice point. -/
lemma main_term_lower {Q : ℝ} (hQ : 1 < Q) (τ₀ : ℝ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (k : ℤ) {C m₁ : ℝ} (hC : ∀ w : ℝ, ‖P.hatψL Q w‖ * (1 + P.L Q * |w|) ^ 2 ≤ C * P.L Q)
    (hm₁ : ∀ t : ℝ, |t - tau P Q τ₀ k| ≤ 1 → m₁ ≤ muChi χ t) (hm₁' : 0 ≤ m₁ + 1)
    (hμ : ∀ t : ℝ, -1 ≤ muChi χ t)
    (hint : Integrable (fun t : ℝ => ‖P.pk Q τ₀ k t‖ ^ 2 * muChi χ t)) :
    m₁ * (2 * Real.pi * P.aInt * P.L Q) - (m₁ + 1) * (2 * C ^ 2 / P.L Q ^ 2 * Real.pi) ≤
      ∫ t : ℝ, ‖P.pk Q τ₀ k t‖ ^ 2 * muChi χ t := by
  have hL := L_pos P hQ
  set c := tau P Q τ₀ k
  set B : ℝ := 2 * C ^ 2 / P.L Q ^ 2
  have hpk : ∀ t : ℝ, ‖P.pk Q τ₀ k t‖ = ‖P.hatψL Q ((t - c : ℝ) : ℂ)‖ := by
    intro t; rw [pk_eq]; push_cast; rfl
  -- far-field bound
  have hfar : ∀ t : ℝ, 1 < |t - c| → ‖P.pk Q τ₀ k t‖ ^ 2 ≤ B * (1 + (t - c) ^ 2)⁻¹ := by
    intro t ht
    rw [hpk]
    set w := t - c
    have hw1 : 1 ≤ w ^ 2 := by nlinarith [sq_abs w, abs_nonneg w]
    have h1 := hC w
    have hnn := norm_nonneg (P.hatψL Q (w : ℂ))
    have hLw : P.L Q * |w| ≤ 1 + P.L Q * |w| := by linarith
    have hLw0 : 0 < P.L Q * |w| := by positivity
    have h2 : ‖P.hatψL Q (w : ℂ)‖ * (P.L Q * |w|) ^ 2 ≤ C * P.L Q :=
      le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hLw0.le hLw 2) hnn) h1
    have hC0 : 0 ≤ C * P.L Q := le_trans (by positivity) h1
    have h3 : ‖P.hatψL Q (w : ℂ)‖ ≤ C / (P.L Q * w ^ 2) := by
      rw [le_div_iff₀ (by positivity)]
      have : (P.L Q * |w|) ^ 2 = P.L Q * w ^ 2 * P.L Q := by rw [mul_pow, sq_abs]; ring
      rw [this] at h2
      have := le_div_iff₀ hL |>.mpr (by nlinarith : ‖P.hatψL Q (w : ℂ)‖ * (P.L Q * w ^ 2) * P.L Q ≤ C * P.L Q)
      field_simp at this ⊢
      nlinarith
    have hC0' : 0 ≤ C := by
      by_contra hneg; push Not at hneg; nlinarith
    have h4 : ‖P.hatψL Q (w : ℂ)‖ ^ 2 ≤ (C / (P.L Q * w ^ 2)) ^ 2 := pow_le_pow_left₀ hnn h3 2
    have hw2 : 1 + w ^ 2 ≤ 2 * (w ^ 2) ^ 2 := by nlinarith
    calc ‖P.hatψL Q (w : ℂ)‖ ^ 2 ≤ (C / (P.L Q * w ^ 2)) ^ 2 := h4
      _ = C ^ 2 / (P.L Q ^ 2 * (w ^ 2) ^ 2) := by rw [div_pow, mul_pow]
      _ ≤ 2 * C ^ 2 / (P.L Q ^ 2 * (1 + w ^ 2)) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_left hw2 (by positivity : (0:ℝ) ≤ C ^ 2 * P.L Q ^ 2)]
      _ = B * (1 + w ^ 2)⁻¹ := by unfold B; field_simp
  -- pointwise lower bound
  have hpt : ∀ t : ℝ, m₁ * ‖P.pk Q τ₀ k t‖ ^ 2 - (m₁ + 1) * (B * (1 + (t - c) ^ 2)⁻¹) ≤
      ‖P.pk Q τ₀ k t‖ ^ 2 * muChi χ t := by
    intro t
    have hn := sq_nonneg ‖P.pk Q τ₀ k t‖
    have hB : 0 ≤ B * (1 + (t - c) ^ 2)⁻¹ := by positivity
    by_cases ht : |t - c| ≤ 1
    · have := hm₁ t ht
      nlinarith [mul_le_mul_of_nonneg_left this hn]
    · push Not at ht
      have hf := hfar t ht
      have := hμ t
      nlinarith [mul_le_mul_of_nonneg_left this hn, mul_le_mul_of_nonneg_left hf hm₁']
  have hint1 : Integrable (fun t : ℝ => m₁ * ‖P.pk Q τ₀ k t‖ ^ 2) :=
    (integrable_normSq_pk P hQ τ₀ k).const_mul m₁
  have hint2 : Integrable (fun t : ℝ => (m₁ + 1) * (B * (1 + (t - c) ^ 2)⁻¹)) :=
    ((integrable_inv_one_add_sq.comp_sub_right c).const_mul B).const_mul (m₁ + 1)
  have hmono : ∫ t : ℝ, (m₁ * ‖P.pk Q τ₀ k t‖ ^ 2 - (m₁ + 1) * (B * (1 + (t - c) ^ 2)⁻¹)) ≤
      ∫ t : ℝ, ‖P.pk Q τ₀ k t‖ ^ 2 * muChi χ t := integral_mono (hint1.sub hint2) hint hpt
  rw [integral_sub hint1 hint2, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_normSq_pk P hQ τ₀ k] at hmono
  have hπ : ∫ t : ℝ, (1 + (t - c) ^ 2)⁻¹ = Real.pi := by
    rw [integral_sub_right_eq_self (fun t => (1 + t ^ 2)⁻¹) c]
    exact integral_univ_inv_one_add_sq
  rw [hπ] at hmono
  linarith

end Families.Ported.Zero
