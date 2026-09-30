/-
# Zero side: the bridge to `zeta23`'s Theorem E development

Families' `Lfun`, `mult`, `zerosI`, `PrimeSetup.strip` and the per-character counts `Nchi`,
`Ns0chi`, `Nstar0chi`, `Ndchi` (`Families/Classical.lean`, `Families/Main.lean`) against
`zeta23`'s `Zeta23.ThmE` layer (`IsNontrivialZeroL`, `zeroMultL`, `zerosInL`, `NcountL`, …,
`LSeam_of`), for a primitive `χ` modulo `q > 1`.

Also: the finite interior matrix `Aint` of a character (sum over the zeros with ordinate in
`I = (T, 2T]` of `m_ρ u(z_ρ) u(z_ρ)ᵀ`), shared by `Blocks.lean` and `Assembly.lean`.
-/
import Families.Main
import Zeta23.ThmE.MainChi
import Zeta23.ThmE.MainTermChi
import Zeta23.ThmE.LocalCountChi
import Zeta23.ThmE.GammaFactsChiProof
import Zeta23.ThmE.ReZeroCountChi

noncomputable section

open scoped BigOperators ComplexConjugate
open Complex Set

namespace Families.Ported.Zero

open Zeta23 Zeta23.ThmE

/-- `z_ρ = (ρ − 1/2)/i` (paper `eq:Gdef`; `zeta23`'s `gammaOf`). -/
def zOf (ρ : ℂ) : ℂ := (ρ - 1 / 2) / Complex.I

lemma zOf_eq_gammaOf (ρ : ℂ) : zOf ρ = gammaOf ρ := rfl

lemma zOf_re (ρ : ℂ) : (zOf ρ).re = ρ.im := by
  simp [zOf, Complex.div_I]

lemma zOf_im (ρ : ℂ) : (zOf ρ).im = -(ρ.re - 1 / 2) := by
  simp [zOf, Complex.div_I]

section Char

variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)

lemma Lfun_eq : Lfun χ = χ.LFunction := by
  funext s
  simp [Lfun, NeZero.ne q]

lemma mult_eq (ρ : ℂ) : mult χ ρ = zeroMultL χ ρ := by
  simp [mult, zeroMultL, analyticOrderNatAt, Lfun_eq]

lemma strip_eq : PrimeSetup.strip χ = {ρ | IsNontrivialZeroL χ ρ} := by
  ext ρ
  simp [PrimeSetup.strip, IsNontrivialZeroL, Lfun_eq]

variable {χ}

/-- A zero of `L(s,χ)` (primitive `χ` mod `q > 1`) off the real axis is nontrivial. -/
lemma re_mem_of_zero (hq : 1 < q) (hprim : χ.IsPrimitive) {s : ℂ} (hs : χ.LFunction s = 0)
    (him : s.im ≠ 0) : 0 < s.re ∧ s.re < 1 := by
  have hχ1 : χ ≠ 1 := ne_one_of_primitive hq hprim
  refine ⟨?_, ?_⟩
  · by_contra hle
    push Not at hle
    have hc : DirichletCharacter.completedLFunction χ s ≠ 0 := completedLFunction_ne_zero_of_re_nonpos hq hprim hle
    have hs0 : s ≠ 0 ∨ q ≠ 1 := Or.inr (by omega)
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s hs0] at hs
    have hg : DirichletCharacter.gammaFactor χ s ≠ 0 := by
      intro h0
      rcases χ.even_or_odd with he | ho
      · rw [he.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff] at h0
        obtain ⟨n, hn⟩ := h0
        apply him
        rw [hn]; simp
      · rw [ho.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff] at h0
        obtain ⟨n, hn⟩ := h0
        apply him
        have : s = -(2 * (n : ℂ)) - 1 := by rw [← hn]; ring
        rw [this]; simp
    exact hc (by
      rcases div_eq_zero_iff.mp hs with h | h
      · exact h
      · exact absurd h hg)
  · by_contra hle
    push Not at hle
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) hle hs

lemma isNontrivialZeroL_of (hq : 1 < q) (hprim : χ.IsPrimitive) {s : ℂ} (hs : Lfun χ s = 0)
    (him : s.im ≠ 0) : IsNontrivialZeroL χ s := by
  rw [Lfun_eq] at hs
  exact ⟨hs, re_mem_of_zero hq hprim hs him⟩

lemma zerosI_eq (hq : 1 < q) (hprim : χ.IsPrimitive) {T : ℝ} (hT : 0 ≤ T) :
    zerosI χ T = zerosInL χ T (2 * T) := by
  ext ρ
  simp only [zerosI, zerosInL, mem_setOf_eq]
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨isNontrivialZeroL_of hq hprim h0 (by linarith), h1, h2⟩
  · rintro ⟨h0, h1, h2⟩
    exact ⟨by rw [Lfun_eq]; exact h0.1, h1, h2⟩

lemma zerosI_finite (hq : 1 < q) (hprim : χ.IsPrimitive) {T : ℝ} (hT : 0 ≤ T) :
    (zerosI χ T).Finite := by
  rw [zerosI_eq hq hprim hT]
  have := (LSeam_of hq hprim).finite_window T (2 * T)
  refine this.subset ?_
  intro ρ hρ
  exact ⟨hρ.1, hρ.2.1, hρ.2.2⟩

lemma Nchi_eq (hq : 1 < q) (hprim : χ.IsPrimitive) {T : ℝ} (hT : 0 ≤ T) :
    Nchi χ T = NcountL χ T (2 * T) := by
  unfold Nchi NcountL
  rw [zerosI_eq hq hprim hT]
  simp only [mult_eq]

lemma Ns0chi_eq (hq : 1 < q) (hprim : χ.IsPrimitive) {T : ℝ} (hT : 0 ≤ T) :
    Ns0chi χ T = N0simpleL χ T (2 * T) := by
  unfold Ns0chi N0simpleL
  rw [zerosI_eq hq hprim hT]
  congr 1
  ext ρ
  simp only [mem_setOf_eq, mem_inter_iff, mult_eq]
  tauto

lemma Nstar0chi_eq (hq : 1 < q) (hprim : χ.IsPrimitive) {T : ℝ} (hT : 0 ≤ T) :
    Nstar0chi χ T = N0starL χ T (2 * T) := by
  unfold Nstar0chi N0starL
  rw [zerosI_eq hq hprim hT]
  rfl

lemma Ndchi_eq (hq : 1 < q) (hprim : χ.IsPrimitive) {T : ℝ} (hT : 0 ≤ T) :
    Ndchi χ T = NdistL χ T (2 * T) := by
  unfold Ndchi NdistL
  rw [zerosI_eq hq hprim hT]

end Char

/-! ### The interior matrix -/

/-- The interior matrix `A_χ = ∑_{ρ : γ ∈ (T,2T]} m_ρ u(z_ρ) u(z_ρ)ᵀ` (holomorphic product, as in
`eq:Gdef`) for a vector-valued `u : ℂ → ι → ℂ`; with `u = (p_k)_{k ∈ K_J}` this is the part of the
Gabor matrix coming from the zeros with ordinate in `I` (paper §3, `A_χ`). -/
def Aint {ι : Type*} {q : ℕ} (u : ℂ → ι → ℂ) (χ : DirichletCharacter ℂ q) (T : ℝ) :
    Matrix ι ι ℂ :=
  ∑ᶠ ρ ∈ zerosI χ T, ((mult χ ρ : ℕ) : ℂ) • Matrix.vecMulVec (u (zOf ρ)) (u (zOf ρ))

/-! ### Exceptional ("bad") characters (paper §4.4, with the adjusted height `Q^{a|δ|}` allowed there) -/

/-- `δ₀ = B₁ log ℓ / ℓ`, `ℓ = log Q` (paper §4.4, `B₁ = 30` there; here `B₁` is adjusted to the
constants of `Montgomery69_Density`, as §4.4 allows). -/
def delta0 (B₁ Q : ℝ) : ℝ := B₁ * Real.log (Real.log Q) / Real.log Q

/-- `χ` is **bad** (parameters `a, B₁`): `L(s,χ)` has a nontrivial zero `ρ = 1/2 + δ + iγ` with
`|δ| ≥ δ₀` and `|γ| ≤ Q^{a|δ|}` (paper §4.4 with the height `Q^{|δ|/2}` replaced by `Q^{a|δ|}`,
as allowed by §4.4). -/
def Bad (a B₁ Q : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) : Prop :=
  ∃ ρ : ℂ, Lfun χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ delta0 B₁ Q ≤ |ρ.re - 1 / 2| ∧
    |ρ.im| ≤ Q ^ (a * |ρ.re - 1 / 2|)

/-! ### The family -/

/-- On the family (`w(q/Q) ≠ 0`) the modulus is at least `η Q`. -/
lemma le_of_w_ne (W : Weight) {Q : ℝ} (hQ : 0 < Q) {q : ℕ} (hw : W.w (q / Q) ≠ 0) :
    W.η * Q ≤ q := by
  have := (W.supp _ hw).1
  rwa [le_div_iff₀ hQ] at this

lemma one_lt_of_w_ne (W : Weight) {Q : ℝ} (hQ : 2 ≤ W.η * Q) {q : ℕ} (hw : W.w (q / Q) ≠ 0) :
    1 < q := by
  have hQ0 : 0 < Q := by
    by_contra h; push_neg at h
    nlinarith [W.η_pos]
  have := le_of_w_ne W hQ0 hw
  have : (1 : ℝ) < q := by linarith
  exact_mod_cast this

lemma mem_primChars {q : ℕ} {χ : DirichletCharacter ℂ q} (h : χ ∈ primChars q) : χ.IsPrimitive := by
  classical
  unfold primChars at h
  simpa using h

end Families.Ported.Zero
