/-
# Zero side: the explicit-formula interface (`lem:explicit`, Appendix B `prop:weil`)

Shared with the second moment (`Families/Ported/Second/`), which needs the explicit-formula
representation of the Gram entries.

For a primitive character `χ` modulo `q > 1`, `Q > 1`, any lattice offset `τ₀` and any `k, l ∈ ℤ`:

`G_{χ,kl} = ∑_ρ m_ρ p_k(z_ρ) p_l(z_ρ) = ∫_ℝ p_k(t) p_l(t) ν_χ(t) dt`   (`gabor_eq_integral`)

with the zero sum absolutely convergent and the integrand integrable. Here
`ν_χ = μ_χ + P_χ` is `nuChi P Q χ` := `zeta23`'s `nuXc (parity χ) q (coeff χ) X` with `X = e^L`:
`μ_χ(t) = (1/2π)(log(q/π) + Re ψ(1/4 + 𝔞/2 + it/2))` (paper `eq:mu`) and the **sharp** prime part
`P_χ(t) = −(1/π) Re ∑_{n ≤ X} Λ(n) χ(n) n^{−1/2−it}`. (The paper's `P_χ` has the smooth cut-off `Υ`;
since `p_k p_l` is the Fourier transform of a function supported in `(−L, L)`, both give the same
`G_χ` — proof of Lemma 2.6.)

The analytic input is `zeta23`'s Weil explicit formula for primitive `χ` with complex `C_c²`
test functions (`Zeta23.ThmE.EF_lit_chi_L`, bridged to the paper form by
`Zeta23.ThmE.explicitFormulaPaperChi_of_lit`), i.e. Appendix B `prop:weil`, proved there
`sorry`-free.

Also here: the window functions `f_k(u) = ψ_L(u) e^{−iτ_k u}` (`fk`), `paperFT f_k = p_k`
(`paperFT_fk`), the conjugation symmetry `p_k(z̄) = conj p_k(z)` (`pk_conj`), and reality of `p_k`
on `ℝ` (`pk_ofReal_conj`).
-/
import Families.Ported.Zero.Bridge

noncomputable section

open scoped BigOperators ComplexConjugate ContDiff
open Complex Set MeasureTheory

namespace Families.Ported.Zero

open Zeta23 Zeta23.ThmE

variable (P : PrimeSetup)

/-! ### Window, lattice, `f_k` -/

/-- `τ_k = τ₀ + 2πk/L`. -/
def tau (Q τ₀ : ℝ) (k : ℤ) : ℝ := τ₀ + 2 * Real.pi * k / P.L Q

/-- `f_k(u) = ψ_L(u) e^{−iτ_k u}` (Appendix B, proof of `lem:explicit`). -/
def fk (Q τ₀ : ℝ) (k : ℤ) : ℝ → ℂ :=
  fun u => ((P.ψL Q u : ℝ) : ℂ) * Complex.exp (-(Complex.I * ((tau P) Q τ₀ k : ℂ) * u))

lemma L_pos {Q : ℝ} (hQ : 1 < Q) : 0 < P.L Q :=
  mul_pos P.lam_pos (Real.log_pos hQ)

lemma pk_eq (Q τ₀ : ℝ) (k : ℤ) (z : ℂ) :
    P.pk Q τ₀ k z = P.hatψL Q (z - ((tau P) Q τ₀ k : ℂ)) := by
  simp [PrimeSetup.pk, tau]

lemma hatψL_eq_paperFT (Q : ℝ) (w : ℂ) :
    P.hatψL Q w = paperFT (fun u => ((P.ψL Q u : ℝ) : ℂ)) w := rfl

lemma paperFT_fk (Q τ₀ : ℝ) (k : ℤ) (z : ℂ) : paperFT ((fk P) Q τ₀ k) z = P.pk Q τ₀ k z := by
  rw [pk_eq]
  unfold paperFT fk PrimeSetup.hatψL
  congr 1
  funext u
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- `ψ_L` is even. -/
lemma ψL_neg (Q u : ℝ) : P.ψL Q (-u) = P.ψL Q u := by
  simp only [PrimeSetup.ψL, neg_div, P.ψ_even]

/-- `\widehat{ψ_L}(\bar w) = \overline{\widehat{ψ_L}(w)}` (`ψ` real and even). -/
lemma hatψL_conj (Q : ℝ) (w : ℂ) : P.hatψL Q (conj w) = conj (P.hatψL Q w) := by
  unfold PrimeSetup.hatψL
  rw [← integral_conj, ← integral_neg_eq_self]
  congr 1
  funext u
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I, map_neg,
    Complex.ofReal_neg, ψL_neg]
  congr 2
  ring

/-- `p_k(\bar z) = \overline{p_k(z)}`. -/
lemma pk_conj (Q τ₀ : ℝ) (k : ℤ) (z : ℂ) : P.pk Q τ₀ k (conj z) = conj (P.pk Q τ₀ k z) := by
  rw [pk_eq, pk_eq, ← hatψL_conj]
  simp

/-- `p_k` is real on `ℝ`. -/
lemma pk_ofReal_conj (Q τ₀ : ℝ) (k : ℤ) (t : ℝ) : conj (P.pk Q τ₀ k t) = P.pk Q τ₀ k t := by
  rw [← pk_conj, Complex.conj_ofReal]

lemma pk_ofReal_im (Q τ₀ : ℝ) (k : ℤ) (t : ℝ) : (P.pk Q τ₀ k t).im = 0 := by
  have := (pk_ofReal_conj P) Q τ₀ k t
  rw [Complex.conj_eq_iff_im] at this
  exact this

/-- `ψ_L(u) = 0` for `|u| > rL`, some `r < 1/2`. -/
lemma ψL_supp : ∃ r : ℝ, r < 1 / 2 ∧ ∀ Q : ℝ, 1 < Q → ∀ u : ℝ, r * P.L Q < |u| → P.ψL Q u = 0 := by
  obtain ⟨r, hr, h⟩ := P.ψ_supp
  refine ⟨r, hr, fun Q hQ u hu => ?_⟩
  have hL := (L_pos P) hQ
  apply h
  rw [abs_div, abs_of_pos hL, lt_div_iff₀ hL]
  exact hu

lemma contDiff_ψL (Q : ℝ) : ContDiff ℝ ∞ (P.ψL Q) := by
  unfold PrimeSetup.ψL
  exact P.ψ_smooth.comp (contDiff_id.div_const _)

lemma contDiff_fk (Q τ₀ : ℝ) (k : ℤ) : ContDiff ℝ 2 ((fk P) Q τ₀ k) := by
  unfold fk
  have h1 : ContDiff ℝ 2 (fun u : ℝ => ((P.ψL Q u : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_infty.mp ((contDiff_ψL P) Q) 2)
  have h2 : ContDiff ℝ 2 (fun u : ℝ => Complex.exp (-(Complex.I * ((tau P) Q τ₀ k : ℂ) * u))) := by
    apply Complex.contDiff_exp.comp
    apply ContDiff.neg
    exact contDiff_const.mul Complex.ofRealCLM.contDiff
  exact h1.mul h2

lemma tsupport_fk {Q : ℝ} (hQ : 1 < Q) (τ₀ : ℝ) (k : ℤ) :
    tsupport ((fk P) Q τ₀ k) ⊆ Icc (-(P.L Q / 2)) (P.L Q / 2) := by
  obtain ⟨r, hr, h⟩ := (ψL_supp P)
  have hL := (L_pos P) hQ
  refine closure_minimal ?_ isClosed_Icc
  intro u hu
  rw [Function.mem_support] at hu
  have hψ : P.ψL Q u ≠ 0 := by
    intro h0; apply hu; simp [fk, h0]
  have : |u| ≤ r * P.L Q := by
    by_contra hc; push Not at hc; exact hψ (h Q hQ u hc)
  have : |u| ≤ P.L Q / 2 := by nlinarith
  exact abs_le.mp this

/-! ### `ν_χ` -/

/-- `ν_χ = μ_χ + P_χ` (paper `eq:mu`, `eq:an`), with the sharp prime cut-off `n ≤ X = e^L`:
`zeta23`'s `nuXc (parity χ) q (coeff χ) X`. -/
def nuChi (Q : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) : ℝ :=
  nuXc (parity χ) q (coeff χ) (P.X Q) t

lemma parity_le_one' {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : parity χ ≤ 1 := by
  unfold parity
  split <;> omega

lemma coeffOK_of {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : CoeffOK q (coeff χ) where
  norm_le := fun n => χ.norm_le_one _
  vanish := fun n hn => by
    have : ¬ IsUnit ((n : ZMod q)) := by
      rwa [ZMod.isUnit_iff_coprime]
    exact χ.map_nonunit this

/-! ### The explicit formula for the Gabor entries -/

/-- The Gabor summand `m_ρ p_k(z_ρ) p_l(z_ρ)` (paper `eq:Gdef`). -/
def gaborTerm (Q τ₀ : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (k l : ℤ) (ρ : ℂ) : ℂ :=
  (mult χ ρ : ℂ) * P.pk Q τ₀ k (zOf ρ) * P.pk Q τ₀ l (zOf ρ)

lemma gabor_apply (Q T τ₀ : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (k l : P.KJ Q T τ₀) :
    P.Gabor Q T τ₀ χ k l = ∑' ρ : PrimeSetup.strip χ, (gaborTerm P) Q τ₀ χ k l ρ := rfl

/-- **`lem:explicit`** (Lemma 2.6; Appendix B): for primitive `χ` mod `q > 1`, `Q > 1`, any `τ₀`
and `k, l ∈ ℤ`, the Gabor zero sum `∑_ρ m_ρ p_k(z_ρ) p_l(z_ρ)` converges absolutely and equals
`∫ p_k p_l ν_χ` (the integrand being integrable). -/
theorem gabor_eq_integral {Q : ℝ} (hQ : 1 < Q) (τ₀ : ℝ) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 1 < q) (hprim : χ.IsPrimitive) (k l : ℤ) :
    Summable (fun ρ : PrimeSetup.strip χ => (gaborTerm P) Q τ₀ χ k l ρ) ∧
    Integrable (fun t : ℝ => P.pk Q τ₀ k t * P.pk Q τ₀ l t * ((nuChi P) Q χ t : ℂ)) ∧
    ∑' ρ : PrimeSetup.strip χ, (gaborTerm P) Q τ₀ χ k l ρ =
      ∫ t : ℝ, P.pk Q τ₀ k t * P.pk Q τ₀ l t * ((nuChi P) Q χ t : ℂ) := by
  have hEF : ExplicitFormulaPaperChi (parity χ) q (coeff χ) (LZeros (LSeam_of hq hprim)) :=
    explicitFormulaPaperChi_of_lit (EF_lit_chi_L hq hprim)
      (GammaChi.gammaFactsChi (parity_le_one' χ) (by omega)) (by omega) (coeffOK_of χ)
  obtain ⟨hsum, hint, heq⟩ := hEF (P.L Q) ((L_pos P) hQ) ((fk P) Q τ₀ k) ((fk P) Q τ₀ l)
    ((contDiff_fk P) Q τ₀ k) ((contDiff_fk P) Q τ₀ l) ((tsupport_fk P) hQ τ₀ k) ((tsupport_fk P) hQ τ₀ l)
  -- the summands agree
  have hterm : ∀ ρ : ℂ, (LZeros (LSeam_of hq hprim)).Wsummand ((fk P) Q τ₀ k) ((fk P) Q τ₀ l) ρ =
      (gaborTerm P) Q τ₀ χ k l ρ := by
    intro ρ
    simp only [ZeroConfig.Wsummand, LZeros_mult, gaborTerm, paperFT_fk, mult_eq]
    rw [(pk_conj P), Complex.conj_conj]
    rfl
  -- the integrands agree
  have hfun : (fun τ : ℝ => paperFT ((fk P) Q τ₀ k) τ * conj (paperFT ((fk P) Q τ₀ l) τ) *
      (nuXc (parity χ) q (coeff χ) (Real.exp (P.L Q)) τ : ℂ)) =
      fun t : ℝ => P.pk Q τ₀ k t * P.pk Q τ₀ l t * ((nuChi P) Q χ t : ℂ) := by
    funext t
    rw [paperFT_fk, paperFT_fk, (pk_ofReal_conj P)]
    rfl
  have hset : (LZeros (LSeam_of hq hprim)).carrier = PrimeSetup.strip χ := by
    rw [LZeros_carrier, strip_eq]
  rw [hfun] at hint heq
  have hsum' : Summable (fun ρ : (LZeros (LSeam_of hq hprim)).carrier =>
      (gaborTerm P) Q τ₀ χ k l ρ) := by
    refine hsum.congr fun ρ => ?_
    exact hterm ρ
  refine ⟨?_, hint, ?_⟩
  · rw [← hset]; exact hsum'
  · rw [← heq, ZeroConfig.W]
    rw [show (∑' ρ : (LZeros (LSeam_of hq hprim)).carrier,
        (LZeros (LSeam_of hq hprim)).Wsummand ((fk P) Q τ₀ k) ((fk P) Q τ₀ l) ρ) =
        ∑' ρ : (LZeros (LSeam_of hq hprim)).carrier, (gaborTerm P) Q τ₀ χ k l ρ from
        tsum_congr fun ρ => hterm ρ]
    exact tsum_congr_set_coe (fun ρ => (gaborTerm P) Q τ₀ χ k l ρ) hset.symm

end Families.Ported.Zero
