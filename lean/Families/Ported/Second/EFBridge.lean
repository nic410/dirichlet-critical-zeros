/-
# Prime side: the explicit formula with the smooth cut-off `Υ` from the sharp one

The zero side proves `lem:explicit` (`Families.Ported.Zero.gabor_eq_integral`) with `zeta23`'s
`ν_χ = nuXc (parity χ) q (coeff χ) X` (`X = e^L`, **sharp** prime cut-off `n ≤ X`). The prime side uses
`ν_χ = μ_χ + P_χ` with the **smooth** cut-off `a_n = Λ(n) n^{-1/2} Υ(n)` (`nuChi`, `eq:an`). The paper notes
(Lemma 2.6 and its proof) that `G_χ` does not depend on the cut-off since `p_k p_l = \widehat{f_k * f_l}`
with `supp (f_k * f_l) ⊂ (−L, L)`. This file proves that remark:

* `integral_pk_pk_exp` : `∫ p_k(t) p_l(t) e^{iξt} dt = 0` for `|ξ| ≥ L`;
* **`explicitGabor_of_sharp : ExplicitGaborSharp_Statement → ExplicitGabor_Statement`**.

`ExplicitGaborSharp_Statement` is stated with `zeta23`'s `nuXc`, `parity`, `coeff`, i.e. with the same
`ν_χ` as `Families.Ported.Zero.nuChi`; it is the second and third components of
`gabor_eq_integral` (wired in `Families/Ported/Full.lean`).
-/
import Families.Ported.Second.Common
import Zeta23.ThmE.Statement

noncomputable section

open scoped BigOperators ComplexConjugate ContDiff FourierTransform
open ArithmeticFunction Finset MeasureTheory Filter Topology

namespace Families.Ported.Second

open Families

/-! ### A Fourier pair: `h(t) = ∫ f(u) e^{itu} du` ⇒ `∫ h(t) e^{-itℓ} dt = 2π f(ℓ)` -/

section FourierPair

variable {f : ℝ → ℂ}

/-- `h(t) = ∫ f(u) e^{itu} du`. -/
def fhat (f : ℝ → ℂ) (t : ℝ) : ℂ := ∫ u, f u * Complex.exp (Complex.I * t * u)

lemma fhat_eq_fourier (t : ℝ) : fhat f t = 𝓕 f (-(t / (2 * Real.pi))) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 2
  push_cast
  field_simp

lemma fourier_integrable_of (hf : ContDiff ℝ ∞ f) (hfs : HasCompactSupport f) :
    Integrable (𝓕 f) := by
  set FS := hfs.toSchwartzMap hf
  have h1 : (FS : ℝ → ℂ) = f := rfl
  have h2 := (𝓕 FS).integrable (μ := volume)
  rw [SchwartzMap.fourier_coe, h1] at h2
  exact h2

lemma fhat_integrable (hf : ContDiff ℝ ∞ f) (hfs : HasCompactSupport f) : Integrable (fhat f) := by
  have h := (fourier_integrable_of hf hfs).comp_mul_left'
    (R := -(1 / (2 * Real.pi))) (by simp [Real.pi_ne_zero])
  refine h.congr (Eventually.of_forall fun r => ?_)
  simp only
  rw [fhat_eq_fourier, show -(1 / (2 * Real.pi)) * r = -(r / (2 * Real.pi)) by ring]

/-- Fourier inversion: `∫ h(t) e^{−itℓ} dt = 2π f(ℓ)`. -/
lemma fhat_inversion (hf : ContDiff ℝ ∞ f) (hfs : HasCompactSupport f) (ℓ : ℝ) :
    ∫ t, fhat f t * Complex.exp (-(Complex.I * t * ℓ)) = 2 * Real.pi * f ℓ := by
  have hinv := congrFun (Continuous.fourierInv_fourier_eq hf.continuous
    (hf.continuous.integrable_of_hasCompactSupport hfs) (fourier_integrable_of hf hfs)) ℓ
  rw [Real.fourierInv_eq'] at hinv
  set h : ℝ → ℂ := fun r => fhat f r * Complex.exp (-(Complex.I * r * ℓ)) with hh
  have hsub := Measure.integral_comp_mul_left h (-(2 * Real.pi))
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [inv_neg, abs_neg, abs_inv, abs_of_pos hpi] at hsub
  have hrhs : ∫ x, h (-(2 * Real.pi) * x) = ∫ v, Complex.exp (↑(2 * Real.pi * inner ℝ v ℓ) * Complex.I) •
      𝓕 f v := by
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [hh, smul_eq_mul]
    rw [fhat_eq_fourier]
    have : -(-(2 * Real.pi) * v / (2 * Real.pi)) = v := by field_simp
    rw [this, mul_comm]
    congr 2
    rw [RCLike.inner_apply, conj_trivial]
    push_cast; ring
  rw [hrhs, hinv] at hsub
  have h2 : (2 * Real.pi)⁻¹ • ∫ r, h r = f ℓ := hsub.symm
  rw [← h2, Complex.real_smul]
  push_cast
  field_simp

end FourierPair

/-! ### `p_k` as a Fourier transform -/

section Pk

variable (P : PrimeSetup)

/-- `f_k(u) = ψ_L(u) e^{−iτ_k u}`, `τ_k = τ₀ + 2πk/L`. -/
def fK (Q τ₀ : ℝ) (k : ℤ) (u : ℝ) : ℂ :=
  (P.ψL Q u : ℂ) * Complex.exp (-(Complex.I * (τ₀ + 2 * Real.pi * k / P.L Q) * u))

lemma fK_contDiff (Q τ₀ : ℝ) (k : ℤ) : ContDiff ℝ ∞ (fK P Q τ₀ k) := by
  unfold fK PrimeSetup.ψL
  refine (Complex.ofRealCLM.contDiff.comp (P.ψ_smooth.comp (contDiff_id.div_const _))).mul ?_
  exact Complex.contDiff_exp.comp ((contDiff_const.mul Complex.ofRealCLM.contDiff).neg)

lemma fK_zero {Q : ℝ} (hQ : 1 < Q) (τ₀ : ℝ) (k : ℤ) {u : ℝ} (hu : P.L Q / 2 ≤ |u|) :
    fK P Q τ₀ k u = 0 := by
  obtain ⟨r, hr, h⟩ := P.ψ_supp
  have hL := P.L_pos hQ
  unfold fK PrimeSetup.ψL
  have : r < |u / P.L Q| := by
    rw [abs_div, abs_of_pos hL, lt_div_iff₀ hL]
    nlinarith [abs_nonneg u]
  rw [h _ this]; simp

lemma fK_hasCompactSupport {Q : ℝ} (hQ : 1 < Q) (τ₀ : ℝ) (k : ℤ) :
    HasCompactSupport (fK P Q τ₀ k) := by
  refine HasCompactSupport.intro (K := Set.Icc (-(P.L Q / 2)) (P.L Q / 2)) isCompact_Icc ?_
  intro u hu
  apply fK_zero P hQ
  by_contra hcon
  push Not at hcon
  exact hu (Set.mem_Icc.mpr (abs_le.mp hcon.le))

lemma pk_eq_fhat (Q τ₀ : ℝ) (k : ℤ) (t : ℝ) : P.pk Q τ₀ k (t : ℂ) = fhat (fK P Q τ₀ k) t := by
  unfold PrimeSetup.pk PrimeSetup.hatψL fhat fK
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  rw [mul_assoc (↑(P.ψL Q u) : ℂ), ← Complex.exp_add]
  congr 2
  ring

lemma pk_integrable {Q : ℝ} (hQ : 1 < Q) (τ₀ : ℝ) (k : ℤ) :
    Integrable (fun t : ℝ => P.pk Q τ₀ k (t : ℂ)) := by
  simp_rw [pk_eq_fhat]
  exact fhat_integrable (fK_contDiff P Q τ₀ k) (fK_hasCompactSupport P hQ τ₀ k)

lemma norm_fK_le (Q τ₀ : ℝ) (k : ℤ) (u : ℝ) : ‖fK P Q τ₀ k u‖ = |P.ψL Q u| := by
  unfold fK
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  simp

lemma pk_norm_le {Q : ℝ} (hQ : 1 < Q) (τ₀ : ℝ) (k : ℤ) (t : ℝ) :
    ‖P.pk Q τ₀ k (t : ℂ)‖ ≤ ∫ u, ‖fK P Q τ₀ k u‖ := by
  rw [pk_eq_fhat]
  unfold fhat
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [norm_mul]
  rw [Complex.norm_exp]; simp

lemma pk_continuous {Q : ℝ} (hQ : 1 < Q) (τ₀ : ℝ) (k : ℤ) :
    Continuous (fun t : ℝ => P.pk Q τ₀ k (t : ℂ)) := by
  simp_rw [pk_eq_fhat]
  have hc : Continuous (fun t : ℝ => 𝓕 (fK P Q τ₀ k) (-(t / (2 * Real.pi)))) := by
    set FS := (fK_hasCompactSupport P hQ τ₀ k).toSchwartzMap (fK_contDiff P Q τ₀ k)
    have h1 : (FS : ℝ → ℂ) = fK P Q τ₀ k := rfl
    have h2 := (𝓕 FS).continuous
    rw [SchwartzMap.fourier_coe, h1] at h2
    exact h2.comp (by fun_prop)
  exact hc.congr fun t => (fhat_eq_fourier t).symm

/-- **Orthogonality** (proof of Lemma 2.6): `∫ p_k(t) p_l(t) e^{iξt} dt = 0` for `|ξ| ≥ L`, because
`p_k p_l = \widehat{f_k * f_l}` and `supp (f_k * f_l) ⊂ (−L, L)`. -/
theorem integral_pk_pk_exp {Q : ℝ} (hQ : 1 < Q) (τ₀ : ℝ) (k l : ℤ) {ξ : ℝ} (hξ : P.L Q ≤ |ξ|) :
    ∫ t : ℝ, P.pk Q τ₀ k (t : ℂ) * P.pk Q τ₀ l (t : ℂ) * Complex.exp (Complex.I * ξ * t) = 0 := by
  simp_rw [pk_eq_fhat]
  set fk := fK P Q τ₀ k
  set fl := fK P Q τ₀ l
  have hfk := fK_contDiff P Q τ₀ k
  have hfl := fK_contDiff P Q τ₀ l
  have hfks := fK_hasCompactSupport P hQ τ₀ k
  have hfls := fK_hasCompactSupport P hQ τ₀ l
  have hfki : Integrable fk := hfk.continuous.integrable_of_hasCompactSupport hfks
  have hpl : Integrable (fhat fl) := fhat_integrable hfl hfls
  -- rewrite `p_k` as an integral and swap
  have e1 : ∀ t : ℝ, fhat fk t * fhat fl t * Complex.exp (Complex.I * ξ * t) =
      ∫ u, fk u * (fhat fl t * Complex.exp (Complex.I * t * (u + ξ))) := by
    intro t
    unfold fhat
    rw [← integral_mul_const, ← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only
    have : Complex.exp (Complex.I * t * u) * Complex.exp (Complex.I * ξ * t) =
        Complex.exp (Complex.I * t * (u + ξ)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    calc fk u * Complex.exp (Complex.I * t * u) * (∫ v, fl v * Complex.exp (Complex.I * t * v)) *
          Complex.exp (Complex.I * ξ * t)
        = fk u * ((∫ v, fl v * Complex.exp (Complex.I * t * v)) *
          (Complex.exp (Complex.I * t * u) * Complex.exp (Complex.I * ξ * t))) := by ring
      _ = _ := by rw [this]
  simp_rw [e1]
  have hint : Integrable (Function.uncurry fun t u =>
      fk u * (fhat fl t * Complex.exp (Complex.I * t * (u + ξ)))) (volume.prod volume) := by
    have hprod : Integrable (fun z : ℝ × ℝ => fhat fl z.1 * fk z.2) (volume.prod volume) :=
      hpl.mul_prod hfki
    have hg : AEStronglyMeasurable (fun z : ℝ × ℝ => Complex.exp (Complex.I * z.1 * (z.2 + ξ)))
        (volume.prod volume) :=
      (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
    have hbd : ∀ᵐ z ∂(volume.prod volume),
        ‖(fun z : ℝ × ℝ => Complex.exp (Complex.I * z.1 * (z.2 + ξ))) z‖ ≤ 1 :=
      Eventually.of_forall fun z => by simp only; rw [Complex.norm_exp]; simp
    refine (hprod.mul_bdd (c := 1) hg hbd).congr (Eventually.of_forall fun z => ?_)
    obtain ⟨a, b⟩ := z
    simp only [Function.uncurry_apply_pair]; ring
  rw [integral_integral_swap hint]
  -- inner integral by Fourier inversion
  have e2 : ∀ u : ℝ, ∫ t, fk u * (fhat fl t * Complex.exp (Complex.I * t * (u + ξ))) =
      fk u * (2 * Real.pi * fl (-(u + ξ))) := by
    intro u
    rw [integral_const_mul, ← fhat_inversion hfl hfls (-(u + ξ))]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only
    congr 2
    push_cast; ring
  simp_rw [e2]
  -- the integrand vanishes
  have hL := P.L_pos hQ
  have hz : ∀ u : ℝ, fk u * (2 * Real.pi * fl (-(u + ξ))) = 0 := by
    intro u
    by_cases hu : P.L Q / 2 ≤ |u|
    · rw [show fk u = 0 from fK_zero P hQ τ₀ k hu, zero_mul]
    · push Not at hu
      have : P.L Q / 2 ≤ |-(u + ξ)| := by
        rw [abs_neg]
        have := abs_sub_abs_le_abs_sub ξ (-u)
        rw [abs_neg, sub_neg_eq_add, add_comm] at this
        linarith
      rw [show fl (-(u + ξ)) = 0 from fK_zero P hQ τ₀ l this]; ring
  simp_rw [hz]
  exact integral_zero ℝ ℂ

end Pk

/-! ### The sharp `ν_χ` and the bridge -/

section Bridge

/-- `ν_χ` with the sharp prime cut-off `n ≤ X = e^L` (`zeta23`'s `nuXc`, as in `Families.Ported.Zero.nuChi`). -/
def nuSharp (P : PrimeSetup) (Q : ℝ) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) : ℝ :=
  Zeta23.ThmE.nuXc (Zeta23.ThmE.parity χ) q (Zeta23.ThmE.coeff χ) (P.X Q) t

/-- **`lem:explicit` with the sharp cut-off** — exactly the second and third components of
`Families.Ported.Zero.gabor_eq_integral` (whose `nuChi` unfolds to `nuSharp`). -/
def ExplicitGaborSharp_Statement : Prop :=
  ∀ (P : PrimeSetup) (Q τ₀ : ℝ), 1 < Q → ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), 1 < q →
    χ.IsPrimitive → ∀ (T : ℝ) (k l : P.KJ Q T τ₀),
      Integrable (fun t : ℝ => P.pk Q τ₀ k t * P.pk Q τ₀ l t * (nuSharp P Q χ t : ℂ)) ∧
      P.Gabor Q T τ₀ χ k l = ∫ t : ℝ, P.pk Q τ₀ k t * P.pk Q τ₀ l t * (nuSharp P Q χ t : ℂ)

variable (P : PrimeSetup)

lemma muChi_eq_muq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    muChi χ t = Zeta23.ThmE.muq (Zeta23.ThmE.parity χ) q t := by
  unfold muChi Zeta23.ThmE.muq digammaRe
  have hpar : ((Zeta23.ThmE.parity χ : ℕ) : ℝ) = aChi χ := by
    unfold Zeta23.ThmE.parity aChi DirichletCharacter.Even
    split_ifs <;> simp
  have harg : (1 / 2 + (aChi χ : ℂ) + Complex.I * t) / 2 =
      1 / 4 + ((Zeta23.ThmE.parity χ : ℕ) : ℂ) / 2 + Complex.I * t / 2 := by
    rw [show ((Zeta23.ThmE.parity χ : ℕ) : ℂ) = ((aChi χ : ℝ) : ℂ) by
      rw [← hpar]; push_cast; rfl]
    ring
  rw [harg, mul_add]
  rfl

/-- The prime terms beyond `X`: `D(t) = −(1/π) Re ∑_{X < n ≤ Y} a_n χ(n) n^{−it}`. -/
def Dtail (Q : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) : ℝ :=
  -(1 / Real.pi) * (∑ n ∈ Finset.Ioc ⌊P.X Q⌋₊ ⌊P.Y Q⌋₊,
    (P.aVec Q n : ℂ) * χ n * (n : ℂ) ^ (-(Complex.I * t))).re

lemma X_le_Y {Q : ℝ} (hQ : 1 < Q) : P.X Q ≤ P.Y Q := by
  have hL := P.L_pos hQ
  have hX1 : 1 ≤ P.X Q := by unfold PrimeSetup.X; exact Real.one_le_exp hL.le
  unfold PrimeSetup.Y
  exact Real.self_le_rpow_of_one_le hX1 (by linarith [P.ε₁_pos])

lemma aVec_small {Q : ℝ} (hQ : 1 < Q) (t : ℝ) {n : ℕ} (hn1 : 1 ≤ n) (hnX : n ≤ ⌊P.X Q⌋₊) :
    (P.aVec Q n : ℂ) * (n : ℂ) ^ (-(Complex.I * t)) =
      (Λ n : ℂ) * (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * t) := by
  have hL := P.L_pos hQ
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hnX' : (n : ℝ) ≤ P.X Q := (Nat.le_floor_iff (Real.exp_pos _).le).mp hnX
  have hUps : P.Ups Q n = 1 := by
    unfold PrimeSetup.Ups
    apply P.Υ₀_one
    · exact div_nonneg (Real.log_nonneg (by exact_mod_cast hn1)) hL.le
    · rw [div_le_one hL]
      have := Real.log_le_log hn0 hnX'
      unfold PrimeSetup.X at this; rwa [Real.log_exp] at this
  have hsq : ((Real.sqrt n : ℝ) : ℂ)⁻¹ = (n : ℂ) ^ (-(1 / 2 : ℂ)) := by
    rw [Real.sqrt_eq_rpow, ← Complex.ofReal_inv, ← Real.rpow_neg hn0.le,
      Complex.ofReal_cpow hn0.le]
    push_cast; ring_nf
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  unfold PrimeSetup.aVec
  rw [hUps, mul_one, sub_eq_add_neg, Complex.cpow_add _ _ hnC, ← hsq]
  push_cast
  ring

lemma PChi_eq_PXc_add {Q : ℝ} (hQ : 1 < Q) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (t : ℝ) : PChi P Q χ t =
      Zeta23.ThmE.PXc (Zeta23.ThmE.coeff χ) (P.X Q) t + Dtail P Q χ t := by
  have hXY : ⌊P.X Q⌋₊ ≤ ⌊P.Y Q⌋₊ := Nat.floor_le_floor (X_le_Y P hQ)
  have hsplit : P.range Q = Finset.Ioc 0 ⌊P.X Q⌋₊ ∪ Finset.Ioc ⌊P.X Q⌋₊ ⌊P.Y Q⌋₊ := by
    unfold PrimeSetup.range
    ext n; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Finset.Ioc 0 ⌊P.X Q⌋₊) (Finset.Ioc ⌊P.X Q⌋₊ ⌊P.Y Q⌋₊) := by
    rw [Finset.disjoint_left]; intro n h1 h2
    simp only [Finset.mem_Ioc] at h1 h2; omega
  have hS1 : ∑ n ∈ Finset.Ioc 0 ⌊P.X Q⌋₊, (P.aVec Q n : ℂ) * χ n * (n : ℂ) ^ (-(Complex.I * t)) =
      ∑ n ∈ Finset.Ioc 0 ⌊P.X Q⌋₊,
        ((Λ n : ℝ) : ℂ) * Zeta23.ThmE.coeff χ n * (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * t) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' := Finset.mem_Ioc.mp hn
    unfold Zeta23.ThmE.coeff
    have h := aVec_small P hQ t (n := n) (by omega) hn'.2
    calc (P.aVec Q n : ℂ) * χ (n : ZMod q) * (n : ℂ) ^ (-(Complex.I * t))
        = χ (n : ZMod q) * ((P.aVec Q n : ℂ) * (n : ℂ) ^ (-(Complex.I * t))) := by ring
      _ = χ (n : ZMod q) * ((Λ n : ℂ) * (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * t)) := by rw [h]
      _ = _ := by ring
  unfold PChi PrimeSetup.Schi Dtail Zeta23.ThmE.PXc
  rw [hsplit, Finset.sum_union hdisj, hS1, Complex.add_re, mul_add]

lemma nuChi_eq {Q : ℝ} (hQ : 1 < Q) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (t : ℝ) :
    nuChi P Q χ t = nuSharp P Q χ t + Dtail P Q χ t := by
  unfold nuChi nuSharp Zeta23.ThmE.nuXc
  rw [muChi_eq_muq, PChi_eq_PXc_add P hQ]
  ring

/-- `∫ p_k p_l D = 0`: the tail `n > X` is invisible to `G_χ`. -/
lemma integral_pk_pk_Dtail {Q : ℝ} (hQ : 1 < Q) (τ₀ : ℝ) (k l : ℤ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    ∫ t : ℝ, P.pk Q τ₀ k t * P.pk Q τ₀ l t * (Dtail P Q χ t : ℂ) = 0 := by
  have hL := P.L_pos hQ
  set S := Finset.Ioc ⌊P.X Q⌋₊ ⌊P.Y Q⌋₊ with hS
  have hlog : ∀ n ∈ S, P.L Q ≤ Real.log n := by
    intro n hn
    have hn' := Finset.mem_Ioc.mp hn
    have hXn : P.X Q < n := by
      have := Nat.lt_of_floor_lt hn'.1
      exact_mod_cast this
    have hX0 : 0 < P.X Q := Real.exp_pos _
    have := Real.log_lt_log hX0 hXn
    unfold PrimeSetup.X at this; rw [Real.log_exp] at this; exact this.le
  have hn1 : ∀ n ∈ S, 1 ≤ n := fun n hn => by have := (Finset.mem_Ioc.mp hn).1; omega
  -- the kernel `p_k p_l` and its integrability against bounded continuous factors
  set K : ℝ → ℂ := fun t => P.pk Q τ₀ k t * P.pk Q τ₀ l t with hK
  have hKi : ∀ ξ : ℝ, Integrable (fun t : ℝ => K t * Complex.exp (Complex.I * ξ * t)) := by
    intro ξ
    have h1 : Integrable K := by
      refine (pk_integrable P hQ τ₀ l).bdd_mul (c := ∫ u, ‖fK P Q τ₀ k u‖)
        (pk_continuous P hQ τ₀ k).aestronglyMeasurable
        (Eventually.of_forall fun t => pk_norm_le P hQ τ₀ k t)
    refine h1.mul_bdd (c := 1) (Continuous.aestronglyMeasurable (by fun_prop))
      (Eventually.of_forall fun t => ?_)
    rw [Complex.norm_exp]; simp
  have hzero : ∀ ξ : ℝ, P.L Q ≤ |ξ| → ∫ t : ℝ, K t * Complex.exp (Complex.I * ξ * t) = 0 :=
    fun ξ hξ => integral_pk_pk_exp P hQ τ₀ k l hξ
  -- expand `D`
  have hD : ∀ t : ℝ, (Dtail P Q χ t : ℂ) = ∑ n ∈ S,
      ((-(1 / (2 * Real.pi)) * (P.aVec Q n * χ n : ℂ)) *
        Complex.exp (Complex.I * ((-Real.log n : ℝ) : ℂ) * t) +
      (-(1 / (2 * Real.pi)) * (P.aVec Q n * conj (χ n) : ℂ)) *
        Complex.exp (Complex.I * (Real.log n) * t)) := by
    intro t
    unfold Dtail
    rw [Complex.ofReal_mul, Complex.re_eq_add_conj, map_sum, ← Finset.sum_add_distrib,
      Finset.sum_div, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 := hn1 n hn
    rw [PrimeSetup.natCast_cpow n hn0]
    simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_neg, Complex.conj_I]
    have e1 : Complex.exp (↑(Real.log ↑n) * -(Complex.I * ↑t)) =
        Complex.exp (Complex.I * ↑(-Real.log ↑n) * ↑t) := by congr 1; push_cast; ring
    have e2 : Complex.exp (↑(Real.log ↑n) * -(-Complex.I * ↑t)) =
        Complex.exp (Complex.I * ↑(Real.log ↑n) * ↑t) := by congr 1; push_cast; ring
    rw [e1, e2]
    push_cast
    ring
  simp_rw [hD, Finset.mul_sum]
  rw [integral_finsetSum]
  · refine Finset.sum_eq_zero fun n hn => ?_
    have hA : ∀ (c : ℂ) (ξ : ℝ), ∫ t : ℝ, K t * (c * Complex.exp (Complex.I * ξ * t)) =
        c * ∫ t : ℝ, K t * Complex.exp (Complex.I * ξ * t) := by
      intro c ξ
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_); simp only; ring
    have hsplit : ∀ t : ℝ, P.pk Q τ₀ k t * P.pk Q τ₀ l t *
        ((-(1 / (2 * Real.pi)) * (P.aVec Q n * χ n : ℂ)) *
            Complex.exp (Complex.I * ((-Real.log n : ℝ) : ℂ) * t) +
          (-(1 / (2 * Real.pi)) * (P.aVec Q n * conj (χ n) : ℂ)) *
            Complex.exp (Complex.I * (Real.log n) * t)) =
        K t * ((-(1 / (2 * Real.pi)) * (P.aVec Q n * χ n : ℂ)) *
            Complex.exp (Complex.I * ((-Real.log n : ℝ) : ℂ) * t)) +
        K t * ((-(1 / (2 * Real.pi)) * (P.aVec Q n * conj (χ n) : ℂ)) *
            Complex.exp (Complex.I * (Real.log n) * t)) := by
      intro t; simp only [hK]; ring
    simp_rw [hsplit]
    have hi1 := (hKi (-Real.log n)).const_mul (-(1 / (2 * Real.pi)) * (P.aVec Q n * χ n : ℂ))
    have hi2 := (hKi (Real.log n)).const_mul
      (-(1 / (2 * Real.pi)) * (P.aVec Q n * conj (χ n) : ℂ))
    rw [integral_add (hi1.congr (Eventually.of_forall fun t => by simp only; ring))
      (hi2.congr (Eventually.of_forall fun t => by simp only; ring)), hA, hA]
    have hl := hlog n hn
    have hl0 : 0 ≤ Real.log n := le_trans hL.le hl
    rw [hzero _ (by rw [abs_neg, abs_of_nonneg hl0]; exact hl),
      hzero _ (by rw [abs_of_nonneg hl0]; exact hl)]
    ring
  · intro n hn
    have hi1 := (hKi (-Real.log n)).const_mul (-(1 / (2 * Real.pi)) * (P.aVec Q n * χ n : ℂ))
    have hi2 := (hKi (Real.log n)).const_mul
      (-(1 / (2 * Real.pi)) * (P.aVec Q n * conj (χ n) : ℂ))
    refine (hi1.add hi2).congr (Eventually.of_forall fun t => ?_)
    simp only [hK, Pi.add_apply]; ring

/-- **`lem:explicit` with the smooth cut-off** from the sharp one (Lemma 2.6 and its proof). -/
theorem explicitGabor_of_sharp (hS : ExplicitGaborSharp_Statement) : ExplicitGabor_Statement := by
  intro P W
  have hη := W.η_pos
  refine ⟨max 2 (2 / W.η), fun Q hQ T hT τ₀ q χ hχ k l => ?_⟩
  have hQ2 : 2 ≤ Q := le_trans (le_max_left _ _) hQ
  have hQ1 : 1 < Q := by linarith
  have hQη : 2 / W.η ≤ Q := le_trans (le_max_right _ _) hQ
  obtain ⟨hprim, hw⟩ := hχ
  have hq : 1 < q := by
    have hsupp := (W.supp _ hw.ne').1
    have hQ0 : 0 < Q := by linarith
    rw [le_div_iff₀ hQ0] at hsupp
    rw [div_le_iff₀ hη] at hQη
    have : (1 : ℝ) < q := by nlinarith
    exact_mod_cast this
  have : NeZero q := ⟨by omega⟩
  obtain ⟨hint, hG⟩ := hS P Q τ₀ hQ1 q χ hq hprim T k l
  rw [hG]
  have e : ∀ t : ℝ, P.pk Q τ₀ k t * P.pk Q τ₀ l t * (nuChi P Q χ t : ℂ) =
      P.pk Q τ₀ k t * P.pk Q τ₀ l t * (nuSharp P Q χ t : ℂ) +
        P.pk Q τ₀ k t * P.pk Q τ₀ l t * (Dtail P Q χ t : ℂ) := by
    intro t; rw [nuChi_eq P hQ1 χ t]; push_cast; ring
  simp_rw [e]
  have hDint : Integrable (fun t : ℝ => P.pk Q τ₀ k t * P.pk Q τ₀ l t * (Dtail P Q χ t : ℂ)) := by
    -- integrable: `p_k` bounded, `p_l` integrable, `D` bounded continuous
    have hKi : Integrable (fun t : ℝ => P.pk Q τ₀ k t * P.pk Q τ₀ l t) :=
      (pk_integrable P hQ1 τ₀ l).bdd_mul (c := ∫ u, ‖fK P Q τ₀ k u‖)
        (pk_continuous P hQ1 τ₀ k).aestronglyMeasurable
        (Eventually.of_forall fun t => pk_norm_le P hQ1 τ₀ k t)
    have hDb : ∀ t, ‖(Dtail P Q χ t : ℂ)‖ ≤ 1 / Real.pi * ∑ n ∈ Finset.Ioc ⌊P.X Q⌋₊ ⌊P.Y Q⌋₊,
        |P.aVec Q n| := by
      intro t
      unfold Dtail
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_neg,
        abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi)]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
      refine Finset.sum_le_sum fun n hn => ?_
      have hn1 : 1 ≤ n := by have := (Finset.mem_Ioc.mp hn).1; omega
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
      have h2 : ‖(n : ℂ) ^ (-(Complex.I * t))‖ = 1 := by
        rw [Complex.norm_natCast_cpow_of_pos (by omega)]; simp
      rw [h2, mul_one]
      calc |P.aVec Q n| * ‖χ n‖ ≤ |P.aVec Q n| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = |P.aVec Q n| := mul_one _
    have hDc : Continuous (fun t : ℝ => (Dtail P Q χ t : ℂ)) := by
      unfold Dtail
      refine Complex.continuous_ofReal.comp (continuous_const.mul
        (Complex.continuous_re.comp (continuous_finsetSum _ fun n hn => ?_)))
      have hn1 : 1 ≤ n := by have := (Finset.mem_Ioc.mp hn).1; omega
      have hn0 : 0 < ((n : ℂ)).re := by simp; exact_mod_cast hn1
      exact continuous_const.mul (continuous_const.cpow (by fun_prop) fun _ => Or.inl hn0)
    exact hKi.mul_bdd hDc.aestronglyMeasurable (Eventually.of_forall hDb)
  rw [integral_add hint hDint, integral_pk_pk_Dtail P hQ1 τ₀ k l χ, add_zero]

end Bridge

end Families.Ported.Second
