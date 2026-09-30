/-
The main chain of main.tex: zero counts, the Gabor matrices, `prop:zero`, `prop:second`,
`hyp:LS` (LS(C)), `thm:conditional` (LS(C) ⇒ p(C)), `thm:gauss`, `thm:main`, `thm:fixed`,
and `lem:pLip`.

Structure (see STATEMENTS.md and STATUS.md):
* `propZero_Statement`, `propSecond_Statement` enter the proof of `thm:main` as conclusions of
  `ZeroSideReduction`, `SecondMomentAssembly` (`Families/Classical/Reductions.lean`); both are proved
  (`Families/Ported/`).
* `thmMain_Statement` is proved in `Families/Headline.lean` (`thmMain`, no hypotheses).
* `assemblyLimit` ((a)) isolates the limit part of the assembly (`lem:windows`, choice of the
  fixed data, dominated convergence in `ε, ε₄ → 0`); proved in `Families/Wired/Phase4.lean`.
* `thmConditional_Statement`, `thmGauss_Statement`, `thmFixed_Statement` are (c): off the headline chain,
  stated only (not proved in this project).
-/
import Families.PrimeSide
import Families.Variational
import Families.PLip
import Families.Certificate.Ecal

noncomputable section

open scoped BigOperators ComplexConjugate ArithmeticFunction.Moebius ENNReal ContDiff
open ArithmeticFunction Finset MeasureTheory Filter Topology

namespace Families

/-! ### Zero counts (main.tex §1) -/

-- `Lfun` (`L(s,χ)`) and `mult` (multiplicity of a zero) are defined in `Families.Classical`.

/-- The zeros of `L(s,χ)` with ordinate `γ ∈ I = (T, 2T]`. For `T > 0` these are nontrivial zeros
(the trivial zeros are real). -/
def zerosI {q : ℕ} (χ : DirichletCharacter ℂ q) (T : ℝ) : Set ℂ :=
  {ρ | Lfun χ ρ = 0 ∧ T < ρ.im ∧ ρ.im ≤ 2 * T}

/-- `N_χ`: zeros with `γ ∈ I`, with multiplicity. -/
def Nchi {q : ℕ} (χ : DirichletCharacter ℂ q) (T : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosI χ T, mult χ ρ
/-- `N^s_{0,χ}`: simple zeros with `β = 1/2`, `γ ∈ I`. -/
def Ns0chi {q : ℕ} (χ : DirichletCharacter ℂ q) (T : ℝ) : ℕ :=
  Set.ncard {ρ | ρ ∈ zerosI χ T ∧ ρ.re = 1 / 2 ∧ mult χ ρ = 1}
/-- `N^*_{0,χ}`: distinct zeros with `β = 1/2`, `γ ∈ I`. -/
def Nstar0chi {q : ℕ} (χ : DirichletCharacter ℂ q) (T : ℝ) : ℕ :=
  Set.ncard {ρ | ρ ∈ zerosI χ T ∧ ρ.re = 1 / 2}
/-- `N_{d,χ}`: distinct zeros with `γ ∈ I`. -/
def Ndchi {q : ℕ} (χ : DirichletCharacter ℂ q) (T : ℝ) : ℕ := Set.ncard (zerosI χ T)

/-- `∑_{χ ∈ 𝓕} ω_χ c(χ)`. -/
def famSum (W : Weight) (Q : ℝ) (c : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ χ ∈ primChars q, c q χ

/-- `N = ∑ ω_χ N_χ`, `N^s_0`, `N^*_0`, `N_d`. -/
def Nfam (W : Weight) (Q T : ℝ) : ℝ := famSum W Q fun _ χ => Nchi χ T
def Ns0 (W : Weight) (Q T : ℝ) : ℝ := famSum W Q fun _ χ => Ns0chi χ T
def Nstar0 (W : Weight) (Q T : ℝ) : ℝ := famSum W Q fun _ χ => Nstar0chi χ T
def Nd (W : Weight) (Q T : ℝ) : ℝ := famSum W Q fun _ χ => Ndchi χ T

/-! ### Gabor matrices and `𝔐` (main.tex §2.4 and §3, `eq:Gdef`, `eq:Mfrak`) -/

namespace PrimeSetup
variable (P : PrimeSetup)

/-- `\widehat{ψ_L}(w) = ∫ ψ_L(u) e^{iwu} du` (entire in `w`). -/
def hatψL (Q : ℝ) (w : ℂ) : ℂ := ∫ u, (P.ψL Q u : ℂ) * Complex.exp (Complex.I * w * u)
/-- The lattice `K_J = {k ∈ ℤ : τ_k ∈ J}`, `τ_k = τ₀ + 2πk/L`. -/
def KJ (Q T τ₀ : ℝ) : Finset ℤ :=
  (Finset.Icc ⌈((1 + P.θ) * T - τ₀) * P.L Q / (2 * Real.pi)⌉
    ⌊((2 - P.θ) * T - τ₀) * P.L Q / (2 * Real.pi)⌋)
/-- `p_k(z) = \widehat{ψ_L}(z − τ_k)`. -/
def pk (Q τ₀ : ℝ) (k : ℤ) (z : ℂ) : ℂ := P.hatψL Q (z - (τ₀ + 2 * Real.pi * k / P.L Q))
/-- The nontrivial zeros (critical strip). -/
def strip {q : ℕ} (χ : DirichletCharacter ℂ q) : Set ℂ :=
  {ρ | Lfun χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}
/-- The Gabor matrix `G_{χ,kl} = ∑_ρ m_ρ p_k(z_ρ) p_l(z_ρ)`, `z_ρ = (ρ − 1/2)/i` (`eq:Gdef`). -/
def Gabor (Q T τ₀ : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Matrix (P.KJ Q T τ₀) (P.KJ Q T τ₀) ℂ := fun k l =>
  ∑' ρ : strip χ, (mult χ ρ : ℂ) * P.pk Q τ₀ k ((ρ - 1 / 2) / Complex.I) *
    P.pk Q τ₀ l ((ρ - 1 / 2) / Complex.I)
/-- `𝔐 = ∑_χ ω_χ ‖Ĝ_χ‖_F²`, `Ĝ_χ = G_χ/(aL²)` (`eq:Mfrak`). -/
def Mfrak (W : Weight) (Q T τ₀ : ℝ) : ℝ :=
  famSum W Q fun _ χ =>
    ∑ k, ∑ l, ‖P.Gabor Q T τ₀ χ k l / (P.aInt * P.L Q ^ 2)‖ ^ 2

end PrimeSetup

/-! ### `prop:zero` and `prop:second` (main.tex §3, §4.5, §5.9) -/

/-- **`prop:zero`** (zero-side reduction; (b): enters only through the named hypothesis
`ZeroSideReduction`). For every `B > 0`, uniformly in `T`:
`N^s_0, N^*_0 ≥ (2−8θ)N − 𝔐 − o(N) − O_B(ℓ^{-B}(H𝔐)^{1/2})` and
`N_d ≥ ½((3−8θ)N − 𝔐) − o(N) − O_B(ℓ^{-B}(H𝔐)^{1/2})`. -/
def propZero_Statement : Prop :=
  ∀ (P : PrimeSetup) (W : Weight) (τ₀ B δ : ℝ), 0 < B → 0 < δ → ∃ C Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
    ∀ T ∈ P.heights Q,
      let N := Nfam W Q T
      let M := P.Mfrak W Q T τ₀
      let err := δ * N + C * Real.log Q ^ (-B) * Real.sqrt (W.H Q * M)
      (2 - 8 * P.θ) * N - M - err ≤ Ns0 W Q T ∧
      (2 - 8 * P.θ) * N - M - err ≤ Nstar0 W Q T ∧
      ((3 - 8 * P.θ) * N - M) / 2 - err ≤ Nd W Q T

/-- **`prop:second`** (second moment with a profile; (b): enters only through the named hypothesis
`SecondMomentAssembly`). If `c : ℝ → [1,∞)` is smooth and the profile bound `eq:profile`
(`P.ProfileBound W c`) holds uniformly in `T`, then `𝔐 ≤ (1−2θ) 𝒬_F(f_v) N + o(N)` with
`F(α) = c(α) min(α, 1+ε₄)`, `ε₄ = 2ε₃`, `f_v(x) = v(x/λ)/(λa)`. -/
def propSecond_Statement : Prop :=
  ∀ (P : PrimeSetup) (W : Weight) (τ₀ : ℝ) (c : ℝ → ℝ), ContDiff ℝ ∞ c → (∀ α, 1 ≤ c α) →
    P.ProfileBound W c →
    ∀ δ : ℝ, 0 < δ → ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ P.heights Q,
      P.Mfrak W Q T τ₀ ≤
        (1 - 2 * P.θ) * Qf (fun α => c α * min α (1 + 2 * P.ε₃))
          (fun x => P.vfun (x / P.lam) / (P.lam * P.aInt)) * Nfam W Q T + δ * Nfam W Q T

/-! ### `hyp:LS` and `thm:conditional` -/

/-- **`hyp:LS` (LS(C)).** For every `ε > 0`, uniformly in `K ≤ Q^{2−ε}`: `Λ_mult(K) ≤ (C + o(1)) H`. -/
def LS (W : Weight) (C : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
    ∀ K : ℕ, (K : ℝ) ≤ Q ^ (2 - ε) → LmultLE W Q K ((C + δ) * W.H Q)

/-- The three conclusions `liminf_Q inf_T N^s_0/N ≥ p`, `N^*_0/N ≥ p`, `N_d/N ≥ (1+p)/2`
(for fixed `0 < a₀ < A₀`, `ℓ^{a₀} ≤ T ≤ ℓ^{A₀}`), in `ε`–`Q₀` form. -/
def ProportionsAtLeast (W : Weight) (a0 A0 p : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
    ∀ T ∈ Set.Icc (Real.log Q ^ a0) (Real.log Q ^ A0),
      (p - ε) * Nfam W Q T ≤ Ns0 W Q T ∧ (p - ε) * Nfam W Q T ≤ Nstar0 W Q T ∧
      ((1 + p) / 2 - ε) * Nfam W Q T ≤ Nd W Q T

/-- **`thm:conditional` (Theorem A′).** If `LS(C)` holds for `𝓕(Q,w)`, then
`liminf_Q inf_T N^s_0/N ≥ p(C)`, `N^*_0/N ≥ p(C)`, `N_d/N ≥ (1+p(C))/2`.

Stated only; not proved in this project (see README). The implication
`Phase4.A.thmConditional_of_components` derives it from the profile bound `profileLS_Statement` (`prop:TI`
re-run with `LS(C)` in place of `cor:LmultA`, `main.tex` §7.3), which is not proved here, together with
`lem:B2`, `eqB:Mrat` and the named hypotheses. `thm:main` does not use this statement: its proof reuses the
*proof* of `thm:conditional` (`assembly_fixed` + `assemblyLimit`). -/
def thmConditional_Statement : Prop :=
  ∀ (W : Weight) (C a0 A0 : ℝ), 0 < a0 → a0 < A0 → LS W C → ProportionsAtLeast W a0 A0 (pC C)

/-! ### `assemblyLimit`: the limit part of the assembly ((a)) -/

/-- The certified value `2 − 8θ − (1−2θ) 𝒬_F(f_v)` for the fixed data `P` and a profile `c`, with
`F(α) = c(α) min(α, 1+ε₄)`, `ε₄ = 2ε₃`, `f_v(x) = v(x/λ)/(λa)` (proof of `thm:conditional`, Theorem 5.16:
`N^s_0 ≥ (2 − 8θ − (1−2θ)𝒬_{F_ε}(f_v) − o(1)) N`). -/
def PrimeSetup.certValue (P : PrimeSetup) (c : ℝ → ℝ) : ℝ :=
  2 - 8 * P.θ - (1 - 2 * P.θ) *
    Qf (fun α => c α * min α (1 + 2 * P.ε₃)) (fun x => P.vfun (x / P.lam) / (P.lam * P.aInt))

/-- **Assembly limit** ((a)). This isolates the analytic limit step of the proofs of
`thm:conditional` and `thm:main` (§7.3, `sec:assembly`): given `1 ≤ C ≤ C_max` and `η' > 0`,
there are fixed data `P` (with the prescribed `a₀ < A₀`) and a band parameter `ε ∈ (0, 1/3)`,
`ε < ε₁/4`, such that for **every** continuous profile `C̃ : ℝ → [1, C_max]` with `C̃ = 1` on
`(−∞, 1−2ε]` and `C̃ = C` on `[1+2ε, ∞)`,
`P.certValue C̃ = 2 − 8θ − (1−2θ) 𝒬_F(f_v) ≥ p(C) − η'`, `F(α) = C̃(α) min(α, 1+ε₄)`, `ε₄ = 2ε₃`,
`f_v(x) = v(x/λ)/(λa)`.

Mathematical content: choose an even admissible `f` with `2 − 𝒬_{F_C}(f) ≥ p(C) − η'/3`; `lem:windows`
(Lemma 7.2) gives `λ < 2` and an even window `ψ ∈ C_c^∞((−½,½))` with
`𝒬_{F_C}(f_v) ≤ 𝒬_{F_C}(f) + η'/3`; then choose `ε₁`, the cut-offs `Υ₀`, `(ψ_j)`, and `θ, ε, ε₃` so small
that `8θ + |𝒬_F(f_v) − 𝒬_{F_C}(f_v)| ≤ η'/3` uniformly in `C̃` (`F → F_C` off `α = 1`, `|F| ≤ 2C_max`:
dominated convergence, proofs of Theorems 5.16 and 1.1 in §7.3). This is not a labelled result of the paper; it is
the part of §7.3 that is not "plumbing". -/
def assemblyLimit_Statement : Prop :=
  ∀ (a0 A0 : ℝ), 0 < a0 → a0 < A0 → ∀ (C Cmax : ℝ), 1 ≤ C → C ≤ Cmax → ∀ η' : ℝ, 0 < η' →
    ∃ (P : PrimeSetup) (ε : ℝ), P.a0 = a0 ∧ P.A0 = A0 ∧ 0 < ε ∧ ε < 1 / 3 ∧ ε < P.ε₁ / 4 ∧
      ∀ Ct : ℝ → ℝ, Continuous Ct → (∀ α, 1 ≤ Ct α ∧ Ct α ≤ Cmax) →
        (∀ α, α ≤ 1 - 2 * ε → Ct α = 1) → (∀ α, 1 + 2 * ε ≤ α → Ct α = C) →
        pC C - η' ≤ P.certValue Ct

-- `assemblyLimit` is proved in `Families/Wired/Phase4.lean` (wired from Families/Phase4/A/*).

/-! ### `thm:gauss`, `thm:main`, `thm:fixed` -/

/-- **`thm:gauss`** ((c): Gauss route, off the headline chain). (1) For every admissible `w`: `liminf inf_T N^s_0/N ≥ p(C_G R_w)` (etc.).
(2) For every `ε > 0` there is `η₀` with: for `η ≤ η₀` and `w ∈ {w_η, w^sm_η}`, the proportions are
`≥ p(C_G) − ε`; and `p(C_G) ≥ 0.885912`.

Stated only; not proved in this project (see README). -/
def thmGauss_Statement : Prop :=
  (∀ (W : Weight) (a0 A0 : ℝ), 0 < a0 → a0 < A0 → ProportionsAtLeast W a0 A0 (pC (Cw W))) ∧
  (∀ (a0 A0 ε : ℝ), 0 < a0 → a0 < A0 → 0 < ε → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
    ∀ W : Weight, (W.w = wSharpFun η ∨ W.w = wSmoothFun η) →
      ProportionsAtLeast W a0 A0 (pC CG - ε)) ∧
  (0.885912 : ℝ) ≤ pC CG

/-- **`thm:main`.** For every `ε > 0` there is `η₀(ε) > 0` such that for `η ≤ η₀` and
`w ∈ {w_η, w^sm_η}`: `liminf inf_T N^s_0/N ≥ p(1) − ε ≥ 0.9322 − ε`, the same for `N^*_0/N`, and
`N_d/N ≥ (1+p(1))/2 − ε`. -/
def thmMain_Statement : Prop :=
  (∀ (a0 A0 ε : ℝ), 0 < a0 → a0 < A0 → 0 < ε → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
    ∀ W : Weight, (W.w = wSharpFun η ∨ W.w = wSmoothFun η) →
      ProportionsAtLeast W a0 A0 (pC 1 - ε)) ∧
  (0.932282 : ℝ) ≤ pC 1

-- `thmMain` (the headline, `thmMain_Statement` with no hypotheses) and the glue theorems are in
-- `Families.Headline`.

/-- **`thm:fixed`** ((c); fixed `η`; numerical input stated as a hypothesis), `w = w^sm_η`:
(i) `η = 10⁻³`: `C_T^+(w) ≤ 1.0911 ⇒` proportions `≥ 0.9155` (`N_d/N ≥ 0.9577`);
(ii) `η = 10⁻⁴`: `C_T^+(w) ≤ 1.0434 ⇒` `≥ 0.9241` (`N_d/N ≥ 0.9620`);
(iii) Gauss route: `R_w ≤ 1.0599, 1.0289, 1.0159` for `η = 10⁻³, 10⁻⁴, 10⁻⁵` ⇒ `≥ 0.8744, 0.8802, 0.8827`.
(Formally: `ProportionsAtLeast` with the stated `p`; the `N_d` bound is `(1+p)/2` with the certified `p`.)

Stated only; not proved in this project (see README). -/
def thmFixed_Statement : Prop :=
  ∀ (a0 A0 : ℝ), 0 < a0 → a0 < A0 → ∀ W : Weight,
    (W.w = wSmoothFun (1 / 1000) → CTp W ≤ ENNReal.ofReal 1.0911 →
      ProportionsAtLeast W a0 A0 0.9155) ∧
    (W.w = wSmoothFun (1 / 10000) → CTp W ≤ ENNReal.ofReal 1.0434 →
      ProportionsAtLeast W a0 A0 0.9241) ∧
    (W.w = wSmoothFun (1 / 1000) → Rw W ≤ ENNReal.ofReal 1.0599 →
      ProportionsAtLeast W a0 A0 0.8744) ∧
    (W.w = wSmoothFun (1 / 10000) → Rw W ≤ ENNReal.ofReal 1.0289 →
      ProportionsAtLeast W a0 A0 0.8802) ∧
    (W.w = wSmoothFun (1 / 100000) → Rw W ≤ ENNReal.ofReal 1.0159 →
      ProportionsAtLeast W a0 A0 0.8827)

/-! ### `lem:pLip` -/

/-- **`lem:pLip`.** `p` is nonincreasing and `p(C') ≥ p(C) − (C' − C)` for `C' ≥ C ≥ 1`. -/
def lemPLip_Statement : Prop :=
  ∀ C C' : ℝ, 1 ≤ C → C ≤ C' → pC C' ≤ pC C ∧ pC C - (C' - C) ≤ pC C'

theorem lemPLip : lemPLip_Statement := fun C C' hC h => pC_antitone_lip C C' hC h

/-- `C_G ≤ 1.2688` (numerical: `C_G = 1.268773…`); proved in `Families.Certificate.Ecal`
(`ℰ ≥ 0.47914` from a kernel-checked partial Euler product over `p ≤ 50000` plus a tail bound). -/
theorem CG_le : CG ≤ 1.2688 := CG_le_12688

end Families
