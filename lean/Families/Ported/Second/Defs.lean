/-
# Prime side (paper §5): definitions and the interface to the explicit formula

Notation of `main.tex` §2.4 (`sec:explicit`):

* `aChi χ = 𝔞_χ = (1 − χ(−1))/2 ∈ {0,1}`;
* `muChi χ t = μ_χ(t) = (1/2π) log(q/π) + (1/2π) Re ψ((1/2 + 𝔞_χ + it)/2)` (`eq:mu`), written with
  `Families.digammaRe`;
* `PChi P Q χ t = P_χ(t) = −(1/2π)(S_χ[a](t) + conj S_χ[a](t)) = −(1/π) Re S_χ[a](t)` (`eq:an`);
* `nuChi = ν_χ = μ_χ + P_χ`;
* `Mcal P W Q T = 𝓜 = ∑_χ ω_χ ∬_{J²} Φ(t−t')² ν_χ(t) ν_χ(t') dt dt'` (§5.1).

`ExplicitGabor_Statement` is `lem:explicit` (Lemma 2.6), in the weakest form used here: for
`χ ∈ 𝓕(Q)`, large `Q`, admissible `T` and `k, l ∈ K_J`, `G_{χ,kl} = ∫ p_k(t) p_l(t) ν_χ(t) dt`.
It is the interface to the zero side (Weil's explicit formula, Appendix B); here it is only a hypothesis
(it is proved in `Families/Ported/Zero/ExplicitFormula.lean` and supplied in `Families/Ported/Full.lean`).
-/
import Families.Classical.Reductions

noncomputable section

open scoped BigOperators ComplexConjugate ArithmeticFunction.Moebius ENNReal ContDiff
open ArithmeticFunction Finset MeasureTheory Filter Topology

namespace Families.Ported.Second

open Families

/-- `𝔞_χ = (1 − χ(−1))/2`: `0` for even `χ`, `1` otherwise. -/
def aChi {q : ℕ} (χ : DirichletCharacter ℂ q) : ℝ := if χ (-1) = 1 then 0 else 1

/-- `μ_χ(t) = (1/2π) log(q/π) + (1/2π) Re (Γ'/Γ)((1/2 + 𝔞_χ + it)/2)` (`eq:mu`). -/
def muChi {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) : ℝ :=
  1 / (2 * Real.pi) * Real.log (q / Real.pi) + 1 / (2 * Real.pi) * digammaRe (aChi χ) t

/-- `P_χ(t) = −(1/2π)(S_χ[a](t) + \overline{S_χ[a](t)}) = −(1/π) Re S_χ[a](t)` (`eq:an`). -/
def PChi (P : PrimeSetup) (Q : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) : ℝ :=
  -(1 / Real.pi) * (P.Schi χ Q (P.aVec Q) t).re

/-- `ν_χ = μ_χ + P_χ`. -/
def nuChi (P : PrimeSetup) (Q : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) : ℝ :=
  muChi χ t + PChi P Q χ t

/-- `Φ(r)²` as a real number (`Φ` is real-valued since `ψ_L²` is real and even). -/
def PhiSq (P : PrimeSetup) (Q r : ℝ) : ℝ := (P.Φ Q r ^ 2).re

/-- `𝓜 = ∑_{χ∈𝓕} ω_χ ∬_{J²} Φ(t−t')² ν_χ(t) ν_χ(t') dt dt'` (§5.1, before `eq:split`). -/
def Mcal (P : PrimeSetup) (W : Weight) (Q T : ℝ) : ℝ :=
  famSum W Q fun _ χ =>
    ∫ t in P.J T, ∫ t' in P.J T, PhiSq P Q (t - t') * nuChi P Q χ t * nuChi P Q χ t'

/-- The mixed term `M_{μΛ} = ∑_χ ω_χ ∬_{J²} Φ(t−t')² μ_χ(t) P_χ(t') dt dt'` (`eq:split`). -/
def Mmix (P : PrimeSetup) (W : Weight) (Q T : ℝ) : ℝ :=
  famSum W Q fun _ χ =>
    ∫ t in P.J T, ∫ t' in P.J T, PhiSq P Q (t - t') * muChi χ t * PChi P Q χ t'

/-- The archimedean term `M_{μμ} = ∑_χ ω_χ ∬_{J²} Φ(t−t')² μ_χ(t) μ_χ(t') dt dt'` (`eq:split`). -/
def Mmumu (P : PrimeSetup) (W : Weight) (Q T : ℝ) : ℝ :=
  famSum W Q fun _ χ =>
    ∫ t in P.J T, ∫ t' in P.J T, PhiSq P Q (t - t') * muChi χ t * muChi χ t'

/-- The same-sign sum `∑_χ ω_χ ∬_{J²} Φ(t−t')² S_χ[a](t) S_χ[a](t') dt dt'` (complex); the same-sign
term of `eq:Mrat` is `M^{ss}_{ΛΛ} = (1/2π²) Re SSC`. -/
def SSC (P : PrimeSetup) (W : Weight) (Q T : ℝ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (W.omega Q q : ℂ) * ∑ χ ∈ primChars q,
    ∫ t in P.J T, ∫ t' in P.J T,
      (PhiSq P Q (t - t') : ℂ) * P.Schi χ Q (P.aVec Q) t * P.Schi χ Q (P.aVec Q) t'

/-- **`lem:explicit`** (Lemma 2.6; interface, Weil's explicit formula,
Appendix B): for `χ ∈ 𝓕(Q)` and `k, l ∈ K_J`, `G_{χ,kl} = ∫_ℝ p_k(t) p_l(t) ν_χ(t) dt`.
Stated in the weakest form used by the prime side (all large `Q`, admissible `T`); the TeX statement
(every `χ ∈ 𝓕`, every `Q`, `T`, `τ₀`) implies it. -/
def ExplicitGabor_Statement : Prop :=
  ∀ (P : PrimeSetup) (W : Weight), ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ P.heights Q, ∀ τ₀ : ℝ,
    ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), InFamily W Q q χ →
    ∀ k l : P.KJ Q T τ₀,
      P.Gabor Q T τ₀ χ k l =
        ∫ t : ℝ, P.pk Q τ₀ k (t : ℂ) * P.pk Q τ₀ l (t : ℂ) * (nuChi P Q χ t : ℂ)

/-- **Finite-centre replacement, upper half** (`eq:fc2`, display (4.3), in the `o(N)` form used by
`prop:second`): `𝔐 ≤ 𝓜/(aL)² + o(HTℓ)`, uniformly in `T` and for each fixed `τ₀`. -/
def FC2_Statement : Prop :=
  ∀ (P : PrimeSetup) (W : Weight) (τ₀ : ℝ), ∀ δ : ℝ, 0 < δ → ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
    ∀ T ∈ P.heights Q,
      P.Mfrak W Q T τ₀ ≤ Mcal P W Q T / (P.aInt * P.L Q) ^ 2 + δ * (W.H Q * T * ell Q)

/-- **The prime-side bound for `𝓜`** (proof of `prop:second`, Proposition 5.13: `lem:mumu`, `lem:muLambda`, `lem:ss` and
the ratio terms): under the profile bound `eq:profile`,
`𝓜 ≤ (aL)² (H|J|ℓ/2π) 𝒬_F(f_v) + o(H T L² ℓ)`, `F(α) = c(α) min(α, 1+ε₄)`, `f_v(x) = v(x/λ)/(λa)`.
(`(aL)²(H|J|ℓ/2π)𝒬_F(f_v) = (H|J|Lℓ²/2π)(b + 2λ∫₀¹F(λs)(v*v)(s)ds)`.) -/
def McalBound_Statement : Prop :=
  ∀ (P : PrimeSetup) (W : Weight) (c : ℝ → ℝ), ContDiff ℝ ∞ c → (∀ α, 1 ≤ c α) →
    P.ProfileBound W c →
    ∀ δ : ℝ, 0 < δ → ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ P.heights Q,
      Mcal P W Q T ≤
        (P.aInt * P.L Q) ^ 2 * (W.H Q * P.Jlen T * ell Q / (2 * Real.pi)) *
          Qf (fun α => c α * min α (1 + 2 * P.ε₃))
            (fun x => P.vfun (x / P.lam) / (P.lam * P.aInt)) +
        δ * (W.H Q * T * P.L Q ^ 2 * ell Q)

end Families.Ported.Second
