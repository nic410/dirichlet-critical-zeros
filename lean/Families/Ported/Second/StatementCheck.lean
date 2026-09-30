/-
Statement check: Lean parsing of the statements consumed by `SecondMomentAssembly`.
Each `example` pins a statement to an explicitly parenthesised form by `Iff.rfl` / `rfl`.
-/
import Families.Ported.Second.Defs

open scoped BigOperators ContDiff
open Families Families.Ported.Second

namespace Families.Ported.Second.StatementCheck

/-- `eq:profile`: the `∑` does not absorb the trailing `+ δ H |J| L² ℓ`. -/
example (P : PrimeSetup) (W : Weight) (c : ℝ → ℝ) :
    P.ProfileBound W c ↔ ∀ δ : ℝ, 0 < δ → ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ P.heights Q,
      (P.ratioForm W Q T (P.bVec Q T)).re ≤
        ((1 + δ) * W.H Q * (∑ n ∈ P.range Q,
          (P.bVec Q T n ^ 2 * c (Real.log n / ell Q) * (P.𝒦 Q T n n).re))) +
        (δ * W.H Q * P.Jlen T * P.L Q ^ 2 * ell Q) := Iff.rfl

/-- `prop:second`. -/
example : propSecond_Statement ↔
    ∀ (P : PrimeSetup) (W : Weight) (τ₀ : ℝ) (c : ℝ → ℝ), ContDiff ℝ ∞ c → (∀ α, 1 ≤ c α) →
    P.ProfileBound W c →
    ∀ δ : ℝ, 0 < δ → ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ P.heights Q,
      P.Mfrak W Q T τ₀ ≤
        ((1 - 2 * P.θ) * Qf (fun α => c α * min α (1 + 2 * P.ε₃))
          (fun x => P.vfun (x / P.lam) / (P.lam * P.aInt)) * Nfam W Q T) + (δ * Nfam W Q T) :=
  Iff.rfl

/-- `Qf`: the first integral is closed before `+`. -/
example (F f : ℝ → ℝ) : Qf F f = (∫ x, f x ^ 2) + (∫ x, ∫ y, f x * f y * F |x - y|) := rfl

/-- `ratioForm`: the kernel entries use the `ℤ`-casts of `n, m`. -/
example (P : PrimeSetup) (W : Weight) (Q T : ℝ) (x : ℕ → ℝ) :
    P.ratioForm W Q T x = ∑ n ∈ P.range Q, ∑ m ∈ P.range Q,
      (((x n : ℂ) * (x m : ℂ)) * Δ W Q (n : ℤ) (m : ℤ)) * P.𝒦 Q T n m := rfl

/-- `𝔐`: the Frobenius sum is over `K_J × K_J` and inside the family sum. -/
example (P : PrimeSetup) (W : Weight) (Q T τ₀ : ℝ) :
    P.Mfrak W Q T τ₀ = ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ χ ∈ primChars q,
      (∑ k, ∑ l, ‖P.Gabor Q T τ₀ χ k l / (P.aInt * P.L Q ^ 2)‖ ^ 2) := rfl

/-- `lemRvM_lower`. -/
example : lemRvM_lower_Statement ↔
    ∀ (W : Weight) (a0 A0 : ℝ), 0 < a0 → a0 < A0 → ∀ δ : ℝ, 0 < δ → ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
      ∀ T ∈ Set.Icc (Real.log Q ^ a0) (Real.log Q ^ A0),
        ((1 - δ) * (W.H Q * T * Real.log Q / (2 * Real.pi))) ≤ Nfam W Q T := Iff.rfl

end Families.Ported.Second.StatementCheck
