/-
# Montgomery 1969 density: shared definitions

* `beta X N n = ∑_{d ∣ n, d ≤ X, n/d ≤ N} μ(d)`: the coefficients of the product of the mollifier
  `M_X(s,χ) = ∑_{d≤X} μ(d)χ(d)d^{-s}` with the partial sum `∑_{m≤N} χ(m)m^{-s}`.
* `Montgomery69_Density_upTo A`: `Families.Montgomery69_Density` restricted to heights `T' ≤ Q^A`
  (the q-aspect range; this is the only range the paper uses, §4.4, `lem:bad` (Lemma 4.7)).
-/
import Families.Classical

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius
open ArithmeticFunction Finset

namespace Families.Hyp.Montgomery

/-- `β_{X,N}(n) = ∑_{d ∣ n, d ≤ X, n/d ≤ N} μ(d)`. -/
def beta (X N n : ℕ) : ℤ := ∑ d ∈ n.divisors.filter (fun d => d ≤ X ∧ n / d ≤ N), μ d

/-- `Families.Montgomery69_Density` restricted to the q-aspect range `T' ≤ Q ^ A`. -/
def Montgomery69_Density_upTo (A : ℝ) : Prop :=
  ∃ C c C₁ : ℝ, 0 < c ∧ ∀ Q : ℝ, 1 ≤ Q → ∀ T' : ℝ, 2 ≤ T' → T' ≤ Q ^ A →
    ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / 2 →
    (∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ ∈ primChars q, (Ndens χ (1 / 2 + δ) T' : ℝ))
      ≤ C * (Q ^ 2 * T') ^ (1 - c * δ) * Real.log (Q * T') ^ C₁

end Families.Hyp.Montgomery
