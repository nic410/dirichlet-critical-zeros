/-
# Theorem 1.4(a), package Z: the zero side at polynomial height (the component `propZeroH_unconditional`)

`propZeroH_unconditional_proof : propZeroH_Statement ∧ lemRvMH_lower_Statement` — Proposition 9.9 and
the lower half of Lemma 9.2, with **no hypotheses** (standard axioms only). Files:
* `Z/Basic.lean`: `toPS` (the cell data as a `Families.PrimeSetup`; the Gabor objects at bandwidth
  argument `QT` are definitionally the families ones), `Mfrak_eqH`, height facts;
* `Z/RvM.lean`: `rvm_familyH` (two-sided `N ~ H T ℓ_*/2π`, uniformly in `T ≥ ℓ^{a₀}`),
  `lemRvMH_lower_proof`;
* `Z/TracePrime.lean`: the prime part of the family trace, `≪ Q √X log X` uniformly in `T`
  (`trace_prime_bound`: exact Fourier identity for `|p_k|²` plus cancellation over the lattice `K_J`);
* `Z/Trace.lean`: `trace_lowerH` (`∑ ω tr Ĝ ≥ (1 − 2θ − δ) N`);
* `Z/Exterior.lean`: `exterior_tailH` (good characters, bad set at the family parameter `Q`);
* `Z/Assembly.lean`: `perchar_uniformH`, the budgets, `propZeroH_proof`.
-/
import FamiliesH.Z.Assembly
import FamiliesH.Z.RvM

namespace Families.Hybrid.Z

/-- **Package Z** (Proposition 9.9 and Lemma 9.2, lower half), unconditionally. -/
theorem propZeroH_unconditional_proof : propZeroH_Statement ∧ lemRvMH_lower_Statement :=
  ⟨propZeroH_proof, lemRvMH_lower_proof⟩

end Families.Hybrid.Z
