/-
# The two ported reductions and the bundle `PortedReductions`

`ZeroSideReduction` (paper §4) and `SecondMomentAssembly` (paper §5) are the two reduction steps that
are stated as named hypotheses (b6)–(b7). **They are the paper's own arguments, ported, not literature results.**
They are stated here, not in `Families/Classical.lean`, because they refer to the statements of
`Families/Main.lean` and `Families/PrimeSide.lean`, which import `Families.Classical`.

The two reductions are bundled in `PortedReductions`, separately from `ClassicalInputs`
(`Families.Classical`: large sieve, Montgomery 1969, PNT, Stirling, `lem:WH`). The conditional variant
`thmMain_of_components (…) (hC : ClassicalInputs) (hR : PortedReductions) : thmMain_Statement` therefore shows
which hypotheses are classical and which are the paper's own §4/§5.

**Form.** Each reduction is stated as an *implication* whose premises are exactly the named inputs
that the paper's proof of it cites: the classical inputs of `Families.Classical` and the Lean
statements of results proved elsewhere in the formalisation ((a) targets and `lemRvM_lower_Statement`).
So a reduction asserts only "the paper's §4 (resp. §5) argument, fed with these inputs, yields
`prop:zero` (resp. `prop:second`)". Ingredients of each proof that are neither named inputs nor Lean
statements are listed in the docstrings as *internal*.

**What this does and does not buy.** Taken alone, each
reduction is weaker than its conclusion. But every classical premise is also a field of
`ClassicalInputs`, so `ClassicalInputs ∧ PortedReductions` is logically equivalent to assuming the four
classical inputs, `lem:WH`, `propZero_Statement ∧ lemRvM_lower_Statement`, and
`lemB2 ∧ eqBMrat → propSecond`. The implication form records the dependency structure (which classical
inputs §4 and §5 consume, and that `lem:B2`, `eqB:Mrat` feed §5), so that proving a reduction removes
it without changing the other hypotheses. `Montgomery69_Density` and `StirlingDigamma`
are used by the headline *only* as premises of the reductions.

**Status.** Both reductions are theorems (`Families.portedReductions`), and the headline
`Families.thmMain : thmMain_Statement` is **unconditional**: it takes the zero side's conclusion from
`Families.Ported.Zero.propZero_unconditional` (Montgomery 1969 only in the proved q-aspect range
`T' ≤ Q`) via the glue `Families.thmMain_of_parts`, so it needs neither `ZeroSideReduction`'s
`Montgomery69_Density` premise nor these bundles. They are used only by the conditional variants
`thmMain_of_components`, `thmMain_of_montgomery`.
-/
import Families.Main

noncomputable section

open scoped BigOperators ComplexConjugate ArithmeticFunction.Moebius ENNReal ContDiff
open ArithmeticFunction Finset MeasureTheory Filter Topology

namespace Families

/-- **`lem:RvM`, lower half** (Lemma 4.1): for fixed `w` and `0 < a₀ < A₀`, uniformly for
`ℓ^{a₀} ≤ T ≤ ℓ^{A₀}`, `N ≥ (1 − o(1)) H T ℓ/(2π)`.

The TeX states the two-sided asymptotic `N = (HTℓ/2π)(1 + O((log T + log 1/η)/ℓ + 1/T))`; since
`log T ≤ A₀ log ℓ` and `T ≥ ℓ^{a₀}`, the error is `o(1)` uniformly in `T`. Only the lower bound is
consumed downstream: by `SecondMomentAssembly` (the step "use `N = (1+o(1))HTℓ/(2π)`" in the proof of
`prop:second` (Proposition 5.13), which bounds `𝔐` from above by a multiple of `N`) and by the glue
(`H = o(N)`, to absorb the error `O_B(ℓ^{−B}(H𝔐)^{1/2})` of `prop:zero`, in the proof of `thm:conditional`, Theorem 5.16). It is
proved in §4.1, so it is part of the output of `ZeroSideReduction`. -/
def lemRvM_lower_Statement : Prop :=
  ∀ (W : Weight) (a0 A0 : ℝ), 0 < a0 → a0 < A0 → ∀ δ : ℝ, 0 < δ → ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
    ∀ T ∈ Set.Icc (Real.log Q ^ a0) (Real.log Q ^ A0),
      (1 - δ) * (W.H Q * T * Real.log Q / (2 * Real.pi)) ≤ Nfam W Q T

/-- **`ZeroSideReduction`** (named hypothesis (b6)).

The zero side of the paper (§4, `sec:zero`, a port of Hua–Yang [HY26] to the weighted
family): given the large sieve, Montgomery's density theorem, Stirling's formula and the masses
`lem:WH`, the zero-side reduction `prop:zero` holds, and so does the lower half of the weighted
Riemann–von Mangoldt formula `lem:RvM` (§4.1).

*Premises as used in §4:* `MV_LargeSieve` in `lem:pointwise` (hence `lem:tails`,
`prop:finitecentre`); `Montgomery69_Density` in `lem:bad`; `StirlingDigamma` in `lem:pointwise`,
`prop:trace`; `lemWH_Statement` for `H ≍_w Q²` (`lem:pointwise`, `lem:bad`).

*Internal ingredients* (classical facts used only inside §4 and Appendix B, not named here):
Riemann–von Mangoldt for a single `L(s,χ)` (Davenport Ch. 16; BMOR21), the local zero count
`eq:localcount`, the functional equation (Davenport Ch. 9) for `lem:blocks`, Weil's explicit formula
(`prop:weil`, proved in Appendix B), and IK (3.9) (proved here as `sum_primChars_eq`). The per-character
certificate `prop:perchi` is proved in Lean (`Cert.BlockData.perchi`), but its link to the Gabor matrix of
`L(s,χ)` (`lem:blocks`) is internal to this reduction.

*Status.* A theorem (`Families.Ported.zeroSide_proof`). Its proof uses `Montgomery69_Density` only at
heights `T' ≤ Q` (`lem:bad`); the conclusion is proved unconditionally as
`Families.Ported.Zero.propZero_unconditional`, which is what the headline uses. -/
def ZeroSideReduction : Prop :=
  MV_LargeSieve → Montgomery69_Density → StirlingDigamma → lemWH_Statement →
    propZero_Statement ∧ lemRvM_lower_Statement

/-- **`SecondMomentAssembly`** (named hypothesis (b7); a theorem:
`Families.Ported.secondMoment`).

The prime side of the paper (§5, `sec:prime`): given the large sieve, Stirling's formula,
`lem:WH`, the lower half of `lem:RvM`, and the Lean statements of `lem:B2` and `eqB:Mrat`, the second
moment with a profile `prop:second` holds.

*Premises as used in the proof of `prop:second` (Proposition 5.13):* `lemB2_Statement` (applied with
`h(y) = c(y/ℓ) g(y)`), `eqBMrat_Statement` (the swap `a → b` in `M^rat`), `MV_LargeSieve` in `lem:ss`,
`StirlingDigamma` in `lem:mumu`, `lem:muLambda`, `lemWH_Statement` (`H ≍ Q²` in `lem:ss`,
`lem:muLambda`), `lemRvM_lower_Statement` (final division by `N`).

*Internal ingredients:* the finite-centre replacement `eq:fc2` (`prop:finitecentre`, §4), the family
first moment `lem:firstmoment` (IK (3.9)), `eq:Kdiag` (proved in Lean: `lemM1_diag`), and the
elementary estimates of `lem:mumu`, `lem:muLambda`, `lem:ss`. -/
def SecondMomentAssembly : Prop :=
  MV_LargeSieve → StirlingDigamma → lemWH_Statement → lemRvM_lower_Statement →
    lemB2_Statement → eqBMrat_Statement → propSecond_Statement

/-- **The ported reductions of the headline theorem** ((b6)–(b7), kept separate from `ClassicalInputs`).
These are **the paper's own §4 and §5, not classical results**: a conditional variant that assumes this bundle
assumes `prop:zero` and the lower half of `lem:RvM` (field `zeroSide`) and `prop:second`, given `lem:B2` and
`eqB:Mrat` (field `secondMoment`). Each field is an
implication from the classical inputs it consumes (see the module docstring).
Used by `thmMain_of_components` (`Families.Headline`); both fields are theorems
(`Families.portedReductions`), and the headline `thmMain` does not use this bundle. -/
structure PortedReductions : Prop where
  /-- (b6) the zero-side reduction (§4), `Families.ZeroSideReduction` -/
  zeroSide : ZeroSideReduction
  /-- (b7) the second-moment assembly (§5), `Families.SecondMomentAssembly` -/
  secondMoment : SecondMomentAssembly

end Families
