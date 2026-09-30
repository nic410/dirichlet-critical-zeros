/-
# Named classical hypotheses and the bundle `ClassicalInputs`

This file states, as `def … : Prop`, the classical analytic inputs of the proof (named hypotheses (b1)–(b5)),
and bundles them in the structure `Families.ClassicalInputs`. No `axiom` is declared anywhere: each input enters
a theorem either as an explicit hypothesis or through its proof (`Families/Hyp`, `Families.lemWH`).

Each classical input is stated in the weakest form that the proofs of the paper use, as a consequence
of the cited source (never a strengthening). The docstrings give the citation, the TeX label and the
place in the paper where it is used (by LaTeX label and the number printed in the paper).

`ClassicalInputs` contains
*only* the literature inputs (b1)–(b4) and the elementary mass asymptotics (b5). The paper's own
ported reductions `ZeroSideReduction` (§4) and `SecondMomentAssembly` (§5) are **not** classical; they
are bundled separately in `Families.PortedReductions` (`Families/Classical/Reductions.lean`).

**Status.** The headline `Families.thmMain : thmMain_Statement` is unconditional and does not take
`ClassicalInputs`. `MV_LargeSieve`, `PNT_dlVP`, `StirlingDigamma` and
`lemWH_Statement` are theorems (`Families/Hyp`, `Families.lemWH`). `Montgomery69_Density` (all heights)
is **not** proved and **not** needed: the headline uses Montgomery 1969 only in the q-aspect range
`T' ≤ Q` (`Families.Hyp.Montgomery.Montgomery69_Density_upTo_proof`, in `lem:bad`). The bundles and
`Montgomery69_Density` are used only by the conditional variants `thmMain_of_components`,
`thmMain_of_montgomery` (`Families/Headline.lean`).

| Lean name | Source | Used by (Lean) |
|---|---|---|
| `MV_LargeSieve` | Montgomery–Vaughan 1973; IK Thms 7.7, 7.13 | `propTIsharp` (a); band constant in `thmMain_of_components`; premise of both reductions |
| `Montgomery69_Density` | Montgomery, Invent. Math. 8 (1969), Thm 1 (uniform consequence, unspecified `c > 0`, log power) | premise of `ZeroSideReduction`; **not used by the headline** (only its q-aspect restriction, which is proved) |
| `PNT_dlVP` | de la Vallée Poussin; Davenport Ch. 18 | `lemB2` (a) |
| `StirlingDigamma` | Stirling's series for `Γ'/Γ` | premises of both reductions |
| `lemWH_Statement` | `lem:WH` (elementary; proved as `Families.lemWH`) | `propSharpLS`, `propTIsharp` (a); glue; premises of both reductions |

Not in this bundle (see `Families/Classical/Reductions.lean`, bundle `PortedReductions`):

| Lean name | Source | Used by (Lean) |
|---|---|---|
| `ZeroSideReduction` | paper §4 (port of Hua–Yang); **not classical** | glue |
| `SecondMomentAssembly` | paper §5; **not classical** | glue |

`Lfun` and `mult` (the Dirichlet `L`-function and the multiplicity of a zero) are defined here, rather than
in `Main.lean`, so that `Montgomery69_Density` can be stated before the main chain.
-/
import Families.Basic

noncomputable section

open scoped BigOperators ComplexConjugate ArithmeticFunction.Moebius
open ArithmeticFunction Finset

namespace Families

/-! ### Dirichlet `L`-functions and multiplicities -/

/-- `L(s,χ)` (Mathlib's `DirichletCharacter.LFunction`, the analytic continuation of the L-series);
the modulus `q = 0` never occurs and is given the junk value `0`. -/
def Lfun {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  if h : q = 0 then 0 else haveI : NeZero q := ⟨h⟩; DirichletCharacter.LFunction χ s

/-- Multiplicity of a zero. -/
def mult {q : ℕ} (χ : DirichletCharacter ℂ q) (ρ : ℂ) : ℕ :=
  analyticOrderNatAt (Lfun χ) ρ

/-! ### (b1) The large sieve (Montgomery–Vaughan) -/

/-- The multiplicative large sieve with constant `C₀`, in the form of `eq:MVLS`
(display (4.1), in the proof of `lem:pointwise`, Lemma 4.2): for `Q ≥ 1`, every interval `I = [N₀, N₀+K)` of `K`
consecutive integers and every `x`,
`∑_{q≤Q} (q/φ(q)) ∑*_{χ mod q} |∑_{n∈I} x_n χ(n)|² ≤ C₀ (Q² + K) ‖x‖²`
(`∑*` over primitive characters; `q = 1` contributes the trivial character). -/
def MVLargeSieveMult (C₀ : ℝ) : Prop :=
  ∀ Q : ℝ, 1 ≤ Q → ∀ (N₀ : ℤ) (K : ℕ) (x : ℤ → ℂ),
    ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ((q : ℝ) / (Nat.totient q : ℝ)) *
        ∑ χ ∈ primChars q, ‖∑ n ∈ intervalZ N₀ K, x n * χ n‖ ^ 2
      ≤ C₀ * (Q ^ 2 + K) * normSq (intervalZ N₀ K) x

/-- The additive large sieve at the Farey fractions of order `E` with constant `C₀`, in the form
displayed in the proof of `prop:TIsharp` (Proposition 6.24, "Levels `e ≤ R_max`"):
`∑_{e≤E} ∑*_{c mod e} |S_x(c/e)|² ≤ C₀ (K + E²) ‖x‖²` for `x` supported on `K` consecutive integers. -/
def MVLargeSieveAdd (C₀ : ℝ) : Prop :=
  ∀ (E : ℕ) (N₀ : ℤ) (K : ℕ) (x : ℤ → ℂ),
    ∑ e ∈ Finset.Icc 1 E, ∑ c ∈ reduced e, ‖S (intervalZ N₀ K) x ((c : ℝ) / e)‖ ^ 2
      ≤ C₀ * (K + E ^ 2) * normSq (intervalZ N₀ K) x

/-- **`MV_LargeSieve`** (classical input (b1)). The large sieve inequality, additive and
multiplicative, with *some* absolute constant `C₀`.

*Source.* Montgomery–Vaughan, "The large sieve", Mathematika 20 (1973) [MV73];
Iwaniec–Kowalski, *Analytic Number Theory*, Thm 7.7 (additive: `(δ⁻¹ + N − 1)‖a‖²` for
`δ`-spaced points; Farey fractions of order `E` are `E⁻²`-spaced) and Thm 7.13 (multiplicative:
`(Q² + N − 1)‖a‖²`). Both hold with `C₀ = 1`.

*Form used by the paper.* `eq:MVLS` (display (4.1)) and the additive inequality displayed in
the proof of `prop:TIsharp` (Proposition 6.24), both with constant `1`. Every use of either inequality in the
paper is an `O(·)` bound (`lem:pointwise`, `lem:ss`, the tails and prime powers in `prop:TIsharp`,
and the band constant `C_band = 2w_max/(ℰ I_w)`, which only needs to be `O(1)`; proof of `thm:main`, §7.3:
"any bound `O(H)` suffices on the band"), so we assume only an unspecified absolute constant `C₀`.
This is weaker than [MV73]/IK, and allows a later discharge with a non-sharp constant (e.g. from a
Hilbert-type inequality). -/
def MV_LargeSieve : Prop :=
  ∃ C₀ : ℝ, MVLargeSieveMult C₀ ∧ MVLargeSieveAdd C₀

/-! ### (b2) Montgomery's zero-density theorem -/

/-- `N(σ, T', χ)`: the zeros `ρ` of `L(s,χ)` with `β ≥ σ` and `|γ| ≤ T'`, counted with multiplicity
(§4.4, `sec:exterior`). For `σ > 0` these are nontrivial zeros. (The set is finite; if it were not,
Lean's `∑ᶠ` would give `0`, which could only weaken an upper-bound hypothesis.) -/
def Ndens {q : ℕ} (χ : DirichletCharacter ℂ q) (σ T' : ℝ) : ℕ :=
  ∑ᶠ ρ ∈ {ρ : ℂ | Lfun χ ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T'}, mult χ ρ

/-- **`Montgomery69_Density`** (classical input (b2)). A zero-density estimate for the family of all
primitive characters of conductor `≤ Q`, uniform in `σ = 1/2 + δ`: there are constants `C`, `c > 0`,
`C₁` such that for `Q ≥ 1`, `T' ≥ 2`, `0 ≤ δ ≤ 1/2`,
`∑_{q≤Q} ∑*_{χ mod q} N(1/2+δ, T', χ) ≤ C (Q²T')^{1−cδ} (log QT')^{C₁}`.

*Source.* H. L. Montgomery, "Zeros of L-functions", Invent. Math. 8 (1969), 346–354, Theorem 1:
the two-range bound `eq:Montgomery` (display (4.4)), `≪ (Q²T')^{3(1−σ)/(2−σ)} (log QT')^{13}`
for `1/2 ≤ σ ≤ 4/5` and `≪ (Q²T')^{2(1−σ)/σ} (log QT')^{13}` for `4/5 ≤ σ ≤ 1`. The paper derives from it
(§4.4) the uniform consequence `eq:Montuniform` (display (4.5)), i.e. the statement here with `c = 4/3`,
`C₁ = 13`, by the exponent comparisons `3(½−δ)/(3/2−δ) ≤ 1 − 4δ/3` and `(1−2δ)/(½+δ) ≤ 1 − 4δ/3`.

*Form used.* Only this uniform consequence is used, in `lem:bad` (inside `ZeroSideReduction`), and the
paper states (§4.4) that "any bound `(Q²T')^{1−cδ}(log QT')^{C₀}` with `c > 0` would do after adjusting
`B₁` and replacing the height `Q^{|δ|/2}` in the definition of bad characters by `Q^{a|δ|}` with
`0 < a < 2c`". We therefore assume only that form, with unspecified `c > 0` and `C₁`. (The log power `13` of
Montgomery's Theorem 1, quoted by the paper, is not needed and so not hard-coded; `ZeroSideReduction`'s proof
uses the adjusted `B₁`, `a` of §4.4.) The Lean encoding counts zeros with `β ≥ σ`, `|γ| ≤ T'`, with multiplicity
(`Ndens`); `q = 1` contributes `ζ`.

*Status.* **Not proved, and not needed by the headline.** `lem:bad` invokes the
bound only at heights `T' ≤ Q` (for `Q ≥ e²`, with `a = min(c, 1)`), so the headline
`Families.thmMain : thmMain_Statement` uses only the q-aspect restriction
`Families.Hyp.Montgomery.Montgomery69_Density_upTo 1`, which is a theorem
(`Montgomery69_Density_upTo_proof`). This full form (all heights `T' ≥ 2`, including `Q = 1`,
i.e. a zero-density theorem for `ζ`) follows from an unproved `t`-aspect input
(`Montgomery69_Density_of_tAspect`); it is the premise of `ZeroSideReduction` and of the
conditional variants `thmMain_of_components`, `thmMain_of_montgomery`. -/
def Montgomery69_Density : Prop :=
  ∃ C c C₁ : ℝ, 0 < c ∧ ∀ Q : ℝ, 1 ≤ Q → ∀ T' : ℝ, 2 ≤ T' → ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / 2 →
    (∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ ∈ primChars q, (Ndens χ (1 / 2 + δ) T' : ℝ))
      ≤ C * (Q ^ 2 * T') ^ (1 - c * δ) * Real.log (Q * T') ^ C₁

/-! ### (b3) The prime number theorem with an error term -/

/-- **`PNT_dlVP`** (classical input (b3)). The prime number theorem with a power-of-log error term:
`|θ(x) − x| ≤ C₀ x / (log x)³` for `x ≥ 2`, where `θ(x) = ∑_{p≤x} log p` (Mathlib's
`Chebyshev.theta`).

*Source.* de la Vallée Poussin's error term, `ψ(x) = x + O(x e^{−c√log x})` (Davenport,
*Multiplicative Number Theory*, Ch. 18), with `0 ≤ ψ(x) − θ(x) ≪ √x log x`.

*Form used.* The paper states `eqB:PNT` (display (5.8)):
`|θ(x) − x| ≤ C₀ x e^{−c₀√log x}`. This implies the statement here (`e^{−c₀√log x} ≪ (log x)^{−3}`).
It is used only in the proof of `lem:B2`, steps (2), (3) and (5) (Lemma 5.7), where the only property
needed of the relative error `ε(x)` is `∑_{j≥2} (1+j) ε(2^{j−1}) < ∞` (the sum `eqB:B2err`); the
exponent `3` gives this. So we assume the weaker power-of-log form. **This is deliberately weaker
than `eqB:PNT`**; the proof of `lem:B2` in this project uses it. It is proved as `Families.Hyp.PNT_dlVP_proof`. -/
def PNT_dlVP : Prop :=
  ∃ C₀ : ℝ, ∀ x : ℝ, 2 ≤ x → |Chebyshev.theta x - x| ≤ C₀ * x / Real.log x ^ 3

/-! ### (b4) Stirling's formula for the digamma function -/

/-- `Re (Γ'/Γ)((1/2 + 𝔞 + it)/2)` (`𝔞 ∈ {0,1}`), the non-constant part of
`μ_χ(t) = (1/2π) log(q/π) + (1/2π) Re (Γ'/Γ)((1/2+𝔞_χ+it)/2)` (`eq:mu`, display (2.3)). -/
def digammaRe (a t : ℝ) : ℝ :=
  (logDeriv Complex.Gamma ((1 / 2 + a + Complex.I * t) / 2)).re

/-- **`StirlingDigamma`** (classical input (b4)). There is an absolute `C` such that for `𝔞 ∈ {0,1}`:
(i) `|Re ψ((1/2+𝔞+it)/2) − log(t/2)| ≤ C/t` for `t ≥ 1`;
(ii) `|Re ψ((1/2+𝔞+it)/2)| ≤ C log(|t|+2)` for all real `t`;
(iii) `|d/dt Re ψ((1/2+𝔞+it)/2)| ≤ C/t` for `t ≥ 1`;
where `ψ = Γ'/Γ` (Lean: `logDeriv Complex.Gamma`).

*Source.* Stirling's series `ψ(s) = log s − 1/(2s) + O(|s|^{−2})` and `ψ'(s) = 1/s + O(|s|^{−2})`
for `Re s ≥ 1/4` (e.g. Whittaker–Watson §12.33; Davenport Ch. 10; Montgomery–Vaughan,
*Multiplicative Number Theory I*, App. C). With `s = (1/2+𝔞+it)/2`, `Re log s = log(t/2) + O(t^{−2})`.

*Form used.* (i) is "by Stirling, `μ_χ(t) = (1/2π) log(qt/2π) + O(1/t)` for `t ≥ 1`" in the proof of
`prop:trace` (Proposition 4.6), and also gives `μ_χ = ℓ/2π + O(log T + log 1/η)` on `J` in
`lem:mumu` (Lemma 5.1); (ii) is "by the digamma asymptotic, `|μ_χ(t)| ≪ ℓ + log(|t|+2)`" in
`lem:pointwise` (Lemma 4.2); (iii) is "`A_q', B' ≪ 1/T` on `J`" in `lem:muLambda` (Lemma 5.2). All three
are used only inside `ZeroSideReduction` and `SecondMomentAssembly`. (Lean's `deriv` is `0` at points
of non-differentiability, which could only weaken (iii); the function is in fact smooth.) -/
def StirlingDigamma : Prop :=
  ∃ C : ℝ, ∀ a : ℝ, (a = 0 ∨ a = 1) →
    (∀ t : ℝ, 1 ≤ t → |digammaRe a t - Real.log (t / 2)| ≤ C / t) ∧
    (∀ t : ℝ, |digammaRe a t| ≤ C * Real.log (|t| + 2)) ∧
    (∀ t : ℝ, 1 ≤ t → |deriv (digammaRe a) t| ≤ C / t)

/-! ### (b5) The masses `W` and `H` (`lem:WH`) -/

/-- **`lem:WH`** (named hypothesis (b5); proved as `Families.lemWH`).
There is an absolute `c₀` with `|W − c_w Q²| ≤ c₀ V_w Q log(2Q)` and
`|H − ℰ I_w Q²| ≤ c₀ V_w Q^{3/2}` for every admissible `w` and every real `Q ≥ 2`
(`lem:WH`, Lemma 6.1; exact statement).

*Status.* Elementary (`∑_{q≤x} φ(q) = 3x²/π² + O(x log x)`, `φ*/φ = 1 * g`, Abel summation against
a BV weight), not a classical citation; proved in `Families/Phase2/B/WH.lean` (`Families.lemWH`). Used by `propSharpLS` and `propTIsharp` (`H ≍ Q²`),
by the glue (band constant; `C_T^+ ≥ 1`), and inside both reductions. -/
def lemWH_Statement : Prop :=
  ∃ c₀ : ℝ, ∀ W : Weight, ∀ Q : ℝ, 2 ≤ Q →
    |W.Wm Q - W.cw * Q ^ 2| ≤ c₀ * W.Vw * Q * Real.log (2 * Q) ∧
    |W.H Q - Ecal * W.Iw * Q ^ 2| ≤ c₀ * W.Vw * Q ^ (3 / 2 : ℝ)

/-! ### The bundle `ClassicalInputs` -/

/-- **The classical inputs of the headline theorem**: the four literature inputs (b1)–(b4) and the mass
asymptotics `lem:WH` (b5). `ClassicalInputs` feeds the bundled glue `thmMain_of_components` and (via
`ClassicalInputsReduced.toFull`, `Families/Hyp/Reduced.lean`) the conditional `thmMain_of_montgomery`
(`Families.Headline`). **The headline `thmMain : thmMain_Statement` does not use this bundle** (it is
unconditional; the only field that is not a theorem, `montgomery69`, is replaced by its proved q-aspect
restriction).

This bundle contains **no** result of the paper itself except `lem:WH`, which is elementary
(`∑ φ(q)` asymptotics and Abel summation against a BV weight) and is proved (`Families.lemWH`). The paper's own zero side (§4: `prop:zero`, lower half of `lem:RvM`) and
prime-side assembly (§5: `prop:second`) are in the separate bundle `Families.PortedReductions`. -/
structure ClassicalInputs : Prop where
  /-- (b1) the large sieve, `Families.MV_LargeSieve` -/
  mvLargeSieve : MV_LargeSieve
  /-- (b2) Montgomery's zero-density theorem, `Families.Montgomery69_Density` -/
  montgomery69 : Montgomery69_Density
  /-- (b3) the prime number theorem with an error term, `Families.PNT_dlVP` -/
  pnt : PNT_dlVP
  /-- (b4) Stirling's formula for `Γ'/Γ`, `Families.StirlingDigamma` -/
  stirling : StirlingDigamma
  /-- (b5) the masses `W`, `H` (`lem:WH`), `Families.lemWH_Statement` -/
  masses : lemWH_Statement

end Families
