# Families: a Lean 4 formalisation of Theorems 1.1 and 1.4(a)

This is a Lean 4 / Mathlib formalisation of two theorems of the paper

> *Simple zeros on the critical line for a weighted family of Dirichlet L-functions, from polylogarithmic to
> polynomial height.*

The project has two libraries, built and audited together:

| Library | Paper | Lean headline |
|---|---|---|
| `Families` | Theorem 1.1 (`thm:main`), polylogarithmic height | `Families.thmMain : Families.thmMain_Statement` |
| `FamiliesH` | Theorem 1.4(a) (`thm:poly`, sharp route), polynomial height, §9; column (a) of the κ-table at κ = 1, 2, 3, 5, 10 | `Families.Hybrid.thmH : Families.Hybrid.thmH_Statement` |

`FamiliesH` imports `Families` and reuses its definitions (the family, the weights, the zero counts, the quadratic
form) verbatim. Theorem, section and equation numbers in this directory (docstrings and Markdown files) are those of the paper.
The table at the top of `STATEMENTS-H.md` maps the Lean names of the polynomial-height components (`lem:B1H`,
`prop:TIsharpH`, …) to the paper's numbers (for example `thmH` = Theorem 1.4(a), `prop:TIsharpH` = Proposition 9.18,
`lem:sizes` = Lemma 9.1).

**Status.** Both headlines are proved **with no hypotheses**, and

```
#print axioms Families.thmMain
'Families.thmMain' depends on axioms: [propext, Classical.choice, Quot.sound]
#print axioms Families.Hybrid.thmH
'Families.Hybrid.thmH' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only Lean's three standard axioms appear, so nothing that either headline depends on uses `sorry` or `native_decide`
(`Lean.ofReduceBool`), in this project or in its dependencies. The project contains no `sorry`, no `axiom`
declarations and no `native_decide` at all. Some further results of the paper (Theorems 1.2 and 1.3 among them) are
stated in Lean as propositions but not proved; they are listed below.

## What is proved: Theorem 1.1 (`Families.thmMain`)

**Theorem 1.1, in the paper's notation.** Let `Q → ∞` and `ℓ = log Q`. For `0 < η < 1/2` and a weight `w`, the family
`𝓕(Q,w)` consists of the primitive Dirichlet characters `χ mod q` with `1 ≤ q ≤ Q`. The character `χ mod q` gets the
weight `ω(q) = w(q/Q) · q/φ(q)`. The two log-wide weights are

* `w_η(u) = u⁻² · 1_{[η,1]}(u)` (sharp), and
* `w^sm_η(u) = u⁻² · sin²(π log u / log η) · 1_{[η,1]}(u)` (smooth).

For `χ ∈ 𝓕` and a height `T`, let

* `N_χ` be the number of zeros `ρ = β + iγ` of `L(s,χ)` with `T < γ ≤ 2T`, counted with multiplicity;
* `N^s_{0,χ}` the number of those zeros that are simple and have `β = 1/2`;
* `N^*_{0,χ}` the number of distinct zeros with `β = 1/2`;
* `N_{d,χ}` the number of distinct zeros.

Write `N = ∑_χ ω_χ N_χ`, and similarly `N^s_0`, `N^*_0`, `N_d`. Define

```
p(C) = 2 − inf { ∫ f² + ∬ f(x) f(y) F_C(|x − y|) dx dy : f ≥ 0 even, supp f ⊂ [−1,1], ∫ f = 1 },
```

where `F_C(α) = α` for `α ≤ 1` and `F_C(α) = C` for `α > 1`.

> **Theorem 1.1.** Fix `0 < a₀ < A₀`. For every `ε > 0` there is `η₀(ε) > 0` such that for every `η ∈ (0, η₀]` and
> `w ∈ {w_η, w^sm_η}`:
> * `liminf_{Q→∞} inf_{ℓ^{a₀} ≤ T ≤ ℓ^{A₀}} N^s_0/N ≥ p(1) − ε`;
> * the same bound holds for `N^*_0/N`;
> * `N_d/N ≥ (1 + p(1))/2 − ε`.
>
> Moreover `p(1) ≥ 0.932282`.

**The Lean statement** is `Families.thmMain_Statement` (`Families/Main.lean`):

```lean
def thmMain_Statement : Prop :=
  (∀ (a0 A0 ε : ℝ), 0 < a0 → a0 < A0 → 0 < ε → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ →
    ∀ W : Weight, (W.w = wSharpFun η ∨ W.w = wSmoothFun η) →
      ProportionsAtLeast W a0 A0 (pC 1 - ε)) ∧
  (0.932282 : ℝ) ≤ pC 1
```

`ProportionsAtLeast W a0 A0 p` writes the three `liminf` bounds without division:

```
∀ δ > 0, ∃ Q₀, ∀ Q ≥ Q₀, ∀ T ∈ [ℓ^{a0}, ℓ^{A0}]:
  (p − δ) N ≤ N^s_0,  (p − δ) N ≤ N^*_0,  ((1 + p)/2 − δ) N ≤ N_d.
```

The theorem `Families.thmMain` is in `Families/Headline.lean`.

The definitions that the statement unfolds to are listed below. `STATEMENTS.md` explains, definition by definition,
how each one corresponds to the paper (see its "Global conventions" table).

| Paper | Lean | File |
|---|---|---|
| admissible weight `w`, `η` | `Weight` | `Families/Basic.lean` |
| `ω(q) = w(q/Q) q/φ(q)` | `Weight.omega` | `Families/Basic.lean` |
| primitive characters mod `q` | `primChars` (Mathlib's `DirichletCharacter.IsPrimitive`) | `Families/Basic.lean` |
| `w_η`, `w^sm_η` | `wSharpFun`, `wSmoothFun` | `Families/LemmaA.lean` |
| `L(s,χ)`, multiplicity `m_ρ` | `Lfun` (Mathlib's `DirichletCharacter.LFunction`), `mult` (`analyticOrderNatAt`) | `Families/Classical.lean` |
| zeros with `T < γ ≤ 2T`; `N_χ`, `N^s_{0,χ}`, `N^*_{0,χ}`, `N_{d,χ}` | `zerosI`, `Nchi`, `Ns0chi`, `Nstar0chi`, `Ndchi` | `Families/Main.lean` |
| `∑_{χ∈𝓕} ω_χ (·)`; `N`, `N^s_0`, `N^*_0`, `N_d` | `famSum`; `Nfam`, `Ns0`, `Nstar0`, `Nd` | `Families/Main.lean` |
| `liminf_Q inf_T … ≥ p` | `ProportionsAtLeast` | `Families/Main.lean` |
| `F_C`, the quadratic form, `p(C)` | `FC`, `Qf`, `AdmissibleWindow`, `pC` | `Families/Variational.lean` |

The zero sets `zerosI χ T` are finite for primitive `χ` modulo `q > 1` and `T ≥ 0`, so the counts are the true
counts; this is proved as `Families.Ported.Zero.zerosI_finite`. Otherwise the values of `∑ᶠ` and `Set.ncard` on an
infinite set would be junk values.

**What the proof uses.** The proof is `thmMain_of_parts` applied to Lean proofs of the paper's steps:

* `lem:C`, `prop:sharpLS`, `lem:CTlimit` (`Families/Phase1`, `Families/Phase2`);
* `lem:B1`, `lem:B2`, `eqB:Mrat`, `prop:TIsharp` (`Families/Phase3`);
* the limit step of §7.3 with `lem:windows` (`Families/Phase4`);
* the zero side of §4 (`Families/Ported/Zero`) and the second moment of §5 (`Families/Ported/Second`);
* the kernel-evaluated certificate `p(1) ≥ 0.932282` (`Families/Certificate`).

The classical inputs are theorems too:

* the Montgomery–Vaughan large sieve (`Families/Hyp/MVLargeSieve.lean`, with the constant `17/4`);
* the prime number theorem with error term and Stirling bounds for `Γ'/Γ` (`Families/Hyp`);
* `lem:WH`;
* a zero-density estimate of Montgomery's type for heights `T' ≤ Q^A` (`Families/Hyp/Montgomery`,
  `Montgomery69_Density_upTo_proof`).

The last one is enough because Montgomery's theorem is used only in `lem:bad`, and there only at heights `T' ≤ Q`
(`Families.Ported.Zero.shellT_le_self`). Weil's explicit formula, zero counting for Dirichlet L-functions,
Stirling-type bounds, a medium-strength PNT and the rank–trace linear algebra come from the `zeta23` dependency (see
below).

**Conditional variants.** `thmMain_of_montgomery` and `thmMain_of_components` (`Families/Headline.lean`) derive
`thmMain_Statement` from named hypotheses (bundled in `ClassicalInputs`, `ClassicalInputsReduced`,
`PortedReductions`). `thmMain_of_montgomery` assumes `Montgomery69_Density` for all heights, which is not proved.
The headline `thmMain` uses neither.

## What is proved: Theorem 1.4(a) (`Families.Hybrid.thmH`)

**Theorem 1.4(a), in the paper's notation.** The family, the weights `w ∈ {w_η, w^sm_η}` and the counts `N`, `N^s_0`,
`N^*_0`, `N_d` (zeros with `T < γ ≤ 2T`) are as above. Put `κ_T = log T / log Q` and `β(κ) = (2+κ)/(1+κ)`
(`β_T = β(κ_T)`), and for `β ∈ [1,2]`

```
p(β; F_C) = 2 − inf { ∫ f² + ∬ f(x) f(y) F_C(|x − y|) dx dy : f ≥ 0 even, f ∈ L², supp f ⊂ [−β/2, β/2], ∫ f = 1 },
```

so that `p(2; F_C) = p(C)`.

> **Theorem 1.4(a) (polynomial height, sharp route).** Fix `a₀ > 0` and `κ₁ > 0`. For every `ε > 0` there is
> `η₀(ε) > 0`, **independent of `a₀` and `κ₁`**, such that for every `η ∈ (0, η₀]` and `w ∈ {w_η, w^sm_η}`:
> * `liminf_{Q→∞} inf_{ℓ^{a₀} ≤ T ≤ Q^{κ₁}} (N^s_0/N − p(β_T; F_1)) ≥ −ε`;
> * the same holds for `N^*_0/N`;
> * for `N_d/N` it holds with `(1 + p(β_T; F_1))/2` in place of `p(β_T; F_1)`.

Column (a) of the κ-table after Theorem 1.4 is part of the Lean statement at κ = 1, 2, 3, 5, 10:

| κ | β(κ) | `p(β; F_1) ≥` (a) | `(1 + p)/2 ≥` (a), distinct | Lean |
|---|---|---|---|---|
| 0 | 2 | 0.932282 | 0.966141 | `thmMain_Statement` (Theorem 1.1) |
| 1 | 3/2 | 0.865673 | 0.932836 | `certH_Statement` |
| 2 | 4/3 | 0.824355 | 0.912177 | `certH_Statement` |
| 3 | 5/4 | 0.797213 | 0.898606 | `certH_Statement` |
| 5 | 7/6 | 0.764149 | 0.882074 | `certH_Statement` |
| 10 | 12/11 | 0.727484 | 0.863742 | `certH_Statement` |

These are the `n = 400` exact rational certificates (step functions with 400 cells), checked by the Lean kernel
(`decide +kernel` on generated integer data, `FamiliesH/V/CertData.lean`); the paper's table prints the same values.
The distinct-zero column is `(1 + p)/2` of the column before, which the theorem gives directly. The rows κ = 1/4 and
κ = 1/2 of the table are not in the Lean statement.

**The Lean statement** is `Families.Hybrid.thmH_Statement` (`FamiliesH/Main.lean`; `certH_Statement` is in
`FamiliesH/Statements.lean`):

```lean
def thmH_Statement : Prop :=
  (∀ ε : ℝ, 0 < ε → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ (a0 κ1 : ℝ), 0 < a0 → 0 < κ1 →
    ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ W : Weight, (W.w = wSharpFun η ∨ W.w = wSmoothFun η) →
      ProportionsAtLeastH W a0 κ1 (fun κ => pB (betaK κ) 1 - ε)) ∧
  certH_Statement

def certH_Statement : Prop :=
  (0.865673 : ℝ) ≤ pB (3 / 2) 1 ∧ (0.824355 : ℝ) ≤ pB (4 / 3) 1 ∧ (0.797213 : ℝ) ≤ pB (5 / 4) 1 ∧
  (0.764149 : ℝ) ≤ pB (7 / 6) 1 ∧ (0.727484 : ℝ) ≤ pB (12 / 11) 1
```

`ProportionsAtLeastH W a0 κ1 p` is `ProportionsAtLeast` with the heights `ℓ^{a0} ≤ T ≤ Q^{κ1}` and the target
`p(κ_T)` evaluated inside the `T`-quantifier. `kappaT`, `betaK`, `AdmissibleWindowB` and `pB β C` are in
`FamiliesH/Basic.lean`; everything else is reused from `Families`. The theorem `Families.Hybrid.thmH` is in
`FamiliesH/Headline.lean`. `STATEMENTS-H.md` gives the definition-by-definition correspondence and the faithfulness
notes; `README-H.md` describes the proof (the κ-cells glue and the five proof packages V, F, Z, S, TS).

**Checked links between the two headlines** (`FamiliesH/StatementCheck.lean`, all proved):
`thmMain_of_thmH : lemMbeta_Statement → thmH_Statement → Families.thmMain_Statement`, with `lemMbeta_Statement`
proved, so in Lean Theorem 1.4(a) implies Theorem 1.1; `pB_two : pB 2 C = Families.pC C`;
`admissibleB_two_iff` (the admissible class at `β = 2` is `Families.AdmissibleWindow`); `kappaT_rpow : κ_{Q^κ} = κ`.

## What is stated but not proved

The following results of the paper are stated in Lean as `Prop` definitions (`def X_Statement : Prop`) but are
**not proved** in this project. There is no theorem for them and nothing uses them as a proved fact; the audit
checks that each definition exists and that no proof constant with the matching name is declared. Their docstrings
say "Stated only; not proved in this project".

| Lean definition | File | Paper |
|---|---|---|
| `thmGauss_Statement` | `Families/Main.lean` | Theorem 1.2 (Gauss transfer, `0.8859 − ε`) |
| `thmFixed_Statement` | `Families/Main.lean` | Theorem 1.3 (fixed `η`: `0.9155`, `0.9241`; Gauss route) |
| `thmConditional_Statement` | `Families/Main.lean` | `thm:conditional` (`LS(C)` implies `p(C)`) |
| `lemA_Statement` | `Families/LemmaA.lean` | Lemma A (`lem:A`, the sharp weighted Farey large sieve) |
| `lemHarm_Statement` | `Families/LemmaA.lean` | `lem:harm` |
| `lemRwlog_Statement`, `lemRwlog_numeric_Statement` | `Families/LemmaA.lean` | `lem:Rwlog` |
| `lemWH_ratio_Statement` | `Families/LemmaA.lean` | the ratio statement `W/H → C_G` of `lem:WH` |
| `propTI_Statement` | `Families/PrimeSide.lean` | `prop:TI` |
| `propCTfixed_Statement` | `Families/LemmaC.lean` | `prop:CTfixed` |

None of them lies on the proof of Theorem 1.1 or of Theorem 1.4(a). They are kept as precise documentation of what
the paper states, and some proved implications take them as hypotheses: `thmGauss_general_of'` derives part (1) of
Theorem 1.2 from `thmConditional_Statement`, `lemA_Statement` and `lemWH_ratio_Statement`, and
`Phase4.A.thmConditional_of_components` derives `thmConditional_Statement` from the profile bound
`profileLS_Statement` (also not proved) and proved inputs. Some ingredients of Theorem 1.2 are proved outright:
`lem:gauss` (`gauss_transfer`), `p(1.2688) ≥ 0.885912` (`pC_12688_ge`), and `ℰ ≥ 0.47914`, hence `C_G ≤ 1.2688`
(`Ecal_ge_047914`, `CG_le`). The unproved results rest on the written proofs in the paper; the numerics of
Theorem 1.3 are certified separately, by interval-arithmetic scripts that ship with the paper as ancillary files.

Also not proved: `Montgomery69_Density` (Montgomery's zero-density estimate at all heights, including `Q = 1`), a
named hypothesis of the conditional variants above that the headline does not need.

Not stated at all: Theorem 1.4(b) (Gauss route) and 1.4(c) (classical route); Corollary 1.5 (the dyadic family);
the rows κ = 1/4, 1/2 of the κ-table after Theorem 1.4, and its columns other than (a).

`STATUS.md` lists the status of every paper result covered by the project.

## Statement correspondence and faithfulness

The correspondence documents are:

* `STATEMENTS.md`: every declaration of `Families` that states a result or defines an object of the paper, with its
  TeX label, its status and a faithfulness note (weaker / stronger / different), and the global conventions
  (`o(1)` as `∀ δ ∃ Q₀`, `liminf` without division, junk values);
* `STATEMENTS-H.md`: the same for `FamiliesH` and Theorem 1.4(a), with the map from the Lean component names to
  the paper's numbering;
* `STATUS.md`: the status of each result (proved, implication proved, stated only).

The Lean kernel checks that the proofs prove `thmMain_Statement` and `thmH_Statement`. It does not check that these
statements say what Theorems 1.1 and 1.4(a) say; to check that, read the definitions they unfold to (the tables
above, `STATEMENTS.md` and `STATEMENTS-H.md`).

* The correspondence between `thmMain_Statement` and Theorem 1.1 was checked in an independent review by a
  frontier AI model from another developer (not Claude), which found it faithful.
* `thmH_Statement` was checked by two further independent audits (Claude-based agents, working separately from
  the formalisation), both of which found it faithful.
* What they read is pinned: the audit prints every definition the two statements unfold to and requires the output
  to equal `scripts/Statements.baseline.txt` (see "Checking"), so any change to the meaning of either headline
  fails the audit.

One Lean-specific trap is worth knowing about when reading the statements. A binder such as `∫ x, f x + c` extends as
far to the right as possible, so `+ c` ends up inside the integral. An intermediate statement of this project
(`lemB2_Statement`, not part of `thmMain_Statement`) was once false for this reason; it is now parenthesised and
pinned by an `rfl` check.

## Toolchain and dependencies

| | Version | Licence |
|---|---|---|
| Lean | `leanprover/lean4:v4.33.0-rc2` (`lean-toolchain`) | Apache-2.0 |
| Mathlib | `51e6992efd06126df61a496bebf8f49482a4e129` | Apache-2.0 |
| `Zeta23`: the Lean formalisation of Alpöge–Furman, arXiv:2608.13637, from [`anthropics/formal-math`](https://github.com/anthropics/formal-math), subdirectory `zeta23` | `fbdc36bbf17d20af3fd0447c6d1a8a02773c9844` | Apache-2.0 (© 2026 Anthropic PBC; includes files derived from PrimeNumberTheoremAnd, Apache-2.0) |
| batteries, aesop, Qq, ProofWidgets4, import-graph, LeanSearchClient, plausible | pinned in `lake-manifest.json` (inherited from Mathlib) | Apache-2.0 |
| Cli (`leanprover/lean4-cli`) | pinned in `lake-manifest.json` | MIT |

All revisions are pinned in `lake-manifest.json`. None of the dependencies is included here; `lake` fetches them.
`lakefile.toml` and `lake-manifest.json` fetch `Zeta23` from `https://github.com/anthropics/formal-math` (the
repository was formerly called `anthropics/zeta-23-lean`; the pinned commit is the same).

From `Zeta23` this project imports:

* the rank–trace inequality and inertia bounds (`Zeta23.LinAlg.*`);
* Weil's explicit formula for primitive characters (`Zeta23.ExplicitFormula.Bridge`, `Zeta23.ThmE.*`);
* zero counting for `L(s,χ)` (`Zeta23.RvM.LocalCount`, `Zeta23.ThmE.LocalCountChi`);
* Stirling bounds (`Zeta23.GammaFacts.StirlingVert`);
* a medium-strength prime number theorem (`Zeta23.FromPNTPlus.MediumPNT`);
* multiplicities of zeros (`Zeta23.ZeroSide.Mult`).

Only `Families` imports `Zeta23`; `FamiliesH` uses it only through `Families`. `#print axioms` is transitive, so the
axiom checks below cover these imported results too.

## Building

Requirements: [`elan`](https://github.com/leanprover/elan) (it installs the pinned toolchain automatically) and
`git`. About 9.5 GB of disk space for the Mathlib cache and the build.

```
cd lean                     # this directory
lake exe cache get          # download the Mathlib build cache (about 5 GB)
lake build                  # builds Families and FamiliesH; expected to end with "Build completed successfully"
```

Do not run `lake update`: all dependencies are pinned in `lake-manifest.json`. `lake build` builds both libraries
(`defaultTargets = ["Families", "FamiliesH"]`); `lake build Families` builds only the first. With the dependencies
already built, building both libraries from scratch takes about 8 minutes on 8 cores; `FamiliesH.V.CertData`, the
five kernel certificate checks of the κ-table, takes about 150 s of that. A fresh clone must also fetch the
dependencies and build the imported `zeta23` modules; Mathlib comes from the cache. The build prints linter
warnings (unused variables and the like) but no `declaration uses 'sorry'` warning.

## Checking

```
scripts/audit.sh            # the audit of both headlines; must end with "AUDIT PASSED"
```

`audit.sh` runs `lake env lean` on `scripts/Audit.lean`, `PrintAxioms.lean`, `AuditH.lean`, `PrintAxiomsH.lean`,
`Statements.lean` and `NonVacuity.lean`. By default it pins to cores 0–3 with `taskset` (skipped where `taskset` is unavailable) and uses 4
threads; set, for example, `CORES=0-7 LEAN_NUM_THREADS=8` to change that, or `CORES=` to disable pinning. It takes about a minute. It checks that:

* the build is up to date with the sources (`lake build --no-build Families FamiliesH`), so the checked `.olean`
  files are those of the sources present;
* there is no `native_decide` and no `axiom` declaration (a textual check, backed by a scan for `Lean.ofReduceBool`);
* there is no `sorry` or `admit` anywhere in the Lean sources (a textual check with comments and string literals
  removed, which also covers files that no library root imports);
* **`Families`:**
  * across all 2,488 declarations of `Families.*`, no axiom other than the three standard ones occurs, there are
    **no** `sorry` roots, and no declaration depends on `sorryAx`;
  * the 10 results that are stated but not proved are present as `Prop` definitions, none depends on `sorryAx`,
    and none has a proof constant (`thmGauss`, `lemA`, …);
  * `thmMain` has no hypotheses (`thmMain hypotheses: none`) and its type is literally `thmMain_Statement`;
  * `#print axioms Families.thmMain` is exactly `[propext, Classical.choice, Quot.sound]`;
  * the `#print axioms` lines of a fixed list of 77 proved declarations (`scripts/PrintAxioms.baseline.txt`) are
    reproduced unchanged, and none of the 131 declarations printed by
    `scripts/PrintAxioms.lean` depends on `sorryAx`;
* **`FamiliesH`:**
  * across all 567 declarations of `FamiliesH.*`, no axiom other than the three standard ones occurs, there are
    **no** `sorry` roots, and no declaration depends on `sorryAx`;
  * the glue and the statement checks are present and sorry-free, among them `thmMain_of_thmH`;
  * `thmH` has no hypotheses, its type is literally `thmH_Statement`, and its axioms are exactly
    `propext, Classical.choice, Quot.sound`;
  * the 51 lines of `scripts/PrintAxiomsH.baseline.txt` (the headline, the 15 components, the glue, the statement
    checks, the package proofs and the five certificates) are reproduced unchanged;
* **the statement pin:** `scripts/Statements.lean` collects every declaration of this project that
  `thmMain_Statement` and `thmH_Statement` unfold to (31 declarations: `thmMain_Statement`, `ProportionsAtLeast`,
  `pC`, `thmH_Statement`, `ProportionsAtLeastH`, `pB`, `certH_Statement`, `betaK`, `kappaT`, `Nfam`, `Ns0`, `Nstar0`,
  `Nd`, the per-character counts, `zerosI`, `Lfun`, `mult`, `famSum`, `Weight`, `Weight.omega`, `primChars`, `Qf`,
  `FC`, `AdmissibleWindow`, `AdmissibleWindowB`, `wSharpFun`, `wSmoothFun`), prints the type and body of each with
  fixed pretty-printer options, together with a structural hash of the expressions, and the output must equal
  `scripts/Statements.baseline.txt` exactly. The type checks above pin the headlines by *name*; the pin fixes what
  the names *mean*. Changing a constant, a quantifier or a definition fails the audit (a docstring does not).
  Definitions from Mathlib and `zeta23` are fixed by the pins in `lake-manifest.json`;
* **non-vacuity:** `scripts/NonVacuity.lean` compiles, and each of its 17 theorems depends only on `propext`,
  `Classical.choice` and `Quot.sound`. The headlines are written without division, so they would hold trivially if
  `N` were `0` or a hypothesis could not be met; this file proves that neither happens. `Nfam_pos_main` and
  `Nfam_pos_hybrid`: `N > 0` for all large `Q`, uniformly for `T` in the height range of Theorem 1.1 resp. 1.4(a).
  `thmMain_ratio`, `thmMain_ratio_numeric` and `thmH_ratio`: each headline implies the paper's ratio statement with
  real division, e.g. `N^s_0/N ≥ p(1) − ε` (and `≥ 0.9322 − ε`), `N^*_0/N ≥ p(1) − ε`, `N_d/N ≥ (1 + p(1))/2 − ε` for
  all `Q ≥ Q₀` and all `T` in the range (`thmMain_ratio_delta`, `thmH_ratio_delta` are the `liminf` forms verbatim).
  `heights_main_nonempty`, `heights_hybrid_eventually_nonempty`: the height ranges are nonempty for large `Q`.
  `weights_exist`: both weights exist for every `0 < η < 1/2`. Also `pB_le_two`, `pB_class_bddBelow` (the `sInf`
  defining `p` is over a set bounded below), the supports `betaK_table`, `betaK_kappaT`, `kappaT_at_pow`, and the
  specialisation `concrete_kappa2` (sharp weight, `T = Q²`: `N^s_0 ≥ (0.824355 − ε − δ) N` with `N > 0`).

It also prints, without enforcing it, a sha256 over the project's files, for provenance.

A passing run prints, among other lines:

```
sorry/admit (outside comments and strings; Families, FamiliesH, scripts): none
...
Families sorry roots: none
stated-only results: 10 Prop definitions, no proof constants, no sorryAx
== regression against scripts/PrintAxioms.baseline.txt ==
all 77 baseline lines reproduced unchanged
PrintAxioms: 131 declarations, none depends on sorryAx
thmMain axioms: propext, Classical.choice, Quot.sound
...
thmH hypotheses: none
thmH type: thmH_Statement
thmH axioms: propext, Classical.choice, Quot.sound

FamiliesH sorry roots: none (all 15 components proved: packages V, F, Z, S and TS)
glue and statement checks: sorry-free
== regression against scripts/PrintAxiomsH.baseline.txt ==
all 51 baseline lines reproduced unchanged
PrintAxiomsH: 51 declarations, none depends on sorryAx
thmH axioms (#print axioms): propext, Classical.choice, Quot.sound

######## statement pin (both headlines) ########
statement pin: 31 declarations, identical to scripts/Statements.baseline.txt

######## non-vacuity checks (scripts/NonVacuity.lean) ########
...
non-vacuity: 17 theorems, each with axioms among propext, Classical.choice, Quot.sound

thmMain, thmH: no hypotheses; axioms propext, Classical.choice, Quot.sound; statements match the pin
non-vacuity: N > 0 eventually (uniformly in T), ratio forms, nonempty height ranges, weights exist
AUDIT PASSED
```

To check the headlines directly:

```
cat > Check.lean <<'EOF'
import Families
import FamiliesH
#check @Families.thmMain
#check @Families.Hybrid.thmH
#print axioms Families.thmMain
#print axioms Families.Hybrid.thmH
#print Families.thmMain_Statement
#print Families.Hybrid.thmH_Statement
EOF
lake env lean Check.lean
```

The expected output starts with:

```
Families.thmMain : Families.thmMain_Statement
Families.Hybrid.thmH : Families.Hybrid.thmH_Statement
'Families.thmMain' depends on axioms: [propext, Classical.choice, Quot.sound]
'Families.Hybrid.thmH' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Layout

| Path | Contents |
|---|---|
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | the project: libraries `Families` and `FamiliesH`, pinned dependencies |
| `Families.lean` | root module of `Families` (imports everything below) |
| `Families/Basic.lean`, `Classical.lean`, `Variational.lean`, `Main.lean`, `LemmaA.lean`, `LemmaC.lean`, `PrimeSide.lean`, `Constants.lean` | definitions and the Lean statements (`…_Statement`) of the paper's results |
| `Families/Toeplitz.lean`, `Schur.lean`, `LemmaS.lean`, `Spokes.lean`, `Weights.lean`, `M1.lean`, `M1Diag.lean`, `M3.lean`, `PLip.lean`, `Glue.lean`, `Assembly.lean` | the components proved first (Toeplitz identity, `lem:gauss`, `lem:S`, `lem:M1`–`lem:M3`, `lem:pLip`, …) and the assembly helpers |
| `Families/Certificate/` | kernel-checked certificates: `p(1) ≥ 0.932282`, `p(1.2688) ≥ 0.885912`, `ℰ ≥ 0.47914`; the per-character certificate (`prop:perchi`) |
| `Families/Phase1/` | `prop:count`, `lem:C` (`A/`); `lem:Omega`, `lem:fS`, `lem:dual`, `prop:sharpLS` (`B/`) |
| `Families/Phase2/` | `lem:CTlimit` (with kernel-checked numerics), `lem:WH` |
| `Families/Phase3/` | `lem:B1`, `lem:B2`, `eqB:Mrat`, `prop:TIsharp` |
| `Families/Phase4/` | the limit step of §7.3 (`assemblyLimit`, `lem:windows`) |
| `Families/Hyp/` | classical inputs as theorems: MV large sieve, PNT with error term, Stirling |
| `Families/Hyp/Montgomery/` | Montgomery-type zero density for `T' ≤ Q^A` (mollifier, mean square, Gallagher, Jensen) |
| `Families/Classical/Reductions.lean`, `Families/Ported/` | the paper's §4 zero side (`Ported/Zero`, including the explicit-formula interface) and §5 second moment (`Ported/Second`) |
| `Families/Wired/` | connects the proofs above to the statement declarations |
| `Families/Headline.lean` | `thmMain` and the glue theorems |
| `FamiliesH.lean` | root module of `FamiliesH` |
| `FamiliesH/Basic.lean`, `Setup.lean`, `Statements.lean`, `Main.lean` | Theorem 1.4(a): definitions, the one-cell data `HSetup`, the component statements, `thmH_Statement` |
| `FamiliesH/Glue.lean`, `Components.lean`, `Headline.lean`, `StatementCheck.lean` | the κ-cells glue, the 15 component theorems, `thmH`, and the faithfulness pins (`thmMain_of_thmH`, `pB_two`, …) |
| `FamiliesH/V/`, `F/`, `Z/`, `S/`, `TS/` | the five proof packages of Theorem 1.4(a) (`README-H.md`) |
| `scripts/` | `audit.sh` (the audit of both headlines); `Audit.lean`, `PrintAxioms.lean` (+ `.baseline.txt`), `PrintAxiomsHyp.lean` for `Families`; `AuditH.lean`, `PrintAxiomsH.lean` (+ `.baseline.txt`) for `FamiliesH`; `Statements.lean` (+ `Statements.baseline.txt`), the statement pin; `NonVacuity.lean`, the non-vacuity checks (`N > 0`, ratio forms, nonempty ranges, weights exist); `gen_hybrid_data.py` (regenerates `FamiliesH/V/CertData.lean` from the paper's ancillary `certify_hybrid.py`) |
| `STATEMENTS.md`, `STATEMENTS-H.md` | the Lean ↔ paper maps, with faithfulness notes (`STATEMENTS-H.md` also maps the Lean component names to the paper's numbering) |
| `STATUS.md` | the status of each result: proved, implication proved, stated only |
| `README-H.md` | Theorem 1.4(a) in detail: statement, proof packages, what is not formalised |

The directories `Families/Phase1/` to `Families/Phase4/` (and the matching namespaces `Families.Phase1.A`, …) are
named after the order in which the headline-chain components were formalised; the names are part of the
declaration names and are kept.

About 39,100 lines of Lean in 135 files (`Families`) and 11,750 lines in 52 files (`FamiliesH`), counting the root
modules.

## Licence

**Licence of this directory's own files** (the Lean sources, scripts and all Markdown files, including this one):
Apache License 2.0 (see the `LICENSE` file at the top level of the repository or ancillary bundle).
Copyright 2026 Nic Johns.
