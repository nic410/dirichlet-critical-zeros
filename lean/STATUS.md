# STATUS.md: the status of each result in the project

This file lists, for each result of the paper that the Lean project covers, the Lean declaration and its status.
`README.md` gives the overview, the build and check instructions and the layout; `STATEMENTS.md` and
`STATEMENTS-H.md` explain how each Lean statement corresponds to the paper.

Status: **P** = proved (depends only on `propext`, `Classical.choice`, `Quot.sound`; kernel-evaluated certificates
depend on no axioms), **I** = implication proved (the theorem takes other *stated* results as hypotheses),
**S** = stated only (a `Prop` definition `X_Statement`; there is no theorem, and nothing in the project uses `sorry`),
**D** = definition, **H** = named hypothesis (a `Prop` definition used only by the conditional variants).

`scripts/audit.sh` checks the statuses mechanically (see `README.md`, "Checking"); `scripts/PrintAxioms.lean`,
`scripts/PrintAxiomsHyp.lean` and `scripts/PrintAxiomsH.lean` print `#print axioms` for the declarations below.

## The two headlines

| Paper | Lean | File | Status |
|---|---|---|---|
| Theorem 1.1 (`thm:main`) | `Families.thmMain : Families.thmMain_Statement`, no hypotheses | `Families/Headline.lean` (statement `Families/Main.lean`) | **P** |
| Theorem 1.4(a) (`thm:poly`, sharp route) with column (a) of the κ-table at κ = 1, 2, 3, 5, 10 | `Families.Hybrid.thmH : Families.Hybrid.thmH_Statement`, no hypotheses | `FamiliesH/Headline.lean` (statement `FamiliesH/Main.lean`) | **P** |
| Theorem 1.4(a) implies Theorem 1.1 | `Families.Hybrid.thmMain_of_thmH` (with `lemMbeta`, proved) | `FamiliesH/StatementCheck.lean` | **P** |

## Theorem 1.1: the proof (library `Families`)

**Glue.** `thmMain = thmMain_of_parts …` (`Families/Headline.lean`, **P**); helpers `assembly_fixed`, `CTp_ge_one`,
`bandLS_of_MV`, `bandProfile_spec` (`Families/Assembly.lean`, **P**).

**Headline-chain results** (class (a) of `STATEMENTS.md`; statement files `LemmaA.lean`, `LemmaC.lean`,
`PrimeSide.lean`, `Main.lean`; proofs wired in `Families/Wired/`):

| Paper | Lean | Proof in | Status |
|---|---|---|---|
| `lem:Omega` (a), (c), (d), (e) | `lemOmega_ac`, `lemOmega_d`, `lemOmega_e` | `Families/Phase1/B/` | **P** |
| `lem:fS` (i)–(iv) | `lemfS` | `Families/Phase1/B/` | **P** |
| `lem:dual` | `lemDual` | `Families/Phase1/B/Dual.lean` | **P** |
| `prop:count` | `propCount` | `Families/Phase1/A/` | **P** |
| `lem:C` | `lemC` | `Families/Phase1/A/LocalC.lean` | **P** |
| `prop:sharpLS` | `propSharpLS` (takes `lemWH_Statement`) | `Families/Phase1/B/SharpLS.lean` | **P** |
| `lem:CTlimit` | `lemCTlimit` | `Families/Phase2/B/` | **P** |
| `lem:WH` | `lemWH` | `Families/Phase2/B/WH.lean` | **P** |
| `lem:B1` | `lemB1` | `Families/Phase3/C/B1.lean` | **P** |
| `eqB:Mrat` | `eqBMrat` | `Families/Phase3/C/Mrat.lean` | **P** |
| `lem:B2` | `lemB2` (takes `PNT_dlVP`) | `Families/Phase3/C/B2*.lean` | **P** |
| `prop:TIsharp` | `propTIsharp` (takes `MV_LargeSieve`, `lemWH_Statement`) | `Families/Phase3/C/TIsharp*.lean` | **P** |
| §7.3, the limit step (`lem:windows` and dominated convergence) | `assemblyLimit` | `Families/Phase4/A/` | **P** |

**Zero side (§4) and second moment (§5).**

| Paper | Lean | File | Status |
|---|---|---|---|
| `prop:zero` and the lower half of `lem:RvM`, unconditional | `Ported.Zero.propZero_unconditional` | `Families/Ported/Zero/Unconditional.lean` | **P** |
| `lem:bad` (heights `T' ≤ Q`) | `Ported.Zero.bad_count_of_upTo`, `bad_weight_of_upTo`, `bad_count_unconditional`, `bad_weight_unconditional` | `Families/Ported/Zero/Bad.lean` | **P** |
| `lem:explicit` / `prop:weil` (Weil's explicit formula) | `Ported.Zero.gabor_eq_integral`, `Ported.explicitGaborSharp` | `Families/Ported/Zero/ExplicitFormula.lean`, `Families/Ported/Full.lean` | **P** |
| `prop:second` (the §5 assembly) | `Ported.secondMoment : SecondMomentAssembly` | `Families/Ported/Full.lean` | **P** |
| the two reductions of §4, §5 | `Ported.zeroSide_proof : ZeroSideReduction`, `portedReductions : PortedReductions` | `Families/Ported/` | **P** |
| finiteness of the zero sets (the counts are true counts) | `Ported.Zero.zerosI_finite` | `Families/Ported/Zero/Bridge.lean` | **P** |

**Classical inputs** (all proved; `Families/Hyp/`):

| Input | Lean | Status |
|---|---|---|
| Montgomery–Vaughan large sieve (`eq:MVLS`), absolute constant `17/4` | `Hyp.MV_LargeSieve_proof : MV_LargeSieve` | **P** |
| prime number theorem with error term (`eqB:PNT`, weak form) | `Hyp.PNT_dlVP_proof : PNT_dlVP` | **P** |
| Stirling bounds for `Re ψ` | `Hyp.StirlingDigamma_proof : StirlingDigamma` | **P** |
| Montgomery-type zero density for `T' ≤ Q^A` (`eq:Montuniform`, q-aspect range) | `Hyp.Montgomery.Montgomery69_Density_upTo_proof` | **P** |
| Montgomery-type zero density at all heights | `Montgomery69_Density` | **H** (not proved, not needed by `thmMain`) |
| the same, from a `t`-aspect input | `Hyp.Montgomery.Montgomery69_Density_of_tAspect` (hypothesis `TAspectDensity`) | **I** |

**Conditional variants** (proved, not used by `thmMain`): `thmMain_of_components` (from the (a) statements,
`ClassicalInputs`, `PortedReductions`), `thmMain_of_montgomery` (from `ClassicalInputsReduced`, i.e. the full
`Montgomery69_Density`), with the bundles `ClassicalInputs`, `ClassicalInputsReduced`, `PortedReductions`,
`PortedReductionsReduced` (**D**) and the reductions `ClassicalInputsReduced.toFull`,
`PortedReductionsReduced.toFull` (**P**).

## Further proved results (library `Families`)

| Paper | Lean (file) | Status |
|---|---|---|
| IK (3.9): primitive-character orthogonality, `φ* = φ * μ` | `sum_primChars_eq`, `sum_primChars_eq_zero_of_not_coprime`, `phiStar_eq` (`Toeplitz.lean`) | **P** |
| `lem:toeplitz`: `Δ = k_ω(n−m)` on rough `n, m`; `k_ω = ∑ Ω(e) c_e`; `eqC:farey`; `k_ω(0) = μ_Ω(𝕋) = H` | `toeplitz_identity`, `Δ_rough_shift_invariant`, `kω_eq_ramanujan`, `famForm_eq_levelForm_Ω`, `kω_zero`, `muΩ_mass` (`Toeplitz.lean`) | **P** |
| `lem:gauss` (Gauss-sum transfer) | `gauss_transfer` (`Toeplitz.lean`) | **P** |
| `lem:S` | `lemmaS`, `lemmaS_forms`, `lemmaS_rough`, `toeplitz_posSemidef`, `toeplitz_mono` (`LemmaS.lean`, `Glue.lean`) | **P** |
| `lem:S`, duality bound, from `lem:dual` | `lemmaS_lambda_of_dual` (`Glue.lean`) | **I** |
| `lem:Omega` (b); `eqC:Omega`, second form; `m(u) = 0` for `u > 1/2` | `lemOmega_b`, `Ωlev_eq_second_form`, `mfun_eq_zero_of_gt_half` | **P** |
| Schur test | `schur_test` (`Schur.lean`) | **P** |
| `lem:M1` | `lemM1` (`M1.lean`), `lemM1_diag` (`M1Diag.lean`) | **P** |
| `lem:M2` (exact statement, constant 4) | `lemM2` (`Glue.lean`) | **P** |
| `lem:M3` (i)–(iv) | `lemM3_i`, `lemM3_ii` (`PrimeSide.lean`), `lemM3_iii_iv` (`M3.lean`) | **P** |
| `prop:count`, finite core (`SL₂(ℤ)` spokes, gcd preservation, isolated point, Möbius step) | `Spokes.*` (`Spokes.lean`) | **P** |
| `lem:A`, side facts: `R_w ≤ w_max/c_w`; sharp weight `V_w = 2η⁻²`, `c_w = (6/π²) log(1/η)` | `Rw_le`, `wSharp_Vw_cw` (`Weights.lean`) | **P** |
| `eq:logwide`: the two weights are admissible | `wSharpWeight`, `wSmoothWeight` (`Weights.lean`) | **P** |
| `lem:ranktrace`, `lem:blocks` (`n₊` bounds), `prop:perchi`, the ω-weighted family sum | `Cert.ranktrace`, `Cert.posIndex_offline_le`, `Cert.BlockData.perchi`, `Cert.perchi_weighted` (`Certificate/PerChar.lean`) | **P** |
| `prop:cert`, rows `C = 1` and `C = 1.2688`: `p(1) ≥ 0.932282`, `p(1.2688) ≥ 0.885912` | `pC_one_ge`, `pC_12688_ge` (`Certificate/Numerics.lean`; kernel data `CertData.cert1`, `cert2`) | **P** |
| `lem:pLip` | `pC_antitone_lip`, `lemPLip` (`PLip.lean`, `Main.lean`) | **P** |
| `ℰ > 0`, `ℰ ≥ 0.47914`, `1 < C_G ≤ 1.2688`, hence `p(C_G) ≥ 0.885912` | `Ecal_pos`, `Ecal_ge_047914`, `one_lt_CG`, `CG_le`, `thmGauss_constant` (`Constants.lean`, `Certificate/Ecal.lean`, `Glue.lean`) | **P** |
| the constant of Theorem 1.1 | `thmMain_constant` | **P** |
| `cor:LmultA`, from `lem:A` and `lem:WH` | `corLmultA_of'` (`Glue.lean`) | **I** |
| Theorem 1.2, part (1) (general `w`), from `thm:conditional`, `lem:A`, `lem:WH` | `thmGauss_general_of'`, `LS_of_corLmultA` (`Glue.lean`) | **I** |
| `thm:conditional`, from the profile bound `profileLS_Statement` and proved inputs | `Phase4.A.thmConditional_of_components` (`Families/Phase4/A/Conditional.lean`) | **I** |

## Theorem 1.4(a): the proof (library `FamiliesH`)

`thmH = thmH_of_parts …` (`FamiliesH/Glue.lean`, **P**), with the κ-cells argument `thmH_of_cells` and the one-cell
theorem `thmHcell_of_parts` (**P**). The 15 component theorems (`FamiliesH/Components.lean`) are all **P**; the
numbering is that of the paper, as in the Lean docstrings (`STATEMENTS-H.md` maps the Lean names to it).

| Paper | Lean | Package (folder) | Status |
|---|---|---|---|
| Proposition 9.9, Lemma 9.2 (lower half): the zero side | `propZeroH_unconditional` | Z (`FamiliesH/Z/`) | **P** |
| Proposition 9.19 via Lemma 9.10: the second moment | `secondMomentH` | S (`FamiliesH/S/`) | **P** |
| Lemma 9.11 (both claims) | `lemB1H`, `eqBMratH` | F (`FamiliesH/F/`) | **P** |
| Lemma 9.12 | `lemB2H` | F | **P** |
| Lemma 9.1 (the sizes (S1)–(S4)) | `lemSizesH` | F | **P** |
| time localisation (§9.3) | `lemM1H`, `lemM3H_iii` | F | **P** |
| Lemma 9.13, Corollary 9.14 (tails) | `lemM3primeH`, `corTailsH` | F | **P** |
| Proposition 9.18 (the band device) | `propTIsharpH` | TS (`FamiliesH/TS/`) | **P** |
| Lemma 9.21 | `lemMbeta` | V (`FamiliesH/V/`) | **P** |
| Lemma 9.22 | `lemPLipH` | V | **P** |
| §9.4, the limit step (with Lemma 9.23) | `assemblyLimitH` | V | **P** |
| Proposition 9.24 (the κ-table certificates, column (a), `n = 400`) | `certH` | V (`FamiliesH/V/CertData.lean`, kernel-evaluated) | **P** |
| checks: `pB 2 C = pC C`; the admissible class at `β = 2`; `κ_{Q^κ} = κ` | `pB_two`, `admissibleB_two_iff`, `kappaT_rpow` (`FamiliesH/StatementCheck.lean`) | | **P** |

## Stated only (not proved in this project)

| Paper | Lean definition (file) | Status |
|---|---|---|
| Theorem 1.2 (`thm:gauss`) | `thmGauss_Statement` (`Families/Main.lean`) | **S** |
| Theorem 1.3 (`thm:fixed`) | `thmFixed_Statement` (`Families/Main.lean`) | **S** |
| `thm:conditional` | `thmConditional_Statement` (`Families/Main.lean`) | **S** |
| Lemma A (`lem:A`) | `lemA_Statement` (`Families/LemmaA.lean`) | **S** |
| `lem:harm` | `lemHarm_Statement` (`Families/LemmaA.lean`) | **S** |
| `lem:Rwlog` | `lemRwlog_Statement`, `lemRwlog_numeric_Statement` (`Families/LemmaA.lean`) | **S** |
| `lem:WH`, the ratio `W/H → C_G` | `lemWH_ratio_Statement` (`Families/LemmaA.lean`) | **S** |
| `prop:TI` | `propTI_Statement` (`Families/PrimeSide.lean`) | **S** |
| `prop:CTfixed` | `propCTfixed_Statement` (`Families/LemmaC.lean`) | **S** |
| the profile bound from `LS(C)` (input of `thm:conditional`) | `Phase4.A.profileLS_Statement` (`Families/Phase4/A/Conditional.lean`) | **S** |

The first nine rows are the 10 `Prop` definitions that `scripts/audit.sh` checks as stated only (the list in
`README.md`); their docstrings say "Stated only; not proved in this project". The last row, `profileLS_Statement`, is
an auxiliary statement (not a labelled result of the paper), used only as the hypothesis of the proved implication
`Phase4.A.thmConditional_of_components`. None of these is used by `thmMain` or `thmH`. They rest on the written proofs of the paper; the numerics of
Theorem 1.3 are certified by the interval-arithmetic scripts shipped with the paper as ancillary files.

## Not stated

Theorem 1.4(b) (Gauss route) and 1.4(c) (classical route); Corollary 1.5 (the dyadic family); the rows κ = 1/4, 1/2
of the κ-table and its columns other than (a); the rows `C = 1.0434, 1.0911, 1.2890, 1.3055, 1.3448` of `prop:cert`
(used only by Theorem 1.3).
