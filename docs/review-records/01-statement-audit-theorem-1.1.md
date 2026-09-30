> **Note on the current state.** Since this review, the 10 unproved results were converted from `sorry`
> placeholders to `Prop` definitions, so the audit now reports zero `sorry`; its check "exactly ten sorry roots" was
> replaced by the check that there are none, together with a check that the ten results are present as `Prop`
> definitions without proof constants. `lean/scripts/NonVacuity.lean`, run by the audit, now ships non-vacuity
> checks of the kind this audit compiled (N > 0 eventually, uniformly in T; the ratio form).

> **Cleaned copy of an internal review record: internal file paths and identifiers removed; content otherwise unchanged.**
> The reviewer is OpenAI's Astra; Claude produced the paper and the formalisation.
> Notes on this copy: the review date, repository paths, branch names and commit identifiers of the audited snapshot
> have been removed. File references such as `Main.lean:122` are relative to `lean/Families/` and give line numbers
> in the audited snapshot; the definitions audited are pinned by `lean/scripts/Statements.baseline.txt` and are
> unchanged in this repository. The audit brief and the evidence files it links to are internal and are not
> included; where the report links to them, the link has been replaced by a note. The report describes an earlier
> state of the Lean project in which ten declarations off the headline chain were `sorry`; in this repository those
> results are present only as `Prop` definitions marked "Stated only; not proved in this project", and there is no `sorry` at all.

# Astra report: current families theorem and formalisation audit

**Reviewer:** Astra  
**Disposition:** Theorem 1.1 passes the requested correctness and statement-faithfulness audit. No substantive defect was found.  
**Scope:** The current headline of the families paper, its definitions and proof dependencies, and the five questions in the audit brief (internal; not included). This is not a fresh audit of the entire wider project.

## 1. Verdict and audited snapshot

`Families.thmMain : Families.thmMain_Statement` is proved with no hypotheses. A fresh build of every local project module and a transitive axiom audit reproduced the claimed result. Independent semantic checks support the correspondence between that statement and the paper's Theorem 1.1. The only difference in its conclusions is a harmless strengthening of the distinct-zero bound at the same named epsilon.

This resolves the earlier concern about an unfinished formal proof of the headline. It materially strengthens the correctness evidence for the weighted-family result. It does not establish publication priority, verify every auxiliary theorem in the paper, or prove RH or GRH.

| Snapshot | Value |
|---|---|
| Lean toolchain | `v4.33.0-rc2` |
| Mathlib revision | `51e6992efd06126df61a496bebf8f49482a4e129` |
| Zeta23 revision | `fbdc36bbf17d20af3fd0447c6d1a8a02773c9844` |
| Repository changes made by this review | None |

(Rows identifying the internal repository worktree, branch and commits have been removed from this copy.)

Source references below are relative to the project root (in this repository: `lean/` and `paper/`; bare Lean file names are under `lean/Families/`). [A preserved copy of the audited sources and the audit brief is kept with the internal record; not included here.]

## 2. What the theorem establishes

The family consists of primitive Dirichlet characters of moduli up to a growing parameter Q. A character of modulus q receives weight `w(q/Q) q/phi(q)`, for either of the paper's sharp or smooth log-wide weights. Zeros are counted in `(T,2T]`, uniformly for `(log Q)^a0 <= T <= (log Q)^A0`, where `0 < a0 < A0` are fixed.

For each prescribed positive error, sufficiently small fixed weight parameter eta gives the following asymptotic lower bounds on ratios of weighted zero totals:

- Simple zeros on the critical line: `N^s_0/N >= p(1) - error`, with `p(1) >= 0.932282`.
- Distinct zeros on the critical line: the same lower bound.
- Distinct zeros anywhere in the window: `N_d/N >= (1+p(1))/2 - error`, giving the limiting benchmark `0.966141` from the certified lower bound for p(1).

These are asymptotic, weighted proportions. The error can be made arbitrarily small by choosing eta appropriately and then taking Q sufficiently large. They are not a claim of those exact percentages in every finite collection, and the theorem supplies no practical numerical threshold for Q. The near-optimal constants require extreme parameter scales.

The denominator counts zeros with multiplicity. A simple zero has multiplicity one. The distinct-zero ratio compares the count of different zero locations with the count that includes repetitions; its numerator is not restricted to the critical line.

Nothing follows about any specified character, modulus, or individual zero. An exceptional off-line zero is compatible with all three bounds. No assertion is made that the remaining fraction actually lies off the line.

## 3. Reproduced machine evidence

The build used a temporary copy of all 169 tracked Lean-project inputs and a fresh local build directory. All **135 local modules** compiled successfully, with no failed or blocked modules. Existing compiled dependencies at the pinned revisions were reused; Mathlib and Zeta23 were not rebuilt from source in their entirety during this audit.

The unmodified `scripts/audit.sh`, run against the temporary project, returned exit code zero and ended with `AUDIT PASSED`. Its scan covered **2,498 non-internal project declarations**. All 77 baseline axiom-output lines were reproduced; 131 printed declarations had no `sorryAx` dependency.

The direct headline check reported:

```text
Families.thmMain : Families.thmMain_Statement
'Families.thmMain' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Those are the standard foundational axioms used by this Lean development. The headline has no residual mathematical hypotheses and no dependency on `sorryAx`, `Lean.ofReduceBool`/`native_decide`, or additional axioms. This is a transitive dependency check, including imported results.

Nineteen independent semantic lemmas were also compiled. These establish explicit parse identities, existence of both weights, nonempty height intervals, a populated and bounded-below variational class, integrability and Fubini, finite zero sets, genuine multiplicities, the modulus-one interpretation, eventual positivity of the denominator, and equivalence to ratio inequalities. Every final lemma depended only on the same standard axioms.

The final repository status was clean, and hashes of all 169 tracked Lean-project inputs matched the initial snapshot. The ancillary Lean code agrees with the development copy apart from provenance comments in two generated data files and an omitted certificate-generator script; the checked theorem content is the same.

## 4. Findings against the five questions

| Brief item | Verdict | Principal evidence |
|---|---|---|
| 1. Parsing and precedence | **FAITHFUL** | `lean/Families/Main.lean:122,186`; `Basic.lean:87`; `Variational.lean:19` |
| 2. Vacuity and default values | **FAITHFUL** | `Ported/Zero/Bridge.lean:101`; `Blocks.lean:67`; `Assembly.lean:82`; `Phase4/A/AssemblyLimit.lean:32` |
| 3. Strength and uniformity | **FAITHFUL**, locally **STRONGER** in the distinct-zero epsilon convention | `Main.lean:122,186`; `Ported/Zero/RvM.lean:149` |
| 4. Hidden restrictions | **FAITHFUL** | `Basic.lean:40,55,87`; `Weights.lean:145,281`; `Classical.lean:56`; `Variational.lean:23` |
| 5. Classical inputs and documentation | **FAITHFUL**, with accurately documented **WEAKER** intermediate estimates | `Hyp/Montgomery/Defs.lean:22`; `Hyp/Montgomery/Main.lean:270`; `paper/main.tex:189,856` (audited snapshot) |

### Item 1: the parsed statement is the intended one

The numeric certificate `0.932282 <= pC 1` is a separate outer conjunct. All three proportion bounds occur inside the uniform-height quantifier. The expression q/Q in the weight is real division; the critical-line coordinate is the real number one-half; the height exponents are real powers. The square integral in Qf is added outside the double-integral binder. Printed elaborated definitions and independently compiled equalities confirm these facts.

### Item 2: no remaining vacuity or default-value loophole was found

Lean assigns default values to some mathematically undefined expressions, so these checks were essential.

- `zerosI_finite` proves that the relevant zero sets are finite for primitive characters with q>1 and nonnegative T (`Ported/Zero/Bridge.lean:101`). Thus the finite sums and cardinalities cannot silently collapse to zero because the set is infinite.
- `mult_pos_of_mem_zerosI` proves that each counted zero has positive multiplicity (`Ported/Zero/Blocks.lean:67`). The analytic-order definition is applied to the actual L-function, with the analyticity and nonzero-function conditions justified by the imported analysis.
- Modulus zero never occurs in the family. Modulus one is the actual Riemann zeta function and its family weight is eventually zero. Density-count finiteness also covers modulus one (`Hyp/Montgomery/Trivial.lean:135`).
- Both specified weights have explicit constructors. The height interval is nonempty once log Q is at least one.
- `H_pos_eventually`, together with the unconditional Riemann-von Mangoldt lower bound, yields **eventual N>0 uniformly throughout the height interval**. This consequence was independently compiled without additional assumptions.
- The variational class contains one-half times the indicator of [-1,1], and Qf is bounded below by zero (`Phase4/A/AssemblyLimit.lean:32,45`). Its infimum is therefore populated and bounded below.
- The admissibility conditions imply genuine integrability of the square and kernel terms. Fubini identifies the iterated integral with the intended product integral. No default zero from a nonintegrable Bochner integral enters this variational constant.

### Item 3: no loss of the paper's uniform conclusion

The Q threshold occurs before the universal T quantifier. It may depend on the fixed exponents, weight and approximation error, as permitted by the statement. Once N>0, the multiplied inequalities are equivalent to the ratio inequalities; this equivalence was separately compiled.

The zero counts use exactly `(T,2T]`. N counts with multiplicity; the simple-line count requires both real part one-half and multiplicity one; the distinct counts use cardinalities. Although `zerosI` does not explicitly require real part between zero and one, the zero bridge proves that condition for the contributing primitive characters at positive heights (`Ported/Zero/Bridge.lean:57`).

There is one harmless difference: using `ProportionsAtLeast (..., pC 1 - epsilon)` gives the distinct-zero bound `(1+pC 1)/2 - epsilon/2` after the internal approximation error vanishes. The paper writes minus epsilon. Lean is stronger at the same named epsilon; the universally quantified formulations are equivalent by rescaling epsilon.

### Item 4: the family and variational domain have not been silently narrowed

`primChars` filters the full character universe solely by primitivity. There is no parity, real-character, or other hidden subfamily restriction. The cutoff is exactly `1 <= q <= floor Q`, and the weight has the stated real q/phi(q) factor. Both sharp and smooth weights satisfy the bounded-variation and positive-integral requirements.

`Lfun` uses Mathlib's analytically continued Dirichlet L-function, not the original series outside its convergence region. Its q=0 branch is irrelevant to the family, and the q=1 branch agrees with zeta.

The explicit L2 requirement in `AdmissibleWindow` preserves the paper's infimum under the usual mathematical interpretation: the excluded non-L2 candidates have infinite nonnegative square-integral cost. The infimum is not restricted to smooth functions, step functions, or the particular numerical certificate. Extending the kernel outside [0,2] also has no effect, since only distances between points in [-1,1] contribute.

### Item 5: the weaker proved classical estimates suffice

| Input | What is actually proved and used |
|---|---|
| Zero density | `Montgomery69_Density_upTo A` covers `2 <= T' <= Q^A`. The proof supplies `c = 1/(16(2+A))` and logarithmic exponent 6. At A=1, c=1/48. This is weaker than the full all-height contract, which is not used by the headline. |
| Large sieve | An absolute constant 17/4, rather than the sharper constant 1. The relevant uses require an absolute bound. |
| Prime number theorem | Error bounded by `C*x/(log x)^3`, sufficient for B2, rather than the stronger exponential error in the classical formulation. |
| Stirling/digamma | The actual logarithmic derivative of Gamma, for both parities, with proved asymptotic, growth and derivative bounds. Genuine derivative proofs rule out an undefined-derivative default. |
| Family mass | The stated W and H estimates, uniformly over admissible weights and real Q>=2, with an absolute constant. Finite variation and convergence of the Euler product are justified. |
| Zero-side reduction | `Ported.Zero.propZero_unconditional` proves the needed zero-side proposition and RvM lower bound. It has no hypotheses. |

`Ported/Zero/Bad.lean:210` proves that every application of the restricted density estimate has height at most Q. The proof adjusts its auxiliary exponents and logarithmic-saving parameter to the weaker density constant; it does not retain an unjustified sharper numerical choice.

The current paper's scope item (7) and Appendix A.4 correctly distinguish the proved headline, weaker formal inputs, handwritten auxiliary results, numerical certification and statement correspondence. Historical comments remain in a few Lean files but do not change their definitions or the current headline.

## 5. Minor findings and remaining formalisation gaps

**Minor audit-harness discrepancy.** The brief says `audit.sh` enforces exactly ten sorry roots. The script reports the global scan and enforces the headline's type, lack of hypotheses and axiom dependencies, but it does not explicitly assert that the root count or root list equals ten. The current independently inspected scan does contain exactly the advertised ten. A future regression check could assert that list explicitly. See `lean/scripts/audit.sh:25` onward (audited snapshot). No files were changed to implement this suggestion. [Editorial note: the audit script was later changed to assert the list explicitly; see review record 04.]

**Harmless epsilon convention.** The distinct-zero strengthening described above could be documented for readers comparing the statements literally. It does not require a mathematical repair.

The ten remaining sorry roots are:

```text
lemWH_ratio, lemRwlog_numeric, lemRwlog, lemHarm, lemA,
propCTfixed, propTI, thmFixed, thmGauss, thmConditional
```

None is used by `thmMain`. Consequently, it is accurate to call Theorem 1.1 formally proved, but inaccurate to call the whole paper formally verified. In particular, the Gauss-transfer and fixed-eta headline variants retain a different verification status.

## 6. Significance and limits of this report

The correctness assessment has improved substantially: the main weighted zero-statistics application now has a complete formal proof, and this audit found its statement faithful to the intended mathematics. There is no correctness-based reason from this audit to discard that application and retain only the sieve contribution.

Publication significance and novelty remain separate questions. The appropriate description is an unconditional, formally verified specialist result about weighted families of Dirichlet L-functions at specified growing heights. Claims of priority or a major advance over the closest literature still require a careful comparison of families, weights, height regimes and conclusions. This audit did not repeat that literature search.

This review did not independently redo every handwritten argument or the auxiliary numerical scripts. It did not rebuild the complete Mathlib/Zeta23 dependencies from source, and it did not review the whole wider project. Fresh compilation covered all local project modules; manual mathematical inspection concentrated on the statement, semantic bridges, relevant classical contracts and documentation. Formal verification assumes the usual correctness of the Lean implementation and foundational environment.

The theorem gives no result about a specified individual L-function and does not rule out all off-line zeros. Its success should be assessed as a family-statistics theorem, with the weights and asymptotic regime included in any public description.

## 7. Evidence and handoff

[The evidence bundle listed here in the original (execution logs, build results, printed definitions, the compiled
semantic-check files `StatementSemantics.lean` and `ZeroSemantics.lean` with their outputs, snapshot hashes, and a
preserved copy of the audited sources) is kept with the internal record and is not included in this repository.]

**Final correspondence verdict:** `Families.thmMain_Statement` is a faithful formalisation of Theorem 1.1, with a harmless strengthening of the distinct-zero epsilon convention.
