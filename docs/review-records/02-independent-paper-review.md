> **Note on the current state.** Since this review, the Lean proofs of both headlines were completed, and the 10
> results that remain unproved were converted from `sorry` placeholders to `Prop` definitions, so the audit now reports
> zero `sorry`. The paper has also changed (§9 was added; see `docs/VERIFICATION.md`).

> **Cleaned copy of an internal review record: internal file paths and identifiers removed; content otherwise unchanged.**
> The reviewer is OpenAI's Astra; Claude produced the paper and the formalisation.
> Notes on this copy:
> - This review was of an **earlier version** of the paper (53 pages), before §9 (polynomial height, Theorem 1.4) was
>   added and before the Lean proof of Theorem 1.1 was complete. Its statements about the Lean project (27 `sorry`
>   declarations; headline depending on `sorryAx`) describe that earlier state, not this repository. Line numbers
>   refer to that version.
> - Internal repository names, paths, branch and commit identifiers, and the review date have been removed. Links to
>   the reviewer's supporting files (three component reports, scripts and logs) have been replaced by a bracketed
>   note: those files are kept with the internal record and are not included here.
> - References to internal development notes (superseded working notes that preceded the paper) are replaced by
>   "[internal development note]"; the findings about them are kept verbatim. The response to this review is
>   summarised in `02b-response-to-paper-review.md`.

# Hostile review of the families paper

Reviewed source: the families paper and its development directory (internal repository; identifiers removed).

## Verdict

**I found no fatal mathematical error or unresolved load-bearing gap in the current assembled argument.** The current paper is a credible candidate for a publishable specialist advance in weighted family zero statistics, with a potentially important large-sieve contribution. Its broader significance and priority remain unestablished. The main proof survived direct scrutiny of its zero-side certificate, exceptional-character deletion, prime-side flattening, time localization, sharp weighted sieve, and the interface connecting those ingredients. Its numerical lower bounds reproduce.

That is an audit finding, not a complete formal proof or an acceptance certificate. The most substantial new analytic estimates remain supported by written proofs. The supplied Lean project proves useful components but leaves the headline theorem and major analytic ingredients unproved. My priority assessment is also bounded by the sources searched and read.

There are six minor corrections in the current mathematical text, including one literally false intermediate estimate and one omitted normalization factor. None breaks the two specified log-wide weight families or the numerical conclusions. There are more serious false or overstated claims in the older development notes, but the assembled paper has replaced the relevant arguments. The research record should mark those notes as superseded.

**Referee disposition:** request the specific corrections below and a focused specialist assessment of the sharp sieve and its application. I found no basis for rejecting this version on a demonstrated major proof gap. If the new analytic chain withstands specialist review, the result has a plausible claim to substantial novelty. Calling it a fully machine-verified theorem would be incorrect.

## Clarification of significance and publication strategy

This qualification incorporates the discussion following the initial review. The earlier description “a substantial result in analytic number theory” was broader than the evidence warrants. The current assessment is a potentially publishable specialist result; neither a field-wide breakthrough nor significant progress toward proving RH has been established. The weighting and height restrictions materially narrow the theorem. The existing 93.22% constant and inherited certificate also mean that the precise new sieve estimate and its application must carry the novelty claim. This does not simply remove GRH from Sono's exact theorem: the statistics differ.

The extreme sufficient thresholds limit concrete applicability, but do not themselves make an asymptotic theorem unimportant. The incomplete Lean formalization limits the verification evidence; it is not itself a gap in the written proof. These qualifications should be kept distinct from the six actual corrections below.

A standalone sieve manuscript is mathematically feasible: the weighted Farey bound, positive Toeplitz majorant and limiting constant can be proved without the zero-counting argument. A paper centred on those results could be easier to review. Its publication case would require a precise comparison with the closest weighted/sifted large-sieve results. The all-vector estimate is for the positive Toeplitz form; identification with the primitive-character family retains the rough-support restriction.

The recommendation is to make the sieve contribution central while preserving the zero theorem as an application or a companion manuscript. The application demonstrates the value of the constant and the coefficient-replacement argument. Removing it would shorten the proof but leave the principal new analytic estimate, and its novelty, to be checked. **No recommendation has been made to discard the application.**

## What the result actually says

For primitive characters of conductors `ηQ ≤ q ≤ Q`, the sharp weight per character is

\[
\omega_\chi=\frac{Q^2}{q\varphi(q)}.
\]

There is also a smooth logarithmic weight. The numerator counts simple zeros on the critical line with `T < Im ρ ≤ 2T`; the denominator counts all zeros in that interval, including multiplicity, with the same character weights. The height satisfies

\[
(\log Q)^{a_0}\le T\le(\log Q)^{A_0},\qquad 0<a_0<A_0\text{ fixed}.
\]

The strongest limiting lower bound is `p(1)−ε`, with an exact certificate `p(1) ≥ 0.932282`. For each required accuracy, choose sufficiently small **fixed** η and then let Q tend to infinity. It is not a theorem with η shrinking arbitrarily as a function of Q. The distinct-zero conclusion is at least `0.9661−ε`; that conclusion counts distinct zeros wherever they lie, and should not be described as 96.61% simple critical zeros.

The best stated fixed-weight example is **92.41%** simple critical zeros at smooth `η=10⁻⁴`; smooth `η=10⁻³` gives **91.55%**. The explicit coarse convergence rate guarantees 93% only at extraordinarily wide conductor ranges: `log(1/η) ≥ 37000` for the smooth weight, or `19000` for the sharp one. These are sufficient bounds, not established necessary thresholds. No useful effective Q threshold is supplied.

These distinctions matter to significance. This would be an unconditional advance for a specific family statistic. It does not prove RH or GRH, improve the proportion for ζ itself or an individual L-function, or establish the same percentage in an unweighted family. The paper states these limitations explicitly at `main.tex:94–96,152–160,762–765`.

## Why the main proof survived

The three delegated reviews were carried out as separate mathematical tasks, with their own derivations and new checks. They are automated reviews, not three human expert endorsements. Prior positive referee reports inside the repository were treated as claims to compare after the initial derivations.

| Part | What was checked | Assessment |
|---|---|---|
| Finite-dimensional zero certificate | Same-character symmetry for complex χ; inertia of off-line pairs; rank–trace inequality; multiplicity charges; nonnegative weighted summation | Correct in the checked derivation. The framework is inherited and attributed. |
| Zero-side analysis | Explicit-formula signs and Fourier normalization; finite-centre errors without a hidden matrix-dimension factor; family zero count; density-shell deletion; exterior tails | No substantive gap found. Montgomery's original theorem was inspected, including the family range and logarithmic power 13. |
| Flattening | Complete-period cancellation of the Ramanujan subtraction; smooth Poisson errors; all three coefficient moments; dyadic overlap; floors and truncation levels | Correct upper bound. No GRH or prime-distribution-in-progressions hypothesis is introduced. |
| Time localization | Actual positive kernel factorization; short-interval Schur estimate; localization tails; uniformity for every fixed `a₀>0` | The loss is `O(T⁻¹/⁴)` and tends to zero throughout the stated range. |
| Weighted Farey and Toeplitz estimates | Local rational/spoke counting, isolated atoms, endpoint and wraparound cases, arithmetic densities for arbitrary finite prime sets, positive majorization and log-wide limit | No counterexample or unresolved gap found in the reviewed proof. This is a principal candidate for novelty. |
| Application of the sharp estimate | Rough-support identity, removal of prime-power residuals, switch to a positive form defined on all vectors, insertion of flattened coefficients, low/high additive denominators | The current argument handles the support mismatch explicitly and pays the errors. |
| Final assembly | Factors of 2, π and bandwidth; smooth-window approximation; monotonicity of p(C); all fixed-parameter limits; exact certificates | The stated constants follow from the checked chain. |

The most tempting fatal objection is that the flattened vector is not supported on integers free of primes up to Q. That objection is valid against a naive application of the rough-support identity, but **not against this version**. The paper first applies the identity to the rough portion of the prime vector, moves into the positive Toeplitz majorant, and only then replaces that vector by the flattened coefficients. At low additive denominators there really are resonances; they are bounded with a length saving. At high denominators, smooth Poisson summation supplies cancellation. The current proof does not assume that all the subtraction terms remain invisible after localization.

Another dangerous point is the deletion of a small number of bad characters whose matrices might be huge. The proof uses the upper bound `4x−x² ≤ 4` for each real eigenvalue, not an absolute-value bound. Large negative contributions cannot spoil that deletion argument. The finite-centre estimate likewise uses a frame bound independent of matrix dimension, with summable endpoint tails. These possible hidden losses were rechecked explicitly.

The separate **88.59%** Gauss-transfer route also survived review. It avoids the sharp positive-Toeplitz application but shares the zero-side argument, flattening, time localization, and parts of the Farey analysis. It is a useful fallback theorem, not an entirely independent verification of every ingredient in the 93.22% route.

Detailed derivations and exact coverage:

- Zero-side review; prime-side and interface review; large-sieve review. [Component reports kept with the internal record; not included.]

## Corrections to the current manuscript

All source locations below refer to the reviewed version of the paper (line numbers in that version). These are actionable corrections, not hypothetical objections.

1. **False intermediate lattice bound for small exponents.** At `paper/main.tex:250`, the proof asserts `Σₖ(1+L|r−τₖ|)⁻²ᴬ ≪ (1+D)¹⁻²ᴬ` over the advertised `A≥0` range. For `A=0` and `r∈J`, the left side is the number of centres, of order TL, while the right side is 1. At `A=1/2` there is logarithmic growth. Prove the lattice estimate for `A>1/2` and obtain smaller requested exponents from a stronger estimate. All actual applications use sufficiently large A, so this is an immediate repair.

2. **Missing weight-size factor in the general far-field bound.** In `paper/lemmas/lemma-toeplitz-C.tex:370`, `m-tilde(t) ≤ 3(t/η)²` needs a factor `‖w-tilde‖∞` for a general weight. Restore that factor in the corresponding `T₁⁻²` term of Proposition CTfixed(b), or impose the normalization explicitly. Both weight shapes actually used for the headline numerical theorems have `‖w-tilde‖∞=1`; their certificates are unaffected. This is a defect in the stated generality and its proof, not a counterexample to the headline theorem.

3. **Incorrect parameter description in a valid seminorm inequality.** At `paper/lemmas/lemma-toeplitz-C.tex:461`, the text says both successive splits use `κ=κ_T`. That would unnecessarily give a residual coefficient of order `κ_T⁻²`, instead of the displayed `O(κ_T⁻¹)`. Use κ_T for the first split and κ=1 for splitting the two residuals. The displayed bound then follows directly and the asymptotic error estimate stands.

4. **Introductory assumptions allow a degenerate weight.** At `paper/main.tex:63`, nonnegative, nonzero BV is insufficient for `H ≍ Q²`. A function equal to 1 at `u=1/2` and zero elsewhere is a counterexample. Require positive integral `∫u w(u)du>0`, as the actual admissibility definition already does at line 203. The stated log-wide weights are safe.

5. **Clarify the local density on overlapping dyadic blocks.** At `paper/lemmas/lemma-B-majorant.tex:126`, the proof controls the square of a blend by a convex combination of block squares. Its density is the corresponding weighted block majorant, not a freely selected block's density. The subsequent proof uses the correct convexity inequality. Adjust the descriptive sentence.

6. **List all fixed-data dependencies consistently.** At `paper/lemmas/lemma-B-majorant.tex:82`, invisibility constants also depend on the smooth cutoff and partition derivative bounds. The global parameter convention already allows this dependence. Make the local notation consistent with it.

## Findings in the associated body of work

The folder contains a history of substantially changing arguments. Its status labels cannot all be read as simultaneous current claims.

- **An older Bochner shortcut is invalid.** [internal development note] identifies the double-time form with a nonnegative scalar mixture of pure twists `bₙn⁻ⁱᵗ`. Such a mixture has a kernel depending only on `log n−log m`, with constant diagonal. The required kernel has diagonal `∫g(u)|Jhat(u−log n)|²du`, which depends on n. The current M1/M3 and TIsharp arguments supply the correct representation and application.
- **An old positivity assertion fails for the smooth weight.** [internal development note] claims positivity extending to log-smooth weights in a range where it need not hold. Take `η=1/3`, odd e, and `Q=3e`. At `e=ηQ`, the smooth endpoints vanish and `Ω(e)=−w(2/3)<0`. The current paper explicitly allows this negative part and majorizes it.
- **A half-integer phase-conjugation claim in [internal development note] is not valid in general.** The current modulus-Schur proof avoids that shortcut. The large-sieve report gives the algebraic issue.
- **The old 94.30% distinct-zero lower bound rounds upward.** [internal development notes] use `0.9430−ε`, whereas the simple-zero certificate 0.885912 gives `(1+0.885912)/2=0.942956`. This does not justify 0.9430 for every ε>0. The current theorem correctly states 0.9429.
- **Numerical evidence is overstated in an open narrow-weight route.** [internal development note] labels a proposed assertion true from experiments while retaining an open input. Proving a theorem after choosing log-wide weights does not prove the same constant for an arbitrary preassigned narrow weight. This is not an assumption of the current main proof.
- **Several old dependency descriptions are stale.** Restrictions such as `R<ηQ`, the claim that the mixed term itself forces bandwidth below 2, and descriptions of Project B as an all-vector primitive-character inequality do not describe the current argument accurately. The assembled paper contains more careful statements.

These are meaningful defects in the historical body of work. They are not grounds for carrying a repaired objection forward against the current paper. Add prominent version/status notices to the old A/B files and make the assembled manuscript the authoritative theorem statement. In particular, previous agents' labels such as “proved,” “truth,” and numerical confidence percentages are not additional proof evidence.

## Novelty and relationship to the literature

The number **0.9322826… is already in the literature**. Sono's Theorem 1.1 obtains it under GRH for a weighted low-lying-zero statistic. The current paper acknowledges this and changes both the hypotheses and the statistic. Its claim should be framed as an unconditional family theorem reaching an existing extremal constant, not as discovery of the constant. [Sono, 2016](https://doi.org/10.1017/S0004972715000623).

| Ingredient or comparison | Priority assessment |
|---|---|
| Finite-compression/inertia certificate | Inherited from Alpöge–Furman and adapted to Dirichlet families by Hua–Yang. Weighted summation is an adaptation, not a newly invented certificate. |
| Truncated Ramanujan approximant and its mean-square motivation | Classical: the identical approximant occurs in Vaughan's work. The present scale choices and use in this proof require checking, but the approximant itself is not new. |
| Rational local-density/spoke method for large sieves | The general strategy has precedents in Wolke/Baier and Ramaré. An elementary Toeplitz identity, Schur test, or rational approximation step is not by itself a strong novelty claim. |
| Explicit normalized weighted profile, positive all-vector Toeplitz envelope, and its constant tending to 1 | Plausible substantive contribution. No inspected source supplied this exact result. |
| Rough-vector transfer followed by the controlled insertion of flattened coefficients | Plausible substantive contribution in the combination and estimates needed here. |
| Unconditional 93.22% limiting weighted simple-critical-zero bound | Plausibly new as precisely stated, subject to the analytic proof and a broader specialist priority check. |

Primary sources actually inspected include [Alpöge–Furman v2](https://arxiv.org/html/2608.13637v2), [Hua–Yang v2](https://arxiv.org/abs/2608.16034), [Chandee–Lee–Liu–Radziwiłł](https://arxiv.org/abs/1211.6725), [Vaughan's author-hosted paper](https://personal.science.psu.edu/rcv4/personal/Publications/newvm001.pdf), [Baier's sparse-moduli paper](https://arxiv.org/abs/math/0512228), and [Ramaré's 2009 book](https://ramare-olivier.github.io/Maths/HRILectures.pdf). The latter two have closely related local concentration and sieve machinery; they should feature in a careful novelty comparison. The recent [Ramaré weighted-sieve preprint](https://arxiv.org/abs/2609.25885) did not, in the sections inspected, state this exact primitive-family positive-Toeplitz theorem.

Alpöge–Furman Remark 7.2 already announces a varying-modulus family result of **81.1%** with different weights and bandwidth, without a detailed derivation there. The current paper appropriately describes the announcement and does not claim its own differently normalized numerical calculation refutes it. The 2025 unconditional **60.44%** simple-critical-zero result of [Sono](https://arxiv.org/abs/2105.07422) concerns a different mollifier-based family statistic. These are relevant comparisons, not a league table of identical theorems.

This was a targeted literature audit as of the review date. It was not a comprehensive review of every older weighted large-sieve theorem, every recent preprint, or every cited paper's full proof. Absence of a competing result in this search is evidence for plausible novelty, not proof of priority.

## Reproduced computations and formal checks

All computations ran against a separate source snapshot. The source worktree remained clean, and all 456 tracked source-file hashes were checked again at the end.

### Exact rational certificates

The supplied `certify.py` was rerun with 1600 intervals. A second implementation was written for this audit without importing manuscript code. It derives the step-function interaction by interval distance, uses exact rational arithmetic after choosing integer heights, and checks positivity, evenness, normalization and all seven relevant lower bounds.

| C | Value at the independently checked admissible step function | Safe stated lower bound |
|---|---:|---:|
| 1 | 0.932282587884294… | 0.932282 |
| 1.0434 | 0.924182281540859… | 0.924182 |
| 1.0911 | 0.915550287631059… | 0.915550 |
| 1.2688 | 0.885913527580974… | 0.885912 |
| 1.2890 | 0.882798788698943… | 0.882798 |
| 1.3055 | 0.880293486145547… | 0.880293 |
| 1.3448 | 0.874467832961742… | 0.874467 |

These are lower certificates for the continuous variational supremum; numerical optimization is not being used as a proof that the optimizer is globally optimal. The exact evaluations at admissible functions suffice.

Evidence: [reviewer's scripts and logs, kept with the internal record; not included].

### Interval arithmetic

All six positive-Toeplitz bounds and all three Farey bounds were recomputed, including the 64 finite prime sets, remote ranges and error allowances. The two crucial smooth-weight estimates returned upper bounds `1.090989281…` and `1.043289188…`, safely below the paper's `1.0911` and `1.0434`. All **17** arithmetic-constant inequalities also passed. This includes the Euler product, `C_G<1.268774`, the uniform convolution bound and the omitted-prime slack.

Evidence: [reviewer's scripts and logs, kept with the internal record; not included]. The current interval programs were read, including exact endpoint comparisons and truncation/interpolation controls. They were not independently rewritten in full. Their numerical enclosure depends on the correctness of the analytic finite-reduction and far-field lemmas, reviewed separately.

### Independent arithmetic and analytic sanity checks

New scripts independently checked 5,952 complete-class cancellation cases, 4,096 Ramanujan orthogonality pairs, 4,212 CRT/spoke-density cases, 3,200 arithmetic-density identities, 2,000 finite-set convolution identities, and 14,406 finite multiplicity configurations. Independently generated primitive characters reproduced the rough Toeplitz identity to floating precision. Separate experiments tested coefficient moments, genuine low-denominator resonances, high-denominator cancellation, and local-count behavior near holes and isolated atoms.

These tests catch signs, factors and finite counterexamples. They do not establish asymptotic uniformity or replace the written proofs. Their implementations and JSON outputs are in the three component-review directories.

### Lean

A fresh build of the local project modules succeeded against the pinned Lean and dependencies. The dependency cache was reused; it was not a from-source rebuild of all Mathlib. There are **27 declarations using `sorry`**. An added audit module printed the axioms of headline and component results.

The main theorem, Gauss theorem, fixed-weight theorem, zero-side proposition, second moment, B1/B2, sharp sieve and its limiting estimate all depend on **`sorryAx`**. They are not machine-proved. In contrast, the sampled claimed-complete results—Toeplitz identity, Gauss transfer, positivity, M1/M2/M3, the per-character certificate, numerical p(C) bounds and the Euler-product lower bound—do not depend on `sorryAx`; their printed dependencies are the standard Lean axioms. The three sampled kernel arithmetic certificates use no axioms.

This agrees with the manuscript's explicit disclosure at `main.tex:817–822`. It is a meaningful partial formalization, not misleading evidence of a complete theorem. I inspected key definitions and statement boundaries, but did not perform a line-by-line semantic audit of all Lean proofs and imported dependencies.

Evidence: [reviewer's scripts and logs, kept with the internal record; not included]. The earlier `lean-build.log` records a sandbox tool-location failure; the later successful log is the relevant build result.

## Coverage and preservation

The tracked folder contains **456 files, 3,749,647 bytes**. A hashed manifest and separate snapshot were made before verification. The review directly covered all current mathematical TeX in `main.tex`, the three substantive lemma files, and `constants.tex`: **2,215 source lines, 204,928 bytes**. These files contain the assembled proof and numerical tables; their relatively small share of the directory's bytes should not be mistaken for the share of mathematics checked, since the folder includes extensive generated logs, duplicated code and historical experiments.

The review also read the principal A/B development notes, selected earlier referee reports and responses, the main certification programs, the Lean status/statement documents, and selected Lean definitions and proofs. The component reports identify their assigned coverage. **We did not independently review every one of the 456 files or rerun every scratch experiment.** No percentage is claimed for the older RH corpus, which was outside this task.

The untracked multi-gigabyte dependency cache was not copied into the source snapshot. All original source hashes still match; git status of the reviewed working copy is clean. No manuscript edits, commits, pushes or external communications were made.

Evidence: [reviewer's scripts and logs, kept with the internal record; not included].

## What should happen before treating this as an established result

Apply the six local corrections, clearly retire the false older proof sketches and rounded claims, and strengthen the comparison with classical weighted/sifted large-sieve work. The main remaining review effort should be concentrated on the arbitrary-centre local-count estimate, its uniformity over rational denominators and prime sets, and the positive-Toeplitz application to the localized flattened vector. These are the mathematically valuable parts and the parts where another expert's scrutiny would add most.

The favorable conclusion is earned by the current derivations and reproduced certificates, not by the number of prior agents' reviews. On the evidence of this audit, the work merits that specialist attention.
