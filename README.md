# Simple zeros on the critical line for a weighted family of Dirichlet L-functions, from polylogarithmic to polynomial height

**Status: pre-publication draft.** Author: Nic Johns. Licensing: the paper and documentation are CC BY 4.0, the Lean
formalisation and scripts are Apache-2.0 (see [Licence](#licence)).

This repository contains a mathematics research paper (74 pages) in analytic number theory, a machine-checked Lean 4
formalisation of its two headline theorems, the scripts and logs behind every numerical constant used in a proof,
and cleaned copies of the independent reviews it has received.

**How it was made.** The mathematics, the proofs, the numerical certificate scripts, the Lean formalisation and the
text were produced by AI agents: instances of Anthropic's Claude working as coordinated agents, with separate Claude
agents acting as hostile referees. The independent checks included a review of the paper and an audit of the Theorem 1.1
statement by a frontier AI model from another developer (not Claude).
**No human mathematician has yet checked the proofs line by line.**

## What the result says, in plain language

The **Riemann zeta function** ζ(s) encodes the distribution of the prime numbers. Its "nontrivial zeros" are complex
numbers ρ = β + iγ with 0 < β < 1. The Riemann Hypothesis (RH), one of the best-known open problems in mathematics,
says that all of them lie on the **critical line** β = 1/2. It is also conjectured that every zero is **simple**
(occurs with multiplicity one).

**Dirichlet L-functions** L(s, χ) are the analogues of ζ(s) attached to "characters" χ modulo an integer q (the
modulus, or conductor). They control primes in arithmetic progressions. The Generalised Riemann Hypothesis (GRH) says
that their nontrivial zeros also all lie on the critical line.

Neither conjecture is proved. A standard way to measure progress is to prove that **a positive proportion** of the
zeros are simple and lie on the critical line. For ζ alone, the best unconditional proportion of zeros proved to be
simple and on the critical line was around 40% (by Levinson–Conrey-type methods, e.g. 40.58% by Bui, Conrey and Young,
2011) until 2026, when it was raised above 2/3 (0.6725, Alpöge and Furman). For large *families* of Dirichlet L-functions, the previous unconditional
records for simple zeros on the line were 0.56 (Conrey–Iwaniec–Soundararajan, 2013) and 0.6044 (Sono, 2025), in
slightly different families and normalisations. At heights polynomial in the modulus, the closest unconditional
result known to us is 38.2%, on average over the primitive characters modulo a single q (Dickinson, 2024).
Under GRH, for a related statistic of low-lying zeros, Sono (2016) obtained 0.9322, and Chirre, Gonçalves and de Laat
(2020) improved this to 0.9350.

**What is new here** (paper §1.1, pp. 2–5):

1. **At least 0.9322 − ε at low height, unconditionally, on weighted average (Theorem 1.1).** Take all primitive Dirichlet
   characters with conductor q between ηQ and Q, give each a specific weight (roughly Q²/(qφ(q))), and count zeros
   with height between T and 2T, where T lies between fixed powers of log Q. Without any unproved hypothesis, the
   weighted proportion of zeros that are simple and on the critical line is at least 0.9322 − ε, for any ε > 0,
   once η is small enough and Q is large enough. This equals the constant Sono obtained under GRH for a related, not
   identical, statistic of low-lying zeros; for that statistic Chirre, Gonçalves and de Laat later obtained 0.9350
   under GRH. The constant itself is not new.
2. **Above 2/3 at every fixed polynomial height (Theorem 1.4).** Fix any power κ₁ > 0. Uniformly for all heights
   T from a fixed power of log Q up to Q^κ₁, the weighted proportion of zeros with height between T and 2T that are
   simple and on the critical line is at least an explicit constant minus ε. The constant depends only on
   κ = log T/log Q and decreases as κ grows: at least 0.8656 − ε for T ≤ Q, 0.7641 − ε for T ≤ Q⁵ and 0.7274 − ε
   for T ≤ Q¹⁰. It stays above the Montgomery–Taylor value 0.6725..., hence above 2/3, for every fixed power of Q.
   Previously the closest result, Hua and Yang's for the characters modulo a single prime q, exceeded 2/3 only at
   heights up to about q^0.0085 (paper §1.2).

The paper also gives a second route to 0.8859 − ε (Theorem 1.2), which avoids the new large-sieve estimate but shares
much of the rest of the argument, and explicit values at fixed η
(Theorem 1.3, smooth weight: 0.9155 at η = 10⁻³ and 0.9241 at η = 10⁻⁴).

**Why the fraction matters.** A proportion close to 1 for a large family is quantitative evidence of GRH-like
behaviour for that family, obtained without assuming GRH. Here the gain over earlier unconditional family results
comes from a large-sieve estimate that the paper claims as new (a sharp bound for a positive Toeplitz form; §1.3
separates it from the classical ingredients), which lets an existing
"positivity certificate" method run at twice the previous range (paper §1.3 and §1.5).

## What it does NOT show

- It is **not a proof of RH or GRH**, and it does not move towards them for any individual function (paper §1.4
  item 6). For ζ itself it gives nothing new.
- It says **nothing about any individual L-function**, modulus or zero. It bounds a *weighted average* over a
  family; a small weighted share of characters could behave arbitrarily. The weights are part of the statement and
  are essential to the constants.
- It gives **lower bounds only**: it does not show that the remaining zeros are off the line.
- The 93% figure is reached only in a **limit** (η → 0, then Q → ∞). The best value certified at a fixed η is 92.41%
  (η = 10⁻⁴). No effective size of Q is given; the implicit thresholds are astronomically large.
- Theorem 1.1 concerns zeros at height between powers of log Q; Theorem 1.4 extends this to fixed powers of Q,
  not beyond.
- **Human expert review is still pending.** All checking so far has been done by machines and AI systems.

## How it was verified

| Kind of evidence | What it covers | Where |
|---|---|---|
| **Lean 4 proof, checked by the Lean kernel** | Theorem 1.1 (`Families.thmMain`) and Theorem 1.4(a) (`Families.Hybrid.thmH`): no hypotheses, only Lean's three standard axioms, no `sorry` or `native_decide` anywhere in the project | `lean/`, `lean/scripts/audit.sh` |
| **Certified numerics** (exact rational or interval arithmetic) | every numerical constant used in a proof | `paper/anc/` |
| **Written proofs only** | Theorems 1.2, 1.3, 1.4(b), 1.4(c) and Corollary 1.5. Theorems 1.2 and 1.3 (together with the conditional Theorem 5.16, Lemma A and a few lemmas used only on the Gauss route or at fixed η; 10 definitions in all) are stated in Lean as `Prop` definitions only, marked "Stated only; not proved in this project"; Theorems 1.4(b), 1.4(c) and Corollary 1.5 are not stated in Lean | `paper/` |
| **Independent AI reviews** | the paper (one review by a frontier AI model from another developer, not Claude, and several Claude referees), the faithfulness of the Lean statements, the literature | `docs/review-records/`, `docs/VERIFICATION.md` |

What the Lean kernel guarantees is that the **Lean statements** follow from the axioms. Whether those Lean
statements say the same thing as the theorems printed in the paper is a separate question. It was audited by AI
reviewers, not by humans: for Theorem 1.1 by a frontier AI model from another developer (not Claude), and for
Theorem 1.4(a) by two Claude audits only (an audit of that statement by a model other than Claude has not been done).
The project also proves that the headlines are not vacuous (`lean/scripts/NonVacuity.lean`, run by the audit). The full list of what was and was not checked,
including errors found and corrected along the way, is in [`docs/VERIFICATION.md`](docs/VERIFICATION.md).

## Repository map

| Path | Contents |
|---|---|
| `README.md` | this overview |
| `paper/main.tex`, `paper/macros.tex`, `paper/refs.bib` | the paper's LaTeX sources |
| `paper/lemmas/` | the section files that `main.tex` inputs: `lemma-B-majorant.tex` (§§5.7–5.8), `lemma-A.tex` (§6.1), `lemma-toeplitz-C.tex` (§6.2), `polyheight.tex` (§9), `constants.tex` (App. A.5) |
| `paper/main.pdf` | the compiled paper (74 pages) |
| `paper/build.sh` | rebuilds `paper/main.pdf` (latexmk, or pdflatex and bibtex) |
| `paper/make-arxiv-bundle.sh` | assembles the arXiv source bundle (TeX sources, `main.bbl`, `anc/`, `lean/` copied to `anc/lean`, and the two licence files copied to `anc/`) and test-compiles it from a clean unpack |
| `paper/anc/` | the ancillary files as they would be posted on arXiv: certificate scripts, their output logs, and `README.md` with commands and expected output (on arXiv, `anc/lean` is added by the bundle script) |
| `lean/` | the Lean 4 Lake project, two libraries: `Families` (Theorem 1.1) and `FamiliesH` (Theorem 1.4(a)); its own `README.md`, `README-H.md`, `STATEMENTS.md`, `STATEMENTS-H.md`, `STATUS.md` and `scripts/audit.sh` |
| `docs/READING-GUIDE.md` | guided tour of the paper for a technical reviewer, with page numbers and the known weak points |
| `docs/VERIFICATION.md` | what was checked, how, by whom, with what result, and what was not checked |
| `docs/REFERENCES.md` | the key literature, with links, and how each work relates to this paper |
| `docs/review-records/` | cleaned copies of the most important independent review and audit reports (records 01–08 and 02b, with a `README.md`) |
| `.github/workflows/lean.yml` | continuous integration: builds the Lean project and runs the audit |
| `.gitignore` | ignores build products (`.lake/`, LaTeX auxiliary files, `paper/build/`) |

## Where to start

- **5-minute skim.** This file, then the abstract and §1.4 "What is claimed and what is not" of
  `paper/main.pdf` (pp. 1 and 8), then the "Limitations" section of `docs/VERIFICATION.md`.
- **A mathematician.** `docs/READING-GUIDE.md` (structure, precise statements, what is new and what is classical,
  where to look first), then `paper/main.pdf`. §1.3 (p. 6) separates the new ingredients from the classical ones;
  the table of dependencies (p. 10) shows which results each theorem uses.
- **A Lean user.** `lean/README.md`, then `lean/STATEMENTS.md` and `lean/STATEMENTS-H.md` (the definition-by-definition
  correspondence between the Lean statements and the paper), then run `lake build` and `scripts/audit.sh`
  (commands in `docs/VERIFICATION.md`). The two statement audits are in `docs/review-records/`.
- **Reproducing the numerics.** `paper/anc/README.md` (requirements, commands, expected results), with the
  summary and expected checks in `docs/VERIFICATION.md` §3. Everything runs in minutes on a single machine.

## Relation to other work

The method builds on the finite-compression positivity certificate of Alpöge and Furman (arXiv:2608.13637; the
paper records that the argument there is due to Claude) and its adaptation to Dirichlet families by Hua and Yang
(arXiv:2608.16034, arXiv:2609.27808). The Lean formalisation depends on Mathlib and on Anthropic's public Lean
formalisation of Alpöge–Furman (`zeta23` in <https://github.com/anthropics/formal-math>). See
[`docs/REFERENCES.md`](docs/REFERENCES.md).

## Licence

Copyright 2026 Nic Johns.

- **Paper and documentation** (`paper/*.tex`, `paper/lemmas/`, `paper/refs.bib`, `paper/main.pdf`, everything under
  `docs/`, and this top-level `README.md`): [Creative Commons Attribution 4.0 International](LICENSE-CC-BY-4.0)
  (CC BY 4.0).
- **Code** (everything under `lean/`, including its Markdown documentation; everything under `paper/anc/`, including
  its `README.md`; the build scripts `paper/build.sh` and `paper/make-arxiv-bundle.sh`; and the CI workflow in
  `.github/`): [Apache License 2.0](LICENSE).

The Lean dependencies downloaded by the build, Mathlib and `zeta23` from
[`anthropics/formal-math`](https://github.com/anthropics/formal-math), are Apache-2.0 and are not included here.

