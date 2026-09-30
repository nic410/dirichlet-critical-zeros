# Post-merge cross-check of §9 and the unified Lean project, and the fixes applied

> **Note on the current state.** Since this review, the 10 unproved results were converted from `sorry` placeholders
> to `Prop` definitions, so the audit now reports zero `sorry` (the "exactly the expected 10 sorry roots" check below
> became a check that there are none); the script `scripts/audit_hybrid.sh` was merged into `lean/scripts/audit.sh`.

> **Cleaned copy of an internal review record: internal file paths and identifiers removed; content otherwise unchanged
> apart from the condensation described below.**
> **Condensed.** This record combines three internal documents: (A) an independent cross-check of the paper after
> §9 was merged, (B) an independent cross-check of the merged Lean project, and (C) the list of fixes applied in
> response. Sections about the arXiv tarball, internal production documents and internal merge-proposal documents
> have been omitted, as has the full audit transcript in (B); the retained sections are verbatim apart from the
> removal of commit identifiers, branch names, temporary and internal paths, dates, and the author's name. Both
> cross-checks were carried out by Claude agents (the same model family as the authoring agents), so they are **not** cross-model checks. "Astra" (mentioned in (B)) is OpenAI's Astra,
> the reviewer that audited the Theorem 1.1 statement (record 01).
> At the time of these checks the Lean project still contained ten `sorry` declarations off the headline chain
> (Theorems 1.2, 1.3 and others; see record 01). In this repository those results are present only as `Prop`
> definitions marked "Stated only; not proved in this project", and the project contains no `sorry`; statements below about "the
> expected 10 sorry roots" describe the earlier state. At that time a copy of the Lean project was also shipped
> inside the paper's ancillary directory (`paper/anc/lean`); in this repository the Lean project is at `lean/`.

---

# Part A. Cross-check of the paper side of the merge

Line numbers refer to the paper sources as merged at the time of the check. Sections 1–4 and 6 of the original are
kept; §5 (tarball) and §7 (internal production documents) are omitted.

## Verdicts

| # | Item | Verdict |
|---|---|---|
| 1a | Dickinson (arXiv:2211.06264): description, locators, effect on novelty | **CONFIRMED.** The published-version theorem numbering was NOT VERIFIED (Wiley returns 403). |
| 1b | HY26b "sub-polynomial", 0.279, CKLT 36.58%, Yıldırım | The four fixes are **CONFIRMED**. **DISCREPANCY (minor):** two neighbouring sentences in §1.2 are contradicted by HY26b at small θ (see D1). There is also a wording nit on Yıldırım's range. |
| 1c | Math fixes: Rem 9.16(1), Cor 9.27, §9.1 list, Thm 1.4(c), Rems 5.3/5.8, §9.6 (D10) | **CONFIRMED.** Every changed statement was re-derived. There are small documentation nits. |
| 2 | Build, label map | **CONFIRMED.** 73 pp; 0 errors, 0 undefined references, 0 warnings, 0 overfull; 153/153 labels unchanged, plus a stronger check. |
| 3 | Numbers vs Lean; "9-digit values now true floors" | **CONFIRMED.** One **DISCREPANCY (trivial)**: the "at most 8·10⁻⁶" for n = 800 is actually 8.08·10⁻⁶ (see D2). |
| 4 | Verification statements vs Lean state | **CONFIRMED** |
| 5 | Tarball (preview and `--strict`) | **CONFIRMED.** A comment in `polyheight.tex:4` ships an internal path (nit). |
| 6 | Review record addressed | **CONFIRMED** for everything that concerns the paper. The unaddressed items are optional or proposal-side documents only (listed below). |


## 1. Content diff, proposal → merged

These are all the differences. Nothing else differs: `macros.tex`, `constants.tex`, `lemma-A.tex` and
`lemma-toeplitz-C.tex` are byte-identical to the proposal.

| where (merged) | change | source |
|---|---|---|
| `main.tex:140` | Thm 1.4(c) now also lists "the mass asymptotic of Lemma 6.1" (`lem:WH`) | review A4 |
| `main.tex:188` | new Table 1 row: Dickinson, primitive χ mod q, simple and on line, 0.382, no hypothesis | lit. |
| `main.tex:203` | caption note (b) reworded (HY26b: every sub-polynomial height); new note (e) for Dickinson | lit. |
| `main.tex:207` | §1.2 "Polynomial height" rewritten: Dickinson is called the closest polynomial-height result; HY26b sub-polynomial; 0.280 → 0.279; CKLT "about 1/3 or less (… 36.58%)"; sweep date 25 → 28 Sep | lit. |
| `main.tex:664` (Rem 5.3) and `lemma-B-majorant.tex:194` (Rem 5.8) | "(for Y > Q² see Lemma 9.13 and Corollary 9.14)" | review A5 |
| `main.tex:878` | AI-use statement: the referees read "the standalone draft from which §9 was ported" | D13 |
| `main.tex:922/924/926` | App. A.4: one Lean project `lean/` with two libraries; `lean/STATEMENTS-H.md`; `audit.sh` covers both headlines; "not stated in the Lean project" | Lean move |
| `polyheight.tex:4` | header comment (not rendered) | – |
| `polyheight.tex:45` | the §9.1 "used with changes" list adds (5.4), (5.7), (5.10), redone in Lemma 9.1(S3), Lemma 9.11 and (9.10) | review A6 |
| `polyheight.tex:337` | Rem 9.16(1): the tail after the factor 1 + ϰ_loc⁻¹ | review A1 |
| `polyheight.tex:543` | Cor 9.27 proof: ϰ = min(√E, 1), with the case E > 1 treated | review A2 |
| `polyheight.tex:591` | Yıldırım: "an average over all pairs of characters … as quoted in [KLM26]" | D14 |
| `polyheight.tex:594` | "more than 2/3 at every polynomial height" is now derived from Thm 1.4(c) | D10 |
| `refs.bib` | new `Dic24` and `KLM26`; `Yil91` comment | lit. |
| `anc/` | `certify_hybrid.py` prints true floors; logs regenerated; README sections; `anc/lean` refreshed | D12 |

### 1a. Dickinson

I read arXiv v1, the only version (11 Nov 2022). Crossref gives Mathematika 70 (2024), no. 1, e12239.
- In Thm 1.4, N₀(T,χ) counts the **simple** zeros with β = ½ and 0 < γ < T. N(T,q) and N₀(T,q) are averages over the
  primitive χ mod q.
- Cor 1.1 states liminf_{qT→∞} N₀/N ≥ 0.382, "for every integer q".
- The hypothesis is T ≫ q^ε (Thm 1.2 and §4). The method is Levinson's, with a twisted second moment that is uniform
  in q and t.

The paper's description in §1.2, note (e) and the Table 1 row is accurate, and the locators "Theorem 1.4, Corollary 1.1"
are right for v1. The result uses a different method and family (a single-modulus average, zeros up to T), and 0.382 is
below 2/3. So Theorem 1.4's claim of more than 2/3 at every polynomial height is **not** affected. `refs.bib` itself
discloses that the published numbering was not checked.

Wording nit: HY26b's reduced-bandwidth constant is larger than 0.382 for θ < 0.378 (0.486 at θ = ¼, as the next sentence
of the paper says). Dickinson's result is best described as "the only unconditional result we know that is uniform over
all polynomial heights", rather than "the closest".

### 1b. HY26b, CKLT and Yıldırım

- **HY26b.** Remark 2.4 says: "If T = q^{o(1)} and ℓ^s = o(T) … then λ_bw = 1 … If T = q^{θ+o(1)} … λ_bw = (1+θ)⁻¹".
  The §1.2 sentence reproduces this exactly.
  - My mpmath evaluation of 2 − 1/c*_{1/(1+θ)} gives 0.486267 at θ = ¼ and **0.279459** at θ = ½. The old "0.280" came
    from double rounding 0.2795.
  - The constant reaches zero at θ = 0.8175, so "nothing for θ ≳ 0.8" is acceptable.
- **CKLT, footnote 2 (p. 3).** "With Conrey's modification [Con83], the proportion improves slightly to 36.58%." It is
  attached to the GL₂ statement "at least 1/3 … matching the proportion obtained by Levinson". The paper's paraphrase is
  faithful.
- **Yıldırım.** KLM26 (Math. Ann. 394 (2026), no. 2, art. 43; arXiv v2), Theorem 1: under GRH,
  F⁺_q(x,T) ∼ φ(q)T log x/(2π) for 1 ≤ q ≤ √x/log³x and x/(q log x) ≤ T ≤ exp(x^{1/4}). "As quoted in KLM26 … up to
  bandwidth 1 in units of log(qT)" is correct for the upper end.
  - Nit: the range also requires x ≥ q² log⁶x, so it is empty unless T ≳ q log⁵q. For T = q^θ with θ < 1 the quoted
    theorem says nothing, and for θ ≥ 1 it covers only α ∈ [2/(1+θ), 1].
  - "In the corresponding range" therefore reads more broadly than the source. This is harmless, because the paragraph
    is labelled "(Heuristic; not used.)".

**D1: DISCREPANCY (minor) in `main.tex:207`.** Two claims ignore HY26b's own reduced-bandwidth constants at small θ.
The values are in [internal evidence file], and 0.6013 at θ = 0.1 is already in the paper's
`anc/kappa_curve.log`.
1. "the other unconditional results for Dirichlet families in Table 1 with a proportion above 1/2 … concern heights that
   are at most sub-polynomial". This is false: HY26b gives more than ½ at T = q^θ for every θ < 0.2326, for example
   0.601 at θ = 0.1.
2. "… no unconditional bound above 2/3 for a family of Dirichlet L-functions at height polynomial in the conductor".
   This is literally false: by Thm 2.2 and Rem 2.4, HY26b gives 0.6691 at T = q^{0.005} and more than 2/3 for every
   θ < 0.00849.

The novelty of Theorem 1.4 is unaffected: it gives more than 2/3 uniformly up to every fixed power (0.8656 for T ≤ Q).
An earlier internal priority note says HY26b "stays below 2/3" at polynomial height, and the review
did not catch this.

*Suggested fix.* After "…nothing for θ≳0.8" add "(it exceeds 1/2 for θ < 0.23 and 2/3 only for θ < 0.0085)". Replace
the two claims with "with a proportion above 1/2 concern sub-polynomial heights, or heights q^θ with θ < 0.23 in the
reduced-bandwidth form of [HY26b]" and "no unconditional bound above 2/3 … at heights T ≥ q^{0.01}". Alternatively, use
"uniformly up to a fixed power of the conductor".

Caption nit: "(b) … at every sub-polynomial height T = q^{o(1)} in [HY26b]" omits HY26b's condition (log q)^s = o(T),
which §1.2 does state.

### 1c. Mathematics, re-derived

- **Rem 9.16(1).** Lemma 9.15 with δ = T^{−1+ε₅}, ‖y‖² ≪ L² (9.10) and Y/(Q²T) ≤ (QT)^{−ε₁} (S1) gives
  O(log log Q·(T^{−ε₅} + (QT)^{−ε₁})).
  - Multiplying by 1 + ϰ_loc⁻¹ ≤ 2T^{ε₅/2} (S4) gives O(log log Q·(T^{−ε₅/2} + T^{ε₅/2}(QT)^{−ε₁})).
  - This is ≤ log ℓ·ℓ^{−a₀ε₅/2} + log log Q·Q^{−7ε₁/8}, which is o(1) uniformly. Correct.
- **Cor 9.27.**
  - δ = |J|^{−1+ε/2} ≤ ¼ and 9δY ≤ Q^{2−ε}|J|^{−ε/2}. The relative tail E is as stated.
  - For E ≤ 1: (1+√E)(C+ϑ′) + (1+E^{−½})c_wE = C + ϑ′ + O_w(√E), and √E ≪_{w,ε} |J|^{−ε/5}.
  - For E > 1: |J| is bounded, so the O(1) loss is absorbed. Correct.
  - Nit: the text says "O_w(1)", but the bound is O_{w,ε}(1). This is immaterial, because the loss is absorbed into
    O_{w,ε}.
- **§9.1 list.**
  - (5.4) = `eqB:Rj`: redone in (S3), where R_j ≤ N_j^{½−ε₃} uses N_j ≤ 2Y < (QT)².
  - (5.7) = `eqB:Mrat`: redone in Lemma 9.11. Σ|b_n| ≪ Q^{3+κ₁} gives Q^{2κ₁+7−A} with A = 2κ₁ + 8. The exponent is
    conservative, and correct.
  - (5.10) = `eqB:norms`: redone in (9.10).
  - The review's "(5.13)" does not exist as an equation: §5 has (5.1)–(5.11), and 5.13 is Proposition 5.13, already on
    the list. Using (5.10) is correct.
- **Thm 1.4(c).** LS(C_cl) comes from (9.1) together with H = ℰ(∫uw)Q²(1+o(1)), which is Lemma 6.1
  (`polyheight.tex:341,494`). The new wording is correct.
- **Rems 5.3 and 5.8.** They point to Lemma 9.13 and Cor 9.14, which is right for the localisation tails.
  - Optional: for Y > Q² the pointwise and M^ss uses are handled by Lemmas 9.3 and 9.10(c), which could be added to
    the pointer.
- **§9.6 (D10).** For w = 1_{[1/2,1]} (admissible with η < ½), C_cl = 8/(3ℰ). Lemma 9.21 gives
  p(λ̄_T; F_C) ≥ p(1; F_C), and F_C = F₁ on [0,1] gives p(1; F_C) = 0.6725…. So the "more than 2/3" claim is correct.

## 3. Numbers

**Lean.** `certH_Statement` (Statements.lean:239–241) proves 0.865673, 0.824355, 0.797213, 0.764149 and 0.727484 at
β = 3/2, 4/3, 5/4, 7/6, 12/11.
- The table's column (a) at κ = 1, 2, 3, 5, 10 prints exactly these values.
- The abstract prints 0.8656 and 0.7641, and Table 1 and note (d) print 0.8656 and 0.7641. All are ≤ the Lean values.
- The "(a), distinct" entries equal ⌊(1+p)/2⌋₆, so they are implied by the Lean N_d bound.
- No n = 800 values (0.865674, …) remain anywhere in the sources.

**Independent checks.**
- My own exact evaluator (piecewise integration of the cell-pair kernel, not second differences of G) confirms
  Q ≤ B/10⁶ for the five `msK*` lists in `CertData.lean`.
- `scripts/gen_hybrid_data.py` regenerates `CertData.lean` **byte-identically** from `anc/certify_hybrid.py`.

**Reruns.** Environment: numpy 2.5.3, scipy 1.18.1, core 0.
- `certify_hybrid.py 400` (4.2 s), `certify_hybrid.py 800` (34 s), `certify_dyadic.py 400`,
  `classical_constant_check.py` and `kappa_curve.py` all reproduce the shipped logs **byte for byte** (sha256 in an internal evidence file).
- The only differences between the proposal's logs and the merged logs are 9-decimal values lowered by exactly 10⁻⁹:
  45 (n = 400), 53 (n = 800) and 11 + 11 (dyadic). Nothing else changed.

**True floors.**
- Re-evaluating every step function with my evaluator gives 55/55 rationals identical to `exact_Q`.
- All 103 log lines (n = 400, n = 800, dyadic) print p and "distinct" as true 9-decimal and 6-decimal floors.
- All 39 printed κ-table cells match the logs.
- The 800 − 400 differences are ≤ 4.3·10⁻⁷ for (a) and ≤ 9.8·10⁻⁷ for (b).
- The classical constants (4.175 up to η ≤ 0.0146911; 8/(3ℰ) ≤ 5.5654652), the κ → ∞ values (0.6856, 0.6792), the
  ε₅ ≤ 2.6·10⁻⁴ figure and the log T ≥ 1.27·10⁵ threshold (after the table) all check out.

**D2: DISCREPANCY (trivial).** In column (c) at κ = 0, n = 800 exceeds n = 400 by **8.08·10⁻⁶**
(0.738261417 vs 0.738253340). Three places say "at most 8·10⁻⁶":
- `main.tex:169`
- `polyheight.tex:509`
- `anc/README.md:271`

The claim is true only for the 6-decimal certified values. These statements are not part of any proof. Fix: write
"at most 9·10⁻⁶", or "8·10⁻⁶ in the printed six decimals".

## 4. Verification statements

App. A.4, scope item (7) and the AI-use statement agree with each other and with the Lean sources:
- `thmMain` and `Families.Hybrid.thmH` are proved (the shipped audit log reports the standard axioms only and no sorry
  roots).
- `thmGauss`, `thmFixed` and `thmConditional` are stated as `sorry` (`Families/Main.lean:180,213`,
  `Headline.lean:176`).
- `FamiliesH` states no Gauss or classical route and no Cor 1.5; its `_Statement` definitions were checked.
- `thmH_Statement` includes `certH`.

The claims made are "Thm 1.4(a) formal; 1.4(b), (c), Cor 1.5, Thm 9.20 for general C and §9.5 not stated". The
`anc/lean` snapshot equals `../lean` apart from the two documented comment lines. Lean was not rebuilt, because cores
1–3 are busy.

## 6. Review record (`REVIEW.md`, record 03)

**Addressed and verified:**
- A1, A2, A4, A5, A6 (as (5.10)).
- A3, deliberately left as is; it is correct.
- D10, D12, D13, D14.
- Dickinson, HY26b sub-polynomial, 0.279, CKLT 36.6%.
- STATEMENTS-H note 5 (now n = 400) and its numbering.
- The reframe draft.

**Not addressed (none of these affect the paper's text):**
1. Optional: Yıldırım 1991 / Özlük 1990 as conditional hybrid precedents in §1.2. Özlük 1990 is not cited.
2. The "> 99%" qualification and the "Given FAM = 96%" cell. The internal merge-proposal documents
   are unchanged. REVIEW listed the qualification as a pre-merge condition; the paper itself states no confidences.
3. D11: an internal merge-proposal status file still says "All 40 cells" (there are 39). D7 concerns the reviewer guide only.
4. Other tracks (limits note, barrier, obstruction map): outside the families paper; not checked.


---

# Part B. Cross-check of the Lean side of the merge

Sections 1, 2 and 5 of the original (source-identity checks against pre-merge commits and the ancillary copy) and the
full audit transcript are omitted; the verdict table, §3, §4, §6 and §7 are kept.

## Verdict

| # | Item | Verdict |
|---|---|---|
| 1 | Audited `Families` sources, `lake-manifest.json`, `lean-toolchain` untouched | **CONFIRMED** |
| 2 | Changes to the FamiliesH sources | **CONFIRMED**: 11 of 52 files changed, all in comments/docstrings only; no statement, proof, import or namespace changed |
| 3 | Full build and `scripts/audit.sh`; axioms and types of both headlines; statement texts vs. pre-merge | **CONFIRMED**: AUDIT PASSED; both headlines `[propext, Classical.choice, Quot.sound]`; both statements identical to the pre-merge (audited) ones |
| 4 | Statement pin (`scripts/Statements.lean` + baseline) and negative controls | **CONFIRMED** for the pin: it covers every project declaration the two statements unfold to, and it is the only check that catches a change of meaning that still builds. The commit's negative controls are not recorded in the repo; I rebuilt them (7 controls). One **latent gap** in the `sorry` scans, not in the pin, is shown by NC-F (§4.4, F-a) |
| 5 | `paper/anc/lean` vs `lean/`; clean-copy build and audit | **CONFIRMED**: the only source differences are two comment-only, pre-existing, documented ones; the clean copy builds and gives AUDIT PASSED |
| 6 | Docs (README, README-H, STATEMENTS, STATEMENTS-H, STATUS) | **CONFIRMED** on every substantive claim (sorry-root counts, axioms, declaration counts, commands, expected outputs). **Minor DISCREPANCIES** (doc lag) D1–D5 in §6; none affects a Lean result |

**Overall.** No discrepancy affects any Lean statement, proof or audit result. The merge moved FamiliesH into the families
project without changing any statement or proof. Both headlines check against only the three standard axioms, and their
statements are byte-for-byte the pre-merge ones: I re-ran the pre-merge statement-audit printers against the merged build
and the outputs are identical. The unified audit passes in the worktree and in a clean copy of `anc/lean`. §7 lists the
recommended fixes; all are small, and the one for F-a is tested.


## 3. Build, audit, headlines

**Build.** `lake build` in the worktree (both default targets) gives `Build completed successfully (9001 jobs)` in 857 s
on 3 cores.
- 185 project modules were compiled: 133 in `Families` (including the root) and 52 in `FamiliesH`. The dependencies were
  reused and none was rebuilt.
- There are exactly **10** `declaration uses sorry` warnings, all in `Families`: `LemmaA` ×5, `LemmaC`, `PrimeSide`,
  `Main` ×2 and `Headline`. None is in `FamiliesH`, and there are no errors [internal evidence file].

**Audit.** `CORES=1-3 LEAN_NUM_THREADS=3 scripts/audit.sh` exits 0 with **AUDIT PASSED** in 28 s. The full output is
omitted in this copy (its final lines are as in `lean/README.md` at the time). Compared with the pre-merge logs:
- the `Audit.lean` section (65 lines) is **byte-identical** to the corresponding pre-merge log (internal);
- the `AuditH.lean` section (23 lines) is **byte-identical** to the corresponding pre-merge log (internal).

**Independent scratch check** [internal evidence file], run with `lake env lean`; output in [internal evidence file]:

```
Families.thmMain : Families.thmMain_Statement
Families.Hybrid.thmH : Families.Hybrid.thmH_Statement
'Families.thmMain' depends on axioms: [propext, Classical.choice, Quot.sound]
'Families.Hybrid.thmH' depends on axioms: [propext, Classical.choice, Quot.sound]
Families.thmMain: kind theorem; levelParams []; type == Expr.const Families.thmMain_Statement []: true
  Families.thmMain_Statement: kind def; type is Prop: true
Families.Hybrid.thmH: kind theorem; levelParams []; type == Expr.const Families.Hybrid.thmH_Statement []: true
  Families.Hybrid.thmH_Statement: kind def; type is Prop: true
[scan Families] constants incl. internal: 4396 (internal: 1898); axiom decls: #[]; non-standard axioms: 0 []
[scan Families] constants whose own value mentions sorryAx: 10: [Families.lemA, Families.lemHarm, Families.lemRwlog, Families.lemRwlog_numeric, Families.lemWH_ratio, Families.propCTfixed, Families.propTI, Families.thmConditional, Families.thmFixed, Families.thmGauss]
[scan Families] constants depending on sorryAx only transitively: 0
[scan FamiliesH] constants incl. internal: 958 (internal: 391); axiom decls: #[]; non-standard axioms: 0 []
[scan FamiliesH] constants whose own value mentions sorryAx: 0: []
[scan FamiliesH] constants depending on sorryAx only transitively: 0
```

My scan imports both libraries and includes internal, private and auxiliary names, which the project's scans skip
(`Name.isInternal`). It confirms exactly the 10 documented `Families` sorry roots and no `sorry` anywhere in
`FamiliesH`. The README's "To check the headlines directly" snippet reproduces its four expected lines exactly
[internal evidence file].

**The statement texts are unchanged from before the merge.**
- **`thmMain`.** I re-ran Astra's pre-merge evidence files (`PrintDefinitions`, `StatementSemantics`, `ZeroSemantics`; internal, see
  record 01) on the merged build, with the flags of its `run_lean.py`. All three outputs
  are **byte-identical** to `definitions.log` (135 lines), `statement-semantics.log` and `zero-semantics.log`.
  `definitions.log` includes `#print Families.thmMain_Statement` with coercions shown, and `pp.all` prints of `Ns0chi`
  and `ProportionsAtLeast`. In addition, all 77 lines of `PrintAxioms.baseline.txt` are reproduced, and the Lean block
  in README.md equals the source of `thmMain_Statement` (`Families/Main.lean`, a byte-identical file).
- **`thmH`.** I re-ran the pre-merge internal statement-audit evidence files (`PrintDefinitionsH`, `StatementSemanticsH`, `NegativeControlsH`, `ClosureH`, `Probe`,
  `AuxProofs`; internal, see record 06). All six outputs are **byte-identical** to their pre-merge logs. The only normalisation was the file
  path prefix of 14 warning lines in `aux-proofs.log` (the directory had moved). `FamiliesH/Main.lean` (where `thmH_Statement` lives) is byte-identical to the pre-merge file.


## 4. The statement pin

### 4.1 How it works

`scripts/Statements.lean` starts from 22 roots (the two statements and their building blocks) and computes a transitive
closure. It follows:
- the type and value of every `def` and `opaque`;
- the constructor types of every inductive or structure;
- constructors and recursors to their inductive.

The closure is restricted to declarations of `Families*` and `FamiliesH*` modules. Theorems are not followed, which is
sound by proof irrelevance. For each declaration it prints the kind, name, universe parameters, type and body (or
constructor types), with fixed pretty-printer options, plus a 64-bit structural hash (`Expr.hash`) of the type and body.
`audit.sh` requires the output to equal the 229-line `scripts/Statements.baseline.txt` exactly. The headline *theorems*
are pinned by name in `Audit.lean` and `AuditH.lean`, as an `Expr` equality `type == .const X_Statement []` (confirmed in
§3). The pin fixes what those names mean.

### 4.2 Does it pin every definition the statements unfold to? Yes, for project declarations

I computed an independent closure in `XCheck.lean`, starting from the two headline *theorems* instead of the root list
and following everything, including theorem types and constructor/recursor data.
- It reaches **34** project declarations: the **31** pinned ones plus 3 constructors (`Weight.mk`,
  `AdmissibleWindow.mk`, `AdmissibleWindowB.mk`), which the pin prints inside their structures. The name sets match
  exactly.
- The only other project constants it reaches are auto-generated `_proof_i` lemmas (side conditions of numerals), whose
  types mention only Mathlib.

What the pin does not cover:
- Mathlib and Zeta23 definitions. These are fixed by `lake-manifest.json`. I checked that the package checkouts equal
  the manifest and are unmodified. Lake's up-to-date check (0) also traces the imported dependency modules, but I did
  not test it with a modified dependency.
- Docstrings, by design.

### 4.3 Negative controls

The commit says "negative controls fail as intended", but I found no script or log for them in the repository. The
review record lists findings F1 and F2 without controls. The older statement-semantics controls
(`NegativeControlsH.lean`) still reproduce (§3). I therefore built my own controls in a scratch copy of the built project
(a scratch copy). Its `lake build --no-build` reported the copy up to date, and control NC0 passed.

| Control | Modification (scratch copy only) | Rebuild | Expected | Result |
|---|---|---|---|---|
| NC0 | none | none | PASS | **AUDIT PASSED** |
| NC-A | append a comment line to `FamiliesH/Headline.lean`, no rebuild | none | FAIL (stale build) | **AUDIT FAILED**. Only FAIL: "the build is not up to date" (`FamiliesH.Headline` out of date) |
| NC-B | `Statements.baseline.txt`: `0.727484` → `0.727485` | none | FAIL (pin) | **AUDIT FAILED**. Only FAIL: the pin (diff at baseline line 52) |
| NC-C | `certH_Statement`: `(0.727484 : ℝ)` → `(0.727480 : ℝ)`, a weaker claim; the proof still goes through by `linarith` | 48 FamiliesH modules, **build green** | FAIL only at the pin | **AUDIT FAILED**. The **only** FAIL is the pin (hash `4390364266799495465` → `17864837651610756098`). Up-to-date build, sorry roots, both axiom baselines and `thmH` type and axioms all passed. The pre-merge `audit_hybrid.sh` would have passed this change (review finding F2) |
| NC-D | restore the constant; change only `certH_Statement`'s docstring | 48 modules | PASS | **AUDIT PASSED** (docstrings are not pinned, as documented) |
| NC-G | new module `FamiliesH/XcheckNCG.lean` with `theorem … : (1:ℕ) = 2 := by sorry`, imported by the `FamiliesH` root | 2 modules | FAIL | **AUDIT FAILED**: "FamiliesH sorry roots remain" (1: `xcheck_nc_g`) |
| NC-F | new module `Families/XcheckNCF.lean` with the same `sorry` theorem, imported **only by the `FamiliesH` root** | 2 modules | FAIL (README: "it fails if any is added") | **AUDIT PASSED**: this is gap F-a |

The logs are in [internal evidence file],
`ncD-docstring.log`, `ncG-sorryH.log` and `ncF-scan-gap.log`.

### 4.4 Findings

- **F-a. Coverage gap in the `sorry` scans (latent, low severity; not in the pin).**
  - `Audit.lean` imports only the `Families` root and scans the `Families.*` modules of that environment. `AuditH.lean`
    scans only modules named `FamiliesH.*`.
  - A `Families.*` module that only the `FamiliesH` root imports is built by `lake build` and passes check (0), but
    neither scan sees it. In NC-F an 11th `sorry` declaration passes as "sorry roots: exactly the expected 10".
  - The headline guarantees are unaffected: any use by `thmMain` or `thmH` would appear in their axiom checks.
  - The gap is not exercised by the merged tree. Every `Families.*` module reachable from the `FamiliesH` root is also
    reachable from the `Families` root, and my combined scan finds exactly the 10 roots.
  - Fix (tested): §7, item 1.
- **F-b. The hash is brittle, but fails safe.** Elaborated values reuse cached auxiliary proofs that belong to other
  declarations.
  - For example, `certH_Statement` references `propZeroH_Statement._proof_2`, `lemRvMH_lower_Statement._proof_1` and
    `lemSizesH_Statement._proof_1/_proof_2` (side conditions of numerals, [internal evidence file]. None of these is
    pinned.
  - `Expr.hash` includes those names. Editing an *unpinned* component statement could therefore change a pinned hash
    without changing any meaning: a false alarm, never a false pass.
- **F-c. Two modules are unreachable (pre-existing, harmless).** `Families/Phase1/A/Axioms.lean` (a `#print axioms`
  helper) and `Families/Ported/Second/StatementCheck.lean` (`rfl` checks) are imported by neither root, so they are
  neither built nor scanned. They contain no `sorry` and no `axiom`, and they were untouched by the merge.


## 6. Documentation

| Claim | Where | Observed |
|---|---|---|
| `thmMain`, `thmH`: no hypotheses; types literally `…_Statement`; axioms `[propext, Classical.choice, Quot.sound]` | README, README-H, STATUS header, anc README | reproduced |
| `Families`: exactly the 10 listed `sorry` declarations, none used by a headline; `FamiliesH`: none | README, README-H, STATUS, anc README | reproduced (including internal names) |
| no `axiom` declarations, no `native_decide` | all | reproduced (textual check and `ofReduceBool` scan) |
| 2,498 / 567 declarations scanned | README, README-H, anc README | 2,498 / 567 |
| 77 baseline lines and 131 declarations (PrintAxioms); 51 lines and 51 declarations (PrintAxiomsH) | README, README-H | reproduced |
| 31 pinned declarations (named list) | README, STATEMENTS-H §6, anc README | 31, names match |
| 15 component theorems, 10 glue/check declarations including `thmMain_of_thmH` | README, README-H, STATEMENTS-H | reproduced |
| `lake build` builds both libraries; `scripts/audit.sh` ends with `AUDIT PASSED`; default 4 threads on cores 0-3, override with `CORES`/`LEAN_NUM_THREADS` | README, README-H, STATUS, anc README | as described |
| the "passing run ends with" excerpts; the direct-check snippet's expected output | README, README-H | match the actual output |
| the audit takes about 30 s | README | 28 s on 3 cores |
| about 39,000 lines in 135 files (`Families`); about 11,750 lines in 52 files (`FamiliesH`) | README, README-H, STATUS | 39,140 / 135; 11,752 / 52 |
| Zeta23 is imported only by `Families/**` (module list in the lakefile) | lakefile, README, README-H | reproduced |
| the paper prints the n = 400 constants | README-H, STATEMENTS-H note 5, `certH_Statement` docstring | `paper/main.tex` contains 0.865673 … 0.727484 and none of the n = 800 values |
| `gen_hybrid_data.py` regenerates `CertData.lean` byte-identically | README-H | **NOT VERIFIED**: numpy is unavailable and there is no network. The emitted header matches byte for byte |

**Discrepancies.** None affects a Lean result.

- **D1. STATUS.md contradicts README.md** (predates the merge). STATUS.md "Current state" still says
  "(a cross-model statement audit is pending)" (lines 17–18), and line 128 says "A cross-model statement audit
  (Astra) is still pending". README.md, the audit brief and README-H say the Astra cross-model audit was done
 , FAITHFUL). Both sentences were already there at [commit], after the Astra evidence commit [commit].
  The merge added a header to STATUS.md but left them unchanged.
- **D2. "It fails if any is added" is not true in the F-a case.** README.md ("What is not proved") and the `audit.sh`
  header both claim this about the `sorry` declarations. It is latent (§4.4).
- **D3. README-H's per-package line counts are slightly off.** V is now 1,470, because `CertData.lean` lost one comment
  line in the merge; README-H still says 1,471. Base is 1,255; README-H says 1,254, which was already off by one before
  the merge. The total of about 11,750 is right.
- **D4. README-H line 166 cites "`TS-NOTES.md` §2"** without the new directory prefix. Other references were
  updated. Cosmetic.
- **D5. The commit message says "negative controls fail as intended"**, but the controls are not recorded anywhere. I
  reproduced them independently (§4.3).

## 7. Recommended fixes

1. **Close F-a.** Add one line, `import FamiliesH`, to `scripts/Audit.lean` after `import Families`. I tested this in the
   scratch copy:
   - With the NC-F module present, the audit now fails: "sorry roots changed … got: … xcheck_nc_f"
     [internal evidence file].
   - Without it, the audit output is **identical** to the current one apart from the provenance line
     [internal evidence file], so no baseline changes. The `Families` scan filters by the module prefix `Families`,
     which does not match `FamiliesH.*`.
   - Alternatively, `audit.sh` could check that every built `Families.*` module is reachable from the `Families` root.
2. **STATUS.md (D1).** Replace the two "pending" sentences with a pointer to the Astra audit record (record 01)
   (FAITHFUL; `thmMain` only).
3. **README-H (D3, D4).** Change "V 1,471" to "1,470" and "base 1,254" to "1,255", and cite the internal notes file
   §2.
4. **Optional (D5).** Commit the negative controls as a script, for example the NC-A/B/C/D/G/F recipes of §4.3, so that
   the claim is reproducible.
5. **Optional (F-b).** Make the pin's hash insensitive to proofs, for example by erasing proof subterms or hashing their
   types. Alternatively, document that editing an unpinned component statement may require regenerating the baseline.


---

# Part C. Fixes applied after the two cross-checks

The inputs are the two independent cross-checks above:
- Part A: no mathematical errors, discrepancies D1–D3;
- Part B: everything confirmed, one latent audit gap (F-a), doc lag D1–D5.

There are no theorem-statement changes, no changes to any proof or Lean source file, and no renumbering. Evidence logs
are kept with the internal record.

### P1. §1.2 "Polynomial height" (`main.tex:207`) and the Table 1 caption (`main.tex:203`)

At height T = q^θ, HY26b's bound for the characters mod one prime q has bandwidth 1/(1+θ). That exceeds 1/2 for
θ < 0.2327 and 2/3 for θ < 0.0085, with 0.601 at θ = 0.1. These were recomputed independently:
0.6013, 0.4863 and 0.2795 at θ = 0.1, 1/4 and 1/2, with crossings at θ ≈ 0.0085 and 0.2327. Two sentences were
therefore literally false. The fixes:

| Where | Before | After |
|---|---|---|
| `main.tex:207`, first sentence | "… concern heights that are at most sub-polynomial in the conductor: \cite{HY26b} obtains …" | "… concern heights that are sub-polynomial in the conductor, except that the bound of \cite{HY26b} at height $T=q^\theta$ (see below) stays above $1/2$ for $\theta$ below about $0.23$, and above $2/3$ for $\theta$ below about $0.0085$: \cite{HY26b} obtains …" |
| `main.tex:207`, HY26b values | "which gives $0.486$ at $\theta=\frac14$, …" | "which gives $0.601$ at $\theta=0.1$, $0.486$ at $\theta=\frac14$, …" |
| `main.tex:207`, last sentence | "… no statement of Theorem 1.4, and no unconditional bound above $2/3$ for a family … at height polynomial in the conductor." | "… no statement of Theorem 1.4, and, apart from \cite{HY26b} at heights $T=q^\theta$ with $\theta$ below about $0.0085$, no unconditional bound above $2/3$ …" |
| `main.tex:203`, caption note (b) | "at every sub-polynomial height $T=q^{o(1)}$ in \cite{HY26b}" | "at every sub-polynomial height $T=q^{o(1)}$ with $(\log q)^s=o(T)$ for some fixed $s>1$ in \cite{HY26b}" (the paper-check caption nit) |

The same literal claim was searched for in the abstract, §1 (scope, "what is claimed"), `polyheight.tex` (§9 intro and
remarks), internal production documents, and was found nowhere else. An internal reframing draft's
"more than 2/3 at every polynomial height" is a claim about Theorem 1.4 and is true.

Novelty is unaffected: Theorem 1.4 gives more than 2/3 at every polynomial height (0.8656 for T ≤ Q).

### P2. The discretisation remark

In column (c) at κ = 0, n = 800 exceeds n = 400 by **8.08·10⁻⁶** (0.738261417 against 0.738253340; recomputed from
`anc/certify_hybrid_n800.log` and `anc/certify_hybrid_n400_rerun.log`). For columns (a) and (b) the gaps are
4.3·10⁻⁷ and 9.8·10⁻⁷. The fix changes "at most 8·10⁻⁶" to "at most 9·10⁻⁶" in:
- `main.tex:169` (column (c));
- `lemmas/polyheight.tex:509` (columns (a)–(c));
- `anc/README.md:271` (C = 4.175).

### Nits from the paper check

- `lemmas/polyheight.tex:4`: the header comment no longer names an internal path or branch. Comments are stripped by the
  lint but shipped in the arXiv source.
- `anc/README.md:231`, "What was left out of this snapshot": it now says `scripts/gen_hybrid_data.py` *is* shipped.
  Only the families generators `scripts/cert-gen/`, the internal working-notes directory and the development records are
  omitted. This was verified by comparing the file lists of `anc/lean` and `lean`. The line adds two lines, so the
  licence placeholder moves from `anc/README.md:311` to `:313`.

## Lean (`lean/` and the ancillary copy `paper/anc/lean/`)

### L1. Close gap F-a in the `sorry` scan

`scripts/Audit.lean` now also has `import FamiliesH`, with a 3-line comment explaining why. The change is identical in
both copies. Verification:
- **Normal audit** (internal logs): `AUDIT PASSED` before and after. The output is identical apart
  from the provenance digest, with the same 10 families sorry roots, 0 FamiliesH roots, both headlines on propext,
  Classical.choice and Quot.sound, and the pin unchanged.
- **Negative control NC-F** (scratch copy, removed afterwards): a new `Families/XfixNCF.lean` holds
  `theorem xfix_nc_f : (1 : Nat) = 2 := by sorry`, imported only by the `FamiliesH` root.
  - With the pre-fix `Audit.lean`: **AUDIT PASSED**, reporting "sorry roots: exactly the expected 10". This reproduces
    the gap ([internal log]).
  - With the fixed `Audit.lean`: **AUDIT FAILED**, "sorry roots changed (… got: … xfix_nc_f)"
    ([internal log]).
- **Shipped copy:** a clean copy of `anc/lean` (dependency packages symlinked, warm build cache) builds in 59 s and
  gives **AUDIT PASSED** (internal logs).

### L2. Documentation (identical edits in both copies)

**`STATUS.md`:**
- The "cross-model statement audit is pending" sentences (lines 17–18 and 128) now say that Astra's cross-model audit
  of `thmMain_Statement` found it FAITHFUL, with a pointer to the audit record (record 01).
- The header gains "Statement audits": `thmH_Statement` was found FAITHFUL by the internal Claude audit
  and by the independent review (also Claude). A non-Claude audit of `thmH_Statement` is still recommended.

**`README.md`:** "it fails if any is added" now explains that the `Families` scan imports both roots, so it also covers
a `Families.*` module reachable only through `FamiliesH`. The claim is true after L1, and the negative control confirms
it.

**`README-H.md`:**
- line counts corrected to base 1,255 and V 1,470 (recounted with `wc -l`; total 11,752 in 52 files);
- `TS-NOTES.md` → an internal notes file;
- "a non-Claude (cross-model) audit … is recommended".

**`scripts/audit.sh`:** the header comment for (2) records that the scan covers every built `Families.*` module. The
change is comment-only (`bash -n` ok).

### L3. The generator reproduces `CertData.lean`

`scripts/gen_hybrid_data.py`, run with the venv Python (numpy), regenerates `FamiliesH/V/CertData.lean`
**byte-identically**, from `lean/` and from `anc/lean/` (the latter via the anc lookup path; sha256 prefix
`539c1025b22d835e3539`). Log: [internal log].

## Not done (optional, or outside this pass)

- The optional Özlük (1990) and Yıldırım (1991) citations as conditional hybrid precedents in §1.2 (review item; not a
  correctness issue).
- Review item D7 (an entry missing from the reviewer guide's §9 list).
- Committing the negative controls as a script (Lean cross-check D5), and making the pin's hash insensitive to proofs
  (F-b). Both are optional.
- The review's "other tracks" items for the limits note, the barrier and the obstruction map. They are outside the
  families paper and are needed only before any posting of the limits note.

## Hostile self-review

- Every changed file was diffed line by line (`git diff`).
- The `anc/lean` copies of `README.md`, `README-H.md`, `STATUS.md`, `scripts/audit.sh` and `scripts/Audit.lean` are
  byte-identical to `lean/`.
- The Lean audit was re-run after the last edit (`AUDIT PASSED`).
- The tarball was rebuilt after the last change to a shipped file. [Tarball details omitted in this copy.]
