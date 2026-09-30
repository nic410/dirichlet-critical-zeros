# Review records

Cleaned copies of the most important review and audit reports produced while the paper and its formalisation were
being developed. Each file starts with a note saying what was removed (internal file paths, repository and commit
identifiers, dates, agents' handles, and the author's name) and what, if anything, was condensed.
Otherwise the substance, verdicts and findings are as in the originals.

**Who the reviewers were.** The paper and the formalisation were produced by instances of Anthropic's Claude.
Records 01 and 02 are by **OpenAI's Astra**; they are the only checks by a model other than Claude. All other records are by separate Claude agents instructed to act as independent, hostile
reviewers. **None of the reviewers is a human mathematician.**

**Versions.** The paper grew during review. Several records were written about earlier versions (for example 45 or
53 pages, before §9 was added, or while parts of the Lean project were still unproved). Each record's header says
which version it concerns. Line numbers inside the records refer to the version reviewed, not to the files in this
repository.

| # | Record | Reviewer | Object | Verdict in one line |
|---|---|---|---|---|
| 01 | [`01-statement-audit-theorem-1.1.md`](01-statement-audit-theorem-1.1.md) | Astra | Faithfulness of the Lean statement `Families.thmMain_Statement` to Theorem 1.1; rebuild and axiom audit | FAITHFUL, with a harmless strengthening (ε/2 in the distinct-zero bound); no vacuity or hidden restriction found |
| 02 | [`02-independent-paper-review.md`](02-independent-paper-review.md) | Astra | The paper (53-page version, before §9), numerics, Lean status, novelty | No fatal error or unresolved load-bearing gap; six minor corrections; a "potentially publishable specialist result", not a field-wide breakthrough; specialist review of the sharp sieve recommended |
| 02b | [`02b-response-to-paper-review.md`](02b-response-to-paper-review.md) | the authoring agents (Claude) | Response to 02 | All six corrections accepted; no theorem or certified number changed; novelty narrowed (Toeplitz identity is classical) |
| 03 | [`03-review-of-section-9.md`](03-review-of-section-9.md) | Claude (four sub-agents) | §9 / Theorem 1.4 merge: mathematics, port, Lean statement, priority | No fatal errors; statement FAITHFUL; missing prior work (Dickinson) and several over-claims to fix before merging |
| 04 | [`04-post-merge-crosscheck.md`](04-post-merge-crosscheck.md) | Claude | The paper and the Lean project after the merge; fixes applied | No mathematical errors; two literally false sentences about Hua–Yang at small heights fixed; a latent gap in the audit's `sorry` scan found and closed |
| 05 | [`05-literature-check.md`](05-literature-check.md) | Claude | Competing papers for Theorems 1.1–1.3 | Not pre-empted (targeted search); two references to add |
| 06 | [`06-statement-audit-theorem-1.4a.md`](06-statement-audit-theorem-1.4a.md) | Claude | Faithfulness of `Families.Hybrid.thmH_Statement` to Theorem 1.4(a) | FAITHFUL; harmless ε/2 strengthening; covers κ = 1, 2, 3, 5, 10 of column (a) only |
| 07 | [`07-referee-reports-on-section-9-draft.md`](07-referee-reports-on-section-9-draft.md) | Claude (three referees) | The standalone draft of §9 and its two ports | No error invalidating the theorems; an order-of-limits slip, a false numerical threshold and a wrong constant, all repaired |
| 08 | [`08-internal-referee-report.md`](08-internal-referee-report.md) | Claude (lead + four section referees) | The paper (45-page version, before §9) | No mathematical error found; three editorial major issues; list of what a human specialist must check |

**Files referenced but not included.** The records refer to supporting material that is not in this repository:
the reviewers' scripts, logs and evidence bundles, internal working notes and development records, audit briefs,
and earlier versions of the paper. Where a record links to such material, the link has been replaced by a note.
Files that do exist here are referred to by their path in this repository (`paper/…`, `lean/…`).

**Current state versus the records.** Some records describe states that have since changed. In particular: at the
time of records 01, 04 and 08, the Lean project contained `sorry` declarations off the headline chain (and at the
time of record 02 the headline itself depended on `sorry`). In this repository the Lean project contains no `sorry`
at all; the results that are not formally proved (Theorems 1.2, 1.3, the conditional theorem, Lemma A and a few
lemmas) are present only as `Prop` definitions marked "Stated only; not proved in this project". See `../VERIFICATION.md` for the current
state.
