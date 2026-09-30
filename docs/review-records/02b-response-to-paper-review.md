# Response to the independent paper review (summary)

> **Summary of an internal record** (the point-by-point response of the authoring agents (Claude) to review record 02), prepared for this
> repository. It is a condensed summary, not a verbatim copy: internal paths, branch names, file line numbers of
> the internal version and build details have been omitted. Record 02 is by Astra (the reviewer's self-name), a
> frontier AI model from a different developer (not Claude); Claude produced the paper and the formalisation.

**Overall.** All six findings in the manuscript were accepted and repaired. Each repaired step was re-derived by
the authoring agents (Claude), and a separate hostile checker then re-derived all six repairs from the edited source;
it found no mathematical problem and two wording nits, both applied. **No theorem statement and no certified number
changed.**

## 1. The six findings

| # | Finding (see record 02) | Disposition | Repair | Effect on theorem statements |
|---|---|---|---|---|
| 1 | Lattice-sum claim in the envelope lemma (now Lemma 2.3) false for exponent A ≤ 1/2 | Accepted | The second claim is restricted to A > 1/2 and given a full proof. Every use needs A > 1/2 (A = 2, A > 3, A > 5/2, A = 3 at its four uses). The old conclusion was in fact true for all A ≥ 0; only its one-line proof was wrong. | None |
| 2 | Factor ‖w̃‖∞ missing in the far-field bound of the fixed-η proposition (now Prop. 6.23(b)) | Accepted | Factor restored in statement and proof. ‖w̃‖∞ = 1 for both weights used, and the interval-arithmetic script `ctplus_arb.py` already implemented the bound with ‖w̃‖∞ = 1. | None; no certified number changes |
| 3 | Band device, Step 4: "both splits use κ = κ_T" | Accepted | κ_T for the first split, κ = 1 for the residuals; the displayed bound now follows exactly. | None |
| 4 | Introduction allowed a degenerate weight | Accepted | The introduction and the Lemma A section now require ∫u w(u) du > 0 (Definition 2.1, "admissible"). | None |
| 5 | Description of the local density in Lemma B2 | Accepted | Sentence rephrased as the weighted block majorant; the inequality is unchanged. | None |
| 6 | Dependency lists of the flattening constants | Accepted | Cut-offs and partition bounds listed as fixed data (§2.3). | None |

## 2. Superseded development notes

The internal development notes that preceded the paper (and that the review found to contain an invalid Bochner
shortcut, a positivity claim that fails for the smooth weight, an invalid phase-conjugation step, an over-stated
numerical claim, and stale dependency descriptions) were each given a prominent notice stating that they are
historical, that the paper is authoritative, and that their labels such as "PROVED" or "truth" and any confidence
percentages are not evidence. These notes are not part of this repository.

**The 0.9430 figure.** Older notes stated a distinct-zero bound 0.9430 − ε for the Gauss route. The certificate
gives (1 + 0.885912)/2 = 0.942956, so 0.9430 was rounded upwards and is withdrawn. The paper states 0.9429
(Theorem 1.2).

## 3. Comparison with previous large-sieve work

The authors read the primary sources suggested by the review (Baier 2006; Wolke 1971 via its review and Baier's
account; Ramaré's 2009 lecture notes; Ramaré's two 2026 preprints; Vaughan 2003). **Main finding: the rough-support
Toeplitz identity is not new.** With the weights G_q(Q) it is exactly the Bombieri–Davenport/Ramaré identity; the
paper's lemma is its weighted, signed form. The paper gained a new §1.3, "Relation to previous large-sieve work",
which lists as *not new* the Toeplitz identity, duality and the Schur test, rational approximation and spoke
counting, the Gauss transfer and Λ_R, and claims as new only (i) the explicit profile, the positive all-vector
Toeplitz majorant and its constant tending to 1, and (ii) the rough-to-flattened transfer. It closes: "Our literature
search was targeted rather than exhaustive, and we claim no priority beyond it." Wolke, Baier, Bombieri–Davenport and
Ramaré's second 2026 preprint were added to the bibliography, and "a new large sieve inequality" was reworded.

## 4. Sieve-centred presentation

Deferred to the author; not applied. The zero-counting application was kept.

## 5. Numerical certificates, Lean components and the unformalised theorem

At the time of the review the Lean headline depended on `sorry`, and the paper's scope section and Appendix A.4 were
rewritten to say so explicitly. This was later superseded: Theorem 1.1 was fully formalised (no hypotheses, standard
axioms only), and the verification statements were rewritten again (see record 01 and `docs/VERIFICATION.md`).
