> **Note on the current state.** Since this review, the 10 unproved results of the `Families` library were converted
> from `sorry` placeholders to `Prop` definitions, so the audit now reports zero `sorry`; the script
> `scripts/audit_hybrid.sh` was merged into `lean/scripts/audit.sh`, which checks both headlines.

> **Cleaned copy of an internal review record: internal file paths and identifiers removed; content otherwise unchanged.**
> Notes on this copy:
> - This is the review of the proposal to merge the polynomial-height extension (then a standalone draft, "Theorem H")
>   into the paper as §9 and Theorem 1.4. It was carried out by Claude (four sub-agents); it is **not** a
>   cross-model review.
> - Branch names, commit identifiers, the review date and the author's name have been
>   removed. "The merge proposal", "the reviewer guide" (with its §5a checklist and its items D1–D14), `STATUS.md`
>   and the "reframe draft" are internal documents and are not included. R1–R3 are the three referee reports on the
>   standalone draft, summarised in record 07. The internal statement audit mentioned here is record 06.
> - The section "Other tracks (limits note, barrier, obstruction map)" concerned separate internal work that is not
>   part of this repository; it has been replaced by a one-line note.
> - `audit_hybrid.sh` was the audit script of the standalone Lean package; it has since been merged into
>   `lean/scripts/audit.sh`.

# Independent review of the Theorem H merge proposal

**Reviewer:** Claude, using four independent sub-agents. The internal statement audit (record 06) landed during the review. The
sub-agents did not read the internal referee reports (R1–R3) or `STATUS.md` until they had formed their own view.
They made no changes to the branch.

**Outcome.** The author approved the merge (option B), to be applied with the fixes below.

## Summary

| Task | Verdict |
|---|---|
| (A) Mathematics of §9: Thm 1.4(a)–(c), Cor. 1.5, Prop. 9.30 | **No fatal errors.** Every new inequality was re-derived. Six cosmetic items. |
| (B) Faithfulness of the port, and the proposal's claims | **Faithful.** Builds, the numbering check (153/153) and all certificates reproduce bit for bit. Literature and overclaim fixes are needed. |
| (C) Lean statement faithfulness of `thmH_Statement` | **Faithful** on all eight items of guide §5a. Independent rebuild; `AUDIT-H PASSED`. Two weaknesses in the audit script. |
| Other tracks (limits note, barrier, obstruction map) | The mathematics holds and the certificates reproduce. Novelty and positioning are overclaimed. |

## (A) Mathematics (hostile referee, own derivation first)

**Confidence that the written proofs are correct, given families §§2–8:**

| Result | Confidence |
|---|---|
| Thm 1.4(a) | ≈ 93% |
| Thm 1.4(b) | ≈ 94% |
| Thm 1.4(c) | ≈ 95% |
| Cor. 1.5 | ≈ 95% |
| Prop. 9.30 | ≈ 98% |

The residual risk is the families §6.2 lemmas, which were not re-derived.

**Checked in full:**
- Prop. 9.18 Step 4: the chain and seminorms, the factor 4(1+ϰ⁻¹), high and low levels, and the cost
  η⁻²Q^{−3ε₁/8}, uniform in T.
- Lemma 9.13, with its constants.
- Lemma 9.15.
- The zero side: Lemmas 9.2–9.3, Props. 9.5–9.9, Rem. 9.8.
- The written arguments where Lean took another route: Prop. 9.6, Lemma 9.10(b), and the assembly.
- Order of limits: ε₅ is chosen after ε, η₀ is independent of a₀ and κ₁, and the κ-cells hold.
- (S1)–(S4).

**Grep of the families text for upper bounds on T and for Y ≤ Q².** Every hit is either redone in §9, true verbatim
at height T, or commentary. **No silent gap.**

**Cosmetic items:**
1. Rem. 9.16(1) omits the factor (1+ϰ_loc⁻¹); the term is still o(1).
2. Cor. 9.27 needs ϰ = min(√E, 1).
3. Lemma 9.11's exponent is conservative.
4. Thm 1.4(c) also uses Lemma 6.1.
5. Families Rems. 5.3 and 5.8 should point to Lemma 9.13 and Cor. 9.14.
6. The §9.1 list should include (5.4), (5.7) and (5.13).

R1–R3's earlier findings (the ε₅/ε order, 24/π, η ≤ 0.0146, and others) are correctly resolved.

## (B) The port, the claims, the certificates and priority

**Port faithfulness.**
- Every families change is on MERGE-PROPOSAL §3; §§2–7 are untouched.
- A sequence check of all printed item numbers confirms 153/153 unchanged.
- All 48 displays and all 60+ environments of the standalone draft correspond to §9, with no constant or hypothesis
  changed.
- D1–D6 and D9 are accurate. D8 is stale: README-H was already fixed.
- New items:
  - D7 is missing from guide §9.
  - D10: `paper/lemmas/polyheight.tex:593` (reviewed version) cites Cor. 1.5 for "every polynomial height"; it should cite Thm 1.4(c).
  - D11: there are 39 cells, not 40.
  - D12: `certify_hybrid.py` prints its 9-digit value rounded, not floored.
  - D13: the AI-use statement says the referees reviewed "a draft of §9"; they reviewed the standalone draft.
  - D14: Yil91 was known only as quoted in another paper.

**Builds and certificates.**
- The paper is 73 pp, with 0 errors, 0 undefined references and 0 overfull boxes.
- `check_numbering.sh --pre554`: all checks pass.
- All five certificate commands reproduce their logs bit for bit, on numpy 2.2.6 and scipy 1.15.3.
- The evaluator implements Γ_m with G″ = F_C. The printed values are true floors.
- The κ-table (8 × 5) and Cor. 1.5 match digit for digit.
- The Lean `certH` step functions are identical to the script's n = 400 step functions.

**Overclaims.**
- "> 99%" is confidence in the *Lean statement*, not in the written §9 proof: R3 gave 82%, this review ≈ 93%.
- The "Given FAM" cell for 1.4(a) should read 96% (R3).

**Priority sweep** (math.NT/new 28 Sep; pastweek 22–28 Sep; OpenAlex). No pre-emption, but:
- **Missing prior work.** Dickinson, arXiv:2211.06264: ≥ 38.2% of zeros simple and critical for Dirichlet
  L-functions mod q at T ≫ q^ε, unconditionally. This is a polynomial-height result below 2/3, so the novelty claim
  survives, but the "closest statement is HY26b" sentence is wrong without it.
- HY26b covers every **sub-polynomial** height, not only polylog heights.
- HY26b at θ = ½ is 0.279, not 0.280.
- CKLT26 gives ≈ 36.6% with Conrey's modification.
- Optional: Yıldırım 1991 and Özlük 1990 as conditional hybrid precedents.

## (C) The Lean statement (independent rebuild)

**Build and audits.**
- The families build was a no-op. `FamiliesH` built in 3 min 38 s on 8 cores.
- `audit.sh`: AUDIT PASSED. `audit_hybrid.sh`: AUDIT-H PASSED (567 declarations, 0 `sorry` roots, 51 baseline
  lines).
- Headline: `Families.Hybrid.thmH : thmH_Statement`, with axioms `[propext, Classical.choice, Quot.sound]`.

**Guide §5a, item by item:**
1. **Family and weights:** faithful.
2. **Counts:** faithful.
3. **Heights:** faithful; `betaK (kappaT Q T) = log(Q²T)/log(QT)` was proved.
4. **Support and constant:** faithful. The admissible class is nonempty and bounded below; the junk value 2 only
   makes the claim harder.
5. **Quantifiers:** faithful, and literally ∀ε ∃η₀ ∀a₀ κ₁ ∀η ∀W.
6. **liminf form:** faithful. It is equivalent, with N > 0 eventually and uniformly (proved). The N_d bound is
   stronger by ε/2, the same convention as the families theorem.
7. **Table constants:** faithful. The `betaK` values are proved, and the constants match column (a).
8. **`BandLSH`:** faithful. It is discharged from the proved large sieve, not assumed.

Parsing and vacuity checks are clean. `thmMain_of_thmH` compiles and uses only the standard axioms. Seven scratch
sanity lemmas were proved, including a concrete non-vacuous case at T = Q².

**Audit-script weaknesses:**
- **F1.** The "families untouched" check was relative to HEAD.
- **F2.** The headline was pinned by name only, not by content.

Both are fixed in the consolidation that produced the single Lean project in `lean/`. There was also documentation lag in STATEMENTS-H
note 5 (n = 800) and in its numbering.

The agreement with the internal statement audit (record 06) is complete; there are no contradictions.

## Other tracks

[This section reviewed separate internal work (a "limits" note, a barrier analysis and an obstruction map) that is not part of this repository. Omitted.]

## Merge versus a companion paper

Both options are defensible. The reviewers raised a third option: a same-day companion paper. The author chose to merge,
because the polynomial-height statement is the more natural and quotable result, and it answers the "polylog is thin"
objection.

**Conditions before merging:**
- the literature fixes: Dickinson, HY26b sub-polynomial, 0.279, 36.6%;
- D13;
- qualifying the > 99% confidence;
- the statement audit, now done;
- the audit fixes F1 and F2.

**Optional reframing.** Consider leading with the uniform-in-height theorem. There is an internal draft of such a reframing.
