# Verification: what was checked, how, and what was not

This document lists every kind of evidence behind the paper's claims, how to reproduce the machine checks, what each
independent review found (including errors that were found and corrected), and the limitations that remain.

**The most important limitation first.** The paper, its proofs, the certificate scripts and the Lean formalisation
were produced by AI agents (instances of Anthropic's Claude). All checking so far has been done by machines and by AI
reviewers. **No human mathematician has yet checked the proofs line by line.**

Paper references are to `paper/main.pdf` (74 pages). Review records are in `review-records/` and are cited as
"record 01" etc.

## 1. Claims and evidence

| Claim | Lean (kernel-checked) | Certified numerics | Written proof | Independent review | Status |
|---|---|---|---|---|---|
| **Theorem 1.1**: weighted proportion of simple zeros on the line ≥ p(1) − ε ≥ 0.9322 − ε; distinct zeros ≥ 0.9661 − ε (polylogarithmic height) | **Yes**: `Families.thmMain`, no hypotheses, standard axioms only; the bound p(1) ≥ 0.932282 is evaluated by the kernel | `paper/anc/certify.py` (exact rational) | §§2–7, App. B | Statement audit by OpenAI's Astra (record 01); paper review by the same model (record 02, before Lean completion); Claude referees (record 08) | Formally proved. Statement faithfulness audited by AI (a model other than Claude), not by a human. Written proof not yet checked by a human |
| **Theorem 1.2**: ≥ 0.8859 − ε by the Gauss-transfer route; distinct ≥ 0.9429 − ε | No (stated as a `Prop` only). Some ingredients are proved in Lean: the Gauss transfer (Lemma 6.7), p(1.2688) ≥ 0.885912, ℰ ≥ 0.47914 and hence C_G ≤ 1.2688 | `certify.py`, `certify_constants_arb.py` | §6.1, §7 | Records 02, 08 | Rests on the written proof and certified numerics |
| **Theorem 1.3**: fixed η; 0.9155 (η = 10⁻³), 0.9241 (η = 10⁻⁴); Gauss route 0.8744, 0.8802, 0.8827 | No (stated as a `Prop` only) | `ctplus_arb.py`, `rw_arb.py`, `certify_ctplus_arb.py` (interval arithmetic, Arb); independent re-implementation `xcheck_*.py` | Prop. 6.23, Lemma 6.11, §7 | Record 02 reran all nine interval computations; record 08 reran two | Rests on the written proofs and certified numerics |
| **Theorem 1.4(a)**: at polynomial height, ≥ p(λ̄_T; F₁) − ε, with column (a) of the κ-table (0.8656 at T ≤ Q, 0.7641 at T ≤ Q⁵, 0.7274 at T ≤ Q¹⁰) | **Yes**: `Families.Hybrid.thmH`, no hypotheses, standard axioms only; the five constants for κ = 1, 2, 3, 5, 10 are kernel-evaluated | `certify_hybrid.py` (exact rational) | §9 | Statement audits by Claude only (records 06, 03); §9 reviewed by Claude only (records 03, 04, 07) | Formally proved. Statement faithfulness audited by Claude only. Written proof not yet checked by a human |
| κ-table rows κ = 1/4, 1/2 (column (a)) | No | `certify_hybrid.py` | Prop. 9.24 | Records 03, 04 | Certified numerics; not in the Lean statement |
| **Theorem 1.4(b), (c)**, **Corollary 1.5** (dyadic family: 0.7224, 0.7203, 0.7102) | No (not stated in Lean) | `certify_hybrid.py`, `certify_dyadic.py`, `classical_constant_check.py` | §9 | Records 03, 07 (Claude only) | Rests on the written proofs and certified numerics |
| **Conditional theorem** (Theorem 5.16), **Lemma A** (Lemma 6.5), and a few lemmas used only on the Gauss route or at fixed η | No (stated as `Prop`s only) | – | §5, §6.1 | Records 02, 08 | Written proofs only; not used by either Lean headline |
| **Novelty / priority** | – | – | §1.2–1.3 | Literature checks in records 02, 03, 04, 05, 08 | Targeted, not exhaustive searches; no pre-emption found |

"Standard axioms" means `propext`, `Classical.choice` and `Quot.sound`, the usual foundations of Lean and Mathlib.

## 2. The Lean formalisation

### What the Lean kernel does and does not guarantee

- **It guarantees** that the Lean statements `Families.thmMain_Statement` and `Families.Hybrid.thmH_Statement` follow
  from Lean's three standard axioms, given the definitions in the project, in Mathlib and in the `zeta23` dependency
  (all pinned in `lean/lake-manifest.json`), and assuming the Lean kernel and toolchain (`v4.33.0-rc2`, a release
  candidate) are correct.
- **It does not guarantee** that those Lean statements say the same thing as the theorems printed in the paper. That
  correspondence is a matter of reading the definitions. It is set out definition by definition in
  `lean/STATEMENTS.md` and `lean/STATEMENTS-H.md`, and it was audited by AI reviewers: by OpenAI's Astra for Theorem 1.1 (record 01), and by Claude for Theorem 1.4(a) (records 06 and 03).
  Both audits compiled independent Lean lemmas checking parsing, non-vacuity (for example that N > 0 eventually,
  uniformly in T, and that the zero sets are finite) and the equivalence with the paper's liminf-of-ratios form.
  The non-vacuity checks now ship with the project: `lean/scripts/NonVacuity.lean`, compiled by
  `scripts/audit.sh`, proves with the three standard axioms only that N > 0 for all large Q, uniformly for T in the
  height range of each headline (`Nfam_pos_main`, `Nfam_pos_hybrid`); that each headline implies the paper's ratio
  statement with real division, N^s_0/N ≥ p − ε etc. for all Q ≥ Q₀ and all T in the range (`thmMain_ratio`,
  `thmMain_ratio_numeric`, `thmH_ratio`); that the height ranges are nonempty for large Q; and that both weights
  exist for every 0 < η < 1/2 (`weights_exist`). Both found the statements FAITHFUL,
  with one harmless difference: the Lean bound for distinct zeros has ε/2 where the paper has ε, which makes Lean
  slightly stronger. No human has audited either statement.
- **It says nothing** about Theorems 1.2, 1.3, 1.4(b), 1.4(c) or Corollary 1.5, which are not formally proved.

**Pinned meaning.** `lean/scripts/audit.sh` prints the type and body of the two headline statements and of the 31
project definitions they unfold to, and requires the output to equal `lean/scripts/Statements.baseline.txt`
exactly. So a later change to what the headlines mean (a constant, a quantifier, a definition) makes the audit
fail. A cross-check (record 04) confirmed with negative controls that a weakened constant which still builds is
caught by this pin, and that a docstring change is not.

### Commands

Requirements: [`elan`](https://github.com/leanprover/elan) (it installs the pinned toolchain), `git`, and about 9.5 GB
of disk for the dependencies, the Mathlib cache and the build.

```
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none   # if needed
cd lean
lake exe cache get          # download the Mathlib build cache (about 5 GB)
lake build                  # builds Families and FamiliesH; must end with "Build completed successfully"
scripts/audit.sh            # the audit of both headlines; must end with "AUDIT PASSED"
```

Do not run `lake update`: all dependencies are pinned. `scripts/audit.sh` pins itself to cores 0–3 with 4 threads by
default (set `CORES` and `LEAN_NUM_THREADS` to change this; the pinning is skipped where `taskset` is unavailable).

**Fresh-checkout test.** These three commands were run exactly as written in a fresh copy of this repository (no
`.lake/`, empty download cache) on x86_64 Linux, with the build limited to 8 cores: `lake exe cache get` cloned the
pinned dependencies and downloaded the Mathlib cache in about 2 minutes (109 s); `lake build` built the imported
`zeta23` modules from source and both libraries in about 12 minutes (728 s), with no `sorry` warning;
`scripts/audit.sh` scanned 2,488 declarations of `Families` and 567 of `FamiliesH`, checked the 17 non-vacuity
theorems, and printed `AUDIT PASSED` in about 35 seconds. The `.lake/` directory then took 9.4 GB. (Last run on
30 September 2026.) The continuous-integration workflow (`.github/workflows/lean.yml`) runs the same commands
on every push.

The audit checks that: the build is up to date with the sources; there is no `native_decide` and no `axiom`
declaration; no declaration of either library depends on `sorryAx` (there is no `sorry` in the project); both
headlines have no hypotheses, have types literally `thmMain_Statement` and `thmH_Statement`, and depend only on the
three standard axioms; the recorded `#print axioms` baselines are reproduced; the statement pin above matches; and
the 17 theorems of `scripts/NonVacuity.lean` compile and depend only on the three standard axioms. The expected last
three lines are:

```
thmMain, thmH: no hypotheses; axioms propext, Classical.choice, Quot.sound; statements match the pin
non-vacuity: N > 0 eventually (uniformly in T), ratio forms, nonempty height ranges, weights exist
AUDIT PASSED
```

(The exact intermediate lines are listed in `lean/README.md`.) To check the headlines directly:

```
cat > Check.lean <<'EOF'
import Families
import FamiliesH
#check @Families.thmMain
#check @Families.Hybrid.thmH
#print axioms Families.thmMain
#print axioms Families.Hybrid.thmH
EOF
lake env lean Check.lean
```

Expected output:

```
Families.thmMain : Families.thmMain_Statement
Families.Hybrid.thmH : Families.Hybrid.thmH_Statement
'Families.thmMain' depends on axioms: [propext, Classical.choice, Quot.sound]
'Families.Hybrid.thmH' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Independent rebuilds: Astra rebuilt all local modules of the `Families` library and reproduced the
headline check and axioms (record 01); Claude cross-checks rebuilt both libraries, including from a clean copy
(records 03, 04). Mathlib and `zeta23` were not rebuilt from source in those checks (their pinned build caches were
reused).

**How the formal proof relates to the written proof** (paper App. A.4, p. 66). It follows the written proof and
assumes none of its steps. Where it deviates it uses weaker inputs, for example the large sieve with a larger absolute
constant (in Lean the constant is 17/4), and a Montgomery-type zero-density estimate with a smaller exponent, proved in Lean only for heights up
to Q, which is the only range used. Classical inputs come from the `zeta23` dependency: Weil's explicit formula, zero
counting for Dirichlet L-functions, Stirling-type bounds, a prime number theorem with error term, and the rank–trace
linear algebra.

## 3. Certified numerics

Every numerical constant used in a proof is produced by a script in `paper/anc/`, whose output log is shipped next
to it. "CERTIFIED" there means exact rational arithmetic, or interval (ball) arithmetic with every truncation bounded
by a proved inequality; floating point is used only to *choose* test functions, never to prove a bound. Full
instructions, requirements (Python ≥ 3.10, numpy, scipy, `python-flint` ≥ 0.9, mpmath) and expected results are in
`paper/anc/README.md`.

**Quick checks** (from `paper/anc/`; each takes seconds to about two minutes on one core):

```
for n in 400 800 1600; do echo "== n=$n"; python3 certify.py $n; done > /tmp/certify.log
diff /tmp/certify.log certify.log                                   # p(1) >= 0.932282, p(1.2688) >= 0.885912, ...
OMP_NUM_THREADS=1 python3 certify_hybrid.py 400 | diff - certify_hybrid_n400_rerun.log    # κ-table
OMP_NUM_THREADS=1 python3 certify_dyadic.py 400 | diff - certify_hybrid_dyadic_n400.log   # Corollary 1.5
python3 classical_constant_check.py | diff - classical_constant_check.log                 # C_cl <= 4.175, 8/(3ℰ) <= 5.5657
python3 kappa_curve.py | diff - kappa_curve.log                                           # floating-point curve (not used in proofs)
python3 certify_tiers.py | diff - tiers.log                                               # §8.2 tiers (not used in proofs)
python3 certify_ctplus.py 400 130491/100000 120423/100000 115320/100000 123617/100000 109101/100000 104331/100000 | diff - certify_ctplus.log
python3 certify_constants_arb.py > /tmp/ca.log; tail -1 /tmp/ca.log                        # "SUMMARY: all 17 inequalities CERTIFIED ..."
python3 ctplus_arb.py lsmooth 10000 --out /tmp | grep SUMMARY                              # C_T^+ <= 1.043289188 (η = 10⁻⁴), Theorem 1.3(ii)
./run_ctplus_arb.sh                                                                        # all nine interval certificates, about 2 min on 6 cores
```

For the interval certificates, compare the `SUMMARY` lines and the certified bounds with the shipped logs; timings
(and occasionally ball radii) differ between runs, the certified digits should not.

**Reproduction for this document.** In a fresh copy of this repository, on x86_64 Linux with Python 3.10.12, numpy
2.2.6, scipy 1.15.3 and python-flint 0.9.0, the first seven commands above reproduced the shipped logs byte for
byte; `certify_constants_arb.py` reproduced its log exactly apart from timing stamps; `ctplus_arb.py lsmooth 10000`
reproduced the shipped `SUMMARY` line exactly apart from its timing stamp; and `certify_ctplus_arb.py` (which reads the
shipped JSON files) reproduced `certify_ctplus_arb.log` apart from its total-time line. This was last done on
30 September 2026, after the logs of `certify.py`, `certify_ctplus.py`, `certify_ctplus_arb.py`, `certify_tiers.py`,
`certify_dyadic.py` and `classical_constant_check.py` were regenerated with bounds printed rounded down (lower bounds)
or up (upper bounds) instead of to nearest (§5, item 14). The SHA-256 digests of the shipped logs that
were reproduced byte for byte are:

```
8a46c86c917a7d19b0e68b4f805e5ec68568204018ab20c401a2c362dea938a6  certify.log
51e0a5c04b98331f6dff06c8dd57b3cdcc986e7fb4c49df52b8d3e00458d82af  certify_hybrid_n400_rerun.log
f142beb3177c0cbd1146466e599f46a5d81c40f19660940d7e71da59105e3a5a  certify_hybrid_dyadic_n400.log
e3be6dd90ee6201b416edca3e7820bf5456cd855d0245b988a749213a0c5a8e6  classical_constant_check.log
a183f676377dfe466eec8d77ec4b5b90b4b1dcfd4122103322225c0b9ba0b8ba  kappa_curve.log
a424f62f97c3a10767ee6dea1b6c4f488bf5345a2770621b1ca9305cb72487ad  tiers.log
37c2299835b86993a9130d5eed333ffbe2b6971bb40a10a83f4c4f371bb9fe5d  certify_ctplus.log
```

With other numpy/scipy/BLAS versions the floating-point choice of step function can change the last printed digit;
the printed values then remain valid lower bounds, because only the exact rational evaluation is part of the proof.

**Independent reproductions recorded in the review records.** A second implementation of the rational certificates
written by Astra, sharing no code, reproduced all seven rows of Prop. 7.3; it also reran all
nine interval computations and all 17 arithmetic-constant inequalities (record 02). Claude referees reproduced
p(1) = 0.9322826 by an independent solver and the Montgomery–Taylor value 0.6725007 at bandwidth 1 (record 08); two
independent exact evaluators reproduced the κ-table step functions (records 04, 07). The maxima behind C_T⁺(w) are
reproduced to ten digits by the shipped independent implementation `xcheck_*.py`.

## 4. Summary of the independent reviews

Reviews by OpenAI's Astra are marked **[X]**; the others were by
separate Claude agents.

**Record 08: internal end-to-end referee** (Claude; 45-page version, before §9). Lead referee plus four section
referees; five independent readings. Verdict: no mathematical error found; "ready for arXiv after the three major
fixes, all editorial": author placeholders (resolved) and the human responsibility statement (now written); Theorem 1.3's
certification not visible in the text (the text cited double-precision scripts, and an argument used by the R_w
certificate was missing; both fixed); and an unsupported claim that a figure announced in Alpöge–Furman Remark 7.2
was not achieved, resting on uncertified numerics (now worded neutrally, §8.6). About 40 minor items. Its §8 lists
what a human specialist must check personally: Lemma C, Prop. 6.21 and the duality lemma; the swap in Prop. 6.24;
flattening B1/B2; the zero side, including reading Montgomery (1969) Theorem 1 in the source; Appendix B; global
sanity; the Alpöge–Furman remark; and priority.

**Record 02 [X]: independent paper review** (by Astra; 53-page version, before §9 and before the Lean
proof was complete). Verdict: "no fatal mathematical error or unresolved load-bearing gap in the current assembled
argument"; a "credible candidate for a publishable specialist advance", not a field-wide breakthrough or progress
towards RH; "calling it a fully machine-verified theorem would be incorrect" (true at that time). Six minor
corrections, including one literally false intermediate estimate (a lattice-sum bound claimed for exponents A ≥ 0
but false for A ≤ 1/2) and one omitted normalisation factor; none affected a theorem or a number. It found invalid
arguments and a rounded-up figure (0.9430) in superseded internal development notes, and asked for them to be marked
as such. It independently reproduced the rational certificates, all interval computations and the arithmetic
constants. It recommended focused specialist review of the sharp sieve and its application.
**Record 02b: response.** All six corrections accepted; no statement or certified number changed; the superseded
notes were marked; the novelty claim was narrowed (§1.3 added: the Toeplitz identity is the weighted form of the
Bombieri–Davenport/Ramaré identity and is not claimed as new).

**Record 01 [X]: statement audit of Theorem 1.1** (by Astra). Rebuilt all 135 local Lean modules,
reproduced `AUDIT PASSED` and the three-axiom headline, and compiled nineteen independent semantic lemmas. All five
audit questions (parsing, vacuity and default values, strength and uniformity, hidden restrictions, classical
inputs) answered FAITHFUL; the only difference is the harmless ε/2 strengthening. Minor finding: the audit script did
not itself assert the list of then-remaining `sorry` declarations (later fixed). Its framing: "accurate to call
Theorem 1.1 formally proved, but inaccurate to call the whole paper formally verified".

**Record 05: literature check** (Claude; Theorems 1.1–1.3, before §9). Theorems 1.1–1.3 and the sharp-large-sieve
contribution not pre-empted in the sources reachable (arXiv metadata harvest, OpenAlex, Zenodo, Semantic Scholar;
general web search was unavailable). Recommended adding Conrey–Kwan–Lin–Turnage-Butterbaugh and Wang's short-interval
paper (done). It did not find Dickinson (2024), which was added later (record 03).

**Record 07: three referees on the standalone draft of §9** (Claude). No error invalidating the theorems. Errors
found and repaired: the order of limits (ε₅ was fixed before ε; found independently by two referees); a false
numerical threshold (η ≤ 0.0147 should be η ≤ 0.0146 for the classical route); a result applied outside its stated
hypotheses (repair: the hypothesis was unnecessary); an unproved remark on the ceiling for Q-rough vectors (repaired);
a constant 8/π that should be 24/π. Confidence estimates for the written proofs ranged from about 82% (sharp route,
Theorem 1.4(a)) to 90% (classical route), 96–97% conditional on the rest of the paper being correct; certified
constants > 99.9%.

**Record 06: statement audit of Theorem 1.4(a)** (Claude). FAITHFUL on parsing, vacuity, strength and uniformity,
certificates and an internal component correction; 40 compiled semantic lemmas; seven plausible misreadings rejected
by negative controls. Coverage limits: only κ = 1, 2, 3, 5, 10 of column (a); Theorem 1.4(b), (c) and Corollary 1.5
not stated. An audit of this statement by a model other than Claude was recommended and has not been done.

**Record 03: review of the §9 merge** (Claude, four sub-agents). Mathematics: no fatal errors; every new inequality
re-derived; six cosmetic items; confidence about 93% for Theorem 1.4(a) given the rest of the paper (the §6.2 lemmas
were not re-derived). Lean statement: FAITHFUL on all eight checklist items, independent rebuild passed; two
weaknesses in the audit script (the headline pinned only by name; a check relative to the working copy), both fixed
by the statement pin. Priority: no pre-emption, but **missing prior work** (Dickinson 2024, 38.2% at polynomial
height) and several imprecise comparisons (Hua–Yang's range, 0.280 → 0.279, 36.6% for CKLT) to fix before merging;
an internal "> 99%" confidence figure had referred to the Lean statement, not the written §9 proof, and was qualified.

**Record 04: post-merge cross-check and fixes** (Claude). No mathematical errors. Two sentences in §1.2 were
literally false: Hua–Yang's bound at height T = q^θ exceeds 1/2 for θ < 0.23 and 2/3 for θ < 0.0085, so earlier text
saying no unconditional family bound above 2/3 was known at polynomial height needed an exception; fixed. A remark
said "at most 8·10⁻⁶" where the value is 8.08·10⁻⁶; fixed to 9·10⁻⁶. Lean: every claim confirmed; negative controls
showed the statement pin works, and exposed a latent gap in the `sorry` scan (a module reachable only from the second
library was not scanned), which was closed and re-tested.

## 5. Errors found and corrected along the way

Listed for candour; all are documented in the records cited. None changed Theorem 1.1's statement or constant.

1. **A Lean statement-parsing trap.** In Lean a binder such as `∫ x, f x + c` extends as far right as possible, so the
   `+ c` fell inside the integral. This made an earlier intermediate statement (`lemB2_Statement`) false. It was
   caught, fixed and pinned by an `rfl` check; it was not part of the headline statement (`lean/README.md`).
2. **An over-claimed 0.9430 withdrawn.** Development notes stated a distinct-zero bound 0.9430 − ε on the Gauss
   route; the certificate gives (1 + 0.885912)/2 = 0.942956, so the figure was rounded upwards. The paper states
   0.9429 (records 02, 02b).
3. **Invalid arguments in superseded notes** (a Bochner shortcut, a positivity claim that fails for the smooth
   weight, a phase-conjugation step). They had been replaced before the paper was assembled; the notes were marked as
   superseded (record 02).
4. **Six corrections to the paper** from Astra's review, including a false intermediate lattice bound and a
   dropped normalisation factor (records 02, 02b).
5. **Novelty narrowed.** An earlier description of "a new large sieve inequality" was withdrawn once the Toeplitz
   identity was recognised as classical (records 02, 02b; paper §1.3).
6. **A claim about another paper withdrawn.** An earlier version asserted that a figure announced in Alpöge–Furman
   Remark 7.2 was not achieved, on the basis of an uncertified floating-point computation, with internally
   inconsistent numbers; it is now worded neutrally and used in no proof (record 08; paper §8.6).
7. **Theorem 1.3's certification made explicit.** The text had cited double-precision scripts and lacked one argument
   used by the interval certificate; both fixed (record 08).
8. **§9 order of limits.** ε₅ had been fixed before ε; caught independently by two referees and repaired (records
   07, 03).
9. **§9 numerics and constants.** The threshold η ≤ 0.0147 was false (now 0.0146); 8/π should have been 24/π;
   9-decimal log values had been rounded to nearest rather than down (now floors; the 6-decimal values used in the
   paper were unaffected); "at most 8·10⁻⁶" corrected to 9·10⁻⁶ (records 07, 03, 04).
10. **Literature omission fixed.** Dickinson (2024), the closest unconditional result at polynomial height, was
    missing from the §9 draft and was added (record 03).
11. **Two literally false sentences** about Hua–Yang at small polynomial heights, fixed (record 04).
12. **Audit-script gaps closed.** The headline was pinned only by name (now also by content); the `sorry` scan missed
    a module reachable only through the second library (closed and tested with a negative control); the script did
    not assert its expected `sorry` list (fixed) (records 01, 03, 04).
13. **The GRH comparison corrected.** The paper had presented Sono's 0.9322 as the GRH benchmark for the low-lying
    statistic. Chirre, Gonçalves and de Laat (Adv. Math. 2020, Theorem 5 of arXiv:1810.08843v2) obtained 0.9350 under
    GRH for that statistic, with test functions that are not supported in [−2, 2]. The abstract, §1.1, Table 1, §1.3,
    §8.1, §8.7 and §8.8 now say so; Theorem 1.1's constant and statement are unchanged.
14. **Rounding in further certificate logs.** As in item 9, the 9-decimal values printed by `certify.py` and
    `certify_ctplus.py`, the values of `tiers.log`, and some printed ends of enclosures were rounded to nearest; they
    are now rounded down (lower bounds) or up (upper bounds), and the logs were regenerated. Every 6-decimal certified
    value in `certify*.log`, and every constant used in a proof, is unchanged. The two §8.2(a) values from
    `tiers.log`, which are used in no proof, were 10⁻⁶ too large and are now 0.788171 and 0.894085.
15. **Small corrections to the text.** The value of max_S(c_∅ − c_S) in the proof of Lemma 6.19 is 0.16722..., as in
    Table 4 and the interval log (the text had 0.16723...); the log power in Montgomery's zero-density theorem, which
    had been given as 13 without a check against the source, is now an unspecified absolute constant B₀ (any fixed
    power suffices, and the constant B₁ of Lemma 4.7 is adjusted accordingly); §8.2(b) explains why its 0.738236
    differs from the 0.738253 of the κ-table (300- and 400-cell step functions for the same constant); and App. A.4
    now states the Lean form of the N_d bound correctly.

## 6. Limitations

- **No human verification.** No human mathematician has checked the written proofs line by line, or audited the
  correspondence between the Lean statements and the paper. The author's verification and responsibility statement
  is in the paper's AI-use section.
- **Scope of the formal proof.** Only Theorem 1.1 and Theorem 1.4(a) (with five κ-table constants) are formally
  proved. Theorems 1.2, 1.3, 1.4(b), 1.4(c) and Corollary 1.5 rest on the written proofs and certified numerics only.
  It is accurate to call Theorems 1.1 and 1.4(a) formally proved; it is not accurate to call the whole paper formally
  verified.
- **Statement faithfulness is a matter of reading.** The kernel checks the Lean statements, not the printed theorems.
  The correspondence was audited by AI: by OpenAI's Astra for Theorem 1.1,
  and by Claude only for Theorem 1.4(a).
- **Trusted base.** The Lean kernel and toolchain (a release candidate, `v4.33.0-rc2`), Mathlib and `zeta23` at the
  pinned revisions, and the standard axioms. The reviews used cached dependency builds rather than rebuilding Mathlib
  and `zeta23` from source; the fresh-checkout test (§2) built `zeta23` from source but took Mathlib from its
  official build cache.
- **Correlated reviewers.** Most reviews were by Claude, the same model family that produced the work; only two
  (records 01 and 02) were by a model from another developer, and record 02 reviewed an earlier version without §9.
  The confidence percentages quoted in some records are the reviewers' own estimates, not measurements.
- **Nature of the result.** Weighted family averages only; nothing about individual L-functions; lower bounds only;
  93% reached only in the limit η → 0 (the proved rate needs log(1/η) ≥ 3.7·10⁴ for the smooth weight); the best
  value certified at a fixed η is 0.9241; no effective value of Q. Not a proof of, or a step on, RH or GRH for any
  individual function.
- **Literature.** All priority searches were targeted, not exhaustive; general web search was unavailable to one of
  them. The paper claims no priority beyond its searches (§1.3).
- **Development speed.** The work was produced and reviewed quickly, by coordinated agents; the review records show
  that errors were found at every stage and fixed. Further errors, especially in the parts not formally proved,
  cannot be excluded.
