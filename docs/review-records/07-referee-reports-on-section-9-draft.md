# Referee reports on the standalone draft of §9 (condensed)

> **Cleaned copy of an internal review record: internal file paths and identifiers removed; content otherwise unchanged
> apart from the condensation described below.**
> **Condensed.** Before §9 was merged into the paper, the polynomial-height extension ("Theorem H") existed as a
> standalone 22-page draft and as two sets of working notes, a zero-side port and a prime-side port. Three
> independent hostile referees (all Claude; **not** cross-model) reviewed them; these are the R1–R3 of record 03.
> This copy keeps, verbatim, each report's summary and verdicts, its list of errors, and its confidence table; the
> long sections recording what each referee re-derived, and the referees' scripts and logs, are omitted (they are
> kept with the internal record).
> Glossary: "[FAM]" / "FAM26" is this paper (the version then current, before §9 was added). The standalone draft's
> numbering differs from the paper's: its Theorems 1.1, 1.2, 1.3 and Corollary 1.4 are the paper's Theorem 1.4(a),
> (b), (c) and Corollary 1.5; its Lemma 4.4 and Corollary 4.5 became Lemma 9.13 and Corollary 9.14; its §5 became
> §9.5. Upper-case names such as ASSEMBLY, INTERFACE, ZERO-SIDE, PRIME-SIDE, INTERFACE-PRIME, M3-HYBRID,
> SHARP-HYBRID-LS, THEOREM, PRIORITY, STATUS and BRIEF refer to sections of the internal working notes and referee
> brief (not included). Dates, times, file paths and model version strings have been removed. All errors listed
> here were repaired before the merge (record 03 confirms this); in particular E1 (the order of ε₅ and ε), M1 (the
> threshold η ≤ 0.0147, now η ≤ 0.0146) and the constant 8/π → 24/π.

(The labels R1, R2, R3 below are assigned in this copy for reference.)

---

## Report R1: the standalone draft

# Referee report: "Simple zeros of Dirichlet L-functions on the critical line at polynomial height, on weighted average"

Independent hostile referee (Claude).

**Manuscript.** The standalone draft (763 lines of TeX, with its bibliography, ancillary scripts and a 22-page PDF; internal).
- Line numbers below refer to `main.tex`.
- Printed numbers come from a local rebuild (0 LaTeX warnings). They are listed in an internal file, together with the FAM26
  numbers.

**Companion.** [FAM] = FAM26 = this paper (`paper/main.tex` with `lemmas/*.tex`, version before §9).
- Every "[FAM, X]" in the draft was looked up by its printed number, from a local rebuild of FAM26.

**Method.**
- I refereed the text as written. I read the two earlier referee reports (on the working notes) only to avoid duplicating them;
  none of their verdicts is relied on here.
- Labels:
  - **RE-DERIVED**: I redid the step myself.
  - **CERTIFIED**: exact or interval arithmetic that I reran.
  - **CITED**: a FAM26 item, checked only for its statement and hypotheses.

---

## (a) Summary and recommendation

**What the paper claims.** Take the weighted family of FAM26 and heights ℓ^{a0} ≤ T ≤ Q^{κ1}, with κ_T = log T/log Q and
β(κ) = (2+κ)/(1+κ).
- **Theorem 1.1** (sharp route, log-wide weights, η ≤ η0(ε)): N^s_0/N ≥ p(β(κ_T)) − ε.
- **Theorem 1.2** (Gauss route): N^s_0/N ≥ p(β(κ_T); F_{C_G R_w}).
- **Theorem 1.3** (classical route): N^s_0/N ≥ p(β(κ_T); F_{C_cl(w)}).
- **Corollary 1.4**: the dyadic family.

**Mechanism.** Three changes to FAM26:
- log(QT) replaces log Q throughout;
- the time localisation is at δ = T^{−1+ε5} instead of T^{−1/2};
- a new tail lemma (Lemma 4.4, dyadic shells plus the classical large sieve) replaces FAM's Λ_mult(Y) ≤ 2w_max Q², which fails
  once Y ≫ Q².

The zero side is FAM26's, with the pointwise bound weakened by (1+Y/Q²)^{1/2}. Everything else is used from FAM26 verbatim.

**Verdict.**
- **No error found that invalidates Theorems 1.1–1.3 or Corollary 1.4.**
  - I re-derived every new or modified inequality in §§2–6 (list in §(e)), including all of §3 and all of §4.5 (Prop. 4.9).
  - I checked every FAM26 citation against its printed statement and hypotheses. All are correct.
  - I grepped FAM26 for every use of T ≤ (log Q)^{A0} or Y ≤ Q². Each one is replaced in the port.
- **Certificates.** They reproduce bit-for-bit. An independent exact evaluator gives identical rationals, and an independent
  optimiser reproduces the table to within 3·10⁻⁶.
- **Errors found, all repairable in a line or two:**
  - one false numerical statement: the classical-route threshold η ≤ 0.0147 (M1);
  - one proof that invokes a theorem outside its stated hypotheses (Cor. 5.3; M2);
  - one remark whose justification fails near the threshold (the Q-rough ceiling; M3);
  - further inaccurate scope sentences, missing citations and notation clashes (§(c)).

**Recommendation: minor revision.** There are two editorial conditions.

1. **FAM26 must be publicly available first.** About twenty steps read "the proof of [FAM, X] applies verbatim". Theorem 1.1
   rests on FAM26 §6.2, and Theorem 1.2 on FAM26 §6.1. This paper cannot be refereed or read independently of FAM26.
2. **Consider publishing this as a section of FAM26.** The genuinely new mathematics is about four pages:
   - Lemma 2.1;
   - the §3 bookkeeping;
   - Lemma 4.4 and Corollary 4.5;
   - the parameter changes in Prop. 4.9;
   - §5.

   Its main idea, localising at T^{−1+ε}, is already anticipated as a heuristic in FAM26 §8.5.

---

## (b) Major issues: wrong or unproved as written

None of these changes Theorems 1.1–1.3 as stated in symbols. M1 changes the numerical range attached to one column of Table 1.

### M1. The classical-route threshold "η ≤ 0.0147" is false (lines 99, 740; Table 1 column 6, lines 111–112)

**Where.**
- Line 99: "For w = 1_{[η,1]} one has C_cl(w) = 2/(E(1−η²)) ≤ 4.175 for η ≤ 0.0147".
- Line 740 repeats it.
- Table 1's column "p(β;F_{4.175}) ≥ (Thm. 1.3, 1_{[η,1]})" relies on it.

**What fails.** At η = 0.0147, 2/(E(1−η²)) exceeds 4.175 for every E in FAM26's certified interval [0.47914533, 0.47914535]:

| E | C_cl at η = 0.0147 | Largest η with C_cl ≤ 4.175 |
|---|---|---|
| 0.47914533 | 4.17500109 | 0.0146911 |
| 0.4791453444 (true value) | 4.17500096 | 0.0146922 |
| 0.47914535 | 4.17500091 | 0.0146926 |

For η ∈ (0.014692, 0.0147] the C = 4.175 certificates therefore do not cover the classical route. The source is
the referee's script `constants_check.py` and its log (internal) (mpmath, 25 digits, both ends of the certified interval).

**How big.** By Lemma 6.2, p(β;F_{4.1750011}) ≥ (tabulated value) − 1.1·10⁻⁶.
- The six-decimal entries of column 6 can be off by one in the last digit for those η.
- The rounded claims 0.738 and 0.714 (abstract, line 740) survive.

**Repair.** Replace 0.0147 by 0.0146 at lines 99 and 740, and state the η range in the Table 1 caption. FAM26 §8.2(b) used
η ≤ 0.01, which is correct; 0.0147 looks like the threshold 0.01469 rounded *up*.

### M2. Corollary 5.3's proof applies Theorem 5.2 outside its hypotheses (lines 599, 611, 617)

**The mismatch.**
- Theorem 5.2 (line 599) assumes |J| ≥ 16 and δ ∈ [4/|J|, ¼].
- Corollary 5.3 claims uniformity for all |J| ≥ 16.
- Its proof (line 617) takes δ = |J|^{−1+ε/2}.

But |J|^{−1+ε/2} ≥ 4/|J| if and only if |J| ≥ 16^{1/ε}. For 16 ≤ |J| < 16^{1/ε} the hypothesis is violated; for example
ε = ½ and |J| < 256.

**Why the repair is safe.** I re-derived the proof of Theorem 5.2 (line 607).
- Neither δ ≥ 4/|J| nor |J| ≥ 16 is used.
- Only δ ≤ ¼ is used: it gives e^{2δ} ≤ e^{1/2} in the interval count, and it is the hypothesis of Lemma 4.4.

**Repair.**
- State Theorem 5.2 for every δ ∈ (0, ¼] and every bounded J.
- Keep |J| ≥ 16 in Corollary 5.3: for ε < 1 it gives δ = |J|^{−1+ε/2} ≤ 16^{−1/2} = ¼.

Neither result is used in Theorems 1.1–1.3.

### M3. The Q-rough version of the ceiling (line 649) is not proved as written

**The claim.** "restricting it to the Q-rough n in the progression, whose number is ≍ K/(q0 log Q) once K/q0 ≥ Q^C by the
fundamental lemma … so the same threshold holds for Q-rough vectors up to a factor log Q in N."

**What fails.** Near the threshold α ≈ β(κ_T), K/q0 ≍ N/(Q|J|) ≍ Q^{1+(1+κ_T)(α−β(κ_T))}. So K/q0 ≥ Q^C fails there.
- The fundamental lemma needs the sifting range s = log(K/q0)/log Q to be large.
- Even the linear-sieve lower bound needs s > 2, and here s ≈ 1.
- As written, the argument proves the Q-rough ceiling only for α ≥ β(κ_T) + (C−1)/(1+κ_T).

**Repair (elementary; RE-DERIVED).**
1. Any residue class a mod q0 works. On n ≡ a mod q0, χ(n) = χ(a) is constant, so |S_χ[y]| is unchanged.
2. Take y_n = n^{it0}·1[n prime, n ≡ a (mod q0)]·1_I(n).
3. Pigeonhole over the φ(q0) classes a, then over the ⌊N/K⌋ disjoint length-K blocks of [N, 2N]. This gives a and I with
   m ≥ (1+o(1))K/(φ(q0) log N) primes.
4. These primes exceed N > Q, so they are Q-rough.
5. The proof of Prop. 5.6 then gives the ratio ≫ q0Nm/(KQ²|J|) ≫ N/(Q²|J| log N).

So the threshold β(κ_T) holds even for prime-supported vectors, up to a factor log(QT) in N; the draft says log Q. This is not
used in any proof. It does back the "limit of the method" statements (lines 164, 649, 731) for the Q-rough vectors that the sharp
route actually sees.

---


## (d) Confidence per theorem

"Given FAM26" means conditional on the FAM26 statements cited being correct as printed.

| Result | Confidence | Given FAM26 | Main residual risk |
|---|---|---|---|
| Thm 1.3 (classical), with the M1 fix | **90%** | 97% | FAM26 §§2–5 items used verbatim that I read and checked for T- and Y-dependence but did not rebuild from scratch: App. B explicit formula, Prop. 3.3, Lemmas 5.5 and 5.7 steps (1)–(5), Lemma 4.7 |
| Cor 1.4 (dyadic) | **90%** | 97% | as Thm 1.3; the dyadic column is CERTIFIED |
| Thm 1.2 (Gauss) | **85%** | 97% | adds FAM26 Cor. 6.8 (Lemma A and the Gauss transfer), which is T-free and not re-derived |
| Thm 1.1 (sharp) | **82%** | 96% | adds FAM26 §6.2: Prop. 6.21 and Lemmas 6.13, 6.15, 6.17, 6.20, 6.22. I read the statements and the proofs of 6.13 and 6.17 only. The port of Prop. 6.24 (the draft's Prop. 4.9) I re-derived completely |
| Thm 5.2 / Cor 5.3 / Cor 5.4 | 88% / 88% (after M2) / 95% | — | Thm 5.2 and Cor 5.3 inherit FAM26 Prop. 6.21; the second statement of Cor 5.4 is self-contained (MVLS plus Lemma 4.4) |
| Prop 5.6 (ceiling, general vectors) | **98%** | — | none found |
| Ceiling for Q-rough vectors (line 649) | not proved as written | 95% with the M3 repair | — |
| Table 1 and Prop. 6.4 | **CERTIFIED** | — | column 6 needs η ≤ 0.0146 (M1) |

---


---

## Report R2: the prime-side port

# Referee report: the prime side of Theorem H (hybrid height)

Hostile referee (Claude).
- **Submission:** the prime-side port (working notes STATUS, PRIME-SIDE, SHARP-HYBRID-LS, INTERFACE-PRIME, and numerics).
- **Paper labels** (`lem:…`, `prop:…`) refer to `paper/main.tex` and `paper/lemmas/*.tex` (version before §9), which I read in full
  for §§2, 4.2, 5, 6.
- **Zero side:** the zero-side port was read only where it meets the prime side (INTERFACE, M3-HYBRID, ASSEMBLY).
- **Status labels** follow BRIEF rule 6. "Re-derived" means I redid the computation myself, not that I read the author's.

## 0. Verdict

| # | Item | Verdict |
|---|---|---|
| 1 | Localisation at δ = T^{−1+ε_5}: M1–M3, interval lengths, T-dependence of every error term | **HOLDS** |
| 2 | Lemma M3′ (tails by dyadic shells and the classical sieve), and its use across the a/b switch | **HOLDS** (downstream constant slip: see E2) |
| 3 | §6 used verbatim: `prop:sharpLS`, `lem:S`, `lem:C`, the TIsharp swap, low-denominator resonances, Poisson with the t-twist | **HOLDS** |
| 4 | Flattening: B1 invisibility at t ~ T, admissible R_j, B2 density min(α,1) in units of log(QT) | **HOLDS** (one intermediate bound needs a cosmetic repair: E3) |
| 5 | Theorem SH, Corollaries SH-1 and SH-2; literature | **HOLDS WITH REPAIR** (tail constant 8/π should be 24/π: E2). Literature: explicit hybrid constants exist (Ramaré 2016). I did not find the constant-1 form stated, but it follows in a few lines from standard localisation, so claim no novelty. |
| 6 | Ceiling example; "averaging over height neither improves nor worsens C_T⁺" | Ceiling **HOLDS** for general vectors (small hypotheses missing: E6). "Neither worsens" is **PROVED** (it is Theorem SH). "Neither improves" is **HEURISTIC**, as §5 labels it, but STATUS states it unlabelled (E9). |
| 7 | Uniformity over κ | **HOLDS** per κ-cell, exactly as claimed. The interface slip in ASSEMBLY's order of limits (E1: ε_5 was fixed before ε) has **already been repaired** in the current zero-side files. |
| 8 | Numerics | **Independent re-implementation agrees** (explicit characters, sharp window). λ_max tracks N/T and grows linearly past N ≈ Q²T. The ceiling ratio is exactly ∝ N/(Q²\|J\|). The certificate cross-check reproduces bit-for-bit, and its exact evaluator is confirmed by brute force. |

**No step FAILS.** None of the errors below changes Theorem H, the profile F(α) = α on [0,1] and C on (1,β), or any number.

**Overall confidence that the prime side is correct as stated: about 90%.** This is conditional on the paper's §6 (which
I did not re-audit) and on the zero-side inputs (Z1), (Z3), (Z4). Residual risk, most doubtful first:
1. Steps of the paper's proofs that the port reuses "verbatim" and that I re-checked only for their T-dependence (about 5%).
   These are B2 steps (2)–(5) and the TIsharp bookkeeping.
2. Order-of-limits and interface bookkeeping with the zero side (about 3%).
3. Unknown unknowns (about 2%).

---

## 1. Errors, ranked by severity

All are minor. None is fatal.

**E1. Interface: ε_5 was fixed before ε in ASSEMBLY, but the prime side needs ε_5 ≤ ε/(4(1+κ_1)).** Minor; repairable in
one line. **Status: RESOLVED upstream.**
- **Resolution.** The zero-side referee flagged the same slip independently (their E1). The current zero-side files
  (ASSEMBLY §1 step 3 and "Order of limits"; INTERFACE §3 item 3 and §4; M3-HYBRID)
  now set ε_5 := min(ε, ε_1)/(4(1+κ_1)) *after* ε. This is exactly the repair below. I re-derived their new statement that
  the constant-1 region ends at α = 1 − (ε + ε_5κ_T)/(1+κ_T) ≥ 1 − (5/4)ε, with κ_T = log T/log Q here. It follows from
  5δe^u ≤ Q^{1−ε} and ε_5κ_1 ≤ ε/4. Nothing remains to do. The analysis is kept below for the record.
- **Where (version first read).** PRIME-SIDE §0 and INTERFACE-PRIME §1 require ε_5 ≤ min(ε, ε_1)/(4(1+κ_1)).
  zero-side ASSEMBLY §1 step 3 and §4 ("Order of limits", item 2) fixed ε_5 ∈ (0, ε_1/(2(1+κ_1))) *before* θ, ε, ε_3,
  and then let ε be arbitrarily small.
- **Why it matters.** If ε < ε_5, then in regime (i), u ≤ (1−ε)ℓ_*, the localised length is
  K(u) ≤ 5Q^{1−ε}T^{ε_5−ε} + 1. At T = Q^{κ_1} this is Q^{1−ε+κ_1(ε_5−ε)}, which can exceed Q^{1−ε/2} and even Q.
  Then `lem:M2` no longer gives 1 + o(1) all the way up to α = 1 − 2ε.
- **Repair.** ε_5 is internal to the prime side, since deliverable (P) does not mention it. Let the prime side set
  ε_5 := min(ε, ε_1)/(4(1+κ_1)) *after* ε, and delete ε_5 from the assembly's list of data.
- **Alternative repair.** Define regime (i) by K(u) ≤ Q^{1−ε/2}, as zero-side INTERFACE §3 item 3 does. The band then has
  α-width O(ε + ε_5). It still vanishes in the limit, because ε_5 < ε_1/(2(1+κ_1)) → 0 as λ ↑ β.
- **Effect on results:** none.

**E2. Theorem SH states the tail coefficient as 8/π; it should be 24/π.** Minor; an explicit constant.
- **Where.** SHARP-HYBRID-LS §3, Theorem SH, second line of the display.
- **Why.** Lemma P0 is the case g ≡ 1/(2π), and Lemma M3′ then gives 48·(1/2π) = 24/π, not 8/π. The proof of M3′ itself
  collects to 8g_∞(2k_0+7)w_max[3(Q²+1)/δ + (2k_0+6)Y]. With g_∞ = 1/2π this is
  (4/π)(2k_0+7)[3(Q²+1)/δ + 2(k_0+3)Y] ≤ (24/π)(k_0+4)[(Q²+1)/δ + (k_0+3)Y]. No factor 3 is available to reach 8/π.
- **Check.** Symbolic check by this referee: stated − proved = 8g(3Q² + 2Yδk_0² + 16Yδk_0 + 30Yδ + 3)/δ ≥ 0, so
  the M3′ constant 48 itself is fine.
- **Effect.** Corollaries SH-1 and SH-2 and all hybrid uses are O-statements, so they are unaffected.

**E3. "Σ|b_n| ≪ Y^{1/2}L" is not justified for the flattened vector.** Cosmetic.
- **Where.** PRIME-SIDE §2.2 (`eqB:Mrat`); INTERFACE-PRIME §2, item 1.
- **Why.** a^♯ lives on *all* n ≤ Y, not only on prime powers. For squarefree r, |c_r(n)|/φ(r) = 1/φ(r/(r,n)), so
  |Λ_R(n)| ≤ 1.95 τ(n)(1 + log R). The correct bound is Σ|b_n| ≪ Y^{1/2} log² Y.
- **Effect.** Only a bound of the form Q^{O(1+κ_1)} is ever used (with A = A(κ_1)), so nothing changes.

**E4. Notation clash: κ_T means two things.** Editorial.
- In PRIME-SIDE line 4 (inherited from zero-side INTERFACE §1), κ_T = log T/log Q.
- Line 27 redefines κ_T := T^{−ε_5/2}.
- Line 30 then uses the first meaning ("τ := κ_T ≤ κ_1"), as do SHARP-HYBRID-LS l. 132 and l. 190.
- **Repair.** Rename the localisation parameter, for example κ_loc.

**E5. The display in SHARP-HYBRID-LS §4 omits the factor H in the main term.** Editorial. The text says c(u) is "the large
sieve constant divided by H", so the main term should read (1 + κ) H Σ_n |y_n|² 𝒦(n,n) sup c(u).

**E6. The ceiling example (SHARP-HYBRID-LS §6) is missing small hypotheses and is not Q-rough.** Minor.
- **Missing hypotheses.**
  - It needs φ*(q_0) ≍ φ(q_0), because φ*(q) = 0 for q ≡ 2 (mod 4). Take q_0 prime.
  - It needs w(q_0/Q) ≫ 1.
  - It needs |J| ≥ 2/c, so that K ≤ N.
- **Roughness.** The vector is not Q-rough. It therefore shows the ceiling for Δ on general vectors.
- **Q-rough version.** Restrict to the Q-rough n in the progression; their sieve density is ≍ 1/log Q once K/q_0 ≥ Q^C.
  The ratio becomes ≫ N/(Q²|J| log Q). The ceiling for rough vectors is therefore at N ≫ Q²T log Q.
- **Effect.** The conclusion (nothing is possible beyond α = β(κ_T)) is unchanged up to a logarithm.

**E7. Two literature and numerics statements need qualification.** Minor.
- PRIME-SIDE §3 says that Gallagher's inequality "has an unspecified absolute constant … not usable for explicit numbers".
  - This is accurate for Gallagher's own Theorem 3.
  - "Not usable" is too strong: explicit versions exist (Ramaré 2016; see §5 below).
  - The localised classical sieve is still the better route for the constants used here.
- SHARP-HYBRID-LS §7(a) calls "hybrid ≤ non-hybrid at the localised length 4πN/T" a *proved* inequality.
  - It is proved only for the Fejér window of hybrid_lmax.py, whose localisation is exact, and it is compared against a
    maximum over 3 sampled positions, not over all positions.
  - For the sharp window of Theorem SH it is not a theorem. My run shows small excesses over the 3-position value:
    1.9928 vs 1.9561 (flat, N/T = 30, T = 100) and 1.5357 vs 1.5260 (sharp weight, N/T = 5.5, T = 100).
  - This contradicts nothing: Theorem SH carries an explicit tail term.

**E8. Nothing else found.** In particular I looked for, and did not find:
- a T-dependence hidden in §6;
- a failure of the Poisson steps at |t| ≍ T = Q^κ;
- a problem with the a/b switch;
- a loss in B2's normalisation.

**E9. STATUS states "neither improves" without its label.** Labelling. STATUS (Result) states "Averaging over height
neither improves nor worsens C_T⁺" as part of the result. Only "neither worsens" is proved (Theorem SH). "Neither
improves" is the HEURISTIC of SHARP-HYBRID-LS §5, and it is not used anywhere.

---


---

## Report R3: the zero side, assembly, certificates and priority

# Referee report: Theorem H (hybrid height), zero side, M3-HYBRID, assembly, certificates, priority

Independent hostile referee (Claude). Submission: the zero-side port.

**Scope.** Items 1–5 of the referee brief. The prime side proper (Prop. TIsharp-H, the B1/B2 ports) belongs to the prime-side port. I read it only where it meets the zero side, M3-HYBRID or the assembly.

**What I read.**
- The submission: all working notes and certificates.
- The families paper: `main.tex` §§2–4, §5, §7 and App. B, `lemmas/lemma-B-majorant.tex`, and
  `lemma-toeplitz-C.tex` (Prop. sharpLS, Lemma CTlimit, Prop. TIsharp).
- the prime-side port: `STATUS`, `INTERFACE-PRIME`, `PRIME-SIDE`, and `SHARP-HYBRID-LS` §§0–6.

**Primary literature I read myself.**
- Gallagher, Invent. Math. 11 (1970): page scans of pp. 331–332, from GDZ Göttingen.
- AF26 v2 (arXiv 2608.13637): PDF text of Theorem B, §7.2 and Remark 7.2.
- HY26b (arXiv 2609.27808): abstract, plus HTML of Theorem 2.2 and Remark 2.4.
- Conrey–Kwan–Lin–Turnage-Butterbaugh (arXiv 2607.00282): pp. 1–5.
- Chandee–Klinger-Logan–Li (Γ₁(q)): pp. 1–2.
- Quesada-Herrera (arXiv 2108.10238): §1.3.
- Bauer, Acta Arith. 93 (2000): pp. 37–39.
- Abstracts only: CIS13, HY26, Lam26, B. Wang 2609.07918, Garunkštis–Paliulionytė (2025) and Ji 2605.09282. I also
  checked the recent arXiv math.NT listings.

**What I ran** (all pinned to core 0):
- `indep_certify.py`, log `indep_certify.log`;
- `subwindow_comb_check.py`, log `subwindow_comb_check.log`.

## 0. Verdicts

| # | Item | Verdict |
|---|---|---|
| 1a | Bad-character set independent of T; sufficient at height Q^κ; deep off-line zeros inside the window handled by inertia | **HOLDS** |
| 1b | Exterior zeros; Lemma envelope (repaired A > 1/2 form); growth e^{L\|δ\|} with L = λ log(QT) | **HOLDS** |
| 1c | Pointwise family bound loses (1 + Y/Q²)^{1/2}; this is absorbed | **HOLDS** |
| 1d | RvM and Γ-factor terms at height ≍ T | **HOLDS** |
| 1e | One window per character is enough | **HOLDS**. The side claim in ZERO-SIDE §5 about sub-windows is unjustified, but it is not used (E2). |
| 2 | M3-HYBRID (Plancherel in u plus Gallagher's hybrid large sieve) | **HOLDS**. I checked Gallagher's Theorem 3 in the original (small nits: E4). |
| 2 | Support (2+κ/2)/(1+κ) without the lemma, (2+κ)/(1+κ) with it | **HOLDS** (re-derived in §3.3) |
| 3 | Order of limits in ASSEMBLY / INTERFACE | **HOLDS WITH REPAIR**: ε_5 must be chosen after ε (E1) |
| 3 | Continuity p(β) ≤ p(β′) + 2(β/β′ − 1) | **HOLDS** |
| 3 | η_0 independent of κ; uniformity over ℓ^{a_0} ≤ T ≤ Q^{κ_1} by κ-cells | **HOLDS** |
| 4 | Certificates at κ = 0, 1, 5, 10 (sharp, Gauss, classical, dyadic) | **HOLDS**. CERTIFIED, and re-evaluated by independent code. |
| 4 | Classical-route constant C | **HOLDS**. C_cl = w_max/(E_c∫₀¹uw) ≤ 4.175 needs η ≤ 0.0147 (claimed η ≤ 0.01). Dyadic 8/(3E_c) = 5.56546 < 5.5657. |
| 5 | Priority: "apparently open" | **HOLDS**, with omissions (E3) |

**No error found changes a stated constant or breaks the zero side.** The one real defect in the assembly (E1) is a
quantifier-order slip with a one-line repair.

## 1. Errors found, ranked by severity

### E1 (moderate bookkeeping; one-line repair). The order of limits is inconsistent with where the band sits

**Where.**
- ASSEMBLY §1, Theorem cond-H: its hypothesis is that (P) holds "for every fixed choice of (λ, ε_1, θ, ψ, ε, ε_3,
  ε_5)". Its step 3 chooses "…ε_1; then ε_5 ∈ (0, ε_1/(2(1+κ_1))); then θ, ε, ε_3".
- ASSEMBLY §4, "Order of limits": the same order, ε_5 before ε.
- INTERFACE §3 item 3: "0 < ε_5 ≪ ε_1/(1+κ_1) … regime (i) … in units of ℓ_* is α ≤ 1 − O(ε)".

**What fails.** With δ = T^{−1+ε_5}, Lemma M2 (constant 1) applies only while K(u) = 5δe^u + 1 ≤ Q^{1−ε'}. That is,
e^u ≤ Q^{1−ε'}T^{1−ε_5}/5, or in units of ℓ_*:

α ≤ 1 − (ε′ + ε_5κ_T)/(1 + κ_T).

Take κ_T = 1 as an example. The constant-1 region then ends at α = 1 − (ε′ + ε_5)/2. For ε < ε_5/4, the interval
(1 − (ε′ + ε_5)/2, 1 − 2ε) is nonempty. On it only C_band (or C) is available, but (P) as used demands c = 1 there.

So (P) with "c = 1 on (−∞, 1 − 2ε]" is not proved for every choice of data. the prime-side port proves it only for
ε_5 ≤ min(ε, ε_1)/(4(1+κ_1)) (INTERFACE-PRIME §1; PRIME-SIDE (S2), first bullet: K ≤ 5Q^{1−ε}T^{ε_5−ε}).

Step 3's claim that θ, ε, ε_3 can be taken so small that |𝒬_{F_ε}(f_v) − 𝒬_{F_C}(f_v)| ≤ η' with ε_5 already fixed is
therefore false as written. With ε_5 fixed, the profile keeps a band of width ≍ ε_5κ/(1+κ) carrying C_band. That band
does not disappear as ε → 0, and C_band is large:
- 2C_cl ≈ 8.35 for w = 1_{[η,1]};
- 2η^{−2}/(E_c log(1/η)) ≈ 4.5·10⁷ for w_sharp at η = 10^{−4}.

**Repair.**
- Fix θ, ε, ε_3 first, then ε_5 := min(ε, ε_1)/(4(1 + κ_1)).
- In Theorem cond-H, require (P) only for such ε_5.
- In INTERFACE §3 item 3, state ε_5 ≤ ε.

F_ε then no longer depends on ε_5, and every error term still tends to 0 as Q → ∞ for fixed ε_5 > 0. The limit is
unaffected in any case, because ε_5 < ε_1/(2(1+κ_1)) → 0 as λ ↑ β. No constant changes.

### E2 (minor; not used). ZERO-SIDE §5: "the t-orthogonality over the whole of [T, 2T] is not lost" is unjustified

It is false for the worst-case large-sieve bounds the method uses.

This concerns the sub-window variant with sharp disjoint windows J_j = [t_j + θT_0, t_j + (1−θ)T_0] and gaps between them.

**Why it fails.** The prime side sees the time window only through the Fourier transform Û of U = ∪J_j (Lemma M1).
For a single window, |Ĵ(ξ)| ≤ 2/|ξ|. For U, exactly,

|Û(2πk/T_0)| = T|sin(2πkθ)|/(πk).

These are comb peaks of height ≈ 2θT for k ≲ 1/θ. They carry a fraction 2θ/(1−2θ) of the main-peak energy
(`subwindow_comb_check.log`: 393 against the single-window envelope 12.7 at k = 1, for T = 4000, T_0 = 40, θ = 0.05).

The peaks couple n and m with log(m/n) ≈ 2π(k − k')/T_0 ± 1/T. So the localised vectors spread over ranges of relative
length ≍ 1/(θT_0), not 1/T. Once n/T_0 ≫ Q², the family large-sieve constant on such ranges is unbounded.

Equivalently, in t-space the boundary terms near the ≍ T/T_0 fixed boundary points can be bounded only through the
pointwise large sieve, which carries (1 + Y/Q²) ≈ T. Their relative size is then ≍ T/(T_0L), not 1/(T_0L).

the prime-side port independently reached the same conclusion (INTERFACE-PRIME §3). They suggest a smooth partition with Σ W_i² ≡ 1 as
the fix.

**Effect.** None on Theorem H: §5 is explicitly "not needed". Delete or correct the sentence before any write-up.

### E3 (minor). PRIORITY omissions

None of the following anticipates Theorem H. They should still be cited, and the statement "the only polynomial-height
result found is HY26b Rem. 2.4" (STATUS, PRIORITY) should be softened.

- **AF26 v2, Theorem B** (I read the PDF): "Theorem A holds verbatim for L(s,χ) … for any fixed primitive Dirichlet
  character χ". Errors are O_q, and the modulus is not uniform.
  - This is the κ = ∞ endpoint: 0.6725 for each fixed χ as T → ∞.
  - THEOREM Remark 2 ("the Dirichlet-family analogue of Alpöge–Furman at every height") should cite it.
  - PRIORITY cites only AF26 Remark 7.2.
- **Conrey–Kwan–Lin–Turnage-Butterbaugh, arXiv 2607.00282** (1 Jul 2026; I read pp. 1–5). Levinson's method gives an
  unconditional proportion ≥ 1/9 of critical zeros of L(s, Π×χ) (Π on PGL₃, χ primitive of conductor ≤ Q) with
  |γ| ≤ Q^ϖ for ϖ < 1/3, and a stronger result for PGL₂.
  - This is the closest "family at polynomial height" result I found.
  - It concerns twists rather than Dirichlet L-functions, it is a critical-line count, and its proportions are far below
    2/3.
- **Garunkštis–Paliulionytė, Glasnik Mat. 60 (2025) 207–227** (abstract only): an unconditional Montgomery
  pair-correlation theorem for individual Dirichlet L-functions, à la BGSTB, with ≥ 61.7% simple zeros "under certain
  assumptions".
- **Background, not a threat.**
  - Bauer, Acta Arith. 93 (2000): individual L(s,χ), q = o(log T), 0.3658 on the line (I read pp. 37–39).
  - CIS19 (Funct. Approx. 61 (2019)): twisted mean square at the central point. Not about heights.

### E4 (cosmetic)

- THEOREM §2 and INTERFACE give the dyadic C_cl as "5.5656…". The correct value is 8/(3E_c) = 5.56546…. The
  certificate uses 5.5657, a valid upper bound, so nothing changes.
- ZERO-SIDE §3.7 writes "ℓ^{c+1+κ_1}"; it should be (1+κ_1)ℓ^{c+1}.
- "Montgomery only at heights ≤ Q^{1/4}" should read ≤ e^{1/2}Q^{1/4} (T_j = Q^{δ_{j+1}/2} with δ_{j+1} < ½ + 1/ℓ).
- M3-HYBRID says Gallagher applies for D ≥ 1. Theorem 3 is stated on [−T, T] with T ≥ 1, so use T = D/2, which needs
  D ≥ 2, or enlarge the block.
- The q/φ(q)-weighted form without the log log Q loss is not literally in Gallagher. It follows by his proof, with
  Montgomery–Vaughan's weighted large sieve replacing his Lemma 3 (see §3.1).

### E5 (scope caveat, correctly labelled). Super-polynomial range

ZERO-SIDE §4.3 and THEOREM Remark 2 extend the result to all T ≥ ℓ^{a_0}.
- **Zero side.** Fine: e^{L|δ|} < (QT)^{λ/2} ≤ T^{1+1/κ_0}.
- **Prime side.** the prime-side port's parameters (ε ≤ 1/(8(1+κ_1)), ε_5 ≤ min(ε, ε_1)/(4(1+κ_1))) degenerate as κ_1 → ∞. the prime-side port say this
  range is not covered.

It must stay SKETCH.


## 7. Confidence

| Claim | Confidence |
|---|---|
| Zero side of Theorem H as stated (Z1)–(Z4) | 95% |
| M3-HYBRID and the support formula | 97% |
| Assembly after the E1 repair (cells, continuity, η_0, limits) | 94% |
| Certified constants | > 99.9% (exact arithmetic, reproduced) |
| Priority ("nobody has it") | about 75% (targeted search, not exhaustive) |
| **Zero side + assembly jointly correct** | **about 90%** |

Theorem H (sharp), end to end, also rests on the prime-side port's Proposition TIsharp-H, which I did not audit line by line. My spot
checks of items 5(b) and 5(c) and of the prime-side port's (S1)–(S4) are consistent, provided ε_5 ≤ ε (E1). The classical route H-cl
avoids the Toeplitz step and is the most robust.

