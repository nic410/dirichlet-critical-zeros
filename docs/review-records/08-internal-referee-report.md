> **Note on the current state.** Since this review, the Lean proofs of both headlines were completed, and the 10
> results that remain unproved were converted from `sorry` placeholders to `Prop` definitions, so the audit now reports
> zero `sorry`; mentions of Lean `sorry` below describe the state at the time.

> **Cleaned copy of an internal review record: internal file paths and identifiers removed; content otherwise unchanged.**
> Notes on this copy:
> - This is the end-to-end hostile referee report on an **earlier version** of the paper (45 pages): before the
>   independent paper review (record 02), before §9 (polynomial height) was added, and while most of the Lean
>   project was still unproved. It was written by Claude (a lead referee plus four section referees), so it is
>   **not** a cross-model review. Line numbers refer to that version; statements about Lean describe that earlier
>   state. The three major issues M1–M3 and the minor items were addressed in later versions (the AF26 remark is now
>   worded neutrally, §8.6; the certified Arb bounds and the R_w far-field lemma are in the text; C_G ≤ 1.2688 is
>   labelled CERTIFIED). M1's author-reserved items (date, the human verification and responsibility
>   statement) remain open; the author is now named.
> - The four section reports, the referees' scratch scripts, snapshot paths, dates and the author's name have been removed. `anc/` is `paper/anc/`.

# Referee report

**Manuscript.** "More than 93% of the zeros of Dirichlet L-functions at polylogarithmic height are simple and on the critical line, on weighted average".
Frozen snapshot: `main.tex`, the four lemma files, `build/main.pdf` (45 pp.).

**Method of review.**
- I read the whole paper in order, including both appendices, and checked every proof at referee depth.
- Four independent section referees re-checked it in parallel (A: §§2–4 and App. B; B: §5 and `lemma-B-majorant.tex`; C: §6, `lemma-A.tex` and `lemma-toeplitz-C.tex`; D: §7, §8, App. A, the certificates and `anc/`). Their reports are internal and not included.
- I re-verified every claimed error before including it here.
- Line numbers refer to `main.tex` unless a file is named.

**Recommendation (details in §9).** Ready for arXiv after the three major fixes below, all editorial. I found no mathematical error.

---

## 1. Summary

**Setting.** Let $\mathcal F$ be the primitive characters $\chi\bmod q$ with $\eta Q\le q\le Q$. Weight each by $\omega_\chi=w(q/Q)\,q/\varphi(q)$, with a "log-wide" $w$: either $u^{-2}\mathbf 1_{[\eta,1]}$, or its smooth $\sin^2$ variant. The paper counts the zeros with $T<\gamma\le2T$, for $(\log Q)^{a_0}\le T\le(\log Q)^{A_0}$.

**Main results.** Unconditionally, the weighted proportion of zeros that are simple and on the critical line satisfies:
- **Thm 1.1:** at least $p(1)-\varepsilon\ge0.9322-\varepsilon$ for $\eta\le\eta_0(\varepsilon)$; distinct zeros at least $0.9661-\varepsilon$.
- **Thm 1.2:** at least $p(C_G)\ge0.8859-\varepsilon$, by an independent route.
- **Thm 1.3:** fixed-$\eta$ values. The best is $0.9241$ at $\eta=10^{-4}$, with interval-certified constants.

The constant $p(1)$ is the Montgomery–Taylor extremal value for the form factor $\min(\alpha,1)$ on $[0,2]$. It equals Sono's GRH value for the dyadic primitive family.

**Method.** The paper extends the finite Gabor compression of Weil's form, from Alpöge–Furman (argument by Claude) and Hua–Yang, from bandwidth 1 to bandwidth 2.
- The zero side is handled per character. Inertia and a rank–trace inequality give $N^s_{0,\chi}\ge4\operatorname{tr}\hat A_\chi-\|\hat A_\chi\|_F^2-2N_\chi$. Exterior zeros are removed in trace norm. Bad characters are removed with Montgomery's 1969 family density theorem.
- The prime side needs only an **upper** bound for the weighted pair-correlation form. Three devices supply it:
  - **(i) Flattening.** $\Lambda\to\Lambda-\Lambda_R$ is exactly invisible to every $\chi\in\mathcal F$ (B1), and it lowers the diagonal density to $\min(\alpha,1)\ell$ (B2).
  - **(ii) Time localisation** (M1–M3). This gives the exact diagonal constant 1 for $\alpha<1$.
  - **(iii) A sharp constant on $(1,2)$.** There are two routes:
    - the Gauss-sum transfer plus a sharp weighted Farey large sieve (Lemma A), with constant $C_G R_w\to C_G$;
    - an exact Toeplitz identity on $Q$-rough vectors, a positive majorant $\mu^\natural$ of the signed Farey measure, and a local-density count along $\mathrm{SL}_2(\mathbb Z)$ spokes (Lemma C). Its constant $C_T^+(w)\to1$ for log-wide $w$.

  The two routes are joined by a "band device" (`prop:TIsharp`). In that device the flattened vector is swapped in *inside* the PSD majorant $T^\natural$.

## 2. Assessment of correctness

**Verdict.** I found no mathematical error and no hidden gap. Five independent readings agree: mine and the four section referees'. Each of the five paid particular attention to the directions of inequalities, the quantifiers in $T$, the interval lengths, and the order of limits.

**Dependency graph, as I reconstructed it.**
- **Thm 1.1** rests on:
  - `prop:zero` (§3–4: `lem:blocks`, `lem:ranktrace`, `prop:perchi`, `lem:RvM`, `lem:pointwise`, `lem:tails`, `prop:finitecentre`, `prop:trace`, `lem:bad` [Mon69], `prop:tail`);
  - `prop:second` (§5: `lem:mumu`, `lem:muLambda`, `lem:ss`, B1, B2);
  - `prop:TIsharp` (M1–M3, `lem:poisson`, `lem:toeplitz`, `lem:Omega`, `lem:S`, `lem:dual`, `prop:count`, `lem:fS`, `lem:C`, `prop:sharpLS`, `lem:WH`, `lem:harm`, `lem:CTlimit`; band constant from the classical MV large sieve);
  - `lem:windows`, `lem:pLip` and `prop:cert` ($p(1)\ge0.932282$).
- **Thm 1.1 does avoid Lemma A**, `lem:gauss` and `cor:LmultA`, as claimed at l. 713. It uses only the elementary parts of `lemma-A.tex`: `lem:WH`, `lem:dual`, `prop:count`, `lem:harm` and the layer-cake argument.
- **Thm 1.2** is `thm:conditional` with $C=C_G R_w$, via `lem:gauss`, `lem:A`, `lem:WH`, `lem:Rwlog` and `lem:pLip`.
- **Thm 1.3** is the same chain at fixed $\eta$, plus `prop:CTfixed`, the $R_w$ far-field bound (missing from the TeX; see major issue 2), and the Arb certificates.

**Key points checked.**
- **Per-character certificate.** The certificate is *linear* in $(\operatorname{tr}\hat A_\chi,\|\hat A_\chi\|_F^2,N_\chi)$, so summing it with nonnegative weights is legitimate. No Jensen or ratio step is used, and the single Cauchy–Schwarz (l. 501) runs in the right direction.
- **Multiplicities.** Multiple critical zeros are charged to the $R$ side with $n_+\le1$. Off-line orbits have $n_+\le1$ by inertia. The counting identities for $N^s_0$, $N^*_0$, $N_d$ are right.
- **Bad characters** stay in $N$, the trace and $\mathfrak M$. In the certificate they are capped by $4x-x^2\le4$. The bad set is independent of $T$.
- **The Montgomery deduction** (l. 465–479) is correct and robust to the log power: exponent $\le1-\tfrac43\delta$ on both ranges, then $(2+\delta/2)(1-\tfrac43\delta)\le2-\tfrac{13}6\delta$, then $\#\text{bad}\ll Q^2\ell^{-52}$.
- **Explicit formula (App. B)** for complex, non-even $h$: the $\chi(n)h(\log n)$ / $\bar\chi(n)h(-\log n)$ pairing, the gamma factor for both parities, and the contour are correct. Referee A verified the formula numerically against computed zeros of complex characters mod 5 and 7, to $10^{-18}$; swapping $\chi$ and $\bar\chi$ breaks it.
- **B1 (invisibility)** holds for every $r$, including $r\mid q$ and $r=q$. The mean of $c_r\chi$ is 0 for primitive non-principal $\chi$; I checked this numerically for $q\le15$, $r\le30$, with maximum error $10^{-14}$. No condition $R<\eta Q$ is needed.
- **B2's plateau** needs only the PNT for $\zeta$, because $\Lambda_R(p)=G(R)$ for $p>R$.
- **Schur step.** $\Lambda_{\rm mult}I-\Delta\succeq0$ and $\mathcal K\succeq0$ give the needed upper bound.
- **Band device, regime (iii).** This is the crux of Thm 1.1.
  - The Toeplitz identity is applied only to the $Q$-rough part $x_r$ of the *unflattened* localised vector. That is legitimate because B1 is applied before localisation.
  - The non-rough prime powers carry mass $\ll Q^{-1/2}\ell^2$.
  - The flattened (non-rough) $b$ enters only through $\|\cdot\|_{T^\natural}$, and `prop:sharpLS` bounds $T^\natural$ on *all* vectors of an interval of $\le Q^{2-\varepsilon_1}$ integers.
  - $\|x^s_\sharp\|_{T^\natural}$ is negligible: at levels $e>R_{\max}$ by Poisson, using $\|h/r+c/e\|\ge1/(re)$; at levels $e\le R_{\max}$ by the additive large sieve, with relative size $\eta^{-2}Q^{-\varepsilon_1}$.
- **Signed Toeplitz measure.** The paper never uses "norm = sup of the symbol". It replaces $\mu_\Omega$ atom by atom with the positive $\mu^\natural\ge\mu_\Omega^+$, then uses a Fejér-majorant duality lemma valid for positive measures. The main terms of Lemma C are combined with signs, and the errors are summed in absolute value.
- **Order of limits and constraints.**
  - The order is $Q\to\infty$; then $\theta,\varepsilon,\varepsilon_3\to0$; then $\lambda\to2$ with $\lambda(1+\varepsilon_1)\le2-\varepsilon_1$ (so $Y\le Q^{2-\varepsilon_1}$ and every window has $\le Q^{2-\varepsilon_1}$ integers); then $\eta\to0$. This is consistent in §2.3, `rem:orderlimits`, §7.3 and the proof of Thm 1.1.
  - Every $o(1)$ is uniform in $T\in[\ell^{a_0},\ell^{A_0}]$, with rates $\ell^{-a_0/4}$, $\log T/\ell$ or $Q^{-c}$.
  - $\eta$ is fixed before $Q\to\infty$; no uniformity in $\eta$ is claimed, nor needed.
- **External results used within their hypotheses:**
  - Davenport Chs. 9, 12, 16, 18: the functional equation, RvM, the local count, $L'/L$ partial fractions, de la Vallée Poussin;
  - Montgomery 1969 Thm 1: the family over $q\le Q$, $T'\ge2$, $\sigma\in[\frac12,1]$;
  - MV73 (multiplicative with $q/\varphi(q)$, and additive): IK Thm 7.13 and MV73 Thm 1;
  - IK (3.9) for $\sum^*_\chi\chi(a)$ with $(a,q)=1$.

**Numerical spot checks (reproduced independently).**
- $p(C)$ by my own discretised KKT solve (own script): $p(1)=0.9322826$ and $p(1.2688)=0.8859135$ at $n=1600$. All seven rows of `prop:cert` match.
- The uniform $f=\tfrac12\mathbf 1_{[-1,1]}$ gives exactly $11/12$, the CLLR constant: a good sanity check of the functional.
- Referee D reproduced $0.6725007$ (Montgomery–Taylor) at bandwidth 1 and every row of `prop:cert` to 9 digits in exact rationals, with no shared code.
- $\mathcal E=0.47914534\ldots$ and $C_G=1.26877389\ldots<1.2688$ (own script; Referees C and D agree).
- Rank–trace: 20,000 random tests passed. Referee A's adversarial optimisation reaches equality but never violates it.
- The interval certificates were rerun by Referee D (`rw_arb.py 1000`, `ctplus_arb.py lsmooth 10000`) with identical output. Referees C and D reproduced all nine fixed-$\eta$ constants in independent floating point, inside the certified enclosures:
  - $C_T^+\le1.09099,\ 1.04329$;
  - $R_w\le1.059816,\ 1.028831,\ 1.015859$.
- Referee C checked Lemma C end to end: the local count at $Q=3\cdot10^4$ matches the predicted density to $10^{-4}$–$0.3\%$ near rationals.

**Machine-checked (Lean; per the Lean status file at the time).** The Toeplitz identity, the Gauss transfer, Lemma S (positivity), M1–M3, M2, `prop:perchi` from abstract block data, rank–trace, `lem:pLip`, the two main `prop:cert` rows and $C_G\le1.2688$. Everything else is `sorry` and rests on hand checking: B1, B2, Lemma C, `prop:sharpLS`, `prop:TIsharp`, `prop:zero` and `prop:second`. The main text never mentions Lean; that is fine.

---

## 3. Major issues (must fix before posting)

All three are editorial. None requires changing a constant or a statement's strength.

### M1. Draft placeholders and the responsibility statement
- **Where.**
  - the author placeholder (l. 26) and "Draft of \today" (l. 29).
  - The `\todo` in the AI-use statement (l. 756).
  - l. 756: "No human has yet checked every step; the gaps flagged in the accompanying status document should be read before relying on the results." That document is not public.
  - 13 `\NUM{}` markers: l. 100, 105–107, 717, 763, 776, 786; `lemma-A.tex` 328; `lemma-toeplitz-C.tex` 378; `constants.tex` 74–75, 101. Line 100 says the values are "placeholders, to be replaced".
- **Problem.** As frozen, the paper calls the inputs of Thm 1.3 placeholders and points readers to an unavailable status document. No journal referee would accept it in this form, and it should not go to arXiv in this form.
- **Fix.**
  - Drop every `\NUM` (all values stand).
  - The human authors must write the verification and responsibility statement, and either replace the reference to the status document with an explicit list of what has and has not been independently checked (§8 of this report can serve), or ship that list as an ancillary file.

### M2. Theorem 1.3 is not proved by the text as written
- **Where.**
  - Proof of Thm 1.3 (l. 717).
  - App. A (l. 763, 776, 786) and `tab:numerics`.
  - `constants.tex`: the header legend l. 8–11; `tab:constants` l. 29–52; `tab:Rw` l. 65–75; `tab:CTfixed` l. 87–104.
  - `lemma-toeplitz-C.tex` l. 375–379; `lemma-A.tex` `rem:Rwnum` l. 322–329.
- **Problem.**
  - (a) The text cites only the **double-precision** scripts: `ctplus.py`/`ctplus_*.log`, `rw_ess.log`, "`lemmas/scripts/`". The rigorous Arb programs (`anc/ctplus_arb.py`, `anc/rw_arb.py`, `anc/certify_ctplus_arb.log`) are never cited.
  - (b) The tables carry floating-point values under a CERTIFIED label. `tab:CTfixed` has 1.09101/1.04331, and 1.035666 in its "$\mu^-$ region" column where the certified bound is 1.045532. `tab:Rw` has 1.059834 etc.
  - (c) **An argument used by the $R_w$ certificate is missing.** For $t<\eta/T_1$, `rw_arb.py` uses $P_w(t)\le1+2\sup_{y\ge T_1}|E_\varphi(y)|/c_w$, which appears nowhere in `lemma-A.tex` (confirmed by grep). The bound is correct: it follows from the layer-cake proof of `lem:Rwlog`, since every $\alpha_\lambda>T_1$. Referees C and D both re-derived it.
  - (d) The upper bound $C_G\le1.2688$, resp. $<1.268774$, is used in the proofs of Thms 1.2 and 1.3 but labelled COMPUTED (l. 772, `constants.tex` l. 36). This breaks App. A's own rule that "only PROVED and CERTIFIED statements are used in proofs".
  - (e) The CERTIFIED legend in `constants.tex` covers only exact rational arithmetic.
- **Fix.**
  - Apply the patches of the internal numerics report.
  - Add the $R_w$ far-field bound as a one-paragraph lemma or remark after `lem:Rwlog`: it is the analogue of `prop:CTfixed`(a).
  - Cite the Arb files and replace the table values with the certified ones.
  - Relabel $\mathcal E$, $C_G$, $B$, $\delta_{P_0}$ and $\sigma_0^-$ as CERTIFIED, with their sources: the Arb enclosure $\mathcal E\in[0.4791453312,0.4791453473]$, and Lean `CG_le`.
  - Extend the legend to interval arithmetic.
  - Replace all file paths (`cert/`, `scripts/`, `lemmas/scripts/`) by `anc/`.

### M3. The public claim about Alpöge–Furman, Remark 7.2
- **Where.** Table 1 note (a) (l. 139), §8.6 `rem:AF72` (l. 744–745), `tab:otherw` caption (`constants.tex` l. 109–125).
- **Problem.** The paper asserts that the $0.811$ announced in AF26 Remark 7.2 is not achieved for its stated weights. That assertion is:
  - **internally inconsistent:** "$\approx0.807$" in note (a) and §8.6, but "$0.805$" in the same paragraph and in the table; I and Referee D get $p(2.03)=0.8048$;
  - **based on a COMPUTED *signed* constant** $C_T=2.028$. This is not a $C_T^+$, has no proved lower bound, and its scripts are not shipped (an internal open-items note says not to quote it);
  - **a mismatched comparison:** it sets AF26's bandwidth-3/2 claim against a bandwidth-2 computation;
  - **unsupported in one clause:** "the value 0.811 holds for the $q/\varphi(q)$-weighted family" is proved nowhere.

  This is a statement, about another group's paper, that one of its numbers is wrong. It must not rest on uncertified numerics.
- **Fix.**
  - Reword neutrally, for example: "For per-character weights $(1-q/Q)^2$, our computations indicate a large-sieve constant $\approx2.03H$ rather than $1.263H$; with that constant the present method gives $\approx0.805$ at bandwidth 2. We have not been able to reproduce 0.811 for that family."
  - Either ship the computation (the eigenvector evidence) or drop the numbers.
  - Consider contacting the AF26 authors before posting.

---

## 4. Minor issues

There are about 40, grouped below. None affects a theorem.

**Precision in statements and proofs**
1. l. 304 (`lem:blocks`(a)): "of rank one" should be "of rank at most one".
2. l. 226 (`lem:envelope`): "integrate by parts $A$ times" needs integer $A$; use $\lceil A\rceil$.
3. l. 154 and l. 299: the per-character bound is in terms of $\hat A_\chi$, not $G_\chi$. The passage to $\hat G_\chi$ is §4.
4. l. 322 and 337, and Thm 1.1: the separate $N^*_0$ certificate is redundant, since $N^*_0\ge N^s_0$. Say so.
5. l. 379 (`lem:RvM`):
   - Davenport's formula is for $t\ge2$, not $t\ge1$;
   - note that the symmetrisation is exact.
6. l. 262: justify trace-norm convergence for fixed $\chi$, using $e^{L|\delta|}\le e^{L/2}$ with the envelope lemma and the local count.
7. `lem:bad`:
   - say that the bad set is independent of $T$;
   - say that $\delta_j<\tfrac12$ for every shell containing a zero;
   - make the range inclusion $[3/10,1/2]\subset[1/4,3/2]$ explicit.
8. l. 469: "[Mon71, Ch. 12] … one modulus; we do not use it". Verify this description or delete it.
9. l. 162, 576, 646: the level is blockwise, $R_j\le N_j^{1-\varepsilon_3}/(QT)$, not "$R<n^{1-\varepsilon}/(QT)$"; and the rough vectors live on $n>Q^{1+\varepsilon}/2$, not $n\ge Q^{1+\varepsilon}$.
10. l. 576: the density claim omits the factor $1+(2\log T+2)/\ell$ from B2.
11. l. 578: "for each $u$ … relative $O(T^{-1/4})$" holds only after integration in $u$.
12. **Abstract l. 42 and `rem:upper` l. 347–348 misdescribe the key input.** The certificate does not take "a large sieve acting on sifted vectors … directly". What enters is a bound for the PSD Toeplitz majorant on *all* vectors, reached from the sifted identity by the swap of `prop:TIsharp`. A specialist will stumble here, so reword both passages.
13. Small slips:
    - l. 702 cites B1 unnecessarily;
    - `prop:TI` omits the "+1" in its integer counts;
    - "tails in Lemma M3" (`rem:muP`, `rem:bandwidth`) should point to the propositions;
    - in `prop:second`, $c$ must be extended to negative arguments.
14. $\Lambda_{\rm mult}$ is defined twice, differently: l. 293 and `lemma-A.tex` l. 249–250 (with an off-by-one). Unify them.
15. l. 97: "$R_w\ge1$" is asserted without proof. One line fixes it: $P_w(t)\to1$ as $t\to0^+$.
16. `rem:optimal` (l. 697) presupposes that a minimiser exists. Evenness follows directly from convexity: $\mathcal Q((f+f(-\cdot))/2)\le\mathcal Q(f)$.
17. `lem:CTlimit` proof: "31.11" does not follow from the stated $B<3.73$; with it one gets $31.14$. The final bound $<32.6$ still holds.
18. `prop:CTfixed`(b): the factor 2 in $V'_m$ is superfluous. It is harmless.
19. `lemma-toeplitz-C.tex` l. 485: check the theorem number "[MV73, Thm 1]"; IK Thm 7.7 is a safe alternative.
20. Say explicitly that no effective $Q_0$ is claimed; the thresholds are astronomical in $\eta^{-1}$.

**Numerics and documentation**
21. l. 93: $C_G$ is written "$1.268774\ldots$", but the true value is $1.2687738\ldots$, which is *below* 1.268774. Write $1.2687739\ldots$, as on l. 191.
22. l. 763: the numerical facts used in the proofs of Thms 1.1–1.2 are understated. They include $C_G\le1.2688$ (the margin is $2.6\cdot10^{-5}$, so "to four decimals" is not enough) and $\sigma_0^-<1$.
23. `tab:numerics` l. 774: "$p(C_G)\approx0.8859135$" is really $p(1.2688)$; $p(C_G)\approx0.8859177$. The $R_w$ row points to the wrong table.
24. `prop:cert` l. 671: the step functions are not "recorded" in `certify.py`; they are regenerated by a float solve and rounded. Either ship the integer heights or say "generated deterministically by".
25. l. 100: "the only computer-assisted input" also omits `prop:cert`.
26. App. A.1–A.3 cite computations that are not shipped: the Euler–Lagrange/FEM solutions, the eigenvalue validations, the Rayleigh quotients and `tab:otherw`. Ship them or mark them "not included".
27. `rem:negpart`: "$Q=10^7$" should be $Q=10^6$ (the shipped log).
28. There are 30 overfull hboxes, one of 121 pt (`tab:constants`).

**Remarks (§8) and comparisons**
29. §8.4 l. 739: "$w=\mathbf 1_{[1/2,1]}$ has $R_w=2.37$" is false; that weight gives $R_w=4\pi^2/9\approx4.39$ (I verified this). The value 2.37 $=\pi^2/(6\log2)$ belongs to $u^{-2}\mathbf 1_{[1/2,1]}$.
30. §8.4: $\max\omega/\min\omega\asymp\eta^{-2}\log\log Q$, not $\eta^{-2}$.
31. §8.5 l. 742 presents heuristics as facts. With the paper's $\delta=T^{-1/2}$, one gets $1+\tau/2$ rather than $1+\tau$; and "optimal range" is heuristic.
32. §8.1: state the precise reason, namely that CLLR's GRH asymptotic gives form factor 1 on $(1,2)$, so no majorant below $F_1$ can exist.
33. §8.2(a): "0.788172 as $\eta\to0$" should read "$\ge0.788172-\varepsilon$ for $\eta\le\eta_0(\varepsilon)$".
34. §8.6 vs §8.7: CLLR use GRH on the prime side as well (their Lemma 4: prime sums twisted by small-conductor characters). "GRH was needed for one purpose only" should be qualified as "in the certificate". Also, "the Toeplitz identity removes the small-conductor terms exactly" overstates things: the negative part is majorised, not evaluated.
35. Remark at l. 194–196:
    - $\mathcal E$ is only the Euler product in CLLR's $A=\hat W(1)\prod_p(\cdots)$;
    - CLLR's $W$ is supported in $(1,2)$, a dyadic family, so the identification "$W(u)=u^{-1}$" is formal. Say so, since log-wide spreading is exactly what separates this paper's family from the GRH family.
36. l. 344: Lamzouri's Prop. 2.1 also assumes $\eta\in L^2$ with compact support.

**Notation (Referee A's list; all unambiguous in context)**
37. Symbols with several meanings:
    - $a$ is used three ways: $\int v$, the vector $a_n$, and $\mathfrak a_\chi$;
    - $J$ is both the interval and a $2\times2$ matrix;
    - $\omega_A$, $A_k(U)$, $W(t)$, $\mathcal E(t)$ and $H(z)$ each clash with existing symbols;
    - $\mathcal M_\chi$, $\mathcal M$ and $\mathfrak M$ are easily confused;
    - $\eta$ doubles as a function in the Lamzouri remark;
    - $d$ and $\varepsilon$ are each used twice.

**The headline figure**
38. The "93%" is reached only in the double limit. By the proved rate $C_T^+\le1+83/L_\eta$ one needs $L_\eta\gtrsim3.6\cdot10^4$; the best *certified* fixed-$\eta$ value is $92.4\%$ at $\eta=10^{-4}$. Say this explicitly in §1, next to Thm 1.1. The title is literally true, but readers will want this sentence.

---

## 5. Presentation

- **Accuracy and modesty of the introduction.** The introduction is accurate and, on the whole, appropriately modest.
  - §1.3 ("What is claimed and what is not") is exemplary: weighted averages, polylogarithmic heights, nothing about individual $L$-functions, lower bounds only, no bearing on RH.
  - The comparison with Sono/CLLR correctly says "same constant, different statistic".
  - The main residual overclaims are:
    - the AF26 remark (M3);
    - the §8.5 heuristics;
    - "removes the small-conductor terms exactly" (§8.7).
- **Readability for a specialist.** Good, but dense.
  - The logical chain is spread across `main.tex` and three lemma files, with forward references: §5 relies on `prop:TIsharp` in §6.2.
  - **Add a one-page dependency diagram or table** for Thms 1.1–1.3, of the kind in §2 above. It would help referees a great deal.
  - The "Overview" paragraphs in §6 are helpful.
  - The notation needs a de-duplication pass (item 37).
- **Length.** 45 pages is somewhat long for the content. Candidates for cutting:
  - `prop:TI` could be folded into the proof of `thm:conditional`, which already re-runs it;
  - §8 has eight subsections, some speculative (§8.5, §8.6), and could be halved;
  - App. A partly duplicates `constants.tex`;
  - the fixed-$\eta$ machinery (`prop:CTfixed`, far fields, 64 sets $S_1$) could move to an appendix.

  Target: about 38 pages.
- **Titles.** The theorem titles and the table of results are clear. The main-text AI-use statement is appropriate once M1 is fixed.

## 6. Literature

**Prior work is fairly credited** throughout:
- Alpöge–Furman (with the argument attributed to Claude, as AF26 itself states), Hua–Yang (30 citations, as the source of the zero-side port) and HY26b;
- Lamzouri (the table and the remark on his inequality) and Prüzelius;
- Montgomery (1973, 1975, 1969) and Montgomery–Vaughan;
- CLLR, Sono (2016, 2025), Conrey–Iwaniec–Soundararajan and Özlük;
- Goldston, Graham and Goldston–Yıldırım for $\Lambda_R$, and Boca–Cobeli–Zaharescu for the spokes.

I checked the Table 1 entries against the sources:
- HY26 and HY26b: prime modulus, bandwidth $\le1$, $0.6725$;
- Prüzelius (Zenodo v2.4.1): prime modulus, $2/3$;
- Lamzouri: $0.6725$;
- CLLR: $11/12$, with Özlük's $0.8688$ explained in their §6;
- AF26 Rem. 7.2: announced $0.811$ at bandwidth $3/2$.

**Suggested additions:**
- Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh: the unconditional pair correlation behind AF26 and Lamzouri. It is in `refs.bib` but not cited.
- Wang, arXiv:2609.24167, improves $0.6725$ for $\zeta$ by $6.7\cdot10^{-8}$. Mention it where the $\zeta$ records are listed; the paper's "nothing here improves 0.6725 for $\zeta$" remains true.
- Ramaré, arXiv:2609.25885 (the weighted large sieve via Parseval), for context around Lemma A's "sharp weighted Farey large sieve".
- Selberg, for "$\Lambda_R$ in the style of Selberg".
- Possibly Vaughan / Goldston–Vaughan, who pair truncated divisor sums with the large sieve in moments of primes in progressions. A specialist should confirm the exact references before they are added.
- Optionally, note the unrefereed Zenodo claim of 79.62% for $\zeta$ (Yang–Yang, Aug 2026).

**Novelty check (web).**
- arXiv math.NT listings for 21–25 Sep 2026 contain nothing that pre-empts this paper. The relevant items are:
  - Hua–Yang 2609.27808 (prime modulus, bandwidth $\le1$);
  - Wang 2609.24167 ($\zeta$);
  - Ramaré 2609.25879 and 2609.25885;
  - Cossaboom 2609.27715 (GL$_2$ density);
  - Fiori 2609.22624;
  - Kazin–Kadyrov 2609.29898.
- Targeted searches (arXiv, Zenodo, general web) found no unconditional family result beyond bandwidth 1, and nothing near 0.93 without GRH.
- An earlier internal scoop check is consistent with this.
- I did not see Montgomery 1969 myself; see §8.

## 7. Significance and venue

**Significance.**
- This is a technically substantial and, as far as five careful readings can tell, correct extension of the Alpöge–Furman/Hua–Yang method. It pushes the method to its natural barrier, bandwidth 2, and reaches the GRH-level constant 0.9322 unconditionally.
- Its genuinely new components are of independent interest:
  - the flattening–invisibility–swap mechanism;
  - the exact Toeplitz structure of the primitive family on rough vectors;
  - the sharp large-sieve constant $C_T^+\to1$ via local Farey densities.
- The limitations are real and fully disclosed:
  - a specific log-wide conductor weighting, with $93\%$ reached only as $\eta\to0$ and $92.4\%$ certified at $\eta=10^{-4}$;
  - polylogarithmic heights only;
  - dyadic families get much weaker constants;
  - no bearing on individual $L$-functions.
- The conceptual breakthrough (inertia plus rank–trace, replacing RH on the zero side) belongs to AF26, and the area is moving very fast.

**Venue.** IMRN or Algebra & Number Theory are appropriate; Compositio or Math. Annalen are also plausible. Duke would be a stretch unless the sharp primitive large sieve is developed as a standalone result with further applications.

## 8. What a human specialist must check personally

Each item below is new, carries a headline number, and is not machine-checked (Lean `sorry`), or is a literature judgement.

1. **Lemma C, `prop:sharpLS` and `lem:dual`** (`lemma-toeplitz-C.tex` 233–315; `lemma-A.tex` 86–202). This is the only input that moves $0.8859$ to $0.9322$. Check:
   - the spoke count with the coprimality twist: the three cases for $p\mid r$ and the $G_S$ factor;
   - that the signed main terms combine to $Q^2\mathcal E I_w R_S(t)$ while the errors are summed absolutely;
   - the isolated-point and $\mu^m$ bounds;
   - the duality constant $(1+\kappa^2)$.

   Numerics corroborate all of this, but only a proof check settles it.
2. **`prop:TIsharp` Step 4: the swap inside $T^\natural$** (`lemma-toeplitz-C.tex` 427–517). Check:
   - that invisibility is used before localisation;
   - the $Q$-rough split;
   - $\|h/r+c/e\|\ge1/(re)$ and the level split at $R_{\max}$;
   - the prime-power remainder.

   This is the heart of why flattening and the sifted Toeplitz identity can be combined.
3. **Flattening, B1/B2** (`lemma-B-majorant.tex` 47–175): the Poisson bookkeeping with $\Theta=T$; the $\Lambda_R^2$ asymptotic needing $R\le N^{1/2-\varepsilon_3}$; and the fact that the density is only an upper bound.
4. **The zero side, §4** (no Lean coverage):
   - `prop:finitecentre`, `prop:tail` and the deletion step;
   - **read Montgomery, Invent. Math. 8 (1969), Thm 1 in the source.** Confirm the family over $q\le Q$ with primitive $\chi$, $T\ge2$, the two exponents, and the log power (quoted as 13; any fixed power works).
5. **Appendix B, the explicit formula.** The proof is standard, but the write-up is new. Confirm the Davenport chapter pointers.
6. **Global sanity.** $93\%$ far exceeds the Levinson-type family records ($0.56$, $0.6044$). §8.6 explains why there is no conflict. A specialist should satisfy themselves that no positivity at complex arguments is used anywhere: only inertia per character, and upper bounds on the prime side.
7. **AF26 Remark 7.2 (M3).** Read it, and decide what, if anything, the paper may say about it.
8. **Priority of Lemma A and the sifted Toeplitz large sieve** against the literature: Ramaré, Baier–Zhao, Boca–Zaharescu, Huxley, and Vaughan / Goldston–Vaughan for $\Lambda_R$ with the large sieve.
9. Optionally, a line audit of `anc/ctplus_arb.py` and `anc/rw_arb.py`. The stakes are low: two independent reproductions agree.

## 9. Recommendation

**Ready for arXiv once the three major issues are fixed.**
- M1: remove the placeholders; the human authors write the verification and responsibility statement.
- M2: make Thm 1.3's certification visible in the TeX, including the $R_w$ far-field bound.
- M3: soften or substantiate the AF26 remark.

I also recommend fixing minor items 12, 21, 29, 34, 35 and 38 before posting; the rest can wait for the journal version.

The mathematics appears sound. The paper is suitable to send to a human expert now, in parallel with these fixes. The expert should concentrate on §8 items 1–4.

---
*Scratch and reproductions: internal; not included.*
