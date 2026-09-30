> **Cleaned copy of an internal review record: internal file paths and identifiers removed; content otherwise unchanged.**
> Notes on this copy:
> - This literature check was carried out by a Claude sub-agent, for Theorems 1.1–1.3 only, **before** §9
>   (polynomial height, Theorem 1.4) was added. It did not find Dickinson (arXiv:2211.06264), the closest
>   unconditional result at polynomial height; that omission was caught later by the review of §9 (record 03) and
>   fixed in the paper. Hua–Yang's small-θ values at polynomial height were corrected later still (record 04).
> - Section numbers of the paper quoted here are those of the version then checked (e.g. "§7.3" is now §8.3, the
>   ζ barrier). Publication dates of third-party papers and the search-coverage window are kept; the time of the
>   check itself and internal file references have been removed.

# Literature check: competing papers for the families paper (Thms 1.1–1.3, sharp primitive large sieve)

Read-only check by a Claude sub-agent.

**Spot-checks by the checking agent:** we fetched the arXiv abstract pages for 2607.00282 and 2609.07918. Titles, authors and dates
match. We also read CKLT Corollary 1.14 in the PDF text, and it matches the quotation below.

**Paper read:** `paper/main.tex` (abstract, §1.1–1.5, §7) and `paper/refs.bib`.
**Updates:** an internal draft-status note and the internal referee report §6 (record 08).

## 0. Verdict

- **Theorems 1.1 (0.9322), 1.2 (0.8859) and 1.3 (0.9155 / 0.9241) are not pre-empted.** No paper in any reachable
  source claims an unconditional family proportion of simple or critical zeros beyond bandwidth 1, and none claims
  more than 0.7 for a Dirichlet family without GRH.
- **The sharp-large-sieve contribution is not pre-empted.** No paper proves a primitive-character large sieve whose
  constant tends to 1, or a Toeplitz/Farey majorant on rough vectors. The new large-sieve papers are:
  - Ramaré 2609.25885 and 2609.25879 (already cited; additive and arithmetic);
  - Baier 2609.21195 (square moduli, assuming Hooley's R\*);
  - unrelated spectral and quadratic sieves.
- **No new versions of cited papers:**
  - AF26 is still v2 (19 Aug); HY26 v2 (24 Aug); HY26b v1; Lam26 v2 (8 Sep); Wang26 v1.
  - Prüzelius is still Zenodo v2.4.1 (23 Aug).
- **Recommended additions.** None is mandatory; BibTeX is in §4.
  1. **Conrey–Kwan–Lin–Turnage-Butterbaugh, arXiv:2607.00282 (1 Jul 2026). Should add.**
     - It is an unconditional family result: at least 1/3 simple critical zeros for GL(2) twists by primitive χ,
       q ≤ Q.
     - Its key input is a refined asymptotic large sieve.
     - It belongs in Table 1, or in the Levinson footnote next to CIS13 and Sono25.
  2. **Biao Wang, arXiv:2609.07918 (7 Sep 2026). Should add.**
     - It gives the ζ short-interval version of Lamzouri's argument.
     - Our Wang26 cites it as its ref. [14].
     - It is a follow-up to AF26 and Lam26, and we do not currently cite it.
  3. **Optional:**
     - BGSTB, arXiv:2501.14545v3 (revised 1 Sep 2026): a conditional ζ result, 2/3 simple and critical, under a
       narrow-box hypothesis.
     - Prüzelius, Zenodo 10.5281/zenodo.22096771: a note lowering the HY26 height floor.
     - One sentence noting unrefereed Zenodo ζ claims, up to 0.67348.
- **Bibliography housekeeping.** 13 entries in `refs.bib` are never `\cite`d, so `amsplain` drops them: PC26, Ji26,
  Anth26, CIS-ALS, Wu16, DPR23, HR03, KS99, CGG98, Gal70, Lam11, Mon71 and Sel46.
  - Either cite them or accept that they vanish.
  - Natural citation points: CIS-ALS next to CIS13; Anth26 in the AI-use statement; Wu16 in Table 1.

## 1. Sources reached and blocked

| Source | Status | Use |
|---|---|---|
| arXiv OAI-PMH (`oaipmh.arxiv.org`) | **reachable** | Harvested full metadata and abstracts with datestamp ≥ 2026-07-25: math.NT 2,050 records (including 496 cross-lists), all of `math` 27,280, cs.AI 15,319, cs.LO 647. Coverage checked against the math.NT month listings (August 536/536 IDs present, September 649/649) and `/pastweek` (206/206). |
| arXiv listing pages (`/list/math.NT/pastweek`, `/recent`, `/2026-08`, `/2026-09`) | reachable | Coverage check. The latest visible announcement is **Fri 25 Sep 2026**. |
| arXiv API (`export.arxiv.org/api/query`) | 406 via curl; **reachable via WebFetch** | 3 confirmatory queries |
| arXiv abstract and PDF pages | reachable | Version histories and full texts of 2609.07918, 2609.24167, 2607.00282, 2608.16034, 2609.27808, 2609.25885 and 2609.25879 |
| Semantic Scholar | citations endpoint reachable; search endpoint **rate-limited** (429; 1 of 4 queries returned) | Citations of 2608.13637, 2609.02882, 2608.16034, 2609.24167, 2609.27808 and 2609.07918 |
| OpenAlex API | reachable | About 25 keyword searches filtered to publication date ≥ 2026-07-25, plus DOI and citation lookups. There are no citation links for arXiv preprints (cited-by is 0 for all). |
| Zenodo REST API | reachable via curl (Python urllib got 403) | About 40 metadata and description queries, version histories, record descriptions and 2 PDFs |
| MathOverflow (StackExchange API) | reachable | Nothing relevant since 1 Aug |
| anthropic.com/research/riemann-zeta | reachable | Unchanged since the 13 Aug update; no family announcement |
| **General web search** | **unavailable** | not used |
| Google Scholar | **blocked** (403) | not used |
| Bing and DuckDuckGo via curl | unusable (Bing gave irrelevant localised results; DuckDuckGo returned a 202 challenge) | not used |
| Wikipedia | not used (instructions) | not used |

## 2. Queries run

**OAI harvest, then local regex over title, abstract and comments.** The patterns covered:
- simple, distinct and critical zeros; critical line;
- proportions, "two thirds" and NN% figures;
- pair correlation, form factor and Montgomery–Taylor;
- one-level density, low-lying zeros and n-level statistics;
- large sieve, Farey and Toeplitz;
- the Weil explicit formula, positivity, quadratic and Hermitian forms;
- Alpöge, Furman, Lamzouri, 2608.13637 and 2609.02882;
- rank–trace, positive semidefinite, Gabor and finite compression;
- AI terms (LLM, Claude, GPT, Gemini, agentic, Lean, formalisation).

A catch-all pattern matched papers mentioning zeros together with (Dirichlet, character, family, conductor or modulus)
and (L-function or zeta). All math.NT titles since 1 Aug were read in full.

**Author scan of the harvest since 1 Aug:** Alpöge, Furman, Lamzouri, Sono, Chandee, Radziwiłł, Milinovich, Bui,
Ramaré, Baier, Hua, Xiufan Yang, Conrey, Soundararajan, Iwaniec, Goldston, Suriajaya, Baluyot, Turnage-Butterbaugh,
Pratt, Montgomery, X. Wu, Drappeau, Pearce-Crump, Heath-Brown, Maynard, Zaharescu, Boca, Rudnick, S.-C. Liu, Y. Lee
and Biao Wang.

**arXiv API (via WebFetch):**
- `all:"simple zeros"`, sorted by date;
- ("zeta function" or "L-functions" or "Riemann hypothesis") within cs.LG, cs.CL, cs.AI, cs.LO or cs.MA;
- ("simple zeros" or "critical line" or "pair correlation") with (Dirichlet, characters, family or families).

**Semantic Scholar:** the citations endpoint for the six papers in §1, and a search for "simple zeros Dirichlet
L-functions" (year 2026). The other three searches were rate-limited.

**OpenAlex (publication date ≥ 2026-07-25).** Phrase and keyword searches:
- "simple zeros" with "L-functions"; "simple zeros" alone; "simple zeros" with family and characters;
- "critical line" with "Dirichlet L-functions"; "zeros on the critical line"; "critical zeros" with family;
- zeros, "Dirichlet L-functions" and proportion; "distinct zeros" with Dirichlet;
- "pair correlation" with "Dirichlet L-functions"; "low-lying zeros"; "one-level density" with Dirichlet;
- "primitive Dirichlet characters" with zeros; "families of L-functions" with zeros;
- "Montgomery-Taylor"; Alpöge Furman zeros; "finite compression" with Weil; "rank-trace" with zeros;
- "large sieve" with characters; "large sieve" with Farey; "large sieve inequality"; Toeplitz with "large sieve";
  "Bombieri-Davenport"; Farey fractions sieve;
- the Hua–Yang title.

Also a `cites:` lookup on Prüzelius.

**Zenodo (publication date ≥ 2026-07-25).** Metadata searches:
- "simple zeros"; "distinct zeros"; "simple and on the critical line"; "two thirds" with zeros; "Montgomery" with
  "simple zeros";
- "critical line" with Dirichlet; "critical line" with family and Dirichlet; Dirichlet zeros proportion;
- "pair correlation" with L-functions; Lean with zeros;
- large sieve; "large sieve" with (sharp, Toeplitz, Bombieri–Davenport or Farey);
- Alpoge and Alpöge; Furman with zeta;
- the IDs 2608.16034, 2608.13637 and 2609.02882;
- the version history of the Prüzelius concept record.

Description-field searches:
- Dirichlet with (family, conductor, moduli or q-aspect) and (simple or critical line);
- (rank–trace, finite compression, Gabor or Montgomery–Taylor) with Dirichlet;
- primitive characters with (simple, critical line or pair correlation);
- "large sieve" with primitive and (sharp or constant);
- the constants 0.93, 0.9322, 11/12, 0.8688 and 0.811;
- Lamzouri; Wang with 2609.24167; Sono, Chandee and Özlük.

## 3. Candidate table

Overlap levels are NONE, TANGENTIAL, PARTIAL and PRE-EMPTS. "Cited?" means `\cite`d somewhere in `main.tex` or
`lemmas/*.tex`.

### 3a. Directly relevant: families, the AF26/Lam26 line, sharp large sieve

| ID | Date | Authors | Title | What it proves | Overlap | Cited? |
|---|---|---|---|---|---|---|
| 2608.13637v2 | 13 Aug (v2 19 Aug) | Alpöge, Furman (Claude) | More than two thirds of the zeta zeros are simple and on the critical line | ζ: at least 2/3 simple and critical (0.6725 with the MT window), unconditionally, via rank–trace and Weil compression. Abstract: "The results extend to primitive Dirichlet $L$-functions". Rmk 7.2 announces 0.811 for q ≤ Q without details. No new version. | PARTIAL (method source; announced family figure) | **Yes** (AF26) |
| 2608.16034v2 | 17 Aug (v2 24 Aug) | Hua, Yang | Simple and distinct zeros in a prime-modulus Dirichlet family … | Prime q, unweighted, heights (log log q)^{1+η}/log q ≤ T ≤ (log q)^A: at least 0.6725 simple and critical. Unchanged. | PARTIAL (same method; prime modulus; bandwidth ≤ 1) | **Yes** (HY26) |
| 2609.27808v1 | 18 Aug (announced 24 Sep) | Hua, Yang | Gevrey localization for simple and distinct zeros in a prime-modulus Dirichlet family | Prime q. The bound is 2 − 1/c*_{λbw} with **λbw := min{1, …}**, giving 0.6725 at polylog height. | PARTIAL (bandwidth explicitly capped at 1) | **Yes** (HY26b) |
| Zenodo 10.5281/zenodo.21980224 (v2.4.1) | 23 Aug | Prüzelius | Two thirds of the zeros of Dirichlet L-functions at polylogarithmic height … on average | Prime-modulus family, at least 2/3, bandwidth 1. No version after 2.4.1. | PARTIAL | **Yes** (Pru26) |
| Zenodo 10.5281/zenodo.22096771 | 25 Aug | Prüzelius | A Carleman window class for the height floor in Hua–Yang, arXiv:2608.16034 … | A 14-page note. Carleman windows lower the HY26 height floor to T ≥ (log log q)(log log log q)^{2+η}/log q; constants unchanged. | TANGENTIAL | No |
| **2609.07918v1** | **7 Sep** | **Biao Wang** | **Simple critical zeros and distinct zeros of the Riemann zeta-function in short intervals** | ζ on (T, T+T^θ]: the liminf of N₀ˢ/N is at least c(θ) = 2 − θ/2 − (1/√2)cot(θ/√2), positive for θ > 0.5502. Proves short-interval BGSTB pair correlation and applies Lamzouri's inequality. Acknowledges AI assistance. Cites AF26 and Lam26; cited by Wang26 as [14]. | TANGENTIAL (ζ only; follows AF26/Lam26) | **No** |
| 2609.24167v1 | 21 Sep | Biao Wang | Proportions of the non-trivial zeros of the Riemann zeta function | ζ: C₀ + 6.666·10⁻⁸. Unchanged. Acknowledges AI assistance. | TANGENTIAL | **Yes** (Wang26) |
| 2609.02882v2 | 2 Sep (v2 8 Sep) | Lamzouri | A new proof that more than 2/3 … | ζ only; v2 adds 88.76% simple or critical. Unchanged. | TANGENTIAL | **Yes** (Lam26) |
| **2607.00282v1** | **1 Jul** | **Conrey, Kwan, Lin, Turnage-Butterbaugh** | **Critical Zeros and Unconditional Mean Value Theorems for twisted PGL(2) and PGL(3) L-functions** | Family L(s, Π₀ × χ), χ primitive with conductor q ≤ Q, \|γ\| ≤ Q^ε, all unconditional. GL(3): at least 1/9 critical (1/200 simple critical). GL(2): at least 1/3 − O(ε) **simple and critical** (Cor. 1.14). Method: Levinson with a "refined, flexible, and uniform version of the Asymptotic Large Sieve". | TANGENTIAL (different family and method, but an unconditional q-family simple-critical proportion driven by a large sieve) | **No** |
| 2501.14545v3 | v3 1 Sep | Baluyot, Goldston, Suriajaya, Turnage-Butterbaugh | Pair Correlation of Zeros of the Riemann Zeta Function I: Proportions of Simple Zeros and Critical Zeros | ζ: at least 2/3 simple and critical, assuming all zeros lie in a box of width b/log T with b = 0.3185 | TANGENTIAL | No (we cite BGSTB24 = 2306.04799) |
| 2609.15329v1 | 14 Sep | Pearce-Crump | Optimising Selberg's method for critical zeros | ζ: at least 7% critical, by Selberg's method | NONE–TANGENTIAL | In bib (PC26), **not cited** |
| 2609.25885v1 and 2609.25879v1 | 22 Sep | Ramaré | The weighted large sieve through Parseval; The large sieve through Parseval, large sifted sets are regular | Arithmetic (Montgomery-sieve) weighted large sieve via Parseval and the Farey dissection; e.g. Cor. 1.2 has denominator N + c·q(q+Q) with c = 0.8987. No primitive-character family and no normalised constant tending to 1. On re-reading, §1.3(c) of our paper describes them accurately. | TANGENTIAL | **Yes** (Ram26, Ram26b) |
| 2609.21195v1 | 18 Sep | Baier | The large sieve for square moduli under Hooley's hypothesis R\* | Square moduli, conditional; counts Farey points near b/r | TANGENTIAL (same Farey-points-near-a-rational geometry as Bai06) | No (optional) |

### 3b. Other families, low-lying zeros and large sieves (NONE or TANGENTIAL)

| ID | Date | Authors | Title | What it proves | Overlap | Cited? |
|---|---|---|---|---|---|---|
| 2609.06167 | 5 Sep | Durkan, Pearce-Crump | Central non-vanishing of Dirichlet L-functions | At least 3/8 of primitive χ mod q have L(1/2, χ) ≠ 0 | TANGENTIAL | No |
| 2503.15832 (J. Number Theory, published 24 Jul) | Jul | T. Zhao | The positivity technique and low-lying zeros of Dirichlet L-functions | Under GRH: sharper error terms for low-lying zeros; improves Hughes–Rudnick on small first zeros | TANGENTIAL | No |
| 2608.15063 | 18 Aug | Chen, Housholder, Khan, Miller, Pradhan | Bounding the number of zeros near the central point in families of cuspidal newforms | GRH; newforms of prime level | NONE | No |
| 2408.09050 | updated 15 Aug | Cheek, Gilman, Jaber, Miller, Tomé | On the density of low lying zeros of a large family of automorphic L-functions | GRH; n-th centred moments | NONE | No |
| 2608.09906 | 10 Aug | Atherfold | On the β=2 partition function for Dirichlet L-functions in the q-aspect | Maximum of \|L(1/2+ih, χ)\| for typical χ mod a prime q | NONE | No |
| 2607.22930 | 24 Jul | Banks, Loftus | Unshared zeros of Dirichlet L-functions | No L(s, χ₁) vanishes at every zero of L(s, χ₀) | NONE | No |
| 2407.14656 | updated 14 Sep | Liu, Williams, Zaharescu | Pair correlation of zeros of L-functions for non-CM newforms in shifted ranges | A single GL(2) form, shifted pair correlation | NONE | No |
| 2609.27715, 2609.22624, 2609.17875 | Sep | Cossaboom; Fiori; Dubon | GL₂ zero density; zero density in short intervals; zero-density concentration | Zero-density results | NONE | No |
| 2607.15311, 2604.23661, 2608.21573, 2608.29558, 2607.24311 | Jul–Sep | Croot et al.; Munsch–Shparlinski–Sun–Xiao; Murty–Naik; Qi–Qiao; Blomer–Pascadi | Quadratic, Legendre-symbol, non-abelian and spectral large sieves; Kloosterman bilinear forms | None concerns primitive characters with a sharp constant | NONE | No |
| DOI 10.32996/jmss.2026.7.6.3 | 14 Aug | Nagoshi | On universality and simple a-points of a family of Dirichlet L-functions … | Joint universality; simple a-points for a positive proportion of χ mod a prime q | NONE | No |

### 3c. AI/agentic and Zenodo ζ-only rank–trace refinements (all TANGENTIAL, none cited)

None treats a family. All are unrefereed, and most declare AI assistance. The claims are quoted from Zenodo
descriptions and were **not** verified.

| Record | Date | Author | Claim (ζ only) |
|---|---|---|---|
| zenodo.22646541 | 7 Sep | Gebendorfer | ≥ 0.6734760237, the largest ζ claim found |
| zenodo.22119371 | 30 Aug | K. Singh | ≥ 0.67345129; distinct zeros ≥ 0.83672564; "Building on the unconditional finite-compression method of Alpöge and Furman" |
| zenodo.22837912 and 22280747 | 18 Sep and 3 Sep | D. Schäfer | ≥ 0.67342504 and ≥ 0.673320 |
| zenodo.22066689, 21960305, 22287432 | Aug–Sep | M. Devine | ≥ 0.673399. Also claims the fixed MT kernel "with pure Gram/rank machinery cannot force a bound above 0.6736". Analytic δ > 0, partly in Lean. |
| zenodo.21926962 and 21892048 | Aug | Y. Shi; tawanerguo-cn | ≥ 0.673317; ≥ 0.673193 |
| zenodo.22209568 | 31 Aug | T. Komada | 0.672513, Lean-verified; Claude Code and Codex assisted |
| zenodo.21929455, 22171689, 22778066, 22801367, 22286993 | Aug–Sep | Notik; Tyagi; Fabbian; Zeraoulia | Conditional four-moment bound of 16/21; no-go for cubic augmentation; conditional 0.6792 under a narrow box; Widder smoothing; multiplicity bounds |
| zenodo.22940291, 22984155, 22727389, 22860012 | 12–26 Sep | Santibáñez-Leal | **Cites Wang26.** Sharpens Wang's kernel ratio to √2, giving 0.6725007996, plus short-interval ζ results building on 2609.07918 |
| zenodo.21975237 and 22065921 | 17 and 22 Aug | S. Yang, H. Yang | 79.62%, then "almost all", for ζ (low credibility; already noted by the referee) |
| 2608.19047 (cs.AI) | 19 Aug | Wong et al. ("Eureka") | An agentic system; positivity of Suzuki's localised Weil form for a ≤ 0.345 |
| 2608.24827, 2605.20224, 2609.04908 | Aug–Sep | Zhu; Groskin; Shi | Weil positivity and truncated Weil form numerics |

**Papers citing Wang.** Our bibliography's Wang is Biao Wang, arXiv:2609.24167.
- Semantic Scholar lists no papers citing it.
- The only citing works found are the Santibáñez-Leal Zenodo notes, all about ζ.
- Wang's companion paper 2609.07918 is cited by 2609.24167 and by those notes, but not by us.

## 4. Recommended bibliography and related-work additions

**(a) CKLT26: add.** Put it in Table 1, or in footnote (b) with CIS13 and Sono25. Suggested wording:
"Conrey–Kwan–Lin–Turnage-Butterbaugh [CKLT26] obtain, by Levinson's method and a refined asymptotic large sieve, at
least 1/3 simple critical zeros for the family of twists of a fixed GL(2) form by primitive χ with q ≤ Q (and 1/9
critical zeros for GL(3)), for |γ| ≤ Q^ε."

Verbatim from the abstract: "we use Levinson's method to prove that, as $Q\to\infty$, at least $1/9$ of the zeros of
the $L$-functions $L(s,\Pi_0\times\chi)$ lie on the critical line, where $\chi$ ranges over the family of primitive
Dirichlet characters of conductor up to $Q$."

Verbatim from Cor. 1.14 (PDF): "at least 1/3 − O(ϵ) of the zeros … with 0 ≤ β ≤ 1 and |γχ| ≤ Q^ϵ of the L-functions
L(s, Π × χ) lie on the critical line and are simple". The checking agent re-read this in the PDF text; the family is
χ primitive mod q, (q, q_Π) = 1, q ≤ Q.

```bibtex
% VERIFIED via arXiv abs page + PDF (arXiv:2607.00282v1, 1 Jul 2026; 80 pages; Cor. 1.1, Cor. 1.14).
@misc{CKLT26,
  author        = {Conrey, Brian and Kwan, Chung-Hang and Lin, Yongxiao and Turnage-Butterbaugh, Caroline L.},
  title         = {Critical zeros and unconditional mean value theorems for twisted {$\mathrm{PGL}(2)$} and {$\mathrm{PGL}(3)$} {$L$}-functions},
  year          = {2026},
  eprint        = {2607.00282},
  archivePrefix = {arXiv},
  primaryClass  = {math.NT},
  note          = {arXiv:2607.00282v1}
}
```

**(b) Wang, short intervals: add.** Put it next to Wang26 in the ζ-barrier paragraph (§7.3) or in Table 1. Suggested
wording: "…and, in short intervals (T, T+T^θ], an explicit proportion c(θ) [Wang26b]".

```bibtex
% VERIFIED via arXiv OAI-PMH metadata + PDF (arXiv:2609.07918v1, 7 Sep 2026; 13 pages; Theorem 1.1).
@misc{Wang26b,
  author        = {Wang, Biao},
  title         = {Simple critical zeros and distinct zeros of the {R}iemann zeta-function in short intervals},
  year          = {2026},
  eprint        = {2609.07918},
  archivePrefix = {arXiv},
  primaryClass  = {math.NT},
  note          = {arXiv:2609.07918v1}
}
```

**(c) Optional: BGSTB25 (conditional ζ "Pair correlation I", next to BGSTB24) and Pru26b.**

```bibtex
% VERIFIED via arXiv abs page (arXiv:2501.14545v3, 1 Sep 2026; comments: under review, submitted 10 Jun 2026).
@misc{BGSTB25,
  author        = {Baluyot, Siegfred Alan C. and Goldston, Daniel Alan and Suriajaya, Ade Irma and Turnage-Butterbaugh, Caroline L.},
  title         = {Pair correlation of zeros of the {R}iemann zeta function {I}: proportions of simple zeros and critical zeros},
  year          = {2025},
  eprint        = {2501.14545},
  archivePrefix = {arXiv},
  primaryClass  = {math.NT},
  note          = {arXiv:2501.14545v3 (revised 1 September 2026)}
}

% VERIFIED via Zenodo REST API (record 22096771; concept DOI 10.5281/zenodo.22096770; 25 Aug 2026). Unrefereed.
@misc{Pru26b,
  author       = {Pr{\"u}zelius, Fredrik},
  title        = {A {C}arleman window class for the height floor in {H}ua--{Y}ang, ar{X}iv:2608.16034: explicit cutoffs, the {F}ourier--{L}aplace estimate, and the modified {P}roposition 9.2},
  howpublished = {Zenodo technical note},
  year         = {2026},
  month        = aug,
  doi          = {10.5281/zenodo.22096771}
}
```

**(d) Optional: one sentence in §7.3.** Suggested wording: "Several unrefereed Zenodo preprints claim further small
improvements for ζ by refining the finite certificate (the largest we saw is 0.67348 [Geb26])." Add it only to
pre-empt a referee question.

```bibtex
% VERIFIED via Zenodo REST API (record 22646541; concept DOI 10.5281/zenodo.22643956; 7 Sep 2026). Unrefereed; claim not checked.
@misc{Geb26,
  author       = {Gebendorfer, Jonas Jakob},
  title        = {An expanded window and joint position pressures for simple critical-line zeros},
  howpublished = {Zenodo preprint},
  year         = {2026},
  month        = sep,
  doi          = {10.5281/zenodo.22646541}
}
```

**(e) Housekeeping.** PC26, Ji26, Anth26, CIS-ALS, Wu16, DPR23 and seven classical entries are in `refs.bib` but never
cited, so they will not print.
- CIS-ALS is the natural companion to CIS13 and to the asymptotic large sieve used by CKLT26.
- Anth26 fits the AI-use statement.
- Wu16 (distinct zeros in the Dirichlet family) arguably belongs in Table 1.

## 5. Does anything strengthen the sieve-centred framing?

**Yes, three things do.**
1. **HY26b builds the bandwidth cap into its main theorem** (λbw := min{1, …}). A single prime modulus has only q
   harmonics, which matches our §7.3 explanation that the barrier at bandwidth 1 comes from the length term of the
   large sieve.
2. **CKLT26 is an independent 2026 unconditional q-family simple-critical result.** Its key new input is a
   refinement of the (asymptotic) large sieve. So family proportions are large-sieve-driven in both the Levinson
   route and the pair-correlation route.
3. **The ζ-only certificate refinements have stalled.**
   - About a dozen Zenodo refinements in Aug–Sep move 0.6725 by at most +0.001.
   - Devine claims the fixed MT kernel "with pure Gram/rank machinery cannot force a bound above 0.6736". Tyagi's
     no-go points the same way.
   - The certificate side looks nearly saturated. The large gain from 0.6725 to 0.9322 comes from the prime-side
     large-sieve input.

**Extension risk.** Those certificate refinements are independent of our contribution. Someone could combine them with
our bandwidth-2 family bound and push slightly past pC(1) = 0.9322. That would be a follow-up, not a pre-emption.

## 6. What could not be checked

- **General web search was unavailable.** Google Scholar is blocked, and Bing and DuckDuckGo
  are unusable from this host. Blogs, institutional pages, talk abstracts, ResearchGate, SSRN and HAL were not
  searched, except where OpenAlex indexes them.
- **arXiv coverage runs through the Fri 25 Sep 2026 announcement.**
  - Submissions made 24–27 Sep that appear in the Mon 28 Sep listing or later are not covered.
  - That listing is announced Sunday at 20:00 ET, after this check.
  - Submissions not yet announced cannot be seen at all.
- **Citation graphs lag.**
  - Semantic Scholar citations may lag by days or weeks, and its keyword search was mostly rate-limited.
  - OpenAlex has no citation links for arXiv preprints.
  - A family paper that cites AF26 without family keywords in its title or abstract could be missed; the harvest regex
    did cover abstracts and comments.
- **Zenodo search covers metadata and descriptions only**, not PDF text. A family result inside a ζ-titled Zenodo PDF
  would be missed. The Zenodo ζ claims were not verified.
- **Full texts read:** 2609.07918; 2609.24167; 2607.00282 (introduction and corollaries); 2609.27808 (abstract and
  introduction); 2609.25885 (§1); two Santibáñez-Leal notes. Everything else was judged from abstracts and
  descriptions.
- **Not searched:** non-English venues (CNKI, Russian journals), and journal issues without a preprint beyond what
  OpenAlex covers.
- **Papers from before late July were checked only by spot queries.** The OAI harvest starts at datestamp 2026-07-25.
  Earlier items such as 2607.00282 were found through Semantic Scholar and arXiv API queries, not a systematic sweep.
- **Recommended re-check:** run the arXiv part again after the Mon 28 Sep listing, and again just before submission.

## 7. Applied

- Added CKLT26 and Wu16 to Table 1 and its footnote (b). Wu16 was already in `refs.bib` but not cited; it is an
  unconditional family result, 0.6024 simple and 0.8012 distinct, via the asymptotic large sieve.
- Added CIS-ALS to footnote (b), CKLT26 to the Levinson comparison, and Wang26b to the ζ sentence of §7.3.
- Removed the other 10 uncited `refs.bib` entries. Anth26 is kept, available for the AI-use statement.
- The optional BGSTB25, Pru26b and Geb26 were not added.
