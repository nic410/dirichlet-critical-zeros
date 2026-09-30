# Reading guide for a technical reviewer

This guide is for a reader who wants to check the mathematics or the formalisation. It assumes familiarity with
analytic number theory (explicit formulae, large sieve, pair correlation). Page numbers refer to the 74-page build
`paper/main.pdf`; section and theorem numbers are the paper's. If the PDF is rebuilt after edits, page numbers may
shift by a page or so; section and theorem numbers should not.

Status reminder: the text, proofs and formalisation were produced by AI agents (Claude). No human mathematician has
yet checked the proofs line by line. See `VERIFICATION.md` for what has been checked and how.

## 1. Structure of the paper

| § | Title | Page | What it does |
|---|---|---|---|
| 1 | Introduction | 2 | Statements (§1.1), context table (§1.2, p. 5), relation to previous large-sieve work (§1.3, p. 6), what is claimed and what is not (§1.4, p. 8), the method (§1.5, p. 8), organisation and a dependency table (§1.6, p. 10) |
| 2 | Setup and notation | 10 | The weighted family, the masses H and W, parameters and their order, the window/lattice, the explicit formula on the test class, the Gabor matrix, the second-moment kernels |
| 3 | The positivity certificate | 14 | Block structure (Lemma 3.1), rank–trace inequality (Lemma 3.2), per-character certificate (Prop. 3.3), zero-side reduction (Prop. 3.6) |
| 4 | The zero side | 15 | Weighted Riemann–von Mangoldt, family pointwise bound, finite centres (Prop. 4.4), trace (Prop. 4.6), exceptional characters via Montgomery's zero-density theorem (Lemma 4.7), exterior tail (Prop. 4.8) |
| 5 | The prime side | 19 | Decomposition of the second moment; flattening (Lemmas 5.6 "B1" and 5.7 "B2", pp. 22–23); time localisation (Lemmas 5.9–5.11 "M1–M3", pp. 24–25); the time-integrated majorant (Prop. 5.12); the conditional form (Hypothesis 5.15, Theorem 5.16, p. 26) |
| 6 | The two large-sieve constants | 27 | §6.1 (p. 27): Gauss-sum transfer and a sharp weighted Farey large sieve (Lemma 6.5 = "Lemma A", p. 30; Cor. 6.8). §6.2 (p. 33): exact Toeplitz identity on Q-rough vectors (Lemma 6.13), positive majorant (Lemma 6.17), local densities (Def. 6.18, Lemmas 6.19–6.20 = "Lemma C"), sharp large sieve (Prop. 6.21, p. 38), C_T⁺ → 1 (Lemma 6.22), fixed-η reduction (Prop. 6.23), the band device (Prop. 6.24, p. 40) |
| 7 | The variational problem and the certified constants | 43 | p(C), Lipschitz bound (Lemma 7.1), realisation by windows (Lemma 7.2), rational certificates (Prop. 7.3, p. 43), assembly and order of limits (§7.3) |
| 8 | Remarks | 45 | Limits of the method, which ingredient gives what, the ζ barrier, individual L-functions and the weights, higher zeros, relation to Alpöge–Furman Remark 7.2 (§8.6), "Is 93% plausible?" (§8.7), comparison with GRH results |
| 9 | Zeros at polynomial height | 47 | Setup at height T (§9.1), zero side (§9.2), prime side (§9.3; Lemma 9.13 tails by dyadic shells, Prop. 9.18 sharp majorant at height T, p. 57), variational problem at support λ̄ and proofs (§9.4; certificates Prop. 9.24, p. 60), a sharp hybrid large sieve and the ceiling (§9.5, not used in proofs), remarks (§9.6) |
| – | AI-use statement | 64 | How the paper was produced, and the author's verification and responsibility statement |
| A | Numerical computations | 64 | Certificates (A.1), Farey and Toeplitz constants (A.2), sanity checks (A.3), **what has been checked by machine (A.4, p. 66)**, numerical constants (A.5) |
| B | Proofs of the ported lemmas | 71 | The explicit formula (B.1), the rank–trace inequality (B.2); with §§2–4 these make the paper independent of the cited sources for correctness |
| – | References | 73 | |

## 2. The main theorems

Notation (§1.1, p. 2). Q → ∞, ℓ = log Q. For 0 < η < 1/2 and an admissible weight w (bounded variation,
supp w ⊂ [η, 1], ∫₀¹ u w(u) du > 0), the family F consists of the primitive characters χ mod q with w(q/Q) > 0, and
χ mod q has weight ω_χ = w(q/Q)·q/φ(q). The two "log-wide" weights are

- w_η(u) = u⁻² 1_[η,1](u) (sharp; χ mod q then has weight Q²/(qφ(q))), and
- w_η^sm(u) = u⁻² sin²(π log u / log η) 1_[η,1](u) (smooth).

For I = (T, 2T], N_χ counts zeros of L(s, χ) with γ ∈ I with multiplicity; N^s_{0,χ} counts those that are simple
with β = 1/2; N^*_{0,χ} counts distinct zeros with β = 1/2; N_{d,χ} counts distinct zeros. N, N^s_0, N^*_0, N_d are
the ω-weighted sums over F. With F_C(α) = α on [0, 1] and C on (1, 2],

p(C) := 2 − inf { ∫f² + ∬ f(x)f(y)F_C(|x−y|) dx dy : f ≥ 0 even, supp f ⊂ [−1, 1], ∫f = 1 }.

Prop. 7.3 gives p(1) ≥ 0.932282 and p(1.2688) ≥ 0.885912 by exact rational evaluation at explicit step functions.

**Theorem 1.1 (Main theorem, p. 2).** Fix 0 < a₀ < A₀. For every ε > 0 there is η₀(ε) > 0 such that for every
η ∈ (0, η₀] and w ∈ {w_η, w_η^sm},

liminf_{Q→∞} inf_{ℓ^{a₀} ≤ T ≤ ℓ^{A₀}} N^s_0/N ≥ p(1) − ε ≥ 0.9322 − ε,

the same holds for N^*_0/N, and liminf inf_T N_d/N ≥ (1 + p(1))/2 − ε ≥ 0.9661 − ε.

**Theorem 1.2 (Gauss-transfer bound, p. 3).** With C_G = 6/(π²ℰ) ≈ 1.2687739, ℰ = ∏_p(1 − p⁻² − p⁻³): the same
conclusions with p(1) replaced by p(C_G) ≥ 0.885912, i.e. N^s_0/N ≥ 0.8859 − ε and N_d/N ≥ 0.9429 − ε; more generally
liminf inf_T N^s_0/N ≥ p(C_G R_w) for every admissible w, with an explicit Farey constant R_w ≥ 1.

**Theorem 1.3 (Fixed η, p. 3).** For w = w_η^sm: at η = 10⁻³, C_T⁺(w) ≤ 1.0911 and N^s_0/N ≥ 0.9155 in the limit;
at η = 10⁻⁴, C_T⁺(w) ≤ 1.0434 and N^s_0/N ≥ 0.9241; on the Gauss route at η = 10⁻³, 10⁻⁴, 10⁻⁵, R_w ≤ 1.0599,
1.0289, 1.0159 and N^s_0/N ≥ 0.8744, 0.8802, 0.8827. The constants C_T⁺(w) and R_w are bounded by interval
arithmetic.

**Theorem 1.4 (Polynomial height, p. 4).** Put ℓ_* = log(QT), λ̄(κ) = (2+κ)/(1+κ), λ̄_T = λ̄(log T/log Q), and let
p(λ̄; F) be the analogue of p(C) with supp f ⊂ [−λ̄/2, λ̄/2]. Fix a₀ > 0, κ₁ > 0.
(a) Sharp route: for every ε > 0 there is η₀(ε), independent of a₀ and κ₁, such that for η ≤ η₀ and
w ∈ {w_η, w_η^sm}, liminf_Q inf_{ℓ^{a₀} ≤ T ≤ Q^{κ₁}} (N^s_0/N − p(λ̄_T; F₁)) ≥ −ε; likewise for N^*_0/N, and
for N_d/N with (1 + p(λ̄_T; F₁))/2.
(b) Gauss route, with F_{C_G R_w}, for fixed η and admissible w.
(c) Classical route, with C_cl(w) = w_max/(ℰ ∫uw), using only flattening, time localisation and the classical large
sieve.

**Corollary 1.5 (dyadic family, p. 4).** For conductors q ∈ [Q/2, Q] with weights q/φ(q): at least 0.7224, 0.7203,
0.7102 (minus o(1)) for T ≤ Q³, Q⁵, Q¹⁰.

The κ-table after Theorem 1.4 (p. 4) gives, for column (a): 0.932282 (κ = 0), 0.912574 (1/4), 0.894985 (1/2),
0.865673 (1), 0.824355 (2), 0.797213 (3), 0.764149 (5), 0.727484 (10). As κ → ∞ the constant decreases to the
Montgomery–Taylor value 0.6725... . All entries are exact rational certificates at 400-cell step functions
(Prop. 9.24).

Read §1.4 (p. 8) before anything else: it states precisely what is and is not claimed (weighted averages only;
the height ranges; nothing about individual L-functions; lower bounds only; unconditional; not RH-moving; the three
kinds of verification).

## 3. The key ideas: what is new and what is classical

The paper's own account is §1.3 (p. 6) and §1.5 (p. 8). In brief:

**Inherited.** The positivity certificate is that of Alpöge–Furman (ζ) and Hua–Yang (Dirichlet characters modulo one
large prime): a finite Gabor compression of Weil's Hermitian form, with inertia (off-line zero pairs give blocks with
at most one positive eigenvalue) and a rank–trace inequality turning the trace and Frobenius norm into a lower
bound for simple critical zeros, character by character (§3). Because the certificate is linear and holds for each
character, it can be summed with any nonnegative weights. In those works the bandwidth is at most 1, which gives the
Montgomery–Taylor constant 0.6725. The constant p(1) = 0.9322... itself is Sono's GRH constant for a related
statistic of low-lying zeros (it is what the form factor min(α, 1) gives on [0, 2], with test functions supported
there). It is not the best GRH constant for that statistic: Chirre, Gonçalves and de Laat (Adv. Math. 2020,
Theorem 5) obtained 0.9350 under GRH with test functions that are not supported in [−2, 2] (paper §1.1, §8.8). The
paper does not claim the constant as new.

**The step to bandwidth 2.** The certificate needs only an **upper** bound for the family pair-correlation form, and
an upper bound for a positive semidefinite form is what a large sieve gives. Three devices make it sharp enough up
to bandwidth 2:

1. *Flattening* (§5.6–5.7): subtracting a truncated divisor sum Λ_R from Λ changes no family character sum by more
   than O(Q^{−A}) (B1) but lowers the mean square from log n to about log Q (B2). This produces the plateau
   min(α, 1).
2. *Time localisation* (Lemmas 5.9–5.11): localising |log(n/m)| ≲ T^{−1/2} costs O(T^{−1/4}) and reduces to large
   sieve constants on short intervals; below Q^{1−ε} the constant is exactly 1.
3. *A sharp constant on (1, 2)* (§6): for vectors supported on Q-rough integers (all prime factors > Q), the family
   form is exactly a Toeplitz form attached to a signed Farey measure (Lemma 6.13). Adding an explicit positive
   majorant of its negative part gives a positive semidefinite Toeplitz form T^♮ defined on **all** vectors
   (Lemma 6.17), whose normalised constant C_T⁺(w) on intervals of length ≤ Q^{2−ε} is a supremum of explicit local
   densities (Lemma 6.20, Prop. 6.21) and tends to 1 for log-wide weights (Lemma 6.22: C_T⁺ ≤ 1 + 42/log(1/η) sharp,
   1 + 83/log(1/η) smooth). The flattened vector is not Q-rough; the band device (Prop. 6.24) applies the identity
   to the rough part of the *unflattened* localised vector and only then, inside T^♮, swaps in the flattened
   coefficients, bounding low-denominator resonances by the additive large sieve and high denominators by Poisson.

The bandwidth barrier at 2 is the classical one: beyond Q² the length term of the large sieve dominates the family
mass H ≍ Q² (§8.1).

**What the paper claims as new** (§1.3, verbatim in substance): (i) the explicit normalised local profile of the
signed Farey measure, uniformly over finite sets of primes; the explicit positive majorant giving a positive
semidefinite all-vector Toeplitz form; and its constant tending to 1 for log-wide weights; (ii) the transfer to the
flattened vector described above. **What it does not claim as new**: the Toeplitz identity on sifted vectors (the
invertible-class case of Ramaré's identity, which yields the Bombieri–Davenport inequality; the paper's Lemma 6.13
is its weighted, signed form), the duality and Schur-test argument, rational approximation and spoke counting
(Wolke, Baier), the Gauss-sum transfer, and the approximant Λ_R (Selberg, Goldston, Goldston–Yıldırım, Vaughan).
The paper says its literature search was targeted, not exhaustive.

**The extension to polynomial height** (§1.5 last paragraph, §9). At height T the relevant log-conductor is
ℓ_* = log(QT). Three changes carry the argument to every bandwidth λ < λ̄_T: all densities are measured in units of
ℓ_*; the time localisation is at scale T^{−1+ε₅} instead of T^{−1/2}, so that the large sieve on intervals of at
most Q^{2−ε} integers reaches n ≤ Q^{2−ε}T^{1−ε₅} (this converts height into bandwidth, as in Gallagher's hybrid
large sieve); and the localisation tails are bounded by dyadic shells and the classical large sieve (Lemma 9.13). The
large-sieve constants of §6 are used verbatim. Prop. 9.30 shows that λ̄_T is the ceiling for worst-case bounds.

## 4. Where the Lean headlines live and how they map to the paper

| Paper | Lean theorem | Lean statement | Files |
|---|---|---|---|
| Theorem 1.1, with p(1) ≥ 0.932282 | `Families.thmMain` | `Families.thmMain_Statement` | statement `lean/Families/Main.lean`; theorem `lean/Families/Headline.lean` |
| Theorem 1.4(a), with column (a) of the κ-table at κ = 1, 2, 3, 5, 10 | `Families.Hybrid.thmH` | `Families.Hybrid.thmH_Statement` (includes `certH_Statement`) | `lean/FamiliesH/Main.lean`, `lean/FamiliesH/Statements.lean`, `lean/FamiliesH/Headline.lean` |

Both are proved with no hypotheses; `#print axioms` gives only `propext`, `Classical.choice`, `Quot.sound`.
`lean/FamiliesH/StatementCheck.lean` proves that the Theorem 1.4(a) statement implies the Theorem 1.1 statement.

**How the Lean statements differ in form from the paper** (all documented in `lean/STATEMENTS.md` and
`lean/STATEMENTS-H.md`, and examined in the audits in `review-records/`):

- The liminf is written without division: for every δ > 0 there is Q₀ such that for all Q ≥ Q₀ and all T in the
  range, (p − ε − δ)N ≤ N^s_0, and similarly for N^*_0 and N_d. Both audits compiled a proof that, because N > 0
  eventually and uniformly in T, this is equivalent to the ratio form. These proofs now ship with the project:
  `lean/scripts/NonVacuity.lean`, run by `scripts/audit.sh`, proves N > 0 eventually and uniformly in T for both
  height ranges (`Nfam_pos_main`, `Nfam_pos_hybrid`) and derives the ratio form of both headlines (`thmMain_ratio`,
  `thmH_ratio`).
- For N_d the Lean bound is (1 + p)/2 − ε/2 − δ, slightly *stronger* than the paper's −ε.
- The family in Lean is all primitive χ mod q with 1 ≤ q ≤ ⌊Q⌋, weighted by w(q/Q)q/φ(q); the weight vanishes
  outside ηQ ≤ q ≤ Q, so the effective family is the paper's.
- L(s, χ) is Mathlib's analytically continued Dirichlet L-function; multiplicity is the analytic order.
- Only rows κ = 1, 2, 3, 5, 10 of column (a) are part of the Lean statement (row κ = 0 is Theorem 1.1's constant);
  rows κ = 1/4, 1/2 and columns (b), (c) and the dyadic column are not formalised.

**How the formal proof relates to the written one.** The paper (Appendix A.4, p. 66) says the formal proof follows the
written proof and assumes none of its steps; where it deviates it uses weaker inputs, e.g. the large sieve with a larger
absolute constant (in Lean the constant is 17/4), and a Montgomery-type zero-density estimate with a smaller exponent, proved only for
heights up to Q (the only range used). Weil's explicit formula, zero counting, Stirling bounds, a prime number theorem
with error term and the rank–trace linear algebra come from the `zeta23` dependency (Anthropic's Lean formalisation of
Alpöge–Furman).

**Not formalised** (present in Lean only as `Prop` definitions `*_Statement`, marked "Stated only; not proved in this project"; neither
headline depends on them): Theorems 1.2 and 1.3, the conditional theorem (Theorem 5.16), Lemma A (Lemma 6.5) and a
few lemmas used only on the Gauss route or at fixed η. Theorem 1.4(b), (c) and Corollary 1.5 are not stated in Lean
at all.

## 5. Suggested order of checking for a specialist

1. **Scope.** §1.1 and §1.4 (pp. 2–8). Decide whether the weighted statistic and height ranges are of interest; the
   weights are essential to the constants (§8.4).
2. **Statement correspondence.** If you accept the Lean kernel, the most efficient check of Theorems 1.1 and 1.4(a)
   is to read `lean/STATEMENTS.md` / `STATEMENTS-H.md` against §1.1, and the two statement audits in
   `review-records/`. The audit of Theorem 1.4(a) was done only by Claude; an independent audit of that statement
   would add most value per hour.
3. **The new analytic core** (the parts every reviewer flagged as most important for a human specialist; see the
   internal referee's "what a human specialist must check" list, summarised in `VERIFICATION.md` §4):
   - §6.2, Lemmas 6.19–6.20 and Prop. 6.21 (pp. 35–38), with the duality lemma 6.2 (p. 28): the spoke count with the
     coprimality twist, the combination of signed main terms, isolated-point bounds, the duality constant. This is
     the only input that moves 0.8859 to 0.9322.
   - Prop. 6.24, Step 4 (pp. 40–42): the swap inside T^♮; invisibility used before localisation; the Q-rough split;
     the level split and prime-power remainder.
   - Flattening, Lemmas 5.6–5.7 (pp. 22–24): the Poisson bookkeeping and the fact that the B2 density is only an
     upper bound.
4. **The zero side**, §4 (pp. 15–19) and Appendix B (pp. 71–73): finite centres, exterior tail, deletion of
   exceptional characters. Check Montgomery (Invent. Math. 8 (1969), Theorem 1) in the source.
5. **Assembly and order of limits**, §7.3 (p. 44) and, for §9, §9.4 (p. 59). The §9 draft had an order-of-limits
   slip (ε₅ fixed before ε), found by two referees and repaired; check the repaired order.
6. **Polynomial height**, §9.3 (pp. 52–59): Lemma 9.13 and Prop. 9.18. The independent review of §9 re-derived these
   but did not re-derive the §6.2 lemmas that §9 reuses.
7. **Numerics.** Appendix A and `paper/anc/README.md`. Low stakes: exact rational and interval arithmetic,
   reproduced by independent implementations.
8. **Literature and priority.** §1.2–1.3 and `REFERENCES.md`. The searches were targeted, not exhaustive.

## 6. Known weak points to examine first

Collected from the review records (details and verdicts in `VERIFICATION.md`):

- **The sharp large sieve and its application (§6.2, Prop. 6.24).** This is the principal new mathematics and the
  part every independent review singled out for human scrutiny. The Gauss route (Theorem 1.2) is a fallback that
  avoids Lemma C and Prop. 6.24, but it shares the zero side, flattening, time localisation and parts of §6.1, so it
  is not an independent verification of everything.
- **Written proofs of Theorems 1.2, 1.3, 1.4(b), 1.4(c), Corollary 1.5** are not formalised. Lemma A (Lemma 6.5) and
  the fixed-η reduction (Prop. 6.23) rest on the written proofs and certified numerics only.
- **Statement faithfulness of Theorem 1.4(a)** has been audited only by Claude.
- **Uniformity and limits.** The 93% needs log(1/η) ≥ 3.7·10⁴ (smooth weight) by the proved rate; no effective Q
  is given. At polynomial height, for κ₁ = 10 the tail term is below 10⁻² only once log T ≥ 1.27·10⁵ (p. 5).
- **Comparison with Alpöge–Furman Remark 7.2** (§8.6, p. 46): the announcement of 0.811 (other weights, bandwidth
  3/2) gives no details; the paper records that with its own weights and method the corresponding computation, an
  uncertified floating-point one, gives a different constant, does not pursue the comparison and uses it in no proof.
  A specialist should decide what, if anything, to say about it.
- **Priority.** Literature checks found no pre-emption, but they were targeted. The paper's claim at polynomial
  height ("no unconditional bound above 2/3 ... at height polynomial in the conductor") carries an explicit exception
  for Hua–Yang at T = q^θ with θ below about 0.0085, which the paper states.
