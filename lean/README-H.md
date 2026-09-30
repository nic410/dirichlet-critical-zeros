# FamiliesH: a Lean 4 formalisation of Theorem 1.4(a) (the families theorem at polynomial height)

This is a Lean 4 / Mathlib formalisation of the polynomial-height theorem for families of Dirichlet L-functions,
sharp route:
Theorem 1.4(a) of the paper (label `thm:poly`, proof in §9), together with column (a) of the κ-table after it.

It is the library `FamiliesH` of this Lake project. It imports the library `Families` (the formalisation of the
paper's Theorem 1.1, headline `Families.thmMain`) and uses it **unchanged**. `README.md` is the overview of both;
build and audit instructions are there.

**Numbering.** Theorem, section and equation numbers in this file, in `STATEMENTS-H.md` and in the `FamiliesH`
docstrings are those of the paper. The `H` in Lean names (`thmH`, `lem:B1H`, `prop:TIsharpH`, …) marks the
polynomial-height ("hybrid") versions of the results of §§2–7; the table at the top of `STATEMENTS-H.md` maps
these names to the paper's numbers (for example `thmH` = Theorem 1.4(a), `prop:certH` = Proposition 9.24).

**Status.** `Families.Hybrid.thmH : Families.Hybrid.thmH_Statement` is proved **with no hypotheses**, and

```
#print axioms Families.Hybrid.thmH
'Families.Hybrid.thmH' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only Lean's three standard axioms appear, so nothing `thmH` depends on uses `sorry` or `native_decide`
(`Lean.ofReduceBool`), in this library or in its dependencies. The library itself contains no `sorry`: the audit
finds 0 sorry roots and no declaration depending on `sorryAx`. It has no `axiom` declarations and no
`native_decide`.

## What is proved

**The theorem, in the paper's notation.**
- Let `Q → ∞`, `ℓ = log Q`. The family is as for Theorem 1.1: the primitive characters `χ mod q`, `1 ≤ q ≤ Q`, with
  weights `ω(q) = w(q/Q)·q/φ(q)` and `w ∈ {w_η, w^sm_η}` (the log-wide sharp and smooth weights of Theorem 1.1).
- For a height `T`, `N`, `N^s_0`, `N^*_0` and `N_d` are the weighted counts of Theorem 1.1 for the zeros with
  `T < γ ≤ 2T`: all zeros, simple zeros on the line, distinct zeros on the line, distinct zeros.
- Put `κ_T = log T/log Q` and `β(κ) = (2+κ)/(1+κ)`. (Notation: β in Lean = λ̄ in the paper; the paper writes
  `λ̄(κ)`, `λ̄_T` and `p(λ̄; F)`. The Lean identifiers keep `β`.) For `β ∈ [1,2]` let

```
p(β) = 2 − inf { ∫ f² + ∬ f(x) f(y) F₁(|x − y|) dx dy : f ≥ 0 even, f ∈ L², supp f ⊂ [−β/2, β/2], ∫ f = 1 },
```

  where `F₁(α) = α` for `α ≤ 1` and `F₁(α) = 1` for `α > 1`. So `p(2)` is the constant `p(1) ≥ 0.932282` of Theorem 1.1.

> **Theorem 1.4(a) (sharp route).** Fix `a₀ > 0` and `κ₁ > 0`. For every `ε > 0` there is `η₀(ε) > 0`,
> **independent of `a₀` and `κ₁`**, such that for every `η ∈ (0, η₀]` and `w ∈ {w_η, w^sm_η}`:
> * `liminf_{Q→∞} inf_{ℓ^{a₀} ≤ T ≤ Q^{κ₁}} (N^s_0/N − p(β(κ_T))) ≥ −ε`;
> * the same bound holds for `N^*_0/N`;
> * the same holds for `N_d/N` with `(1 + p(β(κ_T)))/2` in place of `p(β(κ_T))`.
>
> Moreover `p(β(κ)) ≥ 0.865673, 0.824355, 0.797213, 0.764149, 0.727484` at `κ = 1, 2, 3, 5, 10`.

In particular, for `T = Q^κ` the proportion of simple zeros on the line is at least
`p((2+κ)/(1+κ)) − ε − o(1)`.

**The κ-table constants** are exact rational certificates at `n = 400`, checked by the Lean kernel
(`decide +kernel` on generated integer data, `FamiliesH/V/CertData.lean`; no `native_decide`). They are `0.865673, 0.824355, 0.797213, 0.764149, 0.727484`.
The paper's table (after Theorem 1.4) prints exactly these values, noting that finer `n = 800` step functions give
values at most `10⁻⁶` higher; the `n = 800` values are not covered by the Lean proof.

**The Lean statement** is `Families.Hybrid.thmH_Statement` (`FamiliesH/Main.lean`):

```lean
def thmH_Statement : Prop :=
  (∀ ε : ℝ, 0 < ε → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ (a0 κ1 : ℝ), 0 < a0 → 0 < κ1 →
    ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ W : Weight, (W.w = wSharpFun η ∨ W.w = wSmoothFun η) →
      ProportionsAtLeastH W a0 κ1 (fun κ => pB (betaK κ) 1 - ε)) ∧
  certH_Statement

def certH_Statement : Prop :=
  (0.865673 : ℝ) ≤ pB (3 / 2) 1 ∧ (0.824355 : ℝ) ≤ pB (4 / 3) 1 ∧ (0.797213 : ℝ) ≤ pB (5 / 4) 1 ∧
  (0.764149 : ℝ) ≤ pB (7 / 6) 1 ∧ (0.727484 : ℝ) ≤ pB (12 / 11) 1
```

`ProportionsAtLeastH W a0 κ1 p` writes the three `liminf` bounds without division, with the target evaluated at
`κ_T` inside the `T`-quantifier:

```
∀ δ > 0, ∃ Q₀, ∀ Q ≥ Q₀, ∀ T ∈ [ℓ^{a0}, Q^{κ1}]:
  (p(κ_T) − δ) N ≤ N^s_0,  (p(κ_T) − δ) N ≤ N^*_0,  ((1 + p(κ_T))/2 − δ) N ≤ N_d.
```

The theorem `Families.Hybrid.thmH` is in `FamiliesH/Headline.lean`.

| Paper | Lean | File |
|---|---|---|
| `κ_T`, `β(κ)`, `ℓ_* = log(QT)` | `kappaT`, `betaK`, `ellS` | `FamiliesH/Basic.lean` |
| admissible `f` at support `β`; `p(β; F_C)` | `AdmissibleWindowB`, `pB β C` (`Qf`, `FC` from `Families`) | `FamiliesH/Basic.lean` |
| heights `ℓ^{a₀} ≤ T ≤ Q^{κ₁}`; the three bounds | `Set.Icc (Real.log Q ^ a0) (Q ^ κ1)`; `ProportionsAtLeastH` | `FamiliesH/Basic.lean` |
| family, `ω(q)`, `w_η`, `w^sm_η`, `L(s,χ)`, multiplicities, `N`, `N^s_0`, `N^*_0`, `N_d` | `Weight`, `Weight.omega`, `wSharpFun`, `wSmoothFun`, `Lfun`, `mult`, `Nfam`, `Ns0`, `Nstar0`, `Nd` | reused verbatim from `Families` |

`STATEMENTS-H.md` gives the definition-by-definition correspondence and 11 faithfulness notes.

**Checked links to Theorem 1.1.**
- `thmMain_of_thmH : lemMbeta_Statement → thmH_Statement → Families.thmMain_Statement` is proved, and
  `lemMbeta_Statement` is proved too. So in Lean the polynomial-height theorem implies the audited
  headline of Theorem 1.1.
- `pB_two : pB 2 C = Families.pC C`.
- `kappaT_rpow : κ_{Q^κ} = κ`.

## What the proof uses

The proof is the glue `thmH_of_parts` (`FamiliesH/Glue.lean`), applied to the 15 component theorems of
`FamiliesH/Components.lean`.
- **The glue.** `thmH_of_cells` is the κ-cells argument: one-cell theorems for the cell tops `jκ₁/m`, together
  with `lem:Mbeta`. `thmHcell_of_parts` is the one-cell theorem, the port of `Families.thmMain_of_parts`.
- **The components** are proved in five packages:

| Package | Components (paper numbering) | Folder |
|---|---|---|
| V | `lem:Mbeta` (Lemma 9.21), `lem:pLipH` (Lemma 9.22), the limit step (§9.4, with Lemma 9.23), the certificates (Proposition 9.24) | `FamiliesH/V/` |
| F | sizes (Lemma 9.1), flattening (`lem:B1H`, `eqB:MratH`, `lem:B2H`: Lemmas 9.11, 9.12), time localisation (`lem:M1H`, `lem:M3H`(iii), §9.3), tails (Lemma 9.13, Corollary 9.14) | `FamiliesH/F/` |
| Z | the zero side (Proposition 9.9, Lemma 9.2 lower half), unconditional | `FamiliesH/Z/` |
| S | the second moment (Proposition 9.19 via Lemma 9.10) | `FamiliesH/S/` |
| TS | the band device (Proposition 9.18) | `FamiliesH/TS/` |

**Reused from the library `Families`, unchanged:**
- `lem:CTlimit`, `prop:sharpLS`, `lem:WH`;
- the Montgomery–Vaughan large sieve (`Families.Hyp.MV_LargeSieve_proof`, constant `17/4`) and the Stirling
  bounds;
- the definitions of the family, the weights, `Δ`, the forms, the zero counts and the quadratic form.

These classical inputs are theorems there, so `thmH` has no hypotheses. The module docstrings of each package
describe its proof, including the places where the Lean route differs in detail from the paper's: the trace prime
term (Z), the mixed term of the second moment (S), and the prime-power and Farey bookkeeping (TS).

## What is not formalised

- **The Gauss and classical routes.** Theorem 1.4(b), (c) are not stated.
- **The dyadic family.** Corollary 1.5 is not stated.
- **The rows κ = 1/4 and κ = 1/2** of the κ-table, and its columns other than (a), are not in the statement.
- **Other height ranges.** Only `ℓ^{a₀} ≤ T ≤ Q^{κ₁}` with fixed `a₀, κ₁` is covered.
  - There is no super-polynomial range (`T` beyond every fixed power of `Q`).
  - There is nothing below `ℓ^{a₀}`.
- **Other weights.** Only `w ∈ {w_η, w^sm_η}`, as in the paper's theorem.
- **The printed constants.** The table constants are the `n = 400` certificates. They match the paper's
  table exactly; the finer `n = 800` values are not covered (see above).
- **Results of `Families` that are stated but not proved.** The 10 `Prop` definitions of the `Families` library
  that are stated only (Theorems 1.2 and 1.3, `thm:conditional`, Lemma A, and so on; `README.md`) have no proofs
  in the project, so `thmH` cannot use them.

## Statement faithfulness

The Lean kernel checks that `thmH` proves `thmH_Statement`. **It does not check that `thmH_Statement` says what
the paper's theorem says** (Theorem 1.4(a), with column (a) of its κ-table). That
correspondence rests on reading `STATEMENTS-H.md`.
- The reading is supported by proved pins in `FamiliesH/StatementCheck.lean`: `pB_two`, `admissibleB_two_iff`,
  `kappaT_rpow`, the `rfl` parsing pins, and `thmMain_of_thmH`.
- Most objects are reused verbatim from the `Families` library, whose headline statement `thmMain_Statement` was
  checked in an independent review by OpenAI's Astra, which found it
  faithful.
- `thmH_Statement` was checked by two further independent audits (Claude-based agents, i.e. of the same model
  family as the formalisation, working separately from it); both found it faithful. An audit of `thmH_Statement`
  by a system of a different model family has not been done.
- The audit (`scripts/audit.sh`) pins the content of what was audited: it prints every definition that
  `thmH_Statement` (and `thmMain_Statement`) unfolds to and requires an exact match with
  `scripts/Statements.baseline.txt`.

**The band hypothesis.** `BandLSH`, the band hypothesis of the component statement for Proposition 9.18, covers intervals of `Q^{5/4}` integers, as the paper assumes
(`Λ_mult(Q^{5/4}) ≤ (C_band + o(1))H`, exactly what Lemma 9.1 (S2) gives for the band intervals). The glue
derives it from the formally proved large sieve, since `Q^{5/4} ≤ Q²`. `STATEMENTS-H.md` §5 explains why the bound
`Q^{1+2ε}` used at polylogarithmic height would not suffice here.

## Building and checking

See `README.md`: one `lake build` builds both libraries, and one `scripts/audit.sh` checks both headlines and ends
with `AUDIT PASSED`. For `FamiliesH` the audit checks that:
- there is no `native_decide` and no `axiom` declaration (a textual check, backed by the axiom scan);
- across all 567 declarations of the `FamiliesH.*` modules, no axiom other than the three standard ones occurs;
- there are **no** sorry roots, and no declaration depends on `sorryAx`;
- the glue and statement checks are sorry-free, among them `thmMain_of_thmH`;
- `thmH` has no hypotheses, its type is literally `thmH_Statement`, and its axioms are exactly
  `propext, Classical.choice, Quot.sound`;
- the 51 lines of `scripts/PrintAxiomsH.baseline.txt` are reproduced unchanged. They cover the headline, the 15
  components, the glue, the statement checks, the package proofs, and the five certificates, which depend on no
  axioms;
- the statement pin (`scripts/Statements.lean` against `scripts/Statements.baseline.txt`) matches exactly.

The `FamiliesH` part of a passing run ends:

```
thmH hypotheses: none
thmH type: thmH_Statement
thmH axioms: propext, Classical.choice, Quot.sound

FamiliesH sorry roots: none (all 15 components proved: packages V, F, Z, S and TS)
glue and statement checks: sorry-free
== regression against scripts/PrintAxiomsH.baseline.txt ==
all 51 baseline lines reproduced unchanged
PrintAxiomsH: 51 declarations, none depends on sorryAx
thmH axioms (#print axioms): propext, Classical.choice, Quot.sound
```

`FamiliesH.V.CertData`, the five kernel certificate checks, takes about 150 s to build.

## Layout

| Path | Contents |
|---|---|
| `FamiliesH.lean` | root module |
| `FamiliesH/Basic.lean`, `Setup.lean`, `Statements.lean`, `Main.lean` | definitions, the one-cell data `HSetup`, the 17 component statements, `thmHcell_Statement` and `thmH_Statement` |
| `FamiliesH/Glue.lean`, `Components.lean`, `Headline.lean` | the proved glue, the 15 component theorems (wired to the packages), and `thmH` |
| `FamiliesH/StatementCheck.lean` | faithfulness pins and `thmMain_of_thmH` |
| `FamiliesH/V/`, `F/`, `Z/`, `S/`, `TS/` | the five proof packages (table above) |
| `scripts/AuditH.lean`, `PrintAxiomsH.lean` (+ `PrintAxiomsH.baseline.txt`) | the `FamiliesH` part of `scripts/audit.sh` |
| `scripts/Statements.lean` (+ `Statements.baseline.txt`) | the statement pin (both headlines) |
| `scripts/gen_hybrid_data.py` | regenerates `FamiliesH/V/CertData.lean` from the paper's ancillary `certify_hybrid.py` (byte-identical output) |
| `STATEMENTS-H.md` | the Lean ↔ paper map, Lean label ↔ paper numbering, faithfulness notes, and the statement-change record |

About 11,750 lines of Lean in 52 files:
- base 1,255;
- V 1,470;
- F 2,500;
- Z 1,790;
- S 2,807;
- TS 1,930.

## Toolchain and dependencies

As for the whole project (`README.md`): Lean `v4.33.0-rc2`, Mathlib `51e6992e`, `Zeta23` `fbdc36bb`, all pinned in
`lake-manifest.json`. `FamiliesH` imports only `Families` and Mathlib; it uses `Zeta23` only through `Families`.
