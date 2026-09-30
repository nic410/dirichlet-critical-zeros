> **Note on the current state.** Since this review, the 10 unproved results of the `Families` library were converted
> from `sorry` placeholders to `Prop` definitions, so the audit now reports zero `sorry`; the script
> `scripts/audit_hybrid.sh` (which printed `AUDIT-H PASSED`) was merged into `lean/scripts/audit.sh`, which checks both
> headlines and prints `AUDIT PASSED`.

> **Cleaned copy of an internal review record: internal file paths and identifiers removed; content otherwise unchanged.**
> Notes on this copy:
> - This audit was carried out by Claude, the same model family that wrote the formalisation, so it is **not** a
>   cross-model audit. No cross-model audit of `thmH_Statement` has been done.
> - Repository paths, branch names, commit identifiers and the audit date have been removed; the snapshot table of
>   §0 is shortened accordingly. "[H]" is the standalone draft of §9 (internal; not included). Line numbers "l." in
>   `main.tex` refer to the merge-proposal version of the paper that was audited. The evidence files listed in §0
>   (compiled Lean checks and their logs, and two Python recomputations) are kept with the internal record and are
>   not included; line references into them are kept for the record.
> - At the time of the audit the Lean package had its own audit script (`scripts/audit_hybrid.sh`); it has since been
>   merged into `lean/scripts/audit.sh`, which checks both headlines.

# Statement audit: `Families.Hybrid.thmH_Statement` against Theorem 1.4(a)

**Auditor:** Claude (Opus 5.5), acting as an independent, hostile statement auditor. This is the same model family
that wrote the formalisation, so it is **not** a cross-model audit. A brief for one exists (internal).
**Question:** does the kernel-checked Lean statement say what the paper's theorem says? The proofs are not
re-checked here; the kernel did that.

**Targets.**
- Theorem 1.4(a) (`thm:poly`) of the proposed merged manuscript (merge-proposal version of `paper/main.tex`), l. 131–143,
  with the table after it (l. 151–169).
- Theorem 1.1 (`thm:H`) of the standalone draft [H] (internal), l. 74–85, with Table 1 (l. 107–125).

The two statements are word-for-word the same theorem. They differ only in their tables.

**Overall verdict: FAITHFUL.** `thmH_Statement` is a faithful formalisation of merged Theorem 1.4(a) (= [H]
Theorem 1.1) and of column (a) of the table at κ = 1, 2, 3, 5, 10.
- There is one harmless strengthening: the `N_d` bound carries `ε/2`, as in the audited families headline.
- Three items are not covered, and all three are documented:
  - the κ = 1/4 and κ = 1/2 rows;
  - the n = 800 constants of the standalone draft (Lean is weaker there by 10⁻⁶);
  - Theorem 1.4(b), (c) and Corollary 1.5.
- No mismatch, no vacuity and no junk-value loophole was found.
- The approved `BandLSH` correction is internal, is discharged by a proved theorem, and matches the paper.

## 0. Snapshot and what was run

| | |
|---|---|
| Lean sources | `FamiliesH/`, the `Families` library and both papers' theorem text were byte-identical throughout the audit (checked with `sha256sum -c`). |
| Toolchain | Lean `v4.33.0-rc2`, Mathlib `51e6992e`, with `Families` by path, unchanged. |
| Build state | `lake build --no-build FamiliesH` reports `All targets up-to-date (9001 jobs)`, so the oleans are those of these sources. |
| Package audit | `scripts/audit_hybrid.sh` gives **`AUDIT-H PASSED`**: 0 sorry roots, all 51 baseline lines reproduced, `thmH` has no hypotheses, and `#print axioms` = `[propext, Classical.choice, Quot.sound]`. |
| Files written by this audit | Only the audit folder. No package file was modified, and git was used read-only. |

**Evidence files** (all under `evidence/`; each `.lean` runs with `lake env lean` from the package root):

| File | What it contains |
|---|---|
| `PrintDefinitionsH.lean` → `print-definitions.log` | The elaborated headline and every definition it unfolds to (`pp.coercions`, `pp.numericTypes`) |
| `StatementSemanticsH.lean` → `statement-semantics.log` | **40 compiled semantic lemmas** and their axioms: 35 use the three standard axioms, 5 use fewer |
| `ClosureH.lean` → `closure.log` | Mechanical list of every project constant the *statement* depends on (types and definition bodies, never proofs) |
| `AuxProofs.lean` → `aux-proofs.log` | The auxiliary `_proof_n` constants that occur in the statement term |
| `Probe.lean` → `probe.log` | Signatures of the reused lemmas; `#print` of `BandLSH` (shows `Q ^ (5 / 4 : ℝ)`), `LmultLEAny`, `lemRvMH_lower_Statement` and `lemMbeta_Statement` |
| `NegativeControlsH.lean` → `negative-controls.log` | Seven plausible misreadings, all rejected by the definitional-equality check |
| `recheck_certs.py` → `recheck_certs.log`, `flat_cert.py` → `flat_cert.log` | Exact rational recomputation of the certificate values |

## 1. The statement, as elaborated

This is taken from `print-definitions.log`. `ProportionsAtLeastH` is at `FamiliesH/Basic.lean:51`,
`thmH_Statement` at `FamiliesH/Main.lean:38`, and `certH_Statement` at `FamiliesH/Statements.lean:239`.

```
thmH_Statement :=
 (∀ ε : ℝ, 0 < ε → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ (a0 κ1 : ℝ), 0 < a0 → 0 < κ1 → ∀ η : ℝ, 0 < η → η ≤ η₀ →
    ∀ W : Weight, W.w = wSharpFun η ∨ W.w = wSmoothFun η →
      ProportionsAtLeastH W a0 κ1 fun κ => pB (betaK κ) (1 : ℝ) - ε) ∧ certH_Statement
ProportionsAtLeastH W a0 κ1 p :=
 ∀ ε, 0 < ε → ∃ Q₀, ∀ Q, Q₀ ≤ Q → ∀ T ∈ Set.Icc (Real.log Q ^ a0) (Q ^ κ1),
   (p (kappaT Q T) - ε) * Nfam W Q T ≤ Ns0 W Q T ∧ (p (kappaT Q T) - ε) * Nfam W Q T ≤ Nstar0 W Q T ∧
   (((1 : ℝ) + p (kappaT Q T)) / (2 : ℝ) - ε) * Nfam W Q T ≤ Nd W Q T
certH_Statement := 0.865673 ≤ pB (3/2 : ℝ) 1 ∧ 0.824355 ≤ pB (4/3 : ℝ) 1 ∧ 0.797213 ≤ pB (5/4 : ℝ) 1 ∧
                   0.764149 ≤ pB (7/6 : ℝ) 1 ∧ 0.727484 ≤ pB (12/11 : ℝ) 1
kappaT Q T := Real.log T / Real.log Q        betaK κ := (2 + κ) / (1 + κ)
pB β C := 2 - sInf (Qf (FC C) '' {f | AdmissibleWindowB β f})
AdmissibleWindowB β f := f ≥ 0 ∧ f(−x) = f(x) ∧ (f x ≠ 0 → x ∈ [−β/2, β/2]) ∧ MemLp f 2 ∧ ∫ f = 1
Qf F f := (∫ f²) + ∫ x, ∫ y, f x * f y * F |x − y|         FC C α := if α ≤ 1 then α else C
```

`Nfam`, `Ns0`, `Nstar0`, `Nd`, `famSum`, `zerosI`, `Weight`, `omega`, `primChars`, `wSharpFun`, `wSmoothFun`,
`Lfun` and `mult` are the unchanged definitions of the audited `Families` package (printed in the log).

**What the statement depends on** (`closure.log`, computed mechanically):
- 41 project constants: 24 from `Families` and 17 from `Families.Hybrid`.
- Compared with the audited `thmMain_Statement`:
  - the hybrid statement adds exactly `thmH_Statement`, `certH_Statement`, `ProportionsAtLeastH`, `kappaT`,
    `betaK`, `pB`, `AdmissibleWindowB`(`.mk`), and auxiliary `Nat.AtLeastTwo` proofs for numerals;
  - it drops `thmMain_Statement`, `ProportionsAtLeast`, `pC` and `AdmissibleWindow`(`.mk`).
- The auxiliary `_proof_n` constants have types such as `((11 : ℕ) + 1).AtLeastTwo` (`aux-proofs.log`). By proof
  irrelevance they cannot change the meaning of the statement.
- No component statement is reached. In particular `BandLSH`, `LmultLEAny`, `propTIsharpH_Statement`, `HSetup`,
  `lemRvMH_lower_Statement` and `lemMbeta_Statement` are absent (`forbidden constants reached: []`).

## 2. Verdicts

| # | Item | Verdict | Principal evidence |
|---|---|---|---|
| 1 | Parsing and precedence | **FAITHFUL** | `thmH_unfolded` (`Iff.rfl`, `evidence/StatementSemanticsH.lean:49`); negative controls; `Main.lean:38`; `Basic.lean:51` |
| 2 | Vacuity and default values | **FAITHFUL** (no vacuity, no junk) | `N_pos_eventually` (l. 139); `pB_genuine` (l. 281); `integrals_genuine` (l. 293); `pB_ge_two_thirds` (l. 338); `counts_chi_order` (l. 345); `counts_order_eventually` (l. 377); `heights_contain_power` (l. 249); `kappaT_on_range` (l. 269) |
| 3 | Strength and uniformity | **FAITHFUL**; locally **STRONGER** (harmless) for `N_d` | `thmH_part1_iff_paper` (l. 184) and `paperThm14a_holds` (l. 229): Lean ⇔ the literal `liminf`/`inf`/ratio statement |
| 4 | Certificates vs the printed κ-table | **FAITHFUL** to the merged table (exact match, n = 400) for κ = 1, 2, 3, 5, 10; **WEAKER** in coverage and against the standalone table | `Statements.lean:239`; `V/Cert.lean:66`; `recheck_certs.log`; `distinct_column` (l. 477) |
| 5 | `BandLSH` correction | **FAITHFUL**: internal, discharged, consistent with the paper | `closure.log`; `bandLSH_discharged` (l. 500); `bandLSH_parse` (l. 490); git history of `Statements.lean` |
| — | Theorem 1.4 as a whole | **WEAKER** (scope): (b), (c) and Cor. 1.5 are not stated | `README-H.md` "What is not formalised"; merged `main.tex` l. 245, 925 |

In this section, line numbers "l." refer to `evidence/StatementSemanticsH.lean` unless stated otherwise.

## 3. Item 1: parsing and precedence (FAITHFUL)

**Unfolding check.** `thmH_unfolded` (l. 49) states the headline with every definition unfolded and is proved by
`Iff.rfl`. It spells out `ProportionsAtLeastH`, the target, `kappaT`, `betaK`, `pB` and `certH_Statement`, and
writes the heights with `Real.rpow` explicitly.

**What the unfolding shows.**
- **Certificates.** They are a top-level conjunct, outside every quantifier (`thmH_split`, l. 41, `Iff.rfl`).
- **Quantifier order.**
  - The order is `∀ ε ∃ η₀ ∀ a₀ κ₁ ∀ η ∀ W ∀ δ ∃ Q₀ ∀ Q ≥ Q₀ ∀ T ∈ [ℓ^{a₀}, Q^{κ₁}]`.
  - So `η₀` depends only on `ε`, and is independent of `a₀` and `κ₁` as the TeX states.
  - `Q₀` comes before `T`, so the bound is uniform in `T`.
  - `Q₀` may depend on `(ε, a₀, κ₁, η, W, δ)`, which the `liminf` permits.
- **Target.**
  - The target is `pB (betaK (kappaT Q T)) 1 − ε`, evaluated inside the `T` quantifier.
  - `ε` sits outside `p`, since `fun κ => pB (betaK κ) 1 - ε` elaborates as `(pB …) − ε`.
  - The three conclusions form one conjunction under `∀ T`.
- **Numeric types.**
  - `Real.log Q ^ a0` and `Q ^ κ1` are `Real.rpow`, with `a0, κ1 : ℝ` (pinned by `Iff.rfl`).
  - `3/2, 4/3, 5/4, 7/6, 12/11` are real divisions. `cert_literals` (l. 80) shows they equal `betaK 1, 2, 3, 5, 10`.
  - The decimal literals are the exact rationals `865673/10⁶` etc.
  - `ρ.re = (1/2 : ℝ)`, and `(1 + p)/(2 : ℝ)` is real.
  - `ω(q) = w(q/Q) q/φ(q)` uses real division (`omega_parse`, l. 75).
- **`Qf` and `F₁`.** `Qf = (∫ f²) + ∫∫ …`, with the square integral outside the binder (`qf_parse`, l. 64). `FC 1 α
  = min α 1` for all real `α` (`FC_one_eq_min`, l. 68). So `F₁(α) = min(α, 1)`, as in the TeX.

**Negative controls** (`negative-controls.log`). The same definitional-equality check that accepts the faithful
transcription (`good : true`) rejects seven misreadings:

| Misreading | Check result |
|---|---|
| `p(β(κ_T) − ε)` | false |
| a fixed target `p(β(κ₁))` | false |
| the TeX `N_d` convention (`(1+p)/2 − ε`) | false |
| `ℕ`-power heights `Q^⌈κ₁⌉₊` | false |
| `η₀` after `a₀, κ₁` | false |
| `Q₀` after `T` | false |
| the n = 800 constants | false |

So the `Iff.rfl` pins discriminate.

## 4. Item 2: vacuity and default values (FAITHFUL)

Every place where a junk value or an empty class could enter was checked by a compiled lemma.

- **Weights.** A `Weight` with `W.w = wSharpFun η` (resp. `wSmoothFun η`) exists for every `0 < η < 1/2`
  (`sharp_weight_exists`, `smooth_weight_exists`, l. 235). The counts depend on `W` only through `W.w`
  (`counts_depend_only_on_w`, l. 242). So the `∀ W` ranges over exactly the paper's two weighted families.
- **Heights.**
  - For fixed `a₀ > 0` and `0 < κ ≤ κ₁`, eventually `Q^κ ∈ [ℓ^{a₀}, Q^{κ₁}]` and `κ_{Q^κ} = κ`
    (`heights_contain_power`, l. 249, via `isLittleO_log_rpow_rpow_atTop`). So the range is eventually nonempty
    (`heights_nonempty`) and contains genuinely polynomial heights.
  - For `Q > 1` and `log Q ≥ 1`, every `T` in the range has `T ≥ 1`, `0 ≤ κ_T ≤ κ₁`, `β(κ₁) ≤ β(κ_T)` and
    `1 < β(κ_T) ≤ 2` (`kappaT_on_range`, l. 269). So the κ_T-dependent target is only ever evaluated at supports in
    `[β(κ₁), 2] ⊂ (1, 2]`.
  - The junk inputs are never reached on the range: `log Q = 0`, `1 + κ = 0`, and `rpow` of a nonpositive base.
- **`p(β; F₁)` is the paper's constant (`eq:pbeta`), not a junk value.**
  - For every `β ≥ 1` the admissible class is nonempty (it contains `1_{[−1/2,1/2]}`) and `Qf ≥ 0` on it. So
    `2 − pB β 1` is the greatest lower bound of the values of `𝒬_{F₁}` (`pB_genuine`, l. 281, as `IsGLB`).
  - For `β ≤ 2`, `f`, `f²` and `f(x)f(y)F₁(|x−y|)` are genuinely integrable (`integrals_genuine`, l. 293). The
    iterated integral is the product integral by Fubini (`qf_is_product_integral`, l. 305).
  - The Lean class uses pointwise conditions: `f ≥ 0`, even, zero off `[−β/2, β/2]`, in `L²`, `∫ f = 1`. Every
    element of the paper's a.e.-class has a representative in the Lean class with the same functional values:
    symmetrise, take the positive part, and zero it outside the interval. So the two infima coincide. This last
    step is argued, not formalised.
- **The target is a genuine claim at every height.**
  - `pB 1 1 ≥ 0.666666` (`pB_one_ge`, l. 327). This uses the package's own `cert_row` on the flat window at
    support 1, with 400 cells; the integer inequality is checked by `decide +kernel`, and `𝒬_{F₁}(flat) = 4/3`
    exactly (`flat_cert.log`).
  - With the proved `lem:Mbeta`, `pB β 1 ≥ 0.666666` on `[1, 2]` (`pB_ge_two_thirds`, l. 338).
  - So for `ε < 0.66` the target `p(β(κ_T)) − ε` is positive at every height. No conjunct is trivially satisfied
    through `N^s_0 ≥ 0`.
- **Zero sets and multiplicities** (for every `T ≥ 0`, so on the whole polynomial range). For primitive `χ` with
  `q > 1`:
  - `zerosI χ T` is finite, so `∑ᶠ` and `ncard` are not the junk `0`;
  - every counted zero has `mult ≥ 1`;
  - `N^s_{0,χ} ≤ N^*_{0,χ} ≤ N_{d,χ} ≤ N_χ` (`counts_chi_order`, l. 345).
- **Family level.**
  - Eventually in `Q`, for every `T ≥ 0`, `N^s_0 ≤ N^*_0 ≤ N_d ≤ N` (`counts_order_eventually`, l. 377). The three
    statistics are genuine proportions `≤ 1`. The modulus `q = 1`, where `L = ζ`, has weight 0 once `Q > 1/η`
    (`modulus_one_weight_vanishes`, l. 398).
  - **`N > 0` eventually, uniformly on the whole range `ℓ^{a₀} ≤ T ≤ Q^{κ₁}`**, for every weight
    (`N_pos_eventually`, l. 139). It follows from the proved hybrid Riemann–von Mangoldt lower bound
    (`propZeroH_unconditional.2`: `N ≥ ½ H T ℓ_*/(2π)`) together with `H > 0` and `ℓ_* = log(QT) > 0`.
  - `N > 0` forces a nonempty family: some `q ≤ Q` with `ω(q) > 0` and a primitive character
    (`family_nonempty_of_N_pos`, l. 165).

## 5. Item 3: strength and uniformity (FAITHFUL; N_d locally STRONGER)

**The literal paper statement.** `paperThm14a` (l. 126) transcribes merged Theorem 1.4(a) = [H] Theorem 1.1 directly.
- For every `ε > 0` there is `η₀ > 0` such that for all `a₀, κ₁ > 0`, `η ∈ (0, η₀]` and both weights, the three
  bounds below hold.
- `(−ε : EReal) ≤ liminf_{Q→∞} ⨅_{T ∈ [ℓ^{a₀}, Q^{κ₁}]} (N^s_0/N − p(β_T))`, and likewise for `N^*_0/N`.
- The same for `N_d/N − (1+p(β_T))/2`.
- The `liminf` and the `inf` are taken in `EReal`, a complete lattice. So neither the `inf` over an empty set nor
  the `liminf` has a junk value, and the ratios are real divisions.

**Compiled results.**
- `liminf_inf_ge_iff` (l. 93): `c ≤ liminf inf X` ⇔ `∀ δ > 0 ∃ Q₀ ∀ Q ≥ Q₀ ∀ T ∈ S(Q), c − δ ≤ X`.
- **`thmH_part1_iff_paper` (l. 184): the first conjunct of `thmH_Statement` is logically equivalent to
  `paperThm14a`.**
  - This uses `N > 0` (item 2) to pass between multiplied and ratio forms.
  - For `N^s_0` and `N^*_0` the correspondence is at the same `ε`.
  - For `N_d`, Lean at `ε` gives the paper's `N_d/N ≥ (1+p)/2 − ε/2`, which is stronger. The paper at `ε/2` gives
    Lean at `ε`. This is the same harmless convention that the families audit found.
- `paperThm14a_holds` (l. 229): the paper statement follows from `thmH`.

**Uniformity and hidden restrictions.**
- `η₀` depends only on `ε`, and `Q₀` comes before `T`. The negative controls reject the other orders.
- `a₀ > 0` and `κ₁ > 0` are arbitrary, with no upper bound and no relation between them. `Q` is real.
- The family is every primitive `χ mod q` with `1 ≤ q ≤ ⌊Q⌋` and weight `w(q/Q) q/φ(q)`. `primChars` filters
  only by `IsPrimitive`. With `supp w ⊂ [η, 1]` this gives exactly `ηQ ≤ q ≤ Q`.
- No hypothesis appears that is not in the TeX: `thmH` itself has no hypotheses.

**Consequences stated in the paper, compiled from `thmH`.**
- `in_particular_power` (l. 414) is the "in particular, `T = Q^κ`" clause: `liminf N^s_0/N ≥ p((2+κ)/(1+κ)) − ε`.
- `row_uniform`, `row_kappa_one` and `row_kappa_five` (l. 443–466) cover the text after the table ("a value in the
  row κ holds for all `T ≤ Q^κ`"), using the proved `lem:Mbeta`. This includes the abstract's "`0.8656 − ε` for
  `T ≤ Q`" and "`0.7641 − ε` for `T ≤ Q^5`".
- The package's `thmMain_of_thmH` shows that the hybrid headline implies the audited families headline.

**Not covered.** Theorem 1.4(b) (Gauss route), 1.4(c) (classical route) and Corollary 1.5 (dyadic family) are not
stated in Lean. This is documented in `README-H.md` and in merged `main.tex` l. 245 and 925. So
Lean covers **Theorem 1.4(a)**, not all of Theorem 1.4.

## 6. Item 4: the certificate conjuncts against the printed κ-table

| κ | β(κ) | Lean (`certH_Statement`) | Merged table (a), n = 400 | [H] Table 1, n = 800 | Exact `2 − 𝒬` of the Lean step function | Paper n = 400 log, `EXACT` |
|---|---|---|---|---|---|---|
| 1 | 3/2 | 0.865673 | 0.865673 | 0.865674 | 0.865673824 | 0.865673824 |
| 2 | 4/3 | 0.824355 | 0.824355 | 0.824356 | 0.824355736 | 0.824355736 |
| 3 | 5/4 | 0.797213 | 0.797213 | 0.797214 | 0.797213833 | 0.797213833 |
| 5 | 7/6 | 0.764149 | 0.764149 | 0.764150 | 0.764149810 | 0.764149810 |
| 10 | 12/11 | 0.727484 | 0.727484 | 0.727485 | 0.727484891 | 0.727484891 |

Sources: the "exact" column is `recheck_certs.log`, an independent autocorrelation evaluation in Python `Fraction`s
of the step heights parsed from `V/CertData.lean`. The last column is
`paper/anc/certify_hybrid_n400_rerun.log` (merge-proposal version).

- **Merged table: exact match.** The five Lean constants are the printed n = 400 values. Each is the floor to 10⁻⁶
  of the exact value of the kernel-checked step function, and these agree to 9 digits with the paper's log. So the
  Lean step functions are the paper's n = 400 certificates.
- **Distinct column.** The (a)-distinct entries `0.932836, 0.912177, 0.898606, 0.882074, 0.863742`, and `0.966141`
  at κ = 0, follow from the certificates (`distinct_column`, l. 477).
- **Row κ = 0** (`0.932282`) is not a conjunct. It is available as `row_kappa_zero_constant` (l. 471), from the
  families certificate and `pB_two`.
- **Rows κ = 1/4 (0.912574) and κ = 1/2 (0.894985) are not certified in Lean.** This is a coverage gap. The merged
  paper's new appendix text (l. 921) correctly says "for κ = 1, 2, 3, 5, 10".
- **Standalone [H] Table 1** prints the n = 800 values. Against it, Lean is **WEAKER by 10⁻⁶** in column (a). Its
  distinct column is not implied at κ = 1, 2, 3, 5 either (for example `(1+0.865673)/2 = 0.9328365 < 0.932837`).
  This is documented in `README-H.md` and in `STATEMENTS-H.md` note 5.
- Columns (b), (c) and the dyadic column belong to the unformalised parts (§5).

## 7. Item 5: the BandLSH correction (FAITHFUL)

- **Internal.**
  - `BandLSH` is not in the definitional closure of `thmH_Statement` (`closure.log`).
  - Git shows `FamiliesH/Main.lean` and `FamiliesH/Basic.lean` unchanged since the first commit of the package.
  - The only change to `Statements.lean` is exactly the before/after text recorded in
    `STATEMENTS-H.md` §5: `Q ^ (1 + 2 * ε)` became `Q ^ (5 / 4 : ℝ)`, and the binder became `_ε`.
  - `Headline.lean` changed only in its docstrings.
- **Real exponent.** `5/4` is a real exponent (`bandLSH_parse`, l. 490, `Iff.rfl` with `Real.rpow Q (5/4)`;
  `five_quarters_is_real`, l. 494). It is not `ℕ`-division `5/4 = 1`, a trap that would have made the hypothesis
  `K ≤ Q`.
- **Discharged.** `BandLSH` holds for every weight with an explicit `C_band ≥ 1` (`bandLSH_discharged`, l. 500,
  from `Hyp.MV_LargeSieve_proof` and `lemWH`). It is a proved fact, not an assumption, and `thmH` has no hypotheses.
- **Consistent with the paper.**
  - [H] Prop. 4.7 assumes `Λ_mult(Q^{5/4}) ≤ (C_band + o(1))H` ([H] l. 507, used in Step 3(ii) at l. 533).
    The merged version is `lemmas/polyheight.tex` l. 360 and 386.
  - The size lemma (S2) gives `K(u) ≤ Q^{5/4}` on the band ([H] l. 228; `polyheight.tex` l. 83).
  - The paper's `Λ_mult(K)` is a supremum over intervals of at most `K` consecutive **positive** integers, anywhere
    (merged `main.tex` l. 410). That matches `LmultLEAny`, which takes `N₀ ≥ 1` with no location cap.
  - The correction strengthens a component's hypothesis, which weakens that component, and aligns it with the TeX.

## 8. Documentation findings (non-blocking)

1. **`N_d` wording in the appendix.** Merged `main.tex` l. 923 says the Lean statement gives
   `N^s_0 ≥ (p(β_T;F_1) − ε − δ)N` "and similarly for `N^*_0` and `N_d`". For `N_d` the Lean bound is
   `((1 + p(β_T)) − ε)/2 − δ`, which is stronger. Saying so explicitly would help readers comparing the two
   literally; the families audit made the same suggestion.
2. **Stale remark in `STATUS.md`.** Its "Stale docstring" paragraph is itself stale: `Headline.lean`'s docstring
   was updated and now says that `thmH` is sorry-free.
3. **Scope wording.** The paper's new text (l. 245, 913, 921–925) and the updated `README-H.md` accurately
   describe what is formalised (1.4(a) with column (a) at κ = 1, 2, 3, 5, 10) and what is not. I found no
   overclaim. The paper's proof-route remarks (trace prime term, mixed term under the profile bound) concern the
   proof, not the statement, and were not audited here.

## 9. Weakest links and what I did not check

- **Reused definitions** (medium–high confidence). The family, weights, `Lfun`, `mult` and the four counts are the
  `Families` definitions; their faithfulness rests on the Astra audit of `thmMain` (record 01). I re-checked only what could
  change at polynomial height: finiteness, multiplicities, the order of the counts and `N > 0`, for every `T ≥ 0`.
- **a.e. versus pointwise class** for `p(β)` (high confidence). This is argued in §4, not formalised.
- **`paperThm14a` is my transcription** (high confidence). It is much closer to the TeX than `thmH_Statement`: it
  uses `liminf`, `inf` and ratios. Its fidelity to the TeX is still a matter of reading.
- **Out of scope:**
  - the 15 component theorems and the glue;
  - the paper's mathematics;
  - a from-scratch rebuild (I used the existing, up-to-date build);
  - the proof-route claims of merged `main.tex` l. 921.

**Final verdict:** `Families.Hybrid.thmH_Statement` is a **faithful** formalisation of merged Theorem 1.4(a)
(= [H] Theorem 1.1). It includes column (a) of the κ-table at κ = 1, 2, 3, 5, 10, with exactly the printed n = 400
values, and has a harmless `ε/2` strengthening for `N_d`. It is not vacuous and depends on no junk value. The
`BandLSH` correction does not touch it.
