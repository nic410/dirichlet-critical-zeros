# Theorem 1.4(a) in Lean: statement correspondence

This file maps `Families.Hybrid.thmH_Statement` and its component statements to the paper, and lists the
statement-faithfulness risks. It mirrors `STATEMENTS.md`. The library `FamiliesH` imports the library `Families`
**unchanged**, and every definition `Families` provides is reused verbatim.

**Numbering.** Theorem, section and equation numbers are those of the paper: the theorem is Theorem 1.4(a), and
its proof is §9. The Lean components of the proof carry the names of the results they formalise, with an `H`
suffix for the polynomial-height versions of the results of §§2–7 (`lem:B1H` is the polynomial-height `lem:B1`,
and so on). The table maps these names to the paper.

**Notation.** β in Lean = λ̄ in the paper. The Lean sources and these notes write `β` for the support parameter
(`betaK κ`, `β_T`, `pB β C`, `AdmissibleWindowB β`); the paper writes `λ̄(κ)`, `λ̄_T` and `p(λ̄; F_C)`. The Lean
identifiers are not renamed.

| Name in the Lean sources | Paper |
|---|---|
| `thmH`, `thmH_Statement` | Theorem 1.4(a) |
| `certH_Statement` (`prop:certH`) | Proposition 9.24; column (a) of the table after Theorem 1.4 |
| `kappaT` (`κ_T`), `betaK` (`β(κ)`, the paper's `λ̄(κ)`), `ellS` (`ℓ_*`) | (1.4) |
| `AdmissibleWindowB`, `pB` (`p(β; F)`) | (1.5) |
| `HSetup` (the fixed data (P1)–(P3), (P6) of one cell) | §9.1, "Parameters and order of limits" |
| `cellHeights` (`ℓ^{a₀} ≤ T ≤ Q^{κc}`) | (9.2) |
| `ε₅` | (9.3) |
| `HSetup.L` (`L = λℓ_*`), `.X`, `.Y`, `.J` | (9.4) |
| `lem:sizes` (`lemSizesH_Statement`), (S1)–(S4) | Lemma 9.1 |
| `lem:RvMH` | Lemma 9.2 |
| the finite-centre replacement `eq:fc2H` | Proposition 9.5, (9.8) |
| `prop:traceH` | Proposition 9.6 |
| `prop:tailH` | Proposition 9.7 |
| `prop:zeroH` | Proposition 9.9 |
| `HSetup.ratioForm` (the ratio part of the decomposition) | (5.1) (the equation of §5, used in place) |
| `lem:archH` (`M_{μμ}`, the mixed and same-sign terms; package S) | Lemma 9.10 |
| `lem:B1H`, `eqB:MratH` | Lemma 9.11 (first and second claims) |
| `lem:B2H` | Lemma 9.12 |
| `lem:M1H` (Lemma 5.9 at `L = λℓ_*`) | §9.3, "Time localisation"; (9.11) |
| `lem:M3H`(iii) (Lemma 5.11(iii) at `L = λℓ_*`) | §9.3, "Time localisation" |
| `lem:M3prime` | Lemma 9.13 |
| `cor:tails` | Corollary 9.14 |
| `prop:TIsharpH` (the band device), `BandLSH` | Proposition 9.18 |
| `prop:secondH`, `SecondMomentAssemblyH` | Proposition 9.19 |
| `HSetup.ProfileBoundH` (the profile bound) | (9.15) |
| `lem:Mbeta` | Lemma 9.21 |
| `lem:pLipH` | Lemma 9.22 |
| `lem:windowsH` | Lemma 9.23 |
| `thmH_of_cells` (the κ-cells) | §9.4, "Cells"; (9.16)–(9.17) |
| `thmHcell_of_parts`, `assemblyLimitH_Statement` | §9.4, "Proofs": the proof of Theorem 9.20, steps (a)–(e) |
| `FamiliesH/V/CertData.lean` | Proposition 9.24 and Appendix A.1 |

The Lean kernel checks that a proof proves the Lean statement. **It does not check that the Lean
statement says what Theorem 1.4(a) says**; that is checked by reading this file. The proved pins in
`FamiliesH/StatementCheck.lean` (`pB_two`, `kappaT_rpow`, the `rfl` / `Iff.rfl` parsing pins and
`thmMain_of_thmH`) support the reading.

## 1. The headline

**Theorem 1.4(a).** Fix `a₀, κ₁ > 0`. For every `ε > 0` there is `η₀(ε) > 0`, independent of `a₀` and
`κ₁`, such that for every `η ≤ η₀` and `w ∈ {w_η, w^sm_η}`:
`liminf_Q inf_{ℓ^{a₀} ≤ T ≤ Q^{κ₁}} (N^s_0/N − p(β(κ_T))) ≥ −ε`. The same holds for `N^*_0/N`, and for
`N_d/N` with `(1+p(β(κ_T)))/2`.

**Lean** (`FamiliesH/Main.lean`):

```lean
def thmH_Statement : Prop :=
  (∀ ε : ℝ, 0 < ε → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ (a0 κ1 : ℝ), 0 < a0 → 0 < κ1 →
    ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ W : Weight, (W.w = wSharpFun η ∨ W.w = wSmoothFun η) →
      ProportionsAtLeastH W a0 κ1 (fun κ => pB (betaK κ) 1 - ε)) ∧
  certH_Statement

def ProportionsAtLeastH (W : Weight) (a0 κ1 : ℝ) (p : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
    ∀ T ∈ Set.Icc (Real.log Q ^ a0) (Q ^ κ1),
      (p (kappaT Q T) - ε) * Nfam W Q T ≤ Ns0 W Q T ∧
      (p (kappaT Q T) - ε) * Nfam W Q T ≤ Nstar0 W Q T ∧
      ((1 + p (kappaT Q T)) / 2 - ε) * Nfam W Q T ≤ Nd W Q T
```

## 2. Definitions

| Paper | Lean | Where | Note |
|---|---|---|---|
| `κ_T = log T/log Q` (1.4) | `kappaT Q T` | `FamiliesH/Basic.lean` | `kappaT_rpow`: `κ_{Q^κ} = κ` for `Q > 1` (proved) |
| `β(κ) = (2+κ)/(1+κ)` (1.4) | `betaK κ` | `Basic.lean` | `betaK_zero`, `betaK_one`, `betaK_ten`, `betaK_mem` (proved) |
| `ℓ_* = log(QT)` (1.4) | `ellS Q T` | `Basic.lean` | |
| admissible `f` at support `β` (1.5) | `AdmissibleWindowB β f` | `Basic.lean` | `f ≥ 0` even, `supp f ⊂ [−β/2, β/2]`, `f ∈ L²`, `∫ f = 1`. `admissibleB_two_iff`: at `β = 2` it is `Families.AdmissibleWindow` (proved) |
| `p(β; F_C)` (1.5); `p(β) = p(β; F_1)` | `pB β C` | `Basic.lean` | `2 − sInf (Qf (FC C) '' {f \| AdmissibleWindowB β f})`, with `Qf`, `FC` reused. `pB_two`: `pB 2 C = Families.pC C` (proved) |
| heights `ℓ^{a₀} ≤ T ≤ Q^{κ₁}` | `Set.Icc (Real.log Q ^ a0) (Q ^ κ1)` | `ProportionsAtLeastH` | closed interval; `Q ^ κ1` is `Real.rpow` (pinned) |
| a cell `ℓ^{a₀} ≤ T ≤ Q^{κc}` (9.2) | `cellHeights a0 kc Q` | `Basic.lean` | |
| `N`, `N^s_0`, `N^*_0`, `N_d`; `ω_χ`; the family; `L(s,χ)`; multiplicities | `Nfam`, `Ns0`, `Nstar0`, `Nd`, `Weight.omega`, `primChars`, `Lfun`, `mult` | `Families.Main`, `Families.Basic`, `Families.Classical` | **reused verbatim**; covered by the independent audit of `thmMain_Statement` (`README.md`, "Statement faithfulness") |
| `w_η`, `w^sm_η` | `wSharpFun η`, `wSmoothFun η` | `Families.LemmaA` | reused verbatim |
| the one-cell data (P1)–(P3), (P6) | `HSetup` | `FamiliesH/Setup.lean` | port of `Families.PrimeSetup`: `A₀ → κc`, `λ < 2 → λ < β(κc)`, `λ(1+ε₁) ≤ β(κc) − ε₁`, `ε₁ < 1/4`; `L = λℓ_*` |
| `L`, `X`, `Y`, `J`, `a`, `a♯`, `b`, `S_χ`, `ψ_L`, `g`, `Φ`, `𝒦`, `x_y(u)`, Gabor matrices, `𝔐` | `HSetup.L`, `.X`, `.Y`, `.J`, `.aVec`, `.aSharp`, `.bVec`, `.Schi`, `.ψL`, `.g`, `.Φ`, `.𝒦`, `.xVec`, `.Gabor`, `.Mfrak` | `Setup.lean` | line-by-line ports of `Families.PrimeSetup.*` with `P.L Q ↦ P.L Q T`; `Λ_R` (`PrimeSetup.LamR`) and the zeros `PrimeSetup.strip` are reused |
| the profile bound (9.15) | `HSetup.ProfileBoundH` | `Setup.lean` | port of `PrimeSetup.ProfileBound` with `ℓ ↦ ℓ_*` |
| `2 − 8θ − (1−2θ)𝒬_F(f_v)` | `HSetup.certValue` | `Setup.lean` | identical to `PrimeSetup.certValue` |

## 3. Statement-faithfulness notes

1. **Quantifier order.** `ε` comes first, then `η₀`, then `a₀`, `κ₁`, then `η`, then `W`. So `η₀` depends only on
   `ε`, as the TeX says ("independent of `a₀` and `κ₁`"). Inside `ProportionsAtLeastH`, `Q₀` comes before `T`,
   which gives uniformity in `T`, as for Theorem 1.1.
2. **The target depends on `T` and sits inside the `T`-quantifier.** It is `p(β(κ_T)) − ε`, with `ε` outside
   `p`. This is pinned by `rfl`: `(fun κ => pB (betaK κ) 1 - ε) = (fun κ => (pB (betaK κ) 1) - ε)`.
3. **The distinct-zero convention.** With `p(κ) = pB(β(κ)) 1 − ε`, the `N_d` bound is
   `(1 + p(κ_T))/2 − ε' = (1+pB)/2 − ε/2 − ε'`. This is stronger than the TeX's `(1+pB)/2 − ε` at the same `ε`
   and equivalent over all `ε`. It is the same convention as `Families.ProportionsAtLeast`, which the independent audit of `thmMain_Statement` covered.
4. **Junk values.**
   - `kappaT` divides by `log Q`, which is `0` at `Q = 1`. This is harmless because `Q₀` is existential: the glue
     forces `Q ≥ e`.
   - `pB` uses `sInf`. If the admissible class were empty or unbounded below, `sInf = 0` and `pB = 2` (junk). The
     headline part is then **harder, not vacuous**, because the target would be larger. For the certificate
     conjuncts, any proof via an explicit window must use `csInf_le`, which needs `BddBelow`, so a genuine proof
     cannot exploit the junk value. Package V proves non-emptiness (the flat window) and `Qf ≥ 0` on the class,
     as `AssemblyLimit.lean:32,45` does for `pC`.
5. **The certificates are `n = 400` values**: `0.865673, 0.824355, 0.797213, 0.764149, 0.727484`. These are exactly
   the values that the paper's table after Theorem 1.4 prints in column (a) (it notes that `n = 800` step functions
   give values larger by at most `10⁻⁶`). The `n = 800` values
   (`0.865674, 0.824356, 0.797214, 0.764150, 0.727485`) are not covered by the Lean statement; `n = 400` keeps
   the kernel checks cheap. The rows κ = 1/4 and κ = 1/2 of the paper's table are not in the Lean statement.
6. **What `thmH` does not cover.** Theorem 1.4(b) (Gauss route), Theorem 1.4(c) (classical route) and
   Corollary 1.5 (dyadic family) are not stated.
   `thmH` covers `w ∈ {w_η, w^sm_η}` only, as Theorem 1.4(a) does.
7. **Cell tops instead of `κ₁` in (P4)–(P5).** §9.1 fixes `ε_max = 1/(8(1+κ₁))` and `ε₅ = min(ε,ε₁)/(4(1+κ₁))`
   globally. The Lean cell data use the cell top `κc` (`ε ≤ 1/(8(1+κc))` in `propTIsharpH_Statement` and
   `assemblyLimitH_Statement`). Inside a cell `T ≤ Q^{κc}`, so every inequality of Lemma 9.1 holds with `κc`
   in place of `κ₁`. The κ-cells argument (`thmH_of_cells`) never needs a global `ε₅`.
8. **The band hypothesis allows intervals anywhere.** `BandLSH` (via `LmultLEAny`) bounds `Λ_mult` on intervals
   anywhere in `[1, ∞)`. `Families.LmultLE` has the cap `N₀ + K − 1 ≤ Q²`, which is false-by-restriction at
   polynomial height, where band intervals lie in `[1, Y]` with `Y ≫ Q²`. This matches the TeX's
   `eq:MVLS`, which has no location restriction. The glue discharges `BandLSH` (`bandLSH_of_MV`, proved) from
   the formal multiplicative large sieve, which has no location restriction either. `BandLSH`
   bounds intervals of `K ≤ Q^{5/4}` integers, as in Proposition 9.18; the bound `Q^{1+2ε}` used for Theorem 1.1 would be
   too short at polynomial height (§5).
9. **Explicit large-sieve constant in M3′.** `lemM3primeH_Statement` carries the multiplicative large-sieve
   constant `C₀` as a parameter (`MVLargeSieveMult C₀`). The TeX uses `C₀ = 1`; the formal sieve
   `Families.Hyp.MV_LargeSieve_proof` has `C₀ = 17/4`. The statement is the faithful generalisation.
10. **Extra hypotheses of `propTIsharpH`.**
    - `ε < ε₁/4` is inherited from `Families`. It is weaker than the TeX and harmless because `ε → 0`.
    - `ε ≤ 1/(8(1+κc))` is (P4) of §9.1, with the cell top.
11. **Checked by Lean.** `thmMain_of_thmH : lemMbeta_Statement → thmH_Statement → Families.thmMain_Statement`
    (proved, sorry-free). So the hybrid headline, with `lem:Mbeta`, implies the audited families headline:
    `thmH` generalises `thmMain` in Lean.

## 4. Component statements (all proved)

| Lean (`FamiliesH/Statements.lean`) | Paper | Consumed by the glue? | Package |
|---|---|---|---|
| `lemRvMH_lower_Statement` | Lemma 9.2 (lower half) | yes | Z |
| `propZeroH_Statement` | Proposition 9.9 | yes | Z |
| `lemSizesH_Statement` | Lemma 9.1 (S1)–(S4) | no (ingredient of TS, F) | F |
| `lemB1H_Statement` | Lemma 9.11 (first claim) | no (ingredient of `eqBMratH`) | F |
| `eqBMratH_Statement` | Lemma 9.11 (second claim) | yes | F |
| `lemB2H_Statement` | Lemma 9.12 | yes | F |
| `lemM1H_Statement` | (9.11) = Lemma 5.9 at `L = λℓ_*` | no | F |
| `lemM3H_iii_Statement` | §9.3 = Lemma 5.11(iii) | no | F |
| `lemM3primeH_Statement` | Lemma 9.13 (tails by dyadic shells) | no | F |
| `corTailsH_Statement` | Corollary 9.14 (tails at `T^{−1+ε₅}`) | no | F |
| `propTIsharpH_Statement` | Proposition 9.18 (band hypothesis `BandLSH` at `Q^{5/4}`, §5) | yes | TS |
| `propSecondH_Statement` / `SecondMomentAssemblyH` | Proposition 9.19 | yes | S |
| `lemMbeta_Statement` | Lemma 9.21 | yes | V |
| `lemPLipH_Statement` | Lemma 9.22 | yes | V |
| `assemblyLimitH_Statement` | §9.4, steps (a)–(e), with Lemma 9.23 | yes | V |
| `certH_Statement` | Proposition 9.24 / the table after Theorem 1.4 | yes (headline conjunct) | V |

The theorems in `FamiliesH/Components.lean` prove these statements; all 15 are proved (packages V, F, Z, S, TS). The glue (`FamiliesH/Glue.lean`) and the statement checks are sorry-free, and
`scripts/audit.sh` asserts that no declaration depends on `sorryAx`.

## 5. The band hypothesis `BandLSH` at `Q^{5/4}`

**Where.** `FamiliesH/Statements.lean`, `def BandLSH`: the band hypothesis of `propTIsharpH_Statement`, an
internal component statement consumed by the glue. The matching step is in `FamiliesH/Glue.lean`,
`bandLSH_of_MV`.

**The statement:**

```lean
def BandLSH (W : Weight) (_ε Cband : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
    ∀ K : ℕ, (K : ℝ) ≤ Q ^ (5 / 4 : ℝ) → LmultLEAny W Q K ((Cband + δ) * W.H Q)
```

An earlier version, copied from `Families`, bounded intervals of `K ≤ Q^{1+2ε}` integers. That bound does not cover the
band intervals at polynomial height; it was a statement mismatch in the Lean component statement, not a gap in the
paper. The headline `thmH_Statement` is not affected by the choice: `BandLSH` is a hypothesis of an internal
component, and the glue discharges it.

**Rationale.**
- Proposition 9.18 assumes `Λ_mult(Q^{5/4}) ≤ (C_band + o(1))H` (paper §9.3, the
  paragraph "The band constant and the profile").
- That is what (S2) of Lemma 9.1 delivers for the band intervals:
  `K(u) ≤ 5T^{−1+ε₅}e^u + 1 ≤ Q^{5/4}` for `(1−ε)ℓ_* < u ≤ (1+ε)ℓ_*` (`lemSizesH_Statement`, second clause, proved
  as `F.lemSizesH_proof`).
- The bound `Q^{1+2ε}` of `Families` suffices for Theorem 1.1 because the localisation scale is fixed (`δ = 1/4`) and
  `e^u ≤ Q^{1+ε}`. At polynomial height the band vectors fill intervals of `≍ 2Q^{1+ε}T^{ε+ε₅}` integers, which
  exceeds `Q^{1+2ε}` at `T = Q^{κc}` whenever `κc(ε + ε₅) > ε`, i.e. for every `κc ≥ 1`.

**Effect.**
- `propTIsharpH_Statement` has the stronger hypothesis (`Q^{1+2ε} ≤ Q^{5/4}` since `ε ≤ 1/8`), so it is the
  weaker proposition. It is literally `TS.propTIsharpH54_Statement`, proved as `TS.propTIsharpH54_proof`
  (`FamiliesH/TS/`).
- The glue supplies the hypothesis with the constant `C_band = 2 max(C₀,0) w_max/(ℰ I_w) + 1`: `bandLSH_of_MV`
  only uses `K ≤ Q²`, and `Q^{5/4} ≤ Q²`.
- The statement audits of `thmH_Statement` (`README.md`, "Statement faithfulness") covered this definition.

## 6. The statement pin

`scripts/audit.sh` pins the content of `thmH_Statement` and `thmMain_Statement`: `scripts/Statements.lean` prints
every project declaration they unfold to (31 declarations; for `thmH`: `thmH_Statement`, `ProportionsAtLeastH`,
`certH_Statement`, `pB`, `AdmissibleWindowB`, `betaK`, `kappaT`, and the `Families` definitions of §2) with a
structural hash, and the audit requires an exact match with `scripts/Statements.baseline.txt`. A change to any of
them, however small (a digit of a certificate constant, a bound of the height range), fails the audit until the
baseline is regenerated deliberately. Docstrings are not part of the pin.
