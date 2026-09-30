# STATEMENTS.md — Lean declarations ↔ TeX labels

> This file covers the library `Families` (Theorem 1.1). For Theorem 1.4(a) (library `FamiliesH`,
> `Families.Hybrid.thmH`) see `STATEMENTS-H.md`, which also maps the Lean component names to the paper's
> numbering (Theorem 1.4, §9), and `README-H.md`.

Paper: the main text (`main.tex`) and the lemma sections on Lemma A (`lemma-A.tex`), Lemma C / the Toeplitz large
sieve (`lemma-toeplitz-C.tex`) and the Lemma B majorant (`lemma-B-majorant.tex`). TeX labels (`lem:…`, `prop:…`,
`eq:…`) and line numbers refer to these source files of the paper.

Status column: **P** = proved (standard axioms only; `scripts/audit.sh` checks that nothing in the project uses
`sorry`), **S** = stated only (a `Prop` definition `X_Statement`, not proved in this project), **I** = implication
proved (the Lean theorem derives the statement from other *stated* results, which are hypotheses of the theorem),
**D** = definition.

Analytic results are recorded as `def <name>_Statement : Prop`; the theorem `<name> : <name>_Statement` exists when
the result is proved. Implications between statements take them as explicit hypotheses (`Families/Glue.lean`,
`Families/Assembly.lean`, `Families/Headline.lean`).

**Classification.** **(a)** = a result on the proof of Theorem 1.1 (the headline chain); all are proved. Where the
proof needs a classical input the theorem takes it as an argument (e.g. `lemB2 (hPNT : PNT_dlVP)`) and the headline
supplies a proof of it. **(b)** = a named hypothesis (`def … : Prop` in `Families/Classical.lean` /
`Families/Classical/Reductions.lean`), bundled in the structures `ClassicalInputs` (the classical inputs (b1)–(b5))
and `PortedReductions` (the paper's own §4/§5 reductions (b6)–(b7)). **(c)** = a result off the headline chain,
stated only.

**Headline: `Families.thmMain : thmMain_Statement`, with no hypotheses** (`#print axioms`: `propext`,
`Classical.choice`, `Quot.sound`). Every (b) item is a theorem or is bypassed: the classical inputs are
`Hyp.MV_LargeSieve_proof`, `Hyp.StirlingDigamma_proof`, `Hyp.PNT_dlVP_proof`, `lemWH`; the reductions are
`Families.portedReductions`; and Montgomery 1969 enters only through its proved q-aspect restriction
`Hyp.Montgomery.Montgomery69_Density_upTo 1`. **The full `Montgomery69_Density` (all heights) is not proved and not
needed.** The (b) definitions and bundles remain defined for the conditional variants `thmMain_of_components`,
`thmMain_of_montgomery`.
Faithfulness flags: **weaker** (the Lean statement assumes more or concludes less than the TeX),
**stronger**, **different**. For (b) hypotheses "weaker" is the safe direction; for (a) targets
"stronger" would be the dangerous one (none is flagged stronger).

## Global conventions (apply to every entry; read these first)

| Convention | Lean | Faithfulness note |
|---|---|---|
| Family `𝓕(Q,w)` | sums over `q ∈ [1, ⌊Q⌋]`, `χ ∈ primChars q` (`DirichletCharacter ℂ q` with Mathlib's `IsPrimitive`), weighted by `ω(q)` | identical to the paper: `ω(q) = 0` when `w(q/Q) = 0`, so summing over all primitive `χ mod q ≤ Q` is the same sum. |
| Weight `w` | `Weight` (Basic.lean): `w : ℝ → ℝ` (extended by 0), `η ∈ (0,1/2)`, `w ≥ 0`, `supp ⊂ [η,1]`, `BoundedVariationOn w univ`, `∫₀¹ u w > 0` | = `def:admissible`. `w_max = sSup (range w)`, `V_w = (eVariationOn w univ).toReal`. |
| Log-wide weights | `wSharpFun η`, `wSmoothFun η` (LemmaA.lean); theorems quantify over `W : Weight` with `W.w = wSharpFun η` | Non-vacuous: `wSharpWeight η`, `wSmoothWeight η : Weight` are constructed for every `0 < η < 1/2` (`Weights.lean`, proved: bounded variation on ℝ and `I_w > 0`). |
| Vectors | `x : ℤ → ℂ` on a `Finset ℤ`; intervals `intervalZ N₀ K = [N₀, N₀+K)` (exactly `K` integers) | faithful. |
| `x^*Δx` | `famForm` = `∑_χ ω_χ |∑_n x_n χ(n)|²`; proved equal to `∑ x_n x̄_m Δ(n,m)` (`famForm_eq_sum`) | faithful. |
| `λ_max(T_I) ≤ B` | written as the quadratic-form bound `y^*T y ≤ B‖y‖²` for all `y` on `I` | equivalent for Hermitian `T`. |
| Farey-type measures | `levelForm E a I y = ∑_{e∈E} a(e) ∑*_{c mod e} |S_y(c/e)|²`, kernel `levelKernel`, matrix `toeplitz` | `μ_Ω, μ_Ω^+, μ^m, μ^♮` are the level weights `aΩ, aΩplus, aM, aNat` on levels `1 ≤ e ≤ Q` (all have no mass above `Q`). |
| `o(1)`, `Q → ∞` | `∀ δ > 0, ∃ Q₀, ∀ Q ≥ Q₀, …` | uniformity (in `T`, `K`, `I`, `x`) is placed after `Q₀` exactly as in the text. |
| `liminf_Q inf_T N^s_0/N ≥ p` | `ProportionsAtLeast W a0 A0 p`: `∀ε ∃Q₀ ∀Q≥Q₀ ∀T∈[ℓ^{a0},ℓ^{A0}], (p−ε)N ≤ N^s_0` (and `N^*_0`, `N_d` with `(1+p)/2`) | equivalent when `N > 0` (true for large `Q`); avoids division. For `N_d` the Lean bound is `(1+(p−ε))/2 = (1+p)/2 − ε/2`, slightly **stronger** than the TeX's `(1+p)/2 − ε` at the same `ε` (equivalent over all `ε`; noted by the independent statement audit). |
| ess sup constants | `Rw`, `CT`, `CTp : ℝ≥0∞` (`essSup` of `ENNReal.ofReal ∘ P` on `volume.restrict (Ioi 0)`) | exact. Where the text uses the constant as a real number, the Lean statement either stays in `ℝ≥0∞` (`lemC`) or assumes `≠ ⊤` and uses `toReal` (`propSharpLS`, `propTIsharp`). |
| Zero counts | `zerosI χ T = {ρ : L(ρ,χ)=0, T < Im ρ ≤ 2T}` with Mathlib's `DirichletCharacter.LFunction`; multiplicity `analyticOrderNatAt`; `N_χ = ∑ᶠ`, distinct counts `Set.ncard` | For `T > 0` all such zeros are nontrivial. Finiteness (so that `∑ᶠ`/`ncard` are the true counts, not the junk value 0 of an infinite set) is proved for primitive `χ` mod `q > 1`, `T ≥ 0`: `Families.Ported.Zero.zerosI_finite` (`Families/Ported/Zero/Bridge.lean`); `q = 1` has weight `ω(1) = w(1/Q) = 0` once `Q > 1/η`. |
| `p(C)` | `pC C = 2 − sInf (Qf (FC C) '' {f | AdmissibleWindow f})` (Variational.lean) | `AdmissibleWindow`: `f ≥ 0`, even, `supp ⊂ [−1,1]`, `∫f = 1`, **`f ∈ L²`** (implicit in the paper, needed so that junk integrals cannot lower the infimum). The double integral is written as an iterated integral (equal to the product integral on this class). |

## Named hypotheses (b) — `Families/Classical.lean`, `Families/Classical/Reductions.lean`

| Lean | TeX / source | Flag | Note |
|---|---|---|---|
| `MV_LargeSieve` (= `∃ C₀, MVLargeSieveMult C₀ ∧ MVLargeSieveAdd C₀`) | `eq:MVLS` (display (4.1), in the proof of Lemma 4.2); additive LS displayed in the proof of `prop:TIsharp` (Proposition 6.24); MV73, IK Thms 7.7, 7.13 | **weaker** | an unspecified absolute constant `C₀` instead of `1` (every use is an `O(·)` bound; the band constant only needs `O(1)`). Both forms bundled (MV73 is the additive form, 7.13 its multiplicative corollary). Intervals `[N₀, N₀+K)`, any `N₀ ∈ ℤ`; real `Q ≥ 1`, sum over `q ≤ ⌊Q⌋`. |
| `Montgomery69_Density` (`Ndens`) | `eq:Montuniform` (display (4.5)), the consequence of `eq:Montgomery` (display (4.4)) = Montgomery 1969 Thm 1 derived in §4.4 (`sec:exterior`) | **weaker** (a consequence) | `∃ C, c > 0, C₁`: `≤ C (Q²T')^{1−cδ}(log QT')^{C₁}` for `0 ≤ δ ≤ ½`, `Q ≥ 1`, `T' ≥ 2` (the TeX's `eq:Montuniform` is `c = 4/3`, `C₁ = 13`). Weakened because the log power 13 is not needed: the paper says (l. 529) any such bound suffices after adjusting `B₁` and the bad-character height `Q^{a|δ|}`, `0 < a < 2c`. `N(σ,T',χ)` via `∑ᶠ` and `analyticOrderNatAt` (junk values can only weaken an upper bound). **Not proved and not needed by the headline.** It is uniform in all heights, including `Q = 1` (`ζ`); the project reduces it to an unproved `t`-aspect input (`Montgomery69_Density_of_tAspect`). Used only by the conditional forms (`ZeroSideReduction`, `thmMain_of_components`, `thmMain_of_montgomery`). |
| `Hyp.Montgomery.Montgomery69_Density_upTo A` (`Families/Hyp/Montgomery/Defs.lean`) | `eq:Montuniform` restricted to `T' ≤ Q^A` (the q-aspect range; the only range `lem:bad` (Lemma 4.7) uses) | **weaker** than `Montgomery69_Density` (extra hypothesis `T' ≤ Q ^ A`); **P** for every `A > 0` | `Montgomery69_Density_upTo_proof A hA` (`c = 1/(16(2+A))`, `C₁ = 6`). The headline uses `A = 1` (`c = 1/48`): `lem:bad` invokes the bound only at `T_j = Q^{aδ_{j+1}} ≤ Q` for `Q ≥ e²`, with `a = min(c,1)` (`shellT_le_self`). Parsing checked: the double sum is parenthesised. |
| `PNT_dlVP` | `eqB:PNT` (display (5.8)); Davenport Ch. 18 | **weaker** (deliberate) | `|θ(x) − x| ≤ C₀ x/(log x)³`, `x ≥ 2`, Mathlib's `Chebyshev.theta`. The TeX assumes `C₀ x e^{−c₀√log x}`; the proof of `lem:B2` only needs `∑_j (1+j) ε(2^{j−1}) < ∞` (`eqB:B2err`). The proof of `lem:B2` in this project uses this form. |
| `StirlingDigamma` (`digammaRe`) | "by Stirling"/"digamma asymptotic": proofs of `prop:trace` (Proposition 4.6), `lem:pointwise` (Lemma 4.2), `lem:mumu` (Lemma 5.1), `lem:muLambda` (Lemma 5.2) | exact (as used) | for `𝔞 ∈ {0,1}`, `ψ = logDeriv Γ`: (i) `|Re ψ((½+𝔞+it)/2) − log(t/2)| ≤ C/t`, `t ≥ 1`; (ii) `≤ C log(|t|+2)`, all `t`; (iii) `|d/dt Re ψ| ≤ C/t`, `t ≥ 1`. Used only inside the two reductions. |
| `lemWH_Statement` | `lem:WH` (Lemma 6.1) | exact | **P**: proved as `lemWH` (`Families/Wired/Phase2.lean`). |
| `lemRvM_lower_Statement` | `lem:RvM` (Lemma 4.1) | **weaker** | only the lower half, in `o(1)` form: `N ≥ (1−δ)HTℓ/(2π)` for large `Q`, uniformly in `T`. Part of the conclusion of `ZeroSideReduction` (not a separate hypothesis). |
| `ZeroSideReduction` | `prop:zero` (Proposition 3.6) and §4 — **paper's own, not classical**; field of `PortedReductions` | **weaker** alone (implication); together with `ClassicalInputs` equivalent to assuming its conclusion | `MV_LargeSieve → Montgomery69_Density → StirlingDigamma → lemWH_Statement → propZero_Statement ∧ lemRvM_lower_Statement`. The implication form is weaker, consumes the classical inputs explicitly, and adds `lem:RvM` (§4.1), which the assembly needs (`main.tex` l. 766, `H = o(N)`). Internal ingredients listed in the docstring. **P** (`Ported.zeroSide_proof`). Its proof uses `Montgomery69_Density` only at heights `T' ≤ Q` (`lem:bad`); the conclusion is proved unconditionally as `Ported.Zero.propZero_unconditional`, which the headline uses. |
| `SecondMomentAssembly` | `prop:second` (Proposition 5.13) and its proof, and §5 — **paper's own, not classical**; field of `PortedReductions` | **weaker** alone (implication); together with `ClassicalInputs` equivalent to `lemB2 ∧ eqBMrat → propSecond` | `MV_LargeSieve → StirlingDigamma → lemWH_Statement → lemRvM_lower_Statement → lemB2_Statement → eqBMrat_Statement → propSecond_Statement`, so the (a) targets `lem:B2`, `eqB:Mrat` (and `PNT_dlVP` through `lemB2`) are genuinely consumed. |
| `ClassicalInputs` (`Families/Classical.lean`) | (b1)–(b5) | D | structure with the five classical fields (`mvLargeSieve`, `montgomery69`, `pnt`, `stirling`, `masses`). It does not contain the reductions. Only `masses` (`lem:WH`) is not a literature result; it is elementary and proved (`lemWH`). |
| `PortedReductions` (`Families/Classical/Reductions.lean`) | (b6)–(b7) | D | structure with the two fields `zeroSide : ZeroSideReduction`, `secondMoment : SecondMomentAssembly`. **The paper's own §4/§5, not classical:** it assumes `prop:zero`, the lower half of `lem:RvM` and `prop:second` (given `lem:B2`, `eqB:Mrat`). Kept separate from `ClassicalInputs` so that the paper's own reductions are not presented as classical inputs. |

## Lemma 1 and orthogonality (`lemma-toeplitz-C.tex`) — `Families/Toeplitz.lean`

| Lean | TeX | St. | Note |
|---|---|---|---|
| `sum_primChars_eq` | IK (3.9), proof of `lem:toeplitz`(i) | P | `∑*_χ χ(n)χ̄(m) = ∑_{d∣q, d∣n−m} φ(d)μ(q/d)` for `(nm,q)=1`. Proved via full orthogonality + conductor decomposition + Möbius inversion. |
| `sum_primChars_eq_zero_of_not_coprime`, `phiStar_eq` | same | P | `φ*(q) = ∑_{d∣q} φ(d)μ(q/d)`. |
| `Δ_eq_general`, `Δ_diag` | proof of `lem:M2`, `eq:Kdiag`-line | P | general formula for `Δ(n,m)`; diagonal `∑ω(q)φ*(q)1[(n,q)=1]`. |
| `toeplitz_identity` | `lem:toeplitz`, first claim | P | `Δ(n,m) = k_ω(n−m)` for `Q`-rough `n,m`; `kω` defined exactly as in the TeX (sums truncated where `ω = 0`). |
| `Δ_rough_shift_invariant` | "depends only on `n−m`" | P | |
| `kω_eq_ramanujan` | `lem:toeplitz`, `k_ω = ∑_e Ω(e)c_e` with `eqC:Omega` | P | `Ω` defined by the first form of `eqC:Omega`; second form is `Ωlev_eq_second_form` (LemmaS.lean). |
| `famForm_eq_levelForm_Ω` | `eqC:farey` | P | `y^*Δy = ∫|S_y|² dμ_Ω` on `Q`-rough `y`. |
| `kω_zero`, `muΩ_mass` | `k_ω(0) = H`, `μ_Ω(𝕋) = H` | P | |
| `famForm_eq_sum` | definition of `x^*Δx` | P | |
| `gauss_transfer` | `lem:gauss` | P | exact statement. |

## Lemma S, Lemma Ω(b), Schur/M2 — `LemmaS.lean`, `Schur.lean`, `Glue.lean`

| Lean | TeX | St. | Note |
|---|---|---|---|
| `levelForm_eq_sum`, `toeplitz_posSemidef`, `toeplitz_mono`, `levelForm_mono` | proof of `lem:S` | P | a positive Farey-type measure has PSD Toeplitz matrix; monotone in the weights. |
| `Ωlev_eq_second_form` | `eqC:Omega` (second form) | P | |
| `lemOmega_b` | `lem:Omega`(b) | P | `Ω^-(e) ≤ m(e/Q)`. |
| `lemmaS` | `lem:S`: `T_Ω ⪯ T^+ ⪯ T^♮`, `T^+, T^♮ ⪰ 0` | P | as `Matrix.PosSemidef` on `ℂ^I`. |
| `lemmaS_forms`, `lemmaS_rough` | `lem:S` (form version; last claim `y^*Δy ≤ y^*T^♮y` on rough `y`) | P | |
| `lemmaS_lambda_of_dual` | `lem:S` duality bound | I | from `lemDual_Statement`: `y^*T^♮y ≤ (1+κ²) sup_θ(μ^♮*k_ς)(θ)‖y‖²`. |
| `schur_test` | Schur test (`lem:M2`, `lem:dual` step 2) | P | stated for kernels with `|A(n,m)| = |A(m,n)|`; bounds `|x^*Ax|`. |
| `sum_div_totient_le` | `∑_{j≤x} j/φ(j) ≤ (ζ(2)ζ(3)/ζ(6))x` | P | **constant 2** instead of 1.9436; proved via a partial Euler product (≤ 1.9983). |
| `sum_card_divisors_le` | `∑_{h≤K} τ(h) ≤ K(1+log K)` | P | |
| `offdiag_bound`, `Δ_offdiag_le` | `|Δ(n,m)| ≤ 1.95 w_max Q τ(|n−m|)` | P | **constant 2 instead of 1.95** (needs `Q > 0`). |
| `short_interval_abstract`, `lemM2` | `lem:M2` | P | **exact paper statement** `x^*Δx ≤ (H + 4w_max QK(1+log K))‖x‖²` (the paper's 4 = 2·1.95 rounded up; here 4 = 2·2). Hypotheses `Q > 0`, `K ≥ 1`. |

## Lemma A block (`lemma-A.tex`) — `LemmaA.lean`, `Spokes.lean`, `Glue.lean`

| Lean | TeX | St. | Note |
|---|---|---|---|
| `Pw`, `Rw`, `Cw`, `k0`, `kper`, `fareyConv`, `rhoCount` | `eqA:Pw`, `eqA:Rw`, `k_0`, `k_ς`, `𝔪*k_ς`, `eqA:rho` | D | `Pw`, `rhoCount` written as finite sums (terms vanish beyond the cut). |
| `lemWH_Statement` | `lem:WH` | (b); P | exact (absolute `c₀`, `Q ≥ 2`); stated in `Families/Classical.lean`, proved as `lemWH`. |
| `lemWH_ratio_Statement` | `lem:WH` "in particular" | S (c) | only `W/H → C_G` (the rate `O(V_w I_w^{-1}Q^{-1/2})` is implied by `lemWH` but not separately stated). |
| `lemDual` | `lem:dual` | P (a) | **Statement-audit fix:** hypothesis `0 ≤ M` added — without it the statement was false (`s = ∅`, `M < 0`); implicit in the TeX (max over a nonempty positive measure). `lemmaS_lambda_of_dual` (P) derives `0 ≤ M` from `natConv_nonneg`. "Max over atoms" replaced by an arbitrary upper bound `M` (equivalent). Atoms distinct mod 1. |
| `propCount` | `prop:count` | P (a) | Dirichlet approximation `u/v` supplied as hypotheses (any valid choice). **Moved from (c) to (a)**: `lem:C` (Lemma 6.20) uses it in its proof. |
| `Spokes.spokeEquiv`, `gcd_fwd`, `mem_farey_iff`, `sub_eq_spoke`, `isolated_point` | proof of `prop:count`: `SL₂(ℤ)` change of variables, gcd preservation, `b/q−u/v = k/(qv)`, isolated point `k=0` | P | finite combinatorial core. |
| `Spokes.sum_coprime_eq_moebius`, `sum_moebius_div` | Möbius over `d∣k`; `∑_{d∣k}μ(d)/d = φ(k)/k` | P | |
| `lemA_Statement` | `lem:A` | S (c) | `Q₀(ε, V_w/c_w)` encoded as uniformity over all `W` with `V_w/c_w ≤ B`. |
| `wSharp_Vw_cw` (`Weights.lean`) | `lem:A`, sharp weight: `V_w = 2η^{-2}`, `c_w = (6/π²)log(1/η)` | P | |
| `wSharpWeight`, `wSmoothWeight` (`Weights.lean`) | `eq:logwide` are admissible | P | `I_w = log(1/η)` for the sharp weight; `I_w > 0` for the smooth one. |
| `Rw_le` (`Weights.lean`) | "`R_w ≤ w_max/c_w < ∞`" | P | |
| `corLmultA_Statement` / `corLmultA_of'` | `cor:LmultA` | I | proved from `lemA_Statement` + `lemWH_ratio_Statement` (+ proved `gauss_transfer`, `CG_pos`). `Λ_mult(K) ≤ B` is `LmultLE` (intervals in `[1,Q²]`). |
| `lemHarm_Statement` | `lem:harm` | S (c) | left limits written as `∑_{k<y}`. `B_φ`, `c_φ` defined by their series/`ζ` formulas. |
| `lemRwlog_Statement`, `lemRwlog_numeric_Statement` | `lem:Rwlog` | S (c) | **weaker**: only for admissible `W` of the form `u^{-2}h(log 1/u)` (the TeX allows any integrable quasi-concave `h`); quasi-concavity as `OrdConnected {h > λ}` for all `λ`. |

## Lemma C block (`lemma-toeplitz-C.tex`) — `LemmaC.lean`

| Lean | TeX | St. | Note |
|---|---|---|---|
| `fS`, `RS`, `Rm`, `CT`, `CTp`, `natConv`, `sigma0m`, `sigma1m` | `def:RS`, `eqC:RS`, `σ₀⁻`, `σ₁⁻` | D | `S` ranges over all `Finset ℕ` (non-primes in `S` are irrelevant to `f_S`). |
| `lemOmega_ac`, `lemOmega_d`, `lemOmega_e` | `lem:Omega` (a),(c),(d),(e) | P (a) | (b) is proved (`lemOmega_b`); the clause "`m(u) = 0` for `u > 1/2`" of (c) is proved (`mfun_eq_zero_of_gt_half`, `Weights.lean`). (e): Lipschitz constant `‖h'‖_∞` as `LipschitzWith`. |
| `lemfS` | `lem:fS` (i)–(iv) | P (a) | (iii): the "primes `p > P` contribute ≤ 3.2 log P/P³" clause omitted; (iv): only the consequence `R_S ≤ R_{S₁} + ½δ_{S₂} sup R_{S₁}` (not the convolution identity). |
| `lemC` | `lem:C` | P (a) | stated in `ℝ≥0∞` (no finiteness of `C_T^+` presupposed); `Q₁ = Q₁(ε)` uniform in `w`, as in the TeX. |
| `propSharpLS` | `prop:sharpLS` | P (a); theorem takes `lemWH_Statement` | for the `μ^♮` form (`T^♮`); absolute constant `c` existential; assumes `C_T^+ < ∞`. `T^+` and `Δ` versions follow by `lemmaS`, `lemmaS_rough`. |
| `lemCTlimit` | `lem:CTlimit` | P (a) | the final `C_T^+` bounds carry the TeX's side condition `L_η ≥ 3`; the intermediate bound `sup R^m ≤ 8.7/I_w` is not separately stated. |
| `propCTfixed_Statement` | `prop:CTfixed` | S (c) | `δ_{P₀}` replaced by its bound `5.83·10⁻⁵`; far-field (a) stated a.e.; far-field (b) (for `R^m`) **omitted**. |

## Lemma B / majorant block (`lemma-B-majorant.tex`) — `PrimeSide.lean`

| Lean | TeX | St. | Note |
|---|---|---|---|
| `PrimeSetup` | `sec:parameters`, `sec:explicit` | D | fixed data `a₀,A₀,λ,ε₁,θ,ψ,ε₃,Υ₀,ψ_j` with the stated properties as fields. |
| `aVec`, `LamR`, `Rj`, `aSharp`, `bVec`, `Schi`, `g`, `Φ`, `𝒦`, `hatJ`, `ratioForm` | `eq:an`, `Λ_R`, `R_j`, `a♯`, `b`, `S_χ[x]`, `g`, `Φ`, `eq:Delta`, `\hat{1_J}` | D | vectors supported on `[1, Y]`. |
| `lemB1` | `lem:B1` | P (a) | constant depends on `(A, ε₃)` and the fixed data. |
| `eqBMrat` | `eqB:Mrat` | P (a) | without the harmless factor `1/(2π²)`. |
| `lemB2` | `lem:B2` | P (a); theorem takes `PNT_dlVP` | (Note: `eqB:norms` uses step (4) with `h ≡ 1`, not `Integrable`; see the theorem's docstring.) `h` may depend on `Q` through constants `C_i`; **added hypothesis `Integrable h`** (the paper's `h` has compact support; without it Lean's junk value `∫ = 0` would make the statement false); the "more precisely" local-density refinement is not stated. |
| `lemM1` (+ `PrimeSetup.Φ_sq_eq`, `kernel_factorisation`, `ratioForm_factorisation`) | `lem:M1`: `𝒦(n,m) = ∫ g Ĵ(u−log n)\overline{Ĵ(u−log m)}` and `∑y_ny_mΔ𝒦 = ∫g x_y^*Δx_y` | P | `M1.lean`; includes the convolution theorem `Φ² = ĝ`. |
| `lemM1_diag` | `lem:M1`, `𝒦(n,n) = 2π|J|g(log n) + O_v(1)` | P | `M1Diag.lean`; explicit constant `∫|x||V(x)|²dx`, uniform in `Q, T, n`. |
| `lemM2` | `lem:M2` | P | in `Glue.lean` (see above). |
| `lemM3_i`, `lemM3_ii` | `lem:M3` (i), (ii) | P | (i) for any split `x = x^s + x^t`; (ii) as `e^{2δ}−e^{−2δ} ≤ 5δ`. |
| `lemM3_iii_iv` | `lem:M3` (iii), (iv) | P | `M3.lean`; statement true as written (smoothness of `ρ`, `T > 0`, `δ ≤ 1/4` not needed). |
| `propTI_Statement` | `prop:TI` | S (c) | first display (conclusion `P.ProfileBound W Ct`); the "consequently" `M_rat` bound is the input of `prop:second`. |
| `BandLS` | band hypothesis of `prop:TIsharp`: `Λ_mult(Q^{1+2ε}) ≤ (C_band + o(1))H` (the paragraph "The band constant" before Proposition 6.24) | D | intervals in `[1,Q²]` (`LmultLE`), which contain every band interval. |
| `PrimeSetup.ProfileBound` | `eq:profile` (display (5.11)) | D | shared by `propSecond`, `propTI`, `propTIsharp` . |
| `propTIsharp` | `prop:TIsharp` | P (a); theorem takes `MV_LargeSieve`, `lemWH_Statement` | **Statement-audit fix:** `C_band` is a parameter with hypothesis `BandLS W ε C_band`, as in the TeX (the old statement hard-wired `C_band = C_w`, which needs `lem:A` and so is off the headline chain; `thm:main` uses `C_band = 2w_max/(ℰI_w)` from `eq:MVLS`). **Weaker:** extra hypothesis `ε < ε₁/4` (harmless, `ε → 0`); `ε < 1/3` added as in the TeX. **Stronger in one respect:** `BandLS` (via `LmultLE`) only covers intervals inside `[1,Q²]` (still provable: band intervals lie in `[1,Y]`). Assumes `C_T^+ < ∞`; band properties of `C̃_ε` as hypotheses; conclusion `P.ProfileBound W C̃_ε` (the TeX's `(1+ϑ*)(1+κ_T)³ = 1+o(1)`, `𝓔_TI = o(H|J|L²ℓ)`). The "Consequently" sentence is not part of the statement (it is done in the glue). |

## Main chain — `Main.lean`, `PLip.lean`, `Certificate/*`, `Constants.lean`, `Glue.lean`

| Lean | TeX | St. | Note |
|---|---|---|---|
| `Cert.ranktrace` | `lem:ranktrace` | P | restatement of `RHLinalg.rank_trace_ineq_two` from the `zeta23` dependency. |
| `Cert.BlockData`, `posIndex_offline_le`, `posIndex_rankOne_smul` | `lem:blocks` (block forms and `n₊ ≤ 1`) | P | at the level of explicit rank-one/off-line blocks; that the Gabor matrix of `L(s,χ)` has this block form (functional equation) is not formalised. |
| `Cert.BlockData.perchi` | `prop:perchi` | P | exact three inequalities, from the block data. |
| `Cert.perchi_weighted` | ω-weighted family sum (§3) | P | |
| `LS` | `hyp:LS` | D | |
| `thmConditional_Statement` | `thm:conditional` (LS(C) ⇒ p(C)) | S (off-chain); I | Not consumed by `thmMain`: the proof of `thm:main` reuses the *proof* of `thm:conditional` (`assembly_fixed` + `assemblyLimit`), not its statement. `Phase4.A.thmConditional_of_components` (I) derives it from `profileLS_Statement` (`prop:TI` with `LS(C)`, not proved), `lem:B2`, `eqB:Mrat` and the named hypotheses. |
| `PrimeSetup.certValue` | `2 − 8θ − (1−2θ)𝒬_{F}(f_v)`, `F = c·min(·,1+ε₄)` (display in the proof of `thm:conditional` (Theorem 5.16), §7.3) | D | |
| `assemblyLimit` | the limit step of §7.3 (proofs of `thm:conditional` (Theorem 5.16) and `thm:main` (Theorem 1.1)): `lem:windows` + choice of the fixed data + dominated convergence | P (a) | Not a labelled TeX result. For `1 ≤ C ≤ C_max`, `η' > 0`: `∃ P ∃ ε ∈ (0,1/3), ε < ε₁/4` with the given `a₀,A₀`, such that for every continuous `C̃ : ℝ → [1,C_max]`, `= 1` on `(−∞,1−2ε]`, `= C` on `[1+2ε,∞)`: `P.certValue C̃ ≥ p(C) − η'`. Uniform in `C̃` because `F − F_C` is supported on the band plus `O(ε₄)`. |
| `propZero_Statement`, `propSecond_Statement` | `prop:zero`, `prop:second` | D; P | they enter the headline only as conclusions of `ZeroSideReduction` / `SecondMomentAssembly`. Gabor matrix as `tsum` over the nontrivial zeros (convergence true, not proved). `propSecond` phrases its hypothesis as `P.ProfileBound W c`. Both conclusions are proved (`Ported.Zero.propZero_unconditional`, `Ported.secondMoment`). |
| `thmGauss_Statement` | `thm:gauss` | S (c); parts I/P | part (1) (general `w`) is derived by `thmGauss_general_of'` from `thm:conditional` + `lem:A` + `lem:WH`; the constant `p(C_G) ≥ 0.885912` is proved (`thmGauss_constant`). |
| `thmMain_Statement` | `thm:main` (Theorem 1.1) | D | exact up to the conventions above (`ProportionsAtLeast`; the `N_d` bound is `(1+p(1)−ε)/2 ≥ (1+p(1))/2 − ε`, i.e. slightly **stronger** than the TeX). |
| `thmMain_of_parts` | proof of `thm:main` (Theorem 1.1) in §7.3 | **P** (glue) | `lemCTlimit_Statement → propSharpLS_Statement → propTIsharp_Statement → lemB2_Statement → eqBMrat_Statement → assemblyLimit_Statement → MV_LargeSieve → StirlingDigamma → lemWH_Statement → (propZero_Statement ∧ lemRvM_lower_Statement) → SecondMomentAssembly → thmMain_Statement`, standard axioms only. Takes the zero side's *conclusion*, so no Montgomery premise. Helpers (all P): `assembly_fixed`, `CTp_ge_one`, `bandLS_of_MV`, `bandProfile_spec` (`Assembly.lean`). |
| `thmMain_of_components` | proof of `thm:main` (bundled form) | **P** (glue) | `lemCTlimit_Statement → … → assemblyLimit_Statement → ClassicalInputs → PortedReductions → thmMain_Statement`, standard axioms only; a corollary of `thmMain_of_parts`. |
| `thmMain_of_montgomery` | `thm:main`, previous headline | **P** (conditional) | `ClassicalInputsReduced → thmMain_Statement` (i.e. assumes the full `Montgomery69_Density`); a conditional variant. |
| `Ported.Zero.propZero_unconditional` | `prop:zero` + lower half of `lem:RvM` | **P** | `propZero_Statement ∧ lemRvM_lower_Statement`, no hypotheses: `propZero_of_upTo (Montgomery69_Density_upTo_proof 1 _) lemWH` and `lemRvM_lower`. `lem:bad` is `bad_count_of_upTo` / `bad_weight_of_upTo` (`Families/Ported/Zero/Bad.lean`). |
| **`thmMain`** | **`thm:main`** | **P (headline, unconditional)** | **`thmMain : thmMain_Statement`, no hypotheses**, standard axioms only: `thmMain_of_parts` applied to the (a) theorems, `Hyp.MV_LargeSieve_proof`, `Hyp.StirlingDigamma_proof`, `Hyp.PNT_dlVP_proof` (via `lemB2`), `lemWH`, `Ported.Zero.propZero_unconditional` and `Ported.secondMoment`. |
| `thmFixed_Statement` | `thm:fixed` | S (c) | hypotheses `C_T^+ ≤ …`, `R_w ≤ …` as in the TeX. **Slightly stronger in form:** every case asserts all three proportions via `ProportionsAtLeast` with the stated `p` (so `N_d/N ≥ (1+p)/2`, e.g. `0.95775` where the TeX prints `0.9577`; and `N^*_0`, `N_d` also for the Gauss-route case (iii), where the TeX states only `N^s_0`). Both follow from `thm:conditional` and the certificates. |
| `lemPLip` / `pC_antitone_lip` | `lem:pLip` | P | `PLip.lean`; no extra hypothesis. |
| `thmMain_constant`, `thmGauss_constant` | constants in `thm:main`, `thm:gauss` | P | `p(1) ≥ 0.932282`; `p(C_G) ≥ 0.885912`. |
| `pC_ge_of_admissible`, `pC_one_ge`, `pC_12688_ge` | `prop:cert` rows `C = 1`, `C = 1.2688` | P | see `Certificate/Numerics.lean`, `Data.lean`; kernel `decide`, no `native_decide`. |
| `Ecal_pos`, `Ecal_le`, `CG_pos`, `one_lt_CG` | `ℰ > 0`, `C_G > 1` | P | |
| `CG_le` / `CG_le_12688`, `Ecal_ge_047914` | `C_G = 1.268773… ≤ 1.2688`, `ℰ ≥ 0.47914` | P | `Certificate/Ecal.lean`: kernel-checked (`decide +kernel`) partial Euler product over `p ≤ 50000` plus a proved telescoping tail bound; no `native_decide`. |
| `pC_CG_ge_of`, `thmGauss_constant` | `p(C_G) ≥ 0.885912` | P | from `lem:pLip`, `pC_12688_ge` and `CG_le` (all P). |

## Not stated

- `lem:envelope`, `lem:gabor`, `lem:explicit`, `lem:pointwise`, `prop:finitecentre`, `lem:firstmoment`, `prop:trace`, `lem:bad`, `prop:tail`, `lem:mumu`, `lem:muLambda`, `lem:ss`, `rem:optimal`: main-text zero-side and prime-side ingredients, not stated as separate `_Statement` definitions. They are proved as internal lemmas of the proofs of `ZeroSideReduction` / `SecondMomentAssembly` (listed in their docstrings). `lem:RvM` is stated only in its lower half (`lemRvM_lower_Statement`, output of `ZeroSideReduction`); `lem:windows` is folded into `assemblyLimit`. (The internal lemmas are in `Families/Ported/Zero/*` and `Families/Ported/Second/*`; e.g. `lem:bad` is `Ported.Zero.bad_count_of_upTo` / `bad_weight_of_upTo`, with the height `Q^{a|δ|}`, `a = min(c,1)`, allowed by §4.4 (`sec:exterior`), the paragraph before `eq:Montuniform`.)
- `prop:cert` rows `C = 1.0434, 1.0911, 1.2890, 1.3055, 1.3448` (`thm:fixed`): only the two rows used by `thm:main` and `thm:gauss` are certified.

**A precedence trap, fixed.** `lemB2_Statement`'s right-hand side reads `(1 + δ) * (∫ s, ℓ·F_b(s/ℓ)·h(s)) + C·hmax·ℓ`.
An earlier version omitted the parentheses, and Lean's precedence then put the `+ C·hmax·ℓ` term inside the
integral, which is not what `lem:B2` says. The corrected statement is pinned by an `rfl` check
(`Families/Wired/Phase3.lean`).
