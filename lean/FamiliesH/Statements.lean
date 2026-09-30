/-
# Theorem 1.4(a): the component statements (§9)

Each `…_Statement` below is the Lean form of one labelled result of §9 of the paper (`STATEMENTS-H.md`
maps the numbering). They are proved in `FamiliesH.Components`; the
glue in `FamiliesH.Glue` / `FamiliesH.Headline` reduces the headline to them. `STATEMENTS-H.md` gives the
Lean ↔ TeX correspondence and the faithfulness notes.

Classification: items consumed directly by the headline glue are marked (glue); items that are
ingredients of those proofs (not consumed by the glue) are marked (ingredient).
-/
import FamiliesH.Setup

noncomputable section

open scoped BigOperators ComplexConjugate ArithmeticFunction.Moebius
open scoped ENNReal ContDiff
open ArithmeticFunction Finset MeasureTheory Filter Topology

namespace Families.Hybrid

open Families

/-! ## Zero side (§9.2) -/

/-- (glue) **`lem:RvMH`, lower half** (Lemma 9.2): for fixed `w`, `a₀ > 0`, `κc > 0`, uniformly for
`ℓ^{a₀} ≤ T ≤ Q^{κc}`: `N ≥ (1 − o(1)) H T ℓ_*/(2π)`, `ℓ_* = log(QT)`. (The TeX states the two-sided
asymptotic; only the lower bound is consumed downstream, as in `Families`.) -/
def lemRvMH_lower_Statement : Prop :=
  ∀ (W : Weight) (a0 kc : ℝ), 0 < a0 → 0 < kc → ∀ δ : ℝ, 0 < δ → ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
    ∀ T ∈ cellHeights a0 kc Q,
      (1 - δ) * (W.H Q * T * ellS Q T / (2 * Real.pi)) ≤ Nfam W Q T

/-- (glue) **`prop:zeroH`** (Proposition 9.9): for every `B > 0`, uniformly in the cell,
`N^s_0, N^*_0 ≥ (2−8θ)N − 𝔐 − o(N) − O_B(ℓ^{-B}(H𝔐)^{1/2})` and
`N_d ≥ ½((3−8θ)N − 𝔐) − o(N) − O_B(ℓ^{-B}(H𝔐)^{1/2})`. The same shape as
`Families.propZero_Statement`, with the hybrid `𝔐` (`L = λℓ_*`) and heights `ℓ^{a₀} ≤ T ≤ Q^{κc}`. -/
def propZeroH_Statement : Prop :=
  ∀ (P : HSetup) (W : Weight) (τ₀ B δ : ℝ), 0 < B → 0 < δ → ∃ C Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
    ∀ T ∈ P.heights Q,
      let N := Nfam W Q T
      let M := P.Mfrak W Q T τ₀
      let err := δ * N + C * Real.log Q ^ (-B) * Real.sqrt (W.H Q * M)
      (2 - 8 * P.θ) * N - M - err ≤ Ns0 W Q T ∧
      (2 - 8 * P.θ) * N - M - err ≤ Nstar0 W Q T ∧
      ((3 - 8 * P.θ) * N - M) / 2 - err ≤ Nd W Q T

/-! ## Size facts (Lemma 9.1) -/

/-- (ingredient) **`lem:sizes`** (Lemma 9.1, (S1)–(S4)), with the localisation exponent
`ε₅ = min(ε, ε₁)/(4(1+κc))` chosen after the band parameter `ε ∈ (0, 1/(8(1+κc))]` ((9.3)),
`δ = T^{−1+ε₅}`, `κ_loc = T^{−ε₅/2}`, `K(u) = 5δe^u + 1`. -/
def lemSizesH_Statement : Prop :=
  ∀ (P : HSetup) (ε : ℝ), 0 < ε → ε ≤ 1 / (8 * (1 + P.kc)) →
    let ε₅ := min ε P.ε₁ / (4 * (1 + P.kc))
    ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ P.heights Q,
      -- (S1)
      (P.Y Q T ≤ Q ^ (2 - P.ε₁) * T ^ (1 - P.ε₁) ∧ 2 * P.Y Q T < (Q * T) ^ 2) ∧
      -- (S2)
      (∀ u : ℝ, u < P.L Q T →
        (u ≤ (1 - ε) * ellS Q T → 5 * T ^ (-1 + ε₅) * Real.exp u + 1 ≤ Q ^ (1 - ε / 2)) ∧
        (u ≤ (1 + ε) * ellS Q T → 5 * T ^ (-1 + ε₅) * Real.exp u + 1 ≤ Q ^ (5 / 4 : ℝ)) ∧
        5 * T ^ (-1 + ε₅) * Real.exp u + 1 ≤ Q ^ (2 - P.ε₁ / 2)) ∧
      -- (S3)
      (∀ j : ℕ, (2 : ℝ) ^ j ≤ 2 * P.Y Q T →
        (P.Rj Q T j : ℝ) ≤ 2 * P.Y Q T / (Q * T) ∧
        (P.Rj Q T j : ℝ) ≤ ((2 : ℝ) ^ j) ^ (1 / 2 - P.ε₃)) ∧
      -- (S4)
      1 + (T ^ (-(ε₅ / 2)))⁻¹ ≤ 2 * Q ^ (P.ε₁ / 8)

/-! ## Flattening (§9.3) -/

/-- (ingredient) **`lem:B1H`** (Lemma 9.11, first claim): for every `χ ∈ 𝓕`, `|t| ≤ 3T`, `A > 0`:
`S_χ[a♯](t) ≪_A Q^{-A}`, uniformly in the cell. -/
def lemB1H_Statement : Prop :=
  ∀ (P : HSetup) (W : Weight) (A : ℝ), 0 < A → ∃ C Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
    ∀ T ∈ P.heights Q, ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), InFamily W Q q χ →
    ∀ t : ℝ, |t| ≤ 3 * T → ‖P.Schi χ Q T (P.aSharp Q T) t‖ ≤ C * Q ^ (-A)

/-- (glue) **`eqB:MratH`** (Lemma 9.11, second claim, in the `∀ A` form of `Families.eqBMrat_Statement`):
`∑ a_n a_m Δ 𝒦 = ∑ b_n b_m Δ 𝒦 + O(Q^{-A})`, uniformly in the cell. -/
def eqBMratH_Statement : Prop :=
  ∀ (P : HSetup) (W : Weight) (A : ℝ), 0 < A → ∃ C Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
    ∀ T ∈ P.heights Q,
      ‖P.ratioForm W Q T (P.aVec Q T) - P.ratioForm W Q T (P.bVec Q T)‖ ≤ C * Q ^ (-A)

/-- (glue) **`lem:B2H`** (Lemma 9.12), in the form of `Families.lemB2_Statement` with `ℓ` replaced by
`ℓ_*`: `∑_n |b_n|² h(log n) ≤ (1+o(1)) ∫ ℓ_* F_b(s/ℓ_*) h(s) ds + O(‖h‖_∞ ℓ_*)`, `F_b = Families.Fb`,
the integral parenthesised as in `Families.lemB2_Statement`. -/
def lemB2H_Statement : Prop :=
  ∀ (P : HSetup) (Cs : ℕ → ℝ) (δ : ℝ), 0 < δ → ∃ C Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
    ∀ T ∈ P.heights Q, ∀ (h : ℝ → ℝ) (hmax : ℝ), ContDiff ℝ ∞ h → (∀ y, 0 ≤ h y) →
      Integrable h → (∀ y, h y ≤ hmax) → (∀ i y, |iteratedDeriv i h y| ≤ Cs i * hmax) →
      ∑ n ∈ P.range Q T, P.bVec Q T n ^ 2 * h (Real.log n)
        ≤ (1 + δ) * (∫ s, ellS Q T * Fb P.ε₃ (s / ellS Q T) * h s) + C * hmax * ellS Q T

/-! ## Time localisation at scale `T^{−1+ε₅}` (§9.3) -/

/-- The localisation cut-off `ρ ∈ C_c^∞((−2,2))`, `0 ≤ ρ ≤ 1`, `ρ = 1` on `[−1,1]` (§5.8). -/
def IsLocCutoff (ρ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ ρ ∧ (∀ ξ, 0 ≤ ρ ξ ∧ ρ ξ ≤ 1) ∧ (∀ ξ, |ξ| ≤ 1 → ρ ξ = 1) ∧ (∀ ξ, 2 ≤ |ξ| → ρ ξ = 0)

/-- (ingredient) **`lem:M1H`** ((9.11); Lemma 5.9 for `L = λℓ_*`): the time–frequency
factorisation `𝒦(n,m) = ∫ g(u) \hat{1_J}(u−log n) \overline{\hat{1_J}(u−log m)} du` and hence
`∑ y_n y_m Δ 𝒦 = ∫ g(u) x_y(u)^*Δ x_y(u) du`. -/
def lemM1H_Statement : Prop :=
  ∀ (P : HSetup) (Q T : ℝ), 1 < Q → 0 < T →
    (∀ n m : ℕ, 1 ≤ n → 1 ≤ m →
      P.𝒦 Q T n m = ∫ u, (P.g Q T u : ℂ) * P.hatJ T (u - Real.log n) *
        conj (P.hatJ T (u - Real.log m))) ∧
    (∀ (W : Weight) (y : ℕ → ℝ),
      P.ratioForm W Q T y = ∫ u, (P.g Q T u : ℂ) * famForm W Q (P.rangeZ Q T) (P.xVec Q T y u))

/-- (ingredient) **`lem:M3H` (iii)** (§9.3; Lemma 5.11(iii) for `L = λℓ_*`, every
`δ ∈ (0,1/4]`): with `x^s_n = x_n ρ((log n − u)/δ)`,
`∫ g(u) ‖x^s(u)‖² c(u) du ≤ ∑_n |y_n|² 𝒦(n,n) sup{c(u) : |u − log n| < 2δ}` for bounded `c ≥ 0`. -/
def lemM3H_iii_Statement : Prop :=
  ∀ (P : HSetup) (ρ : ℝ → ℝ), IsLocCutoff ρ →
    ∀ (Q T δ : ℝ), 1 < Q → 0 < T → 0 < δ → δ ≤ 1 / 4 → ∀ y : ℕ → ℝ,
    let xs : ℝ → ℤ → ℂ := fun u n => P.xVec Q T y u n * ρ ((Real.log n.toNat - u) / δ)
    ∀ (c : ℝ → ℝ) (Cmax : ℝ), (∀ u, 0 ≤ c u ∧ c u ≤ Cmax) →
      ∫ u, P.g Q T u * normSq (P.rangeZ Q T) (xs u) * c u ≤
        ∑ n ∈ P.range Q T, y n ^ 2 * (P.𝒦 Q T n n).re *
          sSup (c '' {u | |u - Real.log n| < 2 * δ})

/-- (ingredient) **`lem:M3prime`** (Lemma 9.13, tails by dyadic shells), with the multiplicative large
sieve constant `C₀` made explicit (the formal large sieve `Families.Hyp.MV_LargeSieve_proof` has
`C₀ = 17/4`; the TeX uses `C₀ = 1`): for `y` on `[1, Y]`, `δ ∈ (0,1/4]`, `k₀ = ⌈log₂(1/δ)⌉` and measurable
`g₁ : ℝ → [0, g_∞]`,
`∫ g₁(u) x^t(u)^*Δx^t(u) du ≤ 48 C₀ g_∞ w_max (k₀+4) ((Q²+1)/δ + (k₀+3)Y) ‖y‖²`,
`x^t = x_y − x^s`. -/
def lemM3primeH_Statement : Prop :=
  ∀ (C₀ : ℝ), MVLargeSieveMult C₀ → 0 ≤ C₀ →
  ∀ (P : HSetup) (W : Weight) (ρ : ℝ → ℝ), IsLocCutoff ρ →
  ∀ (Q T δ : ℝ), 1 ≤ Q → 0 < T → 0 < δ → δ ≤ 1 / 4 →
  ∀ (y : ℕ → ℝ) (g1 : ℝ → ℝ) (ginf : ℝ), Measurable g1 → (∀ u, 0 ≤ g1 u ∧ g1 u ≤ ginf) →
    let xt : ℝ → ℤ → ℂ := fun u n =>
      P.xVec Q T y u n * (1 - ρ ((Real.log n.toNat - u) / δ))
    let k0 : ℕ := ⌈Real.logb 2 (1 / δ)⌉₊
    ∫ u, g1 u * famForm W Q (P.rangeZ Q T) (xt u) ≤
      48 * C₀ * ginf * W.wmax * ((k0 : ℝ) + 4) * ((Q ^ 2 + 1) / δ + ((k0 : ℝ) + 3) * P.Y Q T) *
        ∑ n ∈ P.range Q T, y n ^ 2

/-- (ingredient) **`cor:tails`** (Corollary 9.14): the tails at the localisation scale
`δ = T^{−1+ε₅}` are negligible: for `y ∈ {a, b}`,
`(1 + κ_loc^{-1}) ∫ g(u) x^t(u)^*Δx^t(u) du = o(H|J|L²ℓ_*)` uniformly in the cell
(`κ_loc = T^{−ε₅/2}`, `ε₅ = min(ε, ε₁)/(4(1+κc))`). -/
def corTailsH_Statement : Prop :=
  ∀ (P : HSetup) (W : Weight) (ρ : ℝ → ℝ), IsLocCutoff ρ → ∀ ε : ℝ, 0 < ε →
    ε ≤ 1 / (8 * (1 + P.kc)) →
    let ε₅ := min ε P.ε₁ / (4 * (1 + P.kc))
    ∀ η : ℝ, 0 < η → ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ P.heights Q,
      ∀ y ∈ ({P.aVec Q T, P.bVec Q T} : Set (ℕ → ℝ)),
      let δ := T ^ (-1 + ε₅)
      let xt : ℝ → ℤ → ℂ := fun u n =>
        P.xVec Q T y u n * (1 - ρ ((Real.log n.toNat - u) / δ))
      (1 + (T ^ (-(ε₅ / 2)))⁻¹) * ∫ u, P.g Q T u * famForm W Q (P.rangeZ Q T) (xt u) ≤
        η * W.H Q * P.Jlen T * P.L Q T ^ 2 * ellS Q T

/-! ## The band device and the second moment (§9.3) -/

/-- `Λ_mult(K) ≤ B` for intervals of `K` integers **anywhere** in `[1, ∞)`. Unlike `Families.LmultLE`
there is no cap `N₀ + K − 1 ≤ Q²`: at polynomial height the band intervals lie in `[1, Y]` and `Y` may
exceed `Q²`. -/
def LmultLEAny (W : Weight) (Q : ℝ) (K : ℕ) (B : ℝ) : Prop :=
  ∀ N₀ : ℤ, 1 ≤ N₀ → ∀ x : ℤ → ℂ, famForm W Q (intervalZ N₀ K) x ≤ B * normSq (intervalZ N₀ K) x

/-- The band hypothesis of `prop:TIsharpH`: `Λ_mult(Q^{5/4}) ≤ (C_band + o(1)) H` for intervals anywhere
(by Lemma 9.1 (S2) every band interval has at most `Q^{5/4}` integers). `ε` is unused. (The bound `Q^{1+2ε}` of
`Families.LmultLE` would not cover the band intervals, whose length `5T^{−1+ε₅}e^u + 1` reaches `5Q^{1+ε}T^{ε+ε₅} + 1` at
`u = (1+ε)ℓ_*`; see `STATEMENTS-H.md` §5.) -/
def BandLSH (W : Weight) (_ε Cband : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
    ∀ K : ℕ, (K : ℝ) ≤ Q ^ (5 / 4 : ℝ) → LmultLEAny W Q K ((Cband + δ) * W.H Q)

/-- (glue) **`prop:TIsharpH`** (Proposition 9.18): the band device at polynomial height. The same
statement as `Families.propTIsharp_Statement` with `HSetup`, the band hypothesis `BandLSH` (intervals
anywhere) and the extra hypothesis `ε ≤ 1/(8(1+κc))` ((P4) of §9.1, with the cell top). -/
def propTIsharpH_Statement : Prop :=
  ∀ (P : HSetup) (W : Weight), CTp W ≠ ⊤ → ∀ (ε : ℝ), 0 < ε → ε < 1 / 3 → ε < P.ε₁ / 4 →
    ε ≤ 1 / (8 * (1 + P.kc)) →
    ∀ Cband : ℝ, 1 ≤ Cband → BandLSH W ε Cband →
    ∀ Ct : ℝ → ℝ, ContDiff ℝ ∞ Ct →
    (∀ α, 1 ≤ Ct α ∧ Ct α ≤ max Cband (CTp W).toReal) → (∀ α, α ≤ 1 - 2 * ε → Ct α = 1) →
    (∀ α, 1 - 3 / 2 * ε ≤ α → α ≤ 1 + 3 / 2 * ε → Cband ≤ Ct α) →
    (∀ α, 1 + ε / 2 ≤ α → (CTp W).toReal ≤ Ct α) → (∀ α, 1 + 2 * ε ≤ α → Ct α = (CTp W).toReal) →
    P.ProfileBoundH W Ct

/-- (glue, via `SecondMomentAssemblyH`) **`prop:secondH`** (Proposition 9.19): if `c : ℝ → [1,∞)` is
smooth and the profile bound holds uniformly in the cell, then `𝔐 ≤ (1−2θ) 𝒬_F(f_v) N + o(N)`,
`F(α) = c(α) min(α, 1+ε₄)`, `f_v(x) = v(x/λ)/(λa)`. -/
def propSecondH_Statement : Prop :=
  ∀ (P : HSetup) (W : Weight) (τ₀ : ℝ) (c : ℝ → ℝ), ContDiff ℝ ∞ c → (∀ α, 1 ≤ c α) →
    P.ProfileBoundH W c →
    ∀ δ : ℝ, 0 < δ → ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ P.heights Q,
      P.Mfrak W Q T τ₀ ≤
        (1 - 2 * P.θ) * Qf (fun α => c α * min α (1 + 2 * P.ε₃))
          (fun x => P.vfun (x / P.lam) / (P.lam * P.aInt)) * Nfam W Q T + δ * Nfam W Q T

/-- (glue) **`SecondMomentAssemblyH`**: the assembly of §9.3 (the analogue of
`Families.SecondMomentAssembly`): given the large sieve, Stirling, `lem:WH`, the lower half of
`lem:RvMH`, `lem:B2H` and `eqB:MratH`, `prop:secondH` holds. -/
def SecondMomentAssemblyH : Prop :=
  MV_LargeSieve → StirlingDigamma → lemWH_Statement → lemRvMH_lower_Statement →
    lemB2H_Statement → eqBMratH_Statement → propSecondH_Statement

/-! ## The variational problem at support `β` (§9.4) -/

/-- (glue) **`lem:Mbeta`** (Lemma 9.21): for `C ≥ 1` and `1 ≤ β' ≤ β ≤ 2`,
`p(β'; F_C) ≤ p(β; F_C) ≤ p(β'; F_C) + 2(β/β' − 1)`. -/
def lemMbeta_Statement : Prop :=
  ∀ C : ℝ, 1 ≤ C → ∀ β' β : ℝ, 1 ≤ β' → β' ≤ β → β ≤ 2 →
    pB β' C ≤ pB β C ∧ pB β C ≤ pB β' C + 2 * (β / β' - 1)

/-- (glue) **`lem:pLipH`** (Lemma 9.22, with the monotonicity of `Families.lemPLip_Statement`): for
`β ∈ [1,2]` and `1 ≤ C ≤ C'`: `p(β; F_{C'}) ≤ p(β; F_C)` and `p(β; F_{C'}) ≥ p(β; F_C) − (C' − C)`. -/
def lemPLipH_Statement : Prop :=
  ∀ β : ℝ, 1 ≤ β → β ≤ 2 → ∀ C C' : ℝ, 1 ≤ C → C ≤ C' →
    pB β C' ≤ pB β C ∧ pB β C - (C' - C) ≤ pB β C'

/-- (glue) **The assembly limit at support `β(κc)`** (the analogue of `Families.assemblyLimit_Statement`;
§9.4, steps (a)–(e), with `lem:windowsH`): given `1 ≤ C ≤ C_max` and `η' > 0`, there are fixed data
`P` for the cell (`P.a0 = a₀`, `P.kc = κc`) and a band parameter `ε ∈ (0,1/3)`, `ε < ε₁/4`,
`ε ≤ 1/(8(1+κc))`, such that for every continuous profile `C̃ : ℝ → [1, C_max]` with `C̃ = 1` on
`(−∞, 1−2ε]` and `C̃ = C` on `[1+2ε, ∞)`: `P.certValue C̃ ≥ p(β(κc); F_C) − η'`. -/
def assemblyLimitH_Statement : Prop :=
  ∀ (a0 kc : ℝ), 0 < a0 → 0 < kc → ∀ (C Cmax : ℝ), 1 ≤ C → C ≤ Cmax → ∀ η' : ℝ, 0 < η' →
    ∃ (P : HSetup) (ε : ℝ), P.a0 = a0 ∧ P.kc = kc ∧ 0 < ε ∧ ε < 1 / 3 ∧ ε < P.ε₁ / 4 ∧
      ε ≤ 1 / (8 * (1 + kc)) ∧
      ∀ Ct : ℝ → ℝ, Continuous Ct → (∀ α, 1 ≤ Ct α ∧ Ct α ≤ Cmax) →
        (∀ α, α ≤ 1 - 2 * ε → Ct α = 1) → (∀ α, 1 + 2 * ε ≤ α → Ct α = C) →
        pB (betaK kc) C - η' ≤ P.certValue Ct

/-- (glue) **`prop:certH`** (Proposition 9.24, the κ-table after Theorem 1.4, column `p(β(κ))`): exact rational certificates
at `κ = 1, 2, 3, 5, 10`, i.e. `β = 3/2, 4/3, 5/4, 7/6, 12/11`. The constants are the **n = 400** values of
`certify_hybrid_n400_rerun.log` (ancillary file; the paper: Proposition 9.24 and the table after Theorem 1.4, which print these
n = 400 values; n = 400 keeps the kernel checks cheap, cf. `Families.Certificate.Numerics`). -/
def certH_Statement : Prop :=
  (0.865673 : ℝ) ≤ pB (3 / 2) 1 ∧ (0.824355 : ℝ) ≤ pB (4 / 3) 1 ∧ (0.797213 : ℝ) ≤ pB (5 / 4) 1 ∧
  (0.764149 : ℝ) ≤ pB (7 / 6) 1 ∧ (0.727484 : ℝ) ≤ pB (12 / 11) 1

end Families.Hybrid
