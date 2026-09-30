/-
`lemma-toeplitz-C.tex` (§6.2), analytic part: `lem:Omega` (a),(c),(d),(e), `def:RS`, `lem:fS`,
`lem:C`, `prop:sharpLS`, `lem:CTlimit`, `prop:CTfixed`.
(`lem:toeplitz` is in `Families.Toeplitz`; `lem:S` and `lem:Omega`(b) in `Families.LemmaS`.)

Classification (see STATEMENTS.md and STATUS.md): (a) headline chain, proved — `lemOmega_ac`,
`lemOmega_d`, `lemOmega_e`, `lemfS`, `lemC`, `propSharpLS`, `lemCTlimit`;
(c) off the chain, stated only — `propCTfixed_Statement` (fixed `η`, `thm:fixed`). `propSharpLS` takes the named hypothesis
`lemWH_Statement` (`Families.Classical`), which its proof uses (proof of Proposition 6.21).
-/
import Families.LemmaA

noncomputable section

open scoped BigOperators ComplexConjugate ArithmeticFunction.Moebius ENNReal
open ArithmeticFunction Finset MeasureTheory Filter Topology

namespace Families

/-! ### Constants and local densities (`def:RS`) -/

/-- `‖w̃‖_∞ = sup_u u² w(u)`. -/
def Weight.wtmax (W : Weight) : ℝ := sSup (Set.range W.wt)

/-- `L_η = log(1/η)`. -/
def Leta (η : ℝ) : ℝ := Real.log (1 / η)

/-- `σ₀⁻ = ∑_{μ(r)=−1} 1/(r²φ(r))`. -/
def sigma0m : ℝ := ∑' r : ℕ, if μ r = -1 then 1 / ((r : ℝ) ^ 2 * Nat.totient r) else 0
/-- `σ₁⁻ = ∑_{μ(r)=−1} log r/(r²φ(r))`. -/
def sigma1m : ℝ :=
  ∑' r : ℕ, if μ r = -1 then Real.log r / ((r : ℝ) ^ 2 * Nat.totient r) else 0

/-- Prime-power values of `f_S` (`def:RS`): `1 − 1/p − 1/p²` for `p ∉ S`; for `p ∈ S`,
`(p−2)/(p−1)` at `a = 1` and `(p−1)/p` for `a ≥ 2`. -/
def fSpp (S : Finset ℕ) (p a : ℕ) : ℝ :=
  if p ∈ S then (if a = 1 then ((p : ℝ) - 2) / (p - 1) else ((p : ℝ) - 1) / p)
  else 1 - 1 / (p : ℝ) - 1 / (p : ℝ) ^ 2

/-- The multiplicative function `f_S` (`def:RS`). -/
def fS (S : Finset ℕ) (n : ℕ) : ℝ := ∏ p ∈ n.primeFactors, fSpp S p (n.factorization p)

/-- `R_S(t) = (ℰ I_w)^{-1} ∑_{n≥1} f_S(n) w̃(nt)/n` (`eqC:RS`). -/
def RS (W : Weight) (S : Finset ℕ) (t : ℝ) : ℝ :=
  (Ecal * W.Iw)⁻¹ * ∑ n ∈ Finset.Icc 1 ⌊1 / t⌋₊, fS S n / n * W.wt (n * t)

/-- `R^m(t) = (ℰ I_w)^{-1} ∑_{k≥1} φ(k) m̃(kt)/k²` (`eqC:RS`); `m̃(kt) = 0` for `kt > 1/2`. -/
def Rm (W : Weight) (t : ℝ) : ℝ :=
  (Ecal * W.Iw)⁻¹ * ∑ k ∈ Finset.Icc 1 ⌊1 / t⌋₊, (Nat.totient k : ℝ) / (k : ℝ) ^ 2 * mt W (k * t)

/-- `C_T(w) = sup_S ess sup_{t>0} R_S(t)` (sup over finite sets of primes; non-primes in `S` are
irrelevant to `f_S`). -/
def CT (W : Weight) : ℝ≥0∞ :=
  ⨆ S : Finset ℕ, essSup (fun t => ENNReal.ofReal (RS W S t)) (volume.restrict (Set.Ioi (0 : ℝ)))

/-- `C_T^+(w) = sup_S ess sup_{t>0} R^+_S(t)`, `R^+_S = R_S + R^m`. -/
def CTp (W : Weight) : ℝ≥0∞ :=
  ⨆ S : Finset ℕ,
    essSup (fun t => ENNReal.ofReal (RS W S t + Rm W t)) (volume.restrict (Set.Ioi (0 : ℝ)))

/-- `(μ^♮ * k_ς)(θ) = ∑_e (Ω(e) + m(e/Q)) ∑*_{c mod e} k_ς(θ − c/e)`. -/
def natConv (W : Weight) (Q ς θ : ℝ) : ℝ :=
  ∑ e ∈ levels Q, aNat W Q e * ∑ c ∈ reduced e, kper ς (θ - c / e)

/-! ### `lem:Omega` (a), (c), (d), (e) -/

/-- **`lem:Omega`(a),(c).** `|Ω(e)| ≤ 3‖w̃‖_∞ min{(Q/e)², η^{-2}}`; `m(u) ≤ 3‖w̃‖_∞ min{u^{-2}/4, η^{-2}}`
and `m(u) = 0` for `u > 1/2`. -/
def lemOmega_ac_Statement : Prop :=
  ∀ (W : Weight) (Q : ℝ), 0 < Q →
    (∀ e : ℕ, 1 ≤ e → |Ωlev W Q e| ≤ 3 * W.wtmax * min ((Q / e) ^ 2) (W.η⁻¹ ^ 2)) ∧
    (∀ u : ℝ, 0 < u → mfun W u ≤ 3 * W.wtmax * min (u⁻¹ ^ 2 / 4) (W.η⁻¹ ^ 2)) ∧
    (∀ u : ℝ, 1 / 2 < u → mfun W u = 0)

-- `lemOmega_ac` is proved in `Families/Wired/Phase1.lean` (wired from Families/Phase1/*).

/-- **`lem:Omega`(d).** If `w̃` is constant on `[η,1]`, then `m = 0` on `[η,∞)` and
`Ω(e) > 0` for `ηQ ≤ e ≤ Q`. -/
def lemOmega_d_Statement : Prop :=
  ∀ (W : Weight), (∃ c : ℝ, ∀ u, W.η ≤ u → u ≤ 1 → W.wt u = c) →
    (∀ u, W.η ≤ u → mfun W u = 0) ∧
    ∀ (Q : ℝ), 0 < Q → ∀ e : ℕ, W.η * Q ≤ e → (e : ℝ) ≤ Q → 0 < Ωlev W Q e

-- `lemOmega_d` is proved in `Families/Wired/Phase1.lean` (wired from Families/Phase1/B/*).

/-- **`lem:Omega`(e).** If `w̃(u) = h(log(1/u))` (`u > 0`) with `h` `L_h`-Lipschitz, then
`m̃(u) ≤ L_h σ₁⁻` for `u ≥ η`. -/
def lemOmega_e_Statement : Prop :=
  ∀ (W : Weight) (h : ℝ → ℝ) (Lh : NNReal), LipschitzWith Lh h →
    (∀ u, 0 < u → W.wt u = h (Real.log (1 / u))) →
    ∀ u, W.η ≤ u → mt W u ≤ Lh * sigma1m

-- `lemOmega_e` is proved in `Families/Wired/Phase1.lean` (wired from Families/Phase1/B/*).

/-! ### `lem:fS` -/

/-- `G_S(k,r) = (φ(k)/k) ∏_{p | r, p ∤ k, p ∉ S}(1 − 1/p) · 1[no p ∈ S divides (k,r)]`. -/
def GS (S : Finset ℕ) (k r : ℕ) : ℝ :=
  (Nat.totient k : ℝ) / k *
    (∏ p ∈ r.primeFactors.filter (fun p => ¬ p ∣ k ∧ p ∉ S), (1 - 1 / (p : ℝ))) *
    (if ∀ p ∈ S, p.Prime → ¬ p ∣ Nat.gcd k r then 1 else 0)

/-- `g_S` (`lem:fS`(ii)): multiplicative with `g_S(p) = −1/p − 1/p²`, `g_S(p^a) = 0` (`a ≥ 2`) for
`p ∉ S`; `g_S(p) = −1/(p−1)`, `g_S(p²) = 1/(p(p−1))`, `g_S(p^a) = 0` (`a ≥ 3`) for `p ∈ S`. -/
def gS (S : Finset ℕ) (n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors,
    (if p ∈ S then
      (if n.factorization p = 1 then -1 / ((p : ℝ) - 1)
       else if n.factorization p = 2 then 1 / ((p : ℝ) * (p - 1)) else 0)
     else (if n.factorization p = 1 then -1 / (p : ℝ) - 1 / (p : ℝ) ^ 2 else 0))

/-- `c_∅ = γ + ∑_p (p^{-2}+p^{-3}) log p / (1 − p^{-2} − p^{-3})`. -/
def cEmpty : ℝ :=
  Real.eulerMascheroniConstant +
    ∑' p : Nat.Primes, (((p : ℕ) : ℝ) ^ (-2 : ℤ) + ((p : ℕ) : ℝ) ^ (-3 : ℤ)) * Real.log (p : ℕ) /
      (1 - ((p : ℕ) : ℝ) ^ (-2 : ℤ) - ((p : ℕ) : ℝ) ^ (-3 : ℤ))

/-- `c_S = c_∅ − ∑_{p∈S} log p / (p³(p−1)(1−p^{-2}−p^{-3}))`. -/
def cS (S : Finset ℕ) : ℝ :=
  cEmpty - ∑ p ∈ S.filter Nat.Prime,
    Real.log p / ((p : ℝ) ^ 3 * (p - 1) * (1 - (p : ℝ) ^ (-2 : ℤ) - (p : ℝ) ^ (-3 : ℤ)))

/-- `B = ∏_p (1 + p^{-1/2}/(p−1) + p^{-1}/(p(p−1)))`. -/
def Bconst : ℝ :=
  ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) / (((p : ℕ) : ℝ) - 1) +
    ((p : ℕ) : ℝ)⁻¹ / (((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) - 1)))

/-- `F_S(s) = ∑_{n ≤ e^s} f_S(n)/n`, `E_S(s) = F_S(s) − ℰ(s + c_S)`. -/
def ES (S : Finset ℕ) (s : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊Real.exp s⌋₊, fS S n / n - Ecal * (s + cS S)

/-- **`lem:fS`** (ii)–(iv) (part (i), the convolution identity for `f_S`, is recorded in (i) below).
(i) `f_S(n) = ∑_{kr=n, r sqfree} μ(r) G_S(k,r)/(rφ(r))`;
(ii) `f_S = 1 * g_S` and `∑_d g_S(d)/d = ℰ`;
(iii) `|E_S(s)| ≤ 2B e^{−s/2}` for `s ≥ 0`, uniformly in `S`; `B < 3.73`; `0 ≤ c_∅ − c_S < 0.168`;
(iv) for `S = S₁ ⊔ S₂`: `R_S(t) ≤ R_{S₁}(t) + ½ δ_{S₂} sup R_{S₁}`,
`δ_{S₂} = ∏_{p∈S₂}(1 + 2/(p³(p−1))) − 1`. -/
def lemfS_Statement : Prop :=
  (∀ (S : Finset ℕ) (n : ℕ), 1 ≤ n →
    fS S n = ∑ kr ∈ n.divisorsAntidiagonal.filter (fun kr => Squarefree kr.2),
      (μ kr.2 : ℝ) * GS S kr.1 kr.2 / (kr.2 * Nat.totient kr.2)) ∧
  (∀ (S : Finset ℕ) (n : ℕ), 1 ≤ n → fS S n = ∑ d ∈ n.divisors, gS S d) ∧
  (∀ S : Finset ℕ, HasSum (fun d : ℕ => gS S d / d) Ecal) ∧
  (∀ (S : Finset ℕ) (s : ℝ), 0 ≤ s → |ES S s| ≤ 2 * Bconst * Real.exp (-s / 2)) ∧
  Bconst < 3.73 ∧
  (∀ S : Finset ℕ, 0 ≤ cEmpty - cS S ∧ cEmpty - cS S < 0.168) ∧
  (∀ (W : Weight) (S₁ S₂ : Finset ℕ), Disjoint S₁ S₂ → ∀ M : ℝ, (∀ t, 0 < t → RS W S₁ t ≤ M) →
    ∀ t, 0 < t → RS W (S₁ ∪ S₂) t ≤ RS W S₁ t +
      (1 / 2) * ((∏ p ∈ S₂.filter Nat.Prime, (1 + 2 / ((p : ℝ) ^ 3 * (p - 1)))) - 1) * M)

-- `lemfS` is proved in `Families/Wired/Phase1.lean` (wired from Families/Phase1/B/*).

/-! ### `lem:C`: the local count for the positive part -/

/-- **`lem:C`.** Fix `ε ∈ (0,1)`. For `Q ≥ Q₁(ε)`, `Q ≤ K ≤ Q^{2−ε}`, `κ = Q^{−ε/4}`, `ς = κ/K`, and every
`θ`: `(μ^♮ * k_ς)(θ) ≤ ℰ I_w Q² C_T^+(w) + 𝔈` with
`𝔈 ≤ 6‖w̃‖_∞ η^{-2} Q^{2−3ε/4} + 120 V_w Q^{2−ε/4}(1+log Q)³ + 3‖w̃‖_∞(L_η+1)`.
(Written in `[0,∞]` so that no finiteness of `C_T^+` is presupposed.) -/
def lemC_Statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ Q₁ : ℝ, ∀ W : Weight, ∀ Q : ℝ, Q₁ ≤ Q → ∀ K : ℕ,
    Q ≤ K → (K : ℝ) ≤ Q ^ (2 - ε) → ∀ θ : ℝ,
    ENNReal.ofReal (natConv W Q (Q ^ (-ε / 4) / K) θ) ≤
      ENNReal.ofReal (Ecal * W.Iw * Q ^ 2) * CTp W +
      ENNReal.ofReal (6 * W.wtmax * W.η⁻¹ ^ 2 * Q ^ (2 - 3 * ε / 4) +
        120 * W.Vw * Q ^ (2 - ε / 4) * (1 + Real.log Q) ^ 3 + 3 * W.wtmax * (Leta W.η + 1))

-- `lemC` is proved in `Families/Wired/Phase1.lean` (wired from Families/Phase1/*).

/-! ### `prop:sharpLS` -/

/-- **`prop:sharpLS`.** Fix `ε ∈ (0,1)` and `w` with `C_T^+(w) < ∞`. As `Q → ∞`, uniformly over intervals of
`K ≤ Q^{2−ε}` integers: `λ_max(T^+_I) ≤ λ_max(T^♮_I) ≤ (C_T^+(w) + ϑ'_Q) H`, with
`ϑ'_Q ≤ c[(V_w + ‖w̃‖_∞η^{-2})/I_w · Q^{−ε/4}(log Q)³ + (Q^{−ε/2} + (V_w/I_w) Q^{−1/2}) C_T^+]`,
`c` absolute. Stated via the quadratic form of `μ^♮` (`= y^* T^♮ y`); the `T^+` and `Δ` versions follow from
`lem:S` and `lem:toeplitz`. -/
def propSharpLS_Statement : Prop :=
  ∃ c : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ W : Weight, CTp W ≠ ⊤ → ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
    ∀ (N₀ : ℤ) (K : ℕ), (K : ℝ) ≤ Q ^ (2 - ε) → ∀ y : ℤ → ℂ,
      levelForm (levels Q) (aNat W Q) (intervalZ N₀ K) y ≤
        ((CTp W).toReal +
          c * ((W.Vw + W.wtmax * W.η⁻¹ ^ 2) / W.Iw * Q ^ (-ε / 4) * Real.log Q ^ 3 +
            (Q ^ (-ε / 2) + W.Vw / W.Iw * Q ^ (-(1 / 2 : ℝ))) * (CTp W).toReal)) *
          W.H Q * normSq (intervalZ N₀ K) y

/- (a). The proof uses `lem:WH` (`H = ℰ I_w Q²(1 + O(V_w I_w⁻¹ Q^{-1/2}))`), which is the
named hypothesis `lemWH_Statement`. -/
-- `propSharpLS` is proved in `Families/Wired/Phase1.lean` (wired from Families/Phase1/*).

/-! ### `lem:CTlimit` -/

/-- **`lem:CTlimit`.** (1) If `w̃(u) = h(log(1/u))` with `h : ℝ → [0,1]` vanishing off `[0, L_η]` and
quasi-concave, then `sup_S ess sup_t R_S(t) ≤ 1 + (c_∅ + 4B/ℰ)/I_w ≤ 1 + 32.6/I_w`.
(2) `C_T^+(w_η) ≤ 1 + 42/L_η` and `C_T^+(w^sm_η) ≤ 1 + 83/L_η` (for `L_η ≥ 3`), hence both `→ 1`. -/
def lemCTlimit_Statement : Prop :=
  (∀ (W : Weight) (h : ℝ → ℝ), (∀ y, 0 ≤ h y ∧ h y ≤ 1) →
    (∀ y, (y < 0 ∨ Leta W.η < y) → h y = 0) → (∀ lam : ℝ, Set.OrdConnected {y | lam < h y}) →
    (∀ u, 0 < u → W.wt u = h (Real.log (1 / u))) →
    CT W ≤ ENNReal.ofReal (1 + (cEmpty + 4 * Bconst / Ecal) / W.Iw) ∧
    CT W ≤ ENNReal.ofReal (1 + 32.6 / W.Iw)) ∧
  (∀ (W : Weight) (η : ℝ), W.w = wSharpFun η → 3 ≤ Leta η →
    CTp W ≤ ENNReal.ofReal (1 + 42 / Leta η)) ∧
  (∀ (W : Weight) (η : ℝ), W.w = wSmoothFun η → 3 ≤ Leta η →
    CTp W ≤ ENNReal.ofReal (1 + 83 / Leta η))

-- `lemCTlimit` is proved in `Families/Wired/Phase2.lean` (wired from Families/Phase2/B/*).

/-! ### `prop:CTfixed`: finite reduction in `S` -/

/-- `P₀ = {2,3,5,7,11,13}`. -/
def P0 : Finset ℕ := {2, 3, 5, 7, 11, 13}

/-- **`prop:CTfixed`** ((c): only `thm:fixed` uses it) (main inequality and far field (a)). With `M_w = max_{S₁ ⊂ P₀} sup_t R_{S₁}(t)`:
`C_T^+(w) ≤ max_{S₁⊂P₀} ess sup_t (R_{S₁} + R^m) + ½ M_w δ_{P₀}`, `δ_{P₀} = ∏_{p>13}(1+2/(p³(p−1))) − 1 < 5.83·10⁻⁵`;
and for `T₁ ≥ 1`, a.e. `t < η/T₁`, every `S`: `R_S(t) ≤ 1 + TV(h) sup_{s ≥ log T₁}|E_S(s)|/(ℰ I_w)`
when `w̃(u) = h(log(1/u))`.

Stated only; not proved in this project (see README). -/
def propCTfixed_Statement : Prop :=
  (∀ (W : Weight) (Mw D : ℝ), (∀ S₁ ⊆ P0, ∀ t, 0 < t → RS W S₁ t ≤ Mw) →
    (∀ S₁ ⊆ P0, essSup (fun t => ENNReal.ofReal (RS W S₁ t + Rm W t))
        (volume.restrict (Set.Ioi (0 : ℝ))) ≤ ENNReal.ofReal D) →
    CTp W ≤ ENNReal.ofReal (D + 1 / 2 * Mw * 5.83e-5)) ∧
  (∀ (W : Weight) (h : ℝ → ℝ) (T₁ : ℝ), 1 ≤ T₁ → BoundedVariationOn h Set.univ →
    (∀ u, 0 < u → W.wt u = h (Real.log (1 / u))) → ∀ S : Finset ℕ, ∀ Emax : ℝ,
    (∀ s, Real.log T₁ ≤ s → |ES S s| ≤ Emax) →
    ∀ᵐ t ∂(volume.restrict (Set.Ioo 0 (W.η / T₁))),
      RS W S t ≤ 1 + (eVariationOn h Set.univ).toReal * Emax / (Ecal * W.Iw))

end Families
