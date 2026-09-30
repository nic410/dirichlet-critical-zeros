/-
`lemma-A.tex` (§6.1): the sharp weighted Farey large sieve on intervals.
Statements of `lem:WH`, `lem:dual`, `prop:count`, `lem:A`, `cor:LmultA`, `lem:harm`, `lem:Rwlog`
(`lem:gauss` is in `Families.Toeplitz`, where it is proved).
Analytic statements are recorded as `def …Statement : Prop`; a proved statement also has a `theorem … : …Statement`
(possibly in another file). Implications between statements take them as hypotheses.

Classification (see STATEMENTS.md and STATUS.md):
* (a) headline chain, proved: `lemDual`, `propCount` (used by `lem:C`); proofs in `Families/Wired/Phase1.lean`.
* (b) named hypothesis: `lem:WH` — its statement `lemWH_Statement` is in `Families.Classical`; it is proved as
  `lemWH` (`Families/Wired/Phase2.lean`).
* (c) off the headline chain, stated only (not proved in this project): `lemWH_ratio_Statement`, `lemA_Statement`,
  `lemHarm_Statement`, `lemRwlog_Statement`, `lemRwlog_numeric_Statement`.
-/
import Families.Classical

noncomputable section

open scoped BigOperators ComplexConjugate ArithmeticFunction.Moebius ENNReal
open ArithmeticFunction Finset MeasureTheory Filter Topology

namespace Families

/-! ### Kernels, Farey profile, `R_w`, `C_w` -/

/-- The triangle kernel `k₀(ξ) = ς⁻¹ (1 − |ξ|/ς)_+` on `ℝ` (`∫ k₀ = 1`). -/
def k0 (ς ξ : ℝ) : ℝ := ς⁻¹ * max (1 - |ξ| / ς) 0

/-- Its periodisation `k_ς(ξ) = ∑_{m∈ℤ} k₀(ξ + m)` (a function on `𝕋 = ℝ/ℤ`). -/
def kper (ς ξ : ℝ) : ℝ := ∑' m : ℤ, k0 ς (ξ + m)

/-- The Farey profile `P_w(t) = (1/c_w) ∑_{k≥1} (φ(k)/k²) w̃(kt)` (`eqA:Pw`); `w̃(kt) = 0` for `kt > 1`. -/
def Pw (W : Weight) (t : ℝ) : ℝ :=
  W.cw⁻¹ * ∑ k ∈ Finset.Icc 1 ⌊1 / t⌋₊, (Nat.totient k : ℝ) / (k : ℝ) ^ 2 * W.wt (k * t)

/-- `R_w = ess sup_{t>0} P_w(t)` w.r.t. Lebesgue measure (`eqA:Rw`), valued in `[0,∞]`. -/
def Rw (W : Weight) : ℝ≥0∞ :=
  essSup (fun t => ENNReal.ofReal (Pw W t)) (volume.restrict (Set.Ioi (0 : ℝ)))

/-- `C_w = C_G R_w` (the Gauss-transfer constant). -/
def Cw (W : Weight) : ℝ := CG * (Rw W).toReal

/-- The convolution of the weighted Farey measure `𝔪 = ∑_q 𝔴(q/Q) ∑*_{b mod q} δ_{b/q}` with `k_ς`. -/
def fareyConv (𝔴 : ℝ → ℝ) (Q ς θ : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, 𝔴 (q / Q) * ∑ b ∈ reduced q, kper ς (θ - b / q)

/-- `ρ_{𝔴,v}(z) = (vz)^{-2} ∑_{k≥1} φ(k) 𝔴(k/(v|z|Q))` (`eqA:rho`); only `k ≤ v|z|Q` contribute. -/
def rhoCount (𝔴 : ℝ → ℝ) (Q : ℝ) (v : ℕ) (z : ℝ) : ℝ :=
  ((v : ℝ) * z)⁻¹ ^ 2 * ∑ k ∈ Finset.Icc 1 ⌊(v : ℝ) * |z| * Q⌋₊,
    (Nat.totient k : ℝ) * 𝔴 (k / ((v : ℝ) * |z| * Q))

/-- The two log-wide weights (`eq:logwide`), extended by `0` off `[η,1]`. -/
def wSharpFun (η u : ℝ) : ℝ := if η ≤ u ∧ u ≤ 1 then u⁻¹ ^ 2 else 0
/-- `w^sm_η(u) = u^{-2} sin²(π log u / log η) 1_{[η,1]}(u)`. -/
def wSmoothFun (η u : ℝ) : ℝ :=
  if η ≤ u ∧ u ≤ 1 then u⁻¹ ^ 2 * Real.sin (Real.pi * Real.log u / Real.log η) ^ 2 else 0

/-! ### `lem:WH`: the masses

`lemWH_Statement` (`lem:WH`) is a named hypothesis ((b)); it is stated in `Families.Classical` and proved as
`lemWH` (`Families/Wired/Phase2.lean`). -/

/-- **`lem:WH`, consequence** ((c): off the headline chain). `W/H → C_G` as `Q → ∞`.

Stated only; not proved in this project (see README). -/
def lemWH_ratio_Statement : Prop :=
  ∀ W : Weight, Tendsto (fun Q : ℝ => W.Wm Q / W.H Q) atTop (𝓝 CG)

/-! ### `lem:dual`: band-limited duality -/

/-- **`lem:dual`** ((a)). For a finite positive measure `μ = ∑_s a_s δ_{θ_s}` on `𝕋` (distinct points),
an interval `I` of `K ≥ 1` integers, `0 < κ ≤ 1/4`, `ς = κ/K`:
`∑_s a_s |S_x(θ_s)|² ≤ (1+κ²) max_s (μ*k_ς)(θ_s) ‖x‖²`. The maximum is expressed through any
upper bound `M ≥ 0` for the values `(μ*k_ς)(θ_s)`. (Statement-audit fix: without `0 ≤ M` the
statement was false for `s = ∅`, `M < 0`; in the TeX the maximum over a nonempty positive measure is
`> 0`, so `0 ≤ M` is implicit.) -/
def lemDual_Statement : Prop :=
  ∀ (σ : Type) (s : Finset σ) (θ a : σ → ℝ), (∀ i ∈ s, 0 < a i) →
    (∀ i ∈ s, ∀ j ∈ s, i ≠ j → Int.fract (θ i) ≠ Int.fract (θ j)) →
    ∀ (N₀ : ℤ) (K : ℕ), 1 ≤ K → ∀ κ : ℝ, 0 < κ → κ ≤ 1 / 4 → ∀ M : ℝ, 0 ≤ M →
    (∀ i ∈ s, ∑ j ∈ s, a j * kper (κ / K) (θ i - θ j) ≤ M) →
    ∀ x : ℤ → ℂ, ∑ i ∈ s, a i * ‖S (intervalZ N₀ K) x (θ i)‖ ^ 2
      ≤ (1 + κ ^ 2) * M * normSq (intervalZ N₀ K) x

-- `lemDual` is proved in `Families/Wired/Phase1.lean` (wired from Families/Phase1/*).

/-! ### `prop:count`: local count along spokes -/

/-- **`prop:count`** ((a): used by `lem:C` with `𝔴 = m_Q` and in its spoke sums, so it is on
the headline chain). For `𝔴 ≥ 0` of bounded variation vanishing off `(0,1]`, `Q ≥ 1`, `0 < ς < 1/2`,
`V ≥ 1`, `θ ∈ ℝ`, and a Dirichlet approximation `u/v` (`1 ≤ v ≤ V`, `(u,v) = 1`,
`|θ − u/v| ≤ 1/(vV)`), with `y = θ − u/v` and `k_* = Q/V + QVς`:
`(𝔪 * k_ς)(θ) = 𝔴(v/Q) k₀(y) + ∫ k₀(z−y) ρ_{𝔴,v}(z) dz + ϱ`, `|ϱ| ≤ 4 V_𝔴 ς⁻¹ k_* (1 + log⁺ k_*)`. -/
def propCount_Statement : Prop :=
  ∀ (𝔴 : ℝ → ℝ), (∀ u, 0 ≤ 𝔴 u) → BoundedVariationOn 𝔴 Set.univ →
    (∀ u, 𝔴 u ≠ 0 → 0 < u ∧ u ≤ 1) →
    ∀ (Q ς V θ : ℝ) (u : ℤ) (v : ℕ), 1 ≤ Q → 0 < ς → ς < 1 / 2 → 1 ≤ V →
    1 ≤ v → (v : ℝ) ≤ V → IsCoprime u (v : ℤ) → |θ - u / v| ≤ 1 / (v * V) →
    let y := θ - u / v
    let kstar := Q / V + Q * V * ς
    |fareyConv 𝔴 Q ς θ - 𝔴 (v / Q) * k0 ς y - ∫ z, k0 ς (z - y) * rhoCount 𝔴 Q v z|
      ≤ 4 * (eVariationOn 𝔴 Set.univ).toReal * ς⁻¹ * kstar * (1 + Real.posLog kstar)

-- `propCount` is proved in `Families/Wired/Phase1.lean` (wired from Families/Phase1/*).

/-! ### `lem:A`: the sharp weighted Farey large sieve -/

/-- **`lem:A`** ((c): Gauss route only). For `ε ∈ (0,1)` there is `Q₀ = Q₀(ε, V_w/c_w)` such that for `Q ≥ Q₀`, every interval
of `K ≤ Q^{2−ε}` integers and every `x`:
`∑_q w(q/Q) ∑*_b |S_x(b/q)|² ≤ (R_w + ϑ_Q) W ‖x‖²`, `ϑ_Q = 30 (R_w + V_w/c_w) Q^{−ε/4} log Q`.
(The uniformity in `w` is encoded by quantifying over all weights with `V_w/c_w ≤ B`.)

Stated only; not proved in this project (see README). -/
def lemA_Statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ B : ℝ, ∃ Q₀ : ℝ, ∀ W : Weight, W.Vw / W.cw ≤ B →
    ∀ Q : ℝ, Q₀ ≤ Q → ∀ (N₀ : ℤ) (K : ℕ), (K : ℝ) ≤ Q ^ (2 - ε) → ∀ x : ℤ → ℂ,
      fareyForm W Q (intervalZ N₀ K) x ≤
        ((Rw W).toReal + 30 * ((Rw W).toReal + W.Vw / W.cw) * Q ^ (-ε / 4) * Real.log Q) *
          W.Wm Q * normSq (intervalZ N₀ K) x

-- `Rw_le` (`R_w ≤ w_max/c_w`) and `wSharp_Vw_cw` (`V_w = 2η⁻²`, `c_w = (6/π²) log(1/η)` for the sharp
-- weight) are proved in `Families.Weights`.

/-! ### `cor:LmultA` -/

/-- The large-sieve bound `Λ_mult(K) ≤ B` in the form used by the paper: for every interval `I` of
`K` integers (inside `[1, Q²]`) and every `x`, `x^*Δx ≤ B ‖x‖²`. -/
def LmultLE (W : Weight) (Q : ℝ) (K : ℕ) (B : ℝ) : Prop :=
  ∀ N₀ : ℤ, 1 ≤ N₀ → ((N₀ + K - 1 : ℤ) : ℝ) ≤ Q ^ 2 →
    ∀ x : ℤ → ℂ, famForm W Q (intervalZ N₀ K) x ≤ B * normSq (intervalZ N₀ K) x

/-- **`cor:LmultA`.** For fixed `ε ∈ (0,1)` and `w`: `Λ_mult(K) ≤ (C_w + o(1)) H` uniformly in
`K ≤ Q^{2−ε}`, as `Q → ∞`. -/
def corLmultA_Statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ W : Weight, ∀ δ : ℝ, 0 < δ → ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
    ∀ K : ℕ, (K : ℝ) ≤ Q ^ (2 - ε) → LmultLE W Q K ((Cw W + δ) * W.H Q)

/-! ### `lem:harm`, `lem:Rwlog` -/

/-- `B_φ = ∑_d |μ(d)| d^{-3/2} = ζ(3/2)/ζ(3)`. -/
def Bphi : ℝ := ∑' d : ℕ, |(μ d : ℝ)| / (d : ℝ) ^ (3 / 2 : ℝ)

/-- `c_φ = γ − ζ'(2)/ζ(2)`. -/
def cphi : ℝ := Real.eulerMascheroniConstant - (deriv riemannZeta 2 / riemannZeta 2).re

/-- `E_φ(y) = ∑_{k≤y} φ(k)/k² − (6/π²)(log y + c_φ)`. -/
def Ephi (y : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 ⌊y⌋₊, (Nat.totient k : ℝ) / (k : ℝ) ^ 2 - 6 / Real.pi ^ 2 * (Real.log y + cphi)

/-- **`lem:harm`** ((c): its statement is not consumed by the headline chain; `lem:fS`(iii) re-runs the
same argument for `f_S`, and `prop:CTfixed` is (c)). `|E_φ(y)| ≤ 2B_φ y^{-1/2}` for `y ≥ 1`, also for the left limits
(`∑_{k<y}` in place of `∑_{k≤y}`), and consequently
`∑_{α≤k≤β} φ(k)/k² ≤ (6/π²) log(β/α) + 4B_φ` for `0 < α ≤ β`.

Stated only; not proved in this project (see README). -/
def lemHarm_Statement : Prop :=
  (∀ y : ℝ, 1 ≤ y → |Ephi y| ≤ 2 * Bphi * y ^ (-(1 / 2 : ℝ))) ∧
  (∀ y : ℝ, 1 ≤ y →
    |∑ k ∈ (Finset.Icc 1 ⌊y⌋₊).filter (fun k : ℕ => (k : ℝ) < y), (Nat.totient k : ℝ) / (k : ℝ) ^ 2
      - 6 / Real.pi ^ 2 * (Real.log y + cphi)| ≤ 2 * Bphi * y ^ (-(1 / 2 : ℝ))) ∧
  (∀ α β : ℝ, 0 < α → α ≤ β →
    ∑ k ∈ (Finset.Icc 1 ⌊β⌋₊).filter (fun k : ℕ => α ≤ k), (Nat.totient k : ℝ) / (k : ℝ) ^ 2
      ≤ 6 / Real.pi ^ 2 * Real.log (β / α) + 4 * Bphi)

/-- **`lem:Rwlog`** ((c); its layer-cake argument is re-run inside `lem:CTlimit`). Let `h : ℝ → [0,1]` vanish on `(−∞,0)`, be integrable and quasi-concave, and let
`w(u) = u^{-2} h(log(1/u))` on `(0,1]`. Then `I_w = ∫h` and `P_w(t) ≤ 1 + (π²/6)(4B_φ)/I_h` for all
`t > 0`. (Formally stated for admissible `W` whose weight has this form.)

Stated only; not proved in this project (see README). -/
def lemRwlog_Statement : Prop :=
  ∀ (W : Weight) (h : ℝ → ℝ), (∀ y, 0 ≤ h y ∧ h y ≤ 1) → (∀ y, y < 0 → h y = 0) →
    Integrable h → (∀ lam : ℝ, (Set.OrdConnected {y | lam < h y})) →
    (∀ u, 0 < u → u ≤ 1 → W.w u = u⁻¹ ^ 2 * h (Real.log (1 / u))) →
    W.Iw = ∫ y, h y ∧
    ∀ t : ℝ, 0 < t → Pw W t ≤ 1 + Real.pi ^ 2 / 6 * (4 * Bphi) / ∫ y, h y

/-- **`lem:Rwlog`, numerical consequences** ((c)). `R_{w_η} ≤ 1 + 14.31/L`, `R_{w^sm_η} ≤ 1 + 28.62/L`,
`L = log(1/η)`; hence `C_{w_η}, C_{w^sm_η} → C_G` as `η → 0`.

Stated only; not proved in this project (see README). -/
def lemRwlog_numeric_Statement : Prop :=
  (∀ (W : Weight) (η : ℝ), W.w = wSharpFun η → Rw W ≤ ENNReal.ofReal (1 + 14.31 / Real.log (1 / η))) ∧
  (∀ (W : Weight) (η : ℝ), W.w = wSmoothFun η →
    Rw W ≤ ENNReal.ofReal (1 + 28.62 / Real.log (1 / η)))

end Families
