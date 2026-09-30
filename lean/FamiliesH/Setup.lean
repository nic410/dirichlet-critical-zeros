/-
# Theorem 1.4(a): the fixed data of one cell and the prime-side objects (§9.1)

`HSetup` is the analogue of `Families.PrimeSetup` for one cell `ℓ^{a₀} ≤ T ≤ Q^{κc}` ((9.2)):
the height exponent `A₀` is replaced by the cell top `κc`, the bandwidth satisfies `λ < β(κc)` instead
of `λ < 2`, and every object that `PrimeSetup` normalises by `L = λ log Q` is normalised by
`L = λ ℓ_* = λ log(QT)` ((9.4)). The definitions are line-by-line ports of `Families/PrimeSide.lean`
and of the Gabor section of `Families/Main.lean`; the ones that do not involve `L` or the heights
(`PrimeSetup.LamR`, `PrimeSetup.strip`, `Δ`, `famForm`, `Nfam`, …) are reused verbatim.
-/
import FamiliesH.Basic

noncomputable section

open scoped BigOperators ComplexConjugate ArithmeticFunction.Moebius
open scoped ENNReal ContDiff
open ArithmeticFunction Finset MeasureTheory Filter Topology

namespace Families.Hybrid

open Families

/-- The data fixed while `Q → ∞` for one cell (§9.1, (P1)–(P3), (P6)): the height exponent
`a₀ > 0`; the cell top `κc > 0`; a bandwidth `λ ∈ (0, β(κc))` and a margin `ε₁ ∈ (0, 1/4)` with
`λ(1+ε₁) ≤ β(κc) − ε₁`; an edge margin `θ ∈ (0,1/4)`; a real even window `ψ ∈ C_c^∞((−1/2,1/2))`,
`ψ ≢ 0`; a flattening margin `ε₃ ∈ (0,1/4)`; the smooth prime cut-off `Υ₀` and the smooth dyadic
partition of unity `ψ_j` exactly as in `Families.PrimeSetup`.

The band parameter `ε` of (P4) and the localisation exponent `ε₅ = min(ε, ε₁)/(4(1+κc))` of (P5) are
**not** fields: `ε` is an argument of `propTIsharpH_Statement` and `assemblyLimitH_Statement`, and `ε₅`
is internal to the proof of `prop:TIsharpH` (it is chosen after `ε`, (9.3)). In §9.1 the cell data
use `κ₁` in `ε_max` and `ε₅`; using the cell top `κc ≤ κ₁` instead is equivalent inside the cell. -/
structure HSetup where
  a0 : ℝ
  kc : ℝ
  lam : ℝ
  ε₁ : ℝ
  θ : ℝ
  ψ : ℝ → ℝ
  ε₃ : ℝ
  Υ₀ : ℝ → ℝ
  ψj : ℕ → ℝ → ℝ
  a0_pos : 0 < a0
  kc_pos : 0 < kc
  lam_pos : 0 < lam
  lam_lt : lam < betaK kc
  ε₁_pos : 0 < ε₁
  ε₁_lt : ε₁ < 1 / 4
  lam_ε₁ : lam * (1 + ε₁) ≤ betaK kc - ε₁
  θ_pos : 0 < θ
  θ_lt : θ < 1 / 4
  ψ_smooth : ContDiff ℝ ∞ ψ
  ψ_even : ∀ x, ψ (-x) = ψ x
  ψ_supp : ∃ r : ℝ, r < 1 / 2 ∧ ∀ x, r < |x| → ψ x = 0
  ψ_ne : ∃ x, ψ x ≠ 0
  ε₃_pos : 0 < ε₃
  ε₃_lt : ε₃ < 1 / 4
  Υ₀_smooth : ContDiff ℝ ∞ Υ₀
  Υ₀_range : ∀ y, 0 ≤ Υ₀ y ∧ Υ₀ y ≤ 1
  Υ₀_one : ∀ y, 0 ≤ y → y ≤ 1 → Υ₀ y = 1
  Υ₀_zero : ∀ y, 1 + ε₁ < y → Υ₀ y = 0
  ψj_smooth : ∀ j, ContDiff ℝ ∞ (ψj j)
  ψj_nonneg : ∀ j y, 0 ≤ ψj j y
  ψj_supp : ∀ j y, ψj j y ≠ 0 → (2 : ℝ) ^ j / 2 ≤ y ∧ y ≤ 2 * 2 ^ j
  ψj_sum : ∀ y : ℝ, 1 ≤ y → ∑' j, ψj j y = 1
  ψj_deriv : ∀ i : ℕ, ∃ C : ℝ, ∀ j y, |iteratedDeriv i (ψj j) y| ≤ C * ((2 : ℝ) ^ j)⁻¹ ^ i

namespace HSetup

variable (P : HSetup)

/-- The admissible heights of the cell: `ℓ^{a₀} ≤ T ≤ Q^{κc}` ((9.2)). -/
def heights (Q : ℝ) : Set ℝ := cellHeights P.a0 P.kc Q

/-- `L = λ ℓ_* = λ log(QT)` ((9.4)). -/
def L (Q T : ℝ) : ℝ := P.lam * ellS Q T
/-- `X = e^L = (QT)^λ`. -/
def X (Q T : ℝ) : ℝ := Real.exp (P.L Q T)
/-- `Y = X^{1+ε₁} ≤ Q^{2−ε₁} T^{1−ε₁}` (Lemma 9.1 (S1)). -/
def Y (Q T : ℝ) : ℝ := P.X Q T ^ (1 + P.ε₁)
/-- `J = [(1+θ)T, (2−θ)T]`. -/
def J (T : ℝ) : Set ℝ := Set.Icc ((1 + P.θ) * T) ((2 - P.θ) * T)
/-- `|J| = (1−2θ)T`. -/
def Jlen (T : ℝ) : ℝ := (1 - 2 * P.θ) * T
/-- The support range `1 ≤ n ≤ Y` of all prime-side vectors. -/
def range (Q T : ℝ) : Finset ℕ := Finset.Icc 1 ⌊P.Y Q T⌋₊
/-- `[1, Y]` as a subset of `ℤ`. -/
def rangeZ (Q T : ℝ) : Finset ℤ := Finset.Icc 1 ⌊P.Y Q T⌋

/-- `Υ(n) = Υ₀(log n / L)`. -/
def Ups (Q T : ℝ) (n : ℕ) : ℝ := P.Υ₀ (Real.log n / P.L Q T)
/-- `a_n = Λ(n) n^{-1/2} Υ(n)`. -/
def aVec (Q T : ℝ) (n : ℕ) : ℝ := Λ n / Real.sqrt n * P.Ups Q T n
/-- `R_j = ⌊N_j^{1−ε₃}/(QT)⌋`, `N_j = 2^j` (§9.3; the same levels as in `Families.PrimeSetup`). -/
def Rj (Q T : ℝ) (j : ℕ) : ℕ := ⌊((2 : ℝ) ^ j) ^ (1 - P.ε₃) / (Q * T)⌋₊
/-- The dyadic blocks that can meet `[1, Y]`. -/
def blocks (Q T : ℝ) : Finset ℕ := Finset.range (Nat.log 2 ⌊P.Y Q T⌋₊ + 2)
/-- `a♯_n = ∑_{j : R_j ≥ 1} ψ_j(n) Υ(n) n^{-1/2} Λ_{R_j}(n)` (`Λ_R = PrimeSetup.LamR`, reused). -/
def aSharp (Q T : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ (P.blocks Q T).filter (fun j => 1 ≤ P.Rj Q T j),
    P.ψj j n * P.Ups Q T n / Real.sqrt n * PrimeSetup.LamR (P.Rj Q T j) n
/-- The flattened vector `b = a − a♯`. -/
def bVec (Q T : ℝ) (n : ℕ) : ℝ := P.aVec Q T n - P.aSharp Q T n

/-- `S_χ[x](t) = ∑_{n ≤ Y} x_n χ(n) n^{-it}`. -/
def Schi {q : ℕ} (χ : DirichletCharacter ℂ q) (Q T : ℝ) (x : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ n ∈ P.range Q T, (x n : ℂ) * χ n * (n : ℂ) ^ (-(Complex.I * t))

/-- `ψ_L(u) = ψ(u/L)`. -/
def ψL (Q T u : ℝ) : ℝ := P.ψ (u / P.L Q T)
/-- `v = ψ²`, `a = ∫v`, `b = ∫v²` (independent of `Q`, `T`). -/
def vfun (s : ℝ) : ℝ := P.ψ s ^ 2
def aInt : ℝ := ∫ s, P.vfun s
def bInt : ℝ := ∫ s, P.vfun s ^ 2
/-- `g = ψ_L² * ψ_L²`. -/
def g (Q T u : ℝ) : ℝ := ∫ s, P.ψL Q T s ^ 2 * P.ψL Q T (u - s) ^ 2
/-- `Φ = \widehat{ψ_L²}`, `\hat f(t) = ∫ f(u) e^{itu} du`. -/
def Φ (Q T t : ℝ) : ℂ := ∫ u, (P.ψL Q T u ^ 2 : ℂ) * Complex.exp (Complex.I * t * u)
/-- The time kernel `𝒦(n,m) = ∬_{J²} Φ(t−t')² n^{−it} m^{it'} dt dt'`. -/
def 𝒦 (Q T : ℝ) (n m : ℕ) : ℂ :=
  ∫ t in P.J T, ∫ t' in P.J T,
    P.Φ Q T (t - t') ^ 2 * (n : ℂ) ^ (-(Complex.I * t)) * (m : ℂ) ^ (Complex.I * t')
/-- `\hat{1_J}(ξ) = ∫_J e^{itξ} dt`. -/
def hatJ (T ξ : ℝ) : ℂ := ∫ t in P.J T, Complex.exp (Complex.I * t * ξ)

/-- The ratio part `∑_{n,m} x_n x_m Δ(n,m) 𝒦(n,m)` of the second moment ((5.1) without the factor
`1/(2π²)`), for a real vector `x` on `[1, Y]`. -/
def ratioForm (W : Weight) (Q T : ℝ) (x : ℕ → ℝ) : ℂ :=
  ∑ n ∈ P.range Q T, ∑ m ∈ P.range Q T, (x n : ℂ) * x m * Δ W Q n m * P.𝒦 Q T n m

/-- `x_y(u)_n = y_n \hat{1_J}(u − log n)` as a vector on `ℤ` (zero off `[1, Y]` by the support of `y`). -/
def xVec (Q T : ℝ) (y : ℕ → ℝ) (u : ℝ) : ℤ → ℂ := fun n =>
  if 1 ≤ n then (y n.toNat : ℂ) * P.hatJ T (u - Real.log n.toNat) else 0

/-! ### Gabor matrices and `𝔐` (§2.4, with `L = λℓ_*`) -/

/-- `\widehat{ψ_L}(w) = ∫ ψ_L(u) e^{iwu} du` (entire in `w`). -/
def hatψL (Q T : ℝ) (w : ℂ) : ℂ := ∫ u, (P.ψL Q T u : ℂ) * Complex.exp (Complex.I * w * u)
/-- The lattice `K_J = {k ∈ ℤ : τ_k ∈ J}`, `τ_k = τ₀ + 2πk/L`. -/
def KJ (Q T τ₀ : ℝ) : Finset ℤ :=
  (Finset.Icc ⌈((1 + P.θ) * T - τ₀) * P.L Q T / (2 * Real.pi)⌉
    ⌊((2 - P.θ) * T - τ₀) * P.L Q T / (2 * Real.pi)⌋)
/-- `p_k(z) = \widehat{ψ_L}(z − τ_k)`. -/
def pk (Q T τ₀ : ℝ) (k : ℤ) (z : ℂ) : ℂ := P.hatψL Q T (z - (τ₀ + 2 * Real.pi * k / P.L Q T))
/-- The Gabor matrix `G_{χ,kl} = ∑_ρ m_ρ p_k(z_ρ) p_l(z_ρ)`, `z_ρ = (ρ − 1/2)/i` (`PrimeSetup.strip`,
the nontrivial zeros, reused). -/
def Gabor (Q T τ₀ : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Matrix (P.KJ Q T τ₀) (P.KJ Q T τ₀) ℂ := fun k l =>
  ∑' ρ : PrimeSetup.strip χ, (mult χ ρ : ℂ) * P.pk Q T τ₀ k ((ρ - 1 / 2) / Complex.I) *
    P.pk Q T τ₀ l ((ρ - 1 / 2) / Complex.I)
/-- `𝔐 = ∑_χ ω_χ ‖Ĝ_χ‖_F²`, `Ĝ_χ = G_χ/(aL²)`. -/
def Mfrak (W : Weight) (Q T τ₀ : ℝ) : ℝ :=
  famSum W Q fun _ χ =>
    ∑ k, ∑ l, ‖P.Gabor Q T τ₀ χ k l / (P.aInt * P.L Q T ^ 2)‖ ^ 2

/-! ### The profile bound and the certified value -/

/-- The profile bound (9.15), the hypothesis of `prop:secondH` and the conclusion of
`prop:TIsharpH`: uniformly for `T` in the cell,
`∑ b_n b_m Δ(n,m) 𝒦(n,m) ≤ (1+o(1)) H ∑ |b_n|² c(log n/ℓ_*) 𝒦(n,n) + o(H|J|L²ℓ_*)`, written with a
single `δ` for both `o(1)` terms. -/
def ProfileBoundH (W : Weight) (c : ℝ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ P.heights Q,
    (P.ratioForm W Q T (P.bVec Q T)).re ≤
      (1 + δ) * W.H Q * ∑ n ∈ P.range Q T,
        P.bVec Q T n ^ 2 * c (Real.log n / ellS Q T) * (P.𝒦 Q T n n).re +
      δ * W.H Q * P.Jlen T * P.L Q T ^ 2 * ellS Q T

/-- The certified value `2 − 8θ − (1−2θ) 𝒬_F(f_v)`, `F(α) = c(α) min(α, 1+ε₄)`, `ε₄ = 2ε₃`,
`f_v(x) = v(x/λ)/(λa)` (identical to `PrimeSetup.certValue`; it does not involve `Q`, `T`). -/
def certValue (c : ℝ → ℝ) : ℝ :=
  2 - 8 * P.θ - (1 - 2 * P.θ) *
    Qf (fun α => c α * min α (1 + 2 * P.ε₃)) (fun x => P.vfun (x / P.lam) / (P.lam * P.aInt))

end HSetup

end Families.Hybrid
