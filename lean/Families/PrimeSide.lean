/-
`lemma-B-majorant.tex` (§5): flattening (`lem:B1`, `lem:B2`, `eqB:Mrat`) and the time-localised
majorant (`lem:M1`, `lem:M2`, `lem:M3`, `prop:TI`), plus the interface `prop:TIsharp` of
`lemma-toeplitz-C.tex`. Notation of main.tex §2 (`sec:setup`).
`lem:M1` is proved in `Families.M1` / `Families.M1Diag`, `lem:M2` in `Families.Glue`, `lem:M3`(i),(ii) here and
(iii),(iv) in `Families.M3`.

Classification (see STATEMENTS.md and STATUS.md): (a) headline chain, proved — `lemB1`,
`eqBMrat`, `lemB2` (takes the named hypothesis `PNT_dlVP`), `propTIsharp` (takes `MV_LargeSieve` and
`lemWH_Statement`); (c) off the chain, stated only — `propTI_Statement` (Gauss route).
-/
import Families.LemmaC

noncomputable section

open scoped BigOperators ComplexConjugate ArithmeticFunction.Moebius
open scoped ENNReal ContDiff
open ArithmeticFunction Finset MeasureTheory Filter Topology

namespace Families

/-! ### Fixed data (main.tex §2.3, `sec:parameters`) -/

/-- The data fixed while `Q → ∞`: height exponents `0 < a₀ < A₀`; bandwidth `λ ∈ (0,2)` and margin
`ε₁ > 0` with `λ(1+ε₁) ≤ 2 − ε₁`; edge margin `θ ∈ (0,1/4)`; a real even window
`ψ ∈ C_c^∞((−1/2,1/2))`, `ψ ≢ 0`; flattening margin `ε₃ ∈ (0,1/4)`; the smooth prime cut-off `Υ₀`
(`0 ≤ Υ₀ ≤ 1`, `Υ₀ = 1` on `[0,1]`, `Υ₀ = 0` on `(1+ε₁, ∞)`); and the smooth dyadic partition of
unity `ψ_j` (`supp ψ_j ⊂ [N_j/2, 2N_j]`, `N_j = 2^j`, `∑_j ψ_j = 1` on `[1,∞)`, `ψ_j^{(i)} ≪_i N_j^{-i}`). -/
structure PrimeSetup where
  a0 : ℝ
  A0 : ℝ
  lam : ℝ
  ε₁ : ℝ
  θ : ℝ
  ψ : ℝ → ℝ
  ε₃ : ℝ
  Υ₀ : ℝ → ℝ
  ψj : ℕ → ℝ → ℝ
  a0_pos : 0 < a0
  a0_lt : a0 < A0
  lam_pos : 0 < lam
  lam_lt : lam < 2
  ε₁_pos : 0 < ε₁
  lam_ε₁ : lam * (1 + ε₁) ≤ 2 - ε₁
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

/-- `ℓ = log Q`. -/
def ell (Q : ℝ) : ℝ := Real.log Q

namespace PrimeSetup

variable (P : PrimeSetup)

/-- `L = λℓ`. -/
def L (Q : ℝ) : ℝ := P.lam * Real.log Q
/-- `X = e^L = Q^λ`. -/
def X (Q : ℝ) : ℝ := Real.exp (P.L Q)
/-- `Y = X^{1+ε₁} ≤ Q^{2−ε₁}`. -/
def Y (Q : ℝ) : ℝ := P.X Q ^ (1 + P.ε₁)
/-- `J = [(1+θ)T, (2−θ)T]`. -/
def J (T : ℝ) : Set ℝ := Set.Icc ((1 + P.θ) * T) ((2 - P.θ) * T)
/-- `|J| = (1−2θ)T`. -/
def Jlen (T : ℝ) : ℝ := (1 - 2 * P.θ) * T
/-- The support range `1 ≤ n ≤ Y` of all prime-side vectors. -/
def range (Q : ℝ) : Finset ℕ := Finset.Icc 1 ⌊P.Y Q⌋₊

/-- `Υ(n) = Υ₀(log n / L)`. -/
def Ups (Q : ℝ) (n : ℕ) : ℝ := P.Υ₀ (Real.log n / P.L Q)
/-- `a_n = Λ(n) n^{-1/2} Υ(n)` (`eq:an`). -/
def aVec (Q : ℝ) (n : ℕ) : ℝ := Λ n / Real.sqrt n * P.Ups Q n
/-- `R_j = ⌊N_j^{1−ε₃}/(QT)⌋`, `N_j = 2^j`. -/
def Rj (Q T : ℝ) (j : ℕ) : ℕ := ⌊((2 : ℝ) ^ j) ^ (1 - P.ε₃) / (Q * T)⌋₊
/-- `Λ_R(n) = ∑_{r≤R} μ(r) c_r(n)/φ(r)` (Selberg–Goldston truncation). -/
def LamR (R n : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 R, (μ r : ℝ) / Nat.totient r * (ramanujan r n).re
/-- The dyadic blocks that can meet `[1, Y]`. -/
def blocks (Q : ℝ) : Finset ℕ := Finset.range (Nat.log 2 ⌊P.Y Q⌋₊ + 2)
/-- `a♯_n = ∑_{j : R_j ≥ 1} ψ_j(n) Υ(n) n^{-1/2} Λ_{R_j}(n)`. -/
def aSharp (Q T : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ (P.blocks Q).filter (fun j => 1 ≤ P.Rj Q T j),
    P.ψj j n * P.Ups Q n / Real.sqrt n * LamR (P.Rj Q T j) n
/-- The flattened vector `b = a − a♯`. -/
def bVec (Q T : ℝ) (n : ℕ) : ℝ := P.aVec Q n - P.aSharp Q T n

/-- `S_χ[x](t) = ∑_n x_n χ(n) n^{-it}`. -/
def Schi {q : ℕ} (χ : DirichletCharacter ℂ q) (Q : ℝ) (x : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ n ∈ P.range Q, (x n : ℂ) * χ n * (n : ℂ) ^ (-(Complex.I * t))

/-- `ψ_L(u) = ψ(u/L)`. -/
def ψL (Q u : ℝ) : ℝ := P.ψ (u / P.L Q)
/-- `v = ψ²`, `a = ∫v`, `b = ∫v²`. -/
def vfun (s : ℝ) : ℝ := P.ψ s ^ 2
def aInt : ℝ := ∫ s, P.vfun s
def bInt : ℝ := ∫ s, P.vfun s ^ 2
/-- `g = ψ_L² * ψ_L²`. -/
def g (Q u : ℝ) : ℝ := ∫ s, P.ψL Q s ^ 2 * P.ψL Q (u - s) ^ 2
/-- `Φ = \widehat{ψ_L²}`, `\hat f(t) = ∫ f(u) e^{itu} du`. -/
def Φ (Q t : ℝ) : ℂ := ∫ u, (P.ψL Q u ^ 2 : ℂ) * Complex.exp (Complex.I * t * u)
/-- The time kernel `𝒦(n,m) = ∬_{J²} Φ(t−t')² n^{−it} m^{it'} dt dt'` (`eq:Delta`). -/
def 𝒦 (Q T : ℝ) (n m : ℕ) : ℂ :=
  ∫ t in P.J T, ∫ t' in P.J T,
    P.Φ Q (t - t') ^ 2 * (n : ℂ) ^ (-(Complex.I * t)) * (m : ℂ) ^ (Complex.I * t')
/-- `\hat{1_J}(ξ) = ∫_J e^{itξ} dt`. -/
def hatJ (T ξ : ℝ) : ℂ := ∫ t in P.J T, Complex.exp (Complex.I * t * ξ)

/-- The ratio part `∑_{n,m} x_n x_m Δ(n,m) 𝒦(n,m)` of the second moment (`eqB:Mrat` without the
factor `1/(2π²)`), for a real vector `x` on `[1, Y]`. -/
def ratioForm (W : Weight) (Q T : ℝ) (x : ℕ → ℝ) : ℂ :=
  ∑ n ∈ P.range Q, ∑ m ∈ P.range Q, (x n : ℂ) * x m * Δ W Q n m * P.𝒦 Q T n m

/-- The admissible heights: `ℓ^{a₀} ≤ T ≤ ℓ^{A₀}`. -/
def heights (Q : ℝ) : Set ℝ := Set.Icc (Real.log Q ^ P.a0) (Real.log Q ^ P.A0)

end PrimeSetup

/-- `χ ∈ 𝓕(Q)`: `χ` primitive mod `q`, `w(q/Q) > 0`. -/
def InFamily (W : Weight) (Q : ℝ) (q : ℕ) (χ : DirichletCharacter ℂ q) : Prop :=
  χ.IsPrimitive ∧ 0 < W.w (q / Q)

/-! ### `lem:B1`: invisibility, and `eqB:Mrat` -/

/-- **`lem:B1`** ((a)). For every `χ ∈ 𝓕`, `|t| ≤ 3T`, `A > 0`: `S_χ[a♯](t) ≪_{A,ε₃} Q^{-A}`. -/
def lemB1_Statement : Prop :=
  ∀ (P : PrimeSetup) (W : Weight) (A : ℝ), 0 < A → ∃ C Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
    ∀ T ∈ P.heights Q, ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), InFamily W Q q χ →
    ∀ t : ℝ, |t| ≤ 3 * T → ‖P.Schi χ Q (P.aSharp Q T) t‖ ≤ C * Q ^ (-A)

-- `lemB1` is proved in `Families/Wired/Phase3.lean` (wired from Families/Phase3/C/*).

/-- **`eqB:Mrat`** ((a)). `∑ a_n a_m Δ 𝒦 = ∑ b_n b_m Δ 𝒦 + O(Q^{-A})`. -/
def eqBMrat_Statement : Prop :=
  ∀ (P : PrimeSetup) (W : Weight) (A : ℝ), 0 < A → ∃ C Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
    ∀ T ∈ P.heights Q,
      ‖P.ratioForm W Q T (P.aVec Q) - P.ratioForm W Q T (P.bVec Q T)‖ ≤ C * Q ^ (-A)

-- `eqBMrat` is proved in `Families/Wired/Phase3.lean` (wired from Families/Phase3/C/*).

/-! ### `lem:B2`: flattened norm -/

/-- `F_b(α) = min(α⁺, 1 + ε₄)`, `ε₄ = 2ε₃`. -/
def Fb (ε₃ α : ℝ) : ℝ := min (max α 0) (1 + 2 * ε₃)

/-- **`lem:B2`.** Let `h ≥ 0` be smooth with `‖h^{(i)}‖_∞ ≤ C_i ‖h‖_∞`. As `Q → ∞`,
`∑_n |b_n|² h(log n) ≤ (1+o(1)) ∫ ℓ F_b(s/ℓ) h(s) ds + O(‖h‖_∞ ℓ)`, the `o(1)` and `O` depending only on
the fixed data and the constants `C_i` (so `h` may vary with `Q`). `h` is assumed integrable (in the paper
`h` has compact support; without it Lean's junk value `∫ = 0` for non-integrable functions would make the
statement false). -/
/- Note on parsing: the integral is parenthesised. Without the parentheses
`∫ s, … * h s + C * hmax * ell Q` would parse with the `+` inside the integrand, making the right side `0`
(non-integrable Bochner integral) and the statement false; see `Families.Phase3.C.lemB2_rhs_collapse`. -/
def lemB2_Statement : Prop :=
  ∀ (P : PrimeSetup) (Cs : ℕ → ℝ) (δ : ℝ), 0 < δ → ∃ C Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
    ∀ T ∈ P.heights Q, ∀ (h : ℝ → ℝ) (hmax : ℝ), ContDiff ℝ ∞ h → (∀ y, 0 ≤ h y) →
      Integrable h → (∀ y, h y ≤ hmax) → (∀ i y, |iteratedDeriv i h y| ≤ Cs i * hmax) →
      ∑ n ∈ P.range Q, P.bVec Q T n ^ 2 * h (Real.log n)
        ≤ (1 + δ) * (∫ s, ell Q * Fb P.ε₃ (s / ell Q) * h s) + C * hmax * ell Q

/- (a). The proof uses the prime number theorem with an error term (`eqB:PNT`), which is the
named hypothesis `PNT_dlVP` (`Families.Classical`; stated there in a weaker power-of-log form that
suffices for this proof). Note: `eqB:norms` (`‖a♯‖² ≪ Lℓ`, used in the tails of
`prop:TIsharp`) applies step (4) of this proof with `h ≡ 1`, which is not `Integrable`; it is derived from
step (4) directly (no PNT is needed there). -/
-- `lemB2` is proved in `Families/Wired/Phase3.lean` (wired from Families/Phase3/C/*).

/-! ### `lem:M1`: time–frequency factorisation -/

/-- `x_y(u)_n = y_n \hat{1_J}(u − log n)` as a vector on `ℤ` (zero off `[1, Y]`). -/
def PrimeSetup.xVec (P : PrimeSetup) (Q T : ℝ) (y : ℕ → ℝ) (u : ℝ) : ℤ → ℂ := fun n =>
  if 1 ≤ n then (y n.toNat : ℂ) * P.hatJ T (u - Real.log n.toNat) else 0

/-- `[1, Y]` as a subset of `ℤ`. -/
def PrimeSetup.rangeZ (P : PrimeSetup) (Q : ℝ) : Finset ℤ := Finset.Icc 1 ⌊P.Y Q⌋

/-- **`lem:M1`.** `𝒦(n,m) = ∫ g(u) \hat{1_J}(u−log n) \overline{\hat{1_J}(u−log m)} du`; hence
`∑ y_n y_m Δ(n,m) 𝒦(n,m) = ∫ g(u) x_y(u)^*Δ x_y(u) du`; and `𝒦(n,n) = 2π|J| g(log n) + O_v(1)`. -/
def lemM1_Statement : Prop :=
  ∀ (P : PrimeSetup) (Q T : ℝ), 1 < Q → 0 < T →
    (∀ n m : ℕ, 1 ≤ n → 1 ≤ m →
      P.𝒦 Q T n m = ∫ u, (P.g Q u : ℂ) * P.hatJ T (u - Real.log n) *
        conj (P.hatJ T (u - Real.log m))) ∧
    (∀ (W : Weight) (y : ℕ → ℝ),
      P.ratioForm W Q T y = ∫ u, (P.g Q u : ℂ) * famForm W Q (P.rangeZ Q) (P.xVec Q T y u))

/-- **`lem:M1`, diagonal.** `𝒦(n,n) = 2π|J| g(log n) + O_v(1)` uniformly. -/
def lemM1_diag_Statement : Prop :=
  ∀ (P : PrimeSetup), ∃ C : ℝ, ∀ (Q T : ℝ), 1 < Q → 0 < T → ∀ n : ℕ, 1 ≤ n →
    ‖P.𝒦 Q T n n - 2 * Real.pi * P.Jlen T * P.g Q (Real.log n)‖ ≤ C

-- `lemM1 : lemM1_Statement` is proved in `Families.M1`.

-- `lemM1_diag : lemM1_diag_Statement` is proved in `Families.M1Diag`.

/-! ### `lem:M3`: localisation -/

/-- **`lem:M3`(i)** (proved). For any split `x = x^s + x^t` and `κ > 0`:
`x^*Δx ≤ (1+κ) x^{s*}Δx^s + (1+κ^{-1}) x^{t*}Δx^t` (only `Δ ⪰ 0` is used). -/
theorem lemM3_i (W : Weight) (Q : ℝ) (I : Finset ℤ) (xs xt : ℤ → ℂ) (κ : ℝ) (hκ : 0 < κ) :
    famForm W Q I (xs + xt) ≤ (1 + κ) * famForm W Q I xs + (1 + κ⁻¹) * famForm W Q I xt := by
  have hω : ∀ q, 0 ≤ W.omega Q q := fun q => by
    unfold Weight.omega
    exact div_nonneg (mul_nonneg (W.nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have key : ∀ a b : ℂ, ‖a + b‖ ^ 2 ≤ (1 + κ) * ‖a‖ ^ 2 + (1 + κ⁻¹) * ‖b‖ ^ 2 := by
    intro a b
    have h1 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
    have h2 : 0 ≤ ‖a + b‖ := norm_nonneg _
    have h3 : 2 * ‖a‖ * ‖b‖ ≤ κ * ‖a‖ ^ 2 + κ⁻¹ * ‖b‖ ^ 2 := by
      have hk : κ * κ⁻¹ = 1 := mul_inv_cancel₀ hκ.ne'
      have := sq_nonneg (κ * ‖a‖ - ‖b‖)
      have hκinv : 0 < κ⁻¹ := inv_pos.mpr hκ
      nlinarith [mul_pos hκ hκinv]
    nlinarith [norm_nonneg a, norm_nonneg b]
  unfold famForm
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun q _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun χ _ => ?_
  have hsplit : ∑ n ∈ I, (xs + xt) n * χ n = ∑ n ∈ I, xs n * χ n + ∑ n ∈ I, xt n * χ n := by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun n _ => by simp [add_mul]
  rw [hsplit]
  have := key (∑ n ∈ I, xs n * χ n) (∑ n ∈ I, xt n * χ n)
  have hq := hω q
  nlinarith [mul_le_mul_of_nonneg_left this hq]

/-- **`lem:M3`(ii)** (proved). `e^{2δ} − e^{−2δ} ≤ 5δ` for `0 < δ ≤ 1/4`, so `{n : |log n − u| < 2δ}`
lies in an interval of length `≤ 5δ e^u`. -/
theorem lemM3_ii (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 4) :
    Real.exp (2 * δ) - Real.exp (-(2 * δ)) ≤ 5 * δ := by
  have h1 : Real.exp (2 * δ) ≤ 1 + 2 * δ + 3 * δ ^ 2 := by
    have := Real.exp_bound' (x := 2 * δ) (by linarith) (by linarith) (n := 2) (by norm_num)
    simp [Finset.sum_range_succ, Nat.factorial] at this
    nlinarith
  have h2 : 1 - 2 * δ ≤ Real.exp (-(2 * δ)) := by
    have := Real.add_one_le_exp (-(2 * δ)); linarith
  nlinarith

/-- **`lem:M3`(iii),(iv).** With `x^s_n = x_n ρ((log n − u)/δ)`, `x^t = x − x^s`
(`ρ ∈ C_c^∞((−2,2))`, `0 ≤ ρ ≤ 1`, `ρ = 1` on `[−1,1]`, `δ ∈ (0,1/4]`):
(iii) `∫ g(u) ‖x^s(u)‖² c(u) du ≤ ∑_n |y_n|² 𝒦(n,n) sup{c(u) : |u − log n| < 2δ}` for bounded `c ≥ 0`;
(iv) `∫ g(u) ‖x^t(u)‖² du ≤ 8bL‖y‖²/δ`. -/
def lemM3_iii_iv_Statement : Prop :=
  ∀ (P : PrimeSetup) (ρ : ℝ → ℝ), ContDiff ℝ ∞ ρ → (∀ ξ, 0 ≤ ρ ξ ∧ ρ ξ ≤ 1) →
    (∀ ξ, |ξ| ≤ 1 → ρ ξ = 1) → (∀ ξ, 2 ≤ |ξ| → ρ ξ = 0) →
    ∀ (Q T δ : ℝ), 1 < Q → 0 < T → 0 < δ → δ ≤ 1 / 4 → ∀ y : ℕ → ℝ,
    let xs : ℝ → ℤ → ℂ := fun u n => P.xVec Q T y u n * ρ ((Real.log n.toNat - u) / δ)
    let xt : ℝ → ℤ → ℂ := fun u n => P.xVec Q T y u n - xs u n
    (∀ (c : ℝ → ℝ) (Cmax : ℝ), (∀ u, 0 ≤ c u ∧ c u ≤ Cmax) →
      ∫ u, P.g Q u * normSq (P.rangeZ Q) (xs u) * c u ≤
        ∑ n ∈ P.range Q, y n ^ 2 * (P.𝒦 Q T n n).re *
          sSup (c '' {u | |u - Real.log n| < 2 * δ})) ∧
    ∫ u, P.g Q u * normSq (P.rangeZ Q) (xt u) ≤
      8 * P.bInt * P.L Q * (∑ n ∈ P.range Q, y n ^ 2) / δ

-- `lemM3_iii_iv : lemM3_iii_iv_Statement` is proved in `Families.M3`.

/-! ### `prop:TI` and `prop:TIsharp` -/

/-- The profile bound `eq:profile` (display (5.11)), the hypothesis of `prop:second` and the
conclusion of `prop:TI` / `prop:TIsharp`: uniformly in `T`,
`∑ b_n b_m Δ(n,m) 𝒦(n,m) ≤ (1+o(1)) H ∑ |b_n|² c(log n/ℓ) 𝒦(n,n) + o(H|J|L²ℓ)`, written with a single
`δ` for both `o(1)` terms. -/
def PrimeSetup.ProfileBound (P : PrimeSetup) (W : Weight) (c : ℝ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ P.heights Q,
    (P.ratioForm W Q T (P.bVec Q T)).re ≤
      (1 + δ) * W.H Q * ∑ n ∈ P.range Q,
        P.bVec Q T n ^ 2 * c (Real.log n / ell Q) * (P.𝒦 Q T n n).re +
      δ * W.H Q * P.Jlen T * P.L Q ^ 2 * ell Q

/-- **`prop:TI`** ((c): Gauss route only). With `C̃_ε : ℝ → [1, C_w]` smooth, `= 1` on `(−∞, 1−2ε]`, `= C_w` on `[1−3ε/2, ∞)`
(`ε ∈ (0,1/3)`): as `Q → ∞`, uniformly in `T`,
`∑ b_n b_m Δ 𝒦 ≤ (1+o(1)) H ∑ |b_n|² C̃_ε(log n/ℓ) 𝒦(n,n) + o(H|J|L²ℓ)`.

Stated only; not proved in this project (see README). -/
def propTI_Statement : Prop :=
  ∀ (P : PrimeSetup) (W : Weight) (ε : ℝ), 0 < ε → ε < 1 / 3 → ∀ Ct : ℝ → ℝ,
    ContDiff ℝ ∞ Ct → (∀ α, 1 ≤ Ct α ∧ Ct α ≤ Cw W) → (∀ α, α ≤ 1 - 2 * ε → Ct α = 1) →
    (∀ α, 1 - 3 / 2 * ε ≤ α → Ct α = Cw W) →
    P.ProfileBound W Ct

/-- The band hypothesis of `prop:TIsharp` (the paragraph "The band constant" before Proposition 6.24): `C_band` is a constant with
`Λ_mult(Q^{1+2ε}) ≤ (C_band + o(1)) H` as `Q → ∞` (intervals of at most `Q^{1+2ε}` integers inside
`[1, Q²]`, which contains every interval used in the band regime). -/
def BandLS (W : Weight) (ε Cband : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
    ∀ K : ℕ, (K : ℝ) ≤ Q ^ (1 + 2 * ε) → LmultLE W Q K ((Cband + δ) * W.H Q)

/-- **`prop:TIsharp`** ((a); band device, Proposition 6.24). Let `C_band ≥ 1`
satisfy the band hypothesis `BandLS W ε C_band`, `C_max = max(C_band, C_T^+(w))` (`C_T^+` finite), and
`C̃_ε : ℝ → [1, C_max]` smooth with `C̃_ε = 1` on `(−∞,1−2ε]`, `C̃_ε ≥ C_band` on `[1−3ε/2, 1+3ε/2]`,
`C̃_ε ≥ C_T^+` on `[1+ε/2, ∞)`, `C̃_ε = C_T^+` on `[1+2ε, ∞)`. For each fixed `ε ∈ (0,1/3)`, as `Q → ∞`
uniformly in `T`: `∑ b_n b_m Δ 𝒦 ≤ (1+o(1)) H ∑ |b_n|² C̃_ε(log n/ℓ) 𝒦(n,n) + o(H|J|L²ℓ)`
(`eqC:TIsharp`, with `(1+ϑ*_Q)(1+κ_T)³ = 1+o(1)` and `𝓔_TI = o(H|J|L²ℓ)`).

`C_band` is a parameter, as in the TeX (statement-audit fix: an earlier Lean statement fixed `C_band = C_w`,
which needs `lem:A`, off the headline chain; `thm:main` uses `C_band = 2w_max/(ℰ I_w)` from
`eq:MVLS`). **Weaker than the TeX:** the extra hypothesis `ε < ε₁/4` (harmless: `ε → 0`).
**Stronger than the TeX in one respect:** `BandLS` (via `LmultLE`) only bounds intervals inside `[1, Q²]`,
while the TeX's `Λ_mult` has no such restriction; this is still provable, since every band interval lies
in `[1, Y] ⊂ [1, Q²]` (statement audit). The
"Consequently" clause of the TeX is not part of this statement (it is `prop:second` plus the limit
`ε, ε₄ → 0`, done in `thmMain_of_components` / `assemblyLimit`). -/
def propTIsharp_Statement : Prop :=
  ∀ (P : PrimeSetup) (W : Weight), CTp W ≠ ⊤ → ∀ (ε : ℝ), 0 < ε → ε < 1 / 3 → ε < P.ε₁ / 4 →
    ∀ Cband : ℝ, 1 ≤ Cband → BandLS W ε Cband →
    ∀ Ct : ℝ → ℝ, ContDiff ℝ ∞ Ct →
    (∀ α, 1 ≤ Ct α ∧ Ct α ≤ max Cband (CTp W).toReal) → (∀ α, α ≤ 1 - 2 * ε → Ct α = 1) →
    (∀ α, 1 - 3 / 2 * ε ≤ α → α ≤ 1 + 3 / 2 * ε → Cband ≤ Ct α) →
    (∀ α, 1 + ε / 2 ≤ α → (CTp W).toReal ≤ Ct α) → (∀ α, 1 + 2 * ε ≤ α → Ct α = (CTp W).toReal) →
    P.ProfileBound W Ct

/- (a). The proof uses `eq:MVLS` and the additive large sieve (tails, prime powers, levels
`e ≤ R_max`), i.e. the named hypothesis `MV_LargeSieve`, and `H ≍ Q²` from `lemWH_Statement`. -/
-- `propTIsharp` is proved in `Families/Wired/Phase3.lean` (wired from Families/Phase3/C/TIsharp*).

end Families
