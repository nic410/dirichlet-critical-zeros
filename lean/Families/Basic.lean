/-
Families paper, Lean formalisation: shared definitions. Everything here is a *definition*; no theorem in this file.

TeX sources of the paper: `main.tex` and the lemma sections `lemma-A.tex`, `lemma-toeplitz-C.tex`,
`lemma-B-majorant.tex`.
-/
import Mathlib

noncomputable section

open scoped BigOperators ComplexConjugate ArithmeticFunction.Moebius
open ArithmeticFunction Finset

namespace Families

/-! ## Additive characters, exponential sums, vectors -/

/-- `e(x) = exp(2πix)`. -/
def eA (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

/-- `S_x(θ) = ∑_{n ∈ I} x_n e(nθ)` for a vector `x` supported on the finite set `I ⊂ ℤ`. -/
def S (I : Finset ℤ) (x : ℤ → ℂ) (θ : ℝ) : ℂ := ∑ n ∈ I, x n * eA (n * θ)

/-- `‖x‖² = ∑_{n ∈ I} |x_n|²`. -/
def normSq (I : Finset ℤ) (x : ℤ → ℂ) : ℝ := ∑ n ∈ I, ‖x n‖ ^ 2

/-- The integer interval `{N₀, N₀+1, …, N₀+K-1}` (it contains exactly `K` integers). -/
def intervalZ (N₀ : ℤ) (K : ℕ) : Finset ℤ := Finset.Ico N₀ (N₀ + K)

/-- The reduced residues `{c : 0 ≤ c < e, (c,e) = 1}` (so `∑*_{c mod e}`). For `e = 1` this is `{0}`. -/
def reduced (e : ℕ) : Finset ℕ := (Finset.range e).filter (fun c => Nat.Coprime c e)

/-- The Ramanujan sum `c_e(h) = ∑*_{c mod e} e(ch/e)`. -/
def ramanujan (e : ℕ) (h : ℤ) : ℂ := ∑ c ∈ reduced e, eA ((c : ℝ) * h / e)

/-! ## Primitive Dirichlet characters -/

/-- The primitive Dirichlet characters modulo `q` (values in `ℂ`). -/
def primChars (q : ℕ) : Finset (DirichletCharacter ℂ q) :=
  haveI := Classical.decPred (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)
  Finset.univ.filter (fun χ => χ.IsPrimitive)

/-- `φ*(q)`: the number of primitive characters modulo `q`. -/
def phiStar (q : ℕ) : ℕ := (primChars q).card

/-- `n ≥ 1` is `Q`-rough: every prime factor of `n` exceeds `Q`. -/
def IsRough (Q : ℝ) (n : ℤ) : Prop := 1 ≤ n ∧ ∀ p : ℕ, p.Prime → (p : ℤ) ∣ n → Q < p

/-! ## Admissible weights (`def:admissible`, Definition 2.1) -/

/-- An admissible modulus weight `w : (0,1] → [0,∞)`, extended by `0` to `ℝ`:
bounded variation on `ℝ` (jumps at the end points included), `supp w ⊂ [η,1]` with `0 < η < 1/2`,
and `∫₀¹ u w(u) du > 0` (which forces `w ≢ 0`). -/
structure Weight where
  /-- the weight, extended by `0` to all of `ℝ` -/
  w : ℝ → ℝ
  /-- the lower cut of the support -/
  η : ℝ
  η_pos : 0 < η
  η_lt_half : η < 1 / 2
  nonneg : ∀ u, 0 ≤ w u
  supp : ∀ u, w u ≠ 0 → η ≤ u ∧ u ≤ 1
  bv : BoundedVariationOn w Set.univ
  Iw_pos : 0 < ∫ u in (0 : ℝ)..1, u * w u

namespace Weight

variable (W : Weight)

/-- `w_max = sup w`. -/
def wmax : ℝ := sSup (Set.range W.w)

/-- `V_w`: total variation of the extended weight on `ℝ`. -/
def Vw : ℝ := (eVariationOn W.w Set.univ).toReal

/-- `I_w = ∫₀¹ u w(u) du`. -/
def Iw : ℝ := ∫ u in (0 : ℝ)..1, u * W.w u

/-- `c_w = (6/π²) I_w`. -/
def cw : ℝ := 6 / Real.pi ^ 2 * W.Iw

/-- `w̃(u) = u² w(u)`. -/
def wt (u : ℝ) : ℝ := u ^ 2 * W.w u

/-- `ω(q) = w(q/Q) q/φ(q)` (`eq:omega`); `ω_χ = ω(q)` for `χ` primitive mod `q`. -/
def omega (Q : ℝ) (q : ℕ) : ℝ := W.w (q / Q) * q / (Nat.totient q : ℝ)

/-- The family mass `H = ∑_{χ ∈ 𝓕} ω_χ = ∑_q ω(q) φ*(q)` (`eq:HW`). Only `q ≤ Q` can contribute. -/
def H (Q : ℝ) : ℝ := ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * phiStar q

/-- The additive (Farey) mass `W = ∑_q w(q/Q) φ(q)` (`eq:HW`). -/
def Wm (Q : ℝ) : ℝ := ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.w (q / Q) * Nat.totient q

end Weight

/-! ## The family Gram kernel and the family form -/

/-- The family Gram kernel `Δ(n,m) = ∑_{χ ∈ 𝓕} ω_χ χ(n) \bar χ(m)` (`eq:Delta`).
The family `𝓕` is the set of primitive `χ mod q` with `w(q/Q) > 0`; since `ω(q) = 0` otherwise,
summing over all primitive `χ mod q`, `1 ≤ q ≤ Q`, is the same. -/
def Δ (W : Weight) (Q : ℝ) (n m : ℤ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (W.omega Q q : ℂ) * ∑ χ ∈ primChars q, χ n * conj (χ m)

/-- The family form `x^*Δx = ∑_{χ ∈ 𝓕} ω_χ |∑_n x_n χ(n)|²` for `x` supported on `I`. -/
def famForm (W : Weight) (Q : ℝ) (I : Finset ℤ) (x : ℤ → ℂ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ χ ∈ primChars q, ‖∑ n ∈ I, x n * χ n‖ ^ 2

/-- The additive large-sieve form of the weighted Farey measure
`𝔉_w = ∑_q w(q/Q) ∑*_{b mod q} δ_{b/q}`: `∫ |S_x|² d𝔉_w`. -/
def fareyForm (W : Weight) (Q : ℝ) (I : Finset ℤ) (x : ℤ → ℂ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.w (q / Q) * ∑ b ∈ reduced q, ‖S I x ((b : ℝ) / q)‖ ^ 2

/-! ## Farey-type measures given by level weights

A measure `μ_a = ∑_{e ∈ E} a(e) ∑*_{c mod e} δ_{c/e}` on `𝕋` (finitely many levels, real weights).
Its quadratic form is `∫|S_x|² dμ_a` and its Toeplitz kernel is `k_a(h) = ∫ e(hθ) dμ_a = ∑_e a(e) c_e(h)`. -/

/-- `∫ |S_x|² dμ_a` for `μ_a = ∑_{e ∈ E} a(e) ∑*_{c mod e} δ_{c/e}`. -/
def levelForm (E : Finset ℕ) (a : ℕ → ℝ) (I : Finset ℤ) (x : ℤ → ℂ) : ℝ :=
  ∑ e ∈ E, a e * ∑ c ∈ reduced e, ‖S I x ((c : ℝ) / e)‖ ^ 2

/-- Toeplitz kernel `k_a(h) = ∑_{e∈E} a(e) c_e(h)` of the level measure `μ_a`. -/
def levelKernel (E : Finset ℕ) (a : ℕ → ℝ) (h : ℤ) : ℂ := ∑ e ∈ E, (a e : ℂ) * ramanujan e h

/-- The Toeplitz matrix `[k(n-m)]_{n,m ∈ I}`. -/
def toeplitz (I : Finset ℤ) (k : ℤ → ℂ) : Matrix I I ℂ := fun n m => k ((n : ℤ) - m)

/-- The Gram matrix `[Δ(n,m)]_{n,m ∈ I}`. -/
def gramMatrix (W : Weight) (Q : ℝ) (I : Finset ℤ) : Matrix I I ℂ := fun n m => Δ W Q n m

/-! ## Lemma 6.13 objects: `k_ω`, `Ω`, `μ_Ω`, `m`, `μ^m`, `μ^♮`, `μ_Ω^+` -/

/-- `k_ω(h) = ∑_{d | h} φ(d) ∑_{j ≥ 1} μ(j) ω(dj)` (`lem:toeplitz`); all `d ≥ 1` if `h = 0`.
Since `ω(q) = 0` for `q > Q`, only `d ≤ Q`, `j ≤ ⌊Q⌋/d` contribute. -/
def kω (W : Weight) (Q : ℝ) (h : ℤ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun d : ℕ => ((d : ℕ) : ℤ) ∣ h),
    (Nat.totient d : ℝ) * ∑ j ∈ Finset.Icc 1 (⌊Q⌋₊ / d), (μ j : ℝ) * W.omega Q (d * j)

/-- The level weights `Ω(e) = (φ(e)/e) ∑_{r sqfree, (r,e)=1} μ(r) ω(er)/r` (`eqC:Omega`, first form).
Only `r ≤ Q` contribute. -/
def Ωlev (W : Weight) (Q : ℝ) (e : ℕ) : ℝ :=
  (Nat.totient e : ℝ) / e *
    ∑ r ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun r : ℕ => Squarefree r ∧ Nat.Coprime r e),
      (μ r : ℝ) * W.omega Q (e * r) / r

/-- `m(u) = (∑_{μ(r) = -1} w(ur)/φ(r) − w(u))_+` for `u > 0` (`eqC:m`); only `r ≤ 1/u` contribute. -/
def mfun (W : Weight) (u : ℝ) : ℝ :=
  max ((∑ r ∈ (Finset.Icc 1 ⌊1 / u⌋₊).filter (fun r : ℕ => μ r = -1), W.w (u * r) / Nat.totient r)
    - W.w u) 0

/-- `m̃(u) = u² m(u)`. -/
def mt (W : Weight) (u : ℝ) : ℝ := u ^ 2 * mfun W u

/-- The levels that can carry mass: `1 ≤ e ≤ Q`. -/
def levels (Q : ℝ) : Finset ℕ := Finset.Icc 1 ⌊Q⌋₊

/-- Level weights of `μ_Ω`. -/
def aΩ (W : Weight) (Q : ℝ) : ℕ → ℝ := fun e => Ωlev W Q e
/-- Level weights of `μ_Ω^+`. -/
def aΩplus (W : Weight) (Q : ℝ) : ℕ → ℝ := fun e => max (Ωlev W Q e) 0
/-- Level weights of `μ^m = ∑_e m(e/Q) ∑*_c δ_{c/e}`. -/
def aM (W : Weight) (Q : ℝ) : ℕ → ℝ := fun e => mfun W (e / Q)
/-- Level weights of `μ^♮ = μ_Ω + μ^m`. -/
def aNat (W : Weight) (Q : ℝ) : ℕ → ℝ := fun e => Ωlev W Q e + mfun W (e / Q)

/-- `T_ω = [k_ω(n-m)]` on `ℂ^I`. -/
def Tω (W : Weight) (Q : ℝ) (I : Finset ℤ) : Matrix I I ℂ := toeplitz I (fun h => (kω W Q h : ℂ))
/-- `T^+`: Toeplitz matrix of `μ_Ω^+`. -/
def Tplus (W : Weight) (Q : ℝ) (I : Finset ℤ) : Matrix I I ℂ :=
  toeplitz I (levelKernel (levels Q) (aΩplus W Q))
/-- `T^♮`: Toeplitz matrix of `μ^♮`. -/
def Tnat (W : Weight) (Q : ℝ) (I : Finset ℤ) : Matrix I I ℂ :=
  toeplitz I (levelKernel (levels Q) (aNat W Q))
/-- `T_{μ_Ω}`: Toeplitz matrix of `μ_Ω` (equal to `T_ω` by Lemma 6.13(ii)). -/
def TΩ (W : Weight) (Q : ℝ) (I : Finset ℤ) : Matrix I I ℂ :=
  toeplitz I (levelKernel (levels Q) (aΩ W Q))

/-! ## Euler-product constants -/

/-- `ℰ = ∏_p (1 − p^{-2} − p^{-3}) = 0.4791…` -/
def Ecal : ℝ := ∏' p : Nat.Primes, (1 - ((p : ℕ) : ℝ) ^ (-2 : ℤ) - ((p : ℕ) : ℝ) ^ (-3 : ℤ))

/-- `C_G = 6/(π² ℰ) = 1.2687…` -/
def CG : ℝ := 6 / (Real.pi ^ 2 * Ecal)

end Families
