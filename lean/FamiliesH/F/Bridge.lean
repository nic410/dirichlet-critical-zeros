/-
# Package F: the bridge `HSetup → PrimeSetup`

The objects of `HSetup` that do not involve the family weights are the objects of the families
`PrimeSetup` with the same fixed data, evaluated at the conductor-like parameter `Q' = QT`:
`L = λ log(QT) = PrimeSetup.L (QT)`, `Y`, `range`, `Υ`, `a`, `ψ_L`, `g`, `Φ`, `𝒦(·,·)` (with the same `J = J(T)`),
`x_y(u)`, …  This lets package F reuse the proved families lemmas that are uniform in `Q ≥ 1`
(they never use `λ < 2` beyond `λ > 0`). `HSetup.toPS` is a legitimate `PrimeSetup` because
`λ < β(κc) ≤ 2` and `λ(1+ε₁) ≤ β(κc) − ε₁ ≤ 2 − ε₁`.
-/
import FamiliesH.Statements

noncomputable section

open scoped BigOperators ComplexConjugate ArithmeticFunction.Moebius
open ArithmeticFunction Finset MeasureTheory

namespace Families.Hybrid

open Families

namespace F

lemma betaK_le_two {κ : ℝ} (hκ : 0 ≤ κ) : betaK κ ≤ 2 := by
  unfold betaK
  rw [div_le_iff₀ (by linarith)]; linarith

end F

namespace HSetup

open Families.Hybrid.F

variable (P : HSetup)

/-- The families fixed data with the same `λ, ε₁, θ, ψ, ε₃, Υ₀, ψ_j` (heights `a₀ < a₀+1` are
irrelevant: no lemma used through this bridge involves `PrimeSetup.heights`). -/
def toPS : PrimeSetup where
  a0 := P.a0
  A0 := P.a0 + 1
  lam := P.lam
  ε₁ := P.ε₁
  θ := P.θ
  ψ := P.ψ
  ε₃ := P.ε₃
  Υ₀ := P.Υ₀
  ψj := P.ψj
  a0_pos := P.a0_pos
  a0_lt := by linarith
  lam_pos := P.lam_pos
  lam_lt := lt_of_lt_of_le P.lam_lt (betaK_le_two P.kc_pos.le)
  ε₁_pos := P.ε₁_pos
  lam_ε₁ := le_trans P.lam_ε₁ (by linarith [betaK_le_two P.kc_pos.le])
  θ_pos := P.θ_pos
  θ_lt := P.θ_lt
  ψ_smooth := P.ψ_smooth
  ψ_even := P.ψ_even
  ψ_supp := P.ψ_supp
  ψ_ne := P.ψ_ne
  ε₃_pos := P.ε₃_pos
  ε₃_lt := P.ε₃_lt
  Υ₀_smooth := P.Υ₀_smooth
  Υ₀_range := P.Υ₀_range
  Υ₀_one := P.Υ₀_one
  Υ₀_zero := P.Υ₀_zero
  ψj_smooth := P.ψj_smooth
  ψj_nonneg := P.ψj_nonneg
  ψj_supp := P.ψj_supp
  ψj_sum := P.ψj_sum
  ψj_deriv := P.ψj_deriv

/-! ### Definitional bridge lemmas (all `rfl`) -/

lemma L_eq (Q T : ℝ) : P.L Q T = P.toPS.L (Q * T) := rfl
lemma X_eq (Q T : ℝ) : P.X Q T = P.toPS.X (Q * T) := rfl
lemma Y_eq (Q T : ℝ) : P.Y Q T = P.toPS.Y (Q * T) := rfl
lemma range_eq (Q T : ℝ) : P.range Q T = P.toPS.range (Q * T) := rfl
lemma rangeZ_eq (Q T : ℝ) : P.rangeZ Q T = P.toPS.rangeZ (Q * T) := rfl
lemma Ups_eq (Q T : ℝ) : P.Ups Q T = P.toPS.Ups (Q * T) := rfl
lemma aVec_eq (Q T : ℝ) : P.aVec Q T = P.toPS.aVec (Q * T) := rfl
lemma blocks_eq (Q T : ℝ) : P.blocks Q T = P.toPS.blocks (Q * T) := rfl
lemma Rj_eq (Q T : ℝ) : P.Rj Q T = P.toPS.Rj Q T := rfl
lemma Schi_eq {q : ℕ} (χ : DirichletCharacter ℂ q) (Q T : ℝ) (x : ℕ → ℝ) (t : ℝ) :
    P.Schi χ Q T x t = P.toPS.Schi χ (Q * T) x t := rfl
lemma J_eq (T : ℝ) : P.J T = P.toPS.J T := rfl
lemma Jlen_eq (T : ℝ) : P.Jlen T = P.toPS.Jlen T := rfl
lemma hatJ_eq (T ξ : ℝ) : P.hatJ T ξ = P.toPS.hatJ T ξ := rfl
lemma ψL_eq (Q T u : ℝ) : P.ψL Q T u = P.toPS.ψL (Q * T) u := rfl
lemma vfun_eq (s : ℝ) : P.vfun s = P.toPS.vfun s := rfl
lemma aInt_eq : P.aInt = P.toPS.aInt := rfl
lemma bInt_eq : P.bInt = P.toPS.bInt := rfl
lemma g_eq (Q T u : ℝ) : P.g Q T u = P.toPS.g (Q * T) u := rfl
lemma Φ_eq (Q T t : ℝ) : P.Φ Q T t = P.toPS.Φ (Q * T) t := rfl
lemma 𝒦_eq (Q T : ℝ) (n m : ℕ) : P.𝒦 Q T n m = P.toPS.𝒦 (Q * T) T n m := rfl
lemma xVec_eq (Q T : ℝ) (y : ℕ → ℝ) (u : ℝ) : P.xVec Q T y u = P.toPS.xVec (Q * T) T y u := rfl

/-- `R_j` of the hybrid setup is `R_j` of the families setup at `(QT, 1)`. -/
lemma Rj_eq_one (Q T : ℝ) (j : ℕ) : P.Rj Q T j = P.toPS.Rj (Q * T) 1 j := by
  simp only [HSetup.Rj, PrimeSetup.Rj, toPS, mul_one]

lemma aSharp_eq (Q T : ℝ) : P.aSharp Q T = P.toPS.aSharp (Q * T) 1 := by
  funext n
  simp only [HSetup.aSharp, PrimeSetup.aSharp, Rj_eq_one]
  rfl

lemma bVec_eq (Q T : ℝ) : P.bVec Q T = P.toPS.bVec (Q * T) 1 := by
  funext n
  simp only [HSetup.bVec, PrimeSetup.bVec, aSharp_eq]
  rfl

end HSetup


end Families.Hybrid
