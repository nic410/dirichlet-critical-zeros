/-
# Theorem 1.4(a), package Z (zero side at polynomial height): the bridge to the families zero side

The hybrid Gabor objects of one cell (`HSetup.L Q T = λ log(QT)`, `HSetup.KJ`, `HSetup.pk`,
`HSetup.Gabor`, `HSetup.Mfrak`) are the families objects of `Families.PrimeSetup` evaluated at the
**bandwidth argument** `Q' = QT`: the families definitions depend on their `Q` only through
`L = λ log Q'`. So `toPS P` (the same fixed data, as a `PrimeSetup`; legitimate because
`λ < β(κc) ≤ 2`) and `Q' = Q * T` give **definitional** equalities (`L_eq`, `KJ_eq`, `pk_eq`,
`Gabor_eq`, `X_eq`), and every per-character lemma of `Families.Ported.Zero` (explicit formula,
envelope, Poisson–Gabor identity, block structure, rank–trace, deletion) applies verbatim.
The family sums keep the family parameter `Q` (conductors `q ≤ Q`), which is why the family-level
lemmas (`lem:RvM`, the trace, the exterior tail, the assembly) are re-proved in this package.
-/
import FamiliesH.Glue

noncomputable section

open scoped BigOperators ComplexConjugate ArithmeticFunction.Moebius
open scoped ENNReal ContDiff
open ArithmeticFunction Finset MeasureTheory Filter Topology RHLinalg

namespace Families.Hybrid.Z

open Families Families.Hybrid Families.Ported.Zero

/-- The fixed data of a cell as a `Families.PrimeSetup` (the height exponent `A₀ := a₀ + 1` is a
dummy: the families heights are never used through `toPS`). -/
def toPS (P : HSetup) : PrimeSetup where
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

variable (P : HSetup)

@[simp] lemma toPS_lam : (toPS P).lam = P.lam := rfl
@[simp] lemma toPS_θ : (toPS P).θ = P.θ := rfl
@[simp] lemma toPS_ψ : (toPS P).ψ = P.ψ := rfl

lemma L_eq (Q T : ℝ) : (toPS P).L (Q * T) = P.L Q T := rfl

lemma X_eq (Q T : ℝ) : (toPS P).X (Q * T) = P.X Q T := rfl

lemma aInt_eq : (toPS P).aInt = P.aInt := rfl

lemma KJ_eq (Q T τ₀ : ℝ) : (toPS P).KJ (Q * T) T τ₀ = P.KJ Q T τ₀ := rfl

lemma hatψL_eq (Q T : ℝ) (w : ℂ) : (toPS P).hatψL (Q * T) w = P.hatψL Q T w := rfl

lemma pk_eq' (Q T τ₀ : ℝ) (k : ℤ) (z : ℂ) : (toPS P).pk (Q * T) τ₀ k z = P.pk Q T τ₀ k z := rfl

lemma Gabor_eq (Q T τ₀ : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (toPS P).Gabor (Q * T) T τ₀ χ = P.Gabor Q T τ₀ χ := rfl

/-- `𝔐` at polynomial height, per character through the families `Ĝ` at `Q' = QT`. -/
lemma Mfrak_eqH (W : Weight) (Q T τ₀ : ℝ) :
    P.Mfrak W Q T τ₀ = famSum W Q (fun _ χ => frobSq (Ghat (toPS P) (Q * T) T τ₀ χ)) := by
  unfold HSetup.Mfrak
  congr 1; funext q χ
  rw [frobSq_eq_sum]
  rfl

/-- `ℓ_* = log(QT) = log Q + log T`. -/
lemma ellS_eq {Q T : ℝ} (hQ : 0 < Q) (hT : 0 < T) : ellS Q T = Real.log Q + Real.log T := by
  unfold ellS; rw [Real.log_mul hQ.ne' hT.ne']

/-- `1 < QT` in the cell. -/
lemma one_lt_QT {Q T : ℝ} (hQ : 1 < Q) (hT : 1 ≤ T) : 1 < Q * T := by nlinarith

end Families.Hybrid.Z
