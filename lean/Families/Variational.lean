/-
The variational constant `p(C)` (`eq:pC`, main.tex §1 and §7) and the rational certificates
(`prop:cert`, `paper/cert/certify.py`).
-/
import Mathlib

noncomputable section

open MeasureTheory

namespace Families

/-- `F_C(α) = α` for `α ≤ 1` and `C` for `α > 1` (`eq:pC`). Only `α = |x-y| ∈ [0,2]` is ever used. -/
def FC (C α : ℝ) : ℝ := if α ≤ 1 then α else C

/-- `𝒬_F(f) = ∫ f² + ∬ f(x) f(y) F(|x-y|) dx dy` (the double integral written as an iterated
integral; for the admissible class below the integrand is integrable on `ℝ²`, so this is the
product integral by Fubini). -/
def Qf (F : ℝ → ℝ) (f : ℝ → ℝ) : ℝ := (∫ x, f x ^ 2) + ∫ x, ∫ y, f x * f y * F |x - y|

/-- The admissible class of `eq:pC`: `f ≥ 0` even, `supp f ⊂ [-1,1]`, `∫ f = 1`, and `f ∈ L²`
(the paper: "the functional is finite on `L²([-1,1])`"). -/
structure AdmissibleWindow (f : ℝ → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ f x
  even : ∀ x, f (-x) = f x
  supp : ∀ x, f x ≠ 0 → x ∈ Set.Icc (-1 : ℝ) 1
  memL2 : MemLp f 2 volume
  integral_eq_one : ∫ x, f x = 1

/-- `p(C) = 2 − inf { 𝒬_{F_C}(f) : f admissible }` (`eq:pC`). -/
def pC (C : ℝ) : ℝ := 2 - sInf (Qf (FC C) '' {f | AdmissibleWindow f})

end Families
