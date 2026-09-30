/-
# Theorem 1.4(a) (families at polynomial height): basic definitions

References are to the paper: Theorem 1.4(a) is proved in §9 (`STATEMENTS-H.md` maps the Lean statements to
it). Theorem 1.1 is formalised in the library `Families`, which this library imports **unchanged**.

Everything here is a definition. The zero counts `Nfam`, `Ns0`, `Nstar0`, `Nd`, the weights `Weight`,
`wSharpFun`, `wSmoothFun`, the quadratic form `Qf` and the form factor `FC` are reused verbatim from
`Families` (they do not involve the height range).
-/
import Families

noncomputable section

open MeasureTheory Filter Topology

namespace Families.Hybrid

open Families

/-- `κ_T = log T / log Q` ((1.4)). Only used for `Q > 1`, `T ≥ 1`. -/
def kappaT (Q T : ℝ) : ℝ := Real.log T / Real.log Q

/-- `β(κ) = (2+κ)/(1+κ)` ((1.4)): the length `Q²T` of Gallagher's hybrid large sieve in units of
`ℓ_* = log(QT)` when `T = Q^κ`. -/
def betaK (κ : ℝ) : ℝ := (2 + κ) / (1 + κ)

/-- `ℓ_* = log(QT)` ((1.4)). -/
def ellS (Q T : ℝ) : ℝ := Real.log (Q * T)

/-- The admissible class of (1.5) at support `β`: `f ≥ 0` even, `supp f ⊂ [−β/2, β/2]`, `f ∈ L²`,
`∫ f = 1`. For `β = 2` this is `Families.AdmissibleWindow` (see `FamiliesH.StatementCheck`). -/
structure AdmissibleWindowB (β : ℝ) (f : ℝ → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ f x
  even : ∀ x, f (-x) = f x
  supp : ∀ x, f x ≠ 0 → x ∈ Set.Icc (-β / 2) (β / 2)
  memL2 : MemLp f 2 volume
  integral_eq_one : ∫ x, f x = 1

/-- `p(β; F_C) = 2 − inf { 𝒬_{F_C}(f) : f admissible at support β }` ((1.5)); `pB 2 C = pC C`
(`FamiliesH.StatementCheck.pB_two`). The paper's `p(β)` is `pB β 1`. -/
def pB (β C : ℝ) : ℝ := 2 - sInf (Qf (FC C) '' {f | AdmissibleWindowB β f})

/-- The heights of a cell with top `κc`: `ℓ^{a₀} ≤ T ≤ Q^{κc}` ((9.2)). -/
def cellHeights (a0 kc Q : ℝ) : Set ℝ := Set.Icc (Real.log Q ^ a0) (Q ^ kc)

/-- The three conclusions of Theorem 1.4(a) with a **height-dependent** target `p(κ_T)`, uniformly for
`ℓ^{a₀} ≤ T ≤ Q^{κ₁}`, in `ε`–`Q₀` form (the analogue of `Families.ProportionsAtLeast`):
`N^s_0 ≥ (p(κ_T) − ε) N`, `N^*_0 ≥ (p(κ_T) − ε) N`, `N_d ≥ ((1+p(κ_T))/2 − ε) N`. -/
def ProportionsAtLeastH (W : Weight) (a0 κ1 : ℝ) (p : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
    ∀ T ∈ Set.Icc (Real.log Q ^ a0) (Q ^ κ1),
      (p (kappaT Q T) - ε) * Nfam W Q T ≤ Ns0 W Q T ∧
      (p (kappaT Q T) - ε) * Nfam W Q T ≤ Nstar0 W Q T ∧
      ((1 + p (kappaT Q T)) / 2 - ε) * Nfam W Q T ≤ Nd W Q T

/-- The same with a **constant** target `p`, uniformly over one cell `ℓ^{a₀} ≤ T ≤ Q^{κc}`. -/
def ProportionsAtLeastCell (W : Weight) (a0 kc p : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
    ∀ T ∈ cellHeights a0 kc Q,
      (p - ε) * Nfam W Q T ≤ Ns0 W Q T ∧
      (p - ε) * Nfam W Q T ≤ Nstar0 W Q T ∧
      ((1 + p) / 2 - ε) * Nfam W Q T ≤ Nd W Q T

end Families.Hybrid
