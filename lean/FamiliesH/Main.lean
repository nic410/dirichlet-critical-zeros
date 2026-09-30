/-
# Theorem 1.4(a): the headline statements

* `thmH_Statement` — **Theorem 1.4(a)** (sharp route), with the certificates of column (a) of the table after
  Theorem 1.4.
* `thmHcell_Statement` — the one-cell form: a constant target `p(β(κc)) − ε` uniformly for
  `ℓ^{a₀} ≤ T ≤ Q^{κc}` (the output of §§9.1–9.4 for a fixed cell top `κc`).

The glue `thmH_of_parts` (`FamiliesH.Glue`) derives `thmH_Statement` from the component statements of
`FamiliesH.Statements` without `sorry`; `thmH` (`FamiliesH.Headline`) applies it.
-/
import FamiliesH.Statements

noncomputable section

open MeasureTheory Filter Topology

namespace Families.Hybrid

open Families

/-- **The one-cell theorem** (sharp route). For every `ε > 0` there is `η₀(ε) > 0`, **independent of
`a₀` and `κc`**, such that for every cell top `κc > 0`, every `a₀ > 0`, `η ≤ η₀` and
`w ∈ {w_η, w^sm_η}`: uniformly for `ℓ^{a₀} ≤ T ≤ Q^{κc}`,
`N^s_0, N^*_0 ≥ (p(β(κc)) − ε − o(1)) N` and `N_d ≥ ((1 + p(β(κc)) − ε)/2 − o(1)) N`. -/
def thmHcell_Statement : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ (a0 kc : ℝ), 0 < a0 → 0 < kc →
    ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ W : Weight, (W.w = wSharpFun η ∨ W.w = wSmoothFun η) →
      ProportionsAtLeastCell W a0 kc (pB (betaK kc) 1 - ε)

/-- **Theorem 1.4(a) (polynomial height; sharp route).** For every `ε > 0` there is `η₀(ε) > 0`,
independent of `a₀` and `κ₁`, such that for every `a₀, κ₁ > 0`, `η ≤ η₀` and `w ∈ {w_η, w^sm_η}`:
uniformly for `ℓ^{a₀} ≤ T ≤ Q^{κ₁}`,
`liminf_Q inf_T (N^s_0/N − p(β(κ_T))) ≥ −ε`, the same for `N^*_0/N`, and for `N_d/N` with
`(1 + p(β(κ_T)))/2` — written without division as `ProportionsAtLeastH W a₀ κ₁ (κ ↦ p(β(κ)) − ε)`
(the `N_d` bound is then `(1 + p(β(κ_T)))/2 − ε/2 − o(1)`, stronger than the TeX's `− ε`, as in
`Families.ProportionsAtLeast`);
and the certified values `p(β(κ)) ≥ 0.865673, 0.824355, 0.797213, 0.764149, 0.727484` at
`κ = 1, 2, 3, 5, 10` (`certH_Statement`). -/
def thmH_Statement : Prop :=
  (∀ ε : ℝ, 0 < ε → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ (a0 κ1 : ℝ), 0 < a0 → 0 < κ1 →
    ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ W : Weight, (W.w = wSharpFun η ∨ W.w = wSmoothFun η) →
      ProportionsAtLeastH W a0 κ1 (fun κ => pB (betaK κ) 1 - ε)) ∧
  certH_Statement

end Families.Hybrid
