/-
**`thm:conditional` reduced to its one analytic input.**

The TeX proof of `thm:conditional` (§7.3) has two parts:

1. **the profile bound from `LS(C)`**: "We check `eq:profile` for `c = c_ε` by rerunning the proof of
   `prop:TI`, which uses `cor:LmultA` only through `Λ_mult(K) ≤ (C_w + o(1))H` for `K ≤ Q^{2−ε₁}`; we use
   `LS(C)` there instead" (`lem:M1` + the `lem:M3` split + `lem:M2` on short intervals + `LS(C)`). This is
   *not* assembly: it is a re-run of the analytic proof of `prop:TI` (which is (c), out of scope, in
   this formalisation), and it is not implied by `propTIsharp_Statement` (whose profile is pinned to
   `C_T^+(w)` above the band, not to `C`). We state it as `profileLS_Statement` (new, not a labelled
   TeX result) and take it as an explicit hypothesis;
2. **the assembly**: `prop:zero` + `prop:second` at fixed data (`assembly_fixed`) and the limit step
   (`assemblyLimit_proof`). This part is proved here: `thmConditional_of_components`, sorry-free.

Also proved: `LS(C)` forces `C ≥ 1` given `lem:WH` (`one_le_of_LS`; the TeX's "Necessarily `C ≥ 1`").
-/
import Families.Assembly
import Families.Phase4.A.AssemblyLimit

noncomputable section

open scoped BigOperators ContDiff
open MeasureTheory Filter Topology

namespace Families.Phase4.A

open Families

/-- **The profile bound from `LS(C)`** (proof of Theorem 5.16; new statement, not a labelled TeX
result). For fixed data `P`, a weight `w` satisfying `LS(C)`, `ε ∈ (0, 1/3)` and a smooth nondecreasing
`c_ε : ℝ → [1, C]` with `c_ε = 1` on `(−∞, 1−2ε]` and `c_ε = C` on `[1−3ε/2, ∞)`, the profile bound
`eq:profile` holds with `c = c_ε`. (The TeX: "rerunning the proof of `prop:TI` … with `LS(C)`".) -/
def profileLS_Statement : Prop :=
  ∀ (P : PrimeSetup) (W : Weight) (C : ℝ), LS W C → ∀ ε : ℝ, 0 < ε → ε < 1 / 3 →
    ∀ c : ℝ → ℝ, ContDiff ℝ ∞ c → Monotone c → (∀ α, 1 ≤ c α ∧ c α ≤ C) →
    (∀ α, α ≤ 1 - 2 * ε → c α = 1) → (∀ α, 1 - 3 / 2 * ε ≤ α → c α = C) →
    P.ProfileBound W c

/-! ### `LS(C)` forces `C ≥ 1` -/

lemma famForm_unitAt1 (W : Weight) (Q : ℝ) : famForm W Q (intervalZ 1 1) unitAt1 = W.H Q := by
  unfold famForm Weight.H
  rw [intervalZ_one_one]
  refine Finset.sum_congr rfl fun q _ => ?_
  congr 1
  simp only [Finset.sum_singleton, unitAt1, if_true, one_mul]
  simp only [Int.cast_one, MulChar.map_one, norm_one, one_pow, Finset.sum_const, nsmul_eq_mul,
    mul_one, phiStar]

/-- `LS(C)` and `lem:WH` imply `C ≥ 1` (the diagonal of `Δ` is `H`). -/
lemma one_le_of_LS (hWH : lemWH_Statement) (W : Weight) {C : ℝ} (hLS : LS W C) : 1 ≤ C := by
  by_contra hlt
  push Not at hlt
  have hδ : 0 < (1 - C) / 2 := by linarith
  obtain ⟨Q₀, hQ₀⟩ := hLS 1 one_pos _ hδ
  obtain ⟨Q, ⟨hQ, hQ1⟩, hH⟩ := (((eventually_ge_atTop Q₀).and (eventually_ge_atTop 1)).and
    (H_pos_eventually hWH W)).exists
  have hK : ((1 : ℕ) : ℝ) ≤ Q ^ (2 - 1 : ℝ) := by
    rw [Nat.cast_one]; exact Real.one_le_rpow hQ1 (by norm_num)
  have h := hQ₀ Q hQ 1 hK 1 le_rfl (by push_cast; nlinarith) unitAt1
  rw [famForm_unitAt1, normSq_unitAt1, mul_one] at h
  nlinarith

/-! ### An explicit smooth nondecreasing `c_ε` -/

/-- `c_ε(α) = 1 + (C − 1) ramp(1 − 2ε, 1 − 3ε/2, α)`. -/
def condProfile (C ε α : ℝ) : ℝ := 1 + (C - 1) * ramp (1 - 2 * ε) (1 - 3 / 2 * ε) α

lemma condProfile_spec {C ε : ℝ} (hC : 1 ≤ C) (hε : 0 < ε) :
    ContDiff ℝ ∞ (condProfile C ε) ∧ Monotone (condProfile C ε) ∧
    (∀ α, 1 ≤ condProfile C ε α ∧ condProfile C ε α ≤ C) ∧
    (∀ α, α ≤ 1 - 2 * ε → condProfile C ε α = 1) ∧
    (∀ α, 1 - 3 / 2 * ε ≤ α → condProfile C ε α = C) := by
  have hab : 1 - 2 * ε < 1 - 3 / 2 * ε := by linarith
  refine ⟨contDiff_const.add (contDiff_const.mul (ramp_contDiff _ _)), fun x y hxy => ?_,
    fun α => ?_, fun α hα => ?_, fun α hα => ?_⟩
  · unfold condProfile ramp
    have : Real.smoothTransition ((x - (1 - 2 * ε)) / (1 - 3 / 2 * ε - (1 - 2 * ε))) ≤
        Real.smoothTransition ((y - (1 - 2 * ε)) / (1 - 3 / 2 * ε - (1 - 2 * ε))) :=
      Real.smoothTransition.monotone (div_le_div_of_nonneg_right (by linarith) (by linarith))
    nlinarith
  · have h0 := ramp_nonneg (1 - 2 * ε) (1 - 3 / 2 * ε) α
    have h1 := ramp_le_one (1 - 2 * ε) (1 - 3 / 2 * ε) α
    unfold condProfile
    constructor <;> nlinarith
  · unfold condProfile; rw [ramp_of_le hab hα]; ring
  · unfold condProfile; rw [ramp_of_ge hab hα]; ring

/-! ### The assembly -/

/-- **`thm:conditional` from its analytic input** (proved; standard axioms only). The profile bound
from `LS(C)` (`profileLS_Statement`), the inputs `lem:B2`, `eqB:Mrat` of `SecondMomentAssembly`,
and the named hypotheses give `thmConditional_Statement`: `assembly_fixed` (`prop:zero` + `prop:second`
at fixed data) and `assemblyLimit_proof` (the §7.3 limit step, with `C_max = C`). -/
theorem thmConditional_of_components (hProf : profileLS_Statement) (hB2 : lemB2_Statement)
    (hMrat : eqBMrat_Statement) (hC : ClassicalInputs) (hR : PortedReductions) :
    thmConditional_Statement := by
  obtain ⟨hZ, hRvM⟩ := hR.zeroSide hC.mvLargeSieve hC.montgomery69 hC.stirling hC.masses
  have hS : propSecond_Statement :=
    hR.secondMoment hC.mvLargeSieve hC.stirling hC.masses hRvM hB2 hMrat
  intro W C a0 A0 ha0 hA0 hLS ε hε
  have hC1 : 1 ≤ C := one_le_of_LS hC.masses W hLS
  obtain ⟨P, ε', hPa0, hPA0, hε'0, hε'3, -, hlim⟩ :=
    assemblyLimit_proof a0 A0 ha0 hA0 C C hC1 le_rfl (ε / 2) (by positivity)
  obtain ⟨hsmooth, hmono, hrange, hbelow, habove⟩ := condProfile_spec hC1 hε'0
  have hprof : P.ProfileBound W (condProfile C ε') :=
    hProf P W C hLS ε' hε'0 hε'3 _ hsmooth hmono hrange hbelow habove
  have hcert : pC C - ε / 2 ≤ P.certValue (condProfile C ε') :=
    hlim _ hsmooth.continuous hrange hbelow fun α hα => habove α (by linarith)
  obtain ⟨Q₀, hQ₀⟩ := assembly_fixed hZ hRvM hS P W _ hsmooth (fun α => (hrange α).1) hprof
    (ε / 2) (by positivity)
  refine ⟨Q₀, fun Q hQ T hT => ?_⟩
  have hT' : T ∈ P.heights Q := by
    unfold PrimeSetup.heights; rw [hPa0, hPA0]; exact hT
  obtain ⟨h1, h2, h3⟩ := hQ₀ Q hQ T hT'
  have hN0 := Nfam_nonneg W Q T
  refine ⟨?_, ?_, ?_⟩
  · exact le_trans (mul_le_mul_of_nonneg_right (by linarith) hN0) h1
  · exact le_trans (mul_le_mul_of_nonneg_right (by linarith) hN0) h2
  · exact le_trans (mul_le_mul_of_nonneg_right (by linarith) hN0) h3

end Families.Phase4.A
