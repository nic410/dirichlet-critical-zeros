/-
# The headline theorem (`thm:main`) and the glue theorems

* **`thmMain : thmMain_Statement`** — **the headline, unconditional** (no hypotheses; `#print axioms`:
  `propext`, `Classical.choice`, `Quot.sound`). It is `thmMain_of_parts` applied to the (a) theorems
  (`lemCTlimit`, `propSharpLS`, `propTIsharp`, `lemB2`, `eqBMrat`, `assemblyLimit`), the discharged
  classical inputs (`Hyp.MV_LargeSieve_proof`, `Hyp.StirlingDigamma_proof`, `Hyp.PNT_dlVP_proof`,
  `lemWH`), the unconditional zero side `Ported.Zero.propZero_unconditional` (`prop:zero` + lower half of
  `lem:RvM`, using Montgomery 1969 only in the q-aspect range `T' ≤ Q`, which is proved) and the §5
  assembly `Ported.secondMoment`.
* `thmMain_of_parts` — **glue theorem, proved**: the (a) statements, `MV_LargeSieve`, `StirlingDigamma`,
  `lemWH_Statement`, the zero-side *conclusion* `propZero_Statement ∧ lemRvM_lower_Statement` and
  `SecondMomentAssembly` imply `thmMain_Statement`.
* `thmMain_of_components` — the glue in bundled form (the (a) statements + `ClassicalInputs` +
  `PortedReductions`), a corollary of `thmMain_of_parts`.
* `thmMain_of_montgomery (hC : ClassicalInputsReduced)` — a conditional variant of the headline. The full
  `Montgomery69_Density` (all heights) is **not** proved and is **not** needed by `thmMain`.

The (a) statements consumed *directly* by the glue are `lemCTlimit` (`C_T^+ → 1`), `propSharpLS`
(`C_T^+ ≥ 1`), `propTIsharp` (the profile bound), `lemB2` and `eqBMrat` (inputs of
`SecondMomentAssembly`) and `assemblyLimit` (the limit `ε, ε₄, θ → 0`, `λ → 2`). The other (a) targets
(`lemOmega_*`, `lemfS`, `lemDual`, `propCount`, `lemC`, `lemB1`) are consumed inside the proofs of these.
-/
import Families.Assembly
import Families.Wired.Phase1
import Families.Wired.Phase4
import Families.Wired.Phase3
import Families.Wired.Phase2
import Families.Hyp.Reduced
import Families.Ported.Reduced
import Families.Ported.Full
import Families.Ported.Zero.Unconditional

noncomputable section

open scoped BigOperators ComplexConjugate ArithmeticFunction.Moebius ENNReal ContDiff
open ArithmeticFunction Finset MeasureTheory Filter Topology

namespace Families

/-- **Glue theorem for `thm:main`, zero-side form** (proved; standard axioms only). The proof of
`thm:main` (Theorem 1.1; proof in §7.3): `lem:CTlimit` gives `C_T^+(w) ≤ 1 + 83/L_η ≤ 1 + ε/3` for
`η ≤ η₀(ε)`; `prop:sharpLS` gives `C_T^+ ≥ 1`; the band constant comes from the large sieve (`eq:MVLS`)
and `lem:WH`; `prop:TIsharp` (with an explicit smooth `C̃_ε`) gives the profile bound `eq:profile`;
`prop:second` (via `SecondMomentAssembly`, fed with `lem:B2`, `eqB:Mrat`) and `prop:zero` (the
zero-side conclusion `hZero`, with the lower half of `lem:RvM`) give `N^s_0 ≥ (P.certValue C̃ − o(1)) N`
(`assembly_fixed`); `assemblyLimit` gives `P.certValue C̃ ≥ p(C_T^+) − ε/3`; `lem:pLip` gives
`p(C_T^+) ≥ p(1) − ε/3`; and `prop:cert` gives `p(1) ≥ 0.932282`.

Unlike `thmMain_of_components`, this takes the zero side's *conclusion* rather than
`ZeroSideReduction` + `Montgomery69_Density`, so the unconditional zero side
(`Ported.Zero.propZero_unconditional`, Montgomery only for `T' ≤ Q`) can be fed in. -/
theorem thmMain_of_parts
    (hCT : lemCTlimit_Statement) (hSharp : propSharpLS_Statement)
    (hTI : propTIsharp_Statement) (hB2 : lemB2_Statement) (hMrat : eqBMrat_Statement)
    (hLim : assemblyLimit_Statement) (hMV : MV_LargeSieve) (hStir : StirlingDigamma)
    (hWH : lemWH_Statement) (hZero : propZero_Statement ∧ lemRvM_lower_Statement)
    (hSec : SecondMomentAssembly) : thmMain_Statement := by
  obtain ⟨hZ, hRvM⟩ := hZero
  have hS : propSecond_Statement := hSec hMV hStir hWH hRvM hB2 hMrat
  refine ⟨fun a0 A0 ε ha0 hA0 hε => ?_, thmMain_constant⟩
  -- the choice of `η₀(ε)`: `L_η = log(1/η) ≥ max(3, 249/ε)`
  set M : ℝ := max 3 (249 / ε) with hMdef
  have hM3 : 3 ≤ M := le_max_left _ _
  have hMε : 249 / ε ≤ M := le_max_right _ _
  refine ⟨Real.exp (-M), Real.exp_pos _, fun η hη hηη₀ W hW => ?_⟩
  have hL : M ≤ Leta η := by
    unfold Leta
    rw [one_div, Real.log_inv]
    have := Real.log_le_log hη hηη₀
    rw [Real.log_exp] at this
    linarith
  have hLpos : 0 < Leta η := by linarith
  have hkey : ∀ k : ℝ, k ≤ 83 → k / Leta η ≤ ε / 3 := by
    intro k hk
    rw [div_le_iff₀ hLpos]
    have h83 : ε / 3 * (249 / ε) = 83 := by field_simp; ring
    have h249 : 249 / ε ≤ Leta η := hMε.trans hL
    calc k ≤ 83 := hk
      _ = ε / 3 * (249 / ε) := h83.symm
      _ ≤ ε / 3 * Leta η := mul_le_mul_of_nonneg_left h249 (by positivity)
  -- `C_T^+(w) ≤ 1 + ε/3` (`lem:CTlimit`)
  have hCTle : CTp W ≤ ENNReal.ofReal (1 + ε / 3) := by
    rcases hW with hW | hW
    · refine (hCT.2.1 W η hW (by linarith)).trans (ENNReal.ofReal_le_ofReal ?_)
      linarith [hkey 42 (by norm_num)]
    · refine (hCT.2.2 W η hW (by linarith)).trans (ENNReal.ofReal_le_ofReal ?_)
      linarith [hkey 83 le_rfl]
  have hCTne : CTp W ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hCTle
  set C := (CTp W).toReal with hCdef
  have hCle : C ≤ 1 + ε / 3 := ENNReal.toReal_le_of_le_ofReal (by positivity) hCTle
  -- `C_T^+(w) ≥ 1` (remark after `prop:sharpLS`)
  have hC1 : 1 ≤ C := CTp_ge_one hSharp hWH W hCTne
  -- the band constant (`eq:MVLS`, `lem:WH`) and the fixed data (`assemblyLimit`)
  obtain ⟨Cband, hCband1, hband⟩ := bandLS_of_MV hMV hWH W
  set Cmax := max Cband C with hCmax
  obtain ⟨P, ε', hPa0, hPA0, hε'0, hε'3, hε'1, hlim⟩ :=
    hLim a0 A0 ha0 hA0 C Cmax hC1 (le_max_right _ _) (ε / 3) (by positivity)
  -- the profile `C̃_ε'` and the profile bound (`prop:TIsharp`)
  obtain ⟨hrange, hbelow, hbandv, habove, hfar⟩ :=
    bandProfile_spec (Cmax := Cmax) hε'0 hC1 (le_max_right _ _)
  have hsmooth : ContDiff ℝ ∞ (bandProfile Cmax C ε') := bandProfile_contDiff _ _ _
  have hprof : P.ProfileBound W (bandProfile Cmax C ε') :=
    hTI P W hCTne ε' hε'0 hε'3 hε'1 Cband hCband1 (hband ε' hε'0 (by linarith))
      (bandProfile Cmax C ε') hsmooth hrange hbelow
      (fun α h1 h2 => by rw [hbandv α h1 h2]; exact le_max_left _ _) habove hfar
  -- the certified value and `lem:pLip`
  have hcert : pC C - ε / 3 ≤ P.certValue (bandProfile Cmax C ε') :=
    hlim _ hsmooth.continuous hrange hbelow hfar
  have hLip := (lemPLip 1 C le_rfl hC1).2
  have hX : pC 1 - 2 * (ε / 3) ≤ P.certValue (bandProfile Cmax C ε') := by linarith
  -- `prop:zero` + `prop:second` at the fixed data
  have hfix := assembly_fixed hZ hRvM hS P W (bandProfile Cmax C ε') hsmooth
    (fun α => (hrange α).1) hprof
  intro ε'' hε''
  obtain ⟨Q₀, hQ₀⟩ := hfix ε'' hε''
  refine ⟨Q₀, fun Q hQ T hT => ?_⟩
  have hT' : T ∈ P.heights Q := by
    unfold PrimeSetup.heights; rw [hPa0, hPA0]; exact hT
  obtain ⟨h1, h2, h3⟩ := hQ₀ Q hQ T hT'
  have hN0 := Nfam_nonneg W Q T
  refine ⟨?_, ?_, ?_⟩
  · exact le_trans (mul_le_mul_of_nonneg_right (by linarith) hN0) h1
  · exact le_trans (mul_le_mul_of_nonneg_right (by linarith) hN0) h2
  · exact le_trans (mul_le_mul_of_nonneg_right (by linarith) hN0) h3

/-- **Glue theorem for `thm:main`** (bundled form; proved, standard axioms only): the (a)
statements, the classical inputs `hC : ClassicalInputs` (large sieve, Montgomery 1969 in its full form
`Montgomery69_Density`, PNT, Stirling, `lem:WH`) and the ported reductions `hR : PortedReductions` (the
paper's own §4 and §5) imply `thmMain_Statement`. A corollary of `thmMain_of_parts`, with the zero side
obtained from `hR.zeroSide` (the headline `thmMain` does not go through it). -/
theorem thmMain_of_components
    (hCT : lemCTlimit_Statement) (hSharp : propSharpLS_Statement)
    (hTI : propTIsharp_Statement) (hB2 : lemB2_Statement) (hMrat : eqBMrat_Statement)
    (hLim : assemblyLimit_Statement) (hC : ClassicalInputs) (hR : PortedReductions) :
    thmMain_Statement :=
  thmMain_of_parts hCT hSharp hTI hB2 hMrat hLim hC.mvLargeSieve hC.stirling hC.masses
    (hR.zeroSide hC.mvLargeSieve hC.montgomery69 hC.stirling hC.masses) hR.secondMoment

/-- **`thm:main` from the full Montgomery 1969 density theorem** (a conditional variant of the
headline). `hC : ClassicalInputsReduced` is `Montgomery69_Density` (all heights
`T' ≥ 2`), which is **not** proved (the project reduces it to a `t`-aspect input) and is **not** needed:
see the unconditional `thmMain`. -/
theorem thmMain_of_montgomery (hC : ClassicalInputsReduced) : thmMain_Statement :=
  let hF : ClassicalInputs := hC.toFull
  thmMain_of_components lemCTlimit (propSharpLS hF.masses) (propTIsharp hF.mvLargeSieve hF.masses)
    (lemB2 hF.pnt) eqBMrat assemblyLimit hF portedReductions

/-- **`thm:main` (Theorem 1.1), headline — unconditional.** For every `ε > 0` there is `η₀ > 0` such
that for `η ≤ η₀` and `w ∈ {w_η, w^sm_η}` the weighted proportions satisfy
`liminf_Q inf_T N^s_0/N, N^*_0/N ≥ p(1) − ε` and `N_d/N ≥ (1+p(1))/2 − ε`, and `p(1) ≥ 0.932282`.

**No hypotheses**; `#print axioms` gives only `propext`, `Classical.choice`, `Quot.sound`. Proved by
`thmMain_of_parts` from
* the (a) theorems `lemCTlimit`, `propSharpLS`, `propTIsharp`, `lemB2`, `eqBMrat`, `assemblyLimit`;
* the classical inputs, all theorems: `Hyp.MV_LargeSieve_proof`, `Hyp.StirlingDigamma_proof`,
  `Hyp.PNT_dlVP_proof`, `lemWH`;
* the zero side `Ported.Zero.propZero_unconditional` (§4: `prop:zero` and the lower half of `lem:RvM`),
  which uses Montgomery 1969 only in the q-aspect range `T' ≤ Q`
  (`Hyp.Montgomery.Montgomery69_Density_upTo_proof 1`), in `lem:bad`;
* the §5 assembly `Ported.secondMoment`.

The full `Montgomery69_Density` (all heights, including `Q = 1`, i.e. `ζ`) is not used. -/
theorem thmMain : thmMain_Statement :=
  thmMain_of_parts lemCTlimit (propSharpLS lemWH) (propTIsharp Hyp.MV_LargeSieve_proof lemWH)
    (lemB2 Hyp.PNT_dlVP_proof) eqBMrat assemblyLimit Hyp.MV_LargeSieve_proof
    Hyp.StirlingDigamma_proof lemWH Ported.Zero.propZero_unconditional Ported.secondMoment

end Families
