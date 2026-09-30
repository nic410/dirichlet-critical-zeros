/-
# Package TS: Proposition 9.18 (`prop:TIsharpH`), proved

`TS.propTIsharpH54_proof : TS.propTIsharpH54_Statement` is `propTIsharpH_Statement` with the band
hypothesis at the interval length `Q^{5/4}` of Lemma 9.1 (S2) (`TS.BandLSH54`), and
`TS.bandLSH54_of_MV` supplies that hypothesis from the large sieve, exactly as the glue's
`bandLSH_of_MV` does for `BandLSH`. Since `BandLSH` bounds intervals of `Q^{5/4}` integers,
`propTIsharpH_Statement` is `propTIsharpH54_Statement` by definition (`STATEMENTS-H.md` §5).
-/
import FamiliesH.TS.Main

namespace Families.Hybrid

namespace TS

/-- The two package-TS results. -/
theorem packageTS :
    propTIsharpH54_Statement ∧
      ∀ W : Families.Weight, ∃ Cband : ℝ, 1 ≤ Cband ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
        BandLSH54 W ε Cband :=
  ⟨propTIsharpH54_proof,
    bandLSH54_of_MV Families.Hyp.MV_LargeSieve_proof Families.lemWH⟩

end TS

end Families.Hybrid
