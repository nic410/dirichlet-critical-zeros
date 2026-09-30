/-
# Theorem 1.4(a), package F (flattening, localisation, tails, sizes): all proofs, no `sorry`

Wiring for `FamiliesH/Components.lean` (import this file):
```
theorem lemB1H : lemB1H_Statement := F.lemB1H_proof
theorem eqBMratH : eqBMratH_Statement := F.eqBMratH_proof
theorem lemB2H : lemB2H_Statement := F.lemB2H_proof
theorem lemSizesH : lemSizesH_Statement := F.lemSizesH_proof
theorem lemM1H : lemM1H_Statement := F.lemM1H_proof
theorem lemM3H_iii : lemM3H_iii_Statement := F.lemM3H_iii_proof
theorem lemM3primeH : lemM3primeH_Statement := F.lemM3primeH_proof
theorem corTailsH : corTailsH_Statement := F.corTailsH_proof
```
Each proof depends only on `propext`, `Classical.choice`, `Quot.sound`.

Files: `Bridge` (`HSetup.toPS`: the hybrid objects are the families objects at `Q' = QT`), `Sizes`
(`lem:sizes`), `M1` (`lem:M1H`), `M3` (`lem:M3H(iii)`), `M3prime` (`lem:M3′`, dyadic shells + MV),
`Tails` (`cor:tails`), `B1` (`lem:B1H`), `Mrat` (`eqB:MratH`), `B2` (`lem:B2H`).
-/
import FamiliesH.F.Bridge
import FamiliesH.F.Sizes
import FamiliesH.F.M1
import FamiliesH.F.M3
import FamiliesH.F.M3prime
import FamiliesH.F.Tails
import FamiliesH.F.B1
import FamiliesH.F.Mrat
import FamiliesH.F.B2

namespace Families.Hybrid.F

/-- The eight package-F roots, bundled. -/
theorem packageF :
    lemB1H_Statement ∧ eqBMratH_Statement ∧ lemB2H_Statement ∧ lemSizesH_Statement ∧
      lemM1H_Statement ∧ lemM3H_iii_Statement ∧ lemM3primeH_Statement ∧ corTailsH_Statement :=
  ⟨lemB1H_proof, eqBMratH_proof, lemB2H_proof, lemSizesH_proof, lemM1H_proof, lemM3H_iii_proof,
    lemM3primeH_proof, corTailsH_proof⟩

end Families.Hybrid.F
