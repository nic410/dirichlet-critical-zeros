/-
# Theorem 1.4(a): the component theorems (all proved)

The 15 component theorems, each proved in one of five packages and wired below:
* V (variational problem at support `β`, certificates; `FamiliesH/V/`): `lemMbeta`, `lemPLipH`,
  `assemblyLimitH`, `certH`;
* F (flattening, localisation, tails, sizes; `FamiliesH/F/`): `lemB1H`, `eqBMratH`, `lemB2H`, `lemSizesH`,
  `lemM1H`, `lemM3H_iii`, `lemM3primeH`, `corTailsH`;
* Z (zero side; `FamiliesH/Z/`): `propZeroH_unconditional`;
* S (second moment; `FamiliesH/S/`): `secondMomentH`;
* TS (the band device `prop:TIsharpH`; `FamiliesH/TS/`): `propTIsharpH`.
None uses `sorry`; `scripts/audit.sh` checks this.
-/
import FamiliesH.Statements
import FamiliesH.V.All
import FamiliesH.F.All
import FamiliesH.Z.All
import FamiliesH.S.All
import FamiliesH.TS.All

noncomputable section

namespace Families.Hybrid

open Families

/-- Lemma 9.2 (lower half) and Proposition 9.9 (package Z; `FamiliesH/Z/`, unconditional). -/
theorem propZeroH_unconditional : propZeroH_Statement ∧ lemRvMH_lower_Statement :=
  Z.propZeroH_unconditional_proof

/-- Proposition 9.19 via Lemma 9.10 (package S; `FamiliesH/S/`). -/
theorem secondMomentH : SecondMomentAssemblyH := S.secondMomentH_proof

/-- Lemma 9.11, first claim (package F). -/
theorem lemB1H : lemB1H_Statement := F.lemB1H_proof

/-- Lemma 9.11, second claim (package F). -/
theorem eqBMratH : eqBMratH_Statement := F.eqBMratH_proof

/-- Lemma 9.12 (package F). -/
theorem lemB2H : lemB2H_Statement := F.lemB2H_proof

/-- Lemma 9.1 (package F). -/
theorem lemSizesH : lemSizesH_Statement := F.lemSizesH_proof

/-- (9.11): Lemma 5.9 for `L = λℓ_*` (package F; mechanical port of `Families.M1`). -/
theorem lemM1H : lemM1H_Statement := F.lemM1H_proof

/-- §9.3: Lemma 5.11(iii) for `L = λℓ_*` (package F; mechanical port of `Families.M3`). -/
theorem lemM3H_iii : lemM3H_iii_Statement := F.lemM3H_iii_proof

/-- Lemma 9.13, tails by dyadic shells (package F; new). -/
theorem lemM3primeH : lemM3primeH_Statement := F.lemM3primeH_proof

/-- Corollary 9.14, tails at the scale `T^{−1+ε₅}` (package F; new). -/
theorem corTailsH : corTailsH_Statement := F.corTailsH_proof

/-- Proposition 9.18 (package TS; `FamiliesH/TS/`). -/
theorem propTIsharpH : propTIsharpH_Statement := TS.propTIsharpH54_proof

/-- Lemma 9.21 (package V; new). -/
theorem lemMbeta : lemMbeta_Statement := V.lemMbeta_proof

/-- Lemma 9.22 (package V; port of `Families.pC_antitone_lip`). -/
theorem lemPLipH : lemPLipH_Statement := V.lemPLipH_proof

/-- §9.4, steps (a)–(e) of the proof of Theorem 9.20, with Lemma 9.23 (package V; port of `Families.Phase4.A.assemblyLimit_proof`). -/
theorem assemblyLimitH : assemblyLimitH_Statement := V.assemblyLimitH_proof

/-- Proposition 9.24, the table after Theorem 1.4 (package V; kernel-checked certificates, port of
`Families.Certificate.Numerics`). -/
theorem certH : certH_Statement := V.certH_proof

end Families.Hybrid
