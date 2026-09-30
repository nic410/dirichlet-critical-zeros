/-
`#print axioms` for the Theorem 1.4(a) headline, its 15 components, the glue and statement checks, the package proofs
and the kernel-checked certificates. The expected output is `scripts/PrintAxiomsH.baseline.txt`;
`scripts/audit.sh` checks that every baseline line is reproduced.
Run (after `lake build`):  lake env lean scripts/PrintAxiomsH.lean
-/
import FamiliesH

-- the headline (Theorem 1.4(a), sharp route)
#print axioms Families.Hybrid.thmH
-- the 15 component theorems (`FamiliesH/Components.lean`)
#print axioms Families.Hybrid.propZeroH_unconditional
#print axioms Families.Hybrid.secondMomentH
#print axioms Families.Hybrid.lemB1H
#print axioms Families.Hybrid.eqBMratH
#print axioms Families.Hybrid.lemB2H
#print axioms Families.Hybrid.lemSizesH
#print axioms Families.Hybrid.lemM1H
#print axioms Families.Hybrid.lemM3H_iii
#print axioms Families.Hybrid.lemM3primeH
#print axioms Families.Hybrid.corTailsH
#print axioms Families.Hybrid.propTIsharpH
#print axioms Families.Hybrid.lemMbeta
#print axioms Families.Hybrid.lemPLipH
#print axioms Families.Hybrid.assemblyLimitH
#print axioms Families.Hybrid.certH
-- the glue (`FamiliesH/Glue.lean`)
#print axioms Families.Hybrid.thmH_of_parts
#print axioms Families.Hybrid.thmHcell_of_parts
#print axioms Families.Hybrid.thmH_of_cells
#print axioms Families.Hybrid.assembly_fixedH
#print axioms Families.Hybrid.bandLSH_of_MV
#print axioms Families.Hybrid.betaK_ratio_le
-- the statement checks (`FamiliesH/StatementCheck.lean`)
#print axioms Families.Hybrid.pB_two
#print axioms Families.Hybrid.admissibleB_two_iff
#print axioms Families.Hybrid.kappaT_rpow
#print axioms Families.Hybrid.betaK_zero
#print axioms Families.Hybrid.betaK_one
#print axioms Families.Hybrid.betaK_ten
#print axioms Families.Hybrid.betaK_mem
#print axioms Families.Hybrid.thmMain_of_thmH
-- package V (`FamiliesH/V/`)
#print axioms Families.Hybrid.V.lemMbeta_proof
#print axioms Families.Hybrid.V.lemPLipH_proof
#print axioms Families.Hybrid.V.assemblyLimitH_proof
#print axioms Families.Hybrid.V.certH_proof
-- the kernel-checked certificates at κ = 1, 2, 3, 5, 10 (`FamiliesH/V/CertData.lean`)
#print axioms Families.Hybrid.V.CertDataH.certK1
#print axioms Families.Hybrid.V.CertDataH.certK2
#print axioms Families.Hybrid.V.CertDataH.certK3
#print axioms Families.Hybrid.V.CertDataH.certK5
#print axioms Families.Hybrid.V.CertDataH.certK10
-- package F (`FamiliesH/F/`)
#print axioms Families.Hybrid.F.lemB1H_proof
#print axioms Families.Hybrid.F.eqBMratH_proof
#print axioms Families.Hybrid.F.lemB2H_proof
#print axioms Families.Hybrid.F.lemSizesH_proof
#print axioms Families.Hybrid.F.lemM1H_proof
#print axioms Families.Hybrid.F.lemM3H_iii_proof
#print axioms Families.Hybrid.F.lemM3primeH_proof
#print axioms Families.Hybrid.F.corTailsH_proof
-- package Z (`FamiliesH/Z/`)
#print axioms Families.Hybrid.Z.propZeroH_unconditional_proof
-- package S (`FamiliesH/S/`)
#print axioms Families.Hybrid.S.secondMomentH_proof
-- package TS (`FamiliesH/TS/`)
#print axioms Families.Hybrid.TS.propTIsharpH54_proof
#print axioms Families.Hybrid.TS.bandLSH54_of_MV
