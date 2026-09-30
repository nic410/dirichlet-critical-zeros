/-
# Theorem 1.4(a), package V (variational problem at support `β`): all proofs, no `sorry`

Wired into `FamiliesH/Components.lean`, which imports this file and states:
```
theorem lemMbeta : lemMbeta_Statement := V.lemMbeta_proof
theorem lemPLipH : lemPLipH_Statement := V.lemPLipH_proof
theorem assemblyLimitH : assemblyLimitH_Statement := V.assemblyLimitH_proof
theorem certH : certH_Statement := V.certH_proof
```
Each proof depends only on `propext`, `Classical.choice`, `Quot.sound`.
-/
import FamiliesH.V.Basic
import FamiliesH.V.PLip
import FamiliesH.V.Mbeta
import FamiliesH.V.Assembly
import FamiliesH.V.CertDefs
import FamiliesH.V.CertData
import FamiliesH.V.CertGen
import FamiliesH.V.Cert
