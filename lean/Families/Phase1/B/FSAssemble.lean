/-
# Assembling `lem:fS`

* `lemfS_of_iii`: `lemfS_Statement` from parts (i), (ii), (iv) (proved) and the three clauses of (iii) as
  hypotheses (this machine-checks that the proved parts have exactly the shapes of the conjuncts).
* `lemfS_of_Bconst`: `lemfS_Statement` from the single numerical hypothesis `Bconst < 3.73`; everything
  else, including (iii)'s `|E_S| ≤ 2B e^{−s/2}` and `0 ≤ c_∅ − c_S < 0.168`, is proved.
-/
import Families.Phase1.B.FS
import Families.Phase1.B.FSii
import Families.Phase1.B.FSiv
import Families.Phase1.B.FSiiia
import Families.Phase1.B.FSiiic

namespace Families.Phase1.B

open Families

theorem lemfS_of_iii
    (h3a : ∀ (S : Finset ℕ) (s : ℝ), 0 ≤ s → |ES S s| ≤ 2 * Bconst * Real.exp (-s / 2))
    (h3b : Bconst < 3.73)
    (h3c : ∀ S : Finset ℕ, 0 ≤ cEmpty - cS S ∧ cEmpty - cS S < 0.168) : lemfS_Statement :=
  ⟨lemfS_i_proof, lemfS_ii_conv, lemfS_ii_euler, h3a, h3b, h3c, lemfS_iv_proof⟩

/-- `lem:fS` from the numerical bound `B < 3.73` alone. -/
theorem lemfS_of_Bconst (h3b : Bconst < 3.73) : lemfS_Statement :=
  lemfS_of_iii lemfS_iii_a h3b lemfS_iii_c

end Families.Phase1.B
