/-
# Theorem 1.4(a), package V: definitions for the certificate checks of `prop:certH`

For `β = p/q` put `D = 400q` (cell width `h = β/400 = p/D`). With `G(x) = |x|³/6` (`|x| ≤ 1`),
`G(x) = 1/6 + (|x|−1)/2 + C(|x|−1)²/2` (`|x| > 1`) and `C = c_n/c_d`:
`GsB k = 6·D³·c_d·G(|k|p/D)`, `ksB k = GsB(k+1) − 2GsB(k) + GsB(k−1)`, and `certCheckB` is the certificate
inequality with denominators cleared. Imports only the (import-free) `Families.Certificate.Data`.
-/
import Families.Certificate.Data

namespace Families.Hybrid.V.CertDataH

open Families.CertData

/-- `6·D³·c_d·G(|k|p/D)` for `C = c_n/c_d`. -/
def GsB (cn cd p D : Int) (k : Int) : Int :=
  if (k.natAbs : Int) * p ≤ D then cd * ((k.natAbs : Int) * p) ^ 3
  else cd * D ^ 3 + 3 * cd * D ^ 2 * ((k.natAbs : Int) * p - D)
    + 3 * cn * D * ((k.natAbs : Int) * p - D) ^ 2

/-- Scaled cell-pair integrals `ksB k = GsB(k+1) − 2 GsB(k) + GsB(k−1)`. -/
def ksB (cn cd p D : Int) (k : Int) : Int :=
  GsB cn cd p D (k + 1) - 2 * GsB cn cd p D k + GsB cn cd p D (k - 1)

/-- `[ksB(−399), …, ksB(399)]`. -/
def kerListB (cn cd p D : Int) : List Int :=
  (List.range 799).map (fun k : Nat => ksB cn cd p D ((k : Int) - 399))

/-- The certificate inequality with denominators cleared (`h = p/D`):
`10⁶ (h∑m² + ∑ m_i m_j κ_{i−j}) ≤ B h² (∑m)²` with `κ = ksB/(6D³c_d)`, multiplied by `6D³c_d·D²/…`. -/
def certCheckB (p D cd B : Int) (l L : List Int) : Bool :=
  decide (1000000 * (6 * p * D ^ 2 * cd * dot l l + quadL l L) ≤ 6 * B * p ^ 2 * D * cd * l.sum ^ 2)

end Families.Hybrid.V.CertDataH
