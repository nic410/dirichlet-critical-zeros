/-
# Theorem 1.4(a), package S (the second moment at polynomial height): the component `secondMomentH`

`secondMomentH_proof : SecondMomentAssemblyH` (Proposition 9.19 via Lemma 9.10 and
Proposition 9.5, second claim (9.8)), standard axioms only. Wiring for `FamiliesH/Components.lean` (import this file):
```
theorem secondMomentH : SecondMomentAssemblyH := S.secondMomentH_proof
```
Files:
* `S/Basic.lean`: the families second-moment objects with the family parameter `Q` and the
  prime-side parameter `Qs = QT` decoupled (`Mcal2`, `MA2`, `MB2`, `PP2`, `RR2`, `SSC2`, `ratio2`, …);
  the large sieve on `[1, Y(Qs)]` for the family at `Q` (factor `Q² + Y`); cell-height facts, including
  `sieve_loss_small` (`Q² + Y ≤ η Q² T`, from (S1));
* `S/Split.lean`: `eq:split` decoupled; **positivity of `K₂`** (`K2_self_nonneg`) and the
  Cauchy–Schwarz bound for the `r`-part of the mixed term (`MA2_abs_le`);
* `S/Mumu.lean`: `M_{μμ}` (Lemma 9.10(a));
* `S/SS.lean`: the same-sign term (Lemma 9.10(c)) and the `β`-part of `M_{μΛ}`;
* `S/Ratio.lean`: the ratio terms under the profile bound;
* `S/McalBound.lean`: the bound for `𝓜`;
* `S/FC2.lean`: the finite-centre replacement `eq:fc2H` (explicit formula at `Q' = QT`);
* `S/Assembly.lean`: `propSecondH_of_parts`, `secondMomentH_proof`.
-/
import FamiliesH.S.Assembly
