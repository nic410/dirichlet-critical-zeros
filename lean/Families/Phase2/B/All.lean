/-
All modules of `Families/Phase2/B` (wired in `Families/Wired/Phase2.lean`).

* **`Families.Phase2.B.lemCTlimit_proof : lemCTlimit_Statement`** (`CTlimit.lean`), from
  - `CTNumerics.lean`: `gamma_le` (`γ ≤ 0.5851`), `cEmpty_le` (`c_∅ ≤ 1.4608`), `cEmpty_pos`,
    `sigma1m_le` (`σ₁⁻ ≤ 0.2809`), the general Abel/Chebyshev tail `abel_theta`;
  - `RSBound.lean`: `sum_Icc_fS_le`, `lintegral_h_eq` (`∫ h = I_w`), the layer-cake bound
    `sum_mul_h_le`, `RS_le_of_quasiconcave`, `lemCTlimit_one` (part (1));
  - `RmBound.lean`: `Rm_le` (the `R^m` bound);
  - `CTlimit.lean`: `CTp_congr` (`C_T^+` depends only on `W.w`), `lemCTlimit_sharp` (part (2)),
    `lemCTlimit_smooth` (part (3)).
* **`Families.Phase2.B.lemWH_proof : lemWH_Statement`** (`WH.lean`, `c₀ = 8`): `mass_general` (divisor
  outside + `eqA:APTV`), `Wm_bound`, `H_bound`, `phiStar_eq_mul` (`φ* = φψ`),
  `hasSum_moebius_div_sq` (`∑ μ(d)/d² = 6/π²`), `eVariationOn_mul_le` (product rule for the variation).
-/
import Families.Phase2.B.CTNumerics
import Families.Phase2.B.RSBound
import Families.Phase2.B.RmBound
import Families.Phase2.B.CTlimit
import Families.Phase2.B.WH
