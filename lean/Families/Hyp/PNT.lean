/-
# Discharging `PNT_dlVP` (classical input (b3)) from `zeta23`'s `MediumPNT`

`Families.Hyp.PNT_dlVP_proof : PNT_dlVP`, i.e. `∃ C₀, ∀ x ≥ 2, |θ(x) − x| ≤ C₀ x/(log x)³`.

Inputs:
* `MediumPNT` (`zeta23`, `Zeta23/FromPNTPlus/MediumPNT.lean`, root namespace; ported from
  PrimeNumberTheoremAnd): `∃ c > 0, (ψ − id) =O[atTop] (x ↦ x·exp(−c (log x)^{1/10}))`, where `ψ` is
  Mathlib's `Chebyshev.psi`;
* Mathlib: `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log` (`|ψ − θ| ≤ 2√x log x` for `x ≥ 1`) and
  `Chebyshev.theta_le_log4_mul_x`, `Chebyshev.theta_nonneg` (the compact range);
  `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero` (`u^30 e^{−cu} → 0`) and
  `isLittleO_log_rpow_rpow_atTop` (`(log x)^4 = o(√x)`).

Proof: for large `x`, `x e^{−c L^{1/10}} ≤ x/L³` (`L = log x`) and `2√x L ≤ 2x/L³`; for `2 ≤ x ≤ X`,
`|θ(x) − x| ≤ (log 4 + 1)x ≤ (log 4 + 1)(log X)³ · x/L³`.
-/
import Families.Classical
import Zeta23.FromPNTPlus.MediumPNT

noncomputable section

open Filter Topology Asymptotics

namespace Families.Hyp

/-- `(log x)³ e^{−c (log x)^{1/10}} → 0`. -/
lemma tendsto_log_cube_mul_exp {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => Real.log x ^ 3 * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)))
      atTop (𝓝 0) := by
  have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 30 c hc
  have h2 : Tendsto (fun x : ℝ => Real.log x ^ ((1 : ℝ) / 10)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  refine (h1.comp h2).congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx
  simp only [Function.comp_apply]
  congr 1
  rw [← Real.rpow_mul hL]
  norm_num

/-- Eventually `x e^{−c (log x)^{1/10}} ≤ x/(log x)³`. -/
lemma eventually_exp_le {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)) ≤ x / Real.log x ^ 3 := by
  have h := (tendsto_log_cube_mul_exp hc).eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [h, eventually_gt_atTop (Real.exp 1)] with x hx hxe
  have hx1 : 1 < x := lt_trans (by
    have := Real.add_one_le_exp (1 : ℝ); linarith) hxe
  have hL : 0 < Real.log x := Real.log_pos hx1
  have hx0 : 0 < x := by linarith
  rw [le_div_iff₀ (by positivity)]
  calc x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)) * Real.log x ^ 3
      = x * (Real.log x ^ 3 * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))) := by ring
    _ ≤ x * 1 := mul_le_mul_of_nonneg_left hx hx0.le
    _ = x := mul_one x

/-- Eventually `2√x log x ≤ 2x/(log x)³`. -/
lemma eventually_sqrt_log_le :
    ∀ᶠ x : ℝ in atTop, 2 * Real.sqrt x * Real.log x ≤ 2 * (x / Real.log x ^ 3) := by
  have h := (isLittleO_log_rpow_rpow_atTop (4 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)).bound
    (by norm_num : (0 : ℝ) < 1)
  filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hL : 0 < Real.log x := Real.log_pos hx1
  have hx0 : 0 < x := by linarith
  have h4 : Real.log x ^ (4 : ℝ) = Real.log x ^ 4 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h4, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by positivity),
    abs_of_pos (by positivity), one_mul, ← Real.sqrt_eq_rpow] at hx
  have hs : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hsq : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  rw [mul_div_assoc', le_div_iff₀ (by positivity)]
  calc 2 * Real.sqrt x * Real.log x * Real.log x ^ 3 = 2 * (Real.sqrt x * Real.log x ^ 4) := by ring
    _ ≤ 2 * (Real.sqrt x * Real.sqrt x) := by gcongr
    _ = 2 * x := by rw [hs]

/-- **`PNT_dlVP` (classical input (b3)) is a theorem**, from `zeta23`'s `MediumPNT` and Mathlib's
Chebyshev bounds. -/
theorem PNT_dlVP_proof : Families.PNT_dlVP := by
  obtain ⟨c, hc, hO⟩ := MediumPNT
  obtain ⟨C₁, hC₁, hB⟩ := hO.exists_pos
  have hB' := hB.bound
  -- the large range
  have hev : ∀ᶠ x : ℝ in atTop,
      |Chebyshev.theta x - x| ≤ (C₁ + 2) * x / Real.log x ^ 3 := by
    filter_upwards [hB', eventually_exp_le hc, eventually_sqrt_log_le,
      eventually_ge_atTop (2 : ℝ)] with x h1 h2 h3 hx2
    have hx0 : 0 < x := by linarith
    have hL : 0 < Real.log x := Real.log_pos (by linarith)
    simp only [Pi.sub_apply, id_eq, Real.norm_eq_abs] at h1
    have hpos : 0 < x * Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10)) := by positivity
    rw [abs_of_pos hpos] at h1
    have hpt := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith : (1 : ℝ) ≤ x)
    have htri : |Chebyshev.theta x - x| ≤
        |Chebyshev.psi x - Chebyshev.theta x| + |Chebyshev.psi x - x| := by
      have := abs_sub_le (Chebyshev.theta x) (Chebyshev.psi x) x
      rw [abs_sub_comm (Chebyshev.theta x) (Chebyshev.psi x)] at this
      exact this
    have hq : 0 ≤ x / Real.log x ^ 3 := by positivity
    calc |Chebyshev.theta x - x|
        ≤ 2 * (x / Real.log x ^ 3) + C₁ * (x / Real.log x ^ 3) := by
          have := mul_le_mul_of_nonneg_left h2 hC₁.le
          linarith
      _ = (C₁ + 2) * x / Real.log x ^ 3 := by ring
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hev
  set X := max X₀ 2 with hX
  have hX2 : 2 ≤ X := le_max_right _ _
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  refine ⟨(C₁ + 2) + (Real.log 4 + 1) * Real.log X ^ 3, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hq : 0 ≤ x / Real.log x ^ 3 := by positivity
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hrest : 0 ≤ (Real.log 4 + 1) * Real.log X ^ 3 := by positivity
  rw [add_mul, add_div]
  rcases le_total X₀ x with hxX | hxX
  · have := hX₀ x hxX
    have : 0 ≤ (Real.log 4 + 1) * Real.log X ^ 3 * x / Real.log x ^ 3 := by positivity
    linarith
  · -- the compact range `2 ≤ x ≤ X₀`
    have hxX' : x ≤ X := hxX.trans (le_max_left _ _)
    have hθ0 := Chebyshev.theta_nonneg x
    have hθ := Chebyshev.theta_le_log4_mul_x hx0.le
    have h1 : |Chebyshev.theta x - x| ≤ (Real.log 4 + 1) * x := by
      rw [abs_le]; constructor <;> nlinarith
    have hLL : Real.log x ^ 3 ≤ Real.log X ^ 3 :=
      pow_le_pow_left₀ hL.le (Real.log_le_log hx0 hxX') 3
    have h2 : (Real.log 4 + 1) * x ≤ (Real.log 4 + 1) * Real.log X ^ 3 * x / Real.log x ^ 3 := by
      rw [le_div_iff₀ (by positivity)]
      have : 0 ≤ (Real.log 4 + 1) * x := by positivity
      nlinarith
    have : 0 ≤ (C₁ + 2) * x / Real.log x ^ 3 := by
      have : 0 < C₁ + 2 := by linarith
      positivity
    linarith

end Families.Hyp
