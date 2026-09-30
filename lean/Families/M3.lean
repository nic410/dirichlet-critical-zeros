/-
`lem:M3`(iii),(iv) (localisation), `lemma-B-majorant.tex` §5.
(iii) `∫ g(u)‖x^s(u)‖² c(u) du ≤ ∑_n |y_n|² 𝒦(n,n) sup{c(u) : |u − log n| < 2δ}`;
(iv)  `∫ g(u)‖x^t(u)‖² du ≤ 8bL‖y‖²/δ`.
Ingredients: `𝒦(n,n) = ∫ g |\hat{1_J}(· − log n)|²` (`Families.M1`), `0 ≤ g ≤ g(0) = bL`
(AM–GM and translation invariance), `|\hat{1_J}(ξ)| ≤ 2/|ξ|`, `∫_{|ξ|>δ} 4ξ⁻² dξ = 8/δ`.
-/
import Families.M1
open scoped BigOperators ComplexConjugate
open MeasureTheory
noncomputable section
namespace Families
namespace PrimeSetup
variable (P : PrimeSetup)

lemma g_nonneg (Q u : ℝ) : 0 ≤ P.g Q u :=
  integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

lemma FR_bounded {Q : ℝ} (hQ : 1 < Q) : ∃ C, ∀ x, ‖P.FR Q x‖ ≤ C :=
  (P.FR_continuous Q).bounded_above_of_compact_support (P.FR_hasCompactSupport hQ)

/-- `g ≤ g(0) = ∫ ψ_L⁴ = L · b`. -/
lemma g_le {Q : ℝ} (hQ : 1 < Q) (u : ℝ) : P.g Q u ≤ P.bInt * P.L Q := by
  obtain ⟨C, hC⟩ := P.FR_bounded hQ
  have hFi := P.FR_integrable hQ
  have hmeas : ∀ c : ℝ, AEStronglyMeasurable (fun s => P.FR Q (c - s)) volume :=
    fun c => ((P.FR_continuous Q).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hsq : Integrable (fun s => P.FR Q s * P.FR Q s) :=
    hFi.mul_bdd (P.FR_continuous Q).aestronglyMeasurable (Filter.Eventually.of_forall hC)
  have hsq' : Integrable (fun s => P.FR Q (u - s) * P.FR Q (u - s)) := by
    have := hsq.comp_sub_left u
    exact this
  have hprod : Integrable (fun s => P.FR Q s * P.FR Q (u - s)) :=
    hFi.mul_bdd (hmeas u) (Filter.Eventually.of_forall fun s => hC _)
  have h1 : P.g Q u = ∫ s, P.FR Q s * P.FR Q (u - s) := rfl
  have h2 : (∫ s, P.FR Q s * P.FR Q (u - s))
      ≤ ∫ s, (P.FR Q s * P.FR Q s + P.FR Q (u - s) * P.FR Q (u - s)) / 2 := by
    refine integral_mono hprod ((hsq.add hsq').div_const 2) fun s => ?_
    have := sq_nonneg (P.FR Q s - P.FR Q (u - s))
    simp only; nlinarith
  have h3 : (∫ s, (P.FR Q s * P.FR Q s + P.FR Q (u - s) * P.FR Q (u - s)) / 2)
      = ∫ s, P.FR Q s * P.FR Q s := by
    rw [integral_div, integral_add hsq hsq',
      integral_sub_left_eq_self (fun s => P.FR Q s * P.FR Q s)]
    ring
  have h4 : (∫ s, P.FR Q s * P.FR Q s) = P.bInt * P.L Q := by
    have hL := P.L_pos hQ
    have := Measure.integral_comp_div (fun t => P.vfun t ^ 2) (P.L Q)
    simp only [smul_eq_mul, abs_of_pos hL] at this
    rw [bInt, mul_comm, ← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [FR, vfun, ψL]; ring
  rw [h1]; linarith

lemma hatJ_sq_le (T ξ : ℝ) (hξ : ξ ≠ 0) : ‖P.hatJ T ξ‖ ^ 2 ≤ 4 / ξ ^ 2 := by
  have hbound : ‖P.hatJ T ξ‖ ≤ 2 / |ξ| := by
    unfold hatJ J
    rcases le_or_gt ((1 + P.θ) * T) ((2 - P.θ) * T) with hab | hab
    · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
      have hc : Complex.I * (ξ : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hξ)
      have heq : (fun t : ℝ => Complex.exp (Complex.I * t * ξ))
          = fun t : ℝ => Complex.exp ((Complex.I * ξ) * t) := by
        funext t; ring_nf
      rw [heq, integral_exp_mul_complex hc, norm_div]
      have hnum : ‖Complex.exp (Complex.I * ξ * ((2 - P.θ) * T : ℝ))
          - Complex.exp (Complex.I * ξ * ((1 + P.θ) * T : ℝ))‖ ≤ 2 := by
        refine (norm_sub_le _ _).trans ?_
        rw [Complex.norm_exp, Complex.norm_exp]; simp; norm_num
      have hden : ‖Complex.I * (ξ : ℂ)‖ = |ξ| := by simp
      rw [hden]
      exact div_le_div_of_nonneg_right hnum (abs_nonneg _)
    · rw [Set.Icc_eq_empty (not_le.mpr hab), Measure.restrict_empty, integral_zero_measure,
        norm_zero]
      positivity
  have h0 : 0 ≤ ‖P.hatJ T ξ‖ := norm_nonneg _
  calc ‖P.hatJ T ξ‖ ^ 2 ≤ (2 / |ξ|) ^ 2 := pow_le_pow_left₀ h0 hbound 2
    _ = 4 / ξ ^ 2 := by rw [div_pow, sq_abs]; norm_num

/-- The tail kernel `h_δ(ξ) = 4/ξ² · 1[|ξ| > δ]`. -/
def tailK (δ ξ : ℝ) : ℝ := if δ < |ξ| then 4 / ξ ^ 2 else 0

lemma tailK_nonneg (δ ξ : ℝ) : 0 ≤ tailK δ ξ := by
  unfold tailK; split_ifs <;> positivity

lemma tailK_integrable {δ : ℝ} (hδ : 0 < δ) : Integrable (tailK δ) := by
  have hdom : Integrable (fun ξ : ℝ => (8 / δ ^ 2) * (1 + (ξ / δ) ^ 2)⁻¹) := by
    have := (integrable_inv_one_add_sq).comp_div (ne_of_gt hδ)
    exact this.const_mul _
  refine hdom.mono' ?_ (Filter.Eventually.of_forall fun ξ => ?_)
  · have hm : Measurable (tailK δ) := by
      unfold tailK
      exact Measurable.ite (measurableSet_lt measurable_const measurable_abs)
        (measurable_const.div (measurable_id.pow_const 2)) measurable_const
    exact hm.aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (tailK_nonneg δ ξ)]
    unfold tailK
    split_ifs with h
    · have hξ : δ ^ 2 < ξ ^ 2 := by
        have := sq_lt_sq' (by linarith [abs_nonneg ξ, neg_abs_le ξ]) h
        rwa [sq_abs] at this
      have hξ0 : 0 < ξ ^ 2 := by nlinarith
      rw [div_pow, show (8 / δ ^ 2) * (1 + ξ ^ 2 / δ ^ 2)⁻¹ = 8 / (δ ^ 2 + ξ ^ 2) by
        field_simp]
      rw [div_le_div_iff₀ hξ0 (by positivity)]
      nlinarith
    · positivity

lemma tailK_integral {δ : ℝ} (hδ : 0 < δ) : ∫ ξ, tailK δ ξ = 8 / δ := by
  set φ : ℝ → ℝ := fun t => if δ < t then 4 / t ^ 2 else 0 with hφ
  have h1 : (fun ξ => tailK δ ξ) = fun ξ => φ |ξ| := by
    funext ξ; simp only [tailK, hφ, sq_abs]
  rw [h1, integral_comp_abs]
  have h2 : ∫ x in Set.Ioi (0 : ℝ), φ x = ∫ x in Set.Ioi δ, 4 * x ^ (-2 : ℝ) := by
    have : ∫ x in Set.Ioi (0 : ℝ), φ x = ∫ x in Set.Ioi (0 : ℝ),
        (Set.Ioi δ).indicator (fun x => 4 * x ^ (-2 : ℝ)) x := by
      refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      simp only [hφ, Set.indicator, Set.mem_Ioi]
      split_ifs with h
      · have hx0 : 0 < x := lt_trans hδ h
        rw [Real.rpow_neg hx0.le, Real.rpow_two]; ring
      · rfl
    rw [this, setIntegral_indicator measurableSet_Ioi,
      Set.inter_eq_right.mpr (Set.Ioi_subset_Ioi hδ.le)]
  rw [h2, integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hδ]
  rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
  field_simp; ring


lemma sum_rangeZ (Q : ℝ) (F : ℕ → ℝ) :
    ∑ n ∈ P.rangeZ Q, F n.toNat = ∑ k ∈ P.range Q, F k := by
  have hY := P.Y_nonneg Q
  have hmem : ∀ k : ℕ, k ∈ P.range Q ↔ (k : ℤ) ∈ P.rangeZ Q := by
    intro k
    simp only [PrimeSetup.range, PrimeSetup.rangeZ, Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by exact_mod_cast h1, ?_⟩
      rw [Int.le_floor]; push_cast
      exact (Nat.le_floor_iff hY).mp h2
    · rintro ⟨h1, h2⟩
      refine ⟨by exact_mod_cast h1, ?_⟩
      rw [Nat.le_floor_iff hY]
      rw [Int.le_floor] at h2; push_cast at h2; exact h2
  symm
  refine Finset.sum_bij' (fun (k : ℕ) _ => (k : ℤ)) (fun (n : ℤ) _ => n.toNat) ?_ ?_ ?_ ?_ ?_
  · intro k hk; exact (hmem k).mp hk
  · intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    rw [hmem, Int.toNat_of_nonneg (by omega)]; exact hn
  · intro k _; simp
  · intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    exact Int.toNat_of_nonneg (by omega)
  · intro k _; simp

lemma xVec_of_pos (Q T : ℝ) (y : ℕ → ℝ) (u : ℝ) {n : ℤ} (hn : 1 ≤ n) :
    P.xVec Q T y u n = (y n.toNat : ℂ) * P.hatJ T (u - Real.log n.toNat) := by
  simp [PrimeSetup.xVec, hn]

lemma gHat_integrable {Q : ℝ} (hQ : 1 < Q) (T ℓ : ℝ) :
    Integrable (fun u => P.g Q u * ‖P.hatJ T (u - ℓ)‖ ^ 2) := by
  refine (P.g_integrable hQ).mul_bdd (c := volume.real (P.J T) ^ 2) ?_
    (Filter.Eventually.of_forall fun u => ?_)
  · exact (((P.hatJ_continuous T).comp (continuous_id.sub continuous_const)).norm.pow 2
      ).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (P.hatJ_norm_le T _) 2

lemma 𝒦_diag_re {Q : ℝ} (hQ : 1 < Q) (T : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (P.𝒦 Q T n n).re = ∫ u, P.g Q u * ‖P.hatJ T (u - Real.log n)‖ ^ 2 := by
  rw [P.kernel_factorisation hQ n n hn hn]
  have : (fun u => (P.g Q u : ℂ) * P.hatJ T (u - Real.log n) * conj (P.hatJ T (u - Real.log n)))
      = fun u => ((P.g Q u * ‖P.hatJ T (u - Real.log n)‖ ^ 2 : ℝ) : ℂ) := by
    funext u
    rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  rw [this, integral_complex_ofReal, Complex.ofReal_re]

end PrimeSetup

open PrimeSetup in
/-- **`lem:M3`(iii),(iv)** (proved). -/
theorem lemM3_iii_iv_proved : lemM3_iii_iv_Statement := by
  intro P ρ _ hρr hρ1 hρ0 Q T δ hQ _ hδ _ y
  simp only []
  set I := P.rangeZ Q with hI
  constructor
  · -- (iii)
    intro c Cmax hc
    set s : ℕ → ℝ := fun k => sSup (c '' {u | |u - Real.log k| < 2 * δ}) with hsdef
    have hs_bdd : ∀ k : ℕ, BddAbove (c '' {u | |u - Real.log k| < 2 * δ}) := by
      intro k; refine ⟨Cmax, ?_⟩; rintro _ ⟨u, _, rfl⟩; exact (hc u).2
    have hs_mem : ∀ k : ℕ, ∀ u, |u - Real.log k| < 2 * δ → c u ≤ s k :=
      fun k u hu => le_csSup (hs_bdd k) ⟨u, hu, rfl⟩
    have hs_nonneg : ∀ k : ℕ, 0 ≤ s k := by
      intro k
      refine le_trans (hc (Real.log k)).1 (hs_mem k _ ?_)
      simp; positivity
    have hpt : ∀ u, P.g Q u * normSq I (fun n => P.xVec Q T y u n *
          ρ ((Real.log n.toNat - u) / δ)) * c u
        ≤ ∑ n ∈ I, y n.toNat ^ 2 * s n.toNat *
            (P.g Q u * ‖P.hatJ T (u - Real.log n.toNat)‖ ^ 2) := by
      intro u
      unfold normSq
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_le_sum fun n hn => ?_
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      beta_reduce
      rw [P.xVec_of_pos Q T y u hn1]
      set ℓ := Real.log n.toNat
      set r := ρ ((ℓ - u) / δ)
      have hr0 := (hρr ((ℓ - u) / δ)).1
      have hr1 := (hρr ((ℓ - u) / δ)).2
      have hnorm : ‖(y n.toNat : ℂ) * P.hatJ T (u - ℓ) * (r : ℂ)‖ ^ 2
          = y n.toNat ^ 2 * ‖P.hatJ T (u - ℓ)‖ ^ 2 * r ^ 2 := by
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
      rw [hnorm]
      have hg0 := P.g_nonneg Q u
      have hc0 := (hc u).1
      by_cases hr : r = 0
      · rw [hr]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
          zero_mul]
        exact mul_nonneg (mul_nonneg (sq_nonneg _) (hs_nonneg _))
          (mul_nonneg hg0 (sq_nonneg _))
      · have hlt : |u - ℓ| < 2 * δ := by
          by_contra hcon
          replace hcon := not_lt.mp hcon
          apply hr
          apply hρ0
          rw [abs_div, abs_of_pos hδ, le_div_iff₀ hδ, abs_sub_comm]
          linarith
        have hcs := hs_mem n.toNat u hlt
        have hr2 : r ^ 2 ≤ 1 := by nlinarith
        have hA : 0 ≤ y n.toNat ^ 2 * ‖P.hatJ T (u - ℓ)‖ ^ 2 * P.g Q u :=
          mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hg0
        calc P.g Q u * (y n.toNat ^ 2 * ‖P.hatJ T (u - ℓ)‖ ^ 2 * r ^ 2) * c u
            = (y n.toNat ^ 2 * ‖P.hatJ T (u - ℓ)‖ ^ 2 * P.g Q u) * (r ^ 2 * c u) := by ring
          _ ≤ (y n.toNat ^ 2 * ‖P.hatJ T (u - ℓ)‖ ^ 2 * P.g Q u) * (1 * s n.toNat) := by
            apply mul_le_mul_of_nonneg_left _ hA
            exact mul_le_mul hr2 hcs hc0 zero_le_one
          _ = _ := by ring
    have hint : Integrable (fun u => ∑ n ∈ I, y n.toNat ^ 2 * s n.toNat *
        (P.g Q u * ‖P.hatJ T (u - Real.log n.toNat)‖ ^ 2)) :=
      integrable_finsetSum _ fun n _ => (P.gHat_integrable hQ T _).const_mul _
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => ?_) hint
      (Filter.Eventually.of_forall hpt)).trans (le_of_eq ?_)
    · exact mul_nonneg (mul_nonneg (P.g_nonneg Q u)
        (Finset.sum_nonneg fun _ _ => sq_nonneg _)) (hc u).1
    · rw [integral_finsetSum _ fun n _ => (P.gHat_integrable hQ T _).const_mul _]
      simp_rw [integral_const_mul]
      rw [P.sum_rangeZ Q (fun k => y k ^ 2 * s k *
        ∫ u, P.g Q u * ‖P.hatJ T (u - Real.log k)‖ ^ 2)]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      rw [P.𝒦_diag_re hQ T k hk1]; ring
  · -- (iv)
    have hbL : 0 ≤ P.bInt * P.L Q := le_trans (P.g_nonneg Q 0) (P.g_le hQ 0)
    have hpt : ∀ u, P.g Q u * normSq I (fun n => P.xVec Q T y u n -
          P.xVec Q T y u n * ρ ((Real.log n.toNat - u) / δ))
        ≤ ∑ n ∈ I, y n.toNat ^ 2 * (P.bInt * P.L Q) * tailK δ (u - Real.log n.toNat) := by
      intro u
      unfold normSq
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun n hn => ?_
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      beta_reduce
      rw [P.xVec_of_pos Q T y u hn1]
      set ℓ := Real.log n.toNat
      set r := ρ ((ℓ - u) / δ)
      have hr0 := (hρr ((ℓ - u) / δ)).1
      have hr1 := (hρr ((ℓ - u) / δ)).2
      have hnorm : ‖(y n.toNat : ℂ) * P.hatJ T (u - ℓ) - (y n.toNat : ℂ) * P.hatJ T (u - ℓ) * (r : ℂ)‖ ^ 2
          = y n.toNat ^ 2 * ‖P.hatJ T (u - ℓ)‖ ^ 2 * (1 - r) ^ 2 := by
        rw [show (y n.toNat : ℂ) * P.hatJ T (u - ℓ) - (y n.toNat : ℂ) * P.hatJ T (u - ℓ) * (r : ℂ)
            = (y n.toNat : ℂ) * P.hatJ T (u - ℓ) * ((1 - r : ℝ) : ℂ) by push_cast; ring]
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
      rw [hnorm]
      have hg0 := P.g_nonneg Q u
      have hgle := P.g_le hQ u
      by_cases hclose : |u - ℓ| ≤ δ
      · have : r = 1 := by
          apply hρ1
          rw [abs_div, abs_of_pos hδ, div_le_one hδ, abs_sub_comm]; exact hclose
        rw [this]; simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow, mul_zero]
        exact mul_nonneg (mul_nonneg (sq_nonneg _) hbL) (tailK_nonneg _ _)
      · replace hclose := not_le.mp hclose
        have hξ : u - ℓ ≠ 0 := by
          intro h0; rw [h0, abs_zero] at hclose; linarith
        have hJ := P.hatJ_sq_le T (u - ℓ) hξ
        have htail : tailK δ (u - ℓ) = 4 / (u - ℓ) ^ 2 := by
          unfold tailK; rw [if_pos hclose]
        have h1r : (1 - r) ^ 2 ≤ 1 := by nlinarith
        rw [htail]
        have hJ0 : 0 ≤ ‖P.hatJ T (u - ℓ)‖ ^ 2 := sq_nonneg _
        have h4 : 0 ≤ 4 / (u - ℓ) ^ 2 := by positivity
        calc P.g Q u * (y n.toNat ^ 2 * ‖P.hatJ T (u - ℓ)‖ ^ 2 * (1 - r) ^ 2)
            = y n.toNat ^ 2 * (P.g Q u * (‖P.hatJ T (u - ℓ)‖ ^ 2 * (1 - r) ^ 2)) := by ring
          _ ≤ y n.toNat ^ 2 * ((P.bInt * P.L Q) * (4 / (u - ℓ) ^ 2 * 1)) := by
            apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
            apply mul_le_mul hgle _ (mul_nonneg hJ0 (sq_nonneg _)) hbL
            exact mul_le_mul hJ h1r (sq_nonneg _) h4
          _ = _ := by ring
    have hint : Integrable (fun u => ∑ n ∈ I, y n.toNat ^ 2 * (P.bInt * P.L Q) *
        tailK δ (u - Real.log n.toNat)) :=
      integrable_finsetSum _ fun n _ => ((tailK_integrable hδ).comp_sub_right _).const_mul _
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => ?_) hint
      (Filter.Eventually.of_forall hpt)).trans (le_of_eq ?_)
    · exact mul_nonneg (P.g_nonneg Q u) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    · rw [integral_finsetSum _ fun n _ =>
        ((tailK_integrable hδ).comp_sub_right _).const_mul _]
      simp_rw [integral_const_mul, integral_sub_right_eq_self (tailK δ), tailK_integral hδ]
      rw [P.sum_rangeZ Q (fun k => y k ^ 2 * (P.bInt * P.L Q) * (8 / δ)), Finset.mul_sum,
        Finset.sum_div]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring

end Families

namespace Families

/-- Alias under the name used in `STATEMENTS.md`. -/
theorem lemM3_iii_iv : lemM3_iii_iv_Statement := lemM3_iii_iv_proved

end Families
