/-
# Montgomery 1969 density: character-sum toolkit

* `norm_sum_Ico_mul_antitone_le` — Abel summation with nonincreasing nonnegative weights.
* `pv_Ico` — Pólya–Vinogradov for primitive characters (via `Families.gauss_identity`,
  `Families.norm_sq_gaussSum`).
* `norm_LFunction_sub_partial_le` — the tail `L(s,χ) − ∑_{m≤N} χ(m) m^{-s}` for `Re s > 0`
  (via `zeta23`'s `LFunction_eq_mul_integral` and Mathlib's Abel summation).
* `norm_LFunction_sub_one_le_of_four_le`, `sum_Icc_two_rpow_le` — `Re s ≥ 4` bounds.
-/
import Families.Toeplitz
import Zeta23.ThmE.LGrowth

noncomputable section

open scoped BigOperators
open Finset

namespace Families.Hyp.Montgomery

/-- Abel summation with nonincreasing nonnegative weights. -/
theorem norm_sum_Ico_mul_antitone_le (f : ℕ → ℂ) (w : ℕ → ℝ) (a b : ℕ) (B : ℝ)
    (hw : ∀ m n, a ≤ m → m ≤ n → w n ≤ w m) (hw0 : ∀ n, 0 ≤ w n)
    (hB : ∀ c, a ≤ c → ‖∑ n ∈ Finset.Ico a c, f n‖ ≤ B) :
    ‖∑ n ∈ Finset.Ico a b, f n * (w n : ℂ)‖ ≤ B * w a := by
  have hB0 : 0 ≤ B := by
    have h := hB a le_rfl
    simpa using h
  rcases lt_or_ge b a with hba | hab
  · rw [Finset.Ico_eq_empty_of_le hba.le, Finset.sum_empty, norm_zero]
    exact mul_nonneg hB0 (hw0 a)
  have key : ∀ c, a ≤ c → ‖∑ n ∈ Finset.Ico a c, f n * (w n : ℂ)
      - (∑ n ∈ Finset.Ico a c, f n) * (w c : ℂ)‖ ≤ B * (w a - w c) := by
    intro c hc
    induction c, hc using Nat.le_induction with
    | base => simp
    | succ c hac ih =>
      have hS := hB (c + 1) (by omega)
      rw [Finset.sum_Ico_succ_top hac] at hS
      rw [Finset.sum_Ico_succ_top hac, Finset.sum_Ico_succ_top hac]
      have hwc : 0 ≤ w c - w (c + 1) := sub_nonneg.2 (hw c (c + 1) hac (by omega))
      have e : (∑ n ∈ Finset.Ico a c, f n * (w n : ℂ) + f c * (w c : ℂ))
          - (∑ n ∈ Finset.Ico a c, f n + f c) * (w (c + 1) : ℂ)
          = (∑ n ∈ Finset.Ico a c, f n * (w n : ℂ) - (∑ n ∈ Finset.Ico a c, f n) * (w c : ℂ))
            + (∑ n ∈ Finset.Ico a c, f n + f c) * ((w c - w (c + 1) : ℝ) : ℂ) := by
        push_cast; ring
      rw [e]
      calc _ ≤ _ + _ := norm_add_le _ _
        _ ≤ B * (w a - w c) + B * (w c - w (c + 1)) := by
          gcongr
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hwc]
          exact mul_le_mul_of_nonneg_right hS hwc
        _ = B * (w a - w (c + 1)) := by ring
  have h := key b hab
  have hSb := hB b hab
  calc ‖∑ n ∈ Finset.Ico a b, f n * (w n : ℂ)‖
      = ‖(∑ n ∈ Finset.Ico a b, f n * (w n : ℂ) - (∑ n ∈ Finset.Ico a b, f n) * (w b : ℂ))
          + (∑ n ∈ Finset.Ico a b, f n) * (w b : ℂ)‖ := by rw [sub_add_cancel]
    _ ≤ ‖∑ n ∈ Finset.Ico a b, f n * (w n : ℂ) - (∑ n ∈ Finset.Ico a b, f n) * (w b : ℂ)‖
          + ‖(∑ n ∈ Finset.Ico a b, f n) * (w b : ℂ)‖ := norm_add_le _ _
    _ ≤ B * (w a - w b) + B * w b := by
          gcongr
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw0 b)]
          exact mul_le_mul_of_nonneg_right hSb (hw0 b)
    _ = B * w a := by ring

/-- Geometric sums on the unit circle: `‖∑_{a ≤ n < b} zⁿ‖ ≤ 2/‖z − 1‖`. -/
private lemma pv_norm_geom_Ico_le {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (a b : ℕ) :
    ‖∑ n ∈ Finset.Ico a b, z ^ n‖ ≤ 2 / ‖z - 1‖ := by
  rcases le_or_gt a b with hab | hab
  · rw [geom_sum_Ico hz1 hab, norm_div]
    have h1 : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz1)
    gcongr
    calc ‖z ^ b - z ^ a‖ ≤ ‖z ^ b‖ + ‖z ^ a‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_pow, hz]; norm_num
  · rw [Finset.Ico_eq_empty_of_le hab.le, Finset.sum_empty, norm_zero]; positivity

/-- Jordan's inequality in the form `1/sin(πv/q) ≤ q/(2v) + q/(2(q−v))` for `0 < v < q`. -/
private lemma pv_one_div_sin_le {q v : ℕ} (hv0 : 0 < v) (hvq : v < q) :
    1 / Real.sin (Real.pi * v / q) ≤ (q : ℝ) / (2 * v) + (q : ℝ) / (2 * ((q - v : ℕ) : ℝ)) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast (lt_trans hv0 hvq)
  have hv : (0 : ℝ) < v := by exact_mod_cast hv0
  have hvq' : (v : ℝ) < q := by exact_mod_cast hvq
  have hqv : ((q - v : ℕ) : ℝ) = (q : ℝ) - v := by rw [Nat.cast_sub hvq.le]
  have hqv0 : (0 : ℝ) < (q : ℝ) - v := by linarith
  rw [hqv]
  have ht1 : 0 ≤ (q : ℝ) / (2 * v) := by positivity
  have ht2 : 0 ≤ (q : ℝ) / (2 * ((q : ℝ) - v)) := by positivity
  rcases le_or_gt (2 * v) q with h2 | h2
  · have h2' : (2 : ℝ) * v ≤ q := by exact_mod_cast h2
    have hθ0 : 0 ≤ Real.pi * v / q := by positivity
    have hθ1 : Real.pi * v / q ≤ Real.pi / 2 := by
      rw [div_le_div_iff₀ hq (by norm_num)]; nlinarith [Real.pi_pos]
    have hs := Real.mul_le_sin hθ0 hθ1
    have hsv : 2 / Real.pi * (Real.pi * v / q) = 2 * v / q := by
      field_simp
    rw [hsv] at hs
    have hpos : 0 < 2 * (v : ℝ) / q := by positivity
    calc 1 / Real.sin (Real.pi * v / q) ≤ 1 / (2 * v / q) := one_div_le_one_div_of_le hpos hs
      _ = q / (2 * v) := by field_simp
      _ ≤ _ := le_add_of_nonneg_right ht2
  · have h2' : (q : ℝ) < 2 * v := by exact_mod_cast h2
    have heq : Real.sin (Real.pi * v / q) = Real.sin (Real.pi * ((q : ℝ) - v) / q) := by
      rw [← Real.sin_pi_sub]; congr 1; field_simp
    have hθ0 : 0 ≤ Real.pi * ((q : ℝ) - v) / q := by positivity
    have hθ1 : Real.pi * ((q : ℝ) - v) / q ≤ Real.pi / 2 := by
      rw [div_le_div_iff₀ hq (by norm_num)]; nlinarith [Real.pi_pos]
    have hs := Real.mul_le_sin hθ0 hθ1
    have hsv : 2 / Real.pi * (Real.pi * ((q : ℝ) - v) / q) = 2 * ((q : ℝ) - v) / q := by
      field_simp
    rw [hsv] at hs
    have hpos : 0 < 2 * ((q : ℝ) - v) / q := by positivity
    rw [heq]
    calc 1 / Real.sin (Real.pi * ((q : ℝ) - v) / q) ≤ 1 / (2 * ((q : ℝ) - v) / q) :=
          one_div_le_one_div_of_le hpos hs
      _ = q / (2 * ((q : ℝ) - v)) := by field_simp
      _ ≤ _ := le_add_of_nonneg_left ht1

/-- For `0 < v < q`: `‖∑_{a ≤ n < b} e(v/q)ⁿ‖ ≤ q/(2v) + q/(2(q−v))`. -/
private lemma pv_norm_sum_Ico_eA_le {q v : ℕ} (hv0 : 0 < v) (hvq : v < q) (a b : ℕ) :
    ‖∑ n ∈ Finset.Ico a b, (Families.eA ((v : ℝ) / q)) ^ n‖
      ≤ (q : ℝ) / (2 * v) + (q : ℝ) / (2 * ((q - v : ℕ) : ℝ)) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast (lt_trans hv0 hvq)
  have hv : (0 : ℝ) < v := by exact_mod_cast hv0
  have hvq' : (v : ℝ) < q := by exact_mod_cast hvq
  set x : ℝ := 2 * Real.pi * v / q with hx
  have hz : Families.eA ((v : ℝ) / q) = Complex.exp (Complex.I * x) := by
    unfold Families.eA; congr 1; rw [hx]; push_cast; ring
  rw [hz]
  have hnorm : ‖Complex.exp (Complex.I * x)‖ = 1 := Complex.norm_exp_I_mul_ofReal x
  have hsin : 0 < Real.sin (Real.pi * v / q) := by
    apply Real.sin_pos_of_pos_of_lt_pi (by positivity)
    rw [div_lt_iff₀ hq]; nlinarith [Real.pi_pos]
  have hsub : ‖Complex.exp (Complex.I * x) - 1‖ = 2 * Real.sin (Real.pi * v / q) := by
    rw [Complex.norm_exp_I_mul_ofReal_sub_one]
    have : x / 2 = Real.pi * v / q := by rw [hx]; ring
    rw [this, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hz1 : Complex.exp (Complex.I * x) ≠ 1 := by
    intro h; rw [h, sub_self, norm_zero] at hsub; linarith
  calc _ ≤ 2 / ‖Complex.exp (Complex.I * x) - 1‖ := pv_norm_geom_Ico_le hnorm hz1 a b
    _ = 1 / Real.sin (Real.pi * v / q) := by rw [hsub]; field_simp
    _ ≤ _ := pv_one_div_sin_le hv0 hvq

/-- **Pólya–Vinogradov** for a primitive character modulo `q ≥ 2`. -/
theorem pv_Ico {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hq : 2 ≤ q)
    (a b : ℕ) :
    ‖∑ n ∈ Finset.Ico a b, χ (n : ZMod q)‖ ≤ 2 * Real.sqrt q * (1 + Real.log q) := by
  have : Fact (1 < q) := ⟨by omega⟩
  have hqR : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hτ : ‖gaussSum χ⁻¹ (ZMod.stdAddChar (N := q))‖ = Real.sqrt q := by
    rw [← Families.norm_sq_gaussSum χ hχ, Real.sqrt_sq (norm_nonneg _)]
  have hψ : ∀ (n : ℕ) (c : ZMod q),
      ZMod.stdAddChar (N := q) ((n : ZMod q) * c) = (Families.eA ((c.val : ℝ) / q)) ^ n := by
    intro n c
    have h := Families.eA_eq_stdAddChar (q := q) c.val (n : ℤ)
    rw [ZMod.natCast_zmod_val, Int.cast_natCast, Int.cast_natCast] at h
    rw [← h]
    unfold Families.eA
    rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
  -- the bound for each frequency `c`
  have hc : ∀ c : ZMod q,
      ‖χ⁻¹ c * ∑ n ∈ Finset.Ico a b, ZMod.stdAddChar (N := q) ((n : ZMod q) * c)‖
        ≤ (q : ℝ) / (2 * (c.val : ℝ)) + (q : ℝ) / (2 * ((-c).val : ℝ)) := by
    intro c
    by_cases h0 : c = 0
    · subst h0; simp [MulChar.map_zero]
    · have hv0 : 0 < c.val := ZMod.val_pos.mpr h0
      have hvq : c.val < q := ZMod.val_lt c
      rw [ZMod.neg_val, if_neg h0, norm_mul]
      simp_rw [hψ]
      calc ‖χ⁻¹ c‖ * ‖∑ n ∈ Finset.Ico a b, Families.eA ((c.val : ℝ) / q) ^ n‖
          ≤ 1 * ((q : ℝ) / (2 * (c.val : ℝ)) + (q : ℝ) / (2 * ((q - c.val : ℕ) : ℝ))) :=
            mul_le_mul (DirichletCharacter.norm_le_one _ _) (pv_norm_sum_Ico_eA_le hv0 hvq a b)
              (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
  have hmain : (∑ n ∈ Finset.Ico a b, χ (n : ZMod q)) * gaussSum χ⁻¹ (ZMod.stdAddChar (N := q))
      = ∑ c : ZMod q, χ⁻¹ c * ∑ n ∈ Finset.Ico a b, ZMod.stdAddChar (N := q) ((n : ZMod q) * c) := by
    rw [Finset.sum_mul]
    simp_rw [Families.gauss_identity χ hχ, Finset.mul_sum]
    exact Finset.sum_comm
  have hval : ∀ F : ℕ → ℝ, ∑ c : ZMod q, F c.val = ∑ v ∈ Finset.range q, F v := by
    intro F
    refine Finset.sum_nbij' (fun c => c.val) (fun v => (v : ZMod q)) ?_ ?_ ?_ ?_ ?_
    · intro c _; exact Finset.mem_range.mpr (ZMod.val_lt c)
    · intros; exact Finset.mem_univ _
    · intro c _; exact ZMod.natCast_zmod_val c
    · intro v hv; exact ZMod.val_cast_of_lt (Finset.mem_range.mp hv)
    · intros; rfl
  have hsum_val : ∑ c : ZMod q, ((q : ℝ) / (2 * (c.val : ℝ)) + (q : ℝ) / (2 * ((-c).val : ℝ)))
      = q * ∑ v ∈ Finset.range q, (1 : ℝ) / v := by
    rw [Finset.sum_add_distrib]
    have hneg : ∑ c : ZMod q, (q : ℝ) / (2 * ((-c).val : ℝ))
        = ∑ c : ZMod q, (q : ℝ) / (2 * (c.val : ℝ)) :=
      Equiv.sum_comp (Equiv.neg (ZMod q)) (fun c => (q : ℝ) / (2 * (c.val : ℝ)))
    rw [hneg, hval (fun v => (q : ℝ) / (2 * (v : ℝ))), Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hv : (v : ℝ) = 0
    · simp [hv]
    · field_simp; ring
  have hH : ∑ v ∈ Finset.range q, (1 : ℝ) / v ≤ 1 + Real.log q := by
    calc ∑ v ∈ Finset.range q, (1 : ℝ) / v ≤ ∑ v ∈ Finset.range (q + 1), (1 : ℝ) / v :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun x hx => Finset.mem_range.mpr (by have := Finset.mem_range.mp hx; omega))
            (fun _ _ _ => by positivity)
      _ = (harmonic q : ℝ) := by
          rw [Finset.sum_range_succ']
          unfold harmonic
          push_cast
          simp
      _ ≤ 1 + Real.log q := harmonic_le_one_add_log q
  have h1 : ‖∑ n ∈ Finset.Ico a b, χ (n : ZMod q)‖ * Real.sqrt q ≤ q * (1 + Real.log q) := by
    rw [← hτ, ← norm_mul, hmain]
    calc _ ≤ ∑ c : ZMod q,
          ‖χ⁻¹ c * ∑ n ∈ Finset.Ico a b, ZMod.stdAddChar (N := q) ((n : ZMod q) * c)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ c : ZMod q, ((q : ℝ) / (2 * (c.val : ℝ)) + (q : ℝ) / (2 * ((-c).val : ℝ))) :=
          Finset.sum_le_sum fun c _ => hc c
      _ = q * ∑ v ∈ Finset.range q, (1 : ℝ) / v := hsum_val
      _ ≤ q * (1 + Real.log q) := by gcongr
  have hsq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hqR.le
  have hsqpos : 0 < Real.sqrt q := Real.sqrt_pos.mpr hqR
  have hlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have h2 : ‖∑ n ∈ Finset.Ico a b, χ (n : ZMod q)‖ ≤ Real.sqrt q * (1 + Real.log q) := by
    refine le_of_mul_le_mul_right ?_ hsqpos
    calc ‖∑ n ∈ Finset.Ico a b, χ (n : ZMod q)‖ * Real.sqrt q ≤ q * (1 + Real.log q) := h1
      _ = Real.sqrt q * (1 + Real.log q) * Real.sqrt q := by rw [mul_right_comm, hsq]
  have h3 : 0 ≤ Real.sqrt q * (1 + Real.log q) := by positivity
  linarith

/-- The tail of the Dirichlet series of `L(s,χ)` for `Re s > 0`, `χ ≠ 1`. -/
theorem norm_LFunction_sub_partial_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) (N : ℕ) (hN : 1 ≤ N) :
    ‖χ.LFunction s - ∑ m ∈ Finset.Icc 1 N, χ (m : ZMod q) * (m : ℂ) ^ (-s)‖
      ≤ q * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) := by
  open MeasureTheory in
  have hq1 : q ≠ 1 := by
    rintro rfl
    exact hχ (DirichletCharacter.level_one χ)
  have : Nontrivial (ZMod q) := ZMod.nontrivial_iff.mpr hq1
  have hχ0 : χ ((0 : ℕ) : ZMod q) = 0 := by rw [Nat.cast_zero]; exact MulChar.map_zero χ
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; exact lt_irrefl _ hs
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set S : ℝ → ℂ := fun t => ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, χ (k : ZMod q) with hSdef
  have hSb : ∀ t, ‖S t‖ ≤ q := fun t => Zeta23.ThmE.norm_sum_Icc_le hχ _
  have hmeasS : Measurable S :=
    (measurable_from_nat (f := fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q))).comp
      Nat.measurable_floor
  set g : ℝ → ℂ := fun t => S t * (t : ℂ) ^ (-(s + 1)) with hgdef
  have hgle : ∀ t : ℝ, 0 < t → ‖g t‖ ≤ q * t ^ (-(s.re + 1)) := by
    intro t ht0
    simp only [hgdef]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have hre : (-(s + 1)).re = -(s.re + 1) := by simp
    rw [hre]
    exact mul_le_mul_of_nonneg_right (hSb t) (by positivity)
  have hgmeas : Measurable g := hmeasS.mul (Complex.measurable_ofReal.pow_const _)
  have hgint : IntegrableOn g (Set.Ioi 1) := by
    have hmaj : IntegrableOn (fun t : ℝ => (q : ℝ) * t ^ (-(s.re + 1))) (Set.Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _
    refine hmaj.mono' hgmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hgle t (lt_trans zero_lt_one ht)
  have hsplit : ∫ t in Set.Ioi (1 : ℝ), g t
      = (∫ t in Set.Ioc (1 : ℝ) N, g t) + ∫ t in Set.Ioi (N : ℝ), g t := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hN1]
    exact setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hgint.mono_set Set.Ioc_subset_Ioi_self) (hgint.mono_set (Set.Ioi_subset_Ioi hN1))
  -- finite Abel summation on `(1, N]`
  have habel : s * ∫ t in Set.Ioc (1 : ℝ) N, g t
      = ∑ m ∈ Finset.Icc 1 N, χ (m : ZMod q) * (m : ℂ) ^ (-s) - S N * (N : ℂ) ^ (-s) := by
    have hc : (fun k : ℕ => χ (k : ZMod q)) 0 = 0 := hχ0
    have hdiff : ∀ t ∈ Set.Icc (1 : ℝ) N,
        DifferentiableAt ℝ (fun x : ℝ => (x : ℂ) ^ (-s)) t :=
      fun t ht => differentiableAt_id.ofReal_cpow_const (zero_lt_one.trans_le ht.1).ne'
        (neg_ne_zero.mpr hs0)
    have hint : IntegrableOn (deriv fun x : ℝ => (x : ℂ) ^ (-s)) (Set.Icc (1 : ℝ) N) :=
      (integrableOn_Ioi_deriv_ofReal_cpow (s := -s) (t := 1 / 2) (by norm_num)
        (by simpa using hs)).mono_set (fun t ht => lt_of_lt_of_le (by norm_num) ht.1)
    have hA := sum_mul_eq_sub_integral_mul₀' (fun k : ℕ => χ (k : ZMod q)) hc N hdiff hint
    have h₄ : ∀ n : ℕ, ∑ k ∈ Finset.Icc 0 n, χ (k : ZMod q)
        = ∑ k ∈ Finset.Icc 1 n, χ (k : ZMod q) := fun n => by
      rw [← Finset.insert_Icc_add_one_left_eq_Icc n.zero_le, Finset.sum_insert (by simp), hχ0,
        zero_add, zero_add]
    have h₅ : ∑ k ∈ Finset.Icc 0 N, ((k : ℝ) : ℂ) ^ (-s) * χ (k : ZMod q)
        = ∑ m ∈ Finset.Icc 1 N, χ (m : ZMod q) * (m : ℂ) ^ (-s) := by
      rw [← Finset.insert_Icc_add_one_left_eq_Icc N.zero_le, Finset.sum_insert (by simp), hχ0,
        mul_zero, zero_add]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Complex.ofReal_natCast, mul_comm]
    have h₆ : ∫ t in Set.Ioc (1 : ℝ) N, deriv (fun x : ℝ => (x : ℂ) ^ (-s)) t
          * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, χ (k : ZMod q)
        = -s * ∫ t in Set.Ioc (1 : ℝ) N, g t := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
      rw [Complex.deriv_ofReal_cpow_const (zero_lt_one.trans ht.1).ne' (neg_ne_zero.mpr hs0), h₄]
      simp only [hgdef, hSdef]
      rw [show -s - 1 = -(s + 1) by ring]; ring
    rw [h₅, h₆, h₄, Complex.ofReal_natCast] at hA
    have hSN : S N = ∑ k ∈ Finset.Icc 1 N, χ (k : ZMod q) := by
      simp only [hSdef, Nat.floor_natCast]
    rw [hSN]
    linear_combination -hA
  have htail : ‖∫ t in Set.Ioi (N : ℝ), g t‖ ≤ q * (N : ℝ) ^ (-s.re) / s.re := by
    have hmaj : IntegrableOn (fun t : ℝ => (q : ℝ) * t ^ (-(s.re + 1))) (Set.Ioi N) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) hN0).const_mul _
    calc ‖∫ t in Set.Ioi (N : ℝ), g t‖ ≤ ∫ t in Set.Ioi (N : ℝ), (q : ℝ) * t ^ (-(s.re + 1)) := by
          apply norm_integral_le_of_norm_le hmaj
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact hgle t (lt_trans hN0 ht)
      _ = q * ∫ t in Set.Ioi (N : ℝ), t ^ (-(s.re + 1)) := integral_const_mul _ _
      _ = q * (N : ℝ) ^ (-s.re) / s.re := by
          rw [integral_Ioi_rpow_of_lt (by linarith) hN0]
          have : -(s.re + 1) + 1 = -s.re := by ring
          rw [this]
          field_simp
  have hSN : ‖S N * (N : ℂ) ^ (-s)‖ ≤ q * (N : ℝ) ^ (-s.re) := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
    exact mul_le_mul_of_nonneg_right (hSb N) (by positivity)
  have hL : χ.LFunction s = s * ∫ t in Set.Ioi (1 : ℝ), g t :=
    Zeta23.ThmE.LFunction_eq_mul_integral hχ hs
  rw [hL, hsplit, mul_add, habel]
  have e : ∑ m ∈ Finset.Icc 1 N, χ (m : ZMod q) * (m : ℂ) ^ (-s) - S N * (N : ℂ) ^ (-s)
      + s * (∫ t in Set.Ioi (N : ℝ), g t) - ∑ m ∈ Finset.Icc 1 N, χ (m : ZMod q) * (m : ℂ) ^ (-s)
      = s * (∫ t in Set.Ioi (N : ℝ), g t) - S N * (N : ℂ) ^ (-s) := by ring
  rw [e]
  calc _ ≤ ‖s * ∫ t in Set.Ioi (N : ℝ), g t‖ + ‖S N * (N : ℂ) ^ (-s)‖ := norm_sub_le _ _
    _ ≤ ‖s‖ * (q * (N : ℝ) ^ (-s.re) / s.re) + q * (N : ℝ) ^ (-s.re) := by
        rw [norm_mul]; gcongr
    _ = q * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) := by field_simp; ring

/-- `π⁴/90 − 1 ≤ 1/10`. -/
private lemma pi_four_div_ninety_sub_one_le : Real.pi ^ 4 / 90 - 1 ≤ 1 / 10 := by
  have h1 : Real.pi ^ 4 < (3.15 : ℝ) ^ 4 :=
    pow_lt_pow_left₀ Real.pi_lt_d2 Real.pi_pos.le (by norm_num)
  have h2 : (3.15 : ℝ) ^ 4 ≤ 99 := by norm_num
  linarith

/-- `∑_{n ≥ 0} 1/(n+2)⁴ = π⁴/90 − 1`. -/
private lemma hasSum_zeta_four_shift_two :
    HasSum (fun n : ℕ => 1 / ((n : ℝ) + 2) ^ 4) (Real.pi ^ 4 / 90 - 1) := by
  have h := (hasSum_nat_add_iff' 2).mpr hasSum_zeta_four
  norm_num [Finset.sum_range_succ] at h
  exact h.congr_fun fun n => by ring

/-- `∑_{2 ≤ n ≤ X} n^{-σ} ≤ 1/10` for `σ ≥ 4`. -/
theorem sum_Icc_two_rpow_le (X : ℕ) {σ : ℝ} (hσ : 4 ≤ σ) :
    ∑ n ∈ Finset.Icc 2 X, (n : ℝ) ^ (-σ) ≤ 1 / 10 := by
  have hle : ∀ n ∈ Finset.Icc 2 X, (n : ℝ) ^ (-σ) ≤ 1 / (n : ℝ) ^ 4 := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by
      have := (Finset.mem_Icc.mp hn).1
      exact_mod_cast (by omega : 1 ≤ n)
    calc (n : ℝ) ^ (-σ) ≤ (n : ℝ) ^ (-(4 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      _ = 1 / (n : ℝ) ^ 4 := by
          rw [Real.rpow_neg (by linarith), Real.rpow_ofNat, one_div]
  have hnot : (1 : ℕ) ∉ Finset.Icc 2 X := by simp
  have hsum := sum_le_hasSum (insert 1 (Finset.Icc 2 X))
    (fun n _ => by positivity) hasSum_zeta_four
  rw [Finset.sum_insert hnot] at hsum
  norm_num at hsum
  calc ∑ n ∈ Finset.Icc 2 X, (n : ℝ) ^ (-σ) ≤ ∑ n ∈ Finset.Icc 2 X, 1 / (n : ℝ) ^ 4 :=
        Finset.sum_le_sum hle
    _ ≤ Real.pi ^ 4 / 90 - 1 := by
        have : ∑ n ∈ Finset.Icc 2 X, 1 / (n : ℝ) ^ 4 = ∑ n ∈ Finset.Icc 2 X, ((n : ℝ) ^ 4)⁻¹ := by
          simp
        linarith
    _ ≤ 1 / 10 := pi_four_div_ninety_sub_one_le

/-- `‖L(s,χ) − 1‖ ≤ 1/10` for `Re s ≥ 4`. -/
theorem norm_LFunction_sub_one_le_of_four_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 4 ≤ s.re) : ‖χ.LFunction s - 1‖ ≤ 1 / 10 := by
  have hs1 : 1 < s.re := by linarith
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs1]
  set f : ℕ → ℂ := fun n => χ (n : ZMod q) with hf
  have hsum : Summable (LSeries.term f s) := DirichletCharacter.LSeriesSummable_of_one_lt_re χ hs1
  have hsplit := hsum.sum_add_tsum_nat_add 2
  have h01 : ∑ i ∈ Finset.range 2, LSeries.term f s i = 1 := by
    simp [Finset.sum_range_succ, LSeries.term, hf]
  have hL : LSeries f s - 1 = ∑' i, LSeries.term f s (i + 2) := by
    rw [LSeries, ← hsplit, h01]; ring
  rw [hL]
  have hle : ∀ i : ℕ, ‖LSeries.term f s (i + 2)‖ ≤ 1 / ((i : ℝ) + 2) ^ 4 := by
    intro i
    have hpos : 0 < i + 2 := by omega
    rw [LSeries.term_of_ne_zero (by omega : i + 2 ≠ 0), norm_div,
      Complex.norm_natCast_cpow_of_pos hpos]
    have h1 : ‖f (i + 2)‖ ≤ 1 := χ.norm_le_one _
    have hbase : (1 : ℝ) ≤ ((i + 2 : ℕ) : ℝ) := by exact_mod_cast hpos
    have hpow : ((i + 2 : ℕ) : ℝ) ^ (4 : ℝ) ≤ ((i + 2 : ℕ) : ℝ) ^ s.re :=
      Real.rpow_le_rpow_of_exponent_le hbase hs
    rw [Real.rpow_ofNat] at hpow
    have h2pos : (0 : ℝ) < ((i + 2 : ℕ) : ℝ) ^ 4 := by positivity
    have hσpos : (0 : ℝ) < ((i + 2 : ℕ) : ℝ) ^ s.re := by positivity
    calc ‖f (i + 2)‖ / ((i + 2 : ℕ) : ℝ) ^ s.re ≤ 1 / ((i + 2 : ℕ) : ℝ) ^ s.re :=
          div_le_div_of_nonneg_right h1 hσpos.le
      _ ≤ 1 / ((i + 2 : ℕ) : ℝ) ^ 4 := one_div_le_one_div_of_le h2pos hpow
      _ = 1 / ((i : ℝ) + 2) ^ 4 := by push_cast; ring
  have hsum' : Summable (fun i => LSeries.term f s (i + 2)) := (summable_nat_add_iff 2).mpr hsum
  calc ‖∑' i, LSeries.term f s (i + 2)‖ ≤ ∑' i, ‖LSeries.term f s (i + 2)‖ :=
        norm_tsum_le_tsum_norm hsum'.norm
    _ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 2) ^ 4 :=
        hsum'.norm.tsum_le_tsum hle hasSum_zeta_four_shift_two.summable
    _ = Real.pi ^ 4 / 90 - 1 := hasSum_zeta_four_shift_two.tsum_eq
    _ ≤ 1 / 10 := pi_four_div_ninety_sub_one_le

end Families.Hyp.Montgomery
