/-
# **`lem:WH`**, the masses `W` and `H` (Lemma 6.1)

`Families.Phase2.B.lemWH_proof : lemWH_Statement`, with `c₀ = 8`:
`|W − c_w Q²| ≤ 8 V_w Q log(2Q)` and `|H − ℰ I_w Q²| ≤ 8 V_w Q^{3/2}` for every admissible `w`, real `Q ≥ 2`.

Route (the readiness survey's "divisor outside"; it replaces the TeX's Abel summation against
`∑_{q≤x} φ(q)` and `∑_{q≤x} qψ(q)`): both masses have the form
`M_b = ∑_{q≤Q} w(q/Q) q ∑_{d∣q} b(d) = ∑_{d≤Q} b(d) d ∑_{m≤Q/d} m w(dm/Q)`, with
`b(d) = μ(d)/d` for `W` (`φ(q) = q ∑_{d∣q} μ(d)/d`) and `b = g` for `H`
(`q φ*(q)/φ(q) = q ψ(q)`, `ψ = 1 * g`, `lem:fS`(ii) with `S ⊇ {p ≤ Q}`).
* Inner sums (`sum_m_w_le`): `eqA:APTV` (`Phase1.A.aptv`) for `f(u) = u w(u)` with step `d/Q`:
  `|∑_m m w(dm/Q) − (Q/d)² I_w| ≤ (Q/d) TV(f)`, and `TV(f) ≤ (3/2) V_w` (`eVariationOn_mul_le`, a product
  rule for the variation, with `f = clamp·w`).
* So `|M_b − Q² I_w ∑_{d≤Q} b(d)/d| ≤ (3/2) V_w Q ∑_{d≤Q} |b(d)|` (`mass_general`).
* `W`: `∑_d μ(d)/d² = 6/π²` (Mathlib: `L(μ,2) ζ(2) = 1`, `ζ(2) = π²/6`), tail `≤ 1/N`,
  `∑_{d≤N} 1/d ≤ 1 + log N`.
* `H`: `∑_d g(d)/d = ℰ` (`lem:fS`(ii)), and `∑_d |g(d)| d^{−1/2} ≤ B < 3.73` (`tsum_gabs_le_Bconst`) gives
  tail `≤ B Q^{−1/2}` and `∑_{d≤Q} |g(d)| ≤ B Q^{1/2}`. `φ* = φ ψ` (`phiStar_eq_mul`) by multiplicativity
  from `phiStar_eq` (`φ* = φ * μ`).
Constants: `I_w ≤ V_w/2`, `w ≤ V_w/2`.
-/
import Families.Phase2.B.RSBound
import Families.Phase1.A.Toolkit

noncomputable section

open scoped BigOperators ENNReal ArithmeticFunction.Moebius ArithmeticFunction.zeta
open Finset MeasureTheory Set

namespace Families.Phase2.B

open Families Families.Phase1.B

/-! ### Variation of `u w(u)` -/

/-- Product rule for the variation: `TV(fg) ≤ A TV(g) + B TV(f)` if `|f| ≤ A`, `|g| ≤ B`. -/
lemma eVariationOn_mul_le (f g : ℝ → ℝ) (s : Set ℝ) {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ∀ x ∈ s, |f x| ≤ A) (hg : ∀ x ∈ s, |g x| ≤ B) :
    eVariationOn (fun x => f x * g x) s ≤
      ENNReal.ofReal A * eVariationOn g s + ENNReal.ofReal B * eVariationOn f s := by
  refine iSup_le fun p => ?_
  obtain ⟨n, u, hu, us⟩ := p
  calc ∑ i ∈ Finset.range n, edist (f (u (i + 1)) * g (u (i + 1))) (f (u i) * g (u i))
      ≤ ∑ i ∈ Finset.range n, (ENNReal.ofReal A * edist (g (u (i + 1))) (g (u i)) +
          ENNReal.ofReal B * edist (f (u (i + 1))) (f (u i))) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [edist_dist, edist_dist, edist_dist, Real.dist_eq, Real.dist_eq, Real.dist_eq,
          ← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul hB,
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have e : f (u (i + 1)) * g (u (i + 1)) - f (u i) * g (u i) =
            f (u (i + 1)) * (g (u (i + 1)) - g (u i)) + g (u i) * (f (u (i + 1)) - f (u i)) := by
          ring
        rw [e]
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul]
        gcongr
        · exact hf _ (us _)
        · exact hg _ (us _)
    _ = ENNReal.ofReal A * ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) +
          ENNReal.ofReal B * ∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := by
        gcongr
        · exact eVariationOn.sum_le hu us
        · exact eVariationOn.sum_le hu us

/-- `clamp(u) = max(0, min(u, 1))`. -/
def clamp01 (u : ℝ) : ℝ := max 0 (min u 1)

lemma eVariationOn_clamp01_le : eVariationOn clamp01 univ ≤ 1 := by
  rw [eVariationOn_univ_eq_Icc clamp01 zero_le_one
    (fun x hx => by simp [clamp01, min_eq_left (hx.trans zero_le_one), max_eq_left hx])
    (fun x hx => by simp [clamp01, min_eq_right hx])]
  have hm : MonotoneOn clamp01 (Icc 0 1) := fun x _ y _ hxy =>
    max_le_max le_rfl (min_le_min hxy le_rfl)
  have := (hm.eVariationOn_eq (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one)).le
  rw [Set.inter_self] at this
  refine this.trans ?_
  simp [clamp01]

lemma w_eq_zero_of_lt (W : Weight) {u : ℝ} (hu : u < W.η) : W.w u = 0 := by
  by_contra h; linarith [(W.supp u h).1]

lemma w_eq_zero_of_gt (W : Weight) {u : ℝ} (hu : 1 < u) : W.w u = 0 := by
  by_contra h; linarith [(W.supp u h).2]

/-- `0 ≤ w ≤ V_w/2`. -/
lemma w_le_half_Vw (W : Weight) (u : ℝ) : W.w u ≤ W.Vw / 2 := by
  have h := Phase1.A.two_mul_abs_le_variation W.bv (A := 0) (B := 1)
    (fun x hx => ⟨le_trans W.η_pos.le (W.supp x hx).1, (W.supp x hx).2⟩) u
  rw [abs_of_nonneg (W.nonneg u)] at h
  unfold Weight.Vw; linarith

lemma Vw_nonneg (W : Weight) : 0 ≤ W.Vw := ENNReal.toReal_nonneg

/-- `TV(u ↦ u w(u)) ≤ (3/2) V_w`. -/
lemma eVariationOn_uw_le (W : Weight) :
    eVariationOn (fun u => u * W.w u) univ ≤ ENNReal.ofReal (3 / 2 * W.Vw) := by
  have heq : (fun u => u * W.w u) = fun u => clamp01 u * W.w u := by
    funext u
    by_cases h : W.w u = 0
    · rw [h, mul_zero, mul_zero]
    · obtain ⟨h1, h2⟩ := W.supp u h
      rw [clamp01, min_eq_left h2, max_eq_right (le_trans W.η_pos.le h1)]
  rw [heq]
  have hV := Vw_nonneg W
  refine (eVariationOn_mul_le clamp01 W.w univ zero_le_one (by positivity : (0 : ℝ) ≤ W.Vw / 2)
    (fun x _ => by
      rw [abs_of_nonneg (le_max_left _ _)]
      exact max_le zero_le_one (min_le_right _ _))
    (fun x _ => by rw [abs_of_nonneg (W.nonneg x)]; exact w_le_half_Vw W x)).trans ?_
  have hVw : eVariationOn W.w univ = ENNReal.ofReal W.Vw := (ENNReal.ofReal_toReal W.bv).symm
  rw [hVw, ENNReal.ofReal_one, one_mul]
  calc ENNReal.ofReal W.Vw + ENNReal.ofReal (W.Vw / 2) * eVariationOn clamp01 univ
      ≤ ENNReal.ofReal W.Vw + ENNReal.ofReal (W.Vw / 2) * 1 := by gcongr; exact eVariationOn_clamp01_le
    _ = ENNReal.ofReal (3 / 2 * W.Vw) := by
        rw [mul_one, ← ENNReal.ofReal_add hV (by positivity)]; ring_nf

lemma bv_uw (W : Weight) : BoundedVariationOn (fun u => u * W.w u) univ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (eVariationOn_uw_le W)

lemma Tuw_le (W : Weight) : (eVariationOn (fun u => u * W.w u) univ).toReal ≤ 3 / 2 * W.Vw :=
  ENNReal.toReal_le_of_le_ofReal (by have := Vw_nonneg W; positivity) (eVariationOn_uw_le W)

/-- `I_w ≤ V_w/2`. -/
lemma Iw_le_half_Vw (W : Weight) : W.Iw ≤ W.Vw / 2 := by
  unfold Weight.Iw
  calc ∫ u in (0 : ℝ)..1, u * W.w u ≤ ∫ u in (0 : ℝ)..1, W.Vw / 2 := by
        refine intervalIntegral.integral_mono_on zero_le_one (intervalIntegrable_Iw W)
          intervalIntegrable_const fun u hu => ?_
        have := w_le_half_Vw W u
        have := W.nonneg u
        have hV := Vw_nonneg W
        nlinarith [hu.1, hu.2]
    _ = W.Vw / 2 := by simp

/-- `∫_ℝ u w(u) du = I_w`. -/
lemma integral_uw (W : Weight) : ∫ u, u * W.w u = W.Iw := by
  unfold Weight.Iw
  rw [intervalIntegral.integral_of_le zero_le_one]
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => ?_).symm
  simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hu
  rcases hu with hu | hu
  · rw [w_eq_zero_of_lt W (lt_of_le_of_lt hu W.η_pos), mul_zero]
  · rw [w_eq_zero_of_gt W hu, mul_zero]

/-! ### The inner sums `∑_m m w(dm/Q)` (`eqA:APTV`) -/

/-- `|∑_{1≤m≤N/d} m w(dm/Q) − (Q/d)² I_w| ≤ (Q/d)·(3/2)V_w`, `N = ⌊Q⌋`. -/
theorem sum_m_w_le (W : Weight) (Q : ℝ) (hQ : 0 < Q) (d : ℕ) (hd : 1 ≤ d) :
    |∑ m ∈ Finset.Icc 1 (⌊Q⌋₊ / d), (m : ℝ) * W.w (d * m / Q) - (Q / d) ^ 2 * W.Iw| ≤
      Q / d * (3 / 2 * W.Vw) := by
  set N := ⌊Q⌋₊
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set D : ℝ := d / Q with hD
  have hDpos : 0 < D := by positivity
  obtain ⟨-, hb⟩ := Phase1.A.aptv (bv_uw W) (A := 0) (B := 1)
    (fun x hx => by
      have hw : W.w x ≠ 0 := fun h => hx (by rw [h, mul_zero])
      exact ⟨le_trans W.η_pos.le (W.supp x hw).1, (W.supp x hw).2⟩) 0 D hDpos
  -- the `ℤ`-sum is the finite sum over `1 ≤ m ≤ N/d`
  have hts : ∑' j : ℤ, (0 + D * j) * W.w (0 + D * j) =
      ∑ m ∈ Finset.Icc 1 (N / d), (D * m) * W.w (D * m) := by
    rw [tsum_eq_sum (s := (Finset.Icc 1 (N / d)).image (fun m : ℕ => (m : ℤ)))]
    · rw [Finset.sum_image (fun a _ b _ h => by exact_mod_cast h)]
      refine Finset.sum_congr rfl fun m _ => ?_
      push_cast; ring_nf
    · intro j hj
      simp only [Finset.mem_image, Finset.mem_Icc, not_exists, not_and] at hj
      rw [zero_add]
      rcases le_or_gt j 0 with hj0 | hj0
      · have : D * j ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hDpos.le (by exact_mod_cast hj0)
        rw [w_eq_zero_of_lt W (lt_of_le_of_lt this W.η_pos), mul_zero]
      · obtain ⟨m, rfl⟩ : ∃ m : ℕ, j = m := ⟨j.toNat, by omega⟩
        have hm1 : 1 ≤ m := by exact_mod_cast hj0
        have hm2 : N / d < m := by
          by_contra h; exact hj m ⟨hm1, not_lt.mp h⟩ rfl
        -- `d m ≥ N + 1 > Q`
        have h1 : N + 1 ≤ d * m := by
          have := Nat.lt_mul_div_succ N hd
          nlinarith [Nat.succ_le_of_lt hm2]
        have h2 : Q < (d : ℝ) * m := by
          have : Q < (N : ℝ) + 1 := Nat.lt_floor_add_one Q
          have h1' : ((N + 1 : ℕ) : ℝ) ≤ ((d * m : ℕ) : ℝ) := by exact_mod_cast h1
          push_cast at h1'; linarith
        have : 1 < D * (m : ℤ) := by
          push_cast; rw [hD, div_mul_eq_mul_div, one_lt_div hQ]; exact h2
        rw [w_eq_zero_of_gt W this, mul_zero]
  simp only at hb
  rw [hts, integral_uw] at hb
  have hT := Tuw_le W
  -- rescale by `Q/d`
  have e1 : ∑ m ∈ Finset.Icc 1 (N / d), (m : ℝ) * W.w (d * m / Q) =
      Q / d * ∑ m ∈ Finset.Icc 1 (N / d), (D * m) * W.w (D * m) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hD]; field_simp
  have e2 : (Q / d) ^ 2 * W.Iw = Q / d * (D⁻¹ * W.Iw) := by rw [hD, inv_div]; ring
  rw [e1, e2, ← mul_sub, abs_mul, abs_of_pos (by positivity)]
  exact mul_le_mul_of_nonneg_left (hb.trans hT) (by positivity)

/-- **General mass.** For any `b`,
`|∑_{q≤Q} w(q/Q) q ∑_{d∣q} b(d) − Q² I_w ∑_{d≤Q} b(d)/d| ≤ Q (3/2)V_w ∑_{d≤Q} |b(d)|`. -/
theorem mass_general (W : Weight) (Q : ℝ) (hQ : 0 < Q) (b : ℕ → ℝ) :
    |∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.w (q / Q) * q * ∑ d ∈ q.divisors, b d -
        Q ^ 2 * W.Iw * ∑ d ∈ Finset.Icc 1 ⌊Q⌋₊, b d / d| ≤
      Q * (3 / 2 * W.Vw) * ∑ d ∈ Finset.Icc 1 ⌊Q⌋₊, |b d| := by
  set N := ⌊Q⌋₊
  have hre : ∑ q ∈ Finset.Icc 1 N, W.w (q / Q) * q * ∑ d ∈ q.divisors, b d =
      ∑ d ∈ Finset.Icc 1 N, b d * d * ∑ m ∈ Finset.Icc 1 (N / d), (m : ℝ) * W.w (d * m / Q) := by
    have := sum_Icc_divisors N (fun d q => b d * (q * W.w (q / Q)))
    rw [show ∑ q ∈ Finset.Icc 1 N, W.w (q / Q) * q * ∑ d ∈ q.divisors, b d =
        ∑ q ∈ Finset.Icc 1 N, ∑ d ∈ q.divisors, b d * (q * W.w (q / Q)) by
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun d _ => by ring, this]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    push_cast; ring
  rw [hre, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d hd => ?_)
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  have h := sum_m_w_le W Q hQ d hd1
  have e : b d * d * ∑ m ∈ Finset.Icc 1 (N / d), (m : ℝ) * W.w (d * m / Q) -
      Q ^ 2 * W.Iw * (b d / d) =
      b d * d * (∑ m ∈ Finset.Icc 1 (N / d), (m : ℝ) * W.w (d * m / Q) - (Q / d) ^ 2 * W.Iw) := by
    field_simp
  rw [e, abs_mul, abs_mul, abs_of_pos hd0]
  calc |b d| * d * |∑ m ∈ Finset.Icc 1 (N / d), (m : ℝ) * W.w (d * m / Q) - (Q / d) ^ 2 * W.Iw|
      ≤ |b d| * d * (Q / d * (3 / 2 * W.Vw)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = Q * (3 / 2 * W.Vw) * |b d| := by field_simp

/-! ### Floor facts for `Q ≥ 2` -/

lemma floor_ge_one {Q : ℝ} (hQ : 2 ≤ Q) : 1 ≤ ⌊Q⌋₊ := Nat.le_floor (by push_cast; linarith)

lemma floor_ge_half {Q : ℝ} (hQ : 2 ≤ Q) : Q / 2 ≤ (⌊Q⌋₊ : ℝ) := by
  have := Nat.lt_floor_add_one Q; linarith

/-! ### Tails of `∑ f(d)` -/

/-- `∑_{i<K} 1/(i+N+1)² ≤ 1/N`, hence the tail `∑_{d>N} 1/d² ≤ 1/N`. -/
lemma tsum_inv_sq_tail_le (N : ℕ) (hN : 1 ≤ N) :
    ∑' i : ℕ, (1 : ℝ) / (((i + (N + 1) : ℕ) : ℝ)) ^ 2 ≤ 1 / N := by
  refine Real.tsum_le_of_sum_range_le (fun i => by positivity) fun K => ?_
  have e : ∀ K, ∑ i ∈ Finset.range K, (1 : ℝ) / (((i + (N + 1) : ℕ) : ℝ)) ^ 2 =
      ∑ n ∈ Finset.Ioc N (N + K), (1 : ℝ) / (n : ℝ) ^ 2 := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ, ih, show N + (K + 1) = N + K + 1 by ring,
        Finset.sum_Ioc_succ_top (by omega)]
      congr 3; ring_nf
  rw [e]
  exact sum_Ioc_inv_sq_le N (N + K) hN

/-- Partial sums of a summable series: `∑_{d≤N} f(d) = ∑' f − ∑' f(· + N + 1)` when `f 0 = 0`. -/
lemma sum_Icc_eq_tsum_sub (f : ℕ → ℝ) (hf : Summable f) (h0 : f 0 = 0) (N : ℕ) :
    ∑ d ∈ Finset.Icc 1 N, f d = ∑' d, f d - ∑' i, f (i + (N + 1)) := by
  rw [← hf.sum_add_tsum_nat_add (N + 1), add_sub_cancel_right]
  refine Finset.sum_subset (fun d hd => ?_) fun d hd hd' => ?_
  · rw [Finset.mem_range]; have := (Finset.mem_Icc.mp hd).2; omega
  · have : d = 0 := by
      by_contra h
      exact hd' (Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr h,
        by have := Finset.mem_range.mp hd; omega⟩)
    rw [this, h0]

/-! ### The additive mass `W` -/

/-- `φ(q) = q ∑_{d∣q} μ(d)/d`. -/
lemma totient_eq_sum_moebius (q : ℕ) (hq : 1 ≤ q) :
    (Nat.totient q : ℝ) = q * ∑ d ∈ q.divisors, (μ d : ℝ) / d := by
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℝ)
    (f := fun n => (Nat.totient n : ℝ)) (g := fun n => (n : ℝ))).mp (fun n _ => by
      have := congrArg (Nat.cast : ℕ → ℝ) (Nat.sum_totient n)
      push_cast at this; exact this) q hq
  rw [← h, Nat.sum_divisorsAntidiagonal (fun a b => (μ a : ℝ) * (b : ℝ)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) hd0]
  field_simp

lemma Wm_eq (W : Weight) (Q : ℝ) : W.Wm Q =
    ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.w (q / Q) * q * ∑ d ∈ q.divisors, (μ d : ℝ) / d := by
  unfold Weight.Wm
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [totient_eq_sum_moebius q (Finset.mem_Icc.mp hq).1]; ring

/-- `∑_d μ(d)/d² = 6/π²` (Mathlib: `L(ζ,2) L(μ,2) = 1`, `ζ(2) = π²/6`). -/
lemma hasSum_moebius_div_sq :
    HasSum (fun n : ℕ => (μ n : ℝ) / (n : ℝ) ^ 2) (6 / Real.pi ^ 2) := by
  have hs : 1 < (2 : ℂ).re := by norm_num
  have h1 := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs, riemannZeta_two] at h1
  have hL : LSeries (fun n => (μ n : ℂ)) 2 = 6 / (Real.pi : ℂ) ^ 2 := by
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp at h1 ⊢
    linear_combination h1
  have hsum := (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs).LSeriesHasSum
  rw [hL] at hsum
  have hre := (Complex.reCLM.hasSum hsum)
  simp only [Complex.reCLM_apply] at hre
  convert hre using 1
  · funext n
    rw [LSeries.term_def]
    split_ifs with hn
    · simp [hn]
    · have : ((n : ℂ) ^ (2 : ℂ)) = ((n : ℝ) ^ 2 : ℝ) := by
        rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]; push_cast; ring
      rw [this, ← Complex.ofReal_intCast, ← Complex.ofReal_div, Complex.ofReal_re]
  · rw [show (6 : ℂ) / (Real.pi : ℂ) ^ 2 = ((6 / Real.pi ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]

/-- `|∑_{d≤N} μ(d)/d² − 6/π²| ≤ 1/N`. -/
lemma moebius_partial_le (N : ℕ) (hN : 1 ≤ N) :
    |∑ d ∈ Finset.Icc 1 N, (μ d : ℝ) / d / d - 6 / Real.pi ^ 2| ≤ (1 : ℝ) / N := by
  set f : ℕ → ℝ := fun n => (μ n : ℝ) / (n : ℝ) ^ 2
  have hf := hasSum_moebius_div_sq
  have e : ∑ d ∈ Finset.Icc 1 N, (μ d : ℝ) / d / d = ∑ d ∈ Finset.Icc 1 N, f d :=
    Finset.sum_congr rfl fun d _ => by simp only [f]; rw [div_div, sq]
  have key : ∑ d ∈ Finset.Icc 1 N, f d - 6 / Real.pi ^ 2 = -∑' i, f (i + (N + 1)) := by
    rw [sum_Icc_eq_tsum_sub f hf.summable (by simp [f]) N, hf.tsum_eq]; ring
  rw [e, key, abs_neg]
  have hg : Summable fun i : ℕ => (1 : ℝ) / (((i + (N + 1) : ℕ) : ℝ)) ^ 2 := by
    have := (summable_nat_add_iff (N + 1)).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa using this
  have hle : ∀ i : ℕ, ‖f (i + (N + 1))‖ ≤ (1 : ℝ) / (((i + (N + 1) : ℕ) : ℝ)) ^ 2 := by
    intro i
    simp only [f, Real.norm_eq_abs, abs_div, abs_pow, Nat.abs_cast]
    push_cast
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  calc |∑' i, f (i + (N + 1))| ≤ ∑' i, ‖f (i + (N + 1))‖ :=
        norm_tsum_le_tsum_norm (hg.of_nonneg_of_le (fun _ => norm_nonneg _) hle)
    _ ≤ ∑' i : ℕ, (1 : ℝ) / (((i + (N + 1) : ℕ) : ℝ)) ^ 2 :=
        (hg.of_nonneg_of_le (fun _ => norm_nonneg _) hle).tsum_le_tsum hle hg
    _ ≤ 1 / N := tsum_inv_sq_tail_le N hN

/-- `∑_{d≤N} |μ(d)/d| ≤ 1 + log N`. -/
lemma sum_abs_moebius_div_le (N : ℕ) :
    ∑ d ∈ Finset.Icc 1 N, |(μ d : ℝ) / d| ≤ 1 + Real.log N := by
  have hH : ∑ k ∈ Finset.Icc 1 N, (1 : ℝ) / k = (harmonic N : ℝ) := by
    rw [harmonic_eq_sum_Icc]; push_cast; simp [one_div]
  refine le_trans (Finset.sum_le_sum fun d hd => ?_) (hH ▸ harmonic_le_one_add_log N)
  rw [abs_div, Nat.abs_cast]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

/-- **`lem:WH`, `W`:** `|W − c_w Q²| ≤ 4 V_w Q log(2Q)` for `Q ≥ 2`. -/
theorem Wm_bound (W : Weight) (Q : ℝ) (hQ : 2 ≤ Q) :
    |W.Wm Q - W.cw * Q ^ 2| ≤ 4 * W.Vw * Q * Real.log (2 * Q) := by
  have hQ0 : 0 < Q := by linarith
  set N := ⌊Q⌋₊ with hNdef
  have hN1 := floor_ge_one hQ
  have hN2 := floor_ge_half hQ
  have hNQ : (N : ℝ) ≤ Q := Nat.floor_le hQ0.le
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hV := Vw_nonneg W
  have hI := Iw_le_half_Vw W
  have hI0 : 0 ≤ W.Iw := W.Iw_pos.le
  have hgen := mass_general W Q hQ0 (fun d => (μ d : ℝ) / d)
  rw [← Wm_eq] at hgen
  have hmu := moebius_partial_le N hN1
  have hab := sum_abs_moebius_div_le N
  have hlogN : Real.log N ≤ Real.log Q := Real.log_le_log hN0 hNQ
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg (by linarith)
  have hlog2 : Real.log (2 * Q) = Real.log 2 + Real.log Q := Real.log_mul (by norm_num) hQ0.ne'
  have hl2 := Real.log_two_gt_d9
  set SN := ∑ d ∈ Finset.Icc 1 N, (μ d : ℝ) / d / d
  have e : W.Wm Q - W.cw * Q ^ 2 = (W.Wm Q - Q ^ 2 * W.Iw * SN) +
      Q ^ 2 * W.Iw * (SN - 6 / Real.pi ^ 2) := by
    unfold Weight.cw; ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ Q ^ 2 * W.Iw)]
  have t1 : |W.Wm Q - Q ^ 2 * W.Iw * SN| ≤ Q * (3 / 2 * W.Vw) * (1 + Real.log Q) :=
    hgen.trans (mul_le_mul_of_nonneg_left (hab.trans (by linarith)) (by positivity))
  have t2 : Q ^ 2 * W.Iw * |SN - 6 / Real.pi ^ 2| ≤ Q * W.Vw := by
    calc Q ^ 2 * W.Iw * |SN - 6 / Real.pi ^ 2| ≤ Q ^ 2 * W.Iw * (1 / N) :=
          mul_le_mul_of_nonneg_left hmu (by positivity)
      _ ≤ Q ^ 2 * (W.Vw / 2) * (2 / Q) := by
          have h1N : 1 / (N : ℝ) ≤ 2 / Q := by rw [div_le_div_iff₀ hN0 hQ0]; linarith
          exact mul_le_mul (mul_le_mul_of_nonneg_left hI (sq_nonneg Q)) h1N (by positivity)
            (by positivity)
      _ = Q * W.Vw := by field_simp
  have t3 : Q * (3 / 2 * W.Vw) * (1 + Real.log Q) + Q * W.Vw ≤
      4 * W.Vw * Q * Real.log (2 * Q) := by
    rw [hlog2]
    have hQV : 0 ≤ Q * W.Vw := by positivity
    nlinarith [mul_nonneg hQV hlogQ]
  linarith

/-! ### The multiplicative mass `H` -/

/-- Local factors of `ψ = φ*/φ`. -/
def psiloc (p a : ℕ) : ℝ := if a = 1 then ((p : ℝ) - 2) / (p - 1) else ((p : ℝ) - 1) / p

lemma toAF_mul_eq (f g : ℕ → ℝ) :
    toAF (fun n => ∑ d ∈ n.divisors, f d * g (n / d)) = toAF f * toAF g := by
  ext n
  rw [ArithmeticFunction.mul_apply]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [toAF]
  rw [toAF_apply _ hn.ne', Nat.sum_divisorsAntidiagonal (fun a b => toAF f a * toAF g b)]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 := Nat.pos_of_mem_divisors hd
  have hnd : n / d ≠ 0 := (Nat.div_pos (Nat.divisor_le hd) hd0).ne'
  rw [toAF_apply _ hd0.ne', toAF_apply _ hnd]

/-- **`φ* = φ ψ`**: `φ*(n) = φ(n) ∏_{p^a ∥ n} ψ_p(a)`. -/
theorem phiStar_eq_mul (n : ℕ) (hn : 1 ≤ n) :
    (phiStar n : ℝ) = Nat.totient n * locProd psiloc n := by
  set F := toAF (fun n => ∑ d ∈ n.divisors, (Nat.totient d : ℝ) * (μ (n / d) : ℝ))
  set G := toAF (fun n => (Nat.totient n : ℝ) * locProd psiloc n)
  have hφ : (toAF (fun n => (Nat.totient n : ℝ))).IsMultiplicative :=
    isMultiplicative_toAF _ (by simp) fun _ _ h => by rw [Nat.totient_mul h]; push_cast; ring
  have hμ : (toAF (fun n => (μ n : ℝ))).IsMultiplicative :=
    isMultiplicative_toAF _ (by simp) fun _ _ h => by
      rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h]; push_cast; ring
  have hF : F.IsMultiplicative := by
    have := toAF_mul_eq (fun n => (Nat.totient n : ℝ)) (fun n => (μ n : ℝ))
    simp only [F]
    rw [this]; exact hφ.mul hμ
  have hG : G.IsMultiplicative :=
    isMultiplicative_toAF _ (by simp) fun _ _ h => by
      rw [Nat.totient_mul h, locProd_mul _ h]; push_cast; ring
  have hFG : F = G := by
    refine (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers F hF G hG).mpr
      fun p i hp => ?_
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    rw [toAF_apply _ (pow_ne_zero _ hp.ne_zero), toAF_apply _ (pow_ne_zero _ hp.ne_zero)]
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    rw [locProd_prime_pow _ hp (by omega), Nat.divisors_prime_pow hp, Finset.sum_map]
    simp only [Function.Embedding.coeFn_mk]
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have hzero : ∑ j ∈ Finset.range k, (Nat.totient (p ^ j) : ℝ) * (μ (p ^ (k + 1) / p ^ j) : ℝ)
        = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj := Finset.mem_range.mp hj
      rw [Nat.pow_div (by omega) hp.pos,
        ArithmeticFunction.moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
      simp
    rw [hzero, zero_add, Nat.pow_div (by omega) hp.pos, Nat.pow_div le_rfl hp.pos,
      show k + 1 - k = 1 by omega, Nat.sub_self, pow_one, pow_zero,
      ArithmeticFunction.moebius_apply_prime hp, ArithmeticFunction.moebius_apply_one,
      Nat.totient_prime_pow_succ hp]
    unfold psiloc
    have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp only [pow_zero, one_mul, Nat.totient_one, if_true, Nat.cast_sub hp.one_le,
        Nat.cast_one, Int.cast_neg, Int.cast_one]
      field_simp; ring
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      rw [if_neg (by omega), Nat.totient_prime_pow_succ hp]
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hp.one_le, Nat.cast_one, Int.cast_neg,
        Int.cast_one]
      field_simp; ring
  have := congrArg (fun f : ArithmeticFunction ℝ => f n) hFG
  simp only [F, G] at this
  rw [toAF_apply _ (by omega), toAF_apply _ (by omega)] at this
  rw [← this]
  exact phiStar_eq_real n hn

lemma fS_eq_psi (S : Finset ℕ) (n : ℕ) (h : ∀ p ∈ n.primeFactors, p ∈ S) :
    fS S n = locProd psiloc n := by
  unfold fS locProd
  refine Finset.prod_congr rfl fun p hp => ?_
  unfold fSpp psiloc
  rw [if_pos (h p hp)]

lemma H_eq (W : Weight) (Q : ℝ) : W.H Q = ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊,
    W.w (q / Q) * q * ∑ d ∈ q.divisors, gS (Finset.range (⌊Q⌋₊ + 1)) d := by
  unfold Weight.H Weight.omega
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq1 := (Finset.mem_Icc.mp hq).1
  have hqN := (Finset.mem_Icc.mp hq).2
  have hφ : (Nat.totient q : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hq1).ne'
  rw [phiStar_eq_mul q hq1, ← fS_eq_psi (Finset.range (⌊Q⌋₊ + 1)) q (fun p hp => by
      rw [Finset.mem_range]; have := Nat.le_of_mem_primeFactors hp; omega),
    lemfS_ii_conv _ q hq1]
  field_simp

/-- `|g_S(d)| = gabs_S(d) √d` (`d ≥ 1`). -/
lemma abs_gS_eq (S : Finset ℕ) {d : ℕ} (hd : 1 ≤ d) : |gS S d| = gabs S d * Real.sqrt d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  unfold gabs
  rw [Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add hd0]; norm_num

/-- `∑_{d≤N} |g_S(d)| ≤ B √N`. -/
lemma sum_abs_gS_le (S : Finset ℕ) (N : ℕ) :
    ∑ d ∈ Finset.Icc 1 N, |gS S d| ≤ Bconst * Real.sqrt N := by
  calc ∑ d ∈ Finset.Icc 1 N, |gS S d| ≤ ∑ d ∈ Finset.Icc 1 N, gabs S d * Real.sqrt N := by
        refine Finset.sum_le_sum fun d hd => ?_
        rw [abs_gS_eq S (Finset.mem_Icc.mp hd).1]
        exact mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt (by exact_mod_cast (Finset.mem_Icc.mp hd).2)) (gabs_nonneg S d)
    _ = (∑ d ∈ Finset.Icc 1 N, gabs S d) * Real.sqrt N := by rw [Finset.sum_mul]
    _ ≤ Bconst * Real.sqrt N := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
        exact ((summable_gabs S).sum_le_tsum _ fun d _ => gabs_nonneg S d).trans
          (tsum_gabs_le_Bconst S)

/-- `|∑_{d≤N} g_S(d)/d − ℰ| ≤ B/√(N+1)`. -/
lemma gS_partial_le (S : Finset ℕ) (N : ℕ) :
    |∑ d ∈ Finset.Icc 1 N, gS S d / d - Ecal| ≤ Bconst / Real.sqrt (N + 1) := by
  set f : ℕ → ℝ := fun d => gS S d / d
  have hf := lemfS_ii_euler S
  have key : ∑ d ∈ Finset.Icc 1 N, f d - Ecal = -∑' i, f (i + (N + 1)) := by
    rw [sum_Icc_eq_tsum_sub f hf.summable (by simp [f]) N, hf.tsum_eq]; ring
  rw [key, abs_neg]
  have hN1 : (0 : ℝ) < Real.sqrt (N + 1) := Real.sqrt_pos.mpr (by positivity)
  have hs := (summable_nat_add_iff (N + 1)).mpr (summable_gabs S)
  have hle : ∀ i : ℕ, ‖f (i + (N + 1))‖ ≤ gabs S (i + (N + 1)) / Real.sqrt (N + 1) := by
    intro i
    have hd : 1 ≤ i + (N + 1) := by omega
    have hd0 : (0 : ℝ) < ((i + (N + 1) : ℕ) : ℝ) := by exact_mod_cast hd
    simp only [f, Real.norm_eq_abs, abs_div, Nat.abs_cast]
    rw [abs_gS_eq S hd]
    have hsq : Real.sqrt (N + 1) ≤ Real.sqrt ((i + (N + 1) : ℕ) : ℝ) :=
      Real.sqrt_le_sqrt (by push_cast; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])
    have hsd : Real.sqrt ((i + (N + 1) : ℕ) : ℝ) * Real.sqrt ((i + (N + 1) : ℕ) : ℝ) =
        ((i + (N + 1) : ℕ) : ℝ) := Real.mul_self_sqrt hd0.le
    rw [div_le_div_iff₀ hd0 hN1]
    have hg := gabs_nonneg S (i + (N + 1))
    calc gabs S (i + (N + 1)) * Real.sqrt ((i + (N + 1) : ℕ) : ℝ) * Real.sqrt (N + 1)
        ≤ gabs S (i + (N + 1)) * Real.sqrt ((i + (N + 1) : ℕ) : ℝ) *
            Real.sqrt ((i + (N + 1) : ℕ) : ℝ) := by gcongr
      _ = gabs S (i + (N + 1)) * ((i + (N + 1) : ℕ) : ℝ) := by rw [mul_assoc, hsd]
  have hs' : Summable fun i : ℕ => gabs S (i + (N + 1)) / Real.sqrt (N + 1) := hs.div_const _
  calc |∑' i, f (i + (N + 1))| ≤ ∑' i, ‖f (i + (N + 1))‖ :=
        norm_tsum_le_tsum_norm (hs'.of_nonneg_of_le (fun _ => norm_nonneg _) hle)
    _ ≤ ∑' i, gabs S (i + (N + 1)) / Real.sqrt (N + 1) :=
        (hs'.of_nonneg_of_le (fun _ => norm_nonneg _) hle).tsum_le_tsum hle hs'
    _ = (∑' i, gabs S (i + (N + 1))) / Real.sqrt (N + 1) := tsum_div_const
    _ ≤ Bconst / Real.sqrt (N + 1) := by
        refine div_le_div_of_nonneg_right ?_ hN1.le
        have := (summable_gabs S).sum_add_tsum_nat_add (N + 1)
        have h0 : 0 ≤ ∑ i ∈ Finset.range (N + 1), gabs S i :=
          Finset.sum_nonneg fun i _ => gabs_nonneg S i
        linarith [tsum_gabs_le_Bconst S]

/-- **`lem:WH`, `H`:** `|H − ℰ I_w Q²| ≤ 8 V_w Q^{3/2}` for `Q ≥ 2`. -/
theorem H_bound (W : Weight) (Q : ℝ) (hQ : 2 ≤ Q) :
    |W.H Q - Ecal * W.Iw * Q ^ 2| ≤ 8 * W.Vw * Q ^ (3 / 2 : ℝ) := by
  have hQ0 : 0 < Q := by linarith
  set N := ⌊Q⌋₊ with hNdef
  set S := Finset.range (N + 1)
  have hNQ : (N : ℝ) ≤ Q := Nat.floor_le hQ0.le
  have hQN : Q < (N : ℝ) + 1 := Nat.lt_floor_add_one Q
  have hV := Vw_nonneg W
  have hI := Iw_le_half_Vw W
  have hI0 : 0 ≤ W.Iw := W.Iw_pos.le
  have hB := Bconst_lt
  have hB0 : 0 ≤ Bconst := le_trans zero_le_one one_le_Bconst
  have hgen := mass_general W Q hQ0 (gS S)
  rw [← H_eq] at hgen
  have hg1 := sum_abs_gS_le S N
  have hg2 := gS_partial_le S N
  have hsQ : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ0
  have hsqQ : Real.sqrt Q * Real.sqrt Q = Q := Real.mul_self_sqrt hQ0.le
  have hsN : Real.sqrt N ≤ Real.sqrt Q := Real.sqrt_le_sqrt hNQ
  have hsN1 : Real.sqrt Q ≤ Real.sqrt (N + 1) := Real.sqrt_le_sqrt hQN.le
  have hpow : Q ^ (3 / 2 : ℝ) = Q * Real.sqrt Q := by
    rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hQ0,
      Real.rpow_one]
  rw [hpow]
  set SN := ∑ d ∈ Finset.Icc 1 N, gS S d / d
  have e : W.H Q - Ecal * W.Iw * Q ^ 2 = (W.H Q - Q ^ 2 * W.Iw * SN) +
      Q ^ 2 * W.Iw * (SN - Ecal) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ Q ^ 2 * W.Iw)]
  have t1 : |W.H Q - Q ^ 2 * W.Iw * SN| ≤ Q * (3 / 2 * W.Vw) * (Bconst * Real.sqrt Q) :=
    hgen.trans (mul_le_mul_of_nonneg_left (hg1.trans
      (mul_le_mul_of_nonneg_left hsN hB0)) (by positivity))
  have t2 : Q ^ 2 * W.Iw * |SN - Ecal| ≤ Q ^ 2 * (W.Vw / 2) * (Bconst / Real.sqrt Q) := by
    calc Q ^ 2 * W.Iw * |SN - Ecal| ≤ Q ^ 2 * W.Iw * (Bconst / Real.sqrt (N + 1)) :=
          mul_le_mul_of_nonneg_left hg2 (by positivity)
      _ ≤ Q ^ 2 * (W.Vw / 2) * (Bconst / Real.sqrt Q) := by
          gcongr
  have hQ2 : Q ^ 2 / Real.sqrt Q = Q * Real.sqrt Q := by
    rw [div_eq_iff hsQ.ne', mul_assoc, hsqQ]; ring
  have e2 : Q ^ 2 * (W.Vw / 2) * (Bconst / Real.sqrt Q) = W.Vw / 2 * Bconst * (Q * Real.sqrt Q) := by
    rw [← hQ2]; ring
  rw [e2] at t2
  have hQs : 0 ≤ W.Vw * (Q * Real.sqrt Q) := by positivity
  have e1 : Q * (3 / 2 * W.Vw) * (Bconst * Real.sqrt Q) = 3 / 2 * Bconst * (W.Vw * (Q * Real.sqrt Q)) := by
    ring
  rw [e1] at t1
  nlinarith

/-! ### `lem:WH` -/

/-- **`lem:WH`**, sorry-free, with `c₀ = 8`. -/
theorem lemWH_proof : lemWH_Statement := by
  refine ⟨8, fun W Q hQ => ⟨?_, H_bound W Q hQ⟩⟩
  have h := Wm_bound W Q hQ
  have hV := Vw_nonneg W
  have hl : 0 ≤ Real.log (2 * Q) := Real.log_nonneg (by linarith)
  have : 0 ≤ W.Vw * Q * Real.log (2 * Q) := by
    have : 0 ≤ Q := by linarith
    positivity
  nlinarith

end Families.Phase2.B
