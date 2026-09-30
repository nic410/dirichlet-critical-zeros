/-
# `lem:Omega` (d), (e)  (Lemma 6.15 and its proof)

* `lemOmega_d_proof : lemOmega_d_Statement` — if `w̃ ≡ c` on `[η,1]`: `m = 0` on `[η,∞)` and `Ω(e) > 0` for
  `ηQ ≤ e ≤ Q`. The TeX uses `σ₀⁻ < 1`; we use the proved tail bound `∑_{r≥2} 1/(r²φ(r)) ≤ 3/4`, and `c > 0`
  (else `w ≡ 0`, contradicting `I_w > 0`).
* `lemOmega_e_proof : lemOmega_e_Statement` — if `w̃(u) = h(log 1/u)` with `h` `L`-Lipschitz, then
  `m̃(u) ≤ L σ₁⁻` (for every `u > 0`; the TeX states it for `u ≥ η`).
* `summable_sigma1m`, `sigma1m_nonneg`, `sum_le_sigma1m`; `sigma0m_le` (`σ₀⁻ ≤ 3/4`).
-/
import Families.Phase1.B.Omega

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius
open ArithmeticFunction Finset

namespace Families.Phase1.B

open Families

/-! ### A lower bound for `Ω(e)` (the chain in the proof of `lem:Omega`(b)) -/

/-- `Ω(e) ≥ w(e/Q) − ∑_{r ≤ Q, μ(r)=−1, (r,e)=1} w(er/Q)/φ(r)` when `1 ≤ e ≤ Q`. -/
lemma Ωlev_ge (W : Weight) (Q : ℝ) (e : ℕ) (he : 1 ≤ e) (heQ : (e : ℝ) ≤ Q) :
    W.w ((e : ℝ) / Q) -
        ∑ r ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter (fun r : ℕ => Squarefree r ∧ Nat.Coprime r e)).filter
          (fun r => μ r = -1), W.w ((e : ℝ) / Q * r) / Nat.totient r
      ≤ Ωlev W Q e := by
  rw [Ωlev_eq_second_form W Q e he]
  set F := (Finset.Icc 1 ⌊Q⌋₊).filter (fun r : ℕ => Squarefree r ∧ Nat.Coprime r e) with hF
  have hQ1 : 1 ≤ ⌊Q⌋₊ := Nat.le_floor (by push_cast; linarith [(by exact_mod_cast he : (1 : ℝ) ≤ e)])
  have harg : ∀ r : ℕ, ((e * r : ℕ) : ℝ) / Q = (e : ℝ) / Q * r := fun r => by push_cast; ring
  rw [← Finset.sum_filter_add_sum_filter_not F (fun r => μ r = -1)]
  have hneg : ∑ r ∈ F.filter (fun r => μ r = -1), (μ r : ℝ) / Nat.totient r * W.w ((e * r : ℕ) / Q)
      = -∑ r ∈ F.filter (fun r => μ r = -1), W.w ((e : ℝ) / Q * r) / Nat.totient r := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [(Finset.mem_filter.mp hr).2, harg]; push_cast; ring
  have hpos : W.w ((e : ℝ) / Q) ≤
      ∑ r ∈ F.filter (fun r => ¬ μ r = -1), (μ r : ℝ) / Nat.totient r * W.w ((e * r : ℕ) / Q) := by
    have hnn : ∀ r ∈ F.filter (fun r => ¬ μ r = -1),
        0 ≤ (μ r : ℝ) / Nat.totient r * W.w ((e * r : ℕ) / Q) := by
      intro r hr
      obtain ⟨hrF, hne⟩ := Finset.mem_filter.mp hr
      have hsq := (Finset.mem_filter.mp hrF).2.1
      have h1 : μ r = 1 := by
        have := (moebius_ne_zero_iff_eq_or (n := r)).mp (moebius_ne_zero_iff_squarefree.mpr hsq)
        tauto
      rw [h1]
      exact mul_nonneg (div_nonneg (by norm_num) (Nat.cast_nonneg _)) (W.nonneg _)
    have hmem : 1 ∈ F.filter (fun r => ¬ μ r = -1) := by
      rw [Finset.mem_filter, hF, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨⟨le_rfl, hQ1⟩, squarefree_one, Nat.coprime_one_left e⟩, ?_⟩
      rw [moebius_apply_one]; decide
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum hnn hmem)
    simp
  linarith

/-! ### `lem:Omega` (d) -/

/-- **`lem:Omega`(d)** (Lemma 6.15). -/
theorem lemOmega_d_proof : lemOmega_d_Statement := by
  intro W ⟨c, hc⟩
  have hη := W.η_pos
  have hη1 : W.η < 1 := by linarith [W.η_lt_half]
  -- `c ≥ 0` and `w(v) ≤ c v⁻²` for `v ≥ η`
  have hc0 : 0 ≤ c := by
    rw [← hc W.η le_rfl hη1.le]; unfold Weight.wt; exact mul_nonneg (sq_nonneg _) (W.nonneg _)
  have hweq : ∀ v, W.η ≤ v → v ≤ 1 → W.w v = c * v⁻¹ ^ 2 := by
    intro v h1 h2
    have hv : 0 < v := by linarith
    have := hc v h1 h2
    unfold Weight.wt at this
    rw [← this]; field_simp
  have hwle : ∀ v, W.η ≤ v → W.w v ≤ c * v⁻¹ ^ 2 := by
    intro v h1
    by_cases h2 : v ≤ 1
    · exact (hweq v h1 h2).le
    · have : W.w v = 0 := by
        by_contra hne; exact h2 (W.supp v hne).2
      rw [this]; positivity
  -- `c > 0`: otherwise `w ≡ 0` and `I_w = 0`
  have hcpos : 0 < c := by
    rcases hc0.lt_or_eq with h | h
    · exact h
    · exfalso
      have hw0 : ∀ v, W.w v = 0 := by
        intro v
        by_contra hne
        obtain ⟨h1, h2⟩ := W.supp v hne
        have := hweq v h1 h2
        rw [← h, zero_mul] at this
        exact hne this
      have := W.Iw_pos
      simp [hw0] at this
  -- the sum over `μ(r) = −1` at `u ≥ η`
  have hsum : ∀ (u : ℝ), W.η ≤ u → ∀ s : Finset ℕ, (∀ r ∈ s, 2 ≤ r) →
      ∑ r ∈ s, W.w (u * r) / Nat.totient r ≤ 3 / 4 * (c * u⁻¹ ^ 2) := by
    intro u hu s hs
    have hu0 : 0 < u := by linarith
    have h1 : ∑ r ∈ s, W.w (u * r) / Nat.totient r ≤
        ∑ r ∈ s, c * u⁻¹ ^ 2 * (1 / ((r : ℝ) ^ 2 * Nat.totient r)) := by
      refine Finset.sum_le_sum fun r hr => ?_
      have hr1 : 1 ≤ r := le_trans (by norm_num) (hs r hr)
      have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
      have hφ := totient_pos_real hr1
      have hur : W.η ≤ u * r := by
        have : (1 : ℝ) ≤ r := by exact_mod_cast hr1
        nlinarith
      calc W.w (u * r) / Nat.totient r ≤ c * (u * r)⁻¹ ^ 2 / Nat.totient r :=
            div_le_div_of_nonneg_right (hwle _ hur) hφ.le
        _ = c * u⁻¹ ^ 2 * (1 / ((r : ℝ) ^ 2 * Nat.totient r)) := by field_simp
    have h2 := sum_inv_sq_totient_le_of_ge 2 (by norm_num) s hs
    rw [← Finset.mul_sum] at h1
    have h4 : (3 : ℝ) / ((2 : ℕ) : ℝ) ^ 2 = 3 / 4 := by norm_num
    rw [h4] at h2
    have : 0 ≤ c * u⁻¹ ^ 2 := by positivity
    nlinarith
  refine ⟨fun u hu => ?_, fun Q hQ e he1 he2 => ?_⟩
  · -- `m(u) = 0`
    have hu0 : 0 < u := by linarith
    unfold mfun
    apply max_eq_right
    rw [sub_nonpos]
    set G := (Finset.Icc 1 ⌊1 / u⌋₊).filter (fun r : ℕ => μ r = -1)
    have hG : ∀ r ∈ G, 2 ≤ r := fun r hr =>
      two_le_of_moebius_eq_neg_one (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1
        (Finset.mem_filter.mp hr).2
    by_cases hu1 : u ≤ 1
    · rw [hweq u hu hu1]
      have := hsum u hu G hG
      have : 0 ≤ c * u⁻¹ ^ 2 := by positivity
      linarith
    · -- `u > 1`: every `u r > 1`, so all terms vanish
      have hz : ∑ r ∈ G, W.w (u * r) / Nat.totient r = 0 := by
        refine Finset.sum_eq_zero fun r hr => ?_
        have hr1 : (1 : ℝ) ≤ r := by
          exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1
        have : W.w (u * r) = 0 := by
          by_contra hne; have := (W.supp _ hne).2; nlinarith
        rw [this, zero_div]
      rw [hz]; exact W.nonneg u
  · -- `Ω(e) > 0`
    have hQpos := hQ
    have heη : 0 < (e : ℝ) := lt_of_lt_of_le (mul_pos hη hQ) he1
    have he : 1 ≤ e := by exact_mod_cast heη
    have hu : W.η ≤ (e : ℝ) / Q := by rw [le_div_iff₀ hQ]; exact he1
    have hu1 : (e : ℝ) / Q ≤ 1 := by rw [div_le_one hQ]; exact he2
    have hlow := Ωlev_ge W Q e he he2
    have hG : ∀ r ∈ ((Finset.Icc 1 ⌊Q⌋₊).filter
        (fun r : ℕ => Squarefree r ∧ Nat.Coprime r e)).filter (fun r => μ r = -1), 2 ≤ r :=
      fun r hr => two_le_of_moebius_eq_neg_one
        (Finset.mem_Icc.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).1).1
        (Finset.mem_filter.mp hr).2
    have := hsum ((e : ℝ) / Q) hu _ hG
    rw [hweq _ hu hu1] at hlow
    have hpos : 0 < c * ((e : ℝ) / Q)⁻¹ ^ 2 := by positivity
    linarith

/-! ### `σ₁⁻` -/

lemma sigma1m_term_nonneg (r : ℕ) :
    0 ≤ (if μ r = -1 then Real.log r / ((r : ℝ) ^ 2 * Nat.totient r) else 0) := by
  split_ifs
  · exact div_nonneg (Real.log_natCast_nonneg r) (by positivity)
  · exact le_rfl

lemma sigma1m_term_le (r : ℕ) :
    (if μ r = -1 then Real.log r / ((r : ℝ) ^ 2 * Nat.totient r) else 0) ≤
      2 * ((r : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
  split_ifs with h
  · have hr1 : 1 ≤ r := by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · subst h0; simp at h
      · exact h0
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
    have hφ : (1 : ℝ) ≤ Nat.totient r := by exact_mod_cast Nat.totient_pos.mpr hr1
    have hlog : Real.log r ≤ (r : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) :=
      Real.log_le_rpow_div hr0.le (by norm_num)
    have h32 : (r : ℝ) ^ (3 / 2 : ℝ) = (r : ℝ) ^ 2 / (r : ℝ) ^ (1 / 2 : ℝ) := by
      rw [eq_div_iff (by positivity), ← Real.rpow_natCast, ← Real.rpow_add hr0]; norm_num
    rw [h32, inv_div]
    have hs : 0 < (r : ℝ) ^ (1 / 2 : ℝ) := by positivity
    calc Real.log r / ((r : ℝ) ^ 2 * Nat.totient r) ≤ Real.log r / ((r : ℝ) ^ 2 * 1) := by
          apply div_le_div_of_nonneg_left (Real.log_natCast_nonneg r) (by positivity)
          exact mul_le_mul_of_nonneg_left hφ (by positivity)
      _ ≤ ((r : ℝ) ^ (1 / 2 : ℝ) / (1 / 2)) / ((r : ℝ) ^ 2 * 1) :=
          div_le_div_of_nonneg_right hlog (by positivity)
      _ = 2 * ((r : ℝ) ^ (1 / 2 : ℝ) / (r : ℝ) ^ 2) := by ring
  · positivity

lemma summable_sigma1m :
    Summable fun r : ℕ => if μ r = -1 then Real.log r / ((r : ℝ) ^ 2 * Nat.totient r) else 0 := by
  have hs : Summable fun r : ℕ => 2 * ((r : ℝ) ^ (3 / 2 : ℝ))⁻¹ :=
    (Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left 2
  exact hs.of_nonneg_of_le sigma1m_term_nonneg sigma1m_term_le

lemma sigma1m_nonneg : 0 ≤ sigma1m := tsum_nonneg sigma1m_term_nonneg

/-- Partial sums of `σ₁⁻`. -/
lemma sum_le_sigma1m (s : Finset ℕ) (hs : ∀ r ∈ s, μ r = -1) :
    ∑ r ∈ s, Real.log r / ((r : ℝ) ^ 2 * Nat.totient r) ≤ sigma1m := by
  have h := summable_sigma1m.sum_le_tsum s (fun r _ => sigma1m_term_nonneg r)
  refine le_trans (le_of_eq ?_) h
  exact Finset.sum_congr rfl fun r hr => by rw [if_pos (hs r hr)]

/-! ### `lem:Omega` (e) -/

/-- **`lem:Omega`(e)** (Lemma 6.15 and its proof). -/
theorem lemOmega_e_proof : lemOmega_e_Statement := by
  intro W h Lh hLip hwt u hu
  have hη := W.η_pos
  have hu0 : 0 < u := by linarith
  set y := Real.log (1 / u) with hy
  set G := (Finset.Icc 1 ⌊1 / u⌋₊).filter (fun r : ℕ => μ r = -1) with hGdef
  have hG1 : ∀ r ∈ G, 1 ≤ r := fun r hr => (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1
  have hG2 : ∀ r ∈ G, 2 ≤ r := fun r hr =>
    two_le_of_moebius_eq_neg_one (hG1 r hr) (Finset.mem_filter.mp hr).2
  -- `h ≥ 0` at `y`: `h(y) = w̃(u) ≥ 0`
  have hhy : h y = W.wt u := (hwt u hu0).symm
  have hwtu : 0 ≤ W.wt u := by unfold Weight.wt; exact mul_nonneg (sq_nonneg _) (W.nonneg _)
  -- `u² w(ur)/φ(r) = h(y − log r)/(r²φ(r)) ≤ (h(y) + L log r)/(r²φ(r))`
  have hterm : ∀ r ∈ G, u ^ 2 * (W.w (u * r) / Nat.totient r) ≤
      h y * (1 / ((r : ℝ) ^ 2 * Nat.totient r)) +
        Lh * (Real.log r / ((r : ℝ) ^ 2 * Nat.totient r)) := by
    intro r hr
    have hr1 := hG1 r hr
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
    have hφ := totient_pos_real hr1
    have hur : 0 < u * r := mul_pos hu0 hr0
    have hwur : W.wt (u * r) = h (y - Real.log r) := by
      rw [hwt _ hur, hy, one_div, one_div, Real.log_inv, Real.log_inv, Real.log_mul hu0.ne'
        hr0.ne']
      ring_nf
    have hlip : h (y - Real.log r) ≤ h y + Lh * Real.log r := by
      have := hLip.dist_le_mul (y - Real.log r) y
      rw [Real.dist_eq, Real.dist_eq, show y - Real.log r - y = -Real.log r by ring, abs_neg,
        abs_of_nonneg (Real.log_natCast_nonneg r)] at this
      linarith [le_abs_self (h (y - Real.log r) - h y)]
    have e1 : u ^ 2 * (W.w (u * r) / Nat.totient r) =
        W.wt (u * r) / ((r : ℝ) ^ 2 * Nat.totient r) := by
      unfold Weight.wt; field_simp
    rw [e1, hwur]
    calc h (y - Real.log r) / ((r : ℝ) ^ 2 * Nat.totient r)
        ≤ (h y + Lh * Real.log r) / ((r : ℝ) ^ 2 * Nat.totient r) :=
          div_le_div_of_nonneg_right hlip (by positivity)
      _ = _ := by ring
  have hsum : u ^ 2 * ∑ r ∈ G, W.w (u * r) / Nat.totient r ≤ h y * (3 / 4) + Lh * sigma1m := by
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h1 := sum_inv_sq_totient_le_of_ge 2 (by norm_num) G hG2
    have h4 : (3 : ℝ) / ((2 : ℕ) : ℝ) ^ 2 = 3 / 4 := by norm_num
    rw [h4] at h1
    have h2 := sum_le_sigma1m G fun r hr => (Finset.mem_filter.mp hr).2
    have hhy0 : 0 ≤ h y := by rw [hhy]; exact hwtu
    have hL0 : (0 : ℝ) ≤ Lh := Lh.2
    have := mul_le_mul_of_nonneg_left h1 hhy0
    have := mul_le_mul_of_nonneg_left h2 hL0
    linarith
  -- conclude
  unfold mt mfun
  have hL0 : (0 : ℝ) ≤ Lh := Lh.2
  have hσ := sigma1m_nonneg
  rw [mul_max_of_nonneg _ _ (sq_nonneg u), mul_zero]
  refine max_le ?_ (by positivity)
  have hwu : u ^ 2 * W.w u = h y := by rw [hhy]; rfl
  rw [mul_sub, hwu]
  have hhy0 : 0 ≤ h y := by rw [hhy]; exact hwtu
  linarith

end Families.Phase1.B
