/-
# `lem:Omega` (a), (c)  (Lemma 6.15)

* `sum_Icc_inv_sq_totient_le` — the tail bound `∑_{a ≤ r ≤ N} 1/(r²φ(r)) ≤ 3/a²` (`a ≥ 1`), and its
  real-`y` form `sum_inv_sq_totient_le_of_real` (`≤ 3/y²` over any finite set of `r ≥ max(1,y)`).
  The TeX proves `∑_{r≥y} μ²(r)/(r²φ(r)) ≤ 3y⁻²` via `1/(r²φ(r)) = r⁻³∑_{d∣r}μ²(d)/φ(d)` and
  `ζ(2)ζ(3)/ζ(6) ≤ 2`; here we use instead an Abel-summation induction against the (proved)
  `sum_div_totient_le` (`∑_{j≤N} j/φ(j) ≤ 2N`, whose proof is that same Euler product), which gives
  `2/a² + 2∑_{r>a} r⁻³ ≤ 3/a²` for all `r` (squarefree or not), i.e. the same constant `3`.
* `wt_le_wtmax`, `wtmax_nonneg`, `w_le_wtmax_div_sq` — `w̃ ≤ ‖w̃‖_∞`, `w(v) ≤ ‖w̃‖_∞ v⁻²`.
* `lemOmega_ac_proof : lemOmega_ac_Statement` — **`lem:Omega`(a),(c)**.
-/
import Families.LemmaC
import Families.LemmaS
import Families.Schur
import Families.Weights

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius
open ArithmeticFunction Finset

namespace Families.Phase1.B

open Families

/-! ### The tail `∑_{r ≥ a} 1/(r²φ(r)) ≤ 3/a²` -/

/-- `A(N) = ∑_{j ≤ N} j/φ(j)`. -/
def Aphi (N : ℕ) : ℝ := ∑ j ∈ Finset.Icc 1 N, (j : ℝ) / Nat.totient j

lemma Aphi_succ (N : ℕ) : Aphi (N + 1) = Aphi N + ((N + 1 : ℕ) : ℝ) / Nat.totient (N + 1) := by
  unfold Aphi
  rw [Finset.sum_Icc_succ_top (by omega)]

lemma Aphi_nonneg (N : ℕ) : 0 ≤ Aphi N :=
  Finset.sum_nonneg fun _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma Aphi_le (N : ℕ) : Aphi N ≤ 2 * N := sum_div_totient_le N

lemma totient_pos_real {r : ℕ} (hr : 1 ≤ r) : (0 : ℝ) < Nat.totient r := by
  exact_mod_cast Nat.totient_pos.mpr (by omega)

/-- The Abel-summation invariant: for `1 ≤ a ≤ N`,
`∑_{a≤r≤N} 1/(r²φ(r)) + (2N − A(N))/N³ + A(a−1)/a³ ≤ 3/a² − 1/N²`. -/
lemma tail_invariant (a : ℕ) (ha : 1 ≤ a) (N : ℕ) (hN : a ≤ N) :
    ∑ r ∈ Finset.Icc a N, (1 : ℝ) / ((r : ℝ) ^ 2 * Nat.totient r)
      + (2 * N - Aphi N) / (N : ℝ) ^ 3 + Aphi (a - 1) / (a : ℝ) ^ 3
      ≤ 3 / (a : ℝ) ^ 2 - 1 / (N : ℝ) ^ 2 := by
  induction N, hN using Nat.le_induction with
  | base =>
    rw [Finset.Icc_self, Finset.sum_singleton]
    have hA : Aphi a = Aphi (a - 1) + (a : ℝ) / Nat.totient a := by
      obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
      rw [Aphi_succ, Nat.add_sub_cancel]
    rw [hA]
    have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
    have hφ := totient_pos_real ha
    field_simp
    ring_nf
    exact le_refl _
  | succ N hN ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Aphi_succ]
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast le_trans ha hN
    have hn0 : (0 : ℝ) < N := by linarith
    have hφ := totient_pos_real (show 1 ≤ N + 1 by omega)
    set D := 2 * (N : ℝ) - Aphi N with hD
    have hD0 : 0 ≤ D := by rw [hD]; linarith [Aphi_le N]
    set b := ((N + 1 : ℕ) : ℝ) / Nat.totient (N + 1) with hb
    have hcast : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    have ht : (1 : ℝ) / (((N + 1 : ℕ) : ℝ) ^ 2 * Nat.totient (N + 1)) = b / ((N : ℝ) + 1) ^ 3 := by
      rw [hb, hcast]
      field_simp
    have hnew : (2 * ((N + 1 : ℕ) : ℝ) - (Aphi N + b)) = D + 2 - b := by
      rw [hcast, hD]; ring
    rw [ht, hnew, hcast]
    -- the increment of the left side is at most `2/(N+1)³`
    have h1 : D / ((N : ℝ) + 1) ^ 3 ≤ D / (N : ℝ) ^ 3 :=
      div_le_div_of_nonneg_left hD0 (by positivity) (by gcongr; linarith)
    have h2 : 2 / ((N : ℝ) + 1) ^ 3 ≤ 1 / (N : ℝ) ^ 2 - 1 / ((N : ℝ) + 1) ^ 2 := by
      rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
        (by positivity)]
      nlinarith [sq_nonneg (N : ℝ), mul_pos hn0 hn0, mul_pos (mul_pos hn0 hn0) hn0]
    have h3 : b / ((N : ℝ) + 1) ^ 3 + (D + 2 - b) / ((N : ℝ) + 1) ^ 3
        = D / ((N : ℝ) + 1) ^ 3 + 2 / ((N : ℝ) + 1) ^ 3 := by
      field_simp; ring
    linarith

/-- **Tail bound.** `∑_{a ≤ r ≤ N} 1/(r²φ(r)) ≤ 3/a²` for `a ≥ 1`. -/
theorem sum_Icc_inv_sq_totient_le (a N : ℕ) (ha : 1 ≤ a) :
    ∑ r ∈ Finset.Icc a N, (1 : ℝ) / ((r : ℝ) ^ 2 * Nat.totient r) ≤ 3 / (a : ℝ) ^ 2 := by
  by_cases hN : a ≤ N
  · have h := tail_invariant a ha N hN
    have hN1 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have h1 : 0 ≤ (2 * N - Aphi N) / (N : ℝ) ^ 3 :=
      div_nonneg (by linarith [Aphi_le N]) (by positivity)
    have h2 : 0 ≤ Aphi (a - 1) / (a : ℝ) ^ 3 := div_nonneg (Aphi_nonneg _) (by positivity)
    have h3 : 0 ≤ 1 / (N : ℝ) ^ 2 := by positivity
    linarith
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    positivity

/-- **Tail bound, any finite set.** If every `r ∈ s` satisfies `a ≤ r` (`a ≥ 1`), then
`∑_{r∈s} 1/(r²φ(r)) ≤ 3/a²`. -/
theorem sum_inv_sq_totient_le_of_ge (a : ℕ) (ha : 1 ≤ a) (s : Finset ℕ) (hs : ∀ r ∈ s, a ≤ r) :
    ∑ r ∈ s, (1 : ℝ) / ((r : ℝ) ^ 2 * Nat.totient r) ≤ 3 / (a : ℝ) ^ 2 := by
  refine le_trans ?_ (sum_Icc_inv_sq_totient_le a (s.sup id) ha)
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
  intro r hr
  rw [Finset.mem_Icc]
  exact ⟨hs r hr, Finset.le_sup (f := id) hr⟩

/-- **Tail bound, real threshold** (the TeX's `∑_{r≥y} μ²(r)/(r²φ(r)) ≤ 3y⁻²`, without `μ²`): if
`y > 0` and every `r ∈ s` satisfies `1 ≤ r` and `y ≤ r`, then `∑_{r∈s} 1/(r²φ(r)) ≤ 3/y²`. -/
theorem sum_inv_sq_totient_le_of_real (y : ℝ) (hy : 0 < y) (s : Finset ℕ)
    (hs : ∀ r ∈ s, 1 ≤ r ∧ y ≤ r) :
    ∑ r ∈ s, (1 : ℝ) / ((r : ℝ) ^ 2 * Nat.totient r) ≤ 3 / y ^ 2 := by
  set a := max 1 ⌈y⌉₊ with ha
  have ha1 : 1 ≤ a := le_max_left _ _
  have h := sum_inv_sq_totient_le_of_ge a ha1 s fun r hr => by
    obtain ⟨h1, h2⟩ := hs r hr
    exact max_le h1 (Nat.ceil_le.mpr h2)
  refine h.trans ?_
  have hya : y ≤ a := by
    rw [ha]; push_cast
    exact (Nat.le_ceil y).trans (le_max_right _ _)
  gcongr

/-! ### `w̃ ≤ ‖w̃‖_∞` -/

lemma wt_le_wmax (W : Weight) (u : ℝ) : W.wt u ≤ W.wmax := by
  unfold Weight.wt
  by_cases h : W.w u = 0
  · rw [h, mul_zero]; exact W.wmax_nonneg
  · obtain ⟨h1, h2⟩ := W.supp u h
    have hη := W.η_pos
    have hu2 : u ^ 2 ≤ 1 := by nlinarith
    calc u ^ 2 * W.w u ≤ 1 * W.w u := mul_le_mul_of_nonneg_right hu2 (W.nonneg u)
      _ = W.w u := one_mul _
      _ ≤ W.wmax := W.le_wmax u

lemma wt_bddAbove (W : Weight) : BddAbove (Set.range W.wt) :=
  ⟨W.wmax, by rintro _ ⟨u, rfl⟩; exact wt_le_wmax W u⟩

/-- `w̃(u) ≤ ‖w̃‖_∞`. -/
lemma wt_le_wtmax (W : Weight) (u : ℝ) : W.wt u ≤ W.wtmax :=
  le_csSup (wt_bddAbove W) ⟨u, rfl⟩

/-- `‖w̃‖_∞ ≥ 0`. -/
lemma wtmax_nonneg (W : Weight) : 0 ≤ W.wtmax := by
  have h := wt_le_wtmax W 0
  simpa [Weight.wt] using h

/-- `w(v) ≤ ‖w̃‖_∞ v⁻²` for `v > 0`. -/
lemma w_le_wtmax_div_sq (W : Weight) {v : ℝ} (hv : 0 < v) : W.w v ≤ W.wtmax * v⁻¹ ^ 2 := by
  have h := wt_le_wtmax W v
  unfold Weight.wt at h
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  linarith

/-! ### The weighted sums in `Ω` and `m` -/

/-- `∑_{r∈s} w(ur)/φ(r) ≤ ‖w̃‖_∞ u⁻² ∑_{r∈s, r ≥ η/u} 1/(r²φ(r))` (`u > 0`, all `r ∈ s` positive):
only `r` with `ur ≥ η` contribute, and `w(ur) ≤ ‖w̃‖_∞ (ur)⁻²`. -/
lemma sum_w_div_totient_le (W : Weight) {u : ℝ} (hu : 0 < u) (s : Finset ℕ)
    (hs : ∀ r ∈ s, 1 ≤ r) :
    ∑ r ∈ s, W.w (u * r) / Nat.totient r ≤
      W.wtmax * u⁻¹ ^ 2 *
        ∑ r ∈ s.filter (fun r : ℕ => W.η / u ≤ r), (1 : ℝ) / ((r : ℝ) ^ 2 * Nat.totient r) := by
  rw [Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_le_sum fun r hr => ?_
  have hr1 := hs r hr
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
  have hφ := totient_pos_real hr1
  split_ifs with hηr
  · have h := w_le_wtmax_div_sq W (mul_pos hu hr0)
    calc W.w (u * r) / Nat.totient r ≤ W.wtmax * (u * r)⁻¹ ^ 2 / Nat.totient r :=
          div_le_div_of_nonneg_right h hφ.le
      _ = W.wtmax * u⁻¹ ^ 2 * (1 / ((r : ℝ) ^ 2 * Nat.totient r)) := by
          field_simp
  · have hw : W.w (u * r) = 0 := by
      by_contra hne
      have h1 := (W.supp _ hne).1
      apply hηr
      rw [div_le_iff₀ hu]; linarith
    rw [hw, zero_div, mul_zero]

lemma sum_w_div_totient_nonneg (W : Weight) (u : ℝ) (s : Finset ℕ) :
    0 ≤ ∑ r ∈ s, W.w (u * r) / Nat.totient r :=
  Finset.sum_nonneg fun _ _ => div_nonneg (W.nonneg _) (Nat.cast_nonneg _)

/-! ### `lem:Omega` (a) -/

/-- **`lem:Omega`(a).** `|Ω(e)| ≤ 3‖w̃‖_∞ min{(Q/e)², η⁻²}`. -/
theorem lemOmega_a (W : Weight) (Q : ℝ) (hQ : 0 < Q) (e : ℕ) (he : 1 ≤ e) :
    |Ωlev W Q e| ≤ 3 * W.wtmax * min ((Q / e) ^ 2) (W.η⁻¹ ^ 2) := by
  rw [Ωlev_eq_second_form W Q e he]
  set F := (Finset.Icc 1 ⌊Q⌋₊).filter (fun r : ℕ => Squarefree r ∧ Nat.Coprime r e) with hF
  have hF1 : ∀ r ∈ F, 1 ≤ r := fun r hr =>
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1
  have he0 : (0 : ℝ) < e := by exact_mod_cast he
  set u : ℝ := (e : ℝ) / Q with hu
  have hu0 : 0 < u := div_pos he0 hQ
  have hwt := wtmax_nonneg W
  -- `|Ω(e)| ≤ ∑_{r∈F} w(ur)/φ(r)`
  have habs : |∑ r ∈ F, (μ r : ℝ) / Nat.totient r * W.w ((e * r : ℕ) / Q)|
      ≤ ∑ r ∈ F, W.w (u * r) / Nat.totient r := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r hr => ?_)
    have hφ := totient_pos_real (hF1 r hr)
    have hμ : |(μ r : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have harg : ((e * r : ℕ) : ℝ) / Q = u * r := by rw [hu]; push_cast; ring
    rw [harg, abs_mul, abs_div, abs_of_pos hφ, abs_of_nonneg (W.nonneg _)]
    calc |(μ r : ℝ)| / Nat.totient r * W.w (u * r) ≤ 1 / Nat.totient r * W.w (u * r) :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hμ hφ.le) (W.nonneg _)
      _ = W.w (u * r) / Nat.totient r := by ring
  refine habs.trans ((sum_w_div_totient_le W hu0 F hF1).trans ?_)
  set T := ∑ r ∈ F.filter (fun r : ℕ => W.η / u ≤ r), (1 : ℝ) / ((r : ℝ) ^ 2 * Nat.totient r)
  have hT1 : T ≤ 3 := by
    have := sum_inv_sq_totient_le_of_ge 1 le_rfl (F.filter (fun r : ℕ => W.η / u ≤ r))
      fun r hr => hF1 r (Finset.mem_filter.mp hr).1
    rw [Nat.cast_one, one_pow, div_one] at this
    exact this
  have hηu : 0 < W.η / u := div_pos W.η_pos hu0
  have hT2 : T ≤ 3 / (W.η / u) ^ 2 :=
    sum_inv_sq_totient_le_of_real (W.η / u) hηu _ fun r hr =>
      ⟨hF1 r (Finset.mem_filter.mp hr).1, (Finset.mem_filter.mp hr).2⟩
  have hinv : u⁻¹ ^ 2 = (Q / e) ^ 2 := by rw [hu, inv_div]
  rw [mul_min_of_nonneg _ _ (by positivity)]
  refine le_min ?_ ?_
  · rw [← hinv]
    calc W.wtmax * u⁻¹ ^ 2 * T ≤ W.wtmax * u⁻¹ ^ 2 * 3 := by gcongr
      _ = 3 * W.wtmax * u⁻¹ ^ 2 := by ring
  · calc W.wtmax * u⁻¹ ^ 2 * T ≤ W.wtmax * u⁻¹ ^ 2 * (3 / (W.η / u) ^ 2) := by gcongr
      _ = 3 * W.wtmax * W.η⁻¹ ^ 2 := by
          have := W.η_pos
          field_simp

/-! ### `lem:Omega` (c) -/

/-- Squarefree `r` with `μ(r) = −1` has `r ≥ 2`. -/
lemma two_le_of_moebius_eq_neg_one {r : ℕ} (hr : 1 ≤ r) (h : μ r = -1) : 2 ≤ r := by
  by_contra hlt
  have : r = 1 := by omega
  subst this
  rw [moebius_apply_one] at h
  norm_num at h

/-- **`lem:Omega`(c), first clause.** `m(u) ≤ 3‖w̃‖_∞ min{u⁻²/4, η⁻²}` for `u > 0`. -/
theorem lemOmega_c (W : Weight) (u : ℝ) (hu : 0 < u) :
    mfun W u ≤ 3 * W.wtmax * min (u⁻¹ ^ 2 / 4) (W.η⁻¹ ^ 2) := by
  set G := (Finset.Icc 1 ⌊1 / u⌋₊).filter (fun r : ℕ => μ r = -1) with hG
  have hG1 : ∀ r ∈ G, 1 ≤ r := fun r hr =>
    (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1
  have hG2 : ∀ r ∈ G, 2 ≤ r := fun r hr =>
    two_le_of_moebius_eq_neg_one (hG1 r hr) (Finset.mem_filter.mp hr).2
  have hwt := wtmax_nonneg W
  have hm : mfun W u ≤ ∑ r ∈ G, W.w (u * r) / Nat.totient r := by
    unfold mfun
    exact max_le (by linarith [W.nonneg u]) (sum_w_div_totient_nonneg W u G)
  refine hm.trans ((sum_w_div_totient_le W hu G hG1).trans ?_)
  set T := ∑ r ∈ G.filter (fun r : ℕ => W.η / u ≤ r), (1 : ℝ) / ((r : ℝ) ^ 2 * Nat.totient r)
  have hT1 : T ≤ 3 / 4 := by
    have := sum_inv_sq_totient_le_of_ge 2 (by norm_num) (G.filter (fun r : ℕ => W.η / u ≤ r))
      fun r hr => hG2 r (Finset.mem_filter.mp hr).1
    have h4 : (3 : ℝ) / ((2 : ℕ) : ℝ) ^ 2 = 3 / 4 := by norm_num
    rw [h4] at this
    exact this
  have hηu : 0 < W.η / u := div_pos W.η_pos hu
  have hT2 : T ≤ 3 / (W.η / u) ^ 2 :=
    sum_inv_sq_totient_le_of_real (W.η / u) hηu _ fun r hr =>
      ⟨hG1 r (Finset.mem_filter.mp hr).1, (Finset.mem_filter.mp hr).2⟩
  rw [mul_min_of_nonneg _ _ (by positivity)]
  refine le_min ?_ ?_
  · calc W.wtmax * u⁻¹ ^ 2 * T ≤ W.wtmax * u⁻¹ ^ 2 * (3 / 4) := by gcongr
      _ = 3 * W.wtmax * (u⁻¹ ^ 2 / 4) := by ring
  · calc W.wtmax * u⁻¹ ^ 2 * T ≤ W.wtmax * u⁻¹ ^ 2 * (3 / (W.η / u) ^ 2) := by gcongr
      _ = 3 * W.wtmax * W.η⁻¹ ^ 2 := by
          have := W.η_pos
          field_simp

/-- **`lem:Omega`(a),(c)** (Lemma 6.15). -/
theorem lemOmega_ac_proof : lemOmega_ac_Statement := fun W Q hQ =>
  ⟨fun e he => lemOmega_a W Q hQ e he, fun u hu => lemOmega_c W u hu,
    fun u hu => mfun_eq_zero_of_gt_half W u hu⟩

end Families.Phase1.B
