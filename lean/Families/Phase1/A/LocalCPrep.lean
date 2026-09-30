/-
Preparation for `lem:C` (`lemma-toeplitz-C.tex`, proof of `lem:C`).

* `lemfS_i_Statement`: part (i) of `lem:fS` (literally the first conjunct of `lemfS_Statement`);
  the only input from `lem:fS` that `lem:C` needs.
* The weights `w(r·)` of the measures `ν_r`, and `m_Q(u) = (∑_{r≤Q, μ(r)=−1} w(ur)/φ(r) − w(u))_+`:
  support in `(0,1]`, `m_Q(e/Q) = m(e/Q)`, `m_Q ≤ m`, `V_{m_Q} ≤ V_w(1 + ∑_{r≤Q}1/φ(r)) ≤ 3V_w(1+log Q)`.
* `natConv_decomp`: `μ^♮ * k_ς = ∑_{r≤Q sqfree} (μ(r)/φ(r)) (ν_r * k_ς) + (μ^m * k_ς)` ("Decomposition").
* `sum_rhoTwist_eq`: `∑_r (μ(r)/φ(r)) ρ_r(z) = Q² ℰ I_w R_S(t)`, `t = 1/(v|z|Q)` (by `lem:fS`(i)), as long
  as `v|z|Q ≤ Q` (then no `r > Q` occurs: the `r > Q` tail of the TeX vanishes identically).
* `rhoTwist_mQ_le`: `ρ_{m_Q}(z) ≤ Q² ℰ I_w R^m(t)`.
-/
import Families.Phase1.A.Count
import Families.Phase1.A.Arith
import Families.LemmaS
import Families.Constants

noncomputable section

open scoped BigOperators ENNReal ArithmeticFunction.Moebius
open Finset MeasureTheory Set

namespace Families.Phase1.A

open Families ArithmeticFunction

/-- **`lem:fS`(i)** (first conjunct of `lemfS_Statement`):
`f_S(n) = ∑_{kr=n, r sqfree} μ(r) G_S(k,r)/(rφ(r))`. -/
def lemfS_i_Statement : Prop :=
  ∀ (S : Finset ℕ) (n : ℕ), 1 ≤ n →
    fS S n = ∑ kr ∈ n.divisorsAntidiagonal.filter (fun kr => Squarefree kr.2),
      (μ kr.2 : ℝ) * GS S kr.1 kr.2 / (kr.2 * Nat.totient kr.2)

lemma lemfS_i_of_lemfS (h : lemfS_Statement) : lemfS_i_Statement := h.1

/-! ### The weight `w` and its dilates `w(r·)` -/

lemma W_zero_of_nonpos (W : Weight) {u : ℝ} (hu : u ≤ 0) : W.w u = 0 := by
  by_contra h; have := (W.supp u h).1; linarith [W.η_pos]

lemma W_zero_of_gt_one (W : Weight) {u : ℝ} (hu : 1 < u) : W.w u = 0 := by
  by_contra h; have := (W.supp u h).2; linarith

lemma W_supp01 (W : Weight) : ∀ u, W.w u ≠ 0 → 0 < u ∧ u ≤ 1 := fun u hu =>
  ⟨lt_of_lt_of_le W.η_pos (W.supp u hu).1, (W.supp u hu).2⟩

lemma w_dil_supp (W : Weight) {r : ℕ} (hr : 1 ≤ r) :
    ∀ u, W.w (r * u) ≠ 0 → 0 < u ∧ u ≤ 1 := by
  intro u hu
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  obtain ⟨h1, h2⟩ := W_supp01 W _ hu
  refine ⟨pos_of_mul_pos_right h1 (by linarith), ?_⟩
  nlinarith

lemma w_dil_var_le (W : Weight) (r : ℕ) :
    eVariationOn (fun u => W.w (r * u)) univ ≤ eVariationOn W.w univ :=
  eVariationOn_comp_mul_le W.w (Nat.cast_nonneg r)

lemma w_dil_bv (W : Weight) (r : ℕ) : BoundedVariationOn (fun u => W.w (r * u)) univ :=
  ne_top_of_le_ne_top W.bv (w_dil_var_le W r)

lemma w_dil_Vw_le (W : Weight) (r : ℕ) :
    (eVariationOn (fun u => W.w (r * u)) univ).toReal ≤ W.Vw :=
  ENNReal.toReal_mono W.bv (w_dil_var_le W r)

lemma Vw_nonneg (W : Weight) : 0 ≤ W.Vw := ENNReal.toReal_nonneg

/-! ### `m_Q` -/

/-- `m_Q(u) = (∑_{r≤Q, μ(r)=−1} w(ur)/φ(r) − w(u))_+`. -/
def mQ (W : Weight) (Q : ℝ) (u : ℝ) : ℝ :=
  max ((∑ r ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun r : ℕ => μ r = -1), W.w (u * r) / Nat.totient r)
    - W.w u) 0

lemma mQ_nonneg (W : Weight) (Q u : ℝ) : 0 ≤ mQ W Q u := le_max_right _ _

lemma mQ_supp (W : Weight) (Q : ℝ) : ∀ u, mQ W Q u ≠ 0 → 0 < u ∧ u ≤ 1 := by
  intro u hu
  by_contra hne
  apply hu
  unfold mQ
  have hw : W.w u = 0 := by
    rcases le_or_gt u 0 with h | h
    · exact W_zero_of_nonpos W h
    · exact W_zero_of_gt_one W (by by_contra h'; exact hne ⟨h, not_lt.mp h'⟩)
  have hs : ∑ r ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun r : ℕ => μ r = -1),
      W.w (u * r) / Nat.totient r = 0 := by
    refine Finset.sum_eq_zero fun r hr => ?_
    have hr1 : (1 : ℝ) ≤ r := by
      exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hr).1).1
    rcases le_or_gt u 0 with h | h
    · rw [W_zero_of_nonpos W (by nlinarith), zero_div]
    · have : 1 < u := by by_contra h'; exact hne ⟨h, not_lt.mp h'⟩
      rw [W_zero_of_gt_one W (by nlinarith), zero_div]
  rw [hs, hw, sub_zero, max_self]

/-- For `u > 0`, the terms `r > 1/u` of the `m`-sums vanish. -/
lemma sum_neg_one_filter_le (W : Weight) (A : Finset ℕ) {u : ℝ} (hu : 0 < u) :
    ∑ r ∈ A.filter (fun r : ℕ => μ r = -1), W.w (u * r) / Nat.totient r =
      ∑ r ∈ (A.filter (fun r : ℕ => μ r = -1)).filter (fun r => r ≤ ⌊1 / u⌋₊),
        W.w (u * r) / Nat.totient r := by
  refine (Finset.sum_filter_of_ne fun r _ hne => ?_).symm
  by_contra h
  apply hne
  have h1 : 1 / u < r := (Nat.floor_lt (by positivity)).mp (not_le.mp h)
  rw [div_lt_iff₀ hu] at h1
  rw [W_zero_of_gt_one W (by rw [mul_comm]; exact h1), zero_div]

lemma mQ_eq_mfun (W : Weight) {Q u : ℝ} (hu : 0 < u) (hQ : 1 / u ≤ Q) : mQ W Q u = mfun W u := by
  unfold mQ mfun
  congr 2
  rw [sum_neg_one_filter_le W _ hu, sum_neg_one_filter_le W _ hu]
  congr 1
  ext r
  simp only [Finset.mem_filter, Finset.mem_Icc]
  have := Nat.floor_le_floor (R := ℝ) hQ
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨⟨⟨h1, h4⟩, h3⟩, h4⟩
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨⟨⟨h1, by omega⟩, h3⟩, h4⟩

lemma mQ_le_mfun (W : Weight) (Q : ℝ) {u : ℝ} (hu : 0 < u) : mQ W Q u ≤ mfun W u := by
  unfold mQ mfun
  refine max_le_max (sub_le_sub_right ?_ _) le_rfl
  rw [sum_neg_one_filter_le W _ hu]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun r _ _ =>
    div_nonneg (W.nonneg _) (Nat.cast_nonneg _)
  intro r hr
  simp only [Finset.mem_filter, Finset.mem_Icc] at hr ⊢
  exact ⟨⟨hr.1.1.1, hr.2⟩, hr.1.2⟩

lemma eVariationOn_mQ_le (W : Weight) (Q : ℝ) :
    eVariationOn (mQ W Q) univ ≤
      ENNReal.ofReal (W.Vw * (1 + ∑ r ∈ Finset.Icc 1 ⌊Q⌋₊, 1 / (Nat.totient r : ℝ))) := by
  set F := (Finset.Icc 1 ⌊Q⌋₊).filter (fun r : ℕ => μ r = -1)
  have hVw : eVariationOn W.w univ = ENNReal.ofReal W.Vw := (ENNReal.ofReal_toReal W.bv).symm
  have hterm : ∀ r ∈ F, eVariationOn (fun u => W.w (u * r) / Nat.totient r) univ ≤
      ENNReal.ofReal (1 / (Nat.totient r : ℝ)) * ENNReal.ofReal W.Vw := by
    intro r _
    have e : (fun u => W.w (u * r) / Nat.totient r) =
        fun u => (1 / (Nat.totient r : ℝ)) * W.w (r * u) := by
      funext u; rw [mul_comm u]; ring
    rw [e]
    refine (eVariationOn_const_mul_le _ _ _).trans ?_
    rw [abs_of_nonneg (by positivity), ← hVw]
    gcongr
    exact w_dil_var_le W r
  calc eVariationOn (mQ W Q) univ
      ≤ eVariationOn (fun u => (∑ r ∈ F, W.w (u * r) / Nat.totient r) - W.w u) univ :=
        eVariationOn_max_zero_le _ _
    _ ≤ eVariationOn (fun u => ∑ r ∈ F, W.w (u * r) / Nat.totient r) univ +
          eVariationOn W.w univ := eVariationOn_sub_le _ _ _
    _ ≤ ∑ r ∈ F, ENNReal.ofReal (1 / (Nat.totient r : ℝ)) * ENNReal.ofReal W.Vw +
          ENNReal.ofReal W.Vw := by
        rw [hVw]
        gcongr
        exact (eVariationOn_sum_le F (fun r u => W.w (u * r) / Nat.totient r) univ).trans
          (Finset.sum_le_sum hterm)
    _ = ENNReal.ofReal (W.Vw * (1 + ∑ r ∈ F, 1 / (Nat.totient r : ℝ))) := by
        rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun r _ => by positivity),
          ← ENNReal.ofReal_mul (Finset.sum_nonneg fun r _ => by positivity),
          ← ENNReal.ofReal_add (by have := Vw_nonneg W; positivity) (Vw_nonneg W)]
        congr 1; ring
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have := Vw_nonneg W
        gcongr
        exact Finset.filter_subset _ _

lemma mQ_bv (W : Weight) (Q : ℝ) : BoundedVariationOn (mQ W Q) univ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (eVariationOn_mQ_le W Q)

/-- `V_{m_Q} ≤ 3 V_w (1 + log Q)` (`lem:C`: `V_{m_Q} ≤ V_w(1 + ∑_{r≤Q} 1/φ(r)) ≤ 3V_w(1+log Q)`). -/
lemma Vw_mQ_le (W : Weight) {Q : ℝ} (hQ : 1 ≤ Q) :
    (eVariationOn (mQ W Q) univ).toReal ≤ 3 * W.Vw * (1 + Real.log Q) := by
  have hVw := Vw_nonneg W
  have h1 := ENNReal.toReal_le_of_le_ofReal (by positivity) (eVariationOn_mQ_le W Q)
  have hN : (1 : ℝ) ≤ ⌊Q⌋₊ := by exact_mod_cast (Nat.floor_pos.mpr hQ : 0 < ⌊Q⌋₊)
  have hlog : Real.log ⌊Q⌋₊ ≤ Real.log Q := Real.log_le_log (by linarith) (Nat.floor_le (by linarith))
  have hlogQ : 0 ≤ Real.log Q := Real.log_nonneg hQ
  have h2 := sum_inv_totient_le ⌊Q⌋₊
  calc (eVariationOn (mQ W Q) univ).toReal
      ≤ W.Vw * (1 + ∑ r ∈ Finset.Icc 1 ⌊Q⌋₊, 1 / (Nat.totient r : ℝ)) := h1
    _ ≤ W.Vw * (1 + 2 * (1 + Real.log Q)) := by gcongr; linarith
    _ ≤ 3 * W.Vw * (1 + Real.log Q) := by nlinarith

/-! ### Decomposition of `μ^♮ * k_ς` -/

/-- **Decomposition** (`lem:C`): `(μ^♮ * k_ς)(θ) = ∑_{r≤Q sqfree} (μ(r)/φ(r)) (ν_r * k_ς)(θ) + (μ^m * k_ς)(θ)`,
with `ν_r` the twisted measure of `w(r·)` and `μ^m` the Farey measure of `m_Q`. -/
theorem natConv_decomp (W : Weight) {Q : ℝ} (hQ : 0 < Q) (ς θ : ℝ) :
    natConv W Q ς θ =
      ∑ r ∈ (Finset.Icc 1 ⌊Q⌋₊).filter Squarefree,
        (μ r : ℝ) / Nat.totient r * twistedConv (fun u => W.w (r * u)) r Q ς θ +
      twistedConv (mQ W Q) 1 Q ς θ := by
  unfold natConv aNat levels
  simp_rw [add_mul, Finset.sum_add_distrib]
  congr 1
  · have hΩ : ∀ e ∈ Finset.Icc 1 ⌊Q⌋₊, Ωlev W Q e * ∑ c ∈ reduced e, kper ς (θ - c / e) =
        ∑ r ∈ Finset.Icc 1 ⌊Q⌋₊, if Squarefree r ∧ Nat.Coprime r e then
          (μ r : ℝ) / Nat.totient r * (W.w (r * (e / Q)) * ∑ c ∈ reduced e, kper ς (θ - c / e))
          else 0 := by
      intro e he
      rw [Ωlev_eq_second_form W Q e (Finset.mem_Icc.mp he).1, Finset.sum_mul, Finset.sum_filter]
      refine Finset.sum_congr rfl fun r _ => ?_
      split_ifs
      · push_cast
        rw [show (e : ℝ) * r / Q = r * (e / Q) by ring]
        ring
      · rfl
    rw [Finset.sum_congr rfl hΩ, Finset.sum_comm, Finset.sum_filter]
    refine Finset.sum_congr rfl fun r _ => ?_
    split_ifs with hr
    · unfold twistedConv
      rw [Finset.mul_sum, Finset.sum_filter]
      refine Finset.sum_congr rfl fun e _ => ?_
      by_cases hc : Nat.Coprime e r
      · rw [if_pos ⟨hr, hc.symm⟩, if_pos hc]
      · rw [if_neg (fun h => hc h.2.symm), if_neg hc]
    · exact Finset.sum_eq_zero fun e _ => if_neg (fun h => hr h.1)
  · unfold twistedConv
    rw [Finset.filter_true_of_mem fun q _ => Nat.coprime_one_right q]
    refine Finset.sum_congr rfl fun e he => ?_
    have he1 : (1 : ℝ) ≤ e := by exact_mod_cast (Finset.mem_Icc.mp he).1
    rw [mQ_eq_mfun W (by positivity) (by rw [one_div_div, div_le_iff₀ (by linarith)]; nlinarith)]

/-! ### The local densities -/

/-- Finite core of `∑_r (μ(r)/φ(r)) ρ_r = Q² ℰ I_w R_S`: by `lem:fS`(i),
`∑_{r≤N sqfree} ∑_{k≤M} (μ(r)/φ(r)) k G_S(k,r) g(kr) = ∑_{n≤M} n f_S(n) g(n)` if `M ≤ N` and
`g(n) = 0` for `n > M`. -/
lemma core_sum (hfS : lemfS_i_Statement) (S : Finset ℕ) (g : ℕ → ℝ) {M N : ℕ} (hMN : M ≤ N)
    (hg : ∀ n, M < n → g n = 0) :
    ∑ r ∈ (Finset.Icc 1 N).filter Squarefree, ∑ k ∈ Finset.Icc 1 M,
        (μ r : ℝ) / Nat.totient r * (k * GS S k r * g (k * r)) =
      ∑ n ∈ Finset.Icc 1 M, n * fS S n * g n := by
  set P := (Finset.Icc 1 M ×ˢ Finset.Icc 1 M).filter
    (fun p : ℕ × ℕ => p.1 * p.2 ≤ M ∧ Squarefree p.2) with hP
  set F : ℕ × ℕ → ℝ := fun p => (μ p.2 : ℝ) / Nat.totient p.2 *
    (p.1 * GS S p.1 p.2 * g (p.1 * p.2)) with hF
  have hL : ∑ r ∈ (Finset.Icc 1 N).filter Squarefree, ∑ k ∈ Finset.Icc 1 M,
      (μ r : ℝ) / Nat.totient r * (k * GS S k r * g (k * r)) = ∑ p ∈ P, F p := by
    rw [Finset.sum_comm, ← Finset.sum_product']
    symm
    refine Finset.sum_subset ?_ ?_
    · intro p hp
      simp only [hP, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp ⊢
      exact ⟨hp.1.1, ⟨hp.1.2.1, by omega⟩, hp.2.2⟩
    · intro p hp hpP
      simp only [hP, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp hpP
      have hMp : M < p.1 * p.2 := by
        by_contra h
        exact hpP ⟨⟨hp.1, ⟨hp.2.1.1, by nlinarith [hp.1.1]⟩⟩, not_lt.mp h, hp.2.2⟩
      simp only [hF]
      rw [hg _ hMp, mul_zero, mul_zero]
  have hR : ∑ n ∈ Finset.Icc 1 M, n * fS S n * g n = ∑ p ∈ P, F p := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := P) (t := Finset.Icc 1 M)
      (g := fun p : ℕ × ℕ => p.1 * p.2)]
    · refine Finset.sum_congr rfl fun n hn => ?_
      obtain ⟨hn1, hnM⟩ := Finset.mem_Icc.mp hn
      rw [hfS S n hn1, Finset.mul_sum, Finset.sum_mul]
      have hset : n.divisorsAntidiagonal.filter (fun kr => Squarefree kr.2) =
          P.filter (fun p => p.1 * p.2 = n) := by
        ext p
        simp only [Nat.mem_divisorsAntidiagonal, hP, Finset.mem_filter, Finset.mem_product,
          Finset.mem_Icc]
        constructor
        · rintro ⟨⟨hp, hn0⟩, hsq⟩
          have h1 : 0 < p.1 := Nat.pos_of_ne_zero fun h => by rw [h, zero_mul] at hp; omega
          have h2 : 0 < p.2 := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hp; omega
          have h3 : p.1 ≤ n := by rw [← hp]; exact Nat.le_mul_of_pos_right _ h2
          have h4 : p.2 ≤ n := by rw [← hp]; exact Nat.le_mul_of_pos_left _ h1
          exact ⟨⟨⟨⟨h1, by omega⟩, ⟨h2, by omega⟩⟩, by omega, hsq⟩, hp⟩
        · rintro ⟨⟨-, -, hsq⟩, hp⟩
          exact ⟨⟨hp, by omega⟩, hsq⟩
      rw [hset]
      refine Finset.sum_congr rfl fun p hp => ?_
      obtain ⟨hpP, hpn⟩ := Finset.mem_filter.mp hp
      simp only [hP, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hpP
      have hp2 : (p.2 : ℝ) ≠ 0 := by exact_mod_cast (by omega : p.2 ≠ 0)
      have hφ : (Nat.totient p.2 : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.totient_pos.mpr (by omega : 0 < p.2)).ne'
      simp only [hF]
      rw [← hpn]
      push_cast
      field_simp
    · intro p hp
      simp only [hP, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
      rw [Finset.mem_Icc]
      exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), hp.2.1⟩
  rw [hL, hR]

lemma Ecal_Iw_pos (W : Weight) : 0 < Ecal * W.Iw := mul_pos Ecal_pos W.Iw_pos

/-- **`lem:C`, main terms of the `ν_r`:** `∑_{r≤Q sqfree} (μ(r)/φ(r)) ρ_r(z) = Q² ℰ I_w R_S(t)`,
`t = 1/(v|z|Q)`, provided `⌊v|z|Q⌋ ≤ ⌊Q⌋` (by `lem:fS`(i)). -/
theorem sum_rhoTwist_eq (hfS : lemfS_i_Statement) (W : Weight) {Q : ℝ} (hQ : 0 < Q) {v : ℕ}
    (hv : 1 ≤ v) (S : Finset ℕ) {z : ℝ} (hz : z ≠ 0)
    (hM : ⌊(v : ℝ) * |z| * Q⌋₊ ≤ ⌊Q⌋₊) :
    ∑ r ∈ (Finset.Icc 1 ⌊Q⌋₊).filter Squarefree,
        (μ r : ℝ) / Nat.totient r * rhoTwist (fun u => W.w (r * u)) S r Q v z =
      Q ^ 2 * (Ecal * W.Iw) * RS W S (1 / ((v : ℝ) * |z| * Q)) := by
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have hzabs : 0 < |z| := abs_pos.mpr hz
  set X := (v : ℝ) * |z| * Q with hX
  have hX0 : 0 < X := by positivity
  set t := 1 / X with ht
  have htX : 1 / t = X := by rw [ht, one_div_one_div]
  set M := ⌊X⌋₊ with hMdef
  set g : ℕ → ℝ := fun n => W.w (n * t) with hg
  have hgz : ∀ n, M < n → g n = 0 := by
    intro n hn
    have h1 : X < n := (Nat.floor_lt hX0.le).mp hn
    simp only [hg]
    exact W_zero_of_gt_one W (by rw [ht, mul_one_div, one_lt_div hX0]; exact h1)
  have hcore := core_sum hfS S g hM hgz
  unfold rhoTwist RS
  rw [htX, ← hMdef]
  have hEI := Ecal_Iw_pos W
  -- `(vz)^{-2} = Q² t²`
  have hvz : ((v : ℝ) * z)⁻¹ ^ 2 = Q ^ 2 * t ^ 2 := by
    rw [ht, hX]
    have hz2 : z ^ 2 = |z| ^ 2 := (sq_abs z).symm
    field_simp
    rw [hz2]
  calc ∑ r ∈ (Finset.Icc 1 ⌊Q⌋₊).filter Squarefree, (μ r : ℝ) / Nat.totient r *
        (((v : ℝ) * z)⁻¹ ^ 2 * ∑ k ∈ Finset.Icc 1 M, (k : ℝ) * GS S k r * W.w (r * (k / X)))
      = Q ^ 2 * t ^ 2 * ∑ r ∈ (Finset.Icc 1 ⌊Q⌋₊).filter Squarefree, ∑ k ∈ Finset.Icc 1 M,
          (μ r : ℝ) / Nat.totient r * (k * GS S k r * g (k * r)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [hvz, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [hg]
        push_cast
        rw [show (r : ℝ) * (k / X) = k * r * t by rw [ht]; ring]
        ring
    _ = Q ^ 2 * t ^ 2 * ∑ n ∈ Finset.Icc 1 M, n * fS S n * g n := by rw [hcore]
    _ = Q ^ 2 * (Ecal * W.Iw) * ((Ecal * W.Iw)⁻¹ *
          ∑ n ∈ Finset.Icc 1 M, fS S n / n * W.wt (n * t)) := by
        rw [← mul_assoc (Q ^ 2 * (Ecal * W.Iw)), mul_inv_cancel_right₀ hEI.ne', mul_assoc,
          Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun n hn => ?_
        have hn0 : (n : ℝ) ≠ 0 := by
          exact_mod_cast (by have := (Finset.mem_Icc.mp hn).1; omega : n ≠ 0)
        simp only [hg, Weight.wt]
        field_simp

/-- **`lem:C`, main term of `μ^m`:** `ρ_{m_Q}(z) ≤ Q² ℰ I_w R^m(t)`, `t = 1/(v|z|Q)`. -/
theorem rhoTwist_mQ_le (W : Weight) {Q : ℝ} (hQ : 0 < Q) {v : ℕ} (hv : 1 ≤ v) (S : Finset ℕ)
    {z : ℝ} (hz : z ≠ 0) :
    rhoTwist (mQ W Q) S 1 Q v z ≤ Q ^ 2 * (Ecal * W.Iw) * Rm W (1 / ((v : ℝ) * |z| * Q)) := by
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have hzabs : 0 < |z| := abs_pos.mpr hz
  set X := (v : ℝ) * |z| * Q with hX
  have hX0 : 0 < X := by positivity
  set t := 1 / X with ht
  have htX : 1 / t = X := by rw [ht, one_div_one_div]
  have hEI := Ecal_Iw_pos W
  rw [rhoTwist_one]
  unfold rhoCount Rm
  rw [htX, ← mul_assoc (Q ^ 2 * (Ecal * W.Iw)), mul_inv_cancel_right₀ hEI.ne',
    Finset.mul_sum, Finset.mul_sum]
  have hvz : ((v : ℝ) * z)⁻¹ ^ 2 = Q ^ 2 * t ^ 2 := by
    rw [ht, hX]
    have hz2 : z ^ 2 = |z| ^ 2 := (sq_abs z).symm
    field_simp
    rw [hz2]
  refine Finset.sum_le_sum fun k hk => ?_
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by have := (Finset.mem_Icc.mp hk).1; omega : 0 < k)
  have hkt : (k : ℝ) / X = k * t := by rw [ht]; ring
  rw [hvz, hkt]
  unfold mt
  have hle := mQ_le_mfun W Q (u := k * t) (by rw [ht]; positivity)
  have hφ : (0 : ℝ) ≤ Nat.totient k := Nat.cast_nonneg _
  calc Q ^ 2 * t ^ 2 * ((Nat.totient k : ℝ) * mQ W Q (k * t))
      ≤ Q ^ 2 * t ^ 2 * ((Nat.totient k : ℝ) * mfun W (k * t)) := by gcongr
    _ = Q ^ 2 * ((Nat.totient k : ℝ) / (k : ℝ) ^ 2 * ((k * t) ^ 2 * mfun W (k * t))) := by
        field_simp

end Families.Phase1.A
