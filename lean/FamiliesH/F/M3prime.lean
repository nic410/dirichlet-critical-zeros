/-
# Package F: `lem:M3prime` (Lemma 9.13, tails by dyadic shells)

Proof (a variant of the proof of Lemma 9.13 with a finite set of pieces, so that no `c_k`-weights are needed): at each `u`
split the tail `x^t(u)` of `x_y(u)` into the dyadic shells `2^kδ ≤ ±(log n − u) < 2^{k+1}δ`, `k < k₀`,
and one far piece `|log n − u| ≥ 2^{k₀}δ ≥ 1`. Cauchy–Schwarz over the `2k₀+1` pieces; the large sieve
`MVLargeSieveMult C₀` on each piece (a shell has diameter `≤ 2·2^kδ Y`, the far piece `≤ Y`); the bounds
`|x^t(u)_n|² ≤ 4|y_n|²/(log n − u)²`; and integration in `u` (a shell has `u`-measure `2^kδ`, the far piece
is dominated by the kernel `tailK`, of integral `16/(2^{k₀}δ)`). The constants give
`(2k₀+1)(20(Q²+1)/δ + 16(k₀+1)Y) ≤ 48(k₀+4)((Q²+1)/δ + (k₀+3)Y)`.
-/
import FamiliesH.F.M3

noncomputable section

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace Families.Hybrid

open Families

namespace F

/-! ### General facts about the family form -/

lemma omega_nonneg (W : Weight) (Q : ℝ) (q : ℕ) : 0 ≤ W.omega Q q := by
  unfold Weight.omega
  exact div_nonneg (mul_nonneg (W.nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

lemma famForm_nonnegH (W : Weight) (Q : ℝ) (I : Finset ℤ) (x : ℤ → ℂ) : 0 ≤ famForm W Q I x :=
  Finset.sum_nonneg fun q _ =>
    mul_nonneg (omega_nonneg W Q q) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-- Cauchy–Schwarz for the family form over finitely many pieces. -/
lemma famForm_sum_le {ι : Type*} (W : Weight) (Q : ℝ) (I : Finset ℤ) (S : Finset ι)
    (p : ι → ℤ → ℂ) :
    famForm W Q I (fun n => ∑ i ∈ S, p i n) ≤ (S.card : ℝ) * ∑ i ∈ S, famForm W Q I (p i) := by
  have key : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      ‖∑ n ∈ I, (∑ i ∈ S, p i n) * χ n‖ ^ 2 ≤
        (S.card : ℝ) * ∑ i ∈ S, ‖∑ n ∈ I, p i n * χ n‖ ^ 2 := by
    intro q χ
    have h1 : ∑ n ∈ I, (∑ i ∈ S, p i n) * χ n = ∑ i ∈ S, ∑ n ∈ I, p i n * χ n := by
      simp_rw [Finset.sum_mul]; rw [Finset.sum_comm]
    rw [h1]
    calc ‖∑ i ∈ S, ∑ n ∈ I, p i n * χ n‖ ^ 2 ≤ (∑ i ∈ S, ‖∑ n ∈ I, p i n * χ n‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ (S.card : ℝ) * ∑ i ∈ S, ‖∑ n ∈ I, p i n * χ n‖ ^ 2 := sq_sum_le_card_mul_sum_sq
  unfold famForm
  calc ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q *
        ∑ χ ∈ primChars q, ‖∑ n ∈ I, (∑ i ∈ S, p i n) * χ n‖ ^ 2
      ≤ ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q *
        ∑ χ ∈ primChars q, (S.card : ℝ) * ∑ i ∈ S, ‖∑ n ∈ I, p i n * χ n‖ ^ 2 := by
        refine Finset.sum_le_sum fun q _ => ?_
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun χ _ => key q χ)
          (omega_nonneg W Q q)
    _ = (S.card : ℝ) * ∑ i ∈ S, ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q *
        ∑ χ ∈ primChars q, ‖∑ n ∈ I, p i n * χ n‖ ^ 2 := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm (s := S)]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.sum_comm (s := S)]
        refine Finset.sum_congr rfl fun χ _ => Finset.sum_congr rfl fun i _ => ?_
        ring

/-- The multiplicative large sieve for a vector whose nonzero entries in `I` span a set of diameter
`≤ D`: `x^*Δx ≤ w_max C₀ (Q² + D + 1) ‖x‖²`. -/
lemma famForm_le_of_diam {C₀ : ℝ} (hMV : MVLargeSieveMult C₀) (hC₀ : 0 ≤ C₀) (W : Weight)
    {Q : ℝ} (hQ : 1 ≤ Q) (I : Finset ℤ) (x : ℤ → ℂ) {D : ℝ}
    (hD : ∀ n ∈ I, ∀ m ∈ I, x n ≠ 0 → x m ≠ 0 → ((n : ℝ) - m) ≤ D) :
    famForm W Q I x ≤ W.wmax * C₀ * (Q ^ 2 + D + 1) * normSq I x := by
  classical
  set F := I.filter (fun n => x n ≠ 0) with hF
  by_cases hFe : F = ∅
  · have hx : ∀ n ∈ I, x n = 0 := fun n hn => by
      by_contra h
      have : n ∈ F := Finset.mem_filter.mpr ⟨hn, h⟩
      rw [hFe] at this; simp at this
    have h1 : famForm W Q I x = 0 := by
      unfold famForm
      refine Finset.sum_eq_zero fun q _ => ?_
      rw [Finset.sum_eq_zero fun χ _ => ?_, mul_zero]
      rw [Finset.sum_eq_zero fun n hn => by rw [hx n hn, zero_mul]]; simp
    have h2 : normSq I x = 0 := by
      unfold normSq
      exact Finset.sum_eq_zero fun n hn => by rw [hx n hn]; simp
    rw [h1, h2]; simp
  · have hFne : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hFe
    set a := F.min' hFne with ha
    set b := F.max' hFne with hb
    have haF : a ∈ F := Finset.min'_mem F hFne
    have hbF : b ∈ F := Finset.max'_mem F hFne
    have hab : a ≤ b := Finset.min'_le_max' F hFne
    have hDab : ((b : ℝ) - a) ≤ D :=
      hD b (Finset.mem_filter.mp hbF).1 a (Finset.mem_filter.mp haF).1
        (Finset.mem_filter.mp hbF).2 (Finset.mem_filter.mp haF).2
    set K : ℕ := (b - a + 1).toNat with hK
    have hKz : (K : ℤ) = b - a + 1 := Int.toNat_of_nonneg (by omega)
    set x' : ℤ → ℂ := fun n => if n ∈ I then x n else 0 with hx'
    have hsupp : ∀ n, x' n ≠ 0 → (n ∈ I ↔ n ∈ intervalZ a K) := by
      intro n hn
      have hnI : n ∈ I := by by_contra h; simp [hx', h] at hn
      have hxn : x n ≠ 0 := by simpa [hx', hnI] using hn
      have hnF : n ∈ F := Finset.mem_filter.mpr ⟨hnI, hxn⟩
      have h1 : a ≤ n := Finset.min'_le F n hnF
      have h2 : n ≤ b := Finset.le_max' F n hnF
      simp only [intervalZ, Finset.mem_Ico, hnI, true_iff]
      omega
    have hfam : famForm W Q I x = famForm W Q (intervalZ a K) x' := by
      rw [← Phase3.C.famForm_congr_supp W Q hsupp]
      unfold famForm
      refine Finset.sum_congr rfl fun q _ => ?_
      congr 1
      refine Finset.sum_congr rfl fun χ _ => ?_
      congr 2
      refine Finset.sum_congr rfl fun n hn => ?_
      simp [hx', hn]
    have hnorm : normSq (intervalZ a K) x' = normSq I x := by
      rw [← Phase3.C.normSq_congr_supp hsupp]
      unfold normSq
      refine Finset.sum_congr rfl fun n hn => ?_
      simp [hx', hn]
    have hmv := hMV Q hQ a K x'
    have hle := Families.famForm_le_mult W Q (intervalZ a K) x'
    have hK' : (K : ℝ) ≤ D + 1 := by
      have : (K : ℝ) = (b : ℝ) - a + 1 := by exact_mod_cast hKz
      linarith
    have hnn : 0 ≤ normSq I x := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hw := W.wmax_nonneg
    rw [hfam]
    calc famForm W Q (intervalZ a K) x'
        ≤ W.wmax * ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ((q : ℝ) / (Nat.totient q : ℝ)) *
            ∑ χ ∈ primChars q, ‖∑ n ∈ intervalZ a K, x' n * χ n‖ ^ 2 := hle
      _ ≤ W.wmax * (C₀ * (Q ^ 2 + K) * normSq (intervalZ a K) x') :=
          mul_le_mul_of_nonneg_left hmv hw
      _ = W.wmax * C₀ * (Q ^ 2 + K) * normSq I x := by rw [hnorm]; ring
      _ ≤ W.wmax * C₀ * (Q ^ 2 + D + 1) * normSq I x := by
          apply mul_le_mul_of_nonneg_right _ hnn
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hw hC₀)
          linarith

/-- `e^a − 1 ≤ 2a` for `0 ≤ a ≤ 1`. -/
lemma exp_sub_one_le_two_mul {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : Real.exp a - 1 ≤ 2 * a := by
  have h := Real.abs_exp_sub_one_sub_id_le (x := a) (by rw [abs_of_nonneg ha0]; exact ha1)
  have := (abs_le.mp h).2
  nlinarith

/-! ### Shells -/

/-- `ξ_n(u) = log n − u`. -/
def xiU (u : ℝ) (n : ℤ) : ℝ := Real.log (n.toNat : ℝ) - u

/-- The shell index of `n` at `u`: `(k, sign ξ ≥ 0)` if `2^kδ ≤ |ξ| < 2^{k+1}δ` with `k < k₀`, and
`(k₀, true)` for the far piece `|ξ| ≥ 2^{k₀}δ` (for `|ξ| ≤ δ` the tail vanishes anyway). -/
def shellIdx (δ u : ℝ) (k0 : ℕ) (n : ℤ) : ℕ × Bool :=
  if k0 ≤ Nat.log 2 ⌊|xiU u n| / δ⌋₊ then (k0, true)
  else (Nat.log 2 ⌊|xiU u n| / δ⌋₊, decide (0 ≤ xiU u n))

/-- The index set: the `2k₀` shells and the far piece. -/
def shellSet (k0 : ℕ) : Finset (ℕ × Bool) := (Finset.range k0 ×ˢ Finset.univ) ∪ {(k0, true)}

lemma shellIdx_mem (δ u : ℝ) (k0 : ℕ) (n : ℤ) : shellIdx δ u k0 n ∈ shellSet k0 := by
  unfold shellIdx shellSet
  split_ifs with h
  · simp
  · simp only [Finset.mem_union, Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true,
      Finset.mem_singleton]
    left; omega

lemma card_shellSet (k0 : ℕ) : ((shellSet k0).card : ℝ) ≤ 2 * k0 + 1 := by
  unfold shellSet
  have h1 := Finset.card_union_le (Finset.range k0 ×ˢ (Finset.univ : Finset Bool)) {(k0, true)}
  rw [Finset.card_product, Finset.card_range, Finset.card_univ, Fintype.card_bool,
    Finset.card_singleton] at h1
  have : ((Finset.range k0 ×ˢ (Finset.univ : Finset Bool) ∪ {(k0, true)}).card : ℝ) ≤
      ((k0 * 2 + 1 : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast at this; linarith

/-- The tail of `x_y(u)` at scale `δ` (the `x^t` of the statement). -/
def xtail (P : HSetup) (Q T δ : ℝ) (ρ : ℝ → ℝ) (y : ℕ → ℝ) (u : ℝ) : ℤ → ℂ := fun n =>
  P.xVec Q T y u n * (1 - ρ ((Real.log n.toNat - u) / δ))

section tails

variable (P : HSetup) {ρ : ℝ → ℝ} (hρ : IsLocCutoff ρ) {Q T δ : ℝ} (hδ : 0 < δ) (y : ℕ → ℝ)

include hρ hδ in
/-- The tail vanishes on `|log n − u| ≤ δ`. -/
lemma xtail_eq_zero {u : ℝ} {n : ℤ} (h : |xiU u n| ≤ δ) : xtail P Q T δ ρ y u n = 0 := by
  unfold xtail
  have h1 : |(Real.log n.toNat - u) / δ| ≤ 1 := by
    rw [abs_div, abs_of_pos hδ, div_le_one hδ]; exact h
  rw [hρ.2.2.1 _ h1]; simp

include hρ hδ in
lemma abs_xi_gt {u : ℝ} {n : ℤ} (h : xtail P Q T δ ρ y u n ≠ 0) : δ < |xiU u n| := by
  by_contra hc; exact h (xtail_eq_zero P hρ hδ y (not_lt.mp hc))

include hρ in
/-- `|x^t(u)_n|² ≤ 4 |y_n|² / (log n − u)²`. -/
lemma xtail_norm_sq_le {u : ℝ} {n : ℤ} (hξ : xiU u n ≠ 0) :
    ‖xtail P Q T δ ρ y u n‖ ^ 2 ≤ (y n.toNat) ^ 2 * (4 / (xiU u n) ^ 2) := by
  unfold xtail
  have hρ1 : ‖(1 - ρ ((Real.log n.toNat - u) / δ) : ℂ)‖ ≤ 1 := by
    have h0 := hρ.2.1 ((Real.log n.toNat - u) / δ)
    rw [show ((1 : ℂ) - (ρ ((Real.log n.toNat - u) / δ) : ℂ)) =
      ((1 - ρ ((Real.log n.toNat - u) / δ) : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  by_cases hn : 1 ≤ n
  · have hx : P.xVec Q T y u n = (y n.toNat : ℂ) * P.hatJ T (u - Real.log n.toNat) := by
      simp [HSetup.xVec, hn]
    rw [hx, norm_mul, norm_mul, mul_pow, mul_pow]
    have hJ : ‖P.hatJ T (u - Real.log n.toNat)‖ ^ 2 ≤ 4 / (xiU u n) ^ 2 := by
      have := P.toPS.hatJ_sq_le T (u - Real.log n.toNat) (by
        intro h0; apply hξ; unfold xiU; linarith)
      rw [HSetup.hatJ_eq]
      calc ‖P.toPS.hatJ T (u - Real.log n.toNat)‖ ^ 2 ≤ 4 / (u - Real.log n.toNat) ^ 2 := this
        _ = 4 / (xiU u n) ^ 2 := by unfold xiU; ring
    have hy : ‖(y n.toNat : ℂ)‖ ^ 2 = (y n.toNat) ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [hy]
    have h1 : ‖(1 - ρ ((Real.log n.toNat - u) / δ) : ℂ)‖ ^ 2 ≤ 1 := by
      have := norm_nonneg ((1 : ℂ) - (ρ ((Real.log n.toNat - u) / δ) : ℂ))
      nlinarith
    have h2 : 0 ≤ ‖P.hatJ T (u - Real.log n.toNat)‖ ^ 2 := sq_nonneg _
    have h3 : 0 ≤ (y n.toNat) ^ 2 := sq_nonneg _
    calc y n.toNat ^ 2 * ‖P.hatJ T (u - Real.log n.toNat)‖ ^ 2 *
          ‖(1 - ρ ((Real.log n.toNat - u) / δ) : ℂ)‖ ^ 2
        ≤ y n.toNat ^ 2 * ‖P.hatJ T (u - Real.log n.toNat)‖ ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg h3 h2)
      _ ≤ y n.toNat ^ 2 * (4 / xiU u n ^ 2) := by
          rw [mul_one]; exact mul_le_mul_of_nonneg_left hJ h3
  · have hx : P.xVec Q T y u n = 0 := by simp [HSetup.xVec, hn]
    rw [hx, zero_mul, norm_zero]
    have : (0 : ℝ) ^ 2 = 0 := by norm_num
    rw [this]; positivity

/-- For `r > 1`, `k = log₂ ⌊r⌋` satisfies `2^k ≤ r < 2^{k+1}`. -/
lemma nat_log_floor_bounds {r : ℝ} (hr : 1 < r) :
    (2 : ℝ) ^ (Nat.log 2 ⌊r⌋₊) ≤ r ∧ r < (2 : ℝ) ^ (Nat.log 2 ⌊r⌋₊ + 1) := by
  have hr0 : 0 ≤ r := by linarith
  have hfl1 : 1 ≤ ⌊r⌋₊ := Nat.le_floor (by exact_mod_cast hr.le)
  have hne : ⌊r⌋₊ ≠ 0 := by omega
  have h1 : 2 ^ (Nat.log 2 ⌊r⌋₊) ≤ ⌊r⌋₊ := Nat.pow_log_le_self 2 hne
  have h2 : ⌊r⌋₊ < 2 ^ (Nat.log 2 ⌊r⌋₊ + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  refine ⟨?_, ?_⟩
  · calc (2 : ℝ) ^ (Nat.log 2 ⌊r⌋₊) = ((2 ^ (Nat.log 2 ⌊r⌋₊) : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (⌊r⌋₊ : ℝ) := by exact_mod_cast h1
      _ ≤ r := Nat.floor_le hr0
  · have h3 : (⌊r⌋₊ : ℝ) + 1 ≤ ((2 ^ (Nat.log 2 ⌊r⌋₊ + 1) : ℕ) : ℝ) := by exact_mod_cast h2
    have h4 := Nat.lt_floor_add_one r
    push_cast at h3; linarith

include hρ hδ in
/-- A nonzero entry of the shell piece `(k, s)`, `k < k₀`, lies in that shell. -/
lemma shell_facts {u : ℝ} {n : ℤ} {k0 k : ℕ} {s : Bool} (hk : k < k0)
    (hidx : shellIdx δ u k0 n = (k, s)) (hx : xtail P Q T δ ρ y u n ≠ 0) :
    (2 : ℝ) ^ k * δ ≤ |xiU u n| ∧ |xiU u n| < (2 : ℝ) ^ (k + 1) * δ ∧
      s = decide (0 ≤ xiU u n) := by
  have hgt := abs_xi_gt P hρ hδ y hx
  have hr : 1 < |xiU u n| / δ := by rw [lt_div_iff₀ hδ]; linarith
  unfold shellIdx at hidx
  split_ifs at hidx with h
  · simp only [Prod.mk.injEq] at hidx; omega
  · simp only [Prod.mk.injEq] at hidx
    obtain ⟨hk', hs⟩ := hidx
    obtain ⟨b1, b2⟩ := nat_log_floor_bounds hr
    rw [hk'] at b1 b2
    refine ⟨?_, ?_, hs.symm⟩
    · rw [le_div_iff₀ hδ] at b1; linarith
    · rw [div_lt_iff₀ hδ] at b2; linarith

include hρ hδ in
/-- A nonzero entry of the far piece has `|log n − u| ≥ 2^{k₀}δ`. -/
lemma far_facts {u : ℝ} {n : ℤ} {k0 : ℕ} (hidx : shellIdx δ u k0 n = (k0, true))
    (hx : xtail P Q T δ ρ y u n ≠ 0) : (2 : ℝ) ^ k0 * δ ≤ |xiU u n| := by
  have hgt := abs_xi_gt P hρ hδ y hx
  have hr : 1 < |xiU u n| / δ := by rw [lt_div_iff₀ hδ]; linarith
  unfold shellIdx at hidx
  split_ifs at hidx with h
  · obtain ⟨b1, -⟩ := nat_log_floor_bounds hr
    have hpow : (2 : ℝ) ^ k0 ≤ (2 : ℝ) ^ (Nat.log 2 ⌊|xiU u n| / δ⌋₊) :=
      pow_le_pow_right₀ (by norm_num) h
    have := hpow.trans b1
    rw [le_div_iff₀ hδ] at this; linarith
  · simp only [Prod.mk.injEq] at hidx; omega

end tails

/-! ### The pieces and the pointwise bound -/

/-- The `u`-set of the shell `(k, s)` of `n`: `2^kδ ≤ ±(log n − u) < 2^{k+1}δ`. -/
def shellU (δ : ℝ) (k : ℕ) (s : Bool) (n : ℤ) : Set ℝ :=
  if s then Set.Ioc (Real.log (n.toNat : ℝ) - 2 ^ (k + 1) * δ) (Real.log (n.toNat : ℝ) - 2 ^ k * δ)
  else Set.Ico (Real.log (n.toNat : ℝ) + 2 ^ k * δ) (Real.log (n.toNat : ℝ) + 2 ^ (k + 1) * δ)

lemma mem_shellU {δ u : ℝ} {k : ℕ} {s : Bool} {n : ℤ}
    (h1 : (2 : ℝ) ^ k * δ ≤ |xiU u n|) (h2 : |xiU u n| < (2 : ℝ) ^ (k + 1) * δ)
    (hs : s = decide (0 ≤ xiU u n)) : u ∈ shellU δ k s n := by
  unfold shellU
  unfold xiU at h1 h2 hs
  by_cases h0 : 0 ≤ Real.log (n.toNat : ℝ) - u
  · have hs' : s = true := by simpa [h0] using hs
    rw [abs_of_nonneg h0] at h1 h2
    simp only [hs', if_true, Set.mem_Ioc]
    constructor <;> linarith
  · have hs' : s = false := by simpa [h0] using hs
    rw [abs_of_neg (not_le.mp h0)] at h1 h2
    simp only [hs', Bool.false_eq_true, if_false, Set.mem_Ico]
    constructor <;> linarith

/-- The piece of the tail with shell index `i`. -/
def piece (P : HSetup) (Q T δ : ℝ) (ρ : ℝ → ℝ) (y : ℕ → ℝ) (k0 : ℕ) (u : ℝ) (i : ℕ × Bool) :
    ℤ → ℂ := fun n => if shellIdx δ u k0 n = i then xtail P Q T δ ρ y u n else 0

lemma xtail_eq_sum (P : HSetup) (Q T δ : ℝ) (ρ : ℝ → ℝ) (y : ℕ → ℝ) (k0 : ℕ) (u : ℝ) :
    xtail P Q T δ ρ y u = fun n => ∑ i ∈ shellSet k0, piece P Q T δ ρ y k0 u i n := by
  funext n
  unfold piece
  rw [Finset.sum_ite_eq (shellSet k0) (shellIdx δ u k0 n) (fun _ => xtail P Q T δ ρ y u n)]
  simp [shellIdx_mem]

section pieces

variable (P : HSetup) {ρ : ℝ → ℝ} (hρ : IsLocCutoff ρ) {Q T δ : ℝ} (hδ : 0 < δ) (y : ℕ → ℝ)

lemma mem_rangeZ_bounds {Q T : ℝ} {n : ℤ} (hn : n ∈ P.rangeZ Q T) :
    1 ≤ n ∧ (n : ℝ) ≤ P.Y Q T := by
  unfold HSetup.rangeZ at hn
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
  refine ⟨h1, ?_⟩
  have := Int.floor_le (P.Y Q T)
  have h2' : (n : ℝ) ≤ (⌊P.Y Q T⌋ : ℝ) := by exact_mod_cast h2
  linarith

lemma toNat_cast_eq {n : ℤ} (hn : 1 ≤ n) : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
  have : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg (by omega)
  exact_mod_cast this

lemma exp_log_toNat {n : ℤ} (hn : 1 ≤ n) : Real.exp (Real.log (n.toNat : ℝ)) = (n : ℝ) := by
  rw [Real.exp_log (by rw [toNat_cast_eq hn]; exact_mod_cast (show (0 : ℤ) < n by omega)),
    toNat_cast_eq hn]

include hρ hδ in
/-- Near piece: its nonzero entries span a set of diameter `≤ 2·2^kδ·Y`. -/
lemma near_diam {k0 k : ℕ} {s : Bool} (hk : k < k0) (hk1 : (2 : ℝ) ^ k * δ ≤ 1) (u : ℝ) :
    ∀ n ∈ P.rangeZ Q T, ∀ m ∈ P.rangeZ Q T, piece P Q T δ ρ y k0 u (k, s) n ≠ 0 →
      piece P Q T δ ρ y k0 u (k, s) m ≠ 0 → ((n : ℝ) - m) ≤ 2 * ((2 : ℝ) ^ k * δ) * P.Y Q T := by
  intro n hn m hm hpn' hpm'
  by_cases hin : shellIdx δ u k0 n = (k, s)
  swap
  · exact absurd (by unfold piece; rw [if_neg hin]) hpn'
  by_cases him : shellIdx δ u k0 m = (k, s)
  swap
  · exact absurd (by unfold piece; rw [if_neg him]) hpm'
  have hpn : xtail P Q T δ ρ y u n ≠ 0 := by
    intro h0; apply hpn'; unfold piece; rw [if_pos hin, h0]
  have hpm : xtail P Q T δ ρ y u m ≠ 0 := by
    intro h0; apply hpm'; unfold piece; rw [if_pos him, h0]
  obtain ⟨n1, nY⟩ := mem_rangeZ_bounds P hn
  obtain ⟨m1, mY⟩ := mem_rangeZ_bounds P hm
  obtain ⟨an, bn, sn⟩ := shell_facts P hρ hδ y hk hin hpn
  obtain ⟨am, bm, sm⟩ := shell_facts P hρ hδ y hk him hpm
  set a := (2 : ℝ) ^ k * δ with ha
  have ha0 : 0 ≤ a := by positivity
  have h2a : (2 : ℝ) ^ (k + 1) * δ = 2 * a := by rw [ha, pow_succ]; ring
  rw [h2a] at bn bm
  have hea : Real.exp a - 1 ≤ 2 * a := exp_sub_one_le_two_mul ha0 hk1
  have hea0 : 0 ≤ Real.exp a - 1 := by linarith [Real.add_one_le_exp a]
  have hnexp := exp_log_toNat n1
  have hmexp := exp_log_toNat m1
  set Ln := Real.log (n.toNat : ℝ)
  set Lm := Real.log (m.toNat : ℝ)
  unfold xiU at an bn sn am bm sm
  have hmY : (m : ℝ) * (Real.exp a - 1) ≤ P.Y Q T * (2 * a) :=
    mul_le_mul mY hea hea0 (Real.rpow_nonneg (Real.exp_pos _).le _)
  by_cases hs : s = true
  · -- `0 ≤ ξ`: `n < e^{u+2a}`, `m ≥ e^{u+a}`
    have hn0 : 0 ≤ Ln - u := by rw [hs] at sn; simpa using sn.symm
    have hm0 : 0 ≤ Lm - u := by rw [hs] at sm; simpa using sm.symm
    rw [abs_of_nonneg hn0] at an bn
    rw [abs_of_nonneg hm0] at am bm
    have h1 : (n : ℝ) < Real.exp (u + 2 * a) := by
      rw [← hnexp]; exact Real.exp_lt_exp.mpr (by linarith)
    have h2 : Real.exp (u + a) ≤ (m : ℝ) := by
      rw [← hmexp]; exact Real.exp_le_exp.mpr (by linarith)
    have h3 : Real.exp (u + 2 * a) = Real.exp (u + a) * Real.exp a := by
      rw [← Real.exp_add]; ring_nf
    have h4 : Real.exp (u + a) * (Real.exp a - 1) ≤ (m : ℝ) * (Real.exp a - 1) :=
      mul_le_mul_of_nonneg_right h2 hea0
    nlinarith
  · -- `ξ < 0`: `n ≤ e^{u−a}`, `m > e^{u−2a}`
    have hsf : s = false := by simpa using hs
    have hn0 : Ln - u < 0 := by
      rw [hsf] at sn; have := sn.symm; simp at this; linarith
    have hm0 : Lm - u < 0 := by
      rw [hsf] at sm; have := sm.symm; simp at this; linarith
    rw [abs_of_neg hn0] at an bn
    rw [abs_of_neg hm0] at am bm
    have h1 : (n : ℝ) ≤ Real.exp (u - a) := by
      rw [← hnexp]; exact Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (u - 2 * a) < (m : ℝ) := by
      rw [← hmexp]; exact Real.exp_lt_exp.mpr (by linarith)
    have h3 : Real.exp (u - a) = Real.exp (u - 2 * a) * Real.exp a := by
      rw [← Real.exp_add]; ring_nf
    have h4 : Real.exp (u - 2 * a) * (Real.exp a - 1) ≤ (m : ℝ) * (Real.exp a - 1) :=
      mul_le_mul_of_nonneg_right h2.le hea0
    nlinarith

include hρ hδ in
/-- Near piece: `‖x^{k,s}(u)‖² ≤ ∑_n |y_n|² (4/(2^kδ)²) 1[u ∈ shell]`. -/
lemma near_normSq {k0 k : ℕ} {s : Bool} (hk : k < k0) (u : ℝ) :
    normSq (P.rangeZ Q T) (piece P Q T δ ρ y k0 u (k, s)) ≤
      ∑ n ∈ P.rangeZ Q T, (y n.toNat) ^ 2 * (4 / ((2 : ℝ) ^ k * δ) ^ 2) *
        (shellU δ k s n).indicator 1 u := by
  unfold normSq
  refine Finset.sum_le_sum fun n hn => ?_
  have hR : 0 ≤ (y n.toNat) ^ 2 * (4 / ((2 : ℝ) ^ k * δ) ^ 2) *
      (shellU δ k s n).indicator 1 u := by
    have : 0 ≤ (shellU δ k s n).indicator (1 : ℝ → ℝ) u :=
      Set.indicator_nonneg (fun _ _ => zero_le_one) u
    positivity
  by_cases hp : piece P Q T δ ρ y k0 u (k, s) n = 0
  · rw [hp, norm_zero]; simpa using hR
  · by_cases hin : shellIdx δ u k0 n = (k, s)
    swap
    · exact absurd (by unfold piece; rw [if_neg hin]) hp
    have hp' : xtail P Q T δ ρ y u n ≠ 0 := by
      intro h0; apply hp; unfold piece; rw [if_pos hin, h0]
    obtain ⟨a1, a2, as⟩ := shell_facts P hρ hδ y hk hin hp'
    have hmem := mem_shellU a1 a2 as
    have hind : (shellU δ k s n).indicator (1 : ℝ → ℝ) u = 1 := by
      simp [Set.indicator_of_mem hmem]
    have hpos : 0 < (2 : ℝ) ^ k * δ := by positivity
    have hξ : xiU u n ≠ 0 := by
      intro h0; rw [h0, abs_zero] at a1; linarith
    have hnorm := xtail_norm_sq_le P hρ (Q := Q) (T := T) (δ := δ) y hξ
    have hsq : ((2 : ℝ) ^ k * δ) ^ 2 ≤ (xiU u n) ^ 2 := by
      rw [← sq_abs (xiU u n)]; exact pow_le_pow_left₀ hpos.le a1 2
    have h4 : 4 / (xiU u n) ^ 2 ≤ 4 / ((2 : ℝ) ^ k * δ) ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq
    unfold piece
    rw [if_pos hin, hind, mul_one]
    calc ‖xtail P Q T δ ρ y u n‖ ^ 2 ≤ (y n.toNat) ^ 2 * (4 / (xiU u n) ^ 2) := hnorm
      _ ≤ (y n.toNat) ^ 2 * (4 / ((2 : ℝ) ^ k * δ) ^ 2) :=
          mul_le_mul_of_nonneg_left h4 (sq_nonneg _)

include hρ hδ in
/-- Far piece: `‖x^{far}(u)‖² ≤ ∑_n |y_n|² tailK_{2^{k₀}δ/2}(u − log n)`. -/
lemma far_normSq {k0 : ℕ} (u : ℝ) :
    normSq (P.rangeZ Q T) (piece P Q T δ ρ y k0 u (k0, true)) ≤
      ∑ n ∈ P.rangeZ Q T, (y n.toNat) ^ 2 *
        PrimeSetup.tailK ((2 : ℝ) ^ k0 * δ / 2) (u - Real.log (n.toNat : ℝ)) := by
  unfold normSq
  refine Finset.sum_le_sum fun n hn => ?_
  have hR : 0 ≤ (y n.toNat) ^ 2 *
      PrimeSetup.tailK ((2 : ℝ) ^ k0 * δ / 2) (u - Real.log (n.toNat : ℝ)) :=
    mul_nonneg (sq_nonneg _) (PrimeSetup.tailK_nonneg _ _)
  by_cases hp : piece P Q T δ ρ y k0 u (k0, true) n = 0
  · rw [hp, norm_zero]; simpa using hR
  · by_cases hin : shellIdx δ u k0 n = (k0, true)
    swap
    · exact absurd (by unfold piece; rw [if_neg hin]) hp
    have hp' : xtail P Q T δ ρ y u n ≠ 0 := by
      intro h0; apply hp; unfold piece; rw [if_pos hin, h0]
    have hfar := far_facts P hρ hδ y hin hp'
    have hpos : 0 < (2 : ℝ) ^ k0 * δ := by positivity
    have hξ : xiU u n ≠ 0 := by
      intro h0; rw [h0, abs_zero] at hfar; linarith
    have hnorm := xtail_norm_sq_le P hρ (Q := Q) (T := T) (δ := δ) y hξ
    have htail : PrimeSetup.tailK ((2 : ℝ) ^ k0 * δ / 2) (u - Real.log (n.toNat : ℝ)) =
        4 / (xiU u n) ^ 2 := by
      unfold PrimeSetup.tailK
      have habs : |u - Real.log (n.toNat : ℝ)| = |xiU u n| := by
        unfold xiU; rw [abs_sub_comm]
      rw [if_pos (by rw [habs]; linarith)]
      congr 1; unfold xiU; ring
    unfold piece
    rw [if_pos hin, htail]
    exact hnorm

end pieces

/-- The pointwise majorant of `x^t(u)^*Δx^t(u)`, up to the factor `(2k₀+1) w_max C₀`. -/
def majorant (P : HSetup) (Q T δ : ℝ) (k0 : ℕ) (y : ℕ → ℝ) (u : ℝ) : ℝ :=
  (∑ k ∈ Finset.range k0, ∑ s : Bool, (Q ^ 2 + 2 * ((2 : ℝ) ^ k * δ) * P.Y Q T + 1) *
      ∑ n ∈ P.rangeZ Q T, (y n.toNat) ^ 2 * (4 / ((2 : ℝ) ^ k * δ) ^ 2) *
        (shellU δ k s n).indicator 1 u) +
  (Q ^ 2 + P.Y Q T + 1) * ∑ n ∈ P.rangeZ Q T, (y n.toNat) ^ 2 *
      PrimeSetup.tailK ((2 : ℝ) ^ k0 * δ / 2) (u - Real.log (n.toNat : ℝ))

/-- The pointwise bound: `x^t(u)^*Δx^t(u) ≤ (2k₀+1) w_max C₀ · majorant(u)`. -/
lemma tail_pointwise {C₀ : ℝ} (hMV : MVLargeSieveMult C₀) (hC₀ : 0 ≤ C₀) (P : HSetup) (W : Weight)
    {ρ : ℝ → ℝ} (hρ : IsLocCutoff ρ) {Q T δ : ℝ} (hQ : 1 ≤ Q) (hδ : 0 < δ) {k0 : ℕ}
    (hk0 : ∀ k < k0, (2 : ℝ) ^ k * δ ≤ 1) (y : ℕ → ℝ) (u : ℝ) :
    famForm W Q (P.rangeZ Q T) (xtail P Q T δ ρ y u) ≤
      (2 * k0 + 1) * (W.wmax * C₀) * majorant P Q T δ k0 y u := by
  set I := P.rangeZ Q T
  set f : ℕ × Bool → ℝ := fun i => famForm W Q I (piece P Q T δ ρ y k0 u i) with hf
  have hf0 : ∀ i, 0 ≤ f i := fun i => famForm_nonnegH W Q I _
  have hw := W.wmax_nonneg
  have hwC : 0 ≤ W.wmax * C₀ := mul_nonneg hw hC₀
  -- Cauchy–Schwarz over the pieces
  have h1 : famForm W Q I (xtail P Q T δ ρ y u) ≤ (2 * k0 + 1) * ∑ i ∈ shellSet k0, f i := by
    rw [xtail_eq_sum P Q T δ ρ y k0 u]
    refine (famForm_sum_le W Q I (shellSet k0) _).trans ?_
    exact mul_le_mul_of_nonneg_right (card_shellSet k0) (Finset.sum_nonneg fun i _ => hf0 i)
  -- split the index set
  have hdisj : Disjoint (Finset.range k0 ×ˢ (Finset.univ : Finset Bool)) {(k0, true)} := by
    rw [Finset.disjoint_singleton_right]; simp
  have hsplit : ∑ i ∈ shellSet k0, f i =
      (∑ k ∈ Finset.range k0, ∑ s : Bool, f (k, s)) + f (k0, true) := by
    unfold shellSet
    rw [Finset.sum_union hdisj, Finset.sum_product, Finset.sum_singleton]
  -- bounds on the pieces
  have hnear : ∀ k ∈ Finset.range k0, ∀ s : Bool,
      f (k, s) ≤ W.wmax * C₀ * ((Q ^ 2 + 2 * ((2 : ℝ) ^ k * δ) * P.Y Q T + 1) *
        ∑ n ∈ I, (y n.toNat) ^ 2 * (4 / ((2 : ℝ) ^ k * δ) ^ 2) *
          (shellU δ k s n).indicator 1 u) := by
    intro k hk s
    have hk' : k < k0 := Finset.mem_range.mp hk
    have hd := famForm_le_of_diam hMV hC₀ W hQ I (piece P Q T δ ρ y k0 u (k, s))
      (near_diam P hρ hδ y hk' (hk0 k hk') u)
    have hn := near_normSq P hρ hδ y (Q := Q) (T := T) (s := s) hk' u
    have hQ2 : 0 ≤ Q ^ 2 + 2 * ((2 : ℝ) ^ k * δ) * P.Y Q T + 1 := by
      have : 0 ≤ P.Y Q T := Real.rpow_nonneg (Real.exp_pos _).le _
      positivity
    calc f (k, s) ≤ W.wmax * C₀ * (Q ^ 2 + 2 * ((2 : ℝ) ^ k * δ) * P.Y Q T + 1) *
          normSq I (piece P Q T δ ρ y k0 u (k, s)) := hd
      _ ≤ W.wmax * C₀ * (Q ^ 2 + 2 * ((2 : ℝ) ^ k * δ) * P.Y Q T + 1) *
          ∑ n ∈ I, (y n.toNat) ^ 2 * (4 / ((2 : ℝ) ^ k * δ) ^ 2) *
            (shellU δ k s n).indicator 1 u :=
          mul_le_mul_of_nonneg_left hn (mul_nonneg hwC hQ2)
      _ = _ := by ring
  have hfar : f (k0, true) ≤ W.wmax * C₀ * ((Q ^ 2 + P.Y Q T + 1) *
      ∑ n ∈ I, (y n.toNat) ^ 2 *
        PrimeSetup.tailK ((2 : ℝ) ^ k0 * δ / 2) (u - Real.log (n.toNat : ℝ))) := by
    have hdiam : ∀ n ∈ I, ∀ m ∈ I, piece P Q T δ ρ y k0 u (k0, true) n ≠ 0 →
        piece P Q T δ ρ y k0 u (k0, true) m ≠ 0 → ((n : ℝ) - m) ≤ P.Y Q T := by
      intro n hn m hm _ _
      obtain ⟨-, nY⟩ := mem_rangeZ_bounds P hn
      obtain ⟨m1, -⟩ := mem_rangeZ_bounds P hm
      have : (1 : ℝ) ≤ m := by exact_mod_cast m1
      linarith
    have hd := famForm_le_of_diam hMV hC₀ W hQ I (piece P Q T δ ρ y k0 u (k0, true)) hdiam
    have hn := far_normSq P hρ hδ y (Q := Q) (T := T) (k0 := k0) u
    have hQ2 : 0 ≤ Q ^ 2 + P.Y Q T + 1 := by
      have : 0 ≤ P.Y Q T := Real.rpow_nonneg (Real.exp_pos _).le _
      positivity
    calc f (k0, true) ≤ W.wmax * C₀ * (Q ^ 2 + P.Y Q T + 1) *
          normSq I (piece P Q T δ ρ y k0 u (k0, true)) := hd
      _ ≤ W.wmax * C₀ * (Q ^ 2 + P.Y Q T + 1) * ∑ n ∈ I, (y n.toNat) ^ 2 *
          PrimeSetup.tailK ((2 : ℝ) ^ k0 * δ / 2) (u - Real.log (n.toNat : ℝ)) :=
          mul_le_mul_of_nonneg_left hn (mul_nonneg hwC hQ2)
      _ = _ := by ring
  have h2 : ∑ i ∈ shellSet k0, f i ≤ W.wmax * C₀ * majorant P Q T δ k0 y u := by
    rw [hsplit]
    unfold majorant
    rw [mul_add, Finset.mul_sum]
    refine add_le_add (Finset.sum_le_sum fun k hk => ?_) hfar
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun s _ => hnear k hk s
  have hk0' : (0 : ℝ) ≤ 2 * k0 + 1 := by positivity
  calc famForm W Q I (xtail P Q T δ ρ y u) ≤ (2 * k0 + 1) * ∑ i ∈ shellSet k0, f i := h1
    _ ≤ (2 * k0 + 1) * (W.wmax * C₀ * majorant P Q T δ k0 y u) :=
        mul_le_mul_of_nonneg_left h2 hk0'
    _ = _ := by ring

/-! ### Integration in `u` -/

lemma shellU_measurable (δ : ℝ) (k : ℕ) (s : Bool) (n : ℤ) : MeasurableSet (shellU δ k s n) := by
  unfold shellU; cases s
  · simp only [Bool.false_eq_true, if_false]; exact measurableSet_Ico
  · simp only [if_true]; exact measurableSet_Ioc

lemma shellU_real {δ : ℝ} (hδ : 0 < δ) (k : ℕ) (s : Bool) (n : ℤ) :
    volume.real (shellU δ k s n) = (2 : ℝ) ^ k * δ := by
  have h2 : (2 : ℝ) ^ (k + 1) * δ = 2 * ((2 : ℝ) ^ k * δ) := by rw [pow_succ]; ring
  have hpos : 0 < (2 : ℝ) ^ k * δ := by positivity
  unfold shellU; cases s
  · simp only [Bool.false_eq_true, if_false, Measure.real, Real.volume_Ico]
    rw [ENNReal.toReal_ofReal (by linarith)]; linarith
  · simp only [if_true, Measure.real, Real.volume_Ioc]
    rw [ENNReal.toReal_ofReal (by linarith)]; linarith

lemma integrable_shell_ind (δ : ℝ) (k : ℕ) (s : Bool) (n : ℤ) :
    Integrable (fun u => (shellU δ k s n).indicator (1 : ℝ → ℝ) u) := by
  have hfin : volume (shellU δ k s n) ≠ ⊤ := by
    unfold shellU; cases s <;> simp [Real.volume_Ico, Real.volume_Ioc]
  exact (integrable_indicator_iff (shellU_measurable δ k s n)).mpr (integrableOn_const hfin)

lemma integrable_majorant (P : HSetup) {Q T δ : ℝ} (hδ : 0 < δ) (k0 : ℕ) (y : ℕ → ℝ) :
    Integrable (majorant P Q T δ k0 y) := by
  have hd : 0 < (2 : ℝ) ^ k0 * δ / 2 := by positivity
  unfold majorant
  refine Integrable.add ?_ ?_
  · refine integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun s _ => ?_
    refine Integrable.const_mul ?_ _
    refine integrable_finsetSum _ fun n _ => ?_
    exact (integrable_shell_ind δ k s n).const_mul _
  · refine Integrable.const_mul ?_ _
    refine integrable_finsetSum _ fun n _ => ?_
    exact ((PrimeSetup.tailK_integrable hd).comp_sub_right _).const_mul _

lemma integral_majorant (P : HSetup) {Q T δ : ℝ} (hδ : 0 < δ) (k0 : ℕ) (y : ℕ → ℝ) :
    ∫ u, majorant P Q T δ k0 y u =
      (∑ k ∈ Finset.range k0, ∑ _s : Bool, (Q ^ 2 + 2 * ((2 : ℝ) ^ k * δ) * P.Y Q T + 1) *
        ∑ n ∈ P.rangeZ Q T, (y n.toNat) ^ 2 * (4 / ((2 : ℝ) ^ k * δ) ^ 2) * ((2 : ℝ) ^ k * δ)) +
      (Q ^ 2 + P.Y Q T + 1) * ∑ n ∈ P.rangeZ Q T, (y n.toNat) ^ 2 *
        (8 / ((2 : ℝ) ^ k0 * δ / 2)) := by
  have hd : 0 < (2 : ℝ) ^ k0 * δ / 2 := by positivity
  unfold majorant
  rw [integral_add]
  · congr 1
    · rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun s _ =>
        (integrable_finsetSum _ fun n _ => (integrable_shell_ind δ k s n).const_mul _).const_mul _]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_finsetSum _ fun s _ =>
        (integrable_finsetSum _ fun n _ => (integrable_shell_ind δ k s n).const_mul _).const_mul _]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [integral_const_mul, integral_finsetSum _ fun n _ =>
        (integrable_shell_ind δ k s n).const_mul _]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [integral_const_mul, integral_indicator_one (shellU_measurable δ k s n),
        shellU_real hδ k s n]
    · rw [integral_const_mul, integral_finsetSum _ fun n _ =>
        ((PrimeSetup.tailK_integrable hd).comp_sub_right _).const_mul _]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [integral_const_mul, integral_sub_right_eq_self (fun u => PrimeSetup.tailK _ u),
        PrimeSetup.tailK_integral hd]
  · exact integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun s _ =>
      (integrable_finsetSum _ fun n _ => (integrable_shell_ind δ k s n).const_mul _).const_mul _
  · exact (integrable_finsetSum _ fun n _ =>
      ((PrimeSetup.tailK_integrable hd).comp_sub_right _).const_mul _).const_mul _

lemma integral_majorant_le (P : HSetup) {Q T δ : ℝ} (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) {k0 : ℕ}
    (hfar : 1 ≤ (2 : ℝ) ^ k0 * δ) (y : ℕ → ℝ) :
    ∫ u, majorant P Q T δ k0 y u ≤
      (20 * ((Q ^ 2 + 1) / δ) + 16 * ((k0 : ℝ) + 1) * P.Y Q T) *
        ∑ n ∈ P.rangeZ Q T, (y n.toNat) ^ 2 := by
  rw [integral_majorant P hδ k0 y]
  set S2 := ∑ n ∈ P.rangeZ Q T, (y n.toNat) ^ 2 with hS2
  have hS0 : 0 ≤ S2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hY : 0 ≤ P.Y Q T := Real.rpow_nonneg (Real.exp_pos _).le _
  have hQ1 : 0 ≤ Q ^ 2 + 1 := by positivity
  -- the near shells, one `k` at a time
  have hk : ∀ k : ℕ, ∑ s : Bool, (Q ^ 2 + 2 * ((2 : ℝ) ^ k * δ) * P.Y Q T + 1) *
        ∑ n ∈ P.rangeZ Q T, (y n.toNat) ^ 2 * (4 / ((2 : ℝ) ^ k * δ) ^ 2) * ((2 : ℝ) ^ k * δ) =
      (8 * ((Q ^ 2 + 1) / δ) * (1 / 2) ^ k + 16 * P.Y Q T) * S2 := by
    intro k
    rw [Fintype.sum_bool]
    have hsum : ∑ n ∈ P.rangeZ Q T, (y n.toNat) ^ 2 * (4 / ((2 : ℝ) ^ k * δ) ^ 2) *
        ((2 : ℝ) ^ k * δ) = S2 * (4 / ((2 : ℝ) ^ k * δ)) := by
      rw [hS2, ← Finset.sum_mul, ← Finset.sum_mul]
      have h2k : (2 : ℝ) ^ k * δ ≠ 0 := by positivity
      field_simp
    rw [hsum]
    have h2k : (2 : ℝ) ^ k ≠ 0 := by positivity
    have hδ0 : δ ≠ 0 := hδ.ne'
    rw [one_div_pow]
    field_simp
    ring
  rw [Finset.sum_congr rfl fun k _ => hk k, ← Finset.sum_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hgeo := sum_geometric_two_le k0
  have hA : 0 ≤ (Q ^ 2 + 1) / δ := div_nonneg hQ1 hδ.le
  -- the far piece
  have hfar' : (Q ^ 2 + P.Y Q T + 1) * ∑ n ∈ P.rangeZ Q T, (y n.toNat) ^ 2 *
      (8 / ((2 : ℝ) ^ k0 * δ / 2)) ≤ (4 * ((Q ^ 2 + 1) / δ) + 16 * P.Y Q T) * S2 := by
    have hdpos : 0 < (2 : ℝ) ^ k0 * δ := by positivity
    have h16 : 8 / ((2 : ℝ) ^ k0 * δ / 2) ≤ 16 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have hsum : ∑ n ∈ P.rangeZ Q T, (y n.toNat) ^ 2 * (8 / ((2 : ℝ) ^ k0 * δ / 2)) =
        S2 * (8 / ((2 : ℝ) ^ k0 * δ / 2)) := by rw [hS2, Finset.sum_mul]
    rw [hsum]
    have h4 : 16 * (Q ^ 2 + 1) ≤ 4 * ((Q ^ 2 + 1) / δ) := by
      rw [mul_div_assoc', le_div_iff₀ hδ]; nlinarith
    have hX : (Q ^ 2 + P.Y Q T + 1) * (S2 * (8 / ((2 : ℝ) ^ k0 * δ / 2))) ≤
        (Q ^ 2 + P.Y Q T + 1) * (S2 * 16) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h16 hS0) (by positivity)
    nlinarith
  have hnear : (8 * ((Q ^ 2 + 1) / δ) * ∑ k ∈ Finset.range k0, (1 / 2 : ℝ) ^ k +
      (k0 : ℝ) * (16 * P.Y Q T)) * S2 ≤ (16 * ((Q ^ 2 + 1) / δ) + 16 * (k0 : ℝ) * P.Y Q T) * S2 := by
    apply mul_le_mul_of_nonneg_right _ hS0
    have := mul_le_mul_of_nonneg_left hgeo (show 0 ≤ 8 * ((Q ^ 2 + 1) / δ) by positivity)
    nlinarith
  linarith

/-- **`lem:M3prime`** (Lemma 9.13). -/
theorem lemM3primeH_proof : lemM3primeH_Statement := by
  intro C₀ hMV hC₀ P W ρ hρ Q T δ hQ hT hδ hδ4 y g1 ginf hg1 hgb xt k0
  have hk0def : k0 = ⌈Real.logb 2 (1 / δ)⌉₊ := rfl
  have hinvδ : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδ]; linarith
  have hlog0 : 0 ≤ Real.logb 2 (1 / δ) := Real.logb_nonneg one_lt_two hinvδ
  have hrpow : (2 : ℝ) ^ Real.logb 2 (1 / δ) = 1 / δ :=
    Real.rpow_logb two_pos (by norm_num) (by positivity)
  have hfar : 1 ≤ (2 : ℝ) ^ k0 * δ := by
    have h1 : Real.logb 2 (1 / δ) ≤ (k0 : ℝ) := Nat.le_ceil _
    have h2 : (2 : ℝ) ^ Real.logb 2 (1 / δ) ≤ (2 : ℝ) ^ (k0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
    rw [hrpow, Real.rpow_natCast] at h2
    rw [div_le_iff₀ hδ] at h2; linarith
  have hnear : ∀ k < k0, (2 : ℝ) ^ k * δ ≤ 1 := by
    intro k hk
    have h1 : (k0 : ℝ) < Real.logb 2 (1 / δ) + 1 := Nat.ceil_lt_add_one hlog0
    have h2 : (k : ℝ) + 1 ≤ k0 := by exact_mod_cast hk
    have h3 : (2 : ℝ) ^ (k : ℝ) < (2 : ℝ) ^ Real.logb 2 (1 / δ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    rw [hrpow, Real.rpow_natCast] at h3
    rw [lt_div_iff₀ hδ] at h3; linarith
  have hginf : 0 ≤ ginf := (hgb 0).1.trans (hgb 0).2
  have hw := W.wmax_nonneg
  set M := majorant P Q T δ k0 y with hM
  have hMint : Integrable M := integrable_majorant P hδ k0 y
  have hpt : ∀ u, g1 u * famForm W Q (P.rangeZ Q T) (xt u) ≤
      ginf * ((2 * k0 + 1) * (W.wmax * C₀) * M u) := by
    intro u
    have h1 : famForm W Q (P.rangeZ Q T) (xt u) ≤ (2 * k0 + 1) * (W.wmax * C₀) * M u :=
      tail_pointwise hMV hC₀ P W hρ (T := T) hQ hδ hnear y u
    have h0 := famForm_nonnegH W Q (P.rangeZ Q T) (xt u)
    calc g1 u * famForm W Q (P.rangeZ Q T) (xt u) ≤ ginf * famForm W Q (P.rangeZ Q T) (xt u) :=
          mul_le_mul_of_nonneg_right (hgb u).2 h0
      _ ≤ ginf * ((2 * k0 + 1) * (W.wmax * C₀) * M u) := mul_le_mul_of_nonneg_left h1 hginf
  have hint : ∫ u, g1 u * famForm W Q (P.rangeZ Q T) (xt u) ≤
      ∫ u, ginf * ((2 * k0 + 1) * (W.wmax * C₀) * M u) :=
    integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun u => mul_nonneg (hgb u).1 (famForm_nonnegH W Q _ _))
      ((hMint.const_mul _).const_mul _) (Filter.Eventually.of_forall hpt)
  rw [integral_const_mul, integral_const_mul] at hint
  have hMle := integral_majorant_le P (Q := Q) (T := T) hδ hδ4 hfar y
  have hsum : ∑ n ∈ P.rangeZ Q T, (y n.toNat) ^ 2 = ∑ n ∈ P.range Q T, y n ^ 2 :=
    P.toPS.sum_rangeZ (Q * T) (fun k => y k ^ 2)
  rw [hsum] at hMle
  set S := ∑ n ∈ P.range Q T, y n ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hY : 0 ≤ P.Y Q T := Real.rpow_nonneg (Real.exp_pos _).le _
  set A := (Q ^ 2 + 1) / δ with hA
  have hA0 : 0 ≤ A := div_nonneg (by positivity) hδ.le
  set K : ℝ := (k0 : ℝ) with hK
  have hK0 : 0 ≤ K := Nat.cast_nonneg _
  have hc : 0 ≤ ginf * ((2 * K + 1) * (W.wmax * C₀)) := by positivity
  have hstep : ginf * ((2 * K + 1) * (W.wmax * C₀) * ∫ u, M u) ≤
      ginf * ((2 * K + 1) * (W.wmax * C₀) * ((20 * A + 16 * (K + 1) * P.Y Q T) * S)) := by
    have := mul_le_mul_of_nonneg_left hMle hc
    nlinarith
  have hpoly : (2 * K + 1) * (20 * A + 16 * (K + 1) * P.Y Q T) ≤
      48 * (K + 4) * (A + (K + 3) * P.Y Q T) := by
    nlinarith [mul_nonneg hK0 hA0, mul_nonneg hK0 hY, mul_nonneg (mul_nonneg hK0 hK0) hY]
  have hfin : ginf * ((2 * K + 1) * (W.wmax * C₀) * ((20 * A + 16 * (K + 1) * P.Y Q T) * S)) ≤
      48 * C₀ * ginf * W.wmax * (K + 4) * (A + (K + 3) * P.Y Q T) * S := by
    have hpos : 0 ≤ ginf * W.wmax * C₀ * S := by positivity
    have := mul_le_mul_of_nonneg_left hpoly hpos
    nlinarith
  calc ∫ u, g1 u * famForm W Q (P.rangeZ Q T) (xt u)
      ≤ ginf * ((2 * K + 1) * (W.wmax * C₀) * ∫ u, M u) := hint
    _ ≤ _ := hstep
    _ ≤ _ := hfin

end F

end Families.Hybrid
