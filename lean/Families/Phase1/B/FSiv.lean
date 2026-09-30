/-
# `lem:fS` (iv)  (Lemma 6.19 and its proof)

`lemfS_iv_proof`: for disjoint `S₁, S₂` and `M ≥ sup R_{S₁}`,
`R_{S₁∪S₂}(t) ≤ R_{S₁}(t) + ½ δ_{S₂} M`, `δ_{S₂} = ∏_{p∈S₂}(1 + 2/(p³(p−1))) − 1`.

Proof (a one-prime-at-a-time version of the TeX's `f_S = f_{S₁} * λ_{S₂}`). For a prime `q ∉ S`,
`f_{S∪{q}}(n) = ∑_{b ≤ v_q(n)} λ_b f_S(n/q^b)`, where `λ_0 = 1`, `λ_1 = −1/(q²(q−1))`,
`λ_{b+2} = c^b λ_2`, `c = (q+1)/q²`, `λ_2 = (q³−q−1)/(q⁴(q−1))` (the coefficients of
`(1 − X/(q−1) + X²/(q(q−1)))/(1 − cX)`, as in the TeX). Hence
`R_{S∪{q}}(t) = ∑_b λ_b q^{−b} R_S(q^b t) ≤ R_S(t) + x_q M'` with `x_q = ∑_{b≥2} λ_b q^{−b} = 1/(q³(q−1))`
(`λ_1 < 0`, `R_S ≥ 0`, `R_S ≤ M'`). Adding the primes of `S₂` one by one gives the factor
`∏(1 + x_p) − 1 ≤ ½(∏(1 + 2x_p) − 1)`.
-/
import Families.Phase1.B.LocalMult
import Families.Constants

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius
open ArithmeticFunction Finset

namespace Families.Phase1.B

open Families

/-! ### The coefficients `λ_b` at one prime `q` -/

/-- `c = (q+1)/q²`. -/
def lamc (q : ℕ) : ℝ := ((q : ℝ) + 1) / (q : ℝ) ^ 2

/-- `λ_2 = (q³−q−1)/(q⁴(q−1))`. -/
def lam2 (q : ℕ) : ℝ := ((q : ℝ) ^ 3 - q - 1) / ((q : ℝ) ^ 4 * (q - 1))

/-- `λ_b`. -/
def lamq (q : ℕ) : ℕ → ℝ
  | 0 => 1
  | 1 => -1 / ((q : ℝ) ^ 2 * (q - 1))
  | b + 2 => lamc q ^ b * lam2 q

/-- `β = f_S(q^a) = 1 − 1/q − 1/q²` for `q ∉ S`, `a ≥ 1`. -/
def betaq (q : ℕ) : ℝ := 1 - 1 / (q : ℝ) - 1 / (q : ℝ) ^ 2

/-- `x_q = 1/(q³(q−1))`. -/
def xq (q : ℕ) : ℝ := 1 / ((q : ℝ) ^ 3 * (q - 1))

section local_identities

variable {q : ℕ} (hq : q.Prime)
include hq

private lemma q2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le

omit hq in
lemma lamq_succ {b : ℕ} (hb : 2 ≤ b) : lamq q (b + 1) = lamc q * lamq q b := by
  obtain ⟨k, rfl⟩ : ∃ k, b = k + 2 := ⟨b - 2, by omega⟩
  show lamc q ^ (k + 1) * lam2 q = lamc q * (lamc q ^ k * lam2 q)
  ring

lemma lamq_one_neg : lamq q 1 < 0 := by
  have := q2 hq
  show -1 / ((q : ℝ) ^ 2 * (q - 1)) < 0
  exact div_neg_of_neg_of_pos (by norm_num) (mul_pos (by positivity) (by linarith))

lemma lam2_pos : 0 < lam2 q := by
  have := q2 hq
  unfold lam2
  apply div_pos _ (mul_pos (by positivity) (by linarith))
  have h4 : (4 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
  nlinarith

lemma lamc_pos : 0 < lamc q := by
  have := q2 hq
  unfold lamc; positivity

lemma lamq_nonneg {b : ℕ} (hb : 2 ≤ b) : 0 ≤ lamq q b := by
  obtain ⟨k, rfl⟩ : ∃ k, b = k + 2 := ⟨b - 2, by omega⟩
  exact mul_nonneg (pow_nonneg (lamc_pos hq).le _) (lam2_pos hq).le

/-- `β + λ_1 = (q−2)/(q−1)`. -/
lemma betaq_add_lam1 : betaq q + lamq q 1 = ((q : ℝ) - 2) / (q - 1) := by
  have := q2 hq
  have h1 : (q : ℝ) - 1 ≠ 0 := by linarith
  have h0 : (q : ℝ) ≠ 0 := by linarith
  show 1 - 1 / (q : ℝ) - 1 / (q : ℝ) ^ 2 + -1 / ((q : ℝ) ^ 2 * (q - 1)) = _
  field_simp; ring

/-- `β Λ(a) + λ_{a+1} = (q−1)/q` for `a ≥ 1`, `Λ(a) = ∑_{b ≤ a} λ_b`. -/
lemma betaq_mul_sum_add (a : ℕ) (ha : 1 ≤ a) :
    betaq q * (∑ b ∈ Finset.range (a + 1), lamq q b) + lamq q (a + 1) = ((q : ℝ) - 1) / q := by
  have hq2 := q2 hq
  have h1 : (q : ℝ) - 1 ≠ 0 := by linarith
  have h0 : (q : ℝ) ≠ 0 := by linarith
  induction a, ha using Nat.le_induction with
  | base =>
    simp only [Finset.sum_range_succ, Finset.range_one, Finset.sum_singleton]
    show betaq q * (1 + -1 / ((q : ℝ) ^ 2 * (q - 1))) + lamc q ^ 0 * lam2 q = _
    unfold betaq lam2
    field_simp; ring
  | succ a ha ih =>
    rw [Finset.sum_range_succ, lamq_succ (show 2 ≤ a + 1 by omega)]
    have hc : betaq q + lamc q - 1 = 0 := by
      unfold betaq lamc; field_simp; ring
    linear_combination ih + lamq q (a + 1) * hc

/-- The local convolution `∑_{b ≤ a} λ_b f_S(q^{a−b})` (`f_S(q^0) = 1`, `f_S(q^k) = β`). -/
lemma local_conv (a : ℕ) :
    ∑ b ∈ Finset.range (a + 1), lamq q b * (if a - b = 0 then 1 else betaq q) =
      if a = 0 then 1 else if a = 1 then ((q : ℝ) - 2) / (q - 1) else ((q : ℝ) - 1) / q := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [lamq]
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  rw [Finset.sum_range_succ, Nat.sub_self, if_pos rfl, mul_one, if_neg (show a' + 1 ≠ 0 by omega)]
  have hsplit : ∑ b ∈ Finset.range (a' + 1), lamq q b * (if a' + 1 - b = 0 then 1 else betaq q) =
      betaq q * ∑ b ∈ Finset.range (a' + 1), lamq q b := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [if_neg (by have := Finset.mem_range.mp hb; omega)]; ring
  rw [hsplit]
  rcases Nat.eq_zero_or_pos a' with rfl | ha'
  · simp only [zero_add, Finset.range_one, Finset.sum_singleton, if_true]
    show betaq q * 1 + lamq q 1 = _
    rw [mul_one, betaq_add_lam1 hq]
  · rw [if_neg (by omega)]
    exact betaq_mul_sum_add hq a' ha'

/-- `∑_{b ∈ [2,N)} λ_b q^{−b} = x_q (1 − (c/q)^{N−2})` for `N ≥ 2`. -/
lemma sum_lam_tail_eq (N : ℕ) (hN : 2 ≤ N) :
    ∑ b ∈ Finset.range N, (if 2 ≤ b then lamq q b / (q : ℝ) ^ b else 0) =
      xq q * (1 - (lamc q / q) ^ (N - 2)) := by
  have hq2 := q2 hq
  have h1 : (q : ℝ) - 1 ≠ 0 := by linarith
  have h0 : (q : ℝ) ≠ 0 := by linarith
  induction N, hN using Nat.le_induction with
  | base => simp [Finset.sum_range_succ]
  | succ N hN ih =>
    rw [Finset.sum_range_succ, ih, if_pos hN]
    obtain ⟨k, rfl⟩ : ∃ k, N = k + 2 := ⟨N - 2, by omega⟩
    simp only [show k + 2 + 1 - 2 = k + 1 by omega, show k + 2 - 2 = k by omega]
    show xq q * (1 - (lamc q / q) ^ k) + lamc q ^ k * lam2 q / (q : ℝ) ^ (k + 2) =
      xq q * (1 - (lamc q / q) ^ (k + 1))
    have hkey : lam2 q / (q : ℝ) ^ 2 = xq q * (1 - lamc q / q) := by
      unfold xq lamc lam2; field_simp; ring
    have e : lamc q ^ k * lam2 q / (q : ℝ) ^ (k + 2) = lam2 q / (q : ℝ) ^ 2 * (lamc q / q) ^ k := by
      rw [div_pow, pow_add]; field_simp
    rw [e, hkey, pow_succ]
    ring

lemma sum_lam_tail_le (N : ℕ) :
    ∑ b ∈ Finset.range N, (if 2 ≤ b then lamq q b / (q : ℝ) ^ b else 0) ≤ xq q := by
  have hq2 := q2 hq
  rcases lt_or_ge N 2 with hN | hN
  · have : ∑ b ∈ Finset.range N, (if 2 ≤ b then lamq q b / (q : ℝ) ^ b else 0) = 0 :=
      Finset.sum_eq_zero fun b hb => by rw [if_neg (by have := Finset.mem_range.mp hb; omega)]
    rw [this]; unfold xq
    exact div_nonneg zero_le_one (mul_nonneg (by positivity) (by linarith))
  · rw [sum_lam_tail_eq hq N hN]
    have hx : 0 ≤ xq q := by
      unfold xq; exact div_nonneg zero_le_one (mul_nonneg (by positivity) (by linarith))
    have hr : 0 ≤ (lamc q / q) ^ (N - 2) := pow_nonneg (div_nonneg (lamc_pos hq).le (by linarith)) _
    nlinarith

end local_identities

/-! ### `f_{S ∪ {q}}` in terms of `f_S` -/

lemma fSpp_nonneg (S : Finset ℕ) {p : ℕ} (hp : p.Prime) (a : ℕ) : 0 ≤ fSpp S p a := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  unfold fSpp
  split_ifs
  · exact div_nonneg (by linarith) (by linarith)
  · exact div_nonneg (by linarith) (by linarith)
  · have : 1 / (p : ℝ) ≤ 1 / 2 := by rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    have : 1 / (p : ℝ) ^ 2 ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith

lemma fS_nonneg (S : Finset ℕ) (n : ℕ) : 0 ≤ fS S n :=
  Finset.prod_nonneg fun _ hp => fSpp_nonneg S (Nat.prime_of_mem_primeFactors hp) _

lemma fS_insert_of_not_dvd (S : Finset ℕ) {q m : ℕ} (hqm : ¬ q ∣ m) :
    fS (insert q S) m = fS S m := by
  unfold fS
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpq : p ≠ q := fun h => hqm (h ▸ Nat.dvd_of_mem_primeFactors hp)
  unfold fSpp
  simp only [Finset.mem_insert, hpq, false_or]

lemma fS_insert_of_not_prime (S : Finset ℕ) {q : ℕ} (hq : ¬ q.Prime) (m : ℕ) :
    fS (insert q S) m = fS S m := by
  unfold fS
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpq : p ≠ q := fun h => hq (h ▸ Nat.prime_of_mem_primeFactors hp)
  unfold fSpp
  simp only [Finset.mem_insert, hpq, false_or]

lemma fS_prime_pow_of_not_mem (S : Finset ℕ) {q : ℕ} (hq : q.Prime) (hqS : q ∉ S) (k : ℕ) :
    fS S (q ^ k) = if k = 0 then 1 else betaq q := by
  rw [show fS S = locProd (fSpp S) from rfl, locProd_prime_pow' _ hq]
  unfold fSpp betaq
  simp [hqS]

lemma fS_insert_prime_pow (S : Finset ℕ) {q : ℕ} (hq : q.Prime) (a : ℕ) :
    fS (insert q S) (q ^ a) =
      if a = 0 then 1 else if a = 1 then ((q : ℝ) - 2) / (q - 1) else ((q : ℝ) - 1) / q := by
  rw [show fS (insert q S) = locProd (fSpp (insert q S)) from rfl, locProd_prime_pow' _ hq]
  unfold fSpp
  simp only [Finset.mem_insert_self, if_true]

lemma fS_mul_of_coprime (S : Finset ℕ) {m n : ℕ} (h : m.Coprime n) :
    fS S (m * n) = fS S m * fS S n := locProd_mul _ h

/-- **The one-prime convolution:** `f_{S∪{q}}(n) = ∑_{b ≤ v_q(n)} λ_b f_S(n/q^b)` (`q ∉ S`). -/
theorem fS_insert_conv (S : Finset ℕ) {q : ℕ} (hq : q.Prime) (hqS : q ∉ S) {n : ℕ} (hn : n ≠ 0) :
    fS (insert q S) n = ∑ b ∈ Finset.range (n.factorization q + 1), lamq q b * fS S (n / q ^ b) := by
  set v := n.factorization q with hv
  set m := n / q ^ v with hm
  have hnm : n = q ^ v * m := (Nat.ordProj_mul_ordCompl_eq_self n q).symm
  have hqm : ¬ q ∣ m := Nat.not_dvd_ordCompl hq hn
  have hcop : ∀ k, (q ^ k).Coprime m := fun k =>
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqm)
  have hL : fS (insert q S) n = fS (insert q S) (q ^ v) * fS S m := by
    conv_lhs => rw [hnm]
    rw [fS_mul_of_coprime _ (hcop v), fS_insert_of_not_dvd S hqm]
  have hR : ∀ b ∈ Finset.range (v + 1), lamq q b * fS S (n / q ^ b) =
      (lamq q b * (if v - b = 0 then 1 else betaq q)) * fS S m := by
    intro b hb
    have hbv : b ≤ v := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
    have hdiv : n / q ^ b = q ^ (v - b) * m := by
      conv_lhs => rw [hnm]
      rw [show v = (v - b) + b by omega, pow_add, mul_comm (q ^ (v - b)) (q ^ b), mul_assoc,
        Nat.mul_div_cancel_left _ (pow_pos hq.pos b), Nat.add_sub_cancel]
    rw [hdiv, fS_mul_of_coprime _ (hcop _), fS_prime_pow_of_not_mem S hq hqS]
    ring
  rw [hL, Finset.sum_congr rfl hR, ← Finset.sum_mul, local_conv hq v, fS_insert_prime_pow S hq]

/-! ### `R_{S∪{q}}` in terms of `R_S` -/

lemma RS_nonneg (W : Weight) (S : Finset ℕ) (t : ℝ) : 0 ≤ RS W S t := by
  unfold RS
  have hE : 0 < Ecal * W.Iw := mul_pos Ecal_pos W.Iw_pos
  refine mul_nonneg (inv_nonneg.mpr hE.le) (Finset.sum_nonneg fun n _ => ?_)
  refine mul_nonneg (div_nonneg (fS_nonneg S n) (Nat.cast_nonneg _)) ?_
  unfold Weight.wt; exact mul_nonneg (sq_nonneg _) (W.nonneg _)

/-- The rearrangement `∑_{n≤X} ∑_{b ≤ v_q(n)} G(b,n) = ∑_{b ≤ X} ∑_{j ≤ X/q^b} G(b, q^b j)`. -/
lemma sum_rearrange {q : ℕ} (hq : q.Prime) (X : ℕ) (G : ℕ → ℕ → ℝ) :
    ∑ n ∈ Finset.Icc 1 X, ∑ b ∈ Finset.range (n.factorization q + 1), G b n =
      ∑ b ∈ Finset.range (X + 1), ∑ j ∈ Finset.Icc 1 (X / q ^ b), G b (q ^ b * j) := by
  -- the inner range as a filter of `range (X+1)`
  have h1 : ∀ n ∈ Finset.Icc 1 X, Finset.range (n.factorization q + 1) =
      (Finset.range (X + 1)).filter (fun b => q ^ b ∣ n) := by
    intro n hn
    obtain ⟨hn1, hnX⟩ := Finset.mem_Icc.mp hn
    ext b
    simp only [Finset.mem_range, Finset.mem_filter]
    rw [hq.pow_dvd_iff_le_factorization (by omega)]
    have := Nat.factorization_lt q (show n ≠ 0 by omega)
    constructor
    · intro h; exact ⟨by omega, by omega⟩
    · intro h; omega
  rw [Finset.sum_congr rfl fun n hn => by rw [h1 n hn]]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_filter]
  have hqb : 0 < q ^ b := pow_pos hq.pos b
  refine Finset.sum_nbij' (fun n => n / q ^ b) (fun j => q ^ b * j) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    obtain ⟨hnI, hdvd⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1, hnX⟩ := Finset.mem_Icc.mp hnI
    rw [Finset.mem_Icc]
    refine ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hqb, Nat.div_le_div_right hnX⟩
  · intro j hj
    obtain ⟨hj1, hjX⟩ := Finset.mem_Icc.mp hj
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (by positivity), ?_⟩, dvd_mul_right _ _⟩
    exact (Nat.le_div_iff_mul_le hqb).mp hjX |>.trans_eq' (mul_comm _ _)
  · intro n hn
    exact Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2
  · intro j _
    exact Nat.mul_div_cancel_left j hqb
  · intro n hn
    rw [Nat.mul_div_cancel' (Finset.mem_filter.mp hn).2]

/-- **One prime.** If `q ∉ S` is prime and `R_S ≤ M'` on `(0,∞)`, then
`R_{S∪{q}}(t) ≤ R_S(t) + x_q M'`, `x_q = 1/(q³(q−1))`. -/
theorem RS_insert_le (W : Weight) (S : Finset ℕ) {q : ℕ} (hq : q.Prime) (hqS : q ∉ S) (M' : ℝ)
    (hM' : ∀ t, 0 < t → RS W S t ≤ M') (t : ℝ) (ht : 0 < t) :
    RS W (insert q S) t ≤ RS W S t + xq q * M' := by
  set X := ⌊1 / t⌋₊ with hX
  have hE : 0 < Ecal * W.Iw := mul_pos Ecal_pos W.Iw_pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  -- `R_{S∪{q}}(t) = ∑_b λ_b q^{−b} R_S(q^b t)`
  have hexp : RS W (insert q S) t =
      ∑ b ∈ Finset.range (X + 1), lamq q b / (q : ℝ) ^ b * RS W S ((q : ℝ) ^ b * t) := by
    unfold RS
    rw [← hX]
    have hconv : ∀ n ∈ Finset.Icc 1 X, fS (insert q S) n / n * W.wt (n * t) =
        ∑ b ∈ Finset.range (n.factorization q + 1),
          lamq q b * fS S (n / q ^ b) / n * W.wt (n * t) := by
      intro n hn
      rw [fS_insert_conv S hq hqS (by have := (Finset.mem_Icc.mp hn).1; omega), Finset.sum_div,
        Finset.sum_mul]
    rw [Finset.sum_congr rfl hconv, sum_rearrange hq X, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hfl : ⌊1 / ((q : ℝ) ^ b * t)⌋₊ = X / q ^ b := by
      rw [hX, show 1 / ((q : ℝ) ^ b * t) = (1 / t) / ((q ^ b : ℕ) : ℝ) by push_cast; field_simp,
        Nat.floor_div_natCast]
    rw [hfl]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Nat.mul_div_cancel_left j (pow_pos hq.pos b)]
    push_cast
    have hqb : (0 : ℝ) < (q : ℝ) ^ b := pow_pos hq0 b
    have e : ((q : ℝ) ^ b * j) * t = j * ((q : ℝ) ^ b * t) := by ring
    rw [e]
    field_simp
  -- termwise bounds
  have hRnn : ∀ s, 0 ≤ RS W S s := RS_nonneg W S
  have hterm : ∀ b ∈ Finset.range (X + 1), lamq q b / (q : ℝ) ^ b * RS W S ((q : ℝ) ^ b * t) ≤
      (if b = 0 then RS W S t else 0) + (if 2 ≤ b then lamq q b / (q : ℝ) ^ b else 0) * M' := by
    intro b _
    rcases Nat.lt_trichotomy b 1 with h | h | h
    · have : b = 0 := by omega
      subst this; simp [lamq]
    · subst h
      rw [if_neg (by norm_num), if_neg (by norm_num), zero_add, zero_mul]
      exact mul_nonpos_of_nonpos_of_nonneg
        (div_nonpos_of_nonpos_of_nonneg (lamq_one_neg hq).le (by positivity)) (hRnn _)
    · rw [if_neg (by omega), if_pos (by omega), zero_add]
      exact mul_le_mul_of_nonneg_left (hM' _ (by positivity))
        (div_nonneg (lamq_nonneg hq (by omega)) (by positivity))
  rw [hexp]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (Finset.range (X + 1)) 0, if_pos (by simp),
    ← Finset.sum_mul]
  have hM0 : 0 ≤ M' := (hRnn t).trans (hM' t ht)
  have := mul_le_mul_of_nonneg_right (sum_lam_tail_le hq (X + 1)) hM0
  linarith

/-! ### Adding `S₂` -/

lemma xq_nonneg {q : ℕ} (hq : q.Prime) : 0 ≤ xq q := by
  have : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  unfold xq; exact div_nonneg zero_le_one (mul_nonneg (by positivity) (by linarith))

lemma one_le_prod_of_one_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) (h : ∀ i ∈ s, 1 ≤ f i) :
    1 ≤ ∏ i ∈ s, f i := by
  have := Finset.prod_le_prod (s := s) (f := fun _ => (1 : ℝ)) (fun _ _ => zero_le_one) h
  simpa using this

/-- `∏(1 + x_i) − 1 ≤ ½(∏(1 + 2x_i) − 1)` for `x_i ≥ 0`. -/
lemma prod_one_add_sub_one_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) :
    ∏ i ∈ s, (1 + x i) - 1 ≤ 1 / 2 * (∏ i ∈ s, (1 + 2 * x i) - 1) := by
  have key : ∀ s' ⊆ s, 2 * ∏ i ∈ s', (1 + x i) - 1 ≤ ∏ i ∈ s', (1 + 2 * x i) ∧
      ∏ i ∈ s', (1 + x i) ≤ ∏ i ∈ s', (1 + 2 * x i) := by
    intro s' hs'
    induction s' using Finset.induction_on with
    | empty => simp; norm_num
    | insert i s' hi ih =>
      obtain ⟨ih1, ih2⟩ := ih ((Finset.subset_insert _ _).trans hs')
      have hxi := hx i (hs' (Finset.mem_insert_self _ _))
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      have hP : 1 ≤ ∏ i ∈ s', (1 + x i) :=
        one_le_prod_of_one_le _ _ fun j hj => by
          have := hx j (hs' (Finset.mem_insert_of_mem hj)); linarith
      constructor <;> nlinarith
  have := (key s le_rfl).1
  linarith

/-- The claim, by induction on `S₂`. -/
theorem RS_union_le (W : Weight) (S₁ S₂ : Finset ℕ) (hdisj : Disjoint S₁ S₂) (M : ℝ)
    (hM : ∀ t, 0 < t → RS W S₁ t ≤ M) (t : ℝ) (ht : 0 < t) :
    RS W (S₁ ∪ S₂) t ≤ RS W S₁ t + (∏ p ∈ S₂.filter Nat.Prime, (1 + xq p) - 1) * M := by
  have hM0 : 0 ≤ M := (RS_nonneg W S₁ 1).trans (hM 1 one_pos)
  induction S₂ using Finset.induction_on generalizing t with
  | empty => simp
  | insert q T hqT ih =>
    have hdisjT : Disjoint S₁ T := Finset.disjoint_of_subset_right (Finset.subset_insert _ _) hdisj
    have hqS₁ : q ∉ S₁ := fun h => Finset.disjoint_left.mp hdisj h (Finset.mem_insert_self _ _)
    have ih' := ih hdisjT
    rw [Finset.union_insert]
    have hPT : 1 ≤ ∏ p ∈ T.filter Nat.Prime, (1 + xq p) := one_le_prod_of_one_le _ _ fun p hp => by
      have := xq_nonneg (Finset.mem_filter.mp hp).2
      linarith
    by_cases hq : q.Prime
    · have hqU : q ∉ S₁ ∪ T := by
        rw [Finset.mem_union, not_or]; exact ⟨hqS₁, hqT⟩
      have hbound : ∀ s, 0 < s → RS W (S₁ ∪ T) s ≤ (∏ p ∈ T.filter Nat.Prime, (1 + xq p)) * M := by
        intro s hs
        have := ih' s hs
        have := hM s hs
        nlinarith
      have h1 := RS_insert_le W (S₁ ∪ T) hq hqU _ hbound t ht
      rw [Finset.filter_insert, if_pos hq, Finset.prod_insert (fun h => hqT (Finset.mem_filter.mp h).1)]
      have hx : 0 ≤ xq q := xq_nonneg hq
      have := ih' t ht
      have hPM : 0 ≤ (∏ p ∈ T.filter Nat.Prime, (1 + xq p)) * M := by positivity
      nlinarith
    · rw [Finset.filter_insert, if_neg hq]
      unfold RS
      simp_rw [fS_insert_of_not_prime _ hq]
      exact ih' t ht

/-- **`lem:fS`(iv)** (Lemma 6.19): the last conjunct of `lemfS_Statement`. -/
theorem lemfS_iv_proof : ∀ (W : Weight) (S₁ S₂ : Finset ℕ), Disjoint S₁ S₂ → ∀ M : ℝ,
    (∀ t, 0 < t → RS W S₁ t ≤ M) →
    ∀ t, 0 < t → RS W (S₁ ∪ S₂) t ≤ RS W S₁ t +
      (1 / 2) * ((∏ p ∈ S₂.filter Nat.Prime, (1 + 2 / ((p : ℝ) ^ 3 * (p - 1)))) - 1) * M := by
  intro W S₁ S₂ hdisj M hM t ht
  have hM0 : 0 ≤ M := (RS_nonneg W S₁ 1).trans (hM 1 one_pos)
  have h1 := RS_union_le W S₁ S₂ hdisj M hM t ht
  have hx : ∀ p ∈ S₂.filter Nat.Prime, 0 ≤ xq p := fun p hp =>
    xq_nonneg (Finset.mem_filter.mp hp).2
  have h2 := prod_one_add_sub_one_le (S₂.filter Nat.Prime) xq hx
  have h3 : ∏ p ∈ S₂.filter Nat.Prime, (1 + 2 * xq p) =
      ∏ p ∈ S₂.filter Nat.Prime, (1 + 2 / ((p : ℝ) ^ 3 * (p - 1))) :=
    Finset.prod_congr rfl fun p _ => by unfold xq; ring
  rw [h3] at h2
  have := mul_le_mul_of_nonneg_right h2 hM0
  linarith

end Families.Phase1.B
