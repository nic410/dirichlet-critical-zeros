/-
Arithmetic sums used in `lem:C` (`lemma-toeplitz-C.tex`, proof of
`lem:C`, "Summing over `r`").

* `sum_inv_totient_le`: `∑_{r≤N} 1/φ(r) ≤ 2(1 + log N)` (the TeX has `1.95`; Abel summation from
  the proved `Families.sum_div_totient_le`, `∑_{j≤N} j/φ(j) ≤ 2N`).
* `sum_sqfree_card_divisors_div_totient_le`: `∑_{r≤N sqfree} τ(r)/φ(r) ≤ (∑_{d≤N} 1/φ(d))²`
  (for squarefree `r`, `τ(r)/φ(r) = ∑_{de=r} 1/(φ(d)φ(e))`), hence `≤ 4(1 + log N)²`.
-/
import Families.Phase1.A.Toolkit

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius
open Finset

namespace Families.Phase1.A

open Families

lemma harmonic_real_eq (N : ℕ) : ((harmonic N : ℚ) : ℝ) = ∑ j ∈ Finset.Icc 1 N, 1 / (j : ℝ) := by
  rw [harmonic_eq_sum_Icc]; push_cast; simp

/-- Abel summation: `∑_{j≤N} a_j/j + 2 ≤ A(N)/N + 2 H_N` for `N ≥ 1`, where `A(N) = ∑_{j≤N} a_j`,
`a_j = j/φ(j)` and `A(n) ≤ 2n`. -/
lemma sum_inv_totient_aux (N : ℕ) (hN : 1 ≤ N) :
    ∑ j ∈ Finset.Icc 1 N, 1 / (Nat.totient j : ℝ) + 2 ≤
      (∑ j ∈ Finset.Icc 1 N, (j : ℝ) / Nat.totient j) / N + 2 * ∑ j ∈ Finset.Icc 1 N, 1 / (j : ℝ) := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
      Finset.sum_Icc_succ_top (by omega)]
    set A := ∑ j ∈ Finset.Icc 1 N, (j : ℝ) / Nat.totient j with hA
    have hA2 : A ≤ 2 * N := Families.sum_div_totient_le N
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by linarith
    have hφ : (0 : ℝ) < Nat.totient (N + 1) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    have key : A / N ≤ A / (N + 1) + 2 / (N + 1) := by
      rw [← add_div, div_le_div_iff₀ hN0 hN1]
      nlinarith
    push_cast
    have e : (A + ((N : ℝ) + 1) / (Nat.totient (N + 1) : ℝ)) / ((N : ℝ) + 1) =
        A / (N + 1) + 1 / (Nat.totient (N + 1) : ℝ) := by
      field_simp
    rw [e]
    have h5 : ∑ j ∈ Finset.Icc 1 N, 1 / (Nat.totient j : ℝ) + 2 ≤
        A / (N + 1) + 2 / (N + 1) + 2 * ∑ j ∈ Finset.Icc 1 N, 1 / (j : ℝ) := by
      linarith [ih, key]
    have h6 : (2 : ℝ) / (N + 1) = 2 * (1 / (N + 1)) := by ring
    linarith [h5, h6]

/-- `∑_{r≤N} 1/φ(r) ≤ 2(1 + log N)`. -/
theorem sum_inv_totient_le (N : ℕ) :
    ∑ j ∈ Finset.Icc 1 N, 1 / (Nat.totient j : ℝ) ≤ 2 * (1 + Real.log N) := by
  rcases Nat.eq_zero_or_pos N with h0 | hN
  · subst h0; simp
  have h1 := sum_inv_totient_aux N hN
  have hA2 : ∑ j ∈ Finset.Icc 1 N, (j : ℝ) / Nat.totient j ≤ 2 * N := Families.sum_div_totient_le N
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hq : (∑ j ∈ Finset.Icc 1 N, (j : ℝ) / Nat.totient j) / N ≤ 2 := by
    rw [div_le_iff₀ hN0]; linarith
  have hH := harmonic_le_one_add_log N
  rw [harmonic_real_eq] at hH
  linarith

lemma sum_inv_totient_nonneg (N : ℕ) : 0 ≤ ∑ j ∈ Finset.Icc 1 N, 1 / (Nat.totient j : ℝ) :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- For squarefree `r` and `d | r`: `(d, r/d) = 1`. -/
lemma coprime_div_of_squarefree {r d : ℕ} (hr : Squarefree r) (hd : d ∣ r) :
    Nat.Coprime d (r / d) := by
  refine Nat.coprime_of_dvd fun p hp h1 h2 => ?_
  refine (Nat.squarefree_iff_prime_squarefree.mp hr) p hp ?_
  have : p * p ∣ d * (r / d) := mul_dvd_mul h1 h2
  rwa [Nat.mul_div_cancel' hd] at this

/-- For squarefree `r`: `τ(r)/φ(r) = ∑_{(d,e) : de = r} 1/(φ(d)φ(e))`. -/
lemma card_divisors_div_totient_eq {r : ℕ} (hr : Squarefree r) :
    ((r.divisors.card : ℕ) : ℝ) / Nat.totient r =
      ∑ p ∈ r.divisorsAntidiagonal, 1 / (Nat.totient p.1 : ℝ) * (1 / Nat.totient p.2) := by
  rw [Nat.sum_divisorsAntidiagonal (fun a b => 1 / (Nat.totient a : ℝ) * (1 / Nat.totient b)),
    Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdr : d ∣ r := Nat.dvd_of_mem_divisors hd
  rw [← Nat.mul_div_cancel' hdr, Nat.totient_mul (coprime_div_of_squarefree hr hdr),
    Nat.mul_div_cancel' hdr]
  push_cast
  rw [one_div_mul_one_div]

/-- `∑_{r≤N sqfree} τ(r)/φ(r) ≤ (∑_{d≤N} 1/φ(d))²`. -/
theorem sum_sqfree_card_divisors_div_totient_le (N : ℕ) :
    ∑ r ∈ (Finset.Icc 1 N).filter Squarefree, ((r.divisors.card : ℕ) : ℝ) / Nat.totient r ≤
      (∑ d ∈ Finset.Icc 1 N, 1 / (Nat.totient d : ℝ)) ^ 2 := by
  set g : ℕ → ℝ := fun d => 1 / (Nat.totient d : ℝ) with hg
  have hg0 : ∀ d, 0 ≤ g d := fun d => by simp only [hg]; positivity
  set P := (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ N) with hP
  -- step 1: drop the squarefree restriction on the (nonnegative) antidiagonal sums
  have h1 : ∑ r ∈ (Finset.Icc 1 N).filter Squarefree, ((r.divisors.card : ℕ) : ℝ) / Nat.totient r ≤
      ∑ r ∈ Finset.Icc 1 N, ∑ p ∈ r.divisorsAntidiagonal, g p.1 * g p.2 := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun r _ => ?_
    split_ifs with hr
    · rw [card_divisors_div_totient_eq hr]
    · exact Finset.sum_nonneg fun p _ => mul_nonneg (hg0 _) (hg0 _)
  -- step 2: the antidiagonals of `r ≤ N` form `P`
  have h2 : ∑ r ∈ Finset.Icc 1 N, ∑ p ∈ r.divisorsAntidiagonal, g p.1 * g p.2 =
      ∑ p ∈ P, g p.1 * g p.2 := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := P) (t := Finset.Icc 1 N)
      (g := fun p : ℕ × ℕ => p.1 * p.2)]
    · refine Finset.sum_congr rfl fun r hr => ?_
      obtain ⟨hr1, hrN⟩ := Finset.mem_Icc.mp hr
      congr 1
      ext p
      simp only [Nat.mem_divisorsAntidiagonal, hP, Finset.mem_filter, Finset.mem_product,
        Finset.mem_Icc]
      constructor
      · rintro ⟨hp, hr0⟩
        have h1 : 0 < p.1 := Nat.pos_of_ne_zero fun h => by rw [h, zero_mul] at hp; omega
        have h2 : 0 < p.2 := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hp; omega
        have h3 : p.1 ≤ r := by rw [← hp]; exact Nat.le_mul_of_pos_right _ h2
        have h4 : p.2 ≤ r := by rw [← hp]; exact Nat.le_mul_of_pos_left _ h1
        exact ⟨⟨⟨⟨h1, by omega⟩, ⟨h2, by omega⟩⟩, by omega⟩, hp⟩
      · rintro ⟨⟨-, -⟩, hp⟩
        exact ⟨hp, by omega⟩
    · intro p hp
      simp only [hP, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
      rw [Finset.mem_Icc]
      exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), hp.2⟩
  -- step 3: enlarge `P` to the full square
  have h3 : ∑ p ∈ P, g p.1 * g p.2 ≤ ∑ p ∈ Finset.Icc 1 N ×ˢ Finset.Icc 1 N, g p.1 * g p.2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      fun p _ _ => mul_nonneg (hg0 _) (hg0 _)
  rw [Finset.sum_product, ← Finset.sum_mul_sum, ← sq] at h3
  linarith

/-- `∑_{r≤N sqfree} τ(r)/φ(r) ≤ 4(1 + log N)²`. -/
theorem sum_sqfree_card_divisors_div_totient_le' (N : ℕ) :
    ∑ r ∈ (Finset.Icc 1 N).filter Squarefree, ((r.divisors.card : ℕ) : ℝ) / Nat.totient r ≤
      4 * (1 + Real.log N) ^ 2 := by
  refine (sum_sqfree_card_divisors_div_totient_le N).trans ?_
  have h := sum_inv_totient_le N
  have h0 := sum_inv_totient_nonneg N
  calc (∑ d ∈ Finset.Icc 1 N, 1 / (Nat.totient d : ℝ)) ^ 2 ≤ (2 * (1 + Real.log N)) ^ 2 :=
        pow_le_pow_left₀ h0 h 2
    _ = 4 * (1 + Real.log N) ^ 2 := by ring

end Families.Phase1.A
