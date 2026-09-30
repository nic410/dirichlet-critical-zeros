/-
# `lem:fS` (i)  (Lemma 6.19)

`f_S(n) = ∑_{kr=n, r sqfree} μ(r) G_S(k,r)/(rφ(r))`.

Proof (as in the TeX: "the summand factors over primes as a function of `(v_p(k), v_p(r))`"). Write
`P = primeFactors n`. The pairs `(k,r)` with `kr = n`, `r` squarefree, are in bijection with the subsets
`T ⊆ P` via `r = ∏_{p∈T} p`, `k = n/r`. For such a pair the summand is
`∏_{p∈P} (if p ∈ T then fT p else gT p)` with `gT p = 1 − 1/p` (the pair `(p^a, 1)`) and `fT p` the
contribution of `(p^{a−1}, p)`; summing over `T` gives `∏_{p∈P} (fT p + gT p)` (`Finset.prod_add`), and
`fT p + gT p = f_S(p^a)` in all four cases (`p ∈ S` or not, `a = 1` or `a ≥ 2`).
-/
import Families.LemmaC

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius
open ArithmeticFunction Finset

namespace Families.Phase1.B

open Families

/-! ### Products of distinct primes -/

lemma factorization_prod_primes {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) (q : ℕ) :
    (∏ p ∈ T, p).factorization q = if q ∈ T then 1 else 0 := by
  rw [Nat.factorization_prod (fun p hp => (hT p hp).ne_zero), Finsupp.finsetSum_apply,
    Finset.sum_congr rfl (fun p hp => by rw [(hT p hp).factorization])]
  simp [Finsupp.single_apply]

lemma prod_primes_ne_zero {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) : ∏ p ∈ T, p ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun p hp => (hT p hp).ne_zero

lemma squarefree_prod_primes {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) : Squarefree (∏ p ∈ T, p) :=
  Nat.squarefree_of_factorization_le_one (prod_primes_ne_zero hT) fun q => by
    rw [factorization_prod_primes hT]; split_ifs <;> norm_num

lemma prod_dvd_of_subset_primeFactors {n : ℕ} {T : Finset ℕ} (hT : T ⊆ n.primeFactors) :
    ∏ p ∈ T, p ∣ n :=
  (Finset.prod_dvd_prod_of_subset _ _ _ hT).trans (Nat.prod_primeFactors_dvd n)

lemma primes_of_subset {n : ℕ} {T : Finset ℕ} (hT : T ⊆ n.primeFactors) : ∀ p ∈ T, p.Prime :=
  fun _ hp => Nat.prime_of_mem_primeFactors (hT hp)

lemma div_prod_ne_zero {n : ℕ} (hn : n ≠ 0) {T : Finset ℕ} (hT : T ⊆ n.primeFactors) :
    n / ∏ p ∈ T, p ≠ 0 := by
  have hd := prod_dvd_of_subset_primeFactors hT
  have hpos : 0 < ∏ p ∈ T, p := Nat.pos_of_ne_zero (prod_primes_ne_zero (primes_of_subset hT))
  exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd) hpos).ne'

lemma factorization_div_prod {n : ℕ} {T : Finset ℕ} (hT : T ⊆ n.primeFactors) (q : ℕ) :
    (n / ∏ p ∈ T, p).factorization q = n.factorization q - (if q ∈ T then 1 else 0) := by
  rw [Nat.factorization_div (prod_dvd_of_subset_primeFactors hT), Finsupp.tsub_apply,
    factorization_prod_primes (primes_of_subset hT)]

lemma one_le_factorization_of_mem {n p : ℕ} (hp : p ∈ n.primeFactors) : 1 ≤ n.factorization p := by
  have hn : n ≠ 0 := (Nat.mem_primeFactors.mp hp).2.2
  exact ((Nat.prime_of_mem_primeFactors hp).dvd_iff_one_le_factorization hn).mp
    (Nat.dvd_of_mem_primeFactors hp)

/-- For `p ∈ P`: `p ∣ n/∏T ↔ p ∉ T ∨ v_p(n) ≥ 2`. -/
lemma mem_primeFactors_div_prod {n : ℕ} {T : Finset ℕ} (hT : T ⊆ n.primeFactors)
    {p : ℕ} (hp : p ∈ n.primeFactors) :
    p ∈ (n / ∏ q ∈ T, q).primeFactors ↔ (p ∉ T ∨ 2 ≤ n.factorization p) := by
  rw [← Nat.support_factorization, Finsupp.mem_support_iff, factorization_div_prod hT]
  have hv := one_le_factorization_of_mem hp
  by_cases h : p ∈ T
  · simp only [h, if_true, not_true_eq_false, false_or]; omega
  · simp only [h, if_false, not_false_eq_true, true_or, iff_true]; omega

lemma primeFactors_div_prod_subset {n : ℕ} (hn : n ≠ 0) {T : Finset ℕ} (hT : T ⊆ n.primeFactors) :
    (n / ∏ q ∈ T, q).primeFactors ⊆ n.primeFactors :=
  Nat.primeFactors_mono (Nat.div_dvd_of_dvd (prod_dvd_of_subset_primeFactors hT)) hn

/-! ### `φ(k)/k` -/

lemma totient_div_self_eq {k : ℕ} (hk : k ≠ 0) :
    (Nat.totient k : ℝ) / k = ∏ p ∈ k.primeFactors, (1 - 1 / (p : ℝ)) := by
  have h : (Nat.totient k : ℝ) = k * ∏ p ∈ k.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors k)
    push_cast at this
    exact this
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  rw [h, mul_div_cancel_left₀ _ hk']
  simp only [one_div]

/-! ### Products over `P` with an indicator -/

lemma prod_ite_mem_eq {P T : Finset ℕ} (hT : T ⊆ P) (f g : ℕ → ℝ) :
    ∏ p ∈ P, (if p ∈ T then f p else g p) = (∏ p ∈ T, f p) * ∏ p ∈ P \ T, g p := by
  rw [Finset.prod_ite]
  congr 1
  · congr 1
    ext p; simp only [Finset.mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hT h, h⟩⟩
  · congr 1
    ext p; simp [Finset.mem_sdiff]

lemma prod_subset_ite {P K : Finset ℕ} (hK : K ⊆ P) (f : ℕ → ℝ) :
    ∏ p ∈ K, f p = ∏ p ∈ P, (if p ∈ K then f p else 1) := by
  rw [Finset.prod_ite_mem, Finset.inter_eq_right.mpr hK]

/-! ### The local factors -/

/-- Contribution of the pair `(p^{a−1}, p)` (`a = v_p(n)`). -/
def fT (S : Finset ℕ) (n p : ℕ) : ℝ :=
  -1 / ((p : ℝ) * p * (1 - 1 / (p : ℝ))) *
    (if 2 ≤ n.factorization p then 1 - 1 / (p : ℝ) else 1) *
    (if n.factorization p = 1 ∧ p ∉ S then 1 - 1 / (p : ℝ) else 1) *
    (if 2 ≤ n.factorization p ∧ p ∈ S then 0 else 1)

/-- Contribution of the pair `(p^a, 1)`. -/
def gT (p : ℕ) : ℝ := 1 - 1 / (p : ℝ)

lemma fT_add_gT (S : Finset ℕ) (n p : ℕ) (hp : p.Prime) (hv : 1 ≤ n.factorization p) :
    fT S n p + gT p = fSpp S p (n.factorization p) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hq : (1 : ℝ) - 1 / p ≠ 0 := by
    rw [sub_ne_zero]; intro h; rw [eq_div_iff hp0] at h; linarith
  unfold fT gT fSpp
  rcases (show n.factorization p = 1 ∨ 2 ≤ n.factorization p by omega) with h | h
  · have h2 : ¬ 2 ≤ n.factorization p := by omega
    by_cases hS : p ∈ S
    · rw [if_neg h2, if_neg (fun h' => h'.2 hS), if_neg (fun h' => h2 h'.1), if_pos hS, if_pos h]
      field_simp
      ring
    · rw [if_neg h2, if_pos ⟨h, hS⟩, if_neg (fun h' => h2 h'.1), if_neg hS]
      field_simp
      ring
  · have h1 : n.factorization p ≠ 1 := by omega
    by_cases hS : p ∈ S
    · rw [if_pos h, if_neg (fun h' => h1 h'.1), if_pos ⟨h, hS⟩, if_pos hS, if_neg h1]
      field_simp
      ring
    · rw [if_pos h, if_neg (fun h' => h1 h'.1), if_neg (fun h' => hS h'.2), if_neg hS]
      field_simp
      ring

/-! ### The summand at a subset `T` -/

theorem summand_eq (S : Finset ℕ) {n : ℕ} (hn : n ≠ 0) {T : Finset ℕ} (hT : T ⊆ n.primeFactors) :
    (μ (∏ p ∈ T, p) : ℝ) * GS S (n / ∏ p ∈ T, p) (∏ p ∈ T, p) /
        ((∏ p ∈ T, p : ℕ) * Nat.totient (∏ p ∈ T, p))
      = ∏ p ∈ n.primeFactors, (if p ∈ T then fT S n p else gT p) := by
  classical
  set P := n.primeFactors with hP
  have hTp := primes_of_subset hT
  set r := ∏ p ∈ T, p with hr
  set k := n / r with hk
  have hr0 : r ≠ 0 := prod_primes_ne_zero hTp
  have hk0 : k ≠ 0 := div_prod_ne_zero hn hT
  have hrpf : r.primeFactors = T := Nat.primeFactors_prod hTp
  have hkP : k.primeFactors ⊆ P := primeFactors_div_prod_subset hn hT
  have hp2 : ∀ p ∈ P, (2 : ℝ) ≤ p := fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have hq : ∀ p ∈ P, (1 : ℝ) - 1 / p ≠ 0 := fun p hp => by
    have := hp2 p hp
    rw [sub_ne_zero]; intro h; rw [eq_div_iff (by linarith)] at h; linarith
  -- `μ(r)/(rφ(r)) = ∏_{p∈T} −1/(p·p·(1−1/p))`
  have hμ : (μ r : ℝ) = ∏ p ∈ T, (-1 : ℝ) := by
    rw [hr, isMultiplicative_moebius.map_prod_of_prime T hTp]
    push_cast
    exact Finset.prod_congr rfl fun p hp => by rw [moebius_apply_prime (hTp p hp)]; norm_num
  have hrR : ((r : ℕ) : ℝ) = ∏ p ∈ T, (p : ℝ) := by rw [hr]; push_cast; rfl
  have hφr : (Nat.totient r : ℝ) = r * ∏ p ∈ T, (1 - 1 / (p : ℝ)) := by
    have := totient_div_self_eq hr0
    rw [hrpf] at this
    have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr0
    rw [← this]; field_simp
  have hA : (μ r : ℝ) / ((r : ℝ) * Nat.totient r) =
      ∏ p ∈ P, (if p ∈ T then -1 / ((p : ℝ) * p * (1 - 1 / (p : ℝ))) else 1) := by
    rw [← prod_subset_ite hT, hφr, hμ, hrR, Finset.prod_div_distrib, Finset.prod_mul_distrib,
      Finset.prod_mul_distrib, mul_assoc]
  -- `φ(k)/k = ∏_{p∈P} (if p ∣ k then 1 − 1/p else 1)`
  have hB : (Nat.totient k : ℝ) / k = ∏ p ∈ P, (if p ∈ k.primeFactors then 1 - 1 / (p : ℝ) else 1) := by
    rw [totient_div_self_eq hk0, prod_subset_ite hkP]
  -- the product over `p ∣ r`, `p ∤ k`, `p ∉ S`
  have hC : ∏ p ∈ r.primeFactors.filter (fun p => ¬ p ∣ k ∧ p ∉ S), (1 - 1 / (p : ℝ)) =
      ∏ p ∈ P, (if p ∈ T ∧ p ∉ k.primeFactors ∧ p ∉ S then 1 - 1 / (p : ℝ) else 1) := by
    rw [hrpf, prod_subset_ite ((Finset.filter_subset _ _).trans hT)]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpk : p ∣ k ↔ p ∈ k.primeFactors := by
      rw [Nat.mem_primeFactors_of_ne_zero hk0]
      exact ⟨fun h => ⟨Nat.prime_of_mem_primeFactors hp, h⟩, fun h => h.2⟩
    simp only [Finset.mem_filter, hpk]
  -- the indicator
  have hD : (if ∀ p ∈ S, p.Prime → ¬ p ∣ Nat.gcd k r then (1 : ℝ) else 0) =
      ∏ p ∈ P, (if p ∈ T ∧ p ∈ k.primeFactors ∧ p ∈ S then (0 : ℝ) else 1) := by
    have hiff : (∀ p ∈ S, p.Prime → ¬ p ∣ Nat.gcd k r) ↔
        ∀ p ∈ P, ¬ (p ∈ T ∧ p ∈ k.primeFactors ∧ p ∈ S) := by
      constructor
      · rintro h p - ⟨hpT, hpk, hpS⟩
        have hpr : p ∣ r := by
          have : p ∈ r.primeFactors := by rw [hrpf]; exact hpT
          exact Nat.dvd_of_mem_primeFactors this
        exact h p hpS (hTp p hpT) (Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hpk) hpr)
      · intro h p hpS hprime hdvd
        obtain ⟨hdk, hdr⟩ := Nat.dvd_gcd_iff.mp hdvd
        have hpT : p ∈ T := by
          rw [← hrpf, Nat.mem_primeFactors_of_ne_zero hr0]; exact ⟨hprime, hdr⟩
        have hpk : p ∈ k.primeFactors := by
          rw [Nat.mem_primeFactors_of_ne_zero hk0]; exact ⟨hprime, hdk⟩
        exact h p (hT hpT) ⟨hpT, hpk, hpS⟩
    have hprod : ∏ p ∈ P, (if p ∈ T ∧ p ∈ k.primeFactors ∧ p ∈ S then (0 : ℝ) else 1) =
        ∏ p ∈ P, (if ¬ (p ∈ T ∧ p ∈ k.primeFactors ∧ p ∈ S) then (1 : ℝ) else 0) :=
      Finset.prod_congr rfl fun p _ => by split_ifs <;> tauto
    rw [hprod, Finset.prod_boole]
    by_cases h : ∀ p ∈ S, p.Prime → ¬ p ∣ Nat.gcd k r
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]
  -- assemble
  have hsplit : (μ r : ℝ) * GS S k r / ((r : ℝ) * Nat.totient r) =
      ((μ r : ℝ) / ((r : ℝ) * Nat.totient r)) * ((Nat.totient k : ℝ) / k) *
        (∏ p ∈ r.primeFactors.filter (fun p => ¬ p ∣ k ∧ p ∉ S), (1 - 1 / (p : ℝ))) *
        (if ∀ p ∈ S, p.Prime → ¬ p ∣ Nat.gcd k r then (1 : ℝ) else 0) := by
    unfold GS; ring
  rw [hsplit, hA, hB, hC, hD, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hmem := mem_primeFactors_div_prod hT hp
  rw [← hk] at hmem
  have hv := one_le_factorization_of_mem hp
  unfold fT gT
  by_cases hpT : p ∈ T
  · have hk' : p ∈ k.primeFactors ↔ 2 ≤ n.factorization p := by
      rw [hmem]; simp [hpT]
    by_cases h2 : 2 ≤ n.factorization p
    · have h1 : ¬ n.factorization p = 1 := by omega
      simp only [hpT, hk'.mpr h2, h2, h1, if_true, true_and, not_true_eq_false, false_and,
        and_false, if_false, mul_one]
    · have h1 : n.factorization p = 1 := by omega
      have hnk : p ∉ k.primeFactors := fun h => h2 (hk'.mp h)
      have h21 : ¬ (2 : ℕ) ≤ 1 := by norm_num
      simp only [hpT, hnk, h21, h1, if_true, if_false, true_and, not_false_eq_true, false_and,
        and_false, mul_one]
  · have hk' : p ∈ k.primeFactors := hmem.mpr (Or.inl hpT)
    simp only [hpT, hk', if_true, if_false, false_and, one_mul, mul_one]

/-! ### `lem:fS` (i) -/

/-- **`lem:fS`(i)** (Lemma 6.19): `f_S(n) = ∑_{kr=n, r sqfree} μ(r)G_S(k,r)/(rφ(r))`
(the first conjunct of `lemfS_Statement`). -/
theorem lemfS_i_proof : ∀ (S : Finset ℕ) (n : ℕ), 1 ≤ n →
    fS S n = ∑ kr ∈ n.divisorsAntidiagonal.filter (fun kr => Squarefree kr.2),
      (μ kr.2 : ℝ) * GS S kr.1 kr.2 / (kr.2 * Nat.totient kr.2) := by
  intro S n hn
  classical
  have hn0 : n ≠ 0 := by omega
  have hbij : ∑ kr ∈ n.divisorsAntidiagonal.filter (fun kr => Squarefree kr.2),
        (μ kr.2 : ℝ) * GS S kr.1 kr.2 / (kr.2 * Nat.totient kr.2) =
      ∑ T ∈ n.primeFactors.powerset,
        (μ (∏ p ∈ T, p) : ℝ) * GS S (n / ∏ p ∈ T, p) (∏ p ∈ T, p) /
          ((∏ p ∈ T, p : ℕ) * Nat.totient (∏ p ∈ T, p)) := by
    symm
    refine Finset.sum_nbij' (fun T => (n / ∏ p ∈ T, p, ∏ p ∈ T, p)) (fun kr => kr.2.primeFactors)
      ?_ ?_ ?_ ?_ ?_
    · intro T hT
      have hT' := Finset.mem_powerset.mp hT
      rw [Finset.mem_filter, Nat.mem_divisorsAntidiagonal]
      exact ⟨⟨Nat.div_mul_cancel (prod_dvd_of_subset_primeFactors hT'), hn0⟩,
        squarefree_prod_primes (primes_of_subset hT')⟩
    · intro kr hkr
      rw [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hkr
      rw [Finset.mem_powerset]
      exact Nat.primeFactors_mono ⟨kr.1, by rw [← hkr.1.1]; ring⟩ hn0
    · intro T hT
      exact Nat.primeFactors_prod (primes_of_subset (Finset.mem_powerset.mp hT))
    · intro kr hkr
      rw [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hkr
      obtain ⟨⟨hmul, -⟩, hsq⟩ := hkr
      have h2 : ∏ p ∈ kr.2.primeFactors, p = kr.2 := Nat.prod_primeFactors_of_squarefree hsq
      have hr0 : kr.2 ≠ 0 := hsq.ne_zero
      refine Prod.ext ?_ h2
      show n / ∏ p ∈ kr.2.primeFactors, p = kr.1
      rw [h2, ← hmul, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hr0)]
    · intro T _
      rfl
  rw [hbij]
  unfold fS
  rw [Finset.prod_congr rfl (fun p hp => (fT_add_gT S n p (Nat.prime_of_mem_primeFactors hp)
    (one_le_factorization_of_mem hp)).symm), Finset.prod_add]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [summand_eq S hn0 (Finset.mem_powerset.mp hT),
    prod_ite_mem_eq (Finset.mem_powerset.mp hT)]

/-- Interface check: `lemfS_i_proof` proves exactly the first conjunct of `lemfS_Statement` (the
statement `lemC` consumes). -/
example (h : lemfS_Statement) : h.1 = lemfS_i_proof := rfl

end Families.Phase1.B
