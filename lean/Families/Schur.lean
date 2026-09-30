/-
The Schur test and `lem:M2` (short intervals), `lemma-B-majorant.tex` §5.
The arithmetic part is stated for the explicit orthogonality expression, so that this file does not
depend on `Families.Toeplitz`; `Families.Glue` combines the two.
-/
import Families.Basic

noncomputable section

open scoped BigOperators ComplexConjugate ArithmeticFunction.Moebius
open ArithmeticFunction Finset

namespace Families

/-! ### The Schur test -/

/-- **Schur test.** A kernel `A` on a finite set `I` with `|A(n,m)| = |A(m,n)|` (e.g. Hermitian),
`|A(n,n)| ≤ H₀` and `∑_{m ≠ n} |A(n,m)| ≤ E` for all `n` satisfies
`|∑_{n,m} x_n \bar x_m A(n,m)| ≤ (H₀ + E) ‖x‖²`. -/
theorem schur_test (I : Finset ℤ) (A : ℤ → ℤ → ℂ) (hsymm : ∀ n m, ‖A n m‖ = ‖A m n‖)
    (H₀ E : ℝ) (hdiag : ∀ n ∈ I, ‖A n n‖ ≤ H₀) (hoff : ∀ n ∈ I, ∑ m ∈ I.erase n, ‖A n m‖ ≤ E)
    (x : ℤ → ℂ) :
    ‖∑ n ∈ I, ∑ m ∈ I, x n * conj (x m) * A n m‖ ≤ (H₀ + E) * normSq I x := by
  have key : ∀ n m, ‖x n * conj (x m) * A n m‖ ≤ (‖x n‖^2 + ‖x m‖^2)/2 * ‖A n m‖ := by
    intro n m
    rw [norm_mul, norm_mul, Complex.norm_conj]
    have h1 := two_mul_le_add_sq ‖x n‖ ‖x m‖
    have hA := norm_nonneg (A n m)
    nlinarith
  have hrow : ∀ n ∈ I, ∑ m ∈ I, ‖A n m‖ ≤ H₀ + E := by
    intro n hn
    rw [← Finset.add_sum_erase I _ hn]
    linarith [hdiag n hn, hoff n hn]
  calc ‖∑ n ∈ I, ∑ m ∈ I, x n * conj (x m) * A n m‖
      ≤ ∑ n ∈ I, ‖∑ m ∈ I, x n * conj (x m) * A n m‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ I, ∑ m ∈ I, ‖x n * conj (x m) * A n m‖ :=
        Finset.sum_le_sum fun n _ => norm_sum_le _ _
    _ ≤ ∑ n ∈ I, ∑ m ∈ I, (‖x n‖^2 + ‖x m‖^2)/2 * ‖A n m‖ :=
        Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun m _ => key n m
    _ = ∑ n ∈ I, ‖x n‖^2 * ∑ m ∈ I, ‖A n m‖ := by
        have hsplit : ∀ n m, (‖x n‖^2 + ‖x m‖^2)/2 * ‖A n m‖
            = ‖x n‖^2 / 2 * ‖A n m‖ + ‖x m‖^2 / 2 * ‖A m n‖ := by
          intro n m; rw [hsymm n m]; ring
        simp_rw [hsplit, Finset.sum_add_distrib]
        rw [Finset.sum_comm (f := fun n m => ‖x m‖ ^ 2 / 2 * ‖A m n‖)]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun m _ => ?_
        ring
    _ ≤ ∑ n ∈ I, ‖x n‖^2 * (H₀ + E) :=
        Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (hrow n hn) (sq_nonneg _)
    _ = (H₀ + E) * normSq I x := by
        rw [normSq, Finset.mul_sum]; exact Finset.sum_congr rfl fun n _ => by ring

/-! ### Arithmetic input for `lem:M2` -/

/-- `w ≤ w_max` (bounded variation gives boundedness). -/
theorem Weight.le_wmax (W : Weight) (u : ℝ) : W.w u ≤ W.wmax := by
  have h2 : W.w 2 = 0 := by
    by_contra h
    have := (W.supp 2 h).2
    norm_num at this
  have hbdd : BddAbove (Set.range W.w) := by
    refine ⟨(eVariationOn W.w Set.univ).toReal, ?_⟩
    rintro _ ⟨v, rfl⟩
    have h := eVariationOn.edist_le W.w (s := Set.univ) (Set.mem_univ v) (Set.mem_univ 2)
    rw [h2, edist_dist] at h
    have hfin := W.bv
    have := (ENNReal.ofReal_le_iff_le_toReal hfin).mp h
    rw [dist_zero_right, Real.norm_eq_abs] at this
    exact le_trans (le_abs_self _) this
  exact le_csSup hbdd ⟨u, rfl⟩

lemma div_totient_eq (j : ℕ) (hj : 0 < j) :
    (j : ℝ) / Nat.totient j = ∏ p ∈ j.primeFactors, (1 + 1 / ((p : ℝ) - 1)) := by
  have h := congrArg (Nat.cast : ℕ → ℝ) (Nat.totient_mul_prod_primeFactors j)
  push_cast at h
  have hsub : ∀ p ∈ j.primeFactors, ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := fun p hp => by
    have := (Nat.prime_of_mem_primeFactors hp).one_le
    push_cast [this]; ring
  rw [Finset.prod_congr rfl hsub] at h
  have hφ : (Nat.totient j : ℝ) ≠ 0 := by
    have := Nat.totient_pos.mpr hj; positivity
  have hP : ∏ p ∈ j.primeFactors, ((p : ℝ) - 1) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    have : (2 : ℝ) ≤ p := by exact_mod_cast this
    linarith
  have h2 : ∀ p ∈ j.primeFactors, 1 + 1 / ((p : ℝ) - 1) = (p : ℝ) / ((p : ℝ) - 1) := by
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    have : (2 : ℝ) ≤ p := by exact_mod_cast this
    have : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [Finset.prod_congr rfl h2, Finset.prod_div_distrib, div_eq_div_iff hφ hP]
  linarith [h]

lemma sum_div_totient_le_mul_prod (N : ℕ) :
    ∑ j ∈ Finset.Icc 1 N, (j : ℝ) / Nat.totient j
      ≤ N * ∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
  set P := (Finset.Icc 1 N).filter Nat.Prime with hP
  set g : Finset ℕ → ℝ := fun t => ∏ p ∈ t, 1 / ((p : ℝ) - 1) with hg
  have hp2 : ∀ p ∈ P, (2 : ℝ) ≤ p := fun p hp => by
    have := (Finset.mem_filter.mp hp).2.two_le
    exact_mod_cast this
  have hg0 : ∀ t ⊆ P, 0 ≤ g t := fun t ht => Finset.prod_nonneg fun p hp => by
    have := hp2 p (ht hp)
    exact div_nonneg zero_le_one (by linarith)
  have hpfP : ∀ j ∈ Finset.Icc 1 N, j.primeFactors ⊆ P := by
    intro j hj p hp
    have hj' := Finset.mem_Icc.mp hj
    rw [hP, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨(Nat.prime_of_mem_primeFactors hp).one_le,
      (Nat.le_of_mem_primeFactors hp).trans hj'.2⟩, Nat.prime_of_mem_primeFactors hp⟩
  have hA : ∀ j ∈ Finset.Icc 1 N, (j : ℝ) / Nat.totient j
      = ∑ t ∈ P.powerset, if t ⊆ j.primeFactors then g t else 0 := by
    intro j hj
    rw [div_totient_eq j (Finset.mem_Icc.mp hj).1, Finset.prod_one_add, ← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext t
    simp only [Finset.mem_powerset, Finset.mem_filter]
    constructor
    · intro h; exact ⟨h.trans (hpfP j hj), h⟩
    · intro h; exact h.2
  rw [Finset.sum_congr rfl hA, Finset.sum_comm]
  have hB : ∀ t ∈ P.powerset, ∑ j ∈ Finset.Icc 1 N, (if t ⊆ j.primeFactors then g t else 0)
      ≤ N * ∏ p ∈ t, 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    intro t ht
    have htP := Finset.mem_powerset.mp ht
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.Icc 1 N).filter (fun j => t ⊆ j.primeFactors)).card
        ≤ N / ∏ p ∈ t, p := by
      rw [← Nat.Ioc_filter_dvd_card_eq_div]
      apply Finset.card_le_card
      intro j hj
      rw [Finset.mem_filter] at hj ⊢
      refine ⟨?_, ?_⟩
      · have := Finset.mem_Icc.mp hj.1
        rw [Finset.mem_Ioc]; omega
      · exact (Finset.prod_dvd_prod_of_subset _ _ _ hj.2).trans (Nat.prod_primeFactors_dvd j)
    have hprod_pos : (0 : ℝ) < ∏ p ∈ t, (p : ℝ) :=
      Finset.prod_pos (fun p hp => by have := hp2 p (htP hp); linarith)
    have hcard' : (((Finset.Icc 1 N).filter (fun j => t ⊆ j.primeFactors)).card : ℝ)
        ≤ (N : ℝ) / ∏ p ∈ t, (p : ℝ) := by
      calc (((Finset.Icc 1 N).filter (fun j => t ⊆ j.primeFactors)).card : ℝ)
          ≤ ((N / ∏ p ∈ t, p : ℕ) : ℝ) := by exact_mod_cast hcard
        _ ≤ (N : ℝ) / ((∏ p ∈ t, p : ℕ) : ℝ) := Nat.cast_div_le
        _ = (N : ℝ) / ∏ p ∈ t, (p : ℝ) := by push_cast; rfl
    calc (((Finset.Icc 1 N).filter (fun j => t ⊆ j.primeFactors)).card : ℝ) * g t
        ≤ (N : ℝ) / (∏ p ∈ t, (p : ℝ)) * g t :=
          mul_le_mul_of_nonneg_right hcard' (hg0 t htP)
      _ = N * ∏ p ∈ t, 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
          rw [hg]
          simp only
          have : ∀ p ∈ t, 1 / ((p : ℝ) * ((p : ℝ) - 1)) = 1 / (p : ℝ) * (1 / ((p : ℝ) - 1)) := by
            intro p _; rw [one_div_mul_one_div]
          rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib]
          simp only [one_div, Finset.prod_inv_distrib]
          ring
  refine (Finset.sum_le_sum hB).trans (le_of_eq ?_)
  rw [← Finset.mul_sum, Finset.prod_one_add]

private lemma prod_le_prod_of_subset_one_le' {s t : Finset ℕ} (f : ℕ → ℝ) (hst : s ⊆ t)
    (hf : ∀ i ∈ t, 1 ≤ f i) : ∏ i ∈ s, f i ≤ ∏ i ∈ t, f i := by
  rw [← Finset.prod_sdiff hst]
  have h0 : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg fun i hi => by linarith [hf i (hst hi)]
  have h1 : 1 ≤ ∏ i ∈ t \ s, f i := by
    have := Finset.prod_le_prod (s := t \ s) (f := fun _ => (1 : ℝ)) (g := f)
      (fun _ _ => zero_le_one) (fun i hi => hf i (Finset.mem_sdiff.mp hi).1)
    simpa using this
  nlinarith

lemma tail_prod_le (N : ℕ) :
    ∏ k ∈ Finset.Icc 29 N, (1 + 1 / ((k : ℝ) * ((k : ℝ) - 1))) ≤ 28 / 27 := by
  have key : ∀ N : ℕ, 28 ≤ N →
      ∏ k ∈ Finset.Icc 29 N, (1 + 1 / ((k : ℝ) * ((k : ℝ) - 1))) ≤ 28 / 27 * (1 - 1 / (N : ℝ)) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      rw [Finset.prod_Icc_succ_top (by omega)]
      have hx : (28 : ℝ) ≤ n := by exact_mod_cast hn
      have hf0 : 0 ≤ 1 + 1 / (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) - 1)) := by
        push_cast
        have : 0 < ((n : ℝ) + 1) * ((n : ℝ) + 1 - 1) := by nlinarith
        positivity
      refine (mul_le_mul_of_nonneg_right ih hf0).trans ?_
      push_cast
      have hxpos : (0 : ℝ) < n := by linarith
      have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hxpos
      have hn1 : (n : ℝ) + 1 ≠ 0 := by linarith
      have hn2 : (n : ℝ) + 1 - 1 ≠ 0 := by linarith
      have e1 : (1 - 1 / (n : ℝ)) * (1 + 1 / (((n : ℝ) + 1) * ((n : ℝ) + 1 - 1)))
          = ((n : ℝ) ^ 3 - 1) / ((n : ℝ) ^ 2 * ((n : ℝ) + 1)) := by
        field_simp; ring
      have e2 : 1 - 1 / ((n : ℝ) + 1) = (n : ℝ) ^ 3 / ((n : ℝ) ^ 2 * ((n : ℝ) + 1)) := by
        field_simp; ring
      rw [mul_assoc, e1, e2]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply div_le_div_of_nonneg_right (by linarith) (by positivity)
  by_cases hN : 28 ≤ N
  · refine (key N hN).trans ?_
    have : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
    nlinarith
  · rw [Finset.Icc_eq_empty (by omega), Finset.prod_empty]; norm_num

lemma euler_partial_le_two (N : ℕ) :
    ∏ p ∈ (Finset.Icc 1 N).filter Nat.Prime, (1 + 1 / ((p : ℝ) * ((p : ℝ) - 1))) ≤ 2 := by
  set f : ℕ → ℝ := fun p => 1 + 1 / ((p : ℝ) * ((p : ℝ) - 1)) with hf
  have hf1 : ∀ p : ℕ, 2 ≤ p → 1 ≤ f p := by
    intro p hp
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    have : 0 < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
    simp only [hf]
    have : 0 ≤ 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by positivity
    linarith
  set P := (Finset.Icc 1 N).filter Nat.Prime
  set S23 : Finset ℕ := {2, 3, 5, 7, 11, 13, 17, 19, 23}
  rw [← Finset.prod_filter_mul_prod_filter_not P (fun p => p ≤ 28)]
  have h1 : ∏ p ∈ P.filter (fun p => p ≤ 28), f p ≤ ∏ p ∈ S23, f p := by
    apply prod_le_prod_of_subset_one_le' f
    · intro p hp
      obtain ⟨hpP, hp28⟩ := Finset.mem_filter.mp hp
      have hpr := (Finset.mem_filter.mp hpP).2
      interval_cases p <;> simp_all (config := { decide := true }) [S23]
    · intro p hp
      apply hf1
      simp only [S23, Finset.mem_insert, Finset.mem_singleton] at hp
      omega
  have h2 : ∏ p ∈ P.filter (fun p => ¬ p ≤ 28), f p ≤ ∏ k ∈ Finset.Icc 29 N, f k := by
    apply prod_le_prod_of_subset_one_le' f
    · intro p hp
      obtain ⟨hpP, hp28⟩ := Finset.mem_filter.mp hp
      have := Finset.mem_Icc.mp (Finset.mem_filter.mp hpP).1
      rw [Finset.mem_Icc]; omega
    · intro k hk
      exact hf1 k (by have := Finset.mem_Icc.mp hk; omega)
  have h3 : ∏ k ∈ Finset.Icc 29 N, f k ≤ 28 / 27 := tail_prod_le N
  have h4 : ∏ p ∈ S23, f p ≤ 19269528 / 10000000 := by
    simp only [S23, hf]
    norm_num
  have h0a : 0 ≤ ∏ p ∈ P.filter (fun p => p ≤ 28), f p :=
    Finset.prod_nonneg fun p hp => by
      have := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.two_le
      linarith [hf1 p this]
  have h0b : 0 ≤ ∏ p ∈ P.filter (fun p => ¬ p ≤ 28), f p :=
    Finset.prod_nonneg fun p hp => by
      have := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.two_le
      linarith [hf1 p this]
  calc (∏ p ∈ P.filter (fun p => p ≤ 28), f p) * ∏ p ∈ P.filter (fun p => ¬ p ≤ 28), f p
      ≤ (19269528 / 10000000) * (28 / 27) := by
        apply mul_le_mul (h1.trans h4) (h2.trans h3) h0b (by norm_num)
    _ ≤ 2 := by norm_num

/-- `∑_{j ≤ N} j/φ(j) ≤ 2N` (the paper uses `≤ (ζ(2)ζ(3)/ζ(6)) N = 1.9436… N`). -/
theorem sum_div_totient_le (N : ℕ) : ∑ j ∈ Finset.Icc 1 N, (j : ℝ) / Nat.totient j ≤ 2 * N := by
  refine (sum_div_totient_le_mul_prod N).trans ?_
  have := euler_partial_le_two N
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  nlinarith

/-- `∑_{h ≤ K} τ(h) ≤ K (1 + log K)`. -/
theorem sum_card_divisors_le (K : ℕ) :
    ∑ h ∈ Finset.Icc 1 K, ((Nat.divisors h).card : ℝ) ≤ K * (1 + Real.log K) := by
  have h1 : ∑ h ∈ Finset.Icc 1 K, (Nat.divisors h).card
      = ∑ d ∈ Finset.Icc 1 K, K / d := by
    have : ∀ h ∈ Finset.Icc 1 K, (Nat.divisors h).card
        = ∑ d ∈ Finset.Icc 1 K, if d ∣ h then 1 else 0 := by
      intro h hh
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
      congr 1
      ext d
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      have hh' := Finset.mem_Icc.mp hh
      constructor
      · rintro ⟨hd, -⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hd (by omega), (Nat.le_of_dvd (by omega) hd).trans hh'.2⟩, hd⟩
      · rintro ⟨-, hd⟩; exact ⟨hd, by omega⟩
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul, mul_one]
    rw [← Nat.Ioc_filter_dvd_card_eq_div]
    rfl
  have h2 : ∑ h ∈ Finset.Icc 1 K, ((Nat.divisors h).card : ℝ) = ∑ d ∈ Finset.Icc 1 K, ((K / d : ℕ) : ℝ) := by
    exact_mod_cast h1
  rw [h2]
  have h3 : ∀ d ∈ Finset.Icc 1 K, ((K / d : ℕ) : ℝ) ≤ K * (1 / (d : ℝ)) := by
    intro d hd
    rw [mul_one_div]
    exact Nat.cast_div_le
  refine (Finset.sum_le_sum h3).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  have hh := harmonic_le_one_add_log K
  have : ((harmonic K : ℚ) : ℝ) = ∑ d ∈ Finset.Icc 1 K, 1 / (d : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    simp
  rw [← this]
  exact hh

lemma mul_div_totient_le (d j : ℕ) (hd : 0 < d) (hj : 0 < j) :
    ((d * j : ℕ) : ℝ) / Nat.totient (d * j)
      ≤ (d : ℝ) / Nat.totient d * ((j : ℝ) / Nat.totient j) := by
  have hφd : (0 : ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.mpr hd
  have hφj : (0 : ℝ) < Nat.totient j := by exact_mod_cast Nat.totient_pos.mpr hj
  have hsup : (Nat.totient d : ℝ) * Nat.totient j ≤ Nat.totient (d * j) := by
    exact_mod_cast Nat.totient_super_multiplicative d j
  calc ((d * j : ℕ) : ℝ) / Nat.totient (d * j)
      ≤ ((d * j : ℕ) : ℝ) / ((Nat.totient d : ℝ) * Nat.totient j) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hsup
    _ = (d : ℝ) / Nat.totient d * ((j : ℝ) / Nat.totient j) := by
        push_cast; rw [div_mul_div_comm]

lemma sum_multiples_div_totient_le (N d : ℕ) (hd : 0 < d) :
    (Nat.totient d : ℝ) * ∑ q ∈ (Finset.Icc 1 N).filter (fun q => d ∣ q), (q : ℝ) / Nat.totient q
      ≤ 2 * N := by
  have hbij : ∑ q ∈ (Finset.Icc 1 N).filter (fun q => d ∣ q), (q : ℝ) / Nat.totient q
      = ∑ j ∈ Finset.Icc 1 (N / d), ((d * j : ℕ) : ℝ) / Nat.totient (d * j) := by
    symm
    refine Finset.sum_bij' (fun j _ => d * j) (fun q _ => q / d) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      have hj' := Finset.mem_Icc.mp hj
      rw [Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩,
        Nat.dvd_mul_right d j⟩
      exact (Nat.le_div_iff_mul_le hd).mp hj'.2 |>.trans' (by rw [mul_comm])
    · intro q hq
      obtain ⟨hq1, hdq⟩ := Finset.mem_filter.mp hq
      have hq1' := Finset.mem_Icc.mp hq1
      rw [Finset.mem_Icc]
      refine ⟨?_, Nat.div_le_div_right hq1'.2⟩
      obtain ⟨k, rfl⟩ := hdq
      rw [Nat.mul_div_cancel_left k hd]
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h; simp at hq1'
      · exact h
    · intro j _; exact Nat.mul_div_cancel_left j hd
    · intro q hq; exact Nat.mul_div_cancel' (Finset.mem_filter.mp hq).2
    · intro j _; rfl
  rw [hbij]
  have hφd : (0 : ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.mpr hd
  have h1 : ∑ j ∈ Finset.Icc 1 (N / d), ((d * j : ℕ) : ℝ) / Nat.totient (d * j)
      ≤ (d : ℝ) / Nat.totient d * ∑ j ∈ Finset.Icc 1 (N / d), (j : ℝ) / Nat.totient j := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j hj =>
      mul_div_totient_le d j hd (Finset.mem_Icc.mp hj).1
  have h2 := sum_div_totient_le (N / d)
  have h3 : ((d * (N / d) : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.mul_div_le N d
  push_cast at h3
  calc (Nat.totient d : ℝ) * ∑ j ∈ Finset.Icc 1 (N / d), ((d * j : ℕ) : ℝ) / Nat.totient (d * j)
      ≤ (Nat.totient d : ℝ) * ((d : ℝ) / Nat.totient d *
          ∑ j ∈ Finset.Icc 1 (N / d), (j : ℝ) / Nat.totient j) :=
        mul_le_mul_of_nonneg_left h1 hφd.le
    _ = (d : ℝ) * ∑ j ∈ Finset.Icc 1 (N / d), (j : ℝ) / Nat.totient j := by
        field_simp
    _ ≤ (d : ℝ) * (2 * ((N / d : ℕ) : ℝ)) := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
    _ ≤ 2 * N := by nlinarith

/-- **Off-diagonal bound of `lem:M2`** for the explicit orthogonality expression:
if `|c_q| ≤ ∑_{d | (q,h)} φ(d)` for every `q` and `h ≠ 0`, then
`|∑_{q ≤ Q} ω(q) c_q| ≤ 2 w_max Q τ(|h|)` (the paper has `1.95` in place of `2`). -/
theorem offdiag_bound (W : Weight) (Q : ℝ) (hQ : 0 < Q) (h : ℤ) (hh : h ≠ 0) (c : ℕ → ℂ)
    (hc : ∀ q, ‖c q‖ ≤ ∑ d ∈ q.divisors.filter (fun d : ℕ => ((d : ℕ) : ℤ) ∣ h),
      (Nat.totient d : ℝ)) :
    ‖∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (W.omega Q q : ℂ) * c q‖
      ≤ 2 * W.wmax * Q * (Nat.divisors h.natAbs).card := by
  set N := ⌊Q⌋₊ with hN
  have hwmax0 : 0 ≤ W.wmax := (W.nonneg 0).trans (W.le_wmax 0)
  have step1 : ‖∑ q ∈ Finset.Icc 1 N, (W.omega Q q : ℂ) * c q‖
      ≤ ∑ q ∈ Finset.Icc 1 N, W.wmax * ((q : ℝ) / Nat.totient q) *
          ∑ d ∈ q.divisors.filter (fun d : ℕ => ((d : ℕ) : ℤ) ∣ h), (Nat.totient d : ℝ) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q hq => ?_)
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hom0 : 0 ≤ W.omega Q q := by
      unfold Weight.omega
      have := W.nonneg ((q : ℝ) / Q)
      positivity
    have homle : W.omega Q q ≤ W.wmax * ((q : ℝ) / Nat.totient q) := by
      unfold Weight.omega
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right (W.le_wmax _) (by positivity)
    rw [abs_of_nonneg hom0]
    exact mul_le_mul homle (hc q) (norm_nonneg _) (by positivity)
  refine step1.trans ?_
  have step2 : ∑ q ∈ Finset.Icc 1 N, W.wmax * ((q : ℝ) / Nat.totient q) *
          ∑ d ∈ q.divisors.filter (fun d : ℕ => ((d : ℕ) : ℤ) ∣ h), (Nat.totient d : ℝ)
      = W.wmax * ∑ d ∈ h.natAbs.divisors, (Nat.totient d : ℝ) *
          ∑ q ∈ (Finset.Icc 1 N).filter (fun q => d ∣ q), (q : ℝ) / Nat.totient q := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm' (t' := h.natAbs.divisors)
      (s' := fun d => (Finset.Icc 1 N).filter (fun q => d ∣ q))]
    · exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun q _ => by ring
    · intro q d
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors, Int.natCast_dvd]
      constructor
      · rintro ⟨hq, ⟨hdq, hq0⟩, hdh⟩
        exact ⟨⟨hq, hdq⟩, hdh, Int.natAbs_ne_zero.mpr hh⟩
      · rintro ⟨⟨hq, hdq⟩, hdh, -⟩
        exact ⟨hq, ⟨hdq, by omega⟩, hdh⟩
  rw [step2]
  have step3 : ∀ d ∈ h.natAbs.divisors, (Nat.totient d : ℝ) *
      ∑ q ∈ (Finset.Icc 1 N).filter (fun q => d ∣ q), (q : ℝ) / Nat.totient q ≤ 2 * Q := by
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    refine (sum_multiples_div_totient_le N d hd0).trans ?_
    have : (N : ℝ) ≤ Q := Nat.floor_le hQ.le
    linarith
  calc W.wmax * ∑ d ∈ h.natAbs.divisors, (Nat.totient d : ℝ) *
          ∑ q ∈ (Finset.Icc 1 N).filter (fun q => d ∣ q), (q : ℝ) / Nat.totient q
      ≤ W.wmax * ∑ d ∈ h.natAbs.divisors, 2 * Q :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum step3) hwmax0
    _ = 2 * W.wmax * Q * (Nat.divisors h.natAbs).card := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **Abstract `lem:M2`.** A kernel on an interval of `K ≥ 1` integers with
`|A(n,n)| ≤ H₀`, `|A(n,m)| ≤ B τ(|n-m|)` (`n ≠ m`) and `|A(n,m)| = |A(m,n)|` satisfies
`|x^*Ax| ≤ (H₀ + 2B K(1 + log K)) ‖x‖²`. -/
theorem short_interval_abstract (N₀ : ℤ) (K : ℕ) (hK : 1 ≤ K) (A : ℤ → ℤ → ℂ)
    (hsymm : ∀ n m, ‖A n m‖ = ‖A m n‖) (H₀ B : ℝ) (hB : 0 ≤ B)
    (hdiag : ∀ n ∈ intervalZ N₀ K, ‖A n n‖ ≤ H₀)
    (hoff : ∀ n ∈ intervalZ N₀ K, ∀ m ∈ intervalZ N₀ K, n ≠ m →
      ‖A n m‖ ≤ B * (Nat.divisors (n - m).natAbs).card)
    (x : ℤ → ℂ) :
    ‖∑ n ∈ intervalZ N₀ K, ∑ m ∈ intervalZ N₀ K, x n * conj (x m) * A n m‖
      ≤ (H₀ + 2 * B * K * (1 + Real.log K)) * normSq (intervalZ N₀ K) x := by
  refine schur_test _ A hsymm H₀ (2 * B * K * (1 + Real.log K)) hdiag ?_ x
  intro n hn
  set I := intervalZ N₀ K with hI
  have h1 : ∑ m ∈ I.erase n, ‖A n m‖ ≤ ∑ m ∈ I.erase n, B * (Nat.divisors (n - m).natAbs).card :=
    Finset.sum_le_sum fun m hm => hoff n hn m (Finset.mem_of_mem_erase hm)
      (Finset.ne_of_mem_erase hm).symm
  refine h1.trans ?_
  have hmaps : ∀ m ∈ I.erase n, (n - m).natAbs ∈ Finset.Icc 1 K := by
    intro m hm
    have hne := Finset.ne_of_mem_erase hm
    have hm' := Finset.mem_Ico.mp (Finset.mem_of_mem_erase hm)
    have hn' := Finset.mem_Ico.mp hn
    rw [Finset.mem_Icc]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have h2 : ∀ h ∈ Finset.Icc 1 K,
      ∑ m ∈ (I.erase n).filter (fun m => (n - m).natAbs = h), B * ((Nat.divisors (n - m).natAbs).card : ℝ)
        ≤ 2 * (B * (Nat.divisors h).card) := by
    intro h _
    have heq : ∀ m ∈ (I.erase n).filter (fun m => (n - m).natAbs = h),
        B * ((Nat.divisors (n - m).natAbs).card : ℝ) = B * (Nat.divisors h).card := by
      intro m hm
      rw [(Finset.mem_filter.mp hm).2]
    rw [Finset.sum_congr rfl heq, Finset.sum_const, nsmul_eq_mul]
    have hcard : ((I.erase n).filter (fun m => (n - m).natAbs = h)).card ≤ 2 := by
      have hsub : (I.erase n).filter (fun m => (n - m).natAbs = h) ⊆ {n - h, n + h} := by
        intro m hm
        have := (Finset.mem_filter.mp hm).2
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      exact (Finset.card_le_card hsub).trans (Finset.card_le_two)
    have hnn : 0 ≤ B * ((Nat.divisors h).card : ℝ) := mul_nonneg hB (Nat.cast_nonneg _)
    have : ((((I.erase n).filter (fun m => (n - m).natAbs = h)).card : ℕ) : ℝ) ≤ 2 := by
      exact_mod_cast hcard
    nlinarith
  refine (Finset.sum_le_sum h2).trans ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  have := sum_card_divisors_le K
  have : 2 * (B * ∑ h ∈ Finset.Icc 1 K, ((Nat.divisors h).card : ℝ)) ≤ 2 * (B * (K * (1 + Real.log K))) := by
    gcongr
  linarith

end Families
