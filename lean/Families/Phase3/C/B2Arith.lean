/-
Arithmetic input for `lem:B2` (Lemma 5.7).

* `ramanujan_coprime`: `c_r(n) = μ(r)` for `(r, n) = 1` (Möbius inversion of `∑_{e|d} c_e(h) = d·1[d|h]`);
  hence `Λ_R(p) = G(R)` for primes `p > R` (`LamR_prime`).
* `G(R) = ∑_{r≤R} μ²(r)/φ(r)`: `log(R+1) ≤ G(R)` (`log_le_Gsum`; via `∑_{m | r^∞} 1/m = r/φ(r)`, the
  Euler product over `factoredNumbers`) and `G(R) ≤ 2 + 2 log R` (`Gsum_le`; Abel summation against
  `∑_{j≤N} j/φ(j) ≤ 2N`).
* `card_pp_le`: at most `√M log₂ M` proper prime powers `p^k ≤ M`, `k ≥ 2`.
* `sum_F_ramanujan_mul_le`: `∑ F(n) c_r(n) c_{r'}(n) = 1[r=r'] φ(r) ∑ F(n) + O(φ(r)φ(r')(rr'/4)^K sup|F^{(K)}|)`
  (orthogonality of Ramanujan sums in the frequency form of step (4)).
-/
import Families.Phase3.C.Freq
import Families.PrimeSide
import Families.Phase1.B.Omega
import Families.Phase1.B.FS

noncomputable section

open scoped ArithmeticFunction.Moebius
open Finset ArithmeticFunction

namespace Families.Phase3.C

open Families

/-! ### `c_r(n) = μ(r)` for `(r, n) = 1` -/

theorem ramanujan_coprime {r n : ℕ} (hr : 0 < r) (h : Nat.Coprime r n) :
    ramanujan r n = (μ r : ℂ) := by
  have key := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℂ)
    (f := fun e => ramanujan e (n : ℤ))
    (g := fun d => if ((d : ℕ) : ℤ) ∣ (n : ℤ) then (d : ℂ) else 0)).mp
    (fun d hd => sum_divisors_ramanujan d hd n) r hr
  rw [← key, Finset.sum_eq_single (r, 1)]
  · simp
  · intro x hx hne
    have hx' := Nat.mem_divisorsAntidiagonal.mp hx
    split_ifs with hdiv
    · exfalso
      have h2 : x.2 ∣ n := by exact_mod_cast hdiv
      have h3 : x.2 ∣ r := ⟨x.1, by rw [← hx'.1]; ring⟩
      have h4 : x.2 = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h3 h) h2
      apply hne
      have h5 : x.1 = r := by rw [← hx'.1, h4, mul_one]
      exact Prod.ext h5 h4
    · simp
  · intro h'; exfalso; exact h' (Nat.mem_divisorsAntidiagonal.mpr ⟨by simp, hr.ne'⟩)

/-- `G(R) = ∑_{r ≤ R} μ²(r)/φ(r)`. -/
def Gsum (R : ℕ) : ℝ := ∑ r ∈ Finset.Icc 1 R, (μ r : ℝ) ^ 2 / Nat.totient r

lemma Gsum_nonneg (R : ℕ) : 0 ≤ Gsum R :=
  Finset.sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

lemma Gsum_zero : Gsum 0 = 0 := by simp [Gsum]

/-- `Λ_R(p) = G(R)` for primes `p > R` (`c_r(p) = μ(r)`). -/
theorem LamR_prime {R p : ℕ} (hp : p.Prime) (hR : R < p) : PrimeSetup.LamR R p = Gsum R := by
  unfold PrimeSetup.LamR Gsum
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
  have hrp : r < p := lt_of_le_of_lt (Finset.mem_Icc.mp hr).2 hR
  have hcop : Nat.Coprime r p := by
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
    intro hd; exact absurd (Nat.le_of_dvd hr1 hd) (not_le.mpr hrp)
  have : ((ramanujan r (p : ℤ)).re) = (μ r : ℝ) := by
    have := ramanujan_coprime hr1 hcop
    rw [show ((p : ℕ) : ℤ) = (p : ℤ) from rfl] at this
    rw [this]; simp
  rw [this]; ring

lemma abs_LamR_le (R n : ℕ) : |PrimeSetup.LamR R n| ≤ R := by
  unfold PrimeSetup.LamR
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ r ∈ Finset.Icc 1 R, |(μ r : ℝ) / Nat.totient r * (ramanujan r n).re| ≤ 1 := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hφ : (0 : ℝ) < Nat.totient r := by exact_mod_cast Nat.totient_pos.mpr hr1
    have hμ : |(μ r : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := r)
    have hc : |(ramanujan r n).re| ≤ Nat.totient r :=
      (Complex.abs_re_le_norm _).trans (norm_ramanujan_le r n)
    rw [abs_mul, abs_div, Nat.abs_cast]
    calc |(μ r : ℝ)| / Nat.totient r * |(ramanujan r n).re|
        ≤ 1 / Nat.totient r * Nat.totient r := by gcongr
      _ = 1 := by field_simp
  refine (Finset.sum_le_sum this).trans ?_
  simp

/-! ### `G(R) ≥ log(R + 1)` -/

/-- `∑_{m ∈ T} 1/m ≤ r/φ(r)` for any finite set of `m ≥ 1` with prime factors among those of `r`. -/
theorem sum_inv_le_of_primeFactors_subset {r : ℕ} (hr : r ≠ 0) (T : Finset ℕ)
    (hT : ∀ m ∈ T, m ≠ 0 ∧ m.primeFactors ⊆ r.primeFactors) :
    ∑ m ∈ T, (m : ℝ)⁻¹ ≤ (r : ℝ) / Nat.totient r := by
  set s := r.primeFactors with hs
  have hf₁ : ((1 : ℕ) : ℝ)⁻¹ = 1 := by simp
  have hmul : ∀ {m n : ℕ}, Nat.Coprime m n → ((m * n : ℕ) : ℝ)⁻¹ = (m : ℝ)⁻¹ * (n : ℝ)⁻¹ := by
    intro m n _; push_cast; rw [mul_inv]
  have hsum : ∀ {p : ℕ}, p.Prime → Summable (fun n : ℕ => ‖(((p ^ n : ℕ) : ℝ))⁻¹‖) := by
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have : (fun n : ℕ => ‖(((p ^ n : ℕ) : ℝ))⁻¹‖) = fun n => ((p : ℝ)⁻¹) ^ n := by
      funext n; push_cast; rw [norm_inv, norm_pow, Real.norm_natCast, inv_pow]
    rw [this]
    exact summable_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hp1)
  have hHas := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (f := fun m : ℕ => (m : ℝ)⁻¹) hf₁ hmul hsum s).2
  -- the value of the product
  have hprod : ∏ p ∈ s with p.Prime, ∑' n : ℕ, (((p ^ n : ℕ) : ℝ))⁻¹ = (r : ℝ) / Nat.totient r := by
    have hfilt : s.filter Nat.Prime = s := Finset.filter_true_of_mem fun p hp =>
      Nat.prime_of_mem_primeFactors hp
    rw [hfilt]
    have hgeom : ∀ p ∈ s, ∑' n : ℕ, (((p ^ n : ℕ) : ℝ))⁻¹ = (1 - 1 / (p : ℝ))⁻¹ := by
      intro p hp
      have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
      have : (fun n : ℕ => (((p ^ n : ℕ) : ℝ))⁻¹) = fun n => ((p : ℝ)⁻¹) ^ n := by
        funext n; push_cast; rw [inv_pow]
      rw [this, tsum_geometric_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hp1), one_div]
    rw [Finset.prod_congr rfl hgeom, Finset.prod_inv_distrib,
      ← Families.Phase1.B.totient_div_self_eq hr, inv_div]
  rw [hprod] at hHas
  -- restrict `T` to the subtype
  have hTsub : ∀ m ∈ T, m ∈ Nat.factoredNumbers s := by
    intro m hm
    rw [Nat.mem_factoredNumbers']
    intro p hp hpm
    exact (hT m hm).2 (Nat.mem_primeFactors.mpr ⟨hp, hpm, (hT m hm).1⟩)
  set T' : Finset (Nat.factoredNumbers s) := T.subtype (· ∈ Nat.factoredNumbers s)
  have hsumT : ∑ m ∈ T, (m : ℝ)⁻¹ = ∑ m ∈ T', ((m : ℕ) : ℝ)⁻¹ := by
    rw [Finset.sum_subtype_of_mem (f := fun m : ℕ => (m : ℝ)⁻¹) hTsub]
  rw [hsumT]
  exact sum_le_hasSum T' (fun _ _ => by positivity) hHas

/-- `rad(n) = ∏_{p | n} p`. -/
def rad (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

lemma rad_dvd (n : ℕ) : rad n ∣ n := Nat.prod_primeFactors_dvd n

lemma rad_primeFactors (n : ℕ) : (rad n).primeFactors = n.primeFactors :=
  Nat.primeFactors_prod fun _ hp => Nat.prime_of_mem_primeFactors hp

lemma rad_squarefree (n : ℕ) : Squarefree (rad n) :=
  Families.Phase1.B.squarefree_prod_primes fun _ hp => Nat.prime_of_mem_primeFactors hp

lemma rad_pos (n : ℕ) : 0 < rad n :=
  Finset.prod_pos fun _ hp => (Nat.prime_of_mem_primeFactors hp).pos

/-- `H_R = ∑_{n ≤ R} 1/n ≤ G(R)`. -/
theorem harmonic_le_Gsum (R : ℕ) : ∑ n ∈ Finset.Icc 1 R, (n : ℝ)⁻¹ ≤ Gsum R := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := rad) (t := (Finset.Icc 1 R).image rad)
    (fun n hn => Finset.mem_image_of_mem rad hn)]
  have hfib : ∀ r ∈ (Finset.Icc 1 R).image rad,
      ∑ n ∈ (Finset.Icc 1 R).filter (fun n => rad n = r), (n : ℝ)⁻¹ ≤
        (μ r : ℝ) ^ 2 / Nat.totient r := by
    intro r hr
    obtain ⟨n₀, hn₀, rfl⟩ := Finset.mem_image.mp hr
    have hn₀1 : 1 ≤ n₀ := (Finset.mem_Icc.mp hn₀).1
    set r := rad n₀ with hrdef
    have hr0 : 0 < r := rad_pos n₀
    have hμ : (μ r : ℝ) ^ 2 = 1 := by
      have := ArithmeticFunction.moebius_sq_eq_one_of_squarefree (rad_squarefree n₀)
      exact_mod_cast this
    rw [hμ]
    -- `n = r · (n / r)` on the fibre
    have hsplit : ∑ n ∈ (Finset.Icc 1 R).filter (fun n => rad n = r), (n : ℝ)⁻¹ =
        (r : ℝ)⁻¹ * ∑ m ∈ ((Finset.Icc 1 R).filter (fun n => rad n = r)).image (· / r),
          (m : ℝ)⁻¹ := by
      rw [Finset.sum_image]
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n hn => ?_
        have hn' := Finset.mem_filter.mp hn
        have hdiv : r ∣ n := hn'.2 ▸ rad_dvd n
        obtain ⟨k, hk⟩ := hdiv
        have hk' : n / r = k := by rw [hk, Nat.mul_div_cancel_left k hr0]
        rw [hk', hk]; push_cast; rw [mul_inv]
      · intro n hn n' hn' h
        have h1 : r ∣ n := (Finset.mem_filter.mp hn).2 ▸ rad_dvd n
        have h2 : r ∣ n' := (Finset.mem_filter.mp hn').2 ▸ rad_dvd n'
        simp only at h
        rw [← Nat.div_mul_cancel h1, ← Nat.div_mul_cancel h2, h]
    rw [hsplit]
    have hbound := sum_inv_le_of_primeFactors_subset (r := r) hr0.ne'
      (((Finset.Icc 1 R).filter (fun n => rad n = r)).image (· / r)) (by
        intro m hm
        obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hm
        have hn' := Finset.mem_filter.mp hn
        have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn'.1).1
        have hdiv : r ∣ n := hn'.2 ▸ rad_dvd n
        have hne : n / r ≠ 0 := by
          intro h0
          rw [Nat.div_eq_zero_iff] at h0
          rcases h0 with h0 | h0
          · omega
          · exact absurd (Nat.le_of_dvd (by omega) hdiv) (not_le.mpr h0)
        refine ⟨hne, ?_⟩
        calc (n / r).primeFactors ⊆ n.primeFactors :=
              Nat.primeFactors_mono (Nat.div_dvd_of_dvd hdiv) (by omega)
          _ = r.primeFactors := by rw [← hn'.2, rad_primeFactors])
    have hr0' : (0 : ℝ) < r := by exact_mod_cast hr0
    have hφ : (0 : ℝ) < Nat.totient r := by exact_mod_cast Nat.totient_pos.mpr hr0
    calc (r : ℝ)⁻¹ * ∑ m ∈ ((Finset.Icc 1 R).filter (fun n => rad n = r)).image (· / r),
          (m : ℝ)⁻¹ ≤ (r : ℝ)⁻¹ * ((r : ℝ) / Nat.totient r) :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = 1 / Nat.totient r := by field_simp
  refine (Finset.sum_le_sum hfib).trans ?_
  unfold Gsum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro r hr
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hr
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnR : n ≤ R := (Finset.mem_Icc.mp hn).2
    refine Finset.mem_Icc.mpr ⟨rad_pos n, le_trans (Nat.le_of_dvd (by omega) (rad_dvd n)) hnR⟩
  · intro r _ _; exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

theorem log_le_Gsum (R : ℕ) : Real.log (R + 1) ≤ Gsum R := by
  have h1 := log_add_one_le_harmonic R
  rw [harmonic_eq_sum_Icc] at h1
  push_cast at h1
  exact h1.trans (harmonic_le_Gsum R)

/-! ### `G(R) ≤ 2 + 2 log R` -/

lemma sum_inv_totient_le_aux (R : ℕ) (hR : 1 ≤ R) :
    ∑ r ∈ Finset.Icc 1 R, ((Nat.totient r : ℝ))⁻¹ ≤
      Families.Phase1.B.Aphi R / R + 2 * (∑ n ∈ Finset.Icc 1 R, (n : ℝ)⁻¹ - 1) := by
  induction R, hR using Nat.le_induction with
  | base => simp [Families.Phase1.B.Aphi]
  | succ R hR ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
      Families.Phase1.B.Aphi_succ]
    have hA := Families.Phase1.B.Aphi_le R
    have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
    have hφ : (0 : ℝ) < Nat.totient (R + 1) := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    have key : Families.Phase1.B.Aphi R / R ≤
        Families.Phase1.B.Aphi R / (R + 1) + 2 * ((R : ℝ) + 1)⁻¹ := by
      rw [← div_eq_mul_inv, ← add_div, div_le_div_iff₀ hR0 (by positivity)]
      nlinarith [Families.Phase1.B.Aphi_nonneg R]
    have : (((R + 1 : ℕ) : ℝ) / Nat.totient (R + 1)) / ((R + 1 : ℕ) : ℝ) =
        ((Nat.totient (R + 1) : ℝ))⁻¹ := by
      field_simp
    push_cast at this ⊢
    rw [add_div, this]
    linarith

theorem Gsum_le (R : ℕ) (hR : 1 ≤ R) : Gsum R ≤ 2 + 2 * Real.log R := by
  have h1 : Gsum R ≤ ∑ r ∈ Finset.Icc 1 R, ((Nat.totient r : ℝ))⁻¹ := by
    unfold Gsum
    refine Finset.sum_le_sum fun r hr => ?_
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hφ : (0 : ℝ) < Nat.totient r := by exact_mod_cast Nat.totient_pos.mpr hr1
    have hμ : (μ r : ℝ) ^ 2 ≤ 1 := by
      have := ArithmeticFunction.abs_moebius_le_one (n := r)
      have h' : |(μ r : ℝ)| ≤ 1 := by exact_mod_cast this
      nlinarith [abs_nonneg (μ r : ℝ), sq_abs (μ r : ℝ)]
    rw [div_eq_mul_inv]
    calc (μ r : ℝ) ^ 2 * ((Nat.totient r : ℝ))⁻¹ ≤ 1 * ((Nat.totient r : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_right hμ (by positivity)
      _ = _ := one_mul _
  have h2 := sum_inv_totient_le_aux R hR
  have h3 : Families.Phase1.B.Aphi R / R ≤ 2 := by
    rw [div_le_iff₀ (by exact_mod_cast hR)]; exact Families.Phase1.B.Aphi_le R
  have h4 : ∑ n ∈ Finset.Icc 1 R, (n : ℝ)⁻¹ ≤ 1 + Real.log R := by
    have := harmonic_le_one_add_log R
    rw [harmonic_eq_sum_Icc] at this; push_cast at this; exact this
  linarith

/-! ### Proper prime powers -/

/-- The proper prime powers `p^k ≤ M`, `k ≥ 2`, are at most `√M log₂ M` in number. -/
theorem card_pp_le (M : ℕ) :
    ((Finset.Icc 1 M).filter (fun n => Λ n ≠ 0 ∧ ¬ n.Prime)).card ≤ Nat.sqrt M * Nat.log 2 M := by
  have hsub : (Finset.Icc 1 M).filter (fun n => Λ n ≠ 0 ∧ ¬ n.Prime) ⊆
      (Finset.Icc 1 (Nat.sqrt M) ×ˢ Finset.Icc 1 (Nat.log 2 M)).image (fun x => x.1 ^ (x.2 + 1)) := by
    intro n hn
    obtain ⟨hnI, hΛ, hnp⟩ := Finset.mem_filter.mp hn
    have hnM : n ≤ M := (Finset.mem_Icc.mp hnI).2
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp (vonMangoldt_ne_zero_iff.mp hΛ)
    have hk2 : 2 ≤ k := by
      by_contra h
      have : k = 1 := by omega
      subst this; exact hnp (by simpa using hp)
    refine Finset.mem_image.mpr ⟨(p, k - 1), Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · refine Finset.mem_Icc.mpr ⟨hp.one_lt.le, Nat.le_sqrt'.mpr ?_⟩
      calc p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk2
        _ ≤ M := hnM
    · refine Finset.mem_Icc.mpr ⟨by omega, ?_⟩
      have : 2 ^ k ≤ M := (Nat.pow_le_pow_left hp.two_le k).trans hnM
      have := Nat.le_log_of_pow_le (by norm_num) this
      omega
    · simp only; congr 1; omega
  refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
  simp

/-! ### Ramanujan products: the frequency form of orthogonality -/

lemma ramanujan_mul_expand {r r' : ℕ} (hr : 0 < r) (hr' : 0 < r') (n : ℕ) :
    ramanujan r n * ramanujan r' n =
      ∑ h ∈ reduced r, ∑ h' ∈ reduced r',
        eA (n * (((h * r' + h' * r : ℤ) : ℝ) / ((r * r' : ℕ) : ℝ))) := by
  unfold ramanujan
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun h' _ => ?_
  rw [← eA_add']
  congr 1
  have hr0 : (r : ℝ) ≠ 0 := by positivity
  have hr0' : (r' : ℝ) ≠ 0 := by positivity
  push_cast; field_simp

/-- For `h` a reduced residue mod `r`, there is exactly one reduced `h'` with `r | h + h'`. -/
lemma sum_neg_residue {r : ℕ} (hr : 0 < r) {h : ℕ} (hh : h ∈ reduced r) :
    ∑ h' ∈ reduced r, (if (r : ℤ) ∣ (h + h' : ℤ) then (1 : ℂ) else 0) = 1 := by
  simp only [reduced, Finset.mem_filter, Finset.mem_range] at hh
  set h₀ := (r - h) % r with hh₀
  have hmem : h₀ ∈ reduced r := by
    simp only [reduced, Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.mod_lt _ hr, ?_⟩
    rcases Nat.eq_zero_or_pos h with h0 | h0
    · subst h0
      have : r = 1 := by
        have := hh.2; simpa [Nat.coprime_zero_left] using this
      subst this; simp [hh₀]
    · rw [hh₀, Nat.mod_eq_of_lt (by omega)]
      exact (Nat.coprime_self_sub_left hh.1.le).mpr hh.2
  have hdiv : ∀ h' ∈ reduced r, ((r : ℤ) ∣ (h + h' : ℤ) ↔ h' = h₀) := by
    intro h' hh'
    simp only [reduced, Finset.mem_filter, Finset.mem_range] at hh'
    constructor
    · intro hd
      have hd' : r ∣ h + h' := by exact_mod_cast hd
      have hlt : h + h' < 2 * r := by omega
      obtain ⟨c, hc⟩ := hd'
      have : c = 0 ∨ c = 1 := by
        rcases Nat.lt_or_ge c 2 with h2 | h2
        · omega
        · exfalso; nlinarith
      rcases this with rfl | rfl
      · simp at hc; rw [hh₀]; rw [hc.1, hc.2]; simp
      · rw [hh₀]
        have hh'eq : h' = r - h := by omega
        rw [hh'eq]
        rcases Nat.eq_zero_or_pos h with h0 | h0
        · subst h0; omega
        · rw [Nat.mod_eq_of_lt (by omega)]
    · rintro rfl
      rcases Nat.eq_zero_or_pos h with h0 | h0
      · subst h0
        rw [hh₀]; simp
      · rw [hh₀, Nat.mod_eq_of_lt (by omega)]
        refine ⟨1, ?_⟩
        push_cast [Nat.cast_sub hh.1.le]; ring
  rw [Finset.sum_eq_single h₀]
  · rw [if_pos ((hdiv h₀ hmem).mpr rfl)]
  · intro h' hh' hne
    rw [if_neg (fun hd => hne ((hdiv h' hh').mp hd))]
  · intro h; exact absurd hmem h

/-- The integer frequencies of `c_r c_{r'}`: `#{(h,h') : rr' | hr' + h'r} = 1[r = r'] φ(r)`. -/
lemma int_freq_count {r r' : ℕ} (hr : 0 < r) (hr' : 0 < r') :
    ∑ h ∈ reduced r, ∑ h' ∈ reduced r',
      (if ((r * r' : ℕ) : ℤ) ∣ (h * r' + h' * r : ℤ) then (1 : ℂ) else 0) =
        if r = r' then (Nat.totient r : ℂ) else 0 := by
  by_cases hrr : r = r'
  · subst hrr
    rw [if_pos rfl]
    have : ∀ h ∈ reduced r, ∀ h' ∈ reduced r,
        (((r * r : ℕ) : ℤ) ∣ (h * r + h' * r : ℤ)) ↔ ((r : ℤ) ∣ (h + h' : ℤ)) := by
      intro h _ h' _
      have hr0 : (r : ℤ) ≠ 0 := by exact_mod_cast hr.ne'
      rw [show (h * r + h' * r : ℤ) = (h + h') * r by ring]
      push_cast
      exact mul_dvd_mul_iff_right hr0
    rw [Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun h' hh' => by
      rw [if_congr (this h hh h' hh') rfl rfl]]
    rw [Finset.sum_congr rfl fun h hh => sum_neg_residue hr hh]
    simp [card_reduced]
  · rw [if_neg hrr]
    refine Finset.sum_eq_zero fun h hh => Finset.sum_eq_zero fun h' hh' => ?_
    rw [if_neg]
    intro hd
    apply hrr
    simp only [reduced, Finset.mem_filter, Finset.mem_range] at hh hh'
    have h1 : (r : ℤ) ∣ (h * r' : ℤ) := by
      have : (r : ℤ) ∣ (h * r' + h' * r : ℤ) :=
        (Int.natCast_dvd_natCast.mpr (dvd_mul_right r r')).trans (by exact_mod_cast hd)
      exact (Int.dvd_add_left (dvd_mul_left _ _)).mp this
    have h2 : (r' : ℤ) ∣ (h' * r : ℤ) := by
      have : (r' : ℤ) ∣ (h * r' + h' * r : ℤ) :=
        (Int.natCast_dvd_natCast.mpr (dvd_mul_left r' r)).trans (by exact_mod_cast hd)
      exact (Int.dvd_add_right (dvd_mul_left _ _)).mp this
    have h1' : r ∣ h * r' := by exact_mod_cast h1
    have h2' : r' ∣ h' * r := by exact_mod_cast h2
    exact Nat.dvd_antisymm (Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_comm.mp hh.2) h1')
      (Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_comm.mp hh'.2) h2')

/-- **Orthogonality in frequency form** (step (4) of `lem:B2`). -/
theorem sum_F_ramanujan_mul_le {r r' : ℕ} (hr : 0 < r) (hr' : 0 < r') {F : ℝ → ℂ} {K : ℕ}
    (hF : ContDiff ℝ K F) {Mb : ℝ} (hM : ∀ y, ‖iteratedDeriv K F y‖ ≤ Mb) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hsupp : ∀ y, F y ≠ 0 → a ≤ y ∧ y ≤ b) (S : Finset ℕ)
    (hS : ∀ n : ℕ, F n ≠ 0 → n ∈ S) :
    ‖∑ n ∈ S, F n * (ramanujan r n * ramanujan r' n) -
        (if r = r' then (Nat.totient r : ℂ) * ∑ n ∈ S, F n else 0)‖ ≤
      Nat.totient r * Nat.totient r' * ((b - a + K + 1) * Mb * (((r * r' : ℕ) : ℝ) / 4) ^ K) := by
  have hM0 : 0 ≤ Mb := (norm_nonneg _).trans (hM 0)
  set M : ℕ := r * r' with hMdef
  have hMpos : 0 < M := Nat.mul_pos hr hr'
  set m : ℕ → ℕ → ℤ := fun h h' => h * r' + h' * r with hm
  set S0 : ℂ := ∑ n ∈ S, F n
  have hexp : ∑ n ∈ S, F n * (ramanujan r n * ramanujan r' n) -
      (if r = r' then (Nat.totient r : ℂ) * S0 else 0) =
      ∑ h ∈ reduced r, ∑ h' ∈ reduced r',
        ((∑ n ∈ S, F n * eA (n * ((m h h' : ℝ) / (M : ℝ)))) -
          (if ((M : ℕ) : ℤ) ∣ m h h' then S0 else 0)) := by
    have hcount := int_freq_count hr hr'
    have h1 : (if r = r' then (Nat.totient r : ℂ) * S0 else 0) =
        ∑ h ∈ reduced r, ∑ h' ∈ reduced r', (if ((M : ℕ) : ℤ) ∣ m h h' then S0 else 0) := by
      have : ∀ h ∈ reduced r, ∀ h' ∈ reduced r',
          (if ((M : ℕ) : ℤ) ∣ m h h' then S0 else 0) =
            (if ((r * r' : ℕ) : ℤ) ∣ (h * r' + h' * r : ℤ) then (1 : ℂ) else 0) * S0 := by
        intro h _ h' _; split_ifs <;> simp
      have h2 : ∑ h ∈ reduced r, ∑ h' ∈ reduced r', (if ((M : ℕ) : ℤ) ∣ m h h' then S0 else 0) =
          ∑ h ∈ reduced r, ∑ h' ∈ reduced r',
            (if ((r * r' : ℕ) : ℤ) ∣ (h * r' + h' * r : ℤ) then (1 : ℂ) else 0) * S0 :=
        Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun h' hh' => this h hh h' hh'
      rw [h2]
      simp_rw [← Finset.sum_mul]
      rw [hcount]; split_ifs <;> simp
    rw [h1]
    simp only [Finset.sum_sub_distrib]
    congr 1
    have : ∀ n ∈ S, F n * (ramanujan r n * ramanujan r' n) =
        ∑ h ∈ reduced r, ∑ h' ∈ reduced r', F n * eA (n * ((m h h' : ℝ) / (M : ℝ))) := by
      intro n _
      rw [ramanujan_mul_expand hr hr' n, Finset.mul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl this]
    calc ∑ n ∈ S, ∑ h ∈ reduced r, ∑ h' ∈ reduced r', F n * eA (n * ((m h h' : ℝ) / (M : ℝ)))
        = ∑ h ∈ reduced r, ∑ n ∈ S, ∑ h' ∈ reduced r', F n * eA (n * ((m h h' : ℝ) / (M : ℝ))) :=
          Finset.sum_comm
      _ = ∑ h ∈ reduced r, ∑ h' ∈ reduced r', ∑ n ∈ S, F n * eA (n * ((m h h' : ℝ) / (M : ℝ))) :=
          Finset.sum_congr rfl fun h _ => Finset.sum_comm
  rw [hexp]
  set Bd : ℝ := (b - a + K + 1) * Mb * ((M : ℝ) / 4) ^ K with hBd
  have hBd0 : 0 ≤ Bd := by
    have : 0 ≤ b - a + K + 1 := by linarith
    positivity
  have hterm : ∀ h ∈ reduced r, ∀ h' ∈ reduced r',
      ‖(∑ n ∈ S, F n * eA (n * ((m h h' : ℝ) / (M : ℝ)))) -
          (if ((M : ℕ) : ℤ) ∣ m h h' then S0 else 0)‖ ≤ Bd := by
    intro h _ h' _
    by_cases hdiv : ((M : ℕ) : ℤ) ∣ m h h'
    · rw [if_pos hdiv]
      have : ∑ n ∈ S, F n * eA (n * ((m h h' : ℝ) / (M : ℝ))) = S0 := by
        refine Finset.sum_congr rfl fun n _ => ?_
        obtain ⟨k, hk⟩ := hdiv
        have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hMpos.ne'
        have : (n : ℝ) * ((m h h' : ℝ) / (M : ℝ)) = ((n * k : ℤ) : ℝ) := by
          rw [hk]; push_cast; field_simp
        rw [this, eA_int, mul_one]
      rw [this, sub_self, norm_zero]; exact hBd0
    · rw [if_neg hdiv, sub_zero]
      exact sum_smooth_eA_rat_le hF hM ha hab hsupp S hS hMpos hdiv
  refine (norm_sum_le _ _).trans ?_
  calc ∑ h ∈ reduced r, ‖∑ h' ∈ reduced r', ((∑ n ∈ S, F n * eA (n * ((m h h' : ℝ) / (M : ℝ)))) -
          (if ((M : ℕ) : ℤ) ∣ m h h' then S0 else 0))‖
      ≤ ∑ h ∈ reduced r, ∑ h' ∈ reduced r', Bd := by
        refine Finset.sum_le_sum fun h hh => (norm_sum_le _ _).trans ?_
        exact Finset.sum_le_sum fun h' hh' => hterm h hh h' hh'
    _ = Nat.totient r * Nat.totient r' * Bd := by
        simp only [Finset.sum_const, card_reduced, nsmul_eq_mul]; ring

end Families.Phase3.C
