/-
# The closed form of `c_S` (log-derivative of the Euler product of `g_S`)

`Lam_eq : ∑_d g_S(d) log d / d = −ℰ (c_S − γ)` (`lemma-toeplitz-C.tex`, proof of `lem:fS`(iii):
`c_S = γ − ℰ⁻¹∑_d g_S(d) log d/d = γ + A_S'(0)/A_S(0)`).

Proof (no complex analysis). Write `G(d) = g_S(d)/d` (`gdiv`) and `log d = ∑_p v_p(d) log p`. The double
series `∑_d ∑_p G(d) v_p(d) log p` converges absolutely (`|G(d)| log d ≤ 2|g_S(d)| d^{−1/2}`), so it may be
summed over `p` first. For a prime `p`, split `d` by `v_p(d) ∈ {0,1,2}` (`G(d) = 0` if `v_p(d) ≥ 3`):
`∑_{v_p(d)=e} G(d) = G(p^e) Z_p`, `Z_p = ∑_{p∤m} G(m)` (via the injection `m ↦ p^e m`). Hence
`ℰ = (1 + G(p) + G(p²)) Z_p = a_p Z_p` and `∑_d G(d) v_p(d) = (G(p) + 2G(p²)) Z_p`, so the `p`-th
column is `log p (G(p) + 2G(p²)) ℰ/a_p = −ℰ b_p/a_p`, `b_p = −(G(p)+2G(p²)) log p`,
`a_p = 1 − p⁻² − p⁻³`. Finally `∑_p b_p/a_p = c_S − γ` by the definitions of `cEmpty`, `cS`.
-/
import Families.Phase1.B.Bconst
import Families.Constants

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius
open ArithmeticFunction Finset

namespace Families.Phase1.B

open Families

/-! ### Preliminaries -/

lemma gdiv_eq_zero_of_three_le (S : Finset ℕ) {p d : ℕ} (hd : 3 ≤ d.factorization p) :
    gdiv S d = 0 := by
  have hd0 : d ≠ 0 := by rintro rfl; simp at hd
  unfold gdiv
  rw [gS_eq_locProd]
  have hpd : p ∈ d.primeFactors := by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff]; omega
  unfold locProd
  have h0 : (∏ q ∈ d.primeFactors, gloc S q (d.factorization q)) = 0 :=
    Finset.prod_eq_zero hpd (gloc_eq_zero S p hd)
  rw [h0, zero_div]

/-- `1 + G(p) + G(p²) = 1 − p⁻² − p⁻³`. -/
lemma gdiv_local_sum (S : Finset ℕ) {p : ℕ} (hp : p.Prime) :
    gdiv S 1 + gdiv S p + gdiv S (p ^ 2) = 1 - (p : ℝ) ^ (-2 : ℤ) - (p : ℝ) ^ (-3 : ℤ) := by
  rw [← euler_factor_gdiv S hp, tsum_prime_pow_three (fun e he => gdiv_prime_pow_eq_zero S hp he)]

lemma summable_gdiv (S : Finset ℕ) : Summable (gdiv S) := (summable_norm_gdiv S).of_norm

/-- `|G(d)| log d ≤ 2 |g_S(d)| d^{−1/2}`. -/
lemma abs_gdiv_mul_log_le (S : Finset ℕ) (d : ℕ) : |gdiv S d| * Real.log d ≤ 2 * gabs S d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [gdiv, gabs_nonneg]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hlog := Real.log_le_rpow_div hd0.le (show (0 : ℝ) < 1 / 2 by norm_num)
  unfold gabs gdiv
  rw [abs_div, abs_of_pos hd0]
  have hsq : (d : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) / d = 2 * (d : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [show -(1 / 2 : ℝ) = 1 / 2 - 1 by norm_num, Real.rpow_sub_one hd0.ne']
    ring
  calc |gS S d| / d * Real.log d ≤ |gS S d| / d * ((d : ℝ) ^ (1 / 2 : ℝ) / (1 / 2)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = |gS S d| * ((d : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) / d) := by ring
    _ = 2 * (|gS S d| * (d : ℝ) ^ (-(1 / 2 : ℝ))) := by rw [hsq]; ring

lemma summable_gdiv_mul_log (S : Finset ℕ) : Summable fun d => gdiv S d * Real.log d := by
  refine Summable.of_norm_bounded ((summable_gabs S).mul_left 2) fun d => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.log_natCast_nonneg d)]
  exact abs_gdiv_mul_log_le S d

/-! ### Splitting by `v_p(d)` -/

section prime

variable (S : Finset ℕ) {p : ℕ} (hp : p.Prime)
include hp

/-- `∑_{v_p(d) = e} G(d) = G(p^e) Z_p`. -/
lemma tsum_gdiv_factorization_eq (e : ℕ) :
    ∑' d, (if d.factorization p = e then gdiv S d else 0) =
      gdiv S (p ^ e) * ∑' m, (if ¬ p ∣ m then gdiv S m else 0) := by
  rw [← tsum_mul_left]
  have hinj : Function.Injective (fun m : ℕ => p ^ e * m) :=
    fun a b h => Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos e) h
  rw [← hinj.tsum_eq]
  · refine tsum_congr fun m => ?_
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [gdiv]
    by_cases hpm : p ∣ m
    · rw [if_neg (not_not.mpr hpm), mul_zero, if_neg]
      rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm.ne', Finsupp.add_apply,
        hp.factorization_pow, Finsupp.single_eq_same]
      have : 1 ≤ m.factorization p := (hp.dvd_iff_one_le_factorization hm.ne').mp hpm
      omega
    · rw [if_pos hpm, if_pos, gdiv_mul S (Nat.Coprime.pow_left e
        ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm))]
      rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm.ne', Finsupp.add_apply,
        hp.factorization_pow, Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hpm,
        add_zero]
  · intro d hd
    rw [Function.mem_support] at hd
    have hv : d.factorization p = e := by by_contra h; exact hd (if_neg h)
    have hd0 : d ≠ 0 := by rintro rfl; simp [gdiv] at hd
    refine ⟨d / p ^ e, ?_⟩
    simp only
    rw [← hv]
    exact Nat.ordProj_mul_ordCompl_eq_self d p

omit hp in
lemma summable_ite_gdiv (P : ℕ → Prop) [DecidablePred P] :
    Summable fun d => if P d then gdiv S d else 0 := by
  refine Summable.of_norm_bounded (summable_norm_gdiv S) fun d => ?_
  split_ifs
  · exact le_rfl
  · simp

omit hp in
/-- `G(d) = ∑_{e ≤ 2} G(d)·[v_p(d) = e]`. -/
lemma gdiv_split (d : ℕ) : gdiv S d = (if d.factorization p = 0 then gdiv S d else 0) +
    (if d.factorization p = 1 then gdiv S d else 0) + (if d.factorization p = 2 then gdiv S d else 0) := by
  rcases Nat.lt_or_ge (d.factorization p) 3 with h | h
  · interval_cases h' : d.factorization p <;> simp
  · rw [gdiv_eq_zero_of_three_le S h]; simp

omit hp in
/-- `G(d) v_p(d) = G(d)[v_p(d)=1] + 2 G(d)[v_p(d)=2]`. -/
lemma gdiv_mul_fact (d : ℕ) : gdiv S d * d.factorization p =
    (if d.factorization p = 1 then gdiv S d else 0) + 2 * (if d.factorization p = 2 then gdiv S d else 0) := by
  rcases Nat.lt_or_ge (d.factorization p) 3 with h | h
  · interval_cases h' : d.factorization p <;> simp <;> ring
  · rw [gdiv_eq_zero_of_three_le S h]; simp

/-- `ℰ = a_p Z_p`. -/
lemma Ecal_eq_mul_Z :
    Ecal = (1 - (p : ℝ) ^ (-2 : ℤ) - (p : ℝ) ^ (-3 : ℤ)) * ∑' m, (if ¬ p ∣ m then gdiv S m else 0) := by
  rw [← (lemfS_ii_euler S).tsum_eq]
  have h : ∑' d, gS S d / d = ∑' d, gdiv S d := rfl
  rw [h, tsum_congr (gdiv_split S), Summable.tsum_add ((summable_ite_gdiv S _).add
    (summable_ite_gdiv S _)) (summable_ite_gdiv S _), Summable.tsum_add
    (summable_ite_gdiv S _) (summable_ite_gdiv S _), tsum_gdiv_factorization_eq S hp,
    tsum_gdiv_factorization_eq S hp, tsum_gdiv_factorization_eq S hp, ← gdiv_local_sum S hp]
  simp only [pow_zero, pow_one]
  ring

/-- `∑_d G(d) v_p(d) = (G(p) + 2G(p²)) Z_p`. -/
lemma tsum_gdiv_mul_fact :
    ∑' d, gdiv S d * d.factorization p =
      (gdiv S p + 2 * gdiv S (p ^ 2)) * ∑' m, (if ¬ p ∣ m then gdiv S m else 0) := by
  rw [tsum_congr (gdiv_mul_fact S), Summable.tsum_add (summable_ite_gdiv S _)
    ((summable_ite_gdiv S _).mul_left 2), tsum_mul_left, tsum_gdiv_factorization_eq S hp,
    tsum_gdiv_factorization_eq S hp]
  simp only [pow_one]
  ring

end prime

/-! ### The double series -/

/-- `F(d, p) = G(d) v_p(d) log p`. -/
def Fdp (S : Finset ℕ) (d p : ℕ) : ℝ := gdiv S d * ((d.factorization p : ℝ) * Real.log p)

lemma sum_fact_mul_log (d : ℕ) : ∑' p, (d.factorization p : ℝ) * Real.log p = Real.log d := by
  rw [Real.log_nat_eq_sum_factorization, Finsupp.sum,
    tsum_eq_sum (s := d.factorization.support) fun p hp => by
      rw [Finsupp.notMem_support_iff.mp hp]; simp]

lemma tsum_Fdp_row (S : Finset ℕ) (d : ℕ) : ∑' p, Fdp S d p = gdiv S d * Real.log d := by
  unfold Fdp
  rw [tsum_mul_left, sum_fact_mul_log]

lemma summable_Fdp_row (S : Finset ℕ) (d : ℕ) : Summable fun p => Fdp S d p :=
  summable_of_ne_finset_zero (s := d.factorization.support) fun p hp => by
    unfold Fdp; rw [Finsupp.notMem_support_iff.mp hp]; simp

lemma summable_Fdp (S : Finset ℕ) : Summable (Function.uncurry (Fdp S)) := by
  have hnn : 0 ≤ fun x : ℕ × ℕ => ‖Function.uncurry (Fdp S) x‖ := fun _ => norm_nonneg _
  refine Summable.of_norm ((summable_prod_of_nonneg hnn).mpr ⟨fun d => ?_, ?_⟩)
  · simp only [Function.uncurry_apply_pair]
    exact (summable_Fdp_row S d).norm
  · have h : ∀ d, ∑' p, ‖Function.uncurry (Fdp S) (d, p)‖ = |gdiv S d| * Real.log d := by
      intro d
      simp only [Function.uncurry_apply_pair, Fdp, Real.norm_eq_abs, abs_mul, Nat.abs_cast]
      rw [tsum_mul_left]
      have : ∀ p, (d.factorization p : ℝ) * |Real.log p| = (d.factorization p : ℝ) * Real.log p :=
        fun p => by rw [abs_of_nonneg (Real.log_natCast_nonneg p)]
      rw [tsum_congr this, sum_fact_mul_log]
    simp only [h]
    refine Summable.of_nonneg_of_le (fun d => mul_nonneg (abs_nonneg _)
      (Real.log_natCast_nonneg d)) (abs_gdiv_mul_log_le S) ((summable_gabs S).mul_left 2)

/-! ### The closed form -/

/-- `a_p = 1 − p⁻² − p⁻³`. -/
def aP (p : ℕ) : ℝ := 1 - (p : ℝ) ^ (-2 : ℤ) - (p : ℝ) ^ (-3 : ℤ)

lemma aP_pos {p : ℕ} (hp : 2 ≤ p) : 0 < aP p := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  unfold aP
  have h1 : (p : ℝ) ^ (-2 : ℤ) ≤ 1 / 4 := by
    rw [zpow_neg, zpow_ofNat, inv_le_comm₀ (by positivity) (by norm_num)]; nlinarith
  have h3 : (p : ℝ) ^ (-3 : ℤ) ≤ 1 / 8 := by
    rw [zpow_neg, zpow_ofNat, inv_le_comm₀ (by positivity) (by norm_num)]
    have := pow_le_pow_left₀ (by norm_num) h2 3
    norm_num at this ⊢; linarith
  linarith

/-- `b_p = −(G(p) + 2G(p²)) log p` (for primes `p`). -/
def bP (S : Finset ℕ) (p : ℕ) : ℝ := -(gloc S p 1 / p + 2 * (gloc S p 2 / (p : ℝ) ^ 2)) * Real.log p

/-- The `p`-th column: `∑_d F(d,p) = −ℰ b_p/a_p` for prime `p`, and `0` otherwise. -/
lemma tsum_Fdp_col (S : Finset ℕ) (p : ℕ) :
    ∑' d, Fdp S d p = if p.Prime then -Ecal * (bP S p / aP p) else 0 := by
  split_ifs with hp
  · have hZ : Ecal = aP p * ∑' m, (if ¬ p ∣ m then gdiv S m else 0) := Ecal_eq_mul_Z S hp
    have ha := (aP_pos hp.two_le).ne'
    unfold Fdp
    have e : ∀ d, gdiv S d * ((d.factorization p : ℝ) * Real.log p) =
        (gdiv S d * d.factorization p) * Real.log p := fun d => by ring
    rw [tsum_congr e, tsum_mul_right, tsum_gdiv_mul_fact S hp, gdiv_prime S hp, gdiv_prime_sq S hp,
      hZ]
    unfold bP
    field_simp
  · unfold Fdp
    have : ∀ d : ℕ, d.factorization p = 0 := fun d => Nat.factorization_eq_zero_of_not_prime d hp
    simp [this]

/-- The `b_p/a_p` series is summable over the primes. -/
lemma summable_bP_div_aP (S : Finset ℕ) :
    Summable fun p : ℕ => if p.Prime then bP S p / aP p else 0 := by
  have hcol := fun p => tsum_Fdp_col S p
  -- the columns are summable in `p` (Fubini)
  have hsc : Summable fun p => ∑' d, Fdp S d p := by
    have := (summable_Fdp S).prod_symm.prod
    simpa [Function.uncurry] using this
  have hE := Ecal_pos
  refine (hsc.mul_left (-Ecal⁻¹)).congr fun p => ?_
  rw [hcol]
  split_ifs
  · field_simp
  · simp

/-- **The log-derivative identity:** `∑_d g_S(d) log d/d = −ℰ ∑_p b_p/a_p`. -/
theorem Lam_eq_tsum (S : Finset ℕ) :
    ∑' d, gdiv S d * Real.log d = -Ecal * ∑' p : ℕ, (if p.Prime then bP S p / aP p else 0) := by
  have h1 : ∑' d, gdiv S d * Real.log d = ∑' d, ∑' p, Fdp S d p :=
    tsum_congr fun d => (tsum_Fdp_row S d).symm
  rw [h1, ← (summable_Fdp S).tsum_comm, tsum_congr (tsum_Fdp_col S), ← tsum_mul_left]
  refine tsum_congr fun p => ?_
  split_ifs <;> simp

/-! ### `∑_p b_p/a_p = c_S − γ` -/

lemma tsum_nat_ite_prime (f : ℕ → ℝ) :
    ∑' p : ℕ, (if p.Prime then f p else 0) = ∑' p : Nat.Primes, f p := by
  have := tsum_subtype {p : ℕ | p.Prime} f
  rw [show (∑' p : Nat.Primes, f p) = ∑' x : ({p : ℕ | p.Prime} : Set ℕ), f x from rfl, this]
  exact tsum_congr fun p => by simp [Set.indicator_apply]

/-- For prime `p`: `b_p^S/a_p = b_p^∅/a_p − [p ∈ S] log p/(p³(p−1)a_p)`. -/
lemma bP_div_aP_eq (S : Finset ℕ) {p : ℕ} (hp : p.Prime) :
    bP S p / aP p = bP ∅ p / aP p -
      (if p ∈ S then Real.log p / ((p : ℝ) ^ 3 * (p - 1) * aP p) else 0) := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have ha := (aP_pos hp.two_le).ne'
  unfold bP
  by_cases hS : p ∈ S
  · simp only [gloc, hS, if_true, Finset.notMem_empty, if_false, OfNat.ofNat_ne_one]
    field_simp
    ring
  · simp only [gloc, hS, if_false, Finset.notMem_empty, OfNat.ofNat_ne_one, sub_zero]

lemma bP_empty_div_aP (p : ℕ) (hp : p.Prime) :
    bP ∅ p / aP p = ((p : ℝ) ^ (-2 : ℤ) + (p : ℝ) ^ (-3 : ℤ)) * Real.log p /
      (1 - (p : ℝ) ^ (-2 : ℤ) - (p : ℝ) ^ (-3 : ℤ)) := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  unfold bP aP
  simp only [gloc, Finset.notMem_empty, if_false, if_true, OfNat.ofNat_ne_one, zpow_neg, zpow_ofNat]
  congr 1
  field_simp
  ring

/-- `∑_p b_p^S/a_p = c_S − γ`. -/
theorem tsum_bP_div_aP (S : Finset ℕ) :
    ∑' p : ℕ, (if p.Prime then bP S p / aP p else 0) = cS S - Real.eulerMascheroniConstant := by
  have hfin : Summable fun p : ℕ => if p.Prime ∧ p ∈ S then
      Real.log p / ((p : ℝ) ^ 3 * (p - 1) * aP p) else 0 :=
    summable_of_ne_finset_zero (s := S) fun p hp => by simp [hp]
  have hF : ∑' p : ℕ, (if p.Prime ∧ p ∈ S then Real.log p / ((p : ℝ) ^ 3 * (p - 1) * aP p) else 0)
      = ∑ p ∈ S.filter Nat.Prime, Real.log p / ((p : ℝ) ^ 3 * (p - 1) * aP p) := by
    rw [tsum_eq_sum (s := S) fun p hp => by simp [hp], Finset.sum_filter]
    exact Finset.sum_congr rfl fun p hp => by simp [hp]
  have hsplit : ∀ p : ℕ, (if p.Prime then bP S p / aP p else 0) =
      (if p.Prime then bP ∅ p / aP p else 0) -
        (if p.Prime ∧ p ∈ S then Real.log p / ((p : ℝ) ^ 3 * (p - 1) * aP p) else 0) := by
    intro p
    by_cases hp : p.Prime
    · rw [if_pos hp, if_pos hp, bP_div_aP_eq S hp]
      by_cases hS : p ∈ S
      · rw [if_pos hS, if_pos ⟨hp, hS⟩]
      · rw [if_neg hS, if_neg (fun h => hS h.2)]
    · rw [if_neg hp, if_neg hp, if_neg (fun h => hp h.1), sub_zero]
  rw [tsum_congr hsplit, Summable.tsum_sub (summable_bP_div_aP ∅) hfin, hF, tsum_nat_ite_prime]
  unfold cS cEmpty
  have e1 : ∑' p : Nat.Primes, bP ∅ p / aP p = ∑' p : Nat.Primes,
      (((p : ℕ) : ℝ) ^ (-2 : ℤ) + ((p : ℕ) : ℝ) ^ (-3 : ℤ)) * Real.log (p : ℕ) /
        (1 - ((p : ℕ) : ℝ) ^ (-2 : ℤ) - ((p : ℕ) : ℝ) ^ (-3 : ℤ)) :=
    tsum_congr fun p => bP_empty_div_aP p p.2
  rw [e1]
  unfold aP
  ring

/-- **The closed form of `c_S`:** `∑_d g_S(d) log d/d = −ℰ (c_S − γ)`. -/
theorem Lam_eq (S : Finset ℕ) :
    ∑' d, gdiv S d * Real.log d = -Ecal * (cS S - Real.eulerMascheroniConstant) := by
  rw [Lam_eq_tsum, tsum_bP_div_aP]

end Families.Phase1.B
