/-
Elementary facts about the Euler-product constants `ℰ = ∏_p (1 − p^{-2} − p^{-3})` and `C_G = 6/(π²ℰ)`:
`0 < ℰ ≤ (5/8)(23/27)`, hence `C_G > 1` (the sharper numerical value `C_G = 1.26877…` is not formalised).
-/
import Families.Basic

noncomputable section

open Real

namespace Families

/-- The Euler factor `1 − p^{-2} − p^{-3}` as `1 + g(p)`. -/
lemma ecal_factor (p : Nat.Primes) :
    (1 - ((p : ℕ) : ℝ) ^ (-2 : ℤ) - ((p : ℕ) : ℝ) ^ (-3 : ℤ)) =
      1 + (-(((p : ℕ) : ℝ) ^ (-2 : ℤ) + ((p : ℕ) : ℝ) ^ (-3 : ℤ))) := by ring

lemma ecal_g_summable :
    Summable fun p : Nat.Primes => -(((p : ℕ) : ℝ) ^ (-2 : ℤ) + ((p : ℕ) : ℝ) ^ (-3 : ℤ)) := by
  have h2 : Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-2 : ℝ) :=
    Nat.Primes.summable_rpow.mpr (by norm_num)
  have h3 : Summable fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-3 : ℝ) :=
    Nat.Primes.summable_rpow.mpr (by norm_num)
  refine (h2.add h3).neg.congr fun p => ?_
  have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
  simp only [neg_inj]
  rw [← Real.rpow_intCast, ← Real.rpow_intCast]
  norm_num

lemma ecal_factor_pos (p : Nat.Primes) :
    0 < 1 - ((p : ℕ) : ℝ) ^ (-2 : ℤ) - ((p : ℕ) : ℝ) ^ (-3 : ℤ) := by
  have hp : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.2.two_le
  have hp0 : (0 : ℝ) < (p : ℕ) := by linarith
  have h2 : ((p : ℕ) : ℝ) ^ (-2 : ℤ) ≤ 1 / 4 := by
    rw [zpow_neg, zpow_ofNat, one_div]
    exact inv_anti₀ (by norm_num) (by nlinarith)
  have h3 : ((p : ℕ) : ℝ) ^ (-3 : ℤ) ≤ 1 / 8 := by
    rw [zpow_neg, zpow_ofNat, one_div]
    have : (2 : ℝ) ^ 3 ≤ ((p : ℕ) : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hp 3
    exact inv_anti₀ (by norm_num) (by linarith)
  linarith

lemma ecal_log_summable :
    Summable fun p : Nat.Primes =>
      Real.log (1 - ((p : ℕ) : ℝ) ^ (-2 : ℤ) - ((p : ℕ) : ℝ) ^ (-3 : ℤ)) := by
  have := Real.summable_log_one_add_of_summable ecal_g_summable
  refine this.congr fun p => ?_
  rw [ecal_factor]

/-- `ℰ = exp(∑_p log(1 − p^{-2} − p^{-3}))`. -/
lemma Ecal_eq_exp :
    Ecal = Real.exp (∑' p : Nat.Primes,
      Real.log (1 - ((p : ℕ) : ℝ) ^ (-2 : ℤ) - ((p : ℕ) : ℝ) ^ (-3 : ℤ))) :=
  (Real.rexp_tsum_eq_tprod ecal_factor_pos ecal_log_summable).symm

/-- `ℰ > 0`. -/
theorem Ecal_pos : 0 < Ecal := by
  rw [Ecal_eq_exp]; exact Real.exp_pos _

/-- `ℰ ≤ (1 − 1/4 − 1/8)(1 − 1/9 − 1/27) = 115/216`. -/
theorem Ecal_le : Ecal ≤ 115 / 216 := by
  set F : Nat.Primes → ℝ := fun p =>
    Real.log (1 - ((p : ℕ) : ℝ) ^ (-2 : ℤ) - ((p : ℕ) : ℝ) ^ (-3 : ℤ)) with hF
  have hnonpos : ∀ p, F p ≤ 0 := fun p => by
    apply Real.log_nonpos (ecal_factor_pos p).le
    have : 0 ≤ ((p : ℕ) : ℝ) ^ (-2 : ℤ) := by positivity
    have : 0 ≤ ((p : ℕ) : ℝ) ^ (-3 : ℤ) := by positivity
    linarith
  have p2 : Nat.Prime 2 := Nat.prime_two
  have p3 : Nat.Prime 3 := Nat.prime_three
  set a2 : Nat.Primes := ⟨2, p2⟩
  set a3 : Nat.Primes := ⟨3, p3⟩
  have h23 : a2 ≠ a3 := by
    intro h; have := congrArg Subtype.val h; simp [a2, a3] at this
  set s : Finset Nat.Primes := {a2, a3} with hs
  have hle : ∑' p, F p ≤ ∑ p ∈ s, F p := by
    have h := Summable.sum_le_tsum s (fun p _ => neg_nonneg.mpr (hnonpos p)) ecal_log_summable.neg
    simp only [Finset.sum_neg_distrib, tsum_neg] at h
    linarith
  have hsum : ∑ p ∈ s, F p = Real.log (5 / 8) + Real.log (23 / 27) := by
    rw [hs, Finset.sum_pair h23]
    simp only [hF, a2, a3]
    norm_num
  rw [Ecal_eq_exp]
  calc Real.exp (∑' p, F p) ≤ Real.exp (Real.log (5 / 8) + Real.log (23 / 27)) :=
        Real.exp_le_exp.mpr (hsum ▸ hle)
    _ = 115 / 216 := by
        rw [Real.exp_add, Real.exp_log (by norm_num), Real.exp_log (by norm_num)]; norm_num

/-- `C_G > 0`. -/
theorem CG_pos : 0 < CG := by
  unfold CG; have := Ecal_pos; positivity

/-- `C_G > 1`. -/
theorem one_lt_CG : 1 < CG := by
  unfold CG
  have hE := Ecal_pos
  have hE' := Ecal_le
  have hpi : Real.pi ^ 2 < 10 := by
    have := Real.pi_lt_d2
    nlinarith [Real.pi_pos]
  rw [lt_div_iff₀ (by positivity)]
  nlinarith [Real.pi_pos]

end Families
