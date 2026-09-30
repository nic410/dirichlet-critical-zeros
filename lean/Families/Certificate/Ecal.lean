/-
`C_G ≤ 1.2688` (used for `thm:gauss`: `p(C_G) ≥ p(1.2688) ≥ 0.885912`).

`C_G = 6/(π² ℰ)`, `ℰ = ∏_p (1 − p⁻² − p⁻³) = 0.4791453…`. We prove `ℰ ≥ (L/S)(1 − T)` with
* head: `L/S ≤ ∏_{p ≤ 50000} (1 − p⁻² − p⁻³)`, `L = EcalData.ecalL`, `S = 10^20`
  (kernel-checked integer loop, `Families.Certificate.EcalData`);
* tail: `∑_{p > 50000} −log(1 − p⁻² − p⁻³) ≤ T := (1001/1000)/(2·50000)`, from
  `−log(1−a) ≤ a/(1−a) ≤ (1001/1000)/(p²−1) = (1001/2000)(1/(p−1) − 1/(p+1))`, injecting the odd
  primes `p > 50000` into the telescoping sequence `j ↦ 1/(50000+2j) − 1/(50002+2j)`;
and `π > 3.141592`.
-/
import Families.Constants
import Families.Certificate.EcalData

noncomputable section

open Real Finset

namespace Families

open EcalData

/-- The Euler factor as a function on `ℕ`. -/
def ecalFactor (k : ℕ) : ℝ := 1 - (k : ℝ) ^ (-2 : ℤ) - (k : ℝ) ^ (-3 : ℤ)

lemma fE_eq (k : ℕ) (hk : 1 ≤ k) : ecalFactor k = ((k : ℝ) ^ 3 - k - 1) / (k : ℝ) ^ 3 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  unfold ecalFactor
  rw [zpow_neg, zpow_neg, zpow_ofNat, zpow_ofNat]
  field_simp

lemma fE_pos (k : ℕ) (hk : 2 ≤ k) : 0 < ecalFactor k := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  rw [fE_eq k (by omega)]
  apply div_pos _ (by positivity)
  have h1 : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have h2 : 4 * (k : ℝ) ≤ (k : ℝ) ^ 3 := by
    have : (k : ℝ) ^ 3 = k * (k : ℝ) ^ 2 := by ring
    rw [this]; nlinarith
  linarith

lemma fE_le_one (k : ℕ) : ecalFactor k ≤ 1 := by
  unfold ecalFactor
  have : 0 ≤ (k : ℝ) ^ (-2 : ℤ) := by positivity
  have : 0 ≤ (k : ℝ) ^ (-3 : ℤ) := by positivity
  linarith

/-! ### Soundness of the kernel loop -/

lemma witness_sound {k : ℕ} (h : witness k = true) : ¬ k.Prime := by
  unfold witness at h
  rw [List.any_eq_true] at h
  obtain ⟨d, -, hd⟩ := h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hd
  exact Nat.not_prime_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero hd.2) hd.1.1 hd.1.2

lemma step_le_mul {k : ℕ} (hk : 2 ≤ k) (L : ℕ) (hw : ¬ witness k = true) :
    (step k L : ℝ) ≤ L * ecalFactor k := by
  unfold step
  rw [if_neg hw]
  have hk3 : k + 1 ≤ k ^ 3 := by
    have e : k ^ 3 = k * (k * k) := by ring
    rw [e]; nlinarith [Nat.mul_le_mul hk hk]
  refine (Nat.cast_div_le).trans (le_of_eq ?_)
  rw [fE_eq k (by omega)]
  push_cast [Nat.sub_sub, Nat.cast_sub hk3]
  ring

lemma step_le {k : ℕ} (hk : 2 ≤ k) (L : ℕ) : (step k L : ℝ) ≤ L := by
  by_cases hw : witness k = true
  · unfold step; rw [if_pos hw]
  · refine (step_le_mul hk L hw).trans ?_
    have := fE_le_one k
    have : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    nlinarith

/-- The product with non-primes contributing `1`. -/
def headProd (k n : ℕ) : ℝ := ∏ j ∈ Finset.Ico k (k + n), if j.Prime then ecalFactor j else 1

lemma headProd_nonneg (k n : ℕ) (hk : 2 ≤ k) : 0 ≤ headProd k n := by
  unfold headProd
  refine Finset.prod_nonneg fun j hj => ?_
  have hj2 : 2 ≤ j := le_trans hk (Finset.mem_Ico.mp hj).1
  split_ifs
  · exact (fE_pos j hj2).le
  · exact zero_le_one

lemma headProd_succ (k n : ℕ) :
    headProd k (n + 1) = (if k.Prime then ecalFactor k else 1) * headProd (k + 1) n := by
  unfold headProd
  rw [show k + (n + 1) = k + 1 + n by omega, Finset.prod_eq_prod_Ico_succ_bot (by omega)]

theorem loopA_le (n : ℕ) : ∀ (k L : ℕ), 2 ≤ k → (loopA n k L : ℝ) ≤ L * headProd k n := by
  induction n with
  | zero =>
    intro k L _
    simp [loopA, headProd]
  | succ n ih =>
    intro k L hk
    have hR := headProd_nonneg (k + 1) n (by omega)
    have h1 := ih (k + 1) (step k L) (by omega)
    simp only [loopA]
    rw [headProd_succ]
    refine h1.trans ?_
    by_cases hw : witness k = true
    · have hnp := witness_sound hw
      rw [if_neg hnp, one_mul]
      exact mul_le_mul_of_nonneg_right (step_le hk L) hR
    · have hs := step_le_mul hk L hw
      split_ifs with hp
      · calc (step k L : ℝ) * headProd (k + 1) n ≤ (L * ecalFactor k) * headProd (k + 1) n :=
              mul_le_mul_of_nonneg_right hs hR
          _ = L * (ecalFactor k * headProd (k + 1) n) := by ring
      · rw [one_mul]
        exact mul_le_mul_of_nonneg_right (step_le hk L) hR

/-- Head bound: `L/S ≤ ∏_{p ≤ 50000} (1 − p⁻² − p⁻³)`. -/
theorem head_bound :
    (ecalL : ℝ) / 10 ^ 20 ≤ ∏ j ∈ (Finset.Ico 2 50001).filter Nat.Prime, ecalFactor j := by
  have h := loopA_le 49999 2 100000000000000000000 le_rfl
  rw [loopA_eq] at h
  have e : headProd 2 49999 = ∏ j ∈ (Finset.Ico 2 50001).filter Nat.Prime, ecalFactor j := by
    unfold headProd
    rw [Finset.prod_filter]
  rw [e] at h
  rw [div_le_iff₀ (by positivity)]
  push_cast at h
  linarith

/-! ### The tail -/

/-- `−log(1 − p⁻² − p⁻³) ≤ (1001/2000)(1/(p−1) − 1/(p+1))` for `p ≥ 1001`. -/
lemma neg_log_fE_le (p : ℕ) (hp : 1001 ≤ p) :
    -Real.log (ecalFactor p) ≤ 1001 / 2000 * (1 / ((p : ℝ) - 1) - 1 / ((p : ℝ) + 1)) := by
  have hp' : (1001 : ℝ) ≤ p := by exact_mod_cast hp
  have hpos := fE_pos p (by omega)
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  have hden : 0 < (p : ℝ) ^ 3 - p - 1 := by
    have h1 : (4 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
    have h2 : 4 * (p : ℝ) ≤ (p : ℝ) ^ 3 := by
      have : (p : ℝ) ^ 3 = p * (p : ℝ) ^ 2 := by ring
      rw [this]; nlinarith
    linarith
  have e1 : (ecalFactor p)⁻¹ = (p : ℝ) ^ 3 / ((p : ℝ) ^ 3 - p - 1) := by
    rw [fE_eq p (by omega), inv_div]
  have e2 : 1 / ((p : ℝ) - 1) - 1 / ((p : ℝ) + 1) = 2 / ((p : ℝ) ^ 2 - 1) := by
    have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
    have h2 : (p : ℝ) + 1 ≠ 0 := by linarith
    rw [div_sub_div _ _ h1 h2]
    congr 1 <;> ring
  rw [e2]
  have key : (p : ℝ) ^ 3 / ((p : ℝ) ^ 3 - p - 1) - 1 ≤ 1001 / 2000 * (2 / ((p : ℝ) ^ 2 - 1)) := by
    have hq : 0 < (p : ℝ) ^ 2 - 1 := by nlinarith
    rw [div_sub_one hden.ne', mul_div_assoc', div_le_div_iff₀ hden (by positivity)]
    nlinarith [sq_nonneg (p : ℝ), mul_pos hq hden]
  rw [e1] at hlog
  linarith

/-- The telescoping majorant `g(j) = (1001/2000)(1/(50000+2j) − 1/(50002+2j))`. -/
def gT (j : ℕ) : ℝ := 1001 / 2000 * (1 / ((50000 : ℝ) + 2 * j) - 1 / ((50000 : ℝ) + 2 * j + 2))

lemma gT_nonneg (j : ℕ) : 0 ≤ gT j := by
  unfold gT
  apply mul_nonneg (by norm_num)
  rw [sub_nonneg]
  apply one_div_le_one_div_of_le (by positivity) (by linarith)

lemma gT_sum_range (n : ℕ) : ∑ j ∈ Finset.range n, gT j ≤ 1001 / 2000 * (1 / 50000) := by
  have : ∑ j ∈ Finset.range n, gT j = 1001 / 2000 *
      ∑ j ∈ Finset.range n, ((fun i : ℕ => 1 / ((50000 : ℝ) + 2 * i)) j
        - (fun i : ℕ => 1 / ((50000 : ℝ) + 2 * i)) (j + 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold gT
    push_cast
    ring_nf
  rw [this, Finset.sum_range_sub']
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  simp only [Nat.cast_zero, mul_zero, add_zero]
  have : 0 ≤ 1 / ((50000 : ℝ) + 2 * n) := by positivity
  linarith

lemma gT_summable : Summable gT := summable_of_sum_range_le gT_nonneg gT_sum_range

lemma gT_tsum_le : ∑' j, gT j ≤ 1001 / 2000 * (1 / 50000) :=
  Real.tsum_le_of_sum_range_le gT_nonneg gT_sum_range

/-- The finite set of primes `≤ 50000`, as a `Finset Nat.Primes`. -/
def headSet : Finset Nat.Primes := (Finset.Ico 2 50001).subtype Nat.Prime

lemma mem_headSet (x : Nat.Primes) : x ∈ headSet ↔ (x : ℕ) ∈ Finset.Ico 2 50001 :=
  Finset.mem_subtype

lemma prod_headSet (g : ℕ → ℝ) :
    ∏ p ∈ headSet, g (p : ℕ) = ∏ j ∈ (Finset.Ico 2 50001).filter Nat.Prime, g j :=
  Finset.prod_subtype_eq_prod_filter g

lemma val_gt_of_notMem_headSet (x : Nat.Primes) (hx : x ∉ headSet) : 50000 < (x : ℕ) := by
  rw [mem_headSet, Finset.mem_Ico, not_and_or] at hx
  have h2 := x.2.two_le
  omega

lemma odd_val_of_notMem_headSet (x : Nat.Primes) (hx : x ∉ headSet) : (x : ℕ) % 2 = 1 := by
  have h := val_gt_of_notMem_headSet x hx
  rcases x.2.eq_two_or_odd with h2 | h2
  · omega
  · exact h2

/-- The injection of the tail primes into `ℕ`: `p ↦ (p − 50001)/2`. -/
def tailIdx (x : ↑((headSet : Set Nat.Primes)ᶜ)) : ℕ := ((x : Nat.Primes) - 50001) / 2

lemma tailIdx_spec (x : ↑((headSet : Set Nat.Primes)ᶜ)) :
    ((x : Nat.Primes) : ℕ) = 50001 + 2 * tailIdx x := by
  have hx : (x : Nat.Primes) ∉ headSet := x.2
  have h1 := val_gt_of_notMem_headSet _ hx
  have h2 := odd_val_of_notMem_headSet _ hx
  unfold tailIdx
  omega

lemma tailIdx_injective : Function.Injective tailIdx := by
  intro x y h
  have hx := tailIdx_spec x
  have hy := tailIdx_spec y
  rw [h] at hx
  exact Subtype.ext (Subtype.ext (hx.trans hy.symm))

theorem tail_bound :
    ∑' x : ↑((headSet : Set Nat.Primes)ᶜ), -Real.log (ecalFactor ((x : Nat.Primes) : ℕ))
      ≤ 1001 / 2000 * (1 / 50000) := by
  have hsum : Summable fun x : ↑((headSet : Set Nat.Primes)ᶜ) =>
      -Real.log (ecalFactor ((x : Nat.Primes) : ℕ)) :=
    (ecal_log_summable.neg).subtype (· ∈ ((headSet : Set Nat.Primes)ᶜ))
  refine (Summable.tsum_le_tsum_of_inj tailIdx tailIdx_injective (fun j _ => gT_nonneg j) ?_ hsum
    gT_summable).trans gT_tsum_le
  intro x
  have hspec := tailIdx_spec x
  have hbig : 1001 ≤ ((x : Nat.Primes) : ℕ) := by omega
  refine (neg_log_fE_le _ hbig).trans (le_of_eq ?_)
  unfold gT
  rw [hspec]
  push_cast
  ring_nf

/-! ### Assembly -/

theorem Ecal_ge : (ecalL : ℝ) / 10 ^ 20 * (1 - 1001 / 2000 * (1 / 50000)) ≤ Ecal := by
  have hsplit := ecal_log_summable.sum_add_tsum_compl (s := headSet)
  rw [Ecal_eq_exp, ← hsplit, Real.exp_add]
  change _ ≤ Real.exp (∑ p ∈ headSet, Real.log (ecalFactor (p : ℕ))) *
    Real.exp (∑' x : ↑((headSet : Set Nat.Primes)ᶜ), Real.log (ecalFactor ((x : Nat.Primes) : ℕ)))
  -- head
  have hhead : Real.exp (∑ p ∈ headSet, Real.log (ecalFactor (p : ℕ)))
      = ∏ j ∈ (Finset.Ico 2 50001).filter Nat.Prime, ecalFactor j := by
    rw [Real.exp_sum, prod_headSet (fun j => Real.exp (Real.log (ecalFactor j)))]
    refine Finset.prod_congr rfl fun j hj => ?_
    have hj2 : 2 ≤ j := (Finset.mem_Ico.mp (Finset.mem_filter.mp hj).1).1
    exact Real.exp_log (fE_pos j hj2)
  -- tail
  have htail : 1 - 1001 / 2000 * (1 / 50000) ≤
      Real.exp (∑' x : ↑((headSet : Set Nat.Primes)ᶜ), Real.log (ecalFactor ((x : Nat.Primes) : ℕ))) := by
    have h1 := tail_bound
    have h2 : ∑' x : ↑((headSet : Set Nat.Primes)ᶜ), Real.log (ecalFactor ((x : Nat.Primes) : ℕ)) =
        -∑' x : ↑((headSet : Set Nat.Primes)ᶜ), -Real.log (ecalFactor ((x : Nat.Primes) : ℕ)) := by
      rw [tsum_neg, neg_neg]
    rw [h2]
    have := Real.add_one_le_exp (-∑' x : ↑((headSet : Set Nat.Primes)ᶜ),
      -Real.log (ecalFactor ((x : Nat.Primes) : ℕ)))
    linarith
  rw [hhead]
  have hH := head_bound
  have hT : (0 : ℝ) ≤ 1 - 1001 / 2000 * (1 / 50000) := by norm_num
  calc (ecalL : ℝ) / 10 ^ 20 * (1 - 1001 / 2000 * (1 / 50000))
      ≤ (∏ j ∈ (Finset.Ico 2 50001).filter Nat.Prime, ecalFactor j) * (1 - 1001 / 2000 * (1 / 50000)) :=
        mul_le_mul_of_nonneg_right hH hT
    _ ≤ _ := mul_le_mul_of_nonneg_left htail
        (Finset.prod_nonneg fun j hj => (fE_pos j (Finset.mem_Ico.mp
          (Finset.mem_filter.mp hj).1).1).le)

/-- `ℰ ≥ 0.47914`. -/
theorem Ecal_ge_047914 : (0.47914 : ℝ) ≤ Ecal := by
  refine le_trans ?_ Ecal_ge
  unfold ecalL
  norm_num

/-- **`C_G ≤ 1.2688`.** -/
theorem CG_le_12688 : CG ≤ 1.2688 := by
  unfold CG
  have hE := Ecal_ge
  have hEpos := Ecal_pos
  have hpi := Real.pi_gt_d6
  have hpi2 : (3.141592 : ℝ) ^ 2 < Real.pi ^ 2 := by
    exact pow_lt_pow_left₀ hpi (by norm_num) (by norm_num)
  rw [div_le_iff₀ (by positivity)]
  have hnum : (6 : ℝ) ≤ 1.2688 * ((3.141592 : ℝ) ^ 2 *
      ((ecalL : ℝ) / 10 ^ 20 * (1 - 1001 / 2000 * (1 / 50000)))) := by
    unfold ecalL; norm_num
  have h1 : (3.141592 : ℝ) ^ 2 * ((ecalL : ℝ) / 10 ^ 20 * (1 - 1001 / 2000 * (1 / 50000)))
      ≤ Real.pi ^ 2 * Ecal := by
    have hL : 0 ≤ (ecalL : ℝ) / 10 ^ 20 * (1 - 1001 / 2000 * (1 / 50000)) := by
      unfold ecalL; norm_num
    calc (3.141592 : ℝ) ^ 2 * ((ecalL : ℝ) / 10 ^ 20 * (1 - 1001 / 2000 * (1 / 50000)))
        ≤ Real.pi ^ 2 * ((ecalL : ℝ) / 10 ^ 20 * (1 - 1001 / 2000 * (1 / 50000))) :=
          mul_le_mul_of_nonneg_right hpi2.le hL
      _ ≤ Real.pi ^ 2 * Ecal := mul_le_mul_of_nonneg_left hE (by positivity)
  linarith

end Families
