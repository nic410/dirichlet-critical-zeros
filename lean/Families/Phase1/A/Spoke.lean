/-
One spoke of the local count with a coprimality twist
(`lemma-toeplitz-C.tex`, proof of `lem:C`, "The measures `ν_r`: spokes with a coprimality twist";
the untwisted case `r = 1` is the spoke step of `prop:count`, `lemma-A.tex`).

For the spoke `k ≠ 0` around `u/v` (with `vu' − uv' = 1`), the Farey pairs `(b,q)` with
`(q,r) = 1` are `q = v'k + vm` with `(m,k) = 1` and `(v'k+vm, r) = 1`. We prove

  `|∑_{m : (m,k)=1, (v'k+vm,r)=1} F(v'k+vm) − (G_S(|k|,r)/v) ∫F| ≤ τ(|k|) τ(r) TV(F)`,

`S` the primes of `v`, for every `F` of bounded variation with compact support: vanishing rule at
the primes `p | (r,v,k)`, inclusion–exclusion over `d₁ | k`, `d₂ | r_k` (CRT: one residue class
modulo `d₁d₂`) and `eqA:APTV`. (The TeX states the error as `2^{ω(k)} 2^{ω(r)} TV`; we use
`τ ≥ 2^ω`, which is what the later summation over `k` uses anyway.)
-/
import Families.Phase1.A.Toolkit
import Families.Spokes

noncomputable section

open scoped BigOperators ENNReal ArithmeticFunction.Moebius
open Finset MeasureTheory Set

namespace Families.Phase1.A

open Families ArithmeticFunction

/-! ### Arithmetic helpers -/

/-- Möbius detection of coprimality: `1[(m,n)=1] = ∑_{d | n} μ(d) 1[d | m]` (`n ≠ 0`). -/
lemma moebius_indicator (n : ℤ) (hn : n ≠ 0) (m : ℤ) :
    (if Int.gcd m n = 1 then (1 : ℝ) else 0) =
      ∑ d ∈ n.natAbs.divisors, if (d : ℤ) ∣ m then (μ d : ℝ) else 0 := by
  have hg : Int.gcd m n ≠ 0 := by
    intro h0; exact hn (Int.gcd_eq_zero_iff.mp h0).2
  have h1 : (∑ d ∈ (Int.gcd m n).divisors, (μ d : ℝ)) = if Int.gcd m n = 1 then 1 else 0 := by
    have := congrArg (fun F : ArithmeticFunction ℤ => ((F (Int.gcd m n) : ℤ) : ℝ))
      ArithmeticFunction.moebius_mul_coe_zeta
    simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at this
    push_cast at this
    rw [this]
  rw [← h1, ← Finset.sum_filter]
  apply Finset.sum_congr
  · ext d
    simp only [Nat.mem_divisors, Finset.mem_filter]
    constructor
    · intro ⟨hd, _⟩
      refine ⟨⟨?_, Int.natAbs_ne_zero.mpr hn⟩, ?_⟩
      · exact (Nat.dvd_trans hd (Int.gcd_dvd_natAbs_right m n))
      · exact Int.dvd_trans (Int.natCast_dvd_natCast.mpr hd) (Int.gcd_dvd_left m n)
    · intro ⟨⟨hd, _⟩, hdm⟩
      refine ⟨?_, hg⟩
      have : (d : ℤ) ∣ n := Int.natCast_dvd.mpr hd
      exact Int.natCast_dvd_natCast.mp (Int.dvd_coe_gcd hdm this)
  · intro _ _; rfl

lemma int_gcd_eq_one_of_forall_prime {q : ℤ} {r : ℕ}
    (h : ∀ p : ℕ, p.Prime → p ∣ r → ¬ (p : ℤ) ∣ q) : Int.gcd q r = 1 := by
  rw [Int.gcd_eq_natAbs, Int.natAbs_natCast]
  exact Nat.coprime_of_dvd fun p hp h1 h2 => h p hp h2 (Int.natCast_dvd.mpr h1)

lemma not_dvd_of_int_gcd_eq_one {q : ℤ} {r : ℕ} (h : Int.gcd q r = 1) {p : ℕ} (hp : p.Prime)
    (hpr : p ∣ r) : ¬ (p : ℤ) ∣ q := by
  intro hpq
  have h1 : (p : ℤ) ∣ ((Int.gcd q r : ℕ) : ℤ) :=
    Int.dvd_coe_gcd hpq (Int.natCast_dvd_natCast.mpr hpr)
  rw [h] at h1
  have h2 : p ∣ 1 := by exact_mod_cast h1
  exact hp.one_lt.ne' (Nat.dvd_one.mp h2)

lemma not_dvd_both_of_int_gcd_eq_one {m k : ℤ} (h : Int.gcd m k = 1) {p : ℕ} (hp : p.Prime)
    (hpm : (p : ℤ) ∣ m) (hpk : (p : ℤ) ∣ k) : False := by
  have h1 : (p : ℤ) ∣ ((Int.gcd m k : ℕ) : ℤ) := Int.dvd_coe_gcd hpm hpk
  rw [h] at h1
  have h2 : p ∣ 1 := by exact_mod_cast h1
  exact hp.one_lt.ne' (Nat.dvd_one.mp h2)

/-- CRT for the spoke: if `(d₁,d₂) = 1` and `(d₂,v) = 1`, the `m` with `d₁ | m` and
`d₂ | v'k + vm` form one residue class modulo `d₁d₂`. -/
lemma crt_class (v : ℕ) (v' k : ℤ) {d1 d2 : ℕ} (h12 : Nat.Coprime d1 d2)
    (h2v : Nat.Coprime d2 v) :
    ∃ c : ℤ, ∀ m : ℤ, ((d1 : ℤ) ∣ m ∧ (d2 : ℤ) ∣ v' * k + v * m) ↔
      ((d1 * d2 : ℕ) : ℤ) ∣ m - c := by
  have hcop : IsCoprime ((v * d1 : ℕ) : ℤ) (d2 : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.mul_left h2v.symm h12
  obtain ⟨x, y, hxy⟩ := hcop
  push_cast at hxy
  have h12' : IsCoprime (d1 : ℤ) d2 := Nat.isCoprime_iff_coprime.mpr h12
  have h2v' : IsCoprime (d2 : ℤ) v := Nat.isCoprime_iff_coprime.mpr h2v
  refine ⟨d1 * (-(v' * k) * x), fun m => ?_⟩
  constructor
  · rintro ⟨h1, h2⟩
    push_cast
    apply h12'.mul_dvd
    · exact dvd_sub h1 (dvd_mul_right _ _)
    · have : (d2 : ℤ) ∣ v * (m - d1 * (-(v' * k) * x)) := by
        have e : (v : ℤ) * (m - d1 * (-(v' * k) * x)) = (v' * k + v * m) - d2 * (v' * k * y) := by
          linear_combination (v' * k) * hxy
        rw [e]; exact dvd_sub h2 (dvd_mul_right _ _)
      exact h2v'.dvd_of_dvd_mul_left this
  · rintro ⟨s, hs⟩
    push_cast at hs
    have hm : m = d1 * (-(v' * k) * x) + d1 * d2 * s := by linarith
    constructor
    · rw [hm]
      exact dvd_add (dvd_mul_right _ _) (by rw [mul_assoc]; exact dvd_mul_right _ _)
    · have e : v' * k + v * m = d2 * (v' * k * y + v * d1 * s) := by
        rw [hm]; linear_combination (-(v' * k)) * hxy
      rw [e]; exact dvd_mul_right _ _

/-- A function on `ℤ` that is nonzero only where `F(c₀ + vm) ≠ 0` (`F` compactly supported,
`v ≥ 1`) has finite support, hence is summable. -/
lemma summable_of_affine {F : ℝ → ℝ} {A B : ℝ} (hsupp : ∀ x, F x ≠ 0 → x ∈ Icc A B)
    (c0 : ℤ) {v : ℕ} (hv : 1 ≤ v) (g : ℤ → ℝ)
    (hg : ∀ m, g m ≠ 0 → F ((c0 + v * m : ℤ) : ℝ) ≠ 0) : Summable g := by
  refine summable_of_ne_finset_zero (s := Finset.Icc ⌊(A - c0) / v⌋ ⌈(B - c0) / v⌉) ?_
  intro m hm
  by_contra hgm
  obtain ⟨h1, h2⟩ := hsupp _ (hg m hgm)
  apply hm
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  push_cast at h1 h2
  rw [Finset.mem_Icc]
  constructor
  · refine Int.floor_le_iff.mpr ?_
    have : (A - c0) / v ≤ m := by rw [div_le_iff₀ hv']; linarith
    linarith
  · refine Int.le_ceil_iff.mpr ?_
    have : (m : ℝ) ≤ (B - c0) / v := by rw [le_div_iff₀ hv']; linarith
    linarith

/-! ### One spoke -/

/-- The spoke sum `∑_{m : (m,k)=1, (v'k+vm, r)=1} F(v'k + vm)`. -/
def spokeSum (F : ℝ → ℝ) (v : ℕ) (v' k : ℤ) (r : ℕ) : ℝ :=
  ∑' m : ℤ, if Int.gcd m k = 1 ∧ Int.gcd (v' * k + v * m) r = 1 then
    F ((v' * k + v * m : ℤ) : ℝ) else 0

/-- **One spoke with a coprimality twist.** For `F` of bounded variation vanishing off `[A,B]`,
`v ≥ 1`, `(v',v) = 1`, `k ≠ 0`, `r` squarefree:
`|∑_{(m,k)=1, (v'k+vm,r)=1} F(v'k+vm) − (G_S(|k|,r)/v)∫F| ≤ τ(|k|) τ(r) TV(F)`, `S` = primes of `v`. -/
theorem spoke_count {F : ℝ → ℝ} (hF : BoundedVariationOn F univ) {A B : ℝ}
    (hsupp : ∀ x, F x ≠ 0 → x ∈ Icc A B) {v : ℕ} (hv : 1 ≤ v) {v' : ℤ}
    (hvv' : Int.gcd v' v = 1) {k : ℤ} (hk : k ≠ 0) {r : ℕ} (hr : Squarefree r) :
    |spokeSum F v v' k r - GS v.primeFactors k.natAbs r / v * ∫ x, F x|
      ≤ (k.natAbs.divisors.card : ℝ) * (r.divisors.card : ℝ) * (eVariationOn F univ).toReal := by
  have hV0 : 0 ≤ (eVariationOn F univ).toReal := ENNReal.toReal_nonneg
  have hv0 : v ≠ 0 := by omega
  by_cases hA : ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ p ∣ v ∧ (p : ℤ) ∣ k
  · -- the vanishing rule: `p | (r, v, k)` kills the whole spoke
    obtain ⟨p, hp, hpr, hpv, hpk⟩ := hA
    have h0 : spokeSum F v v' k r = 0 := by
      unfold spokeSum
      refine (tsum_congr fun m => ?_).trans tsum_zero
      rw [if_neg]
      rintro ⟨-, h2⟩
      refine not_dvd_of_int_gcd_eq_one h2 hp hpr ?_
      exact dvd_add (dvd_mul_of_dvd_right hpk _)
        (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hpv) _)
    have hG : GS v.primeFactors k.natAbs r = 0 := by
      unfold GS
      rw [if_neg, mul_zero]
      push Not
      exact ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpv, hv0⟩, hp,
        Nat.dvd_gcd (Int.natCast_dvd.mp hpk) hpr⟩
    rw [h0, hG, zero_div, zero_mul, sub_zero, abs_zero]
    positivity
  push Not at hA
  -- `r_k` = product of the primes `p | r` with `p ∤ k`, `p ∤ v`
  set T := r.primeFactors.filter (fun p => ¬ p ∣ k.natAbs ∧ p ∉ v.primeFactors) with hT
  set rk := ∏ p ∈ T, p with hrk
  have hTprime : ∀ p ∈ T, p.Prime := fun p hp =>
    Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hTnv : ∀ p ∈ T, ¬ p ∣ v := fun p hp hpv =>
    (Finset.mem_filter.mp hp).2.2 (Nat.mem_primeFactors.mpr ⟨hTprime p hp, hpv, hv0⟩)
  have hTnk : ∀ p ∈ T, ¬ (p : ℤ) ∣ k := fun p hp hpk =>
    (Finset.mem_filter.mp hp).2.1 (Int.natCast_dvd.mp hpk)
  have hrk_dvd : rk ∣ r := by
    have := Finset.prod_dvd_prod_of_subset T r.primeFactors (fun p => p) (Finset.filter_subset _ _)
    rwa [Nat.prod_primeFactors_of_squarefree hr] at this
  have hrk_pos : 0 < rk := Finset.prod_pos fun p hp => (hTprime p hp).pos
  have hrk_cop_v : Nat.Coprime rk v :=
    Nat.Coprime.prod_left fun p hp => (Nat.Prime.coprime_iff_not_dvd (hTprime p hp)).mpr (hTnv p hp)
  have hrk_cop_k : Nat.Coprime rk k.natAbs :=
    Nat.Coprime.prod_left fun p hp => (Nat.Prime.coprime_iff_not_dvd (hTprime p hp)).mpr
      (fun h => hTnk p hp (Int.natCast_dvd.mpr h))
  -- the twist reduces to `(q, r_k) = 1` on the spoke
  have hkey : ∀ m : ℤ, Int.gcd m k = 1 →
      (Int.gcd (v' * k + v * m) r = 1 ↔ Int.gcd (v' * k + v * m) rk = 1) := by
    intro m hmk
    constructor
    · intro h
      rw [Int.gcd_eq_natAbs, Int.natAbs_natCast] at h ⊢
      exact Nat.Coprime.coprime_dvd_right hrk_dvd h
    · intro h
      refine int_gcd_eq_one_of_forall_prime fun p hp hpr hpq => ?_
      have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
      by_cases hpv : p ∣ v
      · have h1 : (p : ℤ) ∣ v' * k := by
          have := dvd_sub hpq (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hpv) m)
          simpa using this
        rcases hpZ.dvd_or_dvd h1 with h2 | h2
        · -- `p | v'` and `p | v` contradict `(v',v) = 1`
          exact not_dvd_of_int_gcd_eq_one hvv' hp hpv h2
        · exact hA p hp hpr hpv h2
      · by_cases hpk : (p : ℤ) ∣ k
        · have h1 : (p : ℤ) ∣ v * m := by
            have := dvd_sub hpq (dvd_mul_of_dvd_right hpk v')
            simpa using this
          rcases hpZ.dvd_or_dvd h1 with h2 | h2
          · exact hpv (Int.natCast_dvd_natCast.mp h2)
          · exact not_dvd_both_of_int_gcd_eq_one hmk hp h2 hpk
        · have hpT : p ∈ T := Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr
            ⟨hp, hpr, hr.ne_zero⟩, fun h => hpk (Int.natCast_dvd.mpr h),
            fun h => hpv (Nat.dvd_of_mem_primeFactors h)⟩
          exact not_dvd_of_int_gcd_eq_one h hp (Finset.dvd_prod_of_mem _ hpT) hpq
  -- notation
  set q : ℤ → ℤ := fun m => v' * k + v * m with hq
  set Ind : ℕ → ℕ → ℤ → ℝ := fun d1 d2 m =>
    if (d1 : ℤ) ∣ m ∧ (d2 : ℤ) ∣ q m then F (q m) else 0 with hInd
  set Dk := k.natAbs.divisors with hDk
  set Dr := rk.divisors with hDr
  have hrkZ : (rk : ℤ) ≠ 0 := by exact_mod_cast hrk_pos.ne'
  -- Step 1: expand the two coprimality conditions by Möbius
  have hexp : ∀ m : ℤ, (if Int.gcd m k = 1 ∧ Int.gcd (v' * k + v * m) r = 1 then
      F ((v' * k + v * m : ℤ) : ℝ) else 0) =
      ∑ d1 ∈ Dk, ∑ d2 ∈ Dr, ((μ d1 : ℝ) * μ d2) * Ind d1 d2 m := by
    intro m
    have e1 : (if Int.gcd m k = 1 ∧ Int.gcd (v' * k + v * m) r = 1 then
        F ((v' * k + v * m : ℤ) : ℝ) else 0) =
        (if Int.gcd m k = 1 then (1 : ℝ) else 0) * (if Int.gcd (q m) (rk : ℤ) = 1 then 1 else 0) *
          F (q m) := by
      by_cases h1 : Int.gcd m k = 1
      · rw [if_pos h1, one_mul]
        by_cases h2 : Int.gcd (v' * k + v * m) r = 1
        · rw [if_pos ⟨h1, h2⟩, if_pos ((hkey m h1).mp h2), one_mul]
        · rw [if_neg (fun h => h2 h.2), if_neg (fun h => h2 ((hkey m h1).mpr h)), zero_mul]
      · rw [if_neg (fun h => h1 h.1), if_neg h1, zero_mul, zero_mul]
    rw [e1, moebius_indicator k hk m, moebius_indicator (rk : ℤ) hrkZ (q m), Int.natAbs_natCast,
      Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d1 _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun d2 _ => ?_
    simp only [hInd]
    by_cases h1 : (d1 : ℤ) ∣ m <;> by_cases h2 : (d2 : ℤ) ∣ q m <;> simp [h1, h2]
  -- summability of the pieces
  have hsumm : ∀ (d1 d2 : ℕ) (c : ℝ), Summable (fun m => c * Ind d1 d2 m) := by
    intro d1 d2 c
    refine summable_of_affine hsupp (v' * k) hv _ fun m hm => ?_
    simp only [hInd] at hm
    split_ifs at hm with h
    · exact right_ne_zero_of_mul hm
    · simp at hm
  have hspoke : spokeSum F v v' k r = ∑ d1 ∈ Dk, ∑ d2 ∈ Dr, ((μ d1 : ℝ) * μ d2) *
      ∑' m, Ind d1 d2 m := by
    unfold spokeSum
    rw [tsum_congr hexp, Summable.tsum_finsetSum (fun d1 _ => summable_sum fun d2 _ =>
      hsumm d1 d2 _)]
    refine Finset.sum_congr rfl fun d1 _ => ?_
    rw [Summable.tsum_finsetSum (fun d2 _ => hsumm d1 d2 _)]
    refine Finset.sum_congr rfl fun d2 _ => ?_
    rw [tsum_mul_left]
  -- Step 2: each inner sum is an arithmetic progression; `eqA:APTV`
  have hinner : ∀ d1 ∈ Dk, ∀ d2 ∈ Dr,
      |∑' m, Ind d1 d2 m - ((v : ℝ) * d1 * d2)⁻¹ * ∫ x, F x| ≤ (eVariationOn F univ).toReal := by
    intro d1 hd1 d2 hd2
    have hd1k : d1 ∣ k.natAbs := Nat.dvd_of_mem_divisors hd1
    have hd2rk : d2 ∣ rk := Nat.dvd_of_mem_divisors hd2
    have hd1pos : 0 < d1 := Nat.pos_of_mem_divisors hd1
    have hd2pos : 0 < d2 := Nat.pos_of_mem_divisors hd2
    have h12 : Nat.Coprime d1 d2 :=
      (Nat.Coprime.coprime_dvd_left hd2rk (Nat.Coprime.coprime_dvd_right hd1k hrk_cop_k)).symm
    have h2v : Nat.Coprime d2 v := Nat.Coprime.coprime_dvd_left hd2rk hrk_cop_v
    obtain ⟨c, hc⟩ := crt_class v v' k h12 h2v
    set D' : ℕ := d1 * d2 with hD'
    have hD'pos : 0 < D' := Nat.mul_pos hd1pos hd2pos
    set g : ℤ → ℤ := fun j => c + (D' : ℤ) * j with hg
    have hginj : Function.Injective g := fun a b hab => by
      simp only [hg] at hab
      have hD0 : (D' : ℤ) ≠ 0 := by exact_mod_cast hD'pos.ne'
      exact mul_left_cancel₀ hD0 (by linarith)
    have hre : ∑' j, Ind d1 d2 (g j) = ∑' m, Ind d1 d2 m := by
      refine hginj.tsum_eq ?_
      intro m hm
      have hm' : (d1 : ℤ) ∣ m ∧ (d2 : ℤ) ∣ q m := by
        by_contra h
        exact hm (by simp only [hInd]; rw [if_neg h])
      obtain ⟨j, hj⟩ := (hc m).mp hm'
      exact ⟨j, by simp only [hg]; linarith⟩
    have hval : ∀ j, Ind d1 d2 (g j) =
        F (((v' * k + v * c : ℤ) : ℝ) + ((v * D' : ℕ) : ℝ) * (j : ℝ)) := by
      intro j
      have hcond : (d1 : ℤ) ∣ g j ∧ (d2 : ℤ) ∣ q (g j) := (hc (g j)).mpr ⟨j, by simp [hg]⟩
      simp only [hInd]
      rw [if_pos hcond]
      congr 1
      simp only [hq, hg]
      push_cast
      ring
    have hDpos : (0 : ℝ) < ((v * D' : ℕ) : ℝ) := by
      have : 0 < v * D' := Nat.mul_pos (by omega) hD'pos
      exact_mod_cast this
    obtain ⟨-, hb⟩ := aptv hF hsupp ((v' * k + v * c : ℤ) : ℝ) ((v * D' : ℕ) : ℝ) hDpos
    rw [← hre, tsum_congr hval]
    have e : ((v : ℝ) * d1 * d2)⁻¹ = ((v * D' : ℕ) : ℝ)⁻¹ := by
      rw [hD']; push_cast; ring
    rw [e]
    exact hb
  -- Step 3: the main term
  have hsum_d : ∀ n : ℕ, n ≠ 0 → ∑ d ∈ n.divisors, (μ d : ℝ) / d = (Nat.totient n : ℝ) / n :=
    fun n hn => Families.Spokes.sum_moebius_div n hn
  have hphi_rk : (Nat.totient rk : ℝ) / rk = ∏ p ∈ T, (1 - 1 / (p : ℝ)) := by
    have h1 := Nat.totient_mul_prod_primeFactors rk
    rw [hrk, Nat.primeFactors_prod hTprime] at h1
    rw [← hrk] at h1
    have h2 : Nat.totient rk = ∏ p ∈ T, (p - 1) := by
      rw [mul_comm rk] at h1
      exact Nat.eq_of_mul_eq_mul_right hrk_pos h1
    rw [h2, hrk]
    push_cast [Nat.cast_prod]
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp1 : 1 ≤ p := (hTprime p hp).one_lt.le
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hTprime p hp).ne_zero
    rw [Nat.cast_sub hp1]
    field_simp
    push_cast
    ring
  have hGS : GS v.primeFactors k.natAbs r =
      (Nat.totient k.natAbs : ℝ) / k.natAbs * ((Nat.totient rk : ℝ) / rk) := by
    unfold GS
    rw [if_pos, mul_one, hphi_rk]
    intro p hpS hp hpg
    have hpv : p ∣ v := Nat.dvd_of_mem_primeFactors hpS
    exact hA p hp (Nat.dvd_trans hpg (Nat.gcd_dvd_right _ _)) hpv
      (Int.natCast_dvd.mpr (Nat.dvd_trans hpg (Nat.gcd_dvd_left _ _)))
  have hmain : GS v.primeFactors k.natAbs r / v * ∫ x, F x =
      ∑ d1 ∈ Dk, ∑ d2 ∈ Dr, ((μ d1 : ℝ) * μ d2) * (((v : ℝ) * d1 * d2)⁻¹ * ∫ x, F x) := by
    have hk0 : k.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hk
    rw [hGS, ← hsum_d _ hk0, ← hsum_d _ hrk_pos.ne', Finset.sum_mul_sum, div_eq_mul_inv,
      Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d1 _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d2 _ => ?_
    rw [mul_inv, mul_inv]
    ring
  -- Step 4: combine
  rw [hspoke, hmain, ← Finset.sum_sub_distrib]
  have hcardDr : (Dr.card : ℝ) ≤ r.divisors.card := by
    exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hr.ne_zero hrk_dvd)
  calc |∑ d1 ∈ Dk, (∑ d2 ∈ Dr, ((μ d1 : ℝ) * μ d2) * ∑' m, Ind d1 d2 m -
        ∑ d2 ∈ Dr, ((μ d1 : ℝ) * μ d2) * (((v : ℝ) * d1 * d2)⁻¹ * ∫ x, F x))|
      ≤ ∑ d1 ∈ Dk, |∑ d2 ∈ Dr, ((μ d1 : ℝ) * μ d2) * ∑' m, Ind d1 d2 m -
        ∑ d2 ∈ Dr, ((μ d1 : ℝ) * μ d2) * (((v : ℝ) * d1 * d2)⁻¹ * ∫ x, F x)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d1 ∈ Dk, ∑ d2 ∈ Dr, (eVariationOn F univ).toReal := by
        refine Finset.sum_le_sum fun d1 hd1 => ?_
        rw [← Finset.sum_sub_distrib]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun d2 hd2 => ?_)
        rw [← mul_sub, abs_mul]
        have hμ : |(μ d1 : ℝ) * μ d2| ≤ 1 := by
          rw [abs_mul]
          have a1 : |(μ d1 : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
          have a2 : |(μ d2 : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
          exact mul_le_one₀ a1 (abs_nonneg _) a2
        calc |(μ d1 : ℝ) * μ d2| * |∑' m, Ind d1 d2 m - ((v : ℝ) * d1 * d2)⁻¹ * ∫ x, F x|
            ≤ 1 * (eVariationOn F univ).toReal :=
              mul_le_mul hμ (hinner d1 hd1 d2 hd2) (abs_nonneg _) zero_le_one
          _ = _ := one_mul _
    _ = (Dk.card : ℝ) * Dr.card * (eVariationOn F univ).toReal := by
        rw [Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]; ring
    _ ≤ _ := by
        rw [hDk]
        gcongr

end Families.Phase1.A
