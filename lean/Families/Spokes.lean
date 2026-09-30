/-
The finite combinatorial core of `prop:count` (`lemma-A.tex`), used by `lem:A` and `lem:C`:
the `SL₂(ℤ)` "spoke" change of variables around a rational `u/v`, gcd preservation, the
identity `b/q − u/v = k/(qv)`, the isolated point `k = 0`, and the Möbius step for `(m,k) = 1`.
-/
import Mathlib

open Finset
open scoped ArithmeticFunction.Moebius

namespace Families.Spokes

variable {u v u' v' : ℤ}

/-- The spoke map `(b,q) ↦ (k,m) = (vb − uq, −v'b + u'q)`. -/
def fwd (u v u' v' : ℤ) (p : ℤ × ℤ) : ℤ × ℤ := (v * p.1 - u * p.2, -v' * p.1 + u' * p.2)
/-- Its inverse `(k,m) ↦ (b,q) = (u'k + um, v'k + vm)`. -/
def bwd (u v u' v' : ℤ) (p : ℤ × ℤ) : ℤ × ℤ := (u' * p.1 + u * p.2, v' * p.1 + v * p.2)

/-- **`prop:count`, change of variables.** If `vu' − uv' = 1`, the spoke map is a bijection of `ℤ²`
(an element of `SL₂(ℤ)`) with inverse `(k,m) ↦ (u'k + um, v'k + vm)`. -/
def spokeEquiv (h : v * u' - u * v' = 1) : ℤ × ℤ ≃ ℤ × ℤ where
  toFun := fwd u v u' v'
  invFun := bwd u v u' v'
  left_inv p := by
    obtain ⟨b, q⟩ := p
    simp only [fwd, bwd, Prod.mk.injEq]
    exact ⟨by linear_combination b * h, by linear_combination q * h⟩
  right_inv p := by
    obtain ⟨k, m⟩ := p
    simp only [fwd, bwd, Prod.mk.injEq]
    exact ⟨by linear_combination k * h, by linear_combination m * h⟩

/-- The spoke map preserves `gcd`. -/
theorem gcd_fwd (h : v * u' - u * v' = 1) (b q : ℤ) :
    Int.gcd (v * b - u * q) (-v' * b + u' * q) = Int.gcd b q := by
  apply Nat.dvd_antisymm
  · -- gcd(k,m) divides b = u'k + um and q = v'k + vm
    set g : ℤ := (Int.gcd (v * b - u * q) (-v' * b + u' * q) : ℤ) with hg
    have hk : g ∣ v * b - u * q := Int.gcd_dvd_left _ _
    have hm : g ∣ -v' * b + u' * q := Int.gcd_dvd_right _ _
    have hb : g ∣ b := by
      have e : u' * (v * b - u * q) + u * (-v' * b + u' * q) = b := by linear_combination b * h
      have := dvd_add (hk.mul_left u') (hm.mul_left u)
      rwa [e] at this
    have hq : g ∣ q := by
      have e : v' * (v * b - u * q) + v * (-v' * b + u' * q) = q := by linear_combination q * h
      have := dvd_add (hk.mul_left v') (hm.mul_left v)
      rwa [e] at this
    exact Int.natCast_dvd_natCast.mp (Int.dvd_coe_gcd hb hq)
  · have hk : (Int.gcd b q : ℤ) ∣ v * b - u * q :=
      dvd_sub ((Int.gcd_dvd_left b q).mul_left v) ((Int.gcd_dvd_right b q).mul_left u)
    have hm : (Int.gcd b q : ℤ) ∣ -v' * b + u' * q :=
      dvd_add ((Int.gcd_dvd_left b q).mul_left (-v')) ((Int.gcd_dvd_right b q).mul_left u')
    exact Int.natCast_dvd_natCast.mp (Int.dvd_coe_gcd hk hm)

/-- `b/q − u/v = k/(qv)` with `k = vb − uq`. -/
theorem sub_eq_spoke (b q : ℤ) (hq : q ≠ 0) (hv : v ≠ 0) :
    (b : ℝ) / q - u / v = ((v * b - u * q : ℤ) : ℝ) / (q * v) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  push_cast
  field_simp

/-- The Farey pairs `𝒫 = {(b,q) : q ≥ 1, (b,q) = 1}` correspond under the spoke map to
`{(k,m) : (m,k) = 1, q := v'k + vm ≥ 1}` (`eqA:spokes`). -/
theorem mem_farey_iff (h : v * u' - u * v' = 1) (b q : ℤ) :
    (1 ≤ q ∧ Int.gcd b q = 1) ↔
      (1 ≤ v' * (fwd u v u' v' (b, q)).1 + v * (fwd u v u' v' (b, q)).2 ∧
        Int.gcd (fwd u v u' v' (b, q)).2 (fwd u v u' v' (b, q)).1 = 1) := by
  have hq : v' * (fwd u v u' v' (b, q)).1 + v * (fwd u v u' v' (b, q)).2 = q := by
    simp only [fwd]; linear_combination q * h
  rw [hq]
  simp only [fwd]
  rw [Int.gcd_comm (-v' * b + u' * q), gcd_fwd h b q]

/-- **The isolated point `k = 0`.** If `v ≥ 1`, a Farey pair `(b,q)` (`q ≥ 1`, `(b,q) = 1`) on the
spoke `k = vb − uq = 0` is `(u,v)`. -/
theorem isolated_point (h : v * u' - u * v' = 1) (hv : 1 ≤ v) (b q : ℤ) (hq : 1 ≤ q)
    (hbq : Int.gcd b q = 1) (hk : v * b - u * q = 0) : b = u ∧ q = v := by
  set m := -v' * b + u' * q with hm
  have hgcd := gcd_fwd h b q
  rw [hk, hbq, ← hm, Int.gcd_zero_left] at hgcd
  have hb : b = u * m := by
    have := congrArg Prod.fst ((spokeEquiv h).left_inv (b, q))
    simp only [spokeEquiv, fwd, bwd] at this
    rw [hk] at this; linarith
  have hq' : q = v * m := by
    have := congrArg Prod.snd ((spokeEquiv h).left_inv (b, q))
    simp only [spokeEquiv, fwd, bwd] at this
    rw [hk] at this; linarith
  have hm1 : m = 1 ∨ m = -1 := by
    rcases Int.natAbs_eq m with e | e <;> [left; right] <;> rw [e, hgcd] <;> simp
  rcases hm1 with e | e
  · exact ⟨by rw [hb, e, mul_one], by rw [hq', e, mul_one]⟩
  · exfalso; rw [hq', e] at hq; linarith

/-- **Möbius step** (`prop:count`, "by Möbius inversion over `d | k`"): for `k ≠ 0` and any finite
set `S ⊂ ℤ`, `∑_{m ∈ S, (m,k)=1} f(m) = ∑_{d | k} μ(d) ∑_{m ∈ S, d | m} f(m)`. -/
theorem sum_coprime_eq_moebius (k : ℤ) (hk : k ≠ 0) (S : Finset ℤ) (f : ℤ → ℝ) :
    ∑ m ∈ S.filter (fun m => Int.gcd m k = 1), f m =
      ∑ d ∈ k.natAbs.divisors, (μ d : ℝ) * ∑ m ∈ S.filter (fun m => (d : ℤ) ∣ m), f m := by
  -- ∑_{d | gcd(m,k)} μ(d) = [gcd(m,k) = 1]
  have key : ∀ m : ℤ, (if Int.gcd m k = 1 then (1 : ℝ) else 0) =
      ∑ d ∈ k.natAbs.divisors, if (d : ℤ) ∣ m then (μ d : ℝ) else 0 := by
    intro m
    have hg : Int.gcd m k ≠ 0 := by
      intro h0; exact hk (Int.gcd_eq_zero_iff.mp h0).2
    have h1 : (∑ d ∈ (Int.gcd m k).divisors, (μ d : ℝ)) = if Int.gcd m k = 1 then 1 else 0 := by
      have := congrArg (fun F : ArithmeticFunction ℤ => ((F (Int.gcd m k) : ℤ) : ℝ))
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
        refine ⟨⟨?_, Int.natAbs_ne_zero.mpr hk⟩, ?_⟩
        · exact (Nat.dvd_trans hd (Int.gcd_dvd_natAbs_right m k))
        · exact Int.dvd_trans (Int.natCast_dvd_natCast.mpr hd) (Int.gcd_dvd_left m k)
      · intro ⟨⟨hd, _⟩, hdm⟩
        refine ⟨?_, hg⟩
        have : (d : ℤ) ∣ k := Int.natCast_dvd.mpr hd
        exact Int.natCast_dvd_natCast.mp (Int.dvd_coe_gcd hdm this)
    · intro _ _; rfl
  calc ∑ m ∈ S.filter (fun m => Int.gcd m k = 1), f m
      = ∑ m ∈ S, (if Int.gcd m k = 1 then (1 : ℝ) else 0) * f m := by
        rw [Finset.sum_filter]; exact Finset.sum_congr rfl fun m _ => by split_ifs <;> simp
    _ = ∑ m ∈ S, ∑ d ∈ k.natAbs.divisors, (if (d : ℤ) ∣ m then (μ d : ℝ) else 0) * f m := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [key m, Finset.sum_mul]
    _ = ∑ d ∈ k.natAbs.divisors, (μ d : ℝ) * ∑ m ∈ S.filter (fun m => (d : ℤ) ∣ m), f m := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.mul_sum, Finset.sum_filter]
        exact Finset.sum_congr rfl fun m _ => by split_ifs <;> simp

/-- `∑_{d | k} μ(d)/d = φ(k)/k` (the density of the coprimality condition). -/
theorem sum_moebius_div (k : ℕ) (hk : k ≠ 0) :
    ∑ d ∈ k.divisors, (μ d : ℝ) / d = (Nat.totient k : ℝ) / k := by
  have hinv := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℝ)
    (f := fun n => (Nat.totient n : ℝ)) (g := fun n => (n : ℝ))).mp
    (fun n _ => by exact_mod_cast Nat.sum_totient n) k (Nat.pos_of_ne_zero hk)
  rw [Nat.sum_divisorsAntidiagonal (f := fun a b => (μ a : ℝ) * (b : ℝ))] at hinv
  rw [← hinv, Finset.sum_div]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdk : d ∣ k := Nat.dvd_of_mem_divisors hd
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  rw [Nat.cast_div hdk hd0]
  field_simp

end Families.Spokes
