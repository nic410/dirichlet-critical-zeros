/-
# Montgomery 1969 density: mollifier coefficients and divisor sums

* `sum_beta_mul` — `∑_{n ≤ XN} β(n) F(n) = ∑_{d ≤ X} ∑_{m ≤ N} μ(d) F(dm)`.
* `beta_one`, `beta_eq_zero` (`β(n) = 0` for `2 ≤ n ≤ min(X,N)`), `abs_beta_le` (`|β(n)| ≤ d(n)`).
* `sum_card_divisors_sq_le` — `∑_{n ≤ Z} d(n)² n^{-1-η} ≤ (1 + 1/η)⁴` (via `d(n)² ≤ d₄(n)`).
-/
import Families.Hyp.Montgomery.Defs

noncomputable section

open scoped BigOperators ArithmeticFunction.Moebius
open ArithmeticFunction Finset

namespace Families.Hyp.Montgomery

theorem sum_beta_mul (X N : ℕ) (F : ℕ → ℂ) :
    ∑ n ∈ Finset.Icc 1 (X * N), (beta X N n : ℂ) * F n =
      ∑ d ∈ Finset.Icc 1 X, ∑ m ∈ Finset.Icc 1 N, (μ d : ℂ) * F (d * m) := by
  rw [← Finset.sum_product (s := Finset.Icc 1 X) (t := Finset.Icc 1 N)
    (f := fun p : ℕ × ℕ => (μ p.1 : ℂ) * F (p.1 * p.2))]
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.Icc 1 X ×ˢ Finset.Icc 1 N)
    (t := Finset.Icc 1 (X * N)) (g := fun p : ℕ × ℕ => p.1 * p.2)]
  swap
  · rintro ⟨d, m⟩ hp
    simp only [Finset.mem_product, Finset.mem_Icc] at hp ⊢
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),
      Nat.mul_le_mul hp.1.2 hp.2.2⟩
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  simp only [beta, Int.cast_sum, Finset.sum_mul]
  refine Finset.sum_bij' (fun d _ => (d, n / d)) (fun p _ => p.1) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdn, -⟩, hdX, hdN⟩ := hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn (by omega)
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    refine ⟨⟨⟨hd0, hdX⟩, ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hdn) hd0, hdN⟩⟩, ?_⟩
    exact Nat.mul_div_cancel' hdn
  · rintro ⟨d, m⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨hd1, hdX⟩, ⟨hm1, hmN⟩⟩, hdm⟩ := hp
    simp only [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨⟨m, hdm.symm⟩, by omega⟩, hdX, ?_⟩
    rw [← hdm, Nat.mul_div_cancel_left _ (by omega)]
    exact hmN
  · intro d _; rfl
  · rintro ⟨d, m⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
    obtain ⟨⟨⟨hd1, hdX⟩, ⟨hm1, hmN⟩⟩, hdm⟩ := hp
    simp only [Prod.mk.injEq, true_and]
    rw [← hdm, Nat.mul_div_cancel_left _ (by omega)]
  · intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    simp only [Nat.mul_div_cancel' hd.1.1]

theorem beta_one {X N : ℕ} (hX : 1 ≤ X) (hN : 1 ≤ N) : beta X N 1 = 1 := by
  unfold beta
  rw [Nat.divisors_one, Finset.filter_true_of_mem]
  · simp
  · intro d hd
    rw [Finset.mem_singleton] at hd
    subst hd
    exact ⟨hX, by simpa using hN⟩

theorem beta_eq_zero {X N n : ℕ} (hn : 2 ≤ n) (hnX : n ≤ X) (hnN : n ≤ N) : beta X N n = 0 := by
  unfold beta
  rw [Finset.filter_true_of_mem]
  · rw [← coe_mul_zeta_apply, moebius_mul_coe_zeta, one_apply_ne (by omega)]
  · intro d hd
    have hd' := Nat.mem_divisors.mp hd
    exact ⟨(Nat.divisor_le hd).trans hnX, (Nat.div_le_self n d).trans hnN⟩

theorem abs_beta_le (X N n : ℕ) : |(beta X N n : ℝ)| ≤ (n.divisors.card : ℝ) := by
  unfold beta
  push_cast
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ d ∈ n.divisors.filter (fun d => d ≤ X ∧ n / d ≤ N), |(μ d : ℝ)|
      ≤ ∑ d ∈ n.divisors.filter (fun d => d ≤ X ∧ n / d ≤ N), (1 : ℝ) := by
        refine Finset.sum_le_sum fun d _ => ?_
        exact_mod_cast abs_moebius_le_one
    _ = ((n.divisors.filter (fun d => d ≤ X ∧ n / d ≤ N)).card : ℝ) := by simp
    _ ≤ (n.divisors.card : ℝ) := by exact_mod_cast Finset.card_filter_le _ _


/-- Telescoping step: `(a+1)^{-1-η} ≤ (a^{-η} - (a+1)^{-η}) / η` for `a > 0`. -/
lemma mont_rpow_step {η : ℝ} (hη : 0 < η) {a : ℝ} (ha : 0 < a) :
    (a + 1) ^ (-(1 + η)) ≤ (a ^ (-η) - (a + 1) ^ (-η)) / η := by
  set b := a + 1 with hb
  have hb0 : 0 < b := by linarith
  have hlog : 1 / b ≤ Real.log b - Real.log a := by
    have h := Real.log_le_sub_one_of_pos (show 0 < a / b by positivity)
    rw [Real.log_div ha.ne' hb0.ne'] at h
    have h' : a / b - 1 = -(1 / b) := by field_simp; linarith
    linarith
  have hexp : a ^ (-η) = b ^ (-η) * Real.exp (η * (Real.log b - Real.log a)) := by
    rw [Real.rpow_def_of_pos ha, Real.rpow_def_of_pos hb0, ← Real.exp_add]
    congr 1; ring
  have h1 : 1 + η * (1 / b) ≤ Real.exp (η * (Real.log b - Real.log a)) := by
    have := Real.add_one_le_exp (η * (Real.log b - Real.log a))
    nlinarith
  have hbη : 0 < b ^ (-η) := Real.rpow_pos_of_pos hb0 _
  have hsplit : b ^ (-(1 + η)) = b ^ (-η) * (1 / b) := by
    rw [show -(1 + η) = -η + (-1) by ring, Real.rpow_add hb0, Real.rpow_neg_one, one_div]
  rw [hsplit, le_div_iff₀ hη, hexp]
  have := mul_le_mul_of_nonneg_left h1 hbη.le
  nlinarith

lemma mont_sum_rpow_le_aux {η : ℝ} (hη : 0 < η) (Z : ℕ) (hZ : 1 ≤ Z) :
    ∑ m ∈ Finset.Icc 1 Z, (m : ℝ) ^ (-(1 + η)) ≤ 1 + 1 / η - (Z : ℝ) ^ (-η) / η := by
  induction Z, hZ using Nat.le_induction with
  | base => simp
  | succ Z hZ ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have h := mont_rpow_step hη (a := (Z : ℝ)) (by exact_mod_cast hZ)
    push_cast
    have : ((Z : ℝ) ^ (-η) - ((Z : ℝ) + 1) ^ (-η)) / η
        = (Z : ℝ) ^ (-η) / η - ((Z : ℝ) + 1) ^ (-η) / η := by ring
    linarith

/-- `∑_{m ≤ Z} m^{-1-η} ≤ 1 + 1/η`. -/
lemma mont_sum_rpow_le {η : ℝ} (hη : 0 < η) (Z : ℕ) :
    ∑ m ∈ Finset.Icc 1 Z, (m : ℝ) ^ (-(1 + η)) ≤ 1 + 1 / η := by
  rcases Nat.eq_zero_or_pos Z with rfl | hZ
  · simp only [zero_lt_one, Finset.Icc_eq_empty_of_lt, Finset.sum_empty]; positivity
  · have := mont_sum_rpow_le_aux hη Z hZ
    have : 0 ≤ (Z : ℝ) ^ (-η) / η := by positivity
    linarith

/-- `gcd(d₁,d₂) · (d₁/g) · (d₂/g) · (n / lcm(d₁,d₂)) = n` for `d₁, d₂ ∣ n`. -/
lemma mont_gcd_prod (n d₁ d₂ : ℕ) (h₁ : d₁ ∣ n) (h₂ : d₂ ∣ n) :
    Nat.gcd d₁ d₂ * (d₁ / Nat.gcd d₁ d₂) * (d₂ / Nat.gcd d₁ d₂) * (n / Nat.lcm d₁ d₂) = n := by
  rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)]
  have : d₁ * (d₂ / Nat.gcd d₁ d₂) = Nat.lcm d₁ d₂ := by
    rw [Nat.lcm, Nat.mul_div_assoc _ (Nat.gcd_dvd_right _ _)]
  rw [this, Nat.mul_div_cancel' (Nat.lcm_dvd h₁ h₂)]

lemma mont_mem_Icc4 {a b c e n Z : ℕ} (h : a * b * c * e = n) (hn : 1 ≤ n) (hnZ : n ≤ Z) :
    (a, b, c, e) ∈ Finset.Icc 1 Z ×ˢ Finset.Icc 1 Z ×ˢ Finset.Icc 1 Z ×ˢ Finset.Icc 1 Z := by
  have hn0 : a * b * c * e ≠ 0 := by omega
  simp only [ne_eq, mul_eq_zero, not_or] at hn0
  obtain ⟨⟨⟨ha, hb⟩, hc⟩, he⟩ := hn0
  have hle : ∀ x, x ∣ n → x ≤ Z := fun x hx => (Nat.le_of_dvd (by omega) hx).trans hnZ
  simp only [Finset.mem_product, Finset.mem_Icc]
  refine ⟨⟨by omega, hle a ⟨b * c * e, by rw [← h]; ring⟩⟩, ⟨by omega, hle b ⟨a * c * e, by rw [← h]; ring⟩⟩,
    ⟨by omega, hle c ⟨a * b * e, by rw [← h]; ring⟩⟩, ⟨by omega, hle e ⟨a * b * c, by rw [← h]; ring⟩⟩⟩

/-- Proof: `(n, d₁, d₂) ↦ (g, d₁/g, d₂/g, n/lcm(d₁,d₂))`, `g = gcd(d₁,d₂)`, injects the pairs of
divisors of `n ≤ Z` into `[1,Z]⁴` with product `n`, so the sum is `≤ (∑_{m ≤ Z} m^{-1-η})⁴`. -/
theorem sum_card_divisors_sq_le (Z : ℕ) {η : ℝ} (hη : 0 < η) :
    ∑ n ∈ Finset.Icc 1 Z, ((n.divisors.card : ℝ)) ^ 2 * (n : ℝ) ^ (-(1 + η)) ≤ (1 + 1 / η) ^ 4 := by
  set f : ℕ → ℝ := fun m => (m : ℝ) ^ (-(1 + η)) with hf
  have hf0 : ∀ m, 0 ≤ f m := fun m => Real.rpow_nonneg (Nat.cast_nonneg m) _
  have hfmul : ∀ a b : ℕ, f (a * b) = f a * f b := by
    intro a b; simp only [hf, Nat.cast_mul]
    exact Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)
  set I := Finset.Icc 1 Z with hI
  set S := I.sigma (fun n => n.divisors ×ˢ n.divisors) with hS
  set F : ℕ × ℕ × ℕ × ℕ → ℝ := fun y => f y.1 * f y.2.1 * f y.2.2.1 * f y.2.2.2 with hF
  set φ : (Σ _ : ℕ, ℕ × ℕ) → ℕ × ℕ × ℕ × ℕ := fun x =>
    (Nat.gcd x.2.1 x.2.2, x.2.1 / Nat.gcd x.2.1 x.2.2, x.2.2 / Nat.gcd x.2.1 x.2.2,
      x.1 / Nat.lcm x.2.1 x.2.2) with hφ
  set ψ : ℕ × ℕ × ℕ × ℕ → (Σ _ : ℕ, ℕ × ℕ) := fun y =>
    ⟨y.1 * y.2.1 * y.2.2.1 * y.2.2.2, (y.1 * y.2.1, y.1 * y.2.2.1)⟩ with hψ
  have hmemS : ∀ x ∈ S, x.1 ∈ I ∧ x.2.1 ∣ x.1 ∧ x.2.2 ∣ x.1 := by
    rintro ⟨n, d₁, d₂⟩ hx
    simp only [hS, Finset.mem_sigma, Finset.mem_product, Nat.mem_divisors] at hx
    exact ⟨hx.1, hx.2.1.1, hx.2.2.1⟩
  have hprod : ∀ x ∈ S, (φ x).1 * (φ x).2.1 * (φ x).2.2.1 * (φ x).2.2.2 = x.1 := by
    intro x hx
    obtain ⟨-, h₁, h₂⟩ := hmemS x hx
    exact mont_gcd_prod x.1 x.2.1 x.2.2 h₁ h₂
  have hleft : ∀ x ∈ S, ψ (φ x) = x := by
    rintro ⟨n, d₁, d₂⟩ hx
    have hp := hprod _ hx
    simp only [hψ]
    rw [hp]
    simp only [hφ, Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _),
      Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)]
  have hinj : Set.InjOn φ S := by
    intro x hx y hy hxy
    have := congrArg ψ hxy
    rwa [hleft x hx, hleft y hy] at this
  have hmaps : ∀ x ∈ S, φ x ∈ I ×ˢ I ×ˢ I ×ˢ I := by
    intro x hx
    obtain ⟨hxI, -, -⟩ := hmemS x hx
    rw [hI, Finset.mem_Icc] at hxI
    exact mont_mem_Icc4 (hprod x hx) hxI.1 hxI.2
  have step1 : ∑ n ∈ I, ((n.divisors.card : ℝ)) ^ 2 * f n = ∑ x ∈ S, f x.1 := by
    rw [hS, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [Finset.sum_const, Finset.card_product, nsmul_eq_mul]
    push_cast; ring
  have step2 : ∑ x ∈ S, f x.1 = ∑ y ∈ S.image φ, F y := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [hF, ← hfmul]
    rw [hprod x hx]
  have step3 : ∑ y ∈ S.image φ, F y ≤ ∑ y ∈ I ×ˢ I ×ˢ I ×ˢ I, F y := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
      exact hmaps x hx
    · intro y _ _
      simp only [hF]
      have := hf0 y.1; have := hf0 y.2.1; have := hf0 y.2.2.1; have := hf0 y.2.2.2
      positivity
  have step4 : ∑ y ∈ I ×ˢ I ×ˢ I ×ˢ I, F y = (∑ m ∈ I, f m) ^ 4 := by
    simp only [hF, Finset.sum_product]
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    ring
  have hsum := mont_sum_rpow_le hη Z
  have hsum0 : 0 ≤ ∑ m ∈ I, f m := Finset.sum_nonneg fun m _ => hf0 m
  calc ∑ n ∈ I, ((n.divisors.card : ℝ)) ^ 2 * f n = ∑ y ∈ S.image φ, F y := by rw [step1, step2]
    _ ≤ (∑ m ∈ I, f m) ^ 4 := step3.trans step4.le
    _ ≤ (1 + 1 / η) ^ 4 := pow_le_pow_left₀ hsum0 hsum 4

end Families.Hyp.Montgomery
