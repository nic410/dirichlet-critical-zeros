/-
`lem:toeplitz` (Lemma 6.13, the exact Toeplitz identity), `lemma-toeplitz-C.tex` §6.2,
and the character-orthogonality facts it rests on ([IK04, (3.9)]).
Also `lem:gauss` (the Gauss-sum transfer, `lemma-A.tex`).
-/
import Families.Basic

noncomputable section

open scoped BigOperators ComplexConjugate ArithmeticFunction.Moebius
open ArithmeticFunction Finset

namespace Families

/-! ### Orthogonality for primitive characters ([IK04, (3.9)]) -/

lemma mem_primChars {q : ℕ} {χ : DirichletCharacter ℂ q} : χ ∈ primChars q ↔ χ.IsPrimitive := by
  unfold primChars; simp

/-- Full orthogonality. -/
lemma sum_chars_mul_conj (d : ℕ) [NeZero d] (n m : ℤ) (hm : IsCoprime m d) :
    ∑ χ : DirichletCharacter ℂ d, χ n * conj (χ m) =
      if ((d : ℕ) : ℤ) ∣ n - m then (Nat.totient d : ℂ) else 0 := by
  set u := ZMod.unitOfIsCoprime m hm
  have hu : ((u : ZMod d)) = (m : ZMod d) := ZMod.coe_unitOfIsCoprime m hm
  have key : ∀ χ : DirichletCharacter ℂ d,
      χ n * conj (χ m) = χ (((u⁻¹ : (ZMod d)ˣ) : ZMod d) * (n : ZMod d)) := by
    intro χ
    have h1 : χ ((u⁻¹ : (ZMod d)ˣ) : ZMod d) * χ (u : ZMod d) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have h2 : conj (χ m) = χ⁻¹ (m : ZMod d) := MulChar.star_apply' χ _
    rw [h2, MulChar.inv_apply_eq_inv', ← hu, map_mul, mul_comm]
    congr 1
    exact (eq_inv_of_mul_eq_one_left h1).symm
  simp_rw [key]
  rw [DirichletCharacter.sum_characters_eq ℂ]
  have : (((u⁻¹ : (ZMod d)ˣ) : ZMod d) * (n : ZMod d) = 1) ↔ ((d : ℕ) : ℤ) ∣ n - m := by
    rw [Units.inv_mul_eq_one, hu, eq_comm, ZMod.intCast_eq_intCast_iff_dvd_sub, dvd_sub_comm]
  simp only [this]

/-- Decomposition of all characters mod `d` by conductor. -/
lemma sum_chars_decomp (d : ℕ) [NeZero d] (n m : ℤ) (hn : IsCoprime n d) (hm : IsCoprime m d) :
    ∑ χ : DirichletCharacter ℂ d, χ n * conj (χ m) =
      ∑ e ∈ d.divisors, ∑ ψ ∈ primChars e, ψ n * conj (ψ m) := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := d.divisors)
    (g := fun χ : DirichletCharacter ℂ d => χ.conductor)
    (fun χ _ => Nat.mem_divisors.mpr ⟨χ.conductor_dvd_level, NeZero.ne d⟩)]
  refine Finset.sum_congr rfl fun e he => ?_
  have hed : e ∣ d := Nat.dvd_of_mem_divisors he
  symm
  refine Finset.sum_bij (fun ψ _ => DirichletCharacter.changeLevel hed ψ) ?_ ?_ ?_ ?_
  · intro ψ hψ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [DirichletCharacter.conductor_changeLevel]
    exact mem_primChars.mp hψ
  · intro ψ₁ _ ψ₂ _ h
    exact DirichletCharacter.changeLevel_injective hed h
  · intro χ hχ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hχ
    have hF : χ.FactorsThrough e := hχ ▸ χ.factorsThrough_conductor
    obtain ⟨h, χ₀, hχ₀⟩ := hF
    refine ⟨χ₀, ?_, hχ₀.symm⟩
    rw [mem_primChars, DirichletCharacter.isPrimitive_def]
    have := DirichletCharacter.conductor_changeLevel χ₀ h
    rw [← hχ₀] at this
    rw [← this, hχ]
  · intro ψ _
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ hed hn,
      DirichletCharacter.changeLevel_eq_cast_of_dvd' ψ hed hm]

/-- `∑*_{χ mod q} χ(n) \bar χ(m) = ∑_{d | q, d | n-m} φ(d) μ(q/d)` for `(nm, q) = 1`
(equivalently `∑*_χ χ(a) = ∑_{d | (q, a-1)} φ(d) μ(q/d)` with `a ≡ n \bar m`). -/
theorem sum_primChars_eq (q : ℕ) (hq : 0 < q) (n m : ℤ) (hn : IsCoprime n q)
    (hm : IsCoprime m q) :
    ∑ χ ∈ primChars q, χ n * conj (χ m) =
      ∑ d ∈ q.divisors.filter (fun d : ℕ => ((d : ℕ) : ℤ) ∣ n - m),
        ((Nat.totient d : ℂ) * (μ (q / d) : ℂ)) := by
  set G : ℕ → ℂ := fun e => ∑ ψ ∈ primChars e, ψ n * conj (ψ m) with hG
  set F : ℕ → ℂ := fun d => if ((d : ℕ) : ℤ) ∣ n - m then (Nat.totient d : ℂ) else 0 with hF
  have hs : ∀ a b : ℕ, a ∣ b → b ∈ {d : ℕ | d ∣ q} → a ∈ {d : ℕ | d ∣ q} :=
    fun a b hab hb => dvd_trans hab hb
  have hsum : ∀ d > 0, d ∈ {d : ℕ | d ∣ q} → ∑ e ∈ d.divisors, G e = F d := by
    intro d hd hdq
    have : NeZero d := ⟨hd.ne'⟩
    have hdq' : ((d : ℕ) : ℤ) ∣ (q : ℤ) := Int.natCast_dvd_natCast.mpr hdq
    rw [← sum_chars_decomp d n m (hn.of_isCoprime_of_dvd_right hdq')
      (hm.of_isCoprime_of_dvd_right hdq'),
      sum_chars_mul_conj d n m (hm.of_isCoprime_of_dvd_right hdq')]
  have := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq_on {d : ℕ | d ∣ q} hs).mp hsum q hq
    (dvd_refl q)
  change G q = _
  rw [← this, Nat.sum_divisorsAntidiagonal' (f := fun a b => (μ a : ℂ) * F b), Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp only [hF]
  split_ifs <;> ring

/-- If `(nm, q) > 1` every character mod `q` kills `χ(n) \bar χ(m)`. -/
theorem sum_primChars_eq_zero_of_not_coprime (q : ℕ) (n m : ℤ) (h : ¬ IsCoprime (n * m) q) :
    ∑ χ ∈ primChars q, χ n * conj (χ m) = 0 := by
  refine Finset.sum_eq_zero fun χ _ => ?_
  rw [IsCoprime.mul_left_iff, not_and_or] at h
  rcases h with h | h
  · rw [(DirichletCharacter.apply_eq_zero_iff χ n).mpr h, zero_mul]
  · rw [(DirichletCharacter.apply_eq_zero_iff χ m).mpr h, _root_.map_zero, mul_zero]

/-- `φ*(q) = ∑_{d | q} φ(d) μ(q/d)`. -/
theorem phiStar_eq (q : ℕ) (hq : 0 < q) :
    (phiStar q : ℤ) = ∑ d ∈ q.divisors, (Nat.totient d : ℤ) * μ (q / d) := by
  have h := sum_primChars_eq q hq 1 1 isCoprime_one_left isCoprime_one_left
  simp only [Int.cast_one, map_one, mul_one, sub_self, dvd_zero, Finset.filter_true_of_mem,
    implies_true, Finset.sum_const, nsmul_eq_mul] at h
  have h2 : ((phiStar q : ℤ) : ℂ) = ((∑ d ∈ q.divisors, (Nat.totient d : ℤ) * μ (q / d) : ℤ) : ℂ) := by
    push_cast
    rw [← h]; simp [phiStar]
  exact_mod_cast h2

/-! ### Lemma 6.13 -/

lemma phiStar_eq_real (q : ℕ) (hq : 0 < q) :
    (phiStar q : ℝ) = ∑ d ∈ q.divisors, (Nat.totient d : ℝ) * (μ (q / d) : ℝ) := by
  have := congrArg (Int.cast : ℤ → ℝ) (phiStar_eq q hq)
  push_cast at this
  exact this

lemma phiStar_eq_complex (q : ℕ) (hq : 0 < q) :
    (phiStar q : ℂ) = ∑ d ∈ q.divisors, (Nat.totient d : ℂ) * (μ (q / d) : ℂ) := by
  have := congrArg (Int.cast : ℤ → ℂ) (phiStar_eq q hq)
  push_cast at this
  exact this

/-- General form of the family kernel (used in `lem:M2`):
`Δ(n,m) = ∑_q ω(q) 1[(nm,q)=1] ∑_{d | (q, n-m)} φ(d) μ(q/d)`. -/
theorem Δ_eq_general (W : Weight) (Q : ℝ) (n m : ℤ) :
    Δ W Q n m = ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (W.omega Q q : ℂ) *
      (if IsCoprime (n * m) q then
        ∑ d ∈ q.divisors.filter (fun d : ℕ => ((d : ℕ) : ℤ) ∣ n - m),
          ((Nat.totient d : ℂ) * (μ (q / d) : ℂ))
       else 0) := by
  unfold Δ
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq0 : 0 < q := (Finset.mem_Icc.mp hq).1
  split_ifs with h
  · rw [IsCoprime.mul_left_iff] at h
    rw [sum_primChars_eq q hq0 n m h.1 h.2]
  · rw [sum_primChars_eq_zero_of_not_coprime q n m h]

/-- The diagonal: `Δ(n,n) = ∑_q ω(q) φ*(q) 1[(n,q)=1]`. -/
theorem Δ_diag (W : Weight) (Q : ℝ) (n : ℤ) :
    Δ W Q n n = ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊,
      (W.omega Q q : ℂ) * (if IsCoprime n q then (phiStar q : ℂ) else 0) := by
  rw [Δ_eq_general]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq0 : 0 < q := (Finset.mem_Icc.mp hq).1
  congr 1
  by_cases h : IsCoprime n q
  · have h' : IsCoprime (n * n) q := IsCoprime.mul_left h h
    rw [if_pos h', if_pos h, phiStar_eq_complex q hq0]
    simp
  · have h' : ¬ IsCoprime (n * n) q := fun h' => h (IsCoprime.mul_left_iff.mp h').1
    rw [if_neg h', if_neg h]

/-- `k_ω` as a sum over moduli `q ≤ Q`. -/
lemma kω_eq_sum_q (W : Weight) (Q : ℝ) (h : ℤ) :
    kω W Q h = ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q *
      ∑ d ∈ q.divisors.filter (fun d : ℕ => ((d : ℕ) : ℤ) ∣ h),
        (Nat.totient d : ℝ) * (μ (q / d) : ℝ) := by
  set N := ⌊Q⌋₊
  have hswap : ∑ q ∈ Finset.Icc 1 N, W.omega Q q *
      ∑ d ∈ q.divisors.filter (fun d : ℕ => ((d : ℕ) : ℤ) ∣ h),
        (Nat.totient d : ℝ) * (μ (q / d) : ℝ)
      = ∑ d ∈ (Finset.Icc 1 N).filter (fun d : ℕ => ((d : ℕ) : ℤ) ∣ h),
          ∑ q ∈ (Finset.Icc 1 N).filter (fun q => d ∣ q),
            W.omega Q q * ((Nat.totient d : ℝ) * (μ (q / d) : ℝ)) := by
    simp_rw [Finset.mul_sum]
    refine Finset.sum_comm' ?_
    intro q d
    simp only [Finset.mem_Icc, Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hq1, hqN⟩, ⟨hdq, -⟩, hdh⟩
      exact ⟨⟨⟨hq1, hqN⟩, hdq⟩,
        ⟨⟨Nat.pos_of_dvd_of_pos hdq hq1, (Nat.le_of_dvd hq1 hdq).trans hqN⟩, hdh⟩⟩
    · rintro ⟨⟨⟨hq1, hqN⟩, hdq⟩, ⟨-, hdh⟩⟩
      exact ⟨⟨hq1, hqN⟩, ⟨hdq, by omega⟩, hdh⟩
  rw [hswap]
  unfold kω
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp (Finset.mem_filter.mp hd).1).1
  have hd0 : 0 < d := hd1
  rw [Finset.mul_sum]
  refine Finset.sum_nbij' (fun j => d * j) (fun q => q / d) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    have hj' := Finset.mem_Icc.mp hj
    simp only [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by nlinarith, ?_⟩, dvd_mul_right d j⟩
    have := (Nat.le_div_iff_mul_le hd0).mp hj'.2
    linarith [mul_comm d j]
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_Icc] at hq
    obtain ⟨⟨hq1, hqN⟩, hdq⟩ := hq
    simp only [Finset.mem_Icc]
    exact ⟨Nat.div_pos (Nat.le_of_dvd hq1 hdq) hd0, Nat.div_le_div_right hqN⟩
  · intro j _
    exact Nat.mul_div_cancel_left j hd0
  · intro q hq
    exact Nat.mul_div_cancel' (Finset.mem_filter.mp hq).2
  · intro j _
    rw [Nat.mul_div_cancel_left j hd0]
    ring

lemma isCoprime_of_rough {Q : ℝ} {n : ℤ} (hn : IsRough Q n) {q : ℕ}
    (hq : q ∈ Finset.Icc 1 ⌊Q⌋₊) : IsCoprime n q := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hg
  have hq' := Finset.mem_Icc.mp hq
  have hp := Nat.minFac_prime hg
  have hg_dvd_q : Int.gcd n q ∣ q := by
    have := Int.gcd_dvd_right (a := n) (b := (q : ℤ))
    exact_mod_cast this
  have hpq : Nat.minFac (Int.gcd n q) ∣ q := dvd_trans (Nat.minFac_dvd _) hg_dvd_q
  have hpn : ((Nat.minFac (Int.gcd n q) : ℕ) : ℤ) ∣ n :=
    dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.minFac_dvd _)) (Int.gcd_dvd_left n q)
  have h1 := hn.2 _ hp hpn
  have h2 : ((Nat.minFac (Int.gcd n q) : ℕ) : ℝ) ≤ Q := by
    have : (Nat.minFac (Int.gcd n q)) ≤ ⌊Q⌋₊ := (Nat.le_of_dvd (by omega) hpq).trans hq'.2
    have hQ : (0 : ℝ) ≤ Q := by
      by_contra hQ
      push Not at hQ
      have : ⌊Q⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      omega
    exact (Nat.cast_le.mpr this).trans (Nat.floor_le hQ)
  linarith

/-- **Lemma 6.13 (`lem:toeplitz`), first statement.** For `Q`-rough `n, m`: `Δ(n,m) = k_ω(n-m)`. -/
theorem toeplitz_identity (W : Weight) (Q : ℝ) {n m : ℤ} (hn : IsRough Q n) (hm : IsRough Q m) :
    Δ W Q n m = (kω W Q (n - m) : ℂ) := by
  rw [kω_eq_sum_q]
  unfold Δ
  push_cast
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [sum_primChars_eq q (Finset.mem_Icc.mp hq).1 n m (isCoprime_of_rough hn hq)
    (isCoprime_of_rough hm hq)]

/-- Consequence: on `Q`-rough integers the family kernel depends only on `n - m`. -/
theorem Δ_rough_shift_invariant (W : Weight) (Q : ℝ) {n m n' m' : ℤ}
    (hn : IsRough Q n) (hm : IsRough Q m) (hn' : IsRough Q n') (hm' : IsRough Q m')
    (h : n - m = n' - m') : Δ W Q n m = Δ W Q n' m' := by
  rw [toeplitz_identity W Q hn hm, toeplitz_identity W Q hn' hm', h]

/-- The family form is the Hermitian form of `Δ`: `x^*Δx = ∑_{n,m} x_n \bar x_m Δ(n,m)`. -/
theorem famForm_eq_sum (W : Weight) (Q : ℝ) (I : Finset ℤ) (x : ℤ → ℂ) :
    (famForm W Q I x : ℂ) = ∑ n ∈ I, ∑ m ∈ I, x n * conj (x m) * Δ W Q n m := by
  have hz : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  unfold famForm Δ
  push_cast
  simp_rw [← Complex.ofReal_pow, hz, map_sum, map_mul, Finset.sum_mul_sum, Finset.mul_sum]
  -- LHS: Σ_q Σ_χ Σ_n Σ_m ;  RHS: Σ_n Σ_m Σ_q Σ_χ
  calc _ = ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ n ∈ I, ∑ m ∈ I, ∑ χ ∈ primChars q,
        (W.omega Q q : ℂ) * (x n * χ n * (conj (x m) * conj (χ m))) := by
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [Finset.sum_comm]
    _ = ∑ n ∈ I, ∑ m ∈ I, ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ ∈ primChars q,
        (W.omega Q q : ℂ) * (x n * χ n * (conj (x m) * conj (χ m))) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [Finset.sum_comm]
    _ = _ := by
          refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
          refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun χ _ => ?_
          ring

/-- `k_ω(0) = H` (the total mass, `lem:toeplitz` last line). -/
theorem kω_zero (W : Weight) (Q : ℝ) : kω W Q 0 = W.H Q := by
  rw [kω_eq_sum_q]
  unfold Weight.H
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [phiStar_eq_real q (Finset.mem_Icc.mp hq).1]
  simp

/-! ### The Gauss-sum transfer (`lem:gauss`) -/

lemma card_reduced (q : ℕ) : (reduced q).card = Nat.totient q := by
  unfold reduced
  rw [Nat.totient_eq_card_coprime]
  congr 1
  ext c
  simp [Nat.coprime_comm]

lemma sum_units_eq_sum_reduced {M : Type*} [AddCommMonoid M] {q : ℕ} [NeZero q]
    (g : ZMod q → M) :
    ∑ b : ZMod q, (if IsUnit b then g b else 0) = ∑ c ∈ reduced q, g (c : ZMod q) := by
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun b => b.val) (fun c => (c : ZMod q)) ?_ ?_ ?_ ?_ ?_
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    simp only [reduced, Finset.mem_filter, Finset.mem_range]
    refine ⟨ZMod.val_lt b, ?_⟩
    rwa [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]
  · intro c hc
    simp only [reduced, Finset.mem_filter, Finset.mem_range] at hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (ZMod.isUnit_iff_coprime c q).mpr hc.2
  · intro b _; exact ZMod.natCast_zmod_val b
  · intro c hc
    simp only [reduced, Finset.mem_filter, Finset.mem_range] at hc
    exact ZMod.val_cast_of_lt hc.1
  · intro b _; simp

lemma norm_sq_char {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a : ZMod q) :
    ‖χ a‖ ^ 2 = if IsUnit a then 1 else 0 := by
  split_ifs with h
  · rw [show a = (h.unit : ZMod q) from h.unit_spec.symm, DirichletCharacter.unit_norm_eq_one]
    simp
  · rw [MulChar.map_nonunit χ h]; simp

lemma sum_norm_sq_char {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∑ a : ZMod q, ‖χ a‖ ^ 2 = Nat.totient q := by
  simp_rw [norm_sq_char]
  rw [sum_units_eq_sum_reduced (fun _ => (1 : ℝ)), Finset.sum_const, card_reduced]
  simp

lemma ofReal_norm_sq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma eA_eq_stdAddChar {q : ℕ} [NeZero q] (c : ℕ) (n : ℤ) :
    eA ((n : ℝ) * ((c : ℝ) / q)) = ZMod.stdAddChar ((n : ZMod q) * (c : ZMod q)) := by
  have : ((n : ZMod q) * (c : ZMod q)) = (((n : ℤ) * c : ℤ) : ZMod q) := by push_cast; ring
  rw [this, ZMod.stdAddChar_coe]
  unfold eA
  congr 1
  push_cast
  ring

/-- `χ(a) τ(\bar χ) = ∑_b \bar χ(b) e(ab/q)` for primitive `χ`. -/
lemma gauss_identity {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (a : ZMod q) :
    χ a * gaussSum χ⁻¹ (ZMod.stdAddChar (N := q)) =
      ∑ b : ZMod q, χ⁻¹ b * ZMod.stdAddChar (a * b) := by
  have hχ' : (χ⁻¹).IsPrimitive := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]; exact hχ
  have := gaussSum_mulShift_of_isPrimitive (ZMod.stdAddChar (N := q)) hχ' a
  rw [inv_inv] at this
  rw [← this]
  unfold gaussSum
  rfl

/-- `|τ(χ)|² = q` for primitive `χ mod q` (by Parseval). -/
lemma norm_sq_gaussSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) :
    ‖gaussSum χ⁻¹ (ZMod.stdAddChar (N := q))‖ ^ 2 = q := by
  set ψ := (ZMod.stdAddChar (N := q))
  set τ := gaussSum χ⁻¹ ψ
  have hφ : (0 : ℝ) < Nat.totient q := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have h1 : ∑ a : ZMod q, ‖χ a * τ‖ ^ 2 = Nat.totient q * ‖τ‖ ^ 2 := by
    simp_rw [norm_mul, mul_pow]
    rw [← Finset.sum_mul, sum_norm_sq_char]
  have hψ : ∀ a b c : ZMod q, ψ (a * b) * conj (ψ (a * c)) = ψ (a * (b - c)) := by
    intro a b c
    rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
    congr 1; ring
  have h2 : ((∑ a : ZMod q, ‖χ a * τ‖ ^ 2 : ℝ) : ℂ) = ((q * Nat.totient q : ℝ) : ℂ) := by
    push_cast
    have hg : ∀ a : ZMod q, χ a * τ = ∑ b : ZMod q, χ⁻¹ b * ψ (a * b) := gauss_identity χ hχ
    simp_rw [← Complex.ofReal_pow, ofReal_norm_sq, hg, map_sum, map_mul,
      Finset.sum_mul_sum]
    calc ∑ a : ZMod q, ∑ b : ZMod q, ∑ c : ZMod q,
          χ⁻¹ b * ψ (a * b) * (conj (χ⁻¹ c) * conj (ψ (a * c)))
        = ∑ b : ZMod q, ∑ c : ZMod q, χ⁻¹ b * conj (χ⁻¹ c) * ∑ a : ZMod q, ψ (a * (b - c)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← hψ]; ring
      _ = ∑ b : ZMod q, ∑ c : ZMod q, χ⁻¹ b * conj (χ⁻¹ c) *
            (if b - c = 0 then (Fintype.card (ZMod q) : ℂ) else 0) := by
          refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
          rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar q)]
          split_ifs <;> simp
      _ = ∑ b : ZMod q, χ⁻¹ b * conj (χ⁻¹ b) * (q : ℂ) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          simp_rw [sub_eq_zero, mul_ite, mul_zero]
          rw [Finset.sum_ite_eq]
          simp [ZMod.card]
      _ = _ := by
          rw [← Finset.sum_mul]
          simp_rw [← ofReal_norm_sq]
          rw [← Complex.ofReal_sum, sum_norm_sq_char]
          push_cast; ring
  have h3 : ∑ a : ZMod q, ‖χ a * τ‖ ^ 2 = q * Nat.totient q := by exact_mod_cast h2
  rw [h1] at h3
  have : (Nat.totient q : ℝ) * (‖τ‖ ^ 2 - q) = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · linarith
  · linarith

/-- Orthogonality of all characters mod `q`, in `ZMod q`. -/
lemma sum_chars_mul_conj_zmod {q : ℕ} [NeZero q] (b c : ZMod q) (hb : IsUnit b) :
    ∑ χ : DirichletCharacter ℂ q, χ c * conj (χ b) =
      if c = b then (Nat.totient q : ℂ) else 0 := by
  obtain ⟨u, rfl⟩ := hb
  have key : ∀ χ : DirichletCharacter ℂ q,
      χ c * conj (χ u) = χ (((u⁻¹ : (ZMod q)ˣ) : ZMod q) * c) := by
    intro χ
    have h1 : χ ((u⁻¹ : (ZMod q)ˣ) : ZMod q) * χ (u : ZMod q) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have h2 : conj (χ u) = χ⁻¹ (u : ZMod q) := MulChar.star_apply' χ _
    rw [h2, MulChar.inv_apply_eq_inv', map_mul, mul_comm]
    congr 1
    exact (eq_inv_of_mul_eq_one_left h1).symm
  simp_rw [key]
  rw [DirichletCharacter.sum_characters_eq ℂ]
  have : (((u⁻¹ : (ZMod q)ˣ) : ZMod q) * c = 1) ↔ c = u := by
    rw [Units.inv_mul_eq_one, eq_comm]
  simp only [this]

/-- Parseval over all characters mod `q`. -/
lemma sum_all_chars_norm_sq {q : ℕ} [NeZero q] (T : ZMod q → ℂ) :
    ∑ χ : DirichletCharacter ℂ q, ‖∑ b : ZMod q, χ⁻¹ b * T b‖ ^ 2 =
      Nat.totient q * ∑ b : ZMod q, (if IsUnit b then ‖T b‖ ^ 2 else 0) := by
  have hinv : ∀ (χ : DirichletCharacter ℂ q) (b : ZMod q), χ⁻¹ b = conj (χ b) :=
    fun χ b => (MulChar.star_apply' χ b).symm
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.ofReal_pow, ofReal_norm_sq, map_sum, map_mul, Finset.sum_mul_sum, hinv,
    Complex.conj_conj]
  calc ∑ χ : DirichletCharacter ℂ q, ∑ b : ZMod q, ∑ c : ZMod q,
        conj (χ b) * T b * (χ c * conj (T c))
      = ∑ b : ZMod q, ∑ c : ZMod q, T b * conj (T c) *
          ∑ χ : DirichletCharacter ℂ q, χ c * conj (χ b) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun χ _ => ?_
        ring
    _ = ∑ b : ZMod q, (if IsUnit b then T b * conj (T b) * (Nat.totient q : ℂ) else 0) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        split_ifs with hb
        · simp_rw [sum_chars_mul_conj_zmod b _ hb, mul_ite, mul_zero]
          rw [Finset.sum_ite_eq']
          simp
        · refine Finset.sum_eq_zero fun c _ => ?_
          have : ∀ χ : DirichletCharacter ℂ q, χ c * conj (χ b) = 0 := fun χ => by
            rw [MulChar.map_nonunit χ hb]; simp
          simp [this]
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        split_ifs
        · rw [← ofReal_norm_sq]; push_cast; ring
        · simp

/-- The per-modulus Gauss transfer:
`q ∑*_χ |∑ x_n χ(n)|² ≤ φ(q) ∑*_{b mod q} |S_x(b/q)|²`. -/
lemma gauss_per_q (q : ℕ) [NeZero q] (I : Finset ℤ) (x : ℤ → ℂ) :
    (q : ℝ) * ∑ χ ∈ primChars q, ‖∑ n ∈ I, x n * χ n‖ ^ 2 ≤
      Nat.totient q * ∑ c ∈ reduced q, ‖S I x ((c : ℝ) / q)‖ ^ 2 := by
  set ψ := (ZMod.stdAddChar (N := q))
  set T : ZMod q → ℂ := fun b => ∑ n ∈ I, x n * ψ ((n : ZMod q) * b) with hT
  have hprim : ∀ χ ∈ primChars q,
      (q : ℝ) * ‖∑ n ∈ I, x n * χ n‖ ^ 2 = ‖∑ b : ZMod q, χ⁻¹ b * T b‖ ^ 2 := by
    intro χ hχ
    have hχ' := mem_primChars.mp hχ
    rw [← norm_sq_gaussSum χ hχ', ← mul_pow, ← norm_mul, Finset.mul_sum]
    congr 2
    simp_rw [hT, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    have := gauss_identity χ hχ' (n : ZMod q)
    calc gaussSum χ⁻¹ ψ * (x n * χ (n : ZMod q))
        = x n * (χ (n : ZMod q) * gaussSum χ⁻¹ ψ) := by ring
      _ = x n * ∑ b : ZMod q, χ⁻¹ b * ψ ((n : ZMod q) * b) := by rw [this]
      _ = _ := by rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun b _ => ?_; ring
  rw [Finset.mul_sum, Finset.sum_congr rfl hprim]
  calc ∑ χ ∈ primChars q, ‖∑ b : ZMod q, χ⁻¹ b * T b‖ ^ 2
      ≤ ∑ χ : DirichletCharacter ℂ q, ‖∑ b : ZMod q, χ⁻¹ b * T b‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => sq_nonneg _)
    _ = Nat.totient q * ∑ b : ZMod q, (if IsUnit b then ‖T b‖ ^ 2 else 0) :=
        sum_all_chars_norm_sq T
    _ = Nat.totient q * ∑ c ∈ reduced q, ‖S I x ((c : ℝ) / q)‖ ^ 2 := by
        rw [sum_units_eq_sum_reduced (fun b => ‖T b‖ ^ 2)]
        congr 1
        refine Finset.sum_congr rfl fun c _ => ?_
        congr 2
        simp only [hT, S]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [eA_eq_stdAddChar]

/-- **`lem:gauss`.** `x^*Δx ≤ ∑_q w(q/Q) ∑*_{b mod q} |S_x(b/q)|²` for every finitely supported `x`. -/
theorem gauss_transfer (W : Weight) (Q : ℝ) (I : Finset ℤ) (x : ℤ → ℂ) :
    famForm W Q I x ≤ fareyForm W Q I x := by
  unfold famForm fareyForm
  refine Finset.sum_le_sum fun q hq => ?_
  have hq0 : 0 < q := (Finset.mem_Icc.mp hq).1
  have : NeZero q := ⟨hq0.ne'⟩
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq0
  have hw := W.nonneg ((q : ℝ) / Q)
  have key := gauss_per_q q I x
  unfold Weight.omega
  rw [mul_div_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hw
  rw [div_mul_eq_mul_div, div_le_iff₀ hφ]
  linarith

/-! ### Lemma 6.13 (ii)–(iv): Ramanujan expansion, `eqC:farey`, mass of `μ_Ω`

Ramanujan sums: `∑_{e|d} c_e(h) = d·1[d|h]`; the level algebra
`∑_{e|d|q} μ(q/d)φ(d)/d = (φ(e)/e)·μ(q/e)/(q/e)·1[(q/e) sqfree, (q/e,e)=1]`
(via the multiplicative functions `fE`, `gE`). -/

lemma eA_add (x y : ℝ) : eA (x + y) = eA x * eA y := by
  unfold eA; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma conj_eA (x : ℝ) : conj (eA x) = eA (-x) := by
  unfold eA; rw [← Complex.exp_conj]; congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]; push_cast; ring

lemma sum_range_eA (d : ℕ) (hd : 0 < d) (h : ℤ) :
    ∑ a ∈ Finset.range d, eA ((a : ℝ) * h / d) = if ((d : ℕ) : ℤ) ∣ h then (d : ℂ) else 0 := by
  have : NeZero d := ⟨hd.ne'⟩
  have h1 : ∀ a : ℕ, eA ((a : ℝ) * h / d) = ZMod.stdAddChar ((a : ZMod d) * (h : ZMod d)) := by
    intro a
    have : ((a : ZMod d) * (h : ZMod d)) = (((a : ℤ) * h : ℤ) : ZMod d) := by push_cast; ring
    rw [this, ZMod.stdAddChar_coe]; unfold eA; congr 1; push_cast; ring
  simp_rw [h1]
  have h2 : ∑ a ∈ Finset.range d, ZMod.stdAddChar ((a : ZMod d) * (h : ZMod d)) =
      ∑ x : ZMod d, ZMod.stdAddChar (x * (h : ZMod d)) := by
    refine Finset.sum_nbij' (fun a => (a : ZMod d)) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
    · intros; exact Finset.mem_univ _
    · intro x _; exact Finset.mem_range.mpr (ZMod.val_lt x)
    · intro a ha; exact ZMod.val_cast_of_lt (Finset.mem_range.mp ha)
    · intro x _; exact ZMod.natCast_zmod_val x
    · intros; rfl
  rw [h2, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar d)]
  simp only [ZMod.intCast_zmod_eq_zero_iff_dvd]
  split_ifs <;> simp [ZMod.card]

/-- `∑_{e | d} c_e(h) = d · 1[d | h]`. -/
lemma sum_divisors_ramanujan (d : ℕ) (hd : 0 < d) (h : ℤ) :
    ∑ e ∈ d.divisors, ramanujan e h = if ((d : ℕ) : ℤ) ∣ h then (d : ℂ) else 0 := by
  rw [← sum_range_eA d hd h]
  unfold ramanujan
  rw [Finset.sum_sigma']
  refine Finset.sum_nbij' (fun p => p.2 * (d / p.1))
    (fun a => (⟨d / Nat.gcd a d, a / Nat.gcd a d⟩ : (_ : ℕ) × ℕ)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨e, c⟩ hp
    simp only [Finset.mem_sigma, Nat.mem_divisors, reduced, Finset.mem_filter,
      Finset.mem_range] at hp
    obtain ⟨⟨hed, -⟩, hce, -⟩ := hp
    simp only [Finset.mem_range]
    have hk : e * (d / e) = d := Nat.mul_div_cancel' hed
    have hkpos : 0 < d / e := Nat.div_pos (Nat.le_of_dvd hd hed) (Nat.pos_of_dvd_of_pos hed hd)
    nlinarith
  · intro a ha
    have ha' := Finset.mem_range.mp ha
    have hg : 0 < Nat.gcd a d := Nat.gcd_pos_of_pos_right a hd
    simp only [Finset.mem_sigma, Nat.mem_divisors, reduced, Finset.mem_filter, Finset.mem_range]
    refine ⟨⟨Nat.div_dvd_of_dvd (Nat.gcd_dvd_right a d), hd.ne'⟩, ?_,
      Nat.coprime_div_gcd_div_gcd hg⟩
    exact Nat.div_lt_div_of_lt_of_dvd (Nat.gcd_dvd_right a d) ha'
  · rintro ⟨e, c⟩ hp
    simp only [Finset.mem_sigma, Nat.mem_divisors, reduced, Finset.mem_filter,
      Finset.mem_range] at hp
    obtain ⟨⟨hed, -⟩, -, hce⟩ := hp
    have hkpos : 0 < d / e := Nat.div_pos (Nat.le_of_dvd hd hed) (Nat.pos_of_dvd_of_pos hed hd)
    have hgcd : Nat.gcd (c * (d / e)) d = d / e := by
      have he0 : 0 < e := Nat.pos_of_dvd_of_pos hed hd
      obtain ⟨k, rfl⟩ := hed
      rw [Nat.mul_div_cancel_left k he0, Nat.gcd_mul_right, Nat.Coprime.gcd_eq_one hce, one_mul]
    simp only [hgcd]
    refine Sigma.ext ?_ (heq_of_eq ?_)
    · exact Nat.div_div_self hed hd.ne'
    · exact Nat.mul_div_cancel c hkpos
  · intro a ha
    simp only
    rw [Nat.div_div_self (Nat.gcd_dvd_right a d) hd.ne']
    exact Nat.div_mul_cancel (Nat.gcd_dvd_left a d)
  · rintro ⟨e, c⟩ hp
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hp
    have hed := hp.1.1
    have he : (e : ℝ) ≠ 0 := by
      have := Nat.pos_of_dvd_of_pos hed hd; positivity
    simp only
    congr 1
    rw [Nat.cast_mul, Nat.cast_div hed he]
    have hd' : (d : ℝ) ≠ 0 := by positivity
    field_simp

/-! ### The level-weight algebra: `∑_{e|d|q} μ(q/d) φ(d)/d` -/

/-- `f_e(t) = φ(et)/(t φ(e))`. -/
def fE (e : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun t => (Nat.totient (e * t) : ℝ) / (t * Nat.totient e), by simp⟩

lemma fE_apply (e t : ℕ) : fE e t = (Nat.totient (e * t) : ℝ) / (t * Nat.totient e) := rfl

/-- `g_e(s) = μ(s)/s · 1[(s,e)=1]`. -/
def gE (e : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun s => if Nat.Coprime s e then (μ s : ℝ) / s else 0, by simp⟩

lemma gE_apply (e s : ℕ) : gE e s = if Nat.Coprime s e then (μ s : ℝ) / s else 0 := rfl

lemma totient_mul_mul_eq (e m n : ℕ) (he : 0 < e) (hmn : m.Coprime n) :
    Nat.totient (e * m * n) * Nat.totient e = Nat.totient (e * m) * Nat.totient (e * n) := by
  have T1 := Nat.totient_gcd_mul_totient_mul (e * m) n
  have T2 := Nat.totient_gcd_mul_totient_mul e n
  have hg : Nat.gcd (e * m) n = Nat.gcd e n := Nat.Coprime.gcd_mul_right_cancel e hmn
  rw [hg] at T1
  have hpos : 0 < Nat.totient (Nat.gcd e n) := Nat.totient_pos.mpr (Nat.gcd_pos_of_pos_left n he)
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc Nat.totient (Nat.gcd e n) * (Nat.totient (e * m * n) * Nat.totient e)
      = (Nat.totient (Nat.gcd e n) * Nat.totient (e * m * n)) * Nat.totient e := by ring
    _ = (Nat.totient (e * m) * Nat.totient n * Nat.gcd e n) * Nat.totient e := by rw [T1]
    _ = Nat.totient (e * m) * (Nat.totient e * Nat.totient n * Nat.gcd e n) := by ring
    _ = Nat.totient (e * m) * (Nat.totient (Nat.gcd e n) * Nat.totient (e * n)) := by rw [T2]
    _ = _ := by ring

lemma fE_mult (e : ℕ) (he : 0 < e) : (fE e).IsMultiplicative := by
  have hφe : (0 : ℝ) < Nat.totient e := by exact_mod_cast Nat.totient_pos.mpr he
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨?_, ?_⟩
  · rw [fE_apply]; simp only [mul_one, Nat.cast_one, one_mul]; exact div_self hφe.ne'
  · intro m n hm hn hmn
    simp only [fE_apply]
    have key : (Nat.totient (e * (m * n)) : ℝ) * Nat.totient e =
        Nat.totient (e * m) * Nat.totient (e * n) := by
      rw [← mul_assoc]; exact_mod_cast totient_mul_mul_eq e m n he hmn
    have hm' : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
    have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
    push_cast
    linear_combination ((m : ℝ) * n * Nat.totient e) * key

lemma gE_mult (e : ℕ) : (gE e).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨?_, ?_⟩
  · simp [gE_apply]
  · intro m n hm hn hmn
    simp only [gE_apply, Nat.coprime_mul_iff_left]
    rw [isMultiplicative_moebius.map_mul_of_coprime hmn]
    split_ifs with h1 h2 h3 <;> simp_all
    · field_simp

lemma totient_mul_prime_pow_of_dvd (e p k : ℕ) (hp : p.Prime) (hpe : p ∣ e) :
    Nat.totient (e * p ^ k) = p ^ k * Nat.totient e := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mul_assoc, mul_comm (e * p ^ k) p,
      Nat.totient_mul_of_prime_of_dvd hp (dvd_mul_of_dvd_left hpe _), ih]
    ring

lemma moebius_mul_prime_pow (f : ArithmeticFunction ℝ) {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    (((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) * f) (p ^ k) =
      f (p ^ k) - f (p ^ (k - 1)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun x y => (((μ : ArithmeticFunction ℤ) :
      ArithmeticFunction ℝ) x) * f y), Nat.sum_divisors_prime_pow hp]
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have hz : ∀ i ∈ Finset.range j, (((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) (p ^ (i + 1 + 1))) *
      f (p ^ (j + 1) / p ^ (i + 1 + 1)) = 0 := by
    intro i _
    rw [ArithmeticFunction.intCoe_apply, moebius_apply_prime_pow hp (by omega)]
    simp
  rw [Finset.sum_eq_zero hz]
  rw [ArithmeticFunction.intCoe_apply, ArithmeticFunction.intCoe_apply, pow_zero,
    ArithmeticFunction.moebius_apply_one, zero_add, pow_one,
    show μ p = -1 from by simpa using moebius_apply_prime_pow hp one_ne_zero]
  rw [pow_succ, Nat.mul_div_cancel _ hp.pos, Nat.div_one]
  simp only [add_tsub_cancel_right]
  push_cast
  ring

lemma moebius_mul_fE (e : ℕ) (he : 0 < e) :
    (((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) * fE e) = gE e := by
  have hm : ((((μ : ArithmeticFunction ℤ) : ArithmeticFunction ℝ) * fE e)).IsMultiplicative :=
    isMultiplicative_moebius.intCast.mul (fE_mult e he)
  rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ hm _ (gE_mult e)]
  intro p i hp
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [hm.map_one, (gE_mult e).map_one]
  rw [moebius_mul_prime_pow _ hp hi]
  have hφe : (0 : ℝ) < Nat.totient e := by exact_mod_cast Nat.totient_pos.mpr he
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  by_cases hpe : p ∣ e
  · have h1 : ∀ k, fE e (p ^ k) = 1 := by
      intro k
      rw [fE_apply, totient_mul_prime_pow_of_dvd e p k hp hpe]
      push_cast
      field_simp
    rw [h1, h1, gE_apply, if_neg]
    · ring
    rw [Nat.coprime_pow_left_iff hi, Nat.Prime.coprime_iff_not_dvd hp]
    exact not_not.mpr hpe
  · have hcop : ∀ k, Nat.Coprime e (p ^ k) := fun k =>
      Nat.Coprime.pow_right k ((Nat.coprime_comm).mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpe))
    have h1 : ∀ k, 0 < k → fE e (p ^ k) = ((p : ℝ) - 1) / p := by
      intro k hk
      rw [fE_apply, Nat.totient_mul (hcop k), Nat.totient_prime_pow hp hk]
      rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_sub hp.one_lt.le, Nat.cast_pow]
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      simp only [add_tsub_cancel_right, Nat.cast_one]
      field_simp
      ring
    have hg : gE e (p ^ i) = if i = 1 then -1 / (p : ℝ) else 0 := by
      rw [gE_apply, if_pos ((Nat.coprime_pow_left_iff hi _ _).mpr
        ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpe)), moebius_apply_prime_pow hp hi.ne']
      split_ifs with h
      · subst h; simp
      · simp
    rw [hg, h1 i hi]
    split_ifs with h
    · subst h
      rw [show 1 - 1 = 0 from rfl, pow_zero, (fE_mult e he).map_one]
      field_simp
      ring
    · rw [h1 (i - 1) (by omega)]; ring

/-- `∑_{e | d | es} μ(es/d) φ(d)/d = (φ(e)/e) g_e(s)` (proof of `lem:toeplitz`(ii)). -/
lemma C_eval (e s : ℕ) (he : 0 < e) (hs : 0 < s) :
    ∑ d ∈ (e * s).divisors.filter (fun d => e ∣ d),
      (μ ((e * s) / d) : ℝ) * ((Nat.totient d : ℝ) / d) =
      ((Nat.totient e : ℝ) / e) * gE e s := by
  have hφe : (0 : ℝ) < Nat.totient e := by exact_mod_cast Nat.totient_pos.mpr he
  rw [← moebius_mul_fE e he, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal' (fun x y => (((μ : ArithmeticFunction ℤ) :
      ArithmeticFunction ℝ) x) * fE e y), Finset.mul_sum]
  symm
  refine Finset.sum_nbij' (fun t => e * t) (fun d => d / e) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    have ht' := Nat.mem_divisors.mp ht
    simp only [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨Nat.mul_dvd_mul_left e ht'.1, by positivity⟩, dvd_mul_right e t⟩
  · intro d hd
    simp only [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hds, -⟩, hed⟩ := hd
    obtain ⟨t, rfl⟩ := hed
    rw [Nat.mul_div_cancel_left t he]
    exact Nat.mem_divisors.mpr ⟨(Nat.mul_dvd_mul_iff_left he).mp hds, hs.ne'⟩
  · intro t _; exact Nat.mul_div_cancel_left t he
  · intro d hd
    exact Nat.mul_div_cancel' (Finset.mem_filter.mp hd).2
  · intro t ht
    have ht' := Nat.mem_divisors.mp ht
    have htpos : 0 < t := Nat.pos_of_dvd_of_pos ht'.1 hs
    rw [Nat.mul_div_mul_left s t he, ArithmeticFunction.intCoe_apply, fE_apply]
    push_cast
    field_simp

/-- Per-modulus Ramanujan expansion:
`∑_{d | (q,h)} φ(d) μ(q/d) = ∑_{e | q} c_e(h) (φ(e)/e) g_e(q/e)`. -/
lemma K_eq (q : ℕ) (hq : 0 < q) (h : ℤ) :
    ∑ d ∈ q.divisors.filter (fun d : ℕ => ((d : ℕ) : ℤ) ∣ h),
      (Nat.totient d : ℂ) * (μ (q / d) : ℂ) =
      ∑ e ∈ q.divisors, ramanujan e h * ((((Nat.totient e : ℝ) / e) * gE e (q / e) : ℝ) : ℂ) := by
  have step1 : ∑ d ∈ q.divisors.filter (fun d : ℕ => ((d : ℕ) : ℤ) ∣ h),
      (Nat.totient d : ℂ) * (μ (q / d) : ℂ)
      = ∑ d ∈ q.divisors, ∑ e ∈ d.divisors,
          (((μ (q / d) : ℝ) * ((Nat.totient d : ℝ) / d) : ℝ) : ℂ) * ramanujan e h := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    rw [← Finset.mul_sum, sum_divisors_ramanujan d hd0 h]
    have : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
    split_ifs
    · push_cast; field_simp
    · simp
  rw [step1, Finset.sum_comm' (t' := q.divisors)
    (s' := fun e => q.divisors.filter (fun d => e ∣ d))]
  · refine Finset.sum_congr rfl fun e he => ?_
    have he0 : 0 < e := Nat.pos_of_mem_divisors he
    obtain ⟨s, rfl⟩ := Nat.dvd_of_mem_divisors he
    have hs0 : 0 < s := Nat.pos_of_ne_zero (by rintro rfl; simp at hq)
    rw [← Finset.sum_mul, mul_comm, Nat.mul_div_cancel_left s he0, ← C_eval e s he0 hs0]
    push_cast
    rfl
  · intro d e
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hdq, hq0⟩, hed, hd0⟩
      exact ⟨⟨⟨hdq, hq0⟩, hed⟩, dvd_trans hed hdq, hq0⟩
    · rintro ⟨⟨⟨hdq, hq0⟩, hed⟩, -, -⟩
      exact ⟨⟨hdq, hq0⟩, hed, by rintro rfl; simp at hdq; omega⟩

lemma omega_eq_zero_of_gt (W : Weight) (Q : ℝ) {n : ℕ} (hn : ⌊Q⌋₊ < n) : W.omega Q n = 0 := by
  unfold Weight.omega
  have : W.w (n / Q) = 0 := by
    by_contra hw
    have hs := W.supp _ hw
    rcases le_or_gt Q 0 with hQ | hQ
    · have : (n : ℝ) / Q ≤ 0 := div_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hQ
      linarith [W.η_pos, hs.1]
    · have hnQ : Q < n := Nat.lt_of_floor_lt hn
      have : 1 < (n : ℝ) / Q := (one_lt_div hQ).mpr hnQ
      linarith [hs.2]
  rw [this]; simp

/-- `Ω(e) = (φ(e)/e) ∑_{r ≤ Q/e} ω(er) g_e(r)`. -/
lemma Ωlev_eq_gE (W : Weight) (Q : ℝ) (e : ℕ) (he : 0 < e) :
    Ωlev W Q e = (Nat.totient e : ℝ) / e *
      ∑ r ∈ Finset.Icc 1 (⌊Q⌋₊ / e), W.omega Q (e * r) * gE e r := by
  unfold Ωlev
  congr 1
  rw [Finset.sum_filter]
  symm
  rw [Finset.sum_subset (s₁ := Finset.Icc 1 (⌊Q⌋₊ / e)) (s₂ := Finset.Icc 1 ⌊Q⌋₊)]
  · refine Finset.sum_congr rfl fun r _ => ?_
    rw [gE_apply]
    by_cases hsq : Squarefree r
    · by_cases hc : Nat.Coprime r e
      · rw [if_pos hc, if_pos (And.intro hsq hc)]; ring
      · have hn : ¬ (Squarefree r ∧ Nat.Coprime r e) := fun h' => hc h'.2
        rw [if_neg hc, if_neg hn]; ring
    · have hn : ¬ (Squarefree r ∧ Nat.Coprime r e) := fun h' => hsq h'.1
      rw [if_neg hn, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
      simp
  · intro r hr
    simp only [Finset.mem_Icc] at hr ⊢
    exact ⟨hr.1, hr.2.trans (Nat.div_le_self _ _)⟩
  · intro r hr hr'
    simp only [Finset.mem_Icc, not_and, not_le] at hr hr'
    have h1 : ⌊Q⌋₊ / e < r := hr' hr.1
    have h2 : ⌊Q⌋₊ < e * r := by
      rw [Nat.div_lt_iff_lt_mul he] at h1; linarith [mul_comm r e]
    rw [omega_eq_zero_of_gt W Q h2]; ring

/-- **Lemma 6.13, Ramanujan expansion** `k_ω(h) = ∑_{e ≥ 1} Ω(e) c_e(h)` (only `e ≤ Q` contribute). -/
theorem kω_eq_ramanujan (W : Weight) (Q : ℝ) (h : ℤ) :
    (kω W Q h : ℂ) = levelKernel (levels Q) (aΩ W Q) h := by
  set N := ⌊Q⌋₊ with hN
  rw [kω_eq_sum_q]
  push_cast
  have h1 : ∀ q ∈ Finset.Icc 1 N, (W.omega Q q : ℂ) *
      ∑ d ∈ q.divisors.filter (fun d : ℕ => ((d : ℕ) : ℤ) ∣ h),
        (Nat.totient d : ℂ) * (μ (q / d) : ℂ)
      = ∑ e ∈ q.divisors, (W.omega Q q : ℂ) *
          (ramanujan e h * ((((Nat.totient e : ℝ) / e) * gE e (q / e) : ℝ) : ℂ)) := by
    intro q hq
    rw [K_eq q (Finset.mem_Icc.mp hq).1 h, Finset.mul_sum]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm' (t' := Finset.Icc 1 N)
    (s' := fun e => (Finset.Icc 1 N).filter (fun q => e ∣ q))]
  · unfold levelKernel levels aΩ
    refine Finset.sum_congr rfl fun e he => ?_
    have he0 : 0 < e := (Finset.mem_Icc.mp he).1
    rw [Ωlev_eq_gE W Q e he0]
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_nbij' (fun q => q / e) (fun r => e * r) ?_ ?_ ?_ ?_ ?_
    · intro q hq
      simp only [Finset.mem_filter, Finset.mem_Icc] at hq ⊢
      obtain ⟨⟨hq1, hqN⟩, t, rfl⟩ := hq
      rw [Nat.mul_div_cancel_left t he0]
      refine ⟨Nat.pos_of_ne_zero (by rintro rfl; simp at hq1), ?_⟩
      rw [Nat.le_div_iff_mul_le he0]; linarith [mul_comm e t]
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_Icc] at hr ⊢
      refine ⟨⟨by nlinarith, ?_⟩, dvd_mul_right e r⟩
      have := (Nat.le_div_iff_mul_le he0).mp hr.2
      linarith [mul_comm e r]
    · intro q hq
      exact Nat.mul_div_cancel' (Finset.mem_filter.mp hq).2
    · intro r _
      exact Nat.mul_div_cancel_left r he0
    · intro q hq
      obtain ⟨t, rfl⟩ := (Finset.mem_filter.mp hq).2
      rw [Nat.mul_div_cancel_left t he0]
      ring
  · intro q e
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hq1, hqN⟩, heq, -⟩
      exact ⟨⟨⟨hq1, hqN⟩, heq⟩, Nat.pos_of_dvd_of_pos heq hq1, (Nat.le_of_dvd hq1 heq).trans hqN⟩
    · rintro ⟨⟨⟨hq1, hqN⟩, heq⟩, -, -⟩
      exact ⟨⟨hq1, hqN⟩, heq, by omega⟩

lemma normSq_S_eq (I : Finset ℤ) (y : ℤ → ℂ) (θ : ℝ) :
    ((‖S I y θ‖ : ℂ)) ^ 2 =
      ∑ n ∈ I, ∑ m ∈ I, y n * conj (y m) * eA (((n : ℝ) - m) * θ) := by
  rw [← Complex.ofReal_pow, ofReal_norm_sq]
  unfold S
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, conj_eA, show ((n : ℝ) - m) * θ = n * θ + -(m * θ) by ring, eA_add]
  ring

/-- **Lemma 6.13, `eqC:farey`.** For `y` supported on `Q`-rough integers,
`y^*Δy = y^*T_ω y = ∫|S_y|² dμ_Ω`. -/
theorem famForm_eq_levelForm_Ω (W : Weight) (Q : ℝ) (I : Finset ℤ) (hI : ∀ n ∈ I, IsRough Q n)
    (y : ℤ → ℂ) : famForm W Q I y = levelForm (levels Q) (aΩ W Q) I y := by
  apply Complex.ofReal_injective
  rw [famForm_eq_sum]
  have hk : ∀ n ∈ I, ∀ m ∈ I, Δ W Q n m = levelKernel (levels Q) (aΩ W Q) (n - m) :=
    fun n hn m hm => by rw [toeplitz_identity W Q (hI n hn) (hI m hm), kω_eq_ramanujan]
  rw [Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun m hm => by rw [hk n hn m hm]]
  unfold levelForm levelKernel ramanujan
  push_cast
  simp_rw [normSq_S_eq, Finset.mul_sum]
  calc ∑ n ∈ I, ∑ m ∈ I, ∑ e ∈ levels Q, ∑ c ∈ reduced e,
        y n * conj (y m) * ((aΩ W Q e : ℂ) * eA ((c : ℝ) * ((n : ℝ) - m) / e))
      = ∑ n ∈ I, ∑ e ∈ levels Q, ∑ c ∈ reduced e, ∑ m ∈ I,
        y n * conj (y m) * ((aΩ W Q e : ℂ) * eA ((c : ℝ) * ((n : ℝ) - m) / e)) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ e ∈ levels Q, ∑ c ∈ reduced e, ∑ n ∈ I, ∑ m ∈ I,
        y n * conj (y m) * ((aΩ W Q e : ℂ) * eA ((c : ℝ) * ((n : ℝ) - m) / e)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.sum_comm]
    _ = _ := by
        refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun c _ => ?_
        refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
        rw [show (c : ℝ) * ((n : ℝ) - m) / e = ((n : ℝ) - m) * ((c : ℝ) / e) by ring]
        ring

/-- `μ_Ω(𝕋) = ∑_e Ω(e) φ(e) = H`. -/
theorem muΩ_mass (W : Weight) (Q : ℝ) :
    ∑ e ∈ levels Q, Ωlev W Q e * Nat.totient e = W.H Q := by
  apply Complex.ofReal_injective
  rw [← kω_zero, kω_eq_ramanujan]
  unfold levelKernel aΩ ramanujan
  push_cast
  refine Finset.sum_congr rfl fun e _ => ?_
  congr 1
  simp only [mul_zero, zero_div]
  rw [show eA 0 = 1 by simp [eA], Finset.sum_const, card_reduced]
  simp

end Families
