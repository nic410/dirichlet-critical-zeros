/-
Frequency expansions for `lem:B1` (`lemma-B-majorant.tex`, "Mean zero").

For `χ` primitive mod `q ≥ 2` and `r ≥ 1`, the function `n ↦ c_r(n) χ(n)` is a combination of the
additive characters `e(n(h/r + b/q))` (Gauss-sum expansion of `χ`). The coefficients of the integer
frequencies sum to zero (`int_freq_sum_zero`; this is the TeX's "mean zero for every `r`"), and
every non-integer frequency has denominator dividing `rq`. With `sum_smooth_eA_rat_le` this gives
`|∑_n F(n) c_r(n) χ(n)| ≤ φ(r) √q (b − a + K + 1) sup|F^{(K)}| (rq/4)^K`
(`sum_F_ramanujan_char_le`), the Poisson estimate of the proof of `lem:B1`.
-/
import Families.Phase3.C.SmoothSum
import Families.Toeplitz
import Families.LemmaS

noncomputable section

open scoped ComplexConjugate
open Finset

namespace Families.Phase3.C

/-! ### Ramanujan sums are real -/

lemma ramanujan_neg (r : ℕ) (h : ℤ) : ramanujan r (-h) = ramanujan r h := by
  unfold ramanujan
  rcases Nat.lt_or_ge r 2 with hr | hr
  · interval_cases r
    · simp [reduced]
    · have : reduced 1 = {0} := by decide
      simp [this]
  · refine Finset.sum_nbij' (fun c => r - c) (fun c => r - c) ?_ ?_ ?_ ?_ ?_
    · intro c hc
      simp only [reduced, Finset.mem_filter, Finset.mem_range] at hc ⊢
      have hc0 : c ≠ 0 := by
        rintro rfl; simp at hc; omega
      refine ⟨by omega, ?_⟩
      exact (Nat.coprime_self_sub_left hc.1.le).mpr hc.2
    · intro c hc
      simp only [reduced, Finset.mem_filter, Finset.mem_range] at hc ⊢
      have hc0 : c ≠ 0 := by
        rintro rfl; simp at hc; omega
      refine ⟨by omega, ?_⟩
      exact (Nat.coprime_self_sub_left hc.1.le).mpr hc.2
    · intro c hc
      simp only [reduced, Finset.mem_filter, Finset.mem_range] at hc
      omega
    · intro c hc
      simp only [reduced, Finset.mem_filter, Finset.mem_range] at hc
      omega
    · intro c hc
      simp only [reduced, Finset.mem_filter, Finset.mem_range] at hc
      have hcr : c ≤ r := hc.1.le
      have hr0 : (r : ℝ) ≠ 0 := by positivity
      rw [Nat.cast_sub hcr]
      have : ((r : ℝ) - c) * (h : ℝ) / r = (c : ℝ) * ((-h : ℤ) : ℝ) / r + ((h : ℤ) : ℝ) := by
        push_cast; field_simp; ring
      rw [this, eA_add', eA_int, mul_one]

lemma ramanujan_im (r : ℕ) (h : ℤ) : (ramanujan r h).im = 0 := by
  have h1 : conj (ramanujan r h) = ramanujan r h := by
    rw [conj_ramanujan, ramanujan_neg]
  exact Complex.conj_eq_iff_im.mp h1

lemma ramanujan_re_coe (r : ℕ) (h : ℤ) : (((ramanujan r h).re : ℝ) : ℂ) = ramanujan r h := by
  apply Complex.ext
  · simp
  · simp [ramanujan_im]

lemma norm_ramanujan_le (r : ℕ) (h : ℤ) : ‖ramanujan r h‖ ≤ Nat.totient r := by
  unfold ramanujan
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_eA', Finset.sum_const, card_reduced, nsmul_eq_mul, mul_one, le_refl]

/-! ### The Gauss-sum expansion of `χ` -/

lemma char_expand {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (n : ℕ) :
    χ n * gaussSum χ⁻¹ (ZMod.stdAddChar (N := q)) =
      ∑ b : ZMod q, χ⁻¹ b * eA (n * ((b.val : ℝ) / q)) := by
  have := gauss_identity χ hχ (n : ZMod q)
  rw [this]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  have h2 := eA_eq_stdAddChar (q := q) b.val (n : ℤ)
  push_cast at h2
  rw [h2, ZMod.natCast_zmod_val]

/-- The Ramanujan–character product as a combination of additive characters. -/
lemma ramanujan_char_expand {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    {r : ℕ} (hr : 0 < r) (n : ℕ) :
    ramanujan r n * χ n * gaussSum χ⁻¹ (ZMod.stdAddChar (N := q)) =
      ∑ h ∈ reduced r, ∑ b : ZMod q, χ⁻¹ b *
        eA (n * (((h * q + b.val * r : ℤ) : ℝ) / ((r * q : ℕ) : ℝ))) := by
  rw [mul_assoc, char_expand χ hχ n]
  unfold ramanujan
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hq : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  have hr' : (r : ℝ) ≠ 0 := by positivity
  rw [mul_left_comm, ← eA_add']
  congr 2
  push_cast
  field_simp

/-! ### Integer frequencies -/

lemma nonprimitive_one {q : ℕ} [NeZero q] (hq : 2 ≤ q) (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) : χ⁻¹ ≠ 1 := by
  intro h
  have h1 : χ = 1 := by
    have := congrArg (·⁻¹) h
    simpa using this
  rw [DirichletCharacter.isPrimitive_def, h1, DirichletCharacter.conductor_one] at hχ
  omega

/-- The integer frequencies carry total coefficient `0` ("mean zero for every `r`"). -/
lemma int_freq_sum_zero {q : ℕ} [NeZero q] (hq : 2 ≤ q) (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) {r : ℕ} (hr : 0 < r) :
    ∑ h ∈ reduced r, ∑ b : ZMod q,
      (if ((r * q : ℕ) : ℤ) ∣ (h * q + b.val * r : ℤ) then χ⁻¹ b else 0) = 0 := by
  have hq0 : 0 < q := by omega
  -- each term vanishes unless `r = q` and `b = -h`
  have key : ∀ h ∈ reduced r, ∀ b : ZMod q,
      (if ((r * q : ℕ) : ℤ) ∣ (h * q + b.val * r : ℤ) then χ⁻¹ b else 0) =
        (if r = q ∧ b = -(h : ZMod q) then χ⁻¹ b else 0) := by
    intro h hh b
    simp only [reduced, Finset.mem_filter, Finset.mem_range] at hh
    by_cases hb : IsUnit b
    · have hbc : Nat.Coprime b.val q := by
        rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]; exact hb
      by_cases hdiv : ((r * q : ℕ) : ℤ) ∣ (h * q + b.val * r : ℤ)
      · have hrq : r = q := by
          have hq1 : (q : ℤ) ∣ (b.val * r : ℤ) := by
            have : (q : ℤ) ∣ (h * q + b.val * r : ℤ) :=
              (Int.natCast_dvd_natCast.mpr (dvd_mul_left q r)).trans (by exact_mod_cast hdiv)
            have h2 : (q : ℤ) ∣ (h * q : ℤ) := dvd_mul_left _ _
            have := (Int.dvd_add_right h2).mp this
            exact this
          have hq2 : q ∣ b.val * r := by exact_mod_cast hq1
          have hqr : q ∣ r := (Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_comm.mp hbc) hq2)
          have hr1 : (r : ℤ) ∣ (h * q : ℤ) := by
            have : (r : ℤ) ∣ (h * q + b.val * r : ℤ) :=
              (Int.natCast_dvd_natCast.mpr (dvd_mul_right r q)).trans (by exact_mod_cast hdiv)
            have h2 : (r : ℤ) ∣ (b.val * r : ℤ) := dvd_mul_left _ _
            exact (Int.dvd_add_left h2).mp this
          have hr2 : r ∣ h * q := by exact_mod_cast hr1
          have hrq : r ∣ q := Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_comm.mp hh.2) hr2
          exact Nat.dvd_antisymm hrq hqr
        subst hrq
        have hbh : b = -(h : ZMod r) := by
          have h3 : ((r * r : ℕ) : ℤ) ∣ ((h + b.val : ℕ) : ℤ) * r := by
            have : (h * r + b.val * r : ℤ) = ((h + b.val : ℕ) : ℤ) * r := by push_cast; ring
            rw [← this]; exact hdiv
          have h4 : ((r : ℕ) : ℤ) ∣ ((h + b.val : ℕ) : ℤ) := by
            have hr0 : (r : ℤ) ≠ 0 := by exact_mod_cast hr.ne'
            push_cast at h3
            exact (mul_dvd_mul_iff_right hr0).mp h3
          have h5 : r ∣ h + b.val := by exact_mod_cast h4
          have h6 : ((h + b.val : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h5
          push_cast at h6
          rw [ZMod.natCast_zmod_val] at h6
          linear_combination h6
        rw [if_pos hdiv, if_pos ⟨rfl, hbh⟩]
      · rw [if_neg hdiv, if_neg]
        rintro ⟨rfl, hbh⟩
        apply hdiv
        have h6 : ((h + b.val : ℕ) : ZMod r) = 0 := by
          push_cast; rw [ZMod.natCast_zmod_val, hbh]; ring
        have h5 : r ∣ h + b.val := (ZMod.natCast_eq_zero_iff _ _).mp h6
        obtain ⟨k, hk⟩ := h5
        refine ⟨k, ?_⟩
        have : (h * r + b.val * r : ℤ) = ((h + b.val : ℕ) : ℤ) * r := by push_cast; ring
        rw [this, hk]; push_cast; ring
    · have h0 : χ⁻¹ b = 0 := MulChar.map_nonunit _ hb
      simp [h0]
  rw [Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun b _ => key h hh b]
  by_cases hrq : r = q
  · subst hrq
    simp only [true_and]
    have : ∀ h ∈ reduced r, (∑ b : ZMod r, if b = -(h : ZMod r) then χ⁻¹ b else 0)
        = χ⁻¹ (-(h : ZMod r)) := fun h _ => by rw [Finset.sum_ite_eq']; simp
    rw [Finset.sum_congr rfl this]
    rw [← sum_units_eq_sum_reduced (fun b => χ⁻¹ (-b))]
    have h1 : ∑ b : ZMod r, (if IsUnit b then χ⁻¹ (-b) else 0) = ∑ b : ZMod r, χ⁻¹ (-b) := by
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs with hb
      · rfl
      · have : ¬ IsUnit (-b) := fun h => hb (by simpa using h.neg)
        rw [MulChar.map_nonunit _ this]
    rw [h1]
    rw [show ∑ b : ZMod r, χ⁻¹ (-b) = ∑ b : ZMod r, χ⁻¹ b from
      Fintype.sum_equiv (Equiv.neg _) _ _ (fun b => rfl)]
    exact MulChar.sum_eq_zero_of_ne_one (nonprimitive_one hq χ hχ)
  · simp [hrq]

/-! ### The Poisson estimate of `lem:B1` -/

/-- `|∑_n F(n) c_r(n) χ(n)| ≤ φ(r) √q (b − a + K + 1) sup|F^{(K)}| (rq/4)^K` for `χ` primitive mod
`q ≥ 2`, `r ≥ 1`, `F` smooth supported in `[a, b] ⊂ [0, ∞)`. -/
theorem sum_F_ramanujan_char_le {q : ℕ} [NeZero q] (hq : 2 ≤ q) (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) {r : ℕ} (hr : 0 < r) {F : ℝ → ℂ} {K : ℕ} (hF : ContDiff ℝ K F)
    {Mb : ℝ} (hM : ∀ y, ‖iteratedDeriv K F y‖ ≤ Mb) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hsupp : ∀ y, F y ≠ 0 → a ≤ y ∧ y ≤ b) (S : Finset ℕ) (hS : ∀ n : ℕ, F n ≠ 0 → n ∈ S) :
    ‖∑ n ∈ S, F n * ramanujan r n * χ n‖ ≤
      Nat.totient r * Real.sqrt q * ((b - a + K + 1) * Mb * (((r * q : ℕ) : ℝ) / 4) ^ K) := by
  set τ := gaussSum χ⁻¹ (ZMod.stdAddChar (N := q)) with hτ
  have hτn : ‖τ‖ = Real.sqrt q := by
    rw [← Real.sqrt_sq (norm_nonneg τ), norm_sq_gaussSum χ hχ]
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hτpos : 0 < ‖τ‖ := by rw [hτn]; exact Real.sqrt_pos.mpr hq0
  have hM0 : 0 ≤ Mb := (norm_nonneg _).trans (hM 0)
  set M : ℕ := r * q with hMdef
  have hMpos : 0 < M := Nat.mul_pos hr (by omega)
  set m : ℕ → ZMod q → ℤ := fun h b => h * q + b.val * r with hm
  set S0 : ℂ := ∑ n ∈ S, F n with hS0
  -- expansion
  have hexp : (∑ n ∈ S, F n * ramanujan r n * χ n) * τ =
      ∑ h ∈ reduced r, ∑ b : ZMod q, χ⁻¹ b *
        ((∑ n ∈ S, F n * eA (n * ((m h b : ℝ) / (M : ℝ)))) -
          (if ((M : ℕ) : ℤ) ∣ m h b then S0 else 0)) := by
    have hint := int_freq_sum_zero hq χ hχ hr
    have hsplit : ∀ h ∈ reduced r, ∀ b : ZMod q,
        χ⁻¹ b * ((∑ n ∈ S, F n * eA (n * ((m h b : ℝ) / (M : ℝ)))) -
          (if ((M : ℕ) : ℤ) ∣ m h b then S0 else 0)) =
        χ⁻¹ b * (∑ n ∈ S, F n * eA (n * ((m h b : ℝ) / (M : ℝ)))) -
          (if ((M : ℕ) : ℤ) ∣ m h b then χ⁻¹ b else 0) * S0 := by
      intro h _ b; split_ifs <;> ring
    rw [Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun b _ => hsplit h hh b]
    simp only [Finset.sum_sub_distrib, ← Finset.sum_mul]
    rw [hint, zero_mul, sub_zero]
    rw [Finset.sum_mul]
    have : ∀ n ∈ S, F n * ramanujan r n * χ n * τ =
        ∑ h ∈ reduced r, ∑ b : ZMod q, χ⁻¹ b * (F n * eA (n * ((m h b : ℝ) / (M : ℝ)))) := by
      intro n _
      rw [mul_assoc, mul_assoc, ← mul_assoc (ramanujan r n), ramanujan_char_expand χ hχ hr n,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [hm, hMdef]; ring
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
  -- each bracket is bounded
  set Bd : ℝ := (b - a + K + 1) * Mb * ((M : ℝ) / 4) ^ K with hBd
  have hBd0 : 0 ≤ Bd := by
    have : 0 ≤ b - a + K + 1 := by linarith
    positivity
  have hterm : ∀ h ∈ reduced r, ∀ bb : ZMod q,
      ‖χ⁻¹ bb * ((∑ n ∈ S, F n * eA (n * ((m h bb : ℝ) / (M : ℝ)))) -
          (if ((M : ℕ) : ℤ) ∣ m h bb then S0 else 0))‖ ≤ Bd := by
    intro h _ bb
    rw [norm_mul]
    have hχn : ‖χ⁻¹ bb‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
    by_cases hdiv : ((M : ℕ) : ℤ) ∣ m h bb
    · rw [if_pos hdiv]
      have : ∑ n ∈ S, F n * eA (n * ((m h bb : ℝ) / (M : ℝ))) = S0 := by
        refine Finset.sum_congr rfl fun n _ => ?_
        obtain ⟨k, hk⟩ := hdiv
        have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hMpos.ne'
        have : (n : ℝ) * ((m h bb : ℝ) / (M : ℝ)) = ((n * k : ℤ) : ℝ) := by
          rw [hk]; push_cast; field_simp
        rw [this, eA_int, mul_one]
      rw [this, sub_self, norm_zero, mul_zero]; exact hBd0
    · rw [if_neg hdiv, sub_zero]
      have := sum_smooth_eA_rat_le hF hM ha hab hsupp S hS hMpos hdiv
      calc ‖χ⁻¹ bb‖ * ‖∑ n ∈ S, F n * eA (n * ((m h bb : ℝ) / (M : ℝ)))‖
          ≤ 1 * Bd := mul_le_mul hχn this (norm_nonneg _) zero_le_one
        _ = Bd := one_mul _
  have hbound : ‖(∑ n ∈ S, F n * ramanujan r n * χ n) * τ‖ ≤ Nat.totient r * q * Bd := by
    rw [hexp]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ h ∈ reduced r, ‖∑ bb : ZMod q, χ⁻¹ bb *
            ((∑ n ∈ S, F n * eA (n * ((m h bb : ℝ) / (M : ℝ)))) -
              (if ((M : ℕ) : ℤ) ∣ m h bb then S0 else 0))‖
        ≤ ∑ h ∈ reduced r, ∑ bb : ZMod q, Bd := by
          refine Finset.sum_le_sum fun h hh => (norm_sum_le _ _).trans ?_
          exact Finset.sum_le_sum fun bb _ => hterm h hh bb
      _ = Nat.totient r * q * Bd := by
          simp only [Finset.sum_const, Finset.card_univ, ZMod.card, card_reduced, nsmul_eq_mul]
          ring
  rw [norm_mul, hτn] at hbound
  have hsq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq0.le
  have hsq0 : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have : ‖∑ n ∈ S, F n * ramanujan r n * χ n‖ * Real.sqrt q ≤
      (Nat.totient r * Real.sqrt q * Bd) * Real.sqrt q := by
    calc _ ≤ Nat.totient r * q * Bd := hbound
      _ = Nat.totient r * (Real.sqrt q * Real.sqrt q) * Bd := by rw [hsq]
      _ = _ := by ring
  exact le_of_mul_le_mul_right this hsq0

end Families.Phase3.C
