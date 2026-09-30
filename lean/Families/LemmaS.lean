/-
`lem:S` (Lemma S: positivity), and `lem:Omega`(b) (`Ω^- ≤ m(e/Q)`), `lemma-toeplitz-C.tex` §6.2.
The quadratic form of a Farey-type measure with real level weights, its Toeplitz matrix,
positivity for nonnegative weights and monotonicity in the weights.
-/
import Families.Basic

noncomputable section

open scoped BigOperators ComplexConjugate ArithmeticFunction.Moebius ComplexOrder
open ArithmeticFunction Finset

namespace Families

/-! ### Farey-type measures: form, kernel, positivity -/

private lemma eA_add (a b : ℝ) : eA (a + b) = eA a * eA b := by
  unfold eA; rw [← Complex.exp_add]; congr 1; push_cast; ring

private lemma conj_eA (a : ℝ) : conj (eA a) = eA (-a) := by
  unfold eA; rw [← Complex.exp_conj]; congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]; push_cast; ring

lemma conj_ramanujan (e : ℕ) (h : ℤ) : conj (ramanujan e h) = ramanujan e (-h) := by
  unfold ramanujan; rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [conj_eA]; congr 1; push_cast; ring

lemma conj_levelKernel (E : Finset ℕ) (a : ℕ → ℝ) (h : ℤ) :
    conj (levelKernel E a h) = levelKernel E a (-h) := by
  unfold levelKernel; rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_mul, Complex.conj_ofReal, conj_ramanujan]

private lemma ofReal_norm_sq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

private lemma ofReal_norm_sq' (z : ℂ) : ((‖z‖ : ℂ)) ^ 2 = z * conj z := by
  rw [← Complex.ofReal_pow, ofReal_norm_sq]

private lemma S_mul_conj (I : Finset ℤ) (y : ℤ → ℂ) (θ : ℝ) :
    S I y θ * conj (S I y θ) = ∑ n ∈ I, ∑ m ∈ I, y n * conj (y m) * eA ((n - m : ℤ) * θ) := by
  unfold S
  rw [map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, conj_eA]
  have : ((n - m : ℤ) : ℝ) * θ = n * θ + -(m * θ) := by push_cast; ring
  rw [this, eA_add]; ring

/-- `∫|S_y|² dμ_a = ∑_{n,m} y_n \bar y_m k_a(n-m)`. -/
theorem levelForm_eq_sum (E : Finset ℕ) (a : ℕ → ℝ) (I : Finset ℤ) (y : ℤ → ℂ) :
    (levelForm E a I y : ℂ) = ∑ n ∈ I, ∑ m ∈ I, y n * conj (y m) * levelKernel E a (n - m) := by
  unfold levelForm levelKernel ramanujan
  push_cast
  simp_rw [ofReal_norm_sq', S_mul_conj, Finset.mul_sum]
  -- LHS: Σ e Σ c Σ n Σ m ; RHS: Σ n Σ m Σ e Σ c
  calc ∑ e ∈ E, ∑ c ∈ reduced e, ∑ n ∈ I, ∑ m ∈ I,
          (a e : ℂ) * (y n * conj (y m) * eA (((n - m : ℤ) : ℝ) * ((c : ℝ) / e)))
      = ∑ e ∈ E, ∑ n ∈ I, ∑ c ∈ reduced e, ∑ m ∈ I,
          (a e : ℂ) * (y n * conj (y m) * eA (((n - m : ℤ) : ℝ) * ((c : ℝ) / e))) :=
        Finset.sum_congr rfl fun e _ => Finset.sum_comm
    _ = ∑ n ∈ I, ∑ e ∈ E, ∑ c ∈ reduced e, ∑ m ∈ I,
          (a e : ℂ) * (y n * conj (y m) * eA (((n - m : ℤ) : ℝ) * ((c : ℝ) / e))) :=
        Finset.sum_comm
    _ = ∑ n ∈ I, ∑ e ∈ E, ∑ m ∈ I, ∑ c ∈ reduced e,
          (a e : ℂ) * (y n * conj (y m) * eA (((n - m : ℤ) : ℝ) * ((c : ℝ) / e))) :=
        Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun e _ => Finset.sum_comm
    _ = ∑ n ∈ I, ∑ m ∈ I, ∑ e ∈ E, ∑ c ∈ reduced e,
          (a e : ℂ) * (y n * conj (y m) * eA (((n - m : ℤ) : ℝ) * ((c : ℝ) / e))) :=
        Finset.sum_congr rfl fun n _ => Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
        refine Finset.sum_congr rfl fun e _ => ?_
        refine Finset.sum_congr rfl fun c _ => ?_
        have h1 : eA (((n - m : ℤ) : ℝ) * ((c : ℝ) / e)) = eA ((c : ℝ) * ((n : ℝ) - m) / e) := by
          congr 1; push_cast; ring
        rw [h1]; ring

lemma levelForm_nonneg (E : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ e ∈ E, 0 ≤ a e) (I : Finset ℤ)
    (y : ℤ → ℂ) : 0 ≤ levelForm E a I y :=
  Finset.sum_nonneg fun e he => mul_nonneg (ha e he) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma toeplitz_isHermitian (E : Finset ℕ) (a : ℕ → ℝ) (I : Finset ℤ) :
    (toeplitz I (levelKernel E a)).IsHermitian := by
  ext n m
  simp only [Matrix.conjTranspose_apply, toeplitz]
  rw [show star (levelKernel E a ((m : ℤ) - n)) = conj (levelKernel E a ((m : ℤ) - n)) from rfl,
    conj_levelKernel, neg_sub]

open Matrix in
lemma toeplitz_quad (E : Finset ℕ) (a : ℕ → ℝ) (I : Finset ℤ) (x : I → ℂ) :
    star x ⬝ᵥ (toeplitz I (levelKernel E a) *ᵥ x) =
      (levelForm E a I (fun n => if h : n ∈ I then star (x ⟨n, h⟩) else 0) : ℂ) := by
  rw [levelForm_eq_sum]
  simp only [dotProduct, Matrix.mulVec, toeplitz, Finset.mul_sum]
  rw [← Finset.sum_coe_sort I]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_coe_sort I]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Finset.coe_mem, dif_pos, Subtype.coe_eta, Pi.star_apply]
  rw [show conj (star (x j)) = x j from star_star _]
  simp only [RCLike.star_def]
  ring

/-- The Toeplitz matrix of a *positive* Farey-type measure is positive semidefinite. -/
theorem toeplitz_posSemidef (E : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ e ∈ E, 0 ≤ a e) (I : Finset ℤ) :
    (toeplitz I (levelKernel E a)).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨toeplitz_isHermitian E a I, fun x => ?_⟩
  rw [toeplitz_quad]
  exact Complex.zero_le_real.mpr (levelForm_nonneg E a ha I _)

lemma toeplitz_sub (I : Finset ℤ) (k₁ k₂ : ℤ → ℂ) :
    toeplitz I k₁ - toeplitz I k₂ = toeplitz I (fun h => k₁ h - k₂ h) := by
  ext n m; rfl

lemma levelKernel_sub (E : Finset ℕ) (a b : ℕ → ℝ) (h : ℤ) :
    levelKernel E b h - levelKernel E a h = levelKernel E (fun e => b e - a e) h := by
  unfold levelKernel
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  push_cast; ring

/-- Monotonicity: `a ≤ b` levelwise gives `T_a ⪯ T_b`. -/
theorem toeplitz_mono (E : Finset ℕ) (a b : ℕ → ℝ) (hab : ∀ e ∈ E, a e ≤ b e) (I : Finset ℤ) :
    (toeplitz I (levelKernel E b) - toeplitz I (levelKernel E a)).PosSemidef := by
  rw [toeplitz_sub]
  simp_rw [levelKernel_sub]
  exact toeplitz_posSemidef E _ (fun e he => sub_nonneg.mpr (hab e he)) I

/-- Monotonicity of the forms: `a ≤ b` levelwise gives `∫|S_y|² dμ_a ≤ ∫|S_y|² dμ_b`. -/
theorem levelForm_mono (E : Finset ℕ) (a b : ℕ → ℝ) (hab : ∀ e ∈ E, a e ≤ b e) (I : Finset ℤ)
    (y : ℤ → ℂ) : levelForm E a I y ≤ levelForm E b I y :=
  Finset.sum_le_sum fun e he =>
    mul_le_mul_of_nonneg_right (hab e he) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

/-! ### `lem:Omega`(b) -/

/-- `eqC:Omega`, second form: `Ω(e) = ∑_{r sqfree, (r,e)=1} (μ(r)/φ(r)) w(er/Q)`. -/
theorem Ωlev_eq_second_form (W : Weight) (Q : ℝ) (e : ℕ) (he : 1 ≤ e) :
    Ωlev W Q e = ∑ r ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun r : ℕ => Squarefree r ∧ Nat.Coprime r e),
      (μ r : ℝ) / Nat.totient r * W.w ((e * r : ℕ) / Q) := by
  unfold Ωlev Weight.omega
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  obtain ⟨hr1, -, hcop⟩ := Finset.mem_filter.mp hr
  have hr0 : 1 ≤ r := (Finset.mem_Icc.mp hr1).1
  rw [Nat.totient_mul hcop.symm]
  have he0 : (e : ℝ) ≠ 0 := by positivity
  have hr0' : (r : ℝ) ≠ 0 := by positivity
  have hφe : (Nat.totient e : ℝ) ≠ 0 := by
    have := Nat.totient_pos.mpr (by omega : 0 < e); positivity
  have hφr : (Nat.totient r : ℝ) ≠ 0 := by
    have := Nat.totient_pos.mpr (by omega : 0 < r); positivity
  push_cast
  field_simp

lemma mfun_nonneg (W : Weight) (u : ℝ) : 0 ≤ mfun W u := le_max_right _ _

/-- **`lem:Omega`(b).** `Ω^-(e) := max(-Ω(e), 0) ≤ m(e/Q)`. -/
theorem lemOmega_b (W : Weight) (Q : ℝ) (hQ : 0 < Q) (e : ℕ) (he : 1 ≤ e) :
    max (-Ωlev W Q e) 0 ≤ mfun W (e / Q) := by
  unfold mfun
  refine max_le_max ?_ le_rfl
  rw [Ωlev_eq_second_form W Q e he]
  set F := (Finset.Icc 1 ⌊Q⌋₊).filter (fun r : ℕ => Squarefree r ∧ Nat.Coprime r e) with hF
  set G := (Finset.Icc 1 ⌊1 / ((e : ℝ) / Q)⌋₊).filter (fun r : ℕ => μ r = -1) with hG
  set f : ℕ → ℝ := fun r => W.w ((e * r : ℕ) / Q) / Nat.totient r with hfdef
  have hf : ∀ r, 0 ≤ f r := fun r => div_nonneg (W.nonneg _) (Nat.cast_nonneg _)
  have hsplit : -(∑ r ∈ F, (μ r : ℝ) / Nat.totient r * W.w ((e * r : ℕ) / Q))
      = ∑ r ∈ F.filter (fun r => μ r = -1), f r - ∑ r ∈ F.filter (fun r => ¬ μ r = -1), f r := by
    have h0 := (Finset.sum_filter_add_sum_filter_not F (fun r => μ r = -1)
      (fun r => (μ r : ℝ) / Nat.totient r * W.w ((e * r : ℕ) / Q))).symm
    have e1 : ∑ r ∈ F.filter (fun r => μ r = -1), (μ r : ℝ) / Nat.totient r * W.w ((e * r : ℕ) / Q)
        = -∑ r ∈ F.filter (fun r => μ r = -1), f r := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [(Finset.mem_filter.mp hr).2, hfdef]; push_cast; ring
    have e2 : ∑ r ∈ F.filter (fun r => ¬ μ r = -1), (μ r : ℝ) / Nat.totient r * W.w ((e * r : ℕ) / Q)
        = ∑ r ∈ F.filter (fun r => ¬ μ r = -1), f r := by
      refine Finset.sum_congr rfl fun r hr => ?_
      obtain ⟨hrF, hne⟩ := Finset.mem_filter.mp hr
      have hsq := (Finset.mem_filter.mp hrF).2.1
      have h1 : μ r = 1 := by
        have := (moebius_ne_zero_iff_eq_or (n := r)).mp (moebius_ne_zero_iff_squarefree.mpr hsq)
        tauto
      rw [h1, hfdef]; push_cast; ring
    rw [h0, e1, e2]; ring
  rw [hsplit]
  -- the μ = -1 part
  have hminus : ∑ r ∈ F.filter (fun r => μ r = -1), f r
      ≤ ∑ r ∈ G, W.w ((e : ℝ) / Q * r) / Nat.totient r := by
    rw [← Finset.sum_filter_ne_zero]
    have hG' : ∀ r ∈ G, W.w ((e : ℝ) / Q * r) / Nat.totient r = f r := by
      intro r _
      rw [hfdef]; push_cast; ring_nf
    rw [Finset.sum_congr rfl hG']
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun r _ _ => hf r)
    intro r hr
    obtain ⟨hr1, hr2⟩ := Finset.mem_filter.mp hr
    obtain ⟨hrF, hmu⟩ := Finset.mem_filter.mp hr1
    have hrIcc := (Finset.mem_filter.mp hrF).1
    have hr1' : 1 ≤ r := (Finset.mem_Icc.mp hrIcc).1
    have hw : W.w ((e * r : ℕ) / Q) ≠ 0 := by
      intro h0; apply hr2; rw [hfdef]; simp only; rw [h0, zero_div]
    have hle := (W.supp _ hw).2
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨hr1', ?_⟩, hmu⟩
    apply Nat.le_floor
    rw [one_div_div, le_div_iff₀ (by positivity : (0 : ℝ) < e)]
    rw [div_le_one hQ] at hle
    push_cast at hle
    linarith
  -- the μ = 1 part contains r = 1
  have hplus : W.w ((e : ℝ) / Q) ≤ ∑ r ∈ F.filter (fun r => ¬ μ r = -1), f r := by
    by_cases hw : W.w ((e : ℝ) / Q) = 0
    · rw [hw]; exact Finset.sum_nonneg fun r _ => hf r
    have hle := (W.supp _ hw).2
    rw [div_le_one hQ] at hle
    have hQ1 : 1 ≤ ⌊Q⌋₊ := Nat.le_floor (by push_cast; exact le_trans (by exact_mod_cast he) hle)
    have hmem : 1 ∈ F.filter (fun r => ¬ μ r = -1) := by
      rw [Finset.mem_filter, hF, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨⟨le_rfl, hQ1⟩, squarefree_one, Nat.coprime_one_left e⟩, ?_⟩
      rw [moebius_apply_one]; decide
    have := Finset.single_le_sum (fun r _ => hf r) hmem
    refine le_trans (le_of_eq ?_) this
    rw [hfdef]; simp
  linarith

/-! ### Lemma S -/

/-- **`lem:S` (positivity part).** `T_{μ_Ω} ⪯ T^+ ⪯ T^♮` and `T^+, T^♮ ⪰ 0`
(as Hermitian matrices on `ℂ^I`). -/
theorem lemmaS (W : Weight) (Q : ℝ) (hQ : 0 < Q) (I : Finset ℤ) :
    (Tplus W Q I - TΩ W Q I).PosSemidef ∧ (Tnat W Q I - Tplus W Q I).PosSemidef ∧
      (Tplus W Q I).PosSemidef ∧ (Tnat W Q I).PosSemidef := by
  have h1 : ∀ e ∈ levels Q, aΩ W Q e ≤ aΩplus W Q e := fun e _ => le_max_left _ _
  have h2 : ∀ e ∈ levels Q, aΩplus W Q e ≤ aNat W Q e := by
    intro e he
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    have hb := lemOmega_b W Q hQ e he1
    have hm := mfun_nonneg W ((e : ℝ) / Q)
    simp only [aΩplus, aNat]
    rcases le_total (Ωlev W Q e) 0 with h | h
    · rw [max_eq_right h]; rw [max_eq_left (neg_nonneg.mpr h)] at hb; linarith
    · rw [max_eq_left h]; linarith
  have h0 : ∀ e ∈ levels Q, 0 ≤ aΩplus W Q e := fun e _ => le_max_right _ _
  exact ⟨toeplitz_mono _ _ _ h1 I, toeplitz_mono _ _ _ h2 I, toeplitz_posSemidef _ _ h0 I,
    toeplitz_posSemidef _ _ (fun e he => (h0 e he).trans (h2 e he)) I⟩

/-- **`lem:S`, form version.** `∫|S_y|²dμ_Ω ≤ ∫|S_y|²dμ_Ω^+ ≤ ∫|S_y|²dμ^♮` for every `y`. -/
theorem lemmaS_forms (W : Weight) (Q : ℝ) (hQ : 0 < Q) (I : Finset ℤ) (y : ℤ → ℂ) :
    levelForm (levels Q) (aΩ W Q) I y ≤ levelForm (levels Q) (aΩplus W Q) I y ∧
      levelForm (levels Q) (aΩplus W Q) I y ≤ levelForm (levels Q) (aNat W Q) I y := by
  have h1 : ∀ e ∈ levels Q, aΩ W Q e ≤ aΩplus W Q e := fun e _ => le_max_left _ _
  have h2 : ∀ e ∈ levels Q, aΩplus W Q e ≤ aNat W Q e := by
    intro e he
    have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
    have hb := lemOmega_b W Q hQ e he1
    have hm := mfun_nonneg W ((e : ℝ) / Q)
    simp only [aΩplus, aNat]
    rcases le_total (Ωlev W Q e) 0 with h | h
    · rw [max_eq_right h]; rw [max_eq_left (neg_nonneg.mpr h)] at hb; linarith
    · rw [max_eq_left h]; linarith
  exact ⟨levelForm_mono _ _ _ h1 I y, levelForm_mono _ _ _ h2 I y⟩

end Families
