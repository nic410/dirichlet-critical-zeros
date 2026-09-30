/-
# Zero side: deletion of the exterior zeros, per character (paper §4.5)

For a primitive `χ` mod `q > 1` and `T > 0`: `Ĝ_χ = Â_χ + Ê_χ` with `Â_χ` the normalised interior
matrix (zeros with ordinate in `(T, 2T]`) and `∑_{k,l} |Ê_{χ,kl}| ≤ ε̂_χ`, the normalised exterior
mass (`ext_entry_bound`). Consequently (`perchi_ext`), with `Y_χ = 4 tr Ĝ_χ − ‖Ĝ_χ‖_F²` and
`X_χ = 4 ε̂ + 2 ‖Ĝ‖_F ε̂ + ε̂²`:

`Y − 2N_χ − X ≤ N^s_{0,χ}`, `Y − 2N_χ − X ≤ N^*_{0,χ}`, `(Y − N_χ − X)/2 ≤ N_{d,χ}`,

and, for every `χ`, `Y_χ ≤ 4 |K_J|` (`diag_bound`).
-/
import Families.Ported.Zero.Blocks
import Families.Ported.Zero.Exterior
import Families.Ported.Zero.Envelope

noncomputable section

open scoped BigOperators ComplexConjugate
open Complex Set Matrix Finset RHLinalg

namespace Families.Ported.Zero

open Zeta23 Zeta23.ThmE

/-! ### Linear algebra -/

section LinAlg

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma frobSq_eq_sum (A : Matrix ι ι ℂ) : frobSq A = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  unfold frobSq
  rw [Matrix.trace, map_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.conjTranspose_apply]
  simp only [RCLike.re_to_complex]
  rw [show star (A j i) * A j i = ((‖A j i‖ ^ 2 : ℝ) : ℂ) by
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]]
  rw [Complex.ofReal_re]

lemma rtrace_eq_sum (A : Matrix ι ι ℂ) : rtrace A = ∑ i, (A i i).re := by
  unfold rtrace
  rw [Matrix.trace, map_sum]
  rfl

/-- `4 tr A − ‖A‖_F² ≤ 4 · #ι` (only the diagonal is used: `4x − x² ≤ 4`). -/
lemma diag_bound (A : Matrix ι ι ℂ) : 4 * rtrace A - frobSq A ≤ 4 * (Fintype.card ι : ℝ) := by
  rw [rtrace_eq_sum, frobSq_eq_sum]
  have h1 : ∀ i, ‖A i i‖ ^ 2 ≤ ∑ j, ‖A i j‖ ^ 2 := fun i =>
    Finset.single_le_sum (f := fun j => ‖A i j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 : ∀ i, 4 * (A i i).re - ∑ j, ‖A i j‖ ^ 2 ≤ 4 := by
    intro i
    have := h1 i
    have h3 : (A i i).re ^ 2 ≤ ‖A i i‖ ^ 2 := by
      have := Complex.abs_re_le_norm (A i i)
      nlinarith [abs_nonneg (A i i).re, sq_abs (A i i).re]
    nlinarith [sq_nonneg ((A i i).re - 2)]
  calc 4 * ∑ i, (A i i).re - ∑ i, ∑ j, ‖A i j‖ ^ 2 = ∑ i, (4 * (A i i).re - ∑ j, ‖A i j‖ ^ 2) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    _ ≤ ∑ _i : ι, (4 : ℝ) := Finset.sum_le_sum fun i _ => h2 i
    _ = 4 * (Fintype.card ι : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]; ring

/-- Deletion: if `∑_{i,j} |(G − A)_{ij}| ≤ ε`, then
`4 tr A − ‖A‖² ≥ 4 tr G − ‖G‖² − (4ε + 2‖G‖_F ε + ε²)`. -/
lemma deletion (G A : Matrix ι ι ℂ) {ε : ℝ} (hε : ∑ i, ∑ j, ‖G i j - A i j‖ ≤ ε) :
    4 * rtrace G - frobSq G - (4 * ε + 2 * Real.sqrt (frobSq G) * ε + ε ^ 2) ≤
      4 * rtrace A - frobSq A := by
  set E : Matrix ι ι ℂ := G - A with hE
  have hε0 : 0 ≤ ε := le_trans (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    norm_nonneg _) hε
  have hEε : ∑ i, ∑ j, ‖E i j‖ ≤ ε := hε
  -- trace
  have htr : rtrace G - rtrace A ≤ ε := by
    rw [rtrace_eq_sum, rtrace_eq_sum, ← Finset.sum_sub_distrib]
    calc ∑ i, ((G i i).re - (A i i).re) ≤ ∑ i, ‖E i i‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          have : (G i i).re - (A i i).re = (E i i).re := by simp [hE]
          rw [this]; exact (Complex.re_le_norm _)
      _ ≤ ∑ i, ∑ j, ‖E i j‖ := Finset.sum_le_sum fun i _ =>
          Finset.single_le_sum (f := fun j => ‖E i j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
      _ ≤ ε := hEε
  -- Frobenius
  have hF : frobSq A ≤ frobSq G + 2 * Real.sqrt (frobSq G) * ε + ε ^ 2 := by
    rw [frobSq_eq_sum, frobSq_eq_sum]
    set F := ∑ i, ∑ j, ‖G i j‖ ^ 2 with hFdef
    have hF0 : 0 ≤ F := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hGle : ∀ i j, ‖G i j‖ ≤ Real.sqrt F := by
      intro i j
      apply Real.le_sqrt_of_sq_le
      calc ‖G i j‖ ^ 2 ≤ ∑ j', ‖G i j'‖ ^ 2 :=
            Finset.single_le_sum (f := fun j' => ‖G i j'‖ ^ 2) (fun _ _ => sq_nonneg _)
              (Finset.mem_univ j)
        _ ≤ F := Finset.single_le_sum (f := fun i' => ∑ j', ‖G i' j'‖ ^ 2)
              (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    have hA : ∀ i j, ‖A i j‖ ^ 2 ≤ ‖G i j‖ ^ 2 + 2 * Real.sqrt F * ‖E i j‖ + ‖E i j‖ ^ 2 := by
      intro i j
      have hAij : A i j = G i j - E i j := by simp [hE]
      have h1 : ‖A i j‖ ≤ ‖G i j‖ + ‖E i j‖ := by rw [hAij]; exact norm_sub_le _ _
      have h2 := hGle i j
      have h3 := norm_nonneg (A i j)
      have h4 := norm_nonneg (E i j)
      have h5 := norm_nonneg (G i j)
      nlinarith
    have hS2 : ∑ i, ∑ j, ‖E i j‖ ^ 2 ≤ ε ^ 2 := by
      set S := ∑ i, ∑ j, ‖E i j‖ with hSdef
      have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
      have hle : ∀ i j, ‖E i j‖ ≤ S := by
        intro i j
        calc ‖E i j‖ ≤ ∑ j', ‖E i j'‖ :=
              Finset.single_le_sum (f := fun j' => ‖E i j'‖) (fun _ _ => norm_nonneg _)
                (Finset.mem_univ j)
          _ ≤ S := Finset.single_le_sum (f := fun i' => ∑ j', ‖E i' j'‖)
                (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
      have : ∑ i, ∑ j, ‖E i j‖ ^ 2 ≤ ∑ i, ∑ j, ‖E i j‖ * S :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
          rw [sq]; exact mul_le_mul_of_nonneg_left (hle i j) (norm_nonneg _)
      have e : ∑ i, ∑ j, ‖E i j‖ * S = S * S := by
        rw [hSdef, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]
      rw [e] at this
      nlinarith
    calc ∑ i, ∑ j, ‖A i j‖ ^ 2
        ≤ ∑ i, ∑ j, (‖G i j‖ ^ 2 + 2 * Real.sqrt F * ‖E i j‖ + ‖E i j‖ ^ 2) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hA i j
      _ = F + 2 * Real.sqrt F * ∑ i, ∑ j, ‖E i j‖ + ∑ i, ∑ j, ‖E i j‖ ^ 2 := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum, hFdef]
      _ ≤ F + 2 * Real.sqrt F * ε + ε ^ 2 := by
          have := mul_le_mul_of_nonneg_left hEε (by positivity : (0:ℝ) ≤ 2 * Real.sqrt F)
          linarith
  linarith

end LinAlg

variable (P : PrimeSetup)

/-! ### The normalised Gabor matrix and the interior part -/

/-- `Ĝ_χ = G_χ/(aL²)` (as in `P.Mfrak`). -/
def Ghat (Q T τ₀ : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Matrix (P.KJ Q T τ₀) (P.KJ Q T τ₀) ℂ :=
  fun k l => P.Gabor Q T τ₀ χ k l / (P.aInt * P.L Q ^ 2)

lemma Mfrak_eq (W : Weight) (Q T τ₀ : ℝ) :
    P.Mfrak W Q T τ₀ = famSum W Q (fun _ χ => frobSq (Ghat P Q T τ₀ χ)) := by
  unfold PrimeSetup.Mfrak
  congr 1; funext q χ
  rw [frobSq_eq_sum]
  rfl

/-- `u(z) = (p_k(z))_{k ∈ K_J}`. -/
def uvec (Q T τ₀ : ℝ) : ℂ → P.KJ Q T τ₀ → ℂ := fun z k => P.pk Q τ₀ k z

lemma uvec_conj (Q T τ₀ : ℝ) (z : ℂ) : uvec P Q T τ₀ (conj z) = star (uvec P Q T τ₀ z) := by
  funext k
  simp only [uvec, Pi.star_apply, RCLike.star_def]
  exact pk_conj P Q τ₀ k z

lemma uvec_bessel {Q : ℝ} (hQ : 1 < Q) (T τ₀ : ℝ) (t : ℝ) :
    ∑ k, ‖uvec P Q T τ₀ (t : ℂ) k‖ ^ 2 ≤ P.aInt * P.L Q ^ 2 := by
  have := bessel P hQ τ₀ (P.KJ Q T τ₀) t
  rw [← Finset.sum_coe_sort] at this
  exact this

/-- `Â_χ = A_χ/(aL²)`. -/
def Ahat (Q T τ₀ : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Matrix (P.KJ Q T τ₀) (P.KJ Q T τ₀) ℂ :=
  (((P.aInt * P.L Q ^ 2)⁻¹ : ℝ) : ℂ) • Aint (uvec P Q T τ₀) χ T

/-! ### The exterior part -/

section Ext

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- The Gabor entry splits into the interior (finite) part and the exterior series. -/
lemma gabor_split {Q : ℝ} (hQ : 1 < Q) (τ₀ : ℝ) (hq : 1 < q) (hprim : χ.IsPrimitive) {T : ℝ}
    (hT : 0 < T) (k l : ℤ)
    (hsumE : Summable (fun ρ : {ρ : ℂ // ρ ∈ PrimeSetup.strip χ ∧ ρ.im ∉ Set.Ioc T (2 * T)} =>
      gaborTerm P Q τ₀ χ k l ρ)) :
    ∑' ρ : PrimeSetup.strip χ, gaborTerm P Q τ₀ χ k l ρ =
      ∑ ρ ∈ zerosFin hq hprim hT, gaborTerm P Q τ₀ χ k l ρ +
        ∑' ρ : {ρ : ℂ // ρ ∈ PrimeSetup.strip χ ∧ ρ.im ∉ Set.Ioc T (2 * T)},
          gaborTerm P Q τ₀ χ k l ρ := by
  set f : ℂ → ℂ := fun ρ => gaborTerm P Q τ₀ χ k l ρ with hf
  set SE : Set ℂ := {ρ | ρ ∈ PrimeSetup.strip χ ∧ ρ.im ∉ Set.Ioc T (2 * T)} with hSE
  have hsI : zerosI χ T = {ρ | ρ ∈ PrimeSetup.strip χ ∧ ρ.im ∈ Set.Ioc T (2 * T)} := by
    ext ρ
    constructor
    · intro h
      have h' := h
      rw [zerosI_eq hq hprim hT.le] at h'
      exact ⟨by rw [strip_eq]; exact h'.1, h.2.1, h.2.2⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1.1, h2, h3⟩
  have hunion : PrimeSetup.strip χ = zerosI χ T ∪ SE := by
    rw [hsI]; ext ρ
    simp only [Set.mem_union, Set.mem_setOf_eq, hSE]
    tauto
  have hdisj : Disjoint (zerosI χ T) SE := by
    rw [hsI, Set.disjoint_left]
    rintro ρ ⟨_, h⟩ ⟨_, h'⟩
    exact h' h
  have hSEsum : Summable (SE.indicator f) := by
    rw [← summable_subtype_iff_indicator]
    exact hsumE
  have hIsum : Summable ((zerosI χ T).indicator f) := by
    apply summable_of_ne_finset_zero (s := zerosFin hq hprim hT)
    intro b hb
    rw [mem_zerosFin] at hb
    exact Set.indicator_of_notMem hb _
  have hind : (PrimeSetup.strip χ).indicator f = fun x =>
      (zerosI χ T).indicator f x + SE.indicator f x := by
    rw [hunion, Set.indicator_union_of_disjoint hdisj]
  rw [tsum_subtype (PrimeSetup.strip χ) f, hind, Summable.tsum_add hIsum hSEsum]
  congr 1
  · rw [tsum_eq_sum (s := zerosFin hq hprim hT)]
    · refine Finset.sum_congr rfl fun ρ hρ => ?_
      exact Set.indicator_of_mem ((mem_zerosFin hq hprim hT).mp hρ) _
    · intro b hb
      rw [mem_zerosFin] at hb
      exact Set.indicator_of_notMem hb _
  · rw [← tsum_subtype SE f]
    rfl

lemma Aint_apply (hq : 1 < q) (hprim : χ.IsPrimitive) {T : ℝ} (hT : 0 < T) (Q τ₀ : ℝ)
    (k l : P.KJ Q T τ₀) :
    Aint (uvec P Q T τ₀) χ T k l = ∑ ρ ∈ zerosFin hq hprim hT, gaborTerm P Q τ₀ χ k l ρ := by
  unfold Aint
  rw [finsum_mem_eq_finite_toFinset_sum _ (zerosI_finite hq hprim hT.le)]
  rw [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, uvec, gaborTerm, smul_eq_mul]
  ring

/-- `∑_{k,l} |Ĝ_{kl} − Â_{kl}| ≤ ε̂_χ`, the normalised exterior mass. -/
theorem ext_entry_bound {Q : ℝ} (hQ : 1 < Q) (τ₀ : ℝ) (hq : 1 < q) (hprim : χ.IsPrimitive)
    {T : ℝ} (hT : 0 < T) (hsum : Summable (extTerm P Q T τ₀ χ)) :
    ∑ k, ∑ l, ‖Ghat P Q T τ₀ χ k l - Ahat P Q T τ₀ χ k l‖ ≤
      (∑' ρ, extTerm P Q T τ₀ χ ρ) / (P.aInt * P.L Q ^ 2) := by
  set c : ℝ := P.aInt * P.L Q ^ 2 with hc
  have hc0 : 0 < c := by have := aInt_pos P; have := L_pos P hQ; positivity
  -- pointwise bound of the exterior terms
  have hterm : ∀ (k l : P.KJ Q T τ₀) (ρ : {ρ : ℂ // ρ ∈ PrimeSetup.strip χ ∧
      ρ.im ∉ Set.Ioc T (2 * T)}), ‖gaborTerm P Q τ₀ χ k l ρ‖ =
        (mult χ ρ : ℝ) * (‖P.pk Q τ₀ k (zOf ρ)‖ * ‖P.pk Q τ₀ l (zOf ρ)‖) := by
    intro k l ρ
    simp only [gaborTerm, norm_mul, Complex.norm_natCast]
    ring
  have hext : ∀ ρ : {ρ : ℂ // ρ ∈ PrimeSetup.strip χ ∧ ρ.im ∉ Set.Ioc T (2 * T)},
      extTerm P Q T τ₀ χ ρ = ∑ k : P.KJ Q T τ₀, ∑ l : P.KJ Q T τ₀,
        (mult χ ρ : ℝ) * (‖P.pk Q τ₀ k (zOf ρ)‖ * ‖P.pk Q τ₀ l (zOf ρ)‖) := by
    intro ρ
    unfold extTerm
    rw [← Finset.sum_coe_sort (P.KJ Q T τ₀), sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
  have hle : ∀ (k l : P.KJ Q T τ₀) (ρ : {ρ : ℂ // ρ ∈ PrimeSetup.strip χ ∧
      ρ.im ∉ Set.Ioc T (2 * T)}), ‖gaborTerm P Q τ₀ χ k l ρ‖ ≤ extTerm P Q T τ₀ χ ρ := by
    intro k l ρ
    rw [hterm, hext]
    have hnn : ∀ (k' l' : P.KJ Q T τ₀), 0 ≤ (mult χ ρ : ℝ) *
        (‖P.pk Q τ₀ k' (zOf ρ)‖ * ‖P.pk Q τ₀ l' (zOf ρ)‖) := fun _ _ => by positivity
    calc (mult χ ρ : ℝ) * (‖P.pk Q τ₀ k (zOf ρ)‖ * ‖P.pk Q τ₀ l (zOf ρ)‖)
        ≤ ∑ l' : P.KJ Q T τ₀, (mult χ ρ : ℝ) * (‖P.pk Q τ₀ k (zOf ρ)‖ * ‖P.pk Q τ₀ l' (zOf ρ)‖) :=
          Finset.single_le_sum (f := fun l' : P.KJ Q T τ₀ => (mult χ ρ : ℝ) *
            (‖P.pk Q τ₀ k (zOf ρ)‖ * ‖P.pk Q τ₀ l' (zOf ρ)‖)) (fun l' _ => hnn k l')
            (Finset.mem_univ l)
      _ ≤ _ := Finset.single_le_sum (f := fun k' : P.KJ Q T τ₀ => ∑ l' : P.KJ Q T τ₀,
            (mult χ ρ : ℝ) * (‖P.pk Q τ₀ k' (zOf ρ)‖ * ‖P.pk Q τ₀ l' (zOf ρ)‖))
            (fun k' _ => Finset.sum_nonneg fun l' _ => hnn k' l') (Finset.mem_univ k)
  have hsumN : ∀ k l : P.KJ Q T τ₀, Summable (fun ρ : {ρ : ℂ // ρ ∈ PrimeSetup.strip χ ∧
      ρ.im ∉ Set.Ioc T (2 * T)} => ‖gaborTerm P Q τ₀ χ k l ρ‖) := fun k l =>
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (hle k l) hsum
  have hkl : ∀ k l : P.KJ Q T τ₀, ‖Ghat P Q T τ₀ χ k l - Ahat P Q T τ₀ χ k l‖ ≤
      (∑' ρ : {ρ : ℂ // ρ ∈ PrimeSetup.strip χ ∧ ρ.im ∉ Set.Ioc T (2 * T)},
        ‖gaborTerm P Q τ₀ χ k l ρ‖) / c := by
    intro k l
    have hsplit := gabor_split P hQ τ₀ hq hprim hT k l (hsumN k l).of_norm
    have hG : Ghat P Q T τ₀ χ k l - Ahat P Q T τ₀ χ k l =
        (∑' ρ : {ρ : ℂ // ρ ∈ PrimeSetup.strip χ ∧ ρ.im ∉ Set.Ioc T (2 * T)},
          gaborTerm P Q τ₀ χ k l ρ) / (c : ℂ) := by
      simp only [Ghat, Ahat, Matrix.smul_apply, smul_eq_mul]
      rw [gabor_apply, hsplit, Aint_apply P hq hprim hT Q τ₀ k l]
      rw [hc]; push_cast
      field_simp
      ring
    rw [hG, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
    exact div_le_div_of_nonneg_right (norm_tsum_le_tsum_norm (hsumN k l)) hc0.le
  calc ∑ k, ∑ l, ‖Ghat P Q T τ₀ χ k l - Ahat P Q T τ₀ χ k l‖
      ≤ ∑ k : P.KJ Q T τ₀, ∑ l : P.KJ Q T τ₀,
          (∑' ρ : {ρ : ℂ // ρ ∈ PrimeSetup.strip χ ∧ ρ.im ∉ Set.Ioc T (2 * T)},
            ‖gaborTerm P Q τ₀ χ k l ρ‖) / c :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hkl k l
    _ = (∑ k : P.KJ Q T τ₀, ∑ l : P.KJ Q T τ₀,
          ∑' ρ : {ρ : ℂ // ρ ∈ PrimeSetup.strip χ ∧ ρ.im ∉ Set.Ioc T (2 * T)},
            ‖gaborTerm P Q τ₀ χ k l ρ‖) / c := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_div]
    _ = (∑' ρ : {ρ : ℂ // ρ ∈ PrimeSetup.strip χ ∧ ρ.im ∉ Set.Ioc T (2 * T)},
          ∑ k : P.KJ Q T τ₀, ∑ l : P.KJ Q T τ₀, ‖gaborTerm P Q τ₀ χ k l ρ‖) / c := by
        congr 1
        rw [Summable.tsum_finsetSum (fun k _ => summable_sum fun l _ => hsumN k l)]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Summable.tsum_finsetSum (fun l _ => hsumN k l)]
    _ = (∑' ρ, extTerm P Q T τ₀ χ ρ) / c := by
        congr 1
        refine tsum_congr fun ρ => ?_
        rw [hext]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
        exact hterm k l ρ

/-- **`prop:perchi` with the exterior part** (paper §4.5, first display of the proof of
`prop:zero`): with `Y = 4 tr Ĝ − ‖Ĝ‖²`, `X = 4ε + 2‖Ĝ‖_F ε + ε²` and `∑_{kl} |Ĝ − Â| ≤ ε`. -/
theorem perchi_ext {Q : ℝ} (hQ : 1 < Q) (τ₀ : ℝ) (hq : 1 < q) (hprim : χ.IsPrimitive)
    {T : ℝ} (hT : 0 < T) {ε : ℝ}
    (hε : ∑ k, ∑ l, ‖Ghat P Q T τ₀ χ k l - Ahat P Q T τ₀ χ k l‖ ≤ ε) :
    let Y := 4 * rtrace (Ghat P Q T τ₀ χ) - frobSq (Ghat P Q T τ₀ χ)
    let X := 4 * ε + 2 * Real.sqrt (frobSq (Ghat P Q T τ₀ χ)) * ε + ε ^ 2
    Y - 2 * (Nchi χ T : ℝ) - X ≤ Ns0chi χ T ∧ Y - 2 * (Nchi χ T : ℝ) - X ≤ Nstar0chi χ T ∧
      (Y - Nchi χ T - X) / 2 ≤ Ndchi χ T := by
  intro Y X
  have hdel := deletion (Ghat P Q T τ₀ χ) (Ahat P Q T τ₀ χ) hε
  have hc : 0 < P.aInt * P.L Q ^ 2 := by have := aInt_pos P; have := L_pos P hQ; positivity
  have hpc := perchi_interior hq hprim hT (uvec P Q T τ₀) (uvec_conj P Q T τ₀) hc
    (uvec_bessel P hQ T τ₀)
  simp only at hpc
  have hA : ((((P.aInt * P.L Q ^ 2)⁻¹ : ℝ)) : ℂ) • Aint (uvec P Q T τ₀) χ T = Ahat P Q T τ₀ χ := rfl
  rw [hA] at hpc
  obtain ⟨h1, h2, h3⟩ := hpc
  refine ⟨by linarith, by linarith, by linarith⟩

end Ext

end Families.Ported.Zero
