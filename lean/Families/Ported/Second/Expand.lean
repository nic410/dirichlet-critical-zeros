/-
# Prime side (paper §5): the decomposition `eq:split` of `𝓜`

`Mcal_split`: `𝓜 = M_{μμ} + 2 M_{μΛ} + (1/2π²)(Re ∑ a_n a_m Δ(n,m) 𝒦(n,m) + Re SSC)`
(`eq:split`, display (5.1): `𝓜 = M_{μμ} + 2M_{μΛ} + M^{rat}_{ΛΛ} + M^{ss}_{ΛΛ}`).
-/
import Families.Ported.Second.Common

noncomputable section

open scoped BigOperators ComplexConjugate ContDiff
open Finset MeasureTheory Filter Topology

namespace Families.Ported.Second

open Families

/-! ### Double integrals of continuous functions over `J × J` -/

section DInt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

lemma cont_setIntegral_Icc {F : ℝ → ℝ → E} (hF : Continuous (Function.uncurry F)) (a b : ℝ) :
    Continuous (fun t => ∫ t' in Set.Icc a b, F t t') :=
  continuous_parametric_integral_of_continuous hF isCompact_Icc

lemma intOn_Icc_inner {F : ℝ → ℝ → E} (hF : Continuous (Function.uncurry F)) (a b t : ℝ) :
    IntegrableOn (fun t' => F t t') (Set.Icc a b) :=
  (hF.comp (continuous_const.prodMk continuous_id)).integrableOn_Icc

lemma intOn_Icc_outer {F : ℝ → ℝ → E} (hF : Continuous (Function.uncurry F)) (a b : ℝ) :
    IntegrableOn (fun t => ∫ t' in Set.Icc a b, F t t') (Set.Icc a b) :=
  (cont_setIntegral_Icc hF a b).integrableOn_Icc

lemma dint_add {F G : ℝ → ℝ → E} (hF : Continuous (Function.uncurry F))
    (hG : Continuous (Function.uncurry G)) (a b : ℝ) :
    ∫ t in Set.Icc a b, ∫ t' in Set.Icc a b, (F t t' + G t t') =
      (∫ t in Set.Icc a b, ∫ t' in Set.Icc a b, F t t') +
        ∫ t in Set.Icc a b, ∫ t' in Set.Icc a b, G t t' := by
  have h1 : ∀ t, ∫ t' in Set.Icc a b, (F t t' + G t t') =
      (∫ t' in Set.Icc a b, F t t') + ∫ t' in Set.Icc a b, G t t' := fun t =>
    integral_add (intOn_Icc_inner hF a b t) (intOn_Icc_inner hG a b t)
  simp_rw [h1]
  exact integral_add (intOn_Icc_outer hF a b) (intOn_Icc_outer hG a b)

lemma integrable_prod_Icc {F : ℝ × ℝ → E} (hF : Continuous F) (a b : ℝ) :
    Integrable F ((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc a b))) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)

lemma dint_swap {F : ℝ → ℝ → E} (hF : Continuous (Function.uncurry F)) (a b : ℝ) :
    ∫ t in Set.Icc a b, ∫ t' in Set.Icc a b, F t t' =
      ∫ t in Set.Icc a b, ∫ t' in Set.Icc a b, F t' t :=
  integral_integral_swap (integrable_prod_Icc hF a b)

lemma dint_finsetSum {ι : Type*} (s : Finset ι) {F : ι → ℝ → ℝ → E}
    (hF : ∀ i ∈ s, Continuous (Function.uncurry (F i))) (a b : ℝ) :
    ∫ t in Set.Icc a b, ∫ t' in Set.Icc a b, ∑ i ∈ s, F i t t' =
      ∑ i ∈ s, ∫ t in Set.Icc a b, ∫ t' in Set.Icc a b, F i t t' := by
  have h1 : ∀ t, ∫ t' in Set.Icc a b, ∑ i ∈ s, F i t t' =
      ∑ i ∈ s, ∫ t' in Set.Icc a b, F i t t' := fun t =>
    integral_finsetSum s fun i hi => intOn_Icc_inner (hF i hi) a b t
  simp_rw [h1]
  exact integral_finsetSum s fun i hi => intOn_Icc_outer (hF i hi) a b

lemma dint_const_mul {F : ℝ → ℝ → ℂ} (c : ℂ) (a b : ℝ) :
    ∫ t in Set.Icc a b, ∫ t' in Set.Icc a b, c * F t t' =
      c * ∫ t in Set.Icc a b, ∫ t' in Set.Icc a b, F t t' := by
  have h1 : ∀ t, ∫ t' in Set.Icc a b, c * F t t' = c * ∫ t' in Set.Icc a b, F t t' :=
    fun t => integral_const_mul c _
  simp_rw [h1]
  exact integral_const_mul c _

end DInt

/-! ### The bilinear form `K₂(f, g) = ∬_{J²} Φ(t−t')² f(t) g(t')` -/

section K2

variable (P : PrimeSetup)

/-- `K₂(f, g) = ∬_{J²} Φ(t−t')² f(t) g(t') dt dt'`. -/
def K2 (Q T : ℝ) (f g : ℝ → ℝ) : ℝ :=
  ∫ t in P.J T, ∫ t' in P.J T, PhiSq P Q (t - t') * f t * g t'

variable {P}

lemma K2_cont {Q : ℝ} (hQ : 1 < Q) {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Continuous (Function.uncurry fun t t' => PhiSq P Q (t - t') * f t * g t') :=
  (((PhiSq_continuous P hQ).comp (continuous_fst.sub continuous_snd)).mul
    (hf.comp continuous_fst)).mul (hg.comp continuous_snd)

lemma K2_add_left {Q : ℝ} (hQ : 1 < Q) (T : ℝ) {f₁ f₂ g : ℝ → ℝ} (h₁ : Continuous f₁)
    (h₂ : Continuous f₂) (hg : Continuous g) :
    K2 P Q T (f₁ + f₂) g = K2 P Q T f₁ g + K2 P Q T f₂ g := by
  unfold K2 PrimeSetup.J
  rw [← dint_add (K2_cont hQ h₁ hg) (K2_cont hQ h₂ hg)]
  congr 1; funext t; congr 1; funext t'
  simp only [Pi.add_apply]; ring

lemma K2_add_right {Q : ℝ} (hQ : 1 < Q) (T : ℝ) {f g₁ g₂ : ℝ → ℝ} (hf : Continuous f)
    (h₁ : Continuous g₁) (h₂ : Continuous g₂) :
    K2 P Q T f (g₁ + g₂) = K2 P Q T f g₁ + K2 P Q T f g₂ := by
  unfold K2 PrimeSetup.J
  rw [← dint_add (K2_cont hQ hf h₁) (K2_cont hQ hf h₂)]
  congr 1; funext t; congr 1; funext t'
  simp only [Pi.add_apply]; ring

lemma K2_symm {Q : ℝ} (hQ : 1 < Q) (T : ℝ) {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    K2 P Q T f g = K2 P Q T g f := by
  unfold K2 PrimeSetup.J
  rw [dint_swap (K2_cont hQ hf hg)]
  congr 1; funext t; congr 1; funext t'
  rw [show t' - t = -(t - t') by ring, PhiSq_neg]; ring

end K2

/-! ### The ratio and same-sign parts of `∑_χ ω_χ K₂(P_χ, P_χ)` -/

section PP

variable (P : PrimeSetup)

lemma natCast_cpow_conj (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    conj ((n : ℂ) ^ (-(Complex.I * t))) = (n : ℂ) ^ (Complex.I * t) := by
  rw [PrimeSetup.natCast_cpow n hn, PrimeSetup.natCast_cpow n hn, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
  ring

lemma conj_Schi {q : ℕ} (χ : DirichletCharacter ℂ q) (Q t : ℝ) :
    conj (P.Schi χ Q (P.aVec Q) t) =
      ∑ m ∈ P.range Q, (P.aVec Q m : ℂ) * conj (χ m) * (m : ℂ) ^ (Complex.I * t) := by
  unfold PrimeSetup.Schi
  rw [map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm1 := (SC.mem_range_le P hm).1
  rw [map_mul, map_mul, Complex.conj_ofReal, natCast_cpow_conj m hm1]

lemma cpow_cont {n : ℕ} (hn : 1 ≤ n) (s : ℂ) :
    Continuous (fun t : ℝ => (n : ℂ) ^ (s * t)) := by
  have hn0 : 0 < ((n : ℂ)).re := by simp; exact_mod_cast hn
  exact continuous_const.cpow (by fun_prop) fun _ => Or.inl hn0

/-- `∬_{J²} Φ(t−t')² S_χ(t) \overline{S_χ(t')} = ∑_{n,m} a_n a_m χ(n) \bar χ(m) 𝒦(n,m)`. -/
lemma dint_S_conjS {Q : ℝ} (hQ : 1 < Q) (T : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ∫ t in P.J T, ∫ t' in P.J T, (PhiSq P Q (t - t') : ℂ) * P.Schi χ Q (P.aVec Q) t *
        conj (P.Schi χ Q (P.aVec Q) t') =
      ∑ n ∈ P.range Q, ∑ m ∈ P.range Q,
        (P.aVec Q n : ℂ) * P.aVec Q m * (χ n * conj (χ m)) * P.𝒦 Q T n m := by
  have hK : Continuous fun r => (PhiSq P Q r : ℂ) :=
    Complex.continuous_ofReal.comp (PhiSq_continuous P hQ)
  have e : ∀ t t' : ℝ, (PhiSq P Q (t - t') : ℂ) * P.Schi χ Q (P.aVec Q) t *
      conj (P.Schi χ Q (P.aVec Q) t') = ∑ n ∈ P.range Q, ∑ m ∈ P.range Q,
        (P.aVec Q n : ℂ) * P.aVec Q m * (χ n * conj (χ m)) *
          (P.Φ Q (t - t') ^ 2 * (n : ℂ) ^ (-(Complex.I * t)) * (m : ℂ) ^ (Complex.I * t')) := by
    intro t t'
    rw [conj_Schi, Φ_sq_eq_PhiSq]
    unfold PrimeSetup.Schi
    rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  simp_rw [e]
  unfold PrimeSetup.J
  rw [dint_finsetSum]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [dint_finsetSum]
    · refine Finset.sum_congr rfl fun m hm => ?_
      have hi : ∀ t, ∫ t' in Set.Icc ((1 + P.θ) * T) ((2 - P.θ) * T),
          (P.aVec Q n : ℂ) * P.aVec Q m * (χ n * conj (χ m)) *
            (P.Φ Q (t - t') ^ 2 * (n : ℂ) ^ (-(Complex.I * t)) * (m : ℂ) ^ (Complex.I * t')) =
          (P.aVec Q n : ℂ) * P.aVec Q m * (χ n * conj (χ m)) *
            ∫ t' in Set.Icc ((1 + P.θ) * T) ((2 - P.θ) * T),
              P.Φ Q (t - t') ^ 2 * (n : ℂ) ^ (-(Complex.I * t)) * (m : ℂ) ^ (Complex.I * t') :=
        fun t => integral_const_mul _ _
      simp_rw [hi]
      rw [integral_const_mul]
      rfl
    · intro m hm
      have hm1 := (SC.mem_range_le P hm).1
      have hn1 := (SC.mem_range_le P hn).1
      have h1 := cpow_cont hn1 (-Complex.I)
      have h2 := cpow_cont hm1 Complex.I
      refine continuous_const.mul ((((P.Φ_sq_continuous hQ).comp
        (continuous_fst.sub continuous_snd)).mul ?_).mul ?_)
      · refine (h1.comp continuous_fst).congr fun z => ?_
        simp only [Function.comp, neg_mul]
      · exact h2.comp continuous_snd
  · intro n hn
    have hn1 := (SC.mem_range_le P hn).1
    refine continuous_finsetSum _ fun m hm => ?_
    have hm1 := (SC.mem_range_le P hm).1
    have h1 := cpow_cont hn1 (-Complex.I)
    have h2 := cpow_cont hm1 Complex.I
    refine continuous_const.mul ((((P.Φ_sq_continuous hQ).comp
      (continuous_fst.sub continuous_snd)).mul ?_).mul ?_)
    · refine (h1.comp continuous_fst).congr fun z => ?_
      simp only [Function.comp, neg_mul]
    · exact h2.comp continuous_snd

/-- `∑_χ ω_χ ∬ Φ² S \bar S' = ∑_{n,m} a_n a_m Δ(n,m) 𝒦(n,m)` (the ratio form). -/
lemma famSum_S_conjS {Q : ℝ} (hQ : 1 < Q) (W : Weight) (T : ℝ) :
    ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (W.omega Q q : ℂ) * ∑ χ ∈ primChars q,
      ∫ t in P.J T, ∫ t' in P.J T, (PhiSq P Q (t - t') : ℂ) * P.Schi χ Q (P.aVec Q) t *
        conj (P.Schi χ Q (P.aVec Q) t') = P.ratioForm W Q T (P.aVec Q) := by
  simp_rw [dint_S_conjS P hQ T]
  unfold PrimeSetup.ratioForm Δ
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  -- LHS: ∑_q ∑_χ ∑_n ∑_m;  RHS: ∑_n ∑_m ∑_q ∑_χ
  have stepA : ∀ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∀ F : DirichletCharacter ℂ q → ℕ → ℕ → ℂ,
      ∑ χ ∈ primChars q, ∑ n ∈ P.range Q, ∑ m ∈ P.range Q, F χ n m =
        ∑ n ∈ P.range Q, ∑ m ∈ P.range Q, ∑ χ ∈ primChars q, F χ n m := by
    intro q _ F
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun q hq => stepA q hq _]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  refine Finset.sum_congr rfl fun q _ => ?_
  refine Finset.sum_congr rfl fun χ _ => ?_
  simp only [Int.cast_natCast]
  ring

variable {P}

lemma PChi_eq (Q : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) :
    (PChi P Q χ t : ℂ) = -(1 / (2 * Real.pi)) *
      (P.Schi χ Q (P.aVec Q) t + conj (P.Schi χ Q (P.aVec Q) t)) := by
  unfold PChi
  rw [Complex.ofReal_mul, Complex.re_eq_add_conj]
  push_cast
  ring

/-- `K₂(P_χ, P_χ) = (1/2π²)(Re ∬ Φ² S S' + Re ∬ Φ² S \bar S')`. -/
lemma K2_PP {Q : ℝ} (hQ : 1 < Q) (T : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    K2 P Q T (PChi P Q χ) (PChi P Q χ) = 1 / (2 * Real.pi ^ 2) *
      ((∫ t in P.J T, ∫ t' in P.J T, (PhiSq P Q (t - t') : ℂ) * P.Schi χ Q (P.aVec Q) t *
          P.Schi χ Q (P.aVec Q) t').re +
       (∫ t in P.J T, ∫ t' in P.J T, (PhiSq P Q (t - t') : ℂ) * P.Schi χ Q (P.aVec Q) t *
          conj (P.Schi χ Q (P.aVec Q) t')).re) := by
  set S := P.Schi χ Q (P.aVec Q) with hS
  have hSc : Continuous S := Schi_continuous P χ Q _
  have hK : Continuous fun r => (PhiSq P Q r : ℂ) :=
    Complex.continuous_ofReal.comp (PhiSq_continuous P hQ)
  set A := ∫ t in P.J T, ∫ t' in P.J T, (PhiSq P Q (t - t') : ℂ) * S t * S t' with hA
  set B := ∫ t in P.J T, ∫ t' in P.J T, (PhiSq P Q (t - t') : ℂ) * S t * conj (S t') with hB
  have hcont : ∀ f g : ℝ → ℂ, Continuous f → Continuous g →
      Continuous (Function.uncurry fun t t' : ℝ => (PhiSq P Q (t - t') : ℂ) * f t * g t') :=
    fun f g hf hg => ((hK.comp (continuous_fst.sub continuous_snd)).mul
      (hf.comp continuous_fst)).mul (hg.comp continuous_snd)
  have hconjS : Continuous fun t => conj (S t) := Complex.continuous_conj.comp hSc
  -- complexify
  have hK2 : (K2 P Q T (PChi P Q χ) (PChi P Q χ) : ℂ) =
      ∫ t in P.J T, ∫ t' in P.J T, (PhiSq P Q (t - t') : ℂ) * (PChi P Q χ t : ℂ) *
        (PChi P Q χ t' : ℂ) := by
    unfold K2
    rw [← integral_complex_ofReal]
    congr 1; funext t
    rw [← integral_complex_ofReal]
    congr 1; funext t'
    push_cast; ring
  -- expand
  have hexp : ∀ t t' : ℝ, (PhiSq P Q (t - t') : ℂ) * (PChi P Q χ t : ℂ) * (PChi P Q χ t' : ℂ) =
      (1 / (4 * Real.pi ^ 2) : ℂ) * (((PhiSq P Q (t - t') : ℂ) * S t * S t' +
        (PhiSq P Q (t - t') : ℂ) * S t * conj (S t')) +
       ((PhiSq P Q (t - t') : ℂ) * conj (S t) * S t' +
        (PhiSq P Q (t - t') : ℂ) * conj (S t) * conj (S t'))) := by
    intro t t'
    rw [PChi_eq, PChi_eq]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp
    ring
  have hA' : ∫ t in P.J T, ∫ t' in P.J T, (PhiSq P Q (t - t') : ℂ) * conj (S t) * conj (S t') =
      conj A := by
    rw [hA, ← integral_conj]
    congr 1; funext t
    rw [← integral_conj]
    congr 1; funext t'
    simp only [map_mul, Complex.conj_ofReal]
  have hB' : ∫ t in P.J T, ∫ t' in P.J T, (PhiSq P Q (t - t') : ℂ) * conj (S t) * S t' =
      conj B := by
    rw [hB, ← integral_conj]
    congr 1; funext t
    rw [← integral_conj]
    congr 1; funext t'
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
  have hsum : (K2 P Q T (PChi P Q χ) (PChi P Q χ) : ℂ) =
      (1 / (4 * Real.pi ^ 2) : ℂ) * ((A + B) + (conj B + conj A)) := by
    rw [hK2]
    simp_rw [hexp]
    rw [← hB', ← hA', hA, hB]
    unfold PrimeSetup.J
    rw [dint_const_mul]
    congr 1
    rw [dint_add (((hcont _ _ hSc hSc)).add (hcont _ _ hSc hconjS))
      ((hcont _ _ hconjS hSc).add (hcont _ _ hconjS hconjS))]
    rw [dint_add (hcont _ _ hSc hSc) (hcont _ _ hSc hconjS),
      dint_add (hcont _ _ hconjS hSc) (hcont _ _ hconjS hconjS)]
  have hre := congrArg Complex.re hsum
  rw [Complex.ofReal_re] at hre
  rw [hre]
  have e4 : (1 / (4 * Real.pi ^ 2) : ℂ) = ((1 / (4 * Real.pi ^ 2) : ℝ) : ℂ) := by push_cast; ring
  rw [e4, Complex.re_ofReal_mul]
  simp only [Complex.add_re, Complex.conj_re]
  field_simp
  ring

end PP

/-! ### `eq:split` -/

/-- **`eq:split`**: `𝓜 = M_{μμ} + 2 M_{μΛ} + (1/2π²)(Re ∑ a_n a_m Δ 𝒦 + Re SSC)`. -/
theorem Mcal_split (P : PrimeSetup) (W : Weight) {Q : ℝ} (hQ : 1 < Q) (T : ℝ) :
    Mcal P W Q T = Mmumu P W Q T + 2 * Mmix P W Q T +
      1 / (2 * Real.pi ^ 2) * ((P.ratioForm W Q T (P.aVec Q)).re + (SSC P W Q T).re) := by
  have hsplit : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      ∫ t in P.J T, ∫ t' in P.J T, PhiSq P Q (t - t') * nuChi P Q χ t * nuChi P Q χ t' =
        K2 P Q T (muChi χ) (muChi χ) + 2 * K2 P Q T (muChi χ) (PChi P Q χ) +
          K2 P Q T (PChi P Q χ) (PChi P Q χ) := by
    intro q χ
    have hμ := muChi_continuous χ
    have hP := PChi_continuous P Q χ
    have hν : nuChi P Q χ = muChi χ + PChi P Q χ := rfl
    have : ∫ t in P.J T, ∫ t' in P.J T, PhiSq P Q (t - t') * nuChi P Q χ t * nuChi P Q χ t' =
        K2 P Q T (nuChi P Q χ) (nuChi P Q χ) := rfl
    rw [this, hν, K2_add_left hQ T hμ hP (hμ.add hP), K2_add_right hQ T hμ hμ hP,
      K2_add_right hQ T hP hμ hP, K2_symm hQ T hP hμ]
    ring
  unfold Mcal Mmumu Mmix famSum
  simp_rw [hsplit]
  -- the `PP` part
  have hPP : ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ χ ∈ primChars q,
      K2 P Q T (PChi P Q χ) (PChi P Q χ) =
      1 / (2 * Real.pi ^ 2) * ((P.ratioForm W Q T (P.aVec Q)).re + (SSC P W Q T).re) := by
    simp_rw [K2_PP hQ T]
    rw [← famSum_S_conjS P hQ W T]
    unfold SSC
    have hre : ∀ X : (q : ℕ) → DirichletCharacter ℂ q → ℂ,
        (∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (W.omega Q q : ℂ) * ∑ χ ∈ primChars q, X q χ).re =
          ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ χ ∈ primChars q, (X q χ).re := by
      intro X
      rw [Complex.re_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Complex.re_ofReal_mul, Complex.re_sum]
    rw [hre, hre, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← mul_add, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    ring
  rw [← hPP]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum, K2]
  ring

end Families.Ported.Second
