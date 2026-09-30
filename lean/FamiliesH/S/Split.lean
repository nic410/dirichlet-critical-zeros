/-
# Package S: the decomposition of `𝓜` and the positivity of the kernel `K₂`

* `Mcal2_split`: `𝓜 = M_{μμ} + 2 M_{μΛ} + ∑ω K₂(P,P)`, and `PP2_eq`:
  `∑ω K₂(P,P) = (1/2π²)(Re ∑ a_n a_m Δ 𝒦 + Re SSC)` (the families `eq:split`, decoupled);
* `Mmix2_split`: `M_{μΛ} = M_A + M_B` (`μ_χ = (μ_χ − β_q) + β_q`);
* **`K2_self_nonneg`**: `K₂(f,f) = ∬_{J²} Φ(t−t')² f(t) f(t') ≥ 0` for continuous real `f`, since
  `Φ² = \hat g` with `g = ψ_L² * ψ_L² ≥ 0` (`K₂(f,f) = ∫ g(u) |∫_J f(t) e^{−itu} dt|² du`);
* **`MA2_abs_le`**: `2|M_A| ≤ s ∑ω K₂(r,r) + s⁻¹ ∑ω K₂(P,P)` for every `s > 0`.

The last inequality replaces the pointwise large-sieve bound of the families proof of `lem:muLambda`
(`Families.Ported.Second.MixSS.MA_bound`), which at polynomial height loses a factor
`(1 + Y/Q²)^{1/2}` that is not `o(1)`.
-/
import FamiliesH.S.Basic

noncomputable section

set_option linter.unusedSectionVars false

open scoped BigOperators ComplexConjugate ContDiff
open ArithmeticFunction Finset MeasureTheory Filter Topology

namespace Families.Hybrid.S

open Families Families.Ported.Second Families.Ported.Second.FC2

/-! ### Family sums -/

lemma famSum_abs_le (W : Weight) (Q : ℝ) (f : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) :
    |famSum W Q f| ≤ famSum W Q (fun q χ => |f q χ|) := by
  unfold famSum
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  rw [abs_mul, abs_of_nonneg (W.omega_nonneg Q q)]
  exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (W.omega_nonneg Q q)

/-! ### Positivity of `K₂` -/

section PSD

variable (PS : PrimeSetup)

lemma g_nonneg (Qs u : ℝ) : 0 ≤ PS.g Qs u :=
  integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

lemma J_compact (T : ℝ) : IsCompact (PS.J T) := by unfold PrimeSetup.J; exact isCompact_Icc

lemma J_measurable (T : ℝ) : MeasurableSet (PS.J T) := by
  unfold PrimeSetup.J; exact measurableSet_Icc

lemma norm_exp_I_mul (x : ℝ) : ‖Complex.exp (Complex.I * x)‖ = 1 := by
  rw [Complex.norm_exp]; simp

/-- For bounded continuous real `f`: `K₂(f,f) = ∫ g(u) |∫_J f(t) e^{−itu} dt|² du ≥ 0`. -/
lemma K2_self_nonneg_of_bdd {Qs : ℝ} (hQs : 1 < Qs) (T : ℝ) {f : ℝ → ℝ} (hf : Continuous f)
    {M : ℝ} (hM : ∀ t, |f t| ≤ M) : 0 ≤ K2 PS Qs T f f := by
  set G : ℝ → ℂ := fun u => (PS.g Qs u : ℂ) with hGdef
  set A : ℝ → ℝ → ℂ := fun t u => (f t : ℂ) * Complex.exp (Complex.I * (t * u : ℝ)) with hA
  set B : ℝ → ℝ → ℂ := fun t' u => (f t' : ℂ) * Complex.exp (Complex.I * (-(t' * u) : ℝ))
    with hB
  have hgc : Continuous G := Complex.continuous_ofReal.comp (PS.g_continuous hQs)
  have hgi : Integrable (fun u => ‖G u‖) := by
    simpa [hGdef] using (PS.g_integrable hQs).norm
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hAn : ∀ t u, ‖A t u‖ ≤ M := by
    intro t u
    simp only [hA]
    rw [norm_mul, norm_exp_I_mul, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact hM t
  have hBn : ∀ t u, ‖B t u‖ ≤ M := by
    intro t u
    simp only [hB]
    rw [norm_mul, norm_exp_I_mul, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact hM t
  have hAc : Continuous (fun p : ℝ × ℝ => A p.1 p.2) := by
    simp only [hA]
    exact (Complex.continuous_ofReal.comp (hf.comp continuous_fst)).mul
      (Complex.continuous_exp.comp (continuous_const.mul
        (Complex.continuous_ofReal.comp (continuous_fst.mul continuous_snd))))
  have hBc : Continuous (fun p : ℝ × ℝ => B p.1 p.2) := by
    simp only [hB]
    exact (Complex.continuous_ofReal.comp (hf.comp continuous_fst)).mul
      (Complex.continuous_exp.comp (continuous_const.mul
        (Complex.continuous_ofReal.comp (continuous_fst.mul continuous_snd).neg)))
  -- the integrand of `K₂`
  have hK : ∀ t t', ((PhiSq PS Qs (t - t') * f t * f t' : ℝ) : ℂ) =
      ∫ u, G u * (A t u * B t' u) := by
    intro t t'
    have h1 : ((PhiSq PS Qs (t - t') : ℝ) : ℂ) = PS.Φ Qs (t - t') ^ 2 :=
      (Φ_sq_eq_PhiSq PS Qs (t - t')).symm
    rw [Complex.ofReal_mul, Complex.ofReal_mul, h1, PS.Φ_sq_eq hQs, ← integral_mul_const,
      ← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [hGdef, hA, hB]
    have : Complex.exp (Complex.I * ((t - t' : ℝ) : ℂ) * (u : ℂ)) =
        Complex.exp (Complex.I * ((t * u : ℝ) : ℂ)) *
          Complex.exp (Complex.I * ((-(t' * u) : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [this]; ring
  -- `B_c(u) = ∫_J f(t') e^{−it'u} dt'`
  set Bc : ℝ → ℂ := fun u => ∫ t' in PS.J T, B t' u with hBcdef
  have hBcc : Continuous Bc :=
    continuous_parametric_integral_of_continuous (μ := volume) (f := fun u t' => B t' u)
      (hBc.comp continuous_swap) (J_compact PS T)
  have hBcn : ∀ u, ‖Bc u‖ ≤ M * volume.real (PS.J T) := by
    intro u
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := PS.J T) (C := M)
      (PS.J_finite T) (fun t' _ => hBn t' u)
    simpa [hBcdef, mul_comm] using this
  -- first swap
  have hswap1 : ∀ t, ∫ t' in PS.J T, ∫ u, G u * (A t u * B t' u) = ∫ u, G u * A t u * Bc u := by
    intro t
    have hint : Integrable (Function.uncurry fun t' u => G u * (A t u * B t' u))
        ((volume.restrict (PS.J T)).prod volume) := by
      refine PS.integrable_J_prod T _ (fun u => ‖G u‖ * (M * M)) (hgi.mul_const _) ?_ ?_
      · have h1 : Continuous (fun p : ℝ × ℝ => A t p.2) :=
          hAc.comp (continuous_const.prodMk continuous_snd)
        exact (hgc.comp continuous_snd).mul (h1.mul hBc)
      · rintro ⟨a, b⟩
        simp only [Function.uncurry_apply_pair, norm_mul]
        exact mul_le_mul_of_nonneg_left (mul_le_mul (hAn t b) (hBn a b) (norm_nonneg _) hM0)
          (norm_nonneg _)
    rw [integral_integral_swap hint]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [hBcdef]
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t' => ?_)
    simp only; ring
  -- second swap
  have hswap2 : ∫ t in PS.J T, ∫ u, G u * A t u * Bc u =
      ∫ u, G u * (∫ t in PS.J T, A t u) * Bc u := by
    have hint : Integrable (Function.uncurry fun t u => G u * A t u * Bc u)
        ((volume.restrict (PS.J T)).prod volume) := by
      refine PS.integrable_J_prod T _ (fun u => ‖G u‖ * (M * (M * volume.real (PS.J T))))
        (hgi.mul_const _) ?_ ?_
      · exact ((hgc.comp continuous_snd).mul hAc).mul (hBcc.comp continuous_snd)
      · rintro ⟨a, b⟩
        simp only [Function.uncurry_apply_pair, norm_mul]
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul (hAn a b) (hBcn b) (norm_nonneg _) hM0)
          (norm_nonneg _)
    rw [integral_integral_swap hint]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only
    rw [integral_mul_const, integral_const_mul]
  -- `∫_J A(t,u) dt = conj B_c(u)`
  have hconj : ∀ u, ∫ t in PS.J T, A t u = conj (Bc u) := by
    intro u
    simp only [hBcdef]
    rw [← integral_conj]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hA, hB, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I]
    congr 2
    push_cast; ring
  -- assemble
  have hK2 : (K2 PS Qs T f f : ℂ) = ((∫ u, PS.g Qs u * ‖Bc u‖ ^ 2 : ℝ) : ℂ) := by
    unfold K2
    rw [← integral_complex_ofReal]
    have e1 : ∀ t, ((∫ t' in PS.J T, PhiSq PS Qs (t - t') * f t * f t' : ℝ) : ℂ) =
        ∫ t' in PS.J T, ∫ u, G u * (A t u * B t' u) := by
      intro t
      rw [← integral_complex_ofReal]
      exact integral_congr_ae (Eventually.of_forall fun t' => hK t t')
    simp_rw [e1, hswap1]
    rw [hswap2, ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [hGdef]
    rw [hconj u, mul_assoc, mul_comm (conj (Bc u)), Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  have hK2' : K2 PS Qs T f f = ∫ u, PS.g Qs u * ‖Bc u‖ ^ 2 := by exact_mod_cast hK2
  rw [hK2']
  exact integral_nonneg fun u => mul_nonneg (g_nonneg PS Qs u) (sq_nonneg _)

/-- **`K₂` is positive semidefinite** on continuous real functions. -/
theorem K2_self_nonneg {Qs : ℝ} (hQs : 1 < Qs) (T : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    0 ≤ K2 PS Qs T f f := by
  obtain ⟨M, hM⟩ := (J_compact PS T).exists_bound_of_continuousOn hf.continuousOn
  set f' : ℝ → ℝ := fun t => max (-|M|) (min |M| (f t)) with hf'
  have hf'c : Continuous f' := continuous_const.max (continuous_const.min hf)
  have hf'b : ∀ t, |f' t| ≤ |M| := fun t =>
    abs_le.mpr ⟨le_max_left _ _, max_le (by linarith [abs_nonneg M]) (min_le_left _ _)⟩
  have hf'J : ∀ t ∈ PS.J T, f' t = f t := by
    intro t ht
    have h := hM t ht
    rw [Real.norm_eq_abs] at h
    have h' := abs_le.mp (h.trans (le_abs_self M))
    simp only [hf']
    rw [min_eq_right h'.2, max_eq_right h'.1]
  have heq : K2 PS Qs T f f = K2 PS Qs T f' f' := by
    unfold K2
    refine setIntegral_congr_fun (J_measurable PS T) (fun t ht => ?_)
    refine setIntegral_congr_fun (J_measurable PS T) (fun t' ht' => ?_)
    simp only [hf'J t ht, hf'J t' ht']
  rw [heq]
  exact K2_self_nonneg_of_bdd PS hQs T hf'c hf'b

lemma K2_smul_left (Qs T x : ℝ) (f g : ℝ → ℝ) :
    K2 PS Qs T (fun t => x * f t) g = x * K2 PS Qs T f g := by
  unfold K2
  rw [← integral_const_mul]
  congr 1; funext t
  rw [← integral_const_mul]
  congr 1; funext t'
  ring

lemma K2_smul_right (Qs T x : ℝ) (f g : ℝ → ℝ) :
    K2 PS Qs T f (fun t => x * g t) = x * K2 PS Qs T f g := by
  unfold K2
  rw [← integral_const_mul]
  congr 1; funext t
  rw [← integral_const_mul]
  congr 1; funext t'
  ring

lemma K2_expand {Qs : ℝ} (hQs : 1 < Qs) (T x : ℝ) {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g) :
    K2 PS Qs T (f + fun t => x * g t) (f + fun t => x * g t) =
      K2 PS Qs T f f + 2 * x * K2 PS Qs T f g + x ^ 2 * K2 PS Qs T g g := by
  have hxg : Continuous (fun t => x * g t) := continuous_const.mul hg
  rw [K2_add_left hQs T hf hxg (hf.add hxg), K2_add_right hQs T hf hf hxg,
    K2_add_right hQs T hxg hf hxg, K2_smul_left, K2_smul_left, K2_smul_right, K2_smul_right,
    K2_symm hQs T hg hf]
  ring

/-- `2|K₂(f,g)| ≤ s K₂(f,f) + s⁻¹ K₂(g,g)` for `s > 0` (Cauchy–Schwarz for the PSD form `K₂`). -/
theorem K2_abs_le {Qs : ℝ} (hQs : 1 < Qs) (T : ℝ) {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g) {s : ℝ} (hs : 0 < s) :
    2 * |K2 PS Qs T f g| ≤ s * K2 PS Qs T f f + s⁻¹ * K2 PS Qs T g g := by
  have hc : ∀ x : ℝ, Continuous (f + fun t => x * g t) := fun x =>
    hf.add (continuous_const.mul hg)
  have h1 := K2_self_nonneg PS hQs T (hc s⁻¹)
  have h2 := K2_self_nonneg PS hQs T (hc (-s⁻¹))
  rw [K2_expand PS hQs T _ hf hg] at h1 h2
  set a := K2 PS Qs T f f
  set b := K2 PS Qs T f g
  set c := K2 PS Qs T g g
  have e1 : s * (a + 2 * s⁻¹ * b + s⁻¹ ^ 2 * c) = s * a + 2 * b + s⁻¹ * c := by
    field_simp
  have e2 : s * (a + 2 * (-s⁻¹) * b + (-s⁻¹) ^ 2 * c) = s * a - 2 * b + s⁻¹ * c := by
    field_simp
    ring
  have k1 := mul_nonneg hs.le h1
  have k2 := mul_nonneg hs.le h2
  rw [e1] at k1
  rw [e2] at k2
  rcases abs_cases b with ⟨hb, _⟩ | ⟨hb, _⟩ <;> rw [hb] <;> linarith

end PSD

/-! ### `eq:split`, decoupled -/

section Split

variable (PS : PrimeSetup) (W : Weight)

/-- `∑_χ ω_χ ∬ Φ² S \bar S' = ∑_{n,m} a_n a_m Δ_Q(n,m) 𝒦_{Qs}(n,m)`, decoupled. -/
lemma famSum_S_conjS2 {Qs : ℝ} (hQs : 1 < Qs) (Q T : ℝ) :
    ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (W.omega Q q : ℂ) * ∑ χ ∈ primChars q,
      ∫ t in PS.J T, ∫ t' in PS.J T, (PhiSq PS Qs (t - t') : ℂ) * PS.Schi χ Qs (PS.aVec Qs) t *
        conj (PS.Schi χ Qs (PS.aVec Qs) t') = ratio2 PS W Q Qs T (PS.aVec Qs) := by
  simp_rw [dint_S_conjS PS hQs T]
  unfold ratio2 Δ
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  have stepA : ∀ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∀ F : DirichletCharacter ℂ q → ℕ → ℕ → ℂ,
      ∑ χ ∈ primChars q, ∑ n ∈ PS.range Qs, ∑ m ∈ PS.range Qs, F χ n m =
        ∑ n ∈ PS.range Qs, ∑ m ∈ PS.range Qs, ∑ χ ∈ primChars q, F χ n m := by
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

/-- `∑ω K₂(P,P) = (1/2π²)(Re ∑ a_n a_m Δ 𝒦 + Re SSC)`. -/
theorem PP2_eq {Qs : ℝ} (hQs : 1 < Qs) (Q T : ℝ) :
    PP2 PS W Q Qs T = 1 / (2 * Real.pi ^ 2) *
      ((ratio2 PS W Q Qs T (PS.aVec Qs)).re + (SSC2 PS W Q Qs T).re) := by
  unfold PP2 famSum
  simp_rw [K2_PP hQs T]
  rw [← famSum_S_conjS2 PS W hQs Q T]
  unfold SSC2
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

/-- **`eq:split`**, decoupled: `𝓜 = M_{μμ} + 2 M_{μΛ} + ∑ω K₂(P,P)`. -/
theorem Mcal2_split {Qs : ℝ} (hQs : 1 < Qs) (Q T : ℝ) :
    Mcal2 PS W Q Qs T = Mmumu2 PS W Q Qs T + 2 * Mmix2 PS W Q Qs T + PP2 PS W Q Qs T := by
  have hsplit : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      ∫ t in PS.J T, ∫ t' in PS.J T, PhiSq PS Qs (t - t') * nuChi PS Qs χ t * nuChi PS Qs χ t' =
        K2 PS Qs T (muChi χ) (muChi χ) + 2 * K2 PS Qs T (muChi χ) (PChi PS Qs χ) +
          K2 PS Qs T (PChi PS Qs χ) (PChi PS Qs χ) := by
    intro q χ
    have hμ := muChi_continuous χ
    have hP := PChi_continuous PS Qs χ
    have hν : nuChi PS Qs χ = muChi χ + PChi PS Qs χ := rfl
    have : ∫ t in PS.J T, ∫ t' in PS.J T,
        PhiSq PS Qs (t - t') * nuChi PS Qs χ t * nuChi PS Qs χ t' =
        K2 PS Qs T (nuChi PS Qs χ) (nuChi PS Qs χ) := rfl
    rw [this, hν, K2_add_left hQs T hμ hP (hμ.add hP), K2_add_right hQs T hμ hμ hP,
      K2_add_right hQs T hP hμ hP, K2_symm hQs T hP hμ]
    ring
  unfold Mcal2 Mmumu2 Mmix2 PP2
  simp_rw [hsplit]
  rw [famSum_add, famSum_add, famSum_mul_left]

/-- `M_{μΛ} = M_A + M_B`. -/
theorem Mmix2_split {Qs : ℝ} (hQs : 1 < Qs) (Q T : ℝ) :
    Mmix2 PS W Q Qs T = MA2 PS W Q Qs T + MB2 PS W Q Qs T := by
  unfold Mmix2 MA2 MB2
  rw [← famSum_add]
  congr 1; funext q χ
  have hμ : muChi χ = (fun t => muChi χ t - MixSS.beta q T) + (fun _ => MixSS.beta q T) := by
    funext t; simp
  conv_lhs => rw [hμ]
  exact K2_add_left hQs T ((muChi_continuous χ).sub continuous_const) continuous_const
    (PChi_continuous PS Qs χ)

/-- **The `r`-part by positivity**: `2|M_A| ≤ s ∑ω K₂(r,r) + s⁻¹ ∑ω K₂(P,P)`, `s > 0`. -/
theorem MA2_abs_le {Qs : ℝ} (hQs : 1 < Qs) (Q T : ℝ) {s : ℝ} (hs : 0 < s) :
    2 * |MA2 PS W Q Qs T| ≤ s * RR2 PS W Q Qs T + s⁻¹ * PP2 PS W Q Qs T := by
  unfold MA2 RR2 PP2
  refine (mul_le_mul_of_nonneg_left (famSum_abs_le W Q _) two_pos.le).trans ?_
  rw [← famSum_mul_left, ← famSum_mul_left, ← famSum_mul_left, ← famSum_add]
  refine famSum_mono W Q fun q _ χ => ?_
  exact K2_abs_le PS hQs T ((muChi_continuous χ).sub continuous_const)
    (PChi_continuous PS Qs χ) hs

/-- `∑ω K₂(r,r) ≤ R₀² H ∬_{J²} Φ²` (`|μ_χ − β_q| ≤ R₀` on `J`, Stirling). -/
theorem RR2_le (hStir : StirlingDigamma) : ∃ R₀ : ℝ, 0 ≤ R₀ ∧
    ∀ (PS : PrimeSetup) (W : Weight) (Q Qs T : ℝ), 1 < Qs → 1 ≤ T →
      RR2 PS W Q Qs T ≤ R₀ ^ 2 * W.H Q *
        ∫ t in PS.J T, ∫ t' in PS.J T, PhiSq PS Qs (t - t') := by
  obtain ⟨R₀, hR₀, hnear⟩ := muChi_near_J hStir
  refine ⟨R₀, hR₀, fun PS W Q Qs T hQs hT => ?_⟩
  have hper : ∀ q (χ : DirichletCharacter ℂ q),
      K2 PS Qs T (fun t => muChi χ t - MixSS.beta q T) (fun t => muChi χ t - MixSS.beta q T) ≤
        R₀ ^ 2 * ∫ t in PS.J T, ∫ t' in PS.J T, PhiSq PS Qs (t - t') := by
    intro q χ
    have hr : Continuous (fun t => muChi χ t - MixSS.beta q T) :=
      (muChi_continuous χ).sub continuous_const
    have hcont := K2_cont (P := PS) hQs hr hr
    have hcont1 : Continuous (Function.uncurry fun t t' : ℝ => R₀ ^ 2 * PhiSq PS Qs (t - t')) :=
      continuous_const.mul ((PhiSq_continuous PS hQs).comp (continuous_fst.sub continuous_snd))
    unfold K2
    rw [← integral_const_mul]
    have hin : ∀ t, R₀ ^ 2 * ∫ t' in PS.J T, PhiSq PS Qs (t - t') =
        ∫ t' in PS.J T, R₀ ^ 2 * PhiSq PS Qs (t - t') := fun t => (integral_const_mul _ _).symm
    simp_rw [hin]
    unfold PrimeSetup.J
    refine setIntegral_mono_on (intOn_Icc_outer hcont _ _) (intOn_Icc_outer hcont1 _ _)
      measurableSet_Icc fun t ht => ?_
    refine setIntegral_mono_on (intOn_Icc_inner hcont _ _ t) (intOn_Icc_inner hcont1 _ _ t)
      measurableSet_Icc fun t' ht' => ?_
    have hK0 := PhiSq_nonneg PS Qs (t - t')
    have ha : |muChi χ t - MixSS.beta q T| ≤ R₀ := hnear PS T hT q χ t ht
    have hb : |muChi χ t' - MixSS.beta q T| ≤ R₀ := hnear PS T hT q χ t' ht'
    have hprod : (muChi χ t - MixSS.beta q T) * (muChi χ t' - MixSS.beta q T) ≤ R₀ ^ 2 := by
      have h' : |(muChi χ t - MixSS.beta q T) * (muChi χ t' - MixSS.beta q T)| ≤ R₀ * R₀ := by
        rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) hR₀
      nlinarith [le_abs_self ((muChi χ t - MixSS.beta q T) * (muChi χ t' - MixSS.beta q T))]
    calc PhiSq PS Qs (t - t') * (muChi χ t - MixSS.beta q T) * (muChi χ t' - MixSS.beta q T)
        = PhiSq PS Qs (t - t') * ((muChi χ t - MixSS.beta q T) *
            (muChi χ t' - MixSS.beta q T)) := by ring
      _ ≤ PhiSq PS Qs (t - t') * R₀ ^ 2 := mul_le_mul_of_nonneg_left hprod hK0
      _ = R₀ ^ 2 * PhiSq PS Qs (t - t') := by ring
  unfold RR2
  refine (famSum_mono W Q fun q _ χ => hper q χ).trans (le_of_eq ?_)
  rw [famSum_const]; ring

end Split

end Families.Hybrid.S
