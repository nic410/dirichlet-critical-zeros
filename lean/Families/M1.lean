/-
`lem:M1` (time–frequency factorisation), `lemma-B-majorant.tex` §5:
  `𝒦(n,m) = ∫ g(u) \hat{1_J}(u − log n) \overline{\hat{1_J}(u − log m)} du`, and hence
  `∑ y_n y_m Δ(n,m) 𝒦(n,m) = ∫ g(u) x_y(u)^*Δ x_y(u) du`.
The convolution theorem `Φ(r)² = ∫ g(u) e^{iru} du` (`g = ψ_L² * ψ_L²`, `Φ = \widehat{ψ_L²}`) is proved
directly (Fubini + translation invariance), then two Fubini swaps over `J × ℝ`.
The diagonal asymptotic `𝒦(n,n) = 2π|J| g(log n) + O_v(1)` is not proved here.
-/
import Families.PrimeSide
open scoped BigOperators ComplexConjugate
open MeasureTheory
noncomputable section
namespace Families
namespace PrimeSetup
variable (P : PrimeSetup)

lemma L_pos {Q : ℝ} (hQ : 1 < Q) : 0 < P.L Q := mul_pos P.lam_pos (Real.log_pos hQ)

/-- `ψ_L²` as a real function. -/
def FR (Q : ℝ) (u : ℝ) : ℝ := P.ψL Q u ^ 2

lemma FR_continuous (Q : ℝ) : Continuous (P.FR Q) := by
  unfold FR ψL
  exact ((P.ψ_smooth.continuous).comp (continuous_id.div_const _)).pow 2

lemma FR_hasCompactSupport {Q : ℝ} (hQ : 1 < Q) : HasCompactSupport (P.FR Q) := by
  obtain ⟨r, -, hr⟩ := P.ψ_supp
  have hL := P.L_pos hQ
  refine HasCompactSupport.intro (K := Set.Icc (-(|r| * P.L Q)) (|r| * P.L Q)) isCompact_Icc ?_
  intro x hx
  have hx' : |r| * P.L Q < |x| := by
    by_contra hcon
    exact hx (Set.mem_Icc.mpr (abs_le.mp (not_lt.mp hcon)))
  have : r < |x / P.L Q| := by
    rw [abs_div, abs_of_pos hL, lt_div_iff₀ hL]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_abs_self r) hL.le) hx'
  unfold FR ψL
  rw [hr _ this]; ring

lemma FR_integrable {Q : ℝ} (hQ : 1 < Q) : Integrable (P.FR Q) :=
  (P.FR_continuous Q).integrable_of_hasCompactSupport (P.FR_hasCompactSupport hQ)

lemma g_eq_conv (Q u : ℝ) :
    P.g Q u = (convolution (P.FR Q) (P.FR Q) (ContinuousLinearMap.lsmul ℝ ℝ) volume) u := by
  rw [convolution_def]; rfl

lemma g_continuous {Q : ℝ} (hQ : 1 < Q) : Continuous (P.g Q) := by
  have : P.g Q = (convolution (P.FR Q) (P.FR Q) (ContinuousLinearMap.lsmul ℝ ℝ) volume) := by
    funext u; exact P.g_eq_conv Q u
  rw [this]
  exact (P.FR_hasCompactSupport hQ).continuous_convolution_right _
    (P.FR_integrable hQ).locallyIntegrable (P.FR_continuous Q)

lemma g_integrable {Q : ℝ} (hQ : 1 < Q) : Integrable (P.g Q) := by
  have : P.g Q = (convolution (P.FR Q) (P.FR Q) (ContinuousLinearMap.lsmul ℝ ℝ) volume) := by
    funext u; exact P.g_eq_conv Q u
  rw [this]
  exact (P.FR_integrable hQ).integrable_convolution _ (P.FR_integrable hQ)

/-- The convolution theorem in the form used: `Φ(r)² = ∫ g(u) e^{iru} du`. -/
theorem Φ_sq_eq {Q : ℝ} (hQ : 1 < Q) (r : ℝ) :
    P.Φ Q r ^ 2 = ∫ u, (P.g Q u : ℂ) * Complex.exp (Complex.I * r * u) := by
  set F : ℝ → ℂ := fun u => (P.FR Q u : ℂ) with hF
  set e : ℝ → ℂ := fun u => Complex.exp (Complex.I * r * u) with he
  have hFi : Integrable F := (P.FR_integrable hQ).ofReal
  have hΦ : P.Φ Q r = ∫ u, F u * e u := by
    unfold Φ; congr 1; funext u; simp [hF, he, FR]
  have he_add : ∀ a b : ℝ, e (a + b) = e a * e b := by
    intro a b; simp only [he]; rw [← Complex.exp_add]; congr 1; push_cast; ring
  have he_norm : ∀ a : ℝ, ‖e a‖ = 1 := by
    intro a; simp only [he]
    rw [Complex.norm_exp]; simp
  -- Φ² as an iterated integral
  have h1 : P.Φ Q r ^ 2 = ∫ a, ∫ b, F a * F b * e (a + b) := by
    rw [hΦ, sq, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
    simp only [he_add]; ring
  -- translation b = u - a
  have h2 : ∀ a, ∫ b, F a * F b * e (a + b) = ∫ u, F a * F (u - a) * e u := by
    intro a
    rw [← integral_sub_right_eq_self (fun b => F a * F b * e (a + b)) a]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only; congr 2; ring
  -- integrability for the swap
  have hint : Integrable (Function.uncurry fun a u => F a * F (u - a) * e u)
      (volume.prod volume) := by
    have hc := hFi.convolution_integrand (ContinuousLinearMap.mul ℝ ℂ) hFi
      (μ := volume) (ν := volume)
    have hc' := hc.swap
    have hb : Integrable (fun p : ℝ × ℝ => F p.1 * F (p.2 - p.1) * e p.2) (volume.prod volume) := by
      refine (hc'.mul_bdd (c := 1) ?_ (Filter.Eventually.of_forall fun p => ?_))
      · exact (Continuous.aestronglyMeasurable (by simp only [he]; fun_prop))
      · rw [he_norm]
    exact hb
  -- swap and identify g
  rw [h1, funext h2, integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only
  rw [integral_mul_const]
  congr 1
  unfold g
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only [hF, FR]; push_cast; ring

lemma J_finite (T : ℝ) : volume (P.J T) < ⊤ := by unfold J; exact measure_Icc_lt_top

lemma natCast_cpow (n : ℕ) (hn : 1 ≤ n) (z : ℂ) :
    (n : ℂ) ^ z = Complex.exp ((Real.log n : ℂ) * z) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [Complex.cpow_def_of_ne_zero hn0, Complex.natCast_log]

/-- Integrability over `J × ℝ` of a continuous function dominated by an integrable function of `u`. -/
lemma integrable_J_prod (T : ℝ) (G : ℝ × ℝ → ℂ) (h : ℝ → ℝ) (hh : Integrable h)
    (hG : Continuous G) (hb : ∀ z, ‖G z‖ ≤ h z.2) :
    Integrable G ((volume.restrict (P.J T)).prod volume) := by
  have : IsFiniteMeasure (volume.restrict (P.J T)) := ⟨by
    rw [Measure.restrict_apply_univ]; exact P.J_finite T⟩
  have hbound : Integrable (fun z : ℝ × ℝ => (1 : ℝ) * h z.2)
      ((volume.restrict (P.J T)).prod volume) :=
    (integrable_const (1 : ℝ)).mul_prod hh
  refine hbound.mono' hG.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
  rw [one_mul]; exact hb z

/-- **`lem:M1`, first part.** `𝒦(n,m) = ∫ g(u) \hat{1_J}(u − log n) \overline{\hat{1_J}(u − log m)} du`. -/
theorem kernel_factorisation {Q T : ℝ} (hQ : 1 < Q) (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    P.𝒦 Q T n m = ∫ u, (P.g Q u : ℂ) * P.hatJ T (u - Real.log n) *
      conj (P.hatJ T (u - Real.log m)) := by
  set A : ℝ → ℝ → ℂ := fun t u => Complex.exp (Complex.I * t * (u - Real.log n)) with hA
  set B : ℝ → ℝ → ℂ := fun t' u => Complex.exp (-(Complex.I * t' * (u - Real.log m))) with hB
  set G : ℝ → ℂ := fun u => (P.g Q u : ℂ) with hGdef
  have hgc : Continuous G := Complex.continuous_ofReal.comp (P.g_continuous hQ)
  have hgi : Integrable (fun u => ‖G u‖) := by
    simpa [hGdef] using (P.g_integrable hQ).norm
  have hAn : ∀ t u, ‖A t u‖ = 1 := by
    intro t u; simp only [hA]; rw [Complex.norm_exp]; simp
    right; rw [← Complex.natCast_log, Complex.ofReal_im]
  have hBn : ∀ t u, ‖B t u‖ = 1 := by
    intro t u; simp only [hB]; rw [Complex.norm_exp]; simp
    right; rw [← Complex.natCast_log, Complex.ofReal_im]
  have hAc : Continuous (fun p : ℝ × ℝ => A p.1 p.2) := by simp only [hA]; fun_prop
  have hBc : Continuous (fun p : ℝ × ℝ => B p.1 p.2) := by simp only [hB]; fun_prop
  -- hat J in terms of A, B
  have hJn : ∀ u, P.hatJ T (u - Real.log n) = ∫ t in P.J T, A t u := by
    intro u; unfold hatJ; congr 1; funext t; simp only [hA]; push_cast; ring_nf
  have hJm : ∀ u, conj (P.hatJ T (u - Real.log m)) = ∫ t' in P.J T, B t' u := by
    intro u; unfold hatJ; rw [← integral_conj]; congr 1; funext t'
    simp only [hB]; rw [← Complex.exp_conj]; congr 1
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]; push_cast; ring
  -- the integrand of 𝒦
  have hK : ∀ t t', P.Φ Q (t - t') ^ 2 * (n : ℂ) ^ (-(Complex.I * t)) * (m : ℂ) ^ (Complex.I * t')
      = ∫ u, G u * (A t u * B t' u) := by
    intro t t'
    rw [P.Φ_sq_eq hQ, natCast_cpow n hn, natCast_cpow m hm, ← integral_mul_const,
      ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [hA, hB, hGdef]
    rw [mul_assoc, mul_assoc, ← Complex.exp_add, ← Complex.exp_add, mul_assoc,
      ← Complex.exp_add]
    congr 2; simp only [Complex.ofReal_sub]; ring
  -- Bc: the t'-integral
  set Bc : ℝ → ℂ := fun u => ∫ t' in P.J T, B t' u with hBcdef
  have hBcc : Continuous Bc := by
    have := continuous_parametric_integral_of_continuous (μ := volume)
      (f := fun u t' => B t' u) (by
        have : Continuous (fun p : ℝ × ℝ => B p.2 p.1) := hBc.comp continuous_swap
        exact this) (isCompact_Icc (a := (1 + P.θ) * T) (b := (2 - P.θ) * T))
    exact this
  have hBcn : ∀ u, ‖Bc u‖ ≤ volume.real (P.J T) := by
    intro u
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := P.J T) (C := 1)
      (P.J_finite T) (fun t' _ => (hBn t' u).le)
    simpa [hBcdef] using this
  -- first swap (inner integral, fixed t)
  have hswap1 : ∀ t, ∫ t' in P.J T, ∫ u, G u * (A t u * B t' u)
      = ∫ u, G u * A t u * Bc u := by
    intro t
    have hint : Integrable (Function.uncurry fun t' u => G u * (A t u * B t' u))
        ((volume.restrict (P.J T)).prod volume) := by
      refine P.integrable_J_prod T _ (fun u => ‖G u‖) hgi ?_ ?_
      · have : Continuous (fun p : ℝ × ℝ => G p.2 * (A t p.2 * B p.1 p.2)) := by
          have h1 : Continuous (fun p : ℝ × ℝ => A t p.2) :=
            hAc.comp (continuous_const.prodMk continuous_snd)
          exact (hgc.comp continuous_snd).mul (h1.mul hBc)
        exact this
      · rintro ⟨a, b⟩
        simp only [Function.uncurry_apply_pair, norm_mul, hAn, hBn, mul_one]
        exact le_refl _
    rw [integral_integral_swap hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [hBcdef]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t' => ?_)
    simp only; ring
  -- second swap
  have hswap2 : ∫ t in P.J T, ∫ u, G u * A t u * Bc u
      = ∫ u, G u * (∫ t in P.J T, A t u) * Bc u := by
    have hint : Integrable (Function.uncurry fun t u => G u * A t u * Bc u)
        ((volume.restrict (P.J T)).prod volume) := by
      refine P.integrable_J_prod T _ (fun u => ‖G u‖ * volume.real (P.J T))
        (hgi.mul_const _) ?_ ?_
      · have : Continuous (fun p : ℝ × ℝ => G p.2 * A p.1 p.2 * Bc p.2) :=
          ((hgc.comp continuous_snd).mul hAc).mul (hBcc.comp continuous_snd)
        exact this
      · rintro ⟨a, b⟩
        simp only [Function.uncurry_apply_pair, norm_mul, hAn, mul_one]
        exact mul_le_mul_of_nonneg_left (hBcn b) (norm_nonneg _)
    rw [integral_integral_swap hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only
    rw [integral_mul_const, integral_const_mul]
  -- assemble
  unfold 𝒦
  calc (∫ t in P.J T, ∫ t' in P.J T,
          P.Φ Q (t - t') ^ 2 * (n : ℂ) ^ (-(Complex.I * t)) * (m : ℂ) ^ (Complex.I * t'))
      = ∫ t in P.J T, ∫ t' in P.J T, ∫ u, G u * (A t u * B t' u) := by
        simp_rw [hK]
    _ = ∫ t in P.J T, ∫ u, G u * A t u * Bc u := by simp_rw [hswap1]
    _ = ∫ u, G u * (∫ t in P.J T, A t u) * Bc u := hswap2
    _ = _ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        simp only [hGdef, hBcdef]
        rw [hJn u, hJm u]


lemma hatJ_continuous (T : ℝ) : Continuous (P.hatJ T) := by
  have := continuous_parametric_integral_of_continuous (μ := volume)
    (f := fun (ξ t : ℝ) => Complex.exp (Complex.I * t * ξ)) (by fun_prop)
    (s := P.J T) (by unfold J; exact isCompact_Icc)
  exact this

lemma hatJ_norm_le (T ξ : ℝ) : ‖P.hatJ T ξ‖ ≤ volume.real (P.J T) := by
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := P.J T) (C := 1)
    (f := fun t : ℝ => Complex.exp (Complex.I * t * ξ)) (P.J_finite T) (fun t _ => by
      rw [Complex.norm_exp]; simp)
  simpa [hatJ] using this

private lemma famForm_eq_sum' (W : Weight) (Q : ℝ) (I : Finset ℤ) (x : ℤ → ℂ) :
    (famForm W Q I x : ℂ) = ∑ n ∈ I, ∑ m ∈ I, x n * conj (x m) * Δ W Q n m := by
  have hz : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  unfold famForm Δ
  push_cast
  simp_rw [← Complex.ofReal_pow, hz, map_sum, map_mul, Finset.sum_mul_sum, Finset.mul_sum]
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

lemma Y_nonneg (Q : ℝ) : 0 ≤ P.Y Q := Real.rpow_nonneg (Real.exp_pos _).le _

/-- **`lem:M1`, second part.** `∑ y_n y_m Δ(n,m) 𝒦(n,m) = ∫ g(u) x_y(u)^*Δ x_y(u) du`. -/
theorem ratioForm_factorisation {Q T : ℝ} (hQ : 1 < Q) (W : Weight) (y : ℕ → ℝ) :
    P.ratioForm W Q T y = ∫ u, (P.g Q u : ℂ) * famForm W Q (P.rangeZ Q) (P.xVec Q T y u) := by
  set I := P.rangeZ Q with hI
  set K : ℤ → ℤ → ℝ → ℂ := fun n m u => (P.g Q u : ℂ) * P.hatJ T (u - Real.log n.toNat) *
    conj (P.hatJ T (u - Real.log m.toNat)) with hKdef
  set c : ℤ → ℤ → ℂ := fun n m => (y n.toNat : ℂ) * y m.toNat * Δ W Q n m with hcdef
  have hpt : ∀ u, (P.g Q u : ℂ) * famForm W Q I (P.xVec Q T y u)
      = ∑ n ∈ I, ∑ m ∈ I, c n m * K n m u := by
    intro u
    rw [famForm_eq_sum', Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    simp only [PrimeSetup.xVec, if_pos hn1, if_pos hm1, hcdef, hKdef, map_mul,
      Complex.conj_ofReal]
    ring
  have hKint : ∀ n m, Integrable (K n m) := by
    intro n m
    have hg : Integrable (fun u => (P.g Q u : ℂ)) := (P.g_integrable hQ).ofReal
    have h1 : Integrable (fun u => (P.g Q u : ℂ) * P.hatJ T (u - Real.log n.toNat)) :=
      hg.mul_bdd (c := volume.real (P.J T))
        ((P.hatJ_continuous T).comp (continuous_id.sub continuous_const)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun u => P.hatJ_norm_le T _)
    exact h1.mul_bdd (c := volume.real (P.J T))
      ((Complex.continuous_conj.comp
        ((P.hatJ_continuous T).comp (continuous_id.sub continuous_const)))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by
        rw [Complex.norm_conj]; exact P.hatJ_norm_le T _)
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_finsetSum _ (fun n _ => integrable_finsetSum _ fun m _ => (hKint n m).const_mul _)]
  simp_rw [integral_finsetSum _ (fun m _ => (hKint _ m).const_mul _), integral_const_mul]
  -- replace each ∫ K by 𝒦
  have hK : ∀ n ∈ I, ∀ m ∈ I, ∫ u, K n m u = P.𝒦 Q T n.toNat m.toNat := by
    intro n hn m hm
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    rw [P.kernel_factorisation hQ n.toNat m.toNat (by omega) (by omega)]
  rw [Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun m hm => by rw [hK n hn m hm]]
  -- reindex ℤ ↔ ℕ
  have hY := P.Y_nonneg Q
  have hmem : ∀ k : ℕ, k ∈ P.range Q ↔ (k : ℤ) ∈ I := by
    intro k
    simp only [PrimeSetup.range, hI, PrimeSetup.rangeZ, Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by exact_mod_cast h1, ?_⟩
      rw [Int.le_floor]; push_cast
      exact (Nat.le_floor_iff hY).mp h2
    · rintro ⟨h1, h2⟩
      refine ⟨by exact_mod_cast h1, ?_⟩
      rw [Nat.le_floor_iff hY]
      rw [Int.le_floor] at h2; push_cast at h2; exact h2
  have hreindex : ∀ F : ℤ → ℂ, ∑ n ∈ I, F n = ∑ k ∈ P.range Q, F k := by
    intro F
    symm
    refine Finset.sum_bij' (fun (k : ℕ) _ => (k : ℤ)) (fun (n : ℤ) _ => n.toNat) ?_ ?_ ?_ ?_ ?_
    · intro k hk; exact (hmem k).mp hk
    · intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      rw [hmem, Int.toNat_of_nonneg (by omega)]; exact hn
    · intro k _; simp
    · intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      exact Int.toNat_of_nonneg (by omega)
    · intro k _; rfl
  unfold ratioForm
  rw [hreindex]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hreindex]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [hcdef, Int.toNat_natCast]

/-- **`lem:M1`** (both parts). -/
theorem lemM1_parts : lemM1_Statement := by
  intro P Q T hQ _
  exact ⟨fun n m hn hm => P.kernel_factorisation hQ n m hn hm,
    fun W y => P.ratioForm_factorisation hQ W y⟩

end PrimeSetup
end Families

namespace Families

/-- **`lem:M1`** (`𝒦(n,m) = ∫ g(u) \hat{1_J}(u−log n) \overline{\hat{1_J}(u−log m)} du` and the family-form
identity), proved. The diagonal asymptotic `lemM1_diag` is stated separately (not proved). -/
theorem lemM1 : lemM1_Statement := PrimeSetup.lemM1_parts

end Families
