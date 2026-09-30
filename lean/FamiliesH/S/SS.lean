/-
# Package S: the same-sign term and the `β`-part of the mixed term at polynomial height

* `SSC_smallH` (Lemma 9.10(c)): `‖∑_χ ω_χ ∬ Φ² S_χ S_χ'‖ ≪ (Q² + Y) L³ = o(H T L² ℓ_*)`; the families
  proof (Laplace transform `1/log(nm) = ∫₀^∞ (nm)^{−σ} dσ` + large sieve) is used verbatim with the
  decoupled large sieve, and the factor `Q² + Y` is absorbed by `T` through (S1):
  `Q² + Y ≤ η Q² T` for large `Q` (`sieve_loss_small`).
* `MB_smallH`: `M_B = ∑_χ ω_χ β_q ∬ Φ² P_χ' = o(H T L² ℓ_*)` by the bilinear large sieve
  (`|β_q| ≤ ℓ_*/π`, `|X(n)| ≤ 2∫Φ²/log n`), again with `Q² + Y ≤ Q² T`.
-/
import FamiliesH.S.Split

noncomputable section

set_option linter.unusedSectionVars false

open scoped BigOperators ComplexConjugate ContDiff
open ArithmeticFunction Finset MeasureTheory Filter Topology

namespace Families.Hybrid.S

open Families Families.Ported.Second Families.Ported.Second.FC2

/-! ### The Laplace transform and the large sieve, decoupled -/

lemma laplace_LS2 (hMV : MV_LargeSieve) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧
    ∀ (PS : PrimeSetup) (W : Weight) (Q Qs : ℝ), 1 ≤ Q → ∀ (x y : ℕ → ℂ) (u : ℕ → ℝ),
      (∀ n, ‖x n‖ ≤ u n) → (∀ n, ‖y n‖ ≤ u n) → u 1 = 0 →
      ‖∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (W.omega Q q : ℂ) * ∑ χ ∈ primChars q,
          ∑ n ∈ PS.range Qs, ∑ m ∈ PS.range Qs,
            x n * χ n * (y m * χ m) / ((Real.log n + Real.log m : ℝ) : ℂ)‖
        ≤ W.wmax * C₀ * (Q ^ 2 + PS.Y Qs) * ∑ n ∈ PS.range Qs, u n ^ 2 / (2 * Real.log n) := by
  obtain ⟨C₀, hC₀, hLS⟩ := famLS_omega2 hMV
  refine ⟨C₀, hC₀, fun PS W Q Qs hQ x y u hx hy hu1 => ?_⟩
  have hx1 : x 1 = 0 := norm_le_zero_iff.mp (hu1 ▸ hx 1)
  have hy1 : y 1 = 0 := norm_le_zero_iff.mp (hu1 ▸ hy 1)
  have hrange : ∀ n ∈ PS.range Qs, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  set K : ℝ := W.wmax * C₀ * (Q ^ 2 + PS.Y Qs) with hK
  have hK0 : 0 ≤ K := by
    have := W.wmax_nonneg
    have := PrimeSetup.Y_nonneg PS Qs
    positivity
  set e : ℕ → ℝ → ℝ := fun n σ => Real.exp (-(σ * Real.log n)) with he
  set f : (q : ℕ) → DirichletCharacter ℂ q → ℕ → ℕ → ℝ → ℂ := fun q χ n m σ =>
    (x n * (e n σ : ℂ) * χ n) * (y m * (e m σ : ℂ) * χ m) with hf
  have hterm : ∀ q (χ : DirichletCharacter ℂ q), ∀ n ∈ PS.range Qs, ∀ m ∈ PS.range Qs,
      IntegrableOn (f q χ n m) (Set.Ioi 0) ∧
      ∫ σ in Set.Ioi 0, f q χ n m σ =
        x n * χ n * (y m * χ m) / ((Real.log n + Real.log m : ℝ) : ℂ) := by
    intro q χ n hn m hm
    have hn1 := hrange n hn
    have hm1 := hrange m hm
    by_cases hn2 : n = 1
    · subst hn2; simp [hf, hx1]
    by_cases hm2 : m = 1
    · subst hm2; simp [hf, hy1]
    have hc : 0 < Real.log n + Real.log m := by
      have h1 : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
      have h2 : 0 < Real.log m := Real.log_pos (by exact_mod_cast (by omega : 1 < m))
      linarith
    obtain ⟨hi, hv⟩ := MixSS.laplace_exp _ hc
    have hfe : f q χ n m = fun σ => (x n * χ n * (y m * χ m)) *
        ((Real.exp (-(Real.log n + Real.log m) * σ) : ℝ) : ℂ) := by
      funext σ
      simp only [hf, he]
      have : Real.exp (-(Real.log n + Real.log m) * σ) =
          Real.exp (-(σ * Real.log n)) * Real.exp (-(σ * Real.log m)) := by
        rw [← Real.exp_add]; ring_nf
      rw [this]; push_cast; ring
    rw [hfe]
    refine ⟨hi.ofReal.const_mul _, ?_⟩
    rw [integral_const_mul, integral_complex_ofReal, hv]
    push_cast
    field_simp
  have hswap : ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (W.omega Q q : ℂ) * ∑ χ ∈ primChars q,
        ∑ n ∈ PS.range Qs, ∑ m ∈ PS.range Qs,
          x n * χ n * (y m * χ m) / ((Real.log n + Real.log m : ℝ) : ℂ) =
      ∫ σ in Set.Ioi 0, ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (W.omega Q q : ℂ) * ∑ χ ∈ primChars q,
        ∑ n ∈ PS.range Qs, ∑ m ∈ PS.range Qs, f q χ n m σ := by
    rw [MixSS.integral_famsum _ _ _ fun q _ χ _ =>
      integrable_finsetSum _ fun n hn => integrable_finsetSum _ fun m hm =>
        (hterm q χ n hn m hm).1]
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [MixSS.integral_sum_sum _ _ _ fun n hn m hm => (hterm q χ n hn m hm).1]
    exact Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun m hm =>
      (hterm q χ n hn m hm).2.symm
  rw [hswap]
  set g : ℝ → ℝ := fun σ => K * ∑ n ∈ PS.range Qs, u n ^ 2 * Real.exp (-(2 * Real.log n) * σ)
    with hg
  have hgi : IntegrableOn g (Set.Ioi 0) := by
    refine (integrable_finsetSum _ fun n hn => ?_).const_mul K
    by_cases hn2 : n = 1
    · subst hn2; simp [hu1]
    have h1 : 0 < 2 * Real.log n :=
      mul_pos two_pos (Real.log_pos (by exact_mod_cast (by have := hrange n hn; omega : 1 < n)))
    exact (MixSS.laplace_exp _ h1).1.const_mul _
  have hgv : ∫ σ in Set.Ioi 0, g σ = K * ∑ n ∈ PS.range Qs, u n ^ 2 / (2 * Real.log n) := by
    rw [integral_const_mul]
    congr 1
    rw [integral_finsetSum _ fun n hn => ?_]
    · refine Finset.sum_congr rfl fun n hn => ?_
      by_cases hn2 : n = 1
      · subst hn2; simp [hu1]
      have h1 : 0 < 2 * Real.log n :=
        mul_pos two_pos (Real.log_pos (by exact_mod_cast (by have := hrange n hn; omega : 1 < n)))
      rw [integral_const_mul, (MixSS.laplace_exp _ h1).2]
      ring
    · by_cases hn2 : n = 1
      · subst hn2; simp [hu1]
      have h1 : 0 < 2 * Real.log n :=
        mul_pos two_pos (Real.log_pos (by exact_mod_cast (by have := hrange n hn; omega : 1 < n)))
      exact (MixSS.laplace_exp _ h1).1.const_mul _
  rw [← hgv]
  refine norm_integral_le_of_norm_le hgi (Filter.Eventually.of_forall fun σ => ?_)
  set A : (q : ℕ) → DirichletCharacter ℂ q → ℂ := fun q χ =>
    ∑ n ∈ PS.range Qs, (x n * (e n σ : ℂ)) * χ n with hA
  set B : (q : ℕ) → DirichletCharacter ℂ q → ℂ := fun q χ =>
    ∑ n ∈ PS.range Qs, (y n * (e n σ : ℂ)) * χ n with hB
  have hfac : ∀ q (χ : DirichletCharacter ℂ q),
      ∑ n ∈ PS.range Qs, ∑ m ∈ PS.range Qs, f q χ n m σ = A q χ * B q χ := by
    intro q χ
    simp only [hA, hB, hf, Finset.sum_mul_sum]
  simp_rw [hfac]
  have hω := W.omega_nonneg Q
  have hLA := hLS PS W Q Qs hQ (fun n => x n * (e n σ : ℂ))
  have hLB := hLS PS W Q Qs hQ (fun n => y n * (e n σ : ℂ))
  have hnx : ∑ n ∈ PS.range Qs, ‖x n * (e n σ : ℂ)‖ ^ 2 ≤
      ∑ n ∈ PS.range Qs, u n ^ 2 * Real.exp (-(2 * Real.log n) * σ) := by
    refine Finset.sum_le_sum fun n _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow]
    have : Real.exp (-(σ * Real.log n)) ^ 2 = Real.exp (-(2 * Real.log n) * σ) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [this]
    gcongr
    exact hx n
  have hny : ∑ n ∈ PS.range Qs, ‖y n * (e n σ : ℂ)‖ ^ 2 ≤
      ∑ n ∈ PS.range Qs, u n ^ 2 * Real.exp (-(2 * Real.log n) * σ) := by
    refine Finset.sum_le_sum fun n _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow]
    have : Real.exp (-(σ * Real.log n)) ^ 2 = Real.exp (-(2 * Real.log n) * σ) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [this]
    gcongr
    exact hy n
  set U := ∑ n ∈ PS.range Qs, u n ^ 2 * Real.exp (-(2 * Real.log n) * σ)
  have hAB : ‖∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (W.omega Q q : ℂ) * ∑ χ ∈ primChars q, A q χ * B q χ‖ ≤
      ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ χ ∈ primChars q,
        (‖A q χ‖ ^ 2 + ‖B q χ‖ ^ 2) / 2 := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hω q)]
    refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => ?_))
      (hω q)
    rw [norm_mul]
    nlinarith [sq_nonneg (‖A q χ‖ - ‖B q χ‖)]
  refine hAB.trans ?_
  have hsplit : ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ χ ∈ primChars q,
        (‖A q χ‖ ^ 2 + ‖B q χ‖ ^ 2) / 2 =
      ((∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ χ ∈ primChars q, ‖A q χ‖ ^ 2) +
        ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ χ ∈ primChars q, ‖B q χ‖ ^ 2) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [← mul_add, ← Finset.sum_add_distrib, mul_div_assoc, Finset.sum_div]
  rw [hsplit]
  simp only [hg]
  have h1 : ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ χ ∈ primChars q, ‖A q χ‖ ^ 2 ≤ K * U :=
    hLA.trans (mul_le_mul_of_nonneg_left hnx hK0)
  have h2 : ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ χ ∈ primChars q, ‖B q χ‖ ^ 2 ≤ K * U :=
    hLB.trans (mul_le_mul_of_nonneg_left hny hK0)
  linarith

/-! ### The same-sign term -/

section SS

variable (PS : PrimeSetup)

/-- `G(t,t') = ∑_χ ω_χ S_χ(t) S_χ(t')`, decoupled. -/
def Gss2 (W : Weight) (Q Qs : ℝ) (t t' : ℝ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (W.omega Q q : ℂ) * ∑ χ ∈ primChars q,
    PS.Schi χ Qs (PS.aVec Qs) t * PS.Schi χ Qs (PS.aVec Qs) t'

lemma Gss2_continuous (W : Weight) (Q Qs : ℝ) : Continuous (Function.uncurry (Gss2 PS W Q Qs)) := by
  unfold Gss2
  refine continuous_finsetSum _ fun q _ => continuous_const.mul
    (continuous_finsetSum _ fun χ _ => ?_)
  exact ((Schi_continuous PS χ Qs _).comp continuous_fst).mul
    ((Schi_continuous PS χ Qs _).comp continuous_snd)

lemma Gss2_norm_le (W : Weight) (Q Qs t t' : ℝ) :
    ‖Gss2 PS W Q Qs t t'‖ ≤ ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ _χ ∈ primChars q,
      (∑ n ∈ PS.range Qs, PS.aVec Qs n) ^ 2 := by
  unfold Gss2
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (W.omega_nonneg Q q)]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun χ _ => ?_))
    (W.omega_nonneg Q q)
  rw [norm_mul, sq]
  exact mul_le_mul (MixSS.Schi_norm_le PS χ Qs t) (MixSS.Schi_norm_le PS χ Qs t') (norm_nonneg _)
    (Finset.sum_nonneg fun n _ => aVec_nonneg PS Qs n)

lemma SS_key2 (hMV : MV_LargeSieve) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧
    ∀ (PS : PrimeSetup) (W : Weight) (Q Qs : ℝ), 1 ≤ Q → ∀ r α β : ℝ,
      ‖∫ t in Set.Icc α β, Gss2 PS W Q Qs t (t - r)‖ ≤
        2 * (W.wmax * C₀ * (Q ^ 2 + PS.Y Qs) *
          ∑ n ∈ PS.range Qs, PS.aVec Qs n ^ 2 / (2 * Real.log n)) := by
  obtain ⟨C₀, hC₀, hL⟩ := laplace_LS2 hMV
  refine ⟨C₀, hC₀, fun PS W Q Qs hQ r α β => ?_⟩
  set B := W.wmax * C₀ * (Q ^ 2 + PS.Y Qs) *
    ∑ n ∈ PS.range Qs, PS.aVec Qs n ^ 2 / (2 * Real.log n) with hBdef
  have hB0 : 0 ≤ B := by
    have := W.wmax_nonneg
    have := PrimeSetup.Y_nonneg PS Qs
    have : 0 ≤ ∑ n ∈ PS.range Qs, PS.aVec Qs n ^ 2 / (2 * Real.log n) :=
      Finset.sum_nonneg fun n hn => div_nonneg (sq_nonneg _)
        (mul_nonneg two_pos.le (Real.log_nonneg (by exact_mod_cast MixSS.range_one_le PS hn)))
    positivity
  rcases lt_or_ge β α with h | h
  · rw [Set.Icc_eq_empty (not_le.mpr h), Measure.restrict_empty, integral_zero_measure, norm_zero]
    positivity
  set a := PS.aVec Qs with ha
  set ph : ℕ → ℕ → ℝ → ℂ := fun n m t =>
    (n : ℂ) ^ (-(Complex.I * t)) * (m : ℂ) ^ (-(Complex.I * ((t - r : ℝ) : ℂ))) with hph
  have hexp : ∀ t, Gss2 PS W Q Qs t (t - r) = ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (W.omega Q q : ℂ) *
      ∑ χ ∈ primChars q, ∑ n ∈ PS.range Qs, ∑ m ∈ PS.range Qs,
        ((a n : ℂ) * χ n * ((a m : ℂ) * χ m)) * ph n m t := by
    intro t
    unfold Gss2 PrimeSetup.Schi
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    simp only [hph]; ring
  simp_rw [hexp]
  have hph_cont : ∀ n ∈ PS.range Qs, ∀ m ∈ PS.range Qs, Continuous (ph n m) := by
    intro n hn m hm
    have h2 : Continuous (fun t : ℝ => (m : ℂ) ^ (-(Complex.I * ((t - r : ℝ) : ℂ)))) :=
      (MixSS.continuous_cpow m (MixSS.range_one_le PS hm)).comp
        (continuous_id.sub continuous_const)
    exact (MixSS.continuous_cpow n (MixSS.range_one_le PS hn)).mul h2
  rw [MixSS.integral_famsum (μ := volume.restrict (Set.Icc α β)) (Finset.Icc 1 ⌊Q⌋₊)
    (fun q => (W.omega Q q : ℂ))
    (fun q χ t => ∑ n ∈ PS.range Qs, ∑ m ∈ PS.range Qs,
      ((a n : ℂ) * χ n * ((a m : ℂ) * χ m)) * ph n m t)
    (fun q _ χ _ => integrable_finsetSum _ fun n hn => integrable_finsetSum _ fun m hm =>
      ((hph_cont n hn m hm).integrableOn_Icc).const_mul _)]
  have hint : ∀ q (χ : DirichletCharacter ℂ q),
      ∫ t in Set.Icc α β, ∑ n ∈ PS.range Qs, ∑ m ∈ PS.range Qs,
        ((a n : ℂ) * χ n * ((a m : ℂ) * χ m)) * ph n m t =
      ∑ n ∈ PS.range Qs, ∑ m ∈ PS.range Qs, ((a n : ℂ) * χ n * ((a m : ℂ) * χ m)) *
        (Complex.I / ((Real.log n + Real.log m : ℝ) : ℂ) * (ph n m β - ph n m α)) := by
    intro q χ
    rw [MixSS.integral_sum_sum _ _ _ fun n hn m hm =>
      ((hph_cont n hn m hm).integrableOn_Icc).const_mul _]
    refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun m hm => ?_
    rw [integral_const_mul]
    have hn1 := MixSS.range_one_le PS hn
    have hm1 := MixSS.range_one_le PS hm
    by_cases hn2 : n = 1
    · by_cases hm2 : m = 1
      · subst hn2; subst hm2; simp [ha, aVec_one]
      · congr 1
        exact MixSS.integral_phase n m hn1 hm1 (Or.inr (by omega)) r h
    · congr 1
      exact MixSS.integral_phase n m hn1 hm1 (Or.inl (by omega)) r h
  simp_rw [hint]
  set xγ : ℝ → ℕ → ℂ := fun γ n => (a n : ℂ) * (n : ℂ) ^ (-(Complex.I * γ)) with hxγ
  set yγ : ℝ → ℕ → ℂ := fun γ m => (a m : ℂ) * (m : ℂ) ^ (-(Complex.I * ((γ - r : ℝ) : ℂ)))
    with hyγ
  set Lf : ℝ → ℂ := fun γ => ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (W.omega Q q : ℂ) * ∑ χ ∈ primChars q,
    ∑ n ∈ PS.range Qs, ∑ m ∈ PS.range Qs,
      xγ γ n * χ n * (yγ γ m * χ m) / ((Real.log n + Real.log m : ℝ) : ℂ) with hLf
  have hform : ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (W.omega Q q : ℂ) * ∑ χ ∈ primChars q,
      ∑ n ∈ PS.range Qs, ∑ m ∈ PS.range Qs, ((a n : ℂ) * χ n * ((a m : ℂ) * χ m)) *
        (Complex.I / ((Real.log n + Real.log m : ℝ) : ℂ) * (ph n m β - ph n m α)) =
      Complex.I * (Lf β - Lf α) := by
    simp only [hLf, mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun χ _ =>
      Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    simp only [hxγ, hyγ, hph]
    ring
  rw [hform]
  have hnorm : ∀ γ : ℝ, ∀ n, ‖(a n : ℂ) * (n : ℂ) ^ (-(Complex.I * γ))‖ ≤ a n := by
    intro γ n
    by_cases hn : n = 0
    · subst hn; simp [ha, aVec_zero]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (aVec_nonneg PS Qs n),
      MixSS.norm_cpow_eq_one n (by omega), mul_one]
  have hLb : ∀ γ, ‖Lf γ‖ ≤ B := fun γ =>
    hL PS W Q Qs hQ (xγ γ) (yγ γ) a (fun n => hnorm γ n) (fun n => hnorm (γ - r) n)
      (aVec_one PS Qs)
  calc ‖Complex.I * (Lf β - Lf α)‖ = ‖Lf β - Lf α‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    _ ≤ ‖Lf β‖ + ‖Lf α‖ := norm_sub_le _ _
    _ ≤ B + B := add_le_add (hLb β) (hLb α)
    _ = 2 * B := by ring

lemma SSC2_eq (W : Weight) {Qs : ℝ} (hQs : 1 < Qs) (Q T : ℝ) :
    SSC2 PS W Q Qs T =
      ∫ t in PS.J T, ∫ t' in PS.J T, (PhiSq PS Qs (t - t') : ℂ) * Gss2 PS W Q Qs t t' := by
  have hpt : ∀ t t', (PhiSq PS Qs (t - t') : ℂ) * Gss2 PS W Q Qs t t' =
      ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (W.omega Q q : ℂ) * ∑ χ ∈ primChars q,
        (PhiSq PS Qs (t - t') : ℂ) * PS.Schi χ Qs (PS.aVec Qs) t * PS.Schi χ Qs (PS.aVec Qs) t' := by
    intro t t'
    unfold Gss2
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun χ _ => ?_
    ring
  simp_rw [hpt]
  unfold SSC2 PrimeSetup.J
  rw [MixSS.D_famsum]
  intro q χ
  have h1 : Continuous (fun p : ℝ × ℝ => (PhiSq PS Qs (p.1 - p.2) : ℂ)) :=
    Complex.continuous_ofReal.comp ((PhiSq_continuous PS hQs).comp
      (continuous_fst.sub continuous_snd))
  exact (h1.mul ((Schi_continuous PS χ Qs _).comp continuous_fst)).mul
    ((Schi_continuous PS χ Qs _).comp continuous_snd)

/-- `‖SSC‖ ≤ 2 (∫Φ²) w_max C₀ (Q²+Y) ∑ a_n²/(2 log n)`, decoupled. -/
lemma SSC2_bound (hMV : MV_LargeSieve) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧
    ∀ (PS : PrimeSetup) (W : Weight) (Q Qs : ℝ), 1 ≤ Q → 1 < Qs → ∀ T : ℝ,
      ‖SSC2 PS W Q Qs T‖ ≤ (∫ r, PhiSq PS Qs r) * (2 * (W.wmax * C₀ * (Q ^ 2 + PS.Y Qs) *
          ∑ n ∈ PS.range Qs, PS.aVec Qs n ^ 2 / (2 * Real.log n))) := by
  obtain ⟨C₀, hC₀, hK⟩ := SS_key2 hMV
  refine ⟨C₀, hC₀, fun PS W Q Qs hQ hQs T => ?_⟩
  rw [SSC2_eq PS W hQs Q T]
  unfold PrimeSetup.J
  rw [MixSS.cov (PhiSq PS Qs) (PhiSq_integrable PS hQs) (PhiSq_continuous PS hQs)
    (Gss2 PS W Q Qs) (Gss2_continuous PS W Q Qs) _ (Gss2_norm_le PS W Q Qs)]
  rw [← integral_mul_const]
  refine norm_integral_le_of_norm_le ((PhiSq_integrable PS hQs).mul_const _)
    (Filter.Eventually.of_forall fun r => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (PhiSq_nonneg PS Qs r)]
  exact mul_le_mul_of_nonneg_left (hK PS W Q Qs hQ r _ _) (PhiSq_nonneg PS Qs r)

end SS

/-- **`lem:archH`(c)**: the same-sign term is `o(H T L² ℓ_*)`, uniformly on the cell. -/
theorem SSC_smallH (hMV : MV_LargeSieve) (hWH : lemWH_Statement) (P : HSetup) (W : Weight)
    (δ : ℝ) (hδ : 0 < δ) : ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ P.heights Q,
      ‖SSC2 P.toPS W Q (Q * T) T‖ ≤ δ * (W.H Q * T * P.L Q T ^ 2 * ellS Q T) := by
  obtain ⟨C₀, hC₀, hB⟩ := SSC2_bound hMV
  obtain ⟨CΦ, hCΦ, hΦ⟩ := integral_PhiSq_le P.toPS
  obtain ⟨C₁, Q₁, hC₁, h₁⟩ := sum_aVec_sq_div_log_le P.toPS
  obtain ⟨cH, QH, hcH, hH⟩ := H_lower hWH W
  have hw := W.wmax_nonneg
  have hl := P.lam_pos
  set K : ℝ := 2 * W.wmax * C₀ * C₁ * CΦ / cH with hK
  have hK0 : 0 ≤ K := by positivity
  set η : ℝ := δ / (P.lam * (K + 1)) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨Qη, hQη⟩ := sieve_loss_small P η hη0
  refine ⟨max (max Q₁ QH) (max Qη (Real.exp 1)), fun Q hQ T hT => ?_⟩
  have hQ1' : Q₁ ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hQ
  have hQH : QH ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hQ
  have hQη' : Qη ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hQ
  have hQe : Real.exp 1 ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hQ
  obtain ⟨hT1, hℓ1, hℓs, hQQT, hQT, -⟩ := cell_facts P hQe hT
  have hQ1 : 1 < Q := one_lt_of_exp_one_le hQe
  have hL : 0 < P.L Q T := mul_pos hl (by linarith)
  have hLeq : P.toPS.L (Q * T) = P.L Q T := rfl
  have hloss : Q ^ 2 + P.toPS.Y (Q * T) ≤ η * (Q ^ 2 * T) := hQη Q hQη' T hT
  have hHc : cH * Q ^ 2 ≤ W.H Q := hH Q hQH
  have hH0 : 0 ≤ W.H Q := W.H_nonneg Q
  have hIΦ : ∫ r, PhiSq P.toPS (Q * T) r ≤ CΦ * P.L Q T := hΦ (Q * T) hQT
  have hS : ∑ n ∈ P.toPS.range (Q * T), P.toPS.aVec (Q * T) n ^ 2 / (2 * Real.log n) ≤
      C₁ * P.L Q T ^ 2 := by
    refine le_trans (Finset.sum_le_sum fun n hn => ?_) (h₁ (Q * T) (hQ1'.trans hQQT))
    have h0 : 0 ≤ P.toPS.aVec (Q * T) n ^ 2 / Real.log n :=
      div_nonneg (sq_nonneg _) (Real.log_nonneg (by exact_mod_cast MixSS.range_one_le _ hn))
    rw [mul_comm (2 : ℝ) (Real.log n), ← div_div]
    exact half_le_self h0
  refine (hB P.toPS W Q (Q * T) hQ1.le hQT T).trans ?_
  have hQ2 : Q ^ 2 ≤ W.H Q / cH := by rw [le_div_iff₀ hcH]; linarith
  have step1 : (∫ r, PhiSq P.toPS (Q * T) r) * (2 * (W.wmax * C₀ * (Q ^ 2 + P.toPS.Y (Q * T)) *
      ∑ n ∈ P.toPS.range (Q * T), P.toPS.aVec (Q * T) n ^ 2 / (2 * Real.log n))) ≤
      (CΦ * P.L Q T) * (2 * (W.wmax * C₀ * (η * (W.H Q / cH * T)) * (C₁ * P.L Q T ^ 2))) := by
    have hloss' : Q ^ 2 + P.toPS.Y (Q * T) ≤ η * (W.H Q / cH * T) := by
      refine hloss.trans ?_
      gcongr
    have hS0 : 0 ≤ ∑ n ∈ P.toPS.range (Q * T), P.toPS.aVec (Q * T) n ^ 2 / (2 * Real.log n) :=
      Finset.sum_nonneg fun n hn => div_nonneg (sq_nonneg _)
        (mul_nonneg two_pos.le (Real.log_nonneg (by exact_mod_cast MixSS.range_one_le _ hn)))
    have hY0 := PrimeSetup.Y_nonneg P.toPS (Q * T)
    gcongr
  have step2 : (CΦ * P.L Q T) * (2 * (W.wmax * C₀ * (η * (W.H Q / cH * T)) * (C₁ * P.L Q T ^ 2))) =
      K * η * (W.H Q * T * P.L Q T ^ 3) := by
    rw [hK]; field_simp
  have step3 : K * η * (W.H Q * T * P.L Q T ^ 3) ≤ δ * (W.H Q * T * P.L Q T ^ 2 * ellS Q T) := by
    have hLl : P.L Q T = P.lam * ellS Q T := rfl
    have hKη : K * η * P.lam ≤ δ := by
      rw [hη]
      have : K * (δ / (P.lam * (K + 1))) * P.lam = δ * (K / (K + 1)) := by field_simp
      rw [this]
      have : K / (K + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      nlinarith
    have e : K * η * (W.H Q * T * P.L Q T ^ 3) =
        (K * η * P.lam) * (W.H Q * T * P.L Q T ^ 2 * ellS Q T) := by rw [hLl]; ring
    rw [e]
    have hpos : 0 ≤ W.H Q * T * P.L Q T ^ 2 * ellS Q T := by
      have : 0 ≤ ellS Q T := by linarith
      have : 0 ≤ T := by linarith
      positivity
    exact mul_le_mul_of_nonneg_right hKη hpos
  linarith

/-! ### The `β`-part of the mixed term -/

lemma MB2_eq (PS : PrimeSetup) (W : Weight) {Qs : ℝ} (hQs : 1 < Qs) (Q T : ℝ) :
    MB2 PS W Q Qs T = -(1 / Real.pi) * (∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ ∈ primChars q,
      ((W.omega Q q * MixSS.beta q T : ℝ) : ℂ) *
        ∑ n ∈ PS.range Qs, ((PS.aVec Qs n : ℂ) * MixSS.Xn PS Qs T n) * χ n).re := by
  have hper : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      K2 PS Qs T (fun _ => MixSS.beta q T) (PChi PS Qs χ) = MixSS.beta q T * (-(1 / Real.pi)) *
        (∑ n ∈ PS.range Qs, ((PS.aVec Qs n : ℂ) * MixSS.Xn PS Qs T n) * χ n).re :=
    fun q χ => MixSS.MB_chi PS hQs T (MixSS.beta q T) χ
  unfold MB2 famSum
  simp_rw [hper]
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Complex.re_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [Complex.re_ofReal_mul]
  ring

/-- `|β_q| ≤ ℓ_*/π` for `q ≤ Q` on the cell (`Q ≥ 4`). -/
lemma beta_abs_leH (P : HSetup) {Q T : ℝ} (hQe : Real.exp 1 ≤ Q) (hQ4 : 4 ≤ Q)
    (hT : T ∈ P.heights Q) {q : ℕ} (hq : q ∈ Finset.Icc 1 ⌊Q⌋₊) :
    |MixSS.beta q T| ≤ ellS Q T / Real.pi := by
  obtain ⟨hT1, hℓ1, hℓs, -, -, hlogT⟩ := cell_facts P hQe hT
  have hQ0 : 0 < Q := by linarith
  obtain ⟨hq1, hqQ⟩ := Finset.mem_Icc.mp hq
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hqQ' : (q : ℝ) ≤ Q := (Nat.cast_le.mpr hqQ).trans (Nat.floor_le hQ0.le)
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hq1'
  have hlqQ : Real.log q ≤ Real.log Q := Real.log_le_log (by linarith) hqQ'
  have hpi := Real.pi_pos
  have hpi0 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hpiQ : Real.log Real.pi ≤ Real.log Q := Real.log_le_log hpi (by linarith [Real.pi_lt_four])
  have hℓsT : ellS Q T = Real.log Q + Real.log T := by
    unfold ellS; rw [Real.log_mul hQ0.ne' (by linarith)]
  have hdiv : Real.log (q / Real.pi) = Real.log q - Real.log Real.pi :=
    Real.log_div (by positivity) Real.pi_ne_zero
  unfold MixSS.beta
  rw [hdiv, abs_mul, abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  have habs : |Real.log q - Real.log Real.pi + Real.log T| ≤ 2 * ellS Q T := by
    rw [abs_le]; constructor <;> linarith
  calc 1 / (2 * Real.pi) * |Real.log q - Real.log Real.pi + Real.log T|
      ≤ 1 / (2 * Real.pi) * (2 * ellS Q T) := by gcongr
    _ = ellS Q T / Real.pi := by field_simp

/-- **`lem:archH`(b), the `β`-part**: `M_B = o(H T L² ℓ_*)` (bilinear large sieve). -/
theorem MB_smallH (hMV : MV_LargeSieve) (hWH : lemWH_Statement) (P : HSetup) (W : Weight)
    (δ : ℝ) (hδ : 0 < δ) : ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ P.heights Q,
      |MB2 P.toPS W Q (Q * T) T| ≤ δ * (W.H Q * T * P.L Q T ^ 2 * ellS Q T) := by
  obtain ⟨C₀, hC₀, hbil⟩ := bilinLS2 hMV
  obtain ⟨CΦ, hCΦ, hΦ⟩ := integral_PhiSq_le P.toPS
  obtain ⟨C₂, Q₂, hC₂, h₂⟩ := sum_aVec_sq_div_log_sq_le P.toPS
  obtain ⟨cH, QH, hcH, hH⟩ := H_lower hWH W
  have hw := W.wmax_nonneg
  have hpi := Real.pi_pos
  set K₃ : ℝ := W.wmax * (1 / Real.pi) ^ 2 * (C₀ * (1 / cH) * (4 * CΦ ^ 2 * C₂)) with hK₃
  have hK₃0 : 0 ≤ K₃ := by positivity
  obtain ⟨Q₁, hQ₁⟩ := sieve_loss_small P 1 one_pos
  obtain ⟨QL, hQL⟩ := L_large P (K₃ / (Real.pi * δ) ^ 2)
  refine ⟨max (max Q₂ QH) (max (max Q₁ QL) (max (Real.exp 1) 4)), fun Q hQ T hT => ?_⟩
  have hQ2 : Q₂ ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hQ
  have hQH : QH ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hQ
  have hQ1' : Q₁ ≤ Q := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_max_right _ _)) hQ
  have hQL' : QL ≤ Q := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_max_right _ _)) hQ
  have hQe : Real.exp 1 ≤ Q := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _)) hQ
  have hQ4 : (4 : ℝ) ≤ Q := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_right _ _)) hQ
  obtain ⟨hT1, hℓ1, hℓs, hQQT, hQT, -⟩ := cell_facts P hQe hT
  have hQ1 : 1 < Q := one_lt_of_exp_one_le hQe
  have hl := P.lam_pos
  have hL : 0 < P.L Q T := mul_pos hl (by linarith)
  have hLbig : K₃ / (Real.pi * δ) ^ 2 ≤ P.L Q T := (hQL Q hQL' T hT).1
  have hLbig' : K₃ ≤ (Real.pi * δ) ^ 2 * P.L Q T := by
    rw [div_le_iff₀ (by positivity)] at hLbig; linarith
  have hloss : Q ^ 2 + P.toPS.Y (Q * T) ≤ 1 * (Q ^ 2 * T) := hQ₁ Q hQ1' T hT
  have hHc : cH * Q ^ 2 ≤ W.H Q := hH Q hQH
  have hH0 : 0 ≤ W.H Q := W.H_nonneg Q
  have hQ2H : Q ^ 2 ≤ W.H Q / cH := by rw [le_div_iff₀ hcH]; linarith
  have hω := W.omega_nonneg Q
  set ℓs := ellS Q T with hℓsdef
  have hℓs0 : 0 ≤ ℓs := by linarith
  rw [MB2_eq P.toPS W hQT Q T]
  set Z := ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ ∈ primChars q,
      ((W.omega Q q * MixSS.beta q T : ℝ) : ℂ) *
        ∑ n ∈ P.toPS.range (Q * T), ((P.toPS.aVec (Q * T) n : ℂ) *
          MixSS.Xn P.toPS (Q * T) T n) * χ n with hZ
  -- the `b`-sum
  have h1 : ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ ∈ primChars q, (Nat.totient q : ℝ) / q *
      ‖((W.omega Q q * MixSS.beta q T : ℝ) : ℂ)‖ ^ 2 ≤
      W.wmax * (ℓs / Real.pi) ^ 2 * W.H Q := by
    calc ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ ∈ primChars q, (Nat.totient q : ℝ) / q *
          ‖((W.omega Q q * MixSS.beta q T : ℝ) : ℂ)‖ ^ 2
        ≤ ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ _χ ∈ primChars q,
            W.wmax * (ℓs / Real.pi) ^ 2 * W.omega Q q := by
          refine Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun χ _ => ?_
          have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
          have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
          have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq1
          have hωle := omega_le W Q q
          have hφω : (Nat.totient q : ℝ) / q * W.omega Q q ≤ W.wmax := by
            calc (Nat.totient q : ℝ) / q * W.omega Q q
                ≤ (Nat.totient q : ℝ) / q * (W.wmax * ((q : ℝ) / (Nat.totient q : ℝ))) := by
                  gcongr
              _ = W.wmax := by field_simp
          have hβ := beta_abs_leH P hQe hQ4 hT hq
          have hβ2 : MixSS.beta q T ^ 2 ≤ (ℓs / Real.pi) ^ 2 := by
            rw [← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) hβ 2
          rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
          calc (Nat.totient q : ℝ) / q * (W.omega Q q * MixSS.beta q T) ^ 2
              = ((Nat.totient q : ℝ) / q * W.omega Q q) * (W.omega Q q * MixSS.beta q T ^ 2) := by
                ring
            _ ≤ W.wmax * (W.omega Q q * (ℓs / Real.pi) ^ 2) := by
                refine mul_le_mul hφω ?_ (mul_nonneg (hω q) (sq_nonneg _)) hw
                exact mul_le_mul_of_nonneg_left hβ2 (hω q)
            _ = W.wmax * (ℓs / Real.pi) ^ 2 * W.omega Q q := by ring
      _ = W.wmax * (ℓs / Real.pi) ^ 2 * W.H Q := by
          rw [MixSS.H_eq, Finset.mul_sum]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun χ _ => ?_
          ring
  -- the `x`-sum
  have hIΦ : ∫ r, PhiSq P.toPS (Q * T) r ≤ CΦ * P.L Q T := hΦ (Q * T) hQT
  have h2 : ∑ n ∈ P.toPS.range (Q * T),
      ‖(P.toPS.aVec (Q * T) n : ℂ) * MixSS.Xn P.toPS (Q * T) T n‖ ^ 2 ≤
      4 * CΦ ^ 2 * P.L Q T ^ 2 * (C₂ * P.L Q T) := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left (h₂ (Q * T) (hQ2.trans hQQT))
      (by positivity))
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn1 := MixSS.range_one_le _ hn
    by_cases hn2 : n = 1
    · subst hn2; simp [aVec_one]
    have hn2' : 2 ≤ n := by omega
    have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hX := MixSS.Xn_bound P.toPS hQT T n hn2'
    have hX' : ‖MixSS.Xn P.toPS (Q * T) T n‖ ≤ 2 * (CΦ * P.L Q T) / Real.log n :=
      hX.trans (by gcongr)
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (aVec_nonneg _ _ n), mul_pow]
    calc P.toPS.aVec (Q * T) n ^ 2 * ‖MixSS.Xn P.toPS (Q * T) T n‖ ^ 2
        ≤ P.toPS.aVec (Q * T) n ^ 2 * (2 * (CΦ * P.L Q T) / Real.log n) ^ 2 := by
          gcongr
      _ = 4 * CΦ ^ 2 * P.L Q T ^ 2 * (P.toPS.aVec (Q * T) n ^ 2 / Real.log n ^ 2) := by
          field_simp
          ring
  have hZ2 : ‖Z‖ ^ 2 ≤ K₃ * ℓs ^ 2 * W.H Q ^ 2 * T * P.L Q T ^ 3 := by
    have hb := hbil P.toPS Q (Q * T) hQ1.le
      (fun q χ => ((W.omega Q q * MixSS.beta q T : ℝ) : ℂ))
      (fun n => (P.toPS.aVec (Q * T) n : ℂ) * MixSS.Xn P.toPS (Q * T) T n)
    refine hb.trans ?_
    have hS0 : 0 ≤ ∑ n ∈ P.toPS.range (Q * T),
        ‖(P.toPS.aVec (Q * T) n : ℂ) * MixSS.Xn P.toPS (Q * T) T n‖ ^ 2 :=
      Finset.sum_nonneg fun n _ => sq_nonneg _
    have hY0 := PrimeSetup.Y_nonneg P.toPS (Q * T)
    have hloss' : Q ^ 2 + P.toPS.Y (Q * T) ≤ W.H Q / cH * T := by
      refine hloss.trans ?_
      rw [one_mul]
      exact mul_le_mul_of_nonneg_right hQ2H (by linarith)
    calc (∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ ∈ primChars q, (Nat.totient q : ℝ) / q *
          ‖((W.omega Q q * MixSS.beta q T : ℝ) : ℂ)‖ ^ 2) *
          (C₀ * (Q ^ 2 + P.toPS.Y (Q * T)) * ∑ n ∈ P.toPS.range (Q * T),
            ‖(P.toPS.aVec (Q * T) n : ℂ) * MixSS.Xn P.toPS (Q * T) T n‖ ^ 2)
        ≤ (W.wmax * (ℓs / Real.pi) ^ 2 * W.H Q) *
          (C₀ * (W.H Q / cH * T) * (4 * CΦ ^ 2 * P.L Q T ^ 2 * (C₂ * P.L Q T))) := by
          refine mul_le_mul h1 ?_ (by positivity) (by positivity)
          exact mul_le_mul (mul_le_mul_of_nonneg_left hloss' hC₀) h2 hS0 (by positivity)
      _ = K₃ * ℓs ^ 2 * W.H Q ^ 2 * T * P.L Q T ^ 3 := by
          rw [hK₃]; field_simp
  -- conclusion
  have hX0 : 0 ≤ Real.pi * δ * (W.H Q * T * P.L Q T ^ 2 * ℓs) := by
    have : 0 ≤ T := by linarith
    exact mul_nonneg (by positivity)
      (mul_nonneg (mul_nonneg (mul_nonneg hH0 this) (sq_nonneg _)) hℓs0)
  have hZle : ‖Z‖ ≤ Real.pi * δ * (W.H Q * T * P.L Q T ^ 2 * ℓs) := by
    have hsq : ‖Z‖ ^ 2 ≤ (Real.pi * δ * (W.H Q * T * P.L Q T ^ 2 * ℓs)) ^ 2 := by
      refine hZ2.trans ?_
      have e : (Real.pi * δ * (W.H Q * T * P.L Q T ^ 2 * ℓs)) ^ 2 =
          ((Real.pi * δ) ^ 2 * P.L Q T) * T * (ℓs ^ 2 * W.H Q ^ 2 * T * P.L Q T ^ 3) := by ring
      rw [e]
      have hp : 0 ≤ ℓs ^ 2 * W.H Q ^ 2 * T * P.L Q T ^ 3 := by
        have : 0 ≤ T := by linarith
        positivity
      calc K₃ * ℓs ^ 2 * W.H Q ^ 2 * T * P.L Q T ^ 3
          = K₃ * 1 * (ℓs ^ 2 * W.H Q ^ 2 * T * P.L Q T ^ 3) := by ring
        _ ≤ ((Real.pi * δ) ^ 2 * P.L Q T) * T * (ℓs ^ 2 * W.H Q ^ 2 * T * P.L Q T ^ 3) := by
          gcongr
    have := abs_le_of_sq_le_sq hsq hX0
    rwa [abs_norm] at this
  rw [abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 1 / Real.pi)]
  calc 1 / Real.pi * |Z.re| ≤ 1 / Real.pi * ‖Z‖ := by
        gcongr; exact Complex.abs_re_le_norm Z
    _ ≤ 1 / Real.pi * (Real.pi * δ * (W.H Q * T * P.L Q T ^ 2 * ℓs)) := by gcongr
    _ = δ * (W.H Q * T * P.L Q T ^ 2 * ℓs) := by
        field_simp

end Families.Hybrid.S
