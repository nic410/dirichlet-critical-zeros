/-
# Package S: the finite-centre replacement `eq:fc2H` (Proposition 9.5, second claim (9.8))

`fc2H_proof`: `𝔐 ≤ 𝓜/(aL)² + o(H T ℓ_*)`, uniformly on the cell, for each fixed `τ₀`.

The per-character part of the families proof (`Families.Ported.Second.FC2`: Poisson–Gabor, the kernel
bound `Ek_bound`, `perChi`, `outer_bound`) is used verbatim at `(P.toPS, QT)`; the explicit formula is
Weil's formula for primitive `χ` (`Families.Ported.explicitGaborSharp`, Lemma 2.6) at `Q' = QT`,
converted to the smooth prime cut-off exactly as in `explicitGabor_of_sharp`. The family bound
`∑_χ ω_χ ν_χ(t)² ≤ H (A + B₀|t|)` now carries the large-sieve factor `Q² + Y`, which is `≤ η Q² T`
on the cell for any fixed `η > 0` (`sieve_loss_small`, from (S1)); the resulting error term
`≪ η H T L⁵` is `≤ δ (aL²)² H T ℓ_*` after choosing `η` small (`err_arithH`).
-/
import FamiliesH.S.Basic

noncomputable section

set_option linter.unusedSectionVars false

open scoped BigOperators ComplexConjugate ContDiff FourierTransform
open ArithmeticFunction Finset MeasureTheory Filter Topology

namespace Families.Hybrid.S

open Families Families.Ported.Second Families.Ported.Second.FC2

/-! ### The explicit formula at `Q' = QT` -/

/-- **`lem:explicit`** (smooth cut-off) for a `PrimeSetup` at any bandwidth argument `Qs > 1`, from
Weil's explicit formula (`Families.Ported.explicitGaborSharp`). -/
lemma explicitGabor2 (PS : PrimeSetup) {Qs : ℝ} (hQs : 1 < Qs) (τ₀ : ℝ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (hq : 1 < q) (hprim : χ.IsPrimitive) (T : ℝ)
    (k l : PS.KJ Qs T τ₀) :
    PS.Gabor Qs T τ₀ χ k l =
      ∫ t : ℝ, PS.pk Qs τ₀ k t * PS.pk Qs τ₀ l t * (nuChi PS Qs χ t : ℂ) := by
  have : NeZero q := ⟨by omega⟩
  obtain ⟨hint, hG⟩ := Families.Ported.explicitGaborSharp PS Qs τ₀ hQs q χ hq hprim T k l
  rw [hG]
  have e : ∀ t : ℝ, PS.pk Qs τ₀ k t * PS.pk Qs τ₀ l t * (nuChi PS Qs χ t : ℂ) =
      PS.pk Qs τ₀ k t * PS.pk Qs τ₀ l t * (nuSharp PS Qs χ t : ℂ) +
        PS.pk Qs τ₀ k t * PS.pk Qs τ₀ l t * (Dtail PS Qs χ t : ℂ) := by
    intro t; rw [nuChi_eq PS hQs χ t]; push_cast; ring
  simp_rw [e]
  have hDint : Integrable (fun t : ℝ =>
      PS.pk Qs τ₀ k t * PS.pk Qs τ₀ l t * (Dtail PS Qs χ t : ℂ)) := by
    have hKi : Integrable (fun t : ℝ => PS.pk Qs τ₀ k t * PS.pk Qs τ₀ l t) :=
      (pk_integrable PS hQs τ₀ l).bdd_mul (c := ∫ u, ‖fK PS Qs τ₀ k u‖)
        (pk_continuous PS hQs τ₀ k).aestronglyMeasurable
        (Eventually.of_forall fun t => pk_norm_le PS hQs τ₀ k t)
    have hDb : ∀ t, ‖(Dtail PS Qs χ t : ℂ)‖ ≤ 1 / Real.pi *
        ∑ n ∈ Finset.Ioc ⌊PS.X Qs⌋₊ ⌊PS.Y Qs⌋₊, |PS.aVec Qs n| := by
      intro t
      unfold Dtail
      rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_neg,
        abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi)]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
      refine Finset.sum_le_sum fun n hn => ?_
      have hn1 : 1 ≤ n := by have := (Finset.mem_Ioc.mp hn).1; omega
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have h1 : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
      have h2 : ‖(n : ℂ) ^ (-(Complex.I * t))‖ = 1 := by
        rw [Complex.norm_natCast_cpow_of_pos (by omega)]; simp
      rw [h2, mul_one]
      calc |PS.aVec Qs n| * ‖χ n‖ ≤ |PS.aVec Qs n| * 1 :=
            mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = |PS.aVec Qs n| := mul_one _
    have hDc : Continuous (fun t : ℝ => (Dtail PS Qs χ t : ℂ)) := by
      unfold Dtail
      refine Complex.continuous_ofReal.comp (continuous_const.mul
        (Complex.continuous_re.comp (continuous_finsetSum _ fun n hn => ?_)))
      have hn1 : 1 ≤ n := by have := (Finset.mem_Ioc.mp hn).1; omega
      have hn0 : 0 < ((n : ℂ)).re := by simp; exact_mod_cast hn1
      exact continuous_const.mul (continuous_const.cpow (by fun_prop) fun _ => Or.inl hn0)
    exact hKi.mul_bdd hDc.aestronglyMeasurable (Eventually.of_forall hDb)
  rw [integral_add hint hDint, integral_pk_pk_Dtail PS hQs τ₀ k l χ, add_zero]

/-! ### The family bound for `ν_χ(t)²`, decoupled -/

theorem famSum_nu_sq2 (hMV : MV_LargeSieve) (hStir : StirlingDigamma) (PS : PrimeSetup)
    (W : Weight) : ∃ A₁ B₀ C₀ Ca Qa : ℝ, 0 ≤ A₁ ∧ 0 ≤ B₀ ∧ 0 ≤ C₀ ∧ 0 ≤ Ca ∧
      ∀ Q Qs : ℝ, 1 ≤ Q → Qa ≤ Qs → ∀ t : ℝ,
        famSum W Q (fun _ χ => nuChi PS Qs χ t ^ 2) ≤
          W.H Q * (4 * (Real.log Q + 3) ^ 2 + A₁ + B₀ * |t|) +
            2 * (|W.wmax| * C₀ * (Q ^ 2 + PS.Y Qs) * (Ca * PS.L Qs ^ 3)) := by
  obtain ⟨C, hC0, hC⟩ := muChi_abs_le hStir
  obtain ⟨C₀, hC₀0, hLS⟩ := famLS_omega2 hMV
  obtain ⟨Ca, Qa, hCa0, hCa⟩ := sum_aVec_sq_le PS
  refine ⟨32 * C ^ 2, 16 * C ^ 2, C₀, Ca, Qa, by positivity, by positivity, hC₀0, hCa0,
    fun Q Qs hQ1 hQa t => ?_⟩
  have hH0 := W.H_nonneg Q
  set ℓ := Real.log Q
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg hQ1
  -- per-character bound
  have hpt : ∀ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∀ χ : DirichletCharacter ℂ q,
      nuChi PS Qs χ t ^ 2 ≤ (4 * (ℓ + 3) ^ 2 + 32 * C ^ 2 + 16 * C ^ 2 * |t|) +
        2 * ‖PS.Schi χ Qs (PS.aVec Qs) t‖ ^ 2 := by
    intro q hq χ
    have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
    have hqQ : (q : ℝ) ≤ Q := by
      have := (Finset.mem_Icc.mp hq).2
      exact le_trans (by exact_mod_cast this) (Nat.floor_le (by linarith))
    have hlq := abs_log_div_pi_le hq1 hqQ
    have h1 := hC q χ t
    have hlog0 : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
    have hlogsq : Real.log (|t| + 2) ^ 2 ≤ 4 * (|t| + 2) :=
      log_sq_le (by linarith [abs_nonneg t])
    have hpi : 1 / (2 * Real.pi) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [Real.pi_gt_three]
    have hm : |muChi χ t| ≤ (ℓ + 3) + C * Real.log (|t| + 2) := by
      refine h1.trans ?_
      have hb : 0 ≤ |Real.log (q / Real.pi)| + C * Real.log (|t| + 2) := by positivity
      calc 1 / (2 * Real.pi) * (|Real.log (q / Real.pi)| + C * Real.log (|t| + 2))
          ≤ 1 * (|Real.log (q / Real.pi)| + C * Real.log (|t| + 2)) :=
            mul_le_mul_of_nonneg_right hpi hb
        _ ≤ (ℓ + 3) + C * Real.log (|t| + 2) := by rw [one_mul]; linarith
    have hm2 : muChi χ t ^ 2 ≤ 2 * (ℓ + 3) ^ 2 + 8 * C ^ 2 * (|t| + 2) := by
      have hb : 0 ≤ (ℓ + 3) + C * Real.log (|t| + 2) := by positivity
      have := pow_le_pow_left₀ (abs_nonneg _) hm 2
      rw [sq_abs] at this
      nlinarith [sq_nonneg ((ℓ + 3) - C * Real.log (|t| + 2)), mul_le_mul_of_nonneg_left hlogsq
        (sq_nonneg C)]
    have hp2 := PChi_sq_le PS Qs χ t
    unfold nuChi
    nlinarith [sq_nonneg (muChi χ t - PChi PS Qs χ t)]
  have hsum := famSum_mono W Q (f := fun _ χ => nuChi PS Qs χ t ^ 2)
    (g := fun _ χ => (4 * (ℓ + 3) ^ 2 + 32 * C ^ 2 + 16 * C ^ 2 * |t|) +
      2 * ‖PS.Schi χ Qs (PS.aVec Qs) t‖ ^ 2) hpt
  rw [famSum_add, famSum_const, famSum_mul_left] at hsum
  -- the large sieve
  set x : ℕ → ℂ := fun n => (PS.aVec Qs n : ℂ) * (n : ℂ) ^ (-(Complex.I * t)) with hx
  have hLSx := hLS PS W Q Qs hQ1 x
  have hS : famSum W Q (fun _ χ => ‖PS.Schi χ Qs (PS.aVec Qs) t‖ ^ 2) =
      ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q *
        ∑ χ ∈ primChars q, ‖∑ n ∈ PS.range Qs, x n * χ n‖ ^ 2 := by
    unfold famSum PrimeSetup.Schi
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun χ _ => ?_
    refine congrArg (fun z : ℂ => ‖z‖ ^ 2) (Finset.sum_congr rfl fun n _ => ?_)
    simp only [hx]; ring
  have hxn : ∑ n ∈ PS.range Qs, ‖x n‖ ^ 2 = ∑ n ∈ PS.range Qs, PS.aVec Qs n ^ 2 := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    simp only [hx]
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), Complex.norm_real,
      Real.norm_eq_abs]
    simp
  rw [hxn] at hLSx
  have hA := hCa Qs hQa
  have hsa0 : 0 ≤ ∑ n ∈ PS.range Qs, PS.aVec Qs n ^ 2 := Finset.sum_nonneg fun n _ => sq_nonneg _
  have hLS' : famSum W Q (fun _ χ => ‖PS.Schi χ Qs (PS.aVec Qs) t‖ ^ 2) ≤
      |W.wmax| * C₀ * (Q ^ 2 + PS.Y Qs) * (Ca * PS.L Qs ^ 3) := by
    rw [hS]
    refine hLSx.trans ?_
    have hY0 := PrimeSetup.Y_nonneg PS Qs
    have e1 : W.wmax * C₀ * (Q ^ 2 + PS.Y Qs) ≤ |W.wmax| * C₀ * (Q ^ 2 + PS.Y Qs) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hC₀0)
        (by positivity)
    calc W.wmax * C₀ * (Q ^ 2 + PS.Y Qs) * ∑ n ∈ PS.range Qs, PS.aVec Qs n ^ 2
        ≤ |W.wmax| * C₀ * (Q ^ 2 + PS.Y Qs) * ∑ n ∈ PS.range Qs, PS.aVec Qs n ^ 2 :=
          mul_le_mul_of_nonneg_right e1 hsa0
      _ ≤ |W.wmax| * C₀ * (Q ^ 2 + PS.Y Qs) * (Ca * PS.L Qs ^ 3) :=
          mul_le_mul_of_nonneg_left hA (by positivity)
  calc famSum W Q (fun _ χ => nuChi PS Qs χ t ^ 2)
      ≤ (4 * (ℓ + 3) ^ 2 + 32 * C ^ 2 + 16 * C ^ 2 * |t|) * W.H Q +
        2 * famSum W Q (fun _ χ => ‖PS.Schi χ Qs (PS.aVec Qs) t‖ ^ 2) := hsum
    _ ≤ (4 * (ℓ + 3) ^ 2 + 32 * C ^ 2 + 16 * C ^ 2 * |t|) * W.H Q +
        2 * (|W.wmax| * C₀ * (Q ^ 2 + PS.Y Qs) * (Ca * PS.L Qs ^ 3)) := by linarith
    _ = W.H Q * (4 * (ℓ + 3) ^ 2 + 32 * C ^ 2 + 16 * C ^ 2 * |t|) +
        2 * (|W.wmax| * C₀ * (Q ^ 2 + PS.Y Qs) * (Ca * PS.L Qs ^ 3)) := by ring

/-! ### The pointwise family bound for the error, decoupled -/

theorem famSum_h_le2 (hStir : StirlingDigamma) (PS : PrimeSetup) {CU : ℝ}
    (hCU : ∀ y, ‖U PS y‖ ≤ CU * rho y ^ 8) (W : Weight) (Q : ℝ) {Qs : ℝ} (hQs : 1 < Qs)
    (T τ₀ : ℝ) {A B₀ : ℝ} (hB₀ : 0 ≤ B₀)
    (hfam : ∀ t, famSum W Q (fun _ χ => nuChi PS Qs χ t ^ 2) ≤ W.H Q * (A + B₀ * |t|)) (t : ℝ) :
    famSum W Q (fun _ χ => ∫ t', Ek PS Qs T τ₀ t t' * nuChi PS Qs χ t * nuChi PS Qs χ t') ≤
      (2 * PS.aInt * CU ^ 2 * Clat * PS.L Qs ^ 4) *
        rho (PS.L Qs * Dd ((1 + PS.θ) * T) ((2 - PS.θ) * T) t) ^ 3 *
        (W.H Q * (A + B₀ * |t|) * (I0 / PS.L Qs) + W.H Q * B₀ / 2 * (I1 / PS.L Qs ^ 2)) := by
  have hL := PS.L_pos hQs
  have ha := aInt_pos' PS
  have hH := W.H_nonneg Q
  set L := PS.L Qs
  set d3 := rho (L * Dd ((1 + PS.θ) * T) ((2 - PS.θ) * T) t) ^ 3
  set C := 2 * PS.aInt * CU ^ 2 * Clat * L ^ 4 * d3 with hCdef
  have hd3 : 0 ≤ d3 := pow_nonneg (rho_nonneg _) 3
  have hC : 0 ≤ C := by
    have := Clat_nonneg; positivity
  rw [famSum_integral W Q (fun q χ => (perChi PS hStir hQs T τ₀ χ).1 t)]
  obtain ⟨hi, hv⟩ := inner_integral hL t (C * (W.H Q * (A + B₀ * |t|))) (C * (W.H Q * B₀ / 2))
  have hbound : ∀ t', famSum W Q
      (fun q χ => Ek PS Qs T τ₀ t t' * nuChi PS Qs χ t * nuChi PS Qs χ t') ≤
      C * (W.H Q * (A + B₀ * |t|)) * rho (L * (t' - t)) ^ 3 +
        C * (W.H Q * B₀ / 2) * (rho (L * (t' - t)) ^ 3 * |t' - t|) := by
    intro t'
    have e : famSum W Q (fun q χ => Ek PS Qs T τ₀ t t' * nuChi PS Qs χ t * nuChi PS Qs χ t') =
        Ek PS Qs T τ₀ t t' * famSum W Q (fun q χ => nuChi PS Qs χ t * nuChi PS Qs χ t') := by
      rw [← famSum_mul_left]; congr 1; funext q χ; ring
    rw [e]
    set S := famSum W Q (fun q χ => nuChi PS Qs χ t * nuChi PS Qs χ t')
    have hup : S ≤ (famSum W Q (fun _ χ => nuChi PS Qs χ t ^ 2) +
        famSum W Q (fun _ χ => nuChi PS Qs χ t' ^ 2)) / 2 := by
      have := famSum_mono W Q (f := fun q χ => nuChi PS Qs χ t * nuChi PS Qs χ t')
        (g := fun q χ => (1 / 2) * (nuChi PS Qs χ t ^ 2 + nuChi PS Qs χ t' ^ 2))
        (fun q _ χ => by nlinarith [sq_nonneg (nuChi PS Qs χ t - nuChi PS Qs χ t')])
      rw [famSum_mul_left, famSum_add] at this
      linarith
    have hlo : -S ≤ (famSum W Q (fun _ χ => nuChi PS Qs χ t ^ 2) +
        famSum W Q (fun _ χ => nuChi PS Qs χ t' ^ 2)) / 2 := by
      have := famSum_mono W Q (f := fun q χ => (-1) * (nuChi PS Qs χ t * nuChi PS Qs χ t'))
        (g := fun q χ => (1 / 2) * (nuChi PS Qs χ t ^ 2 + nuChi PS Qs χ t' ^ 2))
        (fun q _ χ => by nlinarith [sq_nonneg (nuChi PS Qs χ t + nuChi PS Qs χ t')])
      rw [famSum_mul_left, famSum_mul_left, famSum_add] at this
      linarith
    have ht' : W.H Q * (A + B₀ * |t'|) ≤ W.H Q * (A + B₀ * |t|) + W.H Q * B₀ * |t' - t| := by
      have : |t'| ≤ |t| + |t' - t| := by have := abs_sub_abs_le_abs_sub t' t; linarith
      have := mul_le_mul_of_nonneg_left this (mul_nonneg hH hB₀)
      nlinarith
    have hS : |S| ≤ W.H Q * (A + B₀ * |t|) + W.H Q * B₀ / 2 * |t' - t| := by
      have h1 := hfam t
      have h2 := hfam t'
      rw [abs_le]; constructor <;> linarith
    have hE := Ek_bound PS hCU hQs T τ₀ t t'
    have hr : rho (L * (t - t')) = rho (L * (t' - t)) := by
      rw [← rho_neg]; congr 1; ring
    rw [hr] at hE
    have hr0 := pow_nonneg (rho_nonneg (L * (t' - t))) 3
    calc Ek PS Qs T τ₀ t t' * S ≤ |Ek PS Qs T τ₀ t t' * S| := le_abs_self _
      _ = |Ek PS Qs T τ₀ t t'| * |S| := abs_mul _ _
      _ ≤ (C * rho (L * (t' - t)) ^ 3) *
          (W.H Q * (A + B₀ * |t|) + W.H Q * B₀ / 2 * |t' - t|) := by
          refine mul_le_mul (le_of_eq_of_le rfl (hE.trans (le_of_eq ?_))) hS (abs_nonneg _)
            (mul_nonneg hC hr0)
          simp only [hCdef, d3]; ring
      _ = _ := by ring
  refine (integral_mono (famSum_integrable W Q fun q χ => (perChi PS hStir hQs T τ₀ χ).1 t) hi
    hbound).trans (le_of_eq ?_)
  rw [hv]; simp only [hCdef]; ring

/-! ### Final arithmetic -/

lemma err_arithH {ℓ ℓs T lam C₂ I0 I1 A₁ A₂ B₀ D Z : ℝ} (hℓ : 1 ≤ ℓ) (hℓs : ℓ ≤ ℓs)
    (hT : 1 ≤ T) (hlam : 0 < lam) (hC₂ : 0 ≤ C₂) (hI0 : 0 ≤ I0) (hI1 : 0 ≤ I1) (hA₁ : 0 ≤ A₁)
    (hA₂ : 0 ≤ A₂) (hB₀ : 0 ≤ B₀) (hD : 0 < D) (_hZ : 0 ≤ Z)
    (h1 : 3 * ((C₂ * I0 ^ 2 * lam ^ 2 * (128 + 2 * A₁) + 3 * C₂ * B₀ * I0 * I1 * lam) +
      3 * B₀ * C₂ * I0 ^ 2 * lam ^ 2) ≤ D * ℓs)
    (h2 : 3 * (2 * A₂ * C₂ * I0 ^ 2 * lam ^ 5) * Z ≤ D * T) :
    C₂ * ((lam * ℓs) ^ 2 * I0 ^ 2 * (2 * (4 * (ℓ + 3) ^ 2 + A₁ + A₂ * Z * (lam * ℓs) ^ 3) +
      B₀ * (3 * T)) + 3 * B₀ * I0 * I1 * (lam * ℓs)) ≤ D * ℓs ^ 5 * T := by
  set M₁ := C₂ * I0 ^ 2 * lam ^ 2 * (128 + 2 * A₁) + 3 * C₂ * B₀ * I0 * I1 * lam with hM₁
  set M₂ := 2 * A₂ * C₂ * I0 ^ 2 * lam ^ 5 with hM₂
  set M₃ := 3 * B₀ * C₂ * I0 ^ 2 * lam ^ 2 with hM₃
  have hM₁0 : 0 ≤ M₁ := by positivity
  have hM₂0 : 0 ≤ M₂ := by positivity
  have hM₃0 : 0 ≤ M₃ := by positivity
  have hℓs1 : 1 ≤ ℓs := le_trans hℓ hℓs
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hℓs0 : 0 ≤ ℓs := by linarith
  have hℓ2 : ℓs ^ 2 ≤ ℓs ^ 4 := pow_le_pow_right₀ hℓs1 (by norm_num)
  have hℓ14 : ℓs ≤ ℓs ^ 4 := by
    have := pow_le_pow_right₀ hℓs1 (show 1 ≤ 4 by norm_num); simpa using this
  have hℓ35 : ℓs ^ 3 ≤ ℓs ^ 5 := pow_le_pow_right₀ hℓs1 (by norm_num)
  have h16 : (ℓ + 3) ^ 2 ≤ 16 * ℓs ^ 2 := by nlinarith
  have s1 : C₂ * ((lam * ℓs) ^ 2 * I0 ^ 2 * (2 * (4 * (ℓ + 3) ^ 2 + A₁ + A₂ * Z * (lam * ℓs) ^ 3) +
      B₀ * (3 * T)) + 3 * B₀ * I0 * I1 * (lam * ℓs)) ≤
      M₁ * ℓs ^ 4 + M₂ * Z * ℓs ^ 5 + M₃ * ℓs ^ 2 * T := by
    have t1 : C₂ * lam ^ 2 * I0 ^ 2 * 8 * ℓs ^ 2 * (ℓ + 3) ^ 2 ≤
        C₂ * lam ^ 2 * I0 ^ 2 * 8 * ℓs ^ 2 * (16 * ℓs ^ 2) :=
      mul_le_mul_of_nonneg_left h16 (by positivity)
    have t2 : C₂ * lam ^ 2 * I0 ^ 2 * 2 * A₁ * ℓs ^ 2 ≤ C₂ * lam ^ 2 * I0 ^ 2 * 2 * A₁ * ℓs ^ 4 :=
      mul_le_mul_of_nonneg_left hℓ2 (by positivity)
    have t3 : 3 * C₂ * B₀ * I0 * I1 * lam * ℓs ≤ 3 * C₂ * B₀ * I0 * I1 * lam * ℓs ^ 4 :=
      mul_le_mul_of_nonneg_left hℓ14 (by positivity)
    have e : C₂ * ((lam * ℓs) ^ 2 * I0 ^ 2 * (2 * (4 * (ℓ + 3) ^ 2 + A₁ + A₂ * Z * (lam * ℓs) ^ 3) +
        B₀ * (3 * T)) + 3 * B₀ * I0 * I1 * (lam * ℓs)) =
        C₂ * lam ^ 2 * I0 ^ 2 * 8 * ℓs ^ 2 * (ℓ + 3) ^ 2 + C₂ * lam ^ 2 * I0 ^ 2 * 2 * A₁ * ℓs ^ 2 +
        M₂ * Z * ℓs ^ 5 + M₃ * ℓs ^ 2 * T + 3 * C₂ * B₀ * I0 * I1 * lam * ℓs := by
      rw [hM₂, hM₃]; ring
    have e2 : M₁ * ℓs ^ 4 = C₂ * lam ^ 2 * I0 ^ 2 * 8 * ℓs ^ 2 * (16 * ℓs ^ 2) +
        C₂ * lam ^ 2 * I0 ^ 2 * 2 * A₁ * ℓs ^ 4 + 3 * C₂ * B₀ * I0 * I1 * lam * ℓs ^ 4 := by
      rw [hM₁]; ring
    rw [e, e2]
    linarith
  have s2 : M₁ * ℓs ^ 4 + M₂ * Z * ℓs ^ 5 + M₃ * ℓs ^ 2 * T ≤ D * ℓs ^ 5 * T := by
    have e1 : 3 * M₁ ≤ D * ℓs := by linarith
    have e3 : 3 * M₃ ≤ D * ℓs := by linarith
    have hℓ4 : 0 ≤ ℓs ^ 4 := by positivity
    have hℓ5 : 0 ≤ ℓs ^ 5 := by positivity
    have u1 : 3 * M₁ * ℓs ^ 4 ≤ D * ℓs * ℓs ^ 4 := mul_le_mul_of_nonneg_right e1 hℓ4
    have u1' : D * ℓs ^ 5 ≤ D * ℓs ^ 5 * T := by
      have := mul_le_mul_of_nonneg_left hT (by positivity : 0 ≤ D * ℓs ^ 5); linarith
    have u2 : 3 * M₂ * Z * ℓs ^ 5 ≤ D * T * ℓs ^ 5 := mul_le_mul_of_nonneg_right h2 hℓ5
    have u3 : 3 * M₃ * (ℓs ^ 2 * T) ≤ D * ℓs * (ℓs ^ 2 * T) :=
      mul_le_mul_of_nonneg_right e3 (by positivity)
    have u3' : D * ℓs ^ 3 * T ≤ D * ℓs ^ 5 * T :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hℓ35 hD.le) (by linarith)
    have r1 : D * ℓs * ℓs ^ 4 = D * ℓs ^ 5 := by ring
    have r3 : D * ℓs * (ℓs ^ 2 * T) = D * ℓs ^ 3 * T := by ring
    have r2 : D * T * ℓs ^ 5 = D * ℓs ^ 5 * T := by ring
    have r4 : 3 * M₃ * (ℓs ^ 2 * T) = 3 * (M₃ * ℓs ^ 2 * T) := by ring
    have r5 : 3 * M₁ * ℓs ^ 4 = 3 * (M₁ * ℓs ^ 4) := by ring
    have r6 : 3 * M₂ * Z * ℓs ^ 5 = 3 * (M₂ * Z * ℓs ^ 5) := by ring
    linarith
  linarith

/-! ### `eq:fc2H` -/

set_option maxHeartbeats 800000 in
/-- **`eq:fc2H`** (finite-centre replacement, upper half, at polynomial height):
`𝔐 ≤ 𝓜/(aL)² + o(HTℓ_*)`, uniformly on the cell, for each fixed `τ₀`. -/
theorem fc2H_proof (hMV : MV_LargeSieve) (hStir : StirlingDigamma) (hWH : lemWH_Statement)
    (P : HSetup) (W : Weight) (τ₀ : ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ P.heights Q,
      P.Mfrak W Q T τ₀ ≤ Mcal2 P.toPS W Q (Q * T) T / (P.aInt * P.L Q T) ^ 2 +
        δ * (W.H Q * T * ellS Q T) := by
  obtain ⟨CU, hCU0, hCU⟩ := U_bound P.toPS
  obtain ⟨A₁, B₀, C₀, Ca, Qa, hA₁, hB₀, hC₀, hCa, hfam0⟩ := famSum_nu_sq2 hMV hStir P.toPS W
  obtain ⟨cH, QH, hcH, hHl⟩ := H_lower hWH W
  have ha := aInt_pos' P.toPS
  have ha' : 0 < P.aInt := ha
  have hlam := P.lam_pos
  have hI0 := I0_nonneg
  have hI1 := I1_nonneg
  have hη := W.η_pos
  set C₂ := 2 * P.aInt * CU ^ 2 * Clat with hC₂def
  have hC₂ : 0 ≤ C₂ := by have := Clat_nonneg; positivity
  set D := δ * P.aInt ^ 2 * P.lam ^ 4 with hDdef
  have hD : 0 < D := by
    have : 0 < P.aInt := ha
    positivity
  set A₂ := 2 * (|W.wmax| * C₀ * Ca) / cH with hA₂def
  have hA₂ : 0 ≤ A₂ := by positivity
  set M₁ := C₂ * I0 ^ 2 * P.lam ^ 2 * (128 + 2 * A₁) + 3 * C₂ * B₀ * I0 * I1 * P.lam with hM₁def
  set M₂ := 2 * A₂ * C₂ * I0 ^ 2 * P.lam ^ 5 with hM₂def
  set M₃ := 3 * B₀ * C₂ * I0 ^ 2 * P.lam ^ 2 with hM₃def
  have hM₂0 : 0 ≤ M₂ := by positivity
  set ηs : ℝ := D / (3 * (M₂ + 1)) with hηs
  have hηs0 : 0 < ηs := by positivity
  obtain ⟨Qη, hQη⟩ := sieve_loss_small P ηs hηs0
  obtain ⟨QL, hQL⟩ := L_large P (3 * (M₁ + M₃) / D + 1)
  refine ⟨max (max (max Qa QH) (max Qη QL)) (max (Real.exp 1) (2 / W.η)), fun Q hQ T hT => ?_⟩
  have hQa' : Qa ≤ Q := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
    (le_max_left _ _))) hQ
  have hQH' : QH ≤ Q := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
    (le_max_left _ _))) hQ
  have hQη' : Qη ≤ Q := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hQ
  have hQL' : QL ≤ Q := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hQ
  have hQe : Real.exp 1 ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hQ
  have hQη2 : 2 / W.η ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hQ
  obtain ⟨hT1, hℓ1, hℓs, hQQT, hQT, -⟩ := cell_facts P hQe hT
  have hQ1 : 1 < Q := one_lt_of_exp_one_le hQe
  have hQ0 : 0 < Q := by linarith
  have hT0 : 0 < T := by linarith
  have hLpos : 0 < P.L Q T := mul_pos hlam (by linarith)
  have hLpos' : 0 < P.toPS.L (Q * T) := hLpos
  have hH := W.H_nonneg Q
  have hℓM : 3 * (M₁ + M₃) ≤ D * ellS Q T := by
    have h := (hQL Q hQL' T hT).2
    have h' : 3 * (M₁ + M₃) / D ≤ ellS Q T := by linarith
    rw [div_le_iff₀ hD] at h'; linarith
  -- the family bound on the cell
  have hloss : Q ^ 2 + P.toPS.Y (Q * T) ≤ ηs * (Q ^ 2 * T) := hQη Q hQη' T hT
  have hQ2H : Q ^ 2 ≤ W.H Q / cH := by
    have := hHl Q hQH'
    rw [le_div_iff₀ hcH]; linarith
  set A := 4 * (Real.log Q + 3) ^ 2 + A₁ + A₂ * (ηs * T) * P.L Q T ^ 3 with hAdef
  have hA0 : 0 ≤ A := by
    have : 0 ≤ ηs * T := by positivity
    have : 0 ≤ P.L Q T ^ 3 := by positivity
    positivity
  have hfam' : ∀ t, famSum W Q (fun _ χ => nuChi P.toPS (Q * T) χ t ^ 2) ≤
      W.H Q * (A + B₀ * |t|) := by
    intro t
    refine (hfam0 Q (Q * T) hQ1.le (hQa'.trans hQQT) t).trans ?_
    have hLS : 2 * (|W.wmax| * C₀ * (Q ^ 2 + P.toPS.Y (Q * T)) * (Ca * P.toPS.L (Q * T) ^ 3)) ≤
        W.H Q * (A₂ * (ηs * T) * P.L Q T ^ 3) := by
      have hL3 : P.toPS.L (Q * T) ^ 3 = P.L Q T ^ 3 := rfl
      rw [hL3]
      have h1 : Q ^ 2 + P.toPS.Y (Q * T) ≤ ηs * (W.H Q / cH * T) :=
        hloss.trans (by gcongr)
      have hw : 0 ≤ |W.wmax| * C₀ := by positivity
      calc 2 * (|W.wmax| * C₀ * (Q ^ 2 + P.toPS.Y (Q * T)) * (Ca * P.L Q T ^ 3))
          ≤ 2 * (|W.wmax| * C₀ * (ηs * (W.H Q / cH * T)) * (Ca * P.L Q T ^ 3)) := by
            gcongr
        _ = W.H Q * (A₂ * (ηs * T) * P.L Q T ^ 3) := by
            rw [hA₂def]; field_simp
    have e : W.H Q * (A + B₀ * |t|) = W.H Q * (4 * (Real.log Q + 3) ^ 2 + A₁ + B₀ * |t|) +
        W.H Q * (A₂ * (ηs * T) * P.L Q T ^ 3) := by rw [hAdef]; ring
    rw [e]; linarith
  -- `𝔐` as a family sum of real Frobenius norms
  set K := P.KJ Q T τ₀
  set X : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ := fun q χ =>
    ∑ k ∈ K, ∑ l ∈ K, (∫ t, pr P.toPS (Q * T) τ₀ k t * pr P.toPS (Q * T) τ₀ l t *
      nuChi P.toPS (Q * T) χ t) ^ 2 with hXdef
  have hMfrak : P.Mfrak W Q T τ₀ = ((P.aInt * P.L Q T ^ 2) ^ 2)⁻¹ * famSum W Q X := by
    rw [← famSum_mul_left]
    unfold HSetup.Mfrak famSum
    refine Finset.sum_congr rfl fun q hq => ?_
    by_cases hω : W.omega Q q = 0
    · simp [hω]
    · congr 1
      refine Finset.sum_congr rfl fun χ hχ => ?_
      have hw : W.w (q / Q) ≠ 0 := by
        intro h; apply hω; unfold Weight.omega; rw [h]; ring
      have hprim : χ.IsPrimitive := mem_primChars.mp hχ
      have hq : 1 < q := by
        have hsupp := (W.supp _ hw).1
        rw [le_div_iff₀ hQ0] at hsupp
        rw [div_le_iff₀ hη] at hQη2
        have : (1 : ℝ) < q := by nlinarith
        exact_mod_cast this
      have hterm : ∀ k l : K, ‖P.Gabor Q T τ₀ χ k l / (P.aInt * P.L Q T ^ 2)‖ ^ 2 =
          ((P.aInt * P.L Q T ^ 2) ^ 2)⁻¹ *
            (∫ t, pr P.toPS (Q * T) τ₀ k t * pr P.toPS (Q * T) τ₀ l t *
              nuChi P.toPS (Q * T) χ t) ^ 2 := by
        intro k l
        have hG : P.Gabor Q T τ₀ χ k l = ∫ t : ℝ, P.toPS.pk (Q * T) τ₀ k t *
            P.toPS.pk (Q * T) τ₀ l t * (nuChi P.toPS (Q * T) χ t : ℂ) :=
          explicitGabor2 P.toPS hQT τ₀ χ hq hprim T k l
        rw [hG]
        have e : (fun t : ℝ => P.toPS.pk (Q * T) τ₀ k (t : ℂ) * P.toPS.pk (Q * T) τ₀ l (t : ℂ) *
            (nuChi P.toPS (Q * T) χ t : ℂ)) = fun t => ((pr P.toPS (Q * T) τ₀ k t *
              pr P.toPS (Q * T) τ₀ l t * nuChi P.toPS (Q * T) χ t : ℝ) : ℂ) := by
          funext t; rw [pk_eq P.toPS hQT, pk_eq P.toPS hQT]; push_cast; ring
        rw [e, integral_complex_ofReal, norm_div, Complex.norm_real, Real.norm_eq_abs, norm_mul,
          norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos ha', abs_of_pos hLpos, div_pow, sq_abs]
        field_simp
      set c := ((P.aInt * P.L Q T ^ 2) ^ 2)⁻¹
      calc ∑ k : K, ∑ l : K, ‖P.Gabor Q T τ₀ χ k l / (P.aInt * P.L Q T ^ 2)‖ ^ 2
          = ∑ k : K, ∑ l : K, c * (∫ t, pr P.toPS (Q * T) τ₀ k t * pr P.toPS (Q * T) τ₀ l t *
              nuChi P.toPS (Q * T) χ t) ^ 2 :=
            Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => hterm k l
        _ = ∑ k : K, c * ∑ l ∈ K, (∫ t, pr P.toPS (Q * T) τ₀ k t * pr P.toPS (Q * T) τ₀ l t *
              nuChi P.toPS (Q * T) χ t) ^ 2 := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_coe_sort K
              (fun l => c * (∫ t, pr P.toPS (Q * T) τ₀ k t * pr P.toPS (Q * T) τ₀ l t *
                nuChi P.toPS (Q * T) χ t) ^ 2)
        _ = ∑ k ∈ K, c * ∑ l ∈ K, (∫ t, pr P.toPS (Q * T) τ₀ k t * pr P.toPS (Q * T) τ₀ l t *
              nuChi P.toPS (Q * T) χ t) ^ 2 :=
            Finset.sum_coe_sort K
              (fun k => c * ∑ l ∈ K, (∫ t, pr P.toPS (Q * T) τ₀ k t *
                pr P.toPS (Q * T) τ₀ l t * nuChi P.toPS (Q * T) χ t) ^ 2)
        _ = c * X q χ := by rw [← Finset.mul_sum]
  -- `∑_χ ω_χ ∑_{k,l} G² − L² 𝓜 = ∫ ∑_χ ω_χ h_χ`
  have hdiff : famSum W Q X - P.L Q T ^ 2 * Mcal2 P.toPS W Q (Q * T) T =
      ∫ t, famSum W Q (fun q χ => ∫ t', Ek P.toPS (Q * T) T τ₀ t t' *
        nuChi P.toPS (Q * T) χ t * nuChi P.toPS (Q * T) χ t') := by
    unfold Mcal2
    rw [← famSum_mul_left, ← famSum_sub,
      ← famSum_integral W Q (fun q χ => (perChi P.toPS hStir hQT T τ₀ χ).2.1)]
    congr 1; funext q χ
    exact (perChi P.toPS hStir hQT T τ₀ χ).2.2
  -- the error integral
  obtain ⟨g, hgi, hgle, hgint⟩ := outer_bound hLpos ((1 + P.θ) * T) ((2 - P.θ) * T)
    (2 * P.aInt * CU ^ 2 * Clat * P.L Q T ^ 4) (W.H Q) A B₀
    (by have := Clat_nonneg; positivity) hH hA0 hB₀
  have hstep3 : ∫ t, famSum W Q (fun q χ => ∫ t', Ek P.toPS (Q * T) T τ₀ t t' *
      nuChi P.toPS (Q * T) χ t * nuChi P.toPS (Q * T) χ t') ≤ ∫ t, g t :=
    integral_mono (famSum_integrable W Q fun q χ => (perChi P.toPS hStir hQT T τ₀ χ).2.1) hgi
      (fun t => (famSum_h_le2 hStir P.toPS hCU W Q hQT T τ₀ hB₀ hfam' t).trans (hgle t))
  have hTM₂ : 3 * M₂ * (ηs * T) ≤ D * T := by
    have e : 3 * M₂ * (ηs * T) = (3 * M₂ * ηs) * T := by ring
    rw [e]
    apply mul_le_mul_of_nonneg_right _ hT0.le
    rw [hηs]
    have hM1 : 0 < M₂ + 1 := by linarith
    rw [show 3 * M₂ * (D / (3 * (M₂ + 1))) = D * (M₂ / (M₂ + 1)) by field_simp]
    have : M₂ / (M₂ + 1) ≤ 1 := by rw [div_le_one hM1]; linarith
    nlinarith
  have key : C₂ * ((P.lam * ellS Q T) ^ 2 * I0 ^ 2 * (2 * (4 * (Real.log Q + 3) ^ 2 + A₁ +
      A₂ * (ηs * T) * (P.lam * ellS Q T) ^ 3) + B₀ * (3 * T)) +
      3 * B₀ * I0 * I1 * (P.lam * ellS Q T)) ≤ D * ellS Q T ^ 5 * T :=
    err_arithH hℓ1 hℓs hT1 hlam hC₂ hI0 hI1 hA₁ hA₂ hB₀ hD (by positivity) hℓM hTM₂
  have hErr : ∫ t, g t ≤ δ * (P.aInt * P.L Q T ^ 2) ^ 2 * (W.H Q * T * ellS Q T) := by
    rw [hgint]
    have hθ1 : 0 < (1 + P.θ) * T := by have := P.θ_pos; positivity
    have hθ2 : 0 < (2 - P.θ) * T := mul_pos (by linarith [P.θ_lt]) hT0
    rw [abs_of_pos hθ1, abs_of_pos hθ2]
    have hLdef : P.L Q T = P.lam * ellS Q T := rfl
    have hL0 : P.L Q T ≠ 0 := hLpos.ne'
    calc _ = W.H Q * (C₂ * (P.L Q T ^ 2 * I0 ^ 2 * (2 * (4 * (Real.log Q + 3) ^ 2 + A₁ +
          A₂ * (ηs * T) * P.L Q T ^ 3) + B₀ * (3 * T)) + 3 * B₀ * I0 * I1 * P.L Q T)) := by
          rw [hAdef, hC₂def]; field_simp; ring
      _ = W.H Q * (C₂ * ((P.lam * ellS Q T) ^ 2 * I0 ^ 2 * (2 * (4 * (Real.log Q + 3) ^ 2 + A₁ +
          A₂ * (ηs * T) * (P.lam * ellS Q T) ^ 3) + B₀ * (3 * T)) +
          3 * B₀ * I0 * I1 * (P.lam * ellS Q T))) := by rw [hLdef]
      _ ≤ W.H Q * (D * ellS Q T ^ 5 * T) := mul_le_mul_of_nonneg_left key hH
      _ = δ * (P.aInt * P.L Q T ^ 2) ^ 2 * (W.H Q * T * ellS Q T) := by
          rw [hDdef, hLdef]; ring
  have hfin : famSum W Q X ≤ P.L Q T ^ 2 * Mcal2 P.toPS W Q (Q * T) T +
      δ * (P.aInt * P.L Q T ^ 2) ^ 2 * (W.H Q * T * ellS Q T) := by
    linarith [hdiff, hstep3, hErr]
  rw [hMfrak]
  have hc : 0 < (P.aInt * P.L Q T ^ 2) ^ 2 := by
    have : 0 < P.aInt := ha
    positivity
  calc ((P.aInt * P.L Q T ^ 2) ^ 2)⁻¹ * famSum W Q X
      ≤ ((P.aInt * P.L Q T ^ 2) ^ 2)⁻¹ * (P.L Q T ^ 2 * Mcal2 P.toPS W Q (Q * T) T +
          δ * (P.aInt * P.L Q T ^ 2) ^ 2 * (W.H Q * T * ellS Q T)) :=
        mul_le_mul_of_nonneg_left hfin (inv_nonneg.mpr hc.le)
    _ = Mcal2 P.toPS W Q (Q * T) T / (P.aInt * P.L Q T) ^ 2 + δ * (W.H Q * T * ellS Q T) := by
        have : 0 < P.aInt := ha
        field_simp

end Families.Hybrid.S
