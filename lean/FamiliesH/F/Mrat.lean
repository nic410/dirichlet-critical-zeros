/-
# Package F: `eqB:MratH` (Lemma 9.11, second claim)

`∑ a_n a_m Δ 𝒦 = ∑ b_n b_m Δ 𝒦 + O(Q^{−A})` at height `T = Q^κ`. The families proof
(`Phase3.C.Mrat`) ports with the family at `Q` and the setup at `Q' = QT`:
* `lem:M1H` writes both sides as `∫ g(u) x_y(u)^*Δx_y(u) du`;
* `x_a = x_b + x_{a♯}` and `∑_n x_{a♯}(u)_n χ(n) = ∫_J e^{itu} S_χ[a♯](t) dt`, so `lem:B1H` (at the
  exponent `A + 10(1+κc)`) makes the `a♯`-part tiny for every family character and every `u`;
* the crude bounds `‖b‖₁ ≤ c (QT)⁶`, `|J| ≤ T`, `QT, T ≤ Q^{1+κc}` absorb the polynomial losses;
* integrating against `g` (`∫ g = (La)²`, `L ≤ λ Q^{1+κc}`) gives the claim.
-/
import FamiliesH.F.B1
import FamiliesH.F.M1
import Families.Phase3.C.Mrat

noncomputable section

open scoped ContDiff Nat ArithmeticFunction.Moebius
open Set ArithmeticFunction MeasureTheory

namespace Families.Hybrid

open Families Families.Phase3.C

namespace F

/-! ### The families integrability lemmas with the family at `Qf` and the setup at `Qs` -/

lemma continuous_famForm_xVec_gen (P : PrimeSetup) (W : Weight) (Qf Qs T : ℝ) (I : Finset ℤ)
    (y : ℕ → ℝ) : Continuous (fun u => famForm W Qf I (P.xVec Qs T y u)) := by
  unfold famForm
  refine continuous_finsetSum _ fun q _ => continuous_const.mul
    (continuous_finsetSum _ fun χ _ => ?_)
  refine (continuous_norm.comp (continuous_finsetSum _ fun n _ => ?_)).pow 2
  refine Continuous.mul ?_ continuous_const
  unfold PrimeSetup.xVec
  split_ifs
  · exact continuous_const.mul ((P.hatJ_continuous T).comp (continuous_id.sub continuous_const))
  · exact continuous_const

lemma famForm_xVec_le_gen (P : PrimeSetup) (W : Weight) (Qf Qs T : ℝ) (I : Finset ℤ) (y : ℕ → ℝ)
    (u : ℝ) :
    famForm W Qf I (P.xVec Qs T y u) ≤
      ∑ q ∈ Finset.Icc 1 ⌊Qf⌋₊, W.omega Qf q * ∑ _χ ∈ primChars q,
        (∑ n ∈ I, |y n.toNat| * volume.real (P.J T)) ^ 2 := by
  unfold famForm
  refine Finset.sum_le_sum fun q _ => ?_
  have hω : 0 ≤ W.omega Qf q := by
    unfold Weight.omega
    exact div_nonneg (mul_nonneg (W.nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun χ _ => ?_) hω
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [norm_mul]
  have h1 : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
  have h2 : ‖P.xVec Qs T y u n‖ ≤ |y n.toNat| * volume.real (P.J T) := by
    unfold PrimeSetup.xVec
    split_ifs
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (P.hatJ_norm_le T _) (abs_nonneg _)
    · rw [norm_zero]; exact mul_nonneg (abs_nonneg _) measureReal_nonneg
  calc ‖P.xVec Qs T y u n‖ * ‖χ n‖ ≤ ‖P.xVec Qs T y u n‖ * 1 :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ ≤ _ := by rw [mul_one]; exact h2

lemma integrable_g_famForm_gen (P : PrimeSetup) {Qs : ℝ} (hQs : 1 < Qs) (W : Weight) (Qf T : ℝ)
    (y : ℕ → ℝ) :
    Integrable (fun u => P.g Qs u * famForm W Qf (P.rangeZ Qs) (P.xVec Qs T y u)) := by
  refine (P.g_integrable hQs).mul_bdd (c := ∑ q ∈ Finset.Icc 1 ⌊Qf⌋₊, W.omega Qf q *
      ∑ χ ∈ primChars q, (∑ n ∈ P.rangeZ Qs, |y n.toNat| * volume.real (P.J T)) ^ 2)
    (continuous_famForm_xVec_gen P W Qf Qs T _ y).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (famForm_nonneg' W Qf _ _)]
  exact famForm_xVec_le_gen P W Qf Qs T _ y u

/-! ### The final arithmetic -/

lemma final_arithH {Q T A w cb CB' x M : ℝ} (hM1 : 1 ≤ M) (hQ0 : 0 ≤ Q) (hQM : Q ≤ M)
    (hT0 : 0 ≤ T) (hTM : T ≤ M) (hQTM : Q * T ≤ M)
    (hw : 0 ≤ w) (hcb : 0 ≤ cb) (hCB : 0 ≤ CB') (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hxM : x * M ^ 10 ≤ Q ^ (-A)) :
    w * Q ^ 2 * (CB' * x * T * (2 * (cb * (Q * T) ^ 6 * T) + CB' * x * T)) ≤
      w * CB' * (2 * cb + CB') * Q ^ (-A) := by
  have hM0 : 0 ≤ M := by linarith
  have hQT0 : 0 ≤ Q * T := mul_nonneg hQ0 hT0
  have hM7 : M ≤ M ^ 7 := by
    calc M = M ^ 1 := (pow_one M).symm
      _ ≤ M ^ 7 := pow_le_pow_right₀ hM1 (by norm_num)
  have hK : 0 ≤ w * CB' * (2 * cb + CB') := by positivity
  calc w * Q ^ 2 * (CB' * x * T * (2 * (cb * (Q * T) ^ 6 * T) + CB' * x * T))
      ≤ w * M ^ 2 * (CB' * x * M * (2 * (cb * M ^ 6 * M) + CB' * 1 * M)) := by
        gcongr
    _ = w * CB' * x * M ^ 3 * (2 * cb * M ^ 7 + CB' * M) := by ring
    _ ≤ w * CB' * x * M ^ 3 * (2 * cb * M ^ 7 + CB' * M ^ 7) := by gcongr
    _ = w * CB' * (2 * cb + CB') * (x * M ^ 10) := by ring
    _ ≤ w * CB' * (2 * cb + CB') * Q ^ (-A) := mul_le_mul_of_nonneg_left hxM hK

end F

namespace HSetup

open Families.Hybrid.F

variable (P : HSetup)

/-- The real form of `lem:M1H`: `∑ y_n y_m Δ 𝒦 = ∫ g(u) x_y(u)^*Δ x_y(u) du`. -/
lemma ratioForm_eq_ofRealH {Q T : ℝ} (hQ : 1 < Q) (hT : 0 < T) (W : Weight) (y : ℕ → ℝ) :
    P.ratioForm W Q T y =
      ((∫ u, P.g Q T u * famForm W Q (P.rangeZ Q T) (P.xVec Q T y u) : ℝ) : ℂ) := by
  rw [(lemM1H_proof P Q T hQ hT).2 W y, ← integral_complex_ofReal]
  congr 1; funext u; push_cast; ring

/-- `x_a = x_b + x_{a♯}`. -/
lemma xVec_split (Q T u : ℝ) :
    P.xVec Q T (P.aVec Q T) u = P.xVec Q T (P.bVec Q T) u + P.xVec Q T (P.aSharp Q T) u := by
  funext n
  simp only [HSetup.xVec, Pi.add_apply, HSetup.bVec]
  split_ifs
  · push_cast; ring
  · simp

/-- On the cell, `T ≤ Q^{κc}`, hence `T, QT ≤ Q^{1+κc}`. -/
lemma cell_bounds {Q T : ℝ} (hQ1 : 1 ≤ Q) (hT1 : 1 ≤ T) (hT : T ∈ P.heights Q) :
    1 ≤ Q ^ (1 + P.kc) ∧ Q ≤ Q ^ (1 + P.kc) ∧ T ≤ Q ^ (1 + P.kc) ∧ Q * T ≤ Q ^ (1 + P.kc) := by
  have hkc := P.kc_pos
  have hQ0 : 0 < Q := by linarith
  have hTk : T ≤ Q ^ P.kc := hT.2
  have hsplit : Q ^ (1 + P.kc) = Q * Q ^ P.kc := by
    rw [Real.rpow_add hQ0, Real.rpow_one]
  have hk1 : 1 ≤ Q ^ P.kc := Real.one_le_rpow hQ1 hkc.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hsplit]; nlinarith
  · rw [hsplit]; nlinarith
  · rw [hsplit]; nlinarith
  · rw [hsplit]; exact mul_le_mul_of_nonneg_left hTk hQ0.le

/-- Step 0 at height `T = Q^κ`: `|x_a^*Δx_a − x_b^*Δx_b| ≤ C Q^{−A}` for every `u`. -/
theorem famForm_ab_closeH (W : Weight) (A : ℝ) (hA : 0 < A) :
    ∃ C Q₀ : ℝ, 0 ≤ C ∧ ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ P.heights Q, ∀ u : ℝ,
      |famForm W Q (P.rangeZ Q T) (P.xVec Q T (P.aVec Q T) u) -
        famForm W Q (P.rangeZ Q T) (P.xVec Q T (P.bVec Q T) u)| ≤ C * Q ^ (-A) := by
  have hkc := P.kc_pos
  set A' : ℝ := A + 10 * (1 + P.kc) with hA'
  obtain ⟨CB, QB, hB1⟩ := lemB1H_proof P W A' (by positivity)
  obtain ⟨cb, hcb0, hcb⟩ := sum_abs_bVec_le P.toPS
  set CB' : ℝ := max CB 1 with hCB'
  have hCB'1 : 1 ≤ CB' := le_max_right _ _
  refine ⟨W.wmax * CB' * (2 * cb + CB'), max QB (Real.exp 1), by
    have := W.wmax_nonneg; positivity, ?_⟩
  intro Q hQ T hT u
  have hQB : QB ≤ Q := le_of_max_le_left hQ
  have hQe : Real.exp 1 ≤ Q := le_of_max_le_right hQ
  have hQ1 : 1 < Q :=
    lt_of_lt_of_le (by have := Real.add_one_lt_exp (x := 1) one_ne_zero; linarith) hQe
  have hQ0 : 0 < Q := by linarith
  have hT1 : 1 ≤ T := by
    have hl : 1 ≤ Real.log Q := by
      have := Real.log_le_log (Real.exp_pos _) hQe; rwa [Real.log_exp] at this
    exact le_trans (Real.one_le_rpow hl P.a0_pos.le) hT.1
  have hT0 : 0 ≤ T := by linarith
  have hQT1 : 1 < Q * T := by nlinarith
  obtain ⟨hM1, hQM, hTM, hQTM⟩ := P.cell_bounds hQ1.le hT1 hT
  rw [P.xVec_split]
  refine (famForm_sub_abs_le W Q _ _ _).trans ?_
  set x : ℝ := Q ^ (-A') with hxdef
  have hx1 : x ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hQ1.le (by linarith)
  have hx0 : 0 ≤ x := Real.rpow_nonneg hQ0.le _
  have hβ : ∀ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∀ χ ∈ primChars q, W.omega Q q ≠ 0 →
      ‖∑ n ∈ P.rangeZ Q T, P.xVec Q T (P.aSharp Q T) u n * χ n‖ ≤ CB' * x * T := by
    intro q _ χ hχ hω
    have hw : 0 < W.w (q / Q) := by
      have := W.nonneg (q / Q)
      rcases this.lt_or_eq with h | h
      · exact h
      · exfalso; apply hω; unfold Weight.omega; rw [← h]; simp
    have hfam : InFamily W Q q χ := ⟨mem_primChars.mp hχ, hw⟩
    refine norm_sum_xVec_char_le_of_Schi P.toPS χ (Q := Q * T) hT0 _ u fun t ht => ?_
    have htT : |t| ≤ 3 * T := by
      unfold PrimeSetup.J at ht
      have eθ : P.toPS.θ = P.θ := rfl
      rw [eθ] at ht
      rw [abs_le]
      have := P.θ_pos; have := P.θ_lt
      constructor <;> nlinarith [ht.1, ht.2]
    have h := hB1 Q hQB T hT q χ hfam t htT
    rw [P.Schi_eq] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hx0)
  have hbsum : ∑ n ∈ P.toPS.range (Q * T), |P.bVec Q T n| ≤ cb * (Q * T) ^ 6 := by
    rw [P.bVec_eq]; exact hcb (Q * T) 1 hQT1 (by linarith)
  have hα : ∀ q (χ : DirichletCharacter ℂ q),
      ‖∑ n ∈ P.rangeZ Q T, P.xVec Q T (P.bVec Q T) u n * χ n‖ ≤ cb * (Q * T) ^ 6 * T := by
    intro q χ
    exact (norm_sum_xVec_char_le P.toPS χ (Q := Q * T) hT0 _ u).trans
      (mul_le_mul_of_nonneg_right hbsum hT0)
  set E : ℝ := CB' * x * T * (2 * (cb * (Q * T) ^ 6 * T) + CB' * x * T) with hE
  have hterm : ∀ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ χ ∈ primChars q,
        ‖∑ n ∈ P.rangeZ Q T, P.xVec Q T (P.aSharp Q T) u n * χ n‖ *
          (2 * ‖∑ n ∈ P.rangeZ Q T, P.xVec Q T (P.bVec Q T) u n * χ n‖ +
            ‖∑ n ∈ P.rangeZ Q T, P.xVec Q T (P.aSharp Q T) u n * χ n‖) ≤
      W.omega Q q * ((primChars q).card : ℝ) * E := by
    intro q hq
    have hω : 0 ≤ W.omega Q q := by
      unfold Weight.omega
      exact div_nonneg (mul_nonneg (W.nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    rcases hω.lt_or_eq with hω | hω
    · rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hω.le
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum fun χ hχ => ?_
      have hb := hβ q hq χ hχ hω.ne'
      have ha := hα q χ
      have h0 : 0 ≤ ‖∑ n ∈ P.rangeZ Q T, P.xVec Q T (P.aSharp Q T) u n * χ n‖ := norm_nonneg _
      rw [hE]
      gcongr
    · rw [← hω]; simp
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  refine (mul_le_mul_of_nonneg_right (sum_omega_card_le W hQ1.le) hE0).trans ?_
  have hxM : x * (Q ^ (1 + P.kc)) ^ 10 ≤ Q ^ (-A) := by
    rw [hxdef, ← Real.rpow_natCast (Q ^ (1 + P.kc)) 10, ← Real.rpow_mul hQ0.le,
      ← Real.rpow_add hQ0]
    apply le_of_eq; congr 1; rw [hA']; push_cast; ring
  exact final_arithH hM1 hQ0.le hQM hT0 hTM hQTM W.wmax_nonneg hcb0 (by linarith) hx0 hx1 hxM

end HSetup

namespace F

/-- **`eqB:MratH`**, proved (from `lem:B1H` and `lem:M1H`). -/
theorem eqBMratH_proof : eqBMratH_Statement := by
  intro P W A hA
  have hkc := P.kc_pos
  obtain ⟨C, Q₀, hC0, hclose⟩ := P.famForm_ab_closeH W (A + 2 * (1 + P.kc)) (by positivity)
  refine ⟨C * (P.lam * P.aInt) ^ 2, max Q₀ (Real.exp 1), ?_⟩
  intro Q hQ T hT
  have hQ₀ : Q₀ ≤ Q := le_of_max_le_left hQ
  have hQe : Real.exp 1 ≤ Q := le_of_max_le_right hQ
  have hQ1 : 1 < Q :=
    lt_of_lt_of_le (by have := Real.add_one_lt_exp (x := 1) one_ne_zero; linarith) hQe
  have hQ0 : 0 < Q := by linarith
  have hT1 : 1 ≤ T := by
    have hl : 1 ≤ Real.log Q := by
      have := Real.log_le_log (Real.exp_pos _) hQe; rwa [Real.log_exp] at this
    exact le_trans (Real.one_le_rpow hl P.a0_pos.le) hT.1
  have hT0 : 0 < T := by linarith
  have hQT1 : 1 < Q * T := by nlinarith
  have hQT0 : 0 < Q * T := by linarith
  obtain ⟨-, -, -, hQTM⟩ := P.cell_bounds hQ1.le hT1 hT
  have hia : Integrable (fun u => P.g Q T u * famForm W Q (P.rangeZ Q T) (P.xVec Q T (P.aVec Q T) u)) :=
    integrable_g_famForm_gen P.toPS hQT1 W Q T _
  have hib : Integrable (fun u => P.g Q T u * famForm W Q (P.rangeZ Q T) (P.xVec Q T (P.bVec Q T) u)) :=
    integrable_g_famForm_gen P.toPS hQT1 W Q T _
  rw [P.ratioForm_eq_ofRealH hQ1 hT0 W, P.ratioForm_eq_ofRealH hQ1 hT0 W, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, ← integral_sub hia hib]
  have hbound : ∀ u, ‖P.g Q T u * famForm W Q (P.rangeZ Q T) (P.xVec Q T (P.aVec Q T) u) -
      P.g Q T u * famForm W Q (P.rangeZ Q T) (P.xVec Q T (P.bVec Q T) u)‖ ≤
        P.g Q T u * (C * Q ^ (-(A + 2 * (1 + P.kc)))) := by
    intro u
    have hg := P.toPS.g_nonneg (Q * T) u
    rw [← mul_sub, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, P.g_eq, abs_of_nonneg hg]
    exact mul_le_mul_of_nonneg_left (hclose Q hQ₀ T hT u) hg
  have hint : Integrable (fun u => P.g Q T u * (C * Q ^ (-(A + 2 * (1 + P.kc))))) :=
    (P.toPS.g_integrable hQT1).mul_const _
  refine (norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall hbound)).trans ?_
  have hgint : ∫ u, P.g Q T u = (P.toPS.L (Q * T) * P.toPS.aInt) ^ 2 := integral_g P.toPS hQT1
  rw [integral_mul_const, hgint]
  -- `(La)² · C Q^{−(A+2(1+κc))} ≤ C (λa)² Q^{−A}` since `L = λ log(QT) ≤ λ QT ≤ λ Q^{1+κc}`
  have hlog : Real.log (Q * T) ≤ Q * T := (Real.log_le_sub_one_of_pos hQT0).trans (by linarith)
  have ha0 : 0 ≤ P.toPS.aInt := integral_nonneg fun s => sq_nonneg _
  have hLQ : P.toPS.L (Q * T) * P.toPS.aInt ≤ P.lam * P.aInt * Q ^ (1 + P.kc) := by
    unfold PrimeSetup.L
    have := P.lam_pos
    have e1 : P.toPS.lam = P.lam := rfl
    have e2 : P.toPS.aInt = P.aInt := rfl
    rw [e1, e2] at *
    calc P.lam * Real.log (Q * T) * P.aInt ≤ P.lam * (Q ^ (1 + P.kc)) * P.aInt := by
          gcongr; exact hlog.trans hQTM
      _ = P.lam * P.aInt * Q ^ (1 + P.kc) := by ring
  have hL0 : 0 ≤ P.toPS.L (Q * T) * P.toPS.aInt := mul_nonneg (L_pos' P.toPS hQT1).le ha0
  have hpow : (Q ^ (1 + P.kc)) ^ 2 * Q ^ (-(A + 2 * (1 + P.kc))) = Q ^ (-A) := by
    rw [← Real.rpow_natCast (Q ^ (1 + P.kc)) 2, ← Real.rpow_mul hQ0.le, ← Real.rpow_add hQ0]
    congr 1; push_cast; ring
  calc (P.toPS.L (Q * T) * P.toPS.aInt) ^ 2 * (C * Q ^ (-(A + 2 * (1 + P.kc))))
      ≤ (P.lam * P.aInt * Q ^ (1 + P.kc)) ^ 2 * (C * Q ^ (-(A + 2 * (1 + P.kc)))) := by
        gcongr
    _ = C * (P.lam * P.aInt) ^ 2 * ((Q ^ (1 + P.kc)) ^ 2 * Q ^ (-(A + 2 * (1 + P.kc)))) := by ring
    _ = C * (P.lam * P.aInt) ^ 2 * Q ^ (-A) := by rw [hpow]

end F

end Families.Hybrid
