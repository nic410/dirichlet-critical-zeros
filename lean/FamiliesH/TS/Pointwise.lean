/-
# Package TS: Steps 0–4 of Proposition 9.18, pointwise in `u`

* `chain_iiiH`: the algebra of Step 4 with the tail `x_a^{t*}Δx_a^t` **kept** (the families proof bounds
  it by `M‖x_a^t‖²` with the global large sieve on `[1, Y]`, `M ≍ Q² + Y`, which is not `O(Q²)` once
  `Y ≫ Q²`; here the tails are integrated separately by `cor:tails`, `corTailsH_Statement`);
* `pointwise_core`: Steps 0–4 for abstract vectors on a finite set `I` — regimes (i), (ii) through the
  hypotheses `h1`, `h2`; regime (iii) through Step 0, the rough split, `lem:S` (`hR`), the sharp large
  sieve (`h3`, `h3'`), the large sieve for the prime powers (`h4`) and Step 4(b) (`h5`);
* Step 4(c): `∑_{n > x, n not Q-rough} a_n² ≤ 2√Y (log Y)³/x` (the families `sum_sq_aPP_le`, with `a` at
  `Q' = QT` and roughness at `Q`), hence `≤ 4μ³ℓ_*³Q^{−ε}` at `x = (QT)^{1+ε}/2`.
-/
import FamiliesH.TS.Levels

noncomputable section

open scoped BigOperators ContDiff
open Set MeasureTheory Filter Topology ArithmeticFunction

namespace Families.Hybrid

open Families Families.Phase3.C

namespace TS

/-- The algebra of Step 4 with the tail term `Fta` kept (from the families `chain_iii`). -/
lemma chain_iiiH {κ ε₀ M A₁ A₂ cH Fb Fa Fsa Fta FR FNR LR Lb Ls LNR Nb Ns Npp : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hM : 0 ≤ M) (hcH : 0 ≤ cH) (hNpp : 0 ≤ Npp) (hLs0 : 0 ≤ Ls)
    (h0 : Fb ≤ Fa + ε₀) (h1 : Fa ≤ (1 + κ) * Fsa + (1 + κ⁻¹) * Fta)
    (h3 : Fsa ≤ (1 + κ) * FR + (1 + κ⁻¹) * FNR) (h4 : FNR ≤ M * Npp) (h5 : FR ≤ LR)
    (h6 : LR ≤ (1 + κ) * Lb + (1 + κ⁻¹) * (2 * Ls + 2 * LNR)) (h7 : Lb ≤ cH * Nb)
    (h8 : LNR ≤ cH * Npp) (h9 : Ls ≤ A₁ * Ns + A₂) :
    Fb ≤ (1 + κ) ^ 3 * cH * Nb + ((1 + κ⁻¹) * Fta + 8 * (1 + κ⁻¹) * (A₁ * Ns + A₂) +
      (1 + κ⁻¹) * (8 * cH + 2 * M) * Npp + ε₀) := by
  have h0' : Fb - (1 + κ⁻¹) * Fta ≤ Fa - (1 + κ⁻¹) * Fta + ε₀ := by linarith
  have h1' : Fa - (1 + κ⁻¹) * Fta ≤ (1 + κ) * Fsa + (1 + κ⁻¹) * 0 := by linarith
  have h2' : (0 : ℝ) ≤ M * 0 := by simp
  have key := chain_iii (κ := κ) (ε₀ := ε₀) (M := M) (A₁ := A₁) (A₂ := A₂) (cH := cH)
    (Fb := Fb - (1 + κ⁻¹) * Fta) (Fa := Fa - (1 + κ⁻¹) * Fta) (Fsa := Fsa) (Fta := 0) (FR := FR)
    (FNR := FNR) (LR := LR) (Lb := Lb) (Ls := Ls) (LNR := LNR) (Nb := Nb) (Nta := 0) (Ns := Ns)
    (Npp := Npp) hκ hκ1 hM hcH hNpp hLs0 h0' h1' h2' h3 h4 h5 h6 h7 h8 h9
  simp only [mul_zero, zero_add] at key
  linarith

/-- **Steps 0–4, pointwise in `u`**, for abstract vectors on a finite set `I`:
`x_b = x_b^s + x_b^t`, `x_a = x_a^s + x_a^t`, `x_a^s = x_R + x_{NR}`, `x_R = x_b^s + (x♯^s − x_{NR})`. -/
theorem pointwise_core (W : Weight) {Q : ℝ} (hQ : 0 < Q) (I : Finset ℤ)
    {ℓ ε κ c₁ c₂ c₃ M A₁ A₂ ε₀ u : ℝ} (hε : 0 ≤ ε) (hℓ : 0 < ℓ) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hH : 0 ≤ W.H Q) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃) (hM : 0 ≤ M) (hA₁ : 0 ≤ A₁)
    (hA₂ : 0 ≤ A₂) (hε₀ : 0 ≤ ε₀)
    (xb xa xsb xtb xsa xta xsR xsNR xsS xsPP : ℤ → ℂ)
    (eb : xb = xsb + xtb) (ea : xa = xsa + xta) (eaR : xsa = xsR + xsNR)
    (eR : xsR = xsb + (xsS - xsNR))
    (h0 : famForm W Q I xb ≤ famForm W Q I xa + ε₀)
    (h1 : u ≤ (1 - ε) * ℓ → famForm W Q I xsb ≤ c₁ * W.H Q * normSq I xsb)
    (h2 : u ≤ (1 + ε) * ℓ → famForm W Q I xsb ≤ c₂ * W.H Q * normSq I xsb)
    (h3 : (1 + ε) * ℓ < u → levelForm (levels Q) (aNat W Q) I xsb ≤ c₃ * W.H Q * normSq I xsb)
    (h3' : (1 + ε) * ℓ < u →
      levelForm (levels Q) (aNat W Q) I xsPP ≤ c₃ * W.H Q * normSq I xsPP)
    (h4 : (1 + ε) * ℓ < u → famForm W Q I xsPP ≤ M * normSq I xsPP)
    (h5 : levelForm (levels Q) (aNat W Q) I xsS ≤ A₁ * normSq I xsS + A₂)
    (h6 : (1 + ε) * ℓ < u → xsNR = xsPP)
    (hR : famForm W Q I xsR ≤ levelForm (levels Q) (aNat W Q) I xsR) :
    famForm W Q I xb ≤ (1 + κ) ^ 3 * (cfun ℓ ε c₁ c₂ c₃ u * W.H Q) * normSq I xsb +
      ((1 + κ⁻¹) * (famForm W Q I xta + famForm W Q I xtb) +
        8 * (1 + κ⁻¹) * (A₁ * normSq I xsS + A₂) +
        (1 + κ⁻¹) * (8 * (c₃ * W.H Q) + 2 * M) * normSq I xsPP + ε₀) := by
  set F := famForm W Q I with hF
  set LF := levelForm (levels Q) (aNat W Q) I with hLF
  set N := normSq I with hN
  have hb0 : 0 ≤ 1 + κ⁻¹ := by have := inv_pos.mpr hκ; linarith
  have ha1 : 1 ≤ 1 + κ := by linarith
  have hNn : ∀ z, 0 ≤ N z := fun z => normSq_nonneg' _ _
  have hFn : ∀ z, 0 ≤ F z := fun z => famForm_nonneg' W Q _ _
  have hLFn : ∀ z, 0 ≤ LF z := fun z =>
    Families.Phase3.C.levelForm_nonneg (fun e he => aNat_nonneg W Q hQ e he) _ _
  set E := (1 + κ⁻¹) * (F xta + F xtb) + 8 * (1 + κ⁻¹) * (A₁ * N xsS + A₂) +
      (1 + κ⁻¹) * (8 * (c₃ * W.H Q) + 2 * M) * N xsPP + ε₀ with hE
  have t1 : 0 ≤ (1 + κ⁻¹) * F xta := mul_nonneg hb0 (hFn _)
  have t1' : 0 ≤ (1 + κ⁻¹) * F xtb := mul_nonneg hb0 (hFn _)
  have t2 : 0 ≤ 8 * (1 + κ⁻¹) * (A₁ * N xsS + A₂) := by have := hNn xsS; positivity
  have t3 : 0 ≤ (1 + κ⁻¹) * (8 * (c₃ * W.H Q) + 2 * M) * N xsPP := by
    have := hNn xsPP; positivity
  have hEb : (1 + κ⁻¹) * F xtb ≤ E := by rw [hE]; nlinarith
  have hEa : (1 + κ⁻¹) * F xta + 8 * (1 + κ⁻¹) * (A₁ * N xsS + A₂) +
      (1 + κ⁻¹) * (8 * (c₃ * W.H Q) + 2 * M) * N xsPP + ε₀ ≤ E := by rw [hE]; nlinarith
  by_cases hreg : u ≤ (1 + ε) * ℓ
  · -- regimes (i), (ii)
    set c := cfun ℓ ε c₁ c₂ c₃ u with hc
    have hc0 : 0 ≤ c := cfun_nonneg hc₁ hc₂ hc₃ u
    have hbound : F xsb ≤ c * W.H Q * N xsb := by
      rw [hc]; unfold cfun
      split_ifs with h
      · exact h1 h
      · exact h2 hreg
    have hsplit := lemM3_i W Q I xsb xtb κ hκ
    rw [← eb] at hsplit
    have hcHN : 0 ≤ c * W.H Q * N xsb := by have := hNn xsb; positivity
    have ha3 : (1 + κ) ≤ (1 + κ) ^ 3 := le_self_pow₀ ha1 (by norm_num)
    calc F xb ≤ (1 + κ) * F xsb + (1 + κ⁻¹) * F xtb := hsplit
      _ ≤ (1 + κ) * (c * W.H Q * N xsb) + (1 + κ⁻¹) * F xtb :=
          add_le_add (mul_le_mul_of_nonneg_left hbound (by linarith)) le_rfl
      _ ≤ (1 + κ) ^ 3 * (c * W.H Q * N xsb) + E :=
          add_le_add (mul_le_mul_of_nonneg_right ha3 hcHN) hEb
      _ = _ := by ring
  · -- regime (iii)
    replace hreg := not_le.mp hreg
    have hcf : cfun ℓ ε c₁ c₂ c₃ u = c₃ := by
      unfold cfun
      rw [if_neg (by nlinarith), if_neg (by linarith)]
    rw [hcf]
    have e1 := lemM3_i W Q I xsa xta κ hκ
    rw [← ea] at e1
    have e3 := lemM3_i W Q I xsR xsNR κ hκ
    rw [← eaR] at e3
    have e6 := levelForm_add_le (fun e he => aNat_nonneg W Q hQ e he) I xsb (xsS - xsNR) hκ
    rw [← eR] at e6
    have e6' := levelForm_sub_le (fun e he => aNat_nonneg W Q hQ e he) I xsS xsNR
    have e6'' : LF xsR ≤ (1 + κ) * LF xsb + (1 + κ⁻¹) * (2 * LF xsS + 2 * LF xsNR) :=
      e6.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left e6' hb0))
    have hPP := h6 hreg
    have h4' : F xsNR ≤ M * N xsPP := by rw [hPP]; exact h4 hreg
    have h8' : LF xsNR ≤ c₃ * W.H Q * N xsPP := by rw [hPP]; exact h3' hreg
    have key := chain_iiiH hκ hκ1 hM (mul_nonneg hc₃ hH) (hNn _) (hLFn _) h0 e1 e3 h4'
      hR e6'' (h3 hreg) h8' h5
    calc F xb ≤ _ := key
      _ ≤ (1 + κ) ^ 3 * (c₃ * W.H Q) * N xsb + E := by linarith

/-! ### Step 4(c): the prime powers -/

variable (P : HSetup)

lemma aPPH_sq_le {Q T x : ℝ} {n : ℕ} (hn : n ∈ P.range Q T) (hx : 0 < x) :
    aPPH P Q T x n ^ 2 ≤ Real.log (P.Y Q T) ^ 2 / x := by
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnN : n ≤ ⌊P.Y Q T⌋₊ := (Finset.mem_Icc.mp hn).2
  unfold aPPH
  split_ifs with h
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have h1 : P.aVec Q T n ^ 2 ≤ Real.log n * (Λ n / n) := aVec_sq_le P.toPS (Q * T) n hn1
    have hΛl : Λ n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
    have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
    have hY0 : 0 ≤ P.Y Q T := Real.rpow_nonneg (Real.exp_pos _).le _
    have hlogY : Real.log n ≤ Real.log (P.Y Q T) :=
      Real.log_le_log hn0 ((Nat.cast_le.mpr hnN).trans (Nat.floor_le hY0))
    have h2 : Real.log n * (Λ n / n) ≤ Real.log (P.Y Q T) * (Real.log (P.Y Q T) / x) := by
      apply mul_le_mul hlogY _ (by positivity) (hlog0.trans hlogY)
      calc Λ n / n ≤ Real.log n / n := div_le_div_of_nonneg_right hΛl hn0.le
        _ ≤ Real.log (P.Y Q T) / n := div_le_div_of_nonneg_right hlogY hn0.le
        _ ≤ Real.log (P.Y Q T) / x := div_le_div_of_nonneg_left (hlog0.trans hlogY) hx h.1.le
    calc P.aVec Q T n ^ 2 ≤ _ := h1
      _ ≤ _ := h2
      _ = Real.log (P.Y Q T) ^ 2 / x := by ring
  · have : 0 ≤ Real.log (P.Y Q T) ^ 2 / x := by positivity
    simpa using this

/-- **Step 4(c)**: `∑_{n > x, n not Q-rough} a_n² ≤ 2√Y (log Y)³/x` for `x ≥ Q` (such `n` with
`a_n ≠ 0` are proper prime powers; `card_pp_le`). -/
theorem sum_sq_aPPH_le {Q T x : ℝ} (hQT : 1 < Q * T) (hQx : Q ≤ x) (hx0 : 0 < x) :
    ∑ n ∈ P.range Q T, aPPH P Q T x n ^ 2 ≤
      2 * Real.sqrt (P.Y Q T) * Real.log (P.Y Q T) ^ 3 / x := by
  set N : ℕ := ⌊P.Y Q T⌋₊ with hN
  have hY1 : 1 ≤ P.Y Q T := one_le_Y P.toPS hQT
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hY1)
  set PP := (Finset.Icc 1 N).filter (fun n => Λ n ≠ 0 ∧ ¬ n.Prime) with hPP
  have hsupp : ∀ n ∈ P.range Q T, n ∉ PP → aPPH P Q T x n ^ 2 = 0 := by
    intro n hn hnPP
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    unfold aPPH
    split_ifs with h
    · by_cases ha : P.aVec Q T n = 0
      · simp [ha]
      · exfalso; apply hnPP
        rw [hPP, Finset.mem_filter]
        exact ⟨hn, aVec_ne_zero P.toPS (Q := Q * T) ha,
          not_prime_of_not_rough (lt_of_le_of_lt hQx h.1) hn1 h.2⟩
    · simp
  have hsub : PP ⊆ P.range Q T := Finset.filter_subset _ _
  rw [← Finset.sum_subset hsub hsupp]
  have hcard : (PP.card : ℝ) ≤ (Nat.sqrt N * Nat.log 2 N : ℕ) := by exact_mod_cast card_pp_le N
  have hlogN : Real.log N ≤ Real.log (P.Y Q T) :=
    Real.log_le_log (by exact_mod_cast hN1) (Nat.floor_le (by linarith))
  have hlogY0 : 0 ≤ Real.log (P.Y Q T) := Real.log_nonneg hY1
  have hsq : (Nat.sqrt N : ℝ) ≤ Real.sqrt (P.Y Q T) :=
    Real.nat_sqrt_le_real_sqrt.trans (Real.sqrt_le_sqrt (Nat.floor_le (by linarith)))
  have hlg : (Nat.log 2 N : ℝ) ≤ 2 * Real.log (P.Y Q T) :=
    (natLog_le_two_log hN1).trans (by linarith)
  calc ∑ n ∈ PP, aPPH P Q T x n ^ 2 ≤ ∑ n ∈ PP, Real.log (P.Y Q T) ^ 2 / x :=
        Finset.sum_le_sum fun n hn => aPPH_sq_le P (hsub hn) hx0
    _ = PP.card * (Real.log (P.Y Q T) ^ 2 / x) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Nat.sqrt N * Nat.log 2 N : ℕ) * (Real.log (P.Y Q T) ^ 2 / x) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ (Real.sqrt (P.Y Q T) * (2 * Real.log (P.Y Q T))) * (Real.log (P.Y Q T) ^ 2 / x) := by
        push_cast
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul hsq hlg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt (P.Y Q T) * Real.log (P.Y Q T) ^ 3 / x := by ring

/-- Step 4(c) at the threshold of regime (iii): with `x = (QT)^{1+ε}/2`, `Q^ε ≥ 2` and
`log Y = μℓ`: `∑ a_pp² ≤ 4μ³ℓ³ Q^{−ε}`. -/
lemma sum_sq_aPPH_le_ell {Q T ε μ ℓ : ℝ} (hQ : 1 < Q) (hT : 1 ≤ T) (hε : 0 ≤ ε)
    (hQε : 2 ≤ Q ^ ε) (hlogY : Real.log (P.Y Q T) = μ * ℓ) (hμ : 0 ≤ μ) (hℓ : 0 ≤ ℓ) :
    ∑ n ∈ P.range Q T, aPPH P Q T ((Q * T) ^ (1 + ε) / 2) n ^ 2 ≤
      4 * μ ^ 3 * ℓ ^ 3 * Q ^ (-ε) := by
  have hQ0 : 0 < Q := by linarith
  have hQT : Q ≤ Q * T := by nlinarith
  have hQT0 : 0 < Q * T := by positivity
  have hQT1 : 1 < Q * T := by nlinarith
  set s := Q * T with hs
  have hx : s ^ (1 + ε) = s * s ^ ε := by rw [Real.rpow_add hQT0, Real.rpow_one]
  have hsε : Q ^ ε ≤ s ^ ε := Real.rpow_le_rpow hQ0.le hQT hε
  have hQx : Q ≤ s ^ (1 + ε) / 2 := by rw [hx]; nlinarith
  have hx0 : 0 < s ^ (1 + ε) / 2 := by positivity
  refine (sum_sq_aPPH_le P hQT1 hQx hx0).trans ?_
  rw [hlogY]
  have hYs : P.Y Q T ≤ s ^ 2 := Y_le_sq P.toPS hQT1.le
  have hsY : Real.sqrt (P.Y Q T) ≤ s :=
    (Real.sqrt_le_sqrt hYs).trans (le_of_eq (Real.sqrt_sq hQT0.le))
  rw [div_le_iff₀ hx0]
  have hQe : 1 ≤ Q ^ (-ε) * s ^ ε := by
    rw [Real.rpow_neg hQ0.le, inv_mul_eq_div, one_le_div (by positivity)]; exact hsε
  have h3 : 0 ≤ (μ * ℓ) ^ 3 := by positivity
  have h4 : 0 ≤ 2 * s * (μ * ℓ) ^ 3 := by positivity
  calc 2 * Real.sqrt (P.Y Q T) * (μ * ℓ) ^ 3 ≤ 2 * s * (μ * ℓ) ^ 3 := by gcongr
    _ ≤ 2 * s * (μ * ℓ) ^ 3 * (Q ^ (-ε) * s ^ ε) := le_mul_of_one_le_right h4 hQe
    _ = 4 * μ ^ 3 * ℓ ^ 3 * Q ^ (-ε) * (s ^ (1 + ε) / 2) := by rw [hx]; ring

end TS

end Families.Hybrid
