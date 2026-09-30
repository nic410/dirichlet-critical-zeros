/-
# Package S (the second moment at polynomial height): decoupled objects and the large sieve

The families second-moment objects (`Families.Ported.Second`) couple two parameters that are
different at polynomial height: the **family** parameter `Q` (conductors `q ≤ Q`, the weights
`ω(q)`, `H`, `Δ`) and the **prime-side** parameter, the conductor-like `Q' = QT` (`L = λ log(QT)`,
`Y`, `[1, Y]`, `a_n`, `ψ_L`, `Φ`, `𝒦`). Every hybrid object of `HSetup` is the families object of
`P.toPS` at `Qs = QT` (`FamiliesH.F.Bridge`, all `rfl`), so the per-character lemmas of
`Families.Ported.Second` apply verbatim at `(P.toPS, QT)`; the family-level ones are restated
here with the two parameters **decoupled** (`Q` for the family, `Qs` for the prime side).

* `Mcal2`, `Mmumu2`, `Mmix2`, `MA2`, `MB2`, `PP2`, `RR2`, `SSC2`, `ratio2`: the families `𝓜`, `M_{μμ}`,
  `M_{μΛ}` (and its parts), `∑ω K₂(P,P)`, `∑ω K₂(r,r)`, the same-sign sum and the ratio form, decoupled;
* `famLS2`, `famLS_omega2`, `bilinLS2`: the multiplicative large sieve on `[1, Y(Qs)]` for the family
  at `Q`, with the factor `Q² + Y(Qs)` (at polynomial height `Y` may exceed `Q²`);
* facts about the cell heights `ℓ^{a₀} ≤ T ≤ Q^{κc}`.
-/
import FamiliesH.F.All

noncomputable section

set_option linter.unusedSectionVars false

open scoped BigOperators ComplexConjugate ContDiff
open ArithmeticFunction Finset MeasureTheory Filter Topology

namespace Families.Hybrid.S

open Families Families.Ported.Second

/-! ### Decoupled objects -/

section Defs

variable (PS : PrimeSetup) (W : Weight)

/-- `𝓜 = ∑_{χ ∈ 𝓕(Q)} ω_χ ∬_{J²} Φ(t−t')² ν_χ(t) ν_χ(t')`, prime side at `Qs`. -/
def Mcal2 (Q Qs T : ℝ) : ℝ :=
  famSum W Q fun _ χ =>
    ∫ t in PS.J T, ∫ t' in PS.J T, PhiSq PS Qs (t - t') * nuChi PS Qs χ t * nuChi PS Qs χ t'

/-- `M_{μμ}`, decoupled. -/
def Mmumu2 (Q Qs T : ℝ) : ℝ :=
  famSum W Q fun _ χ => K2 PS Qs T (muChi χ) (muChi χ)

/-- `M_{μΛ} = ∑ ω K₂(μ, P)`, decoupled. -/
def Mmix2 (Q Qs T : ℝ) : ℝ :=
  famSum W Q fun _ χ => K2 PS Qs T (muChi χ) (PChi PS Qs χ)

/-- The `r`-part `∑ ω K₂(μ − β_q, P)` of `M_{μΛ}`, `β_q = (1/2π)(log(q/π) + log T)`. -/
def MA2 (Q Qs T : ℝ) : ℝ :=
  famSum W Q fun q χ => K2 PS Qs T (fun t => muChi χ t - MixSS.beta q T) (PChi PS Qs χ)

/-- The `β`-part `∑ ω K₂(β_q, P)` of `M_{μΛ}`. -/
def MB2 (Q Qs T : ℝ) : ℝ :=
  famSum W Q fun q χ => K2 PS Qs T (fun _ => MixSS.beta q T) (PChi PS Qs χ)

/-- `∑ ω K₂(P, P)` (`= M^{rat}_{ΛΛ} + M^{ss}_{ΛΛ}`). -/
def PP2 (Q Qs T : ℝ) : ℝ :=
  famSum W Q fun _ χ => K2 PS Qs T (PChi PS Qs χ) (PChi PS Qs χ)

/-- `∑ ω K₂(r, r)`, `r_χ = μ_χ − β_q`. -/
def RR2 (Q Qs T : ℝ) : ℝ :=
  famSum W Q fun q χ =>
    K2 PS Qs T (fun t => muChi χ t - MixSS.beta q T) (fun t => muChi χ t - MixSS.beta q T)

/-- The same-sign sum `∑_χ ω_χ ∬ Φ² S_χ S_χ'`, decoupled. -/
def SSC2 (Q Qs T : ℝ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (W.omega Q q : ℂ) * ∑ χ ∈ primChars q,
    ∫ t in PS.J T, ∫ t' in PS.J T,
      (PhiSq PS Qs (t - t') : ℂ) * PS.Schi χ Qs (PS.aVec Qs) t * PS.Schi χ Qs (PS.aVec Qs) t'

/-- The ratio form `∑_{n,m ≤ Y(Qs)} x_n x_m Δ_Q(n,m) 𝒦_{Qs}(n,m)`, decoupled. -/
def ratio2 (Q Qs T : ℝ) (x : ℕ → ℝ) : ℂ :=
  ∑ n ∈ PS.range Qs, ∑ m ∈ PS.range Qs, (x n : ℂ) * x m * Δ W Q n m * PS.𝒦 Qs T n m

end Defs

/-! ### The hybrid objects are the decoupled ones at `(P.toPS, Q, QT)` -/

section Bridge

variable (P : HSetup) (W : Weight)

lemma ratioForm_eq2 (Q T : ℝ) (x : ℕ → ℝ) :
    P.ratioForm W Q T x = ratio2 P.toPS W Q (Q * T) T x := rfl

lemma ellS_eq_ell (Q T : ℝ) : ellS Q T = ell (Q * T) := rfl

end Bridge

/-! ### The large sieve on `[1, Y(Qs)]` for the family at `Q` -/

section LS

lemma sum_intervalZ_one {M : Type*} [AddCommMonoid M] (K : ℕ) (f : ℤ → M) :
    ∑ n ∈ intervalZ 1 K, f n = ∑ n ∈ Finset.Icc 1 K, f (n : ℤ) := by
  symm
  refine Finset.sum_bij' (fun (k : ℕ) _ => (k : ℤ)) (fun (n : ℤ) _ => n.toNat) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    simp only [intervalZ, Finset.mem_Ico]
    omega
  · intro n hn
    simp only [intervalZ, Finset.mem_Ico] at hn
    simp only [Finset.mem_Icc]
    omega
  · intro k _; simp
  · intro n hn
    simp only [intervalZ, Finset.mem_Ico] at hn
    omega
  · intro k _; rfl

/-- The multiplicative large sieve on `[1, Y(Qs)]`, family at `Q`: factor `Q² + Y(Qs)`. -/
theorem famLS2 (hMV : MV_LargeSieve) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧
    ∀ (PS : PrimeSetup) (Q Qs : ℝ), 1 ≤ Q → ∀ x : ℕ → ℂ,
      ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (q : ℝ) / (Nat.totient q : ℝ) *
          ∑ χ ∈ primChars q, ‖∑ n ∈ PS.range Qs, x n * χ n‖ ^ 2
        ≤ C₀ * (Q ^ 2 + PS.Y Qs) * ∑ n ∈ PS.range Qs, ‖x n‖ ^ 2 := by
  obtain ⟨C₀, hmult, -⟩ := hMV
  refine ⟨max C₀ 0, le_max_right _ _, fun PS Q Qs hQ x => ?_⟩
  set K := ⌊PS.Y Qs⌋₊ with hK
  set x' : ℤ → ℂ := fun n => if 1 ≤ n then x n.toNat else 0 with hx'
  have h := hmult Q hQ 1 K x'
  have hS : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q),
      ∑ n ∈ intervalZ 1 K, x' n * χ n = ∑ n ∈ PS.range Qs, x n * χ n := by
    intro q χ
    rw [sum_intervalZ_one]
    unfold PrimeSetup.range
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    simp only [hx', show (1 : ℤ) ≤ (n : ℤ) by exact_mod_cast hn1, if_true, Int.toNat_natCast,
      Int.cast_natCast]
  have hN : normSq (intervalZ 1 K) x' = ∑ n ∈ PS.range Qs, ‖x n‖ ^ 2 := by
    unfold normSq
    rw [sum_intervalZ_one]
    unfold PrimeSetup.range
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    simp only [hx', show (1 : ℤ) ≤ (n : ℤ) by exact_mod_cast hn1, if_true, Int.toNat_natCast]
  simp_rw [hS] at h
  rw [hN] at h
  have hKY : (K : ℝ) ≤ PS.Y Qs := Nat.floor_le (Families.Phase3.C.Y_pos' PS Qs).le
  have hsum0 : 0 ≤ ∑ n ∈ PS.range Qs, ‖x n‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  refine h.trans ?_
  have hQK : 0 ≤ Q ^ 2 + (K : ℝ) := by positivity
  calc C₀ * (Q ^ 2 + K) * ∑ n ∈ PS.range Qs, ‖x n‖ ^ 2
      ≤ max C₀ 0 * (Q ^ 2 + K) * ∑ n ∈ PS.range Qs, ‖x n‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hsum0
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) hQK
    _ ≤ max C₀ 0 * (Q ^ 2 + PS.Y Qs) * ∑ n ∈ PS.range Qs, ‖x n‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right _ hsum0
        exact mul_le_mul_of_nonneg_left (by linarith) (le_max_right _ _)

/-- The large sieve with the family weights, decoupled. -/
theorem famLS_omega2 (hMV : MV_LargeSieve) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧
    ∀ (PS : PrimeSetup) (W : Weight) (Q Qs : ℝ), 1 ≤ Q → ∀ x : ℕ → ℂ,
      ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ χ ∈ primChars q,
          ‖∑ n ∈ PS.range Qs, x n * χ n‖ ^ 2
        ≤ W.wmax * C₀ * (Q ^ 2 + PS.Y Qs) * ∑ n ∈ PS.range Qs, ‖x n‖ ^ 2 := by
  obtain ⟨C₀, hC₀, h⟩ := famLS2 hMV
  refine ⟨C₀, hC₀, fun PS W Q Qs hQ x => ?_⟩
  have hw := W.wmax_nonneg
  calc ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ χ ∈ primChars q,
        ‖∑ n ∈ PS.range Qs, x n * χ n‖ ^ 2
      ≤ ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.wmax * ((q : ℝ) / (Nat.totient q : ℝ) *
          ∑ χ ∈ primChars q, ‖∑ n ∈ PS.range Qs, x n * χ n‖ ^ 2) := by
        refine Finset.sum_le_sum fun q _ => ?_
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (omega_le W Q q)
          (Finset.sum_nonneg fun _ _ => by positivity)
    _ = W.wmax * ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ((q : ℝ) / (Nat.totient q : ℝ) *
          ∑ χ ∈ primChars q, ‖∑ n ∈ PS.range Qs, x n * χ n‖ ^ 2) := by rw [Finset.mul_sum]
    _ ≤ W.wmax * (C₀ * (Q ^ 2 + PS.Y Qs) * ∑ n ∈ PS.range Qs, ‖x n‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (h PS Q Qs hQ x) hw
    _ = _ := by ring

/-- The bilinear form of the large sieve, decoupled. -/
theorem bilinLS2 (hMV : MV_LargeSieve) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧
    ∀ (PS : PrimeSetup) (Q Qs : ℝ), 1 ≤ Q →
    ∀ (b : (q : ℕ) → DirichletCharacter ℂ q → ℂ) (x : ℕ → ℂ),
      ‖∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ ∈ primChars q, b q χ * ∑ n ∈ PS.range Qs, x n * χ n‖ ^ 2
        ≤ (∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ ∈ primChars q, (Nat.totient q : ℝ) / q * ‖b q χ‖ ^ 2) *
          (C₀ * (Q ^ 2 + PS.Y Qs) * ∑ n ∈ PS.range Qs, ‖x n‖ ^ 2) := by
  obtain ⟨C₀, hC₀, h⟩ := famLS2 hMV
  refine ⟨C₀, hC₀, fun PS Q Qs hQ b x => ?_⟩
  set S : (q : ℕ) → DirichletCharacter ℂ q → ℂ := fun q χ => ∑ n ∈ PS.range Qs, x n * χ n
    with hSdef
  set A := Finset.Icc 1 ⌊Q⌋₊
  set I := A.sigma fun q => primChars q
  set f : (Σ q : ℕ, DirichletCharacter ℂ q) → ℝ := fun z =>
    Real.sqrt ((Nat.totient z.1 : ℝ) / z.1) * ‖b z.1 z.2‖ with hf
  set g : (Σ q : ℕ, DirichletCharacter ℂ q) → ℝ := fun z =>
    Real.sqrt ((z.1 : ℝ) / (Nat.totient z.1 : ℝ)) * ‖S z.1 z.2‖ with hg
  have hmemq : ∀ z ∈ I, 1 ≤ z.1 := by
    intro z hz
    have := (Finset.mem_sigma.mp hz).1
    exact (Finset.mem_Icc.mp this).1
  have hfg : ∀ z ∈ I, ‖b z.1 z.2‖ * ‖S z.1 z.2‖ = f z * g z := by
    intro z hz
    have hq := hmemq z hz
    have hq0 : (0 : ℝ) < z.1 := by exact_mod_cast hq
    have hφ : (0 : ℝ) < Nat.totient z.1 := by exact_mod_cast Nat.totient_pos.mpr hq
    simp only [hf, hg]
    have : Real.sqrt ((Nat.totient z.1 : ℝ) / z.1) * Real.sqrt ((z.1 : ℝ) / (Nat.totient z.1 : ℝ))
        = 1 := by
      rw [← Real.sqrt_mul (by positivity)]
      rw [show (Nat.totient z.1 : ℝ) / z.1 * (z.1 / Nat.totient z.1) = 1 by field_simp]
      simp
    calc ‖b z.1 z.2‖ * ‖S z.1 z.2‖ = (Real.sqrt ((Nat.totient z.1 : ℝ) / z.1) *
        Real.sqrt ((z.1 : ℝ) / (Nat.totient z.1 : ℝ))) * (‖b z.1 z.2‖ * ‖S z.1 z.2‖) := by
          rw [this, one_mul]
      _ = _ := by ring
  have hf2 : ∀ z ∈ I, f z ^ 2 = (Nat.totient z.1 : ℝ) / z.1 * ‖b z.1 z.2‖ ^ 2 := by
    intro z _
    simp only [hf, mul_pow]
    rw [Real.sq_sqrt (by positivity)]
  have hg2 : ∀ z ∈ I, g z ^ 2 = (z.1 : ℝ) / (Nat.totient z.1 : ℝ) * ‖S z.1 z.2‖ ^ 2 := by
    intro z _
    simp only [hg, mul_pow]
    rw [Real.sq_sqrt (by positivity)]
  have hnorm : ‖∑ q ∈ A, ∑ χ ∈ primChars q, b q χ * S q χ‖ ≤ ∑ z ∈ I, f z * g z := by
    rw [Finset.sum_sigma']
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun z hz => ?_
    rw [norm_mul, hfg z hz]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq I f g
  have hsumf : ∑ z ∈ I, f z ^ 2 =
      ∑ q ∈ A, ∑ χ ∈ primChars q, (Nat.totient q : ℝ) / q * ‖b q χ‖ ^ 2 := by
    rw [Finset.sum_congr rfl hf2]
    exact (Finset.sum_sigma' A (fun q => primChars q)
      (fun q χ => (Nat.totient q : ℝ) / q * ‖b q χ‖ ^ 2)).symm
  have hsumg : ∑ z ∈ I, g z ^ 2 =
      ∑ q ∈ A, (q : ℝ) / (Nat.totient q : ℝ) * ∑ χ ∈ primChars q, ‖S q χ‖ ^ 2 := by
    rw [Finset.sum_congr rfl hg2]
    rw [← (Finset.sum_sigma' A (fun q => primChars q)
      (fun q χ => (q : ℝ) / (Nat.totient q : ℝ) * ‖S q χ‖ ^ 2))]
    refine Finset.sum_congr rfl fun q _ => by rw [Finset.mul_sum]
  calc ‖∑ q ∈ A, ∑ χ ∈ primChars q, b q χ * S q χ‖ ^ 2 ≤ (∑ z ∈ I, f z * g z) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ (∑ z ∈ I, f z ^ 2) * ∑ z ∈ I, g z ^ 2 := hCS
    _ ≤ _ := by
        rw [hsumf, hsumg]
        apply mul_le_mul_of_nonneg_left (h PS Q Qs hQ x)
        exact Finset.sum_nonneg fun q _ => Finset.sum_nonneg fun _ _ => by positivity

end LS

/-! ### The cell heights -/

section Cell

variable (P : HSetup)

lemma log_ge_of_exp_le {c Q : ℝ} (h : Real.exp c ≤ Q) : c ≤ Real.log Q := by
  have := Real.log_le_log (Real.exp_pos c) h
  rwa [Real.log_exp] at this

lemma one_lt_of_exp_one_le {Q : ℝ} (hQ : Real.exp 1 ≤ Q) : 1 < Q :=
  lt_of_lt_of_le (by have := Real.add_one_le_exp (1 : ℝ); linarith) hQ

/-- On the cell (`Q ≥ e`): `1 ≤ T`, `1 ≤ log Q ≤ ℓ_*`, `Q ≤ QT`, `1 < QT`. -/
lemma cell_facts {Q T : ℝ} (hQ : Real.exp 1 ≤ Q) (hT : T ∈ P.heights Q) :
    1 ≤ T ∧ 1 ≤ Real.log Q ∧ Real.log Q ≤ ellS Q T ∧ Q ≤ Q * T ∧ 1 < Q * T ∧
      0 ≤ Real.log T := by
  have hℓ : 1 ≤ Real.log Q := log_ge_of_exp_le hQ
  have hQ1 : 1 < Q := one_lt_of_exp_one_le hQ
  have hT1 : 1 ≤ T := le_trans (Real.one_le_rpow hℓ P.a0_pos.le) hT.1
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hQT : Q ≤ Q * T := le_mul_of_one_le_right (by linarith) hT1
  refine ⟨hT1, hℓ, ?_, hQT, by linarith, hlogT⟩
  unfold ellS
  rw [Real.log_mul (by linarith) (by linarith)]
  linarith

/-- `T → ∞` uniformly on the cell. -/
lemma T_large (M : ℝ) : ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ P.heights Q, M ≤ T := by
  set M' := max M 1 with hM'
  have hM'0 : 0 < M' := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨Real.exp (M' ^ P.a0⁻¹), fun Q hQ T hT => ?_⟩
  have hl := log_ge_of_exp_le hQ
  have h0 : 0 ≤ M' ^ P.a0⁻¹ := Real.rpow_nonneg hM'0.le _
  have h1 : (M' ^ P.a0⁻¹) ^ P.a0 ≤ Real.log Q ^ P.a0 :=
    Real.rpow_le_rpow h0 hl P.a0_pos.le
  rw [Real.rpow_inv_rpow hM'0.le P.a0_pos.ne'] at h1
  exact (le_max_left _ _).trans (h1.trans hT.1)

/-- `L = λ ℓ_* ≥ λ log Q`, so `L → ∞` uniformly on the cell. -/
lemma L_large (M : ℝ) : ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ P.heights Q,
    M ≤ P.L Q T ∧ M ≤ ellS Q T := by
  refine ⟨max (Real.exp 1) (max (Real.exp (M / P.lam)) (Real.exp M)), fun Q hQ T hT => ?_⟩
  have hQe : Real.exp 1 ≤ Q := le_trans (le_max_left _ _) hQ
  have hQa : Real.exp (M / P.lam) ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hQ
  have hQb : Real.exp M ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hQ
  obtain ⟨-, -, hℓs, -, -, -⟩ := cell_facts P hQe hT
  have ha := log_ge_of_exp_le hQa
  have hb := log_ge_of_exp_le hQb
  have hl := P.lam_pos
  refine ⟨?_, by linarith⟩
  unfold HSetup.L
  rw [div_le_iff₀ hl] at ha
  nlinarith

/-- (S1): `Y ≤ Q^{2−ε₁} T^{1−ε₁}`, hence `1 + Y/Q² ≤ 1 + Q^{-ε₁} T` and `Y ≤ Q² T`. -/
lemma Y_bounds : ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ P.heights Q,
    P.Y Q T ≤ Q ^ (2 : ℝ) * (Q ^ (-P.ε₁) * T) := by
  have hkc := P.kc_pos
  obtain ⟨Q₀, hQ₀⟩ := F.lemSizesH_proof P (1 / (8 * (1 + P.kc))) (by positivity) le_rfl
  refine ⟨max Q₀ (Real.exp 1), fun Q hQ T hT => ?_⟩
  have hQe : Real.exp 1 ≤ Q := le_trans (le_max_right _ _) hQ
  obtain ⟨hT1, -, -, -, -, -⟩ := cell_facts P hQe hT
  have hQ1 : 1 < Q := one_lt_of_exp_one_le hQe
  have hQ0 : 0 < Q := by linarith
  have hS1 := (hQ₀ Q (le_trans (le_max_left _ _) hQ) T hT).1.1
  have e1 : Q ^ (2 - P.ε₁) = Q ^ (2 : ℝ) * Q ^ (-P.ε₁) := by
    rw [← Real.rpow_add hQ0]; ring_nf
  have e2 : T ^ (1 - P.ε₁) ≤ T := by
    have : T ^ (1 - P.ε₁) ≤ T ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hT1 (by linarith [P.ε₁_pos])
    simpa using this
  rw [e1] at hS1
  refine hS1.trans ?_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact mul_le_mul_of_nonneg_left e2 (by positivity)

/-- The large-sieve loss on the cell: `(1 + Y/Q²) ≤ δ T` for large `Q`, i.e. `Q² + Y ≤ δ Q² T`. -/
lemma sieve_loss_small (δ : ℝ) (hδ : 0 < δ) : ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ P.heights Q,
    Q ^ 2 + P.Y Q T ≤ δ * (Q ^ 2 * T) := by
  obtain ⟨Q₁, h₁⟩ := Y_bounds P
  obtain ⟨Q₂, h₂⟩ := T_large P (2 / δ)
  have hε := P.ε₁_pos
  refine ⟨max (max Q₁ Q₂) (max (Real.exp 1) ((2 / δ) ^ (P.ε₁)⁻¹)), fun Q hQ T hT => ?_⟩
  have hQ1' : Q₁ ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hQ
  have hQ2' : Q₂ ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hQ
  have hQe : Real.exp 1 ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hQ
  have hQδ : (2 / δ) ^ (P.ε₁)⁻¹ ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hQ
  obtain ⟨hT1, -, -, -, -, -⟩ := cell_facts P hQe hT
  have hQ1 : 1 < Q := one_lt_of_exp_one_le hQe
  have hQ0 : 0 < Q := by linarith
  have hY := h₁ Q hQ1' T hT
  have hTδ : 2 / δ ≤ T := h₂ Q hQ2' T hT
  -- `Q^{-ε₁} ≤ δ/2`
  have hQε : Q ^ (-P.ε₁) ≤ δ / 2 := by
    have h1 : (2 / δ) ≤ Q ^ P.ε₁ := by
      have := Real.rpow_le_rpow (by positivity) hQδ hε.le
      rwa [← Real.rpow_mul (by positivity), inv_mul_cancel₀ hε.ne', Real.rpow_one] at this
    rw [Real.rpow_neg hQ0.le]
    have hpos : 0 < Q ^ P.ε₁ := Real.rpow_pos_of_pos hQ0 _
    rw [inv_le_comm₀ hpos (by positivity)]
    calc (δ / 2)⁻¹ = 2 / δ := by field_simp
      _ ≤ Q ^ P.ε₁ := h1
  have hQ2 : Q ^ (2 : ℝ) = Q ^ 2 := by norm_cast
  rw [hQ2] at hY
  have h1 : 1 ≤ δ / 2 * T := by
    rw [div_le_iff₀ hδ] at hTδ; linarith
  have hQsq : 0 ≤ Q ^ 2 := sq_nonneg Q
  have e1 : Q ^ 2 ≤ Q ^ 2 * (δ / 2 * T) := le_mul_of_one_le_right hQsq h1
  have e2 : P.Y Q T ≤ Q ^ 2 * (δ / 2 * T) :=
    hY.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hQε (by linarith)) hQsq)
  nlinarith

end Cell

end Families.Hybrid.S
