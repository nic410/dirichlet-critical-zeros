/-
# Theorem 1.4(a), package Z: the prime part of the trace by cancellation over the lattice (Proposition 9.6)

At polynomial height the families shortcut (bounding `∑_χ ω_χ P_χ(t)` pointwise, lattice point by
lattice point, `Families.Ported.Zero.prime_family_lower`) loses a factor `T`, which is fatal once
`√X ≫ Q`. Here the sum over the lattice `k ∈ K_J` is taken **before** the absolute values:

* `integral_normSq_pk_mul_exp` (Fourier inversion, `Zeta23.EF.paper_inversion`):
  `∫ |p_k(t)|² e^{−itx} dt = 2π e^{−iτ_k x} A(x)`, with the autocorrelation
  `A(x) = ∫ ψ_L(u) ψ_L(u−x) du`, `|A| ≤ aL`, and `A(x) = 0` for `|x| > 2rL` (`abs_autoc_le`,
  `autoc_eq_zero`);
* `norm_sum_exp_Icc_le` (geometric sum over the integer interval `K_J`):
  `|∑_{k∈K_J} e^{ikθ}| ≤ 1/|sin(θ/2)|`, and `sin(πy) ≥ 2(1−2r)y` on `(0, 2r]` (`sin_lower`);
* `trace_prime_bound`: `|∑_χ ω_χ ∑_{k∈K_J} ∫ |p_k|² P_χ| ≤ aL² · (2w_max Q/(1−2r)) · 2√X(1+log X)`,
  **uniformly in `T`**, via the family first moment (`Families.Ported.Zero.first_moment`).
This is the lattice analogue of the bound `|∫_J n^{∓it} dt| ≤ 2/log n` used in the proof of
Proposition 9.6 (which first passes to `∫_J ν_χ` by the finite-centre replacement, Proposition 9.5);
the Lean proof works lattice point by lattice point through the explicit formula, as the `Families`
Lean proof does, and never needs Proposition 9.5. The resulting bound is the paper's
`≪ w_max Q X^{1/2} log X`.
Everything is stated for a `Families.PrimeSetup` and a bandwidth argument `Q'` (used with
`toPS P` and `Q' = QT`), and a separate family parameter `Q`.
-/
import FamiliesH.Z.Basic

noncomputable section

open scoped BigOperators ComplexConjugate
open Complex Set MeasureTheory Filter Topology

namespace Families.Hybrid.Z

open Families Families.Ported.Zero Zeta23

variable (P : PrimeSetup)

/-! ### The autocorrelation of `ψ_L` -/

/-- `A(x) = ∫ ψ_L(u) ψ_L(u − x) du`. -/
def autoc (Q x : ℝ) : ℝ := ∫ u, P.ψL Q u * P.ψL Q (u - x)

lemma ψL_hasCompactSupport {Q : ℝ} (hQ : 1 < Q) : HasCompactSupport (P.ψL Q) := by
  obtain ⟨r, _, h⟩ := ψL_supp P
  have hL := L_pos P hQ
  set B := |r| * P.L Q + 1 with hB
  refine HasCompactSupport.intro (isCompact_Icc (a := -B) (b := B)) fun u hu => ?_
  apply h Q hQ u
  have hrB : r * P.L Q < B := by
    have : r * P.L Q ≤ |r| * P.L Q := mul_le_mul_of_nonneg_right (le_abs_self r) hL.le
    linarith
  by_contra hc
  push Not at hc
  exact hu (abs_le.mp (hc.trans hrB.le))

lemma continuous_ψL (Q : ℝ) : Continuous (P.ψL Q) := (contDiff_ψL P Q).continuous

lemma integrable_ψL_sq {Q : ℝ} (hQ : 1 < Q) : Integrable (fun u => P.ψL Q u ^ 2) := by
  have hc := continuous_ψL P Q
  have hcs := ψL_hasCompactSupport P hQ
  have e : (fun u => P.ψL Q u ^ 2) = P.ψL Q * P.ψL Q := by funext u; simp [sq]
  rw [e]
  exact (hc.mul hc).integrable_of_hasCompactSupport hcs.mul_right

lemma integrable_ψL_mul_shift {Q : ℝ} (hQ : 1 < Q) (x : ℝ) :
    Integrable (fun u => P.ψL Q u * P.ψL Q (u - x)) := by
  have hc := continuous_ψL P Q
  have hcs := ψL_hasCompactSupport P hQ
  exact (hc.mul (hc.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
    (hcs.mul_right)

/-- `|A(x)| ≤ a L`. -/
lemma abs_autoc_le {Q : ℝ} (hQ : 1 < Q) (x : ℝ) : |autoc P Q x| ≤ P.aInt * P.L Q := by
  unfold autoc
  have h1 := integrable_ψL_sq P hQ
  have h2 : Integrable (fun u => P.ψL Q (u - x) ^ 2) := h1.comp_sub_right x
  have hsum : Integrable (fun u => (P.ψL Q u ^ 2 + P.ψL Q (u - x) ^ 2) / 2) :=
    (h1.add h2).div_const 2
  have hprod := integrable_ψL_mul_shift P hQ x
  calc |∫ u, P.ψL Q u * P.ψL Q (u - x)|
      ≤ ∫ u, |P.ψL Q u * P.ψL Q (u - x)| := abs_integral_le_integral_abs
    _ ≤ ∫ u, (P.ψL Q u ^ 2 + P.ψL Q (u - x) ^ 2) / 2 := by
        refine integral_mono hprod.abs hsum fun u => ?_
        simp only
        rw [abs_mul]
        nlinarith [sq_nonneg (|P.ψL Q u| - |P.ψL Q (u - x)|), sq_abs (P.ψL Q u),
          sq_abs (P.ψL Q (u - x))]
    _ = ((∫ u, P.ψL Q u ^ 2) + ∫ u, P.ψL Q (u - x) ^ 2) / 2 := by
        rw [integral_div, integral_add h1 h2]
    _ = P.aInt * P.L Q := by
        rw [integral_sub_right_eq_self (fun u => P.ψL Q u ^ 2) x, integral_ψL_sq P hQ]
        ring

/-- `A(x) = 0` for `|x| > 2rL` (`ψ_L` vanishes outside `[−rL, rL]`). -/
lemma autoc_eq_zero {Q r : ℝ} (hr : ∀ u : ℝ, r * P.L Q < |u| → P.ψL Q u = 0) {x : ℝ}
    (hx : 2 * r * P.L Q < |x|) : autoc P Q x = 0 := by
  unfold autoc
  have hz : ∀ u, P.ψL Q u * P.ψL Q (u - x) = 0 := by
    intro u
    by_cases hu : r * P.L Q < |u|
    · rw [hr u hu, zero_mul]
    · push Not at hu
      have : r * P.L Q < |u - x| := by
        have h3 : |x| ≤ |u| + |u - x| := by
          have := abs_sub_abs_le_abs_sub u (u - x)
          have e : u - (u - x) = x := by ring
          rw [e] at this
          have := abs_sub (u) (u - x)
          rw [e] at this
          linarith [abs_nonneg u, abs_nonneg (u - x)]
        linarith
      rw [hr (u - x) this, mul_zero]
  simp [hz]

/-! ### The Fourier identity for `|p_k|²` -/

lemma fk_mul_conj_shift (Q τ₀ : ℝ) (k : ℤ) (x t : ℝ) :
    fk P Q τ₀ k t * conj (fk P Q τ₀ k (-(x - t))) =
      Complex.exp (-(Complex.I * (tau P Q τ₀ k : ℂ) * x)) *
        ((P.ψL Q t * P.ψL Q (t - x) : ℝ) : ℂ) := by
  unfold fk
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  have e1 : -(x - t) = t - x := by ring
  rw [e1]
  have e2 : conj (-(Complex.I * (tau P Q τ₀ k : ℂ) * ((t - x : ℝ) : ℂ))) =
      Complex.I * (tau P Q τ₀ k : ℂ) * ((t - x : ℝ) : ℂ) := by
    simp [map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [e2]
  have e3 : Complex.exp (-(Complex.I * (tau P Q τ₀ k : ℂ) * (t : ℂ))) *
      Complex.exp (Complex.I * (tau P Q τ₀ k : ℂ) * ((t - x : ℝ) : ℂ)) =
      Complex.exp (-(Complex.I * (tau P Q τ₀ k : ℂ) * x)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  push_cast
  calc (P.ψL Q t : ℂ) * Complex.exp (-(Complex.I * (tau P Q τ₀ k : ℂ) * (t : ℂ))) *
        ((P.ψL Q (t - x) : ℂ) * Complex.exp (Complex.I * (tau P Q τ₀ k : ℂ) * ((t : ℂ) - x)))
      = (Complex.exp (-(Complex.I * (tau P Q τ₀ k : ℂ) * (t : ℂ))) *
          Complex.exp (Complex.I * (tau P Q τ₀ k : ℂ) * (((t - x : ℝ)) : ℂ))) *
          ((P.ψL Q t : ℂ) * (P.ψL Q (t - x) : ℂ)) := by push_cast; ring
    _ = _ := by rw [e3]

/-- The Weil test function `f_k ⋆ \tilde f_k` at `x`: `e^{−iτ_k x} A(x)`. -/
lemma weilTest_fk_apply (Q τ₀ : ℝ) (k : ℤ) (x : ℝ) :
    EF.weilTest (fk P Q τ₀ k) (fk P Q τ₀ k) x =
      Complex.exp (-(Complex.I * (tau P Q τ₀ k : ℂ) * x)) * (autoc P Q x : ℂ) := by
  simp only [EF.weilTest, convolution_def, ContinuousLinearMap.mul_apply', EF.tilde]
  simp_rw [fk_mul_conj_shift P Q τ₀ k x]
  rw [integral_const_mul, integral_complex_ofReal]
  rfl

/-- `∫ |p_k(t)|² e^{−itx} dt = 2π e^{−iτ_k x} A(x)`. -/
theorem integral_normSq_pk_mul_exp {Q : ℝ} (hQ : 1 < Q) (τ₀ : ℝ) (k : ℤ) (x : ℝ) :
    ∫ r : ℝ, ((‖P.pk Q τ₀ k r‖ ^ 2 : ℝ) : ℂ) * Complex.exp (-Complex.I * r * x) =
      2 * Real.pi * (Complex.exp (-(Complex.I * (tau P Q τ₀ k : ℂ) * x)) * (autoc P Q x : ℂ)) := by
  have hfc := contDiff_fk P Q τ₀ k
  have hfs := hasCompactSupport_fk P hQ τ₀ k
  have hKc := EF.weilTest_contDiff hfc hfc.continuous hfs
  have hKs := EF.weilTest_hasCompactSupport hfs hfs
  have hinv := EF.paper_inversion hKc.continuous
    (hKc.continuous.integrable_of_hasCompactSupport hKs)
    (EF.integrable_fourier_of_contDiff_two hKc hKs) x
  have hI : (∫ r : ℝ, paperFT (EF.weilTest (fk P Q τ₀ k) (fk P Q τ₀ k)) r *
      Complex.exp (-Complex.I * r * x)) =
      ∫ r : ℝ, ((‖P.pk Q τ₀ k r‖ ^ 2 : ℝ) : ℂ) * Complex.exp (-Complex.I * r * x) := by
    congr 1
    funext r
    rw [paperFT_weilTest_fk P hQ]
  rw [hI, weilTest_fk_apply] at hinv
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hgen : ∀ z : ℂ, z = 2 * Real.pi * (1 / (2 * Real.pi) * z) := fun z => by field_simp
  rw [hinv]
  exact hgen _

/-! ### Geometric sums over an integer interval -/

lemma geom_zpow_Icc (w : ℂ) (hw : w ≠ 0) (a : ℤ) :
    ∀ b : ℤ, a - 1 ≤ b → (w - 1) * ∑ k ∈ Finset.Icc a b, w ^ k = w ^ (b + 1) - w ^ a := by
  intro b hb
  induction b, hb using Int.leInduction with
  | base =>
    rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, mul_zero, sub_add_cancel, sub_self]
  | succ n hn ih =>
    rw [← Finset.insert_Icc_right_eq_Icc_add_one (by omega), Finset.sum_insert (by simp),
      mul_add, ih, zpow_add_one₀ hw (n + 1), zpow_add_one₀ hw n]
    ring

lemma norm_sum_exp_Icc_le (θ : ℝ) (hs : Real.sin (θ / 2) ≠ 0) (a b : ℤ) :
    ‖∑ k ∈ Finset.Icc a b, Complex.exp (Complex.I * θ * k)‖ ≤ 1 / |Real.sin (θ / 2)| := by
  set w := Complex.exp (Complex.I * θ) with hw_def
  have hw0 : w ≠ 0 := Complex.exp_ne_zero _
  have hpow : ∀ k : ℤ, Complex.exp (Complex.I * θ * k) = w ^ k := by
    intro k
    rw [hw_def, ← Complex.exp_int_mul]
    congr 1; ring
  simp_rw [hpow]
  have hnw : ‖w‖ = 1 := by rw [hw_def]; exact Complex.norm_exp_I_mul_ofReal θ
  have hnorm1 : ∀ k : ℤ, ‖w ^ k‖ = 1 := fun k => by rw [norm_zpow, hnw, one_zpow]
  have hw1 : ‖w - 1‖ = 2 * |Real.sin (θ / 2)| := by
    rw [hw_def, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs,
      Real.norm_eq_abs]
    norm_num
  have hs0 : 0 < |Real.sin (θ / 2)| := abs_pos.mpr hs
  by_cases hab : a - 1 ≤ b
  · have hgeo := geom_zpow_Icc w hw0 a b hab
    have hle : ‖w - 1‖ * ‖∑ k ∈ Finset.Icc a b, w ^ k‖ ≤ 2 := by
      rw [← norm_mul, hgeo]
      calc ‖w ^ (b + 1) - w ^ a‖ ≤ ‖w ^ (b + 1)‖ + ‖w ^ a‖ := norm_sub_le _ _
        _ = 2 := by rw [hnorm1, hnorm1]; norm_num
    rw [hw1] at hle
    rw [le_div_iff₀ hs0]
    nlinarith [norm_nonneg (∑ k ∈ Finset.Icc a b, w ^ k)]
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty, norm_zero]
    positivity

/-- `sin(πy) ≥ 2(1−2r)y` for `0 < y ≤ 2r < 1`. -/
lemma sin_lower {y r : ℝ} (hr : r < 1 / 2) (hy0 : 0 < y) (hy : y ≤ 2 * r) :
    2 * (1 - 2 * r) * y ≤ Real.sin (Real.pi * y) := by
  have hπ := Real.pi_pos
  have hr0 : 0 < r := by linarith
  by_cases h : y ≤ 1 / 2
  · have h1 := Real.mul_le_sin (x := Real.pi * y) (by positivity) (by nlinarith)
    have e : 2 / Real.pi * (Real.pi * y) = 2 * y := by field_simp
    rw [e] at h1
    nlinarith
  · push Not at h
    have hsin : Real.sin (Real.pi * y) = Real.sin (Real.pi * (1 - y)) := by
      rw [← Real.sin_pi_sub]; congr 1; ring
    have hy1 : y < 1 := by linarith
    have h1 := Real.mul_le_sin (x := Real.pi * (1 - y)) (by nlinarith) (by nlinarith)
    have e : 2 / Real.pi * (Real.pi * (1 - y)) = 2 * (1 - y) := by field_simp
    rw [e] at h1
    rw [hsin]
    nlinarith

/-! ### The family prime sum -/

/-- `n^{−1/2−it} = n^{−1/2} e^{−it log n}` for `n ≥ 1`. -/
lemma natCast_cpow_split {n : ℕ} (hn : 0 < n) (t : ℝ) :
    (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * t) =
      (n : ℂ) ^ (-(1 / 2 : ℂ)) * Complex.exp (-Complex.I * t * (Real.log n : ℝ)) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Complex.cpow_def_of_ne_zero hn0, Complex.cpow_def_of_ne_zero hn0, ← Complex.exp_add]
  congr 1
  have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (Nat.cast_nonneg n)]; push_cast; rfl
  rw [hlog]
  ring

/-- `F(n) = ∑_q ω(q) ∑*_χ χ(n)`. -/
def Fmom (W : Weight) (Q : ℝ) (n : ℕ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, (W.omega Q q : ℂ) * ∑ χ ∈ primChars q, χ (n : ZMod q)

/-- `∑_χ ω_χ P_χ(t) = −(1/π) Re ∑_{n ≤ X} Λ(n) F(n) n^{−1/2−it}`. -/
lemma famSum_Pch_eq (W : Weight) (Q X t : ℝ) :
    famSum W Q (fun _ χ => Pch X χ t) =
      -(1 / Real.pi) * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        Fmom W Q n * (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * t)).re := by
  have e2 : (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
      Fmom W Q n * (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * t)) =
      ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ ∈ primChars q, (W.omega Q q : ℂ) *
        ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q) *
          (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * t) := by
    simp only [Fmom, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun χ _ => Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [e2]
  unfold famSum Pch
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Complex.re_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [Complex.re_ofReal_mul]
  ring

/-- `I(k,n) = ∫ |p_k(t)|² n^{−1/2−it} dt`. -/
def Ikn (Q τ₀ : ℝ) (k : ℤ) (n : ℕ) : ℂ :=
  ∫ t : ℝ, ((‖P.pk Q τ₀ k t‖ ^ 2 : ℝ) : ℂ) * (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * t)

lemma continuous_natCast_cpow (n : ℕ) (hn : 0 < n) :
    Continuous (fun t : ℝ => (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * t)) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  exact Continuous.const_cpow (by fun_prop) (Or.inl hn0)

lemma integrable_normSq_mul_cpow {Q : ℝ} (hQ : 1 < Q) (τ₀ : ℝ) (k : ℤ) {n : ℕ} (hn : 0 < n) :
    Integrable (fun t : ℝ => ((‖P.pk Q τ₀ k t‖ ^ 2 : ℝ) : ℂ) *
      (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * t)) := by
  have h := (integrable_normSq_pk P hQ τ₀ k).ofReal (𝕜 := ℂ)
  refine h.mul_bdd (c := 1) (continuous_natCast_cpow n hn).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [norm_natCast_cpow n hn t]
  have : 1 ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn)
  rw [div_le_one (by linarith)]
  exact this

lemma Ikn_eq {Q : ℝ} (hQ : 1 < Q) (τ₀ : ℝ) (k : ℤ) {n : ℕ} (hn : 0 < n) :
    Ikn P Q τ₀ k n = (n : ℂ) ^ (-(1 / 2 : ℂ)) * (2 * Real.pi *
      (Complex.exp (-(Complex.I * (tau P Q τ₀ k : ℂ) * (Real.log n : ℝ))) *
        (autoc P Q (Real.log n) : ℂ))) := by
  unfold Ikn
  simp_rw [natCast_cpow_split hn]
  have e : ∀ t : ℝ, ((‖P.pk Q τ₀ k t‖ ^ 2 : ℝ) : ℂ) * ((n : ℂ) ^ (-(1 / 2 : ℂ)) *
      Complex.exp (-Complex.I * t * (Real.log n : ℝ))) = (n : ℂ) ^ (-(1 / 2 : ℂ)) *
      (((‖P.pk Q τ₀ k t‖ ^ 2 : ℝ) : ℂ) * Complex.exp (-Complex.I * t * (Real.log n : ℝ))) := by
    intro t; ring
  simp_rw [e]
  rw [integral_const_mul, integral_normSq_pk_mul_exp P hQ τ₀ k (Real.log n)]

/-- Per lattice point: `∫ |p_k|² ∑_χ ω_χ P_χ = −(1/π) Re ∑_n Λ(n) F(n) I(k,n)`. -/
lemma integral_normSq_mul_famPch {Q' : ℝ} (hQ' : 1 < Q') (τ₀ : ℝ) (k : ℤ) (W : Weight) (Q X : ℝ) :
    ∫ t : ℝ, ‖P.pk Q' τ₀ k t‖ ^ 2 * famSum W Q (fun _ χ => Pch X χ t) =
      -(1 / Real.pi) * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        Fmom W Q n * Ikn P Q' τ₀ k n).re := by
  simp_rw [famSum_Pch_eq W Q X]
  have hint : ∀ n ∈ Finset.Ioc 0 ⌊X⌋₊, Integrable (fun t : ℝ =>
      ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * Fmom W Q n *
        (((‖P.pk Q' τ₀ k t‖ ^ 2 : ℝ) : ℂ) * (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * t))) := by
    intro n hn
    exact (integrable_normSq_mul_cpow P hQ' τ₀ k (Finset.mem_Ioc.mp hn).1).const_mul _
  have hsumI : Integrable (fun t : ℝ => ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
      ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * Fmom W Q n *
        (((‖P.pk Q' τ₀ k t‖ ^ 2 : ℝ) : ℂ) * (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * t))) :=
    integrable_finsetSum _ hint
  have hpt : ∀ t : ℝ, ‖P.pk Q' τ₀ k t‖ ^ 2 * (-(1 / Real.pi) *
      (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * Fmom W Q n *
        (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * t)).re) =
      -(1 / Real.pi) * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * Fmom W Q n *
          (((‖P.pk Q' τ₀ k t‖ ^ 2 : ℝ) : ℂ) * (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * t))).re := by
    intro t
    have h1 : (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * Fmom W Q n *
        (((‖P.pk Q' τ₀ k t‖ ^ 2 : ℝ) : ℂ) * (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * t))) =
        ((‖P.pk Q' τ₀ k t‖ ^ 2 : ℝ) : ℂ) * ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
          ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * Fmom W Q n *
            (n : ℂ) ^ (-(1 / 2 : ℂ) - Complex.I * t) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      ring
    rw [h1, Complex.re_ofReal_mul]
    ring
  simp_rw [hpt]
  have hre := integral_re hsumI
  simp only [RCLike.re_to_complex] at hre
  rw [integral_const_mul, hre, integral_finsetSum _ hint]
  congr 2
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_const_mul]
  rfl

/-- The family prime part summed over the lattice. -/
lemma famSum_prime_eqH {Q' : ℝ} (hQ' : 1 < Q') (T τ₀ : ℝ) (W : Weight) (Q X : ℝ) :
    famSum W Q (fun _ χ => ∑ k ∈ P.KJ Q' T τ₀, ∫ t : ℝ, ‖P.pk Q' τ₀ k t‖ ^ 2 * Pch X χ t) =
      ∑ k ∈ P.KJ Q' T τ₀, ∫ t : ℝ, ‖P.pk Q' τ₀ k t‖ ^ 2 *
        famSum W Q (fun _ χ => Pch X χ t) := by
  unfold famSum
  have hint : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (k : ℤ),
      Integrable (fun t : ℝ => ‖P.pk Q' τ₀ k t‖ ^ 2 * Pch X χ t) :=
    fun q χ k => integrable_normSq_mul_Pch P hQ' τ₀ k X χ
  have e1 : ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ χ ∈ primChars q,
      ∑ k ∈ P.KJ Q' T τ₀, ∫ t : ℝ, ‖P.pk Q' τ₀ k t‖ ^ 2 * Pch X χ t =
      ∑ k ∈ P.KJ Q' T τ₀, ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ ∈ primChars q,
        ∫ t : ℝ, W.omega Q q * (‖P.pk Q' τ₀ k t‖ ^ 2 * Pch X χ t) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [integral_const_mul]
  rw [e1]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hfun : (fun t : ℝ => ‖P.pk Q' τ₀ k t‖ ^ 2 * ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q *
      ∑ χ ∈ primChars q, Pch X χ t) =
      fun t : ℝ => ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ ∈ primChars q,
        W.omega Q q * (‖P.pk Q' τ₀ k t‖ ^ 2 * Pch X χ t) := by
    funext t
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    ring
  rw [hfun, integral_finsetSum _ (fun q _ => integrable_finsetSum _ fun χ _ =>
    (hint q χ k).const_mul _)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [integral_finsetSum _ (fun χ _ => (hint q χ k).const_mul _)]

/-- `∑_{k ∈ K_J} I(k,n) = n^{−1/2} 2π A(log n) e^{−iτ₀ log n} ∑_{k∈K_J} e^{ik(−2π log n/L)}`, bounded. -/
lemma norm_sum_Ikn_le {Q' : ℝ} (hQ' : 1 < Q') (T τ₀ : ℝ) {r : ℝ} (hr : r < 1 / 2)
    (hrψ : ∀ u : ℝ, r * P.L Q' < |u| → P.ψL Q' u = 0) {n : ℕ} (hn : 2 ≤ n) :
    ‖∑ k ∈ P.KJ Q' T τ₀, Ikn P Q' τ₀ k n‖ ≤
      Real.pi * P.aInt * P.L Q' ^ 2 / ((1 - 2 * r) * Real.log n) / Real.sqrt n := by
  have hn0 : 0 < n := by omega
  have hL := L_pos P hQ'
  have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have ha := aInt_pos P
  set x := Real.log n with hx
  -- rewrite each term
  have hterm : ∀ k ∈ P.KJ Q' T τ₀, Ikn P Q' τ₀ k n = ((n : ℂ) ^ (-(1 / 2 : ℂ)) *
      (2 * Real.pi * (autoc P Q' x : ℂ)) * Complex.exp (-(Complex.I * τ₀ * x))) *
        Complex.exp (Complex.I * (-(2 * Real.pi * x / P.L Q') : ℝ) * (k : ℂ)) := by
    intro k _
    rw [Ikn_eq P hQ' τ₀ k hn0]
    have e : Complex.exp (-(Complex.I * (tau P Q' τ₀ k : ℂ) * (x : ℂ))) =
        Complex.exp (-(Complex.I * τ₀ * x)) *
          Complex.exp (Complex.I * (-(2 * Real.pi * x / P.L Q') : ℝ) * (k : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      unfold tau
      have hL0 : (P.L Q' : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
      push_cast
      field_simp
      ring
    rw [e]; ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, norm_mul]
  -- the constant factor
  have hc1 : ‖(n : ℂ) ^ (-(1 / 2 : ℂ)) * (2 * Real.pi * (autoc P Q' x : ℂ)) *
      Complex.exp (-(Complex.I * τ₀ * x))‖ = 2 * Real.pi * |autoc P Q' x| / Real.sqrt n := by
    rw [norm_mul, norm_mul, norm_mul]
    have h1 : ‖(n : ℂ) ^ (-(1 / 2 : ℂ))‖ = 1 / Real.sqrt n := by
      rw [Complex.norm_natCast_cpow_of_pos hn0]
      have : (-(1 / 2 : ℂ)).re = -(1 / 2) := by simp
      rw [this, Real.rpow_neg (Nat.cast_nonneg n), ← Real.sqrt_eq_rpow, one_div]
    have h2 : ‖Complex.exp (-(Complex.I * τ₀ * x))‖ = 1 := by
      have : -(Complex.I * τ₀ * x) = Complex.I * ((-(τ₀ * x) : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_exp_I_mul_ofReal]
    rw [h1, h2, Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    ring
  rw [hc1]
  by_cases hsupp : 2 * r * P.L Q' < |x|
  · -- the autocorrelation vanishes
    rw [autoc_eq_zero P hrψ hsupp, abs_zero, mul_zero, zero_div, zero_mul]
    exact div_nonneg (div_nonneg (mul_nonneg (mul_nonneg Real.pi_pos.le ha.le) (sq_nonneg _))
      (mul_nonneg (by linarith) hlogn.le)) (Real.sqrt_nonneg _)
  · push Not at hsupp
    rw [abs_of_pos hlogn] at hsupp
    set y := x / P.L Q' with hy
    have hy0 : 0 < y := div_pos hlogn hL
    have hy2 : y ≤ 2 * r := by rw [hy, div_le_iff₀ hL]; linarith
    have hsin := sin_lower hr hy0 hy2
    have hr12 : 0 < 1 - 2 * r := by linarith
    have hsinpos : 0 < Real.sin (Real.pi * y) := lt_of_lt_of_le (by positivity) hsin
    have hθ : Real.sin ((-(2 * Real.pi * x / P.L Q')) / 2) = -Real.sin (Real.pi * y) := by
      rw [← Real.sin_neg]; congr 1; rw [hy]; ring
    have hgeo := norm_sum_exp_Icc_le (-(2 * Real.pi * x / P.L Q')) (by rw [hθ]; linarith)
      (⌈((1 + P.θ) * T - τ₀) * P.L Q' / (2 * Real.pi)⌉)
      (⌊((2 - P.θ) * T - τ₀) * P.L Q' / (2 * Real.pi)⌋)
    have hKJ : P.KJ Q' T τ₀ = Finset.Icc (⌈((1 + P.θ) * T - τ₀) * P.L Q' / (2 * Real.pi)⌉)
        (⌊((2 - P.θ) * T - τ₀) * P.L Q' / (2 * Real.pi)⌋) := rfl
    rw [hKJ]
    rw [hθ, abs_neg, abs_of_pos hsinpos] at hgeo
    have hA := abs_autoc_le P hQ' x
    have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn0)
    -- combine
    have hG : ‖∑ k ∈ Finset.Icc (⌈((1 + P.θ) * T - τ₀) * P.L Q' / (2 * Real.pi)⌉)
        (⌊((2 - P.θ) * T - τ₀) * P.L Q' / (2 * Real.pi)⌋),
          Complex.exp (Complex.I * (-(2 * Real.pi * x / P.L Q') : ℝ) * (k : ℂ))‖ ≤
        P.L Q' / (2 * (1 - 2 * r) * x) := by
      refine hgeo.trans ?_
      rw [div_le_div_iff₀ hsinpos (by positivity)]
      have : 2 * (1 - 2 * r) * y * P.L Q' = 2 * (1 - 2 * r) * x := by
        rw [hy]; field_simp
      nlinarith
    calc 2 * Real.pi * |autoc P Q' x| / Real.sqrt n *
          ‖∑ k ∈ Finset.Icc (⌈((1 + P.θ) * T - τ₀) * P.L Q' / (2 * Real.pi)⌉)
            (⌊((2 - P.θ) * T - τ₀) * P.L Q' / (2 * Real.pi)⌋),
              Complex.exp (Complex.I * (-(2 * Real.pi * x / P.L Q') : ℝ) * (k : ℂ))‖
        ≤ 2 * Real.pi * (P.aInt * P.L Q') / Real.sqrt n * (P.L Q' / (2 * (1 - 2 * r) * x)) := by
          gcongr
      _ = Real.pi * P.aInt * P.L Q' ^ 2 / ((1 - 2 * r) * x) / Real.sqrt n := by
          field_simp

/-- **The prime part of the trace, uniformly in `T`.** -/
theorem trace_prime_bound {Q' : ℝ} (hQ' : 1 < Q') (W : Weight) {Q : ℝ} (hQ : 1 ≤ Q) (T τ₀ : ℝ)
    {r : ℝ} (hr : r < 1 / 2) (hrψ : ∀ u : ℝ, r * P.L Q' < |u| → P.ψL Q' u = 0) :
    |famSum W Q (fun _ χ => ∑ k ∈ P.KJ Q' T τ₀, ∫ t : ℝ, ‖P.pk Q' τ₀ k t‖ ^ 2 *
        Pch (P.X Q') χ t)| ≤
      P.aInt * P.L Q' ^ 2 * (2 * W.wmax * Q / (1 - 2 * r)) *
        (2 * Real.sqrt (P.X Q') * (1 + Real.log (P.X Q'))) := by
  set X := P.X Q' with hX
  have hL := L_pos P hQ'
  have ha := aInt_pos P
  have hX1 : 1 ≤ X := Real.one_le_exp hL.le
  have hwm := W.wmax_nonneg
  have hr12 : 0 < 1 - 2 * r := by linarith
  rw [famSum_prime_eqH P hQ' T τ₀ W Q X]
  simp_rw [integral_normSq_mul_famPch P hQ' τ₀ _ W Q X]
  -- swap the sums
  have hswap : ∑ k ∈ P.KJ Q' T τ₀, -(1 / Real.pi) * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊,
      ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * Fmom W Q n * Ikn P Q' τ₀ k n).re =
      -(1 / Real.pi) * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        Fmom W Q n * ∑ k ∈ P.KJ Q' T τ₀, Ikn P Q' τ₀ k n).re := by
    rw [← Finset.mul_sum, ← Complex.re_sum, Finset.sum_comm]
    congr 2
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.mul_sum]
  rw [hswap, abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 1 / Real.pi)]
  -- termwise bound
  set C₀ : ℝ := P.aInt * P.L Q' ^ 2 * (2 * W.wmax * Q / (1 - 2 * r)) with hC₀
  have hC₀0 : 0 ≤ C₀ := by positivity
  have hterm : ∀ n ∈ Finset.Ioc 0 ⌊X⌋₊,
      ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * Fmom W Q n *
        ∑ k ∈ P.KJ Q' T τ₀, Ikn P Q' τ₀ k n‖ ≤
      Real.pi * (C₀ * ((((n - 1).divisors.card : ℕ) : ℝ) / Real.sqrt n *
        (if 2 ≤ n then 1 else 0))) := by
    intro n hn
    have hn0 : 0 < n := (Finset.mem_Ioc.mp hn).1
    by_cases h2 : 2 ≤ n
    · rw [if_pos h2, mul_one, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      have hΛ : ArithmeticFunction.vonMangoldt n ≤ Real.log n := ArithmeticFunction.vonMangoldt_le_log
      have hF := first_moment W hQ n h2
      have hS := norm_sum_Ikn_le P hQ' T τ₀ hr hrψ h2
      have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn0)
      have hFn : ‖Fmom W Q n‖ ≤ 2 * W.wmax * Q * ((n - 1).divisors.card : ℝ) := hF
      calc ArithmeticFunction.vonMangoldt n * ‖Fmom W Q n‖ *
            ‖∑ k ∈ P.KJ Q' T τ₀, Ikn P Q' τ₀ k n‖
          ≤ Real.log n * (2 * W.wmax * Q * ((n - 1).divisors.card : ℝ)) *
            (Real.pi * P.aInt * P.L Q' ^ 2 / ((1 - 2 * r) * Real.log n) / Real.sqrt n) := by
            gcongr
        _ = Real.pi * (C₀ * ((((n - 1).divisors.card : ℕ) : ℝ) / Real.sqrt n)) := by
            rw [hC₀]; field_simp
    · rw [if_neg h2, mul_zero, mul_zero, mul_zero]
      have hn1 : n = 1 := by omega
      rw [hn1]; simp
  have hsum : ‖∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
      Fmom W Q n * ∑ k ∈ P.KJ Q' T τ₀, Ikn P Q' τ₀ k n‖ ≤
      Real.pi * (C₀ * (2 * Real.sqrt X * (1 + Real.log X))) := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hC₀0) Real.pi_pos.le
    -- restrict to `n ≥ 2`
    have hres : ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ((((n - 1).divisors.card : ℕ) : ℝ) / Real.sqrt n *
        (if 2 ≤ n then 1 else 0)) =
        ∑ n ∈ Finset.Icc 2 ⌊X⌋₊, (((n - 1).divisors.card : ℕ) : ℝ) / Real.sqrt n := by
      rw [← Finset.sum_filter_add_sum_filter_not (Finset.Ioc 0 ⌊X⌋₊) (fun n => 2 ≤ n)]
      have h1 : ∑ n ∈ (Finset.Ioc 0 ⌊X⌋₊).filter (fun n => ¬ 2 ≤ n),
          ((((n - 1).divisors.card : ℕ) : ℝ) / Real.sqrt n * (if 2 ≤ n then 1 else 0)) = 0 := by
        refine Finset.sum_eq_zero fun n hn => ?_
        rw [Finset.mem_filter] at hn
        rw [if_neg hn.2, mul_zero]
      rw [h1, add_zero]
      have hfilt : (Finset.Ioc 0 ⌊X⌋₊).filter (fun n => 2 ≤ n) = Finset.Icc 2 ⌊X⌋₊ := by
        ext n; simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]; omega
      rw [hfilt]
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [if_pos (Finset.mem_Icc.mp hn).1, mul_one]
    rw [hres]
    refine (sum_divisors_div_sqrt_le ⌊X⌋₊).trans ?_
    have hfl : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le (by linarith)
    have hfl0 : (0 : ℝ) ≤ ⌊X⌋₊ := Nat.cast_nonneg _
    have hlogfl : Real.log ⌊X⌋₊ ≤ Real.log X := by
      rcases (Nat.cast_nonneg (α := ℝ) ⌊X⌋₊).eq_or_lt with h | h
      · rw [← h, Real.log_zero]; exact Real.log_nonneg hX1
      · exact Real.log_le_log h hfl
    have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX1
    have hlogfl0 : 0 ≤ 1 + Real.log ⌊X⌋₊ := by
      rcases (Nat.cast_nonneg (α := ℝ) ⌊X⌋₊).eq_or_lt with h | h
      · rw [← h, Real.log_zero]; norm_num
      · have : (1 : ℝ) ≤ ⌊X⌋₊ := by
          have : (0 : ℕ) < ⌊X⌋₊ := by exact_mod_cast h
          exact_mod_cast this
        linarith [Real.log_nonneg this]
    gcongr
  calc 1 / Real.pi * |(∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        Fmom W Q n * ∑ k ∈ P.KJ Q' T τ₀, Ikn P Q' τ₀ k n).re|
      ≤ 1 / Real.pi * ‖∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        Fmom W Q n * ∑ k ∈ P.KJ Q' T τ₀, Ikn P Q' τ₀ k n‖ :=
        mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (by positivity)
    _ ≤ 1 / Real.pi * (Real.pi * (C₀ * (2 * Real.sqrt X * (1 + Real.log X)))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = C₀ * (2 * Real.sqrt X * (1 + Real.log X)) := by field_simp

end Families.Hybrid.Z
