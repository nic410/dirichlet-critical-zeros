/-
# Finite-centre replacement `eq:fc2` (upper half)

`fc2_proof : ExplicitGabor_Statement → MV_LargeSieve → StirlingDigamma → lemWH_Statement → FC2_Statement`.

Route (proof of `prop:finitecentre`, Proposition 4.4, adapted):
* `p_k(t) = L·U(L(t − τ_k))` is real, `U = \hat ψ` has Schwartz decay: `|U(y)| ≤ C_U ρ(y)⁸`,
  `ρ(y) = 1/(1+|y|)`;
* Poisson–Gabor (`lem:gabor`): `∑_{k∈ℤ} p_k(t) p_k(t') = L Re Φ(t−t')` (Parseval on `[−L/2, L/2]`,
  polarised);
* lattice sum `∑_k ρ(x − 2πk)² ≤ C_lat`;
* kernel bound: with `K_d(t,t') = ∑_{k∈K_J} p_k(t)p_k(t')`,
  `E = K_d² − L²Φ(t−t')²1_J(t)1_J(t')` satisfies `|E(t,t')| ≤ C L⁴ ρ(L D(t))³ ρ(L(t−t'))³`,
  `D(t) = min(|t−a|, |t−b|)`, `J = [a,b]`;
* the family bound `∑_χ ω_χ ν_χ(t)² ≤ H (A₀ + B₀|t|)` (Stirling + large sieve + `H ≫ Q²`);
* Fubini: `∑_{k,l∈K} G_{kl}² = ∬ K_d(t,t')² ν(t)ν(t')`, and the error is
  `≪ H(L⁵ + L²T + …) = o(H T L⁵)`.
-/
import Families.Ported.Second.Common

noncomputable section

open scoped BigOperators ComplexConjugate ContDiff FourierTransform
open Finset MeasureTheory Filter Topology

namespace Families.Ported.Second

open Families

namespace FC2

/-! ### The envelope `ρ(x) = 1/(1+|x|)` and the master integrals -/

section Rho

/-- `ρ(x) = 1/(1+|x|)`. -/
def rho (x : ℝ) : ℝ := 1 / (1 + |x|)

lemma rho_pos (x : ℝ) : 0 < rho x := by unfold rho; positivity

lemma rho_nonneg (x : ℝ) : 0 ≤ rho x := (rho_pos x).le

lemma rho_le_one (x : ℝ) : rho x ≤ 1 := by
  unfold rho; rw [div_le_one (by positivity)]; linarith [abs_nonneg x]

lemma rho_anti {x y : ℝ} (h : |x| ≤ |y|) : rho y ≤ rho x := by
  unfold rho; exact one_div_le_one_div_of_le (by positivity) (by linarith)

lemma rho_neg (x : ℝ) : rho (-x) = rho x := by simp [rho, abs_neg]

lemma rho_abs (x : ℝ) : rho |x| = rho x := by simp [rho, abs_abs]

lemma rho_mul_le (x y : ℝ) : rho x * rho y ≤ rho (x - y) := by
  unfold rho
  rw [div_mul_div_comm, one_mul]
  apply one_div_le_one_div_of_le (by positivity)
  have := abs_sub x y
  nlinarith [abs_nonneg x, abs_nonneg y, mul_nonneg (abs_nonneg x) (abs_nonneg y)]

lemma rho_continuous : Continuous rho := by
  unfold rho
  exact continuous_const.div (continuous_const.add continuous_abs)
    (fun x => by positivity)

lemma rho_mul_abs_le (x : ℝ) : rho x * |x| ≤ 1 := by
  unfold rho
  rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; linarith

lemma rho_pow_eq_rpow (x : ℝ) (n : ℕ) : rho x ^ n = (1 + ‖x‖) ^ (-(n : ℝ)) := by
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, Real.norm_eq_abs, rho, one_div, inv_pow]

lemma integrable_rho_pow {n : ℕ} (hn : 2 ≤ n) : Integrable (fun x : ℝ => rho x ^ n) := by
  have h := integrable_one_add_norm (E := ℝ) (μ := volume) (r := (n : ℝ))
    (by rw [Module.finrank_self]; exact_mod_cast (show 1 < n by omega))
  exact h.congr (Eventually.of_forall fun x => (rho_pow_eq_rpow x n).symm)

lemma integrable_rho3_abs : Integrable (fun x : ℝ => rho x ^ 3 * |x|) := by
  refine (integrable_rho_pow (n := 2) le_rfl).mono'
    ((rho_continuous.pow 3).mul continuous_abs).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg (rho_nonneg x) 3) (abs_nonneg x))]
  have h1 := rho_mul_abs_le x
  have h2 := rho_nonneg x
  calc rho x ^ 3 * |x| = rho x ^ 2 * (rho x * |x|) := by ring
    _ ≤ rho x ^ 2 * 1 := mul_le_mul_of_nonneg_left h1 (pow_nonneg h2 2)
    _ = rho x ^ 2 := mul_one _

/-- `I₀ = ∫ ρ³`. -/
def I0 : ℝ := ∫ x, rho x ^ 3
/-- `I₁ = ∫ ρ³ |x|`. -/
def I1 : ℝ := ∫ x, rho x ^ 3 * |x|

lemma I0_nonneg : 0 ≤ I0 := integral_nonneg fun x => pow_nonneg (rho_nonneg x) 3

lemma I1_nonneg : 0 ≤ I1 :=
  integral_nonneg fun x => mul_nonneg (pow_nonneg (rho_nonneg x) 3) (abs_nonneg x)

lemma integrable_rho3_sc {L : ℝ} (hL : 0 < L) (c : ℝ) :
    Integrable (fun t : ℝ => rho (L * (t - c)) ^ 3) :=
  ((integrable_rho_pow (n := 3) (by norm_num)).comp_mul_left' hL.ne').comp_sub_right c

lemma integral_rho3_sc {L : ℝ} (hL : 0 < L) (c : ℝ) :
    ∫ t : ℝ, rho (L * (t - c)) ^ 3 = I0 / L := by
  rw [integral_sub_right_eq_self (fun t => rho (L * t) ^ 3) c,
    Measure.integral_comp_mul_left (fun x => rho x ^ 3) L, abs_inv, abs_of_pos hL, smul_eq_mul,
    I0]
  field_simp

lemma integrable_rho3_abs_sc {L : ℝ} (hL : 0 < L) (c : ℝ) :
    Integrable (fun t : ℝ => rho (L * (t - c)) ^ 3 * |t - c|) := by
  have h := ((integrable_rho3_abs.comp_mul_left' hL.ne').comp_sub_right c).const_mul L⁻¹
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only
  rw [abs_mul, abs_of_pos hL]
  field_simp

lemma integral_rho3_abs_sc {L : ℝ} (hL : 0 < L) (c : ℝ) :
    ∫ t : ℝ, rho (L * (t - c)) ^ 3 * |t - c| = I1 / L ^ 2 := by
  rw [integral_sub_right_eq_self (fun t => rho (L * t) ^ 3 * |t|) c]
  have : (fun t : ℝ => rho (L * t) ^ 3 * |t|) = fun t => L⁻¹ * (rho (L * t) ^ 3 * |L * t|) := by
    funext t; rw [abs_mul, abs_of_pos hL]; field_simp
  rw [this, integral_const_mul, Measure.integral_comp_mul_left (fun x => rho x ^ 3 * |x|) L,
    abs_inv, abs_of_pos hL, smul_eq_mul, I1]
  field_simp

end Rho

/-! ### The lattice sum -/

section Lattice

lemma summable_rho_int_sq : Summable (fun j : ℤ => rho j ^ 2) := by
  refine Summable.of_norm_bounded_eventually (Real.summable_abs_int_rpow (b := 2) (by norm_num)) ?_
  filter_upwards [eventually_cofinite_ne 0] with j hj
  have hj' : (0 : ℝ) < |(j : ℝ)| := abs_pos.mpr (by exact_mod_cast hj)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (rho_nonneg _) 2), Real.rpow_neg hj'.le,
    Real.rpow_two, rho, div_pow, one_pow]
  rw [one_div]
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hj'.le (by linarith) 2)

/-- `C_lat = 4 ∑_j ρ(j)²`. -/
def Clat : ℝ := 4 * ∑' j : ℤ, rho j ^ 2

lemma Clat_nonneg : 0 ≤ Clat :=
  mul_nonneg (by norm_num) (tsum_nonneg fun j => pow_nonneg (rho_nonneg _) 2)

lemma rho_lattice_le (x : ℝ) (k : ℤ) :
    rho (x - 2 * Real.pi * k) ≤ 2 * rho ((⌊x / (2 * Real.pi)⌋ - k : ℤ) : ℝ) := by
  set n₀ := ⌊x / (2 * Real.pi)⌋
  set j : ℤ := n₀ - k with hj
  have hpi := Real.pi_gt_three
  have hpi0 : 0 < 2 * Real.pi := by positivity
  have h1 := Int.floor_le (x / (2 * Real.pi))
  have h2 := Int.lt_floor_add_one (x / (2 * Real.pi))
  have hx : x - 2 * Real.pi * k = 2 * Real.pi * (x / (2 * Real.pi) - k) := by
    field_simp
  set y := x / (2 * Real.pi) - k with hy
  have hjy1 : (j : ℝ) ≤ y := by rw [hj, hy]; push_cast; linarith
  have hjy2 : y < (j : ℝ) + 1 := by rw [hj, hy]; push_cast; linarith
  -- `1 + |j| ≤ 2 (1 + |x − 2πk|)`
  have key : 1 + |(j : ℝ)| ≤ 2 * (1 + |x - 2 * Real.pi * k|) := by
    rw [hx, abs_mul, abs_of_pos hpi0]
    rcases le_or_gt 0 j with hj0 | hj0
    · have hj0' : (0 : ℝ) ≤ j := by exact_mod_cast hj0
      rw [abs_of_nonneg hj0', abs_of_nonneg (by linarith)]
      nlinarith
    · have hj0' : (j : ℝ) ≤ -1 := by exact_mod_cast (show j ≤ -1 by omega)
      rw [abs_of_neg (by linarith), abs_of_nonpos (by linarith)]
      nlinarith
  unfold rho
  rw [show (2 : ℝ) * (1 / (1 + |(j : ℝ)|)) = 1 / ((1 + |(j : ℝ)|) / 2) by field_simp]
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

lemma lattice (x : ℝ) :
    Summable (fun k : ℤ => rho (x - 2 * Real.pi * k) ^ 2) ∧
      ∑' k : ℤ, rho (x - 2 * Real.pi * k) ^ 2 ≤ Clat := by
  set n₀ := ⌊x / (2 * Real.pi)⌋
  have hs : Summable (fun k : ℤ => 4 * rho ((n₀ - k : ℤ) : ℝ) ^ 2) := by
    have := (Equiv.summable_iff (Equiv.subLeft n₀)).mpr summable_rho_int_sq
    exact this.mul_left 4
  have hle : ∀ k : ℤ, rho (x - 2 * Real.pi * k) ^ 2 ≤ 4 * rho ((n₀ - k : ℤ) : ℝ) ^ 2 := by
    intro k
    have := rho_lattice_le x k
    have h0 := rho_nonneg (x - 2 * Real.pi * k)
    nlinarith
  have hs1 : Summable (fun k : ℤ => rho (x - 2 * Real.pi * k) ^ 2) :=
    Summable.of_nonneg_of_le (fun k => pow_nonneg (rho_nonneg _) 2) hle hs
  refine ⟨hs1, ?_⟩
  calc ∑' k : ℤ, rho (x - 2 * Real.pi * k) ^ 2 ≤ ∑' k : ℤ, 4 * rho ((n₀ - k : ℤ) : ℝ) ^ 2 :=
        hs1.tsum_le_tsum hle hs
    _ = 4 * ∑' k : ℤ, rho ((n₀ - k : ℤ) : ℝ) ^ 2 := tsum_mul_left
    _ = Clat := by
        rw [Clat]
        congr 1
        exact (Equiv.subLeft n₀).tsum_eq (fun j : ℤ => rho (j : ℝ) ^ 2)

end Lattice

/-! ### `U = \hat ψ`: scaling, reality, Schwartz envelope -/

section Envelope

variable (P : PrimeSetup)

/-- `ψ` as a complex function. -/
def ψC : ℝ → ℂ := fun s => ((P.ψ s : ℝ) : ℂ)

lemma ψC_hasCompactSupport : HasCompactSupport (ψC P) := by
  obtain ⟨r, -, hr⟩ := P.ψ_supp
  refine HasCompactSupport.intro (K := Set.Icc (-|r|) (|r|)) isCompact_Icc ?_
  intro x hx
  have hx' : r < |x| := by
    by_contra hcon
    exact hx (Set.mem_Icc.mpr (abs_le.mp ((not_lt.mp hcon).trans (le_abs_self r))))
  simp [ψC, hr x hx']

lemma ψC_contDiff : ContDiff ℝ ∞ (ψC P) :=
  Complex.ofRealCLM.contDiff.comp P.ψ_smooth

/-- `U(y) = ∫ ψ(s) e^{iys} ds`. -/
def U (y : ℝ) : ℂ := ∫ s, ψC P s * Complex.exp (Complex.I * y * s)

lemma U_eq_fourier (y : ℝ) : U P y = 𝓕 (ψC P) (-(y / (2 * Real.pi))) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 2
  push_cast
  field_simp

lemma U_continuous : Continuous (U P) := by
  set S := (ψC_hasCompactSupport P).toSchwartzMap (ψC_contDiff P)
  have h1 : (S : ℝ → ℂ) = ψC P := rfl
  have h2 := (𝓕 S).continuous
  rw [SchwartzMap.fourier_coe, h1] at h2
  have : U P = fun y => 𝓕 (ψC P) (-(y / (2 * Real.pi))) := funext (U_eq_fourier P)
  rw [this]; exact h2.comp (by fun_prop)

lemma U_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖U P y‖ ≤ C * rho y ^ 8 := by
  set S := (ψC_hasCompactSupport P).toSchwartzMap (ψC_contDiff P)
  have h1 : (S : ℝ → ℂ) = ψC P := rfl
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ ξ : ℝ, (1 + ‖ξ‖) ^ 8 * ‖𝓕 (ψC P) ξ‖ ≤ M := by
    refine ⟨2 ^ 8 * (Finset.Iic ((8 : ℕ), (0 : ℕ))).sup
      (fun m => SchwartzMap.seminorm ℝ m.1 m.2) (𝓕 S), fun ξ => ?_⟩
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (8, 0)) (k := 8) (n := 0)
      le_rfl le_rfl (𝓕 S) ξ
    rw [norm_iteratedFDeriv_zero, SchwartzMap.fourier_coe, h1] at this
    exact this
  have hM0 : 0 ≤ M := le_trans (by positivity) (hM 0)
  refine ⟨M * (2 * Real.pi) ^ 8, by positivity, fun y => ?_⟩
  rw [U_eq_fourier]
  set ξ := -(y / (2 * Real.pi))
  have hpi : 0 < 2 * Real.pi := by positivity
  have hξ : |y| = 2 * Real.pi * |ξ| := by
    simp only [ξ, abs_neg, abs_div, abs_of_pos hpi]; field_simp
  have h1y : 1 + |y| ≤ 2 * Real.pi * (1 + ‖ξ‖) := by
    rw [hξ, Real.norm_eq_abs]; nlinarith [Real.pi_gt_three, abs_nonneg ξ]
  have hb := hM ξ
  have hpos : 0 < (1 + ‖ξ‖) ^ 8 := by positivity
  have hF : ‖𝓕 (ψC P) ξ‖ ≤ M / (1 + ‖ξ‖) ^ 8 := by
    rw [le_div_iff₀ hpos]; linarith [mul_comm ((1 + ‖ξ‖) ^ 8) ‖𝓕 (ψC P) ξ‖]
  refine hF.trans ?_
  have hy8 : (1 + |y|) ^ 8 ≤ (2 * Real.pi) ^ 8 * (1 + ‖ξ‖) ^ 8 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h1y 8
  rw [rho, div_pow, one_pow, ← mul_div_assoc, mul_one, div_le_div_iff₀ hpos (by positivity)]
  nlinarith

lemma U_conj (y : ℝ) : conj (U P y) = U P y := by
  unfold U
  rw [← integral_conj, ← integral_neg_eq_self (fun s => ψC P s * Complex.exp (Complex.I * y * s))
    volume]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [ψC, map_mul, Complex.conj_ofReal, ← Complex.exp_conj, Complex.conj_I]
  rw [P.ψ_even s]
  congr 2
  push_cast; ring

lemma U_im (y : ℝ) : (U P y).im = 0 := Complex.conj_eq_iff_im.mp (U_conj P y)

lemma hatψL_eq_U {Q : ℝ} (hQ : 1 < Q) (x : ℝ) :
    P.hatψL Q (x : ℂ) = P.L Q * U P (P.L Q * x) := by
  have hL := P.L_pos hQ
  set k : ℝ → ℂ := fun s => ψC P s * Complex.exp (Complex.I * ↑(P.L Q * x) * s) with hk
  have := Measure.integral_comp_div k (P.L Q)
  rw [abs_of_pos hL, Complex.real_smul] at this
  unfold PrimeSetup.hatψL U
  rw [← this]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  have hL' : (P.L Q : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  simp only [hk, ψC, PrimeSetup.ψL]
  push_cast
  congr 2
  field_simp

/-- `τ_k = τ₀ + 2πk/L`. -/
def tau (Q τ₀ : ℝ) (k : ℤ) : ℝ := τ₀ + 2 * Real.pi * k / P.L Q

/-- `p_k(t)` for real `t`, as a real number: `L · U(L(t − τ_k))`. -/
def pr (Q τ₀ : ℝ) (k : ℤ) (t : ℝ) : ℝ := P.L Q * (U P (P.L Q * (t - tau P Q τ₀ k))).re

lemma pk_eq {Q : ℝ} (hQ : 1 < Q) (τ₀ : ℝ) (k : ℤ) (t : ℝ) :
    P.pk Q τ₀ k (t : ℂ) = (pr P Q τ₀ k t : ℂ) := by
  unfold PrimeSetup.pk
  have : (t : ℂ) - (τ₀ + 2 * Real.pi * k / P.L Q) = ((t - tau P Q τ₀ k : ℝ) : ℂ) := by
    simp only [tau]; push_cast; ring
  rw [this, hatψL_eq_U P hQ]
  unfold pr
  apply Complex.ext
  · simp
  · simp [U_im]

lemma pr_continuous (Q τ₀ : ℝ) (k : ℤ) : Continuous (pr P Q τ₀ k) := by
  unfold pr
  exact continuous_const.mul (Complex.continuous_re.comp ((U_continuous P).comp (by fun_prop)))

lemma pr_bound {CU : ℝ} (hCU : ∀ y, ‖U P y‖ ≤ CU * rho y ^ 8) {Q : ℝ} (hQ : 1 < Q) (τ₀ : ℝ)
    (k : ℤ) (t : ℝ) :
    |pr P Q τ₀ k t| ≤ CU * P.L Q * rho (P.L Q * (t - tau P Q τ₀ k)) ^ 8 := by
  have hL := P.L_pos hQ
  unfold pr
  rw [abs_mul, abs_of_pos hL]
  have := (Complex.abs_re_le_norm (U P (P.L Q * (t - tau P Q τ₀ k)))).trans (hCU _)
  nlinarith

end Envelope

/-! ### Poisson–Gabor (`lem:gabor`): `∑_k p_k(t) p_k(t') = L Re Φ(t − t')` -/

section Gabor

variable (P : PrimeSetup)

lemma aInt_pos' : 0 < P.aInt := by
  obtain ⟨x₀, hx₀⟩ := P.ψ_ne
  have hc : Continuous P.vfun := (P.ψ_smooth.continuous).pow 2
  have hcs : HasCompactSupport P.vfun := by
    obtain ⟨r, -, hr⟩ := P.ψ_supp
    refine HasCompactSupport.intro (K := Set.Icc (-|r|) (|r|)) isCompact_Icc ?_
    intro x hx
    have hx' : r < |x| := by
      by_contra hcon
      exact hx (Set.mem_Icc.mpr (abs_le.mp ((not_lt.mp hcon).trans (le_abs_self r))))
    simp [PrimeSetup.vfun, hr x hx']
  have hv : P.vfun x₀ ≠ 0 := by simp only [PrimeSetup.vfun]; exact pow_ne_zero 2 hx₀
  exact hc.integral_pos_of_hasCompactSupport_nonneg_nonzero hcs (fun x => sq_nonneg _) hv

lemma ψL_zero_of {Q : ℝ} (hQ : 1 < Q) {u : ℝ} (hu : P.L Q / 2 ≤ |u|) : P.ψL Q u = 0 := by
  obtain ⟨r, hr, hr0⟩ := P.ψ_supp
  have hL := P.L_pos hQ
  unfold PrimeSetup.ψL
  apply hr0
  rw [abs_div, abs_of_pos hL, lt_div_iff₀ hL]
  by_cases hr' : r ≤ 0
  · nlinarith [abs_nonneg u]
  · nlinarith

lemma ψL_continuous (Q : ℝ) : Continuous (P.ψL Q) :=
  P.ψ_smooth.continuous.comp (continuous_id.div_const _)

lemma not_mem_Ioc_half {L u : ℝ} (hu : u ∉ Set.Ioc (-(L / 2)) (L / 2)) (hL : 0 < L) :
    L / 2 ≤ |u| := by
  simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hu
  rcases hu with h | h
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

/-- The Parseval test function `g_s(u) = ψ_L(u)(e^{i(t−τ₀)u} + s e^{i(t'−τ₀)u})`. -/
def gfun (Q τ₀ t t' s : ℝ) (u : ℝ) : ℂ :=
  (P.ψL Q u : ℂ) * (Complex.exp (Complex.I * ↑(t - τ₀) * ↑u) +
    (s : ℂ) * Complex.exp (Complex.I * ↑(t' - τ₀) * ↑u))

lemma gfun_continuous (Q τ₀ t t' s : ℝ) : Continuous (gfun P Q τ₀ t t' s) := by
  have hψ : Continuous (fun u => (P.ψL Q u : ℂ)) :=
    Complex.continuous_ofReal.comp (ψL_continuous P Q)
  unfold gfun
  fun_prop

lemma piece_integral {Q : ℝ} (hQ : 1 < Q) (τ₀ : ℝ) (k : ℤ) (t : ℝ) :
    ∫ u in (-(P.L Q / 2))..(P.L Q / 2),
      Complex.exp (2 * Real.pi * Complex.I * ((-k : ℤ) : ℂ) * u / (P.L Q : ℂ)) *
        ((P.ψL Q u : ℂ) * Complex.exp (Complex.I * ↑(t - τ₀) * ↑u)) = (pr P Q τ₀ k t : ℂ) := by
  have hL := P.L_pos hQ
  have hL' : (P.L Q : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [intervalIntegral.integral_of_le (by linarith),
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  · rw [← pk_eq P hQ τ₀ k t]
    unfold PrimeSetup.pk PrimeSetup.hatψL
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  · intro u hu
    rw [ψL_zero_of P hQ (not_mem_Ioc_half hu hL)]
    simp

lemma coeff_gfun {Q : ℝ} (hQ : 1 < Q) (τ₀ t t' s : ℝ) (hab : -(P.L Q / 2) < P.L Q / 2) (k : ℤ) :
    fourierCoeffOn hab (gfun P Q τ₀ t t' s) k =
      (((P.L Q)⁻¹ * (pr P Q τ₀ k t + s * pr P Q τ₀ k t') : ℝ) : ℂ) := by
  have hL := P.L_pos hQ
  have hψ : Continuous (fun u => (P.ψL Q u : ℂ)) :=
    Complex.continuous_ofReal.comp (ψL_continuous P Q)
  rw [fourierCoeffOn_eq_integral]
  have hba : P.L Q / 2 - -(P.L Q / 2) = P.L Q := by ring
  have e : ∀ x : ℝ, fourier (-k) (x : AddCircle (P.L Q / 2 - -(P.L Q / 2))) •
      gfun P Q τ₀ t t' s x =
      Complex.exp (2 * Real.pi * Complex.I * ((-k : ℤ) : ℂ) * x / (P.L Q : ℂ)) *
        ((P.ψL Q x : ℂ) * Complex.exp (Complex.I * ↑(t - τ₀) * ↑x)) +
      (s : ℂ) * (Complex.exp (2 * Real.pi * Complex.I * ((-k : ℤ) : ℂ) * x / (P.L Q : ℂ)) *
        ((P.ψL Q x : ℂ) * Complex.exp (Complex.I * ↑(t' - τ₀) * ↑x))) := by
    intro x
    rw [fourier_coe_apply, smul_eq_mul, hba]
    unfold gfun; ring
  rw [intervalIntegral.integral_congr (fun x _ => e x), intervalIntegral.integral_add,
    intervalIntegral.integral_const_mul, piece_integral P hQ, piece_integral P hQ, hba,
    Complex.real_smul]
  · push_cast; ring
  · exact Continuous.intervalIntegrable (by fun_prop) _ _
  · exact Continuous.intervalIntegrable (by fun_prop) _ _

lemma parseval_gfun {Q : ℝ} (hQ : 1 < Q) (τ₀ t t' s : ℝ) :
    HasSum (fun k : ℤ => ((P.L Q)⁻¹ * (pr P Q τ₀ k t + s * pr P Q τ₀ k t')) ^ 2)
      ((P.L Q)⁻¹ * ∫ u in (-(P.L Q / 2))..(P.L Q / 2), ‖gfun P Q τ₀ t t' s u‖ ^ 2) := by
  have hL := P.L_pos hQ
  have hab : -(P.L Q / 2) < P.L Q / 2 := by linarith
  have hcs : HasCompactSupport (gfun P Q τ₀ t t' s) := by
    refine HasCompactSupport.intro (K := Set.Icc (-(P.L Q / 2)) (P.L Q / 2)) isCompact_Icc ?_
    intro u hu
    have : P.L Q / 2 ≤ |u| := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hu
      rcases hu with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    simp [gfun, ψL_zero_of P hQ this]
  have hL2 : MemLp (gfun P Q τ₀ t t' s) 2
      (volume.restrict (Set.Ioc (-(P.L Q / 2)) (P.L Q / 2))) :=
    ((gfun_continuous P Q τ₀ t t' s).memLp_of_hasCompactSupport hcs).restrict _
  have h := hasSum_sq_fourierCoeffOn hab hL2
  have hba : P.L Q / 2 - -(P.L Q / 2) = P.L Q := by ring
  rw [hba, smul_eq_mul] at h
  convert h using 1
  funext k
  rw [coeff_gfun P hQ τ₀ t t' s hab k, Complex.norm_real, Real.norm_eq_abs, sq_abs]

lemma gfun_norm_sq_diff (Q τ₀ t t' u : ℝ) :
    ‖gfun P Q τ₀ t t' 1 u‖ ^ 2 - ‖gfun P Q τ₀ t t' (-1) u‖ ^ 2 =
      4 * (P.ψL Q u ^ 2 * Real.cos ((t - t') * u)) := by
  have e : ∀ α : ℝ, Complex.exp (Complex.I * ↑α * ↑u) = Complex.exp (↑(α * u) * Complex.I) := by
    intro α; congr 1; push_cast; ring
  unfold gfun
  rw [e, e]
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  rw [show (t - t') * u = (t - τ₀) * u - (t' - τ₀) * u by ring, Real.cos_sub]
  ring

lemma Φ_re_eq {Q : ℝ} (hQ : 1 < Q) (r : ℝ) :
    (P.Φ Q r).re = ∫ u in (-(P.L Q / 2))..(P.L Q / 2), P.ψL Q u ^ 2 * Real.cos (r * u) := by
  have hL := P.L_pos hQ
  have hψ : Continuous (fun u => (P.ψL Q u : ℂ)) :=
    Complex.continuous_ofReal.comp (ψL_continuous P Q)
  have hint : Integrable (fun u : ℝ => (P.ψL Q u : ℂ) ^ 2 * Complex.exp (Complex.I * r * u)) := by
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
    refine HasCompactSupport.intro (K := Set.Icc (-(P.L Q / 2)) (P.L Q / 2)) isCompact_Icc ?_
    intro u hu
    have : P.L Q / 2 ≤ |u| := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hu
      rcases hu with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    simp [ψL_zero_of P hQ this]
  unfold PrimeSetup.Φ
  rw [← RCLike.re_to_complex, ← integral_re hint, intervalIntegral.integral_of_le (by linarith),
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  · refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [RCLike.re_to_complex]
    rw [show Complex.I * r * u = ↑(r * u) * Complex.I by push_cast; ring, ← Complex.ofReal_pow,
      Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  · intro u hu; rw [ψL_zero_of P hQ (not_mem_Ioc_half hu hL)]; simp

/-- **Poisson–Gabor** (`lem:gabor`). -/
theorem PG {Q : ℝ} (hQ : 1 < Q) (τ₀ t t' : ℝ) :
    HasSum (fun k : ℤ => pr P Q τ₀ k t * pr P Q τ₀ k t') (P.L Q * (P.Φ Q (t - t')).re) := by
  have hL := P.L_pos hQ
  have h1 := parseval_gfun P hQ τ₀ t t' 1
  have h2 := parseval_gfun P hQ τ₀ t t' (-1)
  have h3 := (h1.sub h2).mul_left (P.L Q ^ 2 / 4)
  have hI : (∫ u in (-(P.L Q / 2))..(P.L Q / 2), ‖gfun P Q τ₀ t t' 1 u‖ ^ 2) -
      (∫ u in (-(P.L Q / 2))..(P.L Q / 2), ‖gfun P Q τ₀ t t' (-1) u‖ ^ 2) =
      4 * (P.Φ Q (t - t')).re := by
    rw [← intervalIntegral.integral_sub, Φ_re_eq P hQ, ← intervalIntegral.integral_const_mul]
    · exact intervalIntegral.integral_congr (fun u _ => gfun_norm_sq_diff P Q τ₀ t t' u)
    · exact ((gfun_continuous P Q τ₀ t t' 1).norm.pow 2).intervalIntegrable _ _
    · exact ((gfun_continuous P Q τ₀ t t' (-1)).norm.pow 2).intervalIntegrable _ _
  have h4 := h3.congr_fun (g := fun k => pr P Q τ₀ k t * pr P Q τ₀ k t')
    (fun k => by field_simp; ring)
  rwa [← mul_sub, hI, show P.L Q ^ 2 / 4 * ((P.L Q)⁻¹ * (4 * (P.Φ Q (t - t')).re)) =
    P.L Q * (P.Φ Q (t - t')).re by field_simp] at h4

lemma abs_LΦ_le {Q : ℝ} (hQ : 1 < Q) (r : ℝ) :
    |P.L Q * (P.Φ Q r).re| ≤ P.aInt * P.L Q ^ 2 := by
  have hL := P.L_pos hQ
  have ha := aInt_pos' P
  have h := PhiSq_le P hQ r
  rw [PhiSq_eq] at h
  have h' : |(P.Φ Q r).re| ≤ P.aInt * P.L Q := by
    have := sq_le_sq.mp h
    rwa [abs_of_pos (mul_pos ha hL)] at this
  rw [abs_mul, abs_of_pos hL]
  nlinarith

lemma sum_sq_le {Q : ℝ} (hQ : 1 < Q) (τ₀ t : ℝ) (K : Finset ℤ) :
    ∑ k ∈ K, pr P Q τ₀ k t ^ 2 ≤ P.aInt * P.L Q ^ 2 := by
  have h := PG P hQ τ₀ t t
  rw [sub_self] at h
  have h1 : ∑ k ∈ K, pr P Q τ₀ k t * pr P Q τ₀ k t ≤ P.L Q * (P.Φ Q 0).re :=
    sum_le_hasSum K (fun k _ => mul_self_nonneg _) h
  have h2 := (abs_le.mp (abs_LΦ_le P hQ 0)).2
  simp only [sq]
  linarith

end Gabor

/-! ### The kernel bound `|E(t,t')| ≤ C L⁴ ρ(L D(t))³ ρ(L(t−t'))³` -/

section Kernel

variable (P : PrimeSetup)

lemma mem_KJ_iff {Q : ℝ} (hQ : 1 < Q) (T τ₀ : ℝ) (k : ℤ) :
    k ∈ P.KJ Q T τ₀ ↔ tau P Q τ₀ k ∈ P.J T := by
  have hL := P.L_pos hQ
  have hpi : 0 < 2 * Real.pi := by positivity
  unfold PrimeSetup.KJ PrimeSetup.J tau
  rw [Finset.mem_Icc, Set.mem_Icc, Int.ceil_le, Int.le_floor, div_le_iff₀ hpi, le_div_iff₀ hpi]
  have e : ∀ x : ℝ, x ≤ τ₀ + 2 * Real.pi * k / P.L Q ↔ (x - τ₀) * P.L Q ≤ k * (2 * Real.pi) := by
    intro x
    rw [← sub_le_iff_le_add', le_div_iff₀ hL]; constructor <;> intro h <;> linarith
  have e' : ∀ x : ℝ, τ₀ + 2 * Real.pi * k / P.L Q ≤ x ↔ k * (2 * Real.pi) ≤ (x - τ₀) * P.L Q := by
    intro x
    rw [← le_sub_iff_add_le', div_le_iff₀ hL]; constructor <;> intro h <;> linarith
  rw [e, e']

/-- `D(t) = min(|t−a|, |t−b|)`. -/
def Dd (a b t : ℝ) : ℝ := min |t - a| |t - b|

lemma Dd_nonneg (a b t : ℝ) : 0 ≤ Dd a b t := le_min (abs_nonneg _) (abs_nonneg _)

lemma Dd_le_of_mem_not_mem {a b x y : ℝ} (hx : x ∈ Set.Icc a b) (hy : y ∉ Set.Icc a b) :
    Dd a b x ≤ |x - y| := by
  simp only [Set.mem_Icc, not_and_or, not_le] at hx hy
  obtain ⟨hxa, hxb⟩ := hx
  rcases hy with hy | hy
  · calc Dd a b x ≤ |x - a| := min_le_left _ _
      _ = x - a := abs_of_nonneg (by linarith)
      _ ≤ x - y := by linarith
      _ ≤ |x - y| := le_abs_self _
  · calc Dd a b x ≤ |x - b| := min_le_right _ _
      _ = b - x := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
      _ ≤ y - x := by linarith
      _ ≤ |x - y| := by rw [abs_sub_comm]; exact le_abs_self _

lemma Dd_le_of_not_mem_mem {a b x y : ℝ} (hx : x ∉ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    Dd a b x ≤ |x - y| := by
  simp only [Set.mem_Icc, not_and_or, not_le] at hx hy
  obtain ⟨hya, hyb⟩ := hy
  rcases hx with hx | hx
  · calc Dd a b x ≤ |x - a| := min_le_left _ _
      _ = a - x := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
      _ ≤ y - x := by linarith
      _ ≤ |x - y| := by rw [abs_sub_comm]; exact le_abs_self _
  · calc Dd a b x ≤ |x - b| := min_le_right _ _
      _ = x - b := abs_of_nonneg (by linarith)
      _ ≤ x - y := by linarith
      _ ≤ |x - y| := le_abs_self _

lemma rhoD_le {L : ℝ} (hL : 0 < L) (a b t : ℝ) :
    rho (L * Dd a b t) ^ 3 ≤ rho (L * (t - a)) ^ 3 + rho (L * (t - b)) ^ 3 := by
  have ha := pow_nonneg (rho_nonneg (L * (t - a))) 3
  have hb := pow_nonneg (rho_nonneg (L * (t - b))) 3
  rcases min_choice |t - a| |t - b| with h | h
  · have : rho (L * Dd a b t) = rho (L * (t - a)) := by
      rw [Dd, h, ← rho_abs (L * (t - a)), abs_mul, abs_of_pos hL]
    rw [this]; linarith
  · have : rho (L * Dd a b t) = rho (L * (t - b)) := by
      rw [Dd, h, ← rho_abs (L * (t - b)), abs_mul, abs_of_pos hL]
    rw [this]; linarith

lemma rho_le_of_le {L x y : ℝ} (hL : 0 < L) (hxy : x ≤ |y|) (hx : 0 ≤ x) :
    rho (L * y) ≤ rho (L * x) := by
  apply rho_anti
  rw [abs_mul, abs_mul, abs_of_pos hL, abs_of_nonneg hx]
  exact mul_le_mul_of_nonneg_left hxy hL.le

lemma pow8_bound_A {r1 r2 R d : ℝ} (h1 : 0 ≤ r1) (h1' : r1 ≤ 1) (h2 : 0 ≤ r2) (h2' : r2 ≤ 1)
    (hR : r1 * r2 ≤ R) (hd : r1 ≤ d) : r1 ^ 8 * r2 ^ 8 ≤ d ^ 3 * R ^ 3 * r2 ^ 2 := by
  have hc : r1 ^ 2 * r2 ^ 3 ≤ 1 :=
    mul_le_one₀ (pow_le_one₀ h1 h1') (pow_nonneg h2 3) (pow_le_one₀ h2 h2')
  have hr12 : 0 ≤ r1 * r2 := mul_nonneg h1 h2
  have a1 : r1 ^ 3 ≤ d ^ 3 := pow_le_pow_left₀ h1 hd 3
  have a2 : (r1 * r2) ^ 3 ≤ R ^ 3 := pow_le_pow_left₀ hr12 hR 3
  have X0 : 0 ≤ r1 ^ 3 * (r1 * r2) ^ 3 * r2 ^ 2 :=
    mul_nonneg (mul_nonneg (pow_nonneg h1 3) (pow_nonneg hr12 3)) (pow_nonneg h2 2)
  calc r1 ^ 8 * r2 ^ 8 = (r1 ^ 3 * (r1 * r2) ^ 3 * r2 ^ 2) * (r1 ^ 2 * r2 ^ 3) := by ring
    _ ≤ (r1 ^ 3 * (r1 * r2) ^ 3 * r2 ^ 2) * 1 := mul_le_mul_of_nonneg_left hc X0
    _ = r1 ^ 3 * (r1 * r2) ^ 3 * r2 ^ 2 := mul_one _
    _ ≤ d ^ 3 * R ^ 3 * r2 ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul a1 a2 (pow_nonneg hr12 3)
          (le_trans (pow_nonneg h1 3) a1)) (pow_nonneg h2 2)

lemma pow8_bound_B {r1 r2 R d : ℝ} (h1 : 0 ≤ r1) (h1' : r1 ≤ 1) (h2 : 0 ≤ r2)
    (hR : r1 * r2 ≤ R) (hd : R ≤ d) : r1 ^ 8 * r2 ^ 8 ≤ d ^ 3 * R ^ 3 * r2 ^ 2 := by
  have hr12 : 0 ≤ r1 * r2 := mul_nonneg h1 h2
  have hR0 : 0 ≤ R := le_trans hr12 hR
  have hc : r1 ^ 2 ≤ 1 := pow_le_one₀ h1 h1'
  have a1 : (r1 * r2) ^ 6 ≤ R ^ 6 := pow_le_pow_left₀ hr12 hR 6
  have a2 : R ^ 3 ≤ d ^ 3 := pow_le_pow_left₀ hR0 hd 3
  have X0 : 0 ≤ (r1 * r2) ^ 6 * r2 ^ 2 := mul_nonneg (pow_nonneg hr12 6) (pow_nonneg h2 2)
  calc r1 ^ 8 * r2 ^ 8 = ((r1 * r2) ^ 6 * r2 ^ 2) * r1 ^ 2 := by ring
    _ ≤ ((r1 * r2) ^ 6 * r2 ^ 2) * 1 := mul_le_mul_of_nonneg_left hc X0
    _ = (r1 * r2) ^ 6 * r2 ^ 2 := mul_one _
    _ ≤ R ^ 6 * r2 ^ 2 := mul_le_mul_of_nonneg_right a1 (pow_nonneg h2 2)
    _ = R ^ 3 * R ^ 3 * r2 ^ 2 := by ring
    _ ≤ d ^ 3 * R ^ 3 * r2 ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right a2 (pow_nonneg hR0 3))
          (pow_nonneg h2 2)

lemma f_bound {CU : ℝ} (hCU : ∀ y, ‖U P y‖ ≤ CU * rho y ^ 8) {Q : ℝ}
    (hQ : 1 < Q) (τ₀ t t' : ℝ) (k : ℤ) (d : ℝ)
    (hd : rho (P.L Q * (t - tau P Q τ₀ k)) ≤ d ∨ rho (P.L Q * (t - t')) ≤ d) :
    |pr P Q τ₀ k t * pr P Q τ₀ k t'| ≤
      CU ^ 2 * P.L Q ^ 2 * (d ^ 3 * rho (P.L Q * (t - t')) ^ 3 *
        rho (P.L Q * (t' - tau P Q τ₀ k)) ^ 2) := by
  have hL := P.L_pos hQ
  set r1 := rho (P.L Q * (t - tau P Q τ₀ k))
  set r2 := rho (P.L Q * (t' - tau P Q τ₀ k))
  set R := rho (P.L Q * (t - t'))
  have hR : r1 * r2 ≤ R := by
    have := rho_mul_le (P.L Q * (t - tau P Q τ₀ k)) (P.L Q * (t' - tau P Q τ₀ k))
    rwa [show P.L Q * (t - tau P Q τ₀ k) - P.L Q * (t' - tau P Q τ₀ k) = P.L Q * (t - t') by
      ring] at this
  have hb : r1 ^ 8 * r2 ^ 8 ≤ d ^ 3 * R ^ 3 * r2 ^ 2 := by
    rcases hd with hd | hd
    · exact pow8_bound_A (rho_nonneg _) (rho_le_one _) (rho_nonneg _) (rho_le_one _) hR hd
    · exact pow8_bound_B (rho_nonneg _) (rho_le_one _) (rho_nonneg _) hR hd
  have h1 := pr_bound P hCU hQ τ₀ k t
  have h2 := pr_bound P hCU hQ τ₀ k t'
  rw [abs_mul]
  calc |pr P Q τ₀ k t| * |pr P Q τ₀ k t'| ≤ (CU * P.L Q * r1 ^ 8) * (CU * P.L Q * r2 ^ 8) :=
        mul_le_mul h1 h2 (abs_nonneg _) (le_trans (abs_nonneg _) h1)
    _ = CU ^ 2 * P.L Q ^ 2 * (r1 ^ 8 * r2 ^ 8) := by ring
    _ ≤ CU ^ 2 * P.L Q ^ 2 * (d ^ 3 * R ^ 3 * r2 ^ 2) :=
        mul_le_mul_of_nonneg_left hb (by positivity)

lemma lattice_tau {Q : ℝ} (hQ : 1 < Q) (τ₀ t' : ℝ) :
    Summable (fun k : ℤ => rho (P.L Q * (t' - tau P Q τ₀ k)) ^ 2) ∧
      ∑' k : ℤ, rho (P.L Q * (t' - tau P Q τ₀ k)) ^ 2 ≤ Clat := by
  have hL := P.L_pos hQ
  have e : ∀ k : ℤ, P.L Q * (t' - tau P Q τ₀ k) = P.L Q * (t' - τ₀) - 2 * Real.pi * k := by
    intro k; unfold tau; field_simp; ring
  simp_rw [e]
  exact lattice _

/-- `K_d(t,t') = ∑_{k∈K_J} p_k(t) p_k(t')`. -/
def Kd (Q T τ₀ t t' : ℝ) : ℝ := ∑ k ∈ P.KJ Q T τ₀, pr P Q τ₀ k t * pr P Q τ₀ k t'

/-- `1_J`. -/
def jI (T t : ℝ) : ℝ := (P.J T).indicator (fun _ => (1 : ℝ)) t

/-- `E(t,t') = K_d(t,t')² − L² Φ(t−t')² 1_J(t) 1_J(t')`. -/
def Ek (Q T τ₀ t t' : ℝ) : ℝ :=
  Kd P Q T τ₀ t t' ^ 2 - P.L Q ^ 2 * PhiSq P Q (t - t') * jI P T t * jI P T t'

lemma jI_of_mem {T t : ℝ} (h : t ∈ P.J T) : jI P T t = 1 := by simp [jI, h]

lemma jI_of_not_mem {T t : ℝ} (h : t ∉ P.J T) : jI P T t = 0 := by simp [jI, h]

lemma Kd_abs_le {Q : ℝ} (hQ : 1 < Q) (T τ₀ t t' : ℝ) :
    |Kd P Q T τ₀ t t'| ≤ P.aInt * P.L Q ^ 2 := by
  unfold Kd
  have h1 := sum_sq_le P hQ τ₀ t (P.KJ Q T τ₀)
  have h2 := sum_sq_le P hQ τ₀ t' (P.KJ Q T τ₀)
  calc |∑ k ∈ P.KJ Q T τ₀, pr P Q τ₀ k t * pr P Q τ₀ k t'|
      ≤ ∑ k ∈ P.KJ Q T τ₀, |pr P Q τ₀ k t * pr P Q τ₀ k t'| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ P.KJ Q T τ₀, (pr P Q τ₀ k t ^ 2 + pr P Q τ₀ k t' ^ 2) / 2 := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul]
        nlinarith [sq_nonneg (|pr P Q τ₀ k t| - |pr P Q τ₀ k t'|), sq_abs (pr P Q τ₀ k t),
          sq_abs (pr P Q τ₀ k t')]
    _ = (∑ k ∈ P.KJ Q T τ₀, pr P Q τ₀ k t ^ 2 + ∑ k ∈ P.KJ Q T τ₀, pr P Q τ₀ k t' ^ 2) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
    _ ≤ P.aInt * P.L Q ^ 2 := by linarith

/-- The kernel bound. -/
theorem Ek_bound {CU : ℝ} (hCU : ∀ y, ‖U P y‖ ≤ CU * rho y ^ 8) {Q : ℝ}
    (hQ : 1 < Q) (T τ₀ t t' : ℝ) :
    |Ek P Q T τ₀ t t'| ≤ 2 * P.aInt * CU ^ 2 * Clat * P.L Q ^ 4 *
      rho (P.L Q * Dd ((1 + P.θ) * T) ((2 - P.θ) * T) t) ^ 3 * rho (P.L Q * (t - t')) ^ 3 := by
  have hL := P.L_pos hQ
  have ha := aInt_pos' P
  set K := P.KJ Q T τ₀
  set d := rho (P.L Q * Dd ((1 + P.θ) * T) ((2 - P.θ) * T) t)
  set R := rho (P.L Q * (t - t'))
  set f : ℤ → ℝ := fun k => pr P Q τ₀ k t * pr P Q τ₀ k t' with hf
  set B : ℤ → ℝ := fun k => CU ^ 2 * P.L Q ^ 2 * (d ^ 3 * R ^ 3 *
    rho (P.L Q * (t' - tau P Q τ₀ k)) ^ 2) with hB
  obtain ⟨hs2, hlat⟩ := lattice_tau P hQ τ₀ t'
  have hB0 : ∀ k, 0 ≤ B k := fun k => by
    have := rho_nonneg (P.L Q * (t' - tau P Q τ₀ k))
    have := rho_nonneg (P.L Q * (t - t'))
    have := rho_nonneg (P.L Q * Dd ((1 + P.θ) * T) ((2 - P.θ) * T) t)
    positivity
  have hd0 : 0 ≤ d := rho_nonneg _
  have hR0 : 0 ≤ R := rho_nonneg _
  have hBs : Summable B := by
    have := hs2.mul_left (CU ^ 2 * P.L Q ^ 2 * (d ^ 3 * R ^ 3))
    refine this.congr fun k => ?_
    simp only [hB]; ring
  have hBsum : ∑' k, B k ≤ CU ^ 2 * P.L Q ^ 2 * (d ^ 3 * R ^ 3) * Clat := by
    have e : ∑' k, B k = CU ^ 2 * P.L Q ^ 2 * (d ^ 3 * R ^ 3) *
        ∑' k : ℤ, rho (P.L Q * (t' - tau P Q τ₀ k)) ^ 2 := by
      rw [← tsum_mul_left]; congr 1; funext k; simp only [hB]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hlat (by positivity)
  have hKd := Kd_abs_le P hQ T τ₀ t t'
  -- the bound off `J × J`
  have off : (∀ k ∈ K, |f k| ≤ B k) → Kd P Q T τ₀ t t' ^ 2 ≤
      P.aInt * P.L Q ^ 2 * (CU ^ 2 * P.L Q ^ 2 * (d ^ 3 * R ^ 3) * Clat) := by
    intro hk
    have h1 : |Kd P Q T τ₀ t t'| ≤ ∑' k, B k := by
      unfold Kd
      calc |∑ k ∈ K, f k| ≤ ∑ k ∈ K, |f k| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ K, B k := Finset.sum_le_sum hk
        _ ≤ ∑' k, B k := hBs.sum_le_tsum K (fun k _ => hB0 k)
    rw [← sq_abs]
    calc |Kd P Q T τ₀ t t'| ^ 2 = |Kd P Q T τ₀ t t'| * |Kd P Q T τ₀ t t'| := sq _
      _ ≤ (P.aInt * P.L Q ^ 2) * (CU ^ 2 * P.L Q ^ 2 * (d ^ 3 * R ^ 3) * Clat) :=
          mul_le_mul hKd (h1.trans hBsum) (abs_nonneg _) (by positivity)
  have hC0 : 0 ≤ CU ^ 2 * P.L Q ^ 2 * (d ^ 3 * R ^ 3) * Clat :=
    mul_nonneg (by positivity) Clat_nonneg
  have final : P.aInt * P.L Q ^ 2 * (CU ^ 2 * P.L Q ^ 2 * (d ^ 3 * R ^ 3) * Clat) ≤
      2 * P.aInt * CU ^ 2 * Clat * P.L Q ^ 4 * d ^ 3 * R ^ 3 := by
    have : 0 ≤ P.aInt * P.L Q ^ 2 * (CU ^ 2 * P.L Q ^ 2 * (d ^ 3 * R ^ 3) * Clat) :=
      mul_nonneg (by positivity) hC0
    nlinarith
  by_cases ht : t ∈ P.J T
  · by_cases ht' : t' ∈ P.J T
    · -- both in `J`: tail of the Poisson–Gabor sum
      have hE : Ek P Q T τ₀ t t' = (Kd P Q T τ₀ t t' - P.L Q * (P.Φ Q (t - t')).re) *
          (Kd P Q T τ₀ t t' + P.L Q * (P.Φ Q (t - t')).re) := by
        unfold Ek; rw [jI_of_mem P ht, jI_of_mem P ht', PhiSq_eq]; ring
      have hPG := PG P hQ τ₀ t t'
      set S := P.L Q * (P.Φ Q (t - t')).re
      have hfin : HasSum (fun k => if k ∈ K then f k else 0) (Kd P Q T τ₀ t t') := by
        have : HasSum (fun k => if k ∈ K then f k else 0)
            (∑ k ∈ K, (if k ∈ K then f k else 0)) :=
          hasSum_sum_of_ne_finset_zero (fun k hk => if_neg hk)
        convert this using 1
        unfold Kd
        exact Finset.sum_congr rfl fun k hk => (if_pos hk).symm
      have htail : HasSum (fun k => if k ∈ K then 0 else f k) (S - Kd P Q T τ₀ t t') :=
        (hPG.sub hfin).congr_fun fun k => by split_ifs <;> simp [hf]
      have hgB : ∀ k, |(if k ∈ K then 0 else f k)| ≤ B k := by
        intro k
        split_ifs with hk
        · simpa using hB0 k
        · have hτ : tau P Q τ₀ k ∉ P.J T := fun h => hk ((mem_KJ_iff P hQ T τ₀ k).mpr h)
          have hD := Dd_le_of_mem_not_mem ht hτ
          exact f_bound P hCU hQ τ₀ t t' k d
            (Or.inl (rho_le_of_le hL hD (Dd_nonneg _ _ _)))
      have hup : S - Kd P Q T τ₀ t t' ≤ ∑' k, B k :=
        hasSum_le (fun k => (abs_le.mp (hgB k)).2) htail hBs.hasSum
      have hlo : -∑' k, B k ≤ S - Kd P Q T τ₀ t t' := by
        have := hasSum_le (fun k => (abs_le.mp (hgB k)).1) hBs.hasSum.neg htail
        simpa using this
      have h1 : |Kd P Q T τ₀ t t' - S| ≤ CU ^ 2 * P.L Q ^ 2 * (d ^ 3 * R ^ 3) * Clat := by
        rw [abs_sub_comm]; exact (abs_le.mpr ⟨hlo, hup⟩).trans hBsum
      have h2 : |Kd P Q T τ₀ t t' + S| ≤ 2 * (P.aInt * P.L Q ^ 2) :=
        (abs_add_le _ _).trans (by linarith [abs_LΦ_le P hQ (t - t')])
      rw [hE, abs_mul]
      calc |Kd P Q T τ₀ t t' - S| * |Kd P Q T τ₀ t t' + S|
          ≤ (CU ^ 2 * P.L Q ^ 2 * (d ^ 3 * R ^ 3) * Clat) * (2 * (P.aInt * P.L Q ^ 2)) :=
            mul_le_mul h1 h2 (abs_nonneg _) hC0
        _ = 2 * P.aInt * CU ^ 2 * Clat * P.L Q ^ 4 * d ^ 3 * R ^ 3 := by ring
    · -- `t ∈ J`, `t' ∉ J`
      have hE : Ek P Q T τ₀ t t' = Kd P Q T τ₀ t t' ^ 2 := by
        unfold Ek; rw [jI_of_not_mem P ht']; ring
      have hD := Dd_le_of_mem_not_mem ht ht'
      rw [hE, abs_of_nonneg (sq_nonneg _)]
      refine le_trans (off fun k _ => ?_) final
      exact f_bound P hCU hQ τ₀ t t' k d
        (Or.inr (rho_le_of_le hL hD (Dd_nonneg _ _ _)))
  · -- `t ∉ J`
    have hE : Ek P Q T τ₀ t t' = Kd P Q T τ₀ t t' ^ 2 := by
      unfold Ek; rw [jI_of_not_mem P ht]; ring
    rw [hE, abs_of_nonneg (sq_nonneg _)]
    refine le_trans (off fun k hk => ?_) final
    have hτ : tau P Q τ₀ k ∈ P.J T := (mem_KJ_iff P hQ T τ₀ k).mp hk
    have hD := Dd_le_of_not_mem_mem ht hτ
    exact f_bound P hCU hQ τ₀ t t' k d (Or.inl (rho_le_of_le hL hD (Dd_nonneg _ _ _)))

end Kernel

/-! ### Family sums -/

section FamSum

variable (W : Weight) (Q : ℝ)

lemma famSum_add (f g : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) :
    famSum W Q (fun q χ => f q χ + g q χ) = famSum W Q f + famSum W Q g := by
  unfold famSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_add_distrib, mul_add]

lemma famSum_sub (f g : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) :
    famSum W Q (fun q χ => f q χ - g q χ) = famSum W Q f - famSum W Q g := by
  unfold famSum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_sub_distrib, mul_sub]

lemma famSum_mul_left (c : ℝ) (f : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) :
    famSum W Q (fun q χ => c * f q χ) = c * famSum W Q f := by
  unfold famSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← Finset.mul_sum]; ring

lemma famSum_mono {f g : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ}
    (h : ∀ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∀ χ, f q χ ≤ g q χ) : famSum W Q f ≤ famSum W Q g := by
  unfold famSum
  refine Finset.sum_le_sum fun q hq => ?_
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun χ _ => h q hq χ) (W.omega_nonneg Q q)

lemma famSum_const (c : ℝ) : famSum W Q (fun _ _ => c) = c * W.H Q := by
  unfold famSum Weight.H phiStar
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul]; ring

lemma famSum_integrable {f : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ → ℝ}
    (hf : ∀ q χ, Integrable (f q χ)) : Integrable (fun t => famSum W Q (fun q χ => f q χ t)) := by
  unfold famSum
  exact integrable_finsetSum _ fun q _ =>
    (integrable_finsetSum _ fun χ _ => hf q χ).const_mul _

lemma famSum_integral {f : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ → ℝ}
    (hf : ∀ q χ, Integrable (f q χ)) :
    famSum W Q (fun q χ => ∫ t, f q χ t) = ∫ t, famSum W Q (fun q χ => f q χ t) := by
  unfold famSum
  rw [integral_finsetSum _ fun q _ => (integrable_finsetSum _ fun χ _ => hf q χ).const_mul _]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [integral_const_mul, integral_finsetSum _ fun χ _ => hf q χ]

end FamSum

/-! ### Pointwise bounds for `ν_χ` -/

section Nu

lemma log_sq_le {x : ℝ} (hx : 1 ≤ x) : Real.log x ^ 2 ≤ 4 * x := by
  have hx0 : 0 < x := by linarith
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx0)
  rw [Real.log_sqrt hx0.le] at h
  have h0 := Real.log_nonneg hx
  have hs := Real.sq_sqrt hx0.le
  have hs0 := Real.sqrt_nonneg x
  nlinarith

lemma log_le_self_add {x : ℝ} (hx : 0 < x) : Real.log x ≤ x := by
  have := Real.log_le_sub_one_of_pos hx; linarith

lemma abs_log_div_pi_le {Q : ℝ} {q : ℕ} (hq1 : 1 ≤ q) (hqQ : (q : ℝ) ≤ Q) :
    |Real.log (q / Real.pi)| ≤ Real.log Q + 3 := by
  have hq : (0 : ℝ) < q := by exact_mod_cast hq1
  rw [Real.log_div hq.ne' Real.pi_pos.ne']
  have h1 : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq1)
  have h2 : Real.log q ≤ Real.log Q := Real.log_le_log hq hqQ
  have h3 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have h4 : Real.log Real.pi ≤ 3 := by
    have := Real.log_le_sub_one_of_pos Real.pi_pos; linarith [Real.pi_lt_four]
  rw [abs_le]; constructor <;> linarith

lemma norm_Schi_le (P : PrimeSetup) (Q : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) :
    ‖P.Schi χ Q (P.aVec Q) t‖ ≤ ∑ n ∈ P.range Q, P.aVec Q n := by
  unfold PrimeSetup.Schi
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  rw [norm_mul, norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (aVec_nonneg P Q n)]
  simp only [Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.ofReal_re, zero_mul,
    Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero, neg_zero, Real.rpow_zero, mul_one]
  exact mul_le_of_le_one_right (aVec_nonneg P Q n) (DirichletCharacter.norm_le_one χ n)

lemma PChi_sq_le (P : PrimeSetup) (Q : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) :
    PChi P Q χ t ^ 2 ≤ ‖P.Schi χ Q (P.aVec Q) t‖ ^ 2 := by
  unfold PChi
  have h1 := Complex.abs_re_le_norm (P.Schi χ Q (P.aVec Q) t)
  have hpi : 1 / Real.pi ≤ 1 := by rw [div_le_one Real.pi_pos]; linarith [Real.pi_gt_three]
  have hpi0 : 0 ≤ 1 / Real.pi := by positivity
  rw [neg_mul, neg_sq, mul_pow, ← sq_abs (P.Schi χ Q (P.aVec Q) t).re]
  have h2 : |(P.Schi χ Q (P.aVec Q) t).re| ^ 2 ≤ ‖P.Schi χ Q (P.aVec Q) t‖ ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h3 : (1 / Real.pi) ^ 2 ≤ 1 := pow_le_one₀ hpi0 hpi
  nlinarith [sq_nonneg |(P.Schi χ Q (P.aVec Q) t).re|]

/-- Growth of `ν_χ`: `|ν_χ(t)| ≤ α + β|t|`. -/
lemma nu_growth (hStir : StirlingDigamma) (P : PrimeSetup) (Q : ℝ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) : ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧
      ∀ t, |nuChi P Q χ t| ≤ α + β * |t| := by
  obtain ⟨C, hC0, hC⟩ := muChi_abs_le hStir
  set Sa := ∑ n ∈ P.range Q, P.aVec Q n
  have hSa : 0 ≤ Sa := Finset.sum_nonneg fun n _ => aVec_nonneg P Q n
  refine ⟨|Real.log (q / Real.pi)| + 2 * C + Sa, C, by positivity, hC0, fun t => ?_⟩
  unfold nuChi
  have h1 := hC q χ t
  have hlog : Real.log (|t| + 2) ≤ |t| + 2 := log_le_self_add (by positivity)
  have hlog0 : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hpi : 1 / (2 * Real.pi) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [Real.pi_gt_three]
  have hm : |muChi χ t| ≤ |Real.log (q / Real.pi)| + C * (|t| + 2) := by
    refine h1.trans ?_
    have hb : 0 ≤ |Real.log (q / Real.pi)| + C * Real.log (|t| + 2) := by positivity
    calc 1 / (2 * Real.pi) * (|Real.log (q / Real.pi)| + C * Real.log (|t| + 2))
        ≤ 1 * (|Real.log (q / Real.pi)| + C * Real.log (|t| + 2)) :=
          mul_le_mul_of_nonneg_right hpi hb
      _ ≤ |Real.log (q / Real.pi)| + C * (|t| + 2) := by
          rw [one_mul]; nlinarith
  have hp : |PChi P Q χ t| ≤ Sa := by
    have h2 := norm_Schi_le P Q χ t
    have h3 := sq_le_sq.mp (PChi_sq_le P Q χ t)
    rw [abs_norm] at h3
    exact h3.trans h2
  calc |muChi χ t + PChi P Q χ t| ≤ |muChi χ t| + |PChi P Q χ t| := abs_add_le _ _
    _ ≤ |Real.log (q / Real.pi)| + C * (|t| + 2) + Sa := add_le_add hm hp
    _ = |Real.log (q / Real.pi)| + 2 * C + Sa + C * |t| := by ring

/-- **Family bound**: `∑_χ ω_χ ν_χ(t)² ≤ H (4(ℓ+3)² + A₁ + A₂ L³ + B₀|t|)` for large `Q`. -/
theorem famSum_nu_sq (hMV : MV_LargeSieve) (hStir : StirlingDigamma) (hWH : lemWH_Statement)
    (P : PrimeSetup) (W : Weight) :
    ∃ A₁ A₂ B₀ Q₁ : ℝ, 0 ≤ A₁ ∧ 0 ≤ A₂ ∧ 0 ≤ B₀ ∧ 1 ≤ Q₁ ∧ ∀ Q : ℝ, Q₁ ≤ Q → ∀ t : ℝ,
      famSum W Q (fun _ χ => nuChi P Q χ t ^ 2) ≤
        W.H Q * (4 * (Real.log Q + 3) ^ 2 + A₁ + A₂ * P.L Q ^ 3 + B₀ * |t|) := by
  obtain ⟨C, hC0, hC⟩ := muChi_abs_le hStir
  obtain ⟨C₀, hC₀0, hLS⟩ := famLS_omega hMV
  obtain ⟨Ca, Qa, hCa0, hCa⟩ := sum_aVec_sq_le P
  obtain ⟨cH, QH, hcH, hH⟩ := H_lower hWH W
  refine ⟨32 * C ^ 2, 4 * |W.wmax| * C₀ * Ca / cH, 16 * C ^ 2, max 1 (max Qa QH),
    by positivity, by positivity, by positivity, le_max_left _ _, fun Q hQ t => ?_⟩
  have hQ1 : 1 ≤ Q := le_trans (le_max_left _ _) hQ
  have hQa : Qa ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hQ
  have hQH : QH ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hQ
  have hL0 : 0 ≤ P.L Q := mul_nonneg P.lam_pos.le (Real.log_nonneg hQ1)
  have hH0 := W.H_nonneg Q
  set ℓ := Real.log Q
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg hQ1
  -- per-character bound
  have hpt : ∀ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∀ χ : DirichletCharacter ℂ q,
      nuChi P Q χ t ^ 2 ≤ (4 * (ℓ + 3) ^ 2 + 32 * C ^ 2 + 16 * C ^ 2 * |t|) +
        2 * ‖P.Schi χ Q (P.aVec Q) t‖ ^ 2 := by
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
    have hp2 := PChi_sq_le P Q χ t
    unfold nuChi
    nlinarith [sq_nonneg (muChi χ t - PChi P Q χ t)]
  have hsum := famSum_mono W Q (f := fun _ χ => nuChi P Q χ t ^ 2)
    (g := fun _ χ => (4 * (ℓ + 3) ^ 2 + 32 * C ^ 2 + 16 * C ^ 2 * |t|) +
      2 * ‖P.Schi χ Q (P.aVec Q) t‖ ^ 2) hpt
  rw [famSum_add, famSum_const, famSum_mul_left] at hsum
  -- the large sieve
  set x : ℕ → ℂ := fun n => (P.aVec Q n : ℂ) * (n : ℂ) ^ (-(Complex.I * t)) with hx
  have hLSx := hLS P W Q hQ1 x
  have hS : famSum W Q (fun _ χ => ‖P.Schi χ Q (P.aVec Q) t‖ ^ 2) =
      ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q *
        ∑ χ ∈ primChars q, ‖∑ n ∈ P.range Q, x n * χ n‖ ^ 2 := by
    unfold famSum PrimeSetup.Schi
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun χ _ => ?_
    refine congrArg (fun z : ℂ => ‖z‖ ^ 2) (Finset.sum_congr rfl fun n _ => ?_)
    simp only [hx]; ring
  have hxn : ∑ n ∈ P.range Q, ‖x n‖ ^ 2 = ∑ n ∈ P.range Q, P.aVec Q n ^ 2 := by
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    simp only [hx]
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), Complex.norm_real,
      Real.norm_eq_abs]
    simp
  rw [hxn] at hLSx
  have hY := Families.Phase3.C.Y_le_sq P hQ1
  have hA := hCa Q hQa
  have hHQ := hH Q hQH
  have hsa0 : 0 ≤ ∑ n ∈ P.range Q, P.aVec Q n ^ 2 := Finset.sum_nonneg fun n _ => sq_nonneg _
  have hQ2 : Q ^ 2 ≤ W.H Q / cH := by rw [le_div_iff₀ hcH]; linarith
  have hLS' : famSum W Q (fun _ χ => ‖P.Schi χ Q (P.aVec Q) t‖ ^ 2) ≤
      |W.wmax| * C₀ * (2 * (W.H Q / cH)) * (Ca * P.L Q ^ 3) := by
    rw [hS]
    refine hLSx.trans ?_
    have e1 : W.wmax * C₀ * (Q ^ 2 + P.Y Q) ≤ |W.wmax| * C₀ * (2 * (W.H Q / cH)) := by
      have : 0 ≤ Q ^ 2 + P.Y Q := by have := (Families.Phase3.C.Y_pos' P Q).le; positivity
      calc W.wmax * C₀ * (Q ^ 2 + P.Y Q) ≤ |W.wmax| * C₀ * (Q ^ 2 + P.Y Q) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hC₀0) this
        _ ≤ |W.wmax| * C₀ * (2 * (W.H Q / cH)) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    calc W.wmax * C₀ * (Q ^ 2 + P.Y Q) * ∑ n ∈ P.range Q, P.aVec Q n ^ 2
        ≤ |W.wmax| * C₀ * (2 * (W.H Q / cH)) * ∑ n ∈ P.range Q, P.aVec Q n ^ 2 :=
          mul_le_mul_of_nonneg_right e1 hsa0
      _ ≤ |W.wmax| * C₀ * (2 * (W.H Q / cH)) * (Ca * P.L Q ^ 3) :=
          mul_le_mul_of_nonneg_left hA (by positivity)
  set X := |W.wmax| * C₀ * (2 * (W.H Q / cH)) * (Ca * P.L Q ^ 3) with hXdef
  have e2 : 2 * X = W.H Q * (4 * |W.wmax| * C₀ * Ca / cH * P.L Q ^ 3) := by
    rw [hXdef]; field_simp; ring
  calc famSum W Q (fun _ χ => nuChi P Q χ t ^ 2)
      ≤ (4 * (ℓ + 3) ^ 2 + 32 * C ^ 2 + 16 * C ^ 2 * |t|) * W.H Q +
        2 * famSum W Q (fun _ χ => ‖P.Schi χ Q (P.aVec Q) t‖ ^ 2) := hsum
    _ ≤ (4 * (ℓ + 3) ^ 2 + 32 * C ^ 2 + 16 * C ^ 2 * |t|) * W.H Q + 2 * X := by linarith
    _ = W.H Q * (4 * (ℓ + 3) ^ 2 + 32 * C ^ 2 + 4 * |W.wmax| * C₀ * Ca / cH * P.L Q ^ 3 +
          16 * C ^ 2 * |t|) := by rw [e2]; ring

end Nu

/-! ### Per character: Fubini and the comparison identity -/

section PerChi

variable (P : PrimeSetup)

lemma abs_mul3_le {a b c A B C : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C) :
    |a * b * c| ≤ A * B * C := by
  rw [abs_mul, abs_mul]
  exact mul_le_mul (mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)) hc (abs_nonneg _)
    (mul_nonneg ((abs_nonneg _).trans ha) ((abs_nonneg _).trans hb))

lemma nu_continuous (Q : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) : Continuous (nuChi P Q χ) :=
  (muChi_continuous χ).add (PChi_continuous P Q χ)

/-- `f_{kl}(t) = p_k(t) p_l(t) ν(t)` is integrable. -/
lemma integrable_f (hStir : StirlingDigamma) {Q : ℝ} (hQ : 1 < Q) (τ₀ : ℝ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (k l : ℤ) :
    Integrable (fun t => pr P Q τ₀ k t * pr P Q τ₀ l t * nuChi P Q χ t) := by
  have hL := P.L_pos hQ
  obtain ⟨CU, hCU0, hCU⟩ := U_bound P
  obtain ⟨α, β, hα, hβ, hν⟩ := nu_growth hStir P Q χ
  set c := tau P Q τ₀ l
  set g : ℝ → ℝ := fun t => (CU * P.L Q) * (CU * P.L Q) *
    ((α + β * |c|) * rho (P.L Q * (t - c)) ^ 3 + β * (rho (P.L Q * (t - c)) ^ 3 * |t - c|))
    with hg_def
  have hg : Integrable g :=
    (((integrable_rho3_sc hL c).const_mul (α + β * |c|)).add
      ((integrable_rho3_abs_sc hL c).const_mul β)).const_mul _
  refine hg.mono' ((((pr_continuous P Q τ₀ k).mul (pr_continuous P Q τ₀ l)).mul
    (nu_continuous P Q χ)).aestronglyMeasurable) (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs]
  have r0 := rho_nonneg (P.L Q * (t - c))
  have r1 := rho_le_one (P.L Q * (t - c))
  have h1 : |pr P Q τ₀ k t| ≤ CU * P.L Q := by
    have := pr_bound P hCU hQ τ₀ k t
    have h8 : rho (P.L Q * (t - tau P Q τ₀ k)) ^ 8 ≤ 1 :=
      pow_le_one₀ (rho_nonneg _) (rho_le_one _)
    calc _ ≤ _ := this
      _ ≤ CU * P.L Q * 1 := mul_le_mul_of_nonneg_left h8 (by positivity)
      _ = _ := mul_one _
  have h2 : |pr P Q τ₀ l t| ≤ CU * P.L Q * rho (P.L Q * (t - c)) ^ 3 := by
    have := pr_bound P hCU hQ τ₀ l t
    have h83 : rho (P.L Q * (t - c)) ^ 8 ≤ rho (P.L Q * (t - c)) ^ 3 :=
      pow_le_pow_of_le_one r0 r1 (by norm_num)
    exact this.trans (mul_le_mul_of_nonneg_left h83 (by positivity))
  have h3 : |nuChi P Q χ t| ≤ (α + β * |c|) + β * |t - c| := by
    have h := hν t
    have : |t| ≤ |c| + |t - c| := by have := abs_sub_abs_le_abs_sub t c; linarith
    nlinarith
  calc |pr P Q τ₀ k t * pr P Q τ₀ l t * nuChi P Q χ t|
      ≤ (CU * P.L Q) * (CU * P.L Q * rho (P.L Q * (t - c)) ^ 3) *
          ((α + β * |c|) + β * |t - c|) := abs_mul3_le h1 h2 h3
    _ = g t := by simp only [hg_def]; ring

/-- `K_d(t,t')² ν(t) ν(t') = ∑_{k,l} f_{kl}(t) f_{kl}(t')`. -/
lemma Kd_sq_expand (Q T τ₀ : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t t' : ℝ) :
    Kd P Q T τ₀ t t' ^ 2 * nuChi P Q χ t * nuChi P Q χ t' =
      ∑ k ∈ P.KJ Q T τ₀, ∑ l ∈ P.KJ Q T τ₀,
        (pr P Q τ₀ k t * pr P Q τ₀ l t * nuChi P Q χ t) *
          (pr P Q τ₀ k t' * pr P Q τ₀ l t' * nuChi P Q χ t') := by
  unfold Kd
  rw [sq, Finset.sum_mul_sum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

lemma J_meas (T : ℝ) : MeasurableSet (P.J T) := by unfold PrimeSetup.J; exact measurableSet_Icc

lemma integral_jI (T : ℝ) (h : ℝ → ℝ) : ∫ t, jI P T t * h t = ∫ t in P.J T, h t := by
  rw [← integral_indicator (J_meas P T)]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  by_cases ht : t ∈ P.J T <;> simp [jI, ht]

lemma integrable_jI (T : ℝ) {h : ℝ → ℝ} (hh : Continuous h) :
    Integrable (fun t => jI P T t * h t) := by
  have e : (fun t => jI P T t * h t) = (P.J T).indicator h := by
    funext t; by_cases ht : t ∈ P.J T <;> simp [jI, ht]
  rw [e, integrable_indicator_iff (J_meas P T)]
  unfold PrimeSetup.J
  exact hh.integrableOn_Icc

/-- `φ(t) = ∫_J Φ(t−t')² ν(t') dt'`. -/
def phiJ (Q T : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) : ℝ :=
  ∫ t' in P.J T, PhiSq P Q (t - t') * nuChi P Q χ t'

lemma phiJ_continuous {Q : ℝ} (hQ : 1 < Q) (T : ℝ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Continuous (phiJ P Q T χ) := by
  unfold phiJ
  have hc : Continuous (Function.uncurry fun t t' : ℝ => PhiSq P Q (t - t') * nuChi P Q χ t') :=
    ((PhiSq_continuous P hQ).comp (continuous_fst.sub continuous_snd)).mul
      ((nu_continuous P Q χ).comp continuous_snd)
  exact continuous_parametric_integral_of_continuous hc
    (by unfold PrimeSetup.J; exact isCompact_Icc)

/-- **Per character.** With `h_χ(t) = ∫ E(t,t') ν(t) ν(t') dt'`:
`∑_{k,l∈K} (∫ f_{kl})² − L² ∬_{J²} Φ(t−t')² ν ν = ∫ h_χ`, all integrands integrable. -/
theorem perChi (hStir : StirlingDigamma) {Q : ℝ} (hQ : 1 < Q) (T τ₀ : ℝ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    (∀ t, Integrable (fun t' => Ek P Q T τ₀ t t' * nuChi P Q χ t * nuChi P Q χ t')) ∧
    Integrable (fun t => ∫ t', Ek P Q T τ₀ t t' * nuChi P Q χ t * nuChi P Q χ t') ∧
    (∑ k ∈ P.KJ Q T τ₀, ∑ l ∈ P.KJ Q T τ₀,
        (∫ t, pr P Q τ₀ k t * pr P Q τ₀ l t * nuChi P Q χ t) ^ 2) -
      P.L Q ^ 2 * (∫ t in P.J T, ∫ t' in P.J T,
        PhiSq P Q (t - t') * nuChi P Q χ t * nuChi P Q χ t') =
      ∫ t, ∫ t', Ek P Q T τ₀ t t' * nuChi P Q χ t * nuChi P Q χ t' := by
  set K := P.KJ Q T τ₀
  set ν := nuChi P Q χ
  set f : ℤ → ℤ → ℝ → ℝ := fun k l t => pr P Q τ₀ k t * pr P Q τ₀ l t * ν t with hf
  have hfi : ∀ k l, Integrable (f k l) := fun k l => integrable_f P hStir hQ τ₀ χ k l
  -- the `K_d²` part
  set x : ℝ → ℝ := fun t => ∑ k ∈ K, ∑ l ∈ K, (∫ s, f k l s) * f k l t with hx
  have hxi : Integrable x :=
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => (hfi k l).const_mul _
  have hKdi : ∀ t, Integrable (fun t' => Kd P Q T τ₀ t t' ^ 2 * ν t * ν t') := by
    intro t
    have e : (fun t' => Kd P Q T τ₀ t t' ^ 2 * ν t * ν t') =
        fun t' => ∑ k ∈ K, ∑ l ∈ K, f k l t * f k l t' := by
      funext t'; exact Kd_sq_expand P Q T τ₀ χ t t'
    rw [e]
    exact integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => (hfi k l).const_mul _
  have hKd : ∀ t, ∫ t', Kd P Q T τ₀ t t' ^ 2 * ν t * ν t' = x t := by
    intro t
    have e : (fun t' => Kd P Q T τ₀ t t' ^ 2 * ν t * ν t') =
        fun t' => ∑ k ∈ K, ∑ l ∈ K, f k l t * f k l t' := by
      funext t'; exact Kd_sq_expand P Q T τ₀ χ t t'
    rw [e, integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => (hfi k l).const_mul _]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ fun l _ => (hfi k l).const_mul _]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul, mul_comm]
  have hxint : ∫ t, x t = ∑ k ∈ K, ∑ l ∈ K, (∫ t, f k l t) ^ 2 := by
    rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => (hfi k l).const_mul _]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ fun l _ => (hfi k l).const_mul _]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul, sq]
  -- the `Φ²` part
  set m : ℝ → ℝ := fun t => jI P T t * (P.L Q ^ 2 * ν t * phiJ P Q T χ t) with hm
  have hmi : Integrable m :=
    integrable_jI P T (((continuous_const.mul (nu_continuous P Q χ)).mul (phiJ_continuous P hQ T χ)))
  have hPhi_i : ∀ t, Integrable (fun t' =>
      P.L Q ^ 2 * PhiSq P Q (t - t') * jI P T t * jI P T t' * ν t * ν t') := by
    intro t
    have e : (fun t' => P.L Q ^ 2 * PhiSq P Q (t - t') * jI P T t * jI P T t' * ν t * ν t') =
        fun t' => (P.L Q ^ 2 * jI P T t * ν t) * (jI P T t' * (PhiSq P Q (t - t') * ν t')) := by
      funext t'; ring
    rw [e]
    exact (integrable_jI P T (((PhiSq_continuous P hQ).comp (continuous_const.sub continuous_id)).mul
      (nu_continuous P Q χ))).const_mul _
  have hPhi : ∀ t, ∫ t', P.L Q ^ 2 * PhiSq P Q (t - t') * jI P T t * jI P T t' * ν t * ν t' =
      m t := by
    intro t
    have e : (fun t' => P.L Q ^ 2 * PhiSq P Q (t - t') * jI P T t * jI P T t' * ν t * ν t') =
        fun t' => (P.L Q ^ 2 * jI P T t * ν t) * (jI P T t' * (PhiSq P Q (t - t') * ν t')) := by
      funext t'; ring
    rw [e, integral_const_mul, integral_jI]
    simp only [hm, phiJ]; ring
  have hmint : ∫ t, m t = P.L Q ^ 2 * (∫ t in P.J T, ∫ t' in P.J T,
      PhiSq P Q (t - t') * ν t * ν t') := by
    have e : (fun t => m t) = fun t => jI P T t * (P.L Q ^ 2 * (ν t * phiJ P Q T χ t)) := by
      funext t; simp only [hm]; ring
    rw [e, integral_jI, integral_const_mul]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [phiJ]
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t' => ?_)
    simp only; ring
  -- the difference
  have hEi : ∀ t, Integrable (fun t' => Ek P Q T τ₀ t t' * ν t * ν t') := by
    intro t
    have e : (fun t' => Ek P Q T τ₀ t t' * ν t * ν t') = fun t' =>
        Kd P Q T τ₀ t t' ^ 2 * ν t * ν t' -
          P.L Q ^ 2 * PhiSq P Q (t - t') * jI P T t * jI P T t' * ν t * ν t' := by
      funext t'; unfold Ek; ring
    rw [e]; exact (hKdi t).sub (hPhi_i t)
  have hE : ∀ t, ∫ t', Ek P Q T τ₀ t t' * ν t * ν t' = x t - m t := by
    intro t
    have e : (fun t' => Ek P Q T τ₀ t t' * ν t * ν t') = fun t' =>
        Kd P Q T τ₀ t t' ^ 2 * ν t * ν t' -
          P.L Q ^ 2 * PhiSq P Q (t - t') * jI P T t * jI P T t' * ν t * ν t' := by
      funext t'; unfold Ek; ring
    rw [e, integral_sub (hKdi t) (hPhi_i t), hKd, hPhi]
  have hfun : (fun t => ∫ t', Ek P Q T τ₀ t t' * ν t * ν t') = fun t => x t - m t := funext hE
  refine ⟨hEi, ?_, ?_⟩
  · rw [hfun]; exact hxi.sub hmi
  · rw [hfun, integral_sub hxi hmi, hxint, hmint]

end PerChi

/-! ### The error integral -/

section ErrorIntegral

lemma inner_integral {L : ℝ} (hL : 0 < L) (c α β : ℝ) :
    Integrable (fun s => α * rho (L * (s - c)) ^ 3 + β * (rho (L * (s - c)) ^ 3 * |s - c|)) ∧
    ∫ s, (α * rho (L * (s - c)) ^ 3 + β * (rho (L * (s - c)) ^ 3 * |s - c|)) =
      α * (I0 / L) + β * (I1 / L ^ 2) := by
  have h1 := (integrable_rho3_sc hL c).const_mul α
  have h2 := (integrable_rho3_abs_sc hL c).const_mul β
  refine ⟨h1.add h2, ?_⟩
  rw [integral_add h1 h2, integral_const_mul, integral_const_mul, integral_rho3_sc hL,
    integral_rho3_abs_sc hL]

lemma outer_bound {L : ℝ} (hL : 0 < L) (a b C H A B₀ : ℝ) (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hA : 0 ≤ A) (hB₀ : 0 ≤ B₀) :
    ∃ g : ℝ → ℝ, Integrable g ∧
      (∀ t, C * rho (L * Dd a b t) ^ 3 *
        (H * (A + B₀ * |t|) * (I0 / L) + H * B₀ / 2 * (I1 / L ^ 2)) ≤ g t) ∧
      ∫ t, g t = C * ((H * (A + B₀ * |a|) * (I0 / L) + H * B₀ / 2 * (I1 / L ^ 2)) * (I0 / L) +
        H * B₀ * (I0 / L) * (I1 / L ^ 2) +
        ((H * (A + B₀ * |b|) * (I0 / L) + H * B₀ / 2 * (I1 / L ^ 2)) * (I0 / L) +
        H * B₀ * (I0 / L) * (I1 / L ^ 2))) := by
  have hI0 := I0_nonneg
  have hI1 := I1_nonneg
  set αa := H * (A + B₀ * |a|) * (I0 / L) + H * B₀ / 2 * (I1 / L ^ 2)
  set αb := H * (A + B₀ * |b|) * (I0 / L) + H * B₀ / 2 * (I1 / L ^ 2)
  set β := H * B₀ * (I0 / L)
  obtain ⟨ia, va⟩ := inner_integral hL a αa β
  obtain ⟨ib, vb⟩ := inner_integral hL b αb β
  refine ⟨fun t => C * ((αa * rho (L * (t - a)) ^ 3 + β * (rho (L * (t - a)) ^ 3 * |t - a|)) +
    (αb * rho (L * (t - b)) ^ 3 + β * (rho (L * (t - b)) ^ 3 * |t - b|))),
    (ia.add ib).const_mul C, fun t => ?_, ?_⟩
  · have hD := rhoD_le hL a b t
    set V := H * (A + B₀ * |t|) * (I0 / L) + H * B₀ / 2 * (I1 / L ^ 2)
    have hV0 : 0 ≤ V := by positivity
    have hVa : V ≤ αa + β * |t - a| := by
      have : |t| ≤ |a| + |t - a| := by have := abs_sub_abs_le_abs_sub t a; linarith
      have h' : H * (A + B₀ * |t|) ≤ H * (A + B₀ * |a|) + H * B₀ * |t - a| := by
        have := mul_le_mul_of_nonneg_left this (mul_nonneg hH hB₀)
        nlinarith
      have := mul_le_mul_of_nonneg_right h' (by positivity : (0 : ℝ) ≤ I0 / L)
      simp only [V, αa, β]; nlinarith
    have hVb : V ≤ αb + β * |t - b| := by
      have : |t| ≤ |b| + |t - b| := by have := abs_sub_abs_le_abs_sub t b; linarith
      have h' : H * (A + B₀ * |t|) ≤ H * (A + B₀ * |b|) + H * B₀ * |t - b| := by
        have := mul_le_mul_of_nonneg_left this (mul_nonneg hH hB₀)
        nlinarith
      have := mul_le_mul_of_nonneg_right h' (by positivity : (0 : ℝ) ≤ I0 / L)
      simp only [V, αb, β]; nlinarith
    have ra := pow_nonneg (rho_nonneg (L * (t - a))) 3
    have rb := pow_nonneg (rho_nonneg (L * (t - b))) 3
    have e1 : rho (L * Dd a b t) ^ 3 * V ≤
        rho (L * (t - a)) ^ 3 * (αa + β * |t - a|) + rho (L * (t - b)) ^ 3 * (αb + β * |t - b|) :=
      calc rho (L * Dd a b t) ^ 3 * V ≤ (rho (L * (t - a)) ^ 3 + rho (L * (t - b)) ^ 3) * V :=
            mul_le_mul_of_nonneg_right hD hV0
        _ = rho (L * (t - a)) ^ 3 * V + rho (L * (t - b)) ^ 3 * V := by ring
        _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hVa ra) (mul_le_mul_of_nonneg_left hVb rb)
    calc C * rho (L * Dd a b t) ^ 3 * V = C * (rho (L * Dd a b t) ^ 3 * V) := by ring
      _ ≤ C * (rho (L * (t - a)) ^ 3 * (αa + β * |t - a|) +
          rho (L * (t - b)) ^ 3 * (αb + β * |t - b|)) := mul_le_mul_of_nonneg_left e1 hC
      _ = _ := by ring
  · rw [integral_const_mul, integral_add ia ib, va, vb]

end ErrorIntegral

/-! ### The pointwise (in `t`) family bound for the error -/

section Pointwise

variable (P : PrimeSetup)

theorem famSum_h_le (hStir : StirlingDigamma) {CU : ℝ} (hCU : ∀ y, ‖U P y‖ ≤ CU * rho y ^ 8)
    (W : Weight) {Q : ℝ} (hQ : 1 < Q) (T τ₀ : ℝ) {A B₀ : ℝ} (hB₀ : 0 ≤ B₀)
    (hfam : ∀ t, famSum W Q (fun _ χ => nuChi P Q χ t ^ 2) ≤ W.H Q * (A + B₀ * |t|)) (t : ℝ) :
    famSum W Q (fun _ χ => ∫ t', Ek P Q T τ₀ t t' * nuChi P Q χ t * nuChi P Q χ t') ≤
      (2 * P.aInt * CU ^ 2 * Clat * P.L Q ^ 4) *
        rho (P.L Q * Dd ((1 + P.θ) * T) ((2 - P.θ) * T) t) ^ 3 *
        (W.H Q * (A + B₀ * |t|) * (I0 / P.L Q) + W.H Q * B₀ / 2 * (I1 / P.L Q ^ 2)) := by
  have hL := P.L_pos hQ
  have ha := aInt_pos' P
  have hH := W.H_nonneg Q
  set L := P.L Q
  set d3 := rho (L * Dd ((1 + P.θ) * T) ((2 - P.θ) * T) t) ^ 3
  set C := 2 * P.aInt * CU ^ 2 * Clat * L ^ 4 * d3 with hCdef
  have hd3 : 0 ≤ d3 := pow_nonneg (rho_nonneg _) 3
  have hC : 0 ≤ C := by
    have := Clat_nonneg; positivity
  rw [famSum_integral W Q (fun q χ => (perChi P hStir hQ T τ₀ χ).1 t)]
  obtain ⟨hi, hv⟩ := inner_integral hL t (C * (W.H Q * (A + B₀ * |t|))) (C * (W.H Q * B₀ / 2))
  have hbound : ∀ t', famSum W Q (fun q χ => Ek P Q T τ₀ t t' * nuChi P Q χ t * nuChi P Q χ t') ≤
      C * (W.H Q * (A + B₀ * |t|)) * rho (L * (t' - t)) ^ 3 +
        C * (W.H Q * B₀ / 2) * (rho (L * (t' - t)) ^ 3 * |t' - t|) := by
    intro t'
    have e : famSum W Q (fun q χ => Ek P Q T τ₀ t t' * nuChi P Q χ t * nuChi P Q χ t') =
        Ek P Q T τ₀ t t' * famSum W Q (fun q χ => nuChi P Q χ t * nuChi P Q χ t') := by
      rw [← famSum_mul_left]; congr 1; funext q χ; ring
    rw [e]
    set S := famSum W Q (fun q χ => nuChi P Q χ t * nuChi P Q χ t')
    have hup : S ≤ (famSum W Q (fun _ χ => nuChi P Q χ t ^ 2) +
        famSum W Q (fun _ χ => nuChi P Q χ t' ^ 2)) / 2 := by
      have := famSum_mono W Q (f := fun q χ => nuChi P Q χ t * nuChi P Q χ t')
        (g := fun q χ => (1 / 2) * (nuChi P Q χ t ^ 2 + nuChi P Q χ t' ^ 2))
        (fun q _ χ => by nlinarith [sq_nonneg (nuChi P Q χ t - nuChi P Q χ t')])
      rw [famSum_mul_left, famSum_add] at this
      linarith
    have hlo : -S ≤ (famSum W Q (fun _ χ => nuChi P Q χ t ^ 2) +
        famSum W Q (fun _ χ => nuChi P Q χ t' ^ 2)) / 2 := by
      have := famSum_mono W Q (f := fun q χ => (-1) * (nuChi P Q χ t * nuChi P Q χ t'))
        (g := fun q χ => (1 / 2) * (nuChi P Q χ t ^ 2 + nuChi P Q χ t' ^ 2))
        (fun q _ χ => by nlinarith [sq_nonneg (nuChi P Q χ t + nuChi P Q χ t')])
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
    have hE := Ek_bound P hCU hQ T τ₀ t t'
    have hr : rho (L * (t - t')) = rho (L * (t' - t)) := by
      rw [← rho_neg]; congr 1; ring
    rw [hr] at hE
    have hr0 := pow_nonneg (rho_nonneg (L * (t' - t))) 3
    calc Ek P Q T τ₀ t t' * S ≤ |Ek P Q T τ₀ t t' * S| := le_abs_self _
      _ = |Ek P Q T τ₀ t t'| * |S| := abs_mul _ _
      _ ≤ (C * rho (L * (t' - t)) ^ 3) *
          (W.H Q * (A + B₀ * |t|) + W.H Q * B₀ / 2 * |t' - t|) := by
          refine mul_le_mul (le_of_eq_of_le rfl (hE.trans (le_of_eq ?_))) hS (abs_nonneg _)
            (mul_nonneg hC hr0)
          simp only [hCdef, d3]; ring
      _ = _ := by ring
  refine (integral_mono (famSum_integrable W Q fun q χ => (perChi P hStir hQ T τ₀ χ).1 t) hi
    hbound).trans (le_of_eq ?_)
  rw [hv]; simp only [hCdef]; ring

end Pointwise

/-! ### Final arithmetic -/

lemma err_arith {ℓ T lam C₂ I0 I1 A₁ A₂ B₀ D : ℝ} (hℓ : 1 ≤ ℓ) (hT : 1 ≤ T) (hlam : 0 < lam)
    (hC₂ : 0 ≤ C₂) (hI0 : 0 ≤ I0) (hI1 : 0 ≤ I1) (hA₁ : 0 ≤ A₁) (hB₀ : 0 ≤ B₀)
    (hD : 0 < D)
    (h1 : 3 * ((C₂ * I0 ^ 2 * lam ^ 2 * (128 + 2 * A₁) + 3 * C₂ * B₀ * I0 * I1 * lam) +
      3 * B₀ * C₂ * I0 ^ 2 * lam ^ 2) ≤ D * ℓ)
    (h2 : 3 * (2 * A₂ * C₂ * I0 ^ 2 * lam ^ 5) ≤ D * T) :
    C₂ * ((lam * ℓ) ^ 2 * I0 ^ 2 * (2 * (4 * (ℓ + 3) ^ 2 + A₁ + A₂ * (lam * ℓ) ^ 3) +
      B₀ * (3 * T)) + 3 * B₀ * I0 * I1 * (lam * ℓ)) ≤ D * ℓ ^ 5 * T := by
  set M₁ := C₂ * I0 ^ 2 * lam ^ 2 * (128 + 2 * A₁) + 3 * C₂ * B₀ * I0 * I1 * lam with hM₁
  set M₂ := 2 * A₂ * C₂ * I0 ^ 2 * lam ^ 5 with hM₂
  set M₃ := 3 * B₀ * C₂ * I0 ^ 2 * lam ^ 2 with hM₃
  have hM₁0 : 0 ≤ M₁ := by positivity
  have hM₃0 : 0 ≤ M₃ := by positivity
  have hℓ0 : 0 ≤ ℓ := by linarith
  have hℓ2 : ℓ ^ 2 ≤ ℓ ^ 4 := pow_le_pow_right₀ hℓ (by norm_num)
  have hℓ14 : ℓ ≤ ℓ ^ 4 := by
    have := pow_le_pow_right₀ hℓ (show 1 ≤ 4 by norm_num); simpa using this
  have hℓ35 : ℓ ^ 3 ≤ ℓ ^ 5 := pow_le_pow_right₀ hℓ (by norm_num)
  have hℓ45 : ℓ ^ 4 ≤ ℓ ^ 5 := pow_le_pow_right₀ hℓ (by norm_num)
  have h16 : (ℓ + 3) ^ 2 ≤ 16 * ℓ ^ 2 := by nlinarith
  have s1 : C₂ * ((lam * ℓ) ^ 2 * I0 ^ 2 * (2 * (4 * (ℓ + 3) ^ 2 + A₁ + A₂ * (lam * ℓ) ^ 3) +
      B₀ * (3 * T)) + 3 * B₀ * I0 * I1 * (lam * ℓ)) ≤ M₁ * ℓ ^ 4 + M₂ * ℓ ^ 5 + M₃ * ℓ ^ 2 * T := by
    have t1 : C₂ * lam ^ 2 * I0 ^ 2 * 8 * ℓ ^ 2 * (ℓ + 3) ^ 2 ≤
        C₂ * lam ^ 2 * I0 ^ 2 * 8 * ℓ ^ 2 * (16 * ℓ ^ 2) :=
      mul_le_mul_of_nonneg_left h16 (by positivity)
    have t2 : C₂ * lam ^ 2 * I0 ^ 2 * 2 * A₁ * ℓ ^ 2 ≤ C₂ * lam ^ 2 * I0 ^ 2 * 2 * A₁ * ℓ ^ 4 :=
      mul_le_mul_of_nonneg_left hℓ2 (by positivity)
    have t3 : 3 * C₂ * B₀ * I0 * I1 * lam * ℓ ≤ 3 * C₂ * B₀ * I0 * I1 * lam * ℓ ^ 4 :=
      mul_le_mul_of_nonneg_left hℓ14 (by positivity)
    rw [hM₁, hM₂, hM₃]
    nlinarith [t1, t2, t3]
  have s2 : M₁ * ℓ ^ 4 + M₂ * ℓ ^ 5 + M₃ * ℓ ^ 2 * T ≤ D * ℓ ^ 5 * T := by
    have e1 : 3 * M₁ ≤ D * ℓ := by linarith
    have e3 : 3 * M₃ ≤ D * ℓ := by linarith
    have hℓ4 : 0 ≤ ℓ ^ 4 := by positivity
    have hℓ5 : 0 ≤ ℓ ^ 5 := by positivity
    have u1 : 3 * M₁ * ℓ ^ 4 ≤ D * ℓ * ℓ ^ 4 := mul_le_mul_of_nonneg_right e1 hℓ4
    have u1' : D * ℓ ^ 5 ≤ D * ℓ ^ 5 * T := by
      have := mul_le_mul_of_nonneg_left hT (by positivity : 0 ≤ D * ℓ ^ 5); linarith
    have u2 : 3 * M₂ * ℓ ^ 5 ≤ D * T * ℓ ^ 5 := mul_le_mul_of_nonneg_right h2 hℓ5
    have u3 : 3 * M₃ * (ℓ ^ 2 * T) ≤ D * ℓ * (ℓ ^ 2 * T) :=
      mul_le_mul_of_nonneg_right e3 (by positivity)
    have u3' : D * ℓ ^ 3 * T ≤ D * ℓ ^ 5 * T :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hℓ35 hD.le) (by linarith)
    have r1 : D * ℓ * ℓ ^ 4 = D * ℓ ^ 5 := by ring
    have r3 : D * ℓ * (ℓ ^ 2 * T) = D * ℓ ^ 3 * T := by ring
    nlinarith
  linarith

end FC2

open FC2 in
/-- **`eq:fc2`** (finite-centre replacement, upper half; display (4.3), Proposition 4.4):
`𝔐 ≤ 𝓜/(aL)² + o(HTℓ)`, uniformly in `T ∈ [ℓ^{a₀}, ℓ^{A₀}]`, for each fixed `τ₀`. -/
theorem fc2_proof (hEF : ExplicitGabor_Statement) (hMV : MV_LargeSieve) (hStir : StirlingDigamma)
    (hWH : lemWH_Statement) : FC2_Statement := by
  intro P W τ₀ δ hδ
  obtain ⟨CU, hCU0, hCU⟩ := U_bound P
  obtain ⟨A₁, A₂, B₀, Q₁, hA₁, hA₂, hB₀, hQ₁, hfam⟩ := famSum_nu_sq hMV hStir hWH P W
  obtain ⟨QE, hQE⟩ := hEF P W
  have ha := aInt_pos' P
  have hlam := P.lam_pos
  have hI0 := I0_nonneg
  have hI1 := I1_nonneg
  set C₂ := 2 * P.aInt * CU ^ 2 * Clat with hC₂def
  have hC₂ : 0 ≤ C₂ := by have := Clat_nonneg; positivity
  set D := δ * P.aInt ^ 2 * P.lam ^ 4 with hDdef
  have hD : 0 < D := by positivity
  set M₁ := C₂ * I0 ^ 2 * P.lam ^ 2 * (128 + 2 * A₁) + 3 * C₂ * B₀ * I0 * I1 * P.lam with hM₁def
  set M₂ := 2 * A₂ * C₂ * I0 ^ 2 * P.lam ^ 5 with hM₂def
  set M₃ := 3 * B₀ * C₂ * I0 ^ 2 * P.lam ^ 2 with hM₃def
  set ℓ₁ := max 1 (3 * (M₁ + M₃) / D) with hℓ₁def
  set m₂ := max 1 (3 * M₂ / D) with hm₂def
  have hm₂0 : 0 ≤ m₂ := le_trans zero_le_one (le_max_left _ _)
  set ℓ₂ := m₂ ^ (P.a0)⁻¹ with hℓ₂def
  have hℓ₂0 : 0 ≤ ℓ₂ := Real.rpow_nonneg hm₂0 _
  refine ⟨max (max Q₁ QE) (max (Real.exp ℓ₁) (Real.exp ℓ₂)), fun Q hQ T hT => ?_⟩
  have hQQ₁ : Q₁ ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hQ
  have hQQE : QE ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hQ
  have hQℓ₁ : Real.exp ℓ₁ ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hQ
  have hQℓ₂ : Real.exp ℓ₂ ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hQ
  have hℓ₁1 : 1 ≤ ℓ₁ := le_max_left _ _
  have hQ1 : 1 < Q := lt_of_lt_of_le (by have := Real.add_one_le_exp ℓ₁; linarith) hQℓ₁
  have hℓℓ₁ : ℓ₁ ≤ Real.log Q := by
    rw [← Real.log_exp ℓ₁]; exact Real.log_le_log (Real.exp_pos _) hQℓ₁
  have hℓℓ₂ : ℓ₂ ≤ Real.log Q := by
    rw [← Real.log_exp ℓ₂]; exact Real.log_le_log (Real.exp_pos _) hQℓ₂
  have hℓ1 : 1 ≤ Real.log Q := le_trans hℓ₁1 hℓℓ₁
  have hLpos : 0 < P.L Q := P.L_pos hQ1
  have hH := W.H_nonneg Q
  -- `T`
  have hm₂T : m₂ ≤ T := by
    have h1 : ℓ₂ ^ P.a0 ≤ Real.log Q ^ P.a0 := Real.rpow_le_rpow hℓ₂0 hℓℓ₂ P.a0_pos.le
    have h2 : ℓ₂ ^ P.a0 = m₂ := Real.rpow_inv_rpow hm₂0 P.a0_pos.ne'
    have h3 := hT.1
    linarith
  have hT1 : 1 ≤ T := le_trans (le_max_left _ _) hm₂T
  have hT0 : 0 < T := by linarith
  have hTM₂ : 3 * M₂ ≤ D * T := by
    have := le_trans (le_max_right _ _) hm₂T
    rw [div_le_iff₀ hD] at this; linarith
  have hℓM : 3 * (M₁ + M₃) ≤ D * Real.log Q := by
    have := le_trans (le_max_right _ _) hℓℓ₁
    rw [div_le_iff₀ hD] at this; linarith
  -- `𝔐` as a family sum of real Frobenius norms
  set K := P.KJ Q T τ₀
  set X : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ := fun q χ =>
    ∑ k ∈ K, ∑ l ∈ K, (∫ t, pr P Q τ₀ k t * pr P Q τ₀ l t * nuChi P Q χ t) ^ 2 with hXdef
  have hMfrak : P.Mfrak W Q T τ₀ = ((P.aInt * P.L Q ^ 2) ^ 2)⁻¹ * famSum W Q X := by
    rw [← famSum_mul_left]
    unfold PrimeSetup.Mfrak famSum
    refine Finset.sum_congr rfl fun q hq => ?_
    by_cases hω : W.omega Q q = 0
    · simp [hω]
    · congr 1
      refine Finset.sum_congr rfl fun χ hχ => ?_
      have hw : W.w (q / Q) ≠ 0 := by
        intro h; apply hω; unfold Weight.omega; rw [h]; ring
      have hF : InFamily W Q q χ :=
        ⟨mem_primChars.mp hχ, lt_of_le_of_ne (W.nonneg _) (Ne.symm hw)⟩
      have hterm : ∀ k l : K, ‖P.Gabor Q T τ₀ χ k l / (P.aInt * P.L Q ^ 2)‖ ^ 2 =
          ((P.aInt * P.L Q ^ 2) ^ 2)⁻¹ *
            (∫ t, pr P Q τ₀ k t * pr P Q τ₀ l t * nuChi P Q χ t) ^ 2 := by
        intro k l
        rw [hQE Q hQQE T hT τ₀ q χ hF k l]
        have e : (fun t : ℝ => P.pk Q τ₀ k (t : ℂ) * P.pk Q τ₀ l (t : ℂ) * (nuChi P Q χ t : ℂ)) =
            fun t => ((pr P Q τ₀ k t * pr P Q τ₀ l t * nuChi P Q χ t : ℝ) : ℂ) := by
          funext t; rw [pk_eq P hQ1, pk_eq P hQ1]; push_cast; ring
        rw [e, integral_complex_ofReal, norm_div, Complex.norm_real, Real.norm_eq_abs, norm_mul,
          norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos ha, abs_of_pos hLpos, div_pow, sq_abs]
        field_simp
      set c := ((P.aInt * P.L Q ^ 2) ^ 2)⁻¹
      calc ∑ k : K, ∑ l : K, ‖P.Gabor Q T τ₀ χ k l / (P.aInt * P.L Q ^ 2)‖ ^ 2
          = ∑ k : K, ∑ l : K, c * (∫ t, pr P Q τ₀ k t * pr P Q τ₀ l t * nuChi P Q χ t) ^ 2 :=
            Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => hterm k l
        _ = ∑ k : K, c * ∑ l ∈ K, (∫ t, pr P Q τ₀ k t * pr P Q τ₀ l t * nuChi P Q χ t) ^ 2 := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_coe_sort K
              (fun l => c * (∫ t, pr P Q τ₀ k t * pr P Q τ₀ l t * nuChi P Q χ t) ^ 2)
        _ = ∑ k ∈ K, c * ∑ l ∈ K, (∫ t, pr P Q τ₀ k t * pr P Q τ₀ l t * nuChi P Q χ t) ^ 2 :=
            Finset.sum_coe_sort K
              (fun k => c * ∑ l ∈ K, (∫ t, pr P Q τ₀ k t * pr P Q τ₀ l t * nuChi P Q χ t) ^ 2)
        _ = c * X q χ := by rw [← Finset.mul_sum]
  -- `∑_χ ω_χ ∑_{k,l} G² − L² 𝓜 = ∫ ∑_χ ω_χ h_χ`
  have hdiff : famSum W Q X - P.L Q ^ 2 * Mcal P W Q T =
      ∫ t, famSum W Q (fun q χ => ∫ t', Ek P Q T τ₀ t t' * nuChi P Q χ t * nuChi P Q χ t') := by
    unfold Mcal
    rw [← famSum_mul_left, ← famSum_sub,
      ← famSum_integral W Q (fun q χ => (perChi P hStir hQ1 T τ₀ χ).2.1)]
    congr 1; funext q χ
    exact (perChi P hStir hQ1 T τ₀ χ).2.2
  -- the error integral
  set A := 4 * (Real.log Q + 3) ^ 2 + A₁ + A₂ * P.L Q ^ 3 with hAdef
  have hA0 : 0 ≤ A := by have := hLpos.le; positivity
  have hfam' : ∀ t, famSum W Q (fun _ χ => nuChi P Q χ t ^ 2) ≤ W.H Q * (A + B₀ * |t|) :=
    fun t => hfam Q hQQ₁ t
  obtain ⟨g, hgi, hgle, hgint⟩ := outer_bound hLpos ((1 + P.θ) * T) ((2 - P.θ) * T)
    (2 * P.aInt * CU ^ 2 * Clat * P.L Q ^ 4) (W.H Q) A B₀
    (by have := Clat_nonneg; positivity) hH hA0 hB₀
  have hstep3 : ∫ t, famSum W Q
      (fun q χ => ∫ t', Ek P Q T τ₀ t t' * nuChi P Q χ t * nuChi P Q χ t') ≤ ∫ t, g t :=
    integral_mono (famSum_integrable W Q fun q χ => (perChi P hStir hQ1 T τ₀ χ).2.1) hgi
      (fun t => (famSum_h_le P hStir hCU W hQ1 T τ₀ hB₀ hfam' t).trans (hgle t))
  have key : C₂ * (P.L Q ^ 2 * I0 ^ 2 * (2 * (4 * (Real.log Q + 3) ^ 2 + A₁ + A₂ * P.L Q ^ 3) +
      B₀ * (3 * T)) + 3 * B₀ * I0 * I1 * P.L Q) ≤ D * Real.log Q ^ 5 * T :=
    err_arith hℓ1 hT1 hlam hC₂ hI0 hI1 hA₁ hB₀ hD hℓM hTM₂
  have hErr : ∫ t, g t ≤ δ * (P.aInt * P.L Q ^ 2) ^ 2 * (W.H Q * T * Real.log Q) := by
    rw [hgint]
    have hθ1 : 0 < (1 + P.θ) * T := by have := P.θ_pos; positivity
    have hθ2 : 0 < (2 - P.θ) * T := mul_pos (by linarith [P.θ_lt]) hT0
    rw [abs_of_pos hθ1, abs_of_pos hθ2]
    have hL0 : P.L Q ≠ 0 := hLpos.ne'
    calc _ = W.H Q * (C₂ * (P.L Q ^ 2 * I0 ^ 2 * (2 * (4 * (Real.log Q + 3) ^ 2 + A₁ +
          A₂ * P.L Q ^ 3) + B₀ * (3 * T)) + 3 * B₀ * I0 * I1 * P.L Q)) := by
          rw [hAdef, hC₂def]; field_simp; ring
      _ ≤ W.H Q * (D * Real.log Q ^ 5 * T) := mul_le_mul_of_nonneg_left key hH
      _ = δ * (P.aInt * P.L Q ^ 2) ^ 2 * (W.H Q * T * Real.log Q) := by
          rw [hDdef]; simp only [PrimeSetup.L]; ring
  have hfin : famSum W Q X ≤ P.L Q ^ 2 * Mcal P W Q T +
      δ * (P.aInt * P.L Q ^ 2) ^ 2 * (W.H Q * T * Real.log Q) := by
    linarith [hdiff, hstep3, hErr]
  rw [hMfrak]
  have hc : 0 < (P.aInt * P.L Q ^ 2) ^ 2 := by positivity
  unfold ell
  calc ((P.aInt * P.L Q ^ 2) ^ 2)⁻¹ * famSum W Q X
      ≤ ((P.aInt * P.L Q ^ 2) ^ 2)⁻¹ * (P.L Q ^ 2 * Mcal P W Q T +
          δ * (P.aInt * P.L Q ^ 2) ^ 2 * (W.H Q * T * Real.log Q)) :=
        mul_le_mul_of_nonneg_left hfin (inv_nonneg.mpr hc.le)
    _ = Mcal P W Q T / (P.aInt * P.L Q) ^ 2 + δ * (W.H Q * T * Real.log Q) := by
        field_simp

end Families.Ported.Second
