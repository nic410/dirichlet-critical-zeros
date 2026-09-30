/-
# Prime side (paper §5): the profile test function and the `𝒬_F(f_v)` identity

* `vv = v * v` (`v = ψ²`): smooth, even, nonnegative, compactly supported; `g(u) = L (v*v)(u/L)`.
* `Hc c σ = (v*v)(σ) c(λσ)` and the test function `hTest c Q y = L Hc(y/L) = c(y/ℓ) g(y)` of the proof of
  `prop:second` (Proposition 5.13: "`h(y) = c(y/ℓ) g(y)`"), with the derivative bounds required by
  `lem:B2` (`|h^{(i)}| ≤ C_i · hmax`, `hmax = L·M`, uniformly in `Q`).
* `IF c = ∫ F_b(λσ) (v*v)(σ) c(λσ) dσ` and `∫ ℓ F_b(s/ℓ) h(s) ds = L² ℓ IF` (proof of Proposition 5.13).
* **`Qf_fv_eq`**: `𝒬_F(f_v) = (b/λ + 2 IF)/a²` (proof of Proposition 5.13).
* a fixed bump `Bmp` (`= 1` on `[0,3]`) for the bound `∑ b_n² ≪ Lℓ`.
-/
import Families.Ported.Second.Common
import Families.Phase4.A.QfBasic
import Families.Phase3.C.B2Density
import Families.Ported.Second.Assembly

noncomputable section

open scoped BigOperators ContDiff
open Finset MeasureTheory Filter Topology

namespace Families.Ported.Second

open Families

variable (P : PrimeSetup)

/-! ### `v = ψ²` and `v * v` -/

lemma vfun_even (s : ℝ) : P.vfun (-s) = P.vfun s := by
  unfold PrimeSetup.vfun; rw [P.ψ_even]

lemma vfun_nonneg (s : ℝ) : 0 ≤ P.vfun s := sq_nonneg _

lemma vfun_contDiff : ContDiff ℝ ∞ P.vfun := P.ψ_smooth.pow 2

lemma vfun_zero_of {x : ℝ} (hx : 1 / 2 ≤ |x|) : P.vfun x = 0 := by
  obtain ⟨r, hr, h⟩ := P.ψ_supp
  unfold PrimeSetup.vfun; rw [h x (by linarith)]; ring

lemma vfun_hasCompactSupport : HasCompactSupport P.vfun := by
  refine HasCompactSupport.intro (K := Set.Icc (-(1 / 2)) (1 / 2)) isCompact_Icc ?_
  intro x hx
  apply vfun_zero_of
  by_contra hcon
  push Not at hcon
  exact hx (Set.mem_Icc.mpr (abs_le.mp hcon.le))

lemma vfun_integrable : Integrable P.vfun :=
  (vfun_contDiff P).continuous.integrable_of_hasCompactSupport (vfun_hasCompactSupport P)

/-- `(v * v)(σ) = ∫ v(s) v(σ − s) ds`. -/
def vv (σ : ℝ) : ℝ := ∫ s, P.vfun s * P.vfun (σ - s)

lemma vv_eq_conv : vv P = convolution P.vfun P.vfun (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  funext σ; rw [convolution_def]; rfl

lemma vv_contDiff : ContDiff ℝ ∞ (vv P) := by
  rw [vv_eq_conv]
  exact (vfun_hasCompactSupport P).contDiff_convolution_right (n := ⊤) _
    (vfun_integrable P).locallyIntegrable (vfun_contDiff P)

lemma vv_hasCompactSupport : HasCompactSupport (vv P) := by
  rw [vv_eq_conv]
  exact (vfun_hasCompactSupport P).convolution _ (vfun_hasCompactSupport P)

lemma vv_continuous : Continuous (vv P) := (vv_contDiff P).continuous

lemma vv_integrable : Integrable (vv P) :=
  (vv_continuous P).integrable_of_hasCompactSupport (vv_hasCompactSupport P)

lemma vv_nonneg (σ : ℝ) : 0 ≤ vv P σ :=
  integral_nonneg fun s => mul_nonneg (vfun_nonneg P s) (vfun_nonneg P _)

lemma vv_even (σ : ℝ) : vv P (-σ) = vv P σ := by
  unfold vv
  rw [← integral_neg_eq_self]
  have h : ∫ s, P.vfun s * P.vfun (σ - s) = ∫ s, P.vfun (σ - s) * P.vfun s := by
    refine integral_congr_ae (Eventually.of_forall fun s => ?_); ring
  rw [h, ← integral_sub_left_eq_self (fun s => P.vfun (σ - s) * P.vfun s) (μ := volume) σ]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [sub_sub_cancel]
  rw [vfun_even, show -σ - -s = -(σ - s) by ring, vfun_even]

/-- `g(u) = ψ_L² * ψ_L² (u) = L (v*v)(u/L)`. -/
lemma g_eq_vv {Q : ℝ} (hQ : 1 < Q) (u : ℝ) : P.g Q u = P.L Q * vv P (u / P.L Q) := by
  have hL := P.L_pos hQ
  have h := Measure.integral_comp_div (fun s => P.vfun s * P.vfun (u / P.L Q - s)) (P.L Q)
  rw [abs_of_pos hL, smul_eq_mul] at h
  unfold vv
  rw [← h]
  unfold PrimeSetup.g PrimeSetup.ψL PrimeSetup.vfun
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [sub_div]

/-! ### The profile function `H_c(σ) = (v*v)(σ) c(λσ)` and the test function `h` -/

/-- `H_c(σ) = (v*v)(σ) c(λσ)`. -/
def Hc (c : ℝ → ℝ) (σ : ℝ) : ℝ := vv P σ * c (P.lam * σ)

variable {P}

lemma Hc_contDiff {c : ℝ → ℝ} (hc : ContDiff ℝ ∞ c) : ContDiff ℝ ∞ (Hc P c) :=
  (vv_contDiff P).mul (hc.comp (contDiff_const.mul contDiff_id))

lemma Hc_hasCompactSupport (c : ℝ → ℝ) : HasCompactSupport (Hc P c) :=
  (vv_hasCompactSupport P).mul_right

lemma Hc_nonneg {c : ℝ → ℝ} (hc1 : ∀ α, 1 ≤ c α) (σ : ℝ) : 0 ≤ Hc P c σ :=
  mul_nonneg (vv_nonneg P σ) (le_trans zero_le_one (hc1 _))

lemma Hc_iteratedDeriv_bounded {c : ℝ → ℝ} (hc : ContDiff ℝ ∞ c) (i : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ σ, |iteratedDeriv i (Hc P c) σ| ≤ D := by
  have hcont : Continuous (iteratedFDeriv ℝ i (Hc P c)) :=
    (Hc_contDiff hc).continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨D, hD⟩ := hcont.bounded_above_of_compact_support
    ((Hc_hasCompactSupport c).iteratedFDeriv i)
  refine ⟨max D 0, le_max_right _ _, fun σ => ?_⟩
  rw [← Real.norm_eq_abs, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact (hD σ).trans (le_max_left _ _)

lemma Hc_bounded {c : ℝ → ℝ} (hc : ContDiff ℝ ∞ c) : ∃ M : ℝ, 1 ≤ M ∧ ∀ σ, Hc P c σ ≤ M := by
  obtain ⟨D, -, hD⟩ := Hc_iteratedDeriv_bounded (P := P) hc 0
  refine ⟨max D 1, le_max_right _ _, fun σ => ?_⟩
  have := hD σ
  simp only [iteratedDeriv_zero] at this
  exact (le_abs_self _).trans (this.trans (le_max_left _ _))

/-- The test function of `prop:second`: `h(y) = L H_c(y/L)` (`= c(y/ℓ) g(y)`, `hTest_eq`). -/
def hTest (P : PrimeSetup) (c : ℝ → ℝ) (Q y : ℝ) : ℝ := P.L Q * Hc P c (y / P.L Q)

lemma hTest_eq {c : ℝ → ℝ} {Q : ℝ} (hQ : 1 < Q) (y : ℝ) :
    hTest P c Q y = c (y / ell Q) * P.g Q y := by
  have hL := P.L_pos hQ
  have hℓ : 0 < ell Q := Real.log_pos hQ
  unfold hTest Hc
  rw [g_eq_vv P hQ]
  have hlam : P.lam ≠ 0 := P.lam_pos.ne'
  have : P.lam * (y / P.L Q) = y / ell Q := by
    unfold PrimeSetup.L ell; field_simp
  rw [this]; ring

lemma hTest_contDiff {c : ℝ → ℝ} (hc : ContDiff ℝ ∞ c) (Q : ℝ) : ContDiff ℝ ∞ (hTest P c Q) :=
  contDiff_const.mul ((Hc_contDiff hc).comp (contDiff_id.div_const _))

lemma hTest_nonneg {c : ℝ → ℝ} (hc1 : ∀ α, 1 ≤ c α) {Q : ℝ} (hQ : 1 < Q) (y : ℝ) :
    0 ≤ hTest P c Q y :=
  mul_nonneg (P.L_pos hQ).le (Hc_nonneg hc1 _)

lemma hTest_integrable {c : ℝ → ℝ} (hc : ContDiff ℝ ∞ c) {Q : ℝ} (hQ : 1 < Q) :
    Integrable (hTest P c Q) := by
  have hL := P.L_pos hQ
  have h1 : Integrable (Hc P c) :=
    (Hc_contDiff hc).continuous.integrable_of_hasCompactSupport (Hc_hasCompactSupport c)
  have h2 := (h1.comp_div hL.ne').const_mul (P.L Q)
  exact h2

lemma hTest_le {c : ℝ → ℝ} {M : ℝ} (hM : ∀ σ, Hc P c σ ≤ M) {Q : ℝ} (hQ : 1 < Q) (y : ℝ) :
    hTest P c Q y ≤ P.L Q * M :=
  mul_le_mul_of_nonneg_left (hM _) (P.L_pos hQ).le

lemma hTest_iteratedDeriv {c : ℝ → ℝ} (hc : ContDiff ℝ ∞ c) {Q : ℝ} (hL1 : 1 ≤ P.L Q) (i : ℕ)
    (y : ℝ) : iteratedDeriv i (hTest P c Q) y =
      P.L Q * ((P.L Q)⁻¹ ^ i * iteratedDeriv i (Hc P c) ((P.L Q)⁻¹ * y)) := by
  have hdiff : ContDiff ℝ i (Hc P c) := (Hc_contDiff hc).of_le (by exact_mod_cast le_top)
  have e : hTest P c Q = fun y => P.L Q * (Hc P c ((P.L Q)⁻¹ * y)) := by
    funext y; unfold hTest; rw [div_eq_inv_mul]
  rw [e, iteratedDeriv_const_mul_field, iteratedDeriv_comp_const_mul hdiff]

lemma hTest_deriv_bound {c : ℝ → ℝ} (hc : ContDiff ℝ ∞ c) {M : ℝ} (hM1 : 1 ≤ M) (i : ℕ)
    {D : ℝ} (hD : ∀ σ, |iteratedDeriv i (Hc P c) σ| ≤ D) {Q : ℝ} (hL1 : 1 ≤ P.L Q) (y : ℝ) :
    |iteratedDeriv i (hTest P c Q) y| ≤ D * (P.L Q * M) := by
  rw [hTest_iteratedDeriv hc hL1, abs_mul, abs_mul]
  have hL0 : 0 < P.L Q := by linarith
  have hinv : |(P.L Q)⁻¹ ^ i| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hL1)
  have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD 0)
  rw [abs_of_pos hL0]
  calc P.L Q * (|(P.L Q)⁻¹ ^ i| * |iteratedDeriv i (Hc P c) ((P.L Q)⁻¹ * y)|)
      ≤ P.L Q * (1 * D) := by
        apply mul_le_mul_of_nonneg_left _ hL0.le
        exact mul_le_mul hinv (hD _) (abs_nonneg _) zero_le_one
    _ ≤ D * (P.L Q * M) := by
        have := mul_le_mul_of_nonneg_left hM1 (mul_nonneg hD0 hL0.le)
        linarith

/-- `I_F = ∫ F_b(λσ) (v*v)(σ) c(λσ) dσ`. -/
def IF (P : PrimeSetup) (c : ℝ → ℝ) : ℝ := ∫ σ, Fb P.ε₃ (P.lam * σ) * Hc P c σ

lemma IF_nonneg {c : ℝ → ℝ} (hc1 : ∀ α, 1 ≤ c α) : 0 ≤ IF P c :=
  integral_nonneg fun σ => mul_nonneg (Families.Phase3.C.Fb_nonneg _ _ P.ε₃_pos.le)
    (Hc_nonneg hc1 σ)

/-- `∫ ℓ F_b(s/ℓ) h(s) ds = L² ℓ I_F`. -/
lemma integral_hTest {c : ℝ → ℝ} {Q : ℝ} (hQ : 1 < Q) :
    ∫ s, ell Q * Fb P.ε₃ (s / ell Q) * hTest P c Q s = P.L Q ^ 2 * ell Q * IF P c := by
  have hL := P.L_pos hQ
  have hℓ : 0 < ell Q := Real.log_pos hQ
  have h := Measure.integral_comp_div
    (fun σ => ell Q * Fb P.ε₃ (P.lam * σ) * (P.L Q * Hc P c σ)) (P.L Q)
  rw [abs_of_pos hL, smul_eq_mul] at h
  have e : ∀ s, ell Q * Fb P.ε₃ (s / ell Q) * hTest P c Q s =
      ell Q * Fb P.ε₃ (P.lam * (s / P.L Q)) * (P.L Q * Hc P c (s / P.L Q)) := by
    intro s
    have hlam : P.lam ≠ 0 := P.lam_pos.ne'
    have : P.lam * (s / P.L Q) = s / ell Q := by unfold PrimeSetup.L ell; field_simp
    rw [this]; rfl
  simp_rw [e]
  rw [h]
  have e2 : ∫ σ, ell Q * Fb P.ε₃ (P.lam * σ) * (P.L Q * Hc P c σ) = ell Q * P.L Q * IF P c := by
    unfold IF; rw [← integral_const_mul]; congr 1; funext σ; ring
  rw [e2]; ring

/-! ### The identity `𝒬_F(f_v) = (b/λ + 2 I_F)/a²` -/

section QfIdentity

variable (P)

/-- The kernel `F(α) = c(α) min(α, 1 + ε₄)` of `prop:second`. -/
def Fker (c : ℝ → ℝ) (α : ℝ) : ℝ := c α * min α (1 + 2 * P.ε₃)

variable {P}

lemma Fker_continuous {c : ℝ → ℝ} (hc : Continuous c) : Continuous (Fker P c) :=
  hc.mul (continuous_id.min continuous_const)

lemma Gplus_integrable {c : ℝ → ℝ} (hc : Continuous c) :
    Integrable (fun σ => Fb P.ε₃ (P.lam * σ) * Hc P c σ) := by
  have hcont : Continuous (fun σ => Fb P.ε₃ (P.lam * σ) * Hc P c σ) := by
    unfold Fb Hc
    exact ((continuous_const.mul continuous_id).max continuous_const |>.min continuous_const).mul
      ((vv_continuous P).mul (hc.comp (continuous_const.mul continuous_id)))
  exact hcont.integrable_of_hasCompactSupport ((Hc_hasCompactSupport c).mul_left)

/-- `F(λ|r|) (v*v)(r) = G⁺(r) + G⁺(−r)` with `G⁺(r) = F_b(λr) H_c(r)`. -/
lemma Fker_split (c : ℝ → ℝ) (r : ℝ) :
    Fker P c (P.lam * |r|) * vv P r =
      Fb P.ε₃ (P.lam * r) * Hc P c r + Fb P.ε₃ (P.lam * -r) * Hc P c (-r) := by
  have hl := P.lam_pos
  have he := P.ε₃_pos
  unfold Fker Fb Hc
  rcases lt_trichotomy r 0 with h | h | h
  · have h1 : P.lam * r < 0 := mul_neg_of_pos_of_neg hl h
    have h2 : 0 < P.lam * -r := mul_pos hl (by linarith)
    rw [abs_of_neg h, max_eq_right h1.le, max_eq_left h2.le, vv_even]
    rw [min_eq_left (by linarith : (0 : ℝ) ≤ 1 + 2 * P.ε₃)]
    ring
  · subst h
    simp only [abs_zero, mul_zero, neg_zero, max_self]
    rw [min_eq_left (by linarith : (0 : ℝ) ≤ 1 + 2 * P.ε₃)]
    ring
  · have h1 : 0 < P.lam * r := mul_pos hl h
    have h2 : P.lam * -r < 0 := by nlinarith
    rw [abs_of_pos h, max_eq_left h1.le, max_eq_right h2.le]
    rw [min_eq_left (by linarith : (0 : ℝ) ≤ 1 + 2 * P.ε₃)]
    ring

lemma integral_Fker_vv {c : ℝ → ℝ} (hc : Continuous c) :
    ∫ r, Fker P c (P.lam * |r|) * vv P r = 2 * IF P c := by
  simp_rw [Fker_split c]
  have hi := Gplus_integrable (P := P) hc
  rw [integral_add hi (hi.comp_neg), integral_neg_eq_self (fun r => Fb P.ε₃ (P.lam * r) * Hc P c r)]
  unfold IF; ring

/-- `∫∫ v(s) v(s') F(λ|s − s'|) = ∫ F(λ|r|) (v*v)(r) dr`. -/
lemma double_v_eq {c : ℝ → ℝ} (hc : Continuous c) :
    ∫ s, ∫ s', P.vfun s * P.vfun s' * Fker P c (P.lam * |s - s'|) =
      ∫ r, Fker P c (P.lam * |r|) * vv P r := by
  have hF := Fker_continuous (P := P) hc
  -- inner substitution `s' = s − r`
  have h1 : ∀ s, ∫ s', P.vfun s * P.vfun s' * Fker P c (P.lam * |s - s'|) =
      ∫ r, P.vfun s * P.vfun (s - r) * Fker P c (P.lam * |r|) := by
    intro s
    rw [← integral_sub_left_eq_self (fun s' => P.vfun s * P.vfun s' * Fker P c (P.lam * |s - s'|))
      (μ := volume) s]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only [sub_sub_cancel]
  simp_rw [h1]
  -- Fubini
  set G : ℝ × ℝ → ℝ := fun z => P.vfun z.1 * P.vfun (z.1 - z.2) * Fker P c (P.lam * |z.2|) with hG
  have hGc : Continuous G := by
    simp only [hG]
    exact (((vfun_contDiff P).continuous.comp continuous_fst).mul
      ((vfun_contDiff P).continuous.comp (continuous_fst.sub continuous_snd))).mul
      (hF.comp (continuous_const.mul (continuous_abs.comp continuous_snd)))
  have hGs : HasCompactSupport G := by
    refine HasCompactSupport.intro (K := Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1)
      (isCompact_Icc.prod isCompact_Icc) ?_
    intro z hz
    simp only [hG]
    by_cases h1 : 1 / 2 ≤ |z.1|
    · rw [vfun_zero_of P h1]; ring
    by_cases h2 : 1 / 2 ≤ |z.1 - z.2|
    · rw [vfun_zero_of P h2]; ring
    exfalso
    push Not at h1 h2
    apply hz
    have ha := abs_lt.mp h1
    have hb := abs_lt.mp h2
    refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hGi : Integrable G (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hGc.integrable_of_hasCompactSupport hGs
  have hswap := integral_integral_swap (f := fun s r => G (s, r)) hGi
  simp only [hG] at hswap
  rw [hswap]
  refine integral_congr_ae (Eventually.of_forall fun r => ?_)
  simp only
  rw [integral_mul_const, mul_comm]
  congr 1
  unfold vv
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only
  rw [show s - r = -(r - s) by ring, vfun_even]

/-- **`𝒬_F(f_v) = (b/λ + 2 I_F)/a²`** (proof of Proposition 5.13). -/
theorem Qf_fv_eq {c : ℝ → ℝ} (hc : Continuous c) :
    Qf (fun α => c α * min α (1 + 2 * P.ε₃)) (fun x => P.vfun (x / P.lam) / (P.lam * P.aInt)) =
      (P.bInt / P.lam + 2 * IF P c) / P.aInt ^ 2 := by
  have hl := P.lam_pos
  have ha := aInt_pos P
  rw [Families.Phase4.A.Qf_div]
  have hsq : ∫ x, P.vfun (x / P.lam) ^ 2 = P.lam * P.bInt := by
    have h := Measure.integral_comp_div (fun s => P.vfun s ^ 2) P.lam
    rw [abs_of_pos hl, smul_eq_mul] at h
    exact h
  have hdbl : ∫ x, ∫ y, P.vfun (x / P.lam) * P.vfun (y / P.lam) *
      (c |x - y| * min |x - y| (1 + 2 * P.ε₃)) = P.lam ^ 2 * (2 * IF P c) := by
    have e1 : ∀ x, ∫ y, P.vfun (x / P.lam) * P.vfun (y / P.lam) *
        (c |x - y| * min |x - y| (1 + 2 * P.ε₃)) =
        P.lam * ∫ s', P.vfun (x / P.lam) * P.vfun s' * Fker P c (P.lam * |x / P.lam - s'|) := by
      intro x
      have h := Measure.integral_comp_div
        (fun s' => P.vfun (x / P.lam) * P.vfun s' * Fker P c (P.lam * |x / P.lam - s'|)) P.lam
      rw [abs_of_pos hl, smul_eq_mul] at h
      rw [← h]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [Fker]
      have : P.lam * |x / P.lam - y / P.lam| = |x - y| := by
        rw [← abs_of_pos hl, ← abs_mul, abs_of_pos hl, mul_sub, mul_div_cancel₀ _ hl.ne',
          mul_div_cancel₀ _ hl.ne']
      rw [this]
    simp_rw [e1]
    rw [integral_const_mul]
    have h := Measure.integral_comp_div
      (fun s => ∫ s', P.vfun s * P.vfun s' * Fker P c (P.lam * |s - s'|)) P.lam
    rw [abs_of_pos hl, smul_eq_mul] at h
    rw [h, double_v_eq hc, integral_Fker_vv hc]
    ring
  unfold Qf
  rw [hsq, hdbl]
  field_simp

end QfIdentity

/-! ### A fixed bump, for `∑ b_n² ≪ Lℓ` -/

section Bump

/-- `Bmp = 1` on `[0, 3]`, `= 0` off `(−1, 4)`, smooth, `0 ≤ Bmp ≤ 1`. -/
def Bmp (x : ℝ) : ℝ := ramp (-1) 0 x * ramp (-4) (-3) (-x)

lemma Bmp_contDiff : ContDiff ℝ ∞ Bmp :=
  (ramp_contDiff _ _).mul ((ramp_contDiff _ _).comp contDiff_neg)

lemma Bmp_nonneg (x : ℝ) : 0 ≤ Bmp x := mul_nonneg (ramp_nonneg _ _ _) (ramp_nonneg _ _ _)

lemma Bmp_le_one (x : ℝ) : Bmp x ≤ 1 := by
  unfold Bmp
  have := ramp_le_one (-1) 0 x
  have := ramp_le_one (-4) (-3) (-x)
  have := ramp_nonneg (-1) 0 x
  have := ramp_nonneg (-4) (-3) (-x)
  nlinarith

lemma Bmp_one {x : ℝ} (h0 : 0 ≤ x) (h3 : x ≤ 3) : Bmp x = 1 := by
  unfold Bmp
  rw [ramp_of_ge (by norm_num) h0, ramp_of_ge (by norm_num) (by linarith)]; ring

lemma Bmp_hasCompactSupport : HasCompactSupport Bmp := by
  refine HasCompactSupport.intro (K := Set.Icc (-1 : ℝ) 4) isCompact_Icc ?_
  intro x hx
  unfold Bmp
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  rcases hx with h | h
  · rw [ramp_of_le (by norm_num) h.le]; ring
  · rw [ramp_of_le (a := -4) (b := -3) (by norm_num) (by linarith)]; ring

lemma Bmp_iteratedDeriv_bounded (i : ℕ) : ∃ D : ℝ, 0 ≤ D ∧ ∀ x, |iteratedDeriv i Bmp x| ≤ D := by
  have hcont : Continuous (iteratedFDeriv ℝ i Bmp) :=
    Bmp_contDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨D, hD⟩ := hcont.bounded_above_of_compact_support (Bmp_hasCompactSupport.iteratedFDeriv i)
  refine ⟨max D 0, le_max_right _ _, fun σ => ?_⟩
  rw [← Real.norm_eq_abs, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact (hD σ).trans (le_max_left _ _)

lemma Bmp_integrable : Integrable Bmp :=
  Bmp_contDiff.continuous.integrable_of_hasCompactSupport Bmp_hasCompactSupport

/-- `h₁(y) = Bmp(y/L)`. -/
def hOne (P : PrimeSetup) (Q y : ℝ) : ℝ := Bmp (y / P.L Q)

lemma hOne_contDiff (Q : ℝ) : ContDiff ℝ ∞ (hOne P Q) :=
  Bmp_contDiff.comp (contDiff_id.div_const _)

lemma hOne_nonneg (Q y : ℝ) : 0 ≤ hOne P Q y := Bmp_nonneg _

lemma hOne_le (Q y : ℝ) : hOne P Q y ≤ 1 := Bmp_le_one _

lemma hOne_integrable {Q : ℝ} (hQ : 1 < Q) : Integrable (hOne P Q) :=
  Bmp_integrable.comp_div (P.L_pos hQ).ne'

lemma hOne_deriv_bound (i : ℕ) {D : ℝ} (hD : ∀ x, |iteratedDeriv i Bmp x| ≤ D) {Q : ℝ}
    (hL1 : 1 ≤ P.L Q) (y : ℝ) : |iteratedDeriv i (hOne P Q) y| ≤ D * 1 := by
  have hL0 : 0 < P.L Q := by linarith
  have hdiff : ContDiff ℝ i Bmp := Bmp_contDiff.of_le (by exact_mod_cast le_top)
  have e : hOne P Q = fun y => Bmp ((P.L Q)⁻¹ * y) := by
    funext y; unfold hOne; rw [div_eq_inv_mul]
  rw [e, iteratedDeriv_comp_const_mul hdiff, abs_mul, mul_one]
  have hinv : |(P.L Q)⁻¹ ^ i| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hL1)
  calc |(P.L Q)⁻¹ ^ i| * |iteratedDeriv i Bmp ((P.L Q)⁻¹ * y)| ≤ 1 * D :=
        mul_le_mul hinv (hD _) (abs_nonneg _) zero_le_one
    _ = D := one_mul D

lemma hOne_one {Q : ℝ} (hQ : 1 < Q) {n : ℕ} (hn : n ∈ P.range Q) : hOne P Q (Real.log n) = 1 := by
  have hL := P.L_pos hQ
  obtain ⟨hl0, hl⟩ := SC.log_le_of_mem_range P hL.le hn
  unfold hOne
  apply Bmp_one (div_nonneg hl0 hL.le)
  rw [div_le_iff₀ hL]; linarith

lemma integral_hOne_le {Q : ℝ} (hQ : 1 < Q) :
    ∫ s, ell Q * Fb P.ε₃ (s / ell Q) * hOne P Q s ≤
      ell Q * (1 + 2 * P.ε₃) * (P.L Q * ∫ x, Bmp x) := by
  have hL := P.L_pos hQ
  have hℓ : 0 < ell Q := Real.log_pos hQ
  have hi := hOne_integrable (P := P) hQ
  have h2 : Integrable (fun s => ell Q * (1 + 2 * P.ε₃) * hOne P Q s) := hi.const_mul _
  have h1 : Integrable (fun s => ell Q * Fb P.ε₃ (s / ell Q) * hOne P Q s) := by
    refine h2.mono' ?_ (Eventually.of_forall fun s => ?_)
    · have hc : Continuous (fun s => ell Q * Fb P.ε₃ (s / ell Q) * hOne P Q s) := by
        unfold Fb
        exact (continuous_const.mul (((continuous_id.div_const _).max continuous_const).min
          continuous_const)).mul (hOne_contDiff Q).continuous
      exact hc.aestronglyMeasurable
    · have hF0 := Families.Phase3.C.Fb_nonneg P.ε₃ (s / ell Q) P.ε₃_pos.le
      have hF1 := Families.Phase3.C.Fb_le P.ε₃ (s / ell Q)
      have h0 := hOne_nonneg (P := P) Q s
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hF1 hℓ.le) h0
  calc ∫ s, ell Q * Fb P.ε₃ (s / ell Q) * hOne P Q s
      ≤ ∫ s, ell Q * (1 + 2 * P.ε₃) * hOne P Q s := by
        refine integral_mono h1 h2 fun s => ?_
        have hF1 := Families.Phase3.C.Fb_le P.ε₃ (s / ell Q)
        have h0 := hOne_nonneg (P := P) Q s
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hF1 hℓ.le) h0
    _ = ell Q * (1 + 2 * P.ε₃) * (P.L Q * ∫ x, Bmp x) := by
        rw [integral_const_mul]
        congr 1
        have h := Measure.integral_comp_div Bmp (P.L Q)
        rw [abs_of_pos hL, smul_eq_mul] at h
        exact h

end Bump

end Families.Ported.Second
