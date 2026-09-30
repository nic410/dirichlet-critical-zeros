/-
**proof of `assemblyLimit_Statement`** (`Families.Main`), the limit part of the
proofs of `thm:conditional` and `thm:main` (§7.3, `sec:assembly`).

Given `0 < a₀ < A₀`, `1 ≤ C ≤ C_max` and `η' > 0`:

1. choose an admissible `f` with `𝒬_{F_C}(f) < inf 𝒬_{F_C} + η'/4` (the infimum in `p(C)`; the
   admissible class is nonempty: `admissible_half`);
2. `lem:windows` (`exists_window`): a smooth even `φ` supported in `[−b, b]`, `b < 1`, with
   `𝒬_{F_C}(φ²/∫φ²) ≤ 𝒬_{F_C}(f) + η'/4`; put `λ = 1 + b < 2`, `ψ(s) = φ(λs)` (so
   `supp ψ ⊂ [−b/λ, b/λ]`, `b/λ < 1/2`, and `f_v = φ²/∫φ²` exactly);
3. `ε₁ = (2 − λ)/(1 + λ)` (so `λ(1+ε₁) = 2 − ε₁`), the cut-offs `Υ₀ = upsilon0 ε₁`, `ψ_j = dyadic j`;
4. `θ, ε₃, ε` small in terms of `η'`, `C`, `C_max` and `M = sup f_v`: then **for every** profile
   `C̃` as in the statement, `F = C̃ · min(·, 1+2ε₃)` satisfies `F ≤ F_C + 2Cε₃ + 2C_max 1_{(1−2ε,1+2ε)}`
   on `[0, ∞)`, so `𝒬_F(f_v) ≤ 𝒬_{F_C}(f_v) + 2Cε₃ + 16 C_max M ε` (`Qf_le_of_band`). This explicit bound
   replaces the dominated convergence in the proof of Theorem 5.16 and gives the uniformity in `C̃`.
-/
import Families.Main
import Families.Phase4.A.Windows
import Families.Phase4.A.Setup

noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace Families.Phase4.A

/-! ### The admissible class is nonempty -/

/-- `f = ½ 1_{[−1,1]}` is admissible. -/
lemma admissible_half : AdmissibleWindow ((Set.Icc (-1 : ℝ) 1).indicator (fun _ => (1 / 2 : ℝ))) where
  nonneg x := Set.indicator_nonneg (fun _ _ => by norm_num) x
  even x := by
    have h : (-x ∈ Set.Icc (-1 : ℝ) 1) ↔ (x ∈ Set.Icc (-1 : ℝ) 1) := by
      simp only [Set.mem_Icc]
      constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
    simp only [Set.indicator_apply, h]
  supp x hx := Set.mem_of_indicator_ne_zero hx
  memL2 := memLp_indicator_const 2 measurableSet_Icc _ (Or.inr measure_Icc_lt_top.ne)
  integral_eq_one := by
    rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le (by norm_num)]
    norm_num

lemma Qf_FC_nonneg {C : ℝ} (hC : 1 ≤ C) {f : ℝ → ℝ} (hf : AdmissibleWindow f) :
    0 ≤ Qf (FC C) f :=
  Qf_nonneg_of (fun α hα => (FC_bounds hC α hα).1) hf.nonneg

/-! ### The kernel comparison for a band profile -/

/-- For a profile `C̃` with values in `[1, C_max]`, `= 1` on `(−∞, 1−2ε]`, `= C` on `[1+2ε, ∞)`, and
`0 < ε₃ ≤ 1/8`: `C̃(α) min(α, 1+2ε₃) ≤ F_C(α) + 2Cε₃ + 2C_max 1_{(1−2ε,1+2ε)}(α)` for `α ≥ 0`. -/
lemma profile_kernel_le {C Cmax ε ε₃ : ℝ} (hC : 1 ≤ C) (hCmax : C ≤ Cmax) (hε : 0 ≤ ε)
    (hε₃ : 0 < ε₃) (hε₃' : ε₃ ≤ 1 / 8) {Ct : ℝ → ℝ} (hrange : ∀ α, 1 ≤ Ct α ∧ Ct α ≤ Cmax)
    (hbelow : ∀ α, α ≤ 1 - 2 * ε → Ct α = 1) (habove : ∀ α, 1 + 2 * ε ≤ α → Ct α = C)
    (α : ℝ) (hα : 0 ≤ α) :
    Ct α * min α (1 + 2 * ε₃) ≤ FC C α + 2 * C * ε₃ +
      2 * Cmax * (Set.Ioo (1 - 2 * ε) (1 + 2 * ε)).indicator (fun _ => (1 : ℝ)) α := by
  have hFC0 : 0 ≤ FC C α := (FC_bounds hC α hα).1
  have hI0 : 0 ≤ (Set.Ioo (1 - 2 * ε) (1 + 2 * ε)).indicator (fun _ => (1 : ℝ)) α :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hCε : 0 ≤ 2 * C * ε₃ := by positivity
  have hmin0 : 0 ≤ min α (1 + 2 * ε₃) := le_min hα (by linarith)
  have hmin1 : min α (1 + 2 * ε₃) ≤ 1 + 2 * ε₃ := min_le_right _ _
  by_cases h1 : α ≤ 1 - 2 * ε
  · have hα1 : α ≤ 1 := by linarith
    rw [hbelow α h1, one_mul, min_eq_left (by linarith)]
    unfold FC; rw [if_pos hα1]
    have : 0 ≤ 2 * Cmax * (Set.Ioo (1 - 2 * ε) (1 + 2 * ε)).indicator (fun _ => (1 : ℝ)) α :=
      mul_nonneg (by linarith) hI0
    linarith
  · push Not at h1
    by_cases h2 : 1 + 2 * ε ≤ α
    · rw [habove α h2]
      have hα1 : ¬ α ≤ 1 := by
        intro h; linarith
      unfold FC; rw [if_neg hα1]
      have : C * min α (1 + 2 * ε₃) ≤ C * (1 + 2 * ε₃) :=
        mul_le_mul_of_nonneg_left hmin1 (by linarith)
      have : 0 ≤ 2 * Cmax * (Set.Ioo (1 - 2 * ε) (1 + 2 * ε)).indicator (fun _ => (1 : ℝ)) α :=
        mul_nonneg (by linarith) hI0
      linarith
    · push Not at h2
      have hI : (Set.Ioo (1 - 2 * ε) (1 + 2 * ε)).indicator (fun _ => (1 : ℝ)) α = 1 :=
        Set.indicator_of_mem (show α ∈ Set.Ioo (1 - 2 * ε) (1 + 2 * ε) from ⟨h1, h2⟩) _
      rw [hI, mul_one]
      have : Ct α * min α (1 + 2 * ε₃) ≤ Cmax * (1 + 2 * ε₃) :=
        mul_le_mul (hrange α).2 hmin1 hmin0 (by linarith [(hrange α).1])
      nlinarith

/-! ### The fixed data built from a window -/

/-- The fixed data `P` built from a window `φ` supported in `[−b, b]` (`0 ≤ b < 1`): `λ = 1 + b`,
`ε₁ = (1 − b)/(2 + b)` (so that `λ(1 + ε₁) = 2 − ε₁`), `ψ(s) = φ(λs)`, `Υ₀ = upsilon0 ε₁`,
`ψ_j = dyadic j`. -/
def mkSetup (a0 A0 θ ε₃ b : ℝ) (φ : ℝ → ℝ) (ha0 : 0 < a0) (hA0 : a0 < A0) (hθ : 0 < θ)
    (hθ' : θ < 1 / 4) (hε₃ : 0 < ε₃) (hε₃' : ε₃ < 1 / 4) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hφs : ContDiff ℝ ∞ φ) (hφe : ∀ x, φ (-x) = φ x) (hφsupp : ∀ x, b < |x| → φ x = 0)
    (hφ0 : φ 0 ≠ 0) : PrimeSetup where
  a0 := a0
  A0 := A0
  lam := 1 + b
  ε₁ := (1 - b) / (2 + b)
  θ := θ
  ψ := fun s => φ ((1 + b) * s)
  ε₃ := ε₃
  Υ₀ := upsilon0 ((1 - b) / (2 + b))
  ψj := dyadic
  a0_pos := ha0
  a0_lt := hA0
  lam_pos := by linarith
  lam_lt := by linarith
  ε₁_pos := div_pos (by linarith) (by linarith)
  lam_ε₁ := by
    have h : (2 + b) ≠ 0 := by linarith
    rw [show (1 + b) * (1 + (1 - b) / (2 + b)) = 2 - (1 - b) / (2 + b) by field_simp; ring]
  θ_pos := hθ
  θ_lt := hθ'
  ψ_smooth := hφs.comp (contDiff_const.mul contDiff_id)
  ψ_even := fun x => by simp only [mul_neg, hφe]
  ψ_supp := by
    refine ⟨b / (1 + b), ?_, fun x hx => hφsupp _ ?_⟩
    · rw [div_lt_iff₀ (by linarith)]; linarith
    · rw [div_lt_iff₀ (by linarith)] at hx
      rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < 1 + b)]
      linarith
  ψ_ne := ⟨0, by simpa using hφ0⟩
  ε₃_pos := hε₃
  ε₃_lt := hε₃'
  Υ₀_smooth := upsilon0_contDiff _
  Υ₀_range := upsilon0_range _
  Υ₀_one := fun _ _ hy => upsilon0_one (div_pos (by linarith) (by linarith)) hy
  Υ₀_zero := fun _ hy => upsilon0_zero (div_pos (by linarith) (by linarith)) hy
  ψj_smooth := dyadic_contDiff
  ψj_nonneg := dyadic_nonneg
  ψj_supp := dyadic_supp
  ψj_sum := fun _ hy => dyadic_sum hy
  ψj_deriv := dyadic_deriv

/-- For `mkSetup`, the paper's `f_v(x) = v(x/λ)/(λa)` is exactly `φ(x)²/∫φ²`. -/
lemma mkSetup_fv (a0 A0 θ ε₃ b : ℝ) (φ : ℝ → ℝ) (ha0 : 0 < a0) (hA0 : a0 < A0) (hθ : 0 < θ)
    (hθ' : θ < 1 / 4) (hε₃ : 0 < ε₃) (hε₃' : ε₃ < 1 / 4) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (hφs : ContDiff ℝ ∞ φ) (hφe : ∀ x, φ (-x) = φ x) (hφsupp : ∀ x, b < |x| → φ x = 0)
    (hφ0 : φ 0 ≠ 0) :
    let P := mkSetup a0 A0 θ ε₃ b φ ha0 hA0 hθ hθ' hε₃ hε₃' hb0 hb1 hφs hφe hφsupp hφ0
    (fun x => P.vfun (x / P.lam) / (P.lam * P.aInt)) = fun x => φ x ^ 2 / ∫ y, φ y ^ 2 := by
  intro P
  funext x
  have hl : (1 + b) ≠ 0 := by linarith
  have hlpos : (0 : ℝ) < 1 + b := by linarith
  have hint : ∫ s, φ ((1 + b) * s) ^ 2 = (1 + b)⁻¹ * ∫ y, φ y ^ 2 := by
    rw [Measure.integral_comp_mul_left (fun y => φ y ^ 2) (1 + b), abs_of_pos (inv_pos.2 hlpos),
      smul_eq_mul]
  show φ ((1 + b) * (x / (1 + b))) ^ 2 / ((1 + b) * ∫ s, φ ((1 + b) * s) ^ 2) = _
  rw [mul_div_cancel₀ x hl, hint, mul_inv_cancel_left₀ hl]

/-! ### The theorem -/

/-- **`assemblyLimit`** (`main.tex` §7.3; (a) target). -/
theorem assemblyLimit_proof : assemblyLimit_Statement := by
  intro a0 A0 ha0 hA0 C Cmax hC hCmax η' hη'
  have hη4 : 0 < η' / 4 := by positivity
  have hC0 : 0 < C := by linarith
  have hCm0 : 0 < Cmax := by linarith
  -- 1. a near-optimal admissible `f`
  have hne : (Qf (FC C) '' {f | AdmissibleWindow f}).Nonempty := ⟨_, _, admissible_half, rfl⟩
  obtain ⟨_, ⟨f, hf, rfl⟩, hfQ⟩ := exists_lt_of_csInf_lt hne (lt_add_of_pos_right _ hη4)
  -- 2. `lem:windows`
  obtain ⟨φ, b, hb0, hb1, hφs, hφe, hφsupp, hφ0, hφQ⟩ := exists_window hC hf hη4
  have hφc := hφs.continuous
  have hφ2s : ∀ x, b < |x| → φ x ^ 2 = 0 := fun x hx => by rw [hφsupp x hx]; ring
  have hφ2i : Integrable (fun x => φ x ^ 2) := integrable_of_continuous_supp (hφc.pow 2) hφ2s
  have hcpos : 0 < ∫ y, φ y ^ 2 :=
    integral_pos_of_integrable_nonneg_nonzero (hφc.pow 2) hφ2i (fun x => sq_nonneg (φ x))
      (pow_ne_zero 2 hφ0)
  obtain ⟨M₀, hM₀⟩ := hφc.bounded_above_of_compact_support
    (HasCompactSupport.intro (isCompact_Icc (a := -b) (b := b))
      fun x hx => hφsupp x (lt_abs_of_notMem_Icc hx))
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = M₀ ^ 2 / ∫ y, φ y ^ 2 := ⟨_, rfl⟩
  have hfvM : ∀ x, φ x ^ 2 / (∫ y, φ y ^ 2) ≤ M := by
    intro x
    rw [hM]
    refine div_le_div_of_nonneg_right ?_ hcpos.le
    have h1 := hM₀ x
    rw [Real.norm_eq_abs] at h1
    rw [← sq_abs (φ x)]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hfv0 : ∀ x, 0 ≤ φ x ^ 2 / (∫ y, φ y ^ 2) := fun x => div_nonneg (sq_nonneg _) hcpos.le
  have hM0 : 0 ≤ M := (hfv0 0).trans (hfvM 0)
  have hfvi : Integrable (fun x => φ x ^ 2 / (∫ y, φ y ^ 2)) := hφ2i.div_const _
  have hfv1 : ∫ x, φ x ^ 2 / (∫ y, φ y ^ 2) = 1 := by
    rw [integral_div, div_self hcpos.ne']
  -- 3. the parameters `θ, ε₃, ε`
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = min (1 / 8) (η' / 64) := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by rw [hθ]; exact lt_min (by norm_num) (by positivity)
  have hθ8 : θ ≤ 1 / 8 := by rw [hθ]; exact min_le_left _ _
  have hθη : 8 * θ ≤ η' / 8 := by
    have : θ ≤ η' / 64 := by rw [hθ]; exact min_le_right _ _
    linarith
  obtain ⟨ε₃, hε₃⟩ : ∃ ε₃ : ℝ, ε₃ = min (1 / 8) (η' / (16 * C)) := ⟨_, rfl⟩
  have hε₃0 : 0 < ε₃ := by rw [hε₃]; exact lt_min (by norm_num) (by positivity)
  have hε₃8 : ε₃ ≤ 1 / 8 := by rw [hε₃]; exact min_le_left _ _
  have hε₃η : 2 * C * ε₃ ≤ η' / 8 := by
    have h1 : ε₃ ≤ η' / (16 * C) := by rw [hε₃]; exact min_le_right _ _
    have h2 : ε₃ * (16 * C) ≤ η' := by rwa [le_div_iff₀ (by positivity)] at h1
    linarith
  have hε₁0 : 0 < (1 - b) / (2 + b) := div_pos (by linarith) (by linarith)
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ,
      ε = min (1 / 8) (min ((1 - b) / (2 + b) / 8) (η' / (128 * Cmax * (M + 1)))) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by
    rw [hε]; exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hε8 : ε ≤ 1 / 8 := by rw [hε]; exact min_le_left _ _
  have hεε₁ : ε ≤ (1 - b) / (2 + b) / 8 := by
    rw [hε]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hεη : 16 * Cmax * M * ε ≤ η' / 8 := by
    have h1 : ε ≤ η' / (128 * Cmax * (M + 1)) := by
      rw [hε]; exact (min_le_right _ _).trans (min_le_right _ _)
    have h2 : ε * (128 * Cmax * (M + 1)) ≤ η' := by rwa [le_div_iff₀ (by positivity)] at h1
    nlinarith
  -- 4. the fixed data
  refine ⟨mkSetup a0 A0 θ ε₃ b φ ha0 hA0 hθ0 (by linarith) hε₃0 (by linarith) hb0 hb1 hφs hφe
    hφsupp hφ0, ε, rfl, rfl, hε0, by linarith, show ε < (1 - b) / (2 + b) / 4 by linarith,
    fun Ct hCt hrange hbelow habove => ?_⟩
  -- the certified value, with `f_v = φ²/∫φ²`
  have hcert : (mkSetup a0 A0 θ ε₃ b φ ha0 hA0 hθ0 (by linarith) hε₃0 (by linarith) hb0 hb1 hφs
      hφe hφsupp hφ0).certValue Ct = 2 - 8 * θ - (1 - 2 * θ) *
        Qf (fun α => Ct α * min α (1 + 2 * ε₃)) (fun x => φ x ^ 2 / ∫ y, φ y ^ 2) := by
    unfold PrimeSetup.certValue
    rw [mkSetup_fv]
    rfl
  rw [hcert]
  -- the kernel comparison, uniformly in `C̃`
  have hFm : Measurable (fun α => Ct α * min α (1 + 2 * ε₃)) :=
    (hCt.mul (continuous_id.min continuous_const)).measurable
  have hFK : ∀ α, 0 ≤ α → |Ct α * min α (1 + 2 * ε₃)| ≤ 2 * Cmax := by
    intro α hα
    have hmin0 : 0 ≤ min α (1 + 2 * ε₃) := le_min hα (by linarith)
    have hmin1 : min α (1 + 2 * ε₃) ≤ 1 + 2 * ε₃ := min_le_right _ _
    rw [abs_of_nonneg (mul_nonneg (by linarith [(hrange α).1]) hmin0)]
    have := mul_le_mul (hrange α).2 hmin1 hmin0 (by linarith [(hrange α).1])
    nlinarith
  have hGK : ∀ α, 0 ≤ α → |FC C α| ≤ 2 * Cmax := by
    intro α hα
    rw [abs_of_nonneg (FC_bounds hC α hα).1]
    linarith [(FC_bounds hC α hα).2]
  have hband := Qf_le_of_band hFm (measurable_FC C) hFK hGK hfv0 hfvM hfvi hfv1
    (a := 2 * C * ε₃) (k := 2 * Cmax) (by linarith) hε0.le
    (profile_kernel_le hC hCmax hε0.le hε₃0 hε₃8 hrange hbelow habove)
  have hQF0 : 0 ≤ Qf (fun α => Ct α * min α (1 + 2 * ε₃)) (fun x => φ x ^ 2 / ∫ y, φ y ^ 2) :=
    Qf_nonneg_of (fun α hα => mul_nonneg (by linarith [(hrange α).1]) (le_min hα (by linarith)))
      hfv0
  -- conclusion
  unfold pC
  have h1 : (1 - 2 * θ) * Qf (fun α => Ct α * min α (1 + 2 * ε₃)) (fun x => φ x ^ 2 / ∫ y, φ y ^ 2)
      ≤ Qf (fun α => Ct α * min α (1 + 2 * ε₃)) (fun x => φ x ^ 2 / ∫ y, φ y ^ 2) := by
    nlinarith
  linarith

end Families.Phase4.A
