/-
# Theorem 1.4(a), package V: the assembly limit at support `β(κc)` (§9.4 (a)–(e), `lem:windowsH`)
— proved, no `sorry`

A port of `Families.Phase4.A.assemblyLimit_proof` from support `2` to support `β = β(κc) ∈ (1, 2)`.

1. choose `f` admissible at support `β` with `𝒬_{F_C}(f) < inf + η'/4` (the class contains `unitW`);
2. **`lem:windowsH`** (`exists_windowB`): a smooth even `φ` supported in `[−b, b]` with `b < β/2` and
   `𝒬_{F_C}(φ²/∫φ²) ≤ 𝒬_{F_C}(f) + η'/4`. This is `Families.Phase4.A.exists_window` with the truncation
   radius `1` replaced by `β/2` (`exists_tail_smallR`); since `β ≤ 2`, `f` is also a
   `Families.AdmissibleWindow`, so the families window estimates (`window_close`, `Qf_normalised_le`)
   apply verbatim;
3. the fixed data (`mkSetupH`): `λ = b + β/2` (so `2b < λ < β`), `ψ(s) = φ(λs)` (supported in
   `[−b/λ, b/λ]`, `b/λ < 1/2`), `ε₁ = min(1/8, (β − λ)/(1 + λ))` (so `λ(1+ε₁) ≤ β − ε₁`), the cut-offs
   `Υ₀ = upsilon0 ε₁`, `ψ_j = dyadic j` of the families package; `f_v = φ²/∫φ²` exactly (`mkSetupH_fv`);
4. `θ, ε₃, ε` small (now also `ε ≤ 1/(8(1+κc))`), and the uniform kernel comparison
   `Families.Phase4.A.Qf_le_of_band` with `Families.Phase4.A.profile_kernel_le`, exactly as in the
   families proof.
-/
import FamiliesH.V.Basic

noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace Families.Hybrid.V

open Families

/-! ### Truncation at radius `R` -/

/-- **Truncation** (dominated convergence; `Families.Phase4.A.exists_tail_small` with radius `R`). If
`f² ∈ L¹` and `f = 0` off `[−R, R]`, then for every `δ > 0` there is `b ∈ (0, R)` with
`∫_{|x| > b} f² ≤ δ`. -/
lemma exists_tail_smallR {f : ℝ → ℝ} (hf : Integrable (fun x => f x ^ 2)) {R : ℝ} (hR : 0 < R)
    (hs : ∀ x, R < |x| → f x = 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ b : ℝ, 0 < b ∧ b < R ∧
      ∫ x, {x : ℝ | b < |x|}.indicator (fun x => f x ^ 2) x ≤ δ := by
  set bn : ℕ → ℝ := fun n => R - R / ((n : ℝ) + 2) with hbn
  set Fn : ℕ → ℝ → ℝ := fun n => {x : ℝ | bn n < |x|}.indicator (fun x => f x ^ 2) with hFn
  have hlim : Tendsto (fun n => ∫ x, Fn n x) atTop (𝓝 (∫ _x : ℝ, (0 : ℝ))) := by
    refine tendsto_integral_of_dominated_convergence (fun x => f x ^ 2)
      (fun n => hf.aestronglyMeasurable.indicator (Families.Phase4.A.measurableSet_lt_abs _)) hf
      (fun n => Eventually.of_forall fun x => ?_) ?_
    · refine (norm_indicator_le_norm_self _ _).trans (le_of_eq ?_)
      exact Real.norm_of_nonneg (sq_nonneg _)
    · have hc : ({R, -R} : Set ℝ).Countable := (Set.toFinite _).countable
      filter_upwards [hc.ae_notMem volume] with x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
      have hx1 : |x| ≠ R := by
        intro h
        rcases abs_eq hR.le |>.1 h with h | h
        · exact hx.1 h
        · exact hx.2 h
      rcases lt_or_gt_of_ne hx1 with hlt | hgt
      · have hpos : 0 < (R - |x|) / R := div_pos (sub_pos.2 hlt) hR
        obtain ⟨N, hN⟩ := exists_nat_one_div_lt hpos
        refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
        have hn' : (N : ℝ) + 1 ≤ (n : ℝ) + 2 := by
          have : (N : ℝ) ≤ n := by exact_mod_cast hn
          linarith
        have h1 : 1 / ((n : ℝ) + 2) ≤ 1 / ((N : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) hn'
        have h2 : R / ((n : ℝ) + 2) < R - |x| := by
          have h3 : R / ((n : ℝ) + 2) = R * (1 / ((n : ℝ) + 2)) := by ring
          have h4 : R * (1 / ((n : ℝ) + 2)) ≤ R * (1 / ((N : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left h1 hR.le
          have h5 : R * (1 / ((N : ℝ) + 1)) < R * ((R - |x|) / R) := mul_lt_mul_of_pos_left hN hR
          have h6 : R * ((R - |x|) / R) = R - |x| := by field_simp
          linarith
        have hmem : x ∉ {x : ℝ | bn n < |x|} := by
          simp only [Set.mem_ofPred_eq, not_lt, hbn]
          linarith
        simp only [hFn, Set.indicator_of_notMem hmem]
      · refine tendsto_const_nhds.congr (fun n => ?_)
        rw [eq_comm]
        simp only [hFn]
        rw [Set.indicator_apply]
        split_ifs <;> simp [hs x hgt]
  rw [integral_zero] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hδ)).exists
  have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  refine ⟨bn n, ?_, ?_, hn.le⟩
  · simp only [hbn]
    have h1 : R / ((n : ℝ) + 2) ≤ R / 2 :=
      div_le_div_of_nonneg_left hR.le (by norm_num) (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
    linarith
  · simp only [hbn]
    have : 0 < R / ((n : ℝ) + 2) := by positivity
    linarith

/-! ### `lem:windowsH` -/

/-- **`lem:windowsH`** (Lemma 9.23). For `f` admissible at support `β ∈ (0, 2]`, `C ≥ 1` and `η > 0`
there are `0 ≤ b < β/2` and a smooth even `φ`, supported in `[−b, b]`, `φ(0) ≠ 0`, with
`𝒬_{F_C}(φ²/∫φ²) ≤ 𝒬_{F_C}(f) + η`. -/
theorem exists_windowB {C : ℝ} (hC : 1 ≤ C) {β : ℝ} (hβ0 : 0 < β) (hβ2 : β ≤ 2) {f : ℝ → ℝ}
    (hf : AdmissibleWindowB β f) {η : ℝ} (hη : 0 < η) :
    ∃ (φ : ℝ → ℝ) (b : ℝ), 0 ≤ b ∧ b < β / 2 ∧ ContDiff ℝ ∞ φ ∧ (∀ x, φ (-x) = φ x) ∧
      (∀ x, b < |x| → φ x = 0) ∧ φ 0 ≠ 0 ∧
      Qf (FC C) (fun x => φ x ^ 2 / ∫ y, φ y ^ 2) ≤ Qf (FC C) f + η := by
  have hf' : AdmissibleWindow f := admissibleB_window hβ2 hf
  have hfL2 := hf.memL2
  have hf2 : Integrable (fun x => f x ^ 2) := hfL2.integrable_sq
  have hfm : AEStronglyMeasurable f := hfL2.aestronglyMeasurable
  have hsfR := admissibleB_supp hf
  have hFb := Families.Phase4.A.FC_bounds hC
  have hq0 : 0 ≤ Qf (FC C) f :=
    Families.Phase4.A.Qf_nonneg_of (fun α hα => (hFb α hα).1) hf.nonneg
  have hB0 : 0 ≤ ∫ x, f x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hκ0 := Families.Phase4.A.kappa_pos (by linarith : (0 : ℝ) ≤ C) hB0
  have hden : 0 < Families.Phase4.A.kappa C (∫ x, f x ^ 2) + 3 * (Qf (FC C) f + η) := by
    positivity
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = min (1 / 4)
      (η / (Families.Phase4.A.kappa C (∫ x, f x ^ 2) + 3 * (Qf (FC C) f + η))) := ⟨_, rfl⟩
  have hd0 : 0 < d := by rw [hd]; exact lt_min (by norm_num) (div_pos hη hden)
  have hd14 : d ≤ 1 / 4 := by rw [hd]; exact min_le_left _ _
  have hdη : d * (Families.Phase4.A.kappa C (∫ x, f x ^ 2) + 3 * (Qf (FC C) f + η)) ≤ η := by
    have h1 : d ≤ η / (Families.Phase4.A.kappa C (∫ x, f x ^ 2) + 3 * (Qf (FC C) f + η)) := by
      rw [hd]; exact min_le_right _ _
    calc d * (Families.Phase4.A.kappa C (∫ x, f x ^ 2) + 3 * (Qf (FC C) f + η))
        ≤ η / (Families.Phase4.A.kappa C (∫ x, f x ^ 2) + 3 * (Qf (FC C) f + η)) *
            (Families.Phase4.A.kappa C (∫ x, f x ^ 2) + 3 * (Qf (FC C) f + η)) :=
          mul_le_mul_of_nonneg_right h1 hden.le
      _ = η := div_mul_cancel₀ _ hden.ne'
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = d / 4 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  -- truncation at radius `β/2`
  obtain ⟨b₀, hb₀0, hb₀1, htail⟩ := exists_tail_smallR hf2 (by linarith : (0 : ℝ) < β / 2) hsfR
    (pow_pos hδ0 2)
  -- smooth approximation (Mathlib: smooth compactly supported functions are dense in `L²`)
  obtain ⟨g, hgcs, hgs, hgle⟩ := hfL2.exist_eLpNorm_sub_le (by norm_num) (by norm_num) hδ0
  have hgc : Continuous g := hgs.continuous
  have hgL2 : MemLp g 2 := hgc.memLp_of_hasCompactSupport hgcs
  have hfg : ∫ x, (f x - g x) ^ 2 ≤ δ ^ 2 :=
    Families.Phase4.A.integral_sq_le_of_eLpNorm_le (hfL2.sub hgL2) hδ0.le hgle
  have hfgi : Integrable (fun x => (f x - g x) ^ 2) := (hfL2.sub hgL2).integrable_sq
  -- symmetrisation
  obtain ⟨hfgsi, hfgs⟩ := Families.Phase4.A.integral_sq_sym_le hf.even hfm hgc hfgi
  -- the window
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = (β / 2 + b₀) / 2 := ⟨_, rfl⟩
  have hb₀b : b₀ < b := by rw [hbdef]; linarith
  have hbβ : b < β / 2 := by rw [hbdef]; linarith
  have hb1 : b < 1 := by linarith
  obtain ⟨hLi, hint⟩ := Families.Phase4.A.window_close hf' hb₀0.le hb₀b hb1 hδ0 hgs hfgsi
    (hfgs.trans hfg) htail
  have hud : ∫ x, (Families.Phase4.A.window b₀ b δ g x ^ 2 - f x) ^ 2 ≤ d ^ 2 := by
    have : 12 * δ ^ 2 ≤ d ^ 2 := by rw [hδ]; nlinarith
    linarith
  refine ⟨Families.Phase4.A.window b₀ b δ g, b, by linarith, hbβ,
    Families.Phase4.A.window_contDiff hδ0 hgs, Families.Phase4.A.window_even b₀ b δ g,
    fun x hx => Families.Phase4.A.window_supp g hb₀0.le hb₀b hx,
    Families.Phase4.A.window_zero_ne g hb₀0.le hb₀b hδ0, ?_⟩
  exact Families.Phase4.A.Qf_normalised_le hC hf' (Families.Phase4.A.window_contDiff hδ0 hgs).continuous
    hb1 (fun x hx => Families.Phase4.A.window_supp g hb₀0.le hb₀b hx) hd0 hd14 hη hLi hud hdη

/-! ### The fixed data of a cell built from a window -/

/-- `ε₁ = min(1/8, (β − λ)/(1 + λ))` with `λ = b + β/2`, `β = β(κc)`. -/
def eps1H (kc b : ℝ) : ℝ :=
  min (1 / 8) ((betaK kc - (b + betaK kc / 2)) / (1 + (b + betaK kc / 2)))

lemma betaK_pos {kc : ℝ} (hkc : 0 < kc) : 0 < betaK kc := by
  have := one_lt_betaK hkc.le; linarith

lemma eps1H_pos {kc b : ℝ} (hkc : 0 < kc) (hb0 : 0 ≤ b) (hbβ : b < betaK kc / 2) :
    0 < eps1H kc b := by
  have hβ := betaK_pos hkc
  unfold eps1H
  exact lt_min (by norm_num) (div_pos (by linarith) (by linarith))

lemma eps1H_le {kc b : ℝ} : eps1H kc b ≤ 1 / 8 := min_le_left _ _

lemma lam_eps1H {kc b : ℝ} (hkc : 0 < kc) (hb0 : 0 ≤ b) :
    (b + betaK kc / 2) * (1 + eps1H kc b) ≤ betaK kc - eps1H kc b := by
  have hβ := betaK_pos hkc
  have hl : 0 < 1 + (b + betaK kc / 2) := by linarith
  have h1 : eps1H kc b ≤ (betaK kc - (b + betaK kc / 2)) / (1 + (b + betaK kc / 2)) :=
    min_le_right _ _
  have h2 : eps1H kc b * (1 + (b + betaK kc / 2)) ≤ betaK kc - (b + betaK kc / 2) := by
    rwa [le_div_iff₀ hl] at h1
  nlinarith

/-- The fixed data `P` of the cell `(a₀, κc)` built from a window `φ` supported in `[−b, b]`,
`0 ≤ b < β(κc)/2`: `λ = b + β/2`, `ε₁ = eps1H κc b`, `ψ(s) = φ(λs)`, `Υ₀ = upsilon0 ε₁`,
`ψ_j = dyadic j`. -/
def mkSetupH (a0 kc θ ε₃ b : ℝ) (φ : ℝ → ℝ) (ha0 : 0 < a0) (hkc : 0 < kc) (hθ : 0 < θ)
    (hθ' : θ < 1 / 4) (hε₃ : 0 < ε₃) (hε₃' : ε₃ < 1 / 4) (hb0 : 0 ≤ b) (hbβ : b < betaK kc / 2)
    (hφs : ContDiff ℝ ∞ φ) (hφe : ∀ x, φ (-x) = φ x) (hφsupp : ∀ x, b < |x| → φ x = 0)
    (hφ0 : φ 0 ≠ 0) : HSetup where
  a0 := a0
  kc := kc
  lam := b + betaK kc / 2
  ε₁ := eps1H kc b
  θ := θ
  ψ := fun s => φ ((b + betaK kc / 2) * s)
  ε₃ := ε₃
  Υ₀ := Families.Phase4.A.upsilon0 (eps1H kc b)
  ψj := Families.Phase4.A.dyadic
  a0_pos := ha0
  kc_pos := hkc
  lam_pos := by have := betaK_pos hkc; linarith
  lam_lt := by linarith
  ε₁_pos := eps1H_pos hkc hb0 hbβ
  ε₁_lt := by have := (eps1H_le (kc := kc) (b := b)); linarith
  lam_ε₁ := lam_eps1H hkc hb0
  θ_pos := hθ
  θ_lt := hθ'
  ψ_smooth := hφs.comp (contDiff_const.mul contDiff_id)
  ψ_even := fun x => by simp only [mul_neg, hφe]
  ψ_supp := by
    have hl : (0 : ℝ) < b + betaK kc / 2 := by have := betaK_pos hkc; linarith
    refine ⟨b / (b + betaK kc / 2), ?_, fun x hx => hφsupp _ ?_⟩
    · rw [div_lt_iff₀ hl]; linarith
    · rw [div_lt_iff₀ hl] at hx
      rw [abs_mul, abs_of_pos hl]
      linarith
  ψ_ne := ⟨0, by simpa using hφ0⟩
  ε₃_pos := hε₃
  ε₃_lt := hε₃'
  Υ₀_smooth := Families.Phase4.A.upsilon0_contDiff _
  Υ₀_range := Families.Phase4.A.upsilon0_range _
  Υ₀_one := fun _ _ hy => Families.Phase4.A.upsilon0_one (eps1H_pos hkc hb0 hbβ) hy
  Υ₀_zero := fun _ hy => Families.Phase4.A.upsilon0_zero (eps1H_pos hkc hb0 hbβ) hy
  ψj_smooth := Families.Phase4.A.dyadic_contDiff
  ψj_nonneg := Families.Phase4.A.dyadic_nonneg
  ψj_supp := Families.Phase4.A.dyadic_supp
  ψj_sum := fun _ hy => Families.Phase4.A.dyadic_sum hy
  ψj_deriv := Families.Phase4.A.dyadic_deriv

/-- For `mkSetupH`, the paper's `f_v(x) = v(x/λ)/(λa)` is exactly `φ(x)²/∫φ²`. -/
lemma mkSetupH_fv (a0 kc θ ε₃ b : ℝ) (φ : ℝ → ℝ) (ha0 : 0 < a0) (hkc : 0 < kc) (hθ : 0 < θ)
    (hθ' : θ < 1 / 4) (hε₃ : 0 < ε₃) (hε₃' : ε₃ < 1 / 4) (hb0 : 0 ≤ b) (hbβ : b < betaK kc / 2)
    (hφs : ContDiff ℝ ∞ φ) (hφe : ∀ x, φ (-x) = φ x) (hφsupp : ∀ x, b < |x| → φ x = 0)
    (hφ0 : φ 0 ≠ 0) :
    let P := mkSetupH a0 kc θ ε₃ b φ ha0 hkc hθ hθ' hε₃ hε₃' hb0 hbβ hφs hφe hφsupp hφ0
    (fun x => P.vfun (x / P.lam) / (P.lam * P.aInt)) = fun x => φ x ^ 2 / ∫ y, φ y ^ 2 := by
  intro P
  funext x
  have hlpos : (0 : ℝ) < b + betaK kc / 2 := by have := betaK_pos hkc; linarith
  have hl : (b + betaK kc / 2) ≠ 0 := hlpos.ne'
  have hint : ∫ s, φ ((b + betaK kc / 2) * s) ^ 2 = (b + betaK kc / 2)⁻¹ * ∫ y, φ y ^ 2 := by
    rw [Measure.integral_comp_mul_left (fun y => φ y ^ 2) (b + betaK kc / 2),
      abs_of_pos (inv_pos.2 hlpos), smul_eq_mul]
  show φ ((b + betaK kc / 2) * (x / (b + betaK kc / 2))) ^ 2 /
    ((b + betaK kc / 2) * ∫ s, φ ((b + betaK kc / 2) * s) ^ 2) = _
  rw [mul_div_cancel₀ x hl, hint, mul_inv_cancel_left₀ hl]

/-! ### The theorem -/

/-- **`assemblyLimitH`** (§9.4, steps (a)–(e)). -/
theorem assemblyLimitH_proof : assemblyLimitH_Statement := by
  intro a0 kc ha0 hkc C Cmax hC hCmax η' hη'
  have hη4 : 0 < η' / 4 := by positivity
  have hC0 : 0 < C := by linarith
  have hCm0 : 0 < Cmax := by linarith
  have hβ1 : 1 < betaK kc := one_lt_betaK hkc.le
  have hβ2 : betaK kc ≤ 2 := betaK_le_two hkc.le
  have hβ0 : 0 < betaK kc := by linarith
  -- 1. a near-optimal admissible `f` at support `β(κc)`
  have hne := pB_nonempty hβ1.le C
  obtain ⟨_, ⟨f, hf, rfl⟩, hfQ⟩ := exists_lt_of_csInf_lt hne (lt_add_of_pos_right _ hη4)
  -- 2. `lem:windowsH`
  obtain ⟨φ, b, hb0, hbβ, hφs, hφe, hφsupp, hφ0, hφQ⟩ := exists_windowB hC hβ0 hβ2 hf hη4
  have hφc := hφs.continuous
  have hφ2s : ∀ x, b < |x| → φ x ^ 2 = 0 := fun x hx => by rw [hφsupp x hx]; ring
  have hφ2i : Integrable (fun x => φ x ^ 2) :=
    Families.Phase4.A.integrable_of_continuous_supp (hφc.pow 2) hφ2s
  have hcpos : 0 < ∫ y, φ y ^ 2 :=
    integral_pos_of_integrable_nonneg_nonzero (hφc.pow 2) hφ2i (fun x => sq_nonneg (φ x))
      (pow_ne_zero 2 hφ0)
  obtain ⟨M₀, hM₀⟩ := hφc.bounded_above_of_compact_support
    (HasCompactSupport.intro (isCompact_Icc (a := -b) (b := b))
      fun x hx => hφsupp x (Families.Phase4.A.lt_abs_of_notMem_Icc hx))
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
  have hε₁0 : 0 < eps1H kc b := eps1H_pos hkc hb0 hbβ
  have hkc8 : 0 < 1 / (8 * (1 + kc)) := by positivity
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = min (1 / 8) (min (eps1H kc b / 8)
      (min (1 / (8 * (1 + kc))) (η' / (128 * Cmax * (M + 1))))) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by
    rw [hε]
    exact lt_min (by norm_num) (lt_min (by positivity) (lt_min hkc8 (by positivity)))
  have hε8 : ε ≤ 1 / 8 := by rw [hε]; exact min_le_left _ _
  have hεε₁ : ε ≤ eps1H kc b / 8 := by
    rw [hε]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hεkc : ε ≤ 1 / (8 * (1 + kc)) := by
    rw [hε]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεη : 16 * Cmax * M * ε ≤ η' / 8 := by
    have h1 : ε ≤ η' / (128 * Cmax * (M + 1)) := by
      rw [hε]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have h2 : ε * (128 * Cmax * (M + 1)) ≤ η' := by rwa [le_div_iff₀ (by positivity)] at h1
    nlinarith
  -- 4. the fixed data
  refine ⟨mkSetupH a0 kc θ ε₃ b φ ha0 hkc hθ0 (by linarith) hε₃0 (by linarith) hb0 hbβ hφs hφe
    hφsupp hφ0, ε, rfl, rfl, hε0, by linarith,
    show ε < eps1H kc b / 4 by linarith, hεkc, fun Ct hCt hrange hbelow habove => ?_⟩
  -- the certified value, with `f_v = φ²/∫φ²`
  have hcert : (mkSetupH a0 kc θ ε₃ b φ ha0 hkc hθ0 (by linarith) hε₃0 (by linarith) hb0 hbβ hφs
      hφe hφsupp hφ0).certValue Ct = 2 - 8 * θ - (1 - 2 * θ) *
        Qf (fun α => Ct α * min α (1 + 2 * ε₃)) (fun x => φ x ^ 2 / ∫ y, φ y ^ 2) := by
    unfold HSetup.certValue
    rw [mkSetupH_fv]
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
    rw [abs_of_nonneg (Families.Phase4.A.FC_bounds hC α hα).1]
    linarith [(Families.Phase4.A.FC_bounds hC α hα).2]
  have hband := Families.Phase4.A.Qf_le_of_band hFm (Families.Phase4.A.measurable_FC C) hFK hGK
    hfv0 hfvM hfvi hfv1 (a := 2 * C * ε₃) (k := 2 * Cmax) (by linarith) hε0.le
    (Families.Phase4.A.profile_kernel_le hC hCmax hε0.le hε₃0 hε₃8 hrange hbelow habove)
  have hQF0 : 0 ≤ Qf (fun α => Ct α * min α (1 + 2 * ε₃)) (fun x => φ x ^ 2 / ∫ y, φ y ^ 2) :=
    Families.Phase4.A.Qf_nonneg_of
      (fun α hα => mul_nonneg (by linarith [(hrange α).1]) (le_min hα (by linarith))) hfv0
  -- conclusion
  unfold pB
  have h1 : (1 - 2 * θ) * Qf (fun α => Ct α * min α (1 + 2 * ε₃)) (fun x => φ x ^ 2 / ∫ y, φ y ^ 2)
      ≤ Qf (fun α => Ct α * min α (1 + 2 * ε₃)) (fun x => φ x ^ 2 / ∫ y, φ y ^ 2) := by
    nlinarith
  linarith

end Families.Hybrid.V
