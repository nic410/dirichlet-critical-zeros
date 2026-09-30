/-
**`lem:windows`** (realisation by windows, Lemma 7.2).

For an admissible `f` (`AdmissibleWindow`), `C ≥ 1` and `η > 0` there are `0 ≤ b < 1` and a smooth even
`φ` supported in `[−b, b]`, `φ(0) ≠ 0`, with `𝒬_{F_C}(φ²/∫φ²) ≤ 𝒬_{F_C}(f) + η`
(`exists_window`). The window of the paper is then `ψ(s) = φ(λs)` with `λ = 1 + b < 2`
(see `Families.Phase4.A.AssemblyLimit`), for which `f_v = φ²/∫φ²` exactly.

Route (slightly different from, but equivalent to, the TeX's): instead of first rescaling `f` into
`[−λ/2, λ/2]`, we truncate: `∫_{|x|>b₀} f² → 0` as `b₀ ↑ 1` (dominated convergence,
`exists_tail_small`); approximate `f` in `L²` by a smooth compactly supported `g` (Mathlib's
`MemLp.exist_eLpNorm_sub_le`); symmetrise `g`; and put `φ = ζ · (g_s² + δ²)^{1/4}` with a smooth even
cut-off `ζ` equal to `1` on `[−b₀, b₀]` and `0` off `(−b, b)`. This is the TeX's square-root
construction `ψ = ζ (f₁ + ε')^{1/2}` with `f₁ + ε'` replaced by the positive smooth function
`(g_s² + δ²)^{1/2}` (so no separate nonnegativity step is needed). All the estimates are explicit, and
the conclusion follows from the continuity estimate `Qf_le_of_close`.
-/
import Families.Phase4.A.QfBasic

noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal

namespace Families.Phase4.A

/-! ### Small helpers -/

lemma lt_abs_of_notMem_Icc {R x : ℝ} (hx : x ∉ Set.Icc (-R) R) : R < |x| := by
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  rcases hx with hx | hx
  · exact lt_of_lt_of_le (by linarith) (neg_le_abs x)
  · exact lt_of_lt_of_le hx (le_abs_self x)

lemma integrable_of_continuous_supp {h : ℝ → ℝ} (hc : Continuous h) {R : ℝ}
    (hs : ∀ x, R < |x| → h x = 0) : Integrable h :=
  hc.integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R))
      fun x hx => hs x (lt_abs_of_notMem_Icc hx))

/-- From an `eLpNorm` bound to an integral bound, for `p = 2`. -/
lemma integral_sq_le_of_eLpNorm_le {h : ℝ → ℝ} (hh : MemLp h 2) {δ : ℝ} (hδ : 0 ≤ δ)
    (hle : eLpNorm h 2 volume ≤ ENNReal.ofReal δ) : ∫ x, h x ^ 2 ≤ δ ^ 2 := by
  rw [hh.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ENNReal.ofReal_le_ofReal_iff hδ] at hle
  have e : ∀ x, ‖h x‖ ^ (2 : ℝ≥0∞).toReal = h x ^ 2 := fun x => by
    rw [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs]
  simp_rw [e] at hle
  have hI : 0 ≤ ∫ x, h x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have h2 : ((∫ x, h x ^ 2) ^ ((2 : ℝ≥0∞).toReal)⁻¹) ^ (2 : ℝ) ≤ δ ^ (2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) hle (by norm_num)
  rw [← Real.rpow_mul hI, ENNReal.toReal_ofNat, inv_mul_cancel₀ (by norm_num), Real.rpow_one,
    Real.rpow_two] at h2
  exact h2

/-! ### Truncation: the tail `∫_{|x|>b} f²` is small for `b` close to `1` -/

lemma measurableSet_lt_abs (c : ℝ) : MeasurableSet {x : ℝ | c < |x|} :=
  measurableSet_lt measurable_const measurable_abs

/-- **Truncation** (dominated convergence). If `f² ∈ L¹` and `f = 0` off `[−1, 1]`, then for every
`δ > 0` there is `b ∈ (0, 1)` with `∫_{|x| > b} f² ≤ δ`. -/
lemma exists_tail_small {f : ℝ → ℝ} (hf : Integrable (fun x => f x ^ 2))
    (hs : ∀ x, 1 < |x| → f x = 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ b : ℝ, 0 < b ∧ b < 1 ∧
      ∫ x, {x : ℝ | b < |x|}.indicator (fun x => f x ^ 2) x ≤ δ := by
  set bn : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 2) with hbn
  set Fn : ℕ → ℝ → ℝ := fun n => {x : ℝ | bn n < |x|}.indicator (fun x => f x ^ 2) with hFn
  have hlim : Tendsto (fun n => ∫ x, Fn n x) atTop (𝓝 (∫ _x : ℝ, (0 : ℝ))) := by
    refine tendsto_integral_of_dominated_convergence (fun x => f x ^ 2)
      (fun n => hf.aestronglyMeasurable.indicator (measurableSet_lt_abs _)) hf
      (fun n => Eventually.of_forall fun x => ?_) ?_
    · refine (norm_indicator_le_norm_self _ _).trans (le_of_eq ?_)
      exact Real.norm_of_nonneg (sq_nonneg _)
    · have hc : ({1, -1} : Set ℝ).Countable := (Set.toFinite _).countable
      filter_upwards [hc.ae_notMem volume] with x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx
      have hx1 : |x| ≠ 1 := by
        intro h
        rcases abs_eq (zero_le_one) |>.1 h with h | h
        · exact hx.1 h
        · exact hx.2 h
      rcases lt_or_gt_of_ne hx1 with hlt | hgt
      · obtain ⟨N, hN⟩ := exists_nat_one_div_lt (sub_pos.2 hlt)
        refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
        have hn' : (N : ℝ) + 1 ≤ (n : ℝ) + 2 := by
          have : (N : ℝ) ≤ n := by exact_mod_cast hn
          linarith
        have h1 : 1 / ((n : ℝ) + 2) ≤ 1 / ((N : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) hn'
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
    have : 1 / ((n : ℝ) + 2) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
    linarith
  · simp only [hbn]
    have : 0 < 1 / ((n : ℝ) + 2) := by positivity
    linarith

/-! ### Symmetrisation -/

/-- The even part `(g(x) + g(−x))/2`. -/
def symm (g : ℝ → ℝ) (x : ℝ) : ℝ := (g x + g (-x)) / 2

lemma symm_even (g : ℝ → ℝ) (x : ℝ) : symm g (-x) = symm g x := by
  simp only [symm, neg_neg, add_comm]

lemma symm_contDiff {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (symm g) :=
  (hg.add (hg.comp contDiff_neg)).div_const 2

/-- Symmetrising `g` does not increase the `L²` distance to an even `f`. -/
lemma integral_sq_sym_le {f g : ℝ → ℝ} (hfe : ∀ x, f (-x) = f x) (hf : AEStronglyMeasurable f)
    (hg : Continuous g) (hfg : Integrable (fun x => (f x - g x) ^ 2)) :
    Integrable (fun x => (f x - symm g x) ^ 2) ∧
      ∫ x, (f x - symm g x) ^ 2 ≤ ∫ x, (f x - g x) ^ 2 := by
  have hneg : Integrable (fun x => (f (-x) - g (-x)) ^ 2) := hfg.comp_neg
  have hB : Integrable (fun x => ((f x - g x) ^ 2 + (f (-x) - g (-x)) ^ 2) / 2) :=
    (hfg.fun_add hneg).div_const 2
  have hpt : ∀ x, (f x - symm g x) ^ 2 ≤ ((f x - g x) ^ 2 + (f (-x) - g (-x)) ^ 2) / 2 := by
    intro x
    rw [hfe x, symm]
    nlinarith [sq_nonneg ((f x - g x) - (f x - g (-x)))]
  have hm : AEStronglyMeasurable (fun x => (f x - symm g x) ^ 2) :=
    (hf.sub ((hg.add (hg.comp continuous_neg)).div_const 2).aestronglyMeasurable).pow 2
  have hi : Integrable (fun x => (f x - symm g x) ^ 2) :=
    hB.mono' hm (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hpt x)
  refine ⟨hi, ?_⟩
  calc ∫ x, (f x - symm g x) ^ 2
      ≤ ∫ x, ((f x - g x) ^ 2 + (f (-x) - g (-x)) ^ 2) / 2 := integral_mono hi hB hpt
    _ = ∫ x, (f x - g x) ^ 2 := by
      rw [integral_div, integral_add hfg hneg,
        integral_neg_eq_self (fun x => (f x - g x) ^ 2) volume]
      ring

/-! ### A smooth even cut-off -/

/-- `ζ(x) = S((b'² − x²)/(b'² − b²))` (`S` = `Real.smoothTransition`): smooth, even, `[0,1]`-valued,
`= 1` on `[−b, b]` and `= 0` off `(−b', b')` (for `0 ≤ b < b'`). -/
def cutoff (b b' x : ℝ) : ℝ := Real.smoothTransition ((b' ^ 2 - x ^ 2) / (b' ^ 2 - b ^ 2))

lemma cutoff_contDiff (b b' : ℝ) : ContDiff ℝ ∞ (cutoff b b') := by
  unfold cutoff
  exact Real.smoothTransition.contDiff.comp ((contDiff_const.sub (contDiff_id.pow 2)).div_const _)

lemma cutoff_even (b b' x : ℝ) : cutoff b b' (-x) = cutoff b b' x := by
  simp [cutoff]

lemma cutoff_nonneg (b b' x : ℝ) : 0 ≤ cutoff b b' x := Real.smoothTransition.nonneg _

lemma cutoff_le_one (b b' x : ℝ) : cutoff b b' x ≤ 1 := Real.smoothTransition.le_one _

lemma cutoff_eq_one {b b' x : ℝ} (hb : 0 ≤ b) (hbb' : b < b') (hx : |x| ≤ b) :
    cutoff b b' x = 1 := by
  unfold cutoff
  apply Real.smoothTransition.one_of_one_le
  have hden : 0 < b' ^ 2 - b ^ 2 := by nlinarith
  rw [le_div_iff₀ hden]
  have : x ^ 2 ≤ b ^ 2 := by
    rw [← sq_abs x]; exact pow_le_pow_left₀ (abs_nonneg x) hx 2
  linarith

lemma cutoff_eq_zero {b b' x : ℝ} (hb : 0 ≤ b) (hbb' : b < b') (hx : b' ≤ |x|) :
    cutoff b b' x = 0 := by
  unfold cutoff
  apply Real.smoothTransition.zero_of_nonpos
  have hden : 0 < b' ^ 2 - b ^ 2 := by nlinarith
  have : b' ^ 2 ≤ x ^ 2 := by
    rw [← sq_abs x]; exact pow_le_pow_left₀ (by linarith) hx 2
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le

/-! ### The pointwise estimate for the square-root construction -/

/-- `|S − c| ≤ δ + |t − c|` when `|t| ≤ S ≤ |t| + δ`, `c ≥ 0`. -/
lemma abs_S_sub_le {S t c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 ≤ δ) (hS1 : |t| ≤ S)
    (hS2 : S ≤ |t| + δ) : |S - c| ≤ δ + |t - c| := by
  rw [abs_sub_le_iff]
  constructor
  · have : |t| - c ≤ |t - c| := by
      have := abs_sub_abs_le_abs_sub t c
      rwa [abs_of_nonneg hc] at this
    linarith
  · have h1 : c - t ≤ |t - c| := by rw [abs_sub_comm]; exact le_abs_self _
    have h2 : t ≤ |t| := le_abs_self t
    linarith

lemma sq_bound_one {S t c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 ≤ δ) (hS1 : |t| ≤ S) (hS2 : S ≤ |t| + δ) :
    (S - c) ^ 2 ≤ 2 * (δ ^ 2 + (c - t) ^ 2) := by
  have h := abs_S_sub_le hc hδ hS1 hS2
  have h0 : 0 ≤ |t - c| := abs_nonneg _
  have e1 : (S - c) ^ 2 = |S - c| ^ 2 := (sq_abs _).symm
  have e2 : (c - t) ^ 2 = |t - c| ^ 2 := by rw [sq_abs]; ring
  rw [e1, e2]
  nlinarith [abs_nonneg (S - c), sq_nonneg (δ - |t - c|)]

lemma sq_bound_gen {z S t c δ : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hc : 0 ≤ c) (hδ : 0 ≤ δ)
    (hS1 : |t| ≤ S) (hS2 : S ≤ |t| + δ) :
    (z ^ 2 * S - c) ^ 2 ≤ 3 * (δ ^ 2 + (c - t) ^ 2 + c ^ 2) := by
  have h := abs_S_sub_le hc hδ hS1 hS2
  have hz2 : z ^ 2 ≤ 1 := by nlinarith
  have hz20 : 0 ≤ z ^ 2 := sq_nonneg z
  have key : |z ^ 2 * S - c| ≤ δ + |t - c| + c := by
    have e : z ^ 2 * S - c = z ^ 2 * (S - c) - (1 - z ^ 2) * c := by ring
    rw [e]
    calc |z ^ 2 * (S - c) - (1 - z ^ 2) * c| ≤ |z ^ 2 * (S - c)| + |(1 - z ^ 2) * c| :=
          abs_sub _ _
      _ = z ^ 2 * |S - c| + (1 - z ^ 2) * c := by
          rw [abs_mul, abs_mul, abs_of_nonneg hz20, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - z ^ 2),
            abs_of_nonneg hc]
      _ ≤ 1 * |S - c| + 1 * c := by
          have := abs_nonneg (S - c)
          nlinarith
      _ ≤ δ + |t - c| + c := by linarith
  have h0 : 0 ≤ |t - c| := abs_nonneg _
  have e1 : (z ^ 2 * S - c) ^ 2 = |z ^ 2 * S - c| ^ 2 := (sq_abs _).symm
  have e2 : (c - t) ^ 2 = |t - c| ^ 2 := by rw [sq_abs]; ring
  rw [e1, e2]
  have hA := abs_nonneg (z ^ 2 * S - c)
  have : |z ^ 2 * S - c| ^ 2 ≤ (δ + |t - c| + c) ^ 2 := pow_le_pow_left₀ hA key 2
  nlinarith [sq_nonneg (δ - |t - c|), sq_nonneg (δ - c), sq_nonneg (|t - c| - c)]

lemma sqrt_sq_add_bounds (t δ : ℝ) (hδ : 0 ≤ δ) :
    |t| ≤ Real.sqrt (t ^ 2 + δ ^ 2) ∧ Real.sqrt (t ^ 2 + δ ^ 2) ≤ |t| + δ := by
  constructor
  · rw [← Real.sqrt_sq (abs_nonneg t), sq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith)
  · rw [Real.sqrt_le_left (by positivity)]
    · rw [← sq_abs t]; nlinarith [abs_nonneg t]

/-! ### `lem:windows` -/

lemma admissible_supp {f : ℝ → ℝ} (hf : AdmissibleWindow f) : ∀ x, 1 < |x| → f x = 0 := by
  intro x hx
  by_contra h
  have h1 : |x| ≤ 1 := abs_le.2 (hf.supp x h)
  linarith

lemma measurable_FC (C : ℝ) : Measurable (FC C) := by
  unfold FC
  exact Measurable.ite measurableSet_Iic measurable_id measurable_const

lemma FC_bounds {C : ℝ} (hC : 1 ≤ C) : ∀ α, 0 ≤ α → 0 ≤ FC C α ∧ FC C α ≤ C := by
  intro α hα
  unfold FC
  split_ifs with h <;> constructor <;> linarith

/-- The window `φ = ζ · (g_s² + δ²)^{1/4}` (`ζ = cutoff b₀ b`, `g_s = symm g`). -/
def window (b₀ b δ : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  cutoff b₀ b x * Real.sqrt (Real.sqrt (symm g x ^ 2 + δ ^ 2))

lemma window_sq (b₀ b δ : ℝ) (g : ℝ → ℝ) (x : ℝ) :
    window b₀ b δ g x ^ 2 = cutoff b₀ b x ^ 2 * Real.sqrt (symm g x ^ 2 + δ ^ 2) := by
  rw [window, mul_pow, Real.sq_sqrt (Real.sqrt_nonneg _)]

lemma sqrt_symm_pos (g : ℝ → ℝ) {δ : ℝ} (hδ : 0 < δ) (x : ℝ) :
    0 < Real.sqrt (symm g x ^ 2 + δ ^ 2) := Real.sqrt_pos.2 (by positivity)

lemma window_contDiff {b₀ b δ : ℝ} {g : ℝ → ℝ} (hδ : 0 < δ) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (window b₀ b δ g) := by
  have h1 : ContDiff ℝ ∞ (fun x => symm g x ^ 2 + δ ^ 2) :=
    ((symm_contDiff hg).pow 2).add contDiff_const
  have h2 : ContDiff ℝ ∞ (fun x => Real.sqrt (symm g x ^ 2 + δ ^ 2)) :=
    h1.sqrt (fun x => by positivity)
  exact (cutoff_contDiff b₀ b).mul (h2.sqrt fun x => (sqrt_symm_pos g hδ x).ne')

lemma window_even (b₀ b δ : ℝ) (g : ℝ → ℝ) (x : ℝ) :
    window b₀ b δ g (-x) = window b₀ b δ g x := by
  simp only [window, cutoff_even, symm_even]

lemma window_supp {b₀ b δ : ℝ} (g : ℝ → ℝ) (hb₀ : 0 ≤ b₀) (hb : b₀ < b) {x : ℝ} (hx : b < |x|) :
    window b₀ b δ g x = 0 := by
  rw [window, cutoff_eq_zero hb₀ hb hx.le, zero_mul]

lemma window_zero_ne {b₀ b δ : ℝ} (g : ℝ → ℝ) (hb₀ : 0 ≤ b₀) (hb : b₀ < b) (hδ : 0 < δ) :
    window b₀ b δ g 0 ≠ 0 := by
  have h1 : cutoff b₀ b 0 = 1 := cutoff_eq_one hb₀ hb (by simp [hb₀])
  rw [window, h1, one_mul]
  exact (Real.sqrt_pos.2 (sqrt_symm_pos g hδ 0)).ne'

/-- The pointwise estimate for the window: `(φ² − f)² ≤ 3(δ² 1_{[−1,1]} + (f − g_s)² + 1_{|x|>b₀} f²)`. -/
lemma window_pt {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hsf : ∀ x, 1 < |x| → f x = 0) {b₀ b δ : ℝ}
    (hb₀ : 0 ≤ b₀) (hb : b₀ < b) (hb1 : b < 1) (hδ : 0 < δ) (g : ℝ → ℝ) (x : ℝ) :
    (window b₀ b δ g x ^ 2 - f x) ^ 2 ≤
      3 * (δ ^ 2 * (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x + (f x - symm g x) ^ 2 +
        {x : ℝ | b₀ < |x|}.indicator (fun x => f x ^ 2) x) := by
  have hT0 : 0 ≤ {x : ℝ | b₀ < |x|}.indicator (fun x => f x ^ 2) x :=
    Set.indicator_nonneg (fun _ _ => sq_nonneg _) _
  have hI0 : 0 ≤ (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hz0 := cutoff_nonneg b₀ b x
  have hz1 := cutoff_le_one b₀ b x
  obtain ⟨hS1, hS2⟩ := sqrt_sq_add_bounds (symm g x) δ hδ.le
  have hc := hf0 x
  rw [window_sq]
  by_cases hx1 : |x| ≤ 1
  · have hI : (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x = 1 :=
      Set.indicator_of_mem (Set.mem_Icc.2 (abs_le.1 hx1)) _
    rw [hI, mul_one]
    by_cases hxb : |x| ≤ b₀
    · rw [cutoff_eq_one hb₀ hb hxb, one_pow, one_mul]
      have := sq_bound_one hc hδ.le hS1 hS2
      nlinarith
    · have hmem : x ∈ {x : ℝ | b₀ < |x|} := lt_of_not_ge hxb
      rw [Set.indicator_of_mem hmem]
      exact sq_bound_gen hz0 hz1 hc hδ.le hS1 hS2
  · have hx1' : 1 < |x| := lt_of_not_ge hx1
    rw [cutoff_eq_zero hb₀ hb (by linarith), hsf x hx1']
    have h3 : 0 ≤ (0 - symm g x) ^ 2 := sq_nonneg _
    have h4 : (0 : ℝ) ^ 2 * Real.sqrt (symm g x ^ 2 + δ ^ 2) - 0 = 0 := by ring
    rw [h4]
    have : (0 : ℝ) ^ 2 = 0 := by ring
    rw [this]
    positivity

lemma integrable_of_admissible {f : ℝ → ℝ} (hf : AdmissibleWindow f) : Integrable f := by
  by_contra h
  have := integral_undef h
  rw [hf.integral_eq_one] at this
  exact one_ne_zero this

/-- `∫ (φ² − f)² ≤ 12 δ²` for the window built from `b₀` (tail `≤ δ²`) and `g` (`‖f − g_s‖₂ ≤ δ`). -/
lemma window_close {f : ℝ → ℝ} (hf : AdmissibleWindow f) {b₀ b δ : ℝ} (hb₀ : 0 ≤ b₀) (hb : b₀ < b)
    (hb1 : b < 1) (hδ : 0 < δ) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hfgsi : Integrable (fun x => (f x - symm g x) ^ 2)) (hfgs : ∫ x, (f x - symm g x) ^ 2 ≤ δ ^ 2)
    (htail : ∫ x, {x : ℝ | b₀ < |x|}.indicator (fun x => f x ^ 2) x ≤ δ ^ 2) :
    Integrable (fun x => (window b₀ b δ g x ^ 2 - f x) ^ 2) ∧
      ∫ x, (window b₀ b δ g x ^ 2 - f x) ^ 2 ≤ 12 * δ ^ 2 := by
  have hf2 : Integrable (fun x => f x ^ 2) := hf.memL2.integrable_sq
  have hfm : AEStronglyMeasurable f := hf.memL2.aestronglyMeasurable
  have hsf := admissible_supp hf
  have hφc : Continuous (window b₀ b δ g) := (window_contDiff hδ hg).continuous
  have hem : AEStronglyMeasurable (fun x => window b₀ b δ g x ^ 2 - f x) :=
    (hφc.pow 2).aestronglyMeasurable.sub hfm
  have t1 : Integrable (fun x => δ ^ 2 * (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x) :=
    (integrable_indicator_Icc 1).const_mul _
  have t3 : Integrable (fun x => {x : ℝ | b₀ < |x|}.indicator (fun x => f x ^ 2) x) :=
    hf2.indicator (measurableSet_lt_abs b₀)
  have hTi : Integrable (fun x => 3 * (δ ^ 2 * (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x +
      (f x - symm g x) ^ 2 + {x : ℝ | b₀ < |x|}.indicator (fun x => f x ^ 2) x)) :=
    ((t1.fun_add hfgsi).fun_add t3).const_mul 3
  have hpt := window_pt hf.nonneg hsf hb₀ hb hb1 hδ g
  have hLi : Integrable (fun x => (window b₀ b δ g x ^ 2 - f x) ^ 2) :=
    hTi.mono' (hem.pow 2) (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hpt x)
  refine ⟨hLi, ?_⟩
  calc ∫ x, (window b₀ b δ g x ^ 2 - f x) ^ 2
      ≤ ∫ x, 3 * (δ ^ 2 * (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x +
          (f x - symm g x) ^ 2 + {x : ℝ | b₀ < |x|}.indicator (fun x => f x ^ 2) x) :=
        integral_mono hLi hTi hpt
    _ = 3 * (δ ^ 2 * 2 + (∫ x, (f x - symm g x) ^ 2) +
          ∫ x, {x : ℝ | b₀ < |x|}.indicator (fun x => f x ^ 2) x) := by
        rw [integral_const_mul, integral_add (t1.fun_add hfgsi) t3, integral_add t1 hfgsi,
          integral_const_mul, integral_indicator_Icc zero_le_one]
        ring
    _ ≤ 12 * δ ^ 2 := by nlinarith

/-- The constant `κ(C, B)` of the continuity estimate, with `A = 2B + 24`. -/
def kappa (C B : ℝ) : ℝ := (1 + 4 * (2 * B + 24)) / 2 + 3 * C * ((2 * B + 24) + 2) / 2

lemma kappa_pos {C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B) : 0 < kappa C B := by
  unfold kappa; positivity

/-- From `‖φ² − f‖₂ ≤ d` to `𝒬_{F_C}(φ²/∫φ²) ≤ 𝒬_{F_C}(f) + η`, when
`d ≤ 1/4` and `d (κ + 3(𝒬(f) + η)) ≤ η`. -/
lemma Qf_normalised_le {C : ℝ} (hC : 1 ≤ C) {f : ℝ → ℝ} (hf : AdmissibleWindow f) {φ : ℝ → ℝ}
    (hφc : Continuous φ) {b : ℝ} (hb1 : b < 1) (hφs : ∀ x, b < |x| → φ x = 0) {d η : ℝ}
    (hd0 : 0 < d) (hd14 : d ≤ 1 / 4) (hη : 0 < η)
    (hudi : Integrable (fun x => (φ x ^ 2 - f x) ^ 2)) (hud : ∫ x, (φ x ^ 2 - f x) ^ 2 ≤ d ^ 2)
    (hdη : d * (kappa C (∫ x, f x ^ 2) + 3 * (Qf (FC C) f + η)) ≤ η) :
    Qf (FC C) (fun x => φ x ^ 2 / ∫ y, φ y ^ 2) ≤ Qf (FC C) f + η := by
  have hf2 : Integrable (fun x => f x ^ 2) := hf.memL2.integrable_sq
  have hfm : AEStronglyMeasurable f := hf.memL2.aestronglyMeasurable
  have hsf := admissible_supp hf
  have hfi := integrable_of_admissible hf
  have hFb := FC_bounds hC
  have hq0 : 0 ≤ Qf (FC C) f := Qf_nonneg_of (fun α hα => (hFb α hα).1) hf.nonneg
  have hB0 : 0 ≤ ∫ x, f x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hφ2c : Continuous (fun x => φ x ^ 2) := hφc.pow 2
  have hφ2s : ∀ x, 1 < |x| → φ x ^ 2 = 0 := fun x hx => by
    rw [hφs x (by linarith)]; ring
  have hφ2i : Integrable (fun x => φ x ^ 2) :=
    integrable_of_continuous_supp hφ2c (R := 1) hφ2s
  have hem : AEStronglyMeasurable (fun x => φ x ^ 2 - f x) := hφ2c.aestronglyMeasurable.sub hfm
  -- `∫ (φ²)² ≤ A`
  have hφ4i : Integrable (fun x => (φ x ^ 2) ^ 2) :=
    integrable_of_continuous_supp (hφ2c.pow 2) (R := 1) fun x hx => by rw [hφ2s x hx]; ring
  have hAu : ∫ x, (φ x ^ 2) ^ 2 ≤ 2 * (∫ x, f x ^ 2) + 24 := by
    have hR : Integrable (fun x => 2 * (φ x ^ 2 - f x) ^ 2 + 2 * f x ^ 2) :=
      (hudi.const_mul 2).fun_add (hf2.const_mul 2)
    calc ∫ x, (φ x ^ 2) ^ 2 ≤ ∫ x, (2 * (φ x ^ 2 - f x) ^ 2 + 2 * f x ^ 2) :=
          integral_mono hφ4i hR fun x => by nlinarith [sq_nonneg (φ x ^ 2 - 2 * f x)]
      _ = 2 * (∫ x, (φ x ^ 2 - f x) ^ 2) + 2 * ∫ x, f x ^ 2 := by
          rw [integral_add (hudi.const_mul 2) (hf2.const_mul 2), integral_const_mul,
            integral_const_mul]
      _ ≤ 2 * (∫ x, f x ^ 2) + 24 := by nlinarith
  have hAw : ∫ x, f x ^ 2 ≤ 2 * (∫ x, f x ^ 2) + 24 := by linarith
  -- continuity of `𝒬`
  have hQ := Qf_le_of_close (measurable_FC C) hFb hφ2c.aestronglyMeasurable hfm hφ4i hf2 hφ2s hsf
    hd0 hAu hAw hud
  have hκ : (1 + 4 * (2 * (∫ x, f x ^ 2) + 24)) / 2 + 3 * C * (2 * (∫ x, f x ^ 2) + 24 + 2) / 2 =
      kappa C (∫ x, f x ^ 2) := rfl
  rw [hκ] at hQ
  -- the normalisation `c = ∫ φ²`
  obtain ⟨-, habs⟩ := integral_abs_le_of_sq (e := fun x => φ x ^ 2 - f x) hem hudi zero_le_one
    (fun x hx => by rw [hφ2s x hx, hsf x hx, sub_zero]) hd0
  have habs' : ∫ x, |φ x ^ 2 - f x| ≤ 3 * d / 2 := by
    have : (∫ x, (φ x ^ 2 - f x) ^ 2) / d ≤ d := by rw [div_le_iff₀ hd0]; nlinarith
    linarith
  have hc1 : 1 - 3 * d / 2 ≤ ∫ y, φ y ^ 2 := by
    have e : (∫ y, φ y ^ 2) - 1 = ∫ x, (φ x ^ 2 - f x) := by
      rw [integral_sub hφ2i hfi, hf.integral_eq_one]
    have h1 := abs_integral_le_integral_abs (f := fun x => φ x ^ 2 - f x) (μ := volume)
    have h2 := neg_abs_le (∫ x, (φ x ^ 2 - f x))
    linarith
  have hcpos : 0 < ∫ y, φ y ^ 2 := by linarith
  have hc2 : 1 - 3 * d ≤ (∫ y, φ y ^ 2) ^ 2 := by
    have h0 : 0 ≤ 1 - 3 * d / 2 := by linarith
    have := pow_le_pow_left₀ h0 hc1 2
    nlinarith
  -- conclusion
  have hdiv := Qf_div (FC C) (fun x => φ x ^ 2) (∫ y, φ y ^ 2)
  rw [hdiv, div_le_iff₀ (pow_pos hcpos 2)]
  have hqη : 0 ≤ Qf (FC C) f + η := by linarith
  have := mul_le_mul_of_nonneg_left hc2 hqη
  nlinarith

/-- **`lem:windows`** (Lemma 7.2). For admissible `f`, `C ≥ 1`, `η > 0` there are
`0 ≤ b < 1` and a smooth even `φ`, supported in `[−b, b]`, `φ(0) ≠ 0`, with
`𝒬_{F_C}(φ²/∫φ²) ≤ 𝒬_{F_C}(f) + η`. -/
theorem exists_window {C : ℝ} (hC : 1 ≤ C) {f : ℝ → ℝ} (hf : AdmissibleWindow f) {η : ℝ}
    (hη : 0 < η) :
    ∃ (φ : ℝ → ℝ) (b : ℝ), 0 ≤ b ∧ b < 1 ∧ ContDiff ℝ ∞ φ ∧ (∀ x, φ (-x) = φ x) ∧
      (∀ x, b < |x| → φ x = 0) ∧ φ 0 ≠ 0 ∧
      Qf (FC C) (fun x => φ x ^ 2 / ∫ y, φ y ^ 2) ≤ Qf (FC C) f + η := by
  have hfL2 := hf.memL2
  have hf2 : Integrable (fun x => f x ^ 2) := hfL2.integrable_sq
  have hfm : AEStronglyMeasurable f := hfL2.aestronglyMeasurable
  have hsf := admissible_supp hf
  have hFb := FC_bounds hC
  have hq0 : 0 ≤ Qf (FC C) f := Qf_nonneg_of (fun α hα => (hFb α hα).1) hf.nonneg
  have hB0 : 0 ≤ ∫ x, f x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hκ0 := kappa_pos (by linarith : (0 : ℝ) ≤ C) hB0
  have hden : 0 < kappa C (∫ x, f x ^ 2) + 3 * (Qf (FC C) f + η) := by positivity
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = min (1 / 4) (η / (kappa C (∫ x, f x ^ 2) + 3 * (Qf (FC C) f + η))) :=
    ⟨_, rfl⟩
  have hd0 : 0 < d := by rw [hd]; exact lt_min (by norm_num) (div_pos hη hden)
  have hd14 : d ≤ 1 / 4 := by rw [hd]; exact min_le_left _ _
  have hdη : d * (kappa C (∫ x, f x ^ 2) + 3 * (Qf (FC C) f + η)) ≤ η := by
    have h1 : d ≤ η / (kappa C (∫ x, f x ^ 2) + 3 * (Qf (FC C) f + η)) := by
      rw [hd]; exact min_le_right _ _
    calc d * (kappa C (∫ x, f x ^ 2) + 3 * (Qf (FC C) f + η))
        ≤ η / (kappa C (∫ x, f x ^ 2) + 3 * (Qf (FC C) f + η)) *
            (kappa C (∫ x, f x ^ 2) + 3 * (Qf (FC C) f + η)) :=
          mul_le_mul_of_nonneg_right h1 hden.le
      _ = η := div_mul_cancel₀ _ hden.ne'
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = d / 4 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  -- truncation
  obtain ⟨b₀, hb₀0, hb₀1, htail⟩ := exists_tail_small hf2 hsf (pow_pos hδ0 2)
  -- smooth approximation (Mathlib: smooth compactly supported functions are dense in `L²`)
  obtain ⟨g, hgcs, hgs, hgle⟩ := hfL2.exist_eLpNorm_sub_le (by norm_num) (by norm_num) hδ0
  have hgc : Continuous g := hgs.continuous
  have hgL2 : MemLp g 2 := hgc.memLp_of_hasCompactSupport hgcs
  have hfg : ∫ x, (f x - g x) ^ 2 ≤ δ ^ 2 :=
    integral_sq_le_of_eLpNorm_le (hfL2.sub hgL2) hδ0.le hgle
  have hfgi : Integrable (fun x => (f x - g x) ^ 2) := (hfL2.sub hgL2).integrable_sq
  -- symmetrisation
  obtain ⟨hfgsi, hfgs⟩ := integral_sq_sym_le hf.even hfm hgc hfgi
  -- the window
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = (1 + b₀) / 2 := ⟨_, rfl⟩
  have hb₀b : b₀ < b := by rw [hbdef]; linarith
  have hb1 : b < 1 := by rw [hbdef]; linarith
  obtain ⟨hLi, hint⟩ := window_close hf hb₀0.le hb₀b hb1 hδ0 hgs hfgsi (hfgs.trans hfg) htail
  have hud : ∫ x, (window b₀ b δ g x ^ 2 - f x) ^ 2 ≤ d ^ 2 := by
    have : 12 * δ ^ 2 ≤ d ^ 2 := by rw [hδ]; nlinarith
    linarith
  refine ⟨window b₀ b δ g, b, by linarith, hb1, window_contDiff hδ0 hgs, window_even b₀ b δ g,
    fun x hx => window_supp g hb₀0.le hb₀b hx, window_zero_ne g hb₀0.le hb₀b hδ0, ?_⟩
  exact Qf_normalised_le hC hf (window_contDiff hδ0 hgs).continuous hb1
    (fun x hx => window_supp g hb₀0.le hb₀b hx) hd0 hd14 hη hLi hud hdη

end Families.Phase4.A
