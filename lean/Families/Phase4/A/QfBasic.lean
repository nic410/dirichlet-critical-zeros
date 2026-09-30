/-
Basic analysis of the functional
`𝒬_F(f) = ∫ f² + ∬ f(x) f(y) F(|x−y|) dx dy` (`Families.Qf`) for general kernels `F`.

* integrability of the kernel integrands (generalising the private lemmas of `Families.PLip`);
* `L¹` control from `L²` control on bounded support (`integral_abs_le_of_sq`);
* homogeneity `𝒬_F(u/c) = 𝒬_F(u)/c²` (`Qf_div`);
* **continuity of `𝒬_F` on `L¹ ∩ L²`** (`main.tex` §7.3, proof of `lem:windows`, first sentence), in the
  explicit form `𝒬_F(u) ≤ 𝒬_F(w) + d · κ(A, K)` when `‖u − w‖₂ ≤ d`, `‖u‖₂², ‖w‖₂² ≤ A`, `0 ≤ F ≤ K`
  and `u, w` vanish outside `[−1, 1]` (`Qf_le_of_close`);
* comparison of two kernels that differ by `a` off a band `(1−2ε, 1+2ε)` and by `a + k` on it, for a
  bounded window (`Qf_le_of_band`): this is the uniform-in-`C̃` replacement of the paper's dominated
  convergence step (proofs of Theorems 5.16 and 1.1, §7.3).
-/
import Families.Variational

noncomputable section

open MeasureTheory Filter Topology

namespace Families.Phase4.A

/-! ### Integrability of kernel integrands -/

lemma aesm_kernel {F : ℝ → ℝ} (hF : Measurable F) :
    AEStronglyMeasurable (fun z : ℝ × ℝ => F |z.1 - z.2|) (volume.prod volume) :=
  (hF.comp (measurable_fst.sub measurable_snd).abs).aestronglyMeasurable

lemma integrable_kernel {u w : ℝ → ℝ} (hu : Integrable u) (hw : Integrable w) {F : ℝ → ℝ}
    (hF : Measurable F) {K : ℝ} (hK : ∀ α, 0 ≤ α → |F α| ≤ K) :
    Integrable (fun z : ℝ × ℝ => u z.1 * w z.2 * F |z.1 - z.2|) (volume.prod volume) := by
  have hprod : Integrable (fun z : ℝ × ℝ => u z.1 * w z.2) (volume.prod volume) := hu.mul_prod hw
  refine hprod.mul_bdd (c := K) (aesm_kernel hF) (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]
  exact hK _ (abs_nonneg _)

lemma inner_integrable {u w : ℝ → ℝ} (hw : Integrable w) {F : ℝ → ℝ}
    (hF : Measurable F) {K : ℝ} (hK : ∀ α, 0 ≤ α → |F α| ≤ K) (x : ℝ) :
    Integrable (fun y => u x * w y * F |x - y|) := by
  refine (hw.const_mul (u x)).mul_bdd (c := K) ?_ (Eventually.of_forall fun y => ?_)
  · exact (hF.comp (measurable_const.sub measurable_id).abs).aestronglyMeasurable
  · rw [Real.norm_eq_abs]; exact hK _ (abs_nonneg _)

lemma outer_integrable {u w : ℝ → ℝ} (hu : Integrable u) (hw : Integrable w) {F : ℝ → ℝ}
    (hF : Measurable F) {K : ℝ} (hK : ∀ α, 0 ≤ α → |F α| ≤ K) :
    Integrable (fun x => ∫ y, u x * w y * F |x - y|) :=
  (integrable_kernel hu hw hF hK).integral_prod_left

/-! ### `L¹` from `L²` on bounded support -/

lemma integrable_indicator_Icc (R : ℝ) :
    Integrable ((Set.Icc (-R) R).indicator (fun _ => (1 : ℝ))) :=
  (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc

lemma integral_indicator_Icc {R : ℝ} (hR : 0 ≤ R) :
    ∫ x, (Set.Icc (-R) R).indicator (fun _ => (1 : ℝ)) x = 2 * R := by
  rw [integral_indicator_const _ measurableSet_Icc, Real.volume_real_Icc_of_le (by linarith)]
  simp; ring

/-- If `e` vanishes outside `[−R, R]` and `e² ∈ L¹`, then `e ∈ L¹` and, for every `d > 0`,
`∫|e| ≤ (∫e²/d + 2Rd)/2` (from `2|e|d ≤ e² + d²`). -/
lemma integral_abs_le_of_sq {e : ℝ → ℝ} (he : AEStronglyMeasurable e)
    (he2 : Integrable (fun x => e x ^ 2)) {R : ℝ} (hR : 0 ≤ R) (hs : ∀ x, R < |x| → e x = 0)
    {d : ℝ} (hd : 0 < d) :
    Integrable e ∧ ∫ x, |e x| ≤ ((∫ x, e x ^ 2) / d + 2 * R * d) / 2 := by
  set S := Set.Icc (-R) R
  set g : ℝ → ℝ := fun x => (e x ^ 2 / d + d * S.indicator (fun _ => (1 : ℝ)) x) / 2 with hg
  have hgi : Integrable g :=
    ((he2.div_const d).add ((integrable_indicator_Icc R).const_mul d)).div_const 2
  have hpt : ∀ x, |e x| ≤ g x := by
    intro x
    by_cases hx : x ∈ S
    · simp only [hg, Set.indicator_of_mem hx, mul_one]
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), div_add' _ _ _ hd.ne', le_div_iff₀ hd]
      have h1 : e x ^ 2 = |e x| ^ 2 := (sq_abs _).symm
      nlinarith [sq_nonneg (|e x| - d)]
    · have hx' : R < |x| := by
        simp only [S, Set.mem_Icc, not_and_or, not_le] at hx
        rcases hx with hx | hx
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; exact hx
      simp only [hg, Set.indicator_of_notMem hx, hs x hx', mul_zero, abs_zero]
      norm_num
  have hei : Integrable e := hgi.mono' he (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hpt x)
  refine ⟨hei, ?_⟩
  calc ∫ x, |e x| ≤ ∫ x, g x := integral_mono hei.abs hgi hpt
    _ = ((∫ x, e x ^ 2) / d + 2 * R * d) / 2 := by
      simp only [hg]
      rw [integral_div, integral_add (he2.div_const d) ((integrable_indicator_Icc R).const_mul d),
        integral_div, integral_const_mul, integral_indicator_Icc hR]
      ring

/-! ### Homogeneity and nonnegativity -/

lemma Qf_div (F u : ℝ → ℝ) (c : ℝ) : Qf F (fun x => u x / c) = Qf F u / c ^ 2 := by
  unfold Qf
  have h1 : ∀ x, (u x / c) ^ 2 = u x ^ 2 / c ^ 2 := fun x => by rw [div_pow]
  have h2 : ∀ x y, u x / c * (u y / c) * F |x - y| = u x * u y * F |x - y| / c ^ 2 :=
    fun x y => by ring
  simp_rw [h1, h2, integral_div, add_div]

lemma Qf_nonneg_of {F u : ℝ → ℝ} (hF : ∀ α, 0 ≤ α → 0 ≤ F α) (hu : ∀ x, 0 ≤ u x) :
    0 ≤ Qf F u := by
  unfold Qf
  refine add_nonneg (integral_nonneg fun x => sq_nonneg _)
    (integral_nonneg fun x => integral_nonneg fun y => ?_)
  exact mul_nonneg (mul_nonneg (hu x) (hu y)) (hF _ (abs_nonneg _))

/-! ### Continuity of `𝒬_F` on `L¹ ∩ L²` (explicit form) -/

/-- **Continuity of `𝒬_F`** (the estimate in the proof of `lem:windows`, Lemma 7.2). Let
`F` be measurable with `0 ≤ F ≤ K` on `[0, ∞)`, and let `u, w` vanish outside `[−1, 1]`, with
`∫u², ∫w² ≤ A` and `∫(u − w)² ≤ d²`, `d > 0`. Then
`𝒬_F(u) ≤ 𝒬_F(w) + d ((1 + 4A)/2 + 3K(A + 2)/2)`. -/
theorem Qf_le_of_close {F : ℝ → ℝ} (hF : Measurable F) {K : ℝ}
    (hK : ∀ α, 0 ≤ α → 0 ≤ F α ∧ F α ≤ K)
    {u w : ℝ → ℝ} (hu : AEStronglyMeasurable u) (hw : AEStronglyMeasurable w)
    (hu2 : Integrable (fun x => u x ^ 2)) (hw2 : Integrable (fun x => w x ^ 2))
    (hsu : ∀ x, 1 < |x| → u x = 0) (hsw : ∀ x, 1 < |x| → w x = 0)
    {A d : ℝ} (hd : 0 < d) (hAu : ∫ x, u x ^ 2 ≤ A) (hAw : ∫ x, w x ^ 2 ≤ A)
    (hud : ∫ x, (u x - w x) ^ 2 ≤ d ^ 2) :
    Qf F u ≤ Qf F w + d * ((1 + 4 * A) / 2 + 3 * K * (A + 2) / 2) := by
  have hK0 : 0 ≤ K := (hK 0 le_rfl).1.trans (hK 0 le_rfl).2
  have hKabs : ∀ α, 0 ≤ α → |F α| ≤ K := fun α hα => by
    rw [abs_of_nonneg (hK α hα).1]; exact (hK α hα).2
  -- `(u − w)² ∈ L¹`
  have hsub : AEStronglyMeasurable (fun x => u x - w x) := hu.sub hw
  have huw2 : Integrable (fun x => (u x - w x) ^ 2) := by
    refine ((hu2.const_mul 2).fun_add (hw2.const_mul 2)).mono' (hsub.pow 2)
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (u x + w x)]
  -- `L¹` bounds
  obtain ⟨hui, hua⟩ := integral_abs_le_of_sq hu hu2 zero_le_one hsu one_pos
  obtain ⟨hwi, hwa⟩ := integral_abs_le_of_sq hw hw2 zero_le_one hsw one_pos
  have hsuw : ∀ x, 1 < |x| → u x - w x = 0 := fun x hx => by rw [hsu x hx, hsw x hx, sub_zero]
  obtain ⟨-, hea⟩ := integral_abs_le_of_sq (e := fun x => u x - w x) hsub huw2 zero_le_one hsuw hd
  have hua' : ∫ x, |u x| ≤ (A + 2) / 2 := by
    have := hua; rw [div_one] at this; linarith
  have hwa' : ∫ x, |w x| ≤ (A + 2) / 2 := by
    have := hwa; rw [div_one] at this; linarith
  have hea' : ∫ x, |u x - w x| ≤ 3 * d / 2 := by
    have h1 : (∫ x, (u x - w x) ^ 2) / d ≤ d := by
      rw [div_le_iff₀ hd]; nlinarith
    linarith
  have hua0 : 0 ≤ ∫ x, |u x| := integral_nonneg fun _ => abs_nonneg _
  have hwa0 : 0 ≤ ∫ x, |w x| := integral_nonneg fun _ => abs_nonneg _
  have hea0 : 0 ≤ ∫ x, |u x - w x| := integral_nonneg fun _ => abs_nonneg _
  -- the `L²` term
  have hsq : (∫ x, u x ^ 2) ≤ (∫ x, w x ^ 2) + d * (1 + 4 * A) / 2 := by
    have hpt : ∀ x, u x ^ 2 ≤ w x ^ 2 + ((u x - w x) ^ 2 / (2 * d) + d * (u x ^ 2 + w x ^ 2)) := by
      intro x
      have h2d : 0 < 2 * d := by linarith
      rw [div_add' _ _ _ h2d.ne', ← sub_le_iff_le_add', le_div_iff₀ h2d]
      nlinarith [sq_nonneg ((u x - w x) - d * (u x + w x)), sq_nonneg (u x - w x),
        sq_nonneg (u x + w x)]
    have hs2 : Integrable (fun x => u x ^ 2 + w x ^ 2) := hu2.fun_add hw2
    have hA1 : Integrable (fun x => (u x - w x) ^ 2 / (2 * d)) := huw2.div_const _
    have hA2 : Integrable (fun x => d * (u x ^ 2 + w x ^ 2)) := hs2.const_mul d
    have hA3 : Integrable (fun x => (u x - w x) ^ 2 / (2 * d) + d * (u x ^ 2 + w x ^ 2)) :=
      hA1.fun_add hA2
    have hR : Integrable (fun x => w x ^ 2 + ((u x - w x) ^ 2 / (2 * d) + d * (u x ^ 2 + w x ^ 2))) :=
      hw2.fun_add hA3
    calc (∫ x, u x ^ 2) ≤ ∫ x, (w x ^ 2 + ((u x - w x) ^ 2 / (2 * d) + d * (u x ^ 2 + w x ^ 2))) :=
          integral_mono hu2 hR hpt
      _ = (∫ x, w x ^ 2) + ((∫ x, (u x - w x) ^ 2) / (2 * d) +
            d * ((∫ x, u x ^ 2) + ∫ x, w x ^ 2)) := by
          rw [integral_add hw2 hA3, integral_add hA1 hA2, integral_div,
            integral_const_mul, integral_add hu2 hw2]
      _ ≤ (∫ x, w x ^ 2) + d * (1 + 4 * A) / 2 := by
          have h1 : (∫ x, (u x - w x) ^ 2) / (2 * d) ≤ d / 2 := by
            rw [div_le_iff₀ (by linarith)]; nlinarith
          have h2 : d * ((∫ x, u x ^ 2) + ∫ x, w x ^ 2) ≤ d * (2 * A) :=
            mul_le_mul_of_nonneg_left (by linarith) hd.le
          linarith
  -- the double integral
  have hin : ∀ x, ∫ y, u x * u y * F |x - y| ≤ ∫ y, (w x * w y * F |x - y| +
      (K * |u x - w x|) * |u y| + (K * |w x|) * |u y - w y|) := by
    intro x
    refine integral_mono (inner_integrable hui hF hKabs x)
      (((inner_integrable hwi hF hKabs x).fun_add (hui.abs.const_mul _)).fun_add
        ((hui.sub' hwi).abs.const_mul _)) fun y => ?_
    have hG0 := (hK |x - y| (abs_nonneg _)).1
    have hGK := (hK |x - y| (abs_nonneg _)).2
    set G := F |x - y|
    have h1 : u x * u y - w x * w y ≤ |u x - w x| * |u y| + |w x| * |u y - w y| := by
      calc u x * u y - w x * w y = (u x - w x) * u y + w x * (u y - w y) := by ring
        _ ≤ |(u x - w x) * u y| + |w x * (u y - w y)| :=
          add_le_add (le_abs_self _) (le_abs_self _)
        _ = _ := by rw [abs_mul, abs_mul]
    have h2 : (u x * u y - w x * w y) * G ≤ (|u x - w x| * |u y| + |w x| * |u y - w y|) * G :=
      mul_le_mul_of_nonneg_right h1 hG0
    have h3 : (|u x - w x| * |u y| + |w x| * |u y - w y|) * G ≤
        (|u x - w x| * |u y| + |w x| * |u y - w y|) * K :=
      mul_le_mul_of_nonneg_left hGK (by positivity)
    nlinarith [h2, h3]
  have hdiffi : Integrable (fun y => u y - w y) := hui.sub' hwi
  have hin' : ∀ x, ∫ y, u x * u y * F |x - y| ≤ (∫ y, w x * w y * F |x - y|) +
      (K * ∫ y, |u y|) * |u x - w x| + (K * ∫ y, |u y - w y|) * |w x| := by
    intro x
    refine (hin x).trans (le_of_eq ?_)
    have i1 : Integrable (fun y => w x * w y * F |x - y|) := inner_integrable hwi hF hKabs x
    have i2 : Integrable (fun y => K * |u x - w x| * |u y|) := hui.abs.const_mul _
    have i3 : Integrable (fun y => K * |w x| * |u y - w y|) := hdiffi.abs.const_mul _
    rw [integral_add (i1.fun_add i2) i3, integral_add i1 i2, integral_const_mul, integral_const_mul]
    ring
  have hdbl : (∫ x, ∫ y, u x * u y * F |x - y|) ≤ (∫ x, ∫ y, w x * w y * F |x - y|) +
      (K * ∫ y, |u y|) * (∫ x, |u x - w x|) + (K * ∫ y, |u y - w y|) * ∫ x, |w x| := by
    have j1 : Integrable (fun x => ∫ y, w x * w y * F |x - y|) := outer_integrable hwi hwi hF hKabs
    have j2 : Integrable (fun x => (K * ∫ y, |u y|) * |u x - w x|) := hdiffi.abs.const_mul _
    have j3 : Integrable (fun x => (K * ∫ y, |u y - w y|) * |w x|) := hwi.abs.const_mul _
    have hRi : Integrable (fun x => (∫ y, w x * w y * F |x - y|) +
        (K * ∫ y, |u y|) * |u x - w x| + (K * ∫ y, |u y - w y|) * |w x|) :=
      (j1.fun_add j2).fun_add j3
    calc (∫ x, ∫ y, u x * u y * F |x - y|)
        ≤ ∫ x, ((∫ y, w x * w y * F |x - y|) +
            (K * ∫ y, |u y|) * |u x - w x| + (K * ∫ y, |u y - w y|) * |w x|) :=
          integral_mono (outer_integrable hui hui hF hKabs) hRi hin'
      _ = _ := by
          rw [integral_add (j1.fun_add j2) j3, integral_add j1 j2,
            integral_const_mul, integral_const_mul]
  have hcross : (K * ∫ y, |u y|) * (∫ x, |u x - w x|) + (K * ∫ y, |u y - w y|) * ∫ x, |w x|
      ≤ d * (3 * K * (A + 2) / 2) := by
    have e1 : (K * ∫ y, |u y|) * (∫ x, |u x - w x|) + (K * ∫ y, |u y - w y|) * ∫ x, |w x|
        = K * ((∫ x, |u x - w x|) * ((∫ y, |u y|) + ∫ x, |w x|)) := by ring
    rw [e1]
    have h1 : (∫ x, |u x - w x|) * ((∫ y, |u y|) + ∫ x, |w x|) ≤ (3 * d / 2) * (A + 2) := by
      have := add_le_add hua' hwa'
      calc (∫ x, |u x - w x|) * ((∫ y, |u y|) + ∫ x, |w x|)
          ≤ (3 * d / 2) * ((∫ y, |u y|) + ∫ x, |w x|) :=
            mul_le_mul_of_nonneg_right hea' (by linarith)
        _ ≤ (3 * d / 2) * (A + 2) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    calc K * ((∫ x, |u x - w x|) * ((∫ y, |u y|) + ∫ x, |w x|)) ≤ K * ((3 * d / 2) * (A + 2)) :=
          mul_le_mul_of_nonneg_left h1 hK0
      _ = d * (3 * K * (A + 2) / 2) := by ring
  unfold Qf
  nlinarith [hsq, hdbl, hcross]

/-! ### Comparison of kernels off a band -/

/-- The indicator of an open interval, as an integrable function. -/
lemma integrable_indicator_Ioo (p q : ℝ) :
    Integrable ((Set.Ioo p q).indicator (fun _ => (1 : ℝ))) :=
  ((continuous_const.integrableOn_Icc (a := p) (b := q)).mono_set Set.Ioo_subset_Icc_self)
    |>.integrable_indicator measurableSet_Ioo

lemma integral_indicator_Ioo {p q : ℝ} (hpq : p ≤ q) :
    ∫ x, (Set.Ioo p q).indicator (fun _ => (1 : ℝ)) x = q - p := by
  rw [integral_indicator_const _ measurableSet_Ioo, Real.volume_real_Ioo_of_le hpq]
  simp

/-- The band `1 − 2ε < |x − y| < 1 + 2ε`, as a function of `y`, is covered by two intervals of
length `4ε`. -/
lemma band_indicator_le (x ε y : ℝ) :
    (Set.Ioo (1 - 2 * ε) (1 + 2 * ε)).indicator (fun _ => (1 : ℝ)) |x - y| ≤
      (Set.Ioo (x - 1 - 2 * ε) (x - 1 + 2 * ε)).indicator (fun _ => (1 : ℝ)) y +
      (Set.Ioo (x + 1 - 2 * ε) (x + 1 + 2 * ε)).indicator (fun _ => (1 : ℝ)) y := by
  have h1 : 0 ≤ (Set.Ioo (x - 1 - 2 * ε) (x - 1 + 2 * ε)).indicator (fun _ => (1 : ℝ)) y :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have h2 : 0 ≤ (Set.Ioo (x + 1 - 2 * ε) (x + 1 + 2 * ε)).indicator (fun _ => (1 : ℝ)) y :=
    Set.indicator_nonneg (fun _ _ => zero_le_one) _
  by_cases hb : |x - y| ∈ Set.Ioo (1 - 2 * ε) (1 + 2 * ε)
  · rw [Set.indicator_of_mem hb]
    rcases le_or_gt 0 (x - y) with hxy | hxy
    · rw [abs_of_nonneg hxy] at hb
      have : y ∈ Set.Ioo (x - 1 - 2 * ε) (x - 1 + 2 * ε) := ⟨by linarith [hb.2], by linarith [hb.1]⟩
      rw [Set.indicator_of_mem this]; linarith
    · rw [abs_of_neg hxy] at hb
      have : y ∈ Set.Ioo (x + 1 - 2 * ε) (x + 1 + 2 * ε) := ⟨by linarith [hb.1], by linarith [hb.2]⟩
      rw [Set.indicator_of_mem this]; linarith
  · rw [Set.indicator_of_notMem hb]; linarith

/-- **Kernel comparison off a band.** Let `w ≥ 0` be integrable and bounded by `M`, `∫ w = 1`, and
let `F, G` be measurable, bounded on `[0, ∞)`, with `F ≤ G + a + k·1_{(1−2ε, 1+2ε)}` on `[0, ∞)`,
`k, ε ≥ 0`. Then `𝒬_F(w) ≤ 𝒬_G(w) + a + 8kMε`. (Used with `G = F_C`, `a = 2Cε₃`: this is the
explicit, uniform-in-the-profile form of the dominated convergence step `F_ε → F_C` off `{1}` of
the proof of Theorem 5.16, §7.3.) -/
theorem Qf_le_of_band {F G : ℝ → ℝ} (hFm : Measurable F) (hGm : Measurable G) {K : ℝ}
    (hF : ∀ α, 0 ≤ α → |F α| ≤ K) (hG : ∀ α, 0 ≤ α → |G α| ≤ K)
    {w : ℝ → ℝ} (hw0 : ∀ x, 0 ≤ w x) {M : ℝ} (hwM : ∀ x, w x ≤ M) (hwi : Integrable w)
    (hw1 : ∫ x, w x = 1) {a k ε : ℝ} (hk : 0 ≤ k) (hε : 0 ≤ ε)
    (hFG : ∀ α, 0 ≤ α →
      F α ≤ G α + a + k * (Set.Ioo (1 - 2 * ε) (1 + 2 * ε)).indicator (fun _ => (1 : ℝ)) α) :
    Qf F w ≤ Qf G w + a + 8 * k * M * ε := by
  have hM0 : 0 ≤ M := (hw0 0).trans (hwM 0)
  -- inner bound
  have hin : ∀ x, ∫ y, w x * w y * F |x - y| ≤
      (∫ y, w x * w y * G |x - y|) + (a + 8 * k * M * ε) * w x := by
    intro x
    set I₁ := Set.Ioo (x - 1 - 2 * ε) (x - 1 + 2 * ε)
    set I₂ := Set.Ioo (x + 1 - 2 * ε) (x + 1 + 2 * ε)
    have i1 : Integrable (fun y => w x * w y * G |x - y|) := inner_integrable hwi hGm hG x
    have i2 : Integrable (fun y => (a * w x) * w y) := hwi.const_mul _
    have i3 : Integrable (fun y => (k * M * w x) * I₁.indicator (fun _ => (1 : ℝ)) y) :=
      (integrable_indicator_Ioo _ _).const_mul _
    have i4 : Integrable (fun y => (k * M * w x) * I₂.indicator (fun _ => (1 : ℝ)) y) :=
      (integrable_indicator_Ioo _ _).const_mul _
    have hpt : ∀ y, w x * w y * F |x - y| ≤ w x * w y * G |x - y| + (a * w x) * w y +
        (k * M * w x) * I₁.indicator (fun _ => (1 : ℝ)) y +
        (k * M * w x) * I₂.indicator (fun _ => (1 : ℝ)) y := by
      intro y
      have hxy : 0 ≤ w x * w y := mul_nonneg (hw0 x) (hw0 y)
      have hband := band_indicator_le x ε y
      set B := (Set.Ioo (1 - 2 * ε) (1 + 2 * ε)).indicator (fun _ => (1 : ℝ)) |x - y|
      have hB0 : 0 ≤ B := Set.indicator_nonneg (fun _ _ => zero_le_one) _
      have e1 : w x * w y * F |x - y| ≤ w x * w y * (G |x - y| + a + k * B) :=
        mul_le_mul_of_nonneg_left (hFG _ (abs_nonneg _)) hxy
      have e2 : w y * B ≤ M * (I₁.indicator (fun _ => (1 : ℝ)) y +
          I₂.indicator (fun _ => (1 : ℝ)) y) := mul_le_mul (hwM y) hband hB0 hM0
      have e3 : k * w x * (w y * B) ≤ k * w x * (M * (I₁.indicator (fun _ => (1 : ℝ)) y +
          I₂.indicator (fun _ => (1 : ℝ)) y)) :=
        mul_le_mul_of_nonneg_left e2 (mul_nonneg hk (hw0 x))
      nlinarith [e1, e3]
    calc ∫ y, w x * w y * F |x - y|
        ≤ ∫ y, (w x * w y * G |x - y| + (a * w x) * w y +
            (k * M * w x) * I₁.indicator (fun _ => (1 : ℝ)) y +
            (k * M * w x) * I₂.indicator (fun _ => (1 : ℝ)) y) :=
          integral_mono (inner_integrable hwi hFm hF x)
            (((i1.fun_add i2).fun_add i3).fun_add i4) hpt
      _ = (∫ y, w x * w y * G |x - y|) + (a + 8 * k * M * ε) * w x := by
          rw [integral_add ((i1.fun_add i2).fun_add i3) i4, integral_add (i1.fun_add i2) i3,
            integral_add i1 i2, integral_const_mul, integral_const_mul, integral_const_mul, hw1,
            integral_indicator_Ioo (by linarith), integral_indicator_Ioo (by linarith)]
          ring
  have j1 : Integrable (fun x => ∫ y, w x * w y * G |x - y|) := outer_integrable hwi hwi hGm hG
  have j2 : Integrable (fun x => (a + 8 * k * M * ε) * w x) := hwi.const_mul _
  have hdbl : (∫ x, ∫ y, w x * w y * F |x - y|) ≤
      (∫ x, ∫ y, w x * w y * G |x - y|) + (a + 8 * k * M * ε) := by
    calc (∫ x, ∫ y, w x * w y * F |x - y|)
        ≤ ∫ x, ((∫ y, w x * w y * G |x - y|) + (a + 8 * k * M * ε) * w x) :=
          integral_mono (outer_integrable hwi hwi hFm hF) (j1.fun_add j2) hin
      _ = _ := by rw [integral_add j1 j2, integral_const_mul, hw1, mul_one]
  unfold Qf
  linarith

end Families.Phase4.A
