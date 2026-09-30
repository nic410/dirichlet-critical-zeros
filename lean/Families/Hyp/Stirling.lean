/-
# Discharging `StirlingDigamma` (classical input (b4)) from `zeta23`

`Families.Hyp.StirlingDigamma_proof : StirlingDigamma`.

With `b = (1/2 + 𝔞)/2 = 1/4 + 𝔞/2 ∈ {1/4, 3/4}` we have `(1/2 + 𝔞 + it)/2 = b + i(t/2)`, and Mathlib's
`Complex.digamma` is by definition `logDeriv Complex.Gamma`, so
`digammaRe 𝔞 t = Re ψ(b + i t/2)` (`digammaRe_eq`). The three clauses:

* (i) `Zeta23.StirlingVert.re_digamma_stirling'` (`|Re ψ(b+is) − log|s|| ≤ 5/s²` for `0 < b ≤ 1`,
  `|s| ≥ 1/2`) at `s = t/2`: the error is `20/t² ≤ 20/t` for `t ≥ 1`.
* (ii) For `|t| ≥ 1` the same Stirling bound and `|log(|t|/2)| ≤ log(|t|+2)`; for `|t| ≤ 1`, the
  monotonicity `Zeta23.MuFields.re_digamma_mono` of `s ↦ Re ψ(b+is)` on `s ≥ 0` and its evenness
  (from the real series `Zeta23.MuFields.re_digamma_vertical`, which depends on `s²` only) squeeze
  `Re ψ(b + i t/2)` between `Re ψ(b)` and `Re ψ(b + i/2)`.
* (iii) The chain rule and the trigamma series `Zeta23.Stirling.hasSum_trigamma`
  (`ψ'(z) = ∑ 1/(z+n)²`): `|∂_t Re ψ(b + it/2)| ≤ ‖ψ'‖/2 ≤ ½ ∑ ((b+n)² + t²/4)⁻¹`, and
  `Zeta23.MuFields.trigamma_tail_le` (`∑ ((1/4+n)² + s²)⁻¹ ≤ 12/|s|`) with `b ≥ 1/4` gives `12/t`.

The constant is `C = 100 + 2(B_{1/4} + B_{3/4})` with `B_b = |Re ψ(b)| + |Re ψ(b + i/2)|`.
-/
import Families.Classical
import Zeta23.GammaFacts.StirlingVert

noncomputable section

open Complex

namespace Families.Hyp

open Families

/-- `Re ψ(b + i s)`. -/
def reDigammaLine (b s : ℝ) : ℝ := (Complex.digamma ((b : ℂ) + Complex.I * (s : ℂ))).re

/-- `digammaRe 𝔞 t = Re ψ(1/4 + 𝔞/2 + i t/2)`. -/
lemma digammaRe_eq (a t : ℝ) : digammaRe a t = reDigammaLine (1 / 4 + a / 2) (t / 2) := by
  unfold digammaRe reDigammaLine
  rw [← Complex.digamma_def]
  congr 2
  push_cast
  ring

lemma abscissa_bounds {a : ℝ} (ha : a = 0 ∨ a = 1) :
    1 / 4 ≤ 1 / 4 + a / 2 ∧ 1 / 4 + a / 2 < 1 := by
  rcases ha with rfl | rfl <;> norm_num

/-- Evenness of `s ↦ Re ψ(b + is)` (the real series depends on `s²` only). -/
lemma reDigammaLine_neg {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) (s : ℝ) :
    reDigammaLine b (-s) = reDigammaLine b s := by
  unfold reDigammaLine
  rw [Zeta23.MuFields.re_digamma_vertical hb0 hb1, Zeta23.MuFields.re_digamma_vertical hb0 hb1,
    neg_sq]

/-- The bound near the real axis: `|Re ψ(b + is)| ≤ |Re ψ(b)| + |Re ψ(b + i/2)|` for `|s| ≤ 1/2`. -/
lemma abs_reDigammaLine_le_of_small {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) {s : ℝ}
    (hs : |s| ≤ 1 / 2) :
    |reDigammaLine b s| ≤ |reDigammaLine b 0| + |reDigammaLine b (1 / 2)| := by
  have heven : reDigammaLine b s = reDigammaLine b |s| := by
    rcases le_total 0 s with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, reDigammaLine_neg hb0 hb1]
  have hmono := Zeta23.MuFields.re_digamma_mono hb0 hb1
  have h1 : reDigammaLine b 0 ≤ reDigammaLine b |s| :=
    hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr (abs_nonneg s)) (abs_nonneg s)
  have h2 : reDigammaLine b |s| ≤ reDigammaLine b (1 / 2) :=
    hmono (Set.mem_Ici.mpr (abs_nonneg s)) (Set.mem_Ici.mpr (by norm_num)) hs
  rw [heven, abs_le]
  constructor
  · have := neg_abs_le (reDigammaLine b 0)
    have := abs_nonneg (reDigammaLine b (1 / 2))
    linarith
  · have := le_abs_self (reDigammaLine b (1 / 2))
    have := abs_nonneg (reDigammaLine b 0)
    linarith

/-- Stirling on the line, from `zeta23`: `|Re ψ(b + it/2) − log(|t|/2)| ≤ 20/t²` for `|t| ≥ 1`. -/
lemma reDigammaLine_stirling {b : ℝ} (hb0 : 0 < b) (hb1 : b ≤ 1) {t : ℝ} (ht : 1 ≤ |t|) :
    |reDigammaLine b (t / 2) - Real.log (|t| / 2)| ≤ 20 / t ^ 2 := by
  have ht' : 1 / 2 ≤ |t / 2| := by rw [abs_div, abs_two]; linarith
  have h := Zeta23.StirlingVert.re_digamma_stirling' hb0 hb1 ht'
  have ht0 : 0 < t ^ 2 := by
    have : 0 < |t| := by linarith
    rw [← sq_abs]; positivity
  unfold reDigammaLine
  rw [abs_div, abs_two] at h
  calc _ ≤ 5 / (t / 2) ^ 2 := h
    _ = 20 / t ^ 2 := by field_simp; norm_num

/-- `|log(|t|/2)| ≤ log(|t| + 2)` for `|t| ≥ 1`. -/
lemma abs_log_half_le {t : ℝ} (ht : 1 ≤ |t|) : |Real.log (|t| / 2)| ≤ Real.log (|t| + 2) := by
  have h0 : 0 < |t| / 2 := by positivity
  rw [abs_le]
  constructor
  · -- `log(|t|/2) ≥ log(1/2) = −log 2 ≥ −log(|t|+2)`
    have h1 : Real.log (1 / 2) ≤ Real.log (|t| / 2) := Real.log_le_log (by norm_num) (by linarith)
    have h2 : Real.log 2 ≤ Real.log (|t| + 2) := Real.log_le_log (by norm_num) (by linarith)
    rw [one_div, Real.log_inv] at h1
    linarith
  · exact Real.log_le_log h0 (by linarith)

/-- `1/2 ≤ log 2 ≤ log(|t| + 2)`. -/
lemma half_le_log_abs_add_two (t : ℝ) : 1 / 2 ≤ Real.log (|t| + 2) := by
  have h1 : Real.log 2 ≤ Real.log (|t| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have h2 := Real.log_two_gt_d9
  linarith

/-- The derivative bound: `|∂_t Re ψ(b + it/2)| ≤ 12/|t|` for `1/4 ≤ b < 1`, `|t| ≥ 1`. -/
lemma abs_deriv_reDigammaLine_le {b : ℝ} (hb0 : 1 / 4 ≤ b) (hb1 : b < 1) {t : ℝ} (ht : 1 ≤ |t|) :
    |deriv (fun t : ℝ => reDigammaLine b (t / 2)) t| ≤ 12 / |t| := by
  have hbpos : 0 < b := by linarith
  have ht0 : (0 : ℝ) < |t| := by linarith
  set z : ℂ := (b : ℂ) + (Complex.I / 2) * (t : ℂ) with hz
  have hz_eq : z = (b : ℂ) + Complex.I * ((t / 2 : ℝ) : ℂ) := by
    rw [hz]; push_cast; ring
  have hmem : z ∈ Complex.integerComplement := by
    rw [hz_eq]; exact Zeta23.MuFields.abscissa_mem hbpos hb1 (t / 2)
  have hψd : DifferentiableAt ℂ Complex.digamma z :=
    Zeta23.Stirling.differentiableAt_digamma hmem
  -- the chain rule
  have hinner : HasDerivAt (fun x : ℝ => (b : ℂ) + (Complex.I / 2) * (x : ℂ)) (Complex.I / 2) t := by
    have h1 : HasDerivAt (fun x : ℝ => ((x : ℝ) : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    simpa using (h1.const_mul (Complex.I / 2)).const_add (b : ℂ)
  have hcomp : HasDerivAt (fun x : ℝ => Complex.digamma ((b : ℂ) + (Complex.I / 2) * (x : ℂ)))
      ((Complex.I / 2) • deriv Complex.digamma z) t :=
    HasDerivAt.scomp t hψd.hasDerivAt hinner
  have hre : HasDerivAt (fun x : ℝ => (Complex.digamma ((b : ℂ) + (Complex.I / 2) * (x : ℂ))).re)
      (((Complex.I / 2) • deriv Complex.digamma z).re) t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hcomp
  have hfun : (fun t : ℝ => reDigammaLine b (t / 2)) =
      fun x : ℝ => (Complex.digamma ((b : ℂ) + (Complex.I / 2) * (x : ℂ))).re := by
    funext x
    unfold reDigammaLine
    congr 3
    push_cast
    ring
  rw [hfun, hre.deriv]
  -- `‖ψ'(z)‖ ≤ 24/|t|` by the trigamma series
  have htri := Zeta23.Stirling.hasSum_trigamma hmem
  have hnorm_term : ∀ n : ℕ, ‖(1 : ℂ) / (z + n) ^ 2‖ = ((b + n) ^ 2 + (t / 2) ^ 2)⁻¹ := by
    intro n
    have hre2 : (z + n).re = b + n := by rw [hz_eq]; simp
    have him2 : (z + n).im = t / 2 := by rw [hz_eq]; simp
    rw [norm_div, norm_one, norm_pow, one_div]
    congr 1
    rw [Complex.sq_norm, Complex.normSq_apply, hre2, him2]
    ring
  have hcmp : ∀ n : ℕ, ((b + n) ^ 2 + (t / 2) ^ 2)⁻¹ ≤ (((1 / 4 : ℝ) + n) ^ 2 + (t / 2) ^ 2)⁻¹ := by
    intro n
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    apply inv_anti₀ (by positivity)
    have : ((1 / 4 : ℝ) + n) ^ 2 ≤ (b + n) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity); linarith
    linarith
  have hsum_q := Zeta23.MuFields.summable_quarter_line (t / 2)
  have hsum_b : Summable (fun n : ℕ => ((b + n) ^ 2 + (t / 2) ^ 2)⁻¹) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hcmp hsum_q
  have hsummable_norm : Summable (fun n : ℕ => ‖(1 : ℂ) / (z + n) ^ 2‖) :=
    hsum_b.congr fun n => (hnorm_term n).symm
  have hψ' : ‖deriv Complex.digamma z‖ ≤ 24 / |t| := by
    rw [← htri.tsum_eq]
    calc ‖∑' n : ℕ, (1 : ℂ) / (z + n) ^ 2‖ ≤ ∑' n : ℕ, ‖(1 : ℂ) / (z + n) ^ 2‖ :=
          norm_tsum_le_tsum_norm hsummable_norm
      _ = ∑' n : ℕ, ((b + n) ^ 2 + (t / 2) ^ 2)⁻¹ := tsum_congr hnorm_term
      _ ≤ ∑' n : ℕ, (((1 / 4 : ℝ) + n) ^ 2 + (t / 2) ^ 2)⁻¹ :=
          Summable.tsum_le_tsum hcmp hsum_b hsum_q
      _ ≤ 12 / |t / 2| := Zeta23.MuFields.trigamma_tail_le (by rw [abs_div, abs_two]; linarith)
      _ = 24 / |t| := by rw [abs_div, abs_two]; field_simp; norm_num
  have hval : |((Complex.I / 2) • deriv Complex.digamma z).re| ≤ ‖deriv Complex.digamma z‖ / 2 := by
    calc |((Complex.I / 2) • deriv Complex.digamma z).re|
        ≤ ‖(Complex.I / 2) • deriv Complex.digamma z‖ := Complex.abs_re_le_norm _
      _ = ‖deriv Complex.digamma z‖ / 2 := by
          rw [norm_smul, norm_div, Complex.norm_I, Complex.norm_two]; ring
  calc _ ≤ ‖deriv Complex.digamma z‖ / 2 := hval
    _ ≤ (24 / |t|) / 2 := by gcongr
    _ = 12 / |t| := by ring

/-- The constant `B_b = |Re ψ(b)| + |Re ψ(b + i/2)|`. -/
def smallBound (b : ℝ) : ℝ := |reDigammaLine b 0| + |reDigammaLine b (1 / 2)|

lemma smallBound_nonneg (b : ℝ) : 0 ≤ smallBound b := by
  unfold smallBound; positivity

/-- **`StirlingDigamma` (classical input (b4)) is a theorem**, from `zeta23`'s Stirling formula on
vertical lines, the real digamma series (monotonicity, evenness) and the trigamma series. -/
theorem StirlingDigamma_proof : StirlingDigamma := by
  set B : ℝ := smallBound (1 / 4) + smallBound (3 / 4) with hB
  have hB0 : 0 ≤ B := add_nonneg (smallBound_nonneg _) (smallBound_nonneg _)
  refine ⟨100 + 2 * B, fun a ha => ?_⟩
  set b : ℝ := 1 / 4 + a / 2 with hbdef
  obtain ⟨hb0, hb1⟩ := abscissa_bounds ha
  rw [← hbdef] at hb0 hb1
  have hbpos : 0 < b := by linarith
  have hBb : smallBound b ≤ B := by
    rcases ha with rfl | rfl
    · have : b = 1 / 4 := by rw [hbdef]; norm_num
      rw [this, hB]; linarith [smallBound_nonneg (3 / 4 : ℝ)]
    · have : b = 3 / 4 := by rw [hbdef]; norm_num
      rw [this, hB]; linarith [smallBound_nonneg (1 / 4 : ℝ)]
  refine ⟨fun t ht => ?_, fun t => ?_, fun t ht => ?_⟩
  · -- (i)
    have ht' : 1 ≤ |t| := by rw [abs_of_pos (by linarith)]; exact ht
    have h := reDigammaLine_stirling hbpos hb1.le ht'
    rw [abs_of_pos (by linarith : (0 : ℝ) < t)] at h
    rw [digammaRe_eq, ← hbdef]
    have ht0 : 0 < t := by linarith
    calc _ ≤ 20 / t ^ 2 := h
      _ ≤ 20 / t := by
          apply div_le_div_of_nonneg_left (by norm_num) ht0
          nlinarith
      _ ≤ (100 + 2 * B) / t := by
          apply div_le_div_of_nonneg_right _ ht0.le; linarith
  · -- (ii)
    rw [digammaRe_eq, ← hbdef]
    have hL := half_le_log_abs_add_two t
    rcases le_or_gt 1 |t| with ht | ht
    · have h := reDigammaLine_stirling hbpos hb1.le ht
      have hlog := abs_log_half_le ht
      have ht2 : 1 ≤ t ^ 2 := by rw [← sq_abs]; nlinarith
      have h20 : 20 / t ^ 2 ≤ 20 := by
        rw [div_le_iff₀ (by linarith)]; nlinarith
      have habs : |reDigammaLine b (t / 2)| ≤ Real.log (|t| + 2) + 20 := by
        have := abs_sub_abs_le_abs_sub (reDigammaLine b (t / 2)) (Real.log (|t| / 2))
        linarith
      have hlog0 : 0 ≤ Real.log (|t| + 2) := by linarith
      nlinarith
    · have hs : |t / 2| ≤ 1 / 2 := by rw [abs_div, abs_two]; linarith
      have h := abs_reDigammaLine_le_of_small hbpos hb1 hs
      have h' : |reDigammaLine b (t / 2)| ≤ B := h.trans hBb
      have hlog0 : 0 ≤ Real.log (|t| + 2) := by linarith
      nlinarith
  · -- (iii)
    have ht' : 1 ≤ |t| := by rw [abs_of_pos (by linarith)]; exact ht
    have hfun : digammaRe a = fun t : ℝ => reDigammaLine b (t / 2) := by
      funext x; rw [digammaRe_eq]
    rw [hfun]
    have h := abs_deriv_reDigammaLine_le hb0 hb1 ht'
    rw [abs_of_pos (by linarith : (0 : ℝ) < t)] at h
    have ht0 : 0 < t := by linarith
    refine h.trans ?_
    apply div_le_div_of_nonneg_right _ ht0.le
    linarith

end Families.Hyp
