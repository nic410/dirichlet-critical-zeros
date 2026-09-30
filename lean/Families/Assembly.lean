/-
# Assembly helpers for the headline (all proved, no `sorry`)

The "logical plumbing" of the proof of `thm:main` (§7.3, `sec:assembly`), used by
`thmMain_of_components` in `Families.Headline`:

* `assembly_fixed` — for fixed data `P` and a profile `c` satisfying `eq:profile`, `prop:zero`,
  `prop:second` and the lower half of `lem:RvM` give
  `N^s_0, N^*_0 ≥ (X − δ) N` and `N_d ≥ ((1+X)/2 − δ) N` for large `Q`, `X = P.certValue c`
  (the display in the proof of `thm:conditional`, Theorem 5.16, §7.3, including the absorption of
  `O_B(ℓ^{−B}(H𝔐)^{1/2})` via `𝔐 = O(N)` and `H = o(N)`);
* `CTp_ge_one` — `C_T^+(w) ≥ 1` from `prop:sharpLS` and `lem:WH` (the remark after `prop:sharpLS`,
  Proposition 6.21);
* `bandLS_of_MV` — the band constant `C_band` from the multiplicative large sieve and `lem:WH`
  (the paragraph "The band constant" before `prop:TIsharp`, Proposition 6.24);
* `bandProfile` — an explicit smooth profile `C̃_ε` with the properties required by `prop:TIsharp`.
-/
import Families.Classical.Reductions
import Families.Glue
import Families.Weights
import Families.Toeplitz

noncomputable section

open scoped BigOperators ComplexConjugate ArithmeticFunction.Moebius ENNReal ContDiff
open ArithmeticFunction Finset MeasureTheory Filter Topology

namespace Families

/-! ### Nonnegativity -/

lemma famSum_nonneg (W : Weight) (Q : ℝ) (c : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ)
    (hc : ∀ q χ, 0 ≤ c q χ) : 0 ≤ famSum W Q c :=
  Finset.sum_nonneg fun q _ =>
    mul_nonneg (W.omega_nonneg Q q) (Finset.sum_nonneg fun χ _ => hc q χ)

lemma Nfam_nonneg (W : Weight) (Q T : ℝ) : 0 ≤ Nfam W Q T :=
  famSum_nonneg W Q _ fun _ _ => Nat.cast_nonneg _

lemma Mfrak_nonneg (P : PrimeSetup) (W : Weight) (Q T τ₀ : ℝ) : 0 ≤ P.Mfrak W Q T τ₀ :=
  famSum_nonneg W Q _ fun _ _ =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-! ### Asymptotics -/

lemma tendsto_rpow_neg_mul_log_pow {r : ℝ} (hr : 0 < r) (k : ℕ) :
    Tendsto (fun Q : ℝ => Q ^ (-r) * Real.log Q ^ k) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (k : ℝ) hr).tendsto_div_nhds_zero
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with Q hQ
  rw [Real.rpow_natCast, Real.rpow_neg (by linarith), div_eq_mul_inv, mul_comm]

/-- From `lem:WH`: for every `κ < 1`, eventually `κ ℰ I_w Q² ≤ H`. -/
lemma H_lower_eventually (hWH : lemWH_Statement) (W : Weight) {κ : ℝ} (hκ : κ < 1) :
    ∀ᶠ Q in atTop, κ * (Ecal * W.Iw * Q ^ 2) ≤ W.H Q := by
  obtain ⟨c₀, hc₀⟩ := hWH
  have hE : 0 < Ecal * W.Iw := mul_pos Ecal_pos W.Iw_pos
  have hk : 0 < (1 - κ) * (Ecal * W.Iw) := mul_pos (by linarith) hE
  have hlim : Tendsto (fun Q : ℝ => Q ^ (1 / 2 : ℝ)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  filter_upwards [hlim.eventually_ge_atTop (|c₀ * W.Vw| / ((1 - κ) * (Ecal * W.Iw))),
    eventually_ge_atTop (2 : ℝ)] with Q hQA hQ2
  have hQ0 : 0 < Q := by linarith
  have h := (hc₀ W Q hQ2).2
  have h1 : Ecal * W.Iw * Q ^ 2 - c₀ * W.Vw * Q ^ (3 / 2 : ℝ) ≤ W.H Q := by
    have := neg_abs_le (W.H Q - Ecal * W.Iw * Q ^ 2)
    linarith
  have hsplit : Q ^ 2 = Q ^ (3 / 2 : ℝ) * Q ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hQ0]; norm_num
  have h32 : 0 < Q ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hQ0 _
  have hA : |c₀ * W.Vw| ≤ (1 - κ) * (Ecal * W.Iw) * Q ^ (1 / 2 : ℝ) := by
    have := (div_le_iff₀ hk).mp hQA
    linarith
  have h2 : c₀ * W.Vw * Q ^ (3 / 2 : ℝ) ≤ (1 - κ) * (Ecal * W.Iw) * Q ^ 2 := by
    calc c₀ * W.Vw * Q ^ (3 / 2 : ℝ) ≤ |c₀ * W.Vw| * Q ^ (3 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) h32.le
      _ ≤ (1 - κ) * (Ecal * W.Iw) * Q ^ (1 / 2 : ℝ) * Q ^ (3 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right hA h32.le
      _ = (1 - κ) * (Ecal * W.Iw) * Q ^ 2 := by rw [hsplit]; ring
  linarith

/-- From `lem:WH`: eventually `H > 0`. -/
lemma H_pos_eventually (hWH : lemWH_Statement) (W : Weight) : ∀ᶠ Q in atTop, 0 < W.H Q := by
  have hE : 0 < Ecal * W.Iw := mul_pos Ecal_pos W.Iw_pos
  filter_upwards [H_lower_eventually hWH W (κ := 1 / 2) (by norm_num), eventually_gt_atTop (0 : ℝ)]
    with Q hQ hQ0
  have : 0 < Ecal * W.Iw * Q ^ 2 := mul_pos hE (by positivity)
  linarith

/-! ### `C_T^+(w) ≥ 1` (remark after `prop:sharpLS`) -/

lemma norm_eA (x : ℝ) : ‖eA x‖ = 1 := by
  unfold eA
  rw [Complex.norm_exp]
  simp

/-- The unit vector at `n = 1`. -/
def unitAt1 : ℤ → ℂ := fun n => if n = 1 then 1 else 0

lemma intervalZ_one_one : intervalZ 1 1 = {1} := by
  unfold intervalZ; decide

lemma normSq_unitAt1 : normSq (intervalZ 1 1) unitAt1 = 1 := by
  rw [intervalZ_one_one]; simp [normSq, unitAt1]

/-- The diagonal entry of `T^♮`: `y^*T^♮y ≥ μ_Ω(𝕋) = H` for `y` the unit vector at `1`. -/
lemma levelForm_unitAt1_ge_H (W : Weight) (Q : ℝ) :
    W.H Q ≤ levelForm (levels Q) (aNat W Q) (intervalZ 1 1) unitAt1 := by
  have hS : ∀ θ : ℝ, ‖S (intervalZ 1 1) unitAt1 θ‖ ^ 2 = 1 := by
    intro θ
    rw [intervalZ_one_one]
    simp [S, unitAt1, norm_eA]
  unfold levelForm
  simp_rw [hS]
  rw [← muΩ_mass W Q]
  refine Finset.sum_le_sum fun e _ => ?_
  rw [Finset.sum_const, card_reduced, nsmul_eq_mul, mul_one]
  unfold aNat
  have hm : 0 ≤ mfun W (e / Q) := le_max_right _ _
  have hφ : (0 : ℝ) ≤ Nat.totient e := Nat.cast_nonneg _
  nlinarith

/-- **`C_T^+(w) ≥ 1`** (the remark after `prop:sharpLS`, Proposition 6.21), from `prop:sharpLS` and `lem:WH`:
the diagonal entries of `T^♮_I` are `≥ H`, so `H ≤ (C_T^+ + ϑ'_Q) H` with `ϑ'_Q → 0` and `H > 0`. -/
theorem CTp_ge_one (hSharp : propSharpLS_Statement) (hWH : lemWH_Statement) (W : Weight)
    (hW : CTp W ≠ ⊤) : 1 ≤ (CTp W).toReal := by
  obtain ⟨c, hc⟩ := hSharp
  obtain ⟨Q₀, hQ₀⟩ := hc (1 / 2) (by norm_num) (by norm_num) W hW
  set C := (CTp W).toReal with hCdef
  set A := (W.Vw + W.wtmax * W.η⁻¹ ^ 2) / W.Iw
  set B := W.Vw / W.Iw
  let f : ℝ → ℝ := fun Q => C + c * (A * Q ^ (-(1 / 2 : ℝ) / 4) * Real.log Q ^ 3 +
      (Q ^ (-(1 / 2 : ℝ) / 2) + B * Q ^ (-(1 / 2 : ℝ))) * C)
  have hf : Tendsto f atTop (𝓝 C) := by
    have h1 : Tendsto (fun Q : ℝ => Q ^ (-(1 / 2 : ℝ) / 4) * Real.log Q ^ 3) atTop (𝓝 0) := by
      have := tendsto_rpow_neg_mul_log_pow (r := 1 / 8) (by norm_num) 3
      refine this.congr' (Eventually.of_forall fun Q => ?_)
      norm_num
    have h2 : Tendsto (fun Q : ℝ => Q ^ (-(1 / 2 : ℝ) / 2)) atTop (𝓝 0) := by
      have := tendsto_rpow_neg_atTop (y := 1 / 4) (by norm_num)
      refine this.congr' (Eventually.of_forall fun Q => ?_)
      norm_num
    have h3 : Tendsto (fun Q : ℝ => Q ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    have := ((h1.const_mul A).add ((h2.add (h3.const_mul B)).mul_const C)).const_mul c |>.const_add C
    simp only [mul_zero, add_zero, zero_mul] at this
    refine this.congr' (Eventually.of_forall fun Q => ?_)
    simp only [f, mul_assoc]
  have hev : ∀ᶠ Q in atTop, 1 ≤ f Q := by
    filter_upwards [eventually_ge_atTop Q₀, eventually_ge_atTop (1 : ℝ), H_pos_eventually hWH W]
      with Q hQ hQ1 hH
    have hK : ((1 : ℕ) : ℝ) ≤ Q ^ (2 - 1 / 2 : ℝ) := by
      rw [Nat.cast_one]; exact Real.one_le_rpow hQ1 (by norm_num)
    have h := hQ₀ Q hQ 1 1 hK unitAt1
    rw [normSq_unitAt1, mul_one] at h
    have hlow := levelForm_unitAt1_ge_H W Q
    have hle : W.H Q ≤ f Q * W.H Q := by
      refine hlow.trans (h.trans (le_of_eq ?_))
      simp only [f, hCdef]
    nlinarith
  exact ge_of_tendsto hf hev

/-! ### The band constant from the large sieve (before `prop:TIsharp`, Proposition 6.24) -/

/-- `x^*Δx ≤ w_max ∑_q (q/φ(q)) ∑*_χ |∑ x_n χ(n)|²` (from `ω(q) ≤ w_max q/φ(q)`). -/
lemma famForm_le_mult (W : Weight) (Q : ℝ) (I : Finset ℤ) (x : ℤ → ℂ) :
    famForm W Q I x ≤ W.wmax * ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ((q : ℝ) / (Nat.totient q : ℝ)) *
        ∑ χ ∈ primChars q, ‖∑ n ∈ I, x n * χ n‖ ^ 2 := by
  unfold famForm
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun q _ => ?_
  have hinner : 0 ≤ ∑ χ ∈ primChars q, ‖∑ n ∈ I, x n * χ n‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hq : 0 ≤ (q : ℝ) / (Nat.totient q : ℝ) := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hω : W.omega Q q ≤ W.wmax * ((q : ℝ) / (Nat.totient q : ℝ)) := by
    unfold Weight.omega
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (W.le_wmax _) hq
  calc W.omega Q q * ∑ χ ∈ primChars q, ‖∑ n ∈ I, x n * χ n‖ ^ 2
      ≤ (W.wmax * ((q : ℝ) / (Nat.totient q : ℝ))) *
          ∑ χ ∈ primChars q, ‖∑ n ∈ I, x n * χ n‖ ^ 2 := mul_le_mul_of_nonneg_right hω hinner
    _ = _ := by ring

/-- **The band constant.** From the multiplicative large sieve (with constant `C₀`) and `lem:WH`:
`Λ_mult(K) ≤ w_max C₀ (Q² + K) ≤ 2 C₀ w_max Q²` for `K ≤ Q²`, and `H ≥ (1 − o(1)) ℰ I_w Q²`, so
`C_band = 2 max(C₀,0) w_max/(ℰ I_w) + 1` works for every band `ε < 1/2`
(the paper's choice is `2w_max/(ℰ I_w)`, in the paragraph "The band constant" before Proposition 6.24; any `O(1)` constant will do). -/
theorem bandLS_of_MV (hMV : MV_LargeSieve) (hWH : lemWH_Statement) (W : Weight) :
    ∃ Cband : ℝ, 1 ≤ Cband ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → BandLS W ε Cband := by
  obtain ⟨C₀, hmult, -⟩ := hMV
  have hE : 0 < Ecal * W.Iw := mul_pos Ecal_pos W.Iw_pos
  set C₁ := max C₀ 0 with hC₁
  have hC₁0 : 0 ≤ C₁ := le_max_right _ _
  set A := 2 * C₁ * W.wmax / (Ecal * W.Iw) with hA
  have hA0 : 0 ≤ A := div_nonneg (by have := W.wmax_nonneg; positivity) hE.le
  refine ⟨A + 1, by linarith, fun ε _ hε2 δ hδ => ?_⟩
  have hκ : A / (A + 1) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  obtain ⟨Q₁, hQ₁⟩ := Filter.eventually_atTop.1 (H_lower_eventually hWH W hκ)
  refine ⟨max Q₁ 1, fun Q hQ K hK N₀ _ _ x => ?_⟩
  have hQ1 : 1 ≤ Q := le_of_max_le_right hQ
  have hHl := hQ₁ Q (le_of_max_le_left hQ)
  have hx : 0 ≤ normSq (intervalZ N₀ K) x := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hK2 : (K : ℝ) ≤ Q ^ 2 := by
    calc (K : ℝ) ≤ Q ^ (1 + 2 * ε) := hK
      _ ≤ Q ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
      _ = Q ^ 2 := by norm_cast
  have hmv := hmult Q hQ1 N₀ K x
  have hC : C₀ * (Q ^ 2 + K) * normSq (intervalZ N₀ K) x ≤
      C₁ * (2 * Q ^ 2) * normSq (intervalZ N₀ K) x := by
    apply mul_le_mul_of_nonneg_right _ hx
    calc C₀ * (Q ^ 2 + K) ≤ C₁ * (Q ^ 2 + K) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ C₁ * (2 * Q ^ 2) := mul_le_mul_of_nonneg_left (by linarith) hC₁0
  have hAA : (A + 1) * (A / (A + 1)) = A := by field_simp
  have hAE : A * (Ecal * W.Iw) = 2 * C₁ * W.wmax := by
    rw [hA, div_mul_cancel₀ _ hE.ne']
  have hH0 : 0 ≤ W.H Q := W.H_nonneg Q
  calc famForm W Q (intervalZ N₀ K) x
      ≤ W.wmax * (C₁ * (2 * Q ^ 2) * normSq (intervalZ N₀ K) x) :=
        (famForm_le_mult W Q _ x).trans
          (mul_le_mul_of_nonneg_left (hmv.trans hC) W.wmax_nonneg)
    _ = (A + 1) * (A / (A + 1) * (Ecal * W.Iw * Q ^ 2)) * normSq (intervalZ N₀ K) x := by
        rw [← mul_assoc (A + 1), hAA]
        calc W.wmax * (C₁ * (2 * Q ^ 2) * normSq (intervalZ N₀ K) x)
            = 2 * C₁ * W.wmax * Q ^ 2 * normSq (intervalZ N₀ K) x := by ring
          _ = A * (Ecal * W.Iw) * Q ^ 2 * normSq (intervalZ N₀ K) x := by rw [hAE]
          _ = _ := by ring
    _ ≤ (A + 1) * W.H Q * normSq (intervalZ N₀ K) x := by
        apply mul_le_mul_of_nonneg_right _ hx
        exact mul_le_mul_of_nonneg_left hHl (by linarith)
    _ ≤ (A + 1 + δ) * W.H Q * normSq (intervalZ N₀ K) x := by
        apply mul_le_mul_of_nonneg_right _ hx
        exact mul_le_mul_of_nonneg_right (by linarith) hH0

/-! ### An explicit smooth band profile `C̃_ε` -/

/-- A smooth ramp: `0` for `x ≤ a`, `1` for `x ≥ b` (when `a < b`), monotone, values in `[0,1]`. -/
def ramp (a b x : ℝ) : ℝ := Real.smoothTransition ((x - a) / (b - a))

lemma ramp_contDiff (a b : ℝ) : ContDiff ℝ ∞ (ramp a b) := by
  unfold ramp
  exact Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

lemma ramp_nonneg (a b x : ℝ) : 0 ≤ ramp a b x := Real.smoothTransition.nonneg _

lemma ramp_le_one (a b x : ℝ) : ramp a b x ≤ 1 := Real.smoothTransition.le_one _

lemma ramp_of_le {a b x : ℝ} (hab : a < b) (hx : x ≤ a) : ramp a b x = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))

lemma ramp_of_ge {a b x : ℝ} (hab : a < b) (hx : b ≤ x) : ramp a b x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- The band profile: `1` on `(−∞, 1−2ε]`, `C_max` on `[1−3ε/2, 1+3ε/2]`, `C` on `[1+2ε, ∞)`,
smooth, with values in `[1, C_max]` (for `1 ≤ C ≤ C_max`, `ε > 0`). -/
def bandProfile (Cmax C ε α : ℝ) : ℝ :=
  1 + (Cmax - 1) * ramp (1 - 2 * ε) (1 - 3 / 2 * ε) α -
    (Cmax - C) * ramp (1 + 3 / 2 * ε) (1 + 2 * ε) α

lemma bandProfile_contDiff (Cmax C ε : ℝ) : ContDiff ℝ ∞ (bandProfile Cmax C ε) := by
  unfold bandProfile
  exact (contDiff_const.add (contDiff_const.mul (ramp_contDiff _ _))).sub
    (contDiff_const.mul (ramp_contDiff _ _))

lemma bandProfile_spec {Cmax C ε : ℝ} (hε : 0 < ε) (hC : 1 ≤ C) (hCm : C ≤ Cmax) :
    (∀ α, 1 ≤ bandProfile Cmax C ε α ∧ bandProfile Cmax C ε α ≤ Cmax) ∧
    (∀ α, α ≤ 1 - 2 * ε → bandProfile Cmax C ε α = 1) ∧
    (∀ α, 1 - 3 / 2 * ε ≤ α → α ≤ 1 + 3 / 2 * ε → bandProfile Cmax C ε α = Cmax) ∧
    (∀ α, 1 + ε / 2 ≤ α → C ≤ bandProfile Cmax C ε α) ∧
    (∀ α, 1 + 2 * ε ≤ α → bandProfile Cmax C ε α = C) := by
  have h1 : 1 - 2 * ε < 1 - 3 / 2 * ε := by linarith
  have h2 : 1 + 3 / 2 * ε < 1 + 2 * ε := by linarith
  refine ⟨fun α => ?_, fun α hα => ?_, fun α hα hα' => ?_, fun α hα => ?_, fun α hα => ?_⟩
  · have r1 := ramp_nonneg (1 - 2 * ε) (1 - 3 / 2 * ε) α
    have r1' := ramp_le_one (1 - 2 * ε) (1 - 3 / 2 * ε) α
    have r2 := ramp_nonneg (1 + 3 / 2 * ε) (1 + 2 * ε) α
    have r2' := ramp_le_one (1 + 3 / 2 * ε) (1 + 2 * ε) α
    unfold bandProfile
    rcases le_or_gt α (1 + 3 / 2 * ε) with hα | hα
    · rw [ramp_of_le h2 hα]
      constructor <;> nlinarith
    · rw [ramp_of_ge h1 (by linarith)]
      constructor <;> nlinarith
  · unfold bandProfile
    rw [ramp_of_le h1 hα, ramp_of_le h2 (by linarith)]
    ring
  · unfold bandProfile
    rw [ramp_of_ge h1 hα, ramp_of_le h2 hα']
    ring
  · have r2' := ramp_le_one (1 + 3 / 2 * ε) (1 + 2 * ε) α
    unfold bandProfile
    rw [ramp_of_ge h1 (by linarith)]
    nlinarith
  · unfold bandProfile
    rw [ramp_of_ge h1 (by linarith), ramp_of_ge h2 hα]
    ring

/-! ### The fixed-data assembly (proof of `thm:conditional`, Theorem 5.16) -/

/-- **Fixed-data assembly.** For fixed data `P` and a smooth profile `c ≥ 1` satisfying `eq:profile`,
`prop:zero` + `prop:second` + the lower half of `lem:RvM` give, for every `δ > 0` and all large `Q`,
uniformly in `T`: `N^s_0, N^*_0 ≥ (X − δ) N` and `N_d ≥ ((1+X)/2 − δ) N`, `X = P.certValue c`.
(The error `O_B(ℓ^{−B}(H𝔐)^{1/2})` of `prop:zero` is absorbed using `𝔐 = O(N)` and `H ≤ N`.) -/
theorem assembly_fixed (hZ : propZero_Statement) (hRvM : lemRvM_lower_Statement)
    (hS : propSecond_Statement) (P : PrimeSetup) (W : Weight) (c : ℝ → ℝ)
    (hc : ContDiff ℝ ∞ c) (hc1 : ∀ α, 1 ≤ c α) (hprof : P.ProfileBound W c) :
    ∀ δ : ℝ, 0 < δ → ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ P.heights Q,
      (P.certValue c - δ) * Nfam W Q T ≤ Ns0 W Q T ∧
      (P.certValue c - δ) * Nfam W Q T ≤ Nstar0 W Q T ∧
      ((1 + P.certValue c) / 2 - δ) * Nfam W Q T ≤ Nd W Q T := by
  intro δ hδ
  set Y := (1 - 2 * P.θ) *
    Qf (fun α => c α * min α (1 + 2 * P.ε₃)) (fun x => P.vfun (x / P.lam) / (P.lam * P.aInt))
    with hY
  have hX : P.certValue c = 2 - 8 * P.θ - Y := rfl
  have hδ3 : 0 < δ / 3 := by positivity
  obtain ⟨Q₁, hQ₁⟩ := hS P W 0 c hc hc1 hprof (δ / 3) hδ3
  obtain ⟨Cz, Q₂, hQ₂⟩ := hZ P W 0 1 (δ / 3) one_pos hδ3
  obtain ⟨Q₃, hQ₃⟩ := hRvM W P.a0 P.A0 P.a0_pos P.a0_lt (1 / 2) (by norm_num)
  set s := max Y 0 + δ / 3 with hs
  have hs0 : 0 ≤ s := by have := le_max_right Y 0; linarith
  set K := |Cz| * Real.sqrt s with hK
  have hK0 : 0 ≤ K := mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  set L₀ := max (max (3 * K / δ) (4 * Real.pi)) 1 with hL₀
  refine ⟨max (max Q₁ Q₂) (max Q₃ (Real.exp L₀)), fun Q hQ T hT => ?_⟩
  have hQ1 : Q₁ ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hQ
  have hQ2 : Q₂ ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hQ
  have hQ3 : Q₃ ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hQ
  have hQ4 : Real.exp L₀ ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hQ
  have hQpos : 0 < Q := lt_of_lt_of_le (Real.exp_pos _) hQ4
  have hlog : L₀ ≤ Real.log Q := by
    rw [← Real.log_exp L₀]; exact Real.log_le_log (Real.exp_pos _) hQ4
  have hlog1 : 1 ≤ Real.log Q := le_trans (le_max_right _ _) hlog
  have hlog4π : 4 * Real.pi ≤ Real.log Q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hlog
  have hlogK : 3 * K / δ ≤ Real.log Q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hlog
  have hlogpos : 0 < Real.log Q := by linarith
  -- the three inputs at `(Q, T)`
  have hM := hQ₁ Q hQ1 T hT
  have hZQ := hQ₂ Q hQ2 T hT
  simp only at hZQ
  have hR := hQ₃ Q hQ3 T hT
  set N := Nfam W Q T with hN
  set M := P.Mfrak W Q T 0 with hMdef
  set H := W.H Q with hH
  have hN0 : 0 ≤ N := Nfam_nonneg W Q T
  have hM0 : 0 ≤ M := Mfrak_nonneg P W Q T 0
  have hH0 : 0 ≤ H := W.H_nonneg Q
  -- `T ≥ 1`
  have hT1 : 1 ≤ T := le_trans (Real.one_le_rpow hlog1 P.a0_pos.le) hT.1
  -- `H ≤ N` (lower half of `lem:RvM`)
  have hHN : H ≤ N := by
    have hTL : 4 * Real.pi ≤ T * Real.log Q := by nlinarith
    have hpi : 0 < Real.pi := Real.pi_pos
    have h1 : H ≤ (1 - 1 / 2) * (H * T * Real.log Q / (2 * Real.pi)) := by
      rw [show (1 - 1 / 2 : ℝ) * (H * T * Real.log Q / (2 * Real.pi)) =
        H * (T * Real.log Q / (4 * Real.pi)) by field_simp; ring]
      have : 1 ≤ T * Real.log Q / (4 * Real.pi) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      nlinarith
    linarith
  -- `𝔐 ≤ s N`
  have hMs : M ≤ s * N := by
    have := le_max_left Y 0
    nlinarith
  -- `√(H𝔐) ≤ √s N`
  have hsqrt : Real.sqrt (H * M) ≤ Real.sqrt s * N := by
    have hHM : H * M ≤ N ^ 2 * s := by nlinarith
    calc Real.sqrt (H * M) ≤ Real.sqrt (N ^ 2 * s) := Real.sqrt_le_sqrt hHM
      _ = Real.sqrt (N ^ 2) * Real.sqrt s := Real.sqrt_mul (sq_nonneg N) s
      _ = Real.sqrt s * N := by rw [Real.sqrt_sq hN0, mul_comm]
  -- the error term of `prop:zero`
  have herr : Cz * Real.log Q ^ (-(1 : ℝ)) * Real.sqrt (H * M) ≤ δ / 3 * N := by
    rw [Real.rpow_neg_one]
    have hinv : 0 ≤ (Real.log Q)⁻¹ := inv_nonneg.mpr hlogpos.le
    have hKδ : K * (Real.log Q)⁻¹ ≤ δ / 3 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hlogpos]
      rw [div_le_iff₀ hδ] at hlogK
      linarith
    calc Cz * (Real.log Q)⁻¹ * Real.sqrt (H * M)
        ≤ |Cz| * (Real.log Q)⁻¹ * Real.sqrt (H * M) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hinv)
            (Real.sqrt_nonneg _)
      _ ≤ |Cz| * (Real.log Q)⁻¹ * (Real.sqrt s * N) :=
          mul_le_mul_of_nonneg_left hsqrt (mul_nonneg (abs_nonneg _) hinv)
      _ = K * (Real.log Q)⁻¹ * N := by rw [hK]; ring
      _ ≤ δ / 3 * N := mul_le_mul_of_nonneg_right hKδ hN0
  obtain ⟨hz1, hz2, hz3⟩ := hZQ
  have hδN : 0 ≤ δ * N := mul_nonneg hδ.le hN0
  rw [hX]
  refine ⟨?_, ?_, ?_⟩
  · linarith only [hz1, hM, herr, hδN]
  · linarith only [hz2, hM, herr, hδN]
  · linarith only [hz3, hM, herr, hδN]

end Families
