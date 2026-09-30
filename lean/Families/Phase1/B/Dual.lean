/-
# `lem:dual` (band-limited duality; Lemma 6.2)

`lemDual_proof : lemDual_Statement`.

Proof, following the TeX but without operator norms. Put `S_i = S_x(θ_i)`, `L = ∑_i a_i|S_i|²`,
`b_i = a_i S_i` and `Y_n = ∑_i b_i e(−nθ_i)`.
* `L = ∑_{n∈I} x_n \bar Y_n`, so by Cauchy–Schwarz `L² ≤ ‖x‖² ∑_{n∈I}|Y_n|²` (this is `‖A‖ = ‖A^*‖`).
* Fejér majorant (Step 1): with an integer centre `c` of `I` (`|n−c| ≤ K/2` on `I`) and
  `g(n) = F(ς(n−c))`, `F(y) = sinc²(πy)`, we have `g ≥ 0`, `g ≥ F₀ := 1 − π²κ²/12` on `I`, and
  `∑_n g(n) e(nξ) = e(cξ) k_ς(ξ)` (`hasSum_fejer_shift`, from Poisson summation, `Fejer.lean`).
  Hence `F₀ ∑_{n∈I}|Y_n|² ≤ ∑_{n∈ℤ} g(n)|Y_n|² = Re ∑_{i,j} b_i\bar b_j e(c(θ_j−θ_i)) k_ς(θ_j−θ_i)
  ≤ ∑_{i,j}|b_i||b_j| k_ς(θ_j−θ_i)`.
* Schur test with weights `a_i` (Step 2): `|b_i||b_j| ≤ ½ a_ia_j(|S_i|² + |S_j|²)` and `k_ς` even give
  `∑_{i,j}|b_i||b_j|k_ς(θ_j−θ_i) ≤ M L`.
* So `L² ≤ ‖x‖² F₀⁻¹ M L`, i.e. `L ≤ F₀⁻¹ M ‖x‖² ≤ (1+κ²) M ‖x‖²` (`κ ≤ 1/4`).
The distinctness hypothesis of `lemDual_Statement` is not needed.
-/
import Families.Phase1.B.Fejer

noncomputable section

open scoped BigOperators ComplexConjugate
open Finset

namespace Families.Phase1.B

open Families

lemma eA_add' (u v : ℝ) : eA (u + v) = eA u * eA v := by
  unfold eA; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma conj_eA' (u : ℝ) : conj (eA u) = eA (-u) := by
  unfold eA; rw [← Complex.exp_conj]; congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]; push_cast; ring

/-- The shifted Fejér series: `∑_n F(ς(n−c)) e(nξ) = e(cξ) k_ς(ξ)`. -/
lemma hasSum_fejer_shift {ς : ℝ} (hς : 0 < ς) (c : ℤ) (ξ : ℝ) :
    HasSum (fun n : ℤ => (fejerCoeff ς (n - c) : ℂ) * eA (n * ξ)) (eA (c * ξ) * kper ς ξ) := by
  have h := (hasSum_fejer_kper hς ξ).mul_left (eA (c * ξ))
  have hfun : ((fun n : ℤ => (fejerCoeff ς (n - c) : ℂ) * eA (n * ξ)) ∘ (Equiv.addRight c)) =
      fun m : ℤ => eA (c * ξ) * ((fejerCoeff ς m : ℂ) * eA (m * ξ)) := by
    funext m
    simp only [Function.comp_apply, Equiv.coe_addRight, add_sub_cancel_right]
    rw [show ((m + c : ℤ) : ℝ) * ξ = (m : ℝ) * ξ + (c : ℝ) * ξ by push_cast; ring, eA_add']
    ring
  rw [← (Equiv.addRight c).hasSum_iff, hfun]
  exact h

/-- For `n` in `I = [N₀, N₀+K)` and `c = N₀ + ⌊(K−1)/2⌋`: `2|n − c| ≤ K`. -/
lemma two_abs_sub_centre_le {N₀ : ℤ} {K : ℕ} {n : ℤ} (hn : n ∈ intervalZ N₀ K) :
    (2 * ((n : ℝ) - ((N₀ + ((K - 1) / 2 : ℕ) : ℤ) : ℝ))) ^ 2 ≤ (K : ℝ) ^ 2 := by
  unfold intervalZ at hn
  rw [Finset.mem_Ico] at hn
  set d : ℤ := 2 * (n - (N₀ + ((K - 1) / 2 : ℕ))) with hd
  have h1 : -(K : ℤ) ≤ d := by omega
  have h2 : d ≤ (K : ℤ) := by omega
  have h1' : ((-(K : ℤ) : ℤ) : ℝ) ≤ (d : ℝ) := Int.cast_le.mpr h1
  have h2' : (d : ℝ) ≤ ((K : ℤ) : ℝ) := Int.cast_le.mpr h2
  have hdR : (d : ℝ) = 2 * ((n : ℝ) - ((N₀ + ((K - 1) / 2 : ℕ) : ℤ) : ℝ)) := by
    rw [hd]; push_cast; ring
  rw [← hdR]
  push_cast at h1' h2'
  nlinarith

/-- `(1+κ²)(1 − π²κ²/12) ≥ 1` for `0 < κ ≤ 1/4`. -/
lemma one_le_mul_F0 {κ : ℝ} (hκ : 0 < κ) (hκ' : κ ≤ 1 / 4) :
    1 ≤ (1 + κ ^ 2) * (1 - Real.pi ^ 2 * κ ^ 2 / 12) := by
  have hπ := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  have hκ2 : κ ^ 2 ≤ 1 / 16 := by nlinarith
  have hπ2 : Real.pi ^ 2 ≤ 10 := by nlinarith
  have : Real.pi ^ 2 * (1 + κ ^ 2) ≤ 12 := by nlinarith
  nlinarith [sq_nonneg κ]

/-- **`lem:dual`** (Lemma 6.2). -/
theorem lemDual_proof : lemDual_Statement := by
  intro σ s θ a ha _hdist N₀ K hK κ hκ hκ' M hM0 hM x
  classical
  set I := intervalZ N₀ K with hI
  set ς := κ / K with hςdef
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hς : 0 < ς := div_pos hκ hK0
  set Sx : σ → ℂ := fun i => S I x (θ i) with hSx
  set L := ∑ i ∈ s, a i * ‖Sx i‖ ^ 2 with hLdef
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun i hi => mul_nonneg (ha i hi).le (sq_nonneg _)
  set b : σ → ℂ := fun i => (a i : ℂ) * Sx i with hb
  set Y : ℤ → ℂ := fun n => ∑ i ∈ s, b i * conj (eA (n * θ i)) with hY
  set c : ℤ := N₀ + ((K - 1) / 2 : ℕ) with hc
  set g : ℤ → ℝ := fun n => fejerCoeff ς (n - c) with hg
  set F₀ : ℝ := 1 - Real.pi ^ 2 * κ ^ 2 / 12 with hF₀
  have hF₀1 := one_le_mul_F0 hκ hκ'
  have hF₀pos : 0 < F₀ := by
    by_contra h
    rw [not_lt] at h
    nlinarith [sq_nonneg κ]
  -- Step A: `L = ∑_{n∈I} x_n \bar Y_n`, hence `L² ≤ ‖x‖² ∑_{n∈I} |Y_n|²`
  have hLC : (L : ℂ) = ∑ n ∈ I, x n * conj (Y n) := by
    simp only [hY, map_sum, map_mul, Complex.conj_conj, Finset.mul_sum]
    rw [Finset.sum_comm]
    rw [hLdef]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : ∑ n ∈ I, x n * (conj (b i) * eA (n * θ i)) = conj (b i) * Sx i := by
      simp only [hSx, S, Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [h1, hb]
    simp only [map_mul, Complex.conj_ofReal]
    rw [mul_assoc, Complex.conj_mul']
  have hA : L ^ 2 ≤ normSq I x * ∑ n ∈ I, ‖Y n‖ ^ 2 := by
    have h1 : L ≤ ∑ n ∈ I, ‖x n‖ * ‖Y n‖ := by
      have : L = ‖(L : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hL0]
      rw [this, hLC]
      refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun n _ => ?_))
      rw [norm_mul, Complex.norm_conj]
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq I (fun n => ‖x n‖) (fun n => ‖Y n‖)
    calc L ^ 2 ≤ (∑ n ∈ I, ‖x n‖ * ‖Y n‖) ^ 2 := pow_le_pow_left₀ hL0 h1 2
      _ ≤ _ := h2
  -- Step B: `g ≥ F₀` on `I`
  have hB : ∀ n ∈ I, F₀ ≤ g n := by
    intro n hn
    have h2 : (2 * ((n : ℝ) - (c : ℝ))) ^ 2 ≤ (K : ℝ) ^ 2 := two_abs_sub_centre_le hn
    simp only [hg, fejerCoeff]
    have hy : (Real.pi * ς * ((n - c : ℤ) : ℝ)) ^ 2 ≤ Real.pi ^ 2 * κ ^ 2 / 4 := by
      have e : (Real.pi * ς * ((n - c : ℤ) : ℝ)) ^ 2 =
          Real.pi ^ 2 * κ ^ 2 * ((2 * ((n : ℝ) - c)) ^ 2 / (K : ℝ) ^ 2) / 4 := by
        rw [hςdef]; push_cast; field_simp; ring
      rw [e]
      have : (2 * ((n : ℝ) - c)) ^ 2 / (K : ℝ) ^ 2 ≤ 1 := (div_le_one (by positivity)).mpr h2
      have hπκ : 0 ≤ Real.pi ^ 2 * κ ^ 2 := by positivity
      nlinarith
    have hy6 : (Real.pi * ς * ((n - c : ℤ) : ℝ)) ^ 2 ≤ 6 := by
      have := Real.pi_lt_d2
      nlinarith [sq_nonneg κ]
    have := sinc_sq_ge hy6
    rw [hF₀]
    linarith
  -- Step C: the Fejér-weighted sum over all `n`
  have hYsq : ∀ n : ℤ, ((g n * ‖Y n‖ ^ 2 : ℝ) : ℂ) = ∑ i ∈ s, ∑ j ∈ s,
      (b i * conj (b j)) * ((fejerCoeff ς (n - c) : ℂ) * eA (n * (θ j - θ i))) := by
    intro n
    have h1 : ((‖Y n‖ ^ 2 : ℝ) : ℂ) = Y n * conj (Y n) := by
      rw [Complex.mul_conj']; push_cast; ring
    push_cast
    rw [← Complex.ofReal_pow, h1, hY]
    simp only [map_sum, map_mul, Complex.conj_conj, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have he : conj (eA (n * θ i)) * eA (n * θ j) = eA (n * (θ j - θ i)) := by
      rw [conj_eA', ← eA_add']; congr 1; ring
    rw [hg]
    simp only
    rw [← he]
    ring
  set V : ℂ := ∑ i ∈ s, ∑ j ∈ s, (b i * conj (b j)) * (eA (c * (θ j - θ i)) * kper ς (θ j - θ i))
    with hV
  have hC : HasSum (fun n : ℤ => ((g n * ‖Y n‖ ^ 2 : ℝ) : ℂ)) V := by
    simp_rw [hYsq]
    exact hasSum_sum fun i _ => hasSum_sum fun j _ =>
      (hasSum_fejer_shift hς c (θ j - θ i)).mul_left (b i * conj (b j))
  have hCre : HasSum (fun n : ℤ => g n * ‖Y n‖ ^ 2) V.re := by
    have := ((Complex.hasSum_iff _ _).mp hC).1
    simpa only [Complex.ofReal_re] using this
  have hgnn : ∀ n, 0 ≤ g n * ‖Y n‖ ^ 2 := fun n =>
    mul_nonneg (fejerCoeff_nonneg _ _) (sq_nonneg _)
  have hIle : F₀ * ∑ n ∈ I, ‖Y n‖ ^ 2 ≤ V.re := by
    rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum fun n hn => ?_) (sum_le_hasSum I (fun n _ => hgnn n) hCre)
    exact mul_le_mul_of_nonneg_right (hB n hn) (sq_nonneg _)
  have hVle : V.re ≤ ∑ i ∈ s, ∑ j ∈ s, ‖b i‖ * ‖b j‖ * kper ς (θ j - θ i) := by
    refine (Complex.re_le_norm V).trans ((norm_sum_le _ _).trans
      (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans (le_of_eq
        (Finset.sum_congr rfl fun j _ => ?_))))
    simp only [norm_mul, Complex.norm_conj, norm_eA', Complex.norm_real, one_mul,
      Real.norm_of_nonneg (kper_nonneg' hς (θ j - θ i))]
  -- Step D: the Schur test with weights `a_i`
  have hD : ∑ i ∈ s, ∑ j ∈ s, ‖b i‖ * ‖b j‖ * kper ς (θ j - θ i) ≤ M * L := by
    have hbnorm : ∀ i ∈ s, ‖b i‖ = a i * ‖Sx i‖ := fun i hi => by
      rw [hb, norm_mul, Complex.norm_real, Real.norm_of_nonneg (ha i hi).le]
    have hterm : ∀ i ∈ s, ∀ j ∈ s, ‖b i‖ * ‖b j‖ * kper ς (θ j - θ i) ≤
        (a i * ‖Sx i‖ ^ 2) * (a j * kper ς (θ i - θ j)) / 2 +
          (a j * ‖Sx j‖ ^ 2) * (a i * kper ς (θ j - θ i)) / 2 := by
      intro i hi j hj
      rw [hbnorm i hi, hbnorm j hj]
      have hk : kper ς (θ i - θ j) = kper ς (θ j - θ i) := by
        rw [← kper_neg]; congr 1; ring
      rw [hk]
      have hk0 := kper_nonneg' hς (θ j - θ i)
      have hai := (ha i hi).le
      have haj := (ha j hj).le
      have hAM : 2 * (‖Sx i‖ * ‖Sx j‖) ≤ ‖Sx i‖ ^ 2 + ‖Sx j‖ ^ 2 := by
        nlinarith [sq_nonneg (‖Sx i‖ - ‖Sx j‖)]
      have hw : 0 ≤ a i * a j * kper ς (θ j - θ i) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hAM hw]
    calc ∑ i ∈ s, ∑ j ∈ s, ‖b i‖ * ‖b j‖ * kper ς (θ j - θ i)
        ≤ ∑ i ∈ s, ∑ j ∈ s, ((a i * ‖Sx i‖ ^ 2) * (a j * kper ς (θ i - θ j)) / 2 +
          (a j * ‖Sx j‖ ^ 2) * (a i * kper ς (θ j - θ i)) / 2) :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hterm i hi j hj
      _ = (∑ i ∈ s, (a i * ‖Sx i‖ ^ 2) * ∑ j ∈ s, a j * kper ς (θ i - θ j)) / 2 +
          (∑ j ∈ s, (a j * ‖Sx j‖ ^ 2) * ∑ i ∈ s, a i * kper ς (θ j - θ i)) / 2 := by
          simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div]
          congr 1
          rw [Finset.sum_comm]
      _ ≤ (∑ i ∈ s, (a i * ‖Sx i‖ ^ 2) * M) / 2 + (∑ j ∈ s, (a j * ‖Sx j‖ ^ 2) * M) / 2 := by
          gcongr with i hi j hj
          · exact mul_nonneg (ha i hi).le (sq_nonneg _)
          · exact hM i hi
          · exact mul_nonneg (ha j hj).le (sq_nonneg _)
          · exact hM j hj
      _ = M * L := by
          rw [hLdef, ← Finset.sum_mul]
          ring
  -- combine
  have hkey : L ^ 2 ≤ normSq I x * (F₀⁻¹ * (M * L)) := by
    refine hA.trans (mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun _ _ => sq_nonneg _))
    rw [le_inv_mul_iff₀ hF₀pos]
    linarith
  have hx0 : 0 ≤ normSq I x := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hinv : F₀⁻¹ ≤ 1 + κ ^ 2 := by
    rw [inv_le_iff_one_le_mul₀ hF₀pos, hF₀]
    linarith [hF₀1, mul_comm (1 + κ ^ 2) (1 - Real.pi ^ 2 * κ ^ 2 / 12)]
  rcases hL0.lt_or_eq with hLpos | hLz
  · have h1 : L ≤ normSq I x * (F₀⁻¹ * M) := by
      have : L * L ≤ (normSq I x * (F₀⁻¹ * M)) * L :=
        calc L * L = L ^ 2 := by ring
          _ ≤ normSq I x * (F₀⁻¹ * (M * L)) := hkey
          _ = (normSq I x * (F₀⁻¹ * M)) * L := by ring
      exact le_of_mul_le_mul_right this hLpos
    calc L ≤ normSq I x * (F₀⁻¹ * M) := h1
      _ ≤ normSq I x * ((1 + κ ^ 2) * M) := by gcongr
      _ = (1 + κ ^ 2) * M * normSq I x := by ring
  · rw [← hLz]; positivity

end Families.Phase1.B
