/-
Basic objects for **`prop:TIsharp`** (§6.2, Proposition 6.24 and the notation before it).

* the localisation cut-off `ρ = rhoLoc` (`ρ ∈ C_c^∞((−2,2))`, `0 ≤ ρ ≤ 1`, `ρ = 1` on `[−1,1]`) and the
  localisation scale `δ = δL = 1/4` (the TeX takes `δ = T^{−1/2}`; any fixed `δ ∈ (0, 1/4]` works, since the
  tails are `≪ T^{1/4}·L³H/δ` against `H|J|L²ℓ`, and `|J| ≍ T → ∞`);
* the localised and tail vectors `x^s_y(u) = xs`, `x^t_y(u) = xt` (literally those of `lem:M3`);
* support bookkeeping (a form over `I` only sees the support of the vector), `[1, Y] = intervalZ 1 ⌊Y⌋₊`;
* the seminorm inequality `eqC:seminorm` for the level forms (nonnegative level weights);
* `0 ≤ ν(e) = Ω(e) + m(e/Q) ≤ 6‖w̃‖_∞η^{−2}` (`eqC:nu`, from `lem:Omega`(a)–(c));
* the multiplicative large sieve on `[1, Y]`.
-/
import Families.Phase3.C.Mrat
import Families.M1Diag
import Families.Wired.Phase1
import Families.Assembly

noncomputable section

open scoped BigOperators ComplexConjugate ContDiff
open Finset MeasureTheory

namespace Families.Phase3.C

open Families

/-! ### The cut-off `ρ` -/

/-- `ρ(ξ) = S(ξ + 2) S(2 − ξ)` with `S = Real.smoothTransition`. -/
def rhoLoc (ξ : ℝ) : ℝ := Real.smoothTransition (ξ + 2) * Real.smoothTransition (2 - ξ)

lemma rhoLoc_contDiff : ContDiff ℝ ∞ rhoLoc := by
  unfold rhoLoc
  exact (Real.smoothTransition.contDiff.comp (contDiff_id.add contDiff_const)).mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id))

lemma rhoLoc_continuous : Continuous rhoLoc := rhoLoc_contDiff.continuous

lemma rhoLoc_nonneg (ξ : ℝ) : 0 ≤ rhoLoc ξ :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma rhoLoc_le_one (ξ : ℝ) : rhoLoc ξ ≤ 1 := by
  unfold rhoLoc
  have h1 := Real.smoothTransition.le_one (ξ + 2)
  have h2 := Real.smoothTransition.le_one (2 - ξ)
  have h3 := Real.smoothTransition.nonneg (ξ + 2)
  have h4 := Real.smoothTransition.nonneg (2 - ξ)
  nlinarith

lemma rhoLoc_one {ξ : ℝ} (h : |ξ| ≤ 1) : rhoLoc ξ = 1 := by
  unfold rhoLoc
  rw [abs_le] at h
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith), one_mul]

lemma rhoLoc_zero {ξ : ℝ} (h : 2 ≤ |ξ|) : rhoLoc ξ = 0 := by
  unfold rhoLoc
  rcases le_abs'.mp h with h | h
  · rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]
  · rw [Real.smoothTransition.zero_of_nonpos (show 2 - ξ ≤ 0 by linarith), mul_zero]

lemma rhoLoc_lt_of_ne_zero {ξ : ℝ} (h : rhoLoc ξ ≠ 0) : |ξ| < 2 := by
  by_contra hc; exact h (rhoLoc_zero (not_lt.mp hc))

/-- The derivatives of `ρ` are bounded. -/
lemma rhoLoc_deriv_bound (i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ, ‖iteratedDeriv i rhoLoc ξ‖ ≤ C := by
  have hcont : Continuous (iteratedDeriv i rhoLoc) :=
    rhoLoc_contDiff.continuous_iteratedDeriv i (by exact_mod_cast le_top)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (-3 : ℝ)) (b := 3)).exists_bound_of_continuousOn
    hcont.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨by norm_num, by norm_num⟩)
  refine ⟨C, hC0, fun ξ => ?_⟩
  by_cases hξ : ξ ∈ Set.Icc (-3 : ℝ) 3
  · exact hC ξ hξ
  · have hξ' : 3 < |ξ| := by
      simp only [Set.mem_Icc, not_and_or, not_le] at hξ
      rcases hξ with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; exact h
    have hz : rhoLoc =ᶠ[nhds ξ] fun _ => 0 := by
      have hopen : IsOpen {z : ℝ | 2 < |z|} := isOpen_lt continuous_const continuous_abs
      filter_upwards [hopen.mem_nhds (show 2 < |ξ| by linarith)] with z hz
      exact rhoLoc_zero (le_of_lt hz)
    rw [hz.iteratedDeriv_eq, iteratedDeriv_const]
    split_ifs <;> simpa using hC0

/-- The localisation scale `δ = 1/4`. -/
def δL : ℝ := 1 / 4

lemma δL_pos : 0 < δL := by norm_num [δL]

variable (P : PrimeSetup)

/-! ### Localised and tail vectors -/

/-- `x^s_y(u)_n = x_y(u)_n ρ((log n − u)/δ)`. -/
def xs (Q T : ℝ) (y : ℕ → ℝ) (u : ℝ) : ℤ → ℂ :=
  fun n => P.xVec Q T y u n * (rhoLoc ((Real.log n.toNat - u) / δL) : ℂ)

/-- `x^t_y(u) = x_y(u) − x^s_y(u)`. -/
def xt (Q T : ℝ) (y : ℕ → ℝ) (u : ℝ) : ℤ → ℂ := fun n => P.xVec Q T y u n - xs P Q T y u n

lemma xVec_eq_xs_add_xt (Q T : ℝ) (y : ℕ → ℝ) (u : ℝ) :
    P.xVec Q T y u = xs P Q T y u + xt P Q T y u := by
  funext n; simp [xt]

lemma xVec_add (Q T : ℝ) (y₁ y₂ : ℕ → ℝ) (u : ℝ) :
    P.xVec Q T (y₁ + y₂) u = P.xVec Q T y₁ u + P.xVec Q T y₂ u := by
  funext n
  simp only [PrimeSetup.xVec, Pi.add_apply]
  split_ifs <;> push_cast <;> ring

lemma xVec_sub (Q T : ℝ) (y₁ y₂ : ℕ → ℝ) (u : ℝ) :
    P.xVec Q T (y₁ - y₂) u = P.xVec Q T y₁ u - P.xVec Q T y₂ u := by
  funext n
  simp only [PrimeSetup.xVec, Pi.sub_apply]
  split_ifs <;> push_cast <;> ring

lemma xs_add (Q T : ℝ) (y₁ y₂ : ℕ → ℝ) (u : ℝ) :
    xs P Q T (y₁ + y₂) u = xs P Q T y₁ u + xs P Q T y₂ u := by
  funext n
  simp only [xs, xVec_add, Pi.add_apply]
  ring

lemma xs_sub (Q T : ℝ) (y₁ y₂ : ℕ → ℝ) (u : ℝ) :
    xs P Q T (y₁ - y₂) u = xs P Q T y₁ u - xs P Q T y₂ u := by
  funext n
  simp only [xs, xVec_sub, Pi.sub_apply]
  ring

lemma xs_congr {Q T : ℝ} {y₁ y₂ : ℕ → ℝ} {u : ℝ}
    (h : ∀ k : ℕ, 1 ≤ k → |Real.log k - u| < 1 / 2 → y₁ k = y₂ k) :
    xs P Q T y₁ u = xs P Q T y₂ u := by
  funext n
  simp only [xs, PrimeSetup.xVec]
  split_ifs with hn
  · by_cases hr : rhoLoc ((Real.log n.toNat - u) / δL) = 0
    · simp [hr]
    · have hlt := rhoLoc_lt_of_ne_zero hr
      rw [abs_div, abs_of_pos δL_pos, div_lt_iff₀ δL_pos] at hlt
      have hk : 1 ≤ n.toNat := by omega
      rw [h n.toNat hk (by unfold δL at hlt; linarith)]
  · simp

/-! ### Supports -/

lemma xVec_ne_zero {Q T : ℝ} {y : ℕ → ℝ} {u : ℝ} {n : ℤ} (h : P.xVec Q T y u n ≠ 0) :
    1 ≤ n ∧ y n.toNat ≠ 0 := by
  unfold PrimeSetup.xVec at h
  split_ifs at h with hn
  · refine ⟨hn, fun h0 => h ?_⟩
    simp [h0]
  · exact absurd rfl h

lemma xs_ne_zero {Q T : ℝ} {y : ℕ → ℝ} {u : ℝ} {n : ℤ} (h : xs P Q T y u n ≠ 0) :
    1 ≤ n ∧ y n.toNat ≠ 0 ∧ |Real.log n.toNat - u| < 1 / 2 := by
  have h1 : P.xVec Q T y u n ≠ 0 := left_ne_zero_of_mul h
  have h2 : rhoLoc ((Real.log n.toNat - u) / δL) ≠ 0 := by
    intro h0; apply h; simp [xs, h0]
  obtain ⟨hn, hy⟩ := xVec_ne_zero P h1
  refine ⟨hn, hy, ?_⟩
  have hlt := rhoLoc_lt_of_ne_zero h2
  rw [abs_div, abs_of_pos δL_pos, div_lt_iff₀ δL_pos] at hlt
  unfold δL at hlt; linarith

/-- `y` vanishes beyond `⌊Y⌋`. -/
def VanishBeyond (Q : ℝ) (y : ℕ → ℝ) : Prop := ∀ k : ℕ, ⌊P.Y Q⌋₊ < k → y k = 0

lemma mem_rangeZ_of_xVec {Q T : ℝ} {y : ℕ → ℝ} (hy : VanishBeyond P Q y) {u : ℝ} {n : ℤ}
    (h : P.xVec Q T y u n ≠ 0) : n ∈ P.rangeZ Q := by
  obtain ⟨hn, hyn⟩ := xVec_ne_zero P h
  have hk : n.toNat ≤ ⌊P.Y Q⌋₊ := by
    by_contra hc; exact hyn (hy _ (not_le.mp hc))
  simp only [PrimeSetup.rangeZ, Finset.mem_Icc]
  refine ⟨hn, ?_⟩
  rw [← Int.natCast_floor_eq_floor (P.Y_nonneg Q)]
  omega

lemma mem_rangeZ_of_xs {Q T : ℝ} {y : ℕ → ℝ} (hy : VanishBeyond P Q y) {u : ℝ} {n : ℤ}
    (h : xs P Q T y u n ≠ 0) : n ∈ P.rangeZ Q :=
  mem_rangeZ_of_xVec P hy (left_ne_zero_of_mul h)

lemma mem_rangeZ_of_xt {Q T : ℝ} {y : ℕ → ℝ} (hy : VanishBeyond P Q y) {u : ℝ} {n : ℤ}
    (h : xt P Q T y u n ≠ 0) : n ∈ P.rangeZ Q := by
  by_contra hc
  apply h
  have h1 : P.xVec Q T y u n = 0 := by
    by_contra h'; exact hc (mem_rangeZ_of_xVec P hy h')
  simp [xt, xs, h1]

lemma VanishBeyond.aVec {Q : ℝ} (hQ : 1 < Q) : VanishBeyond P Q (P.aVec Q) := by
  intro k hk
  have hY : P.Y Q < k := (Nat.floor_lt (P.Y_nonneg Q)).mp hk
  have := UpsL_eq_zero P hQ hY
  simp only [UpsL] at this
  simp [PrimeSetup.aVec, PrimeSetup.Ups, this]

lemma VanishBeyond.aSharp {Q : ℝ} (hQ : 1 < Q) (T : ℝ) : VanishBeyond P Q (P.aSharp Q T) := by
  intro k hk
  have hY : P.Y Q < k := (Nat.floor_lt (P.Y_nonneg Q)).mp hk
  have := UpsL_eq_zero P hQ hY
  simp only [UpsL] at this
  unfold PrimeSetup.aSharp
  refine Finset.sum_eq_zero fun j _ => ?_
  simp [PrimeSetup.Ups, this]

lemma VanishBeyond.sub {Q : ℝ} {y₁ y₂ : ℕ → ℝ} (h₁ : VanishBeyond P Q y₁)
    (h₂ : VanishBeyond P Q y₂) : VanishBeyond P Q (y₁ - y₂) := by
  intro k hk; simp [h₁ k hk, h₂ k hk]

lemma VanishBeyond.bVec {Q : ℝ} (hQ : 1 < Q) (T : ℝ) : VanishBeyond P Q (P.bVec Q T) := by
  intro k hk
  simp [PrimeSetup.bVec, VanishBeyond.aVec P hQ k hk, VanishBeyond.aSharp P hQ T k hk]

lemma VanishBeyond.of_le {Q : ℝ} {y₁ y₂ : ℕ → ℝ} (h₁ : VanishBeyond P Q y₁)
    (h : ∀ k, y₁ k = 0 → y₂ k = 0) : VanishBeyond P Q y₂ :=
  fun k hk => h k (h₁ k hk)

/-! ### Forms only see the support -/

lemma sum_congr_supp {M : Type*} [AddCommMonoid M] {A B : Finset ℤ} (f : ℤ → M)
    (h : ∀ n, f n ≠ 0 → (n ∈ A ↔ n ∈ B)) : ∑ n ∈ A, f n = ∑ n ∈ B, f n := by
  classical
  have e1 : ∑ n ∈ A ∩ B, f n = ∑ n ∈ A, f n := by
    refine Finset.sum_subset Finset.inter_subset_left fun n hnA hn => ?_
    by_contra hf; exact hn (Finset.mem_inter.mpr ⟨hnA, (h n hf).mp hnA⟩)
  have e2 : ∑ n ∈ A ∩ B, f n = ∑ n ∈ B, f n := by
    refine Finset.sum_subset Finset.inter_subset_right fun n hnB hn => ?_
    by_contra hf; exact hn (Finset.mem_inter.mpr ⟨(h n hf).mpr hnB, hnB⟩)
  rw [← e1, e2]

lemma famForm_congr_supp (W : Weight) (Q : ℝ) {A B : Finset ℤ} {x : ℤ → ℂ}
    (h : ∀ n, x n ≠ 0 → (n ∈ A ↔ n ∈ B)) : famForm W Q A x = famForm W Q B x := by
  unfold famForm
  refine Finset.sum_congr rfl fun q _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [sum_congr_supp (fun n => x n * χ n) (fun n hn => h n (left_ne_zero_of_mul hn))]

lemma normSq_congr_supp {A B : Finset ℤ} {x : ℤ → ℂ}
    (h : ∀ n, x n ≠ 0 → (n ∈ A ↔ n ∈ B)) : normSq A x = normSq B x := by
  unfold normSq
  refine sum_congr_supp (fun n => ‖x n‖ ^ 2) fun n hn => h n ?_
  intro h0; apply hn; simp [h0]

lemma S_congr_supp {A B : Finset ℤ} {x : ℤ → ℂ}
    (h : ∀ n, x n ≠ 0 → (n ∈ A ↔ n ∈ B)) (θ : ℝ) : S A x θ = S B x θ := by
  unfold S
  exact sum_congr_supp (fun n => x n * eA (n * θ)) fun n hn => h n (left_ne_zero_of_mul hn)

lemma levelForm_congr_supp (E : Finset ℕ) (a : ℕ → ℝ) {A B : Finset ℤ} {x : ℤ → ℂ}
    (h : ∀ n, x n ≠ 0 → (n ∈ A ↔ n ∈ B)) : levelForm E a A x = levelForm E a B x := by
  unfold levelForm
  simp_rw [S_congr_supp h]

/-- `[1, Y] ∩ ℤ = intervalZ 1 ⌊Y⌋₊`. -/
lemma rangeZ_eq_intervalZ (Q : ℝ) : P.rangeZ Q = intervalZ 1 ⌊P.Y Q⌋₊ := by
  ext n
  simp only [PrimeSetup.rangeZ, intervalZ, Finset.mem_Icc, Finset.mem_Ico]
  rw [← Int.natCast_floor_eq_floor (P.Y_nonneg Q)]
  omega

/-! ### Nonnegativity and the seminorm inequality -/

lemma normSq_nonneg' (I : Finset ℤ) (x : ℤ → ℂ) : 0 ≤ normSq I x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma levelForm_nonneg {E : Finset ℕ} {a : ℕ → ℝ} (ha : ∀ e ∈ E, 0 ≤ a e) (I : Finset ℤ)
    (x : ℤ → ℂ) : 0 ≤ levelForm E a I x :=
  Finset.sum_nonneg fun e he => mul_nonneg (ha e he) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

lemma norm_add_sq_le_kappa (α β : ℂ) {κ : ℝ} (hκ : 0 < κ) :
    ‖α + β‖ ^ 2 ≤ (1 + κ) * ‖α‖ ^ 2 + (1 + κ⁻¹) * ‖β‖ ^ 2 := by
  have h1 : ‖α + β‖ ≤ ‖α‖ + ‖β‖ := norm_add_le α β
  have h2 : 0 ≤ ‖α + β‖ := norm_nonneg _
  have h3 : 2 * ‖α‖ * ‖β‖ ≤ κ * ‖α‖ ^ 2 + κ⁻¹ * ‖β‖ ^ 2 := by
    have hk : κ * κ⁻¹ = 1 := mul_inv_cancel₀ hκ.ne'
    have := sq_nonneg (κ * ‖α‖ - ‖β‖)
    have hκinv : 0 < κ⁻¹ := inv_pos.mpr hκ
    nlinarith [mul_pos hκ hκinv]
  nlinarith [norm_nonneg α, norm_nonneg β]

lemma S_add (I : Finset ℤ) (x x' : ℤ → ℂ) (θ : ℝ) : S I (x + x') θ = S I x θ + S I x' θ := by
  unfold S; rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => by simp [add_mul]

lemma S_neg (I : Finset ℤ) (x : ℤ → ℂ) (θ : ℝ) : S I (-x) θ = -S I x θ := by
  unfold S; rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun n _ => by simp

/-- **`eqC:seminorm`** for the level forms (nonnegative weights). -/
lemma levelForm_add_le {E : Finset ℕ} {a : ℕ → ℝ} (ha : ∀ e ∈ E, 0 ≤ a e) (I : Finset ℤ)
    (x x' : ℤ → ℂ) {κ : ℝ} (hκ : 0 < κ) :
    levelForm E a I (x + x') ≤ (1 + κ) * levelForm E a I x + (1 + κ⁻¹) * levelForm E a I x' := by
  unfold levelForm
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun e he => ?_
  have hae := ha e he
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [S_add]
  have := norm_add_sq_le_kappa (S I x ((c : ℝ) / e)) (S I x' ((c : ℝ) / e)) hκ
  nlinarith [mul_le_mul_of_nonneg_left this hae]

lemma levelForm_neg (E : Finset ℕ) (a : ℕ → ℝ) (I : Finset ℤ) (x : ℤ → ℂ) :
    levelForm E a I (-x) = levelForm E a I x := by
  unfold levelForm; simp_rw [S_neg, norm_neg]

lemma levelForm_sub_le {E : Finset ℕ} {a : ℕ → ℝ} (ha : ∀ e ∈ E, 0 ≤ a e) (I : Finset ℤ)
    (x x' : ℤ → ℂ) :
    levelForm E a I (x - x') ≤ 2 * levelForm E a I x + 2 * levelForm E a I x' := by
  have h := levelForm_add_le ha I x (-x') (κ := 1) one_pos
  rw [levelForm_neg, ← sub_eq_add_neg] at h
  norm_num at h; linarith

/-! ### The level weights of `μ^♮` (`eqC:nu`) -/

lemma wtmax_nonneg (W : Weight) : 0 ≤ W.wtmax := by
  apply Real.sSup_nonneg
  rintro _ ⟨u, rfl⟩
  exact mul_nonneg (sq_nonneg _) (W.nonneg _)

/-- `ν(e) = Ω(e) + m(e/Q) ≤ 6‖w̃‖_∞ η^{−2}`. -/
lemma aNat_le (W : Weight) {Q : ℝ} (hQ : 0 < Q) {e : ℕ} (he : 1 ≤ e) :
    aNat W Q e ≤ 6 * W.wtmax * W.η⁻¹ ^ 2 := by
  obtain ⟨h1, h2, -⟩ := lemOmega_ac W Q hQ
  have hw := wtmax_nonneg W
  have hΩ := h1 e he
  have he0 : (0 : ℝ) < e / Q := div_pos (by exact_mod_cast he) hQ
  have hm := h2 (e / Q) he0
  have hA : 3 * W.wtmax * min ((Q / e) ^ 2) (W.η⁻¹ ^ 2) ≤ 3 * W.wtmax * W.η⁻¹ ^ 2 :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
  have hB : 3 * W.wtmax * min ((e / Q)⁻¹ ^ 2 / 4) (W.η⁻¹ ^ 2) ≤ 3 * W.wtmax * W.η⁻¹ ^ 2 :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
  unfold aNat
  have := le_abs_self (Ωlev W Q e)
  linarith

/-! ### The multiplicative large sieve on `[1, Y]` -/

lemma famForm_rangeZ_le {C₀ : ℝ} (hmult : MVLargeSieveMult C₀) (W : Weight) {Q : ℝ} (hQ : 1 ≤ Q)
    (x : ℤ → ℂ) :
    famForm W Q (P.rangeZ Q) x ≤ W.wmax * C₀ * (Q ^ 2 + ⌊P.Y Q⌋₊) * normSq (P.rangeZ Q) x := by
  rw [rangeZ_eq_intervalZ]
  refine (famForm_le_mult W Q _ x).trans ?_
  have := mul_le_mul_of_nonneg_left (hmult Q hQ 1 ⌊P.Y Q⌋₊ x) W.wmax_nonneg
  linarith

/-! ### Continuity in `u` -/

lemma continuous_xVec_apply (Q T : ℝ) (y : ℕ → ℝ) (n : ℤ) :
    Continuous (fun u => P.xVec Q T y u n) := by
  unfold PrimeSetup.xVec
  split_ifs
  · exact continuous_const.mul ((P.hatJ_continuous T).comp (continuous_id.sub continuous_const))
  · exact continuous_const

lemma continuous_xs_apply (Q T : ℝ) (y : ℕ → ℝ) (n : ℤ) :
    Continuous (fun u => xs P Q T y u n) := by
  unfold xs
  refine (continuous_xVec_apply P Q T y n).mul ?_
  exact Complex.continuous_ofReal.comp
    (rhoLoc_continuous.comp ((continuous_const.sub continuous_id).div_const _))

lemma continuous_normSq_xs (Q T : ℝ) (I : Finset ℤ) (y : ℕ → ℝ) :
    Continuous (fun u => normSq I (xs P Q T y u)) := by
  unfold normSq
  exact continuous_finsetSum _ fun n _ => ((continuous_xs_apply P Q T y n).norm.pow 2)

lemma continuous_normSq_xt (Q T : ℝ) (I : Finset ℤ) (y : ℕ → ℝ) :
    Continuous (fun u => normSq I (xt P Q T y u)) := by
  unfold normSq xt
  exact continuous_finsetSum _ fun n _ =>
    (((continuous_xVec_apply P Q T y n).sub (continuous_xs_apply P Q T y n)).norm.pow 2)

/-- `g · f` is integrable for continuous `f` (`g` is continuous with compact support). -/
lemma integrable_g_mul {Q : ℝ} (hQ : 1 < Q) {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable (fun u => P.g Q u * f u) :=
  ((P.g_continuous hQ).mul hf).integrable_of_hasCompactSupport
    ((P.g_hasCompactSupport hQ).mul_right)

end Families.Phase3.C
