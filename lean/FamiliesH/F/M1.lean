/-
# Package F: `lem:M1H` ((9.11); Lemma 5.9 for `L = λℓ_*`)

For `QT > 1` the hybrid time kernel is the families kernel of `HSetup.toPS` at `Q' = QT` (same `J`),
so the kernel factorisation is `PrimeSetup.kernel_factorisation`. For `QT < 1`, `L < 0` and
`ψ(u/L) = ψ(u/|L|)` (`ψ` even), so the kernel is the families kernel at `Q' = (QT)⁻¹`. For `QT = 1`,
`L = 0`, `g ≡ 0` and `Φ ≡ 0`. The family form identity is the families proof with the family at `Q` and
the setup at `QT` (the proof never ties the two).
-/
import FamiliesH.F.Sizes

noncomputable section

open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace Families.Hybrid

open Families

namespace F

/-- The (private in `Families`) expansion `x^*Δx = ∑_{n,m} x_n \bar x_m Δ(n,m)`. -/
lemma famForm_eq_sumH (W : Weight) (Q : ℝ) (I : Finset ℤ) (x : ℤ → ℂ) :
    (famForm W Q I x : ℂ) = ∑ n ∈ I, ∑ m ∈ I, x n * conj (x m) * Δ W Q n m := by
  have hz : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := fun z => by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  unfold famForm Δ
  push_cast
  simp_rw [← Complex.ofReal_pow, hz, map_sum, map_mul, Finset.sum_mul_sum, Finset.mul_sum]
  calc _ = ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ n ∈ I, ∑ m ∈ I, ∑ χ ∈ primChars q,
        (W.omega Q q : ℂ) * (x n * χ n * (conj (x m) * conj (χ m))) := by
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [Finset.sum_comm]
    _ = ∑ n ∈ I, ∑ m ∈ I, ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ ∈ primChars q,
        (W.omega Q q : ℂ) * (x n * χ n * (conj (x m) * conj (χ m))) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [Finset.sum_comm]
    _ = _ := by
          refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
          refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun χ _ => ?_
          ring

/-- The families ratio-form factorisation with the **family** at `Qf` and the **setup** at `Qs`
(the families proof never ties the two parameters). -/
theorem ratioForm_factorisation_gen (P : PrimeSetup) {Qs : ℝ} (hQs : 1 < Qs) (T : ℝ) (W : Weight)
    (Qf : ℝ) (y : ℕ → ℝ) :
    (∑ n ∈ P.range Qs, ∑ m ∈ P.range Qs, (y n : ℂ) * y m * Δ W Qf n m * P.𝒦 Qs T n m) =
      ∫ u, (P.g Qs u : ℂ) * famForm W Qf (P.rangeZ Qs) (P.xVec Qs T y u) := by
  set LHS := (∑ n ∈ P.range Qs, ∑ m ∈ P.range Qs, (y n : ℂ) * y m * Δ W Qf n m * P.𝒦 Qs T n m)
    with hLHS
  set I := P.rangeZ Qs with hI
  set K : ℤ → ℤ → ℝ → ℂ := fun n m u => (P.g Qs u : ℂ) * P.hatJ T (u - Real.log n.toNat) *
    conj (P.hatJ T (u - Real.log m.toNat)) with hKdef
  set c : ℤ → ℤ → ℂ := fun n m => (y n.toNat : ℂ) * y m.toNat * Δ W Qf n m with hcdef
  have hpt : ∀ u, (P.g Qs u : ℂ) * famForm W Qf I (P.xVec Qs T y u)
      = ∑ n ∈ I, ∑ m ∈ I, c n m * K n m u := by
    intro u
    rw [famForm_eq_sumH, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    simp only [PrimeSetup.xVec, if_pos hn1, if_pos hm1, hcdef, hKdef, map_mul,
      Complex.conj_ofReal]
    ring
  have hKint : ∀ n m, Integrable (K n m) := by
    intro n m
    have hg : Integrable (fun u => (P.g Qs u : ℂ)) := (P.g_integrable hQs).ofReal
    have h1 : Integrable (fun u => (P.g Qs u : ℂ) * P.hatJ T (u - Real.log n.toNat)) :=
      hg.mul_bdd (c := volume.real (P.J T))
        ((P.hatJ_continuous T).comp (continuous_id.sub continuous_const)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun u => P.hatJ_norm_le T _)
    exact h1.mul_bdd (c := volume.real (P.J T))
      ((Complex.continuous_conj.comp
        ((P.hatJ_continuous T).comp (continuous_id.sub continuous_const)))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => by
        rw [Complex.norm_conj]; exact P.hatJ_norm_le T _)
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_finsetSum _ (fun n _ => integrable_finsetSum _ fun m _ => (hKint n m).const_mul _)]
  simp_rw [integral_finsetSum _ (fun m _ => (hKint _ m).const_mul _), integral_const_mul]
  have hK : ∀ n ∈ I, ∀ m ∈ I, ∫ u, K n m u = P.𝒦 Qs T n.toNat m.toNat := by
    intro n hn m hm
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    rw [P.kernel_factorisation hQs n.toNat m.toNat (by omega) (by omega)]
  rw [Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun m hm => by rw [hK n hn m hm]]
  have hY := P.Y_nonneg Qs
  have hmem : ∀ k : ℕ, k ∈ P.range Qs ↔ (k : ℤ) ∈ I := by
    intro k
    simp only [PrimeSetup.range, hI, PrimeSetup.rangeZ, Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨by exact_mod_cast h1, ?_⟩
      rw [Int.le_floor]; push_cast
      exact (Nat.le_floor_iff hY).mp h2
    · rintro ⟨h1, h2⟩
      refine ⟨by exact_mod_cast h1, ?_⟩
      rw [Nat.le_floor_iff hY]
      rw [Int.le_floor] at h2; push_cast at h2; exact h2
  have hreindex : ∀ F : ℤ → ℂ, ∑ n ∈ I, F n = ∑ k ∈ P.range Qs, F k := by
    intro F
    symm
    refine Finset.sum_bij' (fun (k : ℕ) _ => (k : ℤ)) (fun (n : ℤ) _ => n.toNat) ?_ ?_ ?_ ?_ ?_
    · intro k hk; exact (hmem k).mp hk
    · intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      rw [hmem, Int.toNat_of_nonneg (by omega)]; exact hn
    · intro k _; simp
    · intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      exact Int.toNat_of_nonneg (by omega)
    · intro k _; rfl
  rw [hLHS, hreindex]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hreindex]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [hcdef, Int.toNat_natCast]

end F

namespace HSetup

open Families.Hybrid.F

variable (P : HSetup)

/-! ### The case `QT < 1`: `ψ` even -/

lemma ψL_eq_inv {Q T : ℝ} (u : ℝ) : P.ψL Q T u = P.toPS.ψL (Q * T)⁻¹ u := by
  unfold HSetup.ψL HSetup.L PrimeSetup.ψL PrimeSetup.L ellS
  simp only [toPS, Real.log_inv, mul_neg, div_neg]
  rw [P.ψ_even]

lemma g_eq_inv (Q T : ℝ) : P.g Q T = P.toPS.g (Q * T)⁻¹ := by
  funext u
  unfold HSetup.g PrimeSetup.g
  simp only [P.ψL_eq_inv]

lemma Φ_eq_inv (Q T : ℝ) : P.Φ Q T = P.toPS.Φ (Q * T)⁻¹ := by
  funext t
  unfold HSetup.Φ PrimeSetup.Φ
  simp only [P.ψL_eq_inv]

lemma 𝒦_eq_inv (Q T : ℝ) (n m : ℕ) : P.𝒦 Q T n m = P.toPS.𝒦 (Q * T)⁻¹ T n m := by
  unfold HSetup.𝒦 PrimeSetup.𝒦
  rw [P.Φ_eq_inv]; rfl

/-- For `QT < 1` (and `QT > 0`) the range `[1, Y]` is empty. -/
lemma Y_lt_one {Q T : ℝ} (hQT0 : 0 < Q * T) (hQT : Q * T < 1) : P.Y Q T < 1 := by
  unfold HSetup.Y HSetup.X HSetup.L ellS
  have hL : P.lam * Real.log (Q * T) < 0 :=
    mul_neg_of_pos_of_neg P.lam_pos (Real.log_neg hQT0 hQT)
  rw [← Real.exp_mul]
  exact Real.exp_lt_one_iff.mpr (by nlinarith [P.ε₁_pos])

lemma range_empty {Q T : ℝ} (hQT0 : 0 < Q * T) (hQT : Q * T < 1) : P.range Q T = ∅ := by
  unfold HSetup.range
  have h0 : ⌊P.Y Q T⌋₊ = 0 := Nat.floor_eq_zero.mpr (P.Y_lt_one hQT0 hQT)
  rw [h0]; rfl

lemma rangeZ_empty {Q T : ℝ} (hQT0 : 0 < Q * T) (hQT : Q * T < 1) : P.rangeZ Q T = ∅ := by
  unfold HSetup.rangeZ
  have hY0 : 0 ≤ P.Y Q T := Real.rpow_nonneg (Real.exp_pos _).le _
  have h0 : ⌊P.Y Q T⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨hY0, P.Y_lt_one hQT0 hQT⟩
  rw [h0]; rfl

/-! ### The degenerate case `QT = 1` -/

lemma ψL_eq_zero_L {Q T : ℝ} (hQT : Q * T = 1) (u : ℝ) : P.ψL Q T u = P.ψ 0 := by
  unfold HSetup.ψL HSetup.L ellS
  rw [hQT, Real.log_one, mul_zero, div_zero]

lemma g_eq_zero_of {Q T : ℝ} (hQT : Q * T = 1) (u : ℝ) : P.g Q T u = 0 := by
  unfold HSetup.g
  simp only [P.ψL_eq_zero_L hQT]
  rw [integral_const]
  simp [Measure.real]

lemma Φ_eq_zero_of {Q T : ℝ} (hQT : Q * T = 1) (t : ℝ) : P.Φ Q T t = 0 := by
  unfold HSetup.Φ
  simp only [P.ψL_eq_zero_L hQT]
  by_cases h0 : P.ψ 0 = 0
  · simp [h0]
  · apply integral_undef
    intro hint
    have hn : Integrable (fun _ : ℝ => P.ψ 0 ^ 2) volume :=
      hint.norm.congr (Filter.Eventually.of_forall fun a => by simp [Complex.norm_exp])
    rcases (integrable_const_iff).mp hn with h | h
    · exact h0 (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h)
    · have : volume (Set.univ : Set ℝ) < ⊤ := measure_lt_top _ _
      rw [Real.volume_univ] at this
      exact lt_irrefl _ this

lemma 𝒦_eq_zero_of {Q T : ℝ} (hQT : Q * T = 1) (n m : ℕ) : P.𝒦 Q T n m = 0 := by
  unfold HSetup.𝒦
  simp only [P.Φ_eq_zero_of hQT]
  simp

/-! ### `lem:M1H` -/

/-- The kernel factorisation, for all `Q, T` with `QT > 0`. -/
theorem kernel_factorisationH {Q T : ℝ} (hQT0 : 0 < Q * T) (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    P.𝒦 Q T n m = ∫ u, (P.g Q T u : ℂ) * P.hatJ T (u - Real.log n) *
      conj (P.hatJ T (u - Real.log m)) := by
  rcases lt_trichotomy (Q * T) 1 with h | h | h
  · -- `QT < 1`
    have hinv : 1 < (Q * T)⁻¹ := one_lt_inv_iff₀.mpr ⟨hQT0, h⟩
    rw [P.𝒦_eq_inv, P.g_eq_inv]
    exact P.toPS.kernel_factorisation hinv n m hn hm
  · -- `QT = 1`
    rw [P.𝒦_eq_zero_of h]
    simp [P.g_eq_zero_of h]
  · exact P.toPS.kernel_factorisation h n m hn hm

end HSetup

namespace F

/-- **`lem:M1H`** ((9.11)). -/
theorem lemM1H_proof : lemM1H_Statement := by
  intro P Q T hQ hT
  have hQT0 : 0 < Q * T := mul_pos (by linarith) hT
  refine ⟨fun n m hn hm => P.kernel_factorisationH hQT0 n m hn hm, fun W y => ?_⟩
  rcases lt_trichotomy (Q * T) 1 with h | h | h
  · -- `QT < 1`: both sides vanish (empty range)
    unfold HSetup.ratioForm
    rw [P.range_empty hQT0 h, P.rangeZ_empty hQT0 h]
    simp [famForm]
  · -- `QT = 1`: `𝒦 ≡ 0` and `g ≡ 0`
    unfold HSetup.ratioForm
    simp [P.𝒦_eq_zero_of h, P.g_eq_zero_of h]
  · exact ratioForm_factorisation_gen P.toPS h T W Q y

end F

end Families.Hybrid
