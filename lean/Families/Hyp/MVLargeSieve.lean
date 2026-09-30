/-
# Discharging `MV_LargeSieve` (classical input (b1)) from `lem:dual`

`Families.Hyp.MV_LargeSieve_proof : MV_LargeSieve`, with the constant `C₀ = 17/4`.

* **Additive (Farey) large sieve** (`mvAdd_proof : MVLargeSieveAdd (17/4)`). Apply `lem:dual`
  (`Families.lemDual`, proved) to the Farey points `c/e` (`1 ≤ e ≤ E`, `c ∈ reduced e`)
  with unit masses and `κ = 1/4`, so `ς = 1/(4K)`. Since `k₀ ≤ ς⁻¹` is supported on `|ξ| < ς`, and
  the lifts `c/e − m` of the Farey points are `1/E²`-separated in `ℝ` (distinct reduced fractions
  differ by at least `1/(ee')`), an interval of length `2ς` contains at most `2ςE² + 1` of them, so
  `(μ * k_ς)(c/e) ≤ ς⁻¹(2ςE² + 1) = 4K + 2E²`. Hence
  `∑_{e≤E} ∑*_c |S(c/e)|² ≤ (17/16)(4K + 2E²)‖x‖² ≤ (17/4)(K + E²)‖x‖²`.
* **Multiplicative large sieve** (`mvMult_of_add`). The per-modulus Gauss transfer `gauss_per_q`
  (`Families/Toeplitz.lean`): `(q/φ(q)) ∑*_χ |∑ x_n χ(n)|² ≤ ∑*_{c mod q} |S(c/q)|²`; sum over
  `q ≤ ⌊Q⌋` and use `⌊Q⌋² ≤ Q²`.

No `zeta23` input is used (`zeta23`'s Montgomery–Vaughan inequality lives on `ℝ`, not on the circle).
-/
import Families.Wired.Phase1
import Families.Glue

noncomputable section

open scoped BigOperators
open Finset

namespace Families.Hyp

open Families

/-! ### Counting separated points in an interval -/

/-- If `⌊a⌋₊`-values of two nonnegative reals coincide, they are less than `1` apart. -/
lemma natFloor_lt_of_add_one_le {a b : ℝ} (ha : 0 ≤ a) (hab : a + 1 ≤ b) : ⌊a⌋₊ < ⌊b⌋₊ := by
  have h1 : (⌊a⌋₊ : ℝ) + 1 ≤ b := by linarith [Nat.floor_le ha]
  have h2 : ⌊a⌋₊ + 1 ≤ ⌊b⌋₊ := by
    apply Nat.le_floor
    push_cast
    exact h1
  omega

/-- A `δ`-separated finite family of reals in `[A, A + L)` has at most `L/δ + 1` members. -/
lemma card_le_of_separated {α : Type*} (s : Finset α) (y : α → ℝ) {δ A L : ℝ} (hδ : 0 < δ)
    (hL : 0 ≤ L) (hy : ∀ i ∈ s, A ≤ y i ∧ y i < A + L)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → δ ≤ |y i - y j|) :
    (s.card : ℝ) ≤ L / δ + 1 := by
  set f : α → ℕ := fun i => ⌊(y i - A) / δ⌋₊ with hf
  have hmaps : ∀ i ∈ s, f i ∈ Finset.range (⌊L / δ⌋₊ + 1) := by
    intro i hi
    rw [Finset.mem_range, Nat.lt_add_one_iff]
    apply Nat.floor_le_floor
    have := hy i hi
    exact div_le_div_of_nonneg_right (by linarith) hδ.le
  have hinj : Set.InjOn f s := by
    intro i hi j hj hij
    by_contra hne
    have h := hsep i hi j hj hne
    have hi' := hy i hi
    have hj' := hy j hj
    have hai : 0 ≤ (y i - A) / δ := div_nonneg (by linarith) hδ.le
    have haj : 0 ≤ (y j - A) / δ := div_nonneg (by linarith) hδ.le
    rcases le_total (y i) (y j) with hle | hle
    · rw [abs_of_nonpos (by linarith)] at h
      have : (y i - A) / δ + 1 ≤ (y j - A) / δ := by
        rw [div_add_one hδ.ne', div_le_div_iff_of_pos_right hδ]; linarith
      have := natFloor_lt_of_add_one_le hai this
      simp only [hf] at hij
      omega
    · rw [abs_of_nonneg (by linarith)] at h
      have : (y j - A) / δ + 1 ≤ (y i - A) / δ := by
        rw [div_add_one hδ.ne', div_le_div_iff_of_pos_right hδ]; linarith
      have := natFloor_lt_of_add_one_le haj this
      simp only [hf] at hij
      omega
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  rw [Finset.card_range] at hcard
  have : (s.card : ℝ) ≤ (⌊L / δ⌋₊ : ℝ) + 1 := by exact_mod_cast hcard
  linarith [Nat.floor_le (div_nonneg hL hδ.le)]

/-! ### The Farey points -/

/-- The Farey points of order `E`, indexed by `⟨e, c⟩` with `1 ≤ e ≤ E`, `c ∈ reduced e`. -/
def fareyIdx (E : ℕ) : Finset ((_ : ℕ) × ℕ) := (Finset.Icc 1 E).sigma fun e => reduced e

/-- The point `c/e` of the index `⟨e, c⟩`. -/
def fareyPt (p : (_ : ℕ) × ℕ) : ℝ := (p.2 : ℝ) / p.1

lemma mem_fareyIdx {E : ℕ} {p : (_ : ℕ) × ℕ} :
    p ∈ fareyIdx E ↔ (1 ≤ p.1 ∧ p.1 ≤ E) ∧ p.2 < p.1 ∧ Nat.Coprime p.2 p.1 := by
  obtain ⟨e, c⟩ := p
  simp [fareyIdx, reduced, Finset.mem_sigma, Finset.mem_Icc]

lemma fareyPt_mem_Ico {E : ℕ} {p : (_ : ℕ) × ℕ} (hp : p ∈ fareyIdx E) :
    0 ≤ fareyPt p ∧ fareyPt p < 1 := by
  rw [mem_fareyIdx] at hp
  have he : (0 : ℝ) < p.1 := by exact_mod_cast (by omega : 0 < p.1)
  refine ⟨by unfold fareyPt; positivity, ?_⟩
  unfold fareyPt
  rw [div_lt_one he]
  exact_mod_cast hp.2.1

/-- Distinct lifts `c/e − m` of Farey points of order `E` are `1/E²`-separated. -/
lemma farey_lift_sep {E : ℕ} {p p' : (_ : ℕ) × ℕ} (hp : p ∈ fareyIdx E) (hp' : p' ∈ fareyIdx E)
    (m m' : ℤ) (hne : (p, m) ≠ (p', m')) :
    1 / (E : ℝ) ^ 2 ≤ |(fareyPt p - m) - (fareyPt p' - m')| := by
  obtain ⟨e, c⟩ := p
  obtain ⟨e', c'⟩ := p'
  have hp0 := hp
  have hp0' := hp'
  rw [mem_fareyIdx] at hp hp'
  simp only at hp hp'
  have he : (0 : ℝ) < e := by exact_mod_cast (by omega : 0 < e)
  have he' : (0 : ℝ) < e' := by exact_mod_cast (by omega : 0 < e')
  have heE : (e : ℝ) ≤ E := by exact_mod_cast hp.1.2
  have heE' : (e' : ℝ) ≤ E := by exact_mod_cast hp'.1.2
  -- the numerator `N = c e' − c' e + (m' − m) e e'`
  set N : ℤ := (c : ℤ) * e' - (c' : ℤ) * e + (m' - m) * e * e' with hN
  have hdiff : (fareyPt ⟨e, c⟩ - m) - (fareyPt ⟨e', c'⟩ - m') = (N : ℝ) / ((e : ℝ) * e') := by
    unfold fareyPt
    simp only [hN]
    push_cast
    field_simp
    ring
  have hN0 : N ≠ 0 := by
    intro h0
    have hreal : (c : ℝ) / e = (c' : ℝ) / e' - ((m' - m : ℤ) : ℝ) := by
      have : (N : ℝ) = 0 := by exact_mod_cast h0
      simp only [hN] at this
      push_cast at this ⊢
      field_simp
      linarith
    have hfr : Int.fract ((c : ℝ) / e) = Int.fract ((c' : ℝ) / e') := by
      rw [hreal, Int.fract_sub_intCast]
    have hmemr : c ∈ reduced e := by
      simp only [reduced, Finset.mem_filter, Finset.mem_range]; exact ⟨hp.2.1, hp.2.2⟩
    have hmemr' : c' ∈ reduced e' := by
      simp only [reduced, Finset.mem_filter, Finset.mem_range]; exact ⟨hp'.2.1, hp'.2.2⟩
    obtain ⟨hee, hcc⟩ := reduced_frac_inj hmemr hmemr' hfr
    subst hee hcc
    have hm : (m' - m) * e * e = 0 := by
      simp only [hN, sub_self, zero_add] at h0
      linarith
    have he0 : (e : ℤ) ≠ 0 := by exact_mod_cast (by omega : e ≠ 0)
    have : m' - m = 0 := by
      rcases mul_eq_zero.mp hm with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact h
        · exact absurd h he0
      · exact absurd h he0
    exact hne (by rw [show m = m' by linarith])
  have hprod : (0 : ℝ) < (e : ℝ) * e' := mul_pos he he'
  rw [hdiff, abs_div, abs_of_pos hprod]
  have hN1 : (1 : ℝ) ≤ |(N : ℝ)| := by
    have : 1 ≤ |N| := Int.one_le_abs hN0
    exact_mod_cast this
  have hee : (e : ℝ) * e' ≤ (E : ℝ) ^ 2 := by
    rw [sq]; exact mul_le_mul heE heE' he'.le (by linarith)
  calc 1 / (E : ℝ) ^ 2 ≤ 1 / ((e : ℝ) * e') :=
        one_div_le_one_div_of_le (by positivity) hee
    _ ≤ |(N : ℝ)| / ((e : ℝ) * e') := by
        apply div_le_div_of_nonneg_right hN1 (by positivity)

/-- `k_ς(ξ)` for `|ξ| < 1` and `ς ≤ 1` is the finite sum over `m ∈ {−1, 0, 1}`. -/
lemma kper_eq_sum {ς ξ : ℝ} (hς : 0 < ς) (hς1 : ς ≤ 1) (hξ : |ξ| < 1) :
    kper ς ξ = ∑ m ∈ Finset.Icc (-1 : ℤ) 1, k0 ς (ξ + m) := by
  unfold kper
  apply tsum_eq_sum
  intro m hm
  rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hm
  apply Phase1.A.k0_eq_zero hς
  have hm' : (2 : ℝ) ≤ |(m : ℝ)| := by
    rcases hm with hm | hm
    · have : (m : ℝ) ≤ -2 := by exact_mod_cast (by omega : m ≤ -2)
      rw [abs_of_neg (by linarith)]; linarith
    · have : (2 : ℝ) ≤ m := by exact_mod_cast (by omega : 2 ≤ m)
      rw [abs_of_pos (by linarith)]; linarith
  have := abs_sub_abs_le_abs_sub (m : ℝ) (-ξ)
  rw [abs_neg, sub_neg_eq_add, add_comm] at this
  linarith

/-- **The Farey convolution bound.** For `0 < ς ≤ 1/2`, and a Farey point `θ_i` of order `E`,
`∑_j k_ς(θ_i − θ_j) ≤ ς⁻¹ (2ςE² + 1)`. -/
lemma farey_conv_le {E : ℕ} {ς : ℝ} (hς : 0 < ς) (hς1 : ς ≤ 1 / 2) {i : (_ : ℕ) × ℕ}
    (hi : i ∈ fareyIdx E) :
    ∑ j ∈ fareyIdx E, kper ς (fareyPt i - fareyPt j) ≤ ς⁻¹ * (2 * ς * (E : ℝ) ^ 2 + 1) := by
  classical
  have hE : 1 ≤ E := by rw [mem_fareyIdx] at hi; omega
  have hE0 : (0 : ℝ) < E := by exact_mod_cast hE
  set F := Finset.Icc (-1 : ℤ) 1
  set s := fareyIdx E
  set P : ((_ : ℕ) × ℕ) × ℤ → Prop := fun q => |fareyPt i - fareyPt q.1 + q.2| < ς with hP
  -- step 1: expand `kper` as a finite sum
  have h1 : ∑ j ∈ s, kper ς (fareyPt i - fareyPt j) =
      ∑ q ∈ s ×ˢ F, k0 ς (fareyPt i - fareyPt q.1 + q.2) := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun j hj => ?_
    apply kper_eq_sum hς (by linarith)
    have := fareyPt_mem_Ico hi
    have := fareyPt_mem_Ico hj
    rw [abs_lt]; constructor <;> linarith
  -- step 2: bound each term by `ς⁻¹ 1[|·| < ς]`
  have h2 : ∑ q ∈ s ×ˢ F, k0 ς (fareyPt i - fareyPt q.1 + q.2) ≤
      ∑ q ∈ (s ×ˢ F).filter P, ς⁻¹ := by
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun q _ => ?_
    split_ifs with h
    · exact Phase1.A.k0_le hς _
    · rw [Phase1.A.k0_eq_zero hς (not_lt.mp h)]
  -- step 3: count the lifts in `(θ_i − ς, θ_i + ς)`
  have h3 : (((s ×ˢ F).filter P).card : ℝ) ≤ 2 * ς / (1 / (E : ℝ) ^ 2) + 1 := by
    refine card_le_of_separated _ (fun q => fareyPt q.1 - q.2) (A := fareyPt i - ς)
      (by positivity) (by linarith) ?_ ?_
    · intro q hq
      rw [Finset.mem_filter] at hq
      have := hq.2
      simp only [hP] at this
      rw [abs_lt] at this
      constructor <;> linarith
    · intro q hq q' hq' hne
      rw [Finset.mem_filter, Finset.mem_product] at hq hq'
      exact farey_lift_sep hq.1.1 hq'.1.1 q.2 q'.2 hne
  rw [h1]
  refine h2.trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hς' : 0 ≤ ς⁻¹ := inv_nonneg.mpr hς.le
  calc ς⁻¹ * (((s ×ˢ F).filter P).card : ℝ) ≤ ς⁻¹ * (2 * ς / (1 / (E : ℝ) ^ 2) + 1) :=
        mul_le_mul_of_nonneg_left h3 hς'
    _ = ς⁻¹ * (2 * ς * (E : ℝ) ^ 2 + 1) := by rw [div_div_eq_mul_div, div_one]

/-! ### The additive large sieve -/

/-- **The additive large sieve at Farey fractions**, constant `17/4`, from `lem:dual`. -/
theorem mvAdd_proof : MVLargeSieveAdd (17 / 4) := by
  intro E N₀ K x
  classical
  -- the empty interval
  rcases Nat.eq_zero_or_pos K with hK0 | hK
  · subst hK0
    simp [intervalZ, S, normSq]
  have hK1 : 1 ≤ K := hK
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  set ς : ℝ := (1 / 4 : ℝ) / K with hςdef
  have hς : 0 < ς := by positivity
  have hς2 : ς ≤ 1 / 2 := by
    rw [hςdef, div_le_iff₀ (by linarith)]; linarith
  have hςinv : ς⁻¹ = 4 * K := by rw [hςdef]; field_simp
  set M : ℝ := 4 * K + 2 * (E : ℝ) ^ 2 with hM
  have hM0 : 0 ≤ M := by positivity
  have hdual := lemDual (σ := (_ : ℕ) × ℕ) (fareyIdx E) fareyPt (fun _ => 1)
    (fun _ _ => one_pos) ?_ N₀ K hK1 (1 / 4) (by norm_num) le_rfl M hM0 ?_ x
  · -- conclude
    have hlhs : ∑ e ∈ Finset.Icc 1 E, ∑ c ∈ reduced e,
        ‖S (intervalZ N₀ K) x ((c : ℝ) / e)‖ ^ 2 =
        ∑ i ∈ fareyIdx E, 1 * ‖S (intervalZ N₀ K) x (fareyPt i)‖ ^ 2 := by
      rw [fareyIdx, Finset.sum_sigma]
      simp [fareyPt]
    rw [hlhs]
    refine hdual.trans ?_
    have hn : 0 ≤ normSq (intervalZ N₀ K) x :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hE2 : 0 ≤ (E : ℝ) ^ 2 := by positivity
    apply mul_le_mul_of_nonneg_right _ hn
    rw [hM]
    nlinarith
  · -- distinct fractional parts
    intro i hi j hj hij hfr
    obtain ⟨e, c⟩ := i
    obtain ⟨e', c'⟩ := j
    have hr : c ∈ reduced e := (Finset.mem_sigma.mp hi).2
    have hr' : c' ∈ reduced e' := (Finset.mem_sigma.mp hj).2
    obtain ⟨hee, hcc⟩ := reduced_frac_inj hr hr' hfr
    subst hee hcc
    exact hij rfl
  · -- the convolution bound
    intro i hi
    simp only [one_mul]
    refine (farey_conv_le hς hς2 hi).trans (le_of_eq ?_)
    rw [hςinv, hM, hςdef]
    field_simp
    ring

/-! ### The multiplicative large sieve -/

/-- The multiplicative large sieve follows from the additive one via the Gauss transfer
`gauss_per_q`. -/
theorem mvMult_of_add {C₀ : ℝ} (hC₀ : 0 ≤ C₀) (h : MVLargeSieveAdd C₀) : MVLargeSieveMult C₀ := by
  intro Q hQ N₀ K x
  set E := ⌊Q⌋₊ with hE
  have hstep : ∀ q ∈ Finset.Icc 1 E, ((q : ℝ) / (Nat.totient q : ℝ)) *
      ∑ χ ∈ primChars q, ‖∑ n ∈ intervalZ N₀ K, x n * χ n‖ ^ 2 ≤
      ∑ c ∈ reduced q, ‖S (intervalZ N₀ K) x ((c : ℝ) / q)‖ ^ 2 := by
    intro q hq
    have hq0 : 0 < q := (Finset.mem_Icc.mp hq).1
    have : NeZero q := ⟨hq0.ne'⟩
    have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq0
    have key := gauss_per_q q (intervalZ N₀ K) x
    rw [div_mul_eq_mul_div, div_le_iff₀ hφ]
    linarith
  refine (Finset.sum_le_sum hstep).trans ((h E N₀ K x).trans ?_)
  have hn : 0 ≤ normSq (intervalZ N₀ K) x := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hEQ : (E : ℝ) ≤ Q := Nat.floor_le (by linarith)
  have hE0 : (0 : ℝ) ≤ E := Nat.cast_nonneg _
  have hE2 : (E : ℝ) ^ 2 ≤ Q ^ 2 := pow_le_pow_left₀ hE0 hEQ 2
  apply mul_le_mul_of_nonneg_right _ hn
  apply mul_le_mul_of_nonneg_left _ hC₀
  linarith

/-! ### `MV_LargeSieve` -/

/-- **`MV_LargeSieve` (classical input (b1)) is a theorem**, with `C₀ = 17/4`, from `lem:dual` and the
Gauss transfer. -/
theorem MV_LargeSieve_proof : MV_LargeSieve :=
  ⟨17 / 4, mvMult_of_add (by norm_num) mvAdd_proof, mvAdd_proof⟩

end Families.Hyp
