/-
# Montgomery 1969 density: the mollified family mean square

For `σ ≥ 1/2 + δ/2`, `W ≥ 2`, `Q ≥ 1`, `X = ⌊√Q⌋`:
`∑_{2 ≤ q ≤ Q} ∑*_χ ∫_{−W}^{W} |L(σ+iv,χ) M_X(σ+iv,χ) − 1|² dv ≪ (1+2/δ)⁴ (1+log Q)² Q² W Q^{−δ/4}`.

`L M_X − 1 = D^{≤Y} + D^{>Y} + (L − P_N) M_X` (`LM_decomp`), with `D^{≤Y}` bounded by the hybrid large
sieve, `D^{>Y}` by Gallagher + Pólya–Vinogradov per character, and the tail `L − P_N` trivially.
-/
import Families.Hyp.Montgomery.HybridLS
import Families.Hyp.Montgomery.CharSums
import Families.Hyp.Montgomery.Mollifier
import Families.Hyp.Montgomery.Trivial

noncomputable section

open scoped BigOperators ComplexConjugate ArithmeticFunction.Moebius
open MeasureTheory Real Finset ArithmeticFunction

namespace Families.Hyp.Montgomery

open Families

/-! ### The mollifier -/

/-- `M_X(s,χ) = ∑_{d ≤ X} μ(d) χ(d) d^{−s}`. -/
def Mol (X : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 X, (μ d : ℂ) * χ (d : ZMod q) * (d : ℂ) ^ (-s)

/-- The partial sum `P_N(s,χ) = ∑_{m ≤ N} χ(m) m^{−s}`. -/
def Psum (N : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 N, χ (m : ZMod q) * (m : ℂ) ^ (-s)

lemma differentiable_Mol (X : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Differentiable ℂ (Mol X χ) := by
  intro s
  unfold Mol
  refine DifferentiableAt.fun_sum fun d hd => ?_
  have hd0 : (d : ℂ) ≠ 0 := by
    have := (Finset.mem_Icc.mp hd).1; exact_mod_cast (by omega : d ≠ 0)
  exact (differentiableAt_id.neg.const_cpow (Or.inl hd0)).const_mul _

lemma norm_natCast_cpow_neg (n : ℕ) (hn : 1 ≤ n) (s : ℂ) :
    ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega)]; simp

lemma natCast_rpow_neg_le_one (n : ℕ) (hn : 1 ≤ n) {σ : ℝ} (hσ : 0 ≤ σ) :
    (n : ℝ) ^ (-σ) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith)

lemma norm_Mol_le (X : ℕ) {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖Mol X χ s‖ ≤ X := by
  unfold Mol
  refine (norm_sum_le _ _).trans ?_
  calc ∑ d ∈ Finset.Icc 1 X, ‖(μ d : ℂ) * χ (d : ZMod q) * (d : ℂ) ^ (-s)‖
      ≤ ∑ d ∈ Finset.Icc 1 X, (1 : ℝ) := by
        refine Finset.sum_le_sum fun d hd => ?_
        have hd1 := (Finset.mem_Icc.mp hd).1
        rw [norm_mul, norm_mul, norm_natCast_cpow_neg d hd1]
        have h1 : ‖(μ d : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_intCast]; exact_mod_cast abs_moebius_le_one
        have h2 : ‖χ (d : ZMod q)‖ ≤ 1 := χ.norm_le_one _
        have h3 := natCast_rpow_neg_le_one d hd1 hs
        have h4 : (0 : ℝ) ≤ (d : ℝ) ^ (-s.re) := by positivity
        calc ‖(μ d : ℂ)‖ * ‖χ (d : ZMod q)‖ * (d : ℝ) ^ (-s.re) ≤ 1 * 1 * 1 := by gcongr
          _ = 1 := by ring
    _ = X := by simp

lemma sum_Icc_one_eq {M : Type*} [AddCommMonoid M] (X : ℕ) (hX : 1 ≤ X) (f : ℕ → M) :
    ∑ d ∈ Finset.Icc 1 X, f d = f 1 + ∑ d ∈ Finset.Icc 2 X, f d := by
  have e : Finset.Icc 2 X = Finset.Ioc 1 X := Finset.Icc_add_one_left_eq_Ioc 1 X
  rw [Finset.Icc_eq_cons_Ioc hX, Finset.sum_cons, e]

lemma norm_Mol_sub_one_le {X : ℕ} (hX : 1 ≤ X) {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 4 ≤ s.re) : ‖Mol X χ s - 1‖ ≤ 1 / 10 := by
  have hsplit : Mol X χ s - 1 =
      ∑ d ∈ Finset.Icc 2 X, (μ d : ℂ) * χ (d : ZMod q) * (d : ℂ) ^ (-s) := by
    unfold Mol
    rw [sum_Icc_one_eq X hX]
    simp
  rw [hsplit]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun d hd => ?_).trans
    (sum_Icc_two_rpow_le X hs))
  have hd1 : 1 ≤ d := by have := (Finset.mem_Icc.mp hd).1; omega
  rw [norm_mul, norm_mul, norm_natCast_cpow_neg d hd1]
  have h1 : ‖(μ d : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]; exact_mod_cast abs_moebius_le_one
  have h2 : ‖χ (d : ZMod q)‖ ≤ 1 := χ.norm_le_one _
  have h4 : (0 : ℝ) ≤ (d : ℝ) ^ (-s.re) := by positivity
  have h5 : (d : ℝ) ^ (-s.re) ≤ (d : ℝ) ^ (-s.re) := le_rfl
  calc ‖(μ d : ℂ)‖ * ‖χ (d : ZMod q)‖ * (d : ℝ) ^ (-s.re) ≤ 1 * 1 * (d : ℝ) ^ (-s.re) := by
        gcongr
    _ = (d : ℝ) ^ (-s.re) := by ring

/-- `‖L M_X − 1‖ ≤ 1/2` on `Re s ≥ 4`. -/
lemma norm_LMol_sub_one_le {X : ℕ} (hX : 1 ≤ X) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 4 ≤ s.re) : ‖χ.LFunction s * Mol X χ s - 1‖ ≤ 1 / 2 := by
  have hL := norm_LFunction_sub_one_le_of_four_le χ hs
  have hM := norm_Mol_sub_one_le hX χ hs
  have hM' : ‖Mol X χ s‖ ≤ 11 / 10 := by
    have := norm_le_norm_sub_add (Mol X χ s) 1
    rw [norm_one] at this; linarith
  have e : χ.LFunction s * Mol X χ s - 1 =
      (χ.LFunction s - 1) * Mol X χ s + (Mol X χ s - 1) := by ring
  rw [e]
  calc ‖(χ.LFunction s - 1) * Mol X χ s + (Mol X χ s - 1)‖
      ≤ ‖χ.LFunction s - 1‖ * ‖Mol X χ s‖ + ‖Mol X χ s - 1‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_mul]
    _ ≤ 1 / 10 * (11 / 10) + 1 / 10 := by
        gcongr
    _ ≤ 1 / 2 := by norm_num

/-! ### `n^{−s}` on vertical lines -/

lemma natCast_cpow_eq_ex (n : ℕ) (hn : 1 ≤ n) (σ v : ℝ) :
    (n : ℂ) ^ (-((σ : ℂ) + (v : ℂ) * Complex.I)) =
      (((n : ℝ) ^ (-σ) : ℝ) : ℂ) * ex v (Real.log n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0' : ((n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hc : (n : ℂ) = ((n : ℝ) : ℂ) := (Complex.ofReal_natCast n).symm
  rw [hc, Complex.cpow_def_of_ne_zero hn0', ex, Complex.ofReal_cpow hn0.le,
    Complex.cpow_def_of_ne_zero hn0', ← Complex.exp_add, ← Complex.ofReal_log hn0.le]
  congr 1
  push_cast
  ring

/-! ### The decomposition `L M − 1 = D^{≤Y} + D^{>Y} + (L − P_N) M` -/

lemma Psum_mul_Mol {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) (X N : ℕ) :
    Psum N χ s * Mol X χ s =
      ∑ n ∈ Finset.Icc 1 (X * N), (beta X N n : ℂ) * (χ (n : ZMod q) * (n : ℂ) ^ (-s)) := by
  rw [sum_beta_mul, Psum, Mol, Finset.sum_mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun m _ => ?_
  rw [Nat.cast_mul, Nat.cast_mul, map_mul, Complex.natCast_mul_natCast_cpow]
  ring

lemma LM_decomp {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) {X N Y : ℕ}
    (hX : 1 ≤ X) (hXN : X ≤ N) (hXY : X ≤ Y) (hYN : Y ≤ X * N) :
    χ.LFunction s * Mol X χ s - 1 =
      (∑ n ∈ Finset.Ioc X Y, (beta X N n : ℂ) * (χ (n : ZMod q) * (n : ℂ) ^ (-s))) +
      (∑ n ∈ Finset.Ioc Y (X * N), (beta X N n : ℂ) * (χ (n : ZMod q) * (n : ℂ) ^ (-s))) +
      (χ.LFunction s - Psum N χ s) * Mol X χ s := by
  have hPM := Psum_mul_Mol χ s X N
  have hXN1 : 1 ≤ X * N := le_trans hX (le_trans hXY hYN)
  rw [sum_Icc_one_eq _ hXN1] at hPM
  have e2 : Finset.Icc 2 (X * N) = Finset.Ioc 1 (X * N) := Finset.Icc_add_one_left_eq_Ioc 1 _
  rw [e2, ← Finset.sum_Ioc_consecutive _ hX (hXY.trans hYN),
    ← Finset.sum_Ioc_consecutive _ hXY hYN] at hPM
  have hzero : ∑ n ∈ Finset.Ioc 1 X, (beta X N n : ℂ) * (χ (n : ZMod q) * (n : ℂ) ^ (-s)) = 0 := by
    refine Finset.sum_eq_zero fun n hn => ?_
    have hn' := Finset.mem_Ioc.mp hn
    rw [beta_eq_zero (by omega) hn'.2 (hn'.2.trans hXN)]; simp
  rw [hzero, zero_add, beta_one hX (hX.trans hXN)] at hPM
  simp only [Int.cast_one, Nat.cast_one, map_one, Complex.one_cpow, one_mul] at hPM
  have e : χ.LFunction s * Mol X χ s - 1 =
      (Psum N χ s * Mol X χ s - 1) + (χ.LFunction s - Psum N χ s) * Mol X χ s := by ring
  rw [e, hPM]
  ring

/-! ### Per-character bound for interval sums (Pólya–Vinogradov + Abel) -/

/-- `PV(q) = 2√q (1 + log q)`. -/
def PV (q : ℕ) : ℝ := 2 * Real.sqrt q * (1 + Real.log q)

lemma PV_nonneg (q : ℕ) : 0 ≤ PV q := by
  unfold PV
  have : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  positivity

lemma filter_Icc_eq_Ico (d N L U : ℕ) (hd : 1 ≤ d) :
    (Finset.Icc 1 N).filter (fun m => L ≤ d * m ∧ d * m < U) =
      Finset.Ico (max 1 ⌈(L : ℝ) / d⌉₊) (min (N + 1) ⌈(U : ℝ) / d⌉₊) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  ext m
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico, max_le_iff, lt_min_iff]
  have h1 : L ≤ d * m ↔ ⌈(L : ℝ) / d⌉₊ ≤ m := by
    rw [Nat.ceil_le, div_le_iff₀ hd0, ← Nat.cast_mul, mul_comm]; exact_mod_cast Iff.rfl
  have h2 : d * m < U ↔ m < ⌈(U : ℝ) / d⌉₊ := by
    rw [Nat.lt_ceil, lt_div_iff₀ hd0, ← Nat.cast_mul, mul_comm]; exact_mod_cast Iff.rfl
  rw [h1, h2]
  omega

lemma inner_interval_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : 2 ≤ q) {σ : ℝ} (hσ : 0 ≤ σ) (d N L U : ℕ) (hd : 1 ≤ d) (hL : 1 ≤ L) :
    ‖∑ m ∈ Finset.Icc 1 N, (if L ≤ d * m ∧ d * m < U then
        χ (m : ZMod q) * (((m : ℝ) ^ (-σ) : ℝ) : ℂ) else 0)‖ ≤ PV q * ((L : ℝ) / d) ^ (-σ) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  set a := max 1 ⌈(L : ℝ) / d⌉₊ with ha
  set b := min (N + 1) ⌈(U : ℝ) / d⌉₊ with hb
  rw [← Finset.sum_filter, filter_Icc_eq_Ico d N L U hd]
  have hAbel := norm_sum_Ico_mul_antitone_le (fun m => χ (m : ZMod q)) (fun m => (m : ℝ) ^ (-σ))
    a b (PV q)
    (fun m n ham hmn => by
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast le_trans (le_max_left _ _) ham
      exact Real.rpow_le_rpow_of_nonpos (by linarith) (by exact_mod_cast hmn) (by linarith))
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun c _ => pv_Ico χ hχ hq a c)
  refine hAbel.trans (mul_le_mul_of_nonneg_left ?_ (PV_nonneg q))
  have hLd : (0 : ℝ) < (L : ℝ) / d := div_pos (by exact_mod_cast hL) hd0
  have haL : (L : ℝ) / d ≤ a := (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
  exact Real.rpow_le_rpow_of_nonpos hLd haL (by linarith)

/-- **The per-character interval bound**: `|∑_{n ∈ [L, U)} β(n) χ(n) n^{−σ}| ≤ X · PV(q) · L^{−σ}`. -/
lemma interval_beta_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : 2 ≤ q) {σ : ℝ} (hσ : 0 ≤ σ) (X N L U : ℕ) (hL : 1 ≤ L) :
    ‖∑ n ∈ Finset.Icc 1 (X * N), (beta X N n : ℂ) *
        (if L ≤ n ∧ n < U then χ (n : ZMod q) * (((n : ℝ) ^ (-σ) : ℝ) : ℂ) else 0)‖
      ≤ X * PV q * (L : ℝ) ^ (-σ) := by
  rw [sum_beta_mul]
  have hterm : ∀ d ∈ Finset.Icc 1 X, ∀ m ∈ Finset.Icc 1 N,
      (μ d : ℂ) * (if L ≤ d * m ∧ d * m < U then
        χ ((d * m : ℕ) : ZMod q) * ((((d * m : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) else 0) =
      ((μ d : ℂ) * χ (d : ZMod q) * (((d : ℝ) ^ (-σ) : ℝ) : ℂ)) *
        (if L ≤ d * m ∧ d * m < U then χ (m : ZMod q) * (((m : ℝ) ^ (-σ) : ℝ) : ℂ) else 0) := by
    intro d _ m _
    split_ifs
    · rw [Nat.cast_mul, Nat.cast_mul, map_mul,
        Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      push_cast; ring
    · ring
  rw [Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun m hm => hterm d hd m hm]
  simp_rw [← Finset.mul_sum]
  refine (norm_sum_le _ _).trans ?_
  have hbound : ∀ d ∈ Finset.Icc 1 X,
      ‖((μ d : ℂ) * χ (d : ZMod q) * (((d : ℝ) ^ (-σ) : ℝ) : ℂ)) *
        ∑ m ∈ Finset.Icc 1 N, (if L ≤ d * m ∧ d * m < U then
          χ (m : ZMod q) * (((m : ℝ) ^ (-σ) : ℝ) : ℂ) else 0)‖ ≤ PV q * (L : ℝ) ^ (-σ) := by
    intro d hd
    have hd1 := (Finset.mem_Icc.mp hd).1
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg hd0.le _)]
    have h1 : ‖(μ d : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]; exact_mod_cast abs_moebius_le_one
    have h2 : ‖χ (d : ZMod q)‖ ≤ 1 := χ.norm_le_one _
    have h3 := inner_interval_bound χ hχ hq hσ d N L U hd1 hL
    have hdiv : ((L : ℝ) / d) ^ (-σ) = (L : ℝ) ^ (-σ) * (d : ℝ) ^ σ := by
      rw [Real.div_rpow (Nat.cast_nonneg _) hd0.le, Real.rpow_neg hd0.le, div_inv_eq_mul]
    rw [hdiv] at h3
    have hdd : (d : ℝ) ^ (-σ) * (d : ℝ) ^ σ = 1 := by
      rw [Real.rpow_neg hd0.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hd0 _).ne']
    have h4 : 0 ≤ (d : ℝ) ^ (-σ) := Real.rpow_nonneg hd0.le _
    calc ‖(μ d : ℂ)‖ * ‖χ (d : ZMod q)‖ * (d : ℝ) ^ (-σ) * ‖∑ m ∈ Finset.Icc 1 N,
          (if L ≤ d * m ∧ d * m < U then χ (m : ZMod q) * (((m : ℝ) ^ (-σ) : ℝ) : ℂ) else 0)‖
        ≤ 1 * 1 * (d : ℝ) ^ (-σ) * (PV q * ((L : ℝ) ^ (-σ) * (d : ℝ) ^ σ)) := by
          gcongr
      _ = PV q * (L : ℝ) ^ (-σ) * ((d : ℝ) ^ (-σ) * (d : ℝ) ^ σ) := by ring
      _ = PV q * (L : ℝ) ^ (-σ) := by rw [hdd, mul_one]
  refine (Finset.sum_le_sum hbound).trans (le_of_eq ?_)
  simp; ring

/-! ### The tail `D^{>Y}` per character (Gallagher + the interval bound) -/

/-- A Dirichlet polynomial on the line `σ + iv` as an exponential sum. -/
lemma dirichlet_eq_exsum {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset ℕ) (hS : ∀ n ∈ S, 1 ≤ n)
    (c : ℕ → ℂ) (σ v : ℝ) :
    ∑ n ∈ S, c n * (χ (n : ZMod q) * (n : ℂ) ^ (-((σ : ℂ) + (v : ℂ) * Complex.I))) =
      ∑ n ∈ S, (c n * χ (n : ZMod q) * (((n : ℝ) ^ (-σ) : ℝ) : ℂ)) * ex v (Real.log n) := by
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [natCast_cpow_eq_ex n (hS n hn)]; ring

/-- The dominating function for the tail windows. -/
def tailDom (Y : ℕ) (h σ : ℝ) (u : ℝ) : ℝ :=
  (Y : ℝ) ^ (-(2 * σ)) * (Set.Ioc (Real.log Y - h) (Real.log Y)).indicator 1 u +
    (Set.Ioi (Real.log Y)).indicator (fun u => Real.exp (-(2 * σ) * u)) u

lemma integrable_tailDom (Y : ℕ) (h : ℝ) {σ : ℝ} (hσ : 0 < σ) : Integrable (tailDom Y h σ) := by
  unfold tailDom
  refine Integrable.add ?_ ?_
  · refine Integrable.const_mul ?_ _
    exact (integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const (by simp))
  · exact (integrable_indicator_iff measurableSet_Ioi).2
      (integrableOn_exp_mul_Ioi (by linarith) _)

lemma integral_tailDom {Y : ℕ} (hY : 1 ≤ Y) {h : ℝ} (hh : 0 ≤ h) {σ : ℝ} (hσ : 0 < σ) :
    ∫ u, tailDom Y h σ u = (Y : ℝ) ^ (-(2 * σ)) * (h + 1 / (2 * σ)) := by
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY
  unfold tailDom
  rw [integral_add, integral_const_mul, integral_indicator_one measurableSet_Ioc,
    integral_indicator measurableSet_Ioi, integral_exp_mul_Ioi (by linarith), Real.volume_real_Ioc,
    max_eq_left (by linarith)]
  · have e : Real.exp (-(2 * σ) * Real.log Y) = (Y : ℝ) ^ (-(2 * σ)) := by
      rw [Real.rpow_def_of_pos hY0]; ring_nf
    rw [e]; field_simp; ring
  · exact ((integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const (by simp))).const_mul _
  · exact (integrable_indicator_iff measurableSet_Ioi).2 (integrableOn_exp_mul_Ioi (by linarith) _)

lemma tailDom_nonneg (Y : ℕ) (h σ u : ℝ) : 0 ≤ tailDom Y h σ u := by
  unfold tailDom
  refine add_nonneg (mul_nonneg (by positivity) ?_) ?_
  · exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  · exact Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _

/-- Pointwise bound for a tail window. -/
lemma tail_window_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : 2 ≤ q) {σ : ℝ} (hσ : 0 < σ) {h : ℝ} (hh : 0 ≤ h) (X N Y : ℕ) (hY : 1 ≤ Y) (u : ℝ) :
    ‖∑ n ∈ Finset.Ioc Y (X * N), (win h u (Real.log n) : ℂ) *
        ((beta X N n : ℂ) * χ (n : ZMod q) * (((n : ℝ) ^ (-σ) : ℝ) : ℂ))‖ ^ 2
      ≤ (X * PV q) ^ 2 * tailDom Y h σ u := by
  set A := ⌈Real.exp u⌉₊ with hA
  set B := ⌈Real.exp (u + h)⌉₊ with hB
  set L := max (Y + 1) A with hL
  have hL1 : 1 ≤ L := le_trans (by omega) (le_max_left _ _)
  -- rewrite the window sum as an interval sum over `[L, B)`
  have hrw : ∑ n ∈ Finset.Ioc Y (X * N), (win h u (Real.log n) : ℂ) *
        ((beta X N n : ℂ) * χ (n : ZMod q) * (((n : ℝ) ^ (-σ) : ℝ) : ℂ)) =
      ∑ n ∈ Finset.Icc 1 (X * N), (beta X N n : ℂ) *
        (if L ≤ n ∧ n < B then χ (n : ZMod q) * (((n : ℝ) ^ (-σ) : ℝ) : ℂ) else 0) := by
    have hsub : Finset.Ioc Y (X * N) ⊆ Finset.Icc 1 (X * N) := by
      intro n hn; simp only [Finset.mem_Ioc, Finset.mem_Icc] at hn ⊢; omega
    rw [← Finset.sum_subset hsub (fun n hn hn' => by
      simp only [Finset.mem_Ioc, Finset.mem_Icc, not_and, not_le] at hn hn'
      have : ¬ (L ≤ n ∧ n < B) := fun h' => by
        have := le_trans (le_max_left _ _) h'.1; omega
      rw [if_neg this, mul_zero])]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn' := Finset.mem_Ioc.mp hn
    rw [win_log_eq h u (by omega : 1 ≤ n)]
    by_cases hc : A ≤ n ∧ n < B
    · have : L ≤ n ∧ n < B := ⟨max_le (by omega) hc.1, hc.2⟩
      simp only [hA, hB] at hc
      rw [if_pos hc, if_pos this]; push_cast; ring
    · have : ¬ (L ≤ n ∧ n < B) := fun h' => hc ⟨le_trans (le_max_right _ _) h'.1, h'.2⟩
      simp only [hA, hB] at hc
      rw [if_neg hc, if_neg this]; simp
  rw [hrw]
  have hbd := interval_beta_bound χ hχ hq hσ.le X N L B hL1
  have hPV := PV_nonneg q
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL1
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY
  by_cases hcase : u ≤ Real.log Y - h
  · -- the window lies below `Y`: the sum vanishes
    have hBY : B ≤ Y := by
      rw [hB, Nat.ceil_le]
      calc Real.exp (u + h) ≤ Real.exp (Real.log Y) := Real.exp_le_exp.mpr (by linarith)
        _ = Y := Real.exp_log hY0
    have hzero : ∑ n ∈ Finset.Icc 1 (X * N), (beta X N n : ℂ) *
        (if L ≤ n ∧ n < B then χ (n : ZMod q) * (((n : ℝ) ^ (-σ) : ℝ) : ℂ) else 0) = 0 := by
      refine Finset.sum_eq_zero fun n _ => ?_
      have : ¬ (L ≤ n ∧ n < B) := fun h' => by
        have := le_trans (le_max_left _ _) h'.1; omega
      rw [if_neg this, mul_zero]
    rw [hzero, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact mul_nonneg (sq_nonneg _) (tailDom_nonneg _ _ _ _)
  · push Not at hcase
    have hsq : ‖∑ n ∈ Finset.Icc 1 (X * N), (beta X N n : ℂ) *
        (if L ≤ n ∧ n < B then χ (n : ZMod q) * (((n : ℝ) ^ (-σ) : ℝ) : ℂ) else 0)‖ ^ 2 ≤
        (X * PV q) ^ 2 * ((L : ℝ) ^ (-σ)) ^ 2 := by
      rw [mul_pow]
      have h0 : 0 ≤ (X : ℝ) * PV q * (L : ℝ) ^ (-σ) := by positivity
      calc _ ≤ ((X : ℝ) * PV q * (L : ℝ) ^ (-σ)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hbd 2
        _ = _ := by ring
    refine hsq.trans (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _))
    have hLsq : ((L : ℝ) ^ (-σ)) ^ 2 = (L : ℝ) ^ (-(2 * σ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]; congr 1; push_cast; ring
    rw [hLsq]
    unfold tailDom
    by_cases hu : u ≤ Real.log Y
    · have hmem : u ∈ Set.Ioc (Real.log Y - h) (Real.log Y) := ⟨hcase, hu⟩
      have hnot : u ∉ Set.Ioi (Real.log Y) := by simp [hu]
      rw [Set.indicator_of_mem hmem, Set.indicator_of_notMem hnot, Pi.one_apply, mul_one, add_zero]
      have hYL : (Y : ℝ) ≤ L := by
        have : Y ≤ L := le_trans (by omega) (le_max_left _ _)
        exact_mod_cast this
      exact Real.rpow_le_rpow_of_nonpos hY0 hYL (by linarith)
    · push Not at hu
      have hnot : u ∉ Set.Ioc (Real.log Y - h) (Real.log Y) := by simp [not_le.mpr hu]
      have hmem : u ∈ Set.Ioi (Real.log Y) := hu
      rw [Set.indicator_of_mem hmem, Set.indicator_of_notMem hnot, mul_zero, zero_add]
      have hAL : Real.exp u ≤ L := by
        have : A ≤ L := le_max_right _ _
        exact (Nat.le_ceil _).trans (by exact_mod_cast this)
      calc (L : ℝ) ^ (-(2 * σ)) ≤ (Real.exp u) ^ (-(2 * σ)) :=
            Real.rpow_le_rpow_of_nonpos (Real.exp_pos u) hAL (by linarith)
        _ = Real.exp (-(2 * σ) * u) := by
            rw [← Real.exp_mul]; ring_nf

/-- **The tail per character**: `∫_{−W}^{W} |D^{>Y}(σ+iv)|² dv ≤ 5 W² X² PV(q)² Y^{−2σ}`. -/
theorem tail_char_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : 2 ≤ q) {σ : ℝ} (hσ : 1 / 2 ≤ σ) {W : ℝ} (hW : 2 ≤ W) (X N Y : ℕ) (hY : 1 ≤ Y) :
    ∫ v in (-W)..W, ‖∑ n ∈ Finset.Ioc Y (X * N), (beta X N n : ℂ) *
        (χ (n : ZMod q) * (n : ℂ) ^ (-((σ : ℂ) + (v : ℂ) * Complex.I)))‖ ^ 2
      ≤ 5 * W ^ 2 * (X * PV q) ^ 2 * (Y : ℝ) ^ (-(2 * σ)) := by
  have hW0 : 0 < W := by linarith
  have hσ0 : 0 < σ := by linarith
  have hS : ∀ n ∈ Finset.Ioc Y (X * N), 1 ≤ n := fun n hn => by
    have := (Finset.mem_Ioc.mp hn).1; omega
  simp_rw [dirichlet_eq_exsum χ _ hS]
  refine (gallagher _ _ _ hW0).trans ?_
  have hh : (0 : ℝ) ≤ 2 / W := by positivity
  have hmono := integral_mono (integrable_winSum_sq (2 / W) (Finset.Ioc Y (X * N)) _ _)
    ((integrable_tailDom Y (2 / W) hσ0).const_mul ((X * PV q) ^ 2))
    (fun u => tail_window_le χ hχ hq hσ0 hh X N Y hY u)
  rw [integral_const_mul, integral_tailDom hY hh hσ0] at hmono
  have hπ : π < 3.15 := Real.pi_lt_d2
  have h1 : 2 / W + 1 / (2 * σ) ≤ 2 := by
    have : 2 / W ≤ 1 := by rw [div_le_one hW0]; linarith
    have : 1 / (2 * σ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hYp : 0 ≤ (Y : ℝ) ^ (-(2 * σ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hXP : 0 ≤ ((X : ℝ) * PV q) ^ 2 := sq_nonneg _
  calc 3 * π / 4 * W ^ 2 * ∫ u : ℝ, ‖∑ n ∈ Finset.Ioc Y (X * N), (win (2 / W) u (Real.log n) : ℂ) *
        ((beta X N n : ℂ) * χ (n : ZMod q) * (((n : ℝ) ^ (-σ) : ℝ) : ℂ))‖ ^ 2
      ≤ 3 * π / 4 * W ^ 2 * (((X : ℝ) * PV q) ^ 2 * ((Y : ℝ) ^ (-(2 * σ)) *
          (2 / W + 1 / (2 * σ)))) := mul_le_mul_of_nonneg_left hmono (by positivity)
    _ ≤ 3 * 3.15 / 4 * W ^ 2 * (((X : ℝ) * PV q) ^ 2 * ((Y : ℝ) ^ (-(2 * σ)) * 2)) := by
        gcongr
    _ ≤ 5 * W ^ 2 * (X * PV q) ^ 2 * (Y : ℝ) ^ (-(2 * σ)) := by
        have : 0 ≤ W ^ 2 * (((X : ℝ) * PV q) ^ 2 * (Y : ℝ) ^ (-(2 * σ))) := by positivity
        nlinarith

/-! ### The head `D^{≤Y}` (hybrid large sieve) -/

lemma beta_sq_le (X N n : ℕ) : ((beta X N n : ℝ)) ^ 2 ≤ ((n.divisors.card : ℝ)) ^ 2 := by
  have := abs_beta_le X N n
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) this 2

/-- `∑_{X < n ≤ Y} d(n)² n^{−2σ} ≤ X^{−δ/2} (1 + 2/δ)⁴` for `2σ ≥ 1 + δ`. -/
lemma head_sum_one {X Y : ℕ} (hX : 1 ≤ X) {δ σ : ℝ} (hδ : 0 < δ) (hσ : 1 + δ ≤ 2 * σ) :
    ∑ n ∈ Finset.Ioc X Y, ((n.divisors.card : ℝ)) ^ 2 * (n : ℝ) ^ (-(2 * σ)) ≤
      (X : ℝ) ^ (-(δ / 2)) * (1 + 2 / δ) ^ 4 := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hsub : Finset.Ioc X Y ⊆ Finset.Icc 1 Y := by
    intro n hn; simp only [Finset.mem_Ioc, Finset.mem_Icc] at hn ⊢; omega
  have hmain := sum_card_divisors_sq_le Y (η := δ / 2) (by linarith)
  have e2 : (1 + 1 / (δ / 2)) = 1 + 2 / δ := by field_simp
  rw [e2] at hmain
  calc ∑ n ∈ Finset.Ioc X Y, ((n.divisors.card : ℝ)) ^ 2 * (n : ℝ) ^ (-(2 * σ))
      ≤ ∑ n ∈ Finset.Ioc X Y, (X : ℝ) ^ (-(δ / 2)) *
          (((n.divisors.card : ℝ)) ^ 2 * (n : ℝ) ^ (-(1 + δ / 2))) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn' := Finset.mem_Ioc.mp hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        have hXn : (X : ℝ) ≤ n := by exact_mod_cast hn'.1.le
        have h1 : (n : ℝ) ^ (-(2 * σ)) ≤ (n : ℝ) ^ (-(δ / 2)) * (n : ℝ) ^ (-(1 + δ / 2)) := by
          rw [← Real.rpow_add hn0]
          exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ n))
            (by linarith)
        have h2 : (n : ℝ) ^ (-(δ / 2)) ≤ (X : ℝ) ^ (-(δ / 2)) :=
          Real.rpow_le_rpow_of_nonpos hX0 hXn (by linarith)
        have h3 : 0 ≤ ((n.divisors.card : ℝ)) ^ 2 := sq_nonneg _
        have h4 : 0 ≤ (n : ℝ) ^ (-(1 + δ / 2)) := Real.rpow_nonneg hn0.le _
        calc ((n.divisors.card : ℝ)) ^ 2 * (n : ℝ) ^ (-(2 * σ))
            ≤ ((n.divisors.card : ℝ)) ^ 2 * ((n : ℝ) ^ (-(δ / 2)) * (n : ℝ) ^ (-(1 + δ / 2))) :=
              mul_le_mul_of_nonneg_left h1 h3
          _ ≤ ((n.divisors.card : ℝ)) ^ 2 * ((X : ℝ) ^ (-(δ / 2)) * (n : ℝ) ^ (-(1 + δ / 2))) := by
              gcongr
          _ = _ := by ring
    _ = (X : ℝ) ^ (-(δ / 2)) * ∑ n ∈ Finset.Ioc X Y,
          ((n.divisors.card : ℝ)) ^ 2 * (n : ℝ) ^ (-(1 + δ / 2)) := by rw [Finset.mul_sum]
    _ ≤ (X : ℝ) ^ (-(δ / 2)) * (1 + 2 / δ) ^ 4 := by
        refine mul_le_mul_of_nonneg_left ((Finset.sum_le_sum_of_subset_of_nonneg hsub
          fun n _ _ => ?_).trans hmain) (Real.rpow_nonneg hX0.le _)
        exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- `∑_{X < n ≤ Y} d(n)² n^{1−2σ} ≤ Y^{1−δ/2} (1 + 2/δ)⁴` for `2σ ≥ 1 + δ`, `δ ≤ 2`. -/
lemma head_sum_two {X Y : ℕ} {δ σ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 2) (hσ : 1 + δ ≤ 2 * σ) :
    ∑ n ∈ Finset.Ioc X Y, ((n.divisors.card : ℝ)) ^ 2 * ((n : ℝ) * (n : ℝ) ^ (-(2 * σ))) ≤
      (Y : ℝ) ^ (1 - δ / 2) * (1 + 2 / δ) ^ 4 := by
  have hsub : Finset.Ioc X Y ⊆ Finset.Icc 1 Y := by
    intro n hn; simp only [Finset.mem_Ioc, Finset.mem_Icc] at hn ⊢; omega
  have hmain := sum_card_divisors_sq_le Y (η := δ / 2) (by linarith)
  have e2 : (1 + 1 / (δ / 2)) = 1 + 2 / δ := by field_simp
  rw [e2] at hmain
  calc ∑ n ∈ Finset.Ioc X Y, ((n.divisors.card : ℝ)) ^ 2 * ((n : ℝ) * (n : ℝ) ^ (-(2 * σ)))
      ≤ ∑ n ∈ Finset.Ioc X Y, (Y : ℝ) ^ (1 - δ / 2) *
          (((n.divisors.card : ℝ)) ^ 2 * (n : ℝ) ^ (-(1 + δ / 2))) := by
        refine Finset.sum_le_sum fun n hn => ?_
        have hn' := Finset.mem_Ioc.mp hn
        have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
        have hn0 : (0 : ℝ) < n := by linarith
        have hnY : (n : ℝ) ≤ Y := by exact_mod_cast hn'.2
        have h1 : (n : ℝ) * (n : ℝ) ^ (-(2 * σ)) ≤ (n : ℝ) ^ (1 - δ / 2) * (n : ℝ) ^ (-(1 + δ / 2)) := by
          rw [← Real.rpow_add hn0]
          calc (n : ℝ) * (n : ℝ) ^ (-(2 * σ)) = (n : ℝ) ^ (1 + -(2 * σ)) := by
                rw [Real.rpow_add hn0, Real.rpow_one]
            _ ≤ (n : ℝ) ^ (1 - δ / 2 + -(1 + δ / 2)) :=
                Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
        have h2 : (n : ℝ) ^ (1 - δ / 2) ≤ (Y : ℝ) ^ (1 - δ / 2) :=
          Real.rpow_le_rpow hn0.le hnY (by linarith)
        have h3 : 0 ≤ ((n.divisors.card : ℝ)) ^ 2 := sq_nonneg _
        have h4 : 0 ≤ (n : ℝ) ^ (-(1 + δ / 2)) := Real.rpow_nonneg hn0.le _
        calc ((n.divisors.card : ℝ)) ^ 2 * ((n : ℝ) * (n : ℝ) ^ (-(2 * σ)))
            ≤ ((n.divisors.card : ℝ)) ^ 2 * ((n : ℝ) ^ (1 - δ / 2) * (n : ℝ) ^ (-(1 + δ / 2))) :=
              mul_le_mul_of_nonneg_left h1 h3
          _ ≤ ((n.divisors.card : ℝ)) ^ 2 * ((Y : ℝ) ^ (1 - δ / 2) * (n : ℝ) ^ (-(1 + δ / 2))) := by
              gcongr
          _ = _ := by ring
    _ = (Y : ℝ) ^ (1 - δ / 2) * ∑ n ∈ Finset.Ioc X Y,
          ((n.divisors.card : ℝ)) ^ 2 * (n : ℝ) ^ (-(1 + δ / 2)) := by rw [Finset.mul_sum]
    _ ≤ (Y : ℝ) ^ (1 - δ / 2) * (1 + 2 / δ) ^ 4 := by
        refine mul_le_mul_of_nonneg_left ((Finset.sum_le_sum_of_subset_of_nonneg hsub
          fun n _ _ => ?_).trans hmain) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- **The head over the family** (hybrid large sieve). -/
theorem head_family_bound (Q : ℝ) (hQ : 1 ≤ Q) {W : ℝ} (hW : 2 ≤ W) {δ σ : ℝ} (hδ : 0 < δ)
    (hδ2 : δ ≤ 2) (hσ : 1 + δ ≤ 2 * σ) {X N Y : ℕ} (hX : 1 ≤ X) :
    ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ ∈ primChars q, ∫ v in (-W)..W,
        ‖∑ n ∈ Finset.Ioc X Y, (beta X N n : ℂ) *
          (χ (n : ZMod q) * (n : ℂ) ^ (-((σ : ℂ) + (v : ℂ) * Complex.I)))‖ ^ 2
      ≤ 100 * (1 + 2 / δ) ^ 4 * (2 * W * Q ^ 2 * (X : ℝ) ^ (-(δ / 2)) + (Y : ℝ) ^ (1 - δ / 2)) := by
  have hS : ∀ n ∈ Finset.Ioc X Y, 1 ≤ n := fun n hn => by
    have := (Finset.mem_Ioc.mp hn).1; omega
  have hrw : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (v : ℝ),
      ∑ n ∈ Finset.Ioc X Y, (beta X N n : ℂ) *
          (χ (n : ZMod q) * (n : ℂ) ^ (-((σ : ℂ) + (v : ℂ) * Complex.I))) =
        ∑ n ∈ Finset.Ioc X Y, ((beta X N n : ℂ) * (((n : ℝ) ^ (-σ) : ℝ) : ℂ)) *
          χ (n : ZMod q) * ex v (Real.log n) := by
    intro q χ v
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [natCast_cpow_eq_ex n (hS n hn)]; ring
  simp_rw [hrw]
  refine (hybrid_large_sieve Q hQ hW _ hS _).trans ?_
  have hterm : ∀ n ∈ Finset.Ioc X Y,
      ‖(beta X N n : ℂ) * (((n : ℝ) ^ (-σ) : ℝ) : ℂ)‖ ^ 2 * (W * (Q ^ 2 + 1) + n) ≤
        2 * W * Q ^ 2 * (((n.divisors.card : ℝ)) ^ 2 * (n : ℝ) ^ (-(2 * σ))) +
          ((n.divisors.card : ℝ)) ^ 2 * ((n : ℝ) * (n : ℝ) ^ (-(2 * σ))) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by have := hS n hn; omega : 0 < n)
    rw [norm_mul, Complex.norm_intCast, Complex.norm_real, mul_pow, sq_abs,
      Real.norm_of_nonneg (Real.rpow_nonneg hn0.le _)]
    have hsq : ((n : ℝ) ^ (-σ)) ^ 2 = (n : ℝ) ^ (-(2 * σ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]; congr 1; push_cast; ring
    rw [hsq]
    have hb := beta_sq_le X N n
    have hp : 0 ≤ (n : ℝ) ^ (-(2 * σ)) := Real.rpow_nonneg hn0.le _
    have hQ2 : W * (Q ^ 2 + 1) ≤ 2 * W * Q ^ 2 := by
      have h1 : 1 ≤ Q ^ 2 := by nlinarith
      have h2 : W * 1 ≤ W * Q ^ 2 := mul_le_mul_of_nonneg_left h1 (by linarith)
      nlinarith
    have hA : 0 ≤ W * (Q ^ 2 + 1) + n := by positivity
    calc ((beta X N n : ℝ)) ^ 2 * (n : ℝ) ^ (-(2 * σ)) * (W * (Q ^ 2 + 1) + n)
        ≤ ((n.divisors.card : ℝ)) ^ 2 * (n : ℝ) ^ (-(2 * σ)) * (2 * W * Q ^ 2 + n) := by
          gcongr
      _ = _ := by ring
  calc 100 * ∑ n ∈ Finset.Ioc X Y,
        ‖(beta X N n : ℂ) * (((n : ℝ) ^ (-σ) : ℝ) : ℂ)‖ ^ 2 * (W * (Q ^ 2 + 1) + n)
      ≤ 100 * ∑ n ∈ Finset.Ioc X Y, (2 * W * Q ^ 2 * (((n.divisors.card : ℝ)) ^ 2 *
          (n : ℝ) ^ (-(2 * σ))) + ((n.divisors.card : ℝ)) ^ 2 * ((n : ℝ) * (n : ℝ) ^ (-(2 * σ)))) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by norm_num)
    _ = 100 * (2 * W * Q ^ 2 * ∑ n ∈ Finset.Ioc X Y, ((n.divisors.card : ℝ)) ^ 2 *
          (n : ℝ) ^ (-(2 * σ)) + ∑ n ∈ Finset.Ioc X Y, ((n.divisors.card : ℝ)) ^ 2 *
          ((n : ℝ) * (n : ℝ) ^ (-(2 * σ)))) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ 100 * (2 * W * Q ^ 2 * ((X : ℝ) ^ (-(δ / 2)) * (1 + 2 / δ) ^ 4) +
          (Y : ℝ) ^ (1 - δ / 2) * (1 + 2 / δ) ^ 4) := by
        gcongr
        · exact head_sum_one hX hδ hσ
        · exact head_sum_two hδ hδ2 hσ
    _ = _ := by ring

/-! ### One character -/

lemma continuous_dsum {q : ℕ} (χ : DirichletCharacter ℂ q) (S : Finset ℕ) (hS : ∀ n ∈ S, 1 ≤ n)
    (c : ℕ → ℂ) (σ : ℝ) :
    Continuous (fun v : ℝ => ∑ n ∈ S, c n *
      (χ (n : ZMod q) * (n : ℂ) ^ (-((σ : ℂ) + (v : ℂ) * Complex.I)))) := by
  refine continuous_finsetSum _ fun n hn => continuous_const.mul (continuous_const.mul ?_)
  have hn0 : (n : ℂ) ≠ 0 := by have := hS n hn; exact_mod_cast (by omega : n ≠ 0)
  exact Continuous.const_cpow (by fun_prop) (Or.inl hn0)

/-- The remainder `(L − P_N) M_X` on the line. -/
lemma norm_rem_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1) {σ v W : ℝ}
    (hσ : 1 / 2 ≤ σ) (hv : |v| ≤ W) (X N : ℕ) (hN : 1 ≤ N) :
    ‖(χ.LFunction ((σ : ℂ) + (v : ℂ) * Complex.I) - Psum N χ ((σ : ℂ) + (v : ℂ) * Complex.I)) *
        Mol X χ ((σ : ℂ) + (v : ℂ) * Complex.I)‖ ≤ q * (2 + 2 * W) * X * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
  set s : ℂ := (σ : ℂ) + (v : ℂ) * Complex.I with hs
  have hsre : s.re = σ := by simp [hs]
  have hσ0 : 0 < σ := by linarith
  have h1 := norm_LFunction_sub_partial_le χ hχ1 (s := s) (by rw [hsre]; exact hσ0) N hN
  have h2 := norm_Mol_le X χ (s := s) (by rw [hsre]; exact hσ0.le)
  rw [hsre] at h1
  have hsn : ‖s‖ ≤ σ + W := by
    calc ‖s‖ ≤ ‖(σ : ℂ)‖ + ‖(v : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = σ + |v| := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
            Real.norm_of_nonneg hσ0.le, Real.norm_eq_abs]
      _ ≤ σ + W := by linarith
  have hW0 : 0 ≤ W := (abs_nonneg v).trans hv
  have h3 : 1 + ‖s‖ / σ ≤ 2 + 2 * W := by
    have : ‖s‖ / σ ≤ 1 + 2 * W := by
      rw [div_le_iff₀ hσ0]; nlinarith [abs_nonneg v]
    linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h4 : (N : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  rw [norm_mul]
  calc ‖χ.LFunction s - Psum N χ s‖ * ‖Mol X χ s‖
      ≤ (q * (1 + ‖s‖ / σ) * (N : ℝ) ^ (-σ)) * X := by
        refine mul_le_mul ?_ h2 (norm_nonneg _) (by positivity)
        simpa [Psum] using h1
    _ ≤ (q * (2 + 2 * W) * (N : ℝ) ^ (-(1 / 2 : ℝ))) * X := by
        have hp : 0 ≤ (N : ℝ) ^ (-σ) := Real.rpow_nonneg (by linarith) _
        have h5 : (q : ℝ) * (1 + ‖s‖ / σ) ≤ q * (2 + 2 * W) := mul_le_mul_of_nonneg_left h3 hq0
        have h6 : 0 ≤ (q : ℝ) * (2 + 2 * W) := by positivity
        have h7 := mul_le_mul h5 h4 hp h6
        exact mul_le_mul_of_nonneg_right h7 (Nat.cast_nonneg _)
    _ = _ := by ring

/-- `‖a + b + c‖² ≤ 3(‖a‖² + ‖b‖² + ‖c‖²)`. -/
lemma norm_add3_sq_le (a b c : ℂ) : ‖a + b + c‖ ^ 2 ≤ 3 * ‖a‖ ^ 2 + 3 * ‖b‖ ^ 2 + 3 * ‖c‖ ^ 2 := by
  have h := norm_add_le (a + b) c
  have h' := norm_add_le a b
  have ha := norm_nonneg a; have hb := norm_nonneg b; have hc := norm_nonneg c
  have : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ := by linarith
  have h0 : 0 ≤ ‖a + b + c‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖b‖ - ‖c‖), sq_nonneg (‖a‖ - ‖c‖)]

/-- **One character**: the mean square of `L M_X − 1` splits into head, tail and remainder. -/
theorem char_mean_square {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ1 : χ ≠ 1)
    {σ W : ℝ} (hσ : 1 / 2 ≤ σ) (hW : 2 ≤ W) {X N Y : ℕ} (hX : 1 ≤ X) (hXN : X ≤ N)
    (hXY : X ≤ Y) (hYN : Y ≤ X * N) :
    ∫ v in (-W)..W, ‖χ.LFunction ((σ : ℂ) + (v : ℂ) * Complex.I) *
        Mol X χ ((σ : ℂ) + (v : ℂ) * Complex.I) - 1‖ ^ 2
      ≤ 3 * (∫ v in (-W)..W, ‖∑ n ∈ Finset.Ioc X Y, (beta X N n : ℂ) *
          (χ (n : ZMod q) * (n : ℂ) ^ (-((σ : ℂ) + (v : ℂ) * Complex.I)))‖ ^ 2)
        + 3 * (∫ v in (-W)..W, ‖∑ n ∈ Finset.Ioc Y (X * N), (beta X N n : ℂ) *
          (χ (n : ZMod q) * (n : ℂ) ^ (-((σ : ℂ) + (v : ℂ) * Complex.I)))‖ ^ 2)
        + 3 * (2 * W * (q * (2 + 2 * W) * X * (N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2) := by
  have hW0 : 0 < W := by linarith
  have hN : 1 ≤ N := hX.trans hXN
  have hS1 : ∀ n ∈ Finset.Ioc X Y, 1 ≤ n := fun n hn => by
    have := (Finset.mem_Ioc.mp hn).1; omega
  have hS2 : ∀ n ∈ Finset.Ioc Y (X * N), 1 ≤ n := fun n hn => by
    have := (Finset.mem_Ioc.mp hn).1; omega
  set c : ℝ := q * (2 + 2 * W) * X * (N : ℝ) ^ (-(1 / 2 : ℝ)) with hc
  have hC1 := continuous_dsum χ (Finset.Ioc X Y) hS1 (fun n => (beta X N n : ℂ)) σ
  have hC2 := continuous_dsum χ (Finset.Ioc Y (X * N)) hS2 (fun n => (beta X N n : ℂ)) σ
  have hL : Continuous (fun v : ℝ => χ.LFunction ((σ : ℂ) + (v : ℂ) * Complex.I) *
      Mol X χ ((σ : ℂ) + (v : ℂ) * Complex.I) - 1) := by
    have h1 : Continuous (fun v : ℝ => (σ : ℂ) + (v : ℂ) * Complex.I) := by fun_prop
    exact (((DirichletCharacter.differentiable_LFunction hχ1).continuous.comp h1).mul
      ((differentiable_Mol X χ).continuous.comp h1)).sub continuous_const
  have hLc : Continuous (fun v : ℝ => ‖χ.LFunction ((σ : ℂ) + (v : ℂ) * Complex.I) *
      Mol X χ ((σ : ℂ) + (v : ℂ) * Complex.I) - 1‖ ^ 2) := hL.norm.pow 2
  have hpt : ∀ v ∈ Set.Icc (-W) W, ‖χ.LFunction ((σ : ℂ) + (v : ℂ) * Complex.I) *
        Mol X χ ((σ : ℂ) + (v : ℂ) * Complex.I) - 1‖ ^ 2 ≤
      3 * ‖∑ n ∈ Finset.Ioc X Y, (beta X N n : ℂ) *
          (χ (n : ZMod q) * (n : ℂ) ^ (-((σ : ℂ) + (v : ℂ) * Complex.I)))‖ ^ 2 +
      3 * ‖∑ n ∈ Finset.Ioc Y (X * N), (beta X N n : ℂ) *
          (χ (n : ZMod q) * (n : ℂ) ^ (-((σ : ℂ) + (v : ℂ) * Complex.I)))‖ ^ 2 + 3 * c ^ 2 := by
    intro v hv
    have hv' : |v| ≤ W := abs_le.mpr ⟨hv.1, hv.2⟩
    rw [LM_decomp χ _ hX hXN hXY hYN]
    refine (norm_add3_sq_le _ _ _).trans ?_
    have hr := norm_rem_le χ hχ1 hσ hv' X N hN
    have : ‖(χ.LFunction ((σ : ℂ) + (v : ℂ) * Complex.I) -
        Psum N χ ((σ : ℂ) + (v : ℂ) * Complex.I)) * Mol X χ ((σ : ℂ) + (v : ℂ) * Complex.I)‖ ^ 2
        ≤ c ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hr 2
    linarith
  have hint1 : IntervalIntegrable (fun v : ℝ => 3 * ‖∑ n ∈ Finset.Ioc X Y, (beta X N n : ℂ) *
      (χ (n : ZMod q) * (n : ℂ) ^ (-((σ : ℂ) + (v : ℂ) * Complex.I)))‖ ^ 2) volume (-W) W :=
    (continuous_const.mul (hC1.norm.pow 2)).intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun v : ℝ => 3 * ‖∑ n ∈ Finset.Ioc Y (X * N), (beta X N n : ℂ) *
      (χ (n : ZMod q) * (n : ℂ) ^ (-((σ : ℂ) + (v : ℂ) * Complex.I)))‖ ^ 2) volume (-W) W :=
    (continuous_const.mul (hC2.norm.pow 2)).intervalIntegrable _ _
  refine (intervalIntegral.integral_mono_on (by linarith) (hLc.intervalIntegrable _ _)
    ((hint1.add hint2).add intervalIntegrable_const) hpt).trans (le_of_eq ?_)
  have hconst : IntervalIntegrable (fun _ : ℝ => (3 * c ^ 2 : ℝ)) volume (-W) W :=
    intervalIntegrable_const
  have e1 := intervalIntegral.integral_add (hint1.add hint2) hconst
  have e2 := intervalIntegral.integral_add hint1 hint2
  have e3 : ∫ v in (-W)..W, 3 * ‖∑ n ∈ Finset.Ioc X Y, (beta X N n : ℂ) *
      (χ (n : ZMod q) * (n : ℂ) ^ (-((σ : ℂ) + (v : ℂ) * Complex.I)))‖ ^ 2 =
      3 * ∫ v in (-W)..W, ‖∑ n ∈ Finset.Ioc X Y, (beta X N n : ℂ) *
      (χ (n : ZMod q) * (n : ℂ) ^ (-((σ : ℂ) + (v : ℂ) * Complex.I)))‖ ^ 2 :=
    intervalIntegral.integral_const_mul _ _
  have e4 : ∫ v in (-W)..W, 3 * ‖∑ n ∈ Finset.Ioc Y (X * N), (beta X N n : ℂ) *
      (χ (n : ZMod q) * (n : ℂ) ^ (-((σ : ℂ) + (v : ℂ) * Complex.I)))‖ ^ 2 =
      3 * ∫ v in (-W)..W, ‖∑ n ∈ Finset.Ioc Y (X * N), (beta X N n : ℂ) *
      (χ (n : ZMod q) * (n : ℂ) ^ (-((σ : ℂ) + (v : ℂ) * Complex.I)))‖ ^ 2 :=
    intervalIntegral.integral_const_mul _ _
  have e5 : ∫ _ in (-W)..W, (3 * c ^ 2 : ℝ) = (W - -W) * (3 * c ^ 2) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
  -- (no beta-reduction needed)
  rw [e1, e2, e3, e4, e5]
  ring

/-! ### The family -/

lemma card_primChars_le' (q : ℕ) [NeZero q] : ((primChars q).card : ℝ) ≤ q := by
  have h1 : (primChars q).card ≤ Fintype.card (DirichletCharacter ℂ q) :=
    Finset.card_le_univ _
  have h2 : Fintype.card (DirichletCharacter ℂ q) = Nat.totient q := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have h3 : Nat.totient q ≤ q := Nat.totient_le q
  exact_mod_cast h1.trans (h2 ▸ h3)

lemma sum_card_primChars_le {Q : ℝ} (hQ : 1 ≤ Q) :
    ∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, ((primChars q).card : ℝ) ≤ Q ^ 2 := by
  have hM : ((⌊Q⌋₊ : ℕ) : ℝ) ≤ Q := Nat.floor_le (by linarith)
  calc ∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, ((primChars q).card : ℝ)
      ≤ ∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, (⌊Q⌋₊ : ℝ) := by
        refine Finset.sum_le_sum fun q hq => ?_
        have hq' := Finset.mem_Icc.mp hq
        haveI : NeZero q := ⟨by omega⟩
        exact (card_primChars_le' q).trans (by exact_mod_cast hq'.2)
    _ ≤ (⌊Q⌋₊ : ℝ) * ⌊Q⌋₊ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
        have : (Finset.Icc 2 ⌊Q⌋₊).card ≤ ⌊Q⌋₊ := by simp
        exact_mod_cast this
    _ ≤ Q ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) ⌊Q⌋₊]

lemma PV_le {q : ℕ} {Q : ℝ} (hq : (q : ℝ) ≤ Q) (hq1 : 1 ≤ q) :
    PV q ≤ 2 * Real.sqrt Q * (1 + Real.log Q) := by
  unfold PV
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have h1 : Real.sqrt q ≤ Real.sqrt Q := Real.sqrt_le_sqrt hq
  have h2 : Real.log q ≤ Real.log Q := Real.log_le_log hq0 hq
  have h3 : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have h4 : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
  gcongr

/-- The final real-arithmetic step of `family_mean_square`. -/
lemma family_final {Q W δ σ : ℝ} {X Y : ℕ} (hQ : 1 ≤ Q) (hW : 2 ≤ W) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (h2σ : 1 + δ ≤ 2 * σ) (hX0 : (0 : ℝ) < X) (hX2 : (X : ℝ) ^ 2 ≤ Q)
    (hXge : Real.sqrt Q / 2 ≤ X) (hQW1 : 1 ≤ Q ^ 2 * W) (hYge : Q ^ 2 * W ≤ Y)
    (hYle : (Y : ℝ) ≤ 2 * (Q ^ 2 * W)) {A B C : ℝ}
    (hA : A ≤ 100 * (1 + 2 / δ) ^ 4 * (2 * W * Q ^ 2 * (X : ℝ) ^ (-(δ / 2)) + (Y : ℝ) ^ (1 - δ / 2)))
    (hB : B ≤ Q ^ 2 * (5 * W ^ 2 * ((X : ℝ) ^ 2 * (4 * Q * (1 + Real.log Q) ^ 2)) *
        (Y : ℝ) ^ (-(2 * σ))))
    (hC : C ≤ 1) :
    3 * A + 3 * B + 3 * C ≤
      2000 * (1 + 2 / δ) ^ 4 * (1 + Real.log Q) ^ 2 * (Q ^ 2 * W) * Q ^ (-(δ / 4)) := by
  have hQ0 : 0 < Q := by linarith
  have hW0 : 0 < W := by linarith
  -- rpow facts
  have hQd : 0 < Q ^ (-(δ / 4)) := Real.rpow_pos_of_pos hQ0 _
  have hr1 : (X : ℝ) ^ (-(δ / 2)) ≤ 2 * Q ^ (-(δ / 4)) := by
    have hsq0 : 0 < Real.sqrt Q / 2 := by positivity
    calc (X : ℝ) ^ (-(δ / 2)) ≤ (Real.sqrt Q / 2) ^ (-(δ / 2)) :=
          Real.rpow_le_rpow_of_nonpos hsq0 hXge (by linarith)
      _ = Real.sqrt Q ^ (-(δ / 2)) * 2 ^ (δ / 2) := by
          rw [Real.div_rpow (Real.sqrt_nonneg _) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
          field_simp
      _ ≤ Q ^ (-(δ / 4)) * 2 := by
          have e : Real.sqrt Q ^ (-(δ / 2)) = Q ^ (-(δ / 4)) := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hQ0.le]; ring_nf
          rw [e]
          have : (2 : ℝ) ^ (δ / 2) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          rw [Real.rpow_one] at this
          exact mul_le_mul_of_nonneg_left this hQd.le
      _ = 2 * Q ^ (-(δ / 4)) := by ring
  have hQWd : (Q ^ 2 * W) ^ (-(δ / 2)) ≤ Q ^ (-(δ / 4)) := by
    have hQ4 : Q ^ (1 / 2 : ℝ) ≤ Q ^ 2 * W := by
      have : Q ^ (1 / 2 : ℝ) ≤ Q ^ (2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hQ (by norm_num)
      rw [Real.rpow_two] at this; nlinarith
    calc (Q ^ 2 * W) ^ (-(δ / 2)) ≤ (Q ^ (1 / 2 : ℝ)) ^ (-(δ / 2)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hQ4 (by linarith)
      _ = Q ^ (-(δ / 4)) := by rw [← Real.rpow_mul hQ0.le]; ring_nf
  have hr2 : (Y : ℝ) ^ (1 - δ / 2) ≤ 2 * (Q ^ 2 * W) * Q ^ (-(δ / 4)) := by
    have hY0 : (0 : ℝ) < Y := by linarith
    calc (Y : ℝ) ^ (1 - δ / 2) ≤ (2 * (Q ^ 2 * W)) ^ (1 - δ / 2) :=
          Real.rpow_le_rpow hY0.le hYle (by linarith)
      _ = (2 * (Q ^ 2 * W)) * (2 * (Q ^ 2 * W)) ^ (-(δ / 2)) := by
          rw [sub_eq_add_neg, Real.rpow_add (by positivity), Real.rpow_one]
      _ ≤ (2 * (Q ^ 2 * W)) * (Q ^ 2 * W) ^ (-(δ / 2)) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith)
            (by linarith)) (by positivity)
      _ ≤ 2 * (Q ^ 2 * W) * Q ^ (-(δ / 4)) := mul_le_mul_of_nonneg_left hQWd (by positivity)
  have hr3 : (Y : ℝ) ^ (-(2 * σ)) ≤ (Q ^ 2 * W)⁻¹ * Q ^ (-(δ / 4)) := by
    calc (Y : ℝ) ^ (-(2 * σ)) ≤ (Q ^ 2 * W) ^ (-(2 * σ)) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hYge (by linarith)
      _ ≤ (Q ^ 2 * W) ^ (-(1 + δ)) :=
          Real.rpow_le_rpow_of_exponent_le hQW1 (by linarith)
      _ = (Q ^ 2 * W)⁻¹ * (Q ^ 2 * W) ^ (-δ) := by
          rw [neg_add, Real.rpow_add (by positivity), Real.rpow_neg_one]
      _ ≤ (Q ^ 2 * W)⁻¹ * Q ^ (-(δ / 4)) := by
          gcongr
          calc (Q ^ 2 * W) ^ (-δ) ≤ (Q ^ 2 * W) ^ (-(δ / 2)) :=
                Real.rpow_le_rpow_of_exponent_le hQW1 (by linarith)
            _ ≤ Q ^ (-(δ / 4)) := hQWd
  -- final algebra
  have hδ2 : 0 < 2 / δ := by positivity
  have hD1 : 1 ≤ (1 + 2 / δ) ^ 4 := one_le_pow₀ (by linarith)
  have hL1 : 1 ≤ (1 + Real.log Q) ^ 2 := one_le_pow₀ (by linarith [Real.log_nonneg hQ])
  have hP : 0 < Q ^ 2 * W * Q ^ (-(δ / 4)) := by positivity
  have hone : 1 ≤ Q ^ 2 * W * Q ^ (-(δ / 4)) := by
    have : Q ^ (δ / 4) ≤ Q ^ 2 * W := by
      have h1 : Q ^ (δ / 4) ≤ Q ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hQ (by linarith)
      rw [Real.rpow_two] at h1; nlinarith
    rw [Real.rpow_neg hQ0.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hQ0 _), one_mul]
    exact this
  have hAf : 100 * (1 + 2 / δ) ^ 4 * (2 * W * Q ^ 2 * (X : ℝ) ^ (-(δ / 2)) + (Y : ℝ) ^ (1 - δ / 2))
      ≤ 600 * (1 + 2 / δ) ^ 4 * (Q ^ 2 * W * Q ^ (-(δ / 4))) := by
    have h1 : 2 * W * Q ^ 2 * (X : ℝ) ^ (-(δ / 2)) ≤ 2 * W * Q ^ 2 * (2 * Q ^ (-(δ / 4))) :=
      mul_le_mul_of_nonneg_left hr1 (by positivity)
    have hD0 : 0 ≤ (1 + 2 / δ) ^ 4 := by positivity
    nlinarith
  have hBf : Q ^ 2 * (5 * W ^ 2 * ((X : ℝ) ^ 2 * (4 * Q * (1 + Real.log Q) ^ 2)) *
        (Y : ℝ) ^ (-(2 * σ))) ≤ 20 * (1 + Real.log Q) ^ 2 * (Q ^ 2 * W * Q ^ (-(δ / 4))) := by
    have hL0 : 0 ≤ (1 + Real.log Q) ^ 2 := sq_nonneg _
    calc Q ^ 2 * (5 * W ^ 2 * ((X : ℝ) ^ 2 * (4 * Q * (1 + Real.log Q) ^ 2)) *
          (Y : ℝ) ^ (-(2 * σ)))
        ≤ Q ^ 2 * (5 * W ^ 2 * (Q * (4 * Q * (1 + Real.log Q) ^ 2)) *
          ((Q ^ 2 * W)⁻¹ * Q ^ (-(δ / 4)))) := by
          gcongr
      _ = 20 * (1 + Real.log Q) ^ 2 * (Q ^ 2 * W * Q ^ (-(δ / 4))) := by
          field_simp
          ring
  have hAll : 3 * (600 * (1 + 2 / δ) ^ 4 * (Q ^ 2 * W * Q ^ (-(δ / 4)))) +
      3 * (20 * (1 + Real.log Q) ^ 2 * (Q ^ 2 * W * Q ^ (-(δ / 4)))) + 3 * 1 ≤
      2000 * (1 + 2 / δ) ^ 4 * (1 + Real.log Q) ^ 2 * (Q ^ 2 * W) * Q ^ (-(δ / 4)) := by
    have e : 2000 * (1 + 2 / δ) ^ 4 * (1 + Real.log Q) ^ 2 * (Q ^ 2 * W) * Q ^ (-(δ / 4)) =
        2000 * ((1 + 2 / δ) ^ 4 * (1 + Real.log Q) ^ 2) * (Q ^ 2 * W * Q ^ (-(δ / 4))) := by ring
    rw [e]
    set D := (1 + 2 / δ) ^ 4 with hD
    set Lg := (1 + Real.log Q) ^ 2 with hLg
    set P := Q ^ 2 * W * Q ^ (-(δ / 4)) with hPdef
    have hDL : 1 ≤ D * Lg := one_le_mul_of_one_le_of_one_le hD1 hL1
    have hA' : D ≤ D * Lg := le_mul_of_one_le_right (by positivity) hL1
    have hB' : Lg ≤ D * Lg := le_mul_of_one_le_left (by positivity) hD1
    have h1 : D * P ≤ (D * Lg) * P := mul_le_mul_of_nonneg_right hA' hP.le
    have h2 : Lg * P ≤ (D * Lg) * P := mul_le_mul_of_nonneg_right hB' hP.le
    have h3 : 1 ≤ (D * Lg) * P := one_le_mul_of_one_le_of_one_le hDL hone
    have e2 : 3 * (600 * D * P) + 3 * (20 * Lg * P) + 3 * 1 =
        1800 * (D * P) + 60 * (Lg * P) + 3 := by ring
    rw [e2]
    linarith
  linarith


/-- **The mollified family mean square.** -/
theorem family_mean_square {Q W δ σ : ℝ} (hQ : 1 ≤ Q) (hW : 2 ≤ W) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (hσ : 1 / 2 + δ / 2 ≤ σ) :
    ∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, ∑ χ ∈ primChars q, ∫ v in (-W)..W,
        ‖Lfun χ ((σ : ℂ) + (v : ℂ) * Complex.I) *
          Mol ⌊Real.sqrt Q⌋₊ χ ((σ : ℂ) + (v : ℂ) * Complex.I) - 1‖ ^ 2
      ≤ 2000 * (1 + 2 / δ) ^ 4 * (1 + Real.log Q) ^ 2 * (Q ^ 2 * W) * Q ^ (-(δ / 4)) := by
  have hQ0 : 0 < Q := by linarith
  have hW0 : 0 < W := by linarith
  have hσ2 : 1 / 2 ≤ σ := by linarith
  have h2σ : 1 + δ ≤ 2 * σ := by linarith
  -- parameters
  set X : ℕ := ⌊Real.sqrt Q⌋₊ with hXdef
  have hsQ : 1 ≤ Real.sqrt Q := by rw [Real.one_le_sqrt]; exact hQ
  have hX1 : 1 ≤ X := Nat.le_floor (by exact_mod_cast hsQ)
  have hXle : (X : ℝ) ≤ Real.sqrt Q := Nat.floor_le (by linarith)
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX1
  have hX2 : (X : ℝ) ^ 2 ≤ Q := by
    calc (X : ℝ) ^ 2 ≤ Real.sqrt Q ^ 2 := pow_le_pow_left₀ hX0.le hXle 2
      _ = Q := Real.sq_sqrt hQ0.le
  have hXge : Real.sqrt Q / 2 ≤ X := by
    have := Nat.lt_floor_add_one (Real.sqrt Q)
    have h' : Real.sqrt Q < X + 1 := this
    have : (1 : ℝ) ≤ X := by exact_mod_cast hX1
    linarith
  set Y : ℕ := ⌈Q ^ 2 * W⌉₊ with hYdef
  have hQW1 : 1 ≤ Q ^ 2 * W := by nlinarith
  have hYge : Q ^ 2 * W ≤ Y := Nat.le_ceil _
  have hYle : (Y : ℝ) ≤ 2 * (Q ^ 2 * W) := by
    have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ Q ^ 2 * W)
    linarith
  have hY1 : 1 ≤ Y := by
    have : (1 : ℝ) ≤ Y := hQW1.trans hYge
    exact_mod_cast this
  have hXY : X ≤ Y := by
    have : (X : ℝ) ≤ Y := by
      have h1 : Real.sqrt Q ≤ Q := by
        rw [Real.sqrt_le_left (by linarith)]; nlinarith
      nlinarith
    exact_mod_cast this
  set N : ℕ := ⌈2 * W * Q ^ 4 * (2 + 2 * W) ^ 2 * (X : ℝ) ^ 2⌉₊ + Y with hNdef
  have hYN' : Y ≤ N := Nat.le_add_left _ _
  have hXN : X ≤ N := hXY.trans hYN'
  have hYN : Y ≤ X * N := hYN'.trans (Nat.le_mul_of_pos_left _ hX1)
  have hNge : 2 * W * Q ^ 4 * (2 + 2 * W) ^ 2 * (X : ℝ) ^ 2 ≤ N := by
    have := Nat.le_ceil (2 * W * Q ^ 4 * (2 + 2 * W) ^ 2 * (X : ℝ) ^ 2)
    have : ((⌈2 * W * Q ^ 4 * (2 + 2 * W) ^ 2 * (X : ℝ) ^ 2⌉₊ : ℕ) : ℝ) ≤ N := by
      rw [hNdef]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) Y]
    linarith
  have hN0 : (0 : ℝ) < N := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast (hX1.trans hXN)
    linarith
  -- per-character splitting
  set Hd : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ := fun q χ => ∫ v in (-W)..W,
      ‖∑ n ∈ Finset.Ioc X Y, (beta X N n : ℂ) *
        (χ (n : ZMod q) * (n : ℂ) ^ (-((σ : ℂ) + (v : ℂ) * Complex.I)))‖ ^ 2 with hHd
  set Tl : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ := fun q χ => ∫ v in (-W)..W,
      ‖∑ n ∈ Finset.Ioc Y (X * N), (beta X N n : ℂ) *
        (χ (n : ZMod q) * (n : ℂ) ^ (-((σ : ℂ) + (v : ℂ) * Complex.I)))‖ ^ 2 with hTl
  set Rc : ℕ → ℝ := fun q => 2 * W * (q * (2 + 2 * W) * X * (N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 with hRc
  have hchar : ∀ q ∈ Finset.Icc 2 ⌊Q⌋₊, ∀ χ ∈ primChars q, ∫ v in (-W)..W,
        ‖Lfun χ ((σ : ℂ) + (v : ℂ) * Complex.I) *
          Mol X χ ((σ : ℂ) + (v : ℂ) * Complex.I) - 1‖ ^ 2 ≤
        3 * Hd q χ + 3 * Tl q χ + 3 * Rc q := by
    intro q hq χ hχ
    have hq2 : 2 ≤ q := (Finset.mem_Icc.mp hq).1
    haveI : NeZero q := ⟨by omega⟩
    have hprim : χ.IsPrimitive := (mem_primChars.mp hχ)
    have hχ1 : χ ≠ 1 := Zeta23.ThmE.ne_one_of_primitive (by omega) hprim
    rw [Lfun_eq_LFunction]
    exact char_mean_square χ hχ1 hσ2 hW hX1 hXN hXY hYN
  have hnnH : ∀ q (χ : DirichletCharacter ℂ q), 0 ≤ Hd q χ := fun q χ =>
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => sq_nonneg _)
  -- (a) the head
  have hA : ∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, ∑ χ ∈ primChars q, Hd q χ ≤
      100 * (1 + 2 / δ) ^ 4 * (2 * W * Q ^ 2 * (X : ℝ) ^ (-(δ / 2)) + (Y : ℝ) ^ (1 - δ / 2)) := by
    refine le_trans ?_ (head_family_bound Q hQ hW hδ (by linarith) h2σ (N := N) (Y := Y) hX1)
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun q _ _ =>
      Finset.sum_nonneg fun χ _ => hnnH q χ
    intro q hq; simp only [Finset.mem_Icc] at hq ⊢; omega
  -- (b) the tail
  have hPVQ : ∀ q ∈ Finset.Icc 2 ⌊Q⌋₊, PV q ^ 2 ≤ 4 * Q * (1 + Real.log Q) ^ 2 := by
    intro q hq
    have hq' := Finset.mem_Icc.mp hq
    have hqQ : (q : ℝ) ≤ Q := (Nat.cast_le.mpr hq'.2).trans (Nat.floor_le hQ0.le)
    have h1 := PV_le hqQ (by omega)
    have h0 := PV_nonneg q
    have hL : 0 ≤ 1 + Real.log Q := by linarith [Real.log_nonneg hQ]
    calc PV q ^ 2 ≤ (2 * Real.sqrt Q * (1 + Real.log Q)) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = 4 * Real.sqrt Q ^ 2 * (1 + Real.log Q) ^ 2 := by ring
      _ = 4 * Q * (1 + Real.log Q) ^ 2 := by rw [Real.sq_sqrt hQ0.le]
  have hB : ∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, ∑ χ ∈ primChars q, Tl q χ ≤
      Q ^ 2 * (5 * W ^ 2 * ((X : ℝ) ^ 2 * (4 * Q * (1 + Real.log Q) ^ 2)) *
        (Y : ℝ) ^ (-(2 * σ))) := by
    calc ∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, ∑ χ ∈ primChars q, Tl q χ
        ≤ ∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, ((primChars q).card : ℝ) *
            (5 * W ^ 2 * ((X : ℝ) ^ 2 * (4 * Q * (1 + Real.log Q) ^ 2)) *
              (Y : ℝ) ^ (-(2 * σ))) := by
          refine Finset.sum_le_sum fun q hq => ?_
          have hq2 : 2 ≤ q := (Finset.mem_Icc.mp hq).1
          haveI : NeZero q := ⟨by omega⟩
          rw [← nsmul_eq_mul, ← Finset.sum_const]
          refine Finset.sum_le_sum fun χ hχ => ?_
          have hprim : χ.IsPrimitive := (mem_primChars.mp hχ)
          refine (tail_char_bound χ hprim hq2 hσ2 hW X N Y hY1).trans ?_
          have hYp : 0 ≤ (Y : ℝ) ^ (-(2 * σ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
          have := hPVQ q hq
          rw [mul_pow]
          gcongr
      _ = (∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, ((primChars q).card : ℝ)) *
            (5 * W ^ 2 * ((X : ℝ) ^ 2 * (4 * Q * (1 + Real.log Q) ^ 2)) *
              (Y : ℝ) ^ (-(2 * σ))) := by rw [Finset.sum_mul]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right (sum_card_primChars_le hQ) ?_
          have : 0 ≤ (Y : ℝ) ^ (-(2 * σ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
          positivity
  -- (c) the remainder
  have hC : ∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, ∑ χ ∈ primChars q, Rc q ≤ 1 := by
    have hRq : ∀ q ∈ Finset.Icc 2 ⌊Q⌋₊, Rc q ≤ 2 * W * (Q * (2 + 2 * W) * X) ^ 2 / N := by
      intro q hq
      have hq' := Finset.mem_Icc.mp hq
      have hqQ : (q : ℝ) ≤ Q := (Nat.cast_le.mpr hq'.2).trans (Nat.floor_le hQ0.le)
      have hNh : ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (N : ℝ)⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
        rw [Real.rpow_neg_one]
      have e : Rc q = 2 * W * ((q : ℝ) * (2 + 2 * W) * X) ^ 2 / N := by
        simp only [hRc]
        rw [mul_pow, hNh, div_eq_mul_inv]; ring
      rw [e]
      have : ((q : ℝ) * (2 + 2 * W) * X) ^ 2 ≤ (Q * (2 + 2 * W) * X) ^ 2 := by
        apply pow_le_pow_left₀ (by positivity)
        gcongr
      gcongr
    calc ∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, ∑ χ ∈ primChars q, Rc q
        ≤ ∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, ((primChars q).card : ℝ) *
            (2 * W * (Q * (2 + 2 * W) * X) ^ 2 / N) := by
          refine Finset.sum_le_sum fun q hq => ?_
          rw [Finset.sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_left (hRq q hq) (Nat.cast_nonneg _)
      _ = (∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, ((primChars q).card : ℝ)) *
            (2 * W * (Q * (2 + 2 * W) * X) ^ 2 / N) := by rw [Finset.sum_mul]
      _ ≤ Q ^ 2 * (2 * W * (Q * (2 + 2 * W) * X) ^ 2 / N) :=
          mul_le_mul_of_nonneg_right (sum_card_primChars_le hQ) (by positivity)
      _ ≤ 1 := by
          rw [mul_div_assoc', div_le_one hN0]
          calc Q ^ 2 * (2 * W * (Q * (2 + 2 * W) * X) ^ 2)
              = 2 * W * Q ^ 4 * (2 + 2 * W) ^ 2 * (X : ℝ) ^ 2 := by ring
            _ ≤ (N : ℝ) := hNge
  -- sum the three pieces
  have hsum : ∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, ∑ χ ∈ primChars q, ∫ v in (-W)..W,
        ‖Lfun χ ((σ : ℂ) + (v : ℂ) * Complex.I) *
          Mol X χ ((σ : ℂ) + (v : ℂ) * Complex.I) - 1‖ ^ 2 ≤
      3 * (∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, ∑ χ ∈ primChars q, Hd q χ) +
      3 * (∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, ∑ χ ∈ primChars q, Tl q χ) +
      3 * (∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, ∑ χ ∈ primChars q, Rc q) := by
    refine (Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun χ hχ => hchar q hq χ hχ).trans
      (le_of_eq ?_)
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine hsum.trans ?_
  exact family_final hQ hW hδ hδ' h2σ hX0 hX2 hXge hQW1 hYge hYle hA hB hC

end Families.Hyp.Montgomery
