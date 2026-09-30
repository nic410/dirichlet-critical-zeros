/-
**Step 4(b) of `prop:TIsharp`, levels `R_max < e ≤ Q`** (proof of Proposition 6.24,
`eqC:Ssharp`, display (6.16)).

For `(c, e) = 1` and `e` larger than every `R_j`, `|S_{x♯^s(u)}(c/e)| ≪_A Q^{−A}` uniformly in `u` and
`T ∈ heights`:
`S_{x♯^s(u)}(c/e) = ∫_J e^{itu} ∑_j ∑_{r ≤ R_j} (μ(r)/φ(r)) ∑_n G_{j,t,u}(n) c_r(n) e(nc/e) dt`
(`S_xs_eq`, `Sadd_aSharp_eq`) with `G_{j,t,u} = F_{j,t} · ρ((log · − u)/δ)` (`Gjtu`); the frequencies
`h/r + c/e = (he + cr)/(re)` are never integers because `r < e` and `(c,e) = 1`
(`sum_F_ramanujan_add_le`), so summation by parts (`sum_smooth_eA_rat_le`) with the symbol bound of
`G_{j,t,u}` (`Gjtu_deriv_bound`; `ρ` contributes a `comp_log` factor with `c = 1/δ = 4`) gives
`≪ N_j^{3/2 − Kε₃}` per block, exactly as in `lem:B1`.
-/
import Families.Phase3.C.TIsharpBasic

noncomputable section

open scoped BigOperators ContDiff Nat ArithmeticFunction.Moebius
open Set MeasureTheory ArithmeticFunction

namespace Families.Phase3.C

open Families

/-! ### Additive frequencies `h/r + c/e` -/

/-- `|∑_n F(n) c_r(n) e(nc/e)| ≤ φ(r)(b − a + K + 1) sup|F^{(K)}| (re/4)^K` for `1 ≤ r < e`,
`(c, e) = 1`. -/
theorem sum_F_ramanujan_add_le {r e c : ℕ} (hr : 0 < r) (hre : r < e) (hc : c ∈ reduced e)
    {F : ℝ → ℂ} {K : ℕ} (hF : ContDiff ℝ K F) {Mb : ℝ} (hM : ∀ y, ‖iteratedDeriv K F y‖ ≤ Mb)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hsupp : ∀ y, F y ≠ 0 → a ≤ y ∧ y ≤ b)
    (S : Finset ℕ) (hS : ∀ n : ℕ, F n ≠ 0 → n ∈ S) :
    ‖∑ n ∈ S, F n * ramanujan r n * eA (n * ((c : ℝ) / e))‖ ≤
      Nat.totient r * ((b - a + K + 1) * Mb * (((r * e : ℕ) : ℝ) / 4) ^ K) := by
  have he : 0 < e := by omega
  set M : ℕ := r * e with hMdef
  have hMpos : 0 < M := Nat.mul_pos hr he
  set m : ℕ → ℤ := fun h => (h : ℤ) * e + (c : ℤ) * r with hm
  have hexp : ∑ n ∈ S, F n * ramanujan r n * eA (n * ((c : ℝ) / e)) =
      ∑ h ∈ reduced r, ∑ n ∈ S, F n * eA (n * ((m h : ℝ) / (M : ℝ))) := by
    unfold ramanujan
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun n _ => ?_
    rw [mul_assoc, ← eA_add']
    congr 2
    have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
    have he' : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
    simp only [hm, hMdef]
    push_cast
    field_simp
  have hnd : ∀ h ∈ reduced r, ¬ ((M : ℕ) : ℤ) ∣ m h := by
    intro h _ hdiv
    have hc' : Nat.Coprime c e := (Finset.mem_filter.mp hc).2
    have h1 : (e : ℤ) ∣ m h := by
      refine Dvd.dvd.trans ?_ hdiv
      exact Int.natCast_dvd_natCast.mpr (Dvd.intro_left r rfl)
    have h2 : (e : ℤ) ∣ ((c * r : ℕ) : ℤ) := by
      have h3 : (e : ℤ) ∣ (h : ℤ) * e := Dvd.intro_left _ rfl
      have := (dvd_add_right h3).mp h1
      push_cast; exact this
    have h4 : e ∣ c * r := Int.natCast_dvd_natCast.mp h2
    have h5 : e ∣ r := Nat.Coprime.dvd_of_dvd_mul_left hc'.symm h4
    exact absurd (Nat.le_of_dvd hr h5) (by omega)
  rw [hexp]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ h ∈ reduced r, ‖∑ n ∈ S, F n * eA (n * ((m h : ℝ) / (M : ℝ)))‖
      ≤ ∑ h ∈ reduced r, (b - a + K + 1) * Mb * ((M : ℝ) / 4) ^ K :=
        Finset.sum_le_sum fun h hh =>
          sum_smooth_eA_rat_le hF hM ha hab hsupp S hS hMpos (hnd h hh)
    _ = Nat.totient r * ((b - a + K + 1) * Mb * (((r * e : ℕ) : ℝ) / 4) ^ K) := by
        rw [Finset.sum_const, card_reduced, nsmul_eq_mul]

variable (P : PrimeSetup)

/-! ### The weights `G_{j,t,u}` -/

/-- `ρ_u(y) = ρ((log y − u)/δ)`. -/
def rhoU (u y : ℝ) : ℝ := rhoLoc ((Real.log y - u) / δL)

/-- `G_{j,t,u}(y) = F_{j,t}(y) ρ((log y − u)/δ)`. -/
def Gjtu (Q : ℝ) (j : ℕ) (t u y : ℝ) : ℂ := Fjt P Q j t y * (rhoU u y : ℂ)

lemma rhoU_eq (u : ℝ) : rhoU u = fun y => (fun z => rhoLoc (z - 4 * u)) (4 * Real.log y) := by
  funext y; simp only [rhoU, δL]; congr 1; ring

lemma rhoU_contDiffOn (u : ℝ) : ContDiffOn ℝ ∞ (rhoU u) (Ioi 0) := by
  unfold rhoU
  exact rhoLoc_contDiff.comp_contDiffOn
    (((Real.contDiffOn_log.mono fun x hx => ne_of_gt hx).sub contDiffOn_const).div_const _)

lemma rhoU_symb (K : ℕ) {C : ℝ} (hC : ∀ i ≤ K, ∀ ξ, ‖iteratedDeriv i rhoLoc ξ‖ ≤ C) (u : ℝ)
    {N : ℝ} (hN : 0 < N) :
    SymB (rhoU u) (Icc (N / 2) (2 * N)) K (K ! * C) (2 * 4 * K / N) := by
  rw [rhoU_eq]
  refine SymB.comp_log (g := fun z => rhoLoc (z - 4 * u))
    ((rhoLoc_contDiff.of_le (by exact_mod_cast le_top)).comp (contDiff_id.sub contDiff_const))
    (by norm_num) hN ?_
  intro y _ i hi
  rw [iteratedDeriv_comp_sub_const]
  exact hC i hi _

lemma Gjtu_eq (Q : ℝ) (j : ℕ) (t u : ℝ) :
    Gjtu P Q j t u = fun y => (P.ψj j y : ℂ) * (((UpsL P Q y : ℂ) * Et t y) * (rhoU u y : ℂ)) := by
  funext y; simp only [Gjtu, Fjt]; ring

lemma Gjtu_contDiff (Q : ℝ) (j : ℕ) (t u : ℝ) (K : ℕ) : ContDiff ℝ K (Gjtu P Q j t u) := by
  rw [Gjtu_eq]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ j / 2 := by positivity
  exact contDiff_bump_mul ((P.ψj_smooth j).of_le (by exact_mod_cast le_top)) hpos
    (fun y hy => P.ψj_supp j y hy)
    ((((Complex.ofRealCLM.contDiff.comp_contDiffOn (UpsL_contDiffOn P Q)).mul
      (Et_contDiffOn t)).mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
        (rhoU_contDiffOn u))).of_le (by exact_mod_cast le_top))

lemma Gjtu_ne_zero {Q : ℝ} (hQ : 1 < Q) {j : ℕ} {t u y : ℝ} (h : Gjtu P Q j t u y ≠ 0) :
    ((2 : ℝ) ^ j / 2 ≤ y ∧ y ≤ 2 * 2 ^ j) ∧ y ≤ P.Y Q := by
  have hF : Fjt P Q j t y ≠ 0 := left_ne_zero_of_mul h
  refine ⟨Fjt_supp P Q j t y hF, ?_⟩
  by_contra hc
  exact hF (Fjt_eq_zero_of_gt P hQ j t (not_le.mp hc))

/-- **`eqB:derivs` for `G_{j,t,u}`**: an explicit bound for the `K`-th derivative, uniform in `j`,
`t`, `u`, `Q` (with `L ≥ 1`). -/
theorem Gjtu_deriv_bound (K : ℕ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Q : ℝ, 1 ≤ P.L Q → ∀ (j : ℕ) (t u y : ℝ),
      ‖iteratedDeriv K (Gjtu P Q j t u) y‖ ≤
        C * Real.sqrt (2 / 2 ^ j) * (2 * (1 + |t|) * K / 2 ^ j) ^ K := by
  obtain ⟨Cu, hCu0, hCu⟩ := Ups0_deriv_bound P K
  obtain ⟨Cp, hCp0, hCp⟩ := ψj_deriv_uniform P K
  obtain ⟨Cρ, hCρ0, hCρ⟩ := uniform_bound_of_forall
    (P := fun i C => ∀ ξ, ‖iteratedDeriv i rhoLoc ξ‖ ≤ C)
    (fun i C C' hCC' h ξ => (h ξ).trans hCC')
    (fun i => by obtain ⟨C, -, hC⟩ := rhoLoc_deriv_bound i; exact ⟨C, hC⟩) K
  refine ⟨2 ^ K * Cp * (2 ^ K * (2 ^ K * (K ! * Cu) * K !) * (K ! * Cρ)) * 4 ^ K,
    by positivity, ?_⟩
  intro Q hL j t u y
  set N : ℝ := 2 ^ j with hN
  have hN1 : 1 ≤ N := one_le_pow₀ (by norm_num)
  have hN0 : 0 < N := by linarith
  set σ₀ : ℝ := 2 * (1 + |t|) * K / N with hσ₀
  set σ : ℝ := 4 * σ₀ with hσ
  have hσ₀0 : 0 ≤ σ₀ := by positivity
  have hσ0 : 0 ≤ σ := by positivity
  have hσ₀σ : σ₀ ≤ σ := by rw [hσ]; linarith
  have ht1 : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hs : Icc (N / 2) (2 * N) ⊆ Ioi (0 : ℝ) := fun y hy => lt_of_lt_of_le (by linarith) hy.1
  -- `Υ`
  have hU := UpsL_symb P hL K hCu hN1
  have hU' : SymB (fun y => (UpsL P Q y : ℂ)) (Icc (N / 2) (2 * N)) K (K ! * Cu) σ := by
    refine (SymB.ofReal isOpen_Ioi hs ((UpsL_contDiffOn P Q).of_le
      (by exact_mod_cast le_top)) hU).mono le_rfl (by positivity) ?_
    refine le_trans ?_ hσ₀σ
    rw [hσ₀]
    apply div_le_div_of_nonneg_right _ hN0.le
    nlinarith
  -- `E_t`
  have hE : SymB (Et t) (Icc (N / 2) (2 * N)) K (K ! * Real.sqrt (2 / N)) σ :=
    (Et_symb t K hN0).mono le_rfl hσ₀0 hσ₀σ
  have hUE := SymB.mul (U := Ioi 0) isOpen_Ioi hs
    ((Complex.ofRealCLM.contDiff.comp_contDiffOn (UpsL_contDiffOn P Q)).of_le
      (by exact_mod_cast le_top))
    ((Et_contDiffOn t).of_le (by exact_mod_cast le_top)) hσ0 hU' hE
  -- `ρ_u`
  have hR := rhoU_symb K hCρ u hN0
  have hR' : SymB (fun y => (rhoU u y : ℂ)) (Icc (N / 2) (2 * N)) K (K ! * Cρ) σ := by
    refine (SymB.ofReal isOpen_Ioi hs ((rhoU_contDiffOn u).of_le
      (by exact_mod_cast le_top)) hR).mono le_rfl (by positivity) ?_
    rw [hσ, hσ₀]
    rw [show 4 * (2 * (1 + |t|) * K / N) = 2 * 4 * K / N * (1 + |t|) by ring]
    have : 0 ≤ 2 * 4 * K / N := by positivity
    nlinarith
  have hUER := SymB.mul (U := Ioi 0) isOpen_Ioi hs
    (((Complex.ofRealCLM.contDiff.comp_contDiffOn (UpsL_contDiffOn P Q)).mul
      (Et_contDiffOn t)).of_le (by exact_mod_cast le_top))
    ((Complex.ofRealCLM.contDiff.comp_contDiffOn (rhoU_contDiffOn u)).of_le
      (by exact_mod_cast le_top)) hσ0 hUE hR'
  -- the bump
  have hψ : SymB (fun y => (P.ψj j y : ℂ)) (Icc (N / 2) (2 * N)) K Cp σ := by
    refine (SymB.ofReal isOpen_Ioi hs ((P.ψj_smooth j).contDiffOn.of_le
      (by exact_mod_cast le_top)) (ψj_symb P K hCp j _)).mono le_rfl (by positivity) ?_
    refine le_trans ?_ hσ₀σ
    rw [hσ₀, ← hN, inv_eq_one_div]
    apply div_le_div_of_nonneg_right _ hN0.le
    nlinarith
  have hF := SymB.mul (U := Ioi 0) isOpen_Ioi hs
    ((Complex.ofRealCLM.contDiff.comp (P.ψj_smooth j)).contDiffOn.of_le
      (by exact_mod_cast le_top))
    ((((Complex.ofRealCLM.contDiff.comp_contDiffOn (UpsL_contDiffOn P Q)).mul
      (Et_contDiffOn t)).mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
        (rhoU_contDiffOn u))).of_le (by exact_mod_cast le_top)) hσ0 hψ hUER
  have hglob := global_of_bump (ψ := P.ψj j) (a := N / 2) (b := 2 * N)
    (fun y hy => by have := P.ψj_supp j y hy; rw [← hN] at this; exact this)
    (G := fun y => ((UpsL P Q y : ℂ) * Et t y) * (rhoU u y : ℂ)) (by positivity) hσ0 hF K le_rfl y
  rw [Gjtu_eq]
  refine hglob.trans (le_of_eq ?_)
  rw [hσ, mul_pow]
  ring

/-! ### The expansion of `S_{x♯^s(u)}(θ)` -/

/-- `S^ρ_u[y](θ, t) = ∑_k y_k ρ((log k − u)/δ) e(kθ) k^{−it}`. -/
def Sadd (Q u θ : ℝ) (y : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ P.range Q, (y k : ℂ) * (rhoU u k : ℂ) * eA (k * θ) * (k : ℂ) ^ (-(Complex.I * t))

/-- `S_{x^s_y(u)}(θ) = ∫_J e^{itu} S^ρ_u[y](θ, t) dt`. -/
lemma S_xs_eq (Q T : ℝ) (y : ℕ → ℝ) (u θ : ℝ) :
    S (P.rangeZ Q) (xs P Q T y u) θ =
      ∫ t in P.J T, Complex.exp (Complex.I * t * u) * Sadd P Q u θ y t := by
  have h1 : S (P.rangeZ Q) (xs P Q T y u) θ =
      ∑ k ∈ P.range Q, ((y k : ℂ) * (rhoU u k : ℂ) * eA (k * θ)) * P.hatJ T (u - Real.log k) := by
    unfold S
    rw [← sum_rangeZ' P Q (fun k => ((y k : ℂ) * (rhoU u k : ℂ) * eA (k * θ)) *
      P.hatJ T (u - Real.log k))]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hcast : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    simp only [xs, rhoU]
    rw [PrimeSetup.xVec_of_pos P Q T y u hn1, hcast]
    ring
  rw [h1]
  unfold PrimeSetup.hatJ Sadd
  have hint : ∀ k ∈ P.range Q, IntegrableOn
      (fun t : ℝ => ((y k : ℂ) * (rhoU u k : ℂ) * eA (k * θ)) *
        Complex.exp (Complex.I * t * ((u - Real.log k : ℝ) : ℂ))) (P.J T) := by
    intro k _
    unfold PrimeSetup.J
    exact (by fun_prop : Continuous _).integrableOn_Icc
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ hint]
  refine setIntegral_congr_fun (by unfold PrimeSetup.J; exact measurableSet_Icc) fun t _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  rw [exp_hatJ_split t u k hk1]; ring

/-- `S^ρ_u[a♯](θ, t) = ∑_j ∑_{r ≤ R_j} (μ(r)/φ(r)) ∑_k G_{j,t,u}(k) c_r(k) e(kθ)`. -/
lemma Sadd_aSharp_eq (Q T u θ t : ℝ) :
    Sadd P Q u θ (P.aSharp Q T) t =
      ∑ j ∈ (P.blocks Q).filter (fun j => 1 ≤ P.Rj Q T j), ∑ r ∈ Finset.Icc 1 (P.Rj Q T j),
        (((μ r : ℝ) / Nat.totient r : ℝ) : ℂ) *
          ∑ k ∈ P.range Q, Gjtu P Q j t u k * ramanujan r k * eA (k * θ) := by
  unfold Sadd
  have hpt : ∀ k ∈ P.range Q, (P.aSharp Q T k : ℂ) * (rhoU u k : ℂ) * eA (k * θ) *
      (k : ℂ) ^ (-(Complex.I * t)) =
      ∑ j ∈ (P.blocks Q).filter (fun j => 1 ≤ P.Rj Q T j), ∑ r ∈ Finset.Icc 1 (P.Rj Q T j),
        (((μ r : ℝ) / Nat.totient r : ℝ) : ℂ) * (Gjtu P Q j t u k * ramanujan r k * eA (k * θ)) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    unfold PrimeSetup.aSharp PrimeSetup.LamR
    push_cast
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [Gjtu]
    rw [Fjt_nat P Q j t k hk1]
    conv_rhs => rw [← ramanujan_re_coe r k]
    push_cast; ring
  rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]

/-! ### The block estimate -/

/-- One block: `‖∑_{r ≤ R_j} (μ(r)/φ(r)) ∑_n G_{j,t,u}(n) c_r(n) e(nc/e)‖ ≤ C₁ N_j^{3/2 − Kε₃}`
when every `r ≤ R_j` is `< e ≤ Q`. -/
lemma block_bound_add {K : ℕ} (hK1 : 1 ≤ K) {CG : ℝ} (hCG0 : 0 ≤ CG)
    (hCG : ∀ Q : ℝ, 1 ≤ P.L Q → ∀ (j : ℕ) (t u y : ℝ),
      ‖iteratedDeriv K (Gjtu P Q j t u) y‖ ≤
        CG * Real.sqrt (2 / 2 ^ j) * (2 * (1 + |t|) * K / 2 ^ j) ^ K)
    {Q T t : ℝ} (hQ1 : 1 < Q) (hL : 1 ≤ P.L Q) (hT1 : 1 ≤ T) (ht : |t| ≤ 3 * T) (u : ℝ)
    {e c : ℕ} (heQ : (e : ℝ) ≤ Q) (hc : c ∈ reduced e) {j : ℕ} (hRj : 1 ≤ P.Rj Q T j)
    (hRe : P.Rj Q T j < e) :
    ‖∑ r ∈ Finset.Icc 1 (P.Rj Q T j), (((μ r : ℝ) / Nat.totient r : ℝ) : ℂ) *
        ∑ k ∈ P.range Q, Gjtu P Q j t u k * ramanujan r k * eA (k * ((c : ℝ) / e))‖ ≤
      ((K + 3) * CG * Real.sqrt 2 * (2 * K) ^ K) * ((2 : ℝ) ^ j) ^ ((3 : ℝ) / 2 - K * P.ε₃) := by
  set C₁ : ℝ := (K + 3) * CG * Real.sqrt 2 * (2 * K) ^ K with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hQ0 : 0 < Q := by linarith
  have hQT1 : 1 ≤ Q * T := by nlinarith
  obtain ⟨-, hQTR, hRN⟩ := Rj_facts P hQT1 hRj
  set N : ℝ := (2 : ℝ) ^ j with hN
  set R : ℕ := P.Rj Q T j with hR
  have hN1 : 1 ≤ N := one_le_pow₀ (by norm_num)
  have hN0 : 0 < N := by linarith
  have hinner : ∀ r ∈ Finset.Icc 1 R,
      ‖∑ k ∈ P.range Q, Gjtu P Q j t u k * ramanujan r k * eA (k * ((c : ℝ) / e))‖ ≤
        Nat.totient r * (C₁ * N ^ ((1 : ℝ) / 2 - K * P.ε₃)) := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hrR : r ≤ R := (Finset.mem_Icc.mp hr).2
    have hbound := sum_F_ramanujan_add_le (r := r) (e := e) (c := c) hr1 (by omega) hc
      (Gjtu_contDiff P Q j t u K) (fun y => hCG Q hL j t u y) (a := N / 2) (b := 2 * N)
      (by positivity) (by linarith) (fun y hy => (Gjtu_ne_zero P hQ1 hy).1) (P.range Q) (by
        intro n hn
        obtain ⟨hs, hnY⟩ := Gjtu_ne_zero P hQ1 hn
        simp only [PrimeSetup.range, Finset.mem_Icc]
        refine ⟨?_, Nat.le_floor hnY⟩
        have : (1 : ℝ) / 2 ≤ n := le_trans (by linarith) hs.1
        have : (0 : ℝ) < n := by linarith
        exact_mod_cast this)
    refine hbound.trans ?_
    have hφ : (0 : ℝ) ≤ Nat.totient r := Nat.cast_nonneg _
    have hre : ((r * e : ℕ) : ℝ) ≤ R * Q := by
      push_cast
      exact mul_le_mul (by exact_mod_cast hrR) heQ (Nat.cast_nonneg _) (by positivity)
    have hX := block_arith (t := t) (T := T) hN1 (by linarith) (by linarith) hK1 hCG0
      (Nat.cast_nonneg _) hre hQTR
    exact mul_le_mul_of_nonneg_left hX hφ
  have hterm : ∀ r ∈ Finset.Icc 1 R, ‖(((μ r : ℝ) / Nat.totient r : ℝ) : ℂ) *
      ∑ k ∈ P.range Q, Gjtu P Q j t u k * ramanujan r k * eA (k * ((c : ℝ) / e))‖ ≤
        C₁ * N ^ ((1 : ℝ) / 2 - K * P.ε₃) := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hφ : (0 : ℝ) < Nat.totient r := by exact_mod_cast Nat.totient_pos.mpr hr1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, Nat.abs_cast]
    have hμ : |(μ r : ℝ)| ≤ 1 := by
      have := ArithmeticFunction.abs_moebius_le_one (n := r)
      exact_mod_cast this
    calc |(μ r : ℝ)| / Nat.totient r *
          ‖∑ k ∈ P.range Q, Gjtu P Q j t u k * ramanujan r k * eA (k * ((c : ℝ) / e))‖
        ≤ 1 / Nat.totient r * (Nat.totient r * (C₁ * N ^ ((1 : ℝ) / 2 - K * P.ε₃))) := by
          gcongr
          exact hinner r hr
      _ = _ := by field_simp
  have hsumr := (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul] at hsumr
  simp only [add_tsub_cancel_right] at hsumr
  refine hsumr.trans ?_
  have h1 : N * N ^ ((1 : ℝ) / 2 - K * P.ε₃) = N ^ ((3 : ℝ) / 2 - K * P.ε₃) := by
    rw [show N * N ^ ((1 : ℝ) / 2 - K * P.ε₃) = N ^ (1 : ℝ) * N ^ ((1 : ℝ) / 2 - K * P.ε₃) by
      rw [Real.rpow_one], ← Real.rpow_add hN0]
    congr 1; ring
  calc (R : ℝ) * (C₁ * N ^ ((1 : ℝ) / 2 - K * P.ε₃))
      ≤ N * (C₁ * N ^ ((1 : ℝ) / 2 - K * P.ε₃)) := by gcongr
    _ = C₁ * (N * N ^ ((1 : ℝ) / 2 - K * P.ε₃)) := by ring
    _ = C₁ * N ^ ((3 : ℝ) / 2 - K * P.ε₃) := by rw [h1]

/-! ### The Farey levels above `R_max` -/

lemma mem_J_abs_le {T t : ℝ} (hT : 0 ≤ T) (ht : t ∈ P.J T) : |t| ≤ 3 * T := by
  unfold PrimeSetup.J at ht
  have h1 := ht.1
  have h2 := ht.2
  have hθ := P.θ_pos
  have hθ' := P.θ_lt
  rw [abs_le]
  constructor <;> nlinarith

lemma norm_S_xs_le {Q T : ℝ} (hT : 0 ≤ T) (y : ℕ → ℝ) (u θ : ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ t ∈ P.J T, ‖Sadd P Q u θ y t‖ ≤ B) :
    ‖S (P.rangeZ Q) (xs P Q T y u) θ‖ ≤ B * T := by
  rw [S_xs_eq]
  have : ‖∫ t in P.J T, Complex.exp (Complex.I * t * u) * Sadd P Q u θ y t‖ ≤
      B * volume.real (P.J T) := norm_setIntegral_le_of_norm_le_const
    (by unfold PrimeSetup.J; exact measure_Icc_lt_top) (fun t ht => by
      rw [norm_mul]
      have : ‖Complex.exp (Complex.I * t * u)‖ = 1 := by
        rw [Complex.norm_exp]; simp
      rw [this, one_mul]; exact hB t ht)
  exact this.trans (mul_le_mul_of_nonneg_left (volume_J_le P hT) hB0)

/-- **Step 4(b), levels above `R_max`**: `|S_{x♯^s(u)}(c/e)| ≤ C Q^{−A}` for `(c, e) = 1`, `e ≤ Q`,
`e > R_j` for every block `j`; uniformly in `u` and `T ∈ heights`. -/
theorem farey_sharp_le (A : ℝ) :
    ∃ C Q₀ : ℝ, 0 ≤ C ∧ ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ P.heights Q, ∀ u : ℝ, ∀ e c : ℕ,
      (e : ℝ) ≤ Q → (∀ j ∈ P.blocks Q, P.Rj Q T j < e) → c ∈ reduced e →
        ‖S (P.rangeZ Q) (xs P Q T (P.aSharp Q T) u) ((c : ℝ) / e)‖ ≤ C * Q ^ (-A) := by
  set K : ℕ := ⌈(|A| + 5) / P.ε₃⌉₊ + 1 with hKdef
  have hK1 : 1 ≤ K := by omega
  have hKε : |A| + 5 ≤ K * P.ε₃ := by
    have h1 : (|A| + 5) / P.ε₃ ≤ ⌈(|A| + 5) / P.ε₃⌉₊ := Nat.le_ceil _
    have h2 : (⌈(|A| + 5) / P.ε₃⌉₊ : ℝ) ≤ K := by rw [hKdef]; push_cast; linarith
    have := P.ε₃_pos
    rw [div_le_iff₀ this] at h1
    nlinarith
  obtain ⟨CG, hCG0, hCG⟩ := Gjtu_deriv_bound P K hK1
  set C₁ : ℝ := (K + 3) * CG * Real.sqrt 2 * (2 * K) ^ K with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  set c' : ℝ := P.A0 ^ P.A0 with hc'
  have hc'0 : 0 ≤ c' := Real.rpow_nonneg (lt_trans P.a0_pos P.a0_lt).le _
  refine ⟨3 * C₁ * c', max (Real.exp (1 / P.lam)) (Real.exp 1), by positivity, ?_⟩
  intro Q hQ T hT u e c heQ hRe hc
  have hQL : Real.exp (1 / P.lam) ≤ Q := le_of_max_le_left hQ
  have hQe : Real.exp 1 ≤ Q := le_of_max_le_right hQ
  have hQ1 : 1 < Q :=
    lt_of_lt_of_le (by have := Real.add_one_lt_exp (x := 1) one_ne_zero; linarith) hQe
  have hQ0 : 0 < Q := by linarith
  have hL := one_le_L P hQL
  have hT1 := one_le_T P hQe hT
  have hTQ := T_le_Q P hQ1.le hT
  have hexp : (3 : ℝ) / 2 - K * P.ε₃ ≤ 0 := by linarith [abs_nonneg A]
  have hblock : ∀ t ∈ P.J T, ∀ j ∈ (P.blocks Q).filter (fun j => 1 ≤ P.Rj Q T j),
      ‖∑ r ∈ Finset.Icc 1 (P.Rj Q T j), (((μ r : ℝ) / Nat.totient r : ℝ) : ℂ) *
          ∑ k ∈ P.range Q, Gjtu P Q j t u k * ramanujan r k * eA (k * ((c : ℝ) / e))‖ ≤
        C₁ * Q ^ ((3 : ℝ) / 2 - K * P.ε₃) := by
    intro t ht j hj
    have hjb := (Finset.mem_filter.mp hj).1
    have hRj := (Finset.mem_filter.mp hj).2
    refine (block_bound_add P hK1 hCG0 hCG hQ1 hL hT1 (mem_J_abs_le P (by linarith) ht) u heQ hc
      hRj (hRe j hjb)).trans ?_
    have hQT1 : 1 ≤ Q * T := by nlinarith
    have hNQ : Q ≤ (2 : ℝ) ^ j := le_trans (by nlinarith) (Rj_facts P hQT1 hRj).1
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hQ0 hNQ hexp) hC₁0
  have hcard : (((P.blocks Q).filter (fun j => 1 ≤ P.Rj Q T j)).card : ℝ) ≤ 3 * Q ^ 2 :=
    le_trans (by exact_mod_cast Finset.card_filter_le _ _) (card_blocks_le P hQ1.le)
  set B : ℝ := 3 * Q ^ 2 * (C₁ * Q ^ ((3 : ℝ) / 2 - K * P.ε₃)) with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hS := norm_S_xs_le P (by linarith : (0 : ℝ) ≤ T) (P.aSharp Q T) u ((c : ℝ) / e) hB0
    (fun t ht => by
      rw [Sadd_aSharp_eq]
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (hblock t ht)).trans ?_)
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hcard (by positivity))
  refine hS.trans ?_
  have hfin : Q ^ 2 * Q ^ ((3 : ℝ) / 2 - K * P.ε₃) * Q ≤ Q ^ (-A) := by
    rw [← Real.rpow_natCast Q 2, ← Real.rpow_add hQ0,
      show Q ^ ((2 : ℕ) + ((3 : ℝ) / 2 - K * P.ε₃)) * Q =
        Q ^ ((2 : ℕ) + ((3 : ℝ) / 2 - K * P.ε₃)) * Q ^ (1 : ℝ) by rw [Real.rpow_one],
      ← Real.rpow_add hQ0]
    apply Real.rpow_le_rpow_of_exponent_le hQ1.le
    push_cast; linarith [le_abs_self A]
  calc B * T ≤ B * (c' * Q) := mul_le_mul_of_nonneg_left hTQ hB0
    _ = 3 * C₁ * c' * (Q ^ 2 * Q ^ ((3 : ℝ) / 2 - K * P.ε₃) * Q) := by rw [hBdef]; ring
    _ ≤ 3 * C₁ * c' * Q ^ (-A) := by gcongr

end Families.Phase3.C
