/-
# Package TS: Step 4(b), the Farey levels above `R_max` at polynomial height

For `(c, e) = 1`, `e ≤ Q` (the **family** modulus) and `e` larger than every `R_j`,
`|S_{x♯^s(u)}(c/e)| ≪_A Q^{−A}` uniformly in `u`, `T` in the cell and the localisation scale
`δ ∈ [T^{−1}, 1]`. The route is the families one (`Families.Phase3.C.farey_sharp_le`), with
* the setup at `Q' = QT` (`HSetup.toPS`), the levels at `Q`, and `R_j = ⌊N_j^{1−ε₃}/(QT)⌋`, so that
  `QT R_j ≤ N_j^{1−ε₃}` and `r e ≤ R_j Q` (the arithmetic `block_arith` is unchanged);
* the cut-off `ρ((log y − u)/δ)` at the variable scale `δ`: its symbol bound has frequency
  `2δ^{−1}K/N`, and `δ^{−1} ≤ T ≤ |t|` on `t ∈ J`, so it is absorbed by the `(1+|t|)` of `F_{j,t}`
  (this is where `δ ≥ T^{−1}` is used; the TeX's `δ = T^{−1+ε₅}` qualifies);
* at most `3(QT)²` blocks, `|J| ≤ T` and `T, QT ≤ Q^{1+κc}`, absorbed by `K ε₃ ≥ A + 3κc + 5`.
-/
import FamiliesH.TS.Local

noncomputable section

open scoped BigOperators ContDiff Nat ArithmeticFunction.Moebius
open Set MeasureTheory ArithmeticFunction

namespace Families.Hybrid

open Families Families.Phase3.C

namespace TS

/-! ### The cut-off at scale `δ` -/

/-- `ρ_u(y) = ρ((log y − u)/δ)`. -/
def rhoUH (δ u y : ℝ) : ℝ := rhoLoc ((Real.log y - u) / δ)

lemma rhoUH_eq (δ u : ℝ) :
    rhoUH δ u = fun y => (fun z => rhoLoc (z - u / δ)) (δ⁻¹ * Real.log y) := by
  funext y; simp only [rhoUH]; congr 1; ring

lemma rhoUH_contDiffOn (δ u : ℝ) : ContDiffOn ℝ ∞ (rhoUH δ u) (Ioi 0) := by
  unfold rhoUH
  exact rhoLoc_contDiff.comp_contDiffOn
    (((Real.contDiffOn_log.mono fun x hx => ne_of_gt hx).sub contDiffOn_const).div_const _)

lemma rhoUH_symb (K : ℕ) {C : ℝ} (hC : ∀ i ≤ K, ∀ ξ, ‖iteratedDeriv i rhoLoc ξ‖ ≤ C) {δ : ℝ}
    (hδ : 1 ≤ δ⁻¹) (u : ℝ) {N : ℝ} (hN : 0 < N) :
    SymB (rhoUH δ u) (Icc (N / 2) (2 * N)) K (K ! * C) (2 * δ⁻¹ * K / N) := by
  rw [rhoUH_eq]
  refine SymB.comp_log (g := fun z => rhoLoc (z - u / δ))
    ((rhoLoc_contDiff.of_le (by exact_mod_cast le_top)).comp (contDiff_id.sub contDiff_const))
    hδ hN ?_
  intro y _ i hi
  rw [iteratedDeriv_comp_sub_const]
  exact hC i hi _

section PS

variable (P : PrimeSetup)

/-- The localised vector at scale `δ` for a families setup (`xsH P = xsG P.toPS` at `Q' = QT`). -/
def xsG (Qs T δ : ℝ) (y : ℕ → ℝ) (u : ℝ) : ℤ → ℂ :=
  fun n => P.xVec Qs T y u n * rhoLoc ((Real.log n.toNat - u) / δ)

/-! ### The weights `G_{j,t,u}` -/

/-- `G_{j,t,u}(y) = F_{j,t}(y) ρ((log y − u)/δ)`. -/
def GjtuG (Qs : ℝ) (j : ℕ) (t δ u y : ℝ) : ℂ := Fjt P Qs j t y * (rhoUH δ u y : ℂ)

lemma GjtuG_eq (Qs : ℝ) (j : ℕ) (t δ u : ℝ) :
    GjtuG P Qs j t δ u =
      fun y => (P.ψj j y : ℂ) * (((UpsL P Qs y : ℂ) * Et t y) * (rhoUH δ u y : ℂ)) := by
  funext y; simp only [GjtuG, Fjt]; ring

lemma GjtuG_contDiff (Qs : ℝ) (j : ℕ) (t δ u : ℝ) (K : ℕ) : ContDiff ℝ K (GjtuG P Qs j t δ u) := by
  rw [GjtuG_eq]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ j / 2 := by positivity
  exact contDiff_bump_mul ((P.ψj_smooth j).of_le (by exact_mod_cast le_top)) hpos
    (fun y hy => P.ψj_supp j y hy)
    ((((Complex.ofRealCLM.contDiff.comp_contDiffOn (UpsL_contDiffOn P Qs)).mul
      (Et_contDiffOn t)).mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
        (rhoUH_contDiffOn δ u))).of_le (by exact_mod_cast le_top))

lemma GjtuG_ne_zero {Qs : ℝ} (hQs : 1 < Qs) {j : ℕ} {t δ u y : ℝ} (h : GjtuG P Qs j t δ u y ≠ 0) :
    ((2 : ℝ) ^ j / 2 ≤ y ∧ y ≤ 2 * 2 ^ j) ∧ y ≤ P.Y Qs := by
  have hF : Fjt P Qs j t y ≠ 0 := left_ne_zero_of_mul h
  refine ⟨Fjt_supp P Qs j t y hF, ?_⟩
  by_contra hc
  exact hF (Fjt_eq_zero_of_gt P hQs j t (not_le.mp hc))

/-- **`eqB:derivs` for `G_{j,t,u}`** at the scale `δ`: uniform in `j`, `t`, `u`, `Qs` (with
`L ≥ 1`) and `δ` with `1 ≤ δ^{−1} ≤ 4(1+|t|)`. -/
theorem GjtuG_deriv_bound (K : ℕ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Qs : ℝ, 1 ≤ P.L Qs → ∀ (j : ℕ) (t δ u y : ℝ), 1 ≤ δ⁻¹ →
      δ⁻¹ ≤ 4 * (1 + |t|) →
      ‖iteratedDeriv K (GjtuG P Qs j t δ u) y‖ ≤
        C * Real.sqrt (2 / 2 ^ j) * (2 * (1 + |t|) * K / 2 ^ j) ^ K := by
  obtain ⟨Cu, hCu0, hCu⟩ := Ups0_deriv_bound P K
  obtain ⟨Cp, hCp0, hCp⟩ := ψj_deriv_uniform P K
  obtain ⟨Cρ, hCρ0, hCρ⟩ := uniform_bound_of_forall
    (P := fun i C => ∀ ξ, ‖iteratedDeriv i rhoLoc ξ‖ ≤ C)
    (fun i C C' hCC' h ξ => (h ξ).trans hCC')
    (fun i => by obtain ⟨C, -, hC⟩ := rhoLoc_deriv_bound i; exact ⟨C, hC⟩) K
  refine ⟨2 ^ K * Cp * (2 ^ K * (2 ^ K * (K ! * Cu) * K !) * (K ! * Cρ)) * 4 ^ K,
    by positivity, ?_⟩
  intro Qs hL j t δ u y hδ1 hδt
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
  have hU' : SymB (fun y => (UpsL P Qs y : ℂ)) (Icc (N / 2) (2 * N)) K (K ! * Cu) σ := by
    refine (SymB.ofReal isOpen_Ioi hs ((UpsL_contDiffOn P Qs).of_le
      (by exact_mod_cast le_top)) hU).mono le_rfl (by positivity) ?_
    refine le_trans ?_ hσ₀σ
    rw [hσ₀]
    apply div_le_div_of_nonneg_right _ hN0.le
    nlinarith
  -- `E_t`
  have hE : SymB (Et t) (Icc (N / 2) (2 * N)) K (K ! * Real.sqrt (2 / N)) σ :=
    (Et_symb t K hN0).mono le_rfl hσ₀0 hσ₀σ
  have hUE := SymB.mul (U := Ioi 0) isOpen_Ioi hs
    ((Complex.ofRealCLM.contDiff.comp_contDiffOn (UpsL_contDiffOn P Qs)).of_le
      (by exact_mod_cast le_top))
    ((Et_contDiffOn t).of_le (by exact_mod_cast le_top)) hσ0 hU' hE
  -- `ρ_u` at scale `δ`
  have hR := rhoUH_symb K hCρ hδ1 u hN0
  have hR' : SymB (fun y => (rhoUH δ u y : ℂ)) (Icc (N / 2) (2 * N)) K (K ! * Cρ) σ := by
    refine (SymB.ofReal isOpen_Ioi hs ((rhoUH_contDiffOn δ u).of_le
      (by exact_mod_cast le_top)) hR).mono le_rfl (by positivity) ?_
    rw [hσ, hσ₀]
    have hKN : 0 ≤ (K : ℝ) / N := by positivity
    calc 2 * δ⁻¹ * K / N = 2 * δ⁻¹ * ((K : ℝ) / N) := by ring
      _ ≤ 2 * (4 * (1 + |t|)) * ((K : ℝ) / N) := by gcongr
      _ = 4 * (2 * (1 + |t|) * K / N) := by ring
  have hUER := SymB.mul (U := Ioi 0) isOpen_Ioi hs
    (((Complex.ofRealCLM.contDiff.comp_contDiffOn (UpsL_contDiffOn P Qs)).mul
      (Et_contDiffOn t)).of_le (by exact_mod_cast le_top))
    ((Complex.ofRealCLM.contDiff.comp_contDiffOn (rhoUH_contDiffOn δ u)).of_le
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
    ((((Complex.ofRealCLM.contDiff.comp_contDiffOn (UpsL_contDiffOn P Qs)).mul
      (Et_contDiffOn t)).mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
        (rhoUH_contDiffOn δ u))).of_le (by exact_mod_cast le_top)) hσ0 hψ hUER
  have hglob := global_of_bump (ψ := P.ψj j) (a := N / 2) (b := 2 * N)
    (fun y hy => by have := P.ψj_supp j y hy; rw [← hN] at this; exact this)
    (G := fun y => ((UpsL P Qs y : ℂ) * Et t y) * (rhoUH δ u y : ℂ)) (by positivity) hσ0 hF K
    le_rfl y
  rw [GjtuG_eq]
  refine hglob.trans (le_of_eq ?_)
  rw [hσ, mul_pow]
  ring

/-! ### The expansion of `S_{x♯^s(u)}(θ)` -/

/-- `S^ρ_u[y](θ, t) = ∑_k y_k ρ((log k − u)/δ) e(kθ) k^{−it}`. -/
def SaddG (Qs δ u θ : ℝ) (y : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ k ∈ P.range Qs, (y k : ℂ) * (rhoUH δ u k : ℂ) * eA (k * θ) * (k : ℂ) ^ (-(Complex.I * t))

/-- `S_{x^s_y(u)}(θ) = ∫_J e^{itu} S^ρ_u[y](θ, t) dt`. -/
lemma S_xsG_eq (Qs T δ : ℝ) (y : ℕ → ℝ) (u θ : ℝ) :
    S (P.rangeZ Qs) (xsG P Qs T δ y u) θ =
      ∫ t in P.J T, Complex.exp (Complex.I * t * u) * SaddG P Qs δ u θ y t := by
  have h1 : S (P.rangeZ Qs) (xsG P Qs T δ y u) θ =
      ∑ k ∈ P.range Qs, ((y k : ℂ) * (rhoUH δ u k : ℂ) * eA (k * θ)) *
        P.hatJ T (u - Real.log k) := by
    unfold S
    rw [← sum_rangeZ' P Qs (fun k => ((y k : ℂ) * (rhoUH δ u k : ℂ) * eA (k * θ)) *
      P.hatJ T (u - Real.log k))]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hcast : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    simp only [xsG, rhoUH]
    rw [PrimeSetup.xVec_of_pos P Qs T y u hn1, hcast]
    ring
  rw [h1]
  unfold PrimeSetup.hatJ SaddG
  have hint : ∀ k ∈ P.range Qs, IntegrableOn
      (fun t : ℝ => ((y k : ℂ) * (rhoUH δ u k : ℂ) * eA (k * θ)) *
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
lemma SaddG_aSharp_eq (Qs T δ u θ t : ℝ) :
    SaddG P Qs δ u θ (P.aSharp Qs T) t =
      ∑ j ∈ (P.blocks Qs).filter (fun j => 1 ≤ P.Rj Qs T j), ∑ r ∈ Finset.Icc 1 (P.Rj Qs T j),
        (((μ r : ℝ) / Nat.totient r : ℝ) : ℂ) *
          ∑ k ∈ P.range Qs, GjtuG P Qs j t δ u k * ramanujan r k * eA (k * θ) := by
  unfold SaddG
  have hpt : ∀ k ∈ P.range Qs, (P.aSharp Qs T k : ℂ) * (rhoUH δ u k : ℂ) * eA (k * θ) *
      (k : ℂ) ^ (-(Complex.I * t)) =
      ∑ j ∈ (P.blocks Qs).filter (fun j => 1 ≤ P.Rj Qs T j), ∑ r ∈ Finset.Icc 1 (P.Rj Qs T j),
        (((μ r : ℝ) / Nat.totient r : ℝ) : ℂ) *
          (GjtuG P Qs j t δ u k * ramanujan r k * eA (k * θ)) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    unfold PrimeSetup.aSharp PrimeSetup.LamR
    push_cast
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [GjtuG]
    rw [Fjt_nat P Qs j t k hk1]
    conv_rhs => rw [← ramanujan_re_coe r k]
    push_cast; ring
  rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]

/-! ### One block -/

/-- One block at `Q' = Qf T`, `T' = 1`: when every `r ≤ R_j` is `< e ≤ Qf`,
`‖∑_{r ≤ R_j} (μ(r)/φ(r)) ∑_n G_{j,t,u}(n) c_r(n) e(nc/e)‖ ≤ C₁ N_j^{3/2 − Kε₃}`. -/
lemma block_bound_addG {K : ℕ} (hK1 : 1 ≤ K) {CG : ℝ} (hCG0 : 0 ≤ CG)
    (hCG : ∀ Qs : ℝ, 1 ≤ P.L Qs → ∀ (j : ℕ) (t δ u y : ℝ), 1 ≤ δ⁻¹ → δ⁻¹ ≤ 4 * (1 + |t|) →
      ‖iteratedDeriv K (GjtuG P Qs j t δ u) y‖ ≤
        CG * Real.sqrt (2 / 2 ^ j) * (2 * (1 + |t|) * K / 2 ^ j) ^ K)
    {Qf T t δ : ℝ} (hQf1 : 1 < Qf) (hL : 1 ≤ P.L (Qf * T)) (hT1 : 1 ≤ T) (ht : |t| ≤ 3 * T)
    (hδ1 : 1 ≤ δ⁻¹) (hδt : δ⁻¹ ≤ 4 * (1 + |t|)) (u : ℝ)
    {e c : ℕ} (heQ : (e : ℝ) ≤ Qf) (hc : c ∈ reduced e) {j : ℕ} (hRj : 1 ≤ P.Rj (Qf * T) 1 j)
    (hRe : P.Rj (Qf * T) 1 j < e) :
    ‖∑ r ∈ Finset.Icc 1 (P.Rj (Qf * T) 1 j), (((μ r : ℝ) / Nat.totient r : ℝ) : ℂ) *
        ∑ k ∈ P.range (Qf * T), GjtuG P (Qf * T) j t δ u k * ramanujan r k *
          eA (k * ((c : ℝ) / e))‖ ≤
      ((K + 3) * CG * Real.sqrt 2 * (2 * K) ^ K) * ((2 : ℝ) ^ j) ^ ((3 : ℝ) / 2 - K * P.ε₃) := by
  set C₁ : ℝ := (K + 3) * CG * Real.sqrt 2 * (2 * K) ^ K with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hQ0 : 0 < Qf := by linarith
  have hQT1 : 1 ≤ Qf * T * 1 := by nlinarith
  have hQs1 : 1 < Qf * T := by nlinarith
  obtain ⟨-, hQTR, hRN⟩ := Rj_facts P hQT1 hRj
  rw [mul_one] at hQTR
  set N : ℝ := (2 : ℝ) ^ j with hN
  set R : ℕ := P.Rj (Qf * T) 1 j with hR
  have hN1 : 1 ≤ N := one_le_pow₀ (by norm_num)
  have hN0 : 0 < N := by linarith
  have hinner : ∀ r ∈ Finset.Icc 1 R,
      ‖∑ k ∈ P.range (Qf * T), GjtuG P (Qf * T) j t δ u k * ramanujan r k *
          eA (k * ((c : ℝ) / e))‖ ≤
        Nat.totient r * (C₁ * N ^ ((1 : ℝ) / 2 - K * P.ε₃)) := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hrR : r ≤ R := (Finset.mem_Icc.mp hr).2
    have hbound := sum_F_ramanujan_add_le (r := r) (e := e) (c := c) hr1 (by omega) hc
      (GjtuG_contDiff P (Qf * T) j t δ u K) (fun y => hCG (Qf * T) hL j t δ u y hδ1 hδt)
      (a := N / 2) (b := 2 * N) (by positivity) (by linarith)
      (fun y hy => (GjtuG_ne_zero P hQs1 hy).1) (P.range (Qf * T)) (by
        intro n hn
        obtain ⟨hs, hnY⟩ := GjtuG_ne_zero P hQs1 hn
        simp only [PrimeSetup.range, Finset.mem_Icc]
        refine ⟨?_, Nat.le_floor hnY⟩
        have : (1 : ℝ) / 2 ≤ n := le_trans (by linarith) hs.1
        have : (0 : ℝ) < n := by linarith
        exact_mod_cast this)
    refine hbound.trans ?_
    have hφ : (0 : ℝ) ≤ Nat.totient r := Nat.cast_nonneg _
    have hre : ((r * e : ℕ) : ℝ) ≤ R * Qf := by
      push_cast
      exact mul_le_mul (by exact_mod_cast hrR) heQ (Nat.cast_nonneg _) (by positivity)
    have hX := block_arith (t := t) (T := T) hN1 (by linarith) (by linarith) hK1 hCG0
      (Nat.cast_nonneg _) hre hQTR
    exact mul_le_mul_of_nonneg_left hX hφ
  have hterm : ∀ r ∈ Finset.Icc 1 R, ‖(((μ r : ℝ) / Nat.totient r : ℝ) : ℂ) *
      ∑ k ∈ P.range (Qf * T), GjtuG P (Qf * T) j t δ u k * ramanujan r k *
        eA (k * ((c : ℝ) / e))‖ ≤ C₁ * N ^ ((1 : ℝ) / 2 - K * P.ε₃) := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hφ : (0 : ℝ) < Nat.totient r := by exact_mod_cast Nat.totient_pos.mpr hr1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, Nat.abs_cast]
    have hμ : |(μ r : ℝ)| ≤ 1 := by
      have := ArithmeticFunction.abs_moebius_le_one (n := r)
      exact_mod_cast this
    calc |(μ r : ℝ)| / Nat.totient r *
          ‖∑ k ∈ P.range (Qf * T), GjtuG P (Qf * T) j t δ u k * ramanujan r k *
            eA (k * ((c : ℝ) / e))‖
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

lemma norm_S_xsG_le {Qs T : ℝ} (hT : 0 ≤ T) (δ : ℝ) (y : ℕ → ℝ) (u θ : ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ t ∈ P.J T, ‖SaddG P Qs δ u θ y t‖ ≤ B) :
    ‖S (P.rangeZ Qs) (xsG P Qs T δ y u) θ‖ ≤ B * T := by
  rw [S_xsG_eq]
  have : ‖∫ t in P.J T, Complex.exp (Complex.I * t * u) * SaddG P Qs δ u θ y t‖ ≤
      B * volume.real (P.J T) := norm_setIntegral_le_of_norm_le_const
    (by unfold PrimeSetup.J; exact measure_Icc_lt_top) (fun t ht => by
      rw [norm_mul]
      have : ‖Complex.exp (Complex.I * t * u)‖ = 1 := by
        rw [Complex.norm_exp]; simp
      rw [this, one_mul]; exact hB t ht)
  exact this.trans (mul_le_mul_of_nonneg_left (volume_J_le P hT) hB0)

end PS

/-! ### The Farey levels above `R_max` at polynomial height -/

variable (P : HSetup)

lemma xsH_eq_xsG (Q T δ : ℝ) (y : ℕ → ℝ) (u : ℝ) :
    xsH P Q T δ y u = xsG P.toPS (Q * T) T δ y u := rfl

lemma one_le_T_of_mem {Q T : ℝ} (hQe : Real.exp 1 ≤ Q) (hT : T ∈ P.heights Q) : 1 ≤ T := by
  have hl : 1 ≤ Real.log Q := by
    have := Real.log_le_log (Real.exp_pos _) hQe; rwa [Real.log_exp] at this
  exact le_trans (Real.one_le_rpow hl P.a0_pos.le) hT.1

lemma le_abs_of_mem_J {T t : ℝ} (hT : 0 ≤ T) (ht : t ∈ P.J T) : T ≤ |t| := by
  have h1 : (1 + P.θ) * T ≤ t := ht.1
  have hθ := P.θ_pos
  have : T ≤ t := by nlinarith
  exact this.trans (le_abs_self t)

/-- **Step 4(b), levels above `R_max`**: `|S_{x♯^s(u)}(c/e)| ≤ C Q^{−A}` for `(c, e) = 1`, `e ≤ Q`,
`e > R_j` for every block `j`; uniformly in `u`, `T` in the cell and `δ ∈ [T^{−1}, 1]`. -/
theorem farey_sharpH (A : ℝ) :
    ∃ C Q₀ : ℝ, 0 ≤ C ∧ ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ P.heights Q, ∀ δ : ℝ, 1 ≤ δ⁻¹ → δ⁻¹ ≤ T →
      ∀ u : ℝ, ∀ e c : ℕ, (e : ℝ) ≤ Q → (∀ j ∈ P.blocks Q T, P.Rj Q T j < e) → c ∈ reduced e →
        ‖S (P.rangeZ Q T) (xsH P Q T δ (P.aSharp Q T) u) ((c : ℝ) / e)‖ ≤ C * Q ^ (-A) := by
  have hkc := P.kc_pos
  set K : ℕ := ⌈(|A| + 3 * P.kc + 5) / P.ε₃⌉₊ + 1 with hKdef
  have hK1 : 1 ≤ K := by omega
  have hKε : |A| + 3 * P.kc + 5 ≤ K * P.ε₃ := by
    have h1 : (|A| + 3 * P.kc + 5) / P.ε₃ ≤ ⌈(|A| + 3 * P.kc + 5) / P.ε₃⌉₊ := Nat.le_ceil _
    have h2 : (⌈(|A| + 3 * P.kc + 5) / P.ε₃⌉₊ : ℝ) ≤ K := by rw [hKdef]; push_cast; linarith
    have := P.ε₃_pos
    rw [div_le_iff₀ this] at h1
    nlinarith
  obtain ⟨CG, hCG0, hCG⟩ := GjtuG_deriv_bound P.toPS K hK1
  set C₁ : ℝ := (K + 3) * CG * Real.sqrt 2 * (2 * K) ^ K with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  refine ⟨3 * C₁, max (Real.exp (1 / P.lam)) (Real.exp 1), by positivity, ?_⟩
  intro Q hQ T hT δ hδ1 hδT u e c heQ hRe hc
  have hQL : Real.exp (1 / P.lam) ≤ Q := le_of_max_le_left hQ
  have hQe : Real.exp 1 ≤ Q := le_of_max_le_right hQ
  have hQ1 : 1 < Q :=
    lt_of_lt_of_le (by have := Real.add_one_lt_exp (x := 1) one_ne_zero; linarith) hQe
  have hQ0 : 0 < Q := by linarith
  have hT1 : 1 ≤ T := one_le_T_of_mem P hQe hT
  have hQT : Q ≤ Q * T := by nlinarith
  have hQT1 : 1 < Q * T := by nlinarith
  have hL : 1 ≤ P.toPS.L (Q * T) := one_le_L P.toPS (le_trans hQL hQT)
  obtain ⟨hM1, hQM, hTM, hQTM⟩ := P.cell_bounds hQ1.le hT1 hT
  have hexp : (3 : ℝ) / 2 - K * P.ε₃ ≤ 0 := by linarith [abs_nonneg A]
  have hblock : ∀ t ∈ P.toPS.J T,
      ∀ j ∈ (P.toPS.blocks (Q * T)).filter (fun j => 1 ≤ P.toPS.Rj (Q * T) 1 j),
      ‖∑ r ∈ Finset.Icc 1 (P.toPS.Rj (Q * T) 1 j), (((μ r : ℝ) / Nat.totient r : ℝ) : ℂ) *
          ∑ k ∈ P.toPS.range (Q * T), GjtuG P.toPS (Q * T) j t δ u k * ramanujan r k *
            eA (k * ((c : ℝ) / e))‖ ≤
        C₁ * Q ^ ((3 : ℝ) / 2 - K * P.ε₃) := by
    intro t ht j hj
    have hjb := (Finset.mem_filter.mp hj).1
    have hRj := (Finset.mem_filter.mp hj).2
    have htT := mem_J_abs_le P.toPS (by linarith) ht
    have hTt : T ≤ |t| := le_abs_of_mem_J P (by linarith) ht
    have hδt : δ⁻¹ ≤ 4 * (1 + |t|) := by linarith
    have hRe' : P.toPS.Rj (Q * T) 1 j < e := by rw [← P.Rj_eq_one]; exact hRe j hjb
    refine (block_bound_addG P.toPS hK1 hCG0 hCG hQ1 hL hT1 htT hδ1 hδt u heQ hc hRj
      hRe').trans ?_
    have hQT1' : 1 ≤ Q * T * 1 := by nlinarith
    have hNQ : Q ≤ (2 : ℝ) ^ j := by
      have := (Rj_facts P.toPS hQT1' hRj).1
      nlinarith
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hQ0 hNQ hexp) hC₁0
  have hcard : (((P.toPS.blocks (Q * T)).filter
      (fun j => 1 ≤ P.toPS.Rj (Q * T) 1 j)).card : ℝ) ≤ 3 * (Q * T) ^ 2 :=
    le_trans (by exact_mod_cast Finset.card_filter_le _ _) (card_blocks_le P.toPS hQT1.le)
  set B : ℝ := 3 * (Q * T) ^ 2 * (C₁ * Q ^ ((3 : ℝ) / 2 - K * P.ε₃)) with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hS := norm_S_xsG_le P.toPS (Qs := Q * T) (by linarith : (0 : ℝ) ≤ T) δ
    (P.toPS.aSharp (Q * T) 1) u ((c : ℝ) / e) hB0 (fun t ht => by
      rw [SaddG_aSharp_eq]
      refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (hblock t ht)).trans ?_)
      rw [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hcard (by positivity))
  have e1 : S (P.rangeZ Q T) (xsH P Q T δ (P.aSharp Q T) u) ((c : ℝ) / e) =
      S (P.toPS.rangeZ (Q * T)) (xsG P.toPS (Q * T) T δ (P.toPS.aSharp (Q * T) 1) u)
        ((c : ℝ) / e) := by
    rw [P.aSharp_eq]; rfl
  rw [e1]
  refine hS.trans ?_
  set M := Q ^ (1 + P.kc) with hMdef
  have hfin : M ^ 2 * Q ^ ((3 : ℝ) / 2 - K * P.ε₃) * M ≤ Q ^ (-A) := by
    rw [hMdef, ← Real.rpow_natCast (Q ^ (1 + P.kc)) 2, ← Real.rpow_mul hQ0.le,
      ← Real.rpow_add hQ0, ← Real.rpow_add hQ0]
    apply Real.rpow_le_rpow_of_exponent_le hQ1.le
    push_cast; nlinarith [le_abs_self A]
  have hC0 : 0 ≤ 3 * C₁ * Q ^ ((3 : ℝ) / 2 - K * P.ε₃) := by positivity
  calc B * T = 3 * C₁ * Q ^ ((3 : ℝ) / 2 - K * P.ε₃) * ((Q * T) ^ 2 * T) := by rw [hBdef]; ring
    _ ≤ 3 * C₁ * Q ^ ((3 : ℝ) / 2 - K * P.ε₃) * (M ^ 2 * M) := by
        gcongr
    _ = 3 * C₁ * (M ^ 2 * Q ^ ((3 : ℝ) / 2 - K * P.ε₃) * M) := by ring
    _ ≤ 3 * C₁ * Q ^ (-A) := by gcongr

end TS

end Families.Hybrid
