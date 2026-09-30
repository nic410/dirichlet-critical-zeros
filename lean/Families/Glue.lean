/-
Glue: combining the proved pieces into the paper's statements, and proving implications between
stated analytic results (some of them not proved in this project).

* `lemM2` — `lem:M2` exactly as in the paper (constant 4), fully proved.
* `lemmaS_rough` — `lem:S` last claim: `y^*Δy ≤ y^*T^♮y` on `Q`-rough vectors.
* `lemmaS_lambda_of_dual` — `lem:S` duality bound, from `lem:dual`.
* `corLmultA_of` — `cor:LmultA` from `lem:A`, `lem:gauss` (proved) and `lem:WH`.
* `LS_of_corLmultA`, `thmGauss_general_of` — `thm:gauss` (general `w`) from `thm:conditional`.
* `pC_CG_ge_of` — `p(C_G) ≥ 0.885912` from the certificate, `lem:pLip` and `C_G ≤ 1.2688` (`C_G > 1` is proved).
-/
import Families.Toeplitz
import Families.Schur
import Families.LemmaS
import Families.Main
import Families.Certificate.Numerics
import Families.Constants
import Families.Weights

noncomputable section

open scoped BigOperators ComplexConjugate ArithmeticFunction.Moebius ENNReal
open ArithmeticFunction Finset MeasureTheory Filter Topology

namespace Families

/-! ### Elementary properties of `Δ` -/

lemma Weight.omega_nonneg (W : Weight) (Q : ℝ) (q : ℕ) : 0 ≤ W.omega Q q := by
  unfold Weight.omega
  exact div_nonneg (mul_nonneg (W.nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

lemma Weight.H_nonneg (W : Weight) (Q : ℝ) : 0 ≤ W.H Q :=
  Finset.sum_nonneg fun q _ => mul_nonneg (W.omega_nonneg Q q) (Nat.cast_nonneg _)

/-- `Δ(m,n) = \overline{Δ(n,m)}`. -/
lemma Δ_swap (W : Weight) (Q : ℝ) (n m : ℤ) : Δ W Q m n = conj (Δ W Q n m) := by
  unfold Δ
  rw [map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_mul, Complex.conj_ofReal, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [map_mul, Complex.conj_conj, mul_comm]

lemma Δ_norm_symm (W : Weight) (Q : ℝ) (n m : ℤ) : ‖Δ W Q n m‖ = ‖Δ W Q m n‖ := by
  rw [Δ_swap W Q n m, Complex.norm_conj]

/-- `|Δ(n,n)| ≤ H`. -/
lemma Δ_diag_norm_le (W : Weight) (Q : ℝ) (n : ℤ) : ‖Δ W Q n n‖ ≤ W.H Q := by
  rw [Δ_diag]
  refine (norm_sum_le _ _).trans ?_
  unfold Weight.H
  refine Finset.sum_le_sum fun q _ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (W.omega_nonneg Q q)]
  refine mul_le_mul_of_nonneg_left ?_ (W.omega_nonneg Q q)
  split_ifs
  · simp
  · simp

/-- **`lem:M2`, arithmetic bound.** `|Δ(n,m)| ≤ 2 w_max Q τ(|n−m|)` for `n ≠ m`
(from the orthogonality formula; `2` in place of the paper's `1.95`). -/
theorem Δ_offdiag_le (W : Weight) (Q : ℝ) (hQ : 0 < Q) (n m : ℤ) (hnm : n ≠ m) :
    ‖Δ W Q n m‖ ≤ 2 * W.wmax * Q * (Nat.divisors (n - m).natAbs).card := by
  rw [Δ_eq_general]
  refine offdiag_bound W Q hQ (n - m) (sub_ne_zero.mpr hnm) _ fun q => ?_
  split_ifs
  · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => ?_)
    rw [norm_mul, Complex.norm_natCast]
    have : ‖((μ (q / d) : ℤ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    calc (Nat.totient d : ℝ) * ‖((μ (q / d) : ℤ) : ℂ)‖ ≤ (Nat.totient d : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
      _ = _ := mul_one _
  · rw [norm_zero]
    exact Finset.sum_nonneg fun d _ => Nat.cast_nonneg _

/-- **`lem:M2` (short intervals), as in the paper.** For every interval `I` of `K ≥ 1` integers and
`x ∈ ℂ^I`: `x^*Δx ≤ (H + 4 w_max Q K(1 + log K)) ‖x‖²`. -/
theorem lemM2 (W : Weight) (Q : ℝ) (hQ : 0 < Q) (N₀ : ℤ) (K : ℕ) (hK : 1 ≤ K) (x : ℤ → ℂ) :
    famForm W Q (intervalZ N₀ K) x ≤
      (W.H Q + 4 * W.wmax * Q * K * (1 + Real.log K)) * normSq (intervalZ N₀ K) x := by
  have hB : 0 ≤ 2 * W.wmax * Q := by
    have := W.wmax_nonneg; positivity
  have h := short_interval_abstract N₀ K hK (Δ W Q) (Δ_norm_symm W Q) (W.H Q) (2 * W.wmax * Q) hB
    (fun n _ => Δ_diag_norm_le W Q n) (fun n _ m _ hnm => Δ_offdiag_le W Q hQ n m hnm) x
  have heq := famForm_eq_sum W Q (intervalZ N₀ K) x
  have h1 : famForm W Q (intervalZ N₀ K) x ≤
      ‖∑ n ∈ intervalZ N₀ K, ∑ m ∈ intervalZ N₀ K, x n * conj (x m) * Δ W Q n m‖ := by
    rw [← heq, Complex.norm_real, Real.norm_eq_abs]
    exact le_abs_self _
  calc famForm W Q (intervalZ N₀ K) x ≤ _ := h1
    _ ≤ _ := h
    _ = _ := by ring_nf

/-! ### Lemma S on `Q`-rough vectors -/

/-- **`lem:S`, last claim.** `y^*Δy ≤ y^*T^+y ≤ y^*T^♮y` for `y` supported on `Q`-rough integers
(here written with the forms `∫|S_y|² dμ`). -/
theorem lemmaS_rough (W : Weight) (Q : ℝ) (hQ : 0 < Q) (I : Finset ℤ) (hI : ∀ n ∈ I, IsRough Q n)
    (y : ℤ → ℂ) :
    famForm W Q I y ≤ levelForm (levels Q) (aΩplus W Q) I y ∧
      famForm W Q I y ≤ levelForm (levels Q) (aNat W Q) I y := by
  rw [famForm_eq_levelForm_Ω W Q I hI y]
  have h := lemmaS_forms W Q hQ I y
  exact ⟨h.1, h.1.trans h.2⟩

/-! ### `cor:LmultA` from `lem:A`, `lem:gauss`, `lem:WH` -/

/-- **`cor:LmultA`** follows from `lem:A`, the (proved) Gauss transfer and `W/H → C_G`
(the latter with `C_G > 0`). -/
theorem corLmultA_of (hA : lemA_Statement) (hWH : lemWH_ratio_Statement) (hCG : 0 < CG) :
    corLmultA_Statement := by
  intro ε hε hε1 W δ hδ
  set R := (Rw W).toReal with hR
  set B := W.Vw / W.cw with hBdef
  obtain ⟨Q₀, hQ₀⟩ := hA ε hε hε1 B
  -- ϑ_Q → 0
  have hθ : Tendsto (fun Q : ℝ => 30 * (R + B) * Q ^ (-ε / 4) * Real.log Q) atTop (𝓝 0) := by
    have h1 : Tendsto (fun Q : ℝ => Real.log Q * Q ^ (-ε / 4)) atTop (𝓝 0) := by
      have := (isLittleO_log_rpow_atTop (r := ε / 4) (by linarith)).tendsto_div_nhds_zero
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with Q hQ
      rw [neg_div, Real.rpow_neg hQ.le, div_eq_mul_inv]
    have := h1.const_mul (30 * (R + B))
    simp only [mul_zero] at this
    refine this.congr' (Eventually.of_forall fun Q => ?_)
    ring
  -- (R + ϑ_Q) (W/H) → R C_G = C_w
  have hlim : Tendsto (fun Q : ℝ => (R + 30 * (R + B) * Q ^ (-ε / 4) * Real.log Q) *
      (W.Wm Q / W.H Q)) atTop (𝓝 (Cw W)) := by
    have := (hθ.const_add R).mul (hWH W)
    simp only [add_zero] at this
    unfold Cw
    rw [mul_comm CG R]
    exact this
  have hev := (hlim.eventually (gt_mem_nhds (by linarith : Cw W < Cw W + δ)))
  have hHpos : ∀ᶠ Q in atTop, 0 < W.H Q := by
    have := (hWH W).eventually (lt_mem_nhds (by linarith : CG / 2 < CG))
    filter_upwards [this] with Q hQ
    rcases (W.H_nonneg Q).lt_or_eq with h | h
    · exact h
    · rw [← h, div_zero] at hQ; linarith
  obtain ⟨Q₁, hQ₁⟩ := (hev.and hHpos).exists_forall_of_atTop
  refine ⟨max Q₀ Q₁, fun Q hQ K hK => ?_⟩
  intro N₀ _ _ x
  have hQ0 : Q₀ ≤ Q := le_of_max_le_left hQ
  obtain ⟨hlt, hH⟩ := hQ₁ Q (le_of_max_le_right hQ)
  have hfar := hQ₀ W le_rfl Q hQ0 N₀ K hK x
  have hgauss := gauss_transfer W Q (intervalZ N₀ K) x
  have hx : 0 ≤ normSq (intervalZ N₀ K) x := Finset.sum_nonneg fun _ _ => sq_nonneg _
  calc famForm W Q (intervalZ N₀ K) x ≤ fareyForm W Q (intervalZ N₀ K) x := hgauss
    _ ≤ (R + 30 * (R + B) * Q ^ (-ε / 4) * Real.log Q) * W.Wm Q *
          normSq (intervalZ N₀ K) x := hfar
    _ = ((R + 30 * (R + B) * Q ^ (-ε / 4) * Real.log Q) * (W.Wm Q / W.H Q)) * W.H Q *
          normSq (intervalZ N₀ K) x := by
        field_simp
    _ ≤ (Cw W + δ) * W.H Q * normSq (intervalZ N₀ K) x := by
        gcongr

/-! ### `thm:gauss` (general weights) from `thm:conditional` -/

/-- `cor:LmultA` gives `LS(C_w)`. -/
theorem LS_of_corLmultA (h : corLmultA_Statement) (W : Weight) : LS W (Cw W) := by
  intro ε hε δ hδ
  set ε' := min ε (1 / 2) with hε'
  have hε'pos : 0 < ε' := lt_min hε (by norm_num)
  have hε'1 : ε' < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨Q₀, hQ₀⟩ := h ε' hε'pos hε'1 W δ hδ
  refine ⟨max Q₀ 1, fun Q hQ K hK => hQ₀ Q (le_of_max_le_left hQ) K ?_⟩
  have hQ1 : 1 ≤ Q := le_of_max_le_right hQ
  exact hK.trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith [min_le_left ε (1 / 2)]))

/-- **`thm:gauss`, general `w`**, from `thm:conditional` and `cor:LmultA`:
`liminf inf_T N^s_0/N ≥ p(C_G R_w)` (and the `N^*_0`, `N_d` versions). -/
theorem thmGauss_general_of (hcond : thmConditional_Statement) (hcor : corLmultA_Statement)
    (W : Weight) (a0 A0 : ℝ) (ha0 : 0 < a0) (hA0 : a0 < A0) :
    ProportionsAtLeast W a0 A0 (pC (Cw W)) :=
  hcond W (Cw W) a0 A0 ha0 hA0 (LS_of_corLmultA hcor W)

/-- **`cor:LmultA`** from `lem:A` and `lem:WH` alone (`C_G > 0` is proved in `Families.Constants`). -/
theorem corLmultA_of' (hA : lemA_Statement) (hWH : lemWH_ratio_Statement) :
    corLmultA_Statement :=
  corLmultA_of hA hWH CG_pos

/-- **`thm:gauss`, general `w`**, from `thm:conditional`, `lem:A` and `lem:WH`. -/
theorem thmGauss_general_of' (hcond : thmConditional_Statement) (hA : lemA_Statement)
    (hWH : lemWH_ratio_Statement) (W : Weight) (a0 A0 : ℝ) (ha0 : 0 < a0) (hA0 : a0 < A0) :
    ProportionsAtLeast W a0 A0 (pC (Cw W)) :=
  thmGauss_general_of hcond (corLmultA_of' hA hWH) W a0 A0 ha0 hA0

/-- `p(C_G) ≥ 0.885912`, from the certificate `p(1.2688) ≥ 0.885912`, monotonicity (`lem:pLip`) and
`1 ≤ C_G ≤ 1.2688`. -/
theorem pC_CG_ge_of (hLip : lemPLip_Statement) (h2 : CG ≤ 1.2688) :
    (0.885912 : ℝ) ≤ pC CG := by
  have hmono := (hLip CG (12688 / 10000) one_lt_CG.le (by norm_num at h2 ⊢; linarith)).1
  exact pC_12688_ge.trans hmono

end Families

namespace Families

/-! ### Certified constants entering `thm:main` and `thm:gauss` -/

/-- `thm:main`, constant part: `p(1) ≥ 0.932282` (`prop:cert`, proved). -/
theorem thmMain_constant : (0.932282 : ℝ) ≤ pC 1 := pC_one_ge

/-- `thm:gauss`, constant part: `p(C_G) ≥ 0.885912`, given only the numerical fact `C_G ≤ 1.2688`
(`lem:pLip`, the certificate and `C_G > 1` are proved). -/
theorem thmGauss_constant_of (h : CG ≤ 1.2688) : (0.885912 : ℝ) ≤ pC CG :=
  pC_CG_ge_of lemPLip h

/-- `thm:gauss`, constant part, unconditional: `p(C_G) ≥ 0.885912`. -/
theorem thmGauss_constant : (0.885912 : ℝ) ≤ pC CG := thmGauss_constant_of CG_le

/-! ### Lemma S, duality part, from `lem:dual` -/

/-- Distinct reduced fractions `c/e ∈ [0,1)` have distinct fractional parts. -/
lemma reduced_frac_inj {e e' c c' : ℕ} (he : c ∈ reduced e) (he' : c' ∈ reduced e')
    (h : Int.fract ((c : ℝ) / e) = Int.fract ((c' : ℝ) / e')) : e = e' ∧ c = c' := by
  simp only [reduced, Finset.mem_filter, Finset.mem_range] at he he'
  have e0 : (0 : ℝ) < e := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le c) he.1)
  have e0' : (0 : ℝ) < e' := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le c') he'.1)
  have f1 : Int.fract ((c : ℝ) / e) = (c : ℝ) / e := by
    rw [Int.fract_eq_self]
    exact ⟨by positivity, (div_lt_one e0).mpr (by exact_mod_cast he.1)⟩
  have f2 : Int.fract ((c' : ℝ) / e') = (c' : ℝ) / e' := by
    rw [Int.fract_eq_self]
    exact ⟨by positivity, (div_lt_one e0').mpr (by exact_mod_cast he'.1)⟩
  rw [f1, f2, div_eq_div_iff e0.ne' e0'.ne'] at h
  have hN : c * e' = c' * e := by exact_mod_cast h
  have h1 : e ∣ e' := by
    have : e ∣ c * e' := ⟨c', by rw [hN]; ring⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm he.2) this)
  have h2 : e' ∣ e := by
    have : e' ∣ c' * e := ⟨c, by rw [← hN]; ring⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm he'.2) this)
  have hee : e = e' := Nat.dvd_antisymm h1 h2
  subst hee
  refine ⟨rfl, ?_⟩
  have : 0 < e := by exact_mod_cast e0
  exact Nat.eq_of_mul_eq_mul_right this hN

/-- `μ^♮ ≥ 0` levelwise (from `lem:Omega`(b)). -/
lemma aNat_nonneg (W : Weight) (Q : ℝ) (hQ : 0 < Q) (e : ℕ) (he : e ∈ levels Q) :
    0 ≤ aNat W Q e := by
  have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
  have := lemOmega_b W Q hQ e he1
  unfold aNat
  have := le_max_left (-Ωlev W Q e) 0
  linarith

/-- `k_ς ≥ 0`. -/
lemma kper_nonneg {ς : ℝ} (hς : 0 < ς) (ξ : ℝ) : 0 ≤ kper ς ξ :=
  tsum_nonneg fun _ => mul_nonneg (inv_nonneg.mpr hς.le) (le_max_right _ _)

/-- `(μ^♮ * k_ς)(θ) ≥ 0` (`μ^♮ ≥ 0` by `lem:Omega`(b)). -/
lemma natConv_nonneg (W : Weight) (Q : ℝ) (hQ : 0 < Q) {ς : ℝ} (hς : 0 < ς) (θ : ℝ) :
    0 ≤ natConv W Q ς θ :=
  Finset.sum_nonneg fun e he =>
    mul_nonneg (aNat_nonneg W Q hQ e he) (Finset.sum_nonneg fun _ _ => kper_nonneg hς _)

/-- **`lem:S`, duality bound, from `lem:dual`.** If `I` contains `K ≥ 1` integers, `0 < κ ≤ 1/4`,
`ς = κ/K`, and `(μ^♮ * k_ς)(θ) ≤ M` for all `θ`, then `y^*T^♮y ≤ (1+κ²) M ‖y‖²`
(i.e. `λ_max(T^♮_I) ≤ (1+κ²) sup_θ (μ^♮ * k_ς)(θ)`; `λ_max(T^+_I) ≤ λ_max(T^♮_I)` is `lemmaS`). -/
theorem lemmaS_lambda_of_dual (hdual : lemDual_Statement) (W : Weight) (Q : ℝ) (hQ : 0 < Q)
    (N₀ : ℤ) (K : ℕ) (hK : 1 ≤ K) (κ : ℝ) (hκ : 0 < κ) (hκ' : κ ≤ 1 / 4) (M : ℝ)
    (hM : ∀ θ, natConv W Q (κ / K) θ ≤ M) (y : ℤ → ℂ) :
    levelForm (levels Q) (aNat W Q) (intervalZ N₀ K) y ≤
      (1 + κ ^ 2) * M * normSq (intervalZ N₀ K) y := by
  classical
  -- the atoms of μ^♮ with positive mass
  set pts : Finset (ℕ × ℕ) :=
    ((levels Q).sigma fun e => reduced e).map (Equiv.sigmaEquivProd ℕ ℕ).toEmbedding |>.filter
      (fun s => 0 < aNat W Q s.1) with hpts
  set θ : ℕ × ℕ → ℝ := fun s => (s.2 : ℝ) / s.1
  set a : ℕ × ℕ → ℝ := fun s => aNat W Q s.1
  have mem_pts : ∀ s, s ∈ pts ↔ s.1 ∈ levels Q ∧ s.2 ∈ reduced s.1 ∧ 0 < aNat W Q s.1 := by
    intro s
    rw [hpts, Finset.mem_filter, Finset.mem_map]
    constructor
    · rintro ⟨⟨⟨e, c⟩, hec, hs⟩, hpos⟩
      rw [Finset.mem_sigma] at hec
      simp only [Equiv.coe_toEmbedding, Equiv.sigmaEquivProd_apply] at hs
      subst hs
      exact ⟨hec.1, hec.2, hpos⟩
    · rintro ⟨he, hc, hpos⟩
      exact ⟨⟨⟨s.1, s.2⟩, Finset.mem_sigma.mpr ⟨he, hc⟩, rfl⟩, hpos⟩
  -- rewrite a sum over levels and residues as a sum over positive atoms
  have resum : ∀ F : ℕ → ℕ → ℝ,
      ∑ e ∈ levels Q, aNat W Q e * ∑ c ∈ reduced e, F e c = ∑ s ∈ pts, a s * F s.1 s.2 := by
    intro F
    have h1 : ∑ e ∈ levels Q, aNat W Q e * ∑ c ∈ reduced e, F e c =
        ∑ s ∈ ((levels Q).sigma fun e => reduced e), aNat W Q s.1 * F s.1 s.2 := by
      rw [Finset.sum_sigma]
      exact Finset.sum_congr rfl fun e _ => by rw [Finset.mul_sum]
    rw [h1, hpts, Finset.sum_filter, Finset.sum_map]
    refine Finset.sum_congr rfl fun s hs => ?_
    simp only [Equiv.coe_toEmbedding, Equiv.sigmaEquivProd_apply]
    split_ifs with hpos
    · rfl
    · have hnn := aNat_nonneg W Q hQ s.1 (Finset.mem_sigma.mp hs).1
      have : aNat W Q s.1 = 0 := le_antisymm (not_lt.mp hpos) hnn
      simp [this]
  have hform : levelForm (levels Q) (aNat W Q) (intervalZ N₀ K) y =
      ∑ s ∈ pts, a s * ‖S (intervalZ N₀ K) y (θ s)‖ ^ 2 := by
    unfold levelForm
    exact resum (fun e c => ‖S (intervalZ N₀ K) y ((c : ℝ) / e)‖ ^ 2)
  rw [hform]
  have hM0 : 0 ≤ M :=
    (natConv_nonneg W Q hQ (ς := κ / K) (div_pos hκ (Nat.cast_pos.mpr hK)) 0).trans (hM 0)
  refine hdual (ℕ × ℕ) pts θ a (fun s hs => ((mem_pts s).mp hs).2.2) ?_ N₀ K hK κ hκ hκ' M hM0 ?_ y
  · intro i hi j hj hij h
    obtain ⟨_, hi2, _⟩ := (mem_pts i).mp hi
    obtain ⟨_, hj2, _⟩ := (mem_pts j).mp hj
    obtain ⟨h1, h2⟩ := reduced_frac_inj hi2 hj2 h
    exact hij (Prod.ext h1 h2)
  · intro i _
    have := hM (θ i)
    unfold natConv at this
    rw [resum (fun e c => kper (κ / K) (θ i - (c : ℝ) / e))] at this
    exact this

end Families
