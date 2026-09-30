/-
The positivity certificate (main.tex §3): `lem:ranktrace`, the block structure of `lem:blocks`
(at the level of explicit rank-one / off-line blocks), `prop:perchi`, and the ω-weighted family sum.

The rank–trace inequality itself is imported from `zeta23` (anthropics/formal-math)
(`Zeta23.LinAlg.RankTrace`, `RHLinalg.rank_trace_ineq_two`; Apache-2.0, © Anthropic PBC),
as are subadditivity of the positive index (`RHLinalg.posIndex_add_le`) and Sylvester's
characterisation (`RHLinalg.posIndex_eq_max_finrank_posDefOn`).
-/
import Zeta23.LinAlg.RankTrace
import Zeta23.LinAlg.Inertia

noncomputable section

open Matrix Finset RHLinalg
open scoped ComplexOrder

namespace Families.Cert

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`lem:ranktrace`** (main.tex; AF26 Lemma 3.2 / HY26 Lemma 8.2). For `P ⪰ 0` with `rank P ≤ r`
and Hermitian `R` with `n₊(R) ≤ b`: `‖P+R‖_F² ≥ 2 tr P − r + 4 tr R − 4b`.
This is `RHLinalg.rank_trace_ineq_two` of the `zeta23` dependency, restated. -/
theorem ranktrace {P R : Matrix ι ι ℂ} (hP : P.PosSemidef) (hR : R.IsHermitian) {r b : ℕ}
    (hr : P.rank ≤ r) (hb : posIndex hR ≤ b) :
    2 * rtrace P - r + 4 * rtrace R - 4 * (b : ℝ) ≤ frobSq (P + R) := by
  have := rank_trace_ineq_two hP hR hr hb
  linarith

/-! ### Positive index of the blocks -/

omit [DecidableEq ι] in
lemma hermForm_neg (N : Matrix ι ι ℂ) (x : ι → ℂ) : hermForm (-N) x = -hermForm N x := by
  simp [hermForm, neg_mulVec, dotProduct_neg]

/-- A negative semidefinite matrix has no positive eigenvalue. -/
lemma posIndex_neg_of_posSemidef {N : Matrix ι ι ℂ} (hN : N.PosSemidef) (h : (-N).IsHermitian) :
    posIndex h = 0 := by
  obtain ⟨V, hV, hdim⟩ := posIndex_eq_max_finrank_posDefOn h
  by_contra hne
  have hVne : V ≠ ⊥ := by
    intro hbot
    apply hne
    rw [← hdim, Submodule.finrank_eq_zero.mpr hbot]
  obtain ⟨x, hxV, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVne
  have h1 := hV x hxV hx0
  rw [hermForm_neg] at h1
  have h2 := hermForm_nonneg_of_posSemidef hN x
  linarith

/-- A PSD matrix has `n₊ = rank`. -/
lemma posIndex_psd_le_rank {M : Matrix ι ι ℂ} (hM : M.PosSemidef) (h : M.IsHermitian) :
    posIndex h = M.rank := posIndex_eq_rank_of_posSemidef hM

omit [Fintype ι] [DecidableEq ι] in
/-- Hermitian finite sums. -/
lemma isHermitian_sum' {κ : Type*} (s : Finset κ) (M : κ → Matrix ι ι ℂ)
    (hM : ∀ k ∈ s, (M k).IsHermitian) : (∑ k ∈ s, M k).IsHermitian :=
  isSelfAdjoint_sum s hM

/-- Subadditivity of `n₊` over finite sums (iterating `RHLinalg.posIndex_add_le`). -/
lemma posIndex_sum_le {κ : Type*} (s : Finset κ) (M : κ → Matrix ι ι ℂ)
    (hM : ∀ k, (M k).IsHermitian) :
    ∀ hs : (∑ k ∈ s, M k).IsHermitian, posIndex hs ≤ ∑ k ∈ s, posIndex (hM k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro hs
    have h0 : (∑ k ∈ (∅ : Finset κ), M k).PosSemidef := by simpa using PosSemidef.zero
    rw [posIndex_psd_le_rank h0 hs]
    simp
  | insert k s hk ih =>
    intro hs
    have hs' : (∑ j ∈ s, M j).IsHermitian := isHermitian_sum' s M (fun j _ => hM j)
    have hsplit : (∑ j ∈ insert k s, M j) = M k + ∑ j ∈ s, M j := Finset.sum_insert hk
    have key := posIndex_add_le (hM k) hs'
    have e : posIndex hs = posIndex ((hM k).add hs') := by
      unfold posIndex
      congr 1
      simp only [hsplit]
    rw [e, Finset.sum_insert hk]
    exact key.trans (Nat.add_le_add_left (ih hs') _)

/-- `n₊(c · v v^*) ≤ 1` for `c ≥ 0`. -/
lemma posIndex_rankOne_smul (c : ℝ) (hc : 0 ≤ c) (v : ι → ℂ)
    (h : ((c : ℂ) • vecMulVec v (star v)).IsHermitian) : posIndex h ≤ 1 := by
  have hpsd : ((c : ℂ) • vecMulVec v (star v)).PosSemidef :=
    (posSemidef_vecMulVec_self_star v).smul (by exact_mod_cast hc)
  rw [posIndex_psd_le_rank hpsd h]
  have : (c : ℂ) • vecMulVec v (star v) = vecMulVec ((c : ℂ) • v) (star v) := by
    ext i j; simp [vecMulVec_apply, mul_assoc]
  rw [this]
  exact rank_vecMulVec_le _ _

/-- The off-line orbit block `c (a b^* + b a^*)` (`lem:blocks`(b), `c ≥ 0`) has at most one
positive eigenvalue: it equals `(c/2)(a+b)(a+b)^* − (c/2)(a−b)(a−b)^*`. -/
lemma posIndex_offline_le (c : ℝ) (hc : 0 ≤ c) (a b : ι → ℂ)
    (h : ((c : ℂ) • (vecMulVec a (star b) + vecMulVec b (star a))).IsHermitian) :
    posIndex h ≤ 1 := by
  set P₁ : Matrix ι ι ℂ := ((c / 2 : ℝ) : ℂ) • vecMulVec (a + b) (star (a + b))
  set N₁ : Matrix ι ι ℂ := ((c / 2 : ℝ) : ℂ) • vecMulVec (a - b) (star (a - b))
  have hN₁ : N₁.PosSemidef :=
    (posSemidef_vecMulVec_self_star _).smul (by exact_mod_cast (by linarith : (0:ℝ) ≤ c / 2))
  have hP₁ : P₁.PosSemidef :=
    (posSemidef_vecMulVec_self_star _).smul (by exact_mod_cast (by linarith : (0:ℝ) ≤ c / 2))
  have heq : (c : ℂ) • (vecMulVec a (star b) + vecMulVec b (star a)) = P₁ + -N₁ := by
    ext i j
    simp only [P₁, N₁, Matrix.smul_apply, Matrix.add_apply, Matrix.neg_apply, vecMulVec_apply,
      Pi.add_apply, Pi.sub_apply, Pi.star_apply, star_add, star_sub, smul_eq_mul]
    push_cast
    ring
  have hsum := posIndex_add_le hP₁.isHermitian hN₁.isHermitian.neg
  have e : posIndex h = posIndex (hP₁.isHermitian.add hN₁.isHermitian.neg) := by
    unfold posIndex; congr 1; simp only [heq]
  rw [e]
  refine hsum.trans ?_
  rw [posIndex_neg_of_posSemidef hN₁ _]
  have := posIndex_rankOne_smul (c / 2) (by linarith) (a + b) hP₁.isHermitian
  omega

/-! ### Per-character zero data (`lem:blocks`) and the certificate (`prop:perchi`) -/

/-- The zeros of one `L(s,χ)` with ordinate in `I`, in normalised Gabor coordinates
(`u(z) = (p_k(z))_{k ∈ K_J} / (√a L)`), grouped as in `lem:blocks`:
* `s1` simple zeros on the critical line, with vectors `u i`, `‖u i‖² ≤ 1` (`lem:gabor`);
* `s2` distinct multiple zeros on the line, vectors `v j`, multiplicities `mult j ≥ 2`;
* `p` off-line orbits `{ρ, 1-\bar ρ}`, vectors `a l = u(z_ρ)`, `b l = u(\bar z_ρ)`, multiplicity `n l ≥ 1`. -/
structure BlockData (ι : Type*) where
  s1 : ℕ
  s2 : ℕ
  p : ℕ
  u : Fin s1 → ι → ℂ
  v : Fin s2 → ι → ℂ
  mult : Fin s2 → ℕ
  a : Fin p → ι → ℂ
  b : Fin p → ι → ℂ
  n : Fin p → ℕ
  hmult : ∀ j, 2 ≤ mult j
  hn : ∀ l, 1 ≤ n l

namespace BlockData

variable (D : BlockData ι)

/-- `P`: the blocks of the simple critical zeros. -/
def P : Matrix ι ι ℂ := ∑ i, vecMulVec (D.u i) (star (D.u i))

/-- One multiple-critical-zero block `m v v^*`. -/
def Rmult (j : Fin D.s2) : Matrix ι ι ℂ := ((D.mult j : ℝ) : ℂ) • vecMulVec (D.v j) (star (D.v j))

/-- One off-line orbit block `n (a b^* + b a^*)`. -/
def Roff (l : Fin D.p) : Matrix ι ι ℂ :=
  ((D.n l : ℝ) : ℂ) • (vecMulVec (D.a l) (star (D.b l)) + vecMulVec (D.b l) (star (D.a l)))

/-- `R`: all other blocks with ordinate in `I`. -/
def R : Matrix ι ι ℂ := ∑ j, D.Rmult j + ∑ l, D.Roff l

/-- `Â_χ = P + R` (interior part of the normalised Gabor matrix). -/
def A : Matrix ι ι ℂ := D.P + D.R

/-- `N_χ` (zeros with multiplicity). -/
def N : ℕ := D.s1 + ∑ j, D.mult j + 2 * ∑ l, D.n l
/-- `N^s_{0,χ}`: simple zeros on the line. -/
def Ns0 : ℕ := D.s1
/-- `N^*_{0,χ}`: distinct zeros on the line. -/
def Nstar0 : ℕ := D.s1 + D.s2
/-- `N_{d,χ}`: distinct zeros. -/
def Nd : ℕ := D.s1 + D.s2 + 2 * D.p

/-- `𝓜_χ = 4 tr Â_χ − ‖Â_χ‖_F²`. -/
def M : ℝ := 4 * rtrace D.A - frobSq D.A

lemma P_eq : D.P = (Matrix.of fun x i => D.u i x) * (Matrix.of fun x i => D.u i x)ᴴ := by
  ext x y
  simp [P, mul_apply, vecMulVec_apply, Matrix.sum_apply]

lemma P_posSemidef : D.P.PosSemidef := by
  rw [P_eq]; exact posSemidef_self_mul_conjTranspose _

lemma P_rank_le : D.P.rank ≤ D.s1 := by
  rw [P_eq]
  calc _ ≤ (Matrix.of fun x (i : Fin D.s1) => D.u i x).rank := rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin D.s1) := rank_le_card_width _
    _ = D.s1 := Fintype.card_fin _

lemma rtrace_P (hu : ∀ i, ∑ x, ‖D.u i x‖ ^ 2 ≤ 1) : rtrace D.P ≤ D.s1 := by
  have : rtrace D.P = ∑ i, ∑ x, ‖D.u i x‖ ^ 2 := by
    unfold rtrace P
    rw [trace_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [trace, map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [diag_apply, vecMulVec_apply, Pi.star_apply, Complex.star_def, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    exact Complex.ofReal_re _
  rw [this]
  calc ∑ i, ∑ x, ‖D.u i x‖ ^ 2 ≤ ∑ _i : Fin D.s1, (1 : ℝ) := Finset.sum_le_sum fun i _ => hu i
    _ = D.s1 := by simp

lemma Rmult_isHermitian (j : Fin D.s2) : (D.Rmult j).IsHermitian :=
  ((posSemidef_vecMulVec_self_star (D.v j)).smul
    (by exact_mod_cast (Nat.cast_nonneg (D.mult j) : (0:ℝ) ≤ D.mult j))).isHermitian

lemma Roff_isHermitian (l : Fin D.p) : (D.Roff l).IsHermitian := by
  unfold Roff
  refine IsHermitian.ext fun i j => ?_
  simp only [Matrix.smul_apply, Matrix.add_apply, vecMulVec_apply, Pi.star_apply, smul_eq_mul,
    star_mul', star_add, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
  ring

lemma R_isHermitian : D.R.IsHermitian :=
  (isHermitian_sum' _ _ fun j _ => D.Rmult_isHermitian j).add
    (isHermitian_sum' _ _ fun l _ => D.Roff_isHermitian l)

lemma posIndex_R_le : posIndex D.R_isHermitian ≤ D.s2 + D.p := by
  have h1 := posIndex_sum_le (univ : Finset (Fin D.s2)) D.Rmult D.Rmult_isHermitian
    (isHermitian_sum' _ _ fun j _ => D.Rmult_isHermitian j)
  have h2 := posIndex_sum_le (univ : Finset (Fin D.p)) D.Roff D.Roff_isHermitian
    (isHermitian_sum' _ _ fun l _ => D.Roff_isHermitian l)
  have h3 := posIndex_add_le
    (isHermitian_sum' (univ : Finset (Fin D.s2)) D.Rmult fun j _ => D.Rmult_isHermitian j)
    (isHermitian_sum' (univ : Finset (Fin D.p)) D.Roff fun l _ => D.Roff_isHermitian l)
  have hb1 : ∑ j, posIndex (D.Rmult_isHermitian j) ≤ D.s2 := by
    calc ∑ j, posIndex (D.Rmult_isHermitian j) ≤ ∑ _j : Fin D.s2, 1 :=
          Finset.sum_le_sum fun j _ =>
            posIndex_rankOne_smul (D.mult j) (Nat.cast_nonneg _) (D.v j) _
      _ = D.s2 := by simp
  have hb2 : ∑ l, posIndex (D.Roff_isHermitian l) ≤ D.p := by
    calc ∑ l, posIndex (D.Roff_isHermitian l) ≤ ∑ _l : Fin D.p, 1 :=
          Finset.sum_le_sum fun l _ =>
            posIndex_offline_le (D.n l) (Nat.cast_nonneg _) (D.a l) (D.b l) _
      _ = D.p := by simp
  calc posIndex D.R_isHermitian
      = posIndex ((isHermitian_sum' (univ : Finset (Fin D.s2)) D.Rmult
            fun j _ => D.Rmult_isHermitian j).add
          (isHermitian_sum' (univ : Finset (Fin D.p)) D.Roff fun l _ => D.Roff_isHermitian l)) :=
        rfl
    _ ≤ _ := h3
    _ ≤ D.s2 + D.p := Nat.add_le_add (h1.trans hb1) (h2.trans hb2)

/-- `𝓜_χ ≤ 3 s₁ + 4 s₂ + 4p` (proof of `prop:perchi`, via the rank–trace inequality). -/
theorem M_le (hu : ∀ i, ∑ x, ‖D.u i x‖ ^ 2 ≤ 1) :
    D.M ≤ 3 * D.s1 + 4 * D.s2 + 4 * D.p := by
  have hrt := ranktrace D.P_posSemidef D.R_isHermitian D.P_rank_le D.posIndex_R_le
  have htr := D.rtrace_P hu
  have hA : rtrace D.A = rtrace D.P + rtrace D.R := rtrace_add _ _
  unfold M
  rw [hA]
  unfold A at *
  push_cast at hrt
  linarith

lemma N_ge : (D.s1 : ℝ) + 2 * D.s2 + 2 * D.p ≤ D.N := by
  unfold N
  have h1 : 2 * D.s2 ≤ ∑ j, D.mult j := by
    calc 2 * D.s2 = ∑ _j : Fin D.s2, 2 := by simp [mul_comm]
      _ ≤ ∑ j, D.mult j := Finset.sum_le_sum fun j _ => D.hmult j
  have h2 : D.p ≤ ∑ l, D.n l := by
    calc D.p = ∑ _l : Fin D.p, 1 := by simp
      _ ≤ ∑ l, D.n l := Finset.sum_le_sum fun l _ => D.hn l
  have : D.s1 + 2 * D.s2 + 2 * D.p ≤ D.s1 + ∑ j, D.mult j + 2 * ∑ l, D.n l := by omega
  exact_mod_cast this

/-- **`prop:perchi`** (per-character certificate, [HY26, Prop. 8.3]):
`N^s_{0,χ} ≥ 𝓜_χ − 2N_χ`, `N^*_{0,χ} ≥ 𝓜_χ − 2N_χ`, `N_{d,χ} ≥ (𝓜_χ − N_χ)/2`. -/
theorem perchi (hu : ∀ i, ∑ x, ‖D.u i x‖ ^ 2 ≤ 1) :
    D.M - 2 * D.N ≤ D.Ns0 ∧ D.M - 2 * D.N ≤ D.Nstar0 ∧ (D.M - D.N) / 2 ≤ D.Nd := by
  have hM := D.M_le hu
  have hN := D.N_ge
  refine ⟨?_, ?_, ?_⟩
  · unfold Ns0; linarith
  · unfold Nstar0; push_cast; linarith
  · unfold Nd; push_cast; linarith

end BlockData

/-- **The ω-weighted family sum** of `prop:perchi` (main.tex §3, `rem:upper`): for nonnegative
weights `ω_χ`, `N^s_0 ≥ ∑ ω_χ 𝓜_χ − 2N`, `N^*_0 ≥ ∑ ω_χ 𝓜_χ − 2N`, `N_d ≥ (∑ ω_χ 𝓜_χ − N)/2`,
where `N^s_0 = ∑ ω_χ N^s_{0,χ}` etc. -/
theorem perchi_weighted {κ : Type*} (F : Finset κ) (ω : κ → ℝ) (hω : ∀ k ∈ F, 0 ≤ ω k)
    (D : κ → BlockData ι) (hu : ∀ k ∈ F, ∀ i, ∑ x, ‖(D k).u i x‖ ^ 2 ≤ 1) :
    ∑ k ∈ F, ω k * (D k).M - 2 * ∑ k ∈ F, ω k * (D k).N ≤ ∑ k ∈ F, ω k * (D k).Ns0 ∧
    ∑ k ∈ F, ω k * (D k).M - 2 * ∑ k ∈ F, ω k * (D k).N ≤ ∑ k ∈ F, ω k * (D k).Nstar0 ∧
    (∑ k ∈ F, ω k * (D k).M - ∑ k ∈ F, ω k * (D k).N) / 2 ≤ ∑ k ∈ F, ω k * (D k).Nd := by
  have key : ∀ k ∈ F, _ := fun k hk => (D k).perchi (hu k hk)
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun k hk => ?_
    have := mul_le_mul_of_nonneg_left (key k hk).1 (hω k hk)
    linarith
  · rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun k hk => ?_
    have := mul_le_mul_of_nonneg_left (key k hk).2.1 (hω k hk)
    linarith
  · rw [← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_le_sum fun k hk => ?_
    have := mul_le_mul_of_nonneg_left (key k hk).2.2 (hω k hk)
    linarith

end Families.Cert
