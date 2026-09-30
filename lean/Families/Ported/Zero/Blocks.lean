/-
# Zero side: `lem:blocks` and `prop:perchi` for the interior matrix

For a primitive `χ` mod `q > 1`, `T > 0` and a vector-valued `u : ℂ → ι → ℂ` with
`u(z̄) = conj u(z)` and `‖u(t)‖² ≤ c` on `ℝ` (with `u = (p_k)_{k∈K_J}`, `c = aL²`: `pk_conj` and
Bessel), the interior matrix `Â = c⁻¹ A_χ`, `A_χ = ∑_{γ ∈ (T,2T]} m_ρ u(z_ρ) u(z_ρ)ᵀ` (`Aint`),
satisfies, with `𝓜 = 4 tr Â − ‖Â‖_F²`,

`𝓜 − 2N_χ ≤ N^s_{0,χ}`, `𝓜 − 2N_χ ≤ N^*_{0,χ}`, `(𝓜 − N_χ)/2 ≤ N_{d,χ}`   (`perchi_interior`).

The block decomposition (`lem:blocks`) and the rank–trace inequality (`lem:ranktrace`, in the
multiplicity-aware form `rank_trace_mult_k_le`) are `zeta23`'s (`Zeta23.ZeroSide`,
`Zeta23.ZeroSide.RankTraceMult`), instantiated here for the window `I = (T, 2T]` of `L(s,χ)`.
-/
import Families.Ported.Zero.Bridge
import Zeta23.ZeroSide.Mult

noncomputable section

open scoped BigOperators ComplexConjugate
open Complex Set Matrix Finset RHLinalg

namespace Families.Ported.Zero

open Zeta23 Zeta23.ThmE Zeta23.ZeroSide Zeta23.ZeroSide.RankTraceMult

section Abstract

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]

/-- The rank–trace bound before subtracting `N`: `4 tr Â − ‖Â‖² ≤ 3 s₁ + 4 s₂ + 4 p`
(the first half of the proof of `zeta23`'s `ZeroBlockData.mult_two`). -/
theorem blockData_M_le (D : ZeroBlockData ι d) (Pr : D.PairReps) {c : ℝ} (hc : 0 < c)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c) :
    4 * rtrace (D.blockP c + D.blockQ c) - frobSq (D.blockP c + D.blockQ c) ≤
      3 * (D.s₁ : ℝ) + 4 * (D.s₂ : ℝ) + 4 * (Pr.p : ℝ) := by
  classical
  have hR := rank_trace_mult_k_le (𝕜 := ℂ) (fun z => D.mhat_nonneg z) (D.vhat c)
    (D.xsq_vhat_le hc hPois) (D.blockQ_isHermitian c) (D.posIndex_blockQ_le Pr hc) (c := 2)
    (by norm_num)
  rw [← D.blockP_eq_Pmat hc] at hR
  have hk : ∑ z : D.onLine, kc 2 (D.mhat z) = 3 * (D.s₁ : ℝ) + 4 * (D.s₂ : ℝ) := by
    have := sum_kc_two_nat (fun z : D.onLine => D.m z) (fun z => D.one_le_m z)
    simp only [ZeroBlockData.mhat] at this ⊢
    rw [this, D.card_sub_filter (fun n => n = 1), D.card_sub_filter (fun n => 2 ≤ n),
      D.card_onLine_m_eq_one]
    have h2 : (D.onLine.filter (fun z => 2 ≤ D.m z)).card = D.s₂ := by
      unfold ZeroBlockData.s₂ ZeroBlockData.S₂ ZeroBlockData.onLine; rw [Finset.filter_filter]
    rw [h2]
  rw [hk] at hR
  norm_num at hR
  linarith

end Abstract

section Concrete

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

lemma reflect_mem_zerosI (hq : 1 < q) (hprim : χ.IsPrimitive) {T : ℝ} (hT : 0 ≤ T) {ρ : ℂ}
    (h : ρ ∈ zerosI χ T) : reflect ρ ∈ zerosI χ T := by
  rw [zerosI_eq hq hprim hT] at h ⊢
  refine ⟨(LSeam_of hq hprim).reflect_zero ρ h.1, ?_, ?_⟩ <;> rw [Zeta23.reflect_im]
  · exact h.2.1
  · exact h.2.2

lemma mult_pos_of_mem_zerosI (hq : 1 < q) (hprim : χ.IsPrimitive) {T : ℝ} (hT : 0 ≤ T) {ρ : ℂ}
    (h : ρ ∈ zerosI χ T) : 1 ≤ mult χ ρ := by
  rw [zerosI_eq hq hprim hT] at h
  rw [mult_eq]
  exact (LSeam_of hq hprim).one_le_mult ρ h.1

lemma mult_reflect_of_mem_zerosI (hq : 1 < q) (hprim : χ.IsPrimitive) {T : ℝ} (hT : 0 ≤ T) {ρ : ℂ}
    (h : ρ ∈ zerosI χ T) : mult χ (reflect ρ) = mult χ ρ := by
  rw [zerosI_eq hq hprim hT] at h
  rw [mult_eq, mult_eq]
  exact (LSeam_of hq hprim).mult_reflect ρ h.1

lemma zOf_reflect (ρ : ℂ) : zOf (reflect ρ) = conj (zOf ρ) := gammaOf_reflect ρ

variable (hq : 1 < q) (hprim : χ.IsPrimitive) {T : ℝ} (hT : 0 < T)

/-- The zeros with ordinate in `I = (T, 2T]`, as a `Finset`. -/
def zerosFin : Finset ℂ := (zerosI_finite hq hprim hT.le).toFinset

lemma mem_zerosFin {ρ : ℂ} : ρ ∈ zerosFin hq hprim hT ↔ ρ ∈ zerosI χ T :=
  Set.Finite.mem_toFinset _

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ℂ → ι → ℂ)
  (hconj : ∀ z, u (conj z) = star (u z))

/-- The block data of the zeros of `L(s,χ)` with ordinate in `(T, 2T]` (`lem:blocks`). -/
def blockDataI : ZeroBlockData (zerosFin hq hprim hT) ι where
  m z := mult χ z
  one_le_m z := mult_pos_of_mem_zerosI hq hprim hT.le ((mem_zerosFin hq hprim hT).mp z.2)
  v z := u (zOf z)
  σ z := ⟨reflect z, (mem_zerosFin hq hprim hT).mpr
    (reflect_mem_zerosI hq hprim hT.le ((mem_zerosFin hq hprim hT).mp z.2))⟩
  σ_invol _ := Subtype.ext (Zeta23.reflect_reflect _)
  m_σ z := mult_reflect_of_mem_zerosI hq hprim hT.le ((mem_zerosFin hq hprim hT).mp z.2)
  v_σ z := by
    change u (zOf (reflect z)) = star (u (zOf z))
    rw [zOf_reflect, hconj]

lemma blockDataI_σ_eq_iff (z : zerosFin hq hprim hT) :
    (blockDataI hq hprim hT u hconj).σ z = z ↔ (z : ℂ).re = 1 / 2 := by
  rw [Subtype.ext_iff]
  exact reflect_eq_self_iff _

/-- Representatives of the off-line pairs: the member with `β > 1/2`. -/
def pairRepsI : (blockDataI hq hprim hT u hconj).PairReps where
  R := Finset.univ.filter (fun z : zerosFin hq hprim hT => 1 / 2 < (z : ℂ).re)
  off z hz h := by
    rw [blockDataI_σ_eq_iff] at h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
    linarith
  σ_not_mem z hz h := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz h
    change 1 / 2 < (reflect (z : ℂ)).re at h
    rw [Zeta23.reflect_re] at h
    linarith
  cover z hz := by
    rw [ne_eq, blockDataI_σ_eq_iff] at hz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change 1 / 2 < (z : ℂ).re ∨ 1 / 2 < (reflect (z : ℂ)).re
    rw [Zeta23.reflect_re]
    rcases lt_or_gt_of_ne hz with h | h
    · right; linarith
    · left; exact h

lemma Aint_eq_blockA : Aint u χ T = (blockDataI hq hprim hT u hconj).blockA := by
  unfold Aint ZeroBlockData.blockA
  rw [finsum_mem_eq_finite_toFinset_sum _ (zerosI_finite hq hprim hT.le), ← Finset.sum_coe_sort]
  rfl

lemma Nchi_eq_Ncount : Nchi χ T = (blockDataI hq hprim hT u hconj).Ncount := by
  unfold Nchi ZeroBlockData.Ncount
  rw [finsum_mem_eq_finite_toFinset_sum _ (zerosI_finite hq hprim hT.le), ← Finset.sum_coe_sort]
  rfl

lemma Ndchi_eq_card : Ndchi χ T = Fintype.card (zerosFin hq hprim hT) := by
  unfold Ndchi
  rw [Fintype.card_coe, ← Set.ncard_coe_finset]
  congr 1
  ext ρ
  simp [mem_zerosFin]

lemma card_subtype_filter (p : ℂ → Prop) [DecidablePred p] :
    #(Finset.univ.filter (fun z : zerosFin hq hprim hT => p z)) =
      Set.ncard {ρ | ρ ∈ zerosI χ T ∧ p ρ} := by
  have h1 : #(Finset.univ.filter (fun z : zerosFin hq hprim hT => p z)) =
      #((zerosFin hq hprim hT).filter p) := by
    convert card_filter_coe (zerosFin hq hprim hT) p (fun z => p z) (fun _ => Iff.rfl)
  rw [h1, ← Set.ncard_coe_finset]
  congr 1
  ext ρ
  simp [mem_zerosFin]

lemma Ns0chi_eq_s₁ : Ns0chi χ T = (blockDataI hq hprim hT u hconj).s₁ := by
  classical
  unfold Ns0chi ZeroBlockData.s₁ ZeroBlockData.S₁
  rw [show (Finset.univ.filter fun z : zerosFin hq hprim hT =>
      (blockDataI hq hprim hT u hconj).σ z = z ∧ (blockDataI hq hprim hT u hconj).m z = 1) =
      Finset.univ.filter (fun z : zerosFin hq hprim hT => (z : ℂ).re = 1 / 2 ∧ mult χ z = 1) from by
    ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, blockDataI_σ_eq_iff]; rfl]
  rw [card_subtype_filter hq hprim hT (fun ρ => ρ.re = 1 / 2 ∧ mult χ ρ = 1)]

lemma Nstar0chi_eq_onLine :
    Nstar0chi χ T = #(blockDataI hq hprim hT u hconj).onLine := by
  classical
  unfold Nstar0chi ZeroBlockData.onLine
  rw [show (Finset.univ.filter fun z : zerosFin hq hprim hT =>
      (blockDataI hq hprim hT u hconj).σ z = z) =
      Finset.univ.filter (fun z : zerosFin hq hprim hT => (z : ℂ).re = 1 / 2) from by
    ext z; simp only [Finset.mem_filter, Finset.mem_univ, true_and, blockDataI_σ_eq_iff]]
  rw [card_subtype_filter hq hprim hT (fun ρ => ρ.re = 1 / 2)]

include hq hprim hT hconj in
/-- **`prop:perchi` for the interior matrix** (paper §3). -/
theorem perchi_interior {c : ℝ} (hc : 0 < c) (hbes : ∀ t : ℝ, ∑ i, ‖u (t : ℂ) i‖ ^ 2 ≤ c) :
    let Ah : Matrix ι ι ℂ := ((c⁻¹ : ℝ) : ℂ) • Aint u χ T
    let M : ℝ := 4 * rtrace Ah - frobSq Ah
    M - 2 * (Nchi χ T : ℝ) ≤ Ns0chi χ T ∧ M - 2 * (Nchi χ T : ℝ) ≤ Nstar0chi χ T ∧
      (M - Nchi χ T) / 2 ≤ Ndchi χ T := by
  intro Ah M
  set D := blockDataI hq hprim hT u hconj
  set Pr := pairRepsI hq hprim hT u hconj
  have hAh : Ah = D.blockP c + D.blockQ c := by
    simp only [Ah, D.blockP_add_blockQ, Aint_eq_blockA hq hprim hT u hconj]
    rfl
  have hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c := by
    intro z hz
    have hre : (z : ℂ).re = 1 / 2 := (blockDataI_σ_eq_iff hq hprim hT u hconj z).mp
      ((D.mem_onLine).mp hz)
    change ∑ k, ‖u (zOf z) k‖ ^ 2 ≤ c
    rw [zOf_eq_gammaOf, gammaOf_of_re_eq_half hre]
    exact hbes _
  have hM : M ≤ 3 * (D.s₁ : ℝ) + 4 * (D.s₂ : ℝ) + 4 * (Pr.p : ℝ) := by
    simp only [M, hAh]
    exact blockData_M_le D Pr hc hPois
  have hN : (D.s₁ : ℝ) + 2 * D.s₂ + 2 * Pr.p ≤ D.Ncount := by
    exact_mod_cast D.s₁_add_two_s₂_add_two_p_le_Ncount Pr
  have hcard : (Fintype.card (zerosFin hq hprim hT) : ℝ) = D.s₁ + D.s₂ + 2 * Pr.p := by
    exact_mod_cast D.card_eq Pr
  have hon : (#D.onLine : ℝ) = D.s₁ + D.s₂ := by exact_mod_cast D.card_onLine
  rw [Nchi_eq_Ncount hq hprim hT u hconj, Ns0chi_eq_s₁ hq hprim hT u hconj,
    Nstar0chi_eq_onLine hq hprim hT u hconj, Ndchi_eq_card hq hprim hT]
  have hs2 : (0 : ℝ) ≤ D.s₂ := Nat.cast_nonneg _
  have hp : (0 : ℝ) ≤ Pr.p := Nat.cast_nonneg _
  refine ⟨by linarith, ?_, ?_⟩
  · rw [hon]; linarith
  · rw [hcard]; linarith

end Concrete

end Families.Ported.Zero
