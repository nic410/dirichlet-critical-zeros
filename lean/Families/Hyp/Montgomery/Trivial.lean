/-
# Montgomery 1969 density: the trivial zero count

* `Lfun_eq_LFunction` — `Lfun χ = χ.LFunction` for `q ≠ 0`.
* `Ndens_set_finite` — the zero set counted by `Ndens` is finite (`σ > 0`, `χ` primitive).
* `Ndens_le_trivial` — `N(σ,T,χ) ≤ K (T+1) log(q(T+3))` for every primitive `χ` (including `q = 1`,
  where `Lfun χ = ζ`), from `zeta23`'s local counts `localCountChi_uniform_proof` and
  `zeta_local_zero_count`.
-/
import Families.Hyp.Montgomery.Defs
import Zeta23.ThmE.LocalCountChi
import Zeta23.ThmE.SeamL
import Zeta23.RvM.LocalCount

noncomputable section

open scoped BigOperators
open Finset

namespace Families.Hyp.Montgomery

theorem Lfun_eq_LFunction {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Lfun χ = χ.LFunction := by
  funext s
  rw [Lfun, dif_neg (NeZero.ne q)]

/-- Zeros of `Lfun χ` (χ primitive, `q ≥ 1`) have real part `< 1`. -/
lemma mont_re_lt_one {q : ℕ} (χ : DirichletCharacter ℂ q) (hq : 1 ≤ q) (hχ : χ.IsPrimitive)
    {ρ : ℂ} (h : Lfun χ ρ = 0) : ρ.re < 1 := by
  have : NeZero q := ⟨by omega⟩
  rw [Lfun_eq_LFunction] at h
  by_contra hre
  push Not at hre
  rcases Nat.lt_or_ge 1 q with hq1 | hq1
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ
      (Or.inl (Zeta23.ThmE.ne_one_of_primitive hq1 hχ)) hre h
  · obtain rfl : q = 1 := by omega
    rw [DirichletCharacter.LFunction_modOne_eq] at h
    exact riemannZeta_ne_zero_of_one_le_re hre h

/-- The unit window `t < Im ρ ≤ t + 1` of nontrivial zeros of `Lfun χ`. -/
def montWin {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ) : Set ℂ :=
  {ρ | Lfun χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ t < ρ.im ∧ ρ.im ≤ t + 1}

/-- Unit windows: finiteness and the local count (`zeta23`), uniformly in primitive `χ`, `q ≥ 1`. -/
lemma montWin_count : ∃ A : ℝ, 1 ≤ A ∧ ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), 1 ≤ q →
    χ.IsPrimitive → ∀ t : ℝ, (montWin χ t).Finite ∧
      ((∑ᶠ ρ ∈ montWin χ t, mult χ ρ : ℕ) : ℝ) ≤ A * Real.log (q * (|t| + 3)) := by
  obtain ⟨A₁, hA₁, h₁⟩ := Zeta23.ThmE.localCountChi_uniform_proof
  obtain ⟨A₂, hA₂, h₂⟩ := Zeta23.RvM.zeta_local_zero_count
  refine ⟨max A₁ A₂, le_max_of_le_left hA₁, fun q χ hq hχ t => ?_⟩
  have : NeZero q := ⟨by omega⟩
  have hlog : 0 ≤ Real.log (q * (|t| + 3)) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    nlinarith [abs_nonneg t]
  rcases Nat.lt_or_ge 1 q with hq1 | hq1
  · have hW : montWin χ t = Zeta23.ThmE.zerosInL χ t (t + 1) := by
      ext ρ
      simp only [montWin, Zeta23.ThmE.zerosInL, Zeta23.ThmE.IsNontrivialZeroL, Lfun_eq_LFunction,
        Set.mem_ofPred_eq, and_assoc]
    have hm : mult χ = Zeta23.ThmE.zeroMultL χ := by
      funext ρ
      simp only [mult, Zeta23.ThmE.zeroMultL, analyticOrderNatAt, Lfun_eq_LFunction]
    refine ⟨?_, ?_⟩
    · rw [hW]
      exact Zeta23.ThmE.LSeam_finite_window hq1 hχ t (t + 1)
    · rw [hW, hm]
      exact (h₁ q χ hq1 hχ t).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hlog)
  · obtain rfl : q = 1 := by omega
    have hW : montWin χ t = Zeta23.zerosIn t (t + 1) := by
      ext ρ
      simp only [montWin, Zeta23.zerosIn, Zeta23.IsNontrivialZero, Lfun_eq_LFunction,
        DirichletCharacter.LFunction_modOne_eq, Set.mem_ofPred_eq, and_assoc]
    have hm : mult χ = Zeta23.zeroMult := by
      funext ρ
      simp only [mult, Zeta23.zeroMult, analyticOrderNatAt, Lfun_eq_LFunction,
        DirichletCharacter.LFunction_modOne_eq]
    refine ⟨?_, ?_⟩
    · rw [hW]
      exact Zeta23.zetaZeroConfig.finite_window t (t + 1)
    · rw [hW, hm]
      have := h₂ t
      simp only [Nat.cast_one, one_mul]
      exact this.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (by simpa using hlog))

/-- Covering a set of points with `|Im ρ| ≤ T` by the unit windows `W (j - 1)`, `|j| ≤ ⌈T⌉`
(`ρ` lies in the window `W (⌈Im ρ⌉ - 1)`). -/
lemma mont_finsum_le_windows {S : Set ℂ} (W : ℝ → Set ℂ) (m : ℂ → ℕ) {T : ℝ}
    (hS : ∀ ρ ∈ S, |ρ.im| ≤ T ∧ ρ ∈ W ((⌈ρ.im⌉ : ℝ) - 1)) (hW : ∀ t, (W t).Finite) :
    S.Finite ∧ ∑ᶠ ρ ∈ S, m ρ ≤
      ∑ j ∈ Finset.Icc (-(⌈T⌉₊ : ℤ)) ⌈T⌉₊, ∑ᶠ ρ ∈ W ((j : ℝ) - 1), m ρ := by
  set N := ⌈T⌉₊ with hNdef
  have hj : ∀ ρ ∈ S, ⌈ρ.im⌉ ∈ Finset.Icc (-(N : ℤ)) N := by
    intro ρ hρ
    obtain ⟨habs, -⟩ := hS ρ hρ
    have h1 := abs_le.mp habs
    have hN : T ≤ N := Nat.le_ceil T
    rw [Finset.mem_Icc]
    constructor
    · have h2 := Int.le_ceil ρ.im
      have : ((-(N : ℤ) : ℤ) : ℝ) ≤ (⌈ρ.im⌉ : ℝ) := by push_cast; linarith
      exact_mod_cast this
    · exact Int.ceil_le.mpr (by push_cast; linarith)
  have hfin : S.Finite := by
    refine (Set.Finite.biUnion (Finset.Icc (-(N : ℤ)) N).finite_toSet
      fun j _ => hW ((j : ℝ) - 1)).subset ?_
    intro ρ hρ
    exact Set.mem_biUnion (Finset.mem_coe.mpr (hj ρ hρ)) (hS ρ hρ).2
  refine ⟨hfin, ?_⟩
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin,
    ← Finset.sum_fiberwise_of_maps_to (g := fun ρ => ⌈ρ.im⌉) (t := Finset.Icc (-(N : ℤ)) N)
      (fun ρ hρ => hj ρ (hfin.mem_toFinset.mp hρ))]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [finsum_mem_eq_finite_toFinset_sum _ (hW _)]
  refine Finset.sum_le_sum_of_subset ?_
  intro ρ hρ
  rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hρ
  rw [Set.Finite.mem_toFinset]
  have := (hS ρ hρ.1).2
  rwa [hρ.2] at this

/-- Points of the `Ndens` zero set lie in the window `montWin χ (⌈Im ρ⌉ - 1)`. -/
lemma mont_Ndens_mem_win {q : ℕ} (χ : DirichletCharacter ℂ q) (hq : 1 ≤ q) (hχ : χ.IsPrimitive)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ) :
    ∀ ρ ∈ {ρ : ℂ | Lfun χ ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T},
      |ρ.im| ≤ T ∧ ρ ∈ montWin χ ((⌈ρ.im⌉ : ℝ) - 1) := by
  rintro ρ ⟨h0, hre, him⟩
  refine ⟨him, h0, by linarith, mont_re_lt_one χ hq hχ h0, ?_, ?_⟩
  · linarith [Int.ceil_lt_add_one ρ.im]
  · linarith [Int.le_ceil ρ.im]

theorem Ndens_set_finite {q : ℕ} (χ : DirichletCharacter ℂ q) (hq : 1 ≤ q) (hχ : χ.IsPrimitive)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ) :
    {ρ : ℂ | Lfun χ ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T}.Finite := by
  obtain ⟨A, -, hA⟩ := montWin_count
  exact (mont_finsum_le_windows (montWin χ) (mult χ) (mont_Ndens_mem_win χ hq hχ hσ T)
    (fun t => (hA q χ hq hχ t).1)).1

theorem Ndens_le_trivial : ∃ K : ℝ, 0 < K ∧ ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), 1 ≤ q →
    χ.IsPrimitive → ∀ σ T : ℝ, 0 < σ → 0 ≤ T →
    (Ndens χ σ T : ℝ) ≤ K * (T + 1) * Real.log (q * (T + 3)) := by
  obtain ⟨A, hA1, hA⟩ := montWin_count
  refine ⟨6 * A, by positivity, fun q χ hq hχ σ T hσ hT => ?_⟩
  have hcov := (mont_finsum_le_windows (montWin χ) (mult χ) (mont_Ndens_mem_win χ hq hχ hσ T)
    (fun t => (hA q χ hq hχ t).1)).2
  set N := ⌈T⌉₊ with hNdef
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hL0 : 0 ≤ Real.log (q * (T + 3)) := Real.log_nonneg (by nlinarith)
  -- each window is bounded by `2 A log(q(T+3))`
  have hwin : ∀ j ∈ Finset.Icc (-(N : ℤ)) N,
      ((∑ᶠ ρ ∈ montWin χ ((j : ℝ) - 1), mult χ ρ : ℕ) : ℝ) ≤ 2 * A * Real.log (q * (T + 3)) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hNT : (N : ℝ) < T + 1 := Nat.ceil_lt_add_one hT
    have hjl : (-(N : ℤ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj.1
    have hju : (j : ℝ) ≤ (N : ℤ) := by exact_mod_cast hj.2
    push_cast at hjl hju
    have habs : |(j : ℝ) - 1| ≤ T + 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hpos : 0 < (q : ℝ) * (|(j : ℝ) - 1| + 3) := by positivity
    have h1 : Real.log (q * (|(j : ℝ) - 1| + 3)) ≤ Real.log (q * (T + 5)) :=
      Real.log_le_log hpos (by nlinarith)
    have h2 : Real.log (q * (T + 5)) ≤ 2 * Real.log (q * (T + 3)) := by
      rw [← Real.log_rpow (by positivity)]
      refine Real.log_le_log (by positivity) ?_
      rw [show ((q : ℝ) * (T + 3)) ^ (2 : ℝ) = ((q : ℝ) * (T + 3)) * ((q : ℝ) * (T + 3)) by
        rw [Real.rpow_two]; ring]
      have hqT : 0 ≤ (q : ℝ) * T := mul_nonneg (by positivity) hT
      have hx : (3 : ℝ) ≤ q * (T + 3) := by nlinarith
      have := mul_le_mul_of_nonneg_left hx (by positivity : (0 : ℝ) ≤ q * (T + 3))
      nlinarith
    calc ((∑ᶠ ρ ∈ montWin χ ((j : ℝ) - 1), mult χ ρ : ℕ) : ℝ)
        ≤ A * Real.log (q * (|(j : ℝ) - 1| + 3)) := (hA q χ hq hχ _).2
      _ ≤ A * (2 * Real.log (q * (T + 3))) :=
          mul_le_mul_of_nonneg_left (h1.trans h2) (by linarith)
      _ = 2 * A * Real.log (q * (T + 3)) := by ring
  have hcard : ((Finset.Icc (-(N : ℤ)) N).card : ℝ) ≤ 3 * (T + 1) := by
    rw [Int.card_Icc, show (N : ℤ) + 1 - -(N : ℤ) = ((2 * N + 1 : ℕ) : ℤ) by push_cast; ring,
      Int.toNat_natCast]
    have hNT : (N : ℝ) < T + 1 := Nat.ceil_lt_add_one hT
    push_cast
    linarith
  calc (Ndens χ σ T : ℝ)
      ≤ ((∑ j ∈ Finset.Icc (-(N : ℤ)) N, ∑ᶠ ρ ∈ montWin χ ((j : ℝ) - 1), mult χ ρ : ℕ) : ℝ) := by
        exact_mod_cast hcov
    _ = ∑ j ∈ Finset.Icc (-(N : ℤ)) N,
          ((∑ᶠ ρ ∈ montWin χ ((j : ℝ) - 1), mult χ ρ : ℕ) : ℝ) := by push_cast; rfl
    _ ≤ ∑ j ∈ Finset.Icc (-(N : ℤ)) N, 2 * A * Real.log (q * (T + 3)) := Finset.sum_le_sum hwin
    _ = ((Finset.Icc (-(N : ℤ)) N).card : ℝ) * (2 * A * Real.log (q * (T + 3))) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (3 * (T + 1)) * (2 * A * Real.log (q * (T + 3))) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 6 * A * (T + 1) * Real.log (q * (T + 3)) := by ring

end Families.Hyp.Montgomery
