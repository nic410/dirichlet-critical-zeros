/-
# Package F: `lem:B1H` (invisibility at height `T = Q^κ`), Lemma 9.11

Through the bridge, `S_χ[a♯](t)` is the families `S_χ[a♯]` at `Q' = QT` with `T' = 1`
(`R_j = ⌊N_j^{1−ε₃}/(QT)⌋`), so `Phase3.C.Schi_aSharp_eq` applies verbatim. The block estimate is the
families `block_bound` with its three inputs separated: the modulus `q ≤ Q`, the height `|t| ≤ 3T`
and the level `R_j`, which enter only through `rq(1+|t|) ≤ 4 Q T R_j ≤ 4 N_j^{1−ε₃}`
(`Phase3.C.block_arith` with `(Q, T) := (Q, T)`). Each block is `≪ √Q N_j^{3/2−Kε₃}` with
`N_j ≥ QT`; there are `≤ 3(QT)²` blocks, so the total is `≪ (QT)^{4−Kε₃} ≤ Q^{−A}` for
`Kε₃ ≥ A + 4`.
-/
import FamiliesH.F.Bridge
import Families.Phase3.C.B1

noncomputable section

open scoped ContDiff Nat ArithmeticFunction.Moebius
open Set ArithmeticFunction

namespace Families.Hybrid

open Families Families.Phase3.C

namespace F

/-- One block at `Q' = QT`, `T' = 1`, for a character of modulus `q ≤ Q` and `|t| ≤ 3T`:
`‖∑_{r ≤ R_j} (μ(r)/φ(r)) ∑_n F_{j,t}(n) c_r(n) χ(n)‖ ≤ √Q C₁ N_j^{3/2 − Kε₃}`. -/
lemma block_boundH (P : HSetup) {K : ℕ} (hK1 : 1 ≤ K) {CF : ℝ} (hCF0 : 0 ≤ CF)
    (hCF : ∀ Q : ℝ, 1 ≤ P.toPS.L Q → ∀ (j : ℕ) (t : ℝ), ∀ k ≤ K, ∀ y : ℝ,
      ‖iteratedDeriv k (Fjt P.toPS Q j t) y‖ ≤
        CF * Real.sqrt (2 / 2 ^ j) * (2 * (1 + |t|) * K / 2 ^ j) ^ k)
    {Q T t : ℝ} (hQ1 : 1 < Q) (hL : 1 ≤ P.toPS.L (Q * T)) (hT1 : 1 ≤ T) (ht : |t| ≤ 3 * T)
    {q : ℕ} [NeZero q] (hq2 : 2 ≤ q) (hqQ : (q : ℝ) ≤ Q) (χ : DirichletCharacter ℂ q)
    (hprim : χ.IsPrimitive) {j : ℕ} (hRj : 1 ≤ P.toPS.Rj (Q * T) 1 j) :
    ‖∑ r ∈ Finset.Icc 1 (P.toPS.Rj (Q * T) 1 j), (((μ r : ℝ) / Nat.totient r : ℝ) : ℂ) *
        ∑ n ∈ P.toPS.range (Q * T), Fjt P.toPS (Q * T) j t n * ramanujan r n * χ n‖ ≤
      Real.sqrt Q * ((K + 3) * CF * Real.sqrt 2 * (2 * K) ^ K) *
        ((2 : ℝ) ^ j) ^ ((3 : ℝ) / 2 - K * P.ε₃) := by
  set C₁ : ℝ := (K + 3) * CF * Real.sqrt 2 * (2 * K) ^ K with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hQ0 : 0 < Q := by linarith
  have hQT1 : 1 < Q * T := by nlinarith
  have hQT1' : 1 ≤ Q * T * 1 := by linarith
  obtain ⟨-, hQTR, hRN⟩ := Rj_facts P.toPS hQT1' hRj
  set N : ℝ := (2 : ℝ) ^ j with hN
  set R : ℕ := P.toPS.Rj (Q * T) 1 j with hR
  have hQTR' : Q * T * R ≤ N ^ (1 - P.ε₃) := by
    have e : Q * T * 1 * (R : ℝ) = Q * T * R := by ring
    rw [← e]; exact hQTR
  have hN1 : 1 ≤ N := one_le_pow₀ (by norm_num)
  have hN0 : 0 < N := by linarith
  have hinner : ∀ r ∈ Finset.Icc 1 R,
      ‖∑ n ∈ P.toPS.range (Q * T), Fjt P.toPS (Q * T) j t n * ramanujan r n * χ n‖ ≤
        Nat.totient r * (Real.sqrt Q * (C₁ * N ^ ((1 : ℝ) / 2 - K * P.ε₃))) := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hrR : r ≤ R := (Finset.mem_Icc.mp hr).2
    have hbound := sum_F_ramanujan_char_le hq2 χ hprim hr1 (Fjt_contDiff P.toPS (Q * T) j t K)
      (fun y => hCF (Q * T) hL j t K le_rfl y) (a := N / 2) (b := 2 * N) (by positivity)
      (by linarith) (fun y hy => Fjt_supp P.toPS (Q * T) j t y hy) (P.toPS.range (Q * T)) (by
        intro n hn
        have hs := Fjt_supp P.toPS (Q * T) j t n hn
        have hnY : (n : ℝ) ≤ P.toPS.Y (Q * T) := by
          by_contra hc
          exact hn (Fjt_eq_zero_of_gt P.toPS hQT1 j t (not_le.mp hc))
        simp only [PrimeSetup.range, Finset.mem_Icc]
        refine ⟨?_, Nat.le_floor hnY⟩
        have : (1 : ℝ) / 2 ≤ n := le_trans (by linarith) hs.1
        have : (0 : ℝ) < n := by linarith
        exact_mod_cast this)
    refine hbound.trans ?_
    have hφ : (0 : ℝ) ≤ Nat.totient r := Nat.cast_nonneg _
    have hrq : ((r * q : ℕ) : ℝ) ≤ R * Q := by
      push_cast
      exact mul_le_mul (by exact_mod_cast hrR) hqQ (Nat.cast_nonneg _) (by positivity)
    have hX := block_arith (t := t) (T := T) hN1 (by linarith) (by linarith) hK1 hCF0
      (Nat.cast_nonneg _) hrq hQTR'
    have hX0 : 0 ≤ (2 * N - N / 2 + K + 1) *
        (CF * Real.sqrt (2 / N) * (2 * (1 + |t|) * K / N) ^ K) * (((r * q : ℕ) : ℝ) / 4) ^ K := by
      have : 0 ≤ 2 * N - N / 2 + K + 1 := by linarith
      positivity
    have hε₃ : P.toPS.ε₃ = P.ε₃ := rfl
    calc (Nat.totient r : ℝ) * Real.sqrt q * ((2 * N - N / 2 + K + 1) *
          (CF * Real.sqrt (2 / N) * (2 * (1 + |t|) * K / N) ^ K) * (((r * q : ℕ) : ℝ) / 4) ^ K)
        ≤ (Nat.totient r * Real.sqrt Q) * (C₁ * N ^ ((1 : ℝ) / 2 - K * P.ε₃)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hqQ) hφ) hX hX0
            (by positivity)
      _ = _ := by ring
  -- sum over `r`
  have hterm : ∀ r ∈ Finset.Icc 1 R, ‖(((μ r : ℝ) / Nat.totient r : ℝ) : ℂ) *
      ∑ n ∈ P.toPS.range (Q * T), Fjt P.toPS (Q * T) j t n * ramanujan r n * χ n‖ ≤
        Real.sqrt Q * (C₁ * N ^ ((1 : ℝ) / 2 - K * P.ε₃)) := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hφ : (0 : ℝ) < Nat.totient r := by exact_mod_cast Nat.totient_pos.mpr hr1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, Nat.abs_cast]
    have hμ : |(μ r : ℝ)| ≤ 1 := by
      have := ArithmeticFunction.abs_moebius_le_one (n := r)
      exact_mod_cast this
    calc |(μ r : ℝ)| / Nat.totient r *
          ‖∑ n ∈ P.toPS.range (Q * T), Fjt P.toPS (Q * T) j t n * ramanujan r n * χ n‖
        ≤ 1 / Nat.totient r *
            (Nat.totient r * (Real.sqrt Q * (C₁ * N ^ ((1 : ℝ) / 2 - K * P.ε₃)))) := by
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
  calc (R : ℝ) * (Real.sqrt Q * (C₁ * N ^ ((1 : ℝ) / 2 - K * P.ε₃)))
      ≤ N * (Real.sqrt Q * (C₁ * N ^ ((1 : ℝ) / 2 - K * P.ε₃))) := by gcongr
    _ = Real.sqrt Q * C₁ * (N * N ^ ((1 : ℝ) / 2 - K * P.ε₃)) := by ring
    _ = Real.sqrt Q * C₁ * N ^ ((3 : ℝ) / 2 - K * P.ε₃) := by rw [h1]

/-- **`lem:B1H`** (invisibility at height `T = Q^κ`), proved. -/
theorem lemB1H_proof : lemB1H_Statement := by
  intro P W A hA
  set K : ℕ := ⌈(A + 4) / P.ε₃⌉₊ + 1 with hKdef
  have hK1 : 1 ≤ K := by omega
  have hKε : A + 4 ≤ K * P.ε₃ := by
    have h1 : (A + 4) / P.ε₃ ≤ ⌈(A + 4) / P.ε₃⌉₊ := Nat.le_ceil _
    have h2 : (⌈(A + 4) / P.ε₃⌉₊ : ℝ) ≤ K := by rw [hKdef]; push_cast; linarith
    have := P.ε₃_pos
    rw [div_le_iff₀ this] at h1
    nlinarith
  obtain ⟨CF, hCF0, hCF⟩ := Fjt_deriv_bound P.toPS K hK1
  set C₁ : ℝ := (K + 3) * CF * Real.sqrt 2 * (2 * K) ^ K with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  refine ⟨3 * C₁, max (Real.exp (1 / P.lam)) (max (Real.exp 1) (2 / W.η)), ?_⟩
  intro Q hQ T hT q χ hχ t ht
  have hQL : Real.exp (1 / P.lam) ≤ Q := le_of_max_le_left hQ
  have hQe : Real.exp 1 ≤ Q := le_of_max_le_left (le_of_max_le_right hQ)
  have hQη : 2 / W.η ≤ Q := le_of_max_le_right (le_of_max_le_right hQ)
  have hQ1 : 1 < Q :=
    lt_of_lt_of_le (by have := Real.add_one_lt_exp (x := 1) one_ne_zero; linarith) hQe
  have hQ0 : 0 < Q := by linarith
  have hT1 : 1 ≤ T := by
    have hl : 1 ≤ Real.log Q := by
      have := Real.log_le_log (Real.exp_pos _) hQe; rwa [Real.log_exp] at this
    exact le_trans (Real.one_le_rpow hl P.a0_pos.le) hT.1
  have hQQT : Q ≤ Q * T := by nlinarith
  have hQT1 : 1 < Q * T := by linarith
  have hQT0 : 0 < Q * T := by linarith
  have hL : 1 ≤ P.toPS.L (Q * T) := one_le_L P.toPS (le_trans hQL hQQT)
  obtain ⟨hq2, hqQ⟩ := family_modulus hQη hχ
  have : NeZero q := ⟨by omega⟩
  have hexp : (3 : ℝ) / 2 - K * P.ε₃ ≤ 0 := by linarith
  have hblock : ∀ j ∈ (P.toPS.blocks (Q * T)).filter (fun j => 1 ≤ P.toPS.Rj (Q * T) 1 j),
      ‖∑ r ∈ Finset.Icc 1 (P.toPS.Rj (Q * T) 1 j), (((μ r : ℝ) / Nat.totient r : ℝ) : ℂ) *
          ∑ n ∈ P.toPS.range (Q * T), Fjt P.toPS (Q * T) j t n * ramanujan r n * χ n‖ ≤
        Real.sqrt Q * C₁ * (Q * T) ^ ((3 : ℝ) / 2 - K * P.ε₃) := by
    intro j hj
    have hRj := (Finset.mem_filter.mp hj).2
    refine (block_boundH P hK1 hCF0 hCF hQ1 hL hT1 ht hq2 hqQ χ hχ.1 hRj).trans ?_
    have hNQ : Q * T ≤ (2 : ℝ) ^ j := by
      have := (Rj_facts P.toPS (by linarith : 1 ≤ Q * T * 1) hRj).1
      linarith
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hQT0 hNQ hexp) (by positivity)
  rw [P.Schi_eq, P.aSharp_eq, Schi_aSharp_eq]
  refine (norm_sum_le _ _).trans ?_
  refine (Finset.sum_le_sum hblock).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : (((P.toPS.blocks (Q * T)).filter (fun j => 1 ≤ P.toPS.Rj (Q * T) 1 j)).card : ℝ) ≤
      3 * (Q * T) ^ 2 :=
    le_trans (by exact_mod_cast Finset.card_filter_le _ _) (card_blocks_le P.toPS hQT1.le)
  have hsq : Real.sqrt Q ≤ (Q * T) ^ ((1 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow hQ0.le hQQT (by norm_num)
  have hfin : (Q * T) ^ 2 * Real.sqrt Q * (Q * T) ^ ((3 : ℝ) / 2 - K * P.ε₃) ≤ Q ^ (-A) := by
    have h1 : (Q * T) ^ 2 * Real.sqrt Q * (Q * T) ^ ((3 : ℝ) / 2 - K * P.ε₃) ≤
        (Q * T) ^ 2 * (Q * T) ^ ((1 : ℝ) / 2) * (Q * T) ^ ((3 : ℝ) / 2 - K * P.ε₃) := by
      gcongr
    refine h1.trans ?_
    rw [← Real.rpow_natCast (Q * T) 2, ← Real.rpow_add hQT0, ← Real.rpow_add hQT0]
    have h2 : (Q * T) ^ ((2 : ℕ) + (1 : ℝ) / 2 + ((3 : ℝ) / 2 - K * P.ε₃)) ≤ (Q * T) ^ (-A) := by
      apply Real.rpow_le_rpow_of_exponent_le hQT1.le
      push_cast; linarith
    refine h2.trans ?_
    exact Real.rpow_le_rpow_of_nonpos hQ0 hQQT (by linarith)
  calc (((P.toPS.blocks (Q * T)).filter (fun j => 1 ≤ P.toPS.Rj (Q * T) 1 j)).card : ℝ) *
        (Real.sqrt Q * C₁ * (Q * T) ^ ((3 : ℝ) / 2 - K * P.ε₃))
      ≤ (3 * (Q * T) ^ 2) * (Real.sqrt Q * C₁ * (Q * T) ^ ((3 : ℝ) / 2 - K * P.ε₃)) := by gcongr
    _ = 3 * C₁ * ((Q * T) ^ 2 * Real.sqrt Q * (Q * T) ^ ((3 : ℝ) / 2 - K * P.ε₃)) := by ring
    _ ≤ 3 * C₁ * Q ^ (-A) := by gcongr

end F

end Families.Hybrid
