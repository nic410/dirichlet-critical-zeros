/-
# Zero side: the family trace, lower bound (`prop:trace`)

`trace_lower`: uniformly for `ℓ^{a₀} ≤ T ≤ ℓ^{A₀}`,
`∑_χ ω_χ tr Ĝ_χ ≥ (1 − 2θ − δ) N` for `Q ≥ Q₀(δ)`,
where `tr Ĝ_χ = ∑_{k ∈ K_J} Re G_{χ,kk} / (a L²)`.

Only this lower bound is used by `prop:zero`. Main term: per lattice point (`TraceChar.lean`);
prime part: `lem:firstmoment` (`FirstMoment.lean`) and `λ < 2`; comparison with `N`: `lem:RvM` and
`H ≍ Q²` (`lem:WH`).
-/
import Families.Ported.Zero.TraceChar
import Families.Ported.Zero.RvM
import Families.Ported.Zero.Exterior
import Families.Assembly

noncomputable section

open scoped BigOperators ComplexConjugate
open Complex Set MeasureTheory Filter Topology

namespace Families.Ported.Zero

open Zeta23 Zeta23.ThmE

/-- Uniform facts on `μ_χ` (`zeta23` `gammaFactsChi_uniform`): `μ_χ ≥ −1`, and Stirling from below
for `t ≥ 1`. -/
lemma mu_facts : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), 1 ≤ q →
    (∀ t : ℝ, -1 ≤ muChi χ t) ∧
    (∀ t : ℝ, 1 ≤ t → 1 / (2 * Real.pi) * (Real.log q + Real.log t - Real.log (2 * Real.pi)) - C ≤
      muChi χ t) := by
  obtain ⟨C, hC⟩ := GammaChi.gammaFactsChi_uniform
  refine ⟨|C|, abs_nonneg _, fun q χ hq => ?_⟩
  have hκ : parity χ ≤ 1 := by unfold parity; split <;> omega
  have hb := hC (parity χ) q hκ hq
  refine ⟨fun t => ?_, fun t ht => ?_⟩
  · have h1 := hb.mu_zero_le t
    have h2 := hb.neg_one_lt_mu_zero
    unfold muChi; linarith
  · have hst := hb.stirling t (by rw [abs_of_pos (by linarith)]; exact ht)
    rw [abs_of_pos (by linarith : (0:ℝ) < t)] at hst
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
    have ht0 : 0 < t := by linarith
    have hlog : Real.log (q * t / (2 * Real.pi)) =
        Real.log q + Real.log t - Real.log (2 * Real.pi) := by
      rw [Real.log_div (by positivity) (by positivity), Real.log_mul hq0.ne' ht0.ne']
    rw [hlog] at hst
    have hCt : C / t ^ 2 ≤ |C| := by
      calc C / t ^ 2 ≤ |C| / t ^ 2 := div_le_div_of_nonneg_right (le_abs_self C) (by positivity)
        _ ≤ |C| := div_le_self (abs_nonneg C) (by nlinarith)
    have := (abs_le.mp hst).1
    unfold muChi
    linarith

variable (P : PrimeSetup)

/-- `|K_J| ≥ (1 − 2θ) T L/(2π) − 1`. -/
lemma card_KJ_ge {Q : ℝ} (hQ : 1 < Q) (T τ₀ : ℝ) :
    (1 - 2 * P.θ) * T * P.L Q / (2 * Real.pi) - 1 ≤ ((P.KJ Q T τ₀).card : ℝ) := by
  unfold PrimeSetup.KJ
  rw [Int.card_Icc]
  set a := ((1 + P.θ) * T - τ₀) * P.L Q / (2 * Real.pi)
  set b := ((2 - P.θ) * T - τ₀) * P.L Q / (2 * Real.pi)
  have hba : b - a = (1 - 2 * P.θ) * T * P.L Q / (2 * Real.pi) := by
    simp only [a, b]; field_simp; ring
  have h1 : (((⌊b⌋ + 1 - ⌈a⌉ : ℤ) : ℝ)) ≤ (((⌊b⌋ + 1 - ⌈a⌉).toNat : ℕ) : ℝ) := by
    exact_mod_cast Int.self_le_toNat _
  have h2 : b - 1 < (⌊b⌋ : ℝ) := by have := Int.sub_one_lt_floor b; exact_mod_cast this
  have h3 : (⌈a⌉ : ℝ) < a + 1 := Int.ceil_lt_add_one a
  push_cast at h1
  linarith

/-- Pure algebra for `main_norm_lower`. -/
lemma trace_algebra {a lam ℓ T θ c D S π' : ℝ} (hπ : 0 < π') (ha : 0 < a) (hlam : 0 < lam)
    (hℓ : 1 ≤ ℓ) (hT : 1 ≤ T) (hθ0 : 0 < θ) (hθ1 : 0 < 1 - 2 * θ) (hc : 0 ≤ c)
    (hℓc : 0 ≤ ℓ - c - 1) (hD : (1 - 2 * θ) * T * (lam * ℓ) / π' - 1 ≤ D)
    (hS : D * (a * (lam * ℓ) * (ℓ - c - 1)) ≤ S) :
    (1 - 2 * θ) * T * ℓ / π' - ((c + 1) / π' + 1 / lam) * T ≤ S / (a * (lam * ℓ) ^ 2) := by
  have hL : 0 < lam * ℓ := by positivity
  set L := lam * ℓ with hLd
  have h1 : D * (ℓ - c - 1) / L ≤ S / (a * L ^ 2) := by
    have := div_le_div_of_nonneg_right hS (by positivity : (0:ℝ) ≤ a * L ^ 2)
    have e : D * (a * L * (ℓ - c - 1)) / (a * L ^ 2) = D * (ℓ - c - 1) / L := by
      field_simp
    linarith
  have h2 : ((1 - 2 * θ) * T * L / π' - 1) * (ℓ - c - 1) / L ≤ D * (ℓ - c - 1) / L :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hD hℓc) hL.le
  have h3 : ((1 - 2 * θ) * T * L / π' - 1) * (ℓ - c - 1) / L =
      (1 - 2 * θ) * T * (ℓ - c - 1) / π' - (ℓ - c - 1) / L := by
    field_simp
  have h4 : (ℓ - c - 1) / L ≤ T / lam := by
    rw [div_le_div_iff₀ hL hlam, hLd]
    have : (ℓ - c - 1) * lam ≤ ℓ * lam := by nlinarith
    nlinarith
  have h5 : (1 - 2 * θ) * T * ℓ / π' - T * (c + 1) / π' ≤ (1 - 2 * θ) * T * (ℓ - c - 1) / π' := by
    rw [← sub_div]
    apply div_le_div_of_nonneg_right _ hπ.le
    nlinarith [mul_nonneg (mul_nonneg hθ0.le (by linarith : (0:ℝ) ≤ T)) (by linarith : (0:ℝ) ≤ c + 1)]
  have e6 : ((c + 1) / π' + 1 / lam) * T = T * (c + 1) / π' + T / lam := by
    field_simp
  linarith

/-- The per-character main term, normalised. -/
lemma main_norm_lower {Q T : ℝ} (hQ : 1 < Q) (hT : 2 ≤ T) (τ₀ : ℝ) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 1 < q) (hprim : χ.IsPrimitive)
    {C Cg η : ℝ} (hC : ∀ w : ℝ, ‖P.hatψL Q w‖ * (1 + P.L Q * |w|) ^ 2 ≤ C * P.L Q)
    (hCg : 0 ≤ Cg) (hη : 0 < η) (hη1 : η ≤ 1)
    (hμ1 : ∀ t : ℝ, -1 ≤ muChi χ t)
    (hμ2 : ∀ t : ℝ, 1 ≤ t → 1 / (2 * Real.pi) * (Real.log q + Real.log t - Real.log (2 * Real.pi)) - Cg ≤
      muChi χ t)
    (hqη : Real.log Q + Real.log η ≤ Real.log q)
    (hℓ1 : 2 ≤ Real.log Q)
    (hℓ2 : -Real.log η + Real.log (2 * Real.pi) + 2 * Real.pi * Cg + 1 ≤ Real.log Q)
    (hℓ3 : 2 * Real.pi * C ^ 2 ≤ P.aInt * P.lam ^ 3 * Real.log Q ^ 2) :
    (1 - 2 * P.θ) * T * Real.log Q / (2 * Real.pi) -
        ((-Real.log η + Real.log (2 * Real.pi) + 2 * Real.pi * Cg + 1) / (2 * Real.pi) + 1 / P.lam) * T ≤
      (∑ k ∈ P.KJ Q T τ₀, ∫ t : ℝ, ‖P.pk Q τ₀ k t‖ ^ 2 * muChi χ t) / (P.aInt * P.L Q ^ 2) := by
  set ℓ := Real.log Q with hℓ
  set c₂ := -Real.log η + Real.log (2 * Real.pi) + 2 * Real.pi * Cg with hc₂
  set m₁ := (ℓ - c₂) / (2 * Real.pi) with hm₁
  have hπ : 0 < 2 * Real.pi := by positivity
  have hL : 0 < P.L Q := L_pos P hQ
  have hLdef : P.L Q = P.lam * ℓ := rfl
  have ha := aInt_pos P
  have hlam := P.lam_pos
  have hθ1 : 0 < 1 - 2 * P.θ := by linarith [P.θ_lt]
  have hc₂0 : 0 ≤ c₂ := by
    rw [hc₂]
    have := Real.log_nonpos hη.le hη1
    have hl2π : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by nlinarith [Real.pi_gt_three])
    nlinarith [Real.pi_gt_three]
  -- per k
  have hk : ∀ k ∈ P.KJ Q T τ₀, P.aInt * P.L Q * (ℓ - c₂ - 1) ≤
      ∫ t : ℝ, ‖P.pk Q τ₀ k t‖ ^ 2 * muChi χ t := by
    intro k hkK
    obtain ⟨hk1, hk2⟩ := tau_mem_J P hQ T τ₀ hkK
    have hm : ∀ t : ℝ, |t - tau P Q τ₀ k| ≤ 1 → m₁ ≤ muChi χ t := by
      intro t ht
      have ht1 : 1 ≤ t := by
        have := (abs_le.mp ht).1
        nlinarith [P.θ_pos]
      have h := hμ2 t ht1
      have hlt : 0 ≤ Real.log t := Real.log_nonneg ht1
      have : m₁ ≤ 1 / (2 * Real.pi) * (Real.log q + Real.log t - Real.log (2 * Real.pi)) - Cg := by
        rw [hm₁, hc₂]
        have e : 1 / (2 * Real.pi) * (Real.log q + Real.log t - Real.log (2 * Real.pi)) - Cg =
            (Real.log q + Real.log t - Real.log (2 * Real.pi) - 2 * Real.pi * Cg) / (2 * Real.pi) := by
          field_simp
        rw [e]
        apply div_le_div_of_nonneg_right _ hπ.le
        linarith
      linarith
    have hm1 : 0 ≤ m₁ + 1 := by
      rw [hm₁]; have : 0 ≤ (ℓ - c₂) / (2 * Real.pi) := div_nonneg (by linarith) hπ.le
      linarith
    have hmain := main_term_lower P hQ τ₀ χ k hC hm hm1 hμ1
      (integrable_normSq_mul_mu P hQ τ₀ hq hprim k)
    -- simplify the lower bound
    have hm1ℓ : m₁ + 1 ≤ ℓ := by
      rw [hm₁]
      have : (ℓ - c₂) / (2 * Real.pi) ≤ ℓ / 2 := by
        rw [div_le_iff₀ hπ]
        nlinarith [Real.pi_gt_three]
      linarith
    have herr : (m₁ + 1) * (2 * C ^ 2 / P.L Q ^ 2 * Real.pi) ≤ P.aInt * P.L Q := by
      have hC2 : 0 ≤ 2 * C ^ 2 / P.L Q ^ 2 * Real.pi := by positivity
      calc (m₁ + 1) * (2 * C ^ 2 / P.L Q ^ 2 * Real.pi)
          ≤ ℓ * (2 * C ^ 2 / P.L Q ^ 2 * Real.pi) := mul_le_mul_of_nonneg_right hm1ℓ hC2
        _ = 2 * Real.pi * C ^ 2 / (P.lam ^ 2 * ℓ) := by
            rw [hLdef]; field_simp
        _ ≤ P.aInt * P.L Q := by
            rw [div_le_iff₀ (by positivity), hLdef]
            nlinarith
    have e1 : m₁ * (2 * Real.pi * P.aInt * P.L Q) = P.aInt * P.L Q * (ℓ - c₂) := by
      rw [hm₁]; field_simp
    linarith
  have hsum : ((P.KJ Q T τ₀).card : ℝ) * (P.aInt * P.L Q * (ℓ - c₂ - 1)) ≤
      ∑ k ∈ P.KJ Q T τ₀, ∫ t : ℝ, ‖P.pk Q τ₀ k t‖ ^ 2 * muChi χ t := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum hk
  have hD := card_KJ_ge P hQ T τ₀
  rw [hLdef] at hsum hD ⊢
  exact trace_algebra hπ ha hlam (by linarith) (by linarith) P.θ_pos hθ1 hc₂0 (by linarith) hD hsum

/-! ### `famSum` bookkeeping -/

lemma omega_nonneg (W : Weight) (Q : ℝ) (q : ℕ) : 0 ≤ W.omega Q q := by
  unfold Weight.omega
  exact div_nonneg (mul_nonneg (W.nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

lemma famSum_add (W : Weight) (Q : ℝ) (f g : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) :
    famSum W Q (fun q χ => f q χ + g q χ) = famSum W Q f + famSum W Q g := by
  unfold famSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_add_distrib, mul_add]

lemma famSum_congr_family (W : Weight) (Q : ℝ) {f g : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ}
    (h : ∀ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.w (q / Q) ≠ 0 → ∀ χ ∈ primChars q, f q χ = g q χ) :
    famSum W Q f = famSum W Q g := by
  unfold famSum
  refine Finset.sum_congr rfl fun q hq => ?_
  by_cases hw : W.w (q / Q) = 0
  · simp [Weight.omega, hw]
  · rw [Finset.sum_congr rfl (h q hq hw)]

lemma famSum_mono_family (W : Weight) (Q : ℝ) {f g : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ}
    (h : ∀ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.w (q / Q) ≠ 0 → ∀ χ ∈ primChars q, f q χ ≤ g q χ) :
    famSum W Q f ≤ famSum W Q g := by
  unfold famSum
  refine Finset.sum_le_sum fun q hq => ?_
  by_cases hw : W.w (q / Q) = 0
  · simp [Weight.omega, hw]
  · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (h q hq hw)) (omega_nonneg W Q q)

lemma famSum_const (W : Weight) (Q c : ℝ) : famSum W Q (fun _ _ => c) = c * W.H Q := by
  unfold famSum Weight.H phiStar
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_const, nsmul_eq_mul]; ring

lemma famSum_div (W : Weight) (Q c : ℝ) (f : ∀ q : ℕ, DirichletCharacter ℂ q → ℝ) :
    famSum W Q (fun q χ => f q χ / c) = famSum W Q f / c := by
  unfold famSum
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [← Finset.sum_div, mul_div_assoc]

/-- The prime part, family-summed: interchange of the finite sums with the integrals. -/
lemma famSum_prime_eq {Q : ℝ} (hQ : 1 < Q) (T τ₀ : ℝ) (W : Weight) (X : ℝ) :
    famSum W Q (fun _ χ => ∑ k ∈ P.KJ Q T τ₀, ∫ t : ℝ, ‖P.pk Q τ₀ k t‖ ^ 2 * Pch X χ t) =
      ∑ k ∈ P.KJ Q T τ₀, ∫ t : ℝ, ‖P.pk Q τ₀ k t‖ ^ 2 *
        famSum W Q (fun _ χ => Pch X χ t) := by
  unfold famSum
  have hint : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (k : ℤ),
      Integrable (fun t : ℝ => ‖P.pk Q τ₀ k t‖ ^ 2 * Pch X χ t) :=
    fun q χ k => integrable_normSq_mul_Pch P hQ τ₀ k X χ
  -- move the k-sum outside
  have e1 : ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q * ∑ χ ∈ primChars q,
      ∑ k ∈ P.KJ Q T τ₀, ∫ t : ℝ, ‖P.pk Q τ₀ k t‖ ^ 2 * Pch X χ t =
      ∑ k ∈ P.KJ Q T τ₀, ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ ∈ primChars q,
        ∫ t : ℝ, W.omega Q q * (‖P.pk Q τ₀ k t‖ ^ 2 * Pch X χ t) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    rw [integral_const_mul]
  rw [e1]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hfun : (fun t : ℝ => ‖P.pk Q τ₀ k t‖ ^ 2 * ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, W.omega Q q *
      ∑ χ ∈ primChars q, (fun (_ : ℕ) (χ : DirichletCharacter ℂ _) => Pch X χ t) q χ) =
      fun t : ℝ => ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ ∈ primChars q,
        W.omega Q q * (‖P.pk Q τ₀ k t‖ ^ 2 * Pch X χ t) := by
    funext t
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    ring
  rw [hfun, integral_finsetSum _ (fun q _ => integrable_finsetSum _ fun χ _ =>
    (hint q χ k).const_mul _)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [integral_finsetSum _ (fun χ _ => (hint q χ k).const_mul _)]

/-- Final arithmetic of the trace bound. -/
lemma trace_final_arith {N M T θ δ δ₁ c₅ H Pr Mn E : ℝ} (hM : 0 ≤ M) (hθ0 : 0 ≤ θ)
    (hθ : 0 < 1 - 2 * θ)
    (hδ₁ : δ₁ ≤ δ / 6) (hδ₁' : δ₁ ≤ 1 / 2) (hδ : 0 < δ)
    (hN1 : (1 - δ₁) * M ≤ N) (hN2 : N ≤ (1 + δ₁) * M)
    (hMn : (1 - 2 * θ) * M - c₅ * T * H ≤ Mn) (hPr : -E ≤ Pr)
    (hc₅ : c₅ * T * H ≤ δ / 6 * M) (hE : E ≤ δ / 6 * M) :
    (1 - 2 * θ - δ) * N ≤ Mn + Pr := by
  have h1 : (1 - 2 * θ) * N ≤ (1 - 2 * θ) * ((1 + δ₁) * M) := mul_le_mul_of_nonneg_left hN2 hθ.le
  have h2 : δ * ((1 - δ₁) * M) ≤ δ * N := mul_le_mul_of_nonneg_left hN1 hδ.le
  have h3 : (1 - 2 * θ) * ((1 + δ₁) * M) ≤ (1 - 2 * θ) * M + δ₁ * M := by
    have hδ₁0 : 0 ≤ δ₁ ∨ δ₁ < 0 := le_or_gt 0 _
    rcases hδ₁0 with h | h
    · have : 0 ≤ θ * (δ₁ * M) := mul_nonneg hθ0 (mul_nonneg h hM)
      nlinarith
    · -- then (1+δ₁) < 1 and the bound is by N ≤ (1+δ₁)M ≤ M
      have : 0 ≤ θ * (-δ₁ * M) := mul_nonneg hθ0 (mul_nonneg (by linarith) hM)
      nlinarith
  have h4 : δ * ((1 - δ₁) * M) ≥ δ / 2 * M := by
    have : 1 / 2 ≤ 1 - δ₁ := by linarith
    have := mul_le_mul_of_nonneg_right this hM
    nlinarith
  have h5 : δ₁ * M ≤ δ / 6 * M := mul_le_mul_of_nonneg_right hδ₁ hM
  nlinarith

lemma continuous_famSum_Pch (W : Weight) (Q X : ℝ) :
    Continuous (fun t : ℝ => famSum W Q (fun _ χ => Pch X χ t)) := by
  unfold famSum
  exact continuous_finsetSum _ fun q _ => continuous_const.mul
    (continuous_finsetSum _ fun χ _ => continuous_Pch X χ)

/-- The prime part, family-summed and normalised, from below. -/
lemma prime_family_lower {Q T : ℝ} (hQ1 : 1 < Q) (hT1 : 1 ≤ T) (τ₀ : ℝ) (W : Weight)
    (hL1 : 1 ≤ P.L Q) :
    -(4 * Real.pi * (4 / Real.pi * W.wmax * Q * Real.sqrt (P.X Q) * Real.log (P.X Q) *
        (1 + Real.log (P.X Q))) * T) ≤
      famSum W Q (fun _ χ => ∑ k ∈ P.KJ Q T τ₀, ∫ t : ℝ, ‖P.pk Q τ₀ k t‖ ^ 2 * Pch (P.X Q) χ t) /
        (P.aInt * P.L Q ^ 2) := by
  set X := P.X Q with hX
  set Pi0 := 4 / Real.pi * W.wmax * Q * Real.sqrt X * Real.log X * (1 + Real.log X) with hPi0
  have hL := L_pos P hQ1
  have ha := aInt_pos P
  have hX1 : 1 ≤ X := Real.one_le_exp hL.le
  have hwm := W.wmax_nonneg
  have hPi00 : 0 ≤ Pi0 := by
    rw [hPi0]
    have : 0 ≤ Real.log X := Real.log_nonneg hX1
    have : 0 ≤ Q := by linarith
    positivity
  rw [famSum_prime_eq P hQ1 T τ₀ W X]
  have hk : ∀ k ∈ P.KJ Q T τ₀, -(Pi0 * (2 * Real.pi * P.aInt * P.L Q)) ≤
      ∫ t : ℝ, ‖P.pk Q τ₀ k t‖ ^ 2 * famSum W Q (fun _ χ => Pch X χ t) := by
    intro k _
    have hint := integrable_normSq_pk P hQ1 τ₀ k
    have hint2 : Integrable (fun t : ℝ => ‖P.pk Q τ₀ k t‖ ^ 2 *
        famSum W Q (fun _ χ => Pch X χ t)) :=
      hint.mul_bdd (c := Pi0) (continuous_famSum_Pch W Q X).aestronglyMeasurable
        (Eventually.of_forall fun t => by
          rw [Real.norm_eq_abs]; exact abs_famSum_Pch_le W hQ1.le hX1 t)
    have hpt : ∀ t : ℝ, -Pi0 * ‖P.pk Q τ₀ k t‖ ^ 2 ≤
        ‖P.pk Q τ₀ k t‖ ^ 2 * famSum W Q (fun _ χ => Pch X χ t) := by
      intro t
      have h2 := (abs_le.mp (abs_famSum_Pch_le W hQ1.le hX1 t)).1
      have h3 := sq_nonneg ‖P.pk Q τ₀ k t‖
      have := mul_le_mul_of_nonneg_left h2 h3
      linarith
    have := integral_mono (hint.const_mul (-Pi0)) hint2 hpt
    rw [integral_const_mul, integral_normSq_pk P hQ1 τ₀ k] at this
    linarith
  have hsum := Finset.sum_le_sum hk
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  have hD := card_KJ_le P hQ1 (T := T) (by linarith) τ₀
  have hTL : 1 ≤ T * P.L Q := one_le_mul_of_one_le_of_one_le hT1 hL1
  have hDL : ((P.KJ Q T τ₀).card : ℝ) ≤ 2 * T * P.L Q := by nlinarith
  rw [le_div_iff₀ (by positivity)]
  refine le_trans ?_ hsum
  have h1 := mul_le_mul_of_nonneg_right hDL
    (by positivity : (0:ℝ) ≤ Pi0 * (2 * Real.pi * P.aInt * P.L Q))
  have e : 2 * T * P.L Q * (Pi0 * (2 * Real.pi * P.aInt * P.L Q)) =
      4 * Real.pi * Pi0 * T * (P.aInt * P.L Q ^ 2) := by ring
  linarith

/-- The prime part is `o(N)`: `4π Π T ≤ (δ/6) H T ℓ/2π`, given `H ≥ κ₀ Q²` and `K₁/s ≤ Q^s`. -/
lemma prime_small {Q T δ κ₀ H : ℝ} (hQ1 : 1 < Q) (hT0 : 0 < T) (hδ : 0 < δ) (hκ₀ : 0 < κ₀)
    (W : Weight) (hH : κ₀ * Q ^ 2 ≤ H) (hℓ1 : 1 ≤ Real.log Q)
    (hQs : 192 * Real.pi * W.wmax * P.lam * (1 + P.lam) / (δ * κ₀) / ((1 - P.lam / 2) / 2) ≤
      Q ^ ((1 - P.lam / 2) / 2)) :
    4 * Real.pi * (4 / Real.pi * W.wmax * Q * Real.sqrt (P.X Q) * Real.log (P.X Q) *
        (1 + Real.log (P.X Q))) * T ≤ δ / 6 * (H * T * Real.log Q / (2 * Real.pi)) := by
  set ℓ := Real.log Q with hℓ
  set s := (1 - P.lam / 2) / 2 with hs
  have hlam := P.lam_pos
  have hlam2 := P.lam_lt
  have hs0 : 0 < s := by rw [hs]; linarith
  have hQ0 : 0 < Q := by linarith
  have hwm := W.wmax_nonneg
  have hLdef : P.L Q = P.lam * ℓ := rfl
  have hsqrtX : Real.sqrt (P.X Q) = Q ^ (P.lam / 2) := by
    rw [PrimeSetup.X, ← Real.exp_half, Real.rpow_def_of_pos hQ0, hLdef]
    congr 1; ring
  have hlogX : Real.log (P.X Q) = P.lam * ℓ := by rw [PrimeSetup.X, Real.log_exp, hLdef]
  rw [hsqrtX, hlogX]
  have hℓs : ℓ ≤ Q ^ s / s := Real.log_le_rpow_div hQ0.le hs0
  have hQs' : Q ^ (P.lam / 2) * Q ^ s * Q ^ s = Q := by
    rw [← Real.rpow_add hQ0, ← Real.rpow_add hQ0]
    have : P.lam / 2 + s + s = 1 := by rw [hs]; ring
    rw [this, Real.rpow_one]
  have hQl : 0 < Q ^ (P.lam / 2) := Real.rpow_pos_of_pos hQ0 _
  have hQsp : 0 < Q ^ s := Real.rpow_pos_of_pos hQ0 _
  -- LHS = 16 wmax Q Q^{λ/2} λℓ(1+λℓ) T ≤ 16 wmax λ(1+λ) Q Q^{λ/2} ℓ² T
  have h1 : 4 * Real.pi * (4 / Real.pi * W.wmax * Q * Q ^ (P.lam / 2) * (P.lam * ℓ) *
      (1 + P.lam * ℓ)) * T ≤ 16 * W.wmax * P.lam * (1 + P.lam) * Q * Q ^ (P.lam / 2) * ℓ ^ 2 * T := by
    have e : 4 * Real.pi * (4 / Real.pi * W.wmax * Q * Q ^ (P.lam / 2) * (P.lam * ℓ) *
        (1 + P.lam * ℓ)) * T = 16 * W.wmax * P.lam * Q * Q ^ (P.lam / 2) * ℓ * (1 + P.lam * ℓ) * T := by
      field_simp; ring
    rw [e]
    have : ℓ * (1 + P.lam * ℓ) ≤ (1 + P.lam) * ℓ ^ 2 := by nlinarith
    have hpos : 0 ≤ 16 * W.wmax * P.lam * Q * Q ^ (P.lam / 2) * T := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this hpos]
  refine h1.trans ?_
  -- ℓ Q^{λ/2} ≤ Q^{λ/2} Q^s/s and K₁/s ≤ Q^s
  have h2 : ℓ * Q ^ (P.lam / 2) ≤ Q ^ (P.lam / 2) * Q ^ s / s := by
    rw [mul_div_assoc, mul_comm]
    exact mul_le_mul_of_nonneg_left hℓs hQl.le
  have h3 : 192 * Real.pi * W.wmax * P.lam * (1 + P.lam) * (ℓ * Q ^ (P.lam / 2)) ≤ δ * κ₀ * Q := by
    have hK : 192 * Real.pi * W.wmax * P.lam * (1 + P.lam) ≤ δ * κ₀ * s * Q ^ s := by
      rw [div_div, div_le_iff₀ (by positivity)] at hQs
      linarith
    calc 192 * Real.pi * W.wmax * P.lam * (1 + P.lam) * (ℓ * Q ^ (P.lam / 2))
        ≤ δ * κ₀ * s * Q ^ s * (Q ^ (P.lam / 2) * Q ^ s / s) := by
          apply mul_le_mul hK h2 (by positivity) (by positivity)
      _ = δ * κ₀ * (Q ^ (P.lam / 2) * Q ^ s * Q ^ s) := by field_simp
      _ = δ * κ₀ * Q := by rw [hQs']
  -- conclude
  have hH0 : 0 < H := lt_of_lt_of_le (by positivity) hH
  have h4 : 16 * W.wmax * P.lam * (1 + P.lam) * Q * Q ^ (P.lam / 2) * ℓ ^ 2 * T ≤
      δ / 6 * (κ₀ * Q ^ 2 * T * ℓ / (2 * Real.pi)) := by
    have e1 : 16 * W.wmax * P.lam * (1 + P.lam) * Q * Q ^ (P.lam / 2) * ℓ ^ 2 * T =
        (192 * Real.pi * W.wmax * P.lam * (1 + P.lam) * (ℓ * Q ^ (P.lam / 2))) *
          (Q * ℓ * T / (12 * Real.pi)) := by
      field_simp; ring
    have e2 : δ / 6 * (κ₀ * Q ^ 2 * T * ℓ / (2 * Real.pi)) = (δ * κ₀ * Q) * (Q * ℓ * T / (12 * Real.pi)) := by
      field_simp; ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right h3 (by positivity)
  refine h4.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply div_le_div_of_nonneg_right _ (by positivity)
  have := mul_le_mul_of_nonneg_right hH (by positivity : (0:ℝ) ≤ T * ℓ)
  nlinarith

/-- The main part, family-summed and normalised, from below. -/
lemma main_family_lower {Q T : ℝ} (hQ1 : 1 < Q) (hT2 : 2 ≤ T) (τ₀ : ℝ) (W : Weight)
    {Ce Cg : ℝ} (hC : ∀ w : ℝ, ‖P.hatψL Q w‖ * (1 + P.L Q * |w|) ^ 2 ≤ Ce * P.L Q)
    (hCg0 : 0 ≤ Cg)
    (hmu : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), 1 ≤ q → (∀ t : ℝ, -1 ≤ muChi χ t) ∧
      (∀ t : ℝ, 1 ≤ t → 1 / (2 * Real.pi) * (Real.log q + Real.log t - Real.log (2 * Real.pi)) - Cg ≤
        muChi χ t))
    (hQη : 2 ≤ W.η * Q) (hℓ2 : 2 ≤ Real.log Q)
    (hℓc : -Real.log W.η + Real.log (2 * Real.pi) + 2 * Real.pi * Cg + 1 ≤ Real.log Q)
    (hℓ3 : 2 * Real.pi * Ce ^ 2 ≤ P.aInt * P.lam ^ 3 * Real.log Q ^ 2) :
    ((1 - 2 * P.θ) * T * Real.log Q / (2 * Real.pi) -
        ((-Real.log W.η + Real.log (2 * Real.pi) + 2 * Real.pi * Cg + 1) / (2 * Real.pi) +
          1 / P.lam) * T) * W.H Q ≤
      famSum W Q (fun _ χ => (∑ k ∈ P.KJ Q T τ₀, ∫ t : ℝ, ‖P.pk Q τ₀ k t‖ ^ 2 * muChi χ t) /
        (P.aInt * P.L Q ^ 2)) := by
  have hQ0 : 0 < Q := by linarith
  have hη := W.η_pos
  have hη1 : W.η ≤ 1 := by linarith [W.η_lt_half]
  rw [← famSum_const]
  refine famSum_mono_family W Q fun q hq hw χ hχ => ?_
  have hq1 : 1 < q := one_lt_of_w_ne W hQη hw
  have : NeZero q := ⟨by omega⟩
  have hqη : W.η * Q ≤ q := le_of_w_ne W hQ0 hw
  have hlq : Real.log Q + Real.log W.η ≤ Real.log q := by
    have := Real.log_le_log (by positivity) hqη
    rw [Real.log_mul hη.ne' hQ0.ne'] at this
    linarith
  obtain ⟨hμ1, hμ2⟩ := hmu q χ hq1.le
  exact main_norm_lower P hQ1 hT2 τ₀ hq1 (mem_primChars hχ) hC hCg0 hη hη1 hμ1 hμ2 hlq hℓ2
    hℓc hℓ3

/-- **`prop:trace`, lower bound**: `∑_χ ω_χ tr Ĝ_χ ≥ (1 − 2θ − δ) N`, uniformly in `T`. -/
theorem trace_lower (hWH : lemWH_Statement) (W : Weight) (τ₀ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q → ∀ T ∈ P.heights Q,
      (1 - 2 * P.θ - δ) * Nfam W Q T ≤
        famSum W Q (fun _ χ => (∑ k ∈ P.KJ Q T τ₀,
          (∑' ρ : PrimeSetup.strip χ, gaborTerm P Q τ₀ χ k k ρ).re) / (P.aInt * P.L Q ^ 2)) := by
  obtain ⟨Cg, hCg0, hmu⟩ := mu_facts
  obtain ⟨Ce, hCe0, henv⟩ := envelope P 2
  have hη := W.η_pos
  set c₂ := -Real.log W.η + Real.log (2 * Real.pi) + 2 * Real.pi * Cg with hc₂
  set c₅ := (c₂ + 1) / (2 * Real.pi) + 1 / P.lam with hc₅
  set δ₁ := min (δ / 6) (1 / 2) with hδ₁
  have hδ₁0 : 0 < δ₁ := lt_min (by positivity) (by norm_num)
  obtain ⟨Q₁, hRvM⟩ := rvm_family W P.a0_pos hδ₁0 (A0 := P.A0)
  set κ₀ := 1 / 2 * (Ecal * W.Iw) with hκ₀
  have hκ₀0 : 0 < κ₀ := by have := Ecal_pos; have := W.Iw_pos; positivity
  have hHev := H_lower_eventually hWH W (κ := 1 / 2) (by norm_num)
  have hlam := P.lam_pos
  have hlam2 := P.lam_lt
  have hs0 : 0 < (1 - P.lam / 2) / 2 := by linarith
  have ha := aInt_pos P
  have hev := hHev.and ((ev_log_ge 2).and ((ev_log_ge (c₂ + 1)).and
    ((ev_log_ge (12 * Real.pi * c₅ / δ)).and ((ev_log_ge (1 / P.lam)).and
    ((ev_log_rpow_ge 2 P.a0_pos).and (((tendsto_rpow_atTop hs0).eventually_ge_atTop
      (192 * Real.pi * W.wmax * P.lam * (1 + P.lam) / (δ * κ₀) / ((1 - P.lam / 2) / 2))).and
    ((eventually_ge_atTop (2 / W.η + 2)).and
    (((Real.tendsto_log_atTop.atTop_mul_atTop₀ Real.tendsto_log_atTop).eventually_ge_atTop
      (2 * Real.pi * Ce ^ 2 / (P.aInt * P.lam ^ 3)))))))))))
  obtain ⟨Q₂, hQ₂⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max Q₁ Q₂, fun Q hQ T hT => ?_⟩
  obtain ⟨hHQ, hℓ2, hℓc, hℓδ, hℓlam, hℓa0, hQs, hQη, hℓℓ⟩ := hQ₂ Q ((le_max_right _ _).trans hQ)
  obtain ⟨hN1, hN2⟩ := hRvM Q ((le_max_left _ _).trans hQ) T hT
  have hQ1 : 1 < Q := by linarith [div_pos (by norm_num : (0:ℝ) < 2) hη]
  have hQ0 : 0 < Q := by linarith
  have hT2 : 2 ≤ T := hℓa0.trans hT.1
  have hT0 : 0 < T := by linarith
  have hQη' : 2 ≤ W.η * Q := by
    have : 2 / W.η ≤ Q := by linarith
    rw [div_le_iff₀ hη] at this; linarith
  have hC : ∀ w : ℝ, ‖P.hatψL Q w‖ * (1 + P.L Q * |w|) ^ 2 ≤ Ce * P.L Q := by
    intro w
    have := henv Q hQ1 (w : ℂ)
    simpa using this
  have hℓ3 : 2 * Real.pi * Ce ^ 2 ≤ P.aInt * P.lam ^ 3 * Real.log Q ^ 2 := by
    have := hℓℓ
    rw [div_le_iff₀ (by positivity)] at this
    nlinarith
  have hL1 : 1 ≤ P.L Q := by
    show 1 ≤ P.lam * Real.log Q
    rw [div_le_iff₀ hlam] at hℓlam; linarith
  -- decomposition
  have hdecomp : famSum W Q (fun _ χ => (∑ k ∈ P.KJ Q T τ₀,
      (∑' ρ : PrimeSetup.strip χ, gaborTerm P Q τ₀ χ k k ρ).re) / (P.aInt * P.L Q ^ 2)) =
      famSum W Q (fun _ χ => (∑ k ∈ P.KJ Q T τ₀, ∫ t : ℝ, ‖P.pk Q τ₀ k t‖ ^ 2 * muChi χ t) /
        (P.aInt * P.L Q ^ 2)) +
      famSum W Q (fun _ χ => ∑ k ∈ P.KJ Q T τ₀, ∫ t : ℝ, ‖P.pk Q τ₀ k t‖ ^ 2 * Pch (P.X Q) χ t) /
        (P.aInt * P.L Q ^ 2) := by
    rw [← famSum_div, ← famSum_add]
    refine famSum_congr_family W Q fun q hq hw χ hχ => ?_
    have hq1 : 1 < q := one_lt_of_w_ne W hQη' hw
    have : NeZero q := ⟨by omega⟩
    rw [← add_div, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    exact gabor_diag_re P hQ1 τ₀ hq1 (mem_primChars hχ) k
  rw [hdecomp]
  have hMn := main_family_lower P hQ1 hT2 τ₀ W hC hCg0 hmu hQη' hℓ2 hℓc hℓ3
  have hPr := prime_family_lower P hQ1 (T := T) (by linarith) τ₀ W hL1
  have hHQ' : κ₀ * Q ^ 2 ≤ W.H Q := by rw [hκ₀]; linarith
  have hE := prime_small P hQ1 hT0 hδ hκ₀0 W hHQ' (by linarith) hQs
  have hH0 : 0 ≤ W.H Q := le_trans (by positivity) hHQ'
  have hc5 : c₅ * T * W.H Q ≤ δ / 6 * (W.H Q * T * Real.log Q / (2 * Real.pi)) := by
    rw [div_le_iff₀ hδ] at hℓδ
    have : c₅ ≤ δ / 6 * (Real.log Q / (2 * Real.pi)) := by
      rw [show δ / 6 * (Real.log Q / (2 * Real.pi)) = δ * Real.log Q / (12 * Real.pi) by ring,
        le_div_iff₀ (by positivity)]
      linarith
    have := mul_le_mul_of_nonneg_right this (mul_nonneg hT0.le hH0)
    have e : δ / 6 * (Real.log Q / (2 * Real.pi)) * (T * W.H Q) =
        δ / 6 * (W.H Q * T * Real.log Q / (2 * Real.pi)) := by ring
    linarith
  have hM : 0 ≤ W.H Q * T * Real.log Q / (2 * Real.pi) := by positivity
  have hMn' : (1 - 2 * P.θ) * (W.H Q * T * Real.log Q / (2 * Real.pi)) - c₅ * T * W.H Q ≤
      famSum W Q (fun _ χ => (∑ k ∈ P.KJ Q T τ₀, ∫ t : ℝ, ‖P.pk Q τ₀ k t‖ ^ 2 * muChi χ t) /
        (P.aInt * P.L Q ^ 2)) := by
    refine le_trans (le_of_eq ?_) hMn
    rw [hc₅, hc₂]; ring
  exact trace_final_arith hM P.θ_pos.le (by linarith [P.θ_lt]) (min_le_left _ _)
    (min_le_right _ _) hδ hN1 hN2 hMn' hPr hc5 hE

end Families.Ported.Zero
