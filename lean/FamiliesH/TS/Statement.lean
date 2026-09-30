/-
# Package TS: the band hypothesis at the length of Lemma 9.1 (S2)

**Why `Q^{5/4}`.** A band hypothesis covering intervals of `K ≤ Q^{1+2ε}` integers (the length used in `Families`)
does not suffice here: at polynomial height the band vectors `x_b^s(u)` of Proposition 9.18,
`(1−ε)ℓ_* < u ≤ (1+ε)ℓ_*`, `δ = T^{−1+ε₅}`, live on intervals of about `4δe^u` integers, i.e. up to about
`4Q^{1+ε}T^{ε+ε₅}` at the top of the band; at `T = Q^{κc}` this exceeds `Q^{1+2ε}` as soon as
`κc(ε + ε₅) > ε` (e.g. for every `κc ≥ 1`). §9.3 assumes `Λ_mult(Q^{5/4}) ≤ (C_band + o(1))H`, which is
what Lemma 9.1 (S2) delivers (`lemSizesH_Statement`, second clause: `K(u) ≤ 5δe^u + 1 ≤ Q^{5/4}` on the band).
This file states that hypothesis (`BandLSH54`), the corresponding form of `prop:TIsharpH`
(`propTIsharpH54_Statement`, identical to `propTIsharpH_Statement` except for `BandLSH54`), and proves
`bandLSH54_of_MV`, the analogue of the glue's `bandLSH_of_MV` (only the step `K ≤ Q²` changes). `BandLSH`
(`FamiliesH.Statements`) bounds intervals of `Q^{5/4}` integers, so `propTIsharpH_Statement` is
`propTIsharpH54_Statement` by definition. (For `ε ≤ 1/8`, `Q^{1+2ε} ≤ Q^{5/4}`, so a hypothesis at `Q^{5/4}`
is the stronger hypothesis and `propTIsharpH54_Statement` the weaker proposition; the glue supplies the
stronger hypothesis, `bandLSH54_of_MV`.) See `STATEMENTS-H.md` §5.
-/
import FamiliesH.Glue

noncomputable section

open scoped ENNReal ContDiff
open Filter

namespace Families.Hybrid

open Families

namespace TS

/-- The band hypothesis of Proposition 9.18: `Λ_mult(Q^{5/4}) ≤ (C_band + o(1)) H` for intervals
anywhere in `[1, ∞)`. (`ε` is unused; it is kept so that `BandLSH54` has the signature of `BandLSH`.) -/
def BandLSH54 (W : Weight) (_ε Cband : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
    ∀ K : ℕ, (K : ℝ) ≤ Q ^ (5 / 4 : ℝ) → LmultLEAny W Q K ((Cband + δ) * W.H Q)

/-- **`prop:TIsharpH`** with the band hypothesis `BandLSH54` (Proposition 9.18 as stated in the
TeX); otherwise literally `propTIsharpH_Statement`. -/
def propTIsharpH54_Statement : Prop :=
  ∀ (P : HSetup) (W : Weight), CTp W ≠ ⊤ → ∀ (ε : ℝ), 0 < ε → ε < 1 / 3 → ε < P.ε₁ / 4 →
    ε ≤ 1 / (8 * (1 + P.kc)) →
    ∀ Cband : ℝ, 1 ≤ Cband → BandLSH54 W ε Cband →
    ∀ Ct : ℝ → ℝ, ContDiff ℝ ∞ Ct →
    (∀ α, 1 ≤ Ct α ∧ Ct α ≤ max Cband (CTp W).toReal) → (∀ α, α ≤ 1 - 2 * ε → Ct α = 1) →
    (∀ α, 1 - 3 / 2 * ε ≤ α → α ≤ 1 + 3 / 2 * ε → Cband ≤ Ct α) →
    (∀ α, 1 + ε / 2 ≤ α → (CTp W).toReal ≤ Ct α) → (∀ α, 1 + 2 * ε ≤ α → Ct α = (CTp W).toReal) →
    P.ProfileBoundH W Ct

/-- **The band constant** for `BandLSH54` (the glue's `bandLSH_of_MV`, with `K ≤ Q^{5/4} ≤ Q²`). -/
theorem bandLSH54_of_MV (hMV : MV_LargeSieve) (hWH : lemWH_Statement) (W : Weight) :
    ∃ Cband : ℝ, 1 ≤ Cband ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → BandLSH54 W ε Cband := by
  obtain ⟨C₀, hmult, -⟩ := hMV
  have hE : 0 < Ecal * W.Iw := mul_pos Ecal_pos W.Iw_pos
  set C₁ := max C₀ 0 with hC₁
  have hC₁0 : 0 ≤ C₁ := le_max_right _ _
  set A := 2 * C₁ * W.wmax / (Ecal * W.Iw) with hA
  have hA0 : 0 ≤ A := div_nonneg (by have := W.wmax_nonneg; positivity) hE.le
  refine ⟨A + 1, by linarith, fun ε _ _ δ hδ => ?_⟩
  have hκ : A / (A + 1) < 1 := (div_lt_one (by linarith)).mpr (by linarith)
  obtain ⟨Q₁, hQ₁⟩ := Filter.eventually_atTop.1 (H_lower_eventually hWH W hκ)
  refine ⟨max Q₁ 1, fun Q hQ K hK N₀ _ x => ?_⟩
  have hQ1 : 1 ≤ Q := le_of_max_le_right hQ
  have hHl := hQ₁ Q (le_of_max_le_left hQ)
  have hx : 0 ≤ normSq (intervalZ N₀ K) x := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hK2 : (K : ℝ) ≤ Q ^ 2 := by
    calc (K : ℝ) ≤ Q ^ (5 / 4 : ℝ) := hK
      _ ≤ Q ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
      _ = Q ^ 2 := by norm_cast
  have hmv := hmult Q hQ1 N₀ K x
  have hC : C₀ * (Q ^ 2 + K) * normSq (intervalZ N₀ K) x ≤
      C₁ * (2 * Q ^ 2) * normSq (intervalZ N₀ K) x := by
    apply mul_le_mul_of_nonneg_right _ hx
    calc C₀ * (Q ^ 2 + K) ≤ C₁ * (Q ^ 2 + K) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ C₁ * (2 * Q ^ 2) := mul_le_mul_of_nonneg_left (by linarith) hC₁0
  have hAA : (A + 1) * (A / (A + 1)) = A := by field_simp
  have hAE : A * (Ecal * W.Iw) = 2 * C₁ * W.wmax := by
    rw [hA, div_mul_cancel₀ _ hE.ne']
  have hH0 : 0 ≤ W.H Q := W.H_nonneg Q
  calc famForm W Q (intervalZ N₀ K) x
      ≤ W.wmax * (C₁ * (2 * Q ^ 2) * normSq (intervalZ N₀ K) x) :=
        (famForm_le_mult W Q _ x).trans
          (mul_le_mul_of_nonneg_left (hmv.trans hC) W.wmax_nonneg)
    _ = (A + 1) * (A / (A + 1) * (Ecal * W.Iw * Q ^ 2)) * normSq (intervalZ N₀ K) x := by
        rw [← mul_assoc (A + 1), hAA]
        calc W.wmax * (C₁ * (2 * Q ^ 2) * normSq (intervalZ N₀ K) x)
            = 2 * C₁ * W.wmax * Q ^ 2 * normSq (intervalZ N₀ K) x := by ring
          _ = A * (Ecal * W.Iw) * Q ^ 2 * normSq (intervalZ N₀ K) x := by rw [hAE]
          _ = _ := by ring
    _ ≤ (A + 1) * W.H Q * normSq (intervalZ N₀ K) x := by
        apply mul_le_mul_of_nonneg_right _ hx
        exact mul_le_mul_of_nonneg_left hHl (by linarith)
    _ ≤ (A + 1 + δ) * W.H Q * normSq (intervalZ N₀ K) x := by
        apply mul_le_mul_of_nonneg_right _ hx
        exact mul_le_mul_of_nonneg_right (by linarith) hH0

end TS

end Families.Hybrid
