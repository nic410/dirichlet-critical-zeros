/-
# Theorem 1.4(a), package V: `prop:certH` (Proposition 9.24, the κ-table after Theorem 1.4, column `p(β(κ))`) — proved

`p(3/2) ≥ 0.865673`, `p(4/3) ≥ 0.824355`, `p(5/4) ≥ 0.797213`, `p(7/6) ≥ 0.764149`, `p(12/11) ≥ 0.727484`
(`C = 1`; the `n = 400` values of the paper's ancillary `certify_hybrid_n400_rerun.log`). Each is
`2 − 𝒬_{F_1}(windowB) ≤ p(β)` for the explicit admissible step function `windowB p D ms` of
`FamiliesH.V.CertGen`, with `𝒬 ≤ B/10⁶` from the kernel-checked integer inequality in
`FamiliesH.V.CertData` (`decide +kernel`, no `native_decide`).
-/
import FamiliesH.V.CertGen
import FamiliesH.V.CertData

noncomputable section

namespace Families.Hybrid.V

open Families Families.CertData Families.Hybrid.V.CertDataH

/-- One row: from the kernel-checked data to `2 − B/10⁶ ≤ p(400p/D; F_1)`. -/
lemma cert_row {p D B : ℤ} (hp : 0 < p) (hD : 0 < D) {ms : List ℤ} (hlen : ms.length = 400)
    (hl : ms.reverse = ms) (hnn : nonnegCheck ms = true) (hS : 0 < ms.sum)
    (hcert : certCheckB p D 1 B ms (kerListB 1 1 p D) = true) :
    2 - (B : ℝ) / 10 ^ 6 ≤ pB (400 * (p : ℝ) / D) 1 := by
  have hadm := windowB_admissible p D hp hD ms hlen hl hnn hS
  have h1 := pB_ge_of_admissible (C := 1) zero_le_one hadm
  have h2 := Qf_windowB_le p D hp hD ms hlen hl hS 1 1 B one_pos hcert
  have e : ((1 : ℤ) : ℝ) / ((1 : ℤ) : ℝ) = 1 := by norm_num
  rw [e] at h2
  linarith

/-- **`prop:certH`** (Proposition 9.24, `n = 400`). -/
theorem certH_proof : certH_Statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h := cert_row (p := 3) (D := 800) (B := 1134327) (by norm_num) (by norm_num)
      msK1_length msK1_reverse msK1_nonneg msK1_sum_pos certK1
    have hβ : (400 * ((3 : ℤ) : ℝ) / ((800 : ℤ) : ℝ)) = 3 / 2 := by norm_num
    rw [hβ] at h
    norm_num at h ⊢
    linarith
  · have h := cert_row (p := 4) (D := 1200) (B := 1175645) (by norm_num) (by norm_num)
      msK2_length msK2_reverse msK2_nonneg msK2_sum_pos certK2
    have hβ : (400 * ((4 : ℤ) : ℝ) / ((1200 : ℤ) : ℝ)) = 4 / 3 := by norm_num
    rw [hβ] at h
    norm_num at h ⊢
    linarith
  · have h := cert_row (p := 5) (D := 1600) (B := 1202787) (by norm_num) (by norm_num)
      msK3_length msK3_reverse msK3_nonneg msK3_sum_pos certK3
    have hβ : (400 * ((5 : ℤ) : ℝ) / ((1600 : ℤ) : ℝ)) = 5 / 4 := by norm_num
    rw [hβ] at h
    norm_num at h ⊢
    linarith
  · have h := cert_row (p := 7) (D := 2400) (B := 1235851) (by norm_num) (by norm_num)
      msK5_length msK5_reverse msK5_nonneg msK5_sum_pos certK5
    have hβ : (400 * ((7 : ℤ) : ℝ) / ((2400 : ℤ) : ℝ)) = 7 / 6 := by norm_num
    rw [hβ] at h
    norm_num at h ⊢
    linarith
  · have h := cert_row (p := 12) (D := 4400) (B := 1272516) (by norm_num) (by norm_num)
      msK10_length msK10_reverse msK10_nonneg msK10_sum_pos certK10
    have hβ : (400 * ((12 : ℤ) : ℝ) / ((4400 : ℤ) : ℝ)) = 12 / 11 := by norm_num
    rw [hβ] at h
    norm_num at h ⊢
    linarith

end Families.Hybrid.V
