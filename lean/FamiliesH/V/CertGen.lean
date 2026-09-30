/-
# Theorem 1.4(a), package V: the certificate windows at support `β = 400p/D` (no `sorry`)

Generalises `Families.Certificate.Numerics` (support `2`, cell width `1/200`) to support
`β = 400p/D` and cell width `h = p/D` (`D = 400q` for `β = p/q`), `n = 400` cells:

* `Gfun_gridB`, `kappa_gridB`: the exact cell-pair integrals `G((k±1)h) − 2G(kh) + …` as the integers
  `ksB` of `FamiliesH.V.CertDefs`, divided by `6D³c_d`;
* `windowB p D ms`: the step function on the 400 cells of `[−β/2, β/2]` with heights `m_i/(h∑m)`;
  it is admissible at support `β` (`windowB_admissible`);
* `Qf_windowB`, `Qf_windowB_le`: `𝒬_{F_C}(windowB) ≤ B/10⁶` from the kernel-checked integer inequality
  `certCheckB`.

The generic step-function facts (`Families.Qf_stepFn`, `Families.stepFn_neg`, …) and list lemmas
(`Families.dot_eq_sum`, `Families.getD_symm`, …) are reused from the audited families package.
-/
import FamiliesH.V.Basic
import FamiliesH.V.CertDefs

noncomputable section

open MeasureTheory Set

namespace Families.Hybrid.V

open Families Families.CertData Families.Hybrid.V.CertDataH

/-! ### The integer kernel list -/

lemma kerListB_length (cn cd p D : ℤ) : (kerListB cn cd p D).length = 799 := by simp [kerListB]

lemma kerListB_getD (cn cd p D : ℤ) {k : ℕ} (hk : k < 799) :
    (kerListB cn cd p D).getD k 0 = ksB cn cd p D ((k : ℤ) - 399) := by
  rw [List.getD_eq_getElem?_getD, kerListB, List.getElem?_map, List.getElem?_range hk]
  rfl

lemma inner_eqB (ms : List ℤ) (hlen : ms.length = 400) (hl : ms.reverse = ms) (cn cd p D : ℤ)
    {i : ℕ} (hi : i < 400) :
    dot ms ((kerListB cn cd p D).drop i) =
      ∑ j ∈ Finset.range 400, ms.getD j 0 * ksB cn cd p D ((i : ℤ) - j) := by
  rw [dot_eq_sum _ _ (by simp [hlen, kerListB_length]; omega), hlen]
  have hdrop : ∀ t ∈ Finset.range 400, ms.getD t 0 * ((kerListB cn cd p D).drop i).getD t 0
      = ms.getD t 0 * ksB cn cd p D (((i + t : ℕ) : ℤ) - 399) := by
    intro t ht
    have ht' := Finset.mem_range.mp ht
    rw [getD_drop', kerListB_getD cn cd p D (by omega)]
  rw [Finset.sum_congr rfl hdrop]
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  have hs := getD_symm ms hl (i := j) (by omega)
  rw [hlen] at hs
  rw [hs]
  congr 2
  push_cast [Nat.cast_sub (by omega : j ≤ 400 - 1)]
  ring

lemma quad_eqB (ms : List ℤ) (hlen : ms.length = 400) (hl : ms.reverse = ms) (cn cd p D : ℤ) :
    quadL ms (kerListB cn cd p D) = ∑ i ∈ Finset.range 400, ms.getD i 0 *
      ∑ j ∈ Finset.range 400, ms.getD j 0 * ksB cn cd p D ((i : ℤ) - j) := by
  unfold quadL
  rw [dot_eq_sum _ _ (by simp [hlen]), hlen]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  rw [getD_map_range _ hi', inner_eqB ms hlen hl cn cd p D hi']

/-! ### The grid identities for the cell width `h = p/D` -/

lemma Gfun_gridB (cn cd p D : ℤ) (hcd : 0 < cd) (hp : 0 < p) (hD : 0 < D) (k : ℤ) :
    Gfun ((cn : ℝ) / cd) ((k : ℝ) * p / D) = (GsB cn cd p D k : ℝ) / (6 * D ^ 3 * cd) := by
  have hcd' : (0 : ℝ) < cd := by exact_mod_cast hcd
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have habs : |(k : ℝ) * p / D| = |(k : ℝ)| * p / D := by
    rw [abs_div, abs_mul, abs_of_pos hp', abs_of_pos hD']
  have hna : ((k.natAbs : ℤ) : ℝ) = |(k : ℝ)| := natAbs_cast_real k
  unfold Gfun GsB
  by_cases hk : ((k.natAbs : ℤ) * p ≤ D)
  · have hk' : |(k : ℝ)| * p ≤ D := by
      rw [← hna]; exact_mod_cast hk
    rw [if_pos (by rw [habs, div_le_one hD']; exact hk'), if_pos hk]
    push_cast
    rw [habs]
    field_simp
  · have hk' : ¬ |(k : ℝ)| * p ≤ D := by
      rw [← hna]; exact_mod_cast hk
    rw [if_neg (by rw [habs, div_le_one hD']; exact hk'), if_neg hk]
    push_cast
    rw [habs]
    field_simp
    ring

lemma kappa_gridB (cn cd p D : ℤ) (hcd : 0 < cd) (hp : 0 < p) (hD : 0 < D) (i j : ℕ) :
    Gfun ((cn : ℝ) / cd) (((i : ℝ) - j) * ((p : ℝ) / D) + (p : ℝ) / D)
      - 2 * Gfun ((cn : ℝ) / cd) (((i : ℝ) - j) * ((p : ℝ) / D))
      + Gfun ((cn : ℝ) / cd) (((i : ℝ) - j) * ((p : ℝ) / D) - (p : ℝ) / D)
      = (ksB cn cd p D ((i : ℤ) - j) : ℝ) / (6 * D ^ 3 * cd) := by
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have e1 : ((i : ℝ) - j) * ((p : ℝ) / D) + (p : ℝ) / D = (((i : ℤ) - j + 1 : ℤ) : ℝ) * p / D := by
    push_cast; field_simp
  have e2 : ((i : ℝ) - j) * ((p : ℝ) / D) = (((i : ℤ) - j : ℤ) : ℝ) * p / D := by
    push_cast; field_simp
  have e3 : ((i : ℝ) - j) * ((p : ℝ) / D) - (p : ℝ) / D = (((i : ℤ) - j - 1 : ℤ) : ℝ) * p / D := by
    push_cast; field_simp
  rw [e1, e3, e2, Gfun_gridB cn cd p D hcd hp hD, Gfun_gridB cn cd p D hcd hp hD,
    Gfun_gridB cn cd p D hcd hp hD]
  unfold ksB
  push_cast
  ring

/-! ### The certificate windows -/

/-- Heights `c_i = m_i/(h ∑ m)`, `h = p/D`. -/
def cvecB (p D : ℤ) (ms : List ℤ) (i : ℕ) : ℝ := (ms.getD i 0 : ℝ) / (((p : ℝ) / D) * (ms.sum : ℝ))

/-- The certificate window at support `β = 400p/D`: the step function on the 400 cells of
`[−β/2, β/2]` (width `p/D`) with heights `cvecB`. -/
def windowB (p D : ℤ) (ms : List ℤ) : ℝ → ℝ :=
  stepFn (-(200 * (p : ℝ) / D)) ((p : ℝ) / D) 400 (cvecB p D ms)

lemma windowB_admissible (p D : ℤ) (hp : 0 < p) (hD : 0 < D) (ms : List ℤ) (hlen : ms.length = 400)
    (hl : ms.reverse = ms) (hnn : nonnegCheck ms = true) (hS : 0 < ms.sum) :
    AdmissibleWindowB (400 * (p : ℝ) / D) (windowB p D ms) := by
  have hS' : (0 : ℝ) < ms.sum := by exact_mod_cast hS
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hh : (0 : ℝ) < (p : ℝ) / D := div_pos hp' hD'
  have hcnn : ∀ i, 0 ≤ cvecB p D ms i := fun i => by
    unfold cvecB
    exact div_nonneg (by exact_mod_cast getD_nonneg_of_check ms hnn i) (by positivity)
  have hsym : -(200 * (p : ℝ) / D) + ((400 : ℕ) : ℝ) * ((p : ℝ) / D) = -(-(200 * (p : ℝ) / D)) := by
    push_cast; ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    unfold windowB stepFn
    exact Finset.sum_nonneg fun i _ => Set.indicator_nonneg (fun _ _ => hcnn i) x
  · intro x
    refine stepFn_neg _ _ 400 (cvecB p D ms) hsym (fun i hi => ?_) x
    unfold cvecB
    have := getD_symm ms hl (i := i) (by omega)
    rw [hlen] at this
    rw [this]
  · intro x hx
    by_contra hx'
    have hset : Icc (-(200 * (p : ℝ) / D)) (-(200 * (p : ℝ) / D) + ((400 : ℕ) : ℝ) * ((p : ℝ) / D)) =
        Icc (-(400 * (p : ℝ) / D) / 2) (400 * (p : ℝ) / D / 2) := by
      congr 1
      · ring
      · push_cast; ring
    exact hx (stepFn_eq_zero_of_notMem _ _ hh.le 400 (cvecB p D ms) (by rw [hset]; exact hx'))
  · exact memLp_stepFn _ _ _ _
  · unfold windowB
    rw [integral_stepFn _ _ hh.le]
    unfold cvecB
    rw [← Finset.sum_mul, ← Finset.sum_div, sum_getD_real ms hlen]
    field_simp

/-- The exact value: `𝒬_{F_C}(windowB) = (hX + Y/(6D³c_d)) (D/(pS))²`, `h = p/D`, `X = ∑ m_i²`,
`Y = ∑_{i,j} m_i m_j ksB(i−j)`, `S = ∑ m_i`. -/
lemma Qf_windowB (p D : ℤ) (hp : 0 < p) (hD : 0 < D) (ms : List ℤ) (hlen : ms.length = 400)
    (hl : ms.reverse = ms) (hS : 0 < ms.sum) (cn cd : ℤ) (hcd : 0 < cd) :
    Qf (FC ((cn : ℝ) / cd)) (windowB p D ms) =
      (((p : ℝ) / D) * (dot ms ms : ℝ) + (quadL ms (kerListB cn cd p D) : ℝ) / (6 * D ^ 3 * cd))
        * ((D : ℝ) / (p * (ms.sum : ℝ))) ^ 2 := by
  have hS' : (0 : ℝ) < ms.sum := by exact_mod_cast hS
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  have hc : ∀ i, cvecB p D ms i = (ms.getD i 0 : ℝ) * ((D : ℝ) / (p * (ms.sum : ℝ))) := by
    intro i; unfold cvecB; field_simp
  have hX : (dot ms ms : ℝ) = ∑ i ∈ Finset.range 400, (ms.getD i 0 : ℝ) * (ms.getD i 0 : ℝ) := by
    rw [dot_eq_sum ms ms le_rfl, hlen]; push_cast; rfl
  have hY : (quadL ms (kerListB cn cd p D) : ℝ) = ∑ i ∈ Finset.range 400, (ms.getD i 0 : ℝ) *
      ∑ j ∈ Finset.range 400, (ms.getD j 0 : ℝ) * (ksB cn cd p D ((i : ℤ) - j) : ℝ) := by
    rw [quad_eqB ms hlen hl cn cd p D]; push_cast; rfl
  unfold windowB
  rw [Qf_stepFn _ _ _ (div_pos hp' hD')]
  simp_rw [kappa_gridB cn cd p D hcd hp hD, hc]
  rw [hX, hY]
  simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_div, add_mul]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_; ring
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_; ring

/-- From the kernel-checked integer inequality to `𝒬 ≤ B/10⁶`. -/
lemma Qf_windowB_le (p D : ℤ) (hp : 0 < p) (hD : 0 < D) (ms : List ℤ) (hlen : ms.length = 400)
    (hl : ms.reverse = ms) (hS : 0 < ms.sum) (cn cd B : ℤ) (hcd : 0 < cd)
    (hcert : certCheckB p D cd B ms (kerListB cn cd p D) = true) :
    Qf (FC ((cn : ℝ) / cd)) (windowB p D ms) ≤ (B : ℝ) / 10 ^ 6 := by
  have hS' : (0 : ℝ) < ms.sum := by exact_mod_cast hS
  have hcd' : (0 : ℝ) < cd := by exact_mod_cast hcd
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  unfold certCheckB at hcert
  have hz := of_decide_eq_true hcert
  have hr : (1000000 * (6 * (p : ℝ) * (D : ℝ) ^ 2 * (cd : ℝ) * (dot ms ms : ℝ)
      + (quadL ms (kerListB cn cd p D) : ℝ))
      ≤ 6 * (B : ℝ) * (p : ℝ) ^ 2 * (D : ℝ) * (cd : ℝ) * (ms.sum : ℝ) ^ 2) := by exact_mod_cast hz
  rw [Qf_windowB p D hp hD ms hlen hl hS cn cd hcd]
  set X := (dot ms ms : ℝ)
  set Y := (quadL ms (kerListB cn cd p D) : ℝ)
  set S := (ms.sum : ℝ)
  have key : (((p : ℝ) / D) * X + Y / (6 * D ^ 3 * cd)) * ((D : ℝ) / (p * S)) ^ 2
      = (1000000 * (6 * (p : ℝ) * (D : ℝ) ^ 2 * cd * X + Y)) /
          (10 ^ 6 * (6 * (p : ℝ) ^ 2 * (D : ℝ) * cd * S ^ 2)) := by
    field_simp
    ring
  rw [key, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hr]

end Families.Hybrid.V
