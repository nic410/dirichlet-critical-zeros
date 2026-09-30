/-
# Zero side: the exceptional ("bad") characters (paper `lem:bad`)

From Montgomery's zero-density theorem in the **q-aspect range** `Montgomery69_Density_upTo 1`
(`∑_{q≤Q} ∑*_χ N(1/2+δ, T', χ) ≤ C (Q²T')^{1−cδ} (log QT')^{C₁}` for `2 ≤ T' ≤ Q`; proved as
`Families.Hyp.Montgomery.Montgomery69_Density_upTo_proof`) we bound the number of bad characters
(`Bad a B₁ Q χ`, `Families/Ported/Zero/Bridge.lean`), with the adjusted height `Q^{a|δ|}`,
`a = min(c, 1)` (so `0 < a ≤ c < 2c` and `a ≤ 1`), and `B₁` adjusted to the constants (paper §4.4):

* `bad_count_of_upTo`: `∑_{2≤q≤Q} #{χ ∈ primChars q : χ bad} ≤ C Q² (log Q)^{−K}`;
* `bad_weight_of_upTo`: `famSum W Q 1_bad ≤ C Q² (log Q)^{−K}`;
* `bad_count_unconditional`, `bad_weight_unconditional`: the same, with M's theorem fed in;
* `bad_count`, `bad_weight`: the original forms from the full `Montgomery69_Density` (all heights), kept
  for the record; they now go through `Montgomery69_Density_upTo_of_full`.

Proof (paper §4.4, `lem:bad`, Lemma 4.7). A bad `χ` (`q ≥ 2`, primitive) has, by the symmetry `ρ ↦ 1 − ρ̄`, a zero
with `δ = β − 1/2 ∈ [δ₀, 1/2)` and `|γ| ≤ Q^{aδ}`. Cut `[δ₀, 1/2)` into the shells
`[δ_j, δ_{j+1})`, `δ_j = δ₀ + j/ℓ` (`ℓ = log Q`, at most `ℓ + 1` of them), and put
`T_j = Q^{a δ_{j+1}}`; then `N(1/2+δ_j, T_j, χ) ≥ 1` for the shell of the witness. Summing
Montgomery's bound over the shells, `(Q²T_j)^{1−cδ_j} ≤ e^c Q² Q^{−cδ₀} = e^c Q² ℓ^{−cB₁}` and
`log(QT_j) ≤ (1+c)ℓ`, so `#bad ≪ Q² ℓ^{1 + C₁⁺ − cB₁}`. The weighted version follows from
`ω(q) ≤ w_max q/φ(q)`, `b_q ≤ φ(q)` and `(q/φ) b ≤ (ε q²/φ + b/ε)/2`, with `∑ q/φ(q) ≤ 2Q`.

**Heights.** Montgomery's bound is invoked only at `(σ, T') = (1/2 + δ_j, T_j)` for the shells
`j ∈ shells B₁ Q` (`δ_j ≤ 1/2`), and only for `Q ≥ e²` (the `Q₀` of `bad_count_of_upTo`). There
`ℓ ≥ 2`, so `δ_{j+1} = δ_j + 1/ℓ ≤ 1`, and with `a ≤ 1`, `T_j = Q^{a δ_{j+1}} ≤ Q` (`shellT_le_self`);
also `T_j ≥ ℓ ≥ 2` (`shell_estimates`). So the range `2 ≤ T' ≤ Q = Q^1` of
`Montgomery69_Density_upTo 1` suffices; no height above `Q` is needed.
-/
import Families.Ported.Zero.Bridge
import Families.Schur
import Families.Hyp.Montgomery.TAspect

noncomputable section

open scoped BigOperators ComplexConjugate
open Complex Set

namespace Families.Ported.Zero

open Zeta23 Zeta23.ThmE

/-! ### A bad character has a zero in some shell -/

section Char

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- For `σ > 0` the zero set counted by `Ndens χ σ T` is finite (`χ` primitive mod `q > 1`). -/
lemma Ndens_set_finite (hq : 1 < q) (hprim : χ.IsPrimitive) {σ T : ℝ} (hσ : 0 < σ) :
    {ρ : ℂ | Lfun χ ρ = 0 ∧ σ ≤ ρ.re ∧ |ρ.im| ≤ T}.Finite := by
  have hχ1 : χ ≠ 1 := ne_one_of_primitive hq hprim
  refine ((LSeam_of hq hprim).finite_window (-T - 1) T).subset ?_
  rintro ρ ⟨h0, hre, him⟩
  rw [Lfun_eq] at h0
  have h1 : ρ.re < 1 := by
    by_contra hle
    push Not at hle
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1) hle h0
  have := abs_le.mp him
  exact ⟨⟨h0, by linarith, h1⟩, by linarith, by linarith⟩

/-- A zero `ρ` with `σ ≤ β < 1`, `|γ| ≤ T` (`σ > 0`) gives `N(σ, T, χ) ≥ 1`. -/
lemma one_le_Ndens (hq : 1 < q) (hprim : χ.IsPrimitive) {σ T : ℝ} (hσ : 0 < σ) {ρ : ℂ}
    (h0 : Lfun χ ρ = 0) (hre1 : ρ.re < 1) (hre : σ ≤ ρ.re) (him : |ρ.im| ≤ T) :
    1 ≤ Ndens χ σ T := by
  have hfin := Ndens_set_finite hq hprim hσ (T := T)
  unfold Ndens
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hmem : ρ ∈ hfin.toFinset := by
    rw [Set.Finite.mem_toFinset]; exact ⟨h0, hre, him⟩
  have h1 : 1 ≤ mult χ ρ := by
    rw [mult_eq]
    exact (LSeam_of hq hprim).one_le_mult ρ ⟨by rwa [Lfun_eq] at h0, by linarith, hre1⟩
  exact h1.trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem)

/-- The symmetry `ρ ↦ 1 − ρ̄`: a nontrivial zero `ρ` gives one with `β' − 1/2 = |β − 1/2|` and
the same ordinate. -/
lemma exists_right_zero (hq : 1 < q) (hprim : χ.IsPrimitive) {ρ : ℂ} (h0 : Lfun χ ρ = 0)
    (h1 : 0 < ρ.re) (h2 : ρ.re < 1) :
    ∃ ρ' : ℂ, Lfun χ ρ' = 0 ∧ ρ'.re < 1 ∧ ρ'.re - 1 / 2 = |ρ.re - 1 / 2| ∧ ρ'.im = ρ.im := by
  rcases le_or_gt (1 / 2 : ℝ) ρ.re with h | h
  · exact ⟨ρ, h0, h2, (abs_of_nonneg (by linarith)).symm, rfl⟩
  · have hnt : IsNontrivialZeroL χ ρ := ⟨by rwa [Lfun_eq] at h0, h1, h2⟩
    have hr := (LSeam_of hq hprim).reflect_zero ρ hnt
    refine ⟨reflect ρ, by rw [Lfun_eq]; exact hr.1, hr.2.2, ?_, ?_⟩
    · rw [abs_of_neg (by linarith)]; simp [reflect]; ring
    · simp [reflect]

end Char

/-! ### Shells -/

/-- `δ_j = δ₀ + j/ℓ`, `ℓ = log Q`. -/
def shellD (B₁ Q : ℝ) (j : ℕ) : ℝ := delta0 B₁ Q + j / Real.log Q

/-- `T_j = Q^{a δ_{j+1}}`. -/
def shellT (a B₁ Q : ℝ) (j : ℕ) : ℝ := Q ^ (a * shellD B₁ Q (j + 1))

/-- The shells `j ≤ ⌊ℓ⌋` with `δ_j ≤ 1/2` (the only ones that can contain a bad zero). -/
def shells (B₁ Q : ℝ) : Finset ℕ :=
  (Finset.range (⌊Real.log Q⌋₊ + 1)).filter (fun j => shellD B₁ Q j ≤ 1 / 2)

/-- A bad character (`q > 1`, primitive) has `N(1/2 + δ_j, T_j, χ) ≥ 1` for some shell `j`. -/
lemma bad_mem_shell {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hq : 1 < q)
    (hprim : χ.IsPrimitive) {a B₁ Q : ℝ} (ha : 0 < a) (hQ : 1 < Q) (hδ₀ : 0 ≤ delta0 B₁ Q)
    (hbad : Bad a B₁ Q χ) :
    ∃ j ∈ shells B₁ Q, 1 ≤ Ndens χ (1 / 2 + shellD B₁ Q j) (shellT a B₁ Q j) := by
  obtain ⟨ρ, h0, h1, h2, hd, him⟩ := hbad
  obtain ⟨ρ', h0', h2', hre', him'⟩ := exists_right_zero hq hprim h0 h1 h2
  have hℓ : 0 < Real.log Q := Real.log_pos hQ
  have hδlt : |ρ.re - 1 / 2| < 1 / 2 := by rw [abs_lt]; constructor <;> linarith
  have hx0 : 0 ≤ (|ρ.re - 1 / 2| - delta0 B₁ Q) * Real.log Q := mul_nonneg (by linarith) hℓ.le
  have hjle : ((⌊(|ρ.re - 1 / 2| - delta0 B₁ Q) * Real.log Q⌋₊ : ℕ) : ℝ) ≤
      (|ρ.re - 1 / 2| - delta0 B₁ Q) * Real.log Q := Nat.floor_le hx0
  have hjlt : (|ρ.re - 1 / 2| - delta0 B₁ Q) * Real.log Q <
      ⌊(|ρ.re - 1 / 2| - delta0 B₁ Q) * Real.log Q⌋₊ + 1 := Nat.lt_floor_add_one _
  set j := ⌊(|ρ.re - 1 / 2| - delta0 B₁ Q) * Real.log Q⌋₊ with hj
  have hD : shellD B₁ Q j ≤ |ρ.re - 1 / 2| := by
    unfold shellD
    have : (j : ℝ) / Real.log Q ≤ |ρ.re - 1 / 2| - delta0 B₁ Q := by
      rw [div_le_iff₀ hℓ]; exact hjle
    linarith
  have hD1 : |ρ.re - 1 / 2| < shellD B₁ Q (j + 1) := by
    unfold shellD
    have : |ρ.re - 1 / 2| - delta0 B₁ Q < ((j + 1 : ℕ) : ℝ) / Real.log Q := by
      rw [lt_div_iff₀ hℓ]; push_cast; exact hjlt
    linarith
  have hD0 : 0 ≤ shellD B₁ Q j := add_nonneg hδ₀ (div_nonneg (Nat.cast_nonneg _) hℓ.le)
  refine ⟨j, ?_, ?_⟩
  · simp only [shells, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, by linarith⟩
    have : j ≤ ⌊Real.log Q⌋₊ := Nat.floor_le_floor (by nlinarith)
    omega
  · refine one_le_Ndens hq hprim (by linarith) h0' h2' (by linarith) ?_
    rw [him']
    refine him.trans ?_
    unfold shellT
    exact Real.rpow_le_rpow_of_exponent_le hQ.le (mul_le_mul_of_nonneg_left hD1.le ha.le)

/-! ### The shell estimate -/

/-- For `Q ≥ e²`, `cB₁ ≥ 1` and `δ_j ≤ 1/2`: `δ_j ≥ 0`, `T_j ≥ 2`, and Montgomery's bound at
`(1/2 + δ_j, T_j)` is at most `e^{c + 2ℓ − cB₁ log ℓ} ((1+c)ℓ)^{C₁⁺}`. -/
lemma shell_estimates {c B₁ C₁ Q : ℝ} (hc : 0 < c) (hQ : Real.exp 2 ≤ Q) (hB : 1 ≤ c * B₁)
    {j : ℕ} (hj : shellD B₁ Q j ≤ 1 / 2) :
    0 ≤ shellD B₁ Q j ∧ 2 ≤ shellT c B₁ Q j ∧
    (Q ^ 2 * shellT c B₁ Q j) ^ (1 - c * shellD B₁ Q j) * Real.log (Q * shellT c B₁ Q j) ^ C₁
      ≤ Real.exp (c + 2 * Real.log Q - c * B₁ * Real.log (Real.log Q)) *
          ((1 + c) * Real.log Q) ^ (max C₁ 0) := by
  have hQ0 : 0 < Q := lt_of_lt_of_le (Real.exp_pos 2) hQ
  obtain ⟨ℓ, rfl⟩ : ∃ ℓ, Q = Real.exp ℓ := ⟨Real.log Q, (Real.exp_log hQ0).symm⟩
  have hℓ2 : 2 ≤ ℓ := Real.exp_le_exp.mp hQ
  have hℓ : 0 < ℓ := by linarith
  have hL : 0 < Real.log ℓ := Real.log_pos (by linarith)
  have hB₁ : 0 < B₁ := by
    by_contra h; push Not at h; nlinarith
  simp only [shellD, shellT, delta0, Real.log_exp] at hj ⊢
  set L := Real.log ℓ with hLdef
  set d : ℝ := B₁ * L / ℓ + j / ℓ with hd
  have hd1 : B₁ * L / ℓ + ((j + 1 : ℕ) : ℝ) / ℓ = d + 1 / ℓ := by
    rw [hd]; push_cast; ring
  rw [hd1]
  have hd0 : 0 ≤ d := by positivity
  have hu : ℓ * d = B₁ * L + j := by rw [hd]; field_simp
  have hu1 : ℓ * (c * (d + 1 / ℓ)) = c * (ℓ * d) + c := by field_simp
  have hT : Real.exp ℓ ^ (c * (d + 1 / ℓ)) = Real.exp (c * (ℓ * d) + c) := by
    rw [← Real.exp_mul, hu1]
  rw [hT]
  refine ⟨hd0, ?_, ?_⟩
  · -- `T_j ≥ ℓ ≥ 2`
    have : Real.log ℓ ≤ c * (ℓ * d) + c := by
      rw [hu]
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      nlinarith
    calc (2 : ℝ) ≤ ℓ := hℓ2
      _ = Real.exp (Real.log ℓ) := (Real.exp_log hℓ).symm
      _ ≤ _ := Real.exp_le_exp.mpr this
  · have hsq : Real.exp ℓ ^ 2 * Real.exp (c * (ℓ * d) + c) =
        Real.exp (2 * ℓ + (c * (ℓ * d) + c)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
    have hlog : Real.log (Real.exp ℓ * Real.exp (c * (ℓ * d) + c)) = ℓ + (c * (ℓ * d) + c) := by
      rw [← Real.exp_add, Real.log_exp]
    rw [hsq, hlog, ← Real.exp_mul]
    have hud : B₁ * L ≤ ℓ * d := by rw [hu]; linarith [Nat.cast_nonneg (α := ℝ) j]
    have hudh : ℓ * d ≤ ℓ / 2 := by nlinarith
    have hexp : (2 * ℓ + (c * (ℓ * d) + c)) * (1 - c * d) ≤ c + 2 * ℓ - c * B₁ * L := by
      have e : (2 * ℓ + (c * (ℓ * d) + c)) * (1 - c * d) =
          2 * ℓ + c - c * (ℓ * d) - c ^ 2 * (ℓ * d) * d - c ^ 2 * d := by ring
      rw [e]
      have : 0 ≤ c ^ 2 * (ℓ * d) * d := by positivity
      have : 0 ≤ c ^ 2 * d := by positivity
      have : c * (B₁ * L) ≤ c * (ℓ * d) := mul_le_mul_of_nonneg_left hud hc.le
      nlinarith
    have hx1 : 1 ≤ ℓ + (c * (ℓ * d) + c) := by
      have : 0 ≤ c * (ℓ * d) := by positivity
      linarith
    have hx2 : ℓ + (c * (ℓ * d) + c) ≤ (1 + c) * ℓ := by nlinarith
    refine mul_le_mul (Real.exp_le_exp.mpr hexp) ?_ (by positivity) (by positivity)
    calc (ℓ + (c * (ℓ * d) + c)) ^ C₁ ≤ (ℓ + (c * (ℓ * d) + c)) ^ (max C₁ 0) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (le_max_left _ _)
      _ ≤ ((1 + c) * ℓ) ^ (max C₁ 0) :=
          Real.rpow_le_rpow (by linarith) hx2 (le_max_right _ _)

/-! ### The heights stay in the q-aspect range -/

/-- **The heights at which Montgomery's bound is invoked are `≤ Q`.** For `Q ≥ e²` (so
`ℓ = log Q ≥ 2`), `0 ≤ a ≤ 1` and a shell `j` (`δ_j ≤ 1/2`): `δ_{j+1} = δ_j + 1/ℓ ≤ 1`, hence
`T_j = Q^{a δ_{j+1}} ≤ Q`. -/
lemma shellT_le_self {a B₁ Q : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hQ : Real.exp 2 ≤ Q) {j : ℕ}
    (hj : shellD B₁ Q j ≤ 1 / 2) : shellT a B₁ Q j ≤ Q := by
  have hQ1 : 1 ≤ Q := le_trans (by linarith [Real.add_one_le_exp (2 : ℝ)]) hQ
  have hℓ2 : 2 ≤ Real.log Q := by
    have := Real.log_le_log (Real.exp_pos 2) hQ
    rwa [Real.log_exp] at this
  have hD1 : shellD B₁ Q (j + 1) ≤ 1 := by
    have e : shellD B₁ Q (j + 1) = shellD B₁ Q j + 1 / Real.log Q := by
      unfold shellD; push_cast; ring
    have : 1 / Real.log Q ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hℓ2
    linarith
  unfold shellT
  calc Q ^ (a * shellD B₁ Q (j + 1)) ≤ Q ^ (1 : ℝ) := by
        refine Real.rpow_le_rpow_of_exponent_le hQ1 ?_
        calc a * shellD B₁ Q (j + 1) ≤ a * 1 := mul_le_mul_of_nonneg_left hD1 ha0
          _ ≤ 1 := by linarith
    _ = Q := Real.rpow_one Q

/-! ### The count -/

open Classical in
/-- **`lem:bad`, unweighted, from the q-aspect Montgomery bound.** From
`Montgomery69_Density_upTo 1` (heights `2 ≤ T' ≤ Q` only), the number of bad primitive characters of
modulus `2 ≤ q ≤ Q` is `≤ C Q² (log Q)^{−K}`, with `a = min(c, 1)` (`c` the Montgomery exponent) and
`B₁` depending on `K`, for `Q ≥ Q₀ = e²`. The bound is invoked only at the heights `T_j ≤ Q`
(`shellT_le_self`). -/
theorem bad_count_of_upTo (hM : Hyp.Montgomery.Montgomery69_Density_upTo 1) :
    ∃ a : ℝ, 0 < a ∧ ∀ K : ℝ, ∃ B₁ : ℝ, 0 < B₁ ∧
    ∃ C Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
      ∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, ((((primChars q).filter (fun χ => Bad a B₁ Q χ)).card : ℕ) : ℝ)
        ≤ C * Q ^ 2 * Real.log Q ^ (-K) := by
  obtain ⟨C, c₀, C₁, hc₀, hMb₀⟩ := hM
  -- `a = c = min(c₀, 1)`: shrinking the exponent keeps Montgomery's bound, and `a ≤ 1` keeps `T_j ≤ Q`
  obtain ⟨c, hc, hc1, hcc₀⟩ : ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ c ≤ c₀ :=
    ⟨min c₀ 1, lt_min hc₀ one_pos, min_le_right _ _, min_le_left _ _⟩
  refine ⟨c, hc, fun K => ?_⟩
  set D := max C₁ 0 with hDdef
  have hD0 : 0 ≤ D := le_max_right _ _
  have hK0 : K ≤ max K 0 := le_max_left _ _
  have hK0' : 0 ≤ max K 0 := le_max_right _ _
  set B₁ := (D + 2 + max K 0) / c with hB₁def
  have hcB : c * B₁ = D + 2 + max K 0 := by rw [hB₁def]; field_simp
  have hB₁ : 0 < B₁ := by rw [hB₁def]; positivity
  refine ⟨B₁, hB₁, 2 * |C| * Real.exp c * (1 + c) ^ D, Real.exp 2, fun Q hQ => ?_⟩
  have hQ0 : 0 < Q := lt_of_lt_of_le (Real.exp_pos 2) hQ
  have hℓ2 : 2 ≤ Real.log Q := by
    have := Real.log_le_log (Real.exp_pos 2) hQ
    rwa [Real.log_exp] at this
  have hℓ : 0 < Real.log Q := by linarith
  have hL : 0 < Real.log (Real.log Q) := Real.log_pos (by linarith)
  have hQ1' : 1 < Q := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hQ1 : 1 ≤ Q := hQ1'.le
  have hδ₀ : 0 ≤ delta0 B₁ Q := by unfold delta0; positivity
  set M := Real.exp (c + 2 * Real.log Q - c * B₁ * Real.log (Real.log Q)) *
    ((1 + c) * Real.log Q) ^ D with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  -- Step A: every bad character is counted by the shell sums.
  have hA : ∑ q ∈ Finset.Icc 2 ⌊Q⌋₊,
        ((((primChars q).filter (fun χ => Bad c B₁ Q χ)).card : ℕ) : ℝ)
      ≤ ∑ j ∈ shells B₁ Q, ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ ∈ primChars q,
          (Ndens χ (1 / 2 + shellD B₁ Q j) (shellT c B₁ Q j) : ℝ) := by
    calc _ = ∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, ∑ χ ∈ primChars q,
            (if Bad c B₁ Q χ then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [Finset.sum_boole]
      _ ≤ ∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, ∑ χ ∈ primChars q, ∑ j ∈ shells B₁ Q,
            (Ndens χ (1 / 2 + shellD B₁ Q j) (shellT c B₁ Q j) : ℝ) := by
          refine Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun χ hχ => ?_
          have hq2 : 2 ≤ q := (Finset.mem_Icc.mp hq).1
          have : NeZero q := ⟨by omega⟩
          split_ifs with hbad
          · obtain ⟨j, hj, h1⟩ :=
              bad_mem_shell (by omega) (mem_primChars hχ) hc hQ1' hδ₀ hbad
            exact (by exact_mod_cast h1 : (1 : ℝ) ≤ _).trans
              (Finset.single_le_sum
                (f := fun j => (Ndens χ (1 / 2 + shellD B₁ Q j) (shellT c B₁ Q j) : ℝ))
                (fun _ _ => Nat.cast_nonneg _) hj)
          · exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
      _ = ∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, ∑ j ∈ shells B₁ Q, ∑ χ ∈ primChars q,
            (Ndens χ (1 / 2 + shellD B₁ Q j) (shellT c B₁ Q j) : ℝ) :=
          Finset.sum_congr rfl fun q _ => Finset.sum_comm
      _ = ∑ j ∈ shells B₁ Q, ∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, ∑ χ ∈ primChars q,
            (Ndens χ (1 / 2 + shellD B₁ Q j) (shellT c B₁ Q j) : ℝ) := Finset.sum_comm
      _ ≤ _ := by
          refine Finset.sum_le_sum fun j _ => ?_
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.Icc_subset_Icc_left (by norm_num))
            (fun _ _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
  -- Step B: Montgomery on each shell, at the height `T_j ≤ Q` (q-aspect range, `Q ≥ e²`).
  have hB : ∀ j ∈ shells B₁ Q, ∑ q ∈ Finset.Icc 1 ⌊Q⌋₊, ∑ χ ∈ primChars q,
      (Ndens χ (1 / 2 + shellD B₁ Q j) (shellT c B₁ Q j) : ℝ) ≤ |C| * M := by
    intro j hj
    have hj' : shellD B₁ Q j ≤ 1 / 2 := (Finset.mem_filter.mp hj).2
    obtain ⟨hd0, hT2, hbd⟩ := shell_estimates (C₁ := C₁) hc hQ (by rw [hcB]; linarith) hj'
    have hTQ : shellT c B₁ Q j ≤ Q ^ (1 : ℝ) := by
      rw [Real.rpow_one]; exact shellT_le_self hc.le hc1 hQ hj'
    have h := hMb₀ Q hQ1 _ hT2 hTQ _ hd0 hj'
    have hX1 : 1 ≤ Q ^ 2 * shellT c B₁ Q j :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ hQ1) (by linarith)
    have hX : 0 ≤ (Q ^ 2 * shellT c B₁ Q j) ^ (1 - c₀ * shellD B₁ Q j) :=
      Real.rpow_nonneg (by linarith) _
    have hY : 0 ≤ Real.log (Q * shellT c B₁ Q j) ^ C₁ :=
      Real.rpow_nonneg (Real.log_nonneg (one_le_mul_of_one_le_of_one_le hQ1 (by linarith))) _
    -- the exponent `c ≤ c₀`: `(Q²T_j)^{1−c₀δ_j} ≤ (Q²T_j)^{1−cδ_j}` since `Q²T_j ≥ 1`
    have hmono : (Q ^ 2 * shellT c B₁ Q j) ^ (1 - c₀ * shellD B₁ Q j) ≤
        (Q ^ 2 * shellT c B₁ Q j) ^ (1 - c * shellD B₁ Q j) := by
      refine Real.rpow_le_rpow_of_exponent_le hX1 ?_
      have := mul_le_mul_of_nonneg_right hcc₀ hd0
      linarith
    calc _ ≤ _ := h
      _ ≤ |C| * ((Q ^ 2 * shellT c B₁ Q j) ^ (1 - c₀ * shellD B₁ Q j) *
            Real.log (Q * shellT c B₁ Q j) ^ C₁) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) hX) hY
      _ ≤ |C| * ((Q ^ 2 * shellT c B₁ Q j) ^ (1 - c * shellD B₁ Q j) *
            Real.log (Q * shellT c B₁ Q j) ^ C₁) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmono hY) (abs_nonneg C)
      _ ≤ |C| * M := mul_le_mul_of_nonneg_left hbd (abs_nonneg C)
  -- Step C: at most `2ℓ` shells.
  have hcard : ((shells B₁ Q).card : ℝ) ≤ 2 * Real.log Q := by
    have h1 : (shells B₁ Q).card ≤ ⌊Real.log Q⌋₊ + 1 :=
      (Finset.card_filter_le _ _).trans (Finset.card_range _).le
    have h2 : ((⌊Real.log Q⌋₊ : ℕ) : ℝ) ≤ Real.log Q := Nat.floor_le hℓ.le
    have : ((shells B₁ Q).card : ℝ) ≤ (⌊Real.log Q⌋₊ : ℝ) + 1 := by exact_mod_cast h1
    linarith
  -- Step D: `2ℓ · e^{c + 2ℓ − cB₁ log ℓ} ((1+c)ℓ)^D ≪ Q² ℓ^{−K}`.
  have hQ2 : Q ^ 2 = Real.exp (2 * Real.log Q) := by
    rw [show (2 : ℝ) * Real.log Q = ((2 : ℕ) : ℝ) * Real.log Q by norm_num, Real.exp_nat_mul,
      Real.exp_log hQ0]
  have hℓD : Real.log Q * Real.log Q ^ D = Real.exp (Real.log (Real.log Q) * (1 + D)) := by
    rw [← Real.rpow_def_of_pos hℓ, Real.rpow_add hℓ, Real.rpow_one]
  have hℓK : Real.log Q ^ (-K) = Real.exp (Real.log (Real.log Q) * (-K)) :=
    Real.rpow_def_of_pos hℓ _
  have hexp : c + 2 * Real.log Q - c * B₁ * Real.log (Real.log Q) +
      Real.log (Real.log Q) * (1 + D) ≤ c + 2 * Real.log Q + Real.log (Real.log Q) * (-K) := by
    have e : c * B₁ * Real.log (Real.log Q) = (D + 2 + max K 0) * Real.log (Real.log Q) := by
      rw [hcB]
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left hK0 hL.le]
  calc _ ≤ _ := hA
    _ ≤ ∑ j ∈ shells B₁ Q, |C| * M := Finset.sum_le_sum hB
    _ = (shells B₁ Q).card * (|C| * M) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * Real.log Q) * (|C| * M) :=
        mul_le_mul_of_nonneg_right hcard (mul_nonneg (abs_nonneg C) hM0)
    _ = (2 * |C| * (1 + c) ^ D) *
          Real.exp (c + 2 * Real.log Q - c * B₁ * Real.log (Real.log Q) +
            Real.log (Real.log Q) * (1 + D)) := by
        rw [hMdef, Real.mul_rpow (by positivity) hℓ.le, Real.exp_add, ← hℓD]
        ring
    _ ≤ (2 * |C| * (1 + c) ^ D) *
          Real.exp (c + 2 * Real.log Q + Real.log (Real.log Q) * (-K)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
    _ = 2 * |C| * Real.exp c * (1 + c) ^ D * Q ^ 2 * Real.log Q ^ (-K) := by
        rw [hQ2, hℓK, Real.exp_add, Real.exp_add]
        ring

open Classical in
/-- **`lem:bad`, unweighted, unconditional** (`bad_count_of_upTo` with
`Montgomery69_Density_upTo_proof 1`). -/
theorem bad_count_unconditional : ∃ a : ℝ, 0 < a ∧ ∀ K : ℝ, ∃ B₁ : ℝ, 0 < B₁ ∧
    ∃ C Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
      ∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, ((((primChars q).filter (fun χ => Bad a B₁ Q χ)).card : ℕ) : ℝ)
        ≤ C * Q ^ 2 * Real.log Q ^ (-K) :=
  bad_count_of_upTo (Hyp.Montgomery.Montgomery69_Density_upTo_proof 1 one_pos)

open Classical in
/-- **`lem:bad`, unweighted, from the full `Montgomery69_Density`** (all heights; the original form,
kept for the record). It only uses the heights `T' ≤ Q`, via `bad_count_of_upTo`. -/
theorem bad_count (hM : Montgomery69_Density) : ∃ a : ℝ, 0 < a ∧ ∀ K : ℝ, ∃ B₁ : ℝ, 0 < B₁ ∧
    ∃ C Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
      ∑ q ∈ Finset.Icc 2 ⌊Q⌋₊, ((((primChars q).filter (fun χ => Bad a B₁ Q χ)).card : ℕ) : ℝ)
        ≤ C * Q ^ 2 * Real.log Q ^ (-K) :=
  bad_count_of_upTo (Hyp.Montgomery.Montgomery69_Density_upTo_of_full 1 hM)

/-- AM–GM: `(x/f) b ≤ (ε x²/f + b/ε)/2` for `0 ≤ b ≤ f`. -/
lemma amgm_aux {x b f ε : ℝ} (hb : 0 ≤ b) (hbf : b ≤ f) (hf : 0 < f) (hε : 0 < ε) :
    x / f * b ≤ (ε * (x ^ 2 / f) + b / ε) / 2 := by
  have key : 2 * ε * x * b ≤ ε ^ 2 * x ^ 2 + b * f := by
    nlinarith [sq_nonneg (ε * x - b), mul_le_mul_of_nonneg_left hbf hb]
  have : (ε * (x ^ 2 / f) + b / ε) / 2 - x / f * b =
      (ε ^ 2 * x ^ 2 + b * f - 2 * ε * x * b) / (2 * ε * f) := by
    field_simp
  have h2 : 0 ≤ (ε ^ 2 * x ^ 2 + b * f - 2 * ε * x * b) / (2 * ε * f) :=
    div_nonneg (by linarith) (by positivity)
  linarith

open Classical in
/-- **`lem:bad`, weighted, from the q-aspect Montgomery bound.**
`∑_{χ ∈ 𝓕} ω_χ 1_{χ bad} ≤ C Q² (log Q)^{−K}`, from `Montgomery69_Density_upTo 1`. -/
theorem bad_weight_of_upTo (hM : Hyp.Montgomery.Montgomery69_Density_upTo 1) :
    ∃ a : ℝ, 0 < a ∧ ∀ K : ℝ, ∃ B₁ : ℝ, 0 < B₁ ∧
    ∀ W : Weight, ∃ C Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
      famSum W Q (fun _ χ => if Bad a B₁ Q χ then (1 : ℝ) else 0) ≤
        C * Q ^ 2 * Real.log Q ^ (-K) := by
  obtain ⟨a, ha, h⟩ := bad_count_of_upTo hM
  refine ⟨a, ha, fun K => ?_⟩
  obtain ⟨B₁, hB₁, Cb, Q₀, hb⟩ := h (2 * K)
  refine ⟨B₁, hB₁, fun W => ⟨W.wmax * (2 + Cb) / 2, max Q₀ (max 3 (2 / W.η)), fun Q hQ => ?_⟩⟩
  have hQ₀ : Q₀ ≤ Q := le_trans (le_max_left _ _) hQ
  have hQ3 : 3 ≤ Q := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hQ
  have hQη : 2 / W.η ≤ Q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hQ
  have hQ0 : 0 < Q := by linarith
  have hℓ : 0 < Real.log Q := Real.log_pos (by linarith)
  have hwmax : 0 ≤ W.wmax := (W.nonneg 0).trans (W.le_wmax 0)
  set ε := Real.log Q ^ (-K) with hεdef
  have hε : 0 < ε := Real.rpow_pos_of_pos hℓ _
  set N := ⌊Q⌋₊ with hN
  have hNQ : (N : ℝ) ≤ Q := Nat.floor_le hQ0.le
  set b : ℕ → ℝ := fun q => ((((primChars q).filter (fun χ => Bad a B₁ Q χ)).card : ℕ) : ℝ)
    with hbdef
  -- `b_q ≤ φ(q)`
  have hb_le : ∀ q ∈ Finset.Icc 2 N, b q ≤ Nat.totient q := by
    intro q hq
    have hq1 : 0 < q := by have := (Finset.mem_Icc.mp hq).1; omega
    have : NeZero q := ⟨hq1.ne'⟩
    have h1 : ((primChars q).filter (fun χ => Bad a B₁ Q χ)).card ≤
        Fintype.card (DirichletCharacter ℂ q) :=
      (Finset.card_filter_le _ _).trans (Finset.card_le_univ _)
    have h2 : Fintype.card (DirichletCharacter ℂ q) = Nat.totient q := by
      rw [← Nat.card_eq_fintype_card]
      exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
    simp only [hbdef]
    exact_mod_cast h1.trans h2.le
  -- the `q = 1` term vanishes (`w(1/Q) = 0` since `1/Q < η`)
  have hw1 : W.w (((1 : ℕ) : ℝ) / Q) = 0 := by
    by_contra hne
    have h1 := (W.supp _ hne).1
    have h2 : 2 ≤ Q * W.η := (div_le_iff₀ W.η_pos).mp hQη
    rw [Nat.cast_one, le_div_iff₀ hQ0] at h1
    nlinarith [W.η_pos]
  have hfam : famSum W Q (fun _ χ => if Bad a B₁ Q χ then (1 : ℝ) else 0) =
      ∑ q ∈ Finset.Icc 2 N, W.omega Q q * b q := by
    unfold famSum
    simp only [Finset.sum_boole]
    refine (Finset.sum_subset (Finset.Icc_subset_Icc_left (by norm_num)) ?_).symm
    intro q hq hq'
    have : q = 1 := by
      simp only [Finset.mem_Icc] at hq hq'
      omega
    subst this
    simp only [Weight.omega, hw1, zero_mul, zero_div]
  rw [hfam]
  -- termwise: `ω(q) b_q ≤ w_max (ε q²/φ(q) + b_q/ε)/2`
  have hterm : ∀ q ∈ Finset.Icc 2 N, W.omega Q q * b q ≤
      W.wmax * ((ε * ((q : ℝ) ^ 2 / Nat.totient q) + b q / ε) / 2) := by
    intro q hq
    have hq1 : 0 < q := by have := (Finset.mem_Icc.mp hq).1; omega
    have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq1
    have hb0 : 0 ≤ b q := Nat.cast_nonneg _
    calc W.omega Q q * b q = W.w (q / Q) * ((q : ℝ) / Nat.totient q * b q) := by
          unfold Weight.omega; ring
      _ ≤ W.wmax * ((q : ℝ) / Nat.totient q * b q) :=
          mul_le_mul_of_nonneg_right (W.le_wmax _) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (amgm_aux hb0 (hb_le q hq) hφ hε) hwmax
  -- `∑_{q ≤ Q} q²/φ(q) ≤ 2Q²`
  have hA : ∑ q ∈ Finset.Icc 2 N, ((q : ℝ) ^ 2 / Nat.totient q) ≤ 2 * Q ^ 2 := by
    calc _ ≤ ∑ q ∈ Finset.Icc 1 N, ((q : ℝ) ^ 2 / Nat.totient q) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_left (by norm_num))
            (fun _ _ _ => by positivity)
      _ ≤ ∑ q ∈ Finset.Icc 1 N, (N : ℝ) * ((q : ℝ) / Nat.totient q) := by
          refine Finset.sum_le_sum fun q hq => ?_
          have hqN : (q : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hq).2
          rw [sq, mul_div_assoc]
          exact mul_le_mul_of_nonneg_right hqN (by positivity)
      _ = N * ∑ q ∈ Finset.Icc 1 N, ((q : ℝ) / Nat.totient q) := by rw [Finset.mul_sum]
      _ ≤ N * (2 * N) :=
          mul_le_mul_of_nonneg_left (Families.sum_div_totient_le N) (Nat.cast_nonneg _)
      _ ≤ 2 * Q ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hbQ : ∑ q ∈ Finset.Icc 2 N, b q ≤ Cb * Q ^ 2 * Real.log Q ^ (-(2 * K)) := hb Q hQ₀
  have hratio : Cb * Q ^ 2 * Real.log Q ^ (-(2 * K)) / ε = Cb * Q ^ 2 * ε := by
    rw [mul_div_assoc, hεdef, ← Real.rpow_sub hℓ]
    congr 2; ring
  calc ∑ q ∈ Finset.Icc 2 N, W.omega Q q * b q
      ≤ ∑ q ∈ Finset.Icc 2 N, W.wmax * ((ε * ((q : ℝ) ^ 2 / Nat.totient q) + b q / ε) / 2) :=
        Finset.sum_le_sum hterm
    _ = W.wmax / 2 * (ε * ∑ q ∈ Finset.Icc 2 N, ((q : ℝ) ^ 2 / Nat.totient q) +
          (∑ q ∈ Finset.Icc 2 N, b q) / ε) := by
        rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun q _ => by ring
    _ ≤ W.wmax / 2 * (ε * (2 * Q ^ 2) + Cb * Q ^ 2 * Real.log Q ^ (-(2 * K)) / ε) := by
        refine mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hA hε.le)
          (div_le_div_of_nonneg_right hbQ hε.le)) (by positivity)
    _ = W.wmax * (2 + Cb) / 2 * Q ^ 2 * ε := by
        rw [hratio]; ring

open Classical in
/-- **`lem:bad`, weighted, unconditional** (`bad_weight_of_upTo` with
`Montgomery69_Density_upTo_proof 1`). -/
theorem bad_weight_unconditional : ∃ a : ℝ, 0 < a ∧ ∀ K : ℝ, ∃ B₁ : ℝ, 0 < B₁ ∧
    ∀ W : Weight, ∃ C Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
      famSum W Q (fun _ χ => if Bad a B₁ Q χ then (1 : ℝ) else 0) ≤
        C * Q ^ 2 * Real.log Q ^ (-K) :=
  bad_weight_of_upTo (Hyp.Montgomery.Montgomery69_Density_upTo_proof 1 one_pos)

open Classical in
/-- **`lem:bad`, weighted, from the full `Montgomery69_Density`** (the original form, kept for the
record; via `bad_weight_of_upTo`). -/
theorem bad_weight (hM : Montgomery69_Density) : ∃ a : ℝ, 0 < a ∧ ∀ K : ℝ, ∃ B₁ : ℝ, 0 < B₁ ∧
    ∀ W : Weight, ∃ C Q₀ : ℝ, ∀ Q : ℝ, Q₀ ≤ Q →
      famSum W Q (fun _ χ => if Bad a B₁ Q χ then (1 : ℝ) else 0) ≤
        C * Q ^ 2 * Real.log Q ^ (-K) :=
  bad_weight_of_upTo (Hyp.Montgomery.Montgomery69_Density_upTo_of_full 1 hM)

end Families.Ported.Zero
