/-
The local count along spokes with a coprimality twist, and
**`prop:count`** (`lemma-A.tex`) as its case `r = 1`.

For squarefree `r` let `ν = ∑_{q ≤ Q, (q,r)=1} 𝔴(q/Q) ∑*_{b mod q} δ_{b/q}`. With a Dirichlet
approximation `u/v` of `θ` (`1 ≤ v ≤ V`, `|θ − u/v| ≤ 1/(vV)`), `y = θ − u/v`, `k_* = Q/V + QVς`:

  `(ν * k_ς)(θ) = 1[(v,r)=1] 𝔴(v/Q) k₀(y) + ∫ k₀(z−y) ρ_r(z) dz + ϱ`,
  `|ϱ| ≤ τ(r) · 4 V_𝔴 ς⁻¹ k_* (1 + log⁺ k_*)`,

`ρ_r(z) = (vz)^{-2} ∑_{k≥1} k G_S(k,r) 𝔴(k/(v|z|Q))`, `S` = primes of `v` (`lemma-toeplitz-C.tex`, proof
of `lem:C`). Steps: `kper` as a sum over all lifts; the `SL₂(ℤ)` spoke parametrisation
(`Families.Spokes`); the isolated point `k = 0`; `spoke_count` on each spoke `1 ≤ |k| ≤ ⌊k_*⌋`;
`main_term`; `∑_{k≤x} τ(k) ≤ x(1 + log x)`.
-/
import Families.Phase1.A.Spoke
import Families.Phase1.A.MainTerm

noncomputable section

open scoped BigOperators ENNReal ArithmeticFunction.Moebius
open Finset MeasureTheory Set

namespace Families.Phase1.A

open Families

/-! ### Definitions -/

/-- `(ν * k_ς)(θ)` for `ν = ∑_{q ≤ Q, (q,r)=1} 𝔴(q/Q) ∑*_{b mod q} δ_{b/q}`. For `r = 1` this is
`fareyConv 𝔴 Q ς θ`; for `𝔴 = w(r·)` it is `(ν_r * k_ς)(θ)` of `lem:C`. -/
def twistedConv (𝔴 : ℝ → ℝ) (r : ℕ) (Q ς θ : ℝ) : ℝ :=
  ∑ q ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun q => Nat.Coprime q r),
    𝔴 (q / Q) * ∑ b ∈ reduced q, kper ς (θ - b / q)

/-- `ρ_r(z) = (vz)^{-2} ∑_{k≥1} k G_S(k,r) 𝔴(k/(v|z|Q))` (only `k ≤ v|z|Q` contribute). -/
def rhoTwist (𝔴 : ℝ → ℝ) (S : Finset ℕ) (r : ℕ) (Q : ℝ) (v : ℕ) (z : ℝ) : ℝ :=
  ((v : ℝ) * z)⁻¹ ^ 2 * ∑ k ∈ Finset.Icc 1 ⌊(v : ℝ) * |z| * Q⌋₊,
    (k : ℝ) * GS S k r * 𝔴 (k / ((v : ℝ) * |z| * Q))

lemma rhoTwist_eq_rhoGen (𝔴 : ℝ → ℝ) (S : Finset ℕ) (r : ℕ) (Q : ℝ) (v : ℕ) :
    rhoTwist 𝔴 S r Q v = rhoGen 𝔴 (fun k => GS S k r) Q v := rfl

/-- The lattice function on `𝒫 = {(b,q)}`: `1[q ≥ 1, (b,q)=1, (q,r)=1] 𝔴(q/Q) k₀(b/q − θ)`. -/
def latT (𝔴 : ℝ → ℝ) (r : ℕ) (Q ς θ : ℝ) (p : ℤ × ℤ) : ℝ :=
  if 1 ≤ p.2 ∧ Int.gcd p.1 p.2 = 1 ∧ Int.gcd p.2 r = 1 then
    𝔴 (p.2 / Q) * k0 ς ((p.1 : ℝ) / p.2 - θ) else 0

/-! ### Step 1: `∑*_b k_ς(θ − b/q)` as a sum over all `b ∈ ℤ` -/

lemma summable_k0_frac (q : ℕ) (hq : 1 ≤ q) {ς : ℝ} (hς : 0 < ς) (θ : ℝ) (g : ℤ → ℝ)
    (hg : ∀ b, g b ≠ 0 → k0 ς ((b : ℝ) / q - θ) ≠ 0) : Summable g := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  refine summable_of_affine (F := fun x => k0 ς (x / q - θ)) (A := q * (θ - ς)) (B := q * (θ + ς))
    ?_ 0 (v := 1) le_rfl g ?_
  · intro x hx
    have := abs_lt_of_k0_ne_zero hς hx
    rw [abs_lt] at this
    constructor
    · have : θ - ς < x / q := by linarith
      rw [lt_div_iff₀ hq'] at this; linarith
    · have : x / q < θ + ς := by linarith
      rw [div_lt_iff₀ hq'] at this; linarith
  · intro b hb
    have := hg b hb
    simpa using this

lemma sum_reduced_kper (q : ℕ) (hq : 1 ≤ q) {ς : ℝ} (hς : 0 < ς) (θ : ℝ) :
    ∑ b ∈ reduced q, kper ς (θ - b / q) =
      ∑' b : ℤ, (if Int.gcd b q = 1 then k0 ς ((b : ℝ) / q - θ) else 0) := by
  have : NeZero q := ⟨by omega⟩
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  set f : ℤ → ℝ := fun b => if Int.gcd b q = 1 then k0 ς ((b : ℝ) / q - θ) else 0 with hf
  have hfs : Summable f := summable_k0_frac q hq hς θ f fun b hb => by
    simp only [hf] at hb
    split_ifs at hb with h
    · exact hb
    · exact absurd rfl hb
  set e : Fin q × ℤ ≃ ℤ := (Equiv.prodComm (Fin q) ℤ).trans (Int.divModEquiv q).symm with he
  have he_apply : ∀ i : Fin q, ∀ m : ℤ, e (i, m) = m * q + (i : ℕ) := fun i m => by
    simp [he, Int.divModEquiv_symm_apply]
  have hgs : Summable (fun p => f (e p)) := (e.summable_iff (f := f)).mpr hfs
  rw [← e.tsum_eq f, Summable.tsum_prod' hgs (fun i => hgs.prod_factor i), tsum_fintype]
  simp only [he_apply]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ∑' m : ℤ, f (m * q + (i : ℤ))) q]
  rw [reduced, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hgcd : ∀ m : ℤ, Int.gcd (m * q + (i : ℤ)) q = Nat.gcd i q := fun m => by
    rw [Int.gcd_mul_right_add_left, Int.gcd_natCast_natCast]
  split_ifs with hcop
  · -- `kper ς (θ − i/q) = ∑_m k₀(m + i/q − θ)`
    unfold kper
    rw [← (Equiv.neg ℤ).tsum_eq]
    refine tsum_congr fun m => ?_
    simp only [hf, hgcd, hcop.gcd_eq_one, if_true, Equiv.neg_apply]
    rw [← k0_neg]
    congr 1
    push_cast
    field_simp
    ring
  · symm
    refine (tsum_congr fun m => ?_).trans tsum_zero
    simp only [hf, hgcd]
    rw [if_neg hcop]

/-! ### Step 2: `twistedConv` as a lattice sum -/

section lattice

variable {𝔴 : ℝ → ℝ} (hsupp : ∀ u, 𝔴 u ≠ 0 → 0 < u ∧ u ≤ 1) {r : ℕ} {Q ς θ : ℝ}
include hsupp

lemma latT_support (hQ : 0 < Q) (hς : 0 < ς) (p : ℤ × ℤ) (hp : latT 𝔴 r Q ς θ p ≠ 0) :
    1 ≤ p.2 ∧ (p.2 : ℝ) ≤ Q ∧ |(p.1 : ℝ)| ≤ Q * (|θ| + ς) := by
  unfold latT at hp
  split_ifs at hp with hc
  · have hw : 𝔴 (p.2 / Q) ≠ 0 := left_ne_zero_of_mul hp
    have hk : k0 ς ((p.1 : ℝ) / p.2 - θ) ≠ 0 := right_ne_zero_of_mul hp
    have hq1 : (1 : ℝ) ≤ p.2 := by exact_mod_cast hc.1
    have hq0 : (0 : ℝ) < p.2 := by linarith
    have hqQ : (p.2 : ℝ) ≤ Q := (div_le_one hQ).mp (hsupp _ hw).2
    refine ⟨hc.1, hqQ, ?_⟩
    have h1 := abs_lt_of_k0_ne_zero hς hk
    have h2 : |(p.1 : ℝ) / p.2| < |θ| + ς := by
      have := abs_sub_abs_le_abs_sub ((p.1 : ℝ) / p.2) θ
      linarith
    rw [abs_div, abs_of_pos hq0, div_lt_iff₀ hq0] at h2
    have : (|θ| + ς) * p.2 ≤ (|θ| + ς) * Q := mul_le_mul_of_nonneg_left hqQ (by positivity)
    linarith
  · exact absurd rfl hp

lemma summable_latT (hQ : 0 < Q) (hς : 0 < ς) : Summable (latT 𝔴 r Q ς θ) := by
  set B0 : ℤ := ⌈Q * (|θ| + ς)⌉
  refine summable_of_ne_finset_zero (s := Finset.Icc (-B0) B0 ×ˢ Finset.Icc 1 ⌊Q⌋) ?_
  intro p hp
  by_contra hne
  obtain ⟨h1, h2, h3⟩ := latT_support hsupp hQ hς p hne
  apply hp
  rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  rw [abs_le] at h3
  refine ⟨⟨?_, ?_⟩, h1, Int.le_floor.mpr h2⟩
  · have : -(Q * (|θ| + ς)) ≤ (p.1 : ℝ) := h3.1
    have hc := Int.le_ceil (Q * (|θ| + ς))
    have : ((-B0 : ℤ) : ℝ) ≤ p.1 := by push_cast; linarith
    exact_mod_cast this
  · exact Int.le_ceil_iff.mpr (by linarith [h3.2])

/-- `twistedConv 𝔴 r Q ς θ = ∑_{(b,q)} latT(b,q)`. -/
lemma twistedConv_eq_tsum (hQ : 0 < Q) (hς : 0 < ς) :
    twistedConv 𝔴 r Q ς θ = ∑' p : ℤ × ℤ, latT 𝔴 r Q ς θ p := by
  have hs := summable_latT (r := r) (θ := θ) hsupp hQ hς
  have hs' : Summable (fun p : ℤ × ℤ => latT 𝔴 r Q ς θ p.swap) :=
    ((Equiv.prodComm ℤ ℤ).summable_iff (f := latT 𝔴 r Q ς θ)).mpr hs
  rw [← (Equiv.prodComm ℤ ℤ).tsum_eq]
  simp only [Equiv.prodComm_apply]
  rw [Summable.tsum_prod' hs' (fun q => hs'.prod_factor q)]
  simp only [Prod.swap_prod_mk]
  set N := (Finset.Icc 1 ⌊Q⌋₊).filter (fun q => Nat.Coprime q r) with hN
  rw [tsum_eq_sum (s := N.map Nat.castEmbedding)]
  · rw [Finset.sum_map]
    unfold twistedConv
    refine Finset.sum_congr rfl fun q hq => ?_
    obtain ⟨hq1, hqr⟩ := Finset.mem_filter.mp hq
    have hq1' : 1 ≤ q := (Finset.mem_Icc.mp hq1).1
    simp only [Nat.castEmbedding_apply]
    rw [sum_reduced_kper q hq1' hς θ, ← tsum_mul_left]
    refine tsum_congr fun b => ?_
    unfold latT
    simp only [Int.gcd_natCast_natCast, hqr.gcd_eq_one, and_true]
    have : (1 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq1'
    simp only [this, true_and, Int.cast_natCast]
    split_ifs <;> simp
  · intro q hq
    refine (tsum_congr fun b => ?_).trans tsum_zero
    by_contra hne
    obtain ⟨h1, h2, -⟩ := latT_support hsupp hQ hς (b, q) hne
    apply hq
    rw [Finset.mem_map]
    refine ⟨q.toNat, ?_, ?_⟩
    · rw [hN, Finset.mem_filter, Finset.mem_Icc]
      simp only at h1 h2
      have hq0 : 0 ≤ q := by omega
      refine ⟨⟨by omega, ?_⟩, ?_⟩
      · rw [Nat.le_floor_iff hQ.le]
        have : ((q.toNat : ℤ) : ℝ) = (q : ℝ) := by rw [Int.toNat_of_nonneg hq0]
        push_cast at this
        rw [this]; exact h2
      · have hl : latT 𝔴 r Q ς θ (b, q) ≠ 0 := hne
        unfold latT at hl
        split_ifs at hl with hc
        · have := hc.2.2
          rw [← Int.toNat_of_nonneg hq0, Int.gcd_natCast_natCast] at this
          exact this
        · exact absurd rfl hl
    · simp only [Nat.castEmbedding_apply]; omega

end lattice

/-! ### Step 3: the spoke decomposition -/

section spokes

variable {𝔴 : ℝ → ℝ} (hsupp : ∀ u, 𝔴 u ≠ 0 → 0 < u ∧ u ≤ 1) {r : ℕ} {Q ς θ : ℝ}
  {u : ℤ} {v : ℕ} {u' v' : ℤ}
include hsupp

omit hsupp in
/-- The isolated point `k = 0`. -/
lemma spoke_zero (h : (v : ℤ) * u' - u * v' = 1) (hv : 1 ≤ v) :
    ∑' m : ℤ, latT 𝔴 r Q ς θ (Families.Spokes.bwd u v u' v' (0, m)) =
      (if Nat.Coprime v r then 𝔴 (v / Q) else 0) * k0 ς (θ - u / v) := by
  have hv1 : (1 : ℤ) ≤ v := by exact_mod_cast hv
  rw [tsum_eq_single 1]
  · simp only [Families.Spokes.bwd, mul_zero, zero_add, mul_one]
    unfold latT
    have hcop : Int.gcd u v = 1 := by
      rw [← Int.isCoprime_iff_gcd_eq_one]
      exact ⟨-v', u', by linear_combination h⟩
    simp only [hv1, hcop, true_and, Int.gcd_natCast_natCast, Int.cast_natCast]
    rw [k0_sub_comm]
    by_cases hvr : Nat.Coprime v r
    · rw [if_pos hvr.gcd_eq_one, if_pos hvr]
    · rw [if_neg hvr, if_neg hvr, zero_mul]
  · intro m hm
    unfold latT
    rw [if_neg]
    rintro ⟨h1, h2, -⟩
    simp only [Families.Spokes.bwd, mul_zero, zero_add] at h1 h2
    obtain ⟨hb, hq⟩ := Families.Spokes.isolated_point h hv1 (u * m) (v * m) h1 h2 (by ring)
    have : (v : ℤ) * m = v * 1 := by rw [hq, mul_one]
    exact hm (mul_left_cancel₀ (by omega) this)

omit hsupp in
/-- A spoke `k ≠ 0` is a `spokeSum` of the spoke weight `f_k`. -/
lemma spoke_eq (h : (v : ℤ) * u' - u * v' = 1) (hv : 1 ≤ v) (k : ℤ) :
    ∑' m : ℤ, latT 𝔴 r Q ς θ (Families.Spokes.bwd u v u' v' (k, m)) =
      spokeSum (spokeF 𝔴 Q ς (θ - u / v) v k) v v' k r := by
  unfold spokeSum
  refine tsum_congr fun m => ?_
  set b := u' * k + u * m with hb
  set q := v' * k + v * m with hq
  have hbwd : Families.Spokes.bwd u v u' v' (k, m) = (b, q) := rfl
  have hk : (v : ℤ) * b - u * q = k := by rw [hb, hq]; linear_combination k * h
  have hm : -v' * b + u' * q = m := by rw [hb, hq]; linear_combination m * h
  have hg : Int.gcd b q = Int.gcd m k := by
    rw [← Families.Spokes.gcd_fwd h b q, hk, hm, Int.gcd_comm]
  rw [hbwd]
  unfold latT
  simp only
  by_cases hq1 : 1 ≤ q
  · have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
    rw [hg]
    have hval : (b : ℝ) / q - θ = (k : ℝ) / (q * v) - (θ - u / v) := by
      have := Families.Spokes.sub_eq_spoke (u := u) (v := (v : ℤ)) b q (by omega)
        (by exact_mod_cast (by omega : v ≠ 0))
      rw [hk] at this
      push_cast at this
      linarith
    simp only [hq1, true_and]
    split_ifs with hc
    · rw [spokeF_of_pos k hq0, hval]
    · rfl
  · have hq0 : (q : ℝ) ≤ 0 := by
      have : q ≤ 0 := by omega
      exact_mod_cast this
    rw [if_neg (fun hc => hq1 hc.1)]
    have hF : spokeF 𝔴 Q ς (θ - u / v) v k q = 0 := by
      unfold spokeF
      rw [if_neg (not_lt.mpr hq0), mul_zero]
    split_ifs <;> simp [hF]

end spokes

/-! ### Step 4: the twisted count -/

lemma sum_range_card_divisors_le (K : ℕ) :
    ∑ n ∈ Finset.range K, (((n + 1 : ℕ)).divisors.card : ℝ) ≤ K * (1 + Real.log K) := by
  rw [sum_range_succ_eq_sum_Icc (fun k => ((k.divisors.card : ℕ) : ℝ)) K]
  exact Families.sum_card_divisors_le K

/-- **The twisted count, with an explicit spoke range `K₀`.** -/
theorem twisted_count_core {𝔴 : ℝ → ℝ} (hbv : BoundedVariationOn 𝔴 univ)
    (hsupp : ∀ u, 𝔴 u ≠ 0 → 0 < u ∧ u ≤ 1) {Q ς θ : ℝ} (hQ : 0 < Q) (hς : 0 < ς)
    {u : ℤ} {v : ℕ} (hv : 1 ≤ v) (huv : IsCoprime u (v : ℤ)) (K0 : ℕ)
    (hK0 : ∀ z, |z - (θ - u / v)| < ς → (v : ℝ) * |z| * Q < K0 + 1) {r : ℕ} (hr : Squarefree r) :
    Integrable (fun z => k0 ς (z - (θ - u / v)) * rhoTwist 𝔴 v.primeFactors r Q v z) ∧
    |twistedConv 𝔴 r Q ς θ - (if Nat.Coprime v r then 𝔴 (v / Q) else 0) * k0 ς (θ - u / v)
        - ∫ z, k0 ς (z - (θ - u / v)) * rhoTwist 𝔴 v.primeFactors r Q v z|
      ≤ (r.divisors.card : ℝ) *
          (4 * (eVariationOn 𝔴 univ).toReal * ς⁻¹ * (K0 * (1 + Real.log K0))) := by
  set y := θ - u / v with hy
  set V := (eVariationOn 𝔴 univ).toReal with hV
  have hV0 : 0 ≤ V := ENNReal.toReal_nonneg
  -- Bezout: `v u' − u v' = 1`
  obtain ⟨a, b, hab⟩ := huv
  set u' : ℤ := b
  set v' : ℤ := -a
  have h : (v : ℤ) * u' - u * v' = 1 := by simp only [u', v']; linear_combination hab
  have hvv' : Int.gcd v' v = 1 := by
    rw [← Int.isCoprime_iff_gcd_eq_one]; exact ⟨-u, u', by linear_combination h⟩
  -- main term
  obtain ⟨hInt, hmain⟩ := main_term hbv hsupp hQ hς hv y (fun k => GS v.primeFactors k r) K0 hK0
  refine ⟨hInt, ?_⟩
  rw [rhoTwist_eq_rhoGen, ← hmain]
  -- the lattice sum and the spokes
  set Sk : ℤ → ℝ := fun k => ∑' m : ℤ, latT 𝔴 r Q ς θ (Families.Spokes.bwd u v u' v' (k, m))
    with hSk
  have hSk_spoke : ∀ k, Sk k = spokeSum (spokeF 𝔴 Q ς y v k) v v' k r := fun k =>
    spoke_eq h hv k
  have hSk_zero : ∀ k : ℤ, (K0 : ℤ) < |k| → Sk k = 0 := by
    intro k hk
    rw [hSk_spoke]
    unfold spokeSum
    refine (tsum_congr fun m => ?_).trans tsum_zero
    rw [spokeF_eq_zero_of_lt hsupp hQ hς hv K0 hK0 hk]
    split_ifs <;> rfl
  have hlat : twistedConv 𝔴 r Q ς θ = ∑' k : ℤ, Sk k := by
    rw [twistedConv_eq_tsum hsupp hQ hς]
    have hs := summable_latT (r := r) (θ := θ) hsupp hQ hς
    have hs2 : Summable (fun p => latT 𝔴 r Q ς θ ((Families.Spokes.spokeEquiv h).symm p)) :=
      ((Families.Spokes.spokeEquiv h).symm.summable_iff (f := latT 𝔴 r Q ς θ)).mpr hs
    rw [← (Families.Spokes.spokeEquiv h).symm.tsum_eq, Summable.tsum_prod' hs2
      (fun k => hs2.prod_factor k)]
    exact tsum_congr fun k => tsum_congr fun m => rfl
  have hfin1 : ∀ n : ℕ, n ∉ Finset.range (K0 + 1) → Sk n = 0 := fun n hn =>
    hSk_zero n (by rw [Finset.mem_range] at hn; rw [Int.abs_natCast]; omega)
  have hfin2 : ∀ n : ℕ, n ∉ Finset.range K0 → Sk (-(n + 1 : ℤ)) = 0 := fun n hn =>
    hSk_zero _ (by
      rw [Finset.mem_range] at hn
      rw [abs_neg, abs_of_nonneg (by omega : (0 : ℤ) ≤ (n : ℤ) + 1)]; omega)
  have hsplit : ∑' k : ℤ, Sk k = Sk 0 + ∑ n ∈ Finset.range K0,
      (Sk ((n + 1 : ℕ) : ℤ) + Sk (-((n + 1 : ℕ) : ℤ))) := by
    rw [tsum_of_nat_of_neg_add_one (summable_of_ne_finset_zero hfin1)
      (summable_of_ne_finset_zero hfin2), tsum_eq_sum hfin1, tsum_eq_sum hfin2,
      Finset.sum_range_succ', Finset.sum_add_distrib]
    push_cast
    ring
  have hzero : Sk 0 = (if Nat.Coprime v r then 𝔴 (v / Q) else 0) * k0 ς y := spoke_zero h hv
  rw [hlat, hsplit, hzero, add_sub_cancel_left, ← Finset.sum_sub_distrib]
  -- each spoke
  have hTV : ∀ k : ℤ, k ≠ 0 → (eVariationOn (spokeF 𝔴 Q ς y v k) univ).toReal ≤ 2 * V / ς :=
    fun k hk => ENNReal.toReal_le_of_le_ofReal (by positivity)
      (eVariationOn_spokeF_le hbv hsupp hQ hς hv hk)
  have hone : ∀ k : ℤ, k ≠ 0 →
      |Sk k - GS v.primeFactors k.natAbs r / v * ∫ x, spokeF 𝔴 Q ς y v k x|
        ≤ (k.natAbs.divisors.card : ℝ) * r.divisors.card * (2 * V / ς) := by
    intro k hk
    rw [hSk_spoke]
    refine (spoke_count (bv_spokeF hbv hsupp hQ hς hv hk) (spokeF_supp hsupp hQ k) hv hvv' hk
      hr).trans ?_
    gcongr
    exact hTV k hk
  have hτ0 : ∀ n : ℕ, (0 : ℝ) ≤ ((n + 1 : ℕ)).divisors.card := fun n => Nat.cast_nonneg _
  calc |∑ n ∈ Finset.range K0, (Sk ((n + 1 : ℕ) : ℤ) + Sk (-((n + 1 : ℕ) : ℤ)) -
        GS v.primeFactors (n + 1) r / v * ((∫ x, spokeF 𝔴 Q ς y v ((n + 1 : ℕ) : ℤ) x) +
          ∫ x, spokeF 𝔴 Q ς y v (-((n + 1 : ℕ) : ℤ)) x))|
      ≤ ∑ n ∈ Finset.range K0, |Sk ((n + 1 : ℕ) : ℤ) + Sk (-((n + 1 : ℕ) : ℤ)) -
        GS v.primeFactors (n + 1) r / v * ((∫ x, spokeF 𝔴 Q ς y v ((n + 1 : ℕ) : ℤ) x) +
          ∫ x, spokeF 𝔴 Q ς y v (-((n + 1 : ℕ) : ℤ)) x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range K0,
          2 * (((n + 1 : ℕ)).divisors.card * r.divisors.card * (2 * V / ς)) := by
        refine Finset.sum_le_sum fun n _ => ?_
        have hk1 : ((n + 1 : ℕ) : ℤ) ≠ 0 := by omega
        have hk2 : -((n + 1 : ℕ) : ℤ) ≠ 0 := by omega
        have e1 := hone _ hk1
        have e2 := hone _ hk2
        rw [Int.natAbs_natCast] at e1
        rw [Int.natAbs_neg, Int.natAbs_natCast] at e2
        have : Sk ((n + 1 : ℕ) : ℤ) + Sk (-((n + 1 : ℕ) : ℤ)) -
            GS v.primeFactors (n + 1) r / v * ((∫ x, spokeF 𝔴 Q ς y v ((n + 1 : ℕ) : ℤ) x) +
              ∫ x, spokeF 𝔴 Q ς y v (-((n + 1 : ℕ) : ℤ)) x) =
            (Sk ((n + 1 : ℕ) : ℤ) - GS v.primeFactors (n + 1) r / v *
              ∫ x, spokeF 𝔴 Q ς y v ((n + 1 : ℕ) : ℤ) x) +
            (Sk (-((n + 1 : ℕ) : ℤ)) - GS v.primeFactors (n + 1) r / v *
              ∫ x, spokeF 𝔴 Q ς y v (-((n + 1 : ℕ) : ℤ)) x) := by ring
        rw [this]
        refine (abs_add_le _ _).trans ?_
        linarith
    _ = (r.divisors.card : ℝ) * (4 * V * ς⁻¹) *
          ∑ n ∈ Finset.range K0, (((n + 1 : ℕ)).divisors.card : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        ring
    _ ≤ (r.divisors.card : ℝ) * (4 * V * ς⁻¹) * (K0 * (1 + Real.log K0)) := by
        gcongr
        exact sum_range_card_divisors_le K0
    _ = _ := by ring

/-- `K₀(1 + log K₀) ≤ k_*(1 + log⁺ k_*)` for `K₀ = ⌊k_*⌋`. -/
lemma floor_mul_log_le {x : ℝ} (hx : 0 ≤ x) :
    (⌊x⌋₊ : ℝ) * (1 + Real.log ⌊x⌋₊) ≤ x * (1 + Real.posLog x) := by
  have h1 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have h2 : Real.log ⌊x⌋₊ ≤ Real.posLog x := by
    rw [← Real.log_of_nat_eq_posLog]
    exact Real.posLog_le_posLog (Nat.cast_nonneg _) h1
  rcases Nat.eq_zero_or_pos ⌊x⌋₊ with h0 | hpos
  · rw [h0]; simp only [Nat.cast_zero, zero_mul]
    have := Real.posLog_nonneg (x := x); positivity
  · have : (0 : ℝ) ≤ 1 + Real.log ⌊x⌋₊ := by
      have : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hpos
      have := Real.log_nonneg this; linarith
    exact mul_le_mul h1 (by linarith) this hx

/-- On the support of `k₀(· − y)`: `v|z|Q < k_* = Q/V + QVς`. -/
lemma vzQ_lt_kstar {Q ς V θ : ℝ} {u : ℤ} {v : ℕ} (hQ0 : 0 < Q) (hς : 0 < ς) (hV0 : 0 < V)
    (hv : 1 ≤ v) (hvV : (v : ℝ) ≤ V) (hθ : |θ - u / v| ≤ 1 / (v * V)) (z : ℝ)
    (hz : |z - (θ - u / v)| < ς) : (v : ℝ) * |z| * Q < Q / V + Q * V * ς := by
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have h1 : |z| ≤ |θ - u / v| + |z - (θ - u / v)| := by
    have := abs_add_le (θ - u / v) (z - (θ - u / v)); simp only [add_sub_cancel] at this
    linarith
  have h2 : (v : ℝ) * |θ - u / v| ≤ 1 / V := by
    calc (v : ℝ) * |θ - u / v| ≤ v * (1 / (v * V)) := mul_le_mul_of_nonneg_left hθ hv'.le
      _ = 1 / V := by field_simp
  have e1 : (v : ℝ) * |z| ≤ v * |θ - u / v| + v * |z - (θ - u / v)| := by nlinarith
  have e2 : (v : ℝ) * |z - (θ - u / v)| < v * ς := mul_lt_mul_of_pos_left hz hv'
  have e3 : (v : ℝ) * ς ≤ V * ς := mul_le_mul_of_nonneg_right hvV hς.le
  have e4 : (v : ℝ) * |z| < 1 / V + V * ς := by linarith
  calc (v : ℝ) * |z| * Q < (1 / V + V * ς) * Q := mul_lt_mul_of_pos_right e4 hQ0
    _ = Q / V + Q * V * ς := by field_simp

/-- **The twisted local count along spokes** (`lemma-toeplitz-C.tex`, proof of `lem:C`, measures `ν_r`;
`prop:count` for `r = 1`). Hypotheses of `prop:count` plus `r` squarefree. -/
theorem twistedCount {𝔴 : ℝ → ℝ} (hbv : BoundedVariationOn 𝔴 univ)
    (hsupp : ∀ u, 𝔴 u ≠ 0 → 0 < u ∧ u ≤ 1) {Q ς V θ : ℝ} {u : ℤ} {v : ℕ}
    (hQ : 1 ≤ Q) (hς : 0 < ς) (hV : 1 ≤ V) (hv : 1 ≤ v) (hvV : (v : ℝ) ≤ V)
    (huv : IsCoprime u (v : ℤ)) (hθ : |θ - u / v| ≤ 1 / (v * V)) {r : ℕ} (hr : Squarefree r) :
    Integrable (fun z => k0 ς (z - (θ - u / v)) * rhoTwist 𝔴 v.primeFactors r Q v z) ∧
    |twistedConv 𝔴 r Q ς θ - (if Nat.Coprime v r then 𝔴 (v / Q) else 0) * k0 ς (θ - u / v)
        - ∫ z, k0 ς (z - (θ - u / v)) * rhoTwist 𝔴 v.primeFactors r Q v z|
      ≤ (r.divisors.card : ℝ) * (4 * (eVariationOn 𝔴 univ).toReal * ς⁻¹ * (Q / V + Q * V * ς) *
          (1 + Real.posLog (Q / V + Q * V * ς))) := by
  set kstar := Q / V + Q * V * ς with hkstar
  have hQ0 : 0 < Q := by linarith
  have hV0 : 0 < V := by linarith
  have hv' : (0 : ℝ) < v := by exact_mod_cast hv
  have hks0 : 0 ≤ kstar := by positivity
  have hK0 : ∀ z, |z - (θ - u / v)| < ς → (v : ℝ) * |z| * Q < ⌊kstar⌋₊ + 1 := fun z hz =>
    lt_of_lt_of_le (vzQ_lt_kstar hQ0 hς hV0 hv hvV hθ z hz) (Nat.lt_floor_add_one kstar).le
  obtain ⟨hInt, hb⟩ := twisted_count_core hbv hsupp hQ0 hς hv huv ⌊kstar⌋₊ hK0 hr
  refine ⟨hInt, hb.trans ?_⟩
  have hV0' : 0 ≤ (eVariationOn 𝔴 univ).toReal := ENNReal.toReal_nonneg
  have := floor_mul_log_le hks0
  have h4 : 0 ≤ 4 * (eVariationOn 𝔴 univ).toReal * ς⁻¹ := by positivity
  calc (r.divisors.card : ℝ) * (4 * (eVariationOn 𝔴 univ).toReal * ς⁻¹ *
        (⌊kstar⌋₊ * (1 + Real.log ⌊kstar⌋₊)))
      ≤ (r.divisors.card : ℝ) * (4 * (eVariationOn 𝔴 univ).toReal * ς⁻¹ *
        (kstar * (1 + Real.posLog kstar))) := by gcongr
    _ = _ := by ring

/-! ### `prop:count` -/

lemma twistedConv_one (𝔴 : ℝ → ℝ) (Q ς θ : ℝ) : twistedConv 𝔴 1 Q ς θ = fareyConv 𝔴 Q ς θ := by
  unfold twistedConv fareyConv
  rw [Finset.filter_true_of_mem fun q _ => Nat.coprime_one_right q]

lemma GS_one (S : Finset ℕ) (k : ℕ) : GS S k 1 = (Nat.totient k : ℝ) / k := by
  unfold GS
  rw [Nat.primeFactors_one, Finset.filter_empty, Finset.prod_empty, mul_one, Nat.gcd_one_right,
    if_pos, mul_one]
  intro p _ hp hp1
  exact hp.one_lt.ne' (Nat.dvd_one.mp hp1)

lemma rhoTwist_one (𝔴 : ℝ → ℝ) (S : Finset ℕ) (Q : ℝ) (v : ℕ) (z : ℝ) :
    rhoTwist 𝔴 S 1 Q v z = rhoCount 𝔴 Q v z := by
  unfold rhoTwist rhoCount
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk0 : (k : ℝ) ≠ 0 := by
    have := (Finset.mem_Icc.mp hk).1; exact_mod_cast (by omega : k ≠ 0)
  rw [GS_one]
  field_simp

/-- **`prop:count`** (`lemma-A.tex`): proved, as the case `r = 1` of `twistedCount`. -/
theorem propCount_proof : propCount_Statement := by
  intro 𝔴 _h𝔴0 hbv hsupp Q ς V θ u v hQ hς _hς2 hV hv hvV huv hθ
  obtain ⟨-, hb⟩ := twistedCount hbv hsupp hQ hς hV hv hvV huv hθ (r := 1) squarefree_one
  rw [twistedConv_one, if_pos (Nat.coprime_one_right v), Nat.divisors_one, Finset.card_singleton,
    Nat.cast_one, one_mul] at hb
  simp only [rhoTwist_one] at hb
  exact hb

end Families.Phase1.A
