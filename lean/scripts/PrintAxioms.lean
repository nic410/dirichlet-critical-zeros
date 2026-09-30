/-
`#print axioms` for the proved declarations listed in STATUS.md (the headline, its glue and its main components).
Run (after `lake build`):  lake env lean scripts/PrintAxioms.lean
-/
import Families

open Families

-- Lemma 6.13, orthogonality, Gauss transfer (Toeplitz.lean)
#print axioms sum_primChars_eq
#print axioms sum_primChars_eq_zero_of_not_coprime
#print axioms phiStar_eq
#print axioms Δ_eq_general
#print axioms Δ_diag
#print axioms toeplitz_identity
#print axioms Δ_rough_shift_invariant
#print axioms famForm_eq_sum
#print axioms kω_zero
#print axioms kω_eq_ramanujan
#print axioms famForm_eq_levelForm_Ω
#print axioms muΩ_mass
#print axioms gauss_transfer
-- Lemma S, Lemma Ω(b) (LemmaS.lean)
#print axioms levelForm_eq_sum
#print axioms toeplitz_posSemidef
#print axioms toeplitz_mono
#print axioms levelForm_mono
#print axioms Ωlev_eq_second_form
#print axioms lemOmega_b
#print axioms lemmaS
#print axioms lemmaS_forms
-- Schur test and M2 (Schur.lean, Glue.lean)
#print axioms schur_test
#print axioms Weight.le_wmax
#print axioms sum_div_totient_le
#print axioms sum_card_divisors_le
#print axioms offdiag_bound
#print axioms short_interval_abstract
#print axioms Δ_offdiag_le
#print axioms lemM2
-- M3 (PrimeSide.lean)
#print axioms lemM3_i
#print axioms lemM3_ii
-- Spokes (prop:count combinatorics)
#print axioms Spokes.spokeEquiv
#print axioms Spokes.gcd_fwd
#print axioms Spokes.sub_eq_spoke
#print axioms Spokes.mem_farey_iff
#print axioms Spokes.isolated_point
#print axioms Spokes.sum_coprime_eq_moebius
#print axioms Spokes.sum_moebius_div
-- Certificate link (PerChar.lean)
#print axioms Cert.ranktrace
#print axioms Cert.posIndex_offline_le
#print axioms Cert.BlockData.M_le
#print axioms Cert.BlockData.perchi
#print axioms Cert.perchi_weighted
-- Constants
#print axioms Ecal_pos
#print axioms Ecal_le
#print axioms one_lt_CG
-- Glue (implications between stated results, and Lemma S on rough vectors)
#print axioms lemmaS_rough
#print axioms lemmaS_lambda_of_dual
#print axioms corLmultA_of'
#print axioms LS_of_corLmultA
#print axioms thmGauss_general_of'
#print axioms pC_CG_ge_of
-- Certificate numerics, p(C) (Certificate/Numerics.lean, Data.lean), lem:pLip, M1
#print axioms CertData.cert1
#print axioms CertData.cert2
#print axioms pC_ge_of_admissible
#print axioms pC_one_ge
#print axioms pC_12688_ge
#print axioms pC_antitone_lip
#print axioms lemPLip
#print axioms thmMain_constant
#print axioms thmGauss_constant_of
#print axioms PrimeSetup.Φ_sq_eq
#print axioms PrimeSetup.kernel_factorisation
#print axioms PrimeSetup.ratioForm_factorisation
#print axioms lemM1
-- Log-wide weights are admissible; R_w bound (Weights.lean)
#print axioms wSharpWeight
#print axioms wSmoothWeight
#print axioms wSharp_Vw_cw_proof
#print axioms Rw_le'
#print axioms mfun_eq_zero_of_gt_half
-- C_G ≤ 1.2688 (Certificate/Ecal.lean, EcalData.lean)
#print axioms EcalData.loopA_eq
#print axioms Ecal_ge_047914
#print axioms CG_le_12688
#print axioms CG_le
#print axioms thmGauss_constant
-- M1 diagonal, M3 (iii),(iv)
#print axioms lemM1_diag
#print axioms lemM3_iii_iv
-- Glue for the headline (Assembly.lean, Headline.lean); all proved, standard axioms only
#print axioms famSum_nonneg
#print axioms Nfam_nonneg
#print axioms Mfrak_nonneg
#print axioms tendsto_rpow_neg_mul_log_pow
#print axioms H_lower_eventually
#print axioms H_pos_eventually
#print axioms norm_eA
#print axioms levelForm_unitAt1_ge_H
#print axioms CTp_ge_one
#print axioms famForm_le_mult
#print axioms bandLS_of_MV
#print axioms ramp_contDiff
#print axioms bandProfile_contDiff
#print axioms bandProfile_spec
#print axioms assembly_fixed
#print axioms thmMain_of_components

-- Wiring of the headline-chain proofs (Families/Wired/Phase1.lean)
#print axioms Families.lemOmega_ac
#print axioms Families.lemDual
#print axioms Families.propCount
#print axioms Families.lemC
#print axioms Families.propSharpLS
#print axioms Families.assemblyLimit
#print axioms Families.lemOmega_d
#print axioms Families.lemOmega_e
#print axioms Families.lemfS

-- Classical inputs, proved (Families/Hyp)
#print axioms Families.Hyp.MV_LargeSieve_proof
#print axioms Families.Hyp.StirlingDigamma_proof
#print axioms Families.Hyp.PNT_dlVP_proof
#print axioms Families.ClassicalInputsReduced.toFull
#print axioms Families.lemB1
#print axioms Families.eqBMrat
#print axioms Families.lemB2
#print axioms Families.lemCTlimit
#print axioms Families.lemWH
#print axioms Families.propTIsharp
-- the headline (unconditional, no hypotheses; audit.sh fails on any sorryAx in this file and requires
-- `#print axioms Families.thmMain` to be exactly [propext, Classical.choice, Quot.sound])
#print axioms Families.thmMain
#print axioms Families.Ported.zeroSide_proof
#print axioms Families.PortedReductionsReduced.toFull
#print axioms Families.Ported.explicitGaborSharp
#print axioms Families.Ported.secondMoment
#print axioms Families.portedReductions
-- Unconditional headline: Montgomery 1969 only in the q-aspect range T' ≤ Q (lem:bad)
#print axioms Families.Hyp.Montgomery.Montgomery69_Density_upTo_proof
#print axioms Families.Hyp.Montgomery.Montgomery69_Density_upTo_of_full
#print axioms Families.Hyp.Montgomery.Montgomery69_Density_of_tAspect
#print axioms Families.Ported.Zero.shellT_le_self
#print axioms Families.Ported.Zero.bad_count_of_upTo
#print axioms Families.Ported.Zero.bad_weight_of_upTo
#print axioms Families.Ported.Zero.bad_count_unconditional
#print axioms Families.Ported.Zero.bad_weight_unconditional
#print axioms Families.Ported.Zero.propZero_of_upTo
#print axioms Families.Ported.Zero.propZero_proof
#print axioms Families.Ported.Zero.propZero_unconditional
#print axioms Families.thmMain_of_parts
#print axioms Families.thmMain_of_montgomery
