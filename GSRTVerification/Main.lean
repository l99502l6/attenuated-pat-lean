/-
Audit file: checks that every headline result of the development depends only on
Lean's three standard axioms (`propext`, `Classical.choice`, `Quot.sound`), and
in particular on no `sorryAx`.
-/
import GSRTVerification

/-!
# Axiom audit

Running `lake env lean GSRTVerification/Main.lean` prints, for each headline
theorem, the axioms it depends on.  A `sorryAx` in any of these lists would mean
the corresponding statement is not actually proved.
-/

section Attenuation

#print axioms GSRT.psqrt_sq
#print axioms GSRT.psqrt_re_pos
#print axioms GSRT.psqrt_conj
#print axioms GSRT.psqrt_differentiableAt
#print axioms GSRT.two_mul_re_mul_im_psqrt
#print axioms GSRT.kappa1_im_nonneg
#print axioms GSRT.kappa1_symm
#print axioms GSRT.kappa1_ne_zero
#print axioms GSRT.kappa2_im_nonneg
#print axioms GSRT.kappa2_symm
#print axioms GSRT.kappa2_ne_zero
#print axioms GSRT.nsw_ratio_re_pos
#print axioms GSRT.IsAttenuationCoefficient.re_zero
#print axioms GSRT.IsAttenuationCoefficient.re_neg
#print axioms GSRT.IsAttenuationCoefficient.im_neg

end Attenuation

section AttenuationExtension

#print axioms GSRT.kappa1C_ofReal
#print axioms GSRT.kappa1C_im_nonneg
#print axioms GSRT.kappa1C_differentiableOn
#print axioms GSRT.kappa1C_continuousOn
#print axioms GSRT.norm_kappa1C_le
#print axioms GSRT.kappa2C_ofReal
#print axioms GSRT.kappa2C_im_nonneg
#print axioms GSRT.kappa2C_differentiableOn
#print axioms GSRT.kappa2C_continuousOn
#print axioms GSRT.norm_kappa2C_le

end AttenuationExtension

section DerivativeGrowth

#print axioms GSRT.iteratedDeriv_restrict
#print axioms GSRT.polyGrowth_of_bounded
#print axioms GSRT.kappa1_polyGrowth
#print axioms GSRT.kappa2_polyGrowth

end DerivativeGrowth

section AngularFourier

#print axioms GSRT.synth_im_eq_zero
#print axioms GSRT.conjSymm_symmetrize
#print axioms GSRT.synth_symmetrize_im_eq_zero
#print axioms GSRT.symmetrize_zero
#print axioms GSRT.symmetrize_eq_self
#print axioms GSRT.sum_exp_two_pi_I
#print axioms GSRT.conj_fourierIntegral

end AngularFourier

section ContinuousFourier

#print axioms GSRT.integral_exp_int_mul_I
#print axioms GSRT.integral_synth_mul_exp

end ContinuousFourier

section Radial

#print axioms GSRT.discrete_angular_extraction
#print axioms GSRT.Aentry_neg

end Radial

section Tikhonov

#print axioms GSRT.tikhonovObj_eq_add
#print axioms GSRT.tikhonovObj_le_of_isNormalEqSolution
#print axioms GSRT.eq_of_isNormalEqSolution_of_le
#print axioms GSRT.injective_normalOp
#print axioms GSRT.existsUnique_normalEqSolution
#print axioms GSRT.existsUnique_tikhonov_minimizer
#print axioms GSRT.filterFactor_le
#print axioms GSRT.cond_regularized_le

end Tikhonov

section Spectral

#print axioms GSRT.isNormalEqSolution_tikhonovSol
#print axioms GSRT.inner_tikhonovSol
#print axioms GSRT.norm_inner_tikhonovSol_le
#print axioms GSRT.exists_isSingularSystem

end Spectral
