/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import Diaz.HermiteLindemann
public import Diaz.Mirror.aux_linear_system
public import Diaz.Mirror.aux_linear_system_column
public import Diaz.Mirror.auxiliary_construction
public import Diaz.Mirror.auxiliary_construction_column
public import Diaz.Mirror.auxiliary_function_alg
public import Diaz.Mirror.auxiliary_function_alg_column
public import Diaz.Mirror.cauchy_estimate_with_zeros
public import Diaz.Mirror.construction_core_1973
public import Diaz.Mirror.construction_core_column
public import Diaz.Mirror.construction_count_1973
public import Diaz.Mirror.construction_growth
public import Diaz.Mirror.dvd_of_small_values
public import Diaz.Mirror.dvd_of_small_values_at_scale
public import Diaz.Mirror.exists_int_norm
public import Diaz.Mirror.exists_int_pow_repr
public import Diaz.Mirror.exists_irreducible_factor_cofactor_bound
public import Diaz.Mirror.exists_iteratedDeriv_presentation
public import Diaz.Mirror.exists_iteratedDeriv_presentation_column
public import Diaz.Mirror.exists_iteratedDeriv_presentation_of_exp_factor
public import Diaz.Mirror.exists_iteratedDeriv_reduced_presentation
public import Diaz.Mirror.exists_iteratedDeriv_reduced_presentation_column
public import Diaz.Mirror.exists_modByMonic_length_le
public import Diaz.Mirror.exists_monic_integral_model
public import Diaz.Mirror.exists_monic_integral_model_presentation
public import Diaz.Mirror.exists_pow_mul_pow_le_exp_sq_mul_sqrt_log
public import Diaz.Mirror.expPoly_grid_estimate
public import Diaz.Mirror.expPoly_iteratedDeriv_le
public import Diaz.Mirror.expPoly_ne_zero
public import Diaz.Mirror.expPoly_value_le_derivs
public import Diaz.Mirror.expPoly_zero_count
public import Diaz.Mirror.expPoly_zero_count_scaled
public import Diaz.Mirror.exp_e_or_exp_e_sq_transcendental
public import Diaz.Mirror.extrapolation
public import Diaz.Mirror.extrapolation_numbers
public import Diaz.Mirror.four_exponentials_trdeg_one
public import Diaz.Mirror.height_dvd_le
public import Diaz.Mirror.isAlgebraic_adjoin_of_not_algebraicIndependent_pair
public import Diaz.Mirror.length_mul_le
public import Diaz.Mirror.length_sum_le
public import Diaz.Mirror.nonvanishing_derivative
public import Diaz.Mirror.norm_resultant_le_max_norm_eval
public import Diaz.Mirror.norm_to_polynomial_alg
public import Diaz.Mirror.norm_to_polynomial_alg_column
public import Diaz.Mirror.rank_one_parametrization
public import Diaz.Mirror.siegel_aux
public import Diaz.Mirror.siegel_entrywise
public import Diaz.Mirror.presentation_size
public import Diaz.Mirror.small_irreducible_factor
public import Diaz.Mirror.small_polynomials_of_column
public import Diaz.Mirror.small_polynomials_of_counterexample
public import Diaz.Mirror.transcendence_criterion
public import Diaz.Mirror.transcendence_criterion_continuous
public import Diaz.Mirror.trdeg_adjoin_le_one_of_isAlgebraic_adjoin
public import Diaz.Mirror.trdeg_one_presentation
public import Diaz.Mirror.trdeg_one_presentation_column
public import Diaz.Mirror.two_algebraically_independent_of_exp_column
public import Diaz.Mirror.zero_count_arith
public import Diaz.Mirror.zero_count_arith_poly
public import Diaz.Mirror.zero_count_degenerate

/-!
# The four exponentials theorem in transcendence degree one

The library root of this extract of
[diaz-modulus-lean](https://github.com/carlok/diaz-modulus-lean): every module that the three
compared theorems need.
-/
