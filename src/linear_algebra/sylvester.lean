/-
Copyright (c) 2021 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/

import linear_algebra.quadratic_form
import analysis.special_functions.pow

/-!
# Sylvester's law of inertia

This file provides a proof of Sylvester's law of inertia.
-/

/-- Nonzero elements in a field are invertible. This is a definition since it requires a
parameter. -/
def field.invertible {K : Type*} [field K] {z : K} (hz : z ≠ 0) : invertible z :=
{ inv_of := z⁻¹,
  inv_of_mul_self := inv_mul_cancel hz,
  mul_inv_of_self := mul_inv_cancel hz }

variables {R : Type*} [ring R] {R₁ : Type*} [comm_ring R₁]
variables {M : Type*} [add_comm_group M] [module R M] [module R₁ M]
variables {M₁ : Type*} [add_comm_group M₁] [module R M₁]
variables {ι : Type*} [fintype ι] {v : ι → M}

namespace quadratic_form

open_locale big_operators

open finset bilin_form

end quadratic_form
