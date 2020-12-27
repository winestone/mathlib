import field_theory.galois
import ring_theory.eisenstein_criterion
import ring_theory.algebraic
import field_theory.algebraic_closure

noncomputable theory
open_locale classical

open polynomial

section abel_ruffini

variables (F : Type*) [field F] {E : Type*} [field E] [algebra F E]

inductive SBR : E → Prop
| base (a : F) : SBR (algebra_map F E a)
| add (a b : E) : SBR a → SBR b → SBR (a + b)
| neg (α : E) : SBR α → SBR (-α)
| mul (α β : E) : SBR α → SBR β → SBR (α * β)
| inv (α : E) : SBR α → SBR (α⁻¹)
| rad (α : E) (n : ℕ) (hn : n ≠ 0) : SBR (α^n) → SBR α

namespace SBR

variables {F} {α : E}

theorem is_integral (h : SBR F α) : is_integral F α :=
begin
  revert h,
  revert α,
  apply SBR.rec,
  { exact λ _, is_integral_algebra_map },
  { exact λ _ _ _ _, is_integral_add },
  { exact λ _ _, is_integral_neg },
  { exact λ _ _ _ _, is_integral_mul },
  { sorry },
  { intros α n hn _ hα,
    rw ← is_algebraic_iff_is_integral,
    obtain ⟨p, h1, h2⟩ := (is_algebraic_iff_is_integral F).mpr hα,
    refine ⟨p.comp (X ^ n), ⟨_, by rw [aeval_comp, aeval_X_pow, h2]⟩⟩,
    intro h,
    rw [←leading_coeff_eq_zero, leading_coeff_comp, leading_coeff_X_pow, one_pow, mul_one] at h,
    exact h1 (leading_coeff_eq_zero.mp h),
    rwa nat_degree_X_pow, },
end

theorem thm (h : SBR F α) : (is_solvable ((minimal_polynomial (is_integral h)).splitting_field
  ≃ₐ[F] (minimal_polynomial (is_integral h)).splitting_field)) :=
begin
  apply @SBR.rec F _ E _ _ (λ a, ∀ h' : SBR F a,
    (is_solvable ((minimal_polynomial (is_integral h')).splitting_field ≃ₐ[F]
    (minimal_polynomial (is_integral h')).splitting_field))) _ _ _ _ _ _ _ h,
  { sorry },
  { sorry },
  { sorry },
  { sorry },
  { sorry },
  { sorry },
end

end SBR

end abel_ruffini
