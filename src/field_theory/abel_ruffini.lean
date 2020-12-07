import field_theory.galois
import ring_theory.eisenstein_criterion
import ring_theory.algebraic
import field_theory.algebraic_closure

noncomputable theory
open_locale classical

open polynomial

section abel_ruffini

universes u v

variables (F : Type u) [field F] {E : Type v} [field E] [algebra F E]

inductive SBR : E → Type (max u v)
| base (a : F) : SBR (algebra_map F E a)
--| add (a b : E) : SBR a → SBR b → SBR (a + b)
--| neg (a : E) : SBR a → SBR (-a)
--| mul (a b : E) : SBR a → SBR b → SBR (a * b)
--| inv (a : E) : SBR a → SBR (a⁻¹)
--| rad (a b : E) (n : ℕ) (h : a^n = b): SBR b → SBR a

namespace SBR

variables {F}

def to_field : Π x : E, SBR F x → intermediate_field F E :=
| (algebra_map F E x) (base x) := sorry

end SBR

end abel_ruffini
