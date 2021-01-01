import field_theory.galois
import ring_theory.eisenstein_criterion
import ring_theory.algebraic
import field_theory.algebraic_closure

noncomputable theory
open_locale classical

open polynomial intermediate_field

section abel_ruffini

variables (F : Type*) [field F] {E : Type*} [field E] [algebra F E]

inductive is_SBR : E → Prop
| base (a : F) : is_SBR (algebra_map F E a)
| add (a b : E) : is_SBR a → is_SBR b → is_SBR (a + b)
| neg (α : E) : is_SBR α → is_SBR (-α)
| mul (α β : E) : is_SBR α → is_SBR β → is_SBR (α * β)
| inv (α : E) : is_SBR α → is_SBR α⁻¹
| rad (α : E) (n : ℕ) (hn : n ≠ 0) : is_SBR (α^n) → is_SBR α

variables (E)

def SBR : intermediate_field F E :=
{ carrier := is_SBR F,
  zero_mem' := by { convert is_SBR.base (0 : F), rw ring_hom.map_zero },
  add_mem' := is_SBR.add,
  neg_mem' := is_SBR.neg,
  one_mem' := by { convert is_SBR.base (1 : F), rw ring_hom.map_one },
  mul_mem' := is_SBR.mul,
  inv_mem' := is_SBR.inv,
  algebra_map_mem' := is_SBR.base }

namespace SBR

variables {F} {E} {α : E}

lemma induction (P : SBR F E → Prop)
(base : ∀ α : F, P (algebra_map F (SBR F E) α))
(add : ∀ α β : SBR F E, P α → P β → P (α + β))
(neg : ∀ α : SBR F E, P α → P (-α))
(mul : ∀ α β : SBR F E, P α → P β → P (α * β))
(inv : ∀ α : SBR F E, P α → P α⁻¹)
(rad : ∀ α : SBR F E, ∀ n : ℕ, n ≠ 0 → P (α^n) → P α)
(α : SBR F E) : P α :=
begin
  revert α,
  suffices : ∀ (α : E), is_SBR F α → (∃ β : SBR F E, ↑β = α ∧ P β),
  { intro α,
    obtain ⟨α₀, hα₀, Pα⟩ := this α (subtype.mem α),
    convert Pα,
    exact subtype.ext hα₀.symm },
  apply is_SBR.rec,
  { exact λ α, ⟨algebra_map F (SBR F E) α, rfl, base α⟩ },
  { intros α β hα hβ Pα Pβ,
    obtain ⟨⟨α₀, hα₀, Pα⟩, β₀, hβ₀, Pβ⟩ := ⟨Pα, Pβ⟩,
    exact ⟨α₀ + β₀, by {rw [←hα₀, ←hβ₀], refl }, add α₀ β₀ Pα Pβ⟩ },
  { intros α hα Pα,
    obtain ⟨α₀, hα₀, Pα⟩ := Pα,
    exact ⟨-α₀, by {rw ←hα₀, refl }, neg α₀ Pα⟩ },
  { intros α β hα hβ Pα Pβ,
    obtain ⟨⟨α₀, hα₀, Pα⟩, β₀, hβ₀, Pβ⟩ := ⟨Pα, Pβ⟩,
    exact ⟨α₀ * β₀, by {rw [←hα₀, ←hβ₀], refl }, mul α₀ β₀ Pα Pβ⟩ },
  { intros α hα Pα,
    obtain ⟨α₀, hα₀, Pα⟩ := Pα,
    exact ⟨α₀⁻¹, by {rw ←hα₀, refl }, inv α₀ Pα⟩ },
  { intros α n hn hα Pα,
    obtain ⟨α₀, hα₀, Pα⟩ := Pα,
    refine ⟨⟨α, is_SBR.rad α n hn hα⟩, rfl, rad _ n hn _⟩,
    convert Pα,
    exact subtype.ext (eq.trans ((SBR F E).coe_pow _ n) hα₀.symm) }
end

theorem is_integral (α : SBR F E) : is_integral F α :=
begin
  revert α,
  apply SBR.induction,
  { exact λ _, is_integral_algebra_map },
  { exact λ _ _, is_integral_add },
  { exact λ _, is_integral_neg },
  { exact λ _ _, is_integral_mul },
  { exact λ α hα, subalgebra.inv_mem_of_algebraic (integral_closure F (SBR F E))
      (show is_algebraic F ↑(⟨α, hα⟩ : integral_closure F (SBR F E)),
        by exact (is_algebraic_iff_is_integral F).mpr hα) },
  { intros α n hn hα,
    obtain ⟨p, h1, h2⟩ := (is_algebraic_iff_is_integral F).mpr hα,
    refine (is_algebraic_iff_is_integral F).mp ⟨p.comp (X ^ n),
      ⟨λ h, h1 (leading_coeff_eq_zero.mp _), by rw [aeval_comp, aeval_X_pow, h2]⟩⟩,
    rwa [←leading_coeff_eq_zero, leading_coeff_comp, leading_coeff_X_pow, one_pow, mul_one] at h,
    rwa nat_degree_X_pow }
end

def P (α : SBR F E) : Prop :=
  is_solvable ((minimal_polynomial (is_integral α)).splitting_field ≃ₐ[F]
    (minimal_polynomial (is_integral α)).splitting_field)

lemma induction0 : P (0 : SBR F E) :=
begin
  rw [P, minimal_polynomial.zero],
  let K := (X : polynomial F).splitting_field,
  have h1 : ⊤ = ⊥ := (is_splitting_field.splits_iff K X).mp (splits_X (ring_hom.id F)),
  have h2 : K ≃ₐ[F] F := (algebra.top_equiv.symm.trans
    (intermediate_field.subalgebra.equiv_of_eq h1)).trans (algebra.bot_equiv F K),
  have h3 : (K ≃ₐ[F] K) ≃* (F ≃ₐ[F] F),
  { sorry },
  sorry,
end

lemma induction1 {α β : SBR F E} (hγ : ↑β ∈ F⟮(α : E)⟯) (hα : P α) : P β :=
begin
  sorry,
end

lemma induction2 {α β γ : SBR F E} (hγ : ↑γ ∈ F⟮(α : E), (β : E)⟯) (hα : P α) (hβ : P β) : P γ :=
begin
  sorry,
end

lemma induction3 : "nth root stuff" = "seems pretty tricky" := sorry

theorem thm (α : SBR F E) : P α :=
begin
  revert α,
  apply SBR.induction,
  { exact λ α, induction1 (algebra_map_mem _ _) induction0 },
  { intros α β,
    apply induction2,
    change ↑α + ↑β ∈ _,
    sorry },
  { exact λ α, induction1 (neg_mem _ (mem_adjoin_simple_self F (α : E))) },
  { intros α β,
    apply induction2,
    change ↑α * ↑β ∈ _,
    apply mul_mem,/- Maybe add these two lemmas to adjoin.lean ? -/
    sorry,
    sorry },
  { exact λ α, induction1 (inv_mem _ (mem_adjoin_simple_self F (α : E))) },
  { sorry },
end

end SBR

end abel_ruffini
