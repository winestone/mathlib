import field_theory.galois
import ring_theory.eisenstein_criterion
import ring_theory.algebraic
import field_theory.algebraic_closure

noncomputable theory
open_locale classical

open polynomial intermediate_field

def alg_hom.alg_equiv_range {A B C : Type*} [comm_semiring A] [semiring B] [semiring C]
[algebra A B] [algebra A C] (f : B →ₐ[A] C) (hf : function.injective f) : B ≃ₐ[A] f.range :=
alg_equiv.of_bijective (f.cod_restrict f.range (λ x, f.mem_range.mpr ⟨x, rfl⟩))
⟨(f.injective_cod_restrict f.range (λ x, f.mem_range.mpr ⟨x, rfl⟩)).mpr hf,
  λ x, Exists.cases_on (f.mem_range.mp (subtype.mem x)) (λ y hy, ⟨y, subtype.ext hy⟩)⟩

def alg_hom.alg_equiv_range_field {A B C : Type*} [comm_semiring A] [field B] [field C]
[algebra A B] [algebra A C] (f : B →ₐ[A] C) : B ≃ₐ[A] f.range :=
f.alg_equiv_range f.to_ring_hom.injective

section alg_equiv_restrict

variables {F K : Type*} [field F] [field K] [algebra F K] (ϕ ψ : K →ₐ[F] K) (χ ω : K ≃ₐ[F] K)
  (p : polynomial F) (E : Type*) [field E] [algebra F E] [algebra E K]  [is_scalar_tower F E K]

lemma lem1 [hp : is_splitting_field F E p] :
(is_scalar_tower.to_alg_hom F E K).range =
  algebra.adjoin F (↑(p.map (algebra_map F K)).roots.to_finset : set K) :=
begin
  rw [is_scalar_tower.algebra_map_eq F E K, ←map_map, roots_map, ←finset.image_to_finset,
    finset.coe_image, algebra.adjoin_algebra_map, hp.adjoin_roots, algebra.map_top],
  exact ((splits_id_iff_splits (algebra_map F E)).mpr hp.splits),
end

def alg_hom.restrict_is_splitting_field_aux [hp : is_splitting_field F E p] :
(is_scalar_tower.to_alg_hom F E K).range →ₐ[F] (is_scalar_tower.to_alg_hom F E K).range :=
{ to_fun := λ x, ⟨ϕ x, begin
    suffices : (is_scalar_tower.to_alg_hom F E K).range.map ϕ ≤ _,
    { exact this ⟨x, subtype.mem x, rfl⟩ },
    simp only [lem1 p, ←algebra.adjoin_image, ←finset.coe_image, finset.image_to_finset],
    apply algebra.adjoin_mono,
    by_cases p = 0,
    { rw [h, map_zero, roots_zero, multiset.map_zero] },
    { intro y,
      simp only [finset.mem_coe, multiset.mem_to_finset, multiset.mem_map,
        mem_roots (map_ne_zero h), is_root, eval_map],
      rintros ⟨z, hz1, hz2⟩,
      rw [←hz2, ←alg_hom_eval₂_algebra_map, hz1, ϕ.map_zero] },
  end⟩,
  map_zero' := subtype.ext ϕ.map_zero,
  map_one' := subtype.ext ϕ.map_one,
  map_add' := λ x y, subtype.ext (ϕ.map_add x y),
  map_mul' := λ x y, subtype.ext (ϕ.map_mul x y),
  commutes' := λ x, subtype.ext (ϕ.commutes x) }

def alg_hom.restrict_is_splitting_field [hp : is_splitting_field F E p] : E →ₐ[F] E :=
((is_scalar_tower.to_alg_hom F E K).alg_equiv_range_field.symm.to_alg_hom.comp
  (ϕ.restrict_is_splitting_field_aux p E)).comp
    (is_scalar_tower.to_alg_hom F E K).alg_equiv_range_field.to_alg_hom

lemma alg_hom.restrict_is_splitting_field_commutes [hp : is_splitting_field F E p] (x : E) :
algebra_map E K (ϕ.restrict_is_splitting_field p E x) = ϕ (algebra_map E K x) :=
subtype.ext_iff.mp (alg_equiv.apply_symm_apply
  (is_scalar_tower.to_alg_hom F E K).alg_equiv_range_field (ϕ.restrict_is_splitting_field_aux p E
    ⟨is_scalar_tower.to_alg_hom F E K x, ⟨x, ⟨subsemiring.mem_top x, rfl⟩⟩⟩))

lemma alg_hom.restrict_is_splitting_field_comp [hp : is_splitting_field F E p] :
(ϕ.restrict_is_splitting_field p E).comp (ψ.restrict_is_splitting_field p E) =
  (ϕ.comp ψ).restrict_is_splitting_field p E :=
alg_hom.ext (λ _, (algebra_map E K).injective (by
{ simp only [alg_hom.comp_apply, alg_hom.restrict_is_splitting_field_commutes] }))

def alg_equiv.restrict_is_splitting_field [hp : is_splitting_field F E p] : E ≃ₐ[F] E :=
alg_equiv.of_alg_hom (χ.to_alg_hom.restrict_is_splitting_field p E)
(χ.symm.to_alg_hom.restrict_is_splitting_field p E)
(alg_hom.ext (λ _, (algebra_map E K).injective (by
{ simp only [alg_hom.comp_apply, alg_hom.restrict_is_splitting_field_commutes,
    alg_equiv.to_alg_hom_eq_coe, alg_equiv.coe_alg_hom, alg_hom.id_apply, χ.apply_symm_apply] })))
(alg_hom.ext (λ _, (algebra_map E K).injective (by
{ simp only [alg_hom.comp_apply, alg_hom.restrict_is_splitting_field_commutes,
    alg_equiv.to_alg_hom_eq_coe, alg_equiv.coe_alg_hom, alg_hom.id_apply, χ.symm_apply_apply] })))

lemma alg_equiv.restrict_is_splitting_field_commutes [is_splitting_field F E p] (x : E) :
algebra_map E K (χ.restrict_is_splitting_field p E x) = χ (algebra_map E K x) :=
χ.to_alg_hom.restrict_is_splitting_field_commutes p E x

lemma alg_equiv.restrict_is_splitting_field_comp [hp : is_splitting_field F E p] :
(χ.restrict_is_splitting_field p E).trans (ω.restrict_is_splitting_field p E) =
  (χ.trans ω).restrict_is_splitting_field p E :=
alg_equiv.ext (λ _, (algebra_map E K).injective (by
{ simp only [alg_equiv.trans_apply, alg_equiv.restrict_is_splitting_field_commutes] }))

def alg_equiv.restict_is_splitting_field_hom [hp : is_splitting_field F E p] :
(K ≃ₐ[F] K) →* (E ≃ₐ[F] E) :=
monoid_hom.mk' (λ χ, χ.restrict_is_splitting_field p E)
  (λ ω χ, (χ.restrict_is_splitting_field_comp ω p E).symm)

lemma alg_equiv.restrict_is_splitting_field_hom_surjective [hp : is_splitting_field F E p]
  [finite_dimensional E K] : function.surjective
  ((alg_equiv.restict_is_splitting_field_hom p E) : (K ≃ₐ[F] K) →* (E ≃ₐ[F] E)).to_fun :=
begin
  sorry,
end


end alg_equiv_restrict

section abel_ruffini

variables {F : Type*} [field F] {E : Type*} [field E] [algebra F E]

def Gal (p : polynomial F) := p.splitting_field ≃ₐ[F] p.splitting_field

instance (p : polynomial F) : group (Gal p) := alg_equiv.aut

instance (p q : polynomial F) : has_scalar p.splitting_field (p * q).splitting_field :=
{ smul := sorry,
}

instance (p q : polynomial F) : algebra p.splitting_field (p * q).splitting_field :=
{ to_fun := sorry,
  map_zero' := sorry,
  map_one' := sorry,
  map_add' := sorry,
  map_mul' := sorry,
  smul_def' := sorry,
  commutes' := sorry,
}

instance (p q : polynomial F) : is_scalar_tower F p.splitting_field (p * q).splitting_field :=
{ smul_assoc := sorry,
}

def swap {p q : polynomial F} (φ : Gal (p * q)) : Gal (q * p) :=
{ to_fun := sorry,
  inv_fun := sorry,
  map_add' := sorry,
  map_mul' := sorry,
  commutes' := sorry,
  right_inv := sorry,
  left_inv := sorry,
}

def gal_prod_to_prod_gal (p q : polynomial F) : Gal (p * q) →* Gal p × Gal q :=
{ to_fun := λ f, ⟨alg_equiv.restrict_is_splitting_field f p _, alg_equiv.restrict_is_splitting_field (swap f) q _⟩,
  map_one' := sorry,
  map_mul' := sorry,
}

lemma gal_prod_to_prod_gal_inj (p q : polynomial F) :
  function.injective (gal_prod_to_prod_gal p q) := sorry

lemma gal_prod_solvable (p q : polynomial F) (hp : is_solvable (Gal p)) (hq : is_solvable (Gal q)) :
  is_solvable (Gal (p * q)) :=
solvable_of_solvable_injective (gal_prod_to_prod_gal_inj p q) (solvable_prod hp hq)

variables (F)

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

def P (α : SBR F E) : Prop := is_solvable $ Gal $ minimal_polynomial (is_integral α)

lemma induction3 {α : SBR F E} {n : ℕ} (hn : n ≠ 0) (hα : P (α ^ n)) : P α :=
begin
  sorry,
end

lemma induction2 {α β γ : SBR F E} (hγ : γ ∈ F⟮α, β⟯) (hα : P α) (hβ : P β) : P γ :=
begin
  let p := (minimal_polynomial (is_integral α)),
  let q := (minimal_polynomial (is_integral β)),
  let r := (minimal_polynomial (is_integral γ)),
  -- (p * q).splitting_field.aut embeds into p.splitting_field.aut × q.splitting_field.aut
  -- (p * q).splitting_field.aut surjects onto r.splitting_field.aut
  -- Define F(α, β) ↪ (p * q).splitting_field
  -- F⟮α, β⟯ ↪ (p * q).splitting_field takes γ to a root of r
  -- By Galois, r splits
  -- So we get an embedding r.splitting_field ↪ (p * q).splitting_field
  -- So we can use a general theorem of galois theory to say that Gal (p * q) surjects onto Gal r
  sorry,
end

lemma induction1 {α β : SBR F E} (hβ : β ∈ F⟮α⟯) (hα : P α) : P β :=
induction2 (adjoin.mono F _ _ (ge_of_eq (set.pair_eq_singleton α)) hβ) hα hα

lemma top_eq_bot_of_top_eq_bot {R A : Type*} [comm_semiring R] [semiring A] [algebra R A]
(h : ⊤ = (⊥ : subalgebra R A)) : ⊤ = (⊥ : subgroup (A ≃ₐ[R] A)) :=
begin
  rw subgroup.eq_bot_iff_forall,
  rintros f -,
  ext a,
  have key : a ∈ (⊥ : subalgebra R A) := eq_bot_iff.mp h algebra.mem_top,
  rcases set.mem_range.mp (algebra.mem_bot.mp key) with ⟨x, rfl⟩,
  rw [alg_equiv.commutes, alg_equiv.commutes],
end

lemma induction0 : P (0 : SBR F E) :=
begin
  rw [P, minimal_polynomial.zero],
  let K := (X : polynomial F).splitting_field,
  have h : ⊤ = ⊥ := (is_splitting_field.splits_iff K X).mp (splits_X (ring_hom.id F)),
  exact is_solvable_of_top_eq_bot _ (top_eq_bot_of_top_eq_bot h),
end

theorem thm (α : SBR F E) : P α :=
begin
  revert α,
  apply SBR.induction,
  { exact λ α, induction1 (algebra_map_mem _ _) induction0 },
  { exact λ α β, induction2 (add_mem _ (subset_adjoin F _ (set.mem_insert α _))
      (subset_adjoin F _ (set.mem_insert_of_mem α (set.mem_singleton β)))) },
  { exact λ α, induction1 (neg_mem _ (mem_adjoin_simple_self F α)) },
  { exact λ α β, induction2 (mul_mem _ (subset_adjoin F _ (set.mem_insert α _))
      (subset_adjoin F _ (set.mem_insert_of_mem α (set.mem_singleton β)))) },
  { exact λ α, induction1 (inv_mem _ (mem_adjoin_simple_self F α)) },
  { exact λ α n, induction3 },
end

end SBR

end abel_ruffini
