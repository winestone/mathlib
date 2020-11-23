import field_theory.galois
import ring_theory.eisenstein_criterion
import ring_theory.algebraic

noncomputable theory
open_locale classical

open polynomial

variables {F : Type*} [field F]

def set_of_roots (p : polynomial F) (E : Type*) [field E] [algebra F E] :
  set E := ↑(p.map (algebra_map F E)).roots.to_finset

lemma mem_set_of_roots {E : Type*} [field E] [algebra F E] {p : polynomial F} (hp : p ≠ 0) {x : E} :
  x ∈ (set_of_roots p E) ↔ (eval₂ (algebra_map F E) x p = 0) :=
by simp only [set_of_roots, finset.mem_coe, multiset.mem_to_finset,
  mem_roots (map_ne_zero hp), is_root, eval_map]

lemma set_of_roots_zero {E : Type*} [field E] [algebra F E] :
  set_of_roots (0 : polynomial F) E = ∅ :=
by simp only [set_of_roots, map_zero, roots_zero, multiset.to_finset_zero, finset.coe_empty]

variables (p : polynomial F) (E : Type*) [field E] [algebra F E]

instance root_action : mul_action (E ≃ₐ[F] E) (set_of_roots p E) :=
{ smul := λ ϕ x, ⟨ϕ x, begin
  have key := subtype.mem x,
  by_cases p = 0,
  { simp only [h, set_of_roots_zero, set.mem_empty_eq] at key,
    exact false.rec _ key },
  rw mem_set_of_roots h at key,
  rw mem_set_of_roots h,
  change polynomial.eval₂ (algebra_map F E) (ϕ.to_alg_hom x) p = 0,
  rw [←polynomial.alg_hom_eval₂_algebra_map p ϕ.to_alg_hom x, key, alg_hom.map_zero] end⟩,
  one_smul := λ _, by { ext, refl },
  mul_smul := λ _ _ _, by { ext, refl } }

def root_action_hom :
  (p.splitting_field ≃ₐ[F] p.splitting_field) →* equiv.perm (set_of_roots p p.splitting_field) :=
{ to_fun := λ ϕ, equiv.mk (λ x, ϕ • x) (λ x, ϕ⁻¹ • x) (λ x, inv_smul_smul ϕ x) (λ x, smul_inv_smul ϕ x),
  map_one' := by { ext, refl },
  map_mul' := λ _ _, by { ext, refl } }

lemma root_action_hom_injective : function.injective (root_action_hom p) :=
begin
  rw monoid_hom.injective_iff,
  intros ϕ hϕ,
  let equalizer := alg_hom.equalizer ϕ.to_alg_hom (alg_hom.id F p.splitting_field),
  suffices : equalizer = ⊤,
  { exact alg_equiv.ext (λ x, (subalgebra.ext_iff.mp this x).mpr algebra.mem_top) },
  rw [eq_top_iff, ←splitting_field.adjoin_roots p, algebra.adjoin_le_iff],
  exact λ x hx, subtype.ext_iff.mp (equiv.perm.ext_iff.mp hϕ ⟨x, hx⟩),
end

instance : finite_dimensional F p.splitting_field :=
is_splitting_field.finite_dimensional p.splitting_field p

instance gal_fintype : fintype (p.splitting_field ≃ₐ[F] p.splitting_field) :=
alg_equiv.fintype F p.splitting_field

lemma prime_degree_dvd_findim (p_irr : irreducible p) (p_deg : p.nat_degree.prime) :
  p.nat_degree ∣ finite_dimensional.findim F p.splitting_field :=
begin
  have hp : p.degree ≠ 0,
  { intro h,
    apply nat.prime.ne_zero p_deg,
    rw [←with_bot.coe_eq_coe, with_bot.coe_zero, ←degree_eq_nat_degree (p_irr.ne_zero), h] },
  let α : p.splitting_field :=
    root_of_splits (algebra_map F p.splitting_field) (splitting_field.splits p) hp,
  suffices : finite_dimensional.findim F F⟮α⟯ = p.nat_degree,
  { use finite_dimensional.findim F⟮α⟯ p.splitting_field,
    rw ← this,
    exact (finite_dimensional.findim_mul_findim F F⟮α⟯ p.splitting_field).symm },
  have hα : is_integral F α :=
    (is_algebraic_iff_is_integral F).mp (algebra.is_algebraic_of_finite α),
  rw intermediate_field.adjoin.findim hα,
  suffices : minimal_polynomial hα ∣ p,
  { have key := dvd_symm_of_irreducible (minimal_polynomial.irreducible hα) p_irr this,
    apply le_antisymm,
    { exact nat_degree_le_of_dvd this p_irr.ne_zero },
    { exact nat_degree_le_of_dvd key (minimal_polynomial.ne_zero hα) } },
  apply minimal_polynomial.dvd hα,
  rw aeval_def,
  exact map_root_of_splits (algebra_map F p.splitting_field) (splitting_field.splits p) hp,
end

lemma prime_degree_dvd_card (p_irr : irreducible p) (p_sep : p.separable) (p_deg : p.nat_degree.prime) :
  p.nat_degree ∣ fintype.card (p.splitting_field ≃ₐ[F] p.splitting_field) :=
begin
  haveI p_gal := galois.is_galois_of_separable_splitting_field
    (is_splitting_field.splitting_field p) p_sep,
  rw galois.is_galois_implies_card_aut_eq_findim F p.splitting_field,
  exact prime_degree_dvd_findim p p_irr p_deg,
end
