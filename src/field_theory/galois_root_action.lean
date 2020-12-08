import field_theory.galois
import ring_theory.algebraic
import field_theory.algebraic_closure

noncomputable theory
open_locale classical

open polynomial finite_dimensional

def alg_hom.alg_equiv_range {A B C : Type*} [comm_semiring A] [semiring B] [semiring C]
[algebra A B] [algebra A C] (f : B →ₐ[A] C) (hf : function.injective f) : B ≃ₐ[A] f.range :=
alg_equiv.of_bijective (f.cod_restrict f.range (λ x, f.mem_range.mpr ⟨x, rfl⟩))
⟨(f.injective_cod_restrict f.range (λ x, f.mem_range.mpr ⟨x, rfl⟩)).mpr hf,
  λ x, Exists.cases_on (f.mem_range.mp (subtype.mem x)) (λ y hy, ⟨y, subtype.ext hy⟩)⟩

def alg_hom.alg_equiv_range_field {A B C : Type*} [comm_semiring A] [field B] [field C]
[algebra A B] [algebra A C] (f : B →ₐ[A] C) : B ≃ₐ[A] f.range :=
f.alg_equiv_range f.to_ring_hom.injective

section rational_field

namespace rational_polynomial

variables (p : polynomial ℚ)

instance : finite_dimensional ℚ p.splitting_field :=
is_splitting_field.finite_dimensional p.splitting_field p

@[reducible]
def gal := p.splitting_field ≃ₐ[ℚ] p.splitting_field

instance : group (gal p) := alg_equiv.aut

instance : fintype (gal p) := alg_equiv.fintype ℚ p.splitting_field

/- Will be used to show that gal contains a p-cycle -/
lemma prime_degree_dvd_card (p_irr : irreducible p) (p_deg : p.nat_degree.prime) :
  p.nat_degree ∣ fintype.card (gal p) :=
begin
  haveI := of_separable_splitting_field (is_splitting_field.splitting_field p)
    (irreducible.separable p_irr p_irr.ne_zero),/- Todo: refactor irreducible.separable to eliminate ne_zero assumption-/
  rw is_galois.card_aut_eq_findim ℚ p.splitting_field,
  have hp : p.degree ≠ 0 :=
    λ h, nat.prime.ne_zero p_deg (nat_degree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h)),
  let α : p.splitting_field := root_of_splits (algebra_map ℚ p.splitting_field)
    (splitting_field.splits p) hp,
  have hα : is_integral ℚ α :=
    (is_algebraic_iff_is_integral ℚ).mp (algebra.is_algebraic_of_finite α),
  use findim ℚ⟮α⟯ p.splitting_field,
  suffices : (minimal_polynomial hα).nat_degree = p.nat_degree,
  { rw [←findim_mul_findim ℚ ℚ⟮α⟯ p.splitting_field, intermediate_field.adjoin.findim hα, this] },
  suffices : minimal_polynomial hα ∣ p,
  { have key := dvd_symm_of_irreducible (minimal_polynomial.irreducible hα) p_irr this,
    apply le_antisymm,
    { exact nat_degree_le_of_dvd this p_irr.ne_zero },
    { exact nat_degree_le_of_dvd key (minimal_polynomial.ne_zero hα) } },
  apply minimal_polynomial.dvd hα,
  rw [aeval_def, map_root_of_splits _ (splitting_field.splits p) hp]
end

def embedding : p.splitting_field →ₐ[ℚ] ℂ := splitting_field.lift p
  ((splits_id_iff_splits (algebra_map ℚ ℂ)).mp (is_alg_closed.splits (p.map (algebra_map ℚ ℂ))))

instance : algebra p.splitting_field ℂ := ring_hom.to_algebra (embedding p).to_ring_hom

instance : is_scalar_tower ℚ p.splitting_field ℂ :=
is_scalar_tower.of_algebra_map_eq (λ x, ((embedding p).commutes x).symm)

lemma embedding_range : (embedding p).range =
  algebra.adjoin ℚ (↑(p.map (algebra_map ℚ ℂ)).roots.to_finset : set ℂ) :=
begin
  rw [is_scalar_tower.algebra_map_eq ℚ p.splitting_field ℂ, ←map_map,
    roots_map (algebra_map p.splitting_field ℂ), ←finset.image_to_finset, finset.coe_image,
    ←algebra.map_top, ←splitting_field.adjoin_roots p, algebra.adjoin_algebra_map],
  refl,
  exact ((splits_id_iff_splits (algebra_map ℚ p.splitting_field)).mpr (splitting_field.splits p))
end

def embedding_range_alg_hom : (embedding p).range →ₐ[ℚ] (embedding p).range :=
{ to_fun := λ x, ⟨complex.conj x, begin
    let c : ℂ →ₐ[ℚ] ℂ := { commutes' := λ x, by { rw is_scalar_tower.algebra_map_eq ℚ ℝ ℂ,
      exact complex.conj_of_real x, } .. complex.conj },
    suffices : (embedding p).range ≤ ((embedding p).range).map c,
    { have key := this (subtype.mem x),
      cases key with y hy,
      rw ← hy.2,
      rw ← complex.conj_conj y at hy,
      exact hy.1 },
    rw [embedding_range, algebra.adjoin_le_iff],
    intros x hx,
    use c x,
    split,
    { apply algebra.subset_adjoin,
      rw [finset.mem_coe, multiset.mem_to_finset] at *,
      by_cases p = 0,
      { rw [h, map_zero] at hx,
        exact false.rec _ hx },
      { simp only [mem_roots (map_ne_zero h), is_root, eval_map] at *,
        rw [←alg_hom_eval₂_algebra_map, hx, alg_hom.map_zero] } },
    { exact complex.conj_conj x }
  end⟩,
  map_zero' := by { ext1, exact ring_hom.map_zero complex.conj },
  map_one' := by { ext1, exact ring_hom.map_one complex.conj },
  map_add' := λ x y, by { ext1, exact ring_hom.map_add complex.conj x y },
  map_mul' := λ x y, by { ext1, exact ring_hom.map_mul complex.conj x y },
  commutes' := λ x, begin
    ext1,
    change complex.conj (algebra_map (embedding p).range ℂ (algebra_map ℚ (embedding p).range x)) =
      algebra_map (embedding p).range ℂ (algebra_map ℚ (embedding p).range x),
    rw ←is_scalar_tower.algebra_map_apply ℚ (embedding p).range ℂ,
    rw is_scalar_tower.algebra_map_apply ℚ ℝ ℂ,
    exact complex.conj_of_real x,
  end }

lemma embedding_range_alg_hom_involution :
  (embedding_range_alg_hom p).comp (embedding_range_alg_hom p) =
  (alg_hom.id ℚ (embedding p).range) :=
alg_hom.ext (λ x, subtype.ext (complex.conj_conj x))

def embedding_range_alg_equiv : (embedding p).range ≃ₐ[ℚ] (embedding p).range :=
alg_equiv.of_alg_hom (embedding_range_alg_hom p) (embedding_range_alg_hom p)
(embedding_range_alg_hom_involution p) (embedding_range_alg_hom_involution p)

def conjugation : gal p :=
((embedding p).alg_equiv_range_field.trans (embedding_range_alg_equiv p)).trans
  ((embedding p).alg_equiv_range_field.symm)

lemma conjugation_involution : (conjugation p) * (conjugation p) = 1 :=
begin
  change (conjugation p).trans (conjugation p) = 1,
  ext x,
  let ϕ := embedding_range_alg_equiv p,
  have key : ∀ (y : (embedding p).range), ϕ (ϕ y) = y :=
    λ y, alg_hom.ext_iff.mp (embedding_range_alg_hom_involution p) y,
  simp only [conjugation, alg_equiv.trans_apply, alg_equiv.apply_symm_apply,
    alg_equiv.symm_apply_apply, key],
  refl,
end

def roots_aux : set (splitting_field p) :=
↑(p.map (algebra_map ℚ p.splitting_field)).roots.to_finset

def roots : set ℂ := ↑(p.map (algebra_map ℚ ℂ)).roots.to_finset

def map_roots_aux : (roots_aux p) → (roots p) :=
λ x, ⟨embedding p x, begin
  have key := subtype.mem x,
  simp only [roots_aux, roots, finset.mem_coe, multiset.mem_to_finset] at *,
  by_cases p = 0,
  { simp only [h, map_zero] at key,
    exact false.rec _ key },
  { simp only [mem_roots (map_ne_zero h), is_root, eval_map] at *,
    rw [←alg_hom_eval₂_algebra_map, key, alg_hom.map_zero] } end⟩

lemma map_roots_aux_bijective : function.bijective (map_roots_aux p) :=
begin
  split,
  { exact λ _ _ h, subtype.ext ((embedding p).to_ring_hom.injective (subtype.ext_iff.mp h)) },
  { intro y,
    have key := roots_map (embedding p : p.splitting_field →+* ℂ) ((splits_id_iff_splits
      (algebra_map ℚ p.splitting_field)).mpr (is_splitting_field.splits p.splitting_field p)),
    rw [map_map, alg_hom.comp_algebra_map (embedding p)] at key,
    have hy := subtype.mem y,
    simp only [roots, finset.mem_coe, multiset.mem_to_finset, key, multiset.mem_map] at hy,
    rcases hy with ⟨x, hx1, hx2⟩,
    rw [←multiset.mem_to_finset, ←finset.mem_coe] at hx1,
    exact ⟨⟨x, hx1⟩, subtype.ext hx2⟩ }
end

def roots_aux_equiv_roots : (roots_aux p) ≃ (roots p) :=
equiv.of_bijective (map_roots_aux p) (map_roots_aux_bijective p)

instance gal_action_aux : mul_action (gal p) (roots_aux p) :=
{ smul := λ ϕ x, ⟨ϕ x, begin
    have key := subtype.mem x,
    simp only [roots, roots_aux, finset.mem_coe, multiset.mem_to_finset] at *,
    by_cases p = 0,
    { simp only [h, map_zero] at key,
      exact false.rec _ key },
    { simp only [mem_roots (map_ne_zero h), is_root, eval_map] at *,
      change eval₂ (algebra_map ℚ p.splitting_field) (ϕ.to_alg_hom x) p = 0,
      rw [←alg_hom_eval₂_algebra_map, key, alg_hom.map_zero] } end⟩,
  one_smul := λ _, by { ext, refl },
  mul_smul := λ _ _ _, by { ext, refl } }

instance gal_action : mul_action (gal p) (roots p) :=
{ smul := λ ϕ x, roots_aux_equiv_roots p (ϕ • ((roots_aux_equiv_roots p).symm x)),
  one_smul := λ _, by simp only [equiv.apply_symm_apply, one_smul],
  mul_smul := λ _ _ _, by simp only [equiv.apply_symm_apply, equiv.symm_apply_apply, mul_smul] }

/- Will be used to show that gal has a transposition -/
lemma conjugation_action {x : roots p} : ↑((conjugation p) • x) = complex.conj x :=
begin
  let ϕ := (embedding p).alg_equiv_range_field,
  change ↑(ϕ (ϕ.symm _)) = complex.conj x,
  rw alg_equiv.apply_symm_apply ϕ,
  change complex.conj (roots_aux_equiv_roots p ((roots_aux_equiv_roots p).symm x)) = complex.conj x,
  rw equiv.apply_symm_apply (roots_aux_equiv_roots p),
end

def gal_action_hom : gal p →* equiv.perm (roots p) :=
{ to_fun := λ ϕ, equiv.mk (λ x, ϕ • x) (λ x, ϕ⁻¹ • x)
  (λ x, inv_smul_smul ϕ x) (λ x, smul_inv_smul ϕ x),
  map_one' := by { ext1 x, exact mul_action.one_smul x },
  map_mul' := λ x y, by { ext1 z, exact mul_action.mul_smul x y z } }

lemma gal_action_hom_injective : function.injective (gal_action_hom p) :=
begin
  rw monoid_hom.injective_iff,
  intros ϕ hϕ,
  let equalizer := alg_hom.equalizer ϕ.to_alg_hom (alg_hom.id ℚ p.splitting_field),
  suffices : equalizer = ⊤,
  { exact alg_equiv.ext (λ x, (subalgebra.ext_iff.mp this x).mpr algebra.mem_top) },
  rw [eq_top_iff, ←splitting_field.adjoin_roots p, algebra.adjoin_le_iff],
  intros x hx,
  have key := equiv.perm.ext_iff.mp hϕ (roots_aux_equiv_roots p ⟨x, hx⟩),
  change roots_aux_equiv_roots p (ϕ • (roots_aux_equiv_roots p).symm
    (roots_aux_equiv_roots p ⟨x, hx⟩)) = roots_aux_equiv_roots p ⟨x, hx⟩ at key,
  rw equiv.symm_apply_apply at key,
  exact subtype.ext_iff.mp (equiv.injective (roots_aux_equiv_roots p) key),
end

end rational_polynomial

end rational_field
