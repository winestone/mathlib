import field_theory.galois
import ring_theory.eisenstein_criterion
import ring_theory.algebraic
import field_theory.algebraic_closure

noncomputable theory
open_locale classical

open polynomial

section arbitrary_field

variables {F : Type*} [field F] (p : polynomial F) (E : Type*) [field E] [algebra F E]

def set_of_roots : set E := ↑(p.map (algebra_map F E)).roots.to_finset

variables {p} {E}

lemma mem_set_of_roots (hp : p ≠ 0) {x : E} :
  x ∈ (set_of_roots p E) ↔ (eval₂ (algebra_map F E) x p = 0) :=
by simp only [set_of_roots, finset.mem_coe, multiset.mem_to_finset,
  mem_roots (map_ne_zero hp), is_root, eval_map]

lemma set_of_roots_zero : set_of_roots (0 : polynomial F) E = ∅ :=
by simp only [set_of_roots, map_zero, roots_zero, multiset.to_finset_zero, finset.coe_empty]

variables (p) (E)

instance root_action : mul_action (E ≃ₐ[F] E) (set_of_roots p E) :=
{ smul := λ ϕ x, ⟨ϕ x, begin
  have key := subtype.mem x,
  by_cases p = 0,
  { simp only [h, set_of_roots_zero, set.mem_empty_eq] at key,
    exact false.rec _ key },
  rw mem_set_of_roots h at key,
  rw mem_set_of_roots h,
  change eval₂ (algebra_map F E) (ϕ.to_alg_hom x) p = 0,
  rw [←alg_hom_eval₂_algebra_map p ϕ.to_alg_hom x, key, alg_hom.map_zero] end⟩,
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

end arbitrary_field

section rational_field

variables (p : polynomial ℚ)

def complex_embedding : p.splitting_field →ₐ[ℚ] ℂ := is_splitting_field.lift (p.splitting_field) p
begin
  rw ← splits_id_iff_splits (algebra_map ℚ ℂ),
  apply complex.is_alg_closed.splits,
end

lemma complex_embedding_zero_range : (complex_embedding (0 : polynomial ℚ)).range = ⊥ :=
begin
  have key := splitting_field.adjoin_roots (0 : polynomial ℚ),
  rw [map_zero, roots_zero, multiset.to_finset_zero, finset.coe_empty, algebra.adjoin_empty] at key,
  rw [←algebra.map_top, ←key, algebra.map_bot],
end

instance complex_embedding_algebra : algebra p.splitting_field ℂ :=
ring_hom.to_algebra (complex_embedding p).to_ring_hom

instance complex_embedding_scalar_tower : is_scalar_tower ℚ p.splitting_field ℂ :=
⟨begin
  intros x y z,
  simp only [algebra.smul_def],
  rw [ring_hom.map_mul, mul_assoc, ←(complex_embedding p).commutes x],
  refl,
end⟩

lemma complex_embedding_range : (complex_embedding p).range =
  algebra.adjoin ℚ (↑(p.map (algebra_map ℚ ℂ)).roots.to_finset : set ℂ) :=
begin
  by_cases p = 0,
  { rw [h, map_zero, roots_zero, multiset.to_finset_zero, finset.coe_empty, algebra.adjoin_empty],
    exact complex_embedding_zero_range },
  have key := (algebra.adjoin_algebra_map ℚ p.splitting_field ℂ
    (↑(p.map (algebra_map ℚ p.splitting_field)).roots.to_finset : set p.splitting_field)).symm,
  rw [splitting_field.adjoin_roots p, algebra.map_top, ←finset.coe_image, finset.image_to_finset,
      ←roots_map (algebra_map p.splitting_field ℂ) ((splits_id_iff_splits
      (algebra_map ℚ p.splitting_field)).mpr (splitting_field.splits p)), map_map,
      ←is_scalar_tower.algebra_map_eq ℚ p.splitting_field ℂ] at key,
  exact key
end

def complex_embedding_equiv : p.splitting_field ≃ₐ[ℚ] (complex_embedding p).range :=
alg_equiv.of_bijective ((complex_embedding p).cod_restrict (complex_embedding p).range
  (λ x, (alg_hom.mem_range (complex_embedding p)).mpr ⟨x, rfl⟩)) ⟨ring_hom.injective _,
  λ x, Exists.cases_on ((alg_hom.mem_range (complex_embedding p)).mp (subtype.mem x))
  (λ y hy, ⟨y, subtype.ext hy⟩)⟩

def conj : ℂ ≃ₐ[ℚ] ℂ :=
{ to_fun := complex.conj,
  inv_fun := complex.conj,
  left_inv := complex.conj_conj,
  right_inv := complex.conj_conj,
  map_add' := ring_hom.map_add complex.conj,
  map_mul' := ring_hom.map_mul complex.conj,
  commutes' := λ x, by { rw is_scalar_tower.algebra_map_eq ℚ ℝ ℂ, exact complex.conj_of_real x } }

lemma complex_embedding_range.conj_mem_of_mem {x : ℂ} :
  x ∈ (complex_embedding p).range → x.conj ∈ (complex_embedding p).range :=
begin
  suffices : (complex_embedding p).range ≤ ((complex_embedding p).range).map conj.to_alg_hom,
  { intro h,
    cases this h with y hy,
    rw ← hy.2,
    rw ← complex.conj_conj y at hy,
    exact hy.1 },
  by_cases p = 0,
  { rw [h, complex_embedding_zero_range, algebra.map_bot, le_bot_iff] },
  rw [complex_embedding_range, algebra.adjoin_le_iff],
  intros x hx,
  rw [finset.mem_coe, multiset.mem_to_finset, mem_roots (map_ne_zero h), is_root, eval_map] at hx,
  use conj x,
  split,
  { apply algebra.subset_adjoin,
    rw [finset.mem_coe, multiset.mem_to_finset, mem_roots (map_ne_zero h), is_root, eval_map],
    apply eq.trans (alg_hom_eval₂_algebra_map p conj.to_alg_hom x).symm,
    rw [hx, alg_hom.map_zero],
    exact field.to_nontrivial ℂ },
  { exact complex.conj_conj x },
  exact field.to_nontrivial ℂ
end

def conj_complex_embedding_range : (complex_embedding p).range ≃ₐ[ℚ] (complex_embedding p).range :=
{ to_fun := λ x, ⟨complex.conj ↑x, complex_embedding_range.conj_mem_of_mem p (subtype.mem x)⟩,
  inv_fun := λ x, ⟨complex.conj ↑x, complex_embedding_range.conj_mem_of_mem p (subtype.mem x)⟩,
  left_inv := λ x, subtype.ext (complex.conj_conj x),
  right_inv := λ x, subtype.ext (complex.conj_conj x),
  map_add' := λ x y, subtype.ext (conj.map_add x y),
  map_mul' := λ x y, subtype.ext (conj.map_mul x y),
  commutes' := λ x, subtype.ext (conj.commutes x) }

def conj_splitting_field : p.splitting_field ≃ₐ[ℚ] p.splitting_field :=
((complex_embedding_equiv p).trans (conj_complex_embedding_range p)).trans
  (complex_embedding_equiv p).symm

lemma tada (p_irr : irreducible p) (p_deg : p.nat_degree.prime)
  (p_roots : (p.map (algebra_map ℚ ℝ)).roots.card = p.nat_degree - 2) :
function.bijective (root_action_hom p) :=
begin
  split,
  { exact root_action_hom_injective p },
  have FTA := complex.is_alg_closed.splits,
  replace FTA := (splits_id_iff_splits (algebra_map ℚ ℂ)).mp (FTA (p.map (algebra_map ℚ ℂ))),
  have key := is_splitting_field.lift (p.splitting_field) p FTA,
  sorry,
end

end rational_field

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
