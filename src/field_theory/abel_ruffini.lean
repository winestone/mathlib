import field_theory.galois
import ring_theory.eisenstein_criterion
import ring_theory.algebraic
import field_theory.algebraic_closure
import group_theory.solvable
import field_theory.polynomial_galois_group

noncomputable theory
open_locale classical

open polynomial intermediate_field

section abel_ruffini

variables {F : Type*} [field F] {E : Type*} [field E] [algebra F E]

lemma gal_C_solvable (x : F) : is_solvable (gal (C x)) :=
begin
  sorry,
end

lemma gal_mul_solvable {p q : polynomial F}
  (hp : is_solvable (gal p)) (hq : is_solvable (gal q)) : is_solvable (gal (p * q)) :=
begin
  haveI := solvable_prod hp hq,
  exact solvable_of_solvable_injective (gal.restrict_prod_injective p q),
end

lemma gal_prod_solvable {s : multiset (polynomial F)}
  (hs : ∀ p ∈ s, is_solvable (gal p)) : is_solvable (gal s.prod) :=
begin
  sorry,
end

lemma lemma2 {p q : polynomial F} (hpq : fact (splits (algebra_map F q.splitting_field) p))
  (hq : is_solvable (gal q)) : is_solvable (gal p) :=
begin
  haveI : is_solvable (q.splitting_field ≃ₐ[F] q.splitting_field) := hq,
  exact solvable_of_surjective (alg_equiv.restrict_normal_hom_surjective q.splitting_field),
end

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

theorem SBR_is_integral (α : SBR F E) : is_integral F α :=
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

def P (α : SBR F E) : Prop := is_solvable (minpoly F α).gal

--change key to fact!
lemma gal_X_pow_sub_C_is_solvable {n : ℕ} (hn : n ≠ 0) (x : F) : is_solvable (X ^ n - C x).gal :=
begin
  let K := (X ^ n - C (1 : F)).splitting_field,
  let L := (X ^ n - C x).splitting_field,
  have key : (X ^ n - C (1 : F)).splits (algebra_map F (X ^ n - C x).splitting_field) := sorry,
  let f : K →ₐ[F] L := splitting_field.lift (X ^ n - C (1 : F)) key,
  letI : algebra K L := f.to_ring_hom.to_algebra,
  haveI : is_scalar_tower F K L := is_scalar_tower.of_ring_hom f,
  --haveI : normal F K := splitting_field.normal (X ^ n - C (1 : F)),
  --haveI : normal F L := splitting_field.normal (X ^ n - C x),
  sorry,
end

lemma induction3 {α : SBR F E} {n : ℕ} (hn : n ≠ 0) (hα : P (α ^ n)) : P α :=
begin
  let p := minpoly F (α ^ n),
  let K := p.splitting_field,
  let L := (p.comp (X ^ n)).splitting_field,
  let f : K →ₐ[F] L := splitting_field.lift p
    (gal.splits_in_splitting_field_of_comp p (X ^ n) (by rwa [nat_degree_X_pow])),
  letI : algebra K L := f.to_ring_hom.to_algebra,
  haveI : is_scalar_tower F K L := is_scalar_tower.of_ring_hom f,
  haveI : normal F K := splitting_field.normal p,
  haveI nFL : normal F L := splitting_field.normal (p.comp (X ^ n)),
  haveI : is_solvable (K ≃ₐ[F] K) := hα,
  suffices : is_solvable (L ≃ₐ[K] L),
  { haveI := this,
    refine lemma2 (splits_of_splits_of_dvd _ (λ h, _) (splitting_field.splits (p.comp (X ^ n)))
    (minpoly.dvd F α (by rw [aeval_comp, aeval_X_pow, minpoly.aeval]))) (tada F K L),
    cases (comp_eq_zero_iff.mp h) with h' h',
    { exact minpoly.ne_zero (SBR_is_integral (α ^ n)) h' },
    { exact hn (by rw [←nat_degree_C _, ←h'.2, nat_degree_X_pow]) } },
  /-have h1 : is_splitting_field K L ((p.comp (X ^ n)).map (algebra_map F K)),
  { exact is_splitting_field.map (p.comp (X ^ n)) },-/
  have h2 : L ≃ₐ[K] ((p.comp (X ^ n)).map (algebra_map F K)).splitting_field,
  { exact is_splitting_field.alg_equiv L ((p.comp (X ^ n)).map (algebra_map F K)) },
  suffices : is_solvable ((p.comp (X ^ n)).map (algebra_map F K)).gal,
  { /- transfer solvable along the isomorphism -/
    sorry },
  obtain ⟨s, hs⟩ := (splits_iff_exists_multiset (algebra_map F K)).mp (splitting_field.splits p),
  rw [map_comp, map_pow, map_X, hs, mul_comp, C_comp],
  apply gal_mul_solvable,
  { exact gal_C_solvable _ },
  rw ← (show _ = (s.map (λ a, X - C a)).prod.comp (X ^ n), from multiset.prod_hom _
    (monoid_hom.mk (λ (q : polynomial K), q.comp (X ^ n)) one_comp (λ q r, mul_comp q r (X ^ n)))),
  apply gal_prod_solvable,
  intros q hq,
  rw multiset.mem_map at hq,
  rcases hq with ⟨q, hq, rfl⟩,
  rw multiset.mem_map at hq,
  rcases hq with ⟨q, hq, rfl⟩,
  change is_solvable ((X - C q).comp (X ^ n)).gal,
  rw [sub_comp, C_comp, X_comp],
  exact gal_X_pow_sub_C_is_solvable hn _,
end

lemma induction2 {α β γ : SBR F E} (hγ : γ ∈ F⟮α, β⟯) (hα : P α) (hβ : P β) : P γ :=
begin
  let p := (minpoly F α),
  let q := (minpoly F β),
  have hpq := polynomial.splits_of_splits_mul _ (mul_ne_zero (minpoly.ne_zero (SBR_is_integral α))
    (minpoly.ne_zero (SBR_is_integral β))) (splitting_field.splits (p * q)),
  have f : F⟮α, β⟯ →ₐ[F] (p * q).splitting_field := classical.choice (alg_hom_mk_adjoin_splits
  begin
    intros x hx,
    cases hx,
    rw hx,
    exact ⟨SBR_is_integral α, hpq.1⟩,
    cases hx,
    exact ⟨SBR_is_integral β, hpq.2⟩,
  end),
  have key : minpoly F γ = minpoly F (f ⟨γ, hγ⟩) := minpoly.unique' (normal.is_integral
    (splitting_field.normal _) _) (minpoly.irreducible (SBR_is_integral γ)) begin
      suffices : aeval (⟨γ, hγ⟩ : F ⟮α, β⟯) (minpoly F γ) = 0,
      { rw [aeval_alg_hom_apply, this, alg_hom.map_zero] },
      apply (algebra_map F⟮α, β⟯ (SBR F E)).injective,
      rw [ring_hom.map_zero, is_scalar_tower.algebra_map_aeval],
      exact minpoly.aeval F γ,
    end (minpoly.monic (SBR_is_integral γ)),
  rw [P, key],
  haveI : fact (splits (algebra_map F (p * q).splitting_field) (minpoly F (f ⟨γ, hγ⟩))) :=
    normal.splits (splitting_field.normal _) _,
  haveI hpq1 : is_solvable ((p * q).splitting_field ≃ₐ[F] (p * q).splitting_field) :=
    gal_mul_solvable hα hβ,
  exact solvable_of_surjective (alg_equiv.restrict_normal_hom_surjective (p * q).splitting_field),
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
  rw [P, minpoly.zero],
  exact is_solvable_of_top_eq_bot _ (top_eq_bot_of_top_eq_bot ((is_splitting_field.splits_iff
    (X : polynomial F).splitting_field X).mp (splits_X (ring_hom.id F)))),
end

theorem solvable_gal_of_SBR (α : SBR F E) :
  is_solvable (minpoly F α).gal :=
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
