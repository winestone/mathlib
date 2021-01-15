/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import field_theory.minimal_polynomial
import field_theory.splitting_field
import field_theory.tower
import ring_theory.power_basis

/-!
# Normal field extensions

In this file we define normal field extensions and prove that for a finite extension, being normal
is the same as being a splitting field (TODO).

## Main Definitions

- `normal F K` where `K` is a field extension of `F`.
-/

noncomputable theory
open_locale classical
open polynomial

universes u v

variables (F : Type u) (K : Type v) [field F] [field K] [algebra F K]

/-- Typeclass for normal field extension: `K` is a normal extension of `F` iff the minimal
polynomial of every element `x` in `K` splits in `K`, i.e. every conjugate of `x` is in `K`. -/
@[class] def normal : Prop :=
∀ x : K, ∃ H : is_integral F x, splits (algebra_map F K) (minimal_polynomial H)

instance normal_self : normal F F :=
λ x, ⟨is_integral_algebra_map, by { rw minimal_polynomial.eq_X_sub_C, exact splits_X_sub_C _ }⟩

theorem normal.is_integral [h : normal F K] (x : K) : is_integral F x := (h x).fst

theorem normal.splits [h : normal F K] (x : K) :
  splits (algebra_map F K) (minimal_polynomial $ normal.is_integral F K x) := (h x).snd

theorem normal.exists_is_splitting_field [normal F K] [finite_dimensional F K] :
  ∃ p : polynomial F, is_splitting_field F K p :=
begin
  obtain ⟨s, hs⟩ := finite_dimensional.exists_is_basis_finset F K,
  refine ⟨s.prod $ λ x, minimal_polynomial $ normal.is_integral F K x,
    splits_prod _ $ λ x hx, normal.splits F K x,
    subalgebra.to_submodule_injective _⟩,
  rw [algebra.coe_top, eq_top_iff, ← hs.2, submodule.span_le, set.range_subset_iff],
  refine λ x, algebra.subset_adjoin (multiset.mem_to_finset.mpr $
    (mem_roots $ mt (map_eq_zero $ algebra_map F K).1 $
    finset.prod_ne_zero_iff.2 $ λ x hx, _).2 _),
  { exact minimal_polynomial.ne_zero _ },
  rw [is_root.def, eval_map, ← aeval_def, alg_hom.map_prod],
  exact finset.prod_eq_zero x.2 (minimal_polynomial.aeval _)
end

section normal_tower

variables (E : Type*) [field E] [algebra F E] [algebra K E] [is_scalar_tower F K E]

lemma normal.tower_top_of_normal (h : normal F E) : normal K E :=
begin
  intros x,
  cases h x with hx hhx,
  rw is_scalar_tower.algebra_map_eq F K E at hhx,
  exact ⟨is_integral_of_is_scalar_tower x hx, polynomial.splits_of_splits_of_dvd (algebra_map K E)
    (polynomial.map_ne_zero (minimal_polynomial.ne_zero hx))
    ((polynomial.splits_map_iff (algebra_map F K) (algebra_map K E)).mpr hhx)
    (minimal_polynomial.dvd_map_of_is_scalar_tower K hx)⟩,
end

variables {F} {E} {E' : Type*} [field E'] [algebra F E']

lemma normal.of_alg_equiv [h : normal F E] (f : E ≃ₐ[F] E') : normal F E' :=
begin
  intro x,
  cases h (f.symm x) with hx hhx,
  have H := is_integral_alg_hom f.to_alg_hom hx,
  rw [alg_equiv.to_alg_hom_eq_coe, alg_equiv.coe_alg_hom, alg_equiv.apply_symm_apply] at H,
  use H,
  apply polynomial.splits_of_splits_of_dvd (algebra_map F E') (minimal_polynomial.ne_zero hx),
  { rw ← alg_hom.comp_algebra_map f.to_alg_hom,
    exact polynomial.splits_comp_of_splits (algebra_map F E) f.to_alg_hom.to_ring_hom hhx },
  { apply minimal_polynomial.dvd H,
    rw ← add_equiv.map_eq_zero_iff f.symm.to_add_equiv,
    exact eq.trans (polynomial.aeval_alg_hom_apply f.symm.to_alg_hom x
      (minimal_polynomial hx)).symm (minimal_polynomial.aeval hx) },
end

lemma alg_equiv.transfer_normal (f : E ≃ₐ[F] E') : normal F E ↔ normal F E' :=
⟨λ h, by exactI normal.of_alg_equiv f, λ h, by exactI normal.of_alg_equiv f.symm⟩

lemma nat_lemma {a b c : ℕ} (h1 : a * b = c) (h2 : c ≤ a) (h3 : 0 < c) : b = 1 := sorry

/-https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Slow.20instance/near/222791565-/
local attribute [irreducible] ideal.quotient.comm_ring
/- Move to normal.lean -/
theorem big_theorem {F E : Type*} [field F] [field E] [algebra F E] {p : polynomial F}
  [is_splitting_field F E p] : normal F E :=
begin
  intro x,
  haveI hFE : finite_dimensional F E := is_splitting_field.finite_dimensional E p,
  have H : is_integral F x := is_integral_of_noetherian hFE x,
  refine ⟨H, or.inr _⟩,
  rintros q q_irred ⟨r, hr⟩,
  let D := adjoin_root q,
  let pbED := adjoin_root.power_basis q_irred.ne_zero,
  haveI : finite_dimensional E D := power_basis.finite_dimensional pbED,
  have findimED : finite_dimensional.findim E D = q.nat_degree := power_basis.findim pbED,
  letI : algebra F D := ring_hom.to_algebra ((algebra_map E D).comp (algebra_map F E)),
  haveI : is_scalar_tower F E D := is_scalar_tower.of_algebra_map_eq (λ _, rfl),
  haveI : finite_dimensional F D := finite_dimensional.trans F E D,
  suffices : nonempty (D →ₐ[F] E),
  { cases this with ϕ,
    rw [←with_bot.coe_one, degree_eq_iff_nat_degree_eq q_irred.ne_zero, ←findimED],
    exact nat_lemma (finite_dimensional.findim_mul_findim F E D)
      (linear_map.findim_le_findim_of_injective (show function.injective ϕ.to_linear_map,
        from ϕ.to_ring_hom.injective)) finite_dimensional.findim_pos },
  let C := adjoin_root (minimal_polynomial H),
  letI : algebra C D := ring_hom.to_algebra (adjoin_root.lift
    (algebra_map F D) (adjoin_root.root q) (by rw [is_scalar_tower.algebra_map_eq F E D,
      ←eval₂_map, hr, adjoin_root.algebra_map_eq, eval₂_mul, adjoin_root.eval₂_root, zero_mul])),
  letI : algebra C E := ring_hom.to_algebra
    (adjoin_root.lift (algebra_map F E) x (minimal_polynomial.aeval H)),
  haveI : is_scalar_tower F C D :=
    is_scalar_tower.of_algebra_map_eq (λ x, adjoin_root.lift_of.symm),
  haveI : is_scalar_tower F C E :=
    is_scalar_tower.of_algebra_map_eq (λ x, adjoin_root.lift_of.symm),
  suffices : nonempty (D →ₐ[C] E),
  { exact nonempty.map (is_scalar_tower.restrict_base F) this },
  let S : finset E := sorry,
  have key : adjoin C S = ⊤,
  { sorry },
  sorry,
end

end normal_tower
