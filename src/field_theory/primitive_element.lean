/-
Copyright (c) 2020 Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz
-/

import field_theory.adjoin
import field_theory.separable

/-!
# Primitive Element Theorem

In this file we prove the primitive element theorem.

## Main results

- `exists_primitive_element`: a finite separable extension `E / F` has a primitive element, i.e.
  there is an `α : E` such that `F⟮α⟯ = (⊤ : subalgebra F E)`.

## Implementation notes

In declaration names, `primitive_element` abbreviates `adjoin_simple_eq_top`:
it stands for the statement `F⟮α⟯ = (⊤ : subalgebra F E)`. We did not add an extra
declaration `is_primitive_element F α := F⟮α⟯ = (⊤ : subalgebra F E)` because this
requires more unfolding without much obvious benefit.

## Tags

primitive element, separable field extension, separable extension, intermediate field, adjoin,
exists_adjoin_simple_eq_top

-/

noncomputable theory
open_locale classical

open finite_dimensional polynomial intermediate_field

namespace field

section primitive_element_finite
variables (F : Type*) [field F] (E : Type*) [field E] [algebra F E]

/-! ### Primitive element theorem for finite fields -/

/-- Primitive element theorem assuming E is finite. -/
lemma exists_primitive_element_of_fintype_top [fintype E] : ∃ α : E, F⟮α⟯ = ⊤ :=
begin
  obtain ⟨α, hα⟩ := is_cyclic.exists_generator (units E),
  use α,
  apply eq_top_iff.mpr,
  rintros x -,
  by_cases hx : x = 0,
  { rw hx,
    exact F⟮α.val⟯.zero_mem },
  { obtain ⟨n, hn⟩ := set.mem_range.mp (hα (units.mk0 x hx)),
    rw (show x = α^n, by { norm_cast, rw [hn, units.coe_mk0] }),
    exact pow_mem F⟮↑α⟯ (mem_adjoin_simple_self F ↑α) n, },
end

/-- Primitive element theorem for finite dimensional extension of a finite field. -/
theorem exists_primitive_element_of_fintype_bot [fintype F] [finite_dimensional F E] :
  ∃ α : E, F⟮α⟯ = ⊤ :=
begin
  haveI : fintype E := fintype_of_fintype F E,
  exact exists_primitive_element_of_fintype_top F E,
end

end primitive_element_finite

/-! ### Primitive element theorem for infinite fields -/

section primitive_element_inf

variables {F : Type*} [field F] [infinite F] {E : Type*} [field E] (ϕ : F →+* E) (α β : E)

lemma primitive_element_inf_aux_exists_c (f g : polynomial F) :
  ∃ c : F, ∀ (α' ∈ (f.map ϕ).roots) (β' ∈ (g.map ϕ).roots), -(α' - α)/(β' - β) ≠ ϕ c :=
begin
  let sf := (f.map ϕ).roots,
  let sg := (g.map ϕ).roots,
  let s := (sf.bind (λ α', sg.map (λ β', -(α' - α) / (β' - β)))).to_finset,
  let s' := s.preimage ϕ (λ x hx y hy h, ϕ.injective h),
  obtain ⟨c, hc⟩ := infinite.exists_not_mem_finset s',
  simp_rw [finset.mem_preimage, multiset.mem_to_finset, multiset.mem_bind, multiset.mem_map] at hc,
  push_neg at hc,
  exact ⟨c, hc⟩,
end

variables [algebra F E]

-- This is the heart of the proof of the primitive element theorem. It shows that if `F` is
-- infinite and `α` and `β` are separable over `F` then `F⟮α, β⟯` is generated by a single element.
lemma primitive_element_inf_aux (F_sep : is_separable F E) :
  ∃ γ : E, F⟮α, β⟯ = F⟮γ⟯ :=
begin
  have hα := F_sep.is_integral α,
  have hβ := F_sep.is_integral β,
  let f := minpoly F α,
  let g := minpoly F β,
  let ιFE := algebra_map F E,
  let ιEE' := algebra_map E (splitting_field (g.map ιFE)),
  obtain ⟨c, hc⟩ := primitive_element_inf_aux_exists_c (ιEE'.comp ιFE) (ιEE' α) (ιEE' β) f g,
  let γ := α + c • β,
  suffices β_in_Fγ : β ∈ F⟮γ⟯,
  { use γ,
    apply le_antisymm,
    { rw adjoin_le_iff,
      have α_in_Fγ : α ∈ F⟮γ⟯,
      { rw ← add_sub_cancel α (c • β),
        exact F⟮γ⟯.sub_mem (mem_adjoin_simple_self F γ) (F⟮γ⟯.to_subalgebra.smul_mem β_in_Fγ c)},
      exact λ x hx, by cases hx; cases hx; cases hx; assumption },
      { rw adjoin_le_iff,
        change {γ} ⊆ _,
        rw set.singleton_subset_iff,
        have α_in_Fαβ : α ∈ F⟮α, β⟯ := subset_adjoin F {α, β} (set.mem_insert α {β}),
        have β_in_Fαβ : β ∈ F⟮α, β⟯ := subset_adjoin F {α, β} (set.mem_insert_of_mem α rfl),
        exact F⟮α,β⟯.add_mem α_in_Fαβ (F⟮α, β⟯.smul_mem β_in_Fαβ) } },
  let p := euclidean_domain.gcd ((f.map (algebra_map F F⟮γ⟯)).comp
    (C (adjoin_simple.gen F γ) - (C ↑c * X))) (g.map (algebra_map F F⟮γ⟯)),
  let h := euclidean_domain.gcd ((f.map ιFE).comp (C γ - (C (ιFE c) * X))) (g.map ιFE),
  have map_g_ne_zero : g.map ιFE ≠ 0 := map_ne_zero (minpoly.ne_zero hβ),
  have h_ne_zero : h ≠ 0 :=  mt euclidean_domain.gcd_eq_zero_iff.mp
    (not_and.mpr (λ _, map_g_ne_zero)),
  suffices p_linear : p.map (algebra_map F⟮γ⟯ E) = (C h.leading_coeff) * (X - C β),
  { have finale : β = algebra_map F⟮γ⟯ E (-p.coeff 0 / p.coeff 1),
    { rw [ring_hom.map_div, ring_hom.map_neg, ←coeff_map, ←coeff_map, p_linear],
      simp [mul_sub, coeff_C, mul_div_cancel_left β (mt leading_coeff_eq_zero.mp h_ne_zero)] },
    rw finale,
    exact subtype.mem (-p.coeff 0 / p.coeff 1) },
  have h_sep : h.separable := separable_gcd_right _ (separable.map (F_sep.separable β)),
  have h_root : h.eval β = 0,
  { apply eval_gcd_eq_zero,
    { rw [eval_comp, eval_sub, eval_mul, eval_C, eval_C, eval_X, eval_map, ←aeval_def,
          ←algebra.smul_def, add_sub_cancel, minpoly.aeval] },
    { rw [eval_map, ←aeval_def, minpoly.aeval] } },
  have h_splits : splits ιEE' h := splits_of_splits_gcd_right ιEE' map_g_ne_zero
    (splitting_field.splits _),
  have h_roots : ∀ x ∈ (h.map ιEE').roots, x = ιEE' β,
  { intros x hx,
    rw mem_roots_map h_ne_zero at hx,
    specialize hc ((ιEE' γ) - (ιEE' (ιFE c)) * x) (begin
      have f_root := root_left_of_root_gcd hx,
      rw [eval₂_comp, eval₂_sub, eval₂_mul,eval₂_C, eval₂_C, eval₂_X, eval₂_map] at f_root,
      exact (mem_roots_map (minpoly.ne_zero hα)).mpr f_root,
    end),
    specialize hc x (begin
      rw [mem_roots_map (minpoly.ne_zero hβ), ←eval₂_map],
      exact root_right_of_root_gcd hx,
    end),
    by_contradiction a,
    apply hc,
    apply (div_eq_iff (sub_ne_zero.mpr a)).mpr,
    simp only [algebra.smul_def, ring_hom.map_add, ring_hom.map_mul, ring_hom.comp_apply],
    ring },
  rw ← eq_X_sub_C_of_separable_of_root_eq h_ne_zero h_sep h_root h_splits h_roots,
  transitivity euclidean_domain.gcd (_ : polynomial E) (_ : polynomial E),
  { dsimp only [p],
    convert (gcd_map (algebra_map F⟮γ⟯ E)).symm },
  { simpa [map_comp, map_map, ←is_scalar_tower.algebra_map_eq, h] },
end

end primitive_element_inf

variables {F : Type*} [field F] {E : Type*} [field E] [algebra F E]

/-- Primitive element theorem: a finite separable field extension `E` of `F` has a
  primitive element, i.e. there is an `α ∈ E` such that `F⟮α⟯ = (⊤ : subalgebra F E)`.-/
theorem exists_primitive_element [finite_dimensional F E] (F_sep : is_separable F E) :
  ∃ α : E, F⟮α⟯ = ⊤ :=
begin
  by_cases F_finite : nonempty (fintype F),
  { exact nonempty.elim F_finite
    (λ h, by haveI := h; exact exists_primitive_element_of_fintype_bot F E) },
  { let P : intermediate_field F E → Prop := λ K, ∃ α : E, F⟮α⟯ = K,
    have base : P ⊥ := ⟨0, adjoin_zero⟩,
    have ih : ∀ (K : intermediate_field F E) (x : E), P K → P ↑K⟮x⟯,
    { intros K β hK,
      cases hK with α hK,
      rw [←hK, adjoin_simple_adjoin_simple],
      haveI : infinite F := not_nonempty_fintype.mp F_finite,
      cases primitive_element_inf_aux α β F_sep with γ hγ,
      exact ⟨γ, hγ.symm⟩ },
    exact induction_on_adjoin P base ih ⊤ },
end

end field
