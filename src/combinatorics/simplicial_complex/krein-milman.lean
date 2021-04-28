import combinatorics.simplicial_complex.exposed
import order.order_dual

open_locale classical affine big_operators
open set
--TODO: Generalise to LCTVS
variables {E : Type*} [normed_group E] [normed_space ℝ E] {x : E} {A B : set E}

namespace affine

--being proven in another branch, so don't need to unsorry it here
theorem geometric_hahn_banach_compact_closed {A B : set E}
  (hA₁ : convex A) (hA₂ : is_compact A)
  (hB₁ : convex B) (hB₂ : is_closed B)
  (disj : disjoint A B) :
  ∃ (f : E →L[ℝ] ℝ) (s t : ℝ), s < t ∧ (∀ b ∈ B, f b < s) ∧ (∀ a ∈ A, t < f a) :=
sorry

theorem geometric_hahn_banach_closed_point {A : set E}
  (hA₁ : convex A) (hA₂ : is_closed A)
  (disj : x ∉ A) :
  ∃ (f : E →L[ℝ] ℝ) (s : ℝ), (∀ a ∈ A, f a < s) ∧ s < f x := sorry

theorem geometric_hahn_banach_point_point {x y : E} (hxy : x ≠ y) :
  ∃ (f : E →L[ℝ] ℝ), f x < f y :=
sorry

--to move to mathlib
theorem zorn.subset_reverse {α : Type*} (S : set (set α))
  (h : ∀c ⊆ S, zorn.chain (⊆) c → ∃lb ∈ S, ∀ s ∈ c, lb ⊆ s) :
  ∃ m ∈ S, ∀ a ∈ S, a ⊆ m → a = m :=
begin
  let rev : S → S → Prop := λ X Y, Y.1 ⊆ X.1,
  have hS : ∀ (c : set S), zorn.chain rev c → ∃ ub, ∀ a ∈ c, rev a ub,
  { intros c hc,
    obtain ⟨t, ht₁, ht₂⟩ := h (coe '' c) (by simp)
      (by { rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ ne,
            apply (hc _ hx _ hy (λ t, ne (congr_arg coe t))).symm }),
    exact ⟨⟨_, ht₁⟩, λ a ha, ht₂ a ⟨_, ha, rfl⟩⟩ },
  obtain ⟨m, hm₁⟩ := zorn.exists_maximal_of_chains_bounded hS _,
  { refine ⟨m, m.prop, λ a ha ha₂, set.subset.antisymm ha₂ (hm₁ ⟨a, ha⟩ ha₂)⟩ },
  intros x y z xy yz,
  apply set.subset.trans yz xy
end

/--
The Krein-Milman lemma
-/
lemma has_extreme_point_of_convex_of_compact_of_nonempty (hAnemp : A.nonempty)
  (hAcomp : is_compact A) (hAconv : convex A) :
  A.extreme_points.nonempty :=
begin
  let S : set (set E) := {B | B.nonempty ∧ is_closed B ∧ is_extreme A B},
  suffices h : ∃ B ∈ S, ∀ C ∈ S, C ⊆ B → C = B,
  { obtain ⟨B, ⟨hBnemp, hBclos, hAB⟩, hBmin⟩ := h,
    obtain ⟨x, hxB⟩ := hBnemp,
    refine ⟨x, extreme_point_iff_extreme_singleton.2 _⟩,
    suffices h : B = {x},
    { rw ←h,
      exact hAB },
    refine eq_singleton_iff_unique_mem.2 ⟨hxB, λ y hyB, _⟩,
    by_contra hyx,
    obtain ⟨l, hl⟩ := geometric_hahn_banach_point_point hyx,
    obtain ⟨z, hzB, hz⟩ := is_compact.exists_forall_ge (compact_of_is_closed_subset hAcomp hBclos
      hAB.1) ⟨x, hxB⟩ (continuous.continuous_on l.continuous),
    rw ←hBmin {z ∈ B | ∀ w ∈ B, l w ≤ l z} ⟨⟨z, hzB, hz⟩, closed_of_exposed hBclos ⟨l, rfl⟩,
      hAB.trans (is_exposed.is_extreme ⟨l, rfl⟩)⟩ (λ z hz, hz.1) at hyB,
    exact not_le.2 hl (hyB.2 x hxB) },
  apply zorn.subset_reverse,
  rintro F hFS hF,
  cases F.eq_empty_or_nonempty with hFemp hFnemp,
  { rw hFemp,
    refine ⟨A, ⟨hAnemp, is_compact.is_closed hAcomp, is_extreme.refl _⟩, λ B hB, _⟩,
    exfalso,
    exact hB },
  refine ⟨⋂₀ F, ⟨_, is_closed_sInter (λ B hB, (hFS hB).2.1), is_extreme.sInter hFnemp
    (λ B hB, (hFS hB).2.2)⟩, λ B hB, sInter_subset_of_mem hB⟩,
  rw sInter_eq_Inter,
  apply is_compact.nonempty_Inter_of_directed_nonempty_compact_closed _,
  { rintro B C,
    cases zorn.chain.total_of_refl hF (subtype.mem _) (subtype.mem _) with hBC hCB,
    exacts [⟨B, subset.refl _, hBC⟩, ⟨C, hCB, subset.refl _⟩] },
  exacts [λ B, (hFS (subtype.mem _)).1, λ B, compact_of_is_closed_subset hAcomp
    (hFS (subtype.mem _)).2.1 (hFS (subtype.mem _)).2.2.1, λ B, (hFS (subtype.mem _)).2.1,
   nonempty_subtype.2 hFnemp],
end

/--
The Krein-Milman theorem
-/
lemma eq_closure_convex_hull_extreme_points_of_compact_of_convex (hAcomp : is_compact A)
  (hAconv : convex A) :
  A = closure (convex_hull A.extreme_points) :=
begin
  let B := closure (convex_hull A.extreme_points),
  have hBA : B ⊆ A :=
    closure_minimal (convex_hull_min (λ x hx, hx.1) hAconv) (is_compact.is_closed hAcomp),
  refine subset.antisymm _ hBA,
  by_contra hAB,
  have hABdiff : (A \ B).nonempty := nonempty_diff.2 hAB,
  obtain ⟨x, hxA, hxB⟩ := id hABdiff,
  obtain ⟨l, s, hls, hsx⟩ := geometric_hahn_banach_closed_point
    (convex.closure (convex_convex_hull _)) is_closed_closure hxB,
  let C := {y ∈ A | ∀ z ∈ A, l z ≤ l y},
  have hCexp : is_exposed_set A C := ⟨l, rfl⟩,
  obtain ⟨y, hyC⟩ := has_extreme_point_of_convex_of_compact_of_nonempty
    begin
      obtain ⟨z, hzA, hz⟩ := is_compact.exists_forall_ge hAcomp ⟨x, hxA⟩
        (continuous.continuous_on l.continuous),
      exact ⟨z, hzA, hz⟩,
    end
    (compact_of_exposed hAcomp hCexp) (convex_of_exposed hAconv hCexp),
  linarith [hls _ (subset_closure (subset_convex_hull _
    ((extreme_of_exposed hCexp).extreme_points_subset_extreme_points  hyC))),
    hyC.1.2 x hxA],
end

/--
Carathéodory's theorem, the extreme points way
-/
lemma eq_convex_hull_extreme_points_of_compact_of_convex [finite_dimensional ℝ E]
  (hAcomp : is_compact A) (hAconv : convex A) :
  A = convex_hull A.extreme_points :=
begin
  nth_rewrite_lhs 0 eq_closure_convex_hull_extreme_points_of_compact_of_convex hAcomp hAconv,
  rw closure_eq_iff_is_closed,
  sorry
  /-let B := convex_hull A.extreme_points,
  have hBA : B ⊆ A :=
    convex_hull_min (λ x hx, hx.1) hAconv,
  refine subset.antisymm _ hBA,
  by_contra hAB,
  have hABdiff : (A \ B).nonempty := nonempty_diff.2 hAB,
  obtain ⟨x, hxA, hxB⟩ := id hABdiff,
  sorry-/
end

end affine