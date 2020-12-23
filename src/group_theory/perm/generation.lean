import group_theory.perm.cycles

open equiv
open equiv.perm

lemma closure_is_cycle {α : Type*} [fintype α] [linear_order α] :
  subgroup.closure ({σ | is_cycle σ} : set (perm α)) = ⊤ :=
begin
  rw eq_top_iff,
  intros x hx,
  obtain ⟨h1, h2, h3⟩ := subtype.mem (cycle_factors x),
  rw ← h1,
  exact subgroup.list_prod_mem _ (λ y hy, subgroup.subset_closure (h2 y hy)),
end

lemma closure_is_swap {α : Type*} [fintype α] [linear_order α] :
  subgroup.closure ({σ | is_swap σ} : set (perm α)) = ⊤ :=
begin
  rw eq_top_iff,
  intros x hx,
  obtain ⟨h1, h2⟩ := subtype.mem (swap_factors x),
  rw ← h1,
  exact subgroup.list_prod_mem _ (λ y hy, subgroup.subset_closure (h2 y hy)),
end
