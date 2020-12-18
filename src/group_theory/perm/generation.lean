import group_theory.perm.cycles

open equiv
open equiv.perm

lemma lem1 {α : Type*} [fintype α] :
  subgroup.closure ({σ | is_cycle σ} : set (perm α)) = ⊤ :=
begin
  sorry
end

lemma lem2 {α : Type*} [fintype α] [decidable_eq α] :
  subgroup.closure ({σ | is_swap σ} : set (perm α)) = ⊤ :=
begin
  sorry
end
