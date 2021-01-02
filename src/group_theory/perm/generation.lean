import group_theory.perm.cycles
import data.zmod.basic

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

lemma closure_cycle_adjacent_swap {α : Type*} [fintype α] [linear_order α] {σ : perm α}
  (h1 : is_cycle σ) (h2 : σ.support = ⊤) (x : α) :
subgroup.closure ({σ, swap x (σ x)} : set (perm α)) = ⊤ :=
begin
  let H := subgroup.closure ({σ, swap x (σ x)} : set (perm α)),
  have h3 : σ ∈ H := subgroup.subset_closure (set.mem_insert σ _),
  have h4 : swap x (σ x) ∈ H :=
    subgroup.subset_closure (set.mem_insert_of_mem _ (set.mem_singleton _)),
  have step1 : ∀ (n : ℕ), swap ((σ^n) x) ((σ^(n+1)) x) ∈ H,
  { intro n,
    induction n with n ih,
    { exact subgroup.subset_closure (set.mem_insert_of_mem _ (set.mem_singleton _)) },
    { convert H.mul_mem (H.mul_mem h3 ih) (H.inv_mem h3),
      rw [mul_swap_eq_swap_mul, mul_inv_cancel_right], refl } },
  have step2 : ∀ (n : ℕ), swap x ((σ^n) x) ∈ H,
  { intro n,
    induction n with n ih,
    { convert H.one_mem,
      exact swap_self x },
    { by_cases h5 : x = (σ^n) x,
      { rw [pow_succ, mul_apply, ←h5], exact h4 },
      by_cases h6 : x = (σ^(n+1)) x,
      { rw [←h6, swap_self], exact H.one_mem },
      rw [swap_comm, ←swap_mul_swap_mul_swap h5 h6],
      exact H.mul_mem (H.mul_mem (step1 n) ih) (step1 n) } },
  have step3 : ∀ (n : ℤ), swap x ((σ^n) x) ∈ H,
  { intro n,
    have := int.mod_nonneg n (mt int.coe_nat_eq_zero.mp (ne_of_gt (order_of_pos σ))),
    rw [←int.mod_add_div n (order_of σ), gpow_add, gpow_mul, gpow_coe_nat, pow_order_of_eq_one,
        one_gpow, mul_one, ←int.to_nat_of_nonneg this, gpow_coe_nat],
    exact step2 _ },
  have step4 : ∀ (y : α), swap x y ∈ H,
  { intro y,
    have hx : x ∈ (⊤ : finset α) := finset.mem_univ x,
    rw [←h2, mem_support] at hx,
    have hy : y ∈ (⊤ : finset α) := finset.mem_univ y,
    rw [←h2, mem_support] at hy,
    cases exists_gpow_eq_of_is_cycle h1 hx hy with n hn,
    rw ← hn,
    exact step3 n },
  have step5 : ∀ (y z : α), swap y z ∈ H,
  { intros y z,
    by_cases h5 : z = x,
    { rw [h5, swap_comm], exact step4 y },
    by_cases h6 : z = y,
    { rw [h6, swap_self], exact H.one_mem },
    rw [←swap_mul_swap_mul_swap h5 h6, swap_comm z x],
    exact H.mul_mem (H.mul_mem (step4 y) (step4 z)) (step4 y) },
  rw [eq_top_iff ,←closure_is_swap, subgroup.closure_le],
  rintros τ ⟨y, z, h5, h6⟩,
  rw h6,
  exact step5 y z,
end
