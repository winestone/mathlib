import group_theory.perm.cycles

open subgroup equiv equiv.perm

lemma closure_is_cycle {α : Type*} [fintype α] [linear_order α] :
closure ({σ | is_cycle σ} : set (perm α)) = ⊤ :=
begin
  rw eq_top_iff,
  intros x hx,
  obtain ⟨h1, h2, h3⟩ := subtype.mem (cycle_factors x),
  rw ← h1,
  exact list_prod_mem _ (λ y hy, subset_closure (h2 y hy)),
end

lemma closure_is_swap {α : Type*} [fintype α] [linear_order α] :
closure ({σ | is_swap σ} : set (perm α)) = ⊤ :=
begin
  rw eq_top_iff,
  intros x hx,
  obtain ⟨h1, h2⟩ := subtype.mem (swap_factors x),
  rw ← h1,
  exact list_prod_mem _ (λ y hy, subset_closure (h2 y hy)),
end

lemma closure_cycle_adjacent_swap {α : Type*} [fintype α] [linear_order α] {σ : perm α}
  (h1 : is_cycle σ) (h2 : σ.support = ⊤) (x : α) :
closure ({σ, swap x (σ x)} : set (perm α)) = ⊤ :=
begin
  let H := closure ({σ, swap x (σ x)} : set (perm α)),
  have h3 : σ ∈ H := subset_closure (set.mem_insert σ _),
  have h4 : swap x (σ x) ∈ H := subset_closure (set.mem_insert_of_mem _ (set.mem_singleton _)),
  have step1 : ∀ (n : ℕ), swap ((σ^n) x) ((σ^(n+1)) x) ∈ H,
  { intro n,
    induction n with n ih,
    { exact subset_closure (set.mem_insert_of_mem _ (set.mem_singleton _)) },
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
  have step3 : ∀ (y : α), swap x y ∈ H,
  { intro y,
    have hx : x ∈ (⊤ : finset α) := finset.mem_univ x,
    rw [←h2, mem_support] at hx,
    have hy : y ∈ (⊤ : finset α) := finset.mem_univ y,
    rw [←h2, mem_support] at hy,
    cases exists_pow_eq_of_is_cycle h1 hx hy with n hn,
    rw ← hn,
    exact step2 n },
  have step4 : ∀ (y z : α), swap y z ∈ H,
  { intros y z,
    by_cases h5 : z = x,
    { rw [h5, swap_comm], exact step3 y },
    by_cases h6 : z = y,
    { rw [h6, swap_self], exact H.one_mem },
    rw [←swap_mul_swap_mul_swap h5 h6, swap_comm z x],
    exact H.mul_mem (H.mul_mem (step3 y) (step3 z)) (step3 y) },
  rw [eq_top_iff ,←closure_is_swap, closure_le],
  rintros τ ⟨y, z, h5, h6⟩,
  rw h6,
  exact step4 y z,
end

lemma closure_cycle_coprime_swap {α : Type*} [fintype α] [linear_order α] {n : ℕ} {σ : perm α}
  (h0 : nat.coprime n (fintype.card α)) (h1 : is_cycle σ) (h2 : σ.support = ⊤) (x : α) :
closure ({σ, swap x ((σ^n) x)} : set (perm α)) = ⊤ :=
begin
  have h2' : (σ^n).support = ⊤,
  { sorry },
  have h1' : is_cycle (σ^n),
  { sorry },
  rw [eq_top_iff, ←closure_cycle_adjacent_swap h1' h2' x, closure_le, set.insert_subset],
  exact ⟨subgroup.pow_mem (closure _) (subset_closure (set.mem_insert σ _)) n,
    set.singleton_subset_iff.mpr (subset_closure (set.mem_insert_of_mem _ (set.mem_singleton _)))⟩,
end
