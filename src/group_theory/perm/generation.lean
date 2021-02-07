import group_theory.perm.cycles
import group_theory.group_action.basic

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
  have step1 : ∀ (n : ℕ), swap ((σ ^ n) x) ((σ^(n+1)) x) ∈ H,
  { intro n,
    induction n with n ih,
    { exact subset_closure (set.mem_insert_of_mem _ (set.mem_singleton _)) },
    { convert H.mul_mem (H.mul_mem h3 ih) (H.inv_mem h3),
      rw [mul_swap_eq_swap_mul, mul_inv_cancel_right], refl } },
  have step2 : ∀ (n : ℕ), swap x ((σ ^ n) x) ∈ H,
  { intro n,
    induction n with n ih,
    { convert H.one_mem,
      exact swap_self x },
    { by_cases h5 : x = (σ ^ n) x,
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
    cases is_cycle.exists_pow_eq h1 hx hy with n hn,
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

lemma order_of_is_cycle {α : Type*} [fintype α] [decidable_eq α] {σ : perm α}
  (hσ : is_cycle σ) : order_of σ = σ.support.card :=
begin
  obtain ⟨x, hx, hσ⟩ := hσ,
  rw [order_eq_card_gpowers, support, ←fintype.card_coe],
  apply fintype.card_congr,
  refine equiv.of_bijective (λ τ, ⟨τ x, _⟩) ⟨_, _⟩,
  { obtain ⟨τ, n, rfl⟩ := τ,
    rw [finset.mem_coe, finset.mem_filter],
    exact ⟨finset.mem_univ _, λ h, hx ((σ ^ n).injective
      (by rwa [←mul_apply, mul_gpow_self, ←mul_self_gpow, mul_apply]))⟩ },
  { rintros ⟨a, m, rfl⟩ ⟨b, n, rfl⟩ h,
    ext y,
    change (σ ^ m) y = (σ ^ n) y,
    by_cases hy : σ y = y,
    { simp only [gpow_apply_eq_self_of_apply_eq_self hy] },
    { obtain ⟨i, rfl⟩ := hσ y hy,
      rw [←mul_apply, ←gpow_add, add_comm, gpow_add, mul_apply, (show (σ ^ m) x = (σ ^ n) x,
        from subtype.ext_iff.mp h), ←mul_apply, ←gpow_add, add_comm, gpow_add, mul_apply] } },
  { rintros ⟨y, hy⟩,
    rw [finset.mem_coe, finset.mem_filter] at hy,
    cases hσ y hy.2 with n h,
    exact ⟨⟨σ ^ n, n, rfl⟩, subtype.ext h⟩ },
end

lemma lem2 {G : Type*} [group G] [fintype G] [decidable_eq G] {n : ℕ} {g : G}
  (h0 : nat.coprime n (order_of g)) : ∃ m : ℤ, (g ^ n) ^ m = g :=
begin
  use n.gcd_a (order_of g),
  dsimp only [nat.coprime] at h0,
  conv { to_rhs, rw [←pow_one g, ←h0, ←gpow_coe_nat, nat.gcd_eq_gcd_ab, gpow_add, gpow_mul,
    gpow_mul, gpow_coe_nat, gpow_coe_nat, pow_order_of_eq_one, one_gpow, mul_one] },
end

lemma lem3 {G : Type*} [group G] [fintype G] [decidable_eq G] {n : ℕ} {g : G}
  (h0 : nat.coprime n (order_of g)) : ∃ m : ℕ, (g ^ n) ^ m = g :=
begin
  cases lem2 h0 with m hm,
  use (m % (order_of g)).to_nat,
  rwa [←pow_mul, mul_comm, pow_mul, ←gpow_coe_nat, ←gpow_coe_nat, int.to_nat_of_nonneg,
      ←gpow_eq_mod_order_of, ←gpow_mul, mul_comm, gpow_mul, gpow_coe_nat],
  exact int.mod_nonneg _ (int.coe_nat_ne_zero.mpr (ne_of_gt (order_of_pos g))),
end

lemma lem4 {α : Type*} [fintype α] [decidable_eq α] (σ : perm α) (n : ℤ) :
  (σ ^ n).support ≤ σ.support :=
λ x h1, finset.mem_filter.mpr ⟨finset.mem_univ x,
  λ h2, (finset.mem_filter.mp h1).2 (gpow_apply_eq_self_of_apply_eq_self h2 n)⟩

lemma is_cycle_of_is_cycle_pow {α : Type*} [fintype α] [decidable_eq α] {σ : perm α} {n : ℤ}
  (h1 : is_cycle (σ ^ n)) (h2 : σ.support.card ≤ (σ ^ n).support.card) : is_cycle σ :=
begin
  have key : ∀ x : α, (σ ^ n) x ≠ x ↔ σ x ≠ x,
  { simp only [←mem_support],
    exact finset.ext_iff.mp (finset.eq_of_subset_of_card_le (lem4 σ n) h2) },
  obtain ⟨x, hx1, hx2⟩ := h1,
  refine ⟨x, (key x).mp hx1, λ y hy, _⟩,
  cases (hx2 y ((key y).mpr hy)) with i _,
  exact ⟨n * i, by rwa gpow_mul⟩,
end

lemma support_pow_coprime {α : Type*} [fintype α] [decidable_eq α] {σ : perm α} {n : ℕ}
  (h : nat.coprime n (order_of σ)) : (σ ^ n).support = σ.support :=
begin
  cases lem3 h with m hm,
  exact le_antisymm (lem4 σ n) (le_trans (ge_of_eq (congr_arg support hm)) (lem4 (σ ^ n) m)),
end

lemma closure_cycle_coprime_swap {α : Type*} [fintype α] [linear_order α] {n : ℕ} {σ : perm α}
  (h0 : nat.coprime n (fintype.card α)) (h1 : is_cycle σ) (h2 : σ.support = finset.univ) (x : α) :
closure ({σ, swap x ((σ ^ n) x)} : set (perm α)) = ⊤ :=
begin
  rw [←finset.card_univ, ←h2, ←order_of_is_cycle h1] at h0,
  cases lem3 h0 with m hm,
  have h2' : (σ ^ n).support = ⊤ := eq.trans (support_pow_coprime h0) h2,
  have h1' : is_cycle ((σ ^ n) ^ (m : ℤ)) := by rwa ← hm at h1,
  replace h1' : is_cycle (σ ^ n) := is_cycle_of_is_cycle_pow h1'
    (finset.card_le_of_subset (le_trans (lem4 σ n) (ge_of_eq (congr_arg support hm)))),
  rw [eq_top_iff, ←closure_cycle_adjacent_swap h1' h2' x, closure_le, set.insert_subset],
  exact ⟨subgroup.pow_mem (closure _) (subset_closure (set.mem_insert σ _)) n,
    set.singleton_subset_iff.mpr (subset_closure (set.mem_insert_of_mem _ (set.mem_singleton _)))⟩,
end

lemma closure_prime_cycle_swap {α : Type*} [fintype α] [linear_order α] {n : ℕ} {σ τ : perm α}
  (h0 : (fintype.card α).prime) (h1 : is_cycle σ) (h2 : σ.support = finset.univ) (h3 : is_swap τ) :
closure ({σ, τ} : set (perm α)) = ⊤ :=
begin
  obtain ⟨x, y, h4, h5⟩ := h3,
  obtain ⟨i, hi⟩ := h1.exists_pow_eq (mem_support.mp
  ((finset.ext_iff.mp h2 x).mpr (finset.mem_univ x)))
    (mem_support.mp ((finset.ext_iff.mp h2 y).mpr (finset.mem_univ y))),
  rw [h5, ←hi],
  refine closure_cycle_coprime_swap (nat.coprime.symm
    ((nat.prime.coprime_iff_not_dvd h0).mpr (λ h, h4 _))) h1 h2 x,
  cases h with m hm,
  rwa [hm, pow_mul, ←finset.card_univ, ←h2, ←order_of_is_cycle h1,
    pow_order_of_eq_one, one_pow, one_apply] at hi,
end
