import group_theory.perm.cycles
import group_theory.group_action.basic
import group_theory.sylow

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
  have step1 : ∀ (n : ℕ), swap ((σ ^ n) x) ((σ ^ (n + 1)) x) ∈ H,
  { intro n,
    induction n with n ih,
    { exact subset_closure (set.mem_insert_of_mem _ (set.mem_singleton _)) },
    { rw [pow_succ, pow_succ, mul_apply, mul_apply, swap_apply_apply],
      exact H.mul_mem (H.mul_mem h3 ih) (H.inv_mem h3) } },
  have step2 : ∀ (n : ℕ), swap x ((σ ^ n) x) ∈ H,
  { intro n,
    induction n with n ih,
    { rw [pow_zero, one_apply, swap_self],
      exact H.one_mem },
    { by_cases h5 : x = (σ ^ n) x,
      { rwa [pow_succ, mul_apply, ←h5] },
      by_cases h6 : x = (σ ^ (n + 1)) x,
      { rw [←h6, swap_self],
        exact H.one_mem },
      rw [swap_comm, ←swap_mul_swap_mul_swap h5 h6],
      exact H.mul_mem (H.mul_mem (step1 n) ih) (step1 n) } },
  have step3 : ∀ (y : α), swap x y ∈ H,
  { intro y,
    have hx : x ∈ (⊤ : finset α) := finset.mem_univ x,
    have hy : y ∈ (⊤ : finset α) := finset.mem_univ y,
    rw [←h2, mem_support] at *,
    obtain ⟨n, rfl⟩ := is_cycle.exists_pow_eq h1 hx hy,
    exact step2 n },
  have step4 : ∀ (y z : α), swap y z ∈ H,
  { intros y z,
    by_cases h5 : z = x,
    { rw [h5, swap_comm],
      exact step3 y },
    by_cases h6 : z = y,
    { rw [h6, swap_self],
      exact H.one_mem },
    rw [←swap_mul_swap_mul_swap h5 h6, swap_comm z x],
    exact H.mul_mem (H.mul_mem (step3 y) (step3 z)) (step3 y) },
  rw [eq_top_iff, ←closure_is_swap, closure_le],
  rintros τ ⟨y, z, -, rfl⟩,
  exact step4 y z,
end

lemma support_pow_coprime {α : Type*} [fintype α] [decidable_eq α] {σ : perm α} {n : ℕ}
  (h : nat.coprime n (order_of σ)) : (σ ^ n).support = σ.support :=
begin
  cases exists_gpow_eq_self_of_coprime h with m hm,
  exact le_antisymm (support_pow_le σ n)
    (le_trans (ge_of_eq (congr_arg support hm)) (support_pow_le (σ ^ n) m)),
end

lemma closure_cycle_coprime_swap {α : Type*} [fintype α] [linear_order α] {n : ℕ} {σ : perm α}
  (h0 : nat.coprime n (fintype.card α)) (h1 : is_cycle σ) (h2 : σ.support = finset.univ) (x : α) :
closure ({σ, swap x ((σ ^ n) x)} : set (perm α)) = ⊤ :=
begin
  rw [←finset.card_univ, ←h2, ←order_of_is_cycle h1] at h0,
  cases exists_gpow_eq_self_of_coprime h0 with m hm,
  have h2' : (σ ^ n).support = ⊤ := eq.trans (support_pow_coprime h0) h2,
  have h1' : is_cycle ((σ ^ n) ^ (m : ℤ)) := by rwa ← hm at h1,
  replace h1' : is_cycle (σ ^ n) := is_cycle_of_is_cycle_pow h1'
    (finset.card_le_of_subset (le_trans (support_pow_le σ n) (ge_of_eq (congr_arg support hm)))),
  rw [eq_top_iff, ←closure_cycle_adjacent_swap h1' h2' x, closure_le, set.insert_subset],
  exact ⟨subgroup.pow_mem (closure _) (subset_closure (set.mem_insert σ _)) n,
    set.singleton_subset_iff.mpr (subset_closure (set.mem_insert_of_mem _ (set.mem_singleton _)))⟩,
end

lemma closure_prime_cycle_swap {α : Type*} [fintype α] [linear_order α] {σ τ : perm α}
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

lemma lem3 {α : Type*} [fintype α] [linear_order α] {σ : perm α}
  (h0 : (order_of σ).prime) (h1 : order_of σ < 2 * fintype.card α) :
  is_cycle σ :=
begin
  obtain ⟨s, h2, h3⟩ := cycle_factors σ,
  sorry,
end

example {n : ℕ} (hn : 0 < n) (hn' : 1 < 2) : n < 2 * n := (lt_mul_iff_one_lt_left hn).mpr hn'

lemma lem4 {α : Type*} [fintype α] [linear_order α] {σ : perm α}
  (h0 : (fintype.card α).prime) (h1 : order_of σ = fintype.card α) :
  is_cycle σ :=
begin
  have key := lem3,
  rw h1 at key,
  exact key h0 ((lt_mul_iff_one_lt_left (nat.prime.pos h0)).mpr one_lt_two),
  apply_instance,
end

lemma lem5 {α : Type*} [fintype α] [linear_order α] {σ τ : perm α}
  (h0 : (fintype.card α).prime) (h1 : order_of σ = fintype.card α) (h2 : is_swap τ) :
  closure ({σ, τ} : set (perm α)) = ⊤ :=
closure_prime_cycle_swap h0 (lem4 h0 h1)
  (finset.eq_univ_of_card σ.support ((order_of_is_cycle (lem4 h0 h1)).symm.trans h1)) h2

noncomputable instance tada' {G : Type*} [group G] [fintype G] (H : subgroup G) : fintype H :=
  fintype.of_injective coe subtype.coe_injective

lemma lem6 {α : Type*} [fintype α] [linear_order α] {H : subgroup (perm α)} {τ : perm α}
  (h0 : (fintype.card α).prime) (h1 : fintype.card α ∣ fintype.card H) (h2 : τ ∈ H) (h3 : is_swap τ) :
H = ⊤ :=
begin
  haveI : fact (fintype.card α).prime := ⟨h0⟩,
  obtain ⟨σ, hσ⟩ := sylow.exists_prime_order_of_dvd_card (fintype.card α) h1,
  rw ← order_of_subgroup at hσ,
  rw [eq_top_iff, ←lem5 h0 hσ h3, closure_le, set.insert_subset, set.singleton_subset_iff],
  exact ⟨subtype.mem σ, h2⟩,
end
