import data.real.nnreal
import data.finset
import topology.algebra.infinite_sum
import topology.algebra.ordered.basic

import probability_theory.filter


/- This is a combination of finset.sum_congr and finset.sum_const_zero.-/
lemma finite_sum_zero_eq_zero {α β:Type*} [add_comm_monoid α] [decidable_eq β] (f:β → α) (S:finset β):
  (∀ s∈ S, f s = 0) →
  S.sum f = 0 :=
begin
  intro A1,
  let g:β → α := λ a:β, (0:α),
  begin
    have B1:S = S := rfl,
    have B2:(∀ x∈ S, f x = g x),
    { intros x B2A,
      rw A1 x B2A,},
    rw finset.sum_congr B1 B2,
    apply finset.sum_const_zero,
  end
end

lemma all_finset_sum_eq_zero_iff_eq_zero {β:Type*} [D:decidable_eq β] (f:β → nnreal):
 (∀ S:finset β,  S.sum f = 0) ↔ f = 0 :=
begin
  split;intros A1,
  { ext b,
    have A2 := A1 {b},
    simp at A2,
    rw A2,
    simp,},
  { intros S,
    apply finite_sum_zero_eq_zero,
    intros b A2,
    rw A1,
    simp,},
end

lemma le_add_of_nonneg {β:Type*} [ordered_add_comm_monoid β] (a b:β):
  0 ≤ b → a ≤ a + b :=
begin
  intros A1,
  have B1:a + 0 ≤ a + b,
  { apply @add_le_add,
    apply le_refl a,
    apply A1,},
  rw add_zero at B1,
  apply B1,
end

lemma le_add_nonnegative {β:Type*} [canonically_ordered_add_monoid β] (a b:β):
  a ≤ a + b :=
begin
  apply le_add_of_nonneg,
  apply zero_le,
end

lemma finset.sum_monotone {α β:Type*} [decidable_eq α] [canonically_ordered_add_monoid β] {S T:finset α}
  {f:α → β}:S ⊆ T → S.sum f ≤ T.sum f  :=
begin
  intros A2,
  rw ← finset.sum_sdiff A2,
  rw add_comm,
  apply le_add_nonnegative,
end

lemma finset.sum_monotone' {α β:Type*} [D:decidable_eq α] [canonically_ordered_add_monoid β]
  {f:α → β}:monotone (λ S:finset α, S.sum f) :=
begin
  intros S T B1,
  apply finset.sum_monotone B1,
end

lemma set_Iio_in_nhds_of_lt {x y:nnreal}:x ≠ 0 → x < y → set.Iio y ∈ nhds x :=
begin
  intros AX A1,
  rw @mem_nhds_sets_iff,
  apply exists.intro (set.Ioo 0 y),
  split,
  { apply set.Ioo_subset_Iio_self,},
  split,
  { apply is_open_Ioo,},
  simp,
  split,
  { apply bot_lt_iff_ne_bot.mpr,
    apply AX,},
  { apply A1,},
end

lemma has_sum_nnreal_bounds {α:Type*} {f:α → nnreal} [D:decidable_eq α] {x:nnreal}:(x≠ 0) → (has_sum f x) → (∀ S:finset α, S.sum f ≤ x) :=
begin
  intros A1 A2,
  intro S,
  unfold has_sum at A2,
  apply le_of_not_lt,
  intro A3,
  let r := (finset.sum S f) - x,
  begin
    have A5:set.Iio (finset.sum S f) ∈ nhds x,
    { apply set_Iio_in_nhds_of_lt A1 A3,},
    have A6:= set.mem_of_subset_of_mem A2 A5,
    have A7 := filter_at_top_elim A6,
    cases A7 with B A7,
    rw set.subset_def at A7,
    have A8:(B∪ S) ∈ {b : finset α | B ≤ b},
    { simp,
      apply finset.subset_union_left,},
    have A9 := A7 (B ∪ S) A8,
    simp at A9,
    have A10 := not_le_of_lt A9,
    apply A10,
    apply finset.sum_monotone',
    simp,
    apply finset.subset_union_right,
  end
end

lemma has_sum_nnreal_ne_zero {α:Type*} {f:α → nnreal} [decidable_eq α] {x:nnreal}:(x≠ 0) →
  ((∀ ε>0, ∃ S:finset α,
   ∀ T⊇S,  (T.sum f ≤ x) ∧  x - ε < T.sum f  )↔
  (has_sum f x)) :=
begin
  intro AX,
  split;intro A1,
  { unfold has_sum,
    apply filter.tendsto_def.mpr,
    intros b A2,
    have A3:= mem_nhds_elim_nnreal_bound b x AX A2,
    cases A3 with ε A4,
    cases A4 with A5 A6,
    have A7 := A1 ε A5,
    cases A7 with S A8,
    apply filter_at_top_intro3 S,
    intros T A9,
    have A10 := A8 T A9,
    apply A6,
    simp,
    split,
    { apply A10.right,},
    { apply lt_of_le_of_lt,
      apply A10.left,
      apply lt_add_of_pos_right,
      apply A5,},},
  { intros ε A2,
    have A10 := has_sum_nnreal_bounds AX A1,
    unfold has_sum at A1,
    have A3:set.Ioo (x - ε) (x + ε) ∈ nhds x,
    { apply set_Ioo_in_nhds_of_ne_zero AX A2,},
    have A4 := set.mem_of_subset_of_mem A1 A3,
    have A5 := mem_filter_at_top_elim A4,
    cases A5 with S A6,
    apply exists.intro S,
    intros T A7,
    rw set.subset_def at A6,
    have A8 := A6 T A7,
    have A9:T.sum f ∈ set.Ioo (x - ε) (x + ε) := A8,
    split,
    { apply A10 T,},
    { simp at A9,
      apply A9.left,},}
end
