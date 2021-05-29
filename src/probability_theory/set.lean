import data.set

lemma set.disjoint_inter_compl {α:Type*} (A B C:set α):disjoint (A ∩ B) (C∩ Bᶜ) :=
begin
  apply set.disjoint_of_subset_left (set.inter_subset_right A B),
  apply set.disjoint_of_subset_right (set.inter_subset_right C Bᶜ),
  simp [disjoint_iff],
end

def set.symmetric_difference {α :Type*} (A B:set α) := (A \ B) ∪ (B \ A)

class has_symm_diff (α : Type*) := (symm_diff : α → α → α)

-- U+2206: symmetric difference
infixr ` ∆ `:70  := has_symm_diff.symm_diff

instance set.has_symm_diff {α : Type*}: has_symm_diff (set α) := ⟨set.symmetric_difference⟩

lemma set.has_symm_diff.def {α : Type*} {A B:set α}:A ∆ B = (A \ B) ∪ (B \ A) := rfl

lemma set.preimage_fst_def {α β:Type*} {Bα:set (set α)}:
    (@set.preimage (α × β) α (@prod.fst α β) '' Bα) =
    {U : set (α × β) | ∃ (A : set α) (H : A ∈ Bα), U = @set.prod α β A (@set.univ β)} :=
begin
  ext,split;intros A1A,
  { simp at A1A,
    cases A1A with A A1A,
    cases A1A with A1B A1C,
    subst x,
    split,
    simp,
    split,
    apply A1B,
    unfold set.prod,
    simp,
    refl,},
  { simp at A1A,
    cases A1A with A A1A,
    cases A1A with A1B A1C,
    subst x,
    split,
    split,
    apply A1B,
    unfold set.prod,
    simp,
    refl}
end

lemma set.preimage_snd_def {α β:Type*} {Bβ:set (set β)}:
    (@set.preimage (α × β) β (@prod.snd α β) '' Bβ) =
    {U : set (α × β) | ∃ (B : set β) (H : B ∈ Bβ), U = @set.prod α β (@set.univ α) B} :=
begin
    ext,split;intros A1A,
    { simp at A1A,
      cases A1A with A A1A,
      cases A1A with A1B A1C,
      subst x,
      split,
      simp,
      split,
      apply A1B,
      unfold set.prod,
      simp,
      refl,},
    { simp at A1A,
      cases A1A with A A1A,
      cases A1A with A1B A1C,
      subst x,
      split,
      split,
      apply A1B,
      unfold set.prod,
      simp,
      refl}
end

lemma preimage_if {α β:Type*}
  {E:set α} {D:decidable_pred E}
  {X Y:α → β} {S:set β}:
  set.preimage (λ a:α, if (E a) then (X a) else (Y a)) S =
  (E ∩ set.preimage X S) ∪ (Eᶜ ∩ set.preimage Y S) :=
begin
  ext a;split;intros A1,
  { cases (classical.em (a∈ E)) with A2 A2,
    { rw set.mem_preimage at A1,
      rw if_pos at A1,
      apply set.mem_union_left,
      apply set.mem_inter A2,
      rw set.mem_preimage,
      apply A1,
      rw set.mem_def at A2,
      apply A2,},
    { rw set.mem_preimage at A1,
      rw if_neg at A1,
      apply set.mem_union_right,
      apply set.mem_inter,
      apply set.mem_compl,
      apply A2,
      rw set.mem_preimage,
      apply A1,
      rw set.mem_def at A2,
      apply A2,},
  },
  { rw set.mem_preimage,
    rw set.mem_union at A1,
    cases A1 with A1 A1;
    rw set.mem_inter_eq at A1;
    cases A1 with A2 A3;
    rw set.mem_preimage at A3;
    rw set.mem_def at A2,
    { rw if_pos,
      apply A3,
      apply A2,},
    { rw if_neg,
      apply A3,
      apply A2,},},
end
