import group_theory.abelianization

open_locale classical

local notation G ` /ₘ ` H := @quotient_group.quotient G _ H

-- ↓ Goes in subgroup.lean
@[simp] lemma subgroup.mem_normal_closure_iff {G : Type*} [group G] {k : set G} {x : G} :
  x ∈ subgroup.normal_closure k ↔ ∀ K : subgroup G, K.normal → k ⊆ K → x ∈ K :=
begin
  split; intro hx,
    { intros K hK hsub,
      rw (@subgroup.normal_closure_subset_iff _ _ _ _ hK) at hsub,
      exact hsub hx },
    { exact hx (subgroup.normal_closure k) (by apply_instance) subgroup.subset_normal_closure }
end

def subgroup.inclusion {G : Type*} [group G] (H : subgroup G) : H →* G :=
  ⟨λ h, h.1, rfl, λ _ _, rfl⟩

-- ↓ Goes in subgroup.lean
@[to_additive]
lemma subgroup.normal.map {G : Type*} [group G] {N : Type*} [group N]
  {H : subgroup G} (hH : H.normal) (f : G →* N) (hf : function.surjective f) :
  (subgroup.map f H).normal :=
⟨ begin
    intros n hn g,
    rcases hf n with ⟨n, rfl⟩,
    rcases hf g with ⟨g, rfl⟩,
    rcases hn with ⟨u, hu, heq⟩,
    refine ⟨_, hH.conj_mem u hu g, _⟩,
    simp [monoid_hom.map_mul, heq],
  end ⟩

@[simp] lemma subgroup.inclusion_def {G : Type*} [group G] (H : subgroup G) (h : H) :
  H.inclusion h = h.1 := rfl

/-- The `n`-th derived subgroup is the commutator subgroup of the `n - 1`-th derived subgroup-/
def derived_subgroup (G : Type*) [group G] : ℕ → subgroup G
| 0       := ⊤
| (n + 1) := (commutator $ derived_subgroup n).map (derived_subgroup n).inclusion

namespace derived_subgroup

variables {G : Type*} [group G]

-- Make `derived_subgroup (n + 1)` as a subgroup of `derived_subgroup n`
def lift (G : Type*) [group G] (n : ℕ) :=
  (derived_subgroup G n.succ).comap (derived_subgroup G n).inclusion

@[simp] lemma lift_def (G : Type*) [group G] (n : ℕ) :
  derived_subgroup.lift G n = (derived_subgroup G n.succ).comap
    (derived_subgroup G n).inclusion := rfl

@[simp] lemma zero : derived_subgroup G 0 = ⊤ := rfl

@[simp] lemma succ (n : ℕ) :
  derived_subgroup G n.succ =
  subgroup.map (derived_subgroup G n).inclusion (commutator $ derived_subgroup G n) := rfl

instance (n : ℕ) : subgroup.normal $ derived_subgroup.lift G n :=
{ conj_mem :=
  begin
    intros h hh g,
    rw [lift_def, subgroup.mem_comap, subgroup.inclusion_def, succ, subgroup.mem_map] at hh ⊢,
    rcases hh with ⟨a, ha, hha⟩, refine ⟨g * a * g⁻¹, _, by simpa⟩,
    exact (show (commutator $ derived_subgroup G n).normal, by apply_instance).conj_mem _ ha _,
  end }

@[simp] lemma one : derived_subgroup G 1 = commutator G :=
begin
  rw succ, ext, split; rw subgroup.mem_map,
    { rintro ⟨d, hd, rfl⟩,
      rw subgroup.inclusion_def,
      erw subgroup.mem_normal_closure_iff at hd ⊢,
      intros N hN hsub,
      refine hd (subgroup.comap (subgroup.inclusion ⊤) N) (subgroup.normal.comap hN _) _,
      rintro x ⟨⟨p, hp⟩, ⟨q, hq⟩, rfl⟩,
      exact hsub ⟨p, q, rfl⟩ },
    { intro hx,
      refine ⟨⟨x, subgroup.mem_top x⟩, _, rfl⟩,
      erw subgroup.mem_normal_closure_iff at hx ⊢,
      intros N hN hsub,
      specialize hx (subgroup.map (subgroup.inclusion _) N) _ _,
        { rw subgroup.mem_map at hx,
          rcases hx with ⟨x, hx, rfl⟩,
          convert hx, tidy },
        { exact subgroup.normal.map hN _ (λ x, ⟨⟨x, by simp only [zero]⟩, rfl⟩) },
        { rintro x ⟨p, q, rfl⟩,
          erw subgroup.mem_map,
          exact ⟨⟨p * q * p⁻¹ * q⁻¹, _⟩, hsub
            ⟨⟨p, by simp only [zero]⟩, ⟨q, by simp only [zero]⟩, rfl⟩, rfl⟩ } }
end

def is_solvable (G : Type*) [group G] :=
  ∃ n : ℕ, derived_subgroup G n = ⊥

@[simp] lemma is_solvable_def : is_solvable G ↔ ∃ n : ℕ, derived_subgroup G n = ⊥ := iff.rfl

noncomputable def length_of_solvable (h : is_solvable G) := nat.find h

end derived_subgroup

-----

-- def group.nontrivial (G : Type*) [group G] : Prop := (⊥ : subgroup G) ≠ ⊤

-- @[simp] lemma group.nontrivial_def {G : Type*} [group G] :
--   group.nontrivial G ↔ (⊥ : subgroup G) ≠ ⊤ := iff.rfl

def is_simple (G : Type*) [group G] :=
  nontrivial G ∧ ∀ N : subgroup G, N.normal → N = ⊥ ∨ N = ⊤

@[simp] lemma is_simple_def (G : Type*) [group G] : is_simple G ↔
  nontrivial G ∧ ∀ N : subgroup G, N.normal → N = ⊥ ∨ N = ⊤ := iff.rfl

-----

namespace derived_subgroup

variables {G : Type*} [group G]

-- lemma quotient_trival_iff (H : subgroup G) [H.normal] :
--   ¬ nontrivial (G /ₘ H) ↔ H = ⊤ := sorry

-- Show that the commutator subgroup is the a

lemma simple_factor (n : ℕ) (h : nontrivial $ (derived_subgroup G n) /ₘ (lift G n)) : is_simple
  ((derived_subgroup G n) /ₘ (lift G n)) :=
begin
  refine ⟨h, _⟩,
  sorry
end

end derived_subgroup
