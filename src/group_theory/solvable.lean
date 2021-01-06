/-
Copyright (c) 2021 Jordan Brown, Thomas Browning and Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jordan Brown, Thomas Browning and Patrick Lutz
-/

import group_theory.abelianization
import data.bracket

/-!
# Solvable Groups

In this file we introduce the notion of a solvable group. We define a solvable group as one whose
derived series is eventually trivial. This requires defining the commutator of two subgroups and
the derived series of a group.

## Main definitions

* `general_commutator H₁ H₂` : the commutator of the subgroups `H₁` and `H₂`
* `derived_series G n` : the `n`th term in the derived series of `G`, defined by iterating
  `general_commutator` starting with the top subgroup
* `is_solvable G` : the group `G` is solvable
-/

open subgroup

variables {G : Type*} [group G]

section general_commutator

/-- The commutator of two subgroups `H₁` and `H₂`. -/
instance general_commutator : has_bracket (subgroup G) (subgroup G) :=
⟨λ H₁ H₂, closure {x | ∃ (p ∈ H₁) (q ∈ H₂), p * q * p⁻¹ * q⁻¹ = x}⟩

lemma general_commutator_def (H₁ H₂ : subgroup G) :
  ⁅H₁, H₂⁆ = closure {x | ∃ (p ∈ H₁) (q ∈ H₂), p * q * p⁻¹ * q⁻¹ = x} := rfl

instance general_commutator_normal (H₁ H₂ : subgroup G) [h₁ : H₁.normal]
  [h₂ : H₂.normal] : normal ⁅H₁, H₂⁆ :=
begin
  let base : set G := {x | ∃ (p ∈ H₁) (q ∈ H₂), p * q * p⁻¹ * q⁻¹ = x},
  suffices h_base : base = group.conjugates_of_set base,
  { dsimp only [general_commutator_def, ←base],
    rw h_base,
    exact subgroup.normal_closure_normal },
  apply set.subset.antisymm group.subset_conjugates_of_set,
  intros a h,
  rw group.mem_conjugates_of_set_iff at h,
  rcases h with ⟨b, ⟨c, hc, e, he, rfl⟩, d, rfl⟩,
  exact ⟨d * c * d⁻¹, h₁.conj_mem c hc d, d * e * d⁻¹, h₂.conj_mem e he d, by group⟩,
end

lemma general_commutator_mono {H₁ H₂ K₁ K₂ : subgroup G} (h₁ : H₁ ≤ K₁) (h₂ : H₂ ≤ K₂) :
  ⁅H₁, H₂⁆ ≤ ⁅K₁, K₂⁆ :=
begin
  apply closure_mono,
  rintros x ⟨p, hp, q, hq, rfl⟩,
  exact ⟨p, h₁ hp, q, h₂ hq, rfl⟩,
end

lemma general_commutator_def' (H₁ H₂ : subgroup G) [H₁.normal] [H₂.normal] :
  ⁅H₁, H₂⁆ = normal_closure {x | ∃ (p ∈ H₁) (q ∈ H₂), p * q * p⁻¹ * q⁻¹ = x} :=
by rw [← normal_closure_eq_self ⁅H₁, H₂⁆, general_commutator_def,
  normal_closure_closure_eq_normal_closure]

lemma general_commutator_le (H₁ H₂ : subgroup G) (K : subgroup G) :
  ⁅H₁, H₂⁆ ≤ K ↔ ∀ (p ∈ H₁) (q ∈ H₂), p * q * p⁻¹ * q⁻¹ ∈ K :=
begin
  rw [general_commutator, closure_le],
  split,
  { intros h p hp q hq,
    exact h ⟨p, hp, q, hq, rfl⟩, },
  { rintros h x ⟨p, hp, q, hq, rfl⟩,
    exact h p hp q hq, }
end

lemma general_commutator_comm (H₁ H₂ : subgroup G) : ⁅H₁, H₂⁆ = ⁅H₂, H₁⁆ :=
begin
  suffices : ∀ H₁ H₂ : subgroup G, ⁅H₁, H₂⁆ ≤ ⁅H₂, H₁⁆, { exact le_antisymm (this _ _) (this _ _) },
  intros H₁ H₂,
  rw general_commutator_le,
  intros p hp q hq,
  have h : (p * q * p⁻¹ * q⁻¹)⁻¹ ∈ ⁅H₂, H₁⁆ := subset_closure ⟨q, hq, p, hp, by group⟩,
  convert inv_mem ⁅H₂, H₁⁆ h,
  group,
end

lemma general_commutator_le_right (H₁ H₂ : subgroup G) [h : normal H₂] :
  ⁅H₁, H₂⁆ ≤ H₂ :=
begin
  rw general_commutator_le,
  intros p hp q hq,
  exact mul_mem H₂ (h.conj_mem q hq p) (inv_mem H₂ hq),
end

lemma general_commutator_le_left (H₁ H₂ : subgroup G) [h : normal H₁] :
  ⁅H₁, H₂⁆ ≤ H₁ :=
begin
  rw general_commutator_comm,
  exact general_commutator_le_right H₂ H₁,
end

@[simp] lemma general_commutator_bot (H : subgroup G) : ⁅H, ⊥⁆ = (⊥ : subgroup G) :=
by { rw eq_bot_iff, exact general_commutator_le_right H ⊥ }

@[simp] lemma bot_general_commutator (H : subgroup G) : ⁅(⊥ : subgroup G), H⁆ = (⊥ : subgroup G) :=
by { rw eq_bot_iff, exact general_commutator_le_left ⊥ H }

lemma general_commutator_le_inf (H₁ H₂ : subgroup G) [normal H₁] [normal H₂] :
  ⁅H₁, H₂⁆ ≤ H₁ ⊓ H₂ :=
by simp only [general_commutator_le_left, general_commutator_le_right, le_inf_iff, and_self]

end general_commutator

section derived_series
variables (G)

/-- The derived series of the group `G`, obtained by starting from the subgroup `⊤` and repeatedly
  taking the commutator of the previous subgroup with itself for `n` times. -/
def derived_series : ℕ → subgroup G
| 0       := ⊤
| (n + 1) := ⁅(derived_series n), (derived_series n)⁆

@[simp] lemma derived_series_zero : derived_series G 0 = ⊤ := rfl

@[simp] lemma derived_series_succ (n : ℕ) :
  derived_series G (n + 1) = ⁅(derived_series G n), (derived_series G n)⁆ := rfl

lemma derived_series_normal (n : ℕ) : (derived_series G n).normal :=
begin
  induction n with n ih,
  { exact subgroup.top_normal, },
  { rw derived_series_succ,
    exactI general_commutator_normal (derived_series G n) (derived_series G n), }
end

@[simp] lemma general_commutator_eq_commutator :
  ⁅(⊤ : subgroup G), (⊤ : subgroup G)⁆ = commutator G :=
begin
  rw [commutator, general_commutator_def'],
  apply le_antisymm; apply normal_closure_mono,
  { exact λ x ⟨p, _, q, _, h⟩, ⟨p, q, h⟩, },
  { exact λ x ⟨p, q, h⟩, ⟨p, mem_top p, q, mem_top q, h⟩, }
end

lemma commutator_def' : commutator G = subgroup.closure {x : G | ∃ p q, p * q * p⁻¹ * q⁻¹ = x} :=
begin
  rw [← general_commutator_eq_commutator, general_commutator],
  apply le_antisymm; apply closure_mono,
  { exact λ x ⟨p, _, q, _, h⟩, ⟨p, q, h⟩ },
  { exact λ x ⟨p, q, h⟩, ⟨p, mem_top p, q, mem_top q, h⟩ }
end

@[simp] lemma derived_series_one : derived_series G 1 = commutator G :=
general_commutator_eq_commutator G

end derived_series

section general_nth_commutator

variables {G} (H : subgroup G)

def general_nth_commutator (n : ℕ) : subgroup G :=
nat.rec_on n H (λ _ H, ⁅H, H⁆)

lemma general_nth_commutator_succ (n : ℕ) : general_nth_commutator H (nat.succ n) =
  ⁅general_nth_commutator H n, general_nth_commutator H n⁆ :=
rfl

lemma general_nth_commutator_zero : general_nth_commutator H 0 = H :=
rfl

lemma general_nth_commutator_one :
  general_nth_commutator H 1 = ⁅H, H⁆ :=
by rw [general_nth_commutator_succ, general_nth_commutator_zero]

lemma additive_general_nth_commutator (n m : ℕ) :
  general_nth_commutator H (n + m) = general_nth_commutator (general_nth_commutator H n) m :=
begin
  induction m with m ih,
  { simp only [general_nth_commutator_zero, add_zero], },
  { simp only [general_nth_commutator_succ, ih], },
end

lemma additive_general_nth_commutator' (n m : ℕ) :
  general_nth_commutator H (n + m) = general_nth_commutator (general_nth_commutator H m) n :=
begin
  rw add_comm n m,
  exact additive_general_nth_commutator H m n,
end

lemma general_nth_commutator_mono (K : subgroup G) (leq : H ≤ K) (n : ℕ) :
  general_nth_commutator H n ≤ general_nth_commutator K n :=
begin
  induction n with n ih,
  { simp only [general_nth_commutator_zero, leq] },
  { rw [general_nth_commutator_succ, general_nth_commutator_succ],
    exact general_commutator_mono ih ih },
end

lemma nth_commutator_eq_general_nth_commutator_top :
  derived_series G = general_nth_commutator (⊤ : subgroup G) :=
begin
  funext n,
  induction n with n ih,
  { rw [derived_series_zero, general_nth_commutator_zero], },
  { rw [derived_series_succ, general_nth_commutator_succ, ih], },
end

end general_nth_commutator

section commutator_map

variables {G} {G' : Type*} [group G'] {f : G →* G'}

lemma map_commutator_eq_commutator_map (H₁ H₂ : subgroup G) :
  ⁅H₁, H₂⁆.map f = ⁅H₁.map f, H₂.map f⁆ :=
begin
  rw [general_commutator, general_commutator, monoid_hom.map_closure],
  apply le_antisymm; apply closure_mono,
  { rintros _ ⟨x, ⟨p, hp, q, hq, rfl⟩, rfl⟩,
    refine ⟨f p, mem_map.mpr ⟨p, hp, rfl⟩, f q, mem_map.mpr ⟨q, hq, rfl⟩, by simp *⟩, },
  { rintros x ⟨_, ⟨p, hp, rfl⟩, _, ⟨q, hq, rfl⟩, rfl⟩,
    refine ⟨p * q * p⁻¹ * q⁻¹, ⟨p, hp, q, hq, rfl⟩, by simp *⟩, },
end

lemma lift_commutator_eq_commutator_lift_lift {H : subgroup G} (K₁ K₂ : subgroup H) :
  ⁅K₁, K₂⁆.lift = ⁅K₁.lift, K₂.lift⁆ :=
map_commutator_eq_commutator_map _ _

lemma commutator_le_commutator_map {H₁ H₂ : subgroup G} {K₁ K₂ : subgroup G'} (h₁ : K₁ ≤ H₁.map f)
  (h₂ : K₂ ≤ H₂.map f) : ⁅K₁, K₂⁆ ≤ ⁅H₁, H₂⁆.map f :=
begin
  rw map_commutator_eq_commutator_map,
  exact general_commutator_mono h₁ h₂,
end

section nth_commutator_map

variables (f)

lemma map_derived_series_le_derived_series (n : ℕ) :
  (derived_series G n).map f ≤ derived_series G' n :=
begin
  induction n with n ih,
  { simp only [derived_series_zero, le_top], },
  { simp only [derived_series_succ, map_commutator_eq_commutator_map, general_commutator_mono, *], }
end

variables {f}

lemma derived_series_le_map_derived_series (hf : function.surjective f) (n : ℕ) :
  derived_series G' n ≤ (derived_series G n).map f :=
begin
  induction n with n ih,
  { rwa [derived_series_zero, derived_series_zero, top_le_iff, ← monoid_hom.range_eq_map,
    ← monoid_hom.range_top_iff_surjective.mpr], },
  { simp only [*, derived_series_succ, commutator_le_commutator_map], }
end

lemma derived_series_eq_map_derived_series (hf : function.surjective f) (n : ℕ) :
  derived_series G' n = (derived_series G n).map f :=
le_antisymm (derived_series_le_map_derived_series hf n) (map_derived_series_le_derived_series f n)

lemma nth_commutator_lift_le_nth_commutator (H : subgroup G) (n : ℕ) :
  (derived_series H n).lift ≤ derived_series G n :=
map_derived_series_le_derived_series _ n

end nth_commutator_map

section general_nth_commutator_map

variables (f) (H : subgroup G)

lemma map_nth_commutator_eq_nth_commutator_map (n : ℕ) :
  (general_nth_commutator H n).map f = general_nth_commutator (H.map f) n :=
begin
  induction n with n ih,
  { simp only [general_nth_commutator_zero], },
  { rw [general_nth_commutator_succ,general_nth_commutator_succ,
    map_commutator_eq_commutator_map, ih], },
end

lemma lift_nth_commutator_eq_nth_commutator_lift (K : subgroup H) (n : ℕ) :
  (general_nth_commutator K n).lift = general_nth_commutator K.lift n :=
map_nth_commutator_eq_nth_commutator_map _ _ _

lemma nth_commutator_lift_eq_general_nth_commutator (n : ℕ) :
  (derived_series H n).lift = general_nth_commutator H n:=
begin
  induction n with n ih,
  { rw [derived_series_zero, general_nth_commutator_zero, lift_top], },
  { rw [derived_series_succ, general_nth_commutator_succ,
    lift_commutator_eq_commutator_lift_lift, ih], },
end

end general_nth_commutator_map

end commutator_map

section solvable

variables (G)

/-- A group `G` is solvable if its derived series is eventually trivial. We use this definition
  because it's the most convenient one to work with. -/
class is_solvable : Prop :=
(solvable : ∃ n : ℕ, derived_series G n = ⊥)

lemma is_solvable_def : is_solvable G ↔ ∃ n : ℕ, derived_series G n = ⊥ :=
⟨λ h, h.solvable, λ h, ⟨h⟩⟩

@[priority 100]
instance is_solvable_of_comm {G : Type*} [comm_group G] : is_solvable G :=
begin
  use 1,
  rw [eq_bot_iff, derived_series_one],
  calc commutator G ≤ (monoid_hom.id G).ker : abelianization.commutator_subset_ker (monoid_hom.id G)
  ... = ⊥ : rfl,
end

instance is_solvable_of_top_eq_bot (h : (⊤ : subgroup G) = ⊥) : is_solvable G :=
⟨⟨0, by simp *⟩⟩

instance is_solvable_of_subsingleton [subsingleton G] : is_solvable G :=
is_solvable_of_top_eq_bot G (by ext; simp at *)

variables {G} {G' : Type*} [group G'] {f : G →* G'}

lemma solvable_of_solvable_injective (hf : function.injective f) [h : is_solvable G'] :
  is_solvable G :=
begin
  rw is_solvable_def at *,
  cases h with n hn,
  use n,
  rw eq_bot_iff_map_eq_bot hf,
  rw eq_bot_iff at *,
  calc map f (derived_series G n) ≤ derived_series G' n : map_derived_series_le_derived_series f n
  ... ≤ ⊥ : hn,
end

instance subgroup_solvable_of_solvable (H : subgroup G) [h : is_solvable G] : is_solvable H :=
solvable_of_solvable_injective (show function.injective (subtype H), from subtype.val_injective)

lemma solvable_of_surjective (hf : function.surjective f) [h : is_solvable G] :
  is_solvable G' :=
begin
  rw is_solvable_def at *,
  cases h with n hn,
  use n,
  calc derived_series G' n = (derived_series G n).map f : derived_series_eq_map_derived_series hf n
    ... = (⊥ : subgroup G).map f : by rw hn
    ... = ⊥ : map_bot f,
end

instance solvable_quotient_of_solvable (H : subgroup G) [H.normal] [h : is_solvable G] :
  is_solvable (quotient_group.quotient H) :=
solvable_of_surjective (show function.surjective (quotient_group.mk' H), by tidy)


open quotient_group

--this theorem (and its proof) is due to Mario

theorem eq_top_of_trivial_quotient (N:subgroup G) [N.normal]
  (H : (⊤ : subgroup (quotient_group.quotient N)) ≤ ⊥) : N = ⊤ :=
begin
  rw [← ker_mk N, eq_top_iff, monoid_hom.ker, ← subgroup.map_le_iff_le_comap],
  exact le_trans le_top H,
end

--(ker_mk N).symm.trans $ eq_top_iff.2 $ subgroup.map_le_iff_le_comap.1 $ le_trans le_top H

lemma le_ker {G' : Type*} [group G'] (f : G →* G') {H : subgroup G} : H.map f ≤ ⊥ ↔ H ≤ f.ker :=
begin
  split,
  { intros h x hx,
    rw [← eq_bot_iff, eq_bot_iff_forall] at h,
    exact (monoid_hom.mem_ker f).mpr (h (f x) ⟨x, hx, rfl⟩), },
  { rintros h _ ⟨x, hx, rfl⟩,
    exact mem_bot.mpr ((monoid_hom.mem_ker f).mp (h hx)), },
end

lemma nth_commutator_le_ker {G' : Type*} [group G'] (f : G →* G') (h : is_solvable G') :
  ∃ n, derived_series G n ≤ f.ker :=
begin
  rw is_solvable_def at h,
  cases h with n hn,
  have key := map_derived_series_le_derived_series f n,
  exact ⟨n, by rwa [hn, le_ker] at key⟩,
end

lemma nth_commutator_le_of_solvable_quotient (H : subgroup G) [H.normal]
  (h : is_solvable (quotient_group.quotient H)) : ∃ n, (derived_series G n) ≤ H :=
by {rw ← ker_mk H, exact nth_commutator_le_ker (mk' H) h}

lemma nth_commutator_le_map_nth_commutator_of_le_map {G' : Type*} [group G'] {f : G →* G'}
  {H : subgroup G} {K : subgroup G'} (h : K ≤ H.map f) (n : ℕ) :
  general_nth_commutator K n ≤ (general_nth_commutator H n).map f :=
calc general_nth_commutator K n
      ≤ general_nth_commutator (map f H) n : general_nth_commutator_mono _ _ h n
  ... = (general_nth_commutator H n).map f : by rw ← map_nth_commutator_eq_nth_commutator_map

lemma short_exact_sequence_solvable' {G' G'' : Type*} [group G'] [group G''] (f : G' →* G)
  (g : G →* G'') (hfg : f.range = g.ker) (hG' : is_solvable G') (hG'' : is_solvable G'') :
  is_solvable G :=
begin
  rw is_solvable_def at hG' ⊢,
  cases hG' with n hn,
  obtain ⟨m, hm⟩ := nth_commutator_le_ker g hG'',
  use n + m,
  rw [eq_bot_iff, nth_commutator_eq_general_nth_commutator_top, additive_general_nth_commutator',
    ← nth_commutator_eq_general_nth_commutator_top],
  rw [← hfg, monoid_hom.range_eq_map] at hm,
  calc general_nth_commutator (derived_series G m) n
      ≤ (general_nth_commutator (⊤ : subgroup G') n).map f : nth_commutator_le_map_nth_commutator_of_le_map hm n
  ... = (derived_series G' n).map f : by rw ← nth_commutator_eq_general_nth_commutator_top
  ... = (⊥ : subgroup G').map f : by rw hn
  ... = (⊥ : subgroup G) : map_bot f,
end

lemma range_subtype (H : subgroup G) : H.subtype.range = H :=
by { ext, exact ⟨λ ⟨⟨x, hx⟩, rfl⟩, hx, λ hx, ⟨⟨x, hx⟩, rfl⟩⟩ }

lemma short_exact_sequence_solvable'' (H : subgroup G) [H.normal] (h : is_solvable H)
  (h' : is_solvable (quotient_group.quotient H)) : is_solvable G :=
begin
  refine short_exact_sequence_solvable' (subtype H) (mk' H) _ h h',
  rw [ker_mk, range_subtype],
end

lemma solvable_prod {G' : Type*} [group G'] (h : is_solvable G) (h' : is_solvable G') :
  is_solvable (G × G') :=
begin
  refine short_exact_sequence_solvable' (monoid_hom.inl G G') (monoid_hom.snd G G') _ h h',
  ext x, split,
  { rintros ⟨y, rfl⟩,
    simp only [monoid_hom.mem_ker, monoid_hom.inl_apply, monoid_hom.coe_snd], },
  { cases x with x y,
    intros hx,
    simp only [monoid_hom.mem_ker, monoid_hom.coe_snd] at hx,
    simp only [monoid_hom.mem_range, monoid_hom.inl_apply, hx],
    use x, }
end

lemma quotient_something (H : subgroup G) [H.normal]
  (h' : is_solvable (quotient_group.quotient H)) : ∃ m : ℕ, (derived_series G m) ≤ H :=
begin
  rw is_solvable_def at h',
  cases h' with paris france,
  use paris,

  have surj:function.surjective (quotient_group.mk' H),
  convert surjective_quot_mk setoid.r,
  have image: derived_series (quotient H) paris=(derived_series G paris).map (quotient_group.mk' H),
  apply derived_series_eq_map_derived_series surj,
  rw france at image,
  suffices: ↑(derived_series G paris) ⊆ ↑H,
  exact coe_subset_coe.mp this,
  intros x x_in,

  --it seems like this should follow from image in one line
  have bound:(mk' H) x ∈ (⊥:subgroup (quotient H)),
  simp *,
  use x,
  split,
  exact x_in,
  simp only [eq_self_iff_true],
  have reduction:(mk' H) x=(mk' H) 1,
  simp[bound],
  exact mem_bot.mp bound,
  rw  subgroup.set.has_coe,
  have triv_mem':=subgroup.one_mem H,
  have triv_mem: (1:G)∈ ↑ H,
  exact mem_coe.mpr triv_mem',
  have s:= @quotient_group.eq G _inst_1 H 1 x,
  have small:1⁻¹ * x=x,
  simp only [one_inv, one_mul],
  rw small at s,
  apply s.1,
  have hmmmm:↑(1:G)=mk (1:G),
  exact (rfl.congr bound).mp (eq.symm bound),
  have hmmmmmmmm:↑ x=mk x,
  exact (rfl.congr (eq.symm bound)).mp bound,
  change (mk) x=(mk) 1 at reduction,
  symmetry,
  rwa [hmmmm,hmmmmmmmm],
end

lemma short_exact_sequence_solvable (H : subgroup G) [H.normal]
(h : is_solvable H) (h':is_solvable (quotient_group.quotient H)): is_solvable G:=
begin
  have reduction:=quotient_something H h',
  rw is_solvable_def at h,
  cases h with n n_solves,
  cases reduction with m m_solves,
  use n+m,
  rw [nth_commutator_eq_general_nth_commutator_top, additive_general_nth_commutator'],
  rw nth_commutator_eq_general_nth_commutator_top at m_solves,
  rw nth_commutator_eq_general_nth_commutator_top at n_solves,
  apply eq_bot_iff.mpr,

  have s: general_nth_commutator H n≤ ⊥,

  {rw ← nth_commutator_eq_general_nth_commutator_top at n_solves,
  suffices t: (derived_series H n).lift = general_nth_commutator H n,
  rw n_solves at t,
  have v: (⊥:subgroup H).lift =⊥:=(⊥:subgroup H).eq_bot_iff_lift_eq_bot.mp rfl,
  {rw v at t,
  finish},
  apply nth_commutator_lift_eq_general_nth_commutator},

  suffices x:
  general_nth_commutator (general_nth_commutator ⊤ m) n≤ general_nth_commutator H n,
  finish,

  apply general_nth_commutator_mono,
  exact m_solves,
end


inductive weekday : Type
| monday : weekday
| tuesday : weekday
| wednesday : weekday
| thursday : weekday
| friday : weekday

lemma weekday_perm_unsolvable:¬ is_solvable (equiv.perm weekday):=
begin
  rw is_solvable_def,
  push_neg,
  --have stability:∀ n:ℕ,
  --intro n,
  --induction n,
  --pply subgroup.eq_bot_iff_forall (nth_commutator (equiv.perm weekday) ),
  sorry,

end

--nth_commutator_eq_map_nth_commutator

--def alternating_group (X:Type u)[fintype X]:Type u:=(equiv.perm.sign X).ker

--instance (X:Type u)[fintype X]: group((equiv.perm.sign X).ker)

lemma unsolvability_of_S_5 (X : Type*) (big : 5 ≤ cardinal.mk X) [fintype X] :
  ¬ is_solvable (equiv.perm X) :=
begin
  --have x:=X.elems.val.to_list,
  rw is_solvable_def,
  push_neg,
  have moscow:=_inst_3.elems,
  have russia:=_inst_3.complete,
  let delhi:=fintype.elems X,
  let paris:=(delhi).val,
  have france:=(delhi).nodup,
  have u: list X,
  exact list.nil,


  rw cardinal.le_mk_iff_exists_set at big,
  cases big with big_subset florida,
  --have v:cardinal.mk big_subset < cardinal.omega,
  --apply cardinal.lt_omega.2,
  --use 5,

  --exact florida,

  --have u: fintype big_subset,
  --apply fintype.of_equiv,
  have w:fintype.card ↥big_subset=5,

  --library_search,


  have equiv: nonempty((fin 5)≃ big_subset),

  apply fintype.card_eq.1,


  --library_search!,
  --have first: ∃ x_1,x_1∈ big_subset,
  all_goals { sorry },
end

end solvable
