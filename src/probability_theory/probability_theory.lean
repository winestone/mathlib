/-
Copyright 2021 Google LLC
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
      http : //www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
Authors :  Martin Zinkevich (modified for mathlib by Hunter Monroe and Eric Wieser)
 -/

import measure_theory.measurable_space
import measure_theory.measure_space

/-! This file defines the basic concepts in probability theory.
    There are four fundamental principles :
    1. Make theorems as readable as possible. Use Pr[A ∧ B], not μ (A ∩ B). Other examples :
       Pr[(X >ᵣ 3) ∨ (Y =ᵣ 7)]. While events are technically sets, in probability theory,
       they are better written as propositions that may or may not hold.
    2. Avoid absurd statements where possible. Don't allow Pr[A] if A is not an event,
       or Pr[X ∈ᵣ S] if S is not measurable, or Pr[∀ᵣ a in S, E a] if S is not countable.
       It is always possible to write Pr[⟨S, ...proof S is an event...⟩].
    3. Embed measurability into the objects and operations themselves. An event is measurable by
       definition. When we take the and, or, not, for all, exists, measurability should be automatic.
    4. Don't expect the reader to know measure theory, but at times it may be required by the
       author.
    Several concepts are defined in this module :
      probability_space:  a measure_space where the measure has a value of 1.
      event:  a subtype of a set that is measurable (defined based upon the measurable space),
      which is an event on a probability space (defined based upon the probability).
      Pr[E]:  the probability of an event.
      measurable_fun: a subtype of a function that is measurable (denoted (M₁ →ₘ M₂)).
      random_variable: a measurable_fun whose domain is a probability space (denoted (P →ᵣ M)).
     Also, various independence and identical definitions are specified. Some choices :
     * A and B are independent if A has zero probability.
     * an infinite family of events/random variables is independent if every finite subset
       is independent.
     * Two random variables are identical if they have equal probability on every measurable
       set. The probability spaces on which they are defined need not be equal.
      -/

open measure_theory measurable_space
open_locale big_operators classical

namespace probability_theory

/-
A probability space is a measure space with volume one.
-/
class probability_space (α : Type*) extends measure_space α :=
  (volume_univ : volume (set.univ) = 1)

export probability_space (volume_univ)

/- An event is a measurable set in a measurable space that has a probability measure. -/
def event (Ω : Type*) [measurable_space Ω] : Type* := {x : set Ω // measurable_set x}

lemma event_val_eq_coe {Ω : Type*} [probability_space Ω]
  (X : event Ω) : X.val =
  (@coe (subtype (@measurable_set Ω _)) (set Ω) _ X) :=
  by refl

lemma event.eq {Ω : Type*} [probability_space Ω] (A B : event Ω) :
A.val = B.val → A = B := subtype.eq

def event_mem {Ω : Type*} [P : probability_space Ω] (a : Ω) (E : event Ω) : Prop :=
  a∈ E.val

instance {Ω : Type*} [P : probability_space Ω] : has_mem Ω (event Ω) := {
  mem := event_mem
}

lemma event_mem_val {Ω : Type*} [P : probability_space Ω] (ω : Ω) (E : event Ω) :
  (ω ∈ E) = (ω ∈ E.val) := rfl

/- The weight of an event is ≤1. -/
lemma prob_le_1 {Ω : Type*} [probability_space Ω] (S : set Ω) :
  volume S ≤ 1 :=
begin
  have A3 : volume S ≤ volume set.univ := volume.mono (set.subset_univ _),
  rw volume_univ at A3,
  exact A3,
end

/- The probability of an event is not infinite. -/
lemma prob_not_infinite {Ω : Type*} [probability_space Ω] (S : set Ω) :
  (volume S) ≠ ⊤ :=
begin
  have A1 : volume S ≤ 1,
  {  apply prob_le_1,
  },
  intro A2,
  rw A2 at A1,
  have A3 : (1 : ennreal)=⊤,
  { apply complete_linear_order.le_antisymm,
  {   apply (ennreal.complete_linear_order.le_top),
    },
  {   apply A1,
    }
  },
  have A4 : (1 : ennreal) ≠ (⊤ : ennreal),
  { apply ennreal.one_ne_top,
  },
  rw A3 at A4,
  apply A4,
  refl,
end

/- Probabilities are non-negative real numbers. -/
lemma prob_nnreal {Ω : Type*} [probability_space Ω] (S : set Ω) :
   ↑((volume S).to_nnreal) = volume S :=
begin
  apply ennreal.coe_to_nnreal,
  apply prob_not_infinite,
end

/- The probability of an event is equal to its measure. -/
def event_prob {Ω : Type*} [probability_space Ω] (E : event Ω) : nnreal :=
  (volume E.val).to_nnreal

notation `Pr[`E`]` := event_prob E

lemma event_prob_def {Ω : Type*} [probability_space Ω] (E : event Ω) :
  ↑(Pr[E]) = (volume E.val) := by
begin
  unfold event_prob,
  apply prob_nnreal,
end

lemma to_nnreal_almost_monotonic (a b : ennreal) : (a≠ ⊤)→(b≠⊤)→(a ≤ b)→ (a.to_nnreal ≤ b.to_nnreal) :=
begin
  intros A1 A2 A3,
  have A4 : ↑(a.to_nnreal)=a,
  { apply ennreal.coe_to_nnreal,
    apply A1,
  },
  have A5 : ↑(b.to_nnreal)=b,
  { apply ennreal.coe_to_nnreal,
    apply A2,
  },
  rw ← A4 at A3,
  rw ← A5 at A3,
  simp at A3,
  apply A3,
end

-- See ennreal.add_eq_top
lemma add_finite (a b : ennreal) : (a≠ ⊤) → (b≠ ⊤) → (a + b≠ ⊤) :=by finish

/- Probability is monotonoe with respect to set inclusion. -/
lemma event_prob_mono1 {Ω : Type*} [probability_space Ω] (E F : event Ω) :
  volume E.val ≤ volume F.val →
  Pr[E] ≤ Pr[F] :=
begin
  unfold event_prob,
  intro A1,
  apply to_nnreal_almost_monotonic,
  apply prob_not_infinite,
  apply prob_not_infinite,
  apply A1,
end

/- Probability is monotonoe with respect to set inclusion. -/
lemma event_prob_mono2 {Ω : Type*} [probability_space Ω] (E F : event Ω) :
  (E.val ⊆ F.val) →
  Pr[E] ≤ Pr[F] :=
begin
  intro A1,
  apply event_prob_mono1,
  apply volume.mono,
  apply A1,
end

/- The event universe consists of the measurable sets. -/
def event_univ (Ω : Type*) [measurable_space Ω] : event Ω := {
  val := set.univ,
  property := measurable_set.univ,
}

@[simp]
lemma event_univ_val_def {Ω : Type*} [probability_space Ω] :
  (event_univ Ω).val = set.univ :=
begin
  unfold event_univ event_univ,
end

/- The probability of the event universe is 1. -/
@[simp]
lemma Pr_event_univ {Ω : Type*} [probability_space Ω] :
  Pr[event_univ Ω] = 1 :=
begin
  have A1 : ↑(Pr[event_univ Ω]) = (1 : ennreal),
  { rw event_prob_def,
    apply volume_univ,
  },
  simp at A1,
  apply A1
end

/- The probability (Pr) of an event is ≤1. -/
@[simp]
lemma Pr_le_one {Ω : Type*} [probability_space Ω] {E : event Ω} : Pr[E] ≤ 1 :=
begin
  have A1 : Pr[E] ≤ Pr[event_univ Ω],
  { apply event_prob_mono2,
    rw event_univ_val_def,
    rw set.subset_def,simp,
  },
  rw Pr_event_univ at A1,
  apply A1,
end

/- The empty event has weight zero. -/
def event_empty (Ω : Type*) [measurable_space Ω] : event Ω := {
  val := ∅,
  property := measurable_set.empty,
}

instance has_emptyc_event {Ω : Type*} {M : measurable_space Ω} : has_emptyc (event Ω) :=
  ⟨ @event_empty Ω M ⟩

lemma has_emptyc_emptyc_event {Ω : Type*} [probability_space Ω] :
  ∅ = (event_empty Ω) := rfl

@[simp]
lemma event_empty_val_def {Ω : Type*} [probability_space Ω] :
  (event_empty Ω).val = ∅ := rfl

@[simp]
lemma event_empty_val_def2 {Ω : Type*} [probability_space Ω] :
  (@has_emptyc.emptyc (event Ω) _).val = ∅ := rfl

/- The probability of an empty event is zero. -/
@[simp]
lemma Pr_event_empty {Ω : Type*} [probability_space Ω] :
  Pr[event_empty Ω] = 0 :=
begin
  have A1 : ↑(Pr[event_empty Ω]) = (0 : ennreal),
  { rw event_prob_def,
    apply volume.empty,
  },
  simp at A1,
  apply A1
end

/- The probability of the empty set is zero. -/
@[simp]
lemma Pr_event_empty' {Ω : Type*} [probability_space Ω] :
  Pr[(∅ : event Ω)] = 0 :=
begin
  rw has_emptyc_emptyc_event,
  apply Pr_event_empty,
end

def event_const (Ω : Type*) [probability_space Ω] (P : Prop) : event Ω := {
  val := {ω : Ω|P},
  property := measurable_set.const P,
}

@[simp]
lemma event_const_val_def {Ω : Type*} [probability_space Ω] (P : Prop) :
  (event_const _ P).val={ω : Ω|P} := rfl

lemma event_const_true_eq_univ {Ω : Type*} [probability_space Ω] (P : Prop) : P →
(event_const _ P)=event_univ Ω :=
begin
  intro A1,
  apply event.eq,
  simp [A1],
end

lemma event_const_false_eq_empty {Ω : Type*} [probability_space Ω] (P : Prop) : ¬P →
(event_const _ P)=event_empty Ω :=
begin
  intro A1,
  apply event.eq,
  simp [A1],
end

lemma Pr_event_const_true {Ω : Type*} [probability_space Ω] (P : Prop) : P →
Pr[(event_const Ω P)]=1 :=
begin
  intro A1,
  rw event_const_true_eq_univ,
  apply Pr_event_univ,
  exact A1,
end

lemma Pr_event_const_false {Ω : Type*} [probability_space Ω] (P : Prop) : ¬P →
Pr[(event_const Ω P)]=0 :=
begin
  intro A1,
  rw event_const_false_eq_empty,
  apply Pr_event_empty,
  exact A1,
end

/- The "and" of two events is their intersection. -/
def measurable_inter {Ω : Type*} [measurable_space Ω] (A B : event Ω) : event Ω := {
  val :=A.val ∩ B.val,
  property := measurable_set.inter A.property B.property,
}

@[simp]
lemma measurable_inter_val_def {Ω : Type*} [measurable_space Ω] (A B : event Ω) :
  (measurable_inter A B).val= A.val ∩ B.val := rfl

instance event_has_inter {Ω : Type*} [measurable_space Ω] : has_inter (event Ω) := {
  inter := measurable_inter,
}

@[simp]
lemma measurable_inter_val_def2 {Ω : Type*} [measurable_space Ω] (A B : event Ω) :
  (A ∩ B).val= A.val ∩ B.val := rfl

/- eand is the intersection of two events. -/
def eand {Ω : Type*} [probability_space Ω] (A B : event Ω) : event Ω :=
  measurable_inter A B

infixr `∧` := eand

/- The weight of the eand of two events is their intersection. -/
@[simp]
lemma eand_val_def {Ω : Type*} [probability_space Ω] (A B : event Ω) :
  (A ∧ B).val = A.val ∩ B.val :=
begin
  refl,
end

/- Event intersection eand is commutative. -/
lemma eand_comm {Ω : Type*} [probability_space Ω] (A B : event Ω) :
  (A ∧ B) = (B ∧ A) :=
begin
  apply event.eq,
  simp [set.inter_comm],
end

/- Event intersection eand is associative. -/
lemma eand_assoc {Ω : Type*} [probability_space Ω] (A B C : event Ω) :
  ((A ∧ B) ∧ C) = (A ∧ (B ∧ C)) :=
begin
  apply event.eq,
  simp [set.inter_assoc],
end

lemma eand_eq_self_of_subset_left {Ω : Type*} [probability_space Ω] (A B : event Ω) :
  (A.val ⊆ B.val) →
  (A ∧ B) = A :=
begin
  intro A1,
  apply event.eq,
  simp,
  apply set.inter_eq_self_of_subset_left,
  exact A1,
end

lemma eand_eq_self_of_subset_right {Ω : Type*} [probability_space Ω] (A B : event Ω) :
  (B.val ⊆ A.val) →
  (A ∧ B) = B :=
begin
  intro A1,
  rw eand_comm,
  apply eand_eq_self_of_subset_left,
  exact A1,
end

lemma Pr_eand_le_left {Ω : Type*} [probability_space Ω] (A B : event Ω) :
  Pr[A ∧ B]≤ Pr[A] :=
begin
  apply event_prob_mono2,
  rw eand_val_def,
  apply set.inter_subset_left,
end

lemma Pr_eand_le_right {Ω : Type*} [probability_space Ω] (A B : event Ω) :
  Pr[A ∧ B]≤ Pr[B] :=
begin
  rw eand_comm,
  apply Pr_eand_le_left,
end

lemma Pr_eand_le_min {Ω : Type*} [probability_space Ω] (A B : event Ω) :
  Pr[A ∧ B]≤ min Pr[A]  Pr[B] :=
begin
  apply le_min,
  { apply Pr_eand_le_left,
  },
  { apply Pr_eand_le_right,
  }
end

/- The union of two events. -/
def measurable_union {Ω : Type*} [measurable_space Ω] (A B : event Ω) : event Ω := {
  val :=A.val ∪  B.val,
  property := measurable_set.union A.property B.property,
}

@[simp]
lemma measurable_union_val_def {Ω : Type*} [measurable_space Ω] (A B : event Ω) :
  (measurable_union A B).val=A.val ∪ B.val := rfl

instance event_has_union {Ω : Type*} [measurable_space Ω] : has_union (event Ω) := {
  union := measurable_union,
}

@[simp]
lemma measurable_union_val_def2 {Ω : Type*} [measurable_space Ω] (A B : event Ω) :
  (A ∪ B).val = A.val ∪ B.val := rfl


/- The "or" of two events is their measurable union. -/
def eor {Ω : Type*} [probability_space Ω] (A B : event Ω) : event Ω := measurable_union A B

infixr `∨` := eor

@[simp]
lemma eor_val_def {Ω : Type*} [probability_space Ω] (A B : event Ω) :
  (A ∨ B).val = A.val ∪ B.val :=
begin
  refl,
end

/- The or of two events eor is commutative. -/
lemma eor_comm {Ω : Type*} [probability_space Ω] (A B : event Ω) :
  (A ∨ B) = (B ∨ A) :=
begin
  apply event.eq,
  simp [set.union_comm],
end

lemma Pr_le_eor_left {Ω : Type*} [probability_space Ω] (A B : event Ω) :
  Pr[A] ≤ Pr[A ∨ B] :=
begin
  apply event_prob_mono2,
  simp,
end

lemma Pr_le_eor_right {Ω : Type*} [probability_space Ω] (A B : event Ω) :
   Pr[B] ≤ Pr[A ∨ B] :=
begin
  rw eor_comm,
  apply Pr_le_eor_left,
end

lemma Pr_le_eor_sum {Ω : Type*} [probability_space Ω] (A B : event Ω) :
  Pr[A ∨ B]≤ Pr[A] + Pr[B] :=
begin
  have A1 : ↑(Pr[A ∨ B])≤ (Pr[A] : ennreal) + (Pr[B] : ennreal),
  { repeat {rw event_prob_def},
    simp,
    apply measure_theory.outer_measure.union,
  },
  have A2 : ↑(Pr[A ∨ B])≤ ((Pr[A] + Pr[B]) : ennreal) → Pr[A ∨ B]≤ Pr[A] + Pr[B],
  { apply to_nnreal_almost_monotonic,
  {   rw event_prob_def,
      apply prob_not_infinite,
    },
  {   apply add_finite,
      rw event_prob_def,
      apply prob_not_infinite,
      rw event_prob_def,
      apply prob_not_infinite,
    }
  },
  apply A2,
  apply A1,
end

lemma Pr_disjoint_eor {Ω : Type*} [probability_space Ω] (A B : event Ω) :
  disjoint A.val B.val →
  Pr[A ∨ B] =  Pr[A] + Pr[B] :=
begin
  intro A1,
  have A2 : ↑(Pr[A ∨ B])= (Pr[A] : ennreal) + (Pr[B] : ennreal),
  { repeat {rw event_prob_def},
    simp,
    apply measure_theory.measure_union,
    apply A1,
    apply A.property,
    apply B.property,
  },
  have A3 : ((Pr[A ∨ B]) : ennreal).to_nnreal= ((Pr[A] : ennreal) + (Pr[B] : ennreal)).to_nnreal,
  { rw A2,
  },
  simp at A3,
  apply A3,
end

/- enot is the complement of an event. -/
def enot {Ω : Type*} [probability_space Ω] (A : event Ω) : event Ω := {
  val :=(A).valᶜ,
  property := measurable_set.compl A.property,
}

prefix `¬ₑ`  : 100 := enot

@[simp]
lemma enot_val_def {Ω : Type*} [probability_space Ω] (A : event Ω) :
  (¬ₑ A).val = (A.val)ᶜ :=
begin
  refl,
end

/- Double negation elimination by the complement of the complement of an event. -/
@[simp]
lemma enot_enot_eq_self {Ω : Type*} [probability_space Ω] (A : event Ω) :
  (¬ₑ (¬ₑ A)) = (A) :=
begin
  apply event.eq,
  simp,
end

instance event_has_compl {α : Type*} [M : measurable_space α] : has_compl (event α) := {
  compl := λ E, ⟨ E.valᶜ, measurable_set.compl E.property⟩,
}

instance has_sdiff.event {α : Type*} [measurable_space α] :
  has_sdiff (event α) := ⟨λ E F, E ∩ Fᶜ⟩


@[simp]
lemma has_sdiff_event_val {α : Type*} [measurable_space α] (E F : event α) :
  (E \ F).val = E.val \ F.val := rfl

instance event_subtype_has_neg {α : Type*} [M : measurable_space α] : has_neg (subtype (@measurable_set α M)) := {
  neg := λ E, ⟨ E.valᶜ, measurable_set.compl E.property⟩,
}

lemma event_neg_def {α : Type*} [M : measurable_space α] {E : event α} :
    Eᶜ = ⟨ E.valᶜ, measurable_set.compl E.property⟩ :=rfl

@[simp]
lemma event_compl_val_def {α : Type*} [M : measurable_space α] {E : event α} :
    (Eᶜ).val = (E.val)ᶜ :=rfl

@[simp]
lemma event_neg_val_def {α : Type*} [M : probability_space α] {E : event α} :
    (Eᶜ).val = (E.val)ᶜ := rfl

@[simp]
lemma em_event {Ω : Type*} [probability_space Ω] (A : event Ω) :
    (A ∨ (¬ₑ A)) = event_univ _ :=
begin
  apply event.eq,
  simp,
end

lemma compl_eor_eq_compl_eand_compl {Ω : Type*} [probability_space Ω] (A B : event Ω) :
  (A ∨ B)ᶜ = (Aᶜ ∧ Bᶜ) := begin
  apply event.eq,
  simp,
end

/- The probability of an event and its complement is 1. -/
lemma Pr_add_enot_eq_1 {Ω : Type*} [probability_space Ω] (A : event Ω) :
  Pr[A] + Pr[¬ₑ A] = 1 :=
begin
  have A1 : disjoint (A.val) (enot A).val,
  { unfold disjoint,
    rw enot_val_def,
    simp,
  },
  have A2 : (A∨ (¬ₑ A)) = event_univ _,
  { apply em_event,
  },
  have A3 : Pr[A∨ (¬ₑ A)] = Pr[event_univ _],
  { rw A2,
  },
  rw Pr_event_univ at A3,
  rw Pr_disjoint_eor at A3,
  apply A3,
  apply A1,
end

end probability_theory
