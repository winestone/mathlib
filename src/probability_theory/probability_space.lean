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
Author: Martin Zinkevich (modified for mathlib by Hunter Monroe and Eric Wieser)
 -/

import measure_theory.measurable_space
import measure_theory.measure_space
import measure_theory.borel_space
import data.equiv.list
import data.equiv.basic
import topology.basic

import probability_theory.measurable_space
import probability_theory.filter
import probability_theory.set
import probability_theory.sum

open set filter classical
open_locale topological_space filter
noncomputable theory

/-! This file defines the basic concepts in probability theory.
    There are four fundamental principles :
    1. Make theorems as readable as possible. Use Pr[A ∧ B], not μ (A ∩ B). Other examples :
       Pr[(X >ᵣ 3) ∨ (Y =ᵣ 7)]. While events are technically sets, in probability theory,
       they are better written as propositions that may or may not hold.
    2. Avoid absurd statements where possible. Don't allow Pr[A] if A is not an event,
       or Pr[X ∈ᵣ S] if S is not measurable, or Pr[∀ᵣ a in S, E a] if S is not countable.
       It is always possible to write Pr[⟨S, ...proof S is an event...⟩].
    3. Embed measurability into the objects and operations themselves. An event is measurable by
       definition. When we take the and, or, not, for all, exists, measurability should be
       automatic.
    4. Don't expect the reader to know measure theory, but at times it may be required by the
       author.
    Several concepts are defined in this module :
      probability_space: a measure_space where the measure has a value of 1.
      event: a subtype of a set that is measurable (defined based upon the measurable space),
      which is an event on a probability space (defined based upon the probability).
      Pr[E]: the probability of an event.
      measurable_fun: a subtype of a function that is measurable (denoted (M₁ →ₘ M₂)).
      random_variable: a measurable_fun whose domain is a probability space (denoted (P →ᵣ M)).
     Also, various independence and identical definitions are specified. Some choices:
     * A and B are independent if A has zero probability.
     * an infinite family of events/random variables is independent if every finite subset
       is independent.
     * Two random variables are identical if they have equal probability on every measurable
       set. The probability spaces on which they are defined need not be equal.
      -/

open measure_theory measurable_space
open_locale big_operators classical

namespace probability_theory

/- A probability space is a measure space with volume one. -/
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

instance {Ω : Type*} [P : probability_space Ω] : has_mem Ω (event Ω) :=
{ mem := event_mem }

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
  {  apply prob_le_1,},
  intro A2,
  rw A2 at A1,
  have A3 : (1 : ennreal)=⊤,
  { apply complete_linear_order.le_antisymm,
  { apply (ennreal.complete_linear_order.le_top),},
  { apply A1,}},
  have A4 : (1 : ennreal) ≠ (⊤ : ennreal),
  { apply ennreal.one_ne_top,},
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

/- Pr[E] is the probability of an event. -/
notation `Pr[`E`]` := event_prob E

lemma event_prob_def {Ω : Type*} [probability_space Ω] (E : event Ω) :
  ↑(Pr[E]) = (volume E.val) := by
begin
  unfold event_prob,
  apply prob_nnreal,
end

lemma to_nnreal_almost_monotonic (a b : ennreal) : (a ≠ ⊤)→(b ≠ ⊤)→(a ≤ b)  →
  (a.to_nnreal ≤ b.to_nnreal) :=
begin
  exact λ (ha : a ≠ ⊤) (hb : b ≠ ⊤), (ennreal.to_real_le_to_real ha hb).mpr
end

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
def event_univ (Ω : Type*) [measurable_space Ω] : event Ω :=
{ val := set.univ,
  property := measurable_set.univ,}

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
def event_empty (Ω : Type*) [measurable_space Ω] : event Ω :=
  { val := ∅,
  property := measurable_set.empty,}

/- There is an empty event. -/
instance has_emptyc_event {Ω : Type*} {M : measurable_space Ω} : has_emptyc (event Ω) :=
  ⟨ @event_empty Ω M ⟩

/- Every probability space has the empty event, corresponding to the empty set. -/
lemma has_emptyc_emptyc_event {Ω : Type*} [probability_space Ω] :
  ∅ = (event_empty Ω) := rfl

/- Every probability space has the empty event, corresponding to the empty set. -/
@[simp]
lemma event_empty_val_def {Ω : Type*} [probability_space Ω] :
  (event_empty Ω).val = ∅ := rfl

/- Every probability space has the empty event, corresponding to the empty set. -/
@[simp]
lemma event_empty_val_def2 {Ω : Type*} [probability_space Ω] :
  (@has_emptyc.emptyc (event Ω) _).val = ∅ := rfl

/- The probability of an empty event is zero. -/
@[simp]
lemma Pr_event_empty {Ω : Type*} [probability_space Ω] :
  Pr[event_empty Ω] = 0 :=
begin
  have A1 : ↑(Pr[event_empty Ω]) = (0 : ennreal),
  rw event_prob_def,
  apply volume.empty,
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

def event_const (Ω : Type*) [probability_space Ω] (P : Prop) : event Ω :=
  { val := {ω : Ω|P},
  property := measurable_set.const P,}

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
def measurable_inter {Ω : Type*} [measurable_space Ω] (A B : event Ω) : event Ω :=
  { val :=A.val ∩ B.val,
  property := measurable_set.inter A.property B.property,}

@[simp]
lemma measurable_inter_val_def {Ω : Type*} [measurable_space Ω] (A B : event Ω) :
  (measurable_inter A B).val= A.val ∩ B.val := rfl

instance event_has_inter {Ω : Type*} [measurable_space Ω] : has_inter (event Ω) :=
{ inter := measurable_inter,}

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
  (A ∧ B).val = A.val ∩ B.val := by refl

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
  { apply Pr_eand_le_left,},
  { apply Pr_eand_le_right,}
end

/- The union of two events. -/
def measurable_union {Ω : Type*} [measurable_space Ω] (A B : event Ω) : event Ω :=
  {  val :=A.val ∪  B.val,
  property := measurable_set.union A.property B.property,}

@[simp]
lemma measurable_union_val_def {Ω : Type*} [measurable_space Ω] (A B : event Ω) :
  (measurable_union A B).val=A.val ∪ B.val := rfl

instance event_has_union {Ω : Type*} [measurable_space Ω] : has_union (event Ω) :=
  { union := measurable_union,}

@[simp]
lemma measurable_union_val_def2 {Ω : Type*} [measurable_space Ω] (A B : event Ω) :
  (A ∪ B).val = A.val ∪ B.val := rfl

/- The "or" of two events is their measurable union. -/
def eor {Ω : Type*} [probability_space Ω] (A B : event Ω) : event Ω := measurable_union A B

infixr `∨` := eor

@[simp]
lemma eor_val_def {Ω : Type*} [probability_space Ω] (A B : event Ω) :
  (A ∨ B).val = A.val ∪ B.val := by refl

/- The or of two events eor is commutative. -/
lemma eor_comm {Ω : Type*} [probability_space Ω] (A B : event Ω) :
  (A ∨ B) = (B ∨ A) :=
begin
  apply event.eq,
  simp [set.union_comm],
end

/- The probability of an event is less than the probability of eor of that event
with another event. -/
lemma Pr_le_eor_left {Ω : Type*} [probability_space Ω] (A B : event Ω) :
  Pr[A] ≤ Pr[A ∨ B] :=
begin
  apply event_prob_mono2,
  simp,
end

/- The probability of an event is less than the probability of eor of that event
with another event. -/
lemma Pr_le_eor_right {Ω : Type*} [probability_space Ω] (A B : event Ω) :
   Pr[B] ≤ Pr[A ∨ B] :=
begin
  rw eor_comm,
  apply Pr_le_eor_left,
end

-- See ennreal.add_eq_top
lemma add_finite (a b : ennreal) : (a≠ ⊤) → (b≠ ⊤) → (a + b≠ ⊤) :=by finish

/- The probability of the eor of two events is less than the sum of their probabilities. -/
lemma Pr_le_eor_sum {Ω : Type*} [probability_space Ω] (A B : event Ω) :
  Pr[A ∨ B]≤ Pr[A] + Pr[B] :=
begin
  have A1 : ↑(Pr[A ∨ B])≤ (Pr[A] : ennreal) + (Pr[B] : ennreal),
  { repeat {rw event_prob_def},
    simp,
    apply measure_theory.outer_measure.union,},
  have A2 : ↑(Pr[A ∨ B])≤ ((Pr[A] + Pr[B]) : ennreal) → Pr[A ∨ B]≤ Pr[A] + Pr[B],
  { apply to_nnreal_almost_monotonic,
  {   rw event_prob_def,
      apply prob_not_infinite,},
  {   apply add_finite,
      rw event_prob_def,
      apply prob_not_infinite,
      rw event_prob_def,
      apply prob_not_infinite,}},
  apply A2,
  apply A1,
end

/- The probability of disjoint events is their sum. -/
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
    apply B.property,},
  have A3 : ((Pr[A ∨ B]) : ennreal).to_nnreal= ((Pr[A] : ennreal) + (Pr[B] : ennreal)).to_nnreal,
    rw A2,
  simp at A3,
  apply A3,
end

/- enot is the complement of an event. -/
def enot {Ω : Type*} [probability_space Ω] (A : event Ω) : event Ω :=
  { val :=(A).valᶜ,
  property := measurable_set.compl A.property,}

prefix `¬ₑ`  : 100 := enot

@[simp]
lemma enot_val_def {Ω : Type*} [probability_space Ω] (A : event Ω) :
  (¬ₑ A).val = (A.val)ᶜ := by refl

/- Double negation elimination by the complement of the complement of an event. -/
@[simp]
lemma enot_enot_eq_self {Ω : Type*} [probability_space Ω] (A : event Ω) :
  (¬ₑ (¬ₑ A)) = (A) :=
begin
  apply event.eq,
  simp,
end

instance event_has_compl {α : Type*} [M : measurable_space α] : has_compl (event α) :=
  { compl := λ E, ⟨ E.valᶜ, measurable_set.compl E.property⟩,}

/- Set difference is defined for events. -/
instance has_sdiff.event {α : Type*} [measurable_space α] :
  has_sdiff (event α) := ⟨λ E F, E ∩ Fᶜ⟩

@[simp]
lemma has_sdiff_event_val {α : Type*} [measurable_space α] (E F : event α) :
  (E \ F).val = E.val \ F.val := rfl

instance event_subtype_has_neg {α : Type*} [M : measurable_space α] : has_neg (subtype
  (@measurable_set α M)) := { neg := λ E, ⟨ E.valᶜ, measurable_set.compl E.property⟩,}

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

/- The complement of the or is the and of the complements. -/
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
    simp,},
  have A2 : (A∨ (¬ₑ A)) = event_univ _,
  { apply em_event,},
  have A3 : Pr[A∨ (¬ₑ A)] = Pr[event_univ _],
    rw A2,
  rw Pr_event_univ at A3,
  rw Pr_disjoint_eor at A3,
  apply A3,
  apply A1,
end

lemma nnreal_add_sub_right (a b c:nnreal) : a + b = c → c - b = a :=
begin
  intro A1,
  have A2:(a + b) - b = a,
    apply nnreal.add_sub_cancel,
  rw A1 at A2,
  exact A2,
end

lemma nnreal_add_sub_left (a b c:nnreal):a + b = c → c - a = b :=
begin
  intro A1,
  apply nnreal_add_sub_right,
  rw nnreal.comm_semiring.add_comm,
  exact A1,
end

lemma Pr_one_minus_eq_not {Ω:Type*} {p:probability_space Ω} (A:event Ω):
  1 - Pr[A] = Pr[¬ₑ A] :=
begin
  apply nnreal_add_sub_left,
  apply Pr_add_enot_eq_1,
end

lemma Pr_one_minus_not_eq {Ω:Type*} {p:probability_space Ω} (A:event Ω):
  1 - Pr[enot A] = Pr[A] :=
begin
  apply nnreal_add_sub_right,
  apply Pr_add_enot_eq_1,
end

lemma nnreal_le_sub_add {a b c:nnreal}:b ≤ c → c ≤ a →
a ≤ a - b + c :=
begin
  repeat {rw ← nnreal.coe_le_coe},
  repeat {rw nnreal.coe_add},
  intros A1 A2,
  repeat {rw nnreal.coe_sub},
  linarith,
  apply le_trans A1 A2,
end

lemma nnreal_le_sub_add' {a b:nnreal}:a ≤ a - b + b :=
begin
  cases decidable.em (b ≤ a),
  { apply nnreal_le_sub_add,
    apply le_refl _,
    apply h },
  { have h2:a≤ b,
    { apply le_of_not_ge h }, rw nnreal.sub_eq_zero,
    rw zero_add,
    apply h2,
    apply h2 },
end

lemma Pr_not_ge_of_Pr_le {Ω:Type*} {p:probability_space Ω} (A:event Ω) (δ:nnreal):
  Pr[A] ≤ δ → Pr[¬ₑ A] ≥ 1 - δ :=
begin
  intros h1,
  rw ← Pr_one_minus_eq_not,
  simp,
  have h2:1 - Pr[A] + Pr[A] ≤ 1 - Pr[A] + δ,
  { apply add_le_add,
    apply le_refl _,
    apply h1 },
  apply le_trans _ h2,
  apply nnreal_le_sub_add',
end

lemma em_event_cond {Ω:Type*} {p:probability_space Ω} (A B:event Ω):
  ((A ∧ B) ∨ (A ∧ ¬ₑ B)) = A :=
begin
  apply event.eq,
  simp [set.inter_union_compl],
end

lemma Pr_em {Ω:Type*} {p:probability_space Ω} (A B:event Ω):
  Pr[A ∧ B] + Pr[A ∧ ¬ₑ B] = Pr[A] :=
begin
  rw ← Pr_disjoint_eor,
  rw em_event_cond,
  simp [set.disjoint_inter_compl],
end

lemma Pr_diff {Ω:Type*} {p:probability_space Ω} (A B:event Ω):
    A.val ⊆ B.val →
    Pr[B ∧ ¬ₑ A] = Pr[B] - Pr[A] :=
begin
  intro A1,
  have A2:Pr[B ∧ A] + Pr[B ∧ ¬ₑ A] = Pr[B],
    apply Pr_em,
  have A3:(B ∧ A) = A,
    apply eand_eq_self_of_subset_right,
    apply A1,
  rw A3 at A2,
  symmetry,
  apply nnreal_add_sub_left,
  exact A2,
end

/- TODO remove duplicate definition of measurable_set as subtype -/
def measurable_setB {α:Type*} (M:measurable_space α):Type* := subtype (M.measurable_set')

def measurable_setB.mk {α:Type*} {M:measurable_space α} {S:set α}
  (H:measurable_set S):measurable_setB M := ⟨S, H⟩

def measurable_setB.sdiff {Ω:Type*} {M:measurable_space Ω} (A B:measurable_setB M) :
  measurable_setB M := @measurable_setB.mk _ _ (A.val \ B.val)
begin
  apply measurable_set.diff,
  apply A.property,
  apply B.property
end

instance measurable_setB.has_sdiff {Ω:Type*} {M:measurable_space Ω} :has_sdiff
  (measurable_setB M) := ⟨measurable_setB.sdiff⟩

@[simp]
lemma measurable_setB.sdiff_val_def {Ω:Type*} {M:measurable_space Ω} (A B:measurable_setB M):
  (A \ B).val = A.val \ B.val := rfl

instance measurable_setB_has_union {Ω:Type*} {p:measurable_space Ω}:has_union
  (measurable_setB p) := { union := @measurable_union Ω p,}

def measurable_setB.symm_diff {Ω:Type*} {M:measurable_space Ω} (A B:measurable_setB M) :
  measurable_setB M := (A \ B) ∪ (B \ A)

instance measurable_setB.has_symm_diff {Ω:Type*} {M:measurable_space Ω}:has_symm_diff
  (measurable_setB M) := ⟨measurable_setB.symm_diff⟩

lemma measurable_setB.has_symm_diff.def {Ω : Type*} {M:measurable_space Ω}
{A B:measurable_setB M}:A ∆ B = (A \ B) ∪ (B \ A) := rfl

@[simp]
lemma measurable_setB.symm_diff_val_def {Ω:Type*} {M:measurable_space Ω} (A B:measurable_setB M):
  (A ∆ B).val = A.val ∆ B.val := rfl

/- Define the equivalance of two events. -/
def event_eqv {Ω:Type*} {p:probability_space Ω} (A B:event Ω):event Ω :=
    (A ∧ B) ∨ ((¬ₑ A) ∧ (¬ₑ B))

infixr `=ₑ`:100 := event_eqv

lemma event_eqv_def {Ω:Type*} {p:probability_space Ω} (A B:event Ω):
    (A =ₑ B) = ((A ∧ B) ∨ ((¬ₑ A) ∧ (¬ₑ B))) := rfl

lemma eor_partition {Ω:Type*} {p:probability_space Ω} (A B:event Ω):
  (A ∨ B) = ((A ∧ ¬ₑ B) ∨  (A ∧ B)  ∨ (¬ₑ A ∧ B)) :=
begin
  apply event.eq,
  simp,
  ext ω,split;intros A1;simp at A1;simp [A1],
    cases A1 with A1 A1; simp [A1],
    rw or_comm,
    apply classical.em,
    apply classical.em,
    cases A1 with A1 A1,
    simp [A1],
    cases A1 with A1 A1,
    simp [A1],
    simp [A1],
end

lemma Pr_eor_partition {Ω:Type*} {p:probability_space Ω} (A B:event Ω):
  Pr[A ∨ B] = Pr[A ∧ ¬ₑ B] + Pr[A ∧ B] + Pr[¬ₑ A ∧ B] :=
begin
  rw eor_partition A B,
  rw Pr_disjoint_eor,
  rw Pr_disjoint_eor,
  ring,
  simp,
  rw set.disjoint_left,
  intros ω A1,
  simp at A1,
  simp [A1],
  simp,
  split;
  {rw set.disjoint_left,
  intros ω A1,
  simp at A1,
  simp [A1]},
end

lemma Pr_eor_plus_eand {Ω:Type*}  {p:probability_space Ω} (A B:event Ω):
  Pr[A ∨ B] + Pr[A ∧ B] = (Pr[A] + Pr[B]) :=
begin
  rw ← Pr_em A B,
  rw ← Pr_em B A,
  rw eand_comm B A,
  rw eand_comm B (¬ₑ A),
  rw Pr_eor_partition A B,
  ring,
end

lemma Pr_eor_eq_minus_eand {Ω:Type*}  {p:probability_space Ω} (A B:event Ω):
  Pr[A ∨ B] = (Pr[A] + Pr[B])  - Pr[A ∧ B] :=
begin
  rw ← Pr_eor_plus_eand,
  rw nnreal.add_sub_cancel,
end

lemma Pr_eor_eq_minus_eand_real {Ω:Type*}  {p:probability_space Ω} (A B:event Ω):
  (Pr[A ∨ B]:real) = (Pr[A]:real) + (Pr[B]:real)  - (Pr[A ∧ B]:real) :=
begin
  have A1:Pr[A ∨ B] + Pr[A ∧ B] = (Pr[A] + Pr[B]),
  {apply Pr_eor_plus_eand},
  rw ← nnreal.coe_eq at A1,
  repeat {rw nnreal.coe_add at A1},
  linarith,
end

def measurable_setB.Inter {Ω β:Type*} {M:measurable_space Ω} [encodable β]
  (A:β → measurable_setB M):measurable_setB M := { val:=(⋂ b:β, (A b).val),
  property := measurable_set.Inter (λ b:β, (A b).property),}

def eall_encodable {Ω β:Type*} {p:probability_space Ω} [encodable β] (A:β → event Ω):event Ω :=
  { val:=(⋂ b:β, (A b).val),
  property := measurable_set.Inter (λ b:β, (A b).property),}

/- The definition of has_eall.eall_val enforces that the eall function implements intersection.
The proof of measurability is left to the implementer. -/
@[class]
structure has_eall (Ω β:Type*) (p:probability_space Ω) :=
  (eall:(β → event Ω) → event Ω)
  (eall_val:∀ (f:β → event Ω), (⋂ (b:β), (f b).val) = (eall f).val)

/- ∀ᵣ is enforced to be intersection. -/
notation `∀ᵣ` binders `, ` r:(scoped f, has_eall.eall f) := r


@[class]
structure has_eall_in (Ω β γ:Type*) (p:probability_space Ω) :=
  (eall_in:γ → (β → event Ω) → event Ω)
  (as_set:γ → (set β))
  (eall_in_val:∀ (g:γ) (f:β → event Ω), (⋂ b ∈ (as_set g), (f b).val) = (eall_in g f).val)

notation `∀ᵣ` binders  ` in `  A, r:(scoped f, has_eall_in.eall_in A f) := r

instance has_eall_encodable {Ω β:Type*} {p:probability_space Ω} [encodable β]:has_eall Ω β p :=
  { eall := λ (A:β → event Ω), eall_encodable A,
  eall_val := begin
    simp [eall_encodable],
  end,}

notation `∀ᵣ` binders `, ` r:(scoped f, has_eall.eall f) := r

@[simp]
lemma eall_val_def {Ω β:Type*} {p:probability_space Ω} [encodable β] (A:β → event Ω):
  (eall_encodable A).val = (⋂ b:β, (A b).val) := rfl

lemma eall_binder_def {Ω β:Type*} {p:probability_space Ω} [encodable β] (A:β → event Ω):
  (∀ᵣ x, A x) = (eall_encodable A):= rfl

@[simp]
lemma eall_binder_val_def {Ω β:Type*} {p:probability_space Ω} [encodable β] (A:β → event Ω):
  (∀ᵣ x, A x).val = (⋂ b:β, (A b).val) := rfl

def to_set_of_sets {Ω:Type*} {p:probability_space Ω} (A:set (event Ω)):set (set Ω) :=
  (set.image (λ a:event Ω, a.val) A)

lemma all_measurable_to_set_of_sets {Ω:Type*} {p:probability_space Ω} (A:set (event Ω))
  (a∈ (to_set_of_sets A)):measurable_set a :=
begin
  unfold to_set_of_sets at H,
  simp at H,
  cases H with x H,
  cases H with A1 A2,
  subst a,
  exact x.property,
end

lemma countable_to_set_of_sets {Ω:Type*} {p:probability_space Ω} {A:set (event Ω)}:
  (set.countable A)→ (set.countable (to_set_of_sets A)) :=
begin
  unfold to_set_of_sets,
  intro A1,
  apply set.countable.image,
  apply A1,
end

def eall_set {Ω:Type*} {p:probability_space Ω} (A:set (event Ω)) (cA:set.countable A):event Ω:=
{ val:=set.sInter (to_set_of_sets A),
  property:=measurable_set.sInter (countable_to_set_of_sets cA) (all_measurable_to_set_of_sets A),}

def eall_finset_val {Ω β:Type*} {p:probability_space Ω} (S:finset β)
  (A:β → event Ω):set Ω :=  ⋂ s∈ S, (A s).val

lemma eall_finset_val_measurable {Ω β:Type*} {p:probability_space Ω} (S:finset β)
  (A:β → event Ω):measurable_set (eall_finset_val S A) :=
begin
  unfold eall_finset_val,
  apply finset_inter_measurable,
  intros,
  apply (A t).property,
end

def eall_finset {Ω β:Type*} {p:probability_space Ω}
  (S:finset β)
  (A:β → event Ω):event Ω :=
  { val:=eall_finset_val S A,
    property:=eall_finset_val_measurable S A,}

instance has_eall_in.finset {Ω β:Type*} {p:probability_space Ω}:has_eall_in Ω β (finset β) p :=
{ eall_in := (λ S f, eall_finset S f),
  as_set := (λ (S:finset β), ↑S),
  eall_in_val := begin
    simp [eall_finset, eall_finset_val],
  end}


@[simp]
lemma eall_finset_val_def {Ω β:Type*} {p:probability_space Ω}
  (S:finset β) (A:β → event Ω):(eall_finset S A).val = ⋂ s∈ S, (A s).val := rfl

lemma has_eall_in_finset_def {Ω β:Type*} {p:probability_space Ω}
  (S:finset β) (A:β → event Ω):
  (∀ᵣ s in S, A s) = (eall_finset S A) := rfl



@[simp]
lemma has_eall_in_finset_val_def {Ω β:Type*} {p:probability_space Ω}
  (S:finset β) (A:β → event Ω):
  (∀ᵣ s in S, A s).val = ⋂ s∈ S, (A s).val := rfl

@[simp]
lemma has_eall_in_finset_val_def2 {Ω β:Type*} {p:probability_space Ω} {S:finset β} {A:β → event Ω}:
  (has_eall_in.eall_in S A).val = ⋂ s∈ S, (A s).val := rfl

@[simp]
lemma has_eall_in_finset_val_def3 {Ω β:Type*} {p:probability_space Ω} {S:finset β} {A:β → event Ω}:
  @has_coe.coe (event Ω) (set Ω) (coe_subtype) (has_eall_in.eall_in S A) = ⋂ s∈ S, (A s).val := rfl

def eall_fintype {Ω β:Type*} {p:probability_space Ω}
  (F:fintype β) (A:β → event Ω):event Ω := eall_finset finset.univ A

instance has_eall.fintype {Ω β:Type*} {p:probability_space Ω} [F:fintype β]:has_eall Ω β p :=
{ eall := (λ A, eall_fintype F A),
  eall_val := by simp [eall_fintype],}

lemma eall_fintype_eq_eall_finset {Ω β:Type*} {p:probability_space Ω}
  [F:fintype β] (A:β → event Ω):(∀ᵣ b, A b) = eall_finset finset.univ A := rfl

lemma eall_fintype_def {Ω β:Type*} {p:probability_space Ω} (F:fintype β) {A:β → event Ω}:
  (eall_fintype F A) = (∀ᵣ b, A b) := rfl

@[simp]
lemma eall_fintype_val_def {Ω β:Type*} {p:probability_space Ω}
  (F:fintype β) (A:β → event Ω):(eall_fintype F A).val = ⋂ (s:β), (A s).val :=
begin
  unfold eall_fintype,
  simp,
end

def measurable_Union {Ω β:Type*} {p:measurable_space Ω} [encodable β] (A:β → measurable_setB p):
  measurable_setB p :=
{ val:=(⋃ b:β, (A b).val),
  property := measurable_set.Union (λ b:β, (A b).property),}

@[simp]
lemma measurable_Union_val_def {Ω β:Type*} {p:measurable_space Ω} [E:encodable β]
    (A:β → measurable_setB p):
    (@measurable_Union Ω β p E A).val = (⋃ b:β, (A b).val) := rfl


def eany {Ω β:Type*} {p:probability_space Ω} [encodable β] (A:β → event Ω):event Ω :=
  measurable_Union A

lemma measurable_Union_eq_any {Ω β:Type*}
    {p:probability_space Ω} [E:encodable β] (A:β → event Ω):
    measurable_Union A = eany A := rfl

lemma sum_subst {β:Type*} [encodable β] {f g:β → ennreal}:(f = g) →
    (tsum f) = (tsum g) :=
begin
  intro A1,
  rw A1,
end

lemma Pr_measurable_Union_sum_dummy {Ω β:Type*} [M:probability_space Ω]
    [E:encodable β]
    (A:β → set Ω):(∀ (i j:β), i ≠ j →
    (A i ∩ A j = ∅))→
    (∀ i, measurable_set (A i)) →
    ((@measure_theory.measure_space.volume Ω (probability_space.to_measure_space))
      (⋃ (n:β), A n)) =
    (∑' (i:β), (@measure_theory.measure_space.volume Ω (probability_space.to_measure_space))
      (A i)) :=
begin
  intros A1 A3,
  rw measure_theory.measure_Union,
  { intros i j A2,
    simp,
    unfold disjoint function.on_fun,
    simp,
    rw set.subset_empty_iff,
    apply A1 i j A2,},
  { apply A3,},
end

lemma measure_eq_measure {Ω:Type*} [P:probability_space Ω] {S:set Ω}:
  measure_theory.measure_space.volume.to_outer_measure.measure_of S =
  (@measure_theory.measure_space.volume Ω (probability_space.to_measure_space)) S := rfl

@[simp]
lemma eany_val_def {Ω β:Type*} {p:probability_space Ω} [encodable β]
  (A:β → event Ω):(eany A).val=(⋃ b:β, (A b).val) := rfl

@[class]
structure has_eany (Ω β:Type*) (p:probability_space Ω) :=
  (eany:(β → event Ω) → event Ω)
  (eany_val:(∀ (f:β → event Ω), ((⋃ b, (f b).val) = (eany f).val)))

notation `∃ᵣ ` binders `, ` r:(scoped f, has_eany.eany f) := r

@[class]
structure has_eany_in (Ω β γ:Type*) (p:probability_space Ω) :=
  (eany_in:γ → (β → event Ω) → event Ω)
  (as_set:γ → (set β))
  (eany_in_val:∀ (g:γ) (f:β → event Ω), (⋃ b ∈ (as_set g), (f b).val) = (eany_in g f).val)

notation `∃ᵣ ` binders  ` in ` S `, ` r:(scoped f, has_eany_in.eany_in S f) := r

instance has_eany.encodable {Ω β:Type*} {p:probability_space Ω} [E:encodable β]:has_eany Ω β p :=
{ eany := (λ A:β → (event Ω), eany A),
  eany_val := by simp}

lemma eany_encodable_notation_def {Ω β:Type*} {p:probability_space Ω} [encodable β]
  (A:β → event Ω):(∃ᵣ a, A a) = (eany A) := rfl

@[simp]
lemma eany_encodable_val_def {Ω β:Type*} {p:probability_space Ω} [encodable β]
  (A:β → event Ω):(∃ᵣ a, A a).val = (⋃ (b:β), (A b).val) := begin
  rw eany_encodable_notation_def,
  refl
end

def eany_finset_val {Ω β:Type*} {p:probability_space Ω} (S:finset β)
  (A:β → event Ω):set Ω :=  ⋃ s∈ S, (A s).val

lemma eany_finset_val_measurable {Ω β:Type*} {p:probability_space Ω} (S:finset β)
  (A:β → event Ω):measurable_set (eany_finset_val S A) :=
begin
  unfold eany_finset_val,
  apply finset_union_measurable,
  intros,
  apply (A t).property,
end

def eany_finset {Ω β:Type*} {p:probability_space Ω} (S:finset β) (A:β → event Ω):event Ω :=
  { val:=eany_finset_val S A,
    property:=eany_finset_val_measurable S A,}

instance has_eany_in.finset {Ω β:Type*} {p:probability_space Ω}:has_eany_in Ω β (finset β) p :=
{ eany_in := (λ (S:finset β) (A:β → (event Ω)), eany_finset S A),
  as_set := (λ (S:finset β), ↑S),
  eany_in_val := begin
    simp [eany_finset, eany_finset_val],
  end}

@[simp]
lemma eany_finset_val_def {Ω β:Type*} {p:probability_space Ω} (S:finset β)
  (A:β → event Ω):(eany_finset S A).val = ⋃ s∈ S, (A s).val := rfl

lemma eany_in_finset_def {Ω β:Type*} {p:probability_space Ω} {S:finset β} (A:β → event Ω):
  (∃ᵣ s in S, A s) = eany_finset S A := rfl

@[simp]
lemma eany_in_finset_val_def {Ω β:Type*} {p:probability_space Ω} {S:finset β} (A:β → event Ω):
  (∃ᵣ s in S, A s).val = ⋃ s∈ S, (A s).val := rfl

def eany_fintype {Ω β:Type*} {p:probability_space Ω}
  (F:fintype β) (A:β → event Ω):event Ω := eany_finset finset.univ A

lemma eany_fintype_def {Ω β:Type*} {p:probability_space Ω}
  (F:fintype β) (A:β → event Ω):eany_fintype F A = eany_finset finset.univ A := rfl

instance has_eany.fintype {Ω β:Type*} {p:probability_space Ω} [F:fintype β]:has_eany Ω β p :=
{ eany := (λ  (A:β → (event Ω)), eany_fintype F A),
  eany_val := by simp [eany_fintype],}

lemma has_eany_fintype_def {Ω β:Type*} {p:probability_space Ω} [F:fintype β] {A:β→ event Ω}:
  (∃ᵣ s, A s) = (eany_fintype F A) := rfl

@[simp]
lemma has_eany_fintype_val_def {Ω β:Type*} {p:probability_space Ω} [F:fintype β] {A:β→ event Ω}:
  (∃ᵣ s, A s).val = ⋃ (s:β), (A s).val :=
begin
  rw [has_eany_fintype_def,eany_fintype_def],
  simp,
end

lemma eany_eq_eany_fintype {Ω β:Type*} {p:probability_space Ω}
  (F:fintype β) (E:encodable β) (A:β → event Ω):
  eany A = eany_fintype F A := begin
  apply event.eq,
  rw ← has_eany_fintype_def,
  simp,
end

@[simp]
lemma exists_empty {α Ω:Type*} {P:probability_space Ω} (f:α → event Ω):
  (∃ᵣ a in (∅:finset α), f a) = (∅:event Ω) :=
begin
  apply event.eq,
  simp,
end

/- TODO type mismatch
@[simp]
lemma eall_finset_empty {Ω β:Type*} {p:probability_space Ω}
  (A:β → event Ω): (∀ᵣ s in (∅:finset β), A s) = event_univ :=
begin
  apply event.eq,
  simp,
end
-/

lemma eany_finset_insert {Ω β:Type*} [D:decidable_eq β] {p:probability_space Ω}
  {S:finset β} {A:β → event Ω} {a:β}:
  (∃ᵣ (a':β) in (insert a S), A a') = ((A a) ∨ (∃ᵣ a' in S, A a')) :=
begin
  apply event.eq,
  simp,
end

lemma eall_finset_insert {Ω β:Type*} [D:decidable_eq β] {p:probability_space Ω}
  {S:finset β} {A:β → event Ω} {a:β}:
  (∀ᵣ (a':β) in (insert a S), A a') = ((A a) ∧ (∀ᵣ a' in S, A a')) :=
begin
  apply event.eq,
  simp,
end

lemma eany_finset_bound {Ω β:Type*} [D:decidable_eq β]
  {p:probability_space Ω}
  (S:finset β) (A:β → event Ω):Pr[∃ᵣ a in S, A a] ≤ finset.sum S (λ a:β, Pr[A a]) :=
begin
  apply finset.induction_on S,
  { simp,},
  { intros a S2 A1 A2,
    rw finset.sum_insert A1,
    rw eany_finset_insert,
    apply le_trans,
    apply Pr_le_eor_sum,
    apply add_le_add_left,
    apply A2,}
end

lemma eany_fintype_bound {Ω β:Type*} [D:decidable_eq β] {p:probability_space Ω}
  [F:fintype β] (A:β → event Ω):Pr[∃ᵣ (s:β), A s] ≤  ∑' a:β, Pr[A a] :=
begin
  rw tsum_fintype,
  apply eany_finset_bound,
end

lemma finset_sum_le2 {α β:Type*} [decidable_eq α]
    [ordered_add_comm_monoid β] {S:finset α} {f g:α → β}:
  (∀ s∈ S, f s ≤ g s) →  S.sum f ≤ S.sum g :=
begin
  apply finset.induction_on S,
  { intros A1,
    simp,},
  { intros a S2 A1 A2 A3,
    rw finset.sum_insert,
    rw finset.sum_insert,
    apply add_le_add,
    apply A3,
    simp,
    apply A2,
    { intros a2 A4,
      apply A3,
      simp,
      right,
      exact A4,},
    exact A1,
    exact A1,}
end

/- TODO change nsmul to nsmul_rec -/
infix ` •ℕ `:70 := nsmul

/- TODO this notation has been phased out  -/
lemma nnreal_add_monoid_smul_def{n:ℕ} {c:nnreal}:  n •ℕ c = ↑(n) * c :=
begin
  induction n,
  { simp,},
  { simp,}
end

/- TODO add_monoid.smul (card S) k = ↑(card S) * k -/
lemma finset_sum_le_const {α:Type*} [D:decidable_eq α] {S:finset α} {f:α → nnreal} {k:nnreal}:
  (∀ s∈ S, f s ≤ k) →  S.sum f ≤ S.card  * k :=
begin
  have A1:S.sum (λ s, k) = S.card * k,
  { rw finset.sum_const,
    apply nnreal_add_monoid_smul_def,},
  intro A2,
  rw ← A1,
  apply finset_sum_le2,
  intros s A4,
  apply A2,
  apply A4,
end

/- TODO does this belong here? -/
noncomputable def classical.decidable_eq (β:Type*):decidable_eq β:=
  (λ b c:β, classical.prop_decidable (b=c))

lemma eany_fintype_bound2 {Ω β:Type*} {p:probability_space Ω}
  (F:fintype β) (A:β → event Ω) (k:nnreal):
  (∀ a:β, Pr[A a]≤ k) →
  Pr[∃ᵣ (s:β), A s] ≤ (fintype.card β) * k :=
begin
  intro A1,
  have A2:decidable_eq β := classical.decidable_eq β,
  apply le_trans,
  apply @eany_fintype_bound Ω β A2,
  rw tsum_fintype,
  unfold fintype.card,
  apply @finset_sum_le_const β A2,
  intros s A3,
  apply A1,
end

/- Two events are independent if their joint probability is the product of their
probabilities. -/
def independent_event_pair {Ω:Type*} {p:probability_space Ω} (A B:event Ω):Prop :=
  --(event_prob (eand A B)) = (event_prob A) * (event_prob B)
  Pr[ A ∧ B] = Pr[A] * Pr[B]

def independent_events {Ω β:Type*} {p:probability_space Ω}
  (A:β → event Ω):Prop :=
  ∀ (S:finset β), (finset.prod S (λ b, Pr[A b])) = Pr[∀ᵣ s in S, A s]

def events_IID {Ω β:Type*} {p:probability_space Ω}
  (A:β → event Ω):Prop :=
  independent_events A ∧ (∀ x y:β, Pr[A x] = Pr[A y])

lemma events_IID_pow {Ω : Type*} {p : probability_space Ω} {β : Type*}
  [I:inhabited β] (A:β → event Ω) (S:finset β):
  events_IID A → Pr[eall_finset S A] = Pr[A I.default]^(S.card) :=
begin
  intros A1,
  unfold events_IID at A1,
  cases A1 with A2 A3,
  unfold independent_events at A2,
  have A4:(finset.prod S (λ b, Pr[A b])) = Pr[eall_finset S A],
  { apply A2,},
  rw ← A4,
  have A5:(λ (b : β), Pr[A b]) = (λ (b:β), Pr[A (inhabited.default β)]),
  { ext b,
    rw A3,},
  rw A5,
  apply finset.prod_const,
end

@[simp]
lemma forall_fintype_val {α Ω:Type*} {P:probability_space Ω} (f:α → event Ω) [F:fintype α]:
  (∀ᵣ a, f a).val = ⋂ (a:α), (f a).val := begin
  rw ← eall_fintype_def,
  simp,
end

lemma exists_not_eq_not_forall {α Ω:Type*} {P:probability_space Ω} (f:α → event Ω) {S:finset α}:
  (∃ᵣ a in S, ¬ₑ(f a)) = ¬ₑ (∀ᵣ a in S, f a) :=
begin
  apply event.eq,
  simp,
  rw set.Union_eq_comp_Inter_comp,
  simp,
end

lemma not_forall_not_eq_exists {α Ω:Type*} {P:probability_space Ω} (f:α → event Ω) {S:finset α}:
  ¬ₑ (∀ᵣ a in S, ¬ₑ f a) = (∃ᵣ a in S, f a) :=
begin
  apply event.eq,
  simp,
  rw set.Union_eq_comp_Inter_comp,
  simp,
end

lemma not_forall_not_eq_exists' {α Ω:Type*} {P:probability_space Ω} (f:α → event Ω) [fintype α]:
  ¬ₑ (∀ᵣ a, ¬ₑ f a) = (∃ᵣ a, f a) :=
begin
  apply event.eq,
  simp,
  rw set.Union_eq_comp_Inter_comp,
end

lemma not_exists_eq_forall_not {α Ω:Type*} {P:probability_space Ω} (f:α → event Ω) {S:finset α}:
 ¬ₑ (∃ᵣ a in S, (f a)) = (∀ᵣ a in S, ¬ₑ (f a)) :=
begin
  apply event.eq,
  simp,
end

@[simp]
lemma forall_singleton {α Ω:Type*} {P:probability_space Ω} (f:α → event Ω) {x:α}:
  (∀ᵣ a in ({x}:finset α), f a) = f x :=
begin
  apply event.eq,
  simp,
end

@[simp]
lemma exists_singleton {α Ω:Type*} {P:probability_space Ω} (f:α → event Ω) {x:α}:
  (∃ᵣ a in ({x}:finset α), f a) = f x :=
begin
  apply event.eq,
  simp,
end

@[simp]
lemma distrib_exists_and {α Ω:Type*} {P:probability_space Ω} (f:α → event Ω) {S:finset α}
  {A:event Ω}: (∃ᵣ a in S, A ∧ (f a))  =   (A ∧ (∃ᵣ a in S, f a)) :=
begin
  apply event.eq,
  simp,
  ext ω,split;intros A1;simp at A1;simp [A1],
  cases A1 with i A1,
  simp [A1],
  apply exists.intro i,
  simp [A1],
end

lemma finset.pair_erase {α:Type*} {x y:α} [decidable_eq α]:x ≠ y → ({x, y}:finset α).erase
  x  = {y} :=
begin
  intros A1,
  rw finset.erase_insert,
  simp [A1],
end

lemma finset.singleton_erase {α:Type*} {x:α} [decidable_eq α]:({x}:finset α).erase x = ∅ :=
begin
  have A1:{x} = insert x (∅:finset α),
  {simp},
  rw A1,
  rw finset.erase_insert,
  simp,
end

lemma finset.union_erase {α:Type*} {S T:finset α} {x:α} [decidable_eq α]:
  (S ∪ T).erase x = (S.erase x) ∪ (T.erase x) :=
begin
  ext a;split;intros A1;simp at A1;simp,
  {simp [A1]},
  {cases A1;simp [A1]},
end

lemma finset.image_sum {α β:Type*} [add_comm_monoid β] [decidable_eq α] {S:finset α} {f:α → β}
  {g:α → α} : (∀ (s t:α),s∈ S → t∈ S→ s ≠ t → g s ≠ g t) →  (finset.image g S).sum f =
  S.sum (f ∘ g) :=
begin
  apply finset.induction_on S,
  { intros A1,
    refl,},
  { intros a s B1 B2 B3,
    simp,
    rw finset.sum_insert,
    rw finset.sum_insert,
    rw B2,
    intros s' t' B4 B5 B6,
    apply B3,
    {simp [B4]},
    {simp [B5]},
    apply B6,
    apply B1,
    intro B4,
    simp at B4,
    cases B4 with u B4,
    apply B3 u a,
    {simp [B4]},
    {simp},
    intro B5,
    subst u,
    apply B1,
    {simp [B4]},
    {simp [B4]},},
end

lemma finset.powerset_sum {α β:Type*} [add_comm_monoid β][decidable_eq α] {x:α} {S:finset α}
  (f:finset α → β) : (x ∉ S) → ((insert x S).powerset.erase ∅).sum f = (S.powerset.erase ∅).sum f
  + (S.powerset).sum (f ∘ (insert x)) :=
begin
  intros A0,
  rw finset.powerset_insert,
  rw finset.union_erase,
  rw finset.sum_union,
  have A1:((finset.image (insert x) S.powerset).erase ∅).sum f =
          (finset.image (insert x) S.powerset).sum f,
  {have A1A:((finset.image (insert x) S.powerset).erase ∅) =
          (finset.image (insert x) S.powerset),
   { rw finset.ext_iff,
     intros T;split;intros A1A1;simp at A1A1,
     { simp,cases A1A1 with A1A1 A1A2,
       cases A1A2 with U A1A2,
       apply exists.intro U,
       apply A1A2,},
     simp,
     split,
     {cases A1A1 with U A1A1,intros A1,subst T,simp at A1A1,apply A1A1},
     {apply A1A1},},
   rw A1A,},
  rw A1,
  have B1:(finset.image (insert x) S.powerset).sum f =
          S.powerset.sum (f ∘ (insert x)),
  {  apply @finset.image_sum (finset α) β,
     intros s t B1A B1B B1C B1D,
     apply B1C,
     simp at B1A,
     simp at B1B,
     rw finset.subset_iff at B1B,
     rw finset.subset_iff at B1A,
     rw finset.ext_iff at B1D,
     rw finset.ext_iff,
     intros a;split;intros B1F,
     { have B1G:a ∈ insert x s,
       {simp [B1F] },
       have B1H := (B1D a).mp B1G,
       simp at B1H,
       cases B1H,
       subst a,
       exfalso,
       apply A0,
       apply B1A,
       apply B1F,
       apply B1H,},
     { have B1G:a ∈ insert x t,{simp [B1F]},
       have B1H := (B1D a).mpr B1G,
       simp at B1H,
       cases B1H,
       subst a,
       exfalso,
       apply A0,
       apply B1B,
       apply B1F,
       apply B1H,},},
  rw B1,
  rw finset.disjoint_left,
  intros T A2,
  simp at A2,
  simp,
  intros A3 U A5 A6,
  subst T,
  apply A0,
  cases A2 with A2 A7,
  rw finset.subset_iff at A7,
  apply A7,
  simp,
end

lemma distrib_forall_eand {α Ω:Type*} {P:probability_space Ω} (f:α → event Ω) [decidable_eq α]
  {S:finset α} (A:event Ω):S.nonempty → (∀ᵣ a in S, A ∧ f a) = (A ∧ (∀ᵣ a in S, f a)) :=
begin
  intros A1,
  apply event.eq,
  simp,ext ω,split;intros A2;simp at A2;simp [A2],
  {have A3:=finset.nonempty.bex A1,
   cases A3 with a A3,
   have A4 := A2 a A3,
   simp [A4],
   intros b A5,
   apply (A2 b A5).right,},
 { apply A2.right,},
end

/- TODO uncomment
lemma Pr_exists_eq_powerset {α Ω:Type*} {P:probability_space Ω} (f:α → event Ω) [decidable_eq α]
  {S:finset α}:  (Pr[(∃ᵣ a in S, (f a))]:real) = -(S.powerset.erase ∅).sum  (λ T:finset α,
  (Pr[∀ᵣ a in T, f a]:real) *  (-1)^(T.card)) :=
begin
  revert f,
  apply finset.case_strong_induction_on S,
  {intros f, simp [finset.singleton_erase],},
  intros x s A3 A1 f,
  have A6 := (A1 s (finset.subset.refl s) f),
  rw finset.powerset_sum,
  rw eany_finset_insert,
  rw Pr_eor_eq_minus_eand_real,
  simp,
  rw ← distrib_exists_and,
  rw A6,
  have A8:=(A1 s (finset.subset.refl s) (λ a, f x∧ f a)),
  rw A8,
  have A9:
-s.powerset.sum
    (λ (x_1 : finset α), (Pr[has_eall_in.eall_in (insert x x_1) f]:real) * (-1) ^
    (insert x x_1).card) =
(Pr[f x]:real) + (s.powerset.erase ∅).sum
          (λ (T : finset α), (Pr[∀ᵣ (a : α) in T,f x∧ f a]:real) * (-1) ^ T.card),
  { have A9A:insert ∅ (s.powerset.erase ∅) = (s).powerset,
    {rw finset.insert_erase, simp},
     have A9B:
     -(s).powerset.sum
        (λ (x_1 : finset α), (Pr[has_eall_in.eall_in (insert x x_1) f]:real) * (-1) ^
        (insert x x_1).card) =
     -(insert ∅ (s.powerset.erase ∅)).sum
        (λ (x_1 : finset α), (Pr[has_eall_in.eall_in (insert x x_1) f]:real) * (-1) ^
        (insert x x_1).card),
     {rw A9A},
     rw A9B,
     clear A9A A9B,
     rw add_comm (Pr[f x]:real),
     --rw finset.sum_insert,
     simp,
     have A9C:-((s).powerset.erase ∅).sum
        (λ (x_1 : finset α), (Pr[has_eall_in.eall_in (insert x x_1) f]:real) * (-1) ^
        (insert x x_1).card) =
((s).powerset.erase ∅).sum
        ((λ (x_1 : finset α),- (Pr[has_eall_in.eall_in (insert x x_1) f]:real) * (-1) ^
        (insert x x_1).card)),
     {simp},
     rw A9C,
     clear A9C,
     apply finset.sum_congr,
     {refl},
     intros T A9D,
     simp at A9D,
     rw distrib_forall_eand,
     rw eall_finset_insert,
     rw finset.card_insert_of_not_mem,
     rw pow_succ,
     {simp},
     intro A9F,
     cases A9D with A9D A9E,
     rw finset.subset_iff at A9E,
     have A9G := A9E A9F,
     apply A3,
     apply A9G,
     apply finset.nonempty_of_ne_empty,
     apply A9D.left,},
  rw A9,
  linarith,
  apply A3,
end

lemma Pr_all_not_eq_powerset {α Ω:Type*} {P:probability_space Ω} (f:α → event Ω) [decidable_eq α]
  {S:finset α}:  (Pr[(∀ᵣ a in S, ¬ₑ (f a))]:real) = (S.powerset).sum  (λ T:finset α,
  (Pr[∀ᵣ a in T, f a]:real) *  (-1)^(T.card)) :=
begin
  --rw Pr_exists_eq_powerset,
  have A1:(insert ∅ ((S.powerset).erase ∅)).sum (λ T:finset α, (Pr[∀ᵣ a in T, f a]:real) *
    (-1)^(T.card))
    = S.powerset.sum (λ (T : finset α), ↑Pr[∀ᵣ (a : α) in T,f a] * (-1) ^ T.card),
  { rw finset.insert_erase,
    simp,},
  have A1:∅ ∈ S.powerset,
  {simp},
  rw ← finset.insert_erase A1,
  rw finset.sum_insert,simp,
  rw ← not_exists_eq_forall_not,
  rw ← Pr_one_minus_eq_not,
  rw nnreal.coe_sub,
  rw Pr_exists_eq_powerset,
  repeat {simp},
end
-/

/- TODO uncomment
lemma independent_events_not_of_independent_events {α Ω:Type*} {P:probability_space Ω}
  (f:α → event Ω):independent_events f → independent_events (enot ∘ f) :=
begin
  intros A1,
  unfold independent_events,
  intros S,
  haveI A3:=classical.decidable_eq α,

  apply finset.case_strong_induction_on S,
  {simp},
  intros a s B1 B2,
  rw  ← not_exists_eq_forall_not,
  have A2:∀ (A:event Ω), 1 - (Pr[A]:real) = (Pr[¬ₑ A]:real),
  { intro A,rw ← Pr_one_minus_eq_not,
    rw nnreal.coe_sub,
    {simp},
    apply Pr_le_one,},
  rw ← nnreal.coe_eq,
  rw ← A2,
  rw @Pr_exists_eq_powerset α Ω P f A3,
  unfold independent_events at A1,
  rw finset.prod_insert,
  rw finset.powerset_sum,
  rw B2 s (finset.subset.refl s),
  rw nnreal.coe_mul,
  rw ← A2,
  simp,
  rw ← @Pr_exists_eq_powerset α Ω P f A3,
  have A4:∀ x∈ s.powerset,
     (Pr[has_eall_in.eall_in (insert a x) f]:real) * (-1) ^ (insert a x).card =
    -(Pr[f a]:real) * ((Pr[has_eall_in.eall_in x f]:real) * (-1) ^ (x).card),
  {intros x A4A,
   have A4B:a ∉ x,
   {simp at A4A,intro A4B,apply B1,apply A4A,apply A4B},
   rw ← A1,rw finset.prod_insert A4B,
   rw A1,
   rw nnreal.coe_mul,
   rw finset.card_insert_of_not_mem A4B,
   rw pow_succ,
   simp,
   repeat {rw ← mul_assoc},
  },
  have A5:s.powerset = s.powerset := rfl,
  rw finset.sum_congr A5 A4,
  have A6:s.powerset.sum (λ (x : finset α), -(Pr[f a]:real) * (↑Pr[has_eall_in.eall_in x f] *
    (-1) ^ x.card))
    = -((Pr[f a]:real)) * s.powerset.sum (λ (x : finset α), (↑Pr[has_eall_in.eall_in x f] *
      (-1) ^ x.card)),
  {simp,rw finset.sum_distrib_left},
  rw A6,
  rw ← Pr_all_not_eq_powerset,
  rw ← not_forall_not_eq_exists,
  rw ← A2,
  simp,
  ring,
  repeat {exact B1},
end

lemma events_IID_not_of_events_IID {α Ω:Type*} {P:probability_space Ω} (f:α → event Ω) :
  events_IID f → events_IID (enot ∘ f) :=
begin
  intros A1,
  unfold events_IID,
  split,
  { apply independent_events_not_of_independent_events,
    unfold events_IID at A1,
    apply A1.left,},
  { unfold events_IID at A1,
    intros x y,
    have C2 := A1.right x y,
    simp,
    rw ← Pr_one_minus_eq_not,
    rw ← Pr_one_minus_eq_not,
    rw C2,},
end

lemma events_IID_iff_events_IID_enot {α Ω:Type*} {P:probability_space Ω} (f:α → event Ω):events_IID
  f ↔ events_IID (enot ∘ f) :=
begin
  split,
  { apply events_IID_not_of_events_IID,},
  { intros A1,
    have A2:f = enot ∘ (enot ∘ f),
    { apply funext, intro a, simp },
    rw A2,
    apply events_IID_not_of_events_IID,
    apply A1},
end
-/

def measurable_fun {α:Type*}  {β:Type*} (Mα:measurable_space α) (Mβ:measurable_space β):Type*:=
    subtype (@measurable α β _ _)

instance probability_space.to_measurable_space (α:Type*) [probability_space α]:measurable_space α :=
  measure_theory.measure_space.to_measurable_space

/- A random variable is a measurable_fun whose domain is a probability space (denoted (P →ᵣ M)). -/
def random_variable {α:Type*} (p:probability_space α) {β:Type*}
  (Mβ:measurable_space β):Type* := measurable_fun (probability_space.to_measurable_space α) Mβ

infixr  ` →ₘ `:80 := measurable_fun
infixr  ` →ᵣ `:80 := random_variable

lemma random_variable_val_eq_coe {Ω α:Type*} {P:probability_space Ω} {M:measurable_space α}
  (X:P →ᵣ M):X.val =
  (@coe (subtype (@measurable Ω α _ _)) (Ω → α) _ X) :=
begin
  refl
end

lemma measurable_setB_preimageh {α:Type*}  {β:Type*} [Mα:measurable_space α] [Mβ:measurable_space β]
  (f:measurable_fun Mα Mβ) (S:measurable_setB Mβ):measurable_set (set.preimage (f.val) (S.val)) :=
begin
  apply measurable_elim,
  apply f.property,
  apply S.property
end

def measurable_setB_preimage {α:Type*}  {β:Type*} [Mα:measurable_space α] [Mβ:measurable_space β]
  (f:measurable_fun Mα Mβ) (S:measurable_setB Mβ):measurable_setB Mα :=
  { val:= (set.preimage (f.val) (S.val)),
    property:=measurable_setB_preimageh f S,}

def rv_event {Ω:Type*} {p:probability_space Ω} {β:Type*}
  {Mβ:measurable_space β} (X:random_variable p Mβ) (S:measurable_setB Mβ):event Ω :=
   measurable_setB_preimage X S

infixr ` ∈ᵣ `:80 := rv_event

def rv_event_compl {Ω:Type*} {p:probability_space Ω} {β:Type*}
  [Mβ:measurable_space β] (X:random_variable p Mβ) (S:measurable_setB Mβ):event Ω :=
   ¬ₑ(rv_event X S)

infixr `∉ᵣ`:80 := rv_event_compl

@[simp]
def rv_event_compl_val {α:Type*} {p:probability_space α} {β:Type*}
  [Mβ:measurable_space β] (X:random_variable p Mβ) (S:measurable_setB Mβ):
   (rv_event_compl X S).val = (¬ₑ (rv_event X S)).val := rfl

@[simp]
lemma rv_event_val_def {α:Type*} {p : probability_space α} {β : Type*}
  [Mβ : measurable_space β] (X:p →ᵣ Mβ) (S:measurable_setB Mβ):(X ∈ᵣ S).val =
  {a:α|X.val a ∈ S.val} := by refl


instance measurable_setB_has_compl {α:Type*} [M:measurable_space α]:has_compl
(@measurable_setB α M) :=
{ compl := λ E, ⟨ E.valᶜ, measurable_set.compl E.property⟩,}

/- Which of these is simpler is subjective. -/
lemma rv_event_compl_preimage {α:Type*} {p: probability_space α} {β:Type*}
  [Mβ:measurable_space β] (X:random_variable p Mβ) (S:measurable_setB Mβ):
   (X ∈ᵣ Sᶜ) = (X ∈ᵣ S)ᶜ := rfl

def measurable_setB_empty {Ω:Type*} {p:measurable_space Ω}:measurable_setB p :=
{ val := ∅,
  property := measurable_set.empty,}

instance has_emptyc_measurable_setB {Ω:Type*} {M:measurable_space Ω}:has_emptyc
  (measurable_setB M) := ⟨ @measurable_setB_empty Ω M ⟩

lemma rv_event_empty {α:Type*} {p:probability_space α} {β:Type*}
  [Mβ:measurable_space β] (X:random_variable p Mβ):X ∈ᵣ ∅ = ∅ :=
begin
  apply event.eq,
  rw rv_event_val_def,
  rw event_empty_val_def2,
  ext ω;split;intros A1,
  {exfalso,
    simp at A1,
    apply A1,},
  {exfalso,
  apply A1,},
end

lemma rv_event_measurable_union {α:Type*} {p:probability_space α} {β:Type*}
  [Mβ:measurable_space β] (X:random_variable p Mβ)
  {A B:measurable_setB Mβ}:X ∈ᵣ (measurable_union A B) = ((X ∈ᵣ A) ∨ (X∈ᵣ B)) :=
begin
  apply event.eq,
  repeat {rw rv_event_val_def},
  rw eor_val_def,
  repeat {rw rv_event_val_def},
  rw measurable_union_val_def,
  ext ω;split;intros A1;simp;simp at A1;apply A1
end

lemma rv_event_val_def' {α:Type*} {p : probability_space α} {β : Type*}
  [Mβ : measurable_space β] (X:p →ᵣ Mβ) (S:measurable_setB Mβ) {ω:α}:
  (ω ∈ ((X ∈ᵣ S)))↔ (X.val ω ∈ S.val) := by refl

lemma set.mem_Prop_def {α:Type*} {P:α → Prop} {a:α}:
    (a ∈ {a':α|P a'} )= P a := rfl

lemma rv_event_measurable_Union {α:Type*} {p:probability_space α} {β:Type*}
  [Mβ:measurable_space β] {γ:Type*} [E:encodable γ] (X:random_variable p Mβ)
  {f:γ → measurable_setB Mβ}:X ∈ᵣ (measurable_Union f) =
  measurable_Union (λ i, X ∈ᵣ (f i)) :=
begin
  apply event.eq,
  ext ω,
  rw rv_event_val_def,
  rw measurable_Union_val_def,
  rw measurable_Union_val_def,
  split;intro A1,
  { rw set.mem_Prop_def at A1,
    rw set.mem_Union,
    rw set.mem_Union at A1,
    cases A1 with i A1,
    apply exists.intro i,
    rw @rv_event_val_def α p β Mβ X (f i),
    rw set.mem_Prop_def,
    apply A1,},
  { rw set.mem_Prop_def,
    rw set.mem_Union,
    rw set.mem_Union at A1,
    cases A1 with i A1,
    rw @rv_event_val_def α p β Mβ X (f i) at A1,
    apply exists.intro i,
    apply A1,},
end

lemma Pr_compl_ge_of_Pr_le {Ω:Type*} {p:probability_space Ω} (A:event Ω) (δ:nnreal):
  Pr[A] ≤ δ → Pr[Aᶜ] ≥ 1 - δ :=
begin
  intros h1,
  apply Pr_not_ge_of_Pr_le,
  apply h1,
end

--@[simp]
lemma event_simp_def {α:Type*} [p:probability_space α] {X:set α} {H:measurable_set X}:
  (subtype.mk X H).val = X := rfl

--@[simp]
lemma measurable_setB_simp_def {α:Type*} [p:measurable_space α] {X:set α} {H:measurable_set X}:
  (subtype.mk X H).val = X := rfl

lemma pr_comp_event {Ω:Type*} {p:probability_space Ω} {X:p →ᵣ borel real}
 {E:@measurable_setB ℝ (borel ℝ)}:
 (X ∈ᵣ (Eᶜ)) = (X ∈ᵣ E)ᶜ :=
begin
  apply event.eq,
  simp,
  refl,
end

lemma rv_event_compl' {Ω:Type*} {MΩ:probability_space Ω} {β:Type*} [Mβ:measurable_space β]
  (X:MΩ →ᵣ Mβ) (S:measurable_setB Mβ):(X ∈ᵣ (Sᶜ)) = (rv_event X S)ᶜ :=
begin
  apply event.eq,
  simp,
  refl,
end

lemma neg_eq_not {Ω:Type*} {p:probability_space Ω} (A:event Ω):
  Aᶜ = ¬ₑ A :=
begin
  apply event.eq,
  simp,
end

/- Definition of identical random variables. -/
def random_variable_identical {α α':Type*} {p:probability_space α} {p':probability_space α'}
  {β:Type*} {Mβ:measurable_space β} (X:random_variable p Mβ) (Y:random_variable p' Mβ):Prop :=
  ∀ (S:measurable_setB Mβ), Pr[X ∈ᵣ S] = Pr[Y ∈ᵣ S]

/- Definition of indepedent random variables. -/
def random_variable_independent_pair {α:Type*} {p:probability_space α} {β:Type*}
  {Mβ:measurable_space β} {γ:Type*} {Mγ:measurable_space γ} (X:p →ᵣ Mβ)
  (Y:p →ᵣ Mγ):Prop :=
  ∀ (S:measurable_setB Mβ) (T:measurable_setB Mγ), independent_event_pair (X ∈ᵣ S) (Y ∈ᵣ T)

def random_variable_independent {α:Type*} {p:probability_space α} {β:Type*}
  {γ:β → Type*} {Mγ:Π b, measurable_space (γ b)} (X:Π b, random_variable p (Mγ b)):Prop :=
  ∀ (S:Π b, measurable_setB (Mγ b)), independent_events (λ b:β, ((X b) ∈ᵣ (S b)))

def random_variables_IID {α:Type*} {p:probability_space α} {β:Type*}
  {γ:Type*} {Mγ:measurable_space γ} (X:β → random_variable p Mγ):Prop :=
  random_variable_independent X ∧
  ∀ (i j:β), random_variable_identical (X i) (X j)

/- There are a lot of types where everything is measurable. This is equivalent to ⊤. -/
class top_measurable (α:Type*) extends measurable_space α :=
  (all_measurable:∀ S:set α,measurable_set S)

def make_top_measurable_space (α:Type*) :top_measurable α :=
{ to_measurable_space := ⊤,
  all_measurable := begin
    intros S,
    apply measurable_space.measurable_set_top,
  end,}

instance top_measurable.has_coe_measurable_space (α:Type*):has_coe (top_measurable α)
  (measurable_space α) :=
{ coe := λ TM, @top_measurable.to_measurable_space α TM}

instance bool_top_measurable:top_measurable bool :=
{ all_measurable:=@measurable_space.measurable_set_top bool,
  ..bool.measurable_space}

instance int_top_measurable:top_measurable ℤ :=
{ all_measurable:=@measurable_space.measurable_set_top ℤ,
  ..int.measurable_space}

/- In a top measurable space (e.g. bool, ℕ, ℤ, et cetera), everything is measurable. So, we can
make an event from everything. -/
def measurable_setB_top {β:Type*} [M:top_measurable β] (S:set β):
    (@measurable_setB β M.to_measurable_space) :=
{ val := S,
  property := top_measurable.all_measurable S,}

def measurable_setB_top' {β:Type*} (S:set β):
    (@measurable_setB β (⊤:measurable_space β)) :=
{ val := S,
  property := begin
    apply measurable_space.measurable_set_top,
  end,}

@[simp]
lemma measurable_setB_top_val {β:Type*} [M:top_measurable β] (S:set β):
  (measurable_setB_top S).val = S := rfl

lemma fun_top_measurable {β γ:Type*} [M:top_measurable β] [Mγ:measurable_space γ] {f:β → γ}:
  measurable f := begin
  intros S A1,
  apply top_measurable.all_measurable,
end

def top_measurable_fun {β γ:Type*} [M:top_measurable β] (f:β → γ) (Mγ:measurable_space γ):
  (@top_measurable.to_measurable_space β M) →ₘ Mγ :=
{ val := f,
  property := fun_top_measurable}

def rv_top_event {Ω:Type*} {p:probability_space Ω}
 {β:Type*} [Mβ:top_measurable β]
  (X:random_variable p Mβ.to_measurable_space) (S:set β):event Ω :=
  rv_event X (measurable_setB_top S)

--To apply this directly to a set, it has to be top measurable.
infixr ` ∈t `:80 := rv_top_event

lemma rv_top_event_val_def  {α:Type*} {p:probability_space α}
 {β:Type*} [Mβ:top_measurable β]
  (X:random_variable p Mβ.to_measurable_space) (S:set β):
  (rv_top_event X S).val = {a:α|X.val a ∈ S} := rfl

lemma measurable_intro {α β:Type*}
  [measurable_space α] [measurable_space β] (f:α → β):
  (∀ B:(set β), measurable_set B → measurable_set (f ⁻¹' B))
  → (measurable f) :=
begin
  apply (measurable_def _).mp,
end

lemma compose_measurable_fun_measurable2 {α β γ:Type*}
  [Mα:measurable_space α] [Mβ:measurable_space β] [Mγ:measurable_space γ]
  (X:measurable_fun Mβ Mγ) (Y:measurable_fun Mα Mβ):measurable (X.val ∘ Y.val) :=
begin
  apply measurable_intro,
  intros B a,
  have A1:(X.val ∘ Y.val ⁻¹' B)=(Y.val ⁻¹' (X.val ⁻¹' B)),
  { refl,},
  rw A1,
  apply measurable_elim Y.val _ Y.property,
  apply measurable_elim X.val _ X.property,
  apply a
end

def compose_measurable_fun {α β γ:Type*}
  {Mα:measurable_space α} {Mβ:measurable_space β} {Mγ:measurable_space γ}
  (X:measurable_fun Mβ Mγ) (Y:measurable_fun Mα Mβ):(measurable_fun Mα Mγ) :=
  { val := X.val ∘ Y.val,
    property := compose_measurable_fun_measurable2 X Y}

infixr  ` ∘m `:80 := compose_measurable_fun

@[simp]
lemma compose_measurable_fun_val_def {Ω : Type*} {β : Type*} {γ : Type*}
  [MΩ : measurable_space Ω] [Mβ : measurable_space β]
  [Mγ : measurable_space γ] (Y:Mβ →ₘ Mγ) (X:MΩ →ₘ Mβ):
  (Y ∘m X).val = (λ ω:Ω, Y.val (X.val ω)) :=
begin
  refl
end

/- Define the composition of two random variables. -/
def rv_compose {α : Type*} {β : Type*} {γ : Type*}
  {p : probability_space α} {Mβ : measurable_space β}
  {Mγ : measurable_space γ} (X:measurable_fun Mβ Mγ) (Y:random_variable p Mβ):random_variable p Mγ
  := compose_measurable_fun X Y

infixr  ` ∘r `:80 := rv_compose

@[simp]
lemma rv_compose_val_def {Ω : Type*} {β : Type*} {γ : Type*}
  [Mβ : measurable_space β]
  [Mγ : measurable_space γ] {p : probability_space Ω} (Y:Mβ →ₘ Mγ) (X:p →ᵣ Mβ):
  (Y ∘r X).val = (λ ω:Ω, Y.val (X.val ω)) := by refl

/- Define the product space. -/
def prod_space {α β:Type*} (Mα:measurable_space α) (Mβ:measurable_space β):=(@prod.measurable_space
  α β Mα Mβ)

infixr  ` ×ₘ `:80 := prod_space

def measurable_setB.prod {α β:Type*} {Mα:measurable_space α} {Mβ:measurable_space β}
  (A:measurable_setB Mα) (B:measurable_setB Mβ):measurable_setB (Mα ×ₘ Mβ) :=
  @measurable_setB.mk (α × β) (Mα ×ₘ Mβ) (A.val.prod B.val)
begin
  apply measurable_set.prod,
  apply A.property,
  apply B.property,
end

@[simp]
lemma measurable_setB.prod_val {α β:Type*} {Mα:measurable_space α} {Mβ:measurable_space β}
  (A:measurable_setB Mα) (B:measurable_setB Mβ):(A.prod B).val = (A.val).prod (B.val) := rfl

lemma comap_elim {α β:Type*} [M2:measurable_space β] (f:α → β) (B:set β):
  (measurable_set B) →
  (M2.comap f).measurable_set'  (set.preimage f B) :=
begin
  intros a,
  unfold measurable_space.comap,
  simp,
  apply exists.intro B,
  split,
  apply a,
  refl
end

lemma set_Prop_le_def {α:Type*} (M M2:set α → Prop): M ≤ M2 ↔ (∀ X:set α, M X → M2 X) :=
by refl

lemma measurable_space_le_def {α:Type*} (M:measurable_space α) (M2:measurable_space α):
  M.measurable_set' ≤  M2.measurable_set' ↔ M ≤ M2 := by refl

lemma measurable_space_le_def2 {α:Type*}
  (M:measurable_space α) (M2:measurable_space α):
  (∀ X:set α, M.measurable_set' X → M2.measurable_set' X) ↔
   M ≤ M2 :=
begin
  intros,
  apply iff.trans,
  apply set_Prop_le_def,
  apply measurable_space_le_def,
end

lemma measurable_comap {α β:Type*} [M1:measurable_space α] [M2:measurable_space β] (f:α → β):
  (M2.comap f) ≤ M1 → measurable f :=
begin
  intros a,
  apply measurable_intro,
  intros B a_1,
  have A1:(M2.comap f).measurable_set'  (set.preimage f B),
    apply comap_elim,
    apply a_1,
  rw ← measurable_space_le_def2 at a,
  apply a,
  apply A1,
end

lemma measurable_fun_product_measurableh {α β:Type*}
  [M1:measurable_space α] [M2:measurable_space β]:
  (@prod.measurable_space α β M1 M2) = M1.comap prod.fst ⊔ M2.comap prod.snd :=
  by refl

lemma fst_measurable {α β:Type*}
  [M1:measurable_space α] [M2:measurable_space β]:measurable (λ x:(α × β), x.fst) :=
begin
  apply measurable_comap,
  have A1:M1.comap prod.fst ≤ (@prod.measurable_space α β M1 M2),
    rw measurable_fun_product_measurableh,
    apply complete_lattice.le_sup_left (M1.comap prod.fst) (M2.comap prod.snd),
  apply A1,
end

def mf_fst {α β:Type*}
  {Mα:measurable_space α} {Mβ:measurable_space β}:measurable_fun
    (Mα ×ₘ Mβ) Mα :=
  { val:= (λ x:(α × β), x.fst),
    property := fst_measurable,}

@[simp]
lemma mf_fst_val {α β:Type*}
  {Mα:measurable_space α} {Mβ:measurable_space β}:(@mf_fst α β Mα Mβ).val = prod.fst := rfl

lemma snd_measurable {α β:Type*}
  [M1:measurable_space α] [M2:measurable_space β]:measurable (λ x:(α × β), x.snd) :=
begin
  apply measurable_comap,
  have A1:M2.comap prod.snd ≤ (@prod.measurable_space α β M1 M2),
  { rw measurable_fun_product_measurableh,
    apply complete_lattice.le_sup_right (M1.comap prod.fst) (M2.comap prod.snd),},
  apply A1,
end

def mf_snd {α β:Type*}
  {Mα:measurable_space α} {Mβ:measurable_space β}:measurable_fun (prod_space Mα Mβ) Mβ :=
  { val:= (λ x:(α × β), x.snd),
    property := snd_measurable,}

@[simp]
lemma mf_snd_val {α β:Type*}
  {Mα:measurable_space α} {Mβ:measurable_space β}:(@mf_snd α β Mα Mβ).val = prod.snd := rfl

/-- Constant functions are measurable. Different than measurable_set.const. -/
lemma const_measurable {Ω:Type*} [measurable_space Ω] {β:Type*} [measurable_space β] (c:β):
  (measurable (λ ω:Ω, c)) := by apply measurable_const

/- Define constant measurable function. -/
def const_measurable_fun {Ω : Type*} [MΩ : measurable_space Ω] {β : Type*}
   [Mβ : measurable_space β] (c : β):MΩ →ₘ Mβ :=
   { val := (λ (ω : Ω), c),
     property := const_measurable c,}

lemma const_measurable_fun_val_def {Ω : Type*} [MΩ : measurable_space Ω] {β : Type*}
   [Mβ : measurable_space β] (c : β):(const_measurable_fun c).val = (λ (ω : Ω), c) := rfl

def const_random_variable {Ω : Type*} {P:probability_space Ω}
   {β : Type*}
   [Mβ : measurable_space β] (c : β):P →ᵣ Mβ := const_measurable_fun c

lemma preimage_compl {α β:Type*} (f:α → β) (S:set β):
  (f ⁻¹' Sᶜ) = ((f ⁻¹' S)ᶜ) :=
begin
  ext,
  split;intros a,
  { intro a_1,
    unfold set.preimage at a,
    simp at a,
    apply a,
    apply a_1,},
  { unfold set.preimage,
    simp,
    intro a_1,
    apply a,
    apply a_1,}
end

lemma preimage_Union {α β:Type*} (f:α → β) (g:ℕ → set β):
   (f ⁻¹' ⋃ (i : ℕ), g i)=(⋃ (i : ℕ), f ⁻¹' (g i)) :=
begin
  ext,
  split;intros a,
  { cases a with B a,
    cases a with H a,
    cases H with y H,
    split,
    simp,
    split,
    apply exists.intro y,
      simp at H,
      simp at H,
      subst B,
      apply a,},
  { cases a with A a,
    cases a with A1 A2,
    cases A1 with i A3,
    simp at A3,
    subst A,
    split,
    simp,
    split,
      apply exists.intro i,
      refl,
      apply A2,}
end

lemma generate_from_measurable {α β:Type*} [M:measurable_space α] [M2:measurable_space β]
   (X:set (set β)) (f:α → β):
   (measurable_space.generate_from X = M2)→
   (∀ B∈ X, measurable_set (set.preimage f B))→
   (measurable f) :=
begin
  intros a a_1,
  apply measurable_intro,
  intros B a_2,
  have A1:@measurable_set β (measurable_space.generate_from X) B,
  { rw a,
    apply a_2,},
  clear a_2, -- Important for induction later.
  have A2:measurable_space.generate_measurable X B,
  { apply A1,},
  induction A2,
  { apply a_1,
    apply A2_H,},
  { simp,},
  { -- ⊢ measurable_set (f ⁻¹' -A2_s)
    rw set.preimage_compl,
    apply measurable_space.measurable_set_compl,
    apply A2_ih,
    { apply (measurable_set.compl_iff).mp,
      apply A1,},},
  { rw set.preimage_Union,
    apply measurable_space.measurable_set_Union,
    intros i,
    apply A2_ih,
    { apply A2_ᾰ,}}
end

lemma measurable_fun_product_measurable {α β γ:Type*}
  [M1:measurable_space α] [M2:measurable_space β] [M3:measurable_space γ]
  (X: α →  β) (Y: α → γ):
  measurable X →
  measurable Y →
  measurable (λ a:α, prod.mk (X a) (Y a)) :=
begin
  intros B1 B2,
  have A1:@measurable _ _ _ (@prod.measurable_space β γ M2 M3) (λ a:α, prod.mk (X a) (Y a)),
  { have A1A:(@prod.measurable_space β  γ  M2 M3)=measurable_space.generate_from (
      {s : set (β × γ) | ∃ (s' : set β), measurable_space.measurable_set' M2 s' ∧
        prod.fst ⁻¹' s' = s} ∪
      {s : set (β  × γ) | ∃ (s' : set γ), measurable_space.measurable_set' M3 s' ∧
        prod.snd ⁻¹' s' = s}),
    { rw measurable_fun_product_measurableh,
      rw measurable_fun_comap_def,
      rw measurable_fun_comap_def,
      rw measurable_space.generate_from_sup_generate_from,},
    rw A1A,
    apply generate_from_measurable,
    { refl,},
    { intro BC,
      intros H,
      cases H,
      { cases H with B H,
        cases H,
        subst BC,
        have A1B:(λ (a : α), (X a, Y a)) ⁻¹' (prod.fst ⁻¹' B) = (X ⁻¹' B),
        { ext,split;intros a,
          { simp at a,
            apply a,},
          { simp,
            apply a,}},
        rw A1B,
        apply B1,
        apply H_left,},
      { cases H with C H,
        cases H,
        subst BC,
        have A1C:(λ (a : α), (X a, Y a)) ⁻¹' (prod.snd ⁻¹' C) = (Y ⁻¹' C),
        { ext,split;intros a,
          { simp at a,
            apply a,},
          { simp,
            apply a,}},
        rw A1C,
        apply B2,
        apply H_left,}}},
  apply A1,
end

def prod_measurable_fun
{α β γ:Type*}
  {Mα:measurable_space α} {Mβ:measurable_space β} {Mγ:measurable_space γ}
  (X:measurable_fun Mα Mβ) (Y:measurable_fun Mα Mγ):measurable_fun Mα (Mβ ×ₘ Mγ) :=
  { val := (λ a:α, prod.mk (X.val a) (Y.val a)),
    property := measurable_fun_product_measurable X.val Y.val X.property Y.property,}

lemma prod_measurable_fun_val_def {Ω : Type*} {β : Type*} {γ : Type*} {MΩ : measurable_space Ω}
  {Mβ : measurable_space β} {Mγ : measurable_space γ} {X:MΩ  →ₘ Mβ}
  {Y:MΩ  →ₘ Mγ}: (prod_measurable_fun X Y).val = λ ω:Ω, prod.mk (X.val ω) (Y.val ω) := by refl

def prod_random_variable
{α β γ:Type*}
  {P:probability_space α} {Mβ:measurable_space β} {Mγ:measurable_space γ}
  (X:random_variable P Mβ) (Y:random_variable P Mγ):random_variable P (Mβ ×ₘ Mγ) :=
  prod_measurable_fun X Y

infixr  ` ×ᵣ `:80 := prod_random_variable

@[simp]
lemma prod_random_variable_val_def {Ω : Type*} {β : Type*} {γ : Type*}
  {P : probability_space Ω} {Mβ : measurable_space β} {Mγ : measurable_space γ} {X:P →ᵣ Mβ}
  {Y:P →ᵣ Mγ}: (X ×ᵣ Y).val = λ ω:Ω, prod.mk (X.val ω) (Y.val ω) := by refl

lemma measurable_set_of_le_of_measurable_set
{α : Type*} {M1 : measurable_space α} {M2 : measurable_space α} {X:set α}: M1 ≤ M2 →
  measurable_space.measurable_set' M1 X → measurable_space.measurable_set' M2 X :=
begin
  intros A2 A1,
  rw ← measurable_space_le_def2 at A2,
  apply A2,
  apply A1,
end

lemma comap_fst_def {α β:Type*} {Bα:set (set α)}:
  (measurable_space.generate_from Bα).comap (@prod.fst α β) =
  measurable_space.generate_from {U:set (α × β)|∃ A∈ Bα, U = set.prod A set.univ} :=
begin
  rw measurable_space.comap_generate_from,
  rw set.preimage_fst_def,
end

lemma comap_snd_def {α β:Type*} {Bβ:set (set β)}:
  (measurable_space.generate_from Bβ).comap (@prod.snd α β) =
  measurable_space.generate_from {U:set (α × β)|∃ B∈ Bβ, U = set.prod set.univ B} :=
begin
  rw measurable_space.comap_generate_from,
  rw set.preimage_snd_def,
end

lemma measurable_space_sup_def {α:Type*} {B C:set (set α)}:
  (measurable_space.generate_from B) ⊔ (measurable_space.generate_from C) =
  (measurable_space.generate_from (B ∪ C)) :=
begin
  apply measurable_space.generate_from_sup_generate_from,
end

lemma prod_measurable_space_def {α β:Type*} {Bα:set (set α)}
  {Bβ:set (set β)}:
  (@prod.measurable_space α β (measurable_space.generate_from Bα)
  (measurable_space.generate_from Bβ)) =
  @measurable_space.generate_from (α × β) (
    {U:set (α × β)|∃ A∈ Bα, U = set.prod A set.univ} ∪
    {U:set (α × β)|∃ B∈ Bβ, U = set.prod set.univ B})
   :=
begin
  rw measurable_fun_product_measurableh,
  rw comap_fst_def,
  rw comap_snd_def,
  rw measurable_space_sup_def,
end

lemma prod_measurable_space_le {α β:Type*} {Bα:set (set α)}
  {Bβ:set (set β)}:
  @measurable_space.generate_from (α × β)
    {U:set (α × β)|∃ A∈ Bα, ∃ B∈Bβ,  U = set.prod A B} ≤
  (@prod.measurable_space α β (measurable_space.generate_from Bα)
  (measurable_space.generate_from Bβ))
   :=
begin
  rw prod_measurable_space_def,
  apply measurable_space.generate_from_le, intros X A5,
  simp at A5,
  cases A5 with A A5,
  cases A5 with A5 A6,
  cases A6 with B A6,
  cases A6 with A6 A7,
  have A8:(set.prod A (@set.univ β)) ∩
          (set.prod (@set.univ α) B) = set.prod A B,
  { ext p,split;intros A3A;
    { simp at A3A,
      simp,
       --cases p,
      apply A3A,},},
  rw ← A8 at A7,
  rw A7,
  apply measurable_set.inter,
  { apply measurable_space.measurable_set_generate_from,
    apply set.mem_union_left,
    simp,
    apply exists.intro A,
    split,
    apply A5,
    refl,},
  { apply measurable_space.measurable_set_generate_from,
    apply set.mem_union_right,
    simp,
    apply exists.intro B,
    split,
    apply A6,
    refl,},
end

/- TODO cf. measurable_set_prod -/
lemma measurable_set_prod' {β : Type*} {γ : Type*}
  {Mβ : measurable_space β} {Mγ : measurable_space γ}
  {X:set β} {Y:set γ}:measurable_set X →
   measurable_set Y →
   measurable_set (set.prod X Y) :=
begin
  intros A1 A2,
  rw generate_from_self Mβ,
  rw generate_from_self Mγ,
  apply measurable_set_of_le_of_measurable_set,
  apply prod_measurable_space_le,
  apply measurable_space.measurable_set_generate_from,
  simp,
  apply exists.intro X,
  split,
  apply A1,
  apply exists.intro Y,
  split,
  apply A2,
  refl,
end

def prod_measurable_setB {β : Type*} {γ : Type*}
  {Mβ : measurable_space β}
  {Mγ : measurable_space γ}
  (X:measurable_setB Mβ) (Y:measurable_setB Mγ):measurable_setB (Mβ ×ₘ Mγ) :=
{ val := (set.prod X.val Y.val),
  property := measurable_set_prod' X.property Y.property}

@[simp]
lemma prod_measurable_setB_val_def {β : Type*} {γ : Type*}
  {Mβ : measurable_space β}
  {Mγ : measurable_space γ}
  (X:measurable_setB Mβ) (Y:measurable_setB Mγ):
  (prod_measurable_setB X Y).val = set.prod X.val Y.val := rfl


class has_measurable_equality {α:Type*} (M:measurable_space α):Prop :=
  (measurable_set_eq:measurable_set {p:α × α|p.fst = p.snd})

def measurable_setB_eq {α:Type*} {M:measurable_space α} [E:has_measurable_equality M]
  :measurable_setB (M ×ₘ M) := measurable_setB.mk E.measurable_set_eq

lemma measurable_setB_eq_val {α:Type*} {M:measurable_space α} [E:has_measurable_equality M]:
  (@measurable_setB_eq α M E).val = {p:α × α|p.fst = p.snd} := rfl


def measurable_setB_ne {α:Type*} {M:measurable_space α} [E:has_measurable_equality M]
  :measurable_setB (M ×ₘ M) := measurable_setB.mk (measurable_set.compl E.measurable_set_eq)



lemma measurable_setB_ne_val {α:Type*} {M:measurable_space α} [E:has_measurable_equality M]:
  (@measurable_setB_ne α M E).val = {p:α × α|p.fst ≠ p.snd} := rfl

lemma diagonal_eq {α:Type*}:{p:α × α|p.fst  = p.snd}=⋃ (a:α), set.prod {a} {a} :=
begin
    ext,split;intros A1A;simp;simp at A1A,
    { apply exists.intro x.fst,
      ext;simp,
      rw A1A,},
    { cases A1A with i A1A,
      cases A1A,
      simp,},
end

instance measurable_setB_eq_top_measurable {α:Type*} (E:encodable α)
  (M:top_measurable α):has_measurable_equality (M.to_measurable_space) :=
{ measurable_set_eq := begin
  rw diagonal_eq,
  apply measurable_set.Union,
  intros a,
  apply measurable_set_prod',
  repeat {apply M.all_measurable},
end}

/- TODO delete the following and import from data.equiv.list -/
noncomputable def fintype.encodable (α : Type*) [fintype α] : encodable α :=
by { classical, exact (encodable.trunc_encodable_of_fintype α).out }

instance has_measurable_equality.fintype_top {α:Type*} [fintype α] [TM:top_measurable α]:
  has_measurable_equality (TM.to_measurable_space) :=
{ measurable_set_eq := begin
  rw diagonal_eq,
  haveI:encodable α := fintype.encodable α,
  apply measurable_set.Union,
  intros b,
  apply measurable_set.prod,
  apply TM.all_measurable,
  apply TM.all_measurable,
end}

instance measurable_setB_eq_bool:has_measurable_equality bool.measurable_space :=
{ measurable_set_eq := begin
  rw diagonal_eq,
  apply measurable_set.Union,
  intros a,
  apply measurable_set_prod',
  repeat {apply measurable_space.measurable_set_top},
end}

def random_variable_eq {Ω:Type*} {P:probability_space Ω} {α:Type*} [M:measurable_space α]
   [E:has_measurable_equality M] (X Y:P →ᵣ M):event Ω :=
    (X ×ᵣ Y) ∈ᵣ (measurable_setB_eq)

infixr  ` =ᵣ `:100 := random_variable_eq

@[simp]
lemma rv_eq_val_def {α:Type*} {p : probability_space α} {β : Type*}
   [Mβ :measurable_space β] [has_measurable_equality Mβ] (X Y:p →ᵣ Mβ):
  (X =ᵣ Y).val = {a:α| X.val a = Y.val a} :=
begin
  unfold random_variable_eq,
  rw rv_event_val_def,
  rw prod_random_variable_val_def,
  rw measurable_setB_eq_val,
  simp,
end


def random_variable_ne {Ω:Type*} {P:probability_space Ω} {α:Type*} [M:measurable_space α]
   [E:has_measurable_equality M] (X Y:P →ᵣ M):event Ω :=
    ¬ₑ (X =ᵣ Y)

infixr  ` ≠ᵣ `:100 := random_variable_ne

lemma union_func_eq_sUnion_image {α β:Type*}
  [Tβ:measurable_space β] {A:set α} {f:α → set β}:
  (⋃ a∈ A, f a)=set.sUnion (@set.image α (set β) f A) :=
begin
  simp,
end

lemma measurable_set_countable_union_func {α β:Type*}
  [Tβ:measurable_space β] {A:set α} {f:α → set β}:
  set.countable A →
  (∀ a∈ A, measurable_set (f a)) →
  measurable_set (⋃ a∈ A, f a) :=
begin
  intros A1 A2,
  rw union_func_eq_sUnion_image,
  apply measurable_set.sUnion,
  { apply set.countable.image,
    apply A1,},
  intros t A4,
  cases A4 with a A5,
  cases A5 with A6 A7,
  subst t,
  apply A2,
  apply A6,
end

/- TODO cf set.prod_singleton_singleton -/
lemma singleton_prod' {α β:Type*} {ab:α × β}:{ab} = (@set.prod α β {ab.fst} {ab.snd}) :=
begin
  simp,
end

lemma top_measurable_prodh {α β:Type*} [encodable α] [encodable β]
  [Tα:top_measurable α] [Tβ:top_measurable β] (U:set (α × β)):
  measurable_set U :=
begin
  have A2:encodable (α × β):= encodable.prod,
  have A3:set.countable U := set.countable_encodable U,
  have A4:(⋃ a∈U,{a}) = U,
  { simp},
  rw ← A4,
  apply measurable_set_countable_union_func A3,
  intros ab A5,
  rw singleton_prod',
  apply measurable_set.prod,
  { apply top_measurable.all_measurable,},
  { apply top_measurable.all_measurable,},
end

instance top_measurable_prod {α β:Type*} [encodable α] [encodable β]
  [Tα:top_measurable α] [Tβ:top_measurable β]:top_measurable (α × β) :=
  { all_measurable := top_measurable_prodh,}

lemma measurable.if {α β:Type*}
  {Mα:measurable_space α} {Mβ:measurable_space β}
  {E:set α} {D:decidable_pred E}
  {X Y:α → β}:measurable_set E →
  measurable X →
  measurable Y →
  measurable (λ a:α, if (E a) then (X a) else (Y a)) :=
begin
  intros A1 A2 A3,
  intros S B1,
  rw preimage_if,
  apply measurable_set.union,
  { apply measurable_set.inter,
    apply A1,
    apply A2,
    apply B1,},
  { apply measurable_set.inter,
    apply measurable_set.compl,
    apply A1,
    apply A3,
    apply B1,},
end

def if_measurable_fun
{α β:Type*}
  {Mα:measurable_space α} {Mβ:measurable_space β}
  (E:measurable_setB Mα) (D:decidable_pred E.val)
  (X:measurable_fun Mα Mβ) (Y:measurable_fun Mα Mβ):measurable_fun Mα Mβ :=
  { val := λ a:α, if (E.val a) then (X.val a) else (Y.val a),
    property := measurable.if E.property X.property Y.property,}

def if_random_variable
{Ω β:Type*}
  {P:probability_space Ω} {Mβ:measurable_space β}
  (E:event Ω) (D:decidable_pred E.val)
  (X:random_variable P Mβ) (Y:random_variable P Mβ):random_variable P Mβ :=
  if_measurable_fun E D X Y

@[simp]
lemma measurable_setB_preimage_val_def {α:Type*}  {β:Type*} [Mα:measurable_space α]
  [Mβ:measurable_space β] (f:measurable_fun Mα Mβ) (S:measurable_setB Mβ):
  (measurable_setB_preimage f S).val = (set.preimage (f.val) (S.val)) := rfl

lemma compose_measurable_fun_measurable_setB {Ω : Type*} {β : Type*} {γ : Type*}
  [MΩ : measurable_space Ω] [Mβ : measurable_space β]
  [Mγ : measurable_space γ] (Y:Mβ →ₘ Mγ) (X:MΩ →ₘ Mβ) (S:measurable_setB Mγ):
  measurable_setB_preimage (Y ∘m X) S = measurable_setB_preimage X (measurable_setB_preimage Y S) :=
begin
  apply subtype.eq,
  rw measurable_setB_preimage_val_def,
  rw measurable_setB_preimage_val_def,
  rw measurable_setB_preimage_val_def,
  rw compose_measurable_fun_val_def,
  refl,
end

lemma rv_compose_measurable_setB  {α : Type*} {β : Type*} {γ : Type*}
  {p : probability_space α} {Mβ : measurable_space β}
  {Mγ : measurable_space γ} (X:measurable_fun Mβ Mγ) (Y:random_variable p Mβ)
  (S:measurable_setB Mγ):(X ∘r Y) ∈ᵣ S = (Y ∈ᵣ (measurable_setB_preimage X S)) :=
begin
  apply compose_measurable_fun_measurable_setB,
end

lemma compose_independent' {Ω α:Type*} {p:probability_space Ω}
  {γ:α → Type*} [Mγ:Π (a:α), measurable_space (γ a)]
  {κ:α → Type*} [Mκ:Π (a:α), measurable_space (κ a)]
  (X:Π (b:α), p →ᵣ (Mγ b)) (Y:Π (b:α), (Mγ b) →ₘ  (Mκ b)):
  random_variable_independent X → random_variable_independent (λ b:α, (Y b) ∘r (X b)) :=
begin
  unfold random_variable_independent,
  intros A1 S T,
  unfold independent_events,
  have A2:(λ (b : α), Pr[((Y b) ∘r (X b)) ∈ᵣ (S b)]) =
      (λ (b : α), Pr[(X b) ∈ᵣ (measurable_setB_preimage (Y b) (S b))]),
  { ext b,
    rw rv_compose_measurable_setB,},
  rw A2,
  have A3:(λ (b : α), ((Y b) ∘r X b) ∈ᵣ S b) =
      (λ (b : α), (X b) ∈ᵣ (measurable_setB_preimage (Y b) (S b))),
  { ext b,
    rw rv_compose_measurable_setB,},
  rw A3,
  apply A1,
end

lemma compose_independent {α:Type*} {p:probability_space α} {β:Type*}
  {γ:Type*} [Mγ:measurable_space γ]
  {κ:Type*} [Mκ:measurable_space κ] (X:β → random_variable p Mγ) (Y:Mγ →ₘ  Mκ):
  random_variable_independent X → random_variable_independent (λ b:β, Y ∘r (X b)) :=
  by apply compose_independent'

lemma union_disjoint' {Ω β:Type*} {p:probability_space Ω}
    [D:decidable_eq β]
    (A:β → event Ω) (B:event Ω) {S:finset β}:(∀ a'∈ S, disjoint B.val (A a').val) →
    disjoint B.val (⋃ (b:β) (H:b∈ S), (A b).val) :=
begin
  intros A1,
  rw set.disjoint_right,
  intros ω A4 A3,
  simp at A4,
  cases A4 with i A4,
  have A5:= A1 i A4.left,
  rw set.disjoint_right at A5,
  apply A5 A4.right A3,
end

-- lemma union_disjoint {Ω β:Type*} {p:probability_space Ω}
--     [D:decidable_eq β]
--     (A:β → event Ω) {S:finset β} {a:β}:(pairwise (disjoint on λ (i : β), (A i).val)) →
--     (a ∉ S) →
--     disjoint (A a).val (⋃ (b:β) (H:b∈ S), (A b).val) :=
-- begin
--   intros A1 A2,
--   apply union_disjoint',
--   intros a' h_a',
--   apply A1,
--   intros contra,
--   subst a',
--   apply A2 h_a',
-- end

lemma Pr_sum_disjoint_eq' {Ω β:Type*} {p:probability_space Ω}
    [D:decidable_eq β]
    (A:β → event Ω) {S:finset β}:(set.pairwise_on (↑S) (disjoint on (λ i,  (A i).val))) →
    Pr[∃ᵣ a in S, A a] =
finset.sum S (λ (b:β), Pr[A b]) :=
begin
  apply finset.induction_on S,
  { intros A1,
    simp,},
  { intros a T A2 A3 B1,
    rw eany_finset_insert,
    rw Pr_disjoint_eor,
    rw finset.sum_insert A2,
    rw A3,
    { apply set.pairwise_on.mono _ B1,
      simp},
    { apply union_disjoint',
      intros b h_b, apply B1, simp, simp [h_b], intros contra,
      subst b, apply A2 h_b } },
end

lemma Pr_sum_disjoint_eq {Ω β:Type*} {p:probability_space Ω}
    [D:decidable_eq β]
    (A:β → event Ω) {S:finset β}:(pairwise (disjoint on λ (i : β), (A i).val)) →
    Pr[eany_finset S A] =
finset.sum S (λ (b:β), Pr[A b]) :=
begin
  intros h0,
  have h1 := @Pr_sum_disjoint_eq' _ _ _ _ A S _,
  apply h1,
  apply pairwise.pairwise_on h0,
end

lemma Pr_sum_disjoint_bounded {Ω β:Type*} {p:probability_space Ω} [decidable_eq β]
    (A:β → event Ω) {S:finset β}:(pairwise (disjoint on λ (i : β), (A i).val)) →
    finset.sum S (λ (b:β), Pr[A b]) ≤ 1 :=
begin
  intro A1,
  rw ← Pr_sum_disjoint_eq,
  apply Pr_le_one,
  apply A1,
end

/- TODO can this be dropped -/
lemma eq_or_ne2 {α:Type*} [D:decidable_eq α] {x y:α}:(x=y)∨ (x≠ y) :=
begin
  have A1:decidable (x=y) := D x y,
  cases A1,
  { right,
    apply A1,},
  { left,
    apply A1,}
end

/- TODO move to nnreal -/
lemma nnreal_sub_lt_sub_of_lt {a b c:nnreal}:b < c → b < a → a - c < a - b :=
begin
  intros A1 A2,
  --have A2:(a ≤ b)∨ (b ≤ a) := linear_order.le_total a b,
  have A3:(a ≤ c)∨ (c ≤ a) := linear_order.le_total a c,
  { cases A3,
    { rw nnreal.sub_eq_zero A3,
      apply nnreal.sub_pos.mpr A2,},
    rw ← nnreal.coe_lt_coe,
    rw nnreal.coe_sub,
    rw nnreal.coe_sub,
    apply sub_lt_sub_left,
    rw nnreal.coe_lt_coe,
    exact A1,
    apply (le_of_lt A2),
    exact A3,
  },
end

/- TODO move to sum -/
lemma has_sum_of_bounded_nnreal {β:Type*} [D:decidable_eq β] (f:β → nnreal) (v:nnreal):
 (∀ S:finset β,  S.sum f ≤ v) →
 (∀ ε>0, ∃ S:finset β,  v - ε ≤ S.sum f)  →
 has_sum f v :=
begin
  intros A1 A2,
  have A3:v = 0 ∨ v ≠ 0 := @eq_or_ne2 nnreal _ v 0,
  cases A3,
  { subst v,
    have A4:f = 0,
    { rw ← all_finset_sum_eq_zero_iff_eq_zero,
      intro S,
      apply le_bot_iff.mp,
      apply A1 S,},
    subst f,
    apply has_sum_zero,},
  { have A10:0 < v,
    { apply bot_lt_iff_ne_bot.mpr A3,},
    rw ←  has_sum_nnreal_ne_zero A3,
    intros ε A4,
    let k:nnreal := (min ε v)/2,
    begin
      have A8:k = ((min ε v)/2) := rfl,
      have A11:0 < min ε v,
      { rw lt_min_iff,
        split,
        apply A4,
        apply A10,},
      have A7:0 < k,
      { rw A8,
        apply nnreal.half_pos,
        apply A11,},
      have A12:k < min ε v,
      { apply nnreal.half_lt_self,
        apply bot_lt_iff_ne_bot.mp A11,},
      have A6 := A2 k A7,
      cases A6 with S A6,
      apply exists.intro S,
      intro T,
      intro A5,
      split,
      { apply A1,},
      { apply lt_of_lt_of_le,
        have A9:v - ε < v - k,
        { apply nnreal_sub_lt_sub_of_lt,
          { apply lt_of_lt_of_le,
            apply A12,
            apply min_le_left,},
          { apply lt_of_lt_of_le,
            apply A12,
            apply min_le_right,},},
        apply A9,
        apply le_trans,
        apply A6,
        apply finset.sum_monotone',
        apply A5,},
    end,
    apply D,},
end

/- TODO move to sum -/
lemma nnreal.le_Sup {S:set nnreal}:(∃ (x : nnreal), ∀ (y : nnreal), y ∈ S → y ≤ x) →
   ∀ {x : nnreal}, x ∈ S → x ≤ Sup S :=
begin
  intro A1,
  intros x A2,
  rw ← nnreal.coe_le_coe,
  rw nnreal.coe_Sup,
  apply real.le_Sup,
  cases A1 with z A1,
  apply exists.intro (coe z),
  intros y A3,
  cases A3 with y2 A3,
  cases A3 with A3 A4,
  subst y,
  rw nnreal.coe_le_coe,
  apply A1 y2 A3,
  simp,
  apply A2,
end

/- TODO move to sum -/
lemma bdd_above_def {α:Type*} [preorder α] {s:set α}:
  bdd_above s = (upper_bounds s).nonempty := rfl

/- TODO move to sum -/
lemma nnreal.le_Sup_of_bdd_above {S:set nnreal}:
  bdd_above S →
  (∀ x∈ S, (x ≤ Sup S)) :=
begin
  intros A1 y A2,
  apply nnreal.le_Sup,
  rw bdd_above_def at A1,
  unfold set.nonempty upper_bounds at A1,
  cases A1 with x A1,
  apply exists.intro x,
  apply A1,
  apply A2,
end

/- TODO move to sum -/
lemma nnreal.le_supr_of_bdd_above {α:Type*} {f:α → nnreal}:
  bdd_above (set.range f) →
  (∀ x:α, (f x ≤ ⨆ (s : α), f s)) :=
begin
  intro A1,
  unfold supr,
  intro a,
  simp,
  apply nnreal.le_Sup_of_bdd_above A1,
  simp,
end

/- TODO move to sum -/
lemma nnreal.x_eq_zero_of_supr_finset_sum_eq_zero {S:set nnreal}:
   (bdd_above S) →
   (Sup S = 0) →
   (∀ x:nnreal, x∈ S → x = 0):=
begin
  intros A1 A2 x A3,
  have A4:x≤ 0,
  { rw ← A2,
    apply nnreal.le_Sup_of_bdd_above,
    apply A1,
    apply A3,},
  apply le_bot_iff.mp A4,
end

/- TODO move to sum -/
lemma zero_of_supr_finset_sum_eq_zero {α:Type*} [D:decidable_eq α] {f:α → nnreal}:
  (bdd_above (set.range (λ s:finset α, s.sum f))) →
 ((⨆ (s :finset α), finset.sum s f) = 0) →
 (f = 0) :=
begin
  intros A1 A2,
  have A3:(∀ (s :finset α), finset.sum s f= 0),
  { intros S,
    apply nnreal.x_eq_zero_of_supr_finset_sum_eq_zero A1,
    unfold supr at A2,
    apply A2,
    simp,},
  rw @all_finset_sum_eq_zero_iff_eq_zero α D f at A3,
  apply A3
end

/- TODO move to sum -/
lemma set_range_inhabited_domain {α:Type*} {β:Type*} {f:α → β}
  [A1:inhabited α]:(set.range f).nonempty :=
begin
  unfold set.range,
  apply exists.intro (f A1.default),
  simp,
end

/- TODO move to sum -/
lemma set_range_finset_nonempty {α β:Type*} [add_comm_monoid β] {f:α → β}:
  (set.range (λ (s : finset α), s.sum f)).nonempty :=
begin
  apply set_range_inhabited_domain,
end

/- TODO move to sum -/
lemma nnreal.has_sum_of_bdd_above {α:Type*} {f:α → nnreal} [decidable_eq α] {x:nnreal}:
  bdd_above (set.range (λ s:finset α, s.sum f)) →
  (x = ⨆ (s : finset α), s.sum f) →
  has_sum f x  :=
begin
  intros AX A2,
  apply has_sum_of_bounded_nnreal,
  { intro S,
    rw A2,
    apply @nnreal.le_supr_of_bdd_above (finset α) (λ s:finset α, s.sum f) AX,},
  { have A3:(x = 0) ∨ (x ≠ 0) := eq_or_ne2,
    cases A3,
    { subst x,
      intro ε,
      intro A4,
      apply exists.intro ∅,
      rw A3,
      have A4:0 - ε ≤ 0,
      { apply nnreal.sub_le_self,},
      apply le_trans A4,
      apply bot_le,
      have A3A:f = 0,
      { apply zero_of_supr_finset_sum_eq_zero,
        apply AX,
        apply A3,},
      apply finset.has_emptyc,},
    { intros ε A1,
      have A4:x - ε < x,
      { apply nnreal.sub_lt_self,
        apply bot_lt_iff_ne_bot.mpr,
        apply A3,
        apply A1,},
      let T := (set.range (λ (s : finset α), finset.sum s f)),
      begin
        have A5:T = (set.range (λ (s : finset α), finset.sum s f)) := rfl,
        have A6:Sup T = x,
        { rw A2,
          refl,},
        have A7:∃b∈ T, x-ε< b,
        { apply @exists_lt_of_lt_cSup nnreal _ T,
          rw A5,
          apply @set_range_finset_nonempty α nnreal _ f,
          rw A6,
          apply A4,},
        cases A7 with b A7,
        cases A7 with A7 A8,
        rw A5 at A7,
        simp at A7,
        cases A7 with S A7,
        subst b,
        apply exists.intro S,
        apply le_of_lt A8,
      end},},
end

/- TODO move to sum -/
lemma nnreal.has_sum_of_supr {α:Type*} {f:α → nnreal} [decidable_eq α]:
  bdd_above (set.range (λ s:finset α, s.sum f)) →
  has_sum f (⨆ (s : finset α), s.sum f)  :=
begin
  intros A1 A2,
  have A3:(⨆ (s : finset α), s.sum f) = (⨆ (s : finset α), s.sum f),
  { refl,},
  apply nnreal.has_sum_of_bdd_above A1 A3,
end

/- TODO move to sum -/
lemma summable_bounded_nnreal {β:Type*} [decidable_eq β] (f:β → nnreal) (v:nnreal):
 (∀ S:finset β,  S.sum f ≤ v) →
 summable f :=
begin
  intro A1,
  apply has_sum.summable,
  apply nnreal.has_sum_of_supr,
    rw bdd_above_def,
    unfold upper_bounds,
    apply @set.nonempty_of_mem _ _ v,
    simp,
    apply A1,
end

lemma Pr_disjoint_summable {Ω β:Type*} {p:probability_space Ω} [E:encodable β] [decidable_eq β]
    (A:β → event Ω):(pairwise (disjoint on λ (i : β), (A i).val)) →
    summable (λ (b:β), Pr[A b]) :=
begin
  intro A1,
  apply summable_bounded_nnreal,
  { intro S,
    apply Pr_sum_disjoint_bounded,
    apply A1,},
end

/- TODO uncomment, problem with measure_eq_measure
lemma Pr_eany_sum {Ω β:Type*} {p:probability_space Ω} [E:encodable β] [decidable_eq β]
    (A:β → event Ω):(pairwise (disjoint on λ (i : β), (A i).val)) →
    Pr[eany A] = ∑' (b:β), Pr[A b] :=
begin
  intro B1,
  rw ← measurable_Union_eq_any,
  rw ← with_top.coe_eq_coe,
  rw event_prob_def,
  rw measurable_Union_val_def,
  rw ennreal.coe_tsum,
  have A1:(λ (b:β), ↑Pr[A b]) = (λ (b:β), (measure_theory.measure_space.volume
 (A b).val)),
  { ext b,
    rw event_prob_def,
    --rw measure_eq_measure,},
  rw measure_eq_measure,
  rw measure_theory.measure_Union,
  rw sum_subst,
  rw A1,
  apply B1,
  { intro i,
    apply (A i).property,},
  { apply Pr_disjoint_summable,
    apply B1,},
end
-/

lemma mem_prod_random_variable_prod_measurable_setB
  {α β γ:Type*}
  {P:probability_space α} {Mβ:measurable_space β} {Mγ:measurable_space γ}
  (X:random_variable P Mβ) (Y:random_variable P Mγ)
  (S:measurable_setB Mβ) (T:measurable_setB Mγ):
  (X ×ᵣ Y) ∈ᵣ (prod_measurable_setB S T) =
  ((X ∈ᵣ S) ∧ (Y∈ᵣ T)) :=
begin
  apply event.eq,
  simp,
  refl
end

lemma joint_measurable.pi {Ω β:Type*} {γ:β → Type*} [measurable_space Ω] [Π (b:β),
  measurable_space (γ b)] (f:Π (b:β), Ω → (γ b))
  (h:∀ b:β, measurable (f b)):measurable (λ (ω:Ω) (b:β), f b ω) :=
begin
  apply measurable_pi_lambda,
  apply h,
end

def measurable_space.pi_alt {δ:Type*} {π:δ → Type*} (M:Π (d:δ), measurable_space (π d)):
  measurable_space (Π (d:δ), π d) :=
  @measurable_space.pi δ π M

notation `Πₘ` binders `, ` r:(scoped f, measurable_space.pi_alt f) := r

/- Given a function of measurable functions (X), create a measurable function
   whose codomain is a measurable space of functions.
   Alternate name: joint_measurable_fun? -/
def pi.measurable_fun
{α β:Type*} {Mα:measurable_space α} {γ:β → Type*}
  {M:Π (b:β), measurable_space (γ b)}
  (X:Π (b:β), Mα →ₘ (M b)):measurable_fun Mα (@measurable_space.pi β γ M) :=
  { val := (λ (a:α) (b:β), (X b).val a),
    property := begin
      apply measurable_pi_lambda,
      intros b,
      apply (X b).property,
    end,}

/- Given a bunch of random variables in a common probability space, combine them
   to output a function. NOTE: this creates a new random variable in the
   existing probability space. -/
def pi.random_variable_combine
{α β:Type*} {P:probability_space α} {γ:β → Type*}
  {M:Π (b:β), measurable_space (γ b)}
  (X:Π (b:β), P →ᵣ (M b)):P →ᵣ (@measurable_space.pi β γ M) :=
  pi.measurable_fun X

@[simp]
def random_variable.fst {Ω:Type*} {p:probability_space Ω} {α:Type*}
  {Mα:measurable_space α} {β:Type*} {Mβ:measurable_space β} (X:p →ᵣ (Mα ×ₘ Mβ)):p →ᵣ Mα :=
  mf_fst ∘r X

@[simp]
def random_variable.snd {Ω:Type*} {p:probability_space Ω} {α:Type*} {Mα:measurable_space α}
  {β:Type*} {Mβ:measurable_space β} (X:p →ᵣ (Mα ×ₘ Mβ)):p →ᵣ Mβ :=
  mf_snd ∘r X

instance const_measurable_fun.has_coe {α:Type*} [M:measurable_space α] {Ω:Type*}
  {MΩ:measurable_space Ω}:has_coe α (MΩ →ₘ M) :=
{ coe := (λ (a:α), const_measurable_fun a)}

instance const_random_variable.has_coe {α:Type*} [M:measurable_space α] {Ω:Type*}
  {p:probability_space Ω}:has_coe α (p →ᵣ M) :=
{ coe := (λ (a:α), const_random_variable a)}

instance bool.has_coe_to_rv {Ω:Type*} {p:probability_space Ω}:has_coe bool
  (p →ᵣ bool.measurable_space) := const_random_variable.has_coe

instance int.has_coe_to_rv {Ω:Type*} {p:probability_space Ω}:has_coe int
  (p →ᵣ int.measurable_space) := const_random_variable.has_coe

@[simp]
lemma const_random_variable.has_coe.val {α:Type*} [M:measurable_space α]
  {Ω:Type*} {p:probability_space Ω} {a:α}:
 ((↑a):(p →ᵣ M)).val = (λ ω:Ω, a) := by refl

@[simp]
lemma const_measurable_fun.has_coe.val {α:Type*} [M:measurable_space α] {Ω:Type*}
  {MΩ:measurable_space Ω} {a:α}: ((↑a):(MΩ →ₘ M)).val = (λ ω:Ω, a) := by refl

@[simp]
lemma const_random_variable.has_coe.val_apply {α:Type*} [M:measurable_space α] {Ω:Type*}
  {p:probability_space Ω} {a:α} {ω:Ω}: ((↑a):(p →ᵣ M)).val ω = a := by refl

@[simp]
lemma const_measurable_fun.has_coe.val_apply {α:Type*} [M:measurable_space α] {Ω:Type*}
  {MΩ:measurable_space Ω} {a:α} {ω:Ω}: ((↑a):(MΩ →ₘ M)).val ω = a := by refl

lemma random_variable_identical.symm {Ω₁ Ω₂ α:Type*} {P₁:probability_space Ω₁}
{P₂:probability_space Ω₂} {M:measurable_space α} {X₁:P₁ →ᵣ M} {X₂:P₂ →ᵣ M}:
  random_variable_identical X₁ X₂ → random_variable_identical X₂ X₁ :=
begin
  intros h1 S,
  symmetry,
  apply h1,
end

lemma random_variable_identical.trans
  {Ω₁ Ω₂ Ω₃ α:Type*} {P₁:probability_space Ω₁}
  {P₂:probability_space Ω₂}
  {P₃:probability_space Ω₃}
  {M:measurable_space α}
  {X₁:P₁ →ᵣ M}
  {X₂:P₂ →ᵣ M}
  {X₃:P₃ →ᵣ M}:
  random_variable_identical X₁ X₂ →
  random_variable_identical X₂ X₃ →
  random_variable_identical X₁ X₃ :=
begin
  intros h1 h2 S,
  have h3:Pr[X₁ ∈ᵣ S] = Pr[X₂ ∈ᵣ S],
  { apply h1 },
  rw h3,
  apply h2,
end

/- TODO move to ennreal -/
lemma ennreal.coe_infi {α:Sort*} [nonempty α] {f:α → nnreal}:
  @coe nnreal ennreal _ (⨅ i, f i) = (⨅ i,  @coe nnreal ennreal _ (f i)) := begin
  simp only [infi],
  rw ennreal.coe_Inf,
  apply le_antisymm,
  { simp, intros a, apply @infi_le_of_le ennreal nnreal _ _ _ (f a),
    apply @infi_le_of_le ennreal α _ _ _ a,
    rw infi_pos, apply le_refl _, refl },
  { simp, intros a, apply @Inf_le ennreal _ _ _,
    simp, apply exists.intro a, refl },
  apply set.range_nonempty,
end

/- TODO move to set -/
lemma directed_superset_of_monotone_dual {α:Type*} {f:ℕ → set α}:
  (@monotone ℕ (set α) _ (order_dual.preorder (set α)) f) → (directed superset f)
 := begin
  intros h_mono,
  intros i j,
  cases (le_total i j) with h_i_le_j h_j_le_i,
  { apply exists.intro j,
    split,
    apply h_mono,
    apply h_i_le_j,
    apply set.subset.refl },
  { apply exists.intro i,
    split,
    apply set.subset.refl,
    apply h_mono,
    apply h_j_le_i },
end

/- TODO move to set -/
lemma monotone_of_monotone_nat_dual_iff {α:Type*} {f:ℕ → set α}:
  (@monotone ℕ (set α) _ (order_dual.preorder (set α)) f) ↔ (∀ (n:ℕ), f (n.succ) ⊆ f n) := begin
  split,
  { intros h_mono,
    intros n,
    apply h_mono,
    apply le_of_lt (nat.lt_succ_self _) },
  { intros h_mono_nat,
    apply @monotone_of_monotone_nat (set α) (order_dual.preorder (set α)),
    intros n,
    apply h_mono_nat },
end

/- TODO move to set -/
lemma directed_superset_of_monotone_nat_dual {α:Type*} {f:ℕ → set α}:
  (∀ (n:ℕ), f (n.succ) ⊆ f n) → (directed superset f) := begin
  rw ← monotone_of_monotone_nat_dual_iff,
  apply directed_superset_of_monotone_dual,
end

/-- This wraps `measure_theory.measure_Inter_eq_infi`.
    Note that this theorem uses monotonically decreasing instead
    of directed. This could be revisited. -/
lemma Pr_forall_eq_infi {Ω:Type*} {P:probability_space Ω} {f : ℕ → event Ω}:
                           (∀ (i:ℕ), (f i.succ).val ⊆ (f i).val) →
   Pr[∀ᵣ i, f i] = ⨅  i, Pr[f i] := begin
  intros h1,
  rw ← ennreal.coe_eq_coe,
  rw event_prob_def,
  have h2:(∀ᵣ (i : ℕ), f i).val = ⋂  (i : ℕ),(f i).val,
  { simp, },
  rw h2,
  simp,
  rw measure_theory.measure_Inter_eq_infi,
  --simp [infi],
  rw ennreal.coe_infi,
  have h3:(λ (i : ℕ), measure_theory.measure_space.volume ↑(f i)) = λ (i : ℕ), ↑Pr[f i],
  { ext1 i, rw event_prob_def, simp, },
  rw h3,
  { intros i, apply (f i).property },
  { --apply directed_superset_of_monotone_nat_dual,
    apply directed_superset_of_monotone_nat_dual,
    apply h1, },
  apply exists.intro 0,
  apply lt_of_le_of_lt,
  apply prob_le_1,
  simp,
end

lemma Pr_forall_revent_eq_infi {Ω α:Type*} {P:probability_space Ω} {M:measurable_space α}
   {f : ℕ → measurable_setB M} {X:P →ᵣ M}:
                           (∀ (i:ℕ), (f i.succ).val ⊆ (f i).val) →
   Pr[∀ᵣ i, X ∈ᵣ f i] = ⨅  i, Pr[X ∈ᵣ f i] := begin
  intros h1,
  apply Pr_forall_eq_infi,
  intros i,
  simp,
  intros ω h2,
  apply h1,
  apply h2
end
/- TODO move to nnreal -/
lemma ennreal.coe_supr {α:Sort*} [nonempty α] {f:α → nnreal}:
  (bdd_above (set.range f)) →
  @coe nnreal ennreal _ (⨆ i, f i) = (⨆ i,  @coe nnreal ennreal _ (f i)) :=
begin
  intros h1,
  simp only [supr],
  rw ennreal.coe_Sup,
  apply le_antisymm,
  { simp, intros a, apply @le_Sup ennreal _ _ _,
    simp, apply exists.intro a, refl },
  { simp, intros a, apply @le_supr_of_le ennreal nnreal _ _ _ (f a),
    apply @le_supr_of_le ennreal α _ _ _ a,
    rw supr_pos, apply le_refl _, refl },
  apply h1,
end

/- TODO move to set -/
/- Note: monotone is a stronger property than directed.
   e.g., directed can be increasing or decreasing, or
   have a single maximal element in the middle. -/
lemma directed_subset_of_monotone {α:Type*} {f:ℕ → set α}:
  monotone f → (directed set.subset f) := begin
  intros h_mono,
  intros i j,
  cases  (le_total i j),
  { apply exists.intro j,
    split,
    apply h_mono h,
    apply set.subset.refl },
  { apply exists.intro i,
    split,
    apply set.subset.refl,
    apply h_mono h },
end

/- Wraps measure_theory.measure_Union_eq_supr -/
lemma Pr_exists_eq_supr {Ω:Type*} {P:probability_space Ω} {f : ℕ → event Ω}:
                           monotone (λ i, (f i).val) →
   Pr[∃ᵣ i, f i] =  (⨆ (i:ℕ), Pr[f i]) := begin
  intros h1,
  rw ← ennreal.coe_eq_coe,
  rw event_prob_def,
  have h2:(∃ᵣ (i : ℕ), f i).val = ⋃ (i : ℕ),(f i).val,
  { simp, },
  rw h2,
  simp,
  rw measure_theory.measure_Union_eq_supr,
  rw ennreal.coe_supr,
  have h3:(λ (i : ℕ), measure_theory.measure_space.volume ↑(f i)) = λ (i : ℕ), ↑Pr[f i],
  { ext1 i, rw event_prob_def, simp, },
  rw h3,
  { simp [bdd_above], rw set.nonempty_def,
    apply exists.intro (1:nnreal),
    rw mem_upper_bounds,
    intros x h_mem,
    simp at h_mem,
    cases h_mem with i h_mem,
    subst x,
    apply Pr_le_one },
  { intros i, apply (f i).property },
  apply directed_subset_of_monotone,
  apply h1
end

lemma Pr_exists_revent_eq_supr {Ω α:Type*} {P:probability_space Ω} {M:measurable_space α}
   {f : ℕ → measurable_setB M} {X:P →ᵣ M}:
                           (monotone (λ (i:ℕ), (f i).val)) →
   Pr[∃ᵣ i, X ∈ᵣ f i] = ⨆ i, Pr[X ∈ᵣ f i] := begin
  intros h_mono,
  apply Pr_exists_eq_supr,
  intros i j h_le,
  simp,
  intros ω h2,
  have h_mono_i_j := h_mono h_le,
  simp at h_mono_i_j,
  apply h_mono_i_j,
  apply h2,
end

lemma disjoint_preimage {Ω γ:Type*} {P:probability_space Ω}
  {M:measurable_space γ} {S T:measurable_setB M} {X:P →ᵣ M}:
  disjoint S.val T.val → disjoint (X ∈ᵣ S).val (X ∈ᵣ T).val :=
begin
  simp [disjoint_iff],
  intros h,
  ext, split; intros h1,
  { simp at h1,
    have h2:(X.val x) ∈ (↑S ∩ ↑T),
    { simp [h1], rw set.mem_inter_iff, apply h1 },
    rw h at h2,
    exfalso, apply h2 },
  exfalso, apply h1,
end

lemma independent_event_pair.symm {Ω:Type*} {P:probability_space Ω}
  {E F:event Ω}:independent_event_pair E F → independent_event_pair F E :=
begin
  intros h1,
  unfold independent_event_pair,
  rw mul_comm,
  have h2:(F ∧ E) = (E ∧ F),
  { apply event.eq, simp, rw set.inter_comm },
  rw h2,
  apply h1,
end

lemma random_variable_independent_pair.symm {Ω α β:Type*} {P:probability_space Ω}
  {Mα:measurable_space α}
  {Mβ:measurable_space β}
  {X:P →ᵣ Mα} {Y:P →ᵣ Mβ}:random_variable_independent_pair X Y →
  random_variable_independent_pair Y X :=
begin
  intros h1 S T,
  apply independent_event_pair.symm,
  apply h1,
end

instance measurable_setB_top.has_coe
  {α:Type*} [TM:top_measurable α]:has_coe (set α) (measurable_setB (TM.to_measurable_space)) :=
  ⟨measurable_setB_top⟩

@[simp]
lemma measurable_setB_top.coe_val {α:Type*} [TM:top_measurable α] (S:set α):
  (@coe (set α) (measurable_setB (TM.to_measurable_space)) _ S).val = S := rfl

lemma event_eq_disjoint {α Ω:Type*} {P:probability_space Ω}
  {M:measurable_space α} {Y:P →ᵣ M} [has_measurable_equality M]:
  pairwise (disjoint on (λ (a:α), (Y =ᵣ a).val)) :=
begin
  intros i j h_ne,
  simp [function.on_fun, disjoint_iff],
  { ext ω, split; intros h3,
   { simp at h3, exfalso, apply h_ne,
     cases h3, subst i, subst j },
   { exfalso, apply h3 } },
end

/- TODO uncomment, type mismatch
lemma Pr_sum_univ_eq_one {α Ω:Type*} [fintype α] {P:probability_space Ω}
  {M:measurable_space α} {Y:P →ᵣ M} [has_measurable_equality M]:
  finset.univ.sum (λ (a:α), Pr[Y =ᵣ a]) = 1 :=
begin
  classical,
  have h1:(∃ᵣ (a:α), Y =ᵣ a) = event_univ,
  { apply event.eq,
    simp, ext ω, split; intros h1, simp at h1,
    simp, },
  have h2:Pr[(∃ᵣ (a:α), Y =ᵣ a)] = 1,
  { rw h1, simp  },
  have h3:(∃ᵣ (a:α), Y =ᵣ a) = eany_finset (@finset.univ α _) (λ (a:α), Y =ᵣ a),
  { apply event.eq, simp },
  rw h3 at h2,
  haveI:encodable α := fintype.encodable α,
  rw Pr_sum_disjoint_eq at h2,
  apply h2,
  apply event_eq_disjoint,
end
-/

lemma equal_eq_mem {Ω α:Type*} {P:probability_space Ω} {TM:top_measurable α}
  [has_measurable_equality TM.to_measurable_space]
  (X:P →ᵣ TM.to_measurable_space) (a:α):(X =ᵣ a) = (X ∈ᵣ ({a}:set α)) :=
begin
  apply event.eq,
  simp,
end

lemma finset_empty_empty {α:Type*} (S:finset α):(¬(nonempty α)) → (S = ∅) :=
begin
  intros h1,
  ext,split;intros A1,
  { exfalso, apply h1, apply nonempty.intro a },
  { exfalso, apply A1 },
end
/- TODO uncomment, goal unproved
lemma independent_events_empty {Ω α:Type*}
  {P:probability_space Ω} (E:α → event Ω):(¬(nonempty α)) →
  independent_events E := begin
  intros h1,
  simp [independent_events],
  intros S,
  rw finset_empty_empty S h1,
  simp,
end

lemma random_variable_independent_empty {Ω α γ:Type*}
  {P:probability_space Ω} {M:measurable_space γ} (X:α → P →ᵣ M):(¬(nonempty α)) →
  random_variable_independent X := begin
  simp [random_variable_independent],
  intros h1 S,
  apply independent_events_empty,
  apply h1,
end


lemma random_variables_IID_empty {Ω α γ:Type*}
  {P:probability_space Ω} {M:measurable_space γ} (X:α → P →ᵣ M):(¬(nonempty α)) →
  random_variables_IID X := begin
  intros h1,
  simp [random_variables_IID],
  split,
  apply random_variable_independent_empty,
  apply h1,
  intros i,
  exfalso,
  apply h1,
  apply nonempty.intro i,
end

def set.pi_measurable {α:Type*} [F:fintype α] {β:α → Type*} {M:Π a, measurable_space (β a)}
(T:set α) (S:Π a, measurable_setB (M a)):measurable_setB (@measurable_space.pi α β M) :=
{ val := (set.pi T (λ a, (S a).val)),
  property := begin
    simp,
    apply @measurable_set.pi',
    intros a,
    apply (S a).property,
  end}

lemma set.pi_measurable_univ {α:Type*} [F:fintype α] {β:α → Type*} {M:Π a, measurable_space (β a)}
  (S:Π a, measurable_setB (M a)) (T:set α) [decidable_pred T]:set.pi_measurable T S =
  set.pi_measurable (@set.univ α) (λ (a:α), if (a∈ T) then (S a) else (measurable_setB_univ)) :=
begin
  ext x,
  split;intros A1;
  simp [set.pi_measurable, measurable_setB_univ]; intros a;
  simp [set.pi_measurable, measurable_setB_univ] at A1,
  cases decidable.em (a ∈ T) with A2 A2,
  { rw if_pos, apply A1, apply A2, apply A2 },
  { rw if_neg, simp, apply A2 },
  { intros A3, have A4 := A1 a, rw if_pos A3 at A4, apply A4 },
end
-/

/--
  Often, we use the independence of random variables directly.
  Specifically, many different kinds of relationships are implicitly writable
  in the form X ∈ᵣ C, but it is not necessarily to keep them in that form.
  For example, X =ᵣ 3 can be written as X ∈ᵣ {3}, but it is more convenient
  and clearer in the former form.
  More dramatically, there is a D such that
  (∀ᵣ (s : α) in T,X (b s) ∈ᵣ S s) = ((pi.random_variable_combine X) ∈ᵣ D).
-/
lemma random_variable_independent_pair_apply {Ω α β:Type*}
  {P:probability_space Ω} {Mα:measurable_space α} {Mβ:measurable_space β}
  {X:P→ᵣ Mα} {Y:P →ᵣ Mβ} {A B:event Ω}:
  random_variable_independent_pair X Y →
  (∃ C:measurable_setB Mα, X ∈ᵣ C = A) →
  (∃ D:measurable_setB Mβ, Y ∈ᵣ D = B) →
  independent_event_pair A B :=
begin
  intros h1 h2 h3,
  cases h2 with C h2,
  cases h3 with D h3,
  rw ← h2,
  rw ← h3,
  apply h1,
end

lemma equal_eq_mem_exists {Ω α:Type*} {P:probability_space Ω} {TM:top_measurable α}
  [has_measurable_equality TM.to_measurable_space]
  (X:P →ᵣ TM.to_measurable_space) (a:α):
  ∃ (C:measurable_setB TM.to_measurable_space), (X ∈ᵣ C) = (X =ᵣ a) :=
begin
  apply exists.intro (measurable_setB_top {a}),
  rw equal_eq_mem,
  refl,
end

lemma or_mem_exists {Ω α:Type*} {P:probability_space Ω} {M:measurable_space α}
  (X:P →ᵣ M) (A B:event Ω):
  (∃ (C:measurable_setB M), (X ∈ᵣ C) = A) →
  (∃ (D:measurable_setB M), (X ∈ᵣ D) = B) →
  (∃ (E:measurable_setB M), (X ∈ᵣ E) = (A∨ B))
 :=
begin
  intros h1 h2,
  cases h1 with C h1,
  cases h2 with D h2,
  subst A,
  subst B,
  apply exists.intro (C ∪ D),
  apply event.eq,
  ext ω, simp,
end

/- TODO uncomment
lemma and_mem_exists {Ω α:Type*} {P:probability_space Ω} {M:measurable_space α}
  (X:P →ᵣ M) (A B:event Ω):
  (∃ (C:measurable_setB M), (X ∈ᵣ C) = A) →
  (∃ (D:measurable_setB M), (X ∈ᵣ D) = B) →
  (∃ (E:measurable_setB M), (X ∈ᵣ E) = (A∧ B))
 :=
begin
  intros h1 h2,
  cases h1 with C h1,
  cases h2 with D h2,
  subst A,
  subst B,
  apply exists.intro (C ∩ D),
  apply event.eq,
  ext ω, simp,
end
-/

def ms_Inter {α β:Type*} {M:measurable_space α} (S:finset β) (X:β → measurable_setB M):
  measurable_setB M :=
{ val := (⋂ b ∈ S, (X b).val),
  property := begin
    apply finset_inter_measurable,
    intros b h_b,
    apply (X b).property,
  end}

lemma forall_in_mem_exists {Ω α β:Type*} {P:probability_space Ω} {M:measurable_space α}
  (X:P →ᵣ M) (A:β → event Ω) (T:finset β):
  (∀ b ∈ T, (∃ (C:measurable_setB M), (X ∈ᵣ C) = A b)) →
  (∃ (E:measurable_setB M), (X ∈ᵣ E) = (∀ᵣ b in T, A b)):=
begin
  intros h1,
  have h2:∀ (b:β), (∃ (C:measurable_setB M), (b∈ T) → (X ∈ᵣ C) = A b),
  { intros b, cases classical.em (b∈ T) with h2_1 h2_1,
    { have h2_2 := h1 b h2_1, cases h2_2 with C h2_2,
      apply exists.intro C, intros h2_3, apply h2_2 },
    { apply exists.intro measurable_setB_empty, intros contra, apply absurd contra h2_1,
       } },
  rw classical.skolem at h2,
  cases h2 with f h2,
  apply exists.intro (ms_Inter T f),
  apply event.eq,
  ext1 a,
  split; intros h3; simp [ms_Inter] at h3; simp [ms_Inter, h3];
  intros b h_b,
  { rw ← h2, apply h3, apply h_b, apply h_b },
  { have h4 := h3 b h_b,
    have h5 := h2 b h_b,
    rw ← h5 at h4, apply h4 },
end

lemma joint_random_variable_apply_exists {Ω α β:Type*} [fintype α]
  {P:probability_space Ω}  {Mβ:measurable_space β}
  (X:α → P→ᵣ Mβ) (a:α) (E:event Ω):
  (∃ (C: measurable_setB Mβ), X a ∈ᵣ C = E) →
  (∃ (D : measurable_setB measurable_space.pi),
    pi.random_variable_combine X ∈ᵣ D = E) := begin
  classical,
  intros h1,
  cases h1 with C h1,
  let S := (set.preimage (λ (d:α → β), d a) C.val),
  begin
    have h_meas_S:measurable_set S,
    { apply measurable_pi_apply, apply C.property },
    apply exists.intro (measurable_setB.mk h_meas_S),
    apply event.eq,
    rw ← h1,
    simp [pi.random_variable_combine, pi.measurable_fun, measurable_setB.mk],
  end
end

lemma joint_random_variable_mem_exists {Ω α β:Type*} [fintype α]
  {P:probability_space Ω}  {Mβ:measurable_space β}
  (X:α → P→ᵣ Mβ) (T:finset α) (S:α → measurable_setB Mβ):
  ∃ (D : measurable_setB measurable_space.pi),
    pi.random_variable_combine X ∈ᵣ D = ∀ᵣ (s : α) in T,X s ∈ᵣ S s := begin
  apply forall_in_mem_exists,
  intros b h_b,
  apply joint_random_variable_apply_exists _ b,
  apply exists.intro (S b),
  refl,
end

lemma equiv_cancel_left {α β:Type*} (E:equiv α β) (a:α):E.inv_fun (E a) = a := begin
  have h1 := E.left_inv,
  apply h1,
end

lemma pairwise_disjoint_and_right {Ω α:Type*} {P:probability_space Ω}
  (A:event Ω) (X:α → event Ω):
  pairwise (disjoint on (λ (a:α), (X a).val)) →
  pairwise (disjoint on (λ (a:α), (A ∧ (X a)).val))  :=
begin
  intros h1,
  intros i j h_ne,
  have h2 := h1 i j h_ne,
  simp [function.on_fun] at h2,
  rw disjoint_iff at h2,
  simp at h2,
  simp [function.on_fun],
  rw disjoint_iff,
  simp,
  rw set.inter_comm (↑A) (↑(X j)),
  rw ← set.inter_assoc,
  rw set.inter_assoc (↑A),
  rw h2,
  simp,
end

/- TODO uncomment
lemma Pr_sum_partition {Ω α:Type*} {P:probability_space Ω} {TM:top_measurable α}
  [encodable α]
  [has_measurable_equality TM.to_measurable_space]
  (A:event Ω) (X:P →ᵣ TM.to_measurable_space):
  Pr[A] = ∑' (a:α), Pr[A ∧ (X =ᵣ a)] :=
begin
  classical,
  have h1:A = (eany (λ (a:α), A ∧ (X =ᵣ a))),
  { apply event.eq, ext ω, split; intros h_sub; simp at h_sub;
    simp [h_sub] },
  have h2:Pr[A] = Pr[eany (λ (a:α), A ∧ (X =ᵣ a))],
  { rw ← h1 },
  rw h2,
  rw Pr_eany_sum,
  apply pairwise_disjoint_and_right,
  apply event_eq_disjoint,
end
-/

/- Needed for VC dimension proof connecting training and testing. -/
/- TODO uncomment
lemma conditional_independent_event_pair_limit {Ω α:Type*} {P:probability_space Ω}
  {TM:top_measurable α}
  [encodable α]
  [has_measurable_equality TM.to_measurable_space]
  (A B:event Ω) (X:P →ᵣ TM.to_measurable_space) (p:nnreal):
  (∀ (a:α), Pr[A ∧ (X =ᵣ a)] * p ≤ Pr[A ∧ B ∧ (X =ᵣ a)]) →
  (Pr[A] * p ≤ Pr[A ∧ B])  :=
begin
  classical,
  intros h1,
  rw Pr_sum_partition A X,
  rw Pr_sum_partition (A∧ B) X,
  rw mul_comm,
  rw ← summable.tsum_mul_left,
  apply tsum_le_tsum,
  { intros a, rw mul_comm,
    have h3:((A ∧ B)∧ (X =ᵣ a)) = (A∧B∧(X =ᵣ a)),
    { apply event.eq, ext ω, split; intros h_sub1; simp at h_sub1;
      simp [h_sub1] },
    rw h3, apply h1 },
  apply summable.mul_left,
  repeat { apply Pr_disjoint_summable,
    apply pairwise_disjoint_and_right,
    apply event_eq_disjoint },
end
-/

lemma compose_independent_pair_left {α β γ Ω:Type*} {P:probability_space Ω}  {Mα:measurable_space α}
  {Mβ:measurable_space β} {Mγ:measurable_space γ}
{X:P →ᵣ Mα} {Y:P →ᵣ Mβ} {Z:Mα →ₘ Mγ}:random_variable_independent_pair X Y →
random_variable_independent_pair (Z ∘r X) Y := begin
  intros h1,
  intros A B,
  rw rv_compose_measurable_setB,
  apply h1,
end

/- TODO uncomment
lemma compose_independent_pair_right {α β γ Ω:Type*} {P:probability_space Ω} {Mα:measurable_space α}
  {Mβ:measurable_space β} {Mγ:measurable_space γ}
{X:P →ᵣ Mα} {Y:P →ᵣ Mβ} {Z:Mβ →ₘ Mγ}:random_variable_independent_pair X Y →
random_variable_independent_pair X (Z ∘r Y) := begin
  intros h1,
  intros A B,
  rw rv_compose_measurable_setB,
  apply h1,
end
-/

end probability_theory
