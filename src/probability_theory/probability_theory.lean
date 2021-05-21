/-
Copyright 2021 Google LLC

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

      http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
Authors: Martin Zinkevich (modified for mathlib by Hunter Monroe)
 -/

import measure_theory.measurable_space
import measure_theory.measure_space


/-! This file defines the basic concepts in probability theory.
    There are four fundamental principles:
    1. Make theorems as readable as possible. Use Pr[A ∧ B], not μ (A ∩ B). Other examples:
       Pr[(X >ᵣ 3) ∨ (Y =ᵣ 7)]. While events are technically sets, in probability theory,
       they are better written as propositions that may or may not hold.
    2. Avoid absurd statements where possible. Don't allow Pr[A] if A is not an event,
       or Pr[X ∈ᵣ S] if S is not measurable, or Pr[∀ᵣ a in S, E a] if S is not countable.
       It is always possible to write Pr[⟨S, ...proof S is an event...⟩].
    3. Embed measurability into the objects and operations themselves. An event is measurable by
       definition. When we take the and, or, not, for all, exists, measurability should be automatic.
    4. Don't expect the reader to know measure theory, but at times it may be required by the
       author.

    Several concepts are defined in this module:
      probability_space: a measure_space where the measure has a value of 1.
      measurable_set_sub: a subtype of a set that is measurable (defined based upon the measurable space).
      event: a measurable_set_sub on a probability space (defined based upon the probability).
      Pr[E]: the probability of an event (note: expectations are defined in real_random_variable).
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

class probability_space (α: Type*) extends measure_theory.measure_space α :=
  (univ_one : volume (set.univ) = 1)

instance probability_space.to_measurable_space (α:Type*) [probability_space α]:measurable_space α :=
  measure_theory.measure_space.to_measurable_space

/-
  In measure theory (and specifically, in probability theory), not all sets of outcomes have
  probabilities that can be measured. We represent those that can be measured as measurable
  sets.
-/
def measurable_set_sub {α:Type*} (M:measurable_space α):Type* := subtype (M.measurable_set')

def measurable_set_sub.mk {α:Type*} {M:measurable_space α} {S:set α} (H:measurable_set S):measurable_set_sub M := ⟨S, H⟩

lemma measurable_set_sub_val_eq_coe {Ω:Type*} {P:measurable_space Ω}
  (X:measurable_set_sub P):X.val =
  (@coe (subtype (@measurable_set Ω _)) (set Ω) _ X) :=
begin
  refl
end

/-
  A measurable set on a measurable space that has a probability measure is called an event.
-/
def event {Ω:Type*} (M:probability_space Ω):Type* := measurable_set_sub (probability_space.to_measurable_space Ω)

lemma event_val_eq_coe {Ω:Type*} {P:probability_space Ω}
  (X:event P):X.val =
  (@coe (subtype (@measurable_set Ω _)) (set Ω) _ X) :=
begin
  refl
end

lemma event.eq {Ω:Type*} {P:probability_space Ω} (A B:event P):
A.val = B.val → A = B :=
begin
  intro A1,
  apply subtype.eq,
  exact A1
end

def event_mem {Ω:Type*} [P:probability_space Ω] (a:Ω) (E:event P):Prop :=
  a∈ E.val

instance {Ω:Type*} [P:probability_space Ω]:has_mem Ω (event P) := {
  mem := event_mem
}

lemma event_mem_val {Ω:Type*} [P:probability_space Ω] (ω:Ω) (E:event P):
  (ω ∈ E) = (ω ∈ E.val) := rfl


lemma prob_le_1 {Ω:Type*} {P:probability_space Ω} (S:set Ω):
  P.volume.measure_of S ≤ 1 :=
begin
  have A1:P.volume.measure_of set.univ = 1,
  {
    apply P.univ_one,
  },
  have A2:S ⊆ set.univ,
  {
    simp,
  },
  have A3:P.volume.measure_of S ≤ P.volume.measure_of set.univ,
  {
    apply P.volume.mono,
    apply A2,
  },
  rw A1 at A3,
  exact A3,
end

/-
  There are a lot of long proofs here, but this one seems particularly roundabout.
-/
lemma prob_not_infinite {Ω:Type*} {P:probability_space Ω} (S:set Ω):
  (P.volume.measure_of S) ≠ ⊤ :=
begin
  have A1:P.volume.measure_of S ≤ 1,
  {
     apply prob_le_1,
  },
  intro A2,
  rw A2 at A1,
  have A3:(1:ennreal)=⊤,
  {
    apply complete_linear_order.le_antisymm,
    {
      apply (ennreal.complete_linear_order.le_top),
    },
    {
      apply A1,
    }
  },
  have A4:(1:ennreal) ≠ (⊤:ennreal),
  {
    apply ennreal.one_ne_top,
  },
  rw A3 at A4,
  apply A4,
  refl,
end

lemma prob_nnreal {Ω:Type*} {P:probability_space Ω} (S:set Ω):
   ↑((P.volume.measure_of S).to_nnreal) = P.volume.measure_of S :=
begin
  apply ennreal.coe_to_nnreal,
  apply prob_not_infinite,
end

def event_prob {Ω:Type*} {P:probability_space Ω} (E:event P):nnreal :=
  (P.volume.measure_of E.val).to_nnreal

notation `Pr[`E`]` := event_prob E

lemma event_prob_def {Ω:Type*} {p:probability_space Ω} (E:event p):
  ↑(Pr[E]) = (p.volume.measure_of E.val):=
begin
  unfold event_prob,
  apply prob_nnreal,
end

lemma to_nnreal_almost_monotonic (a b:ennreal):(a≠ ⊤)→(b≠⊤)→(a ≤ b)→ (a.to_nnreal ≤ b.to_nnreal) :=
begin
  intros A1 A2 A3,
  have A4:↑(a.to_nnreal)=a,
  {
    apply ennreal.coe_to_nnreal,
    apply A1,
  },
  have A5:↑(b.to_nnreal)=b,
  {
    apply ennreal.coe_to_nnreal,
    apply A2,
  },
  rw ← A4 at A3,
  rw ← A5 at A3,
  simp at A3,
  apply A3,
end

lemma to_ennreal_monotonic (a b:nnreal):(a ≤ b)→ ((a:ennreal) ≤ (b:ennreal)) :=
begin
  intro A1,
  simp,
  apply A1,
end

-- See ennreal.add_eq_top
lemma add_finite (a b:ennreal):(a≠ ⊤) → (b≠ ⊤) → (a + b≠ ⊤) :=
begin
  intros A1 A2 A3,
  rw ennreal.add_eq_top at A3,
  cases A3,
  {
    apply A1,
    apply A3,
  },
  {
    apply A2,
    apply A3,
  }
end


lemma event_prob_mono1 {Ω:Type*} {p:probability_space Ω} (E F:event p):
  p.volume.measure_of E.val ≤ p.volume.measure_of F.val →
  Pr[E] ≤ Pr[F] :=
begin
  unfold event_prob,
  intro A1,
  apply to_nnreal_almost_monotonic,
  apply prob_not_infinite,
  apply prob_not_infinite,
  apply A1,
end

lemma event_prob_mono2 {Ω:Type*} {p:probability_space Ω} (E F:event p):
  (E.val ⊆ F.val) →
  Pr[E] ≤ Pr[F] :=
begin
  intro A1,
  apply event_prob_mono1,
  apply p.volume.mono,
  apply A1,
end

def measurable_set_sub_univ {Ω:Type*} {M:measurable_space Ω}:measurable_set_sub M  := {
  val := set.univ,
  property := measurable_set.univ,
}

def event_univ {Ω:Type*} {p:probability_space Ω}:event p := measurable_set_sub_univ

@[simp]
lemma event_univ_val_def {Ω:Type*} {p:probability_space Ω}:
  (@event_univ Ω p).val = set.univ :=
begin
  unfold event_univ measurable_set_sub_univ,
end

@[simp]
lemma Pr_event_univ {Ω:Type*} {p:probability_space Ω}:
  Pr[@event_univ Ω p] = 1 :=
begin
  have A1:↑(Pr[@event_univ Ω p]) = (1:ennreal),
  {
    rw event_prob_def,
    apply p.univ_one,
  },
  simp at A1,
  apply A1
end

@[simp]
lemma Pr_le_one {Ω:Type*} {p:probability_space Ω} {E:event p}:
  Pr[E] ≤ 1 :=
begin
  have A1:Pr[E] ≤ Pr[@event_univ Ω p],
  {
    apply event_prob_mono2,
    rw event_univ_val_def,
    rw set.subset_def,simp,
  },
  rw Pr_event_univ at A1,
  apply A1,
end

def measurable_set_sub_empty {Ω:Type*} {p:measurable_space Ω}:measurable_set_sub p := {
  val := ∅,
  property := measurable_set.empty,
}

instance has_emptyc_measurable_set_sub {Ω:Type*} {M:measurable_space Ω}:has_emptyc (measurable_set_sub M) := ⟨ @measurable_set_sub_empty Ω M ⟩

def event_empty {Ω:Type*} {p:probability_space Ω}:event p :=
  @measurable_set_sub_empty Ω (probability_space.to_measurable_space Ω)

instance has_emptyc_event {Ω:Type*} {P:probability_space Ω}:has_emptyc (event P) :=
    ⟨ @event_empty Ω P ⟩

lemma has_emptyc_emptyc_event {Ω:Type*} {P:probability_space Ω}:
  ∅ = (@event_empty Ω P) :=  rfl

@[simp]
lemma event_empty_val_def {Ω:Type*} {p:probability_space Ω}:
  (@event_empty Ω p).val = ∅  := rfl

@[simp]
lemma event_empty_val_def2 {Ω:Type*} {p:probability_space Ω}:
  (@has_emptyc.emptyc (event p) _).val = ∅  :=  rfl

@[simp]
lemma Pr_event_empty {Ω:Type*} {p:probability_space Ω}:
  Pr[@event_empty Ω p] = 0 :=
begin
  have A1:↑(Pr[@event_empty Ω p]) = (0:ennreal),
  {
    rw event_prob_def,
    apply p.volume.empty,
  },
  simp at A1,
  apply A1
end

@[simp]
lemma Pr_event_empty' {Ω:Type*} {p:probability_space Ω}:
  Pr[(∅:event p)] = 0 :=
begin
  rw has_emptyc_emptyc_event,
  apply Pr_event_empty,
end

/-Since Pr[E] is a nnreal, this establishes that the probability is in the interval [0,1] -/
lemma event_prob_le_1 {Ω:Type*} {p:probability_space Ω} {E:event p}:
  Pr[E] ≤ 1 :=
begin
  have A1:Pr[@event_univ Ω p] = 1,
  {
    apply Pr_event_univ,
  },
  rw ← A1,
  apply event_prob_mono2,
  rw event_univ_val_def,
  simp,
end

def event_const {Ω:Type*} {p:probability_space Ω} (P:Prop):event p := {
  val := {ω:Ω|P},
  property := measurable_set.const P,
}

@[simp]
lemma event_const_val_def {Ω:Type*} {p:probability_space Ω} (P:Prop):
  (@event_const _ p P).val={ω:Ω|P} := rfl

lemma event_const_true_eq_univ {Ω:Type*} {p:probability_space Ω} (P:Prop):P →
(@event_const _ p P)=event_univ :=
begin
  intro A1,
  apply event.eq,
  simp [A1],
end

lemma event_const_false_eq_empty {Ω:Type*} {p:probability_space Ω} (P:Prop):¬P →
(@event_const _ p P)=event_empty :=
begin
  intro A1,
  apply event.eq,
  simp [A1],
end

lemma Pr_event_const_true {Ω:Type*} {p:probability_space Ω} (P:Prop):P →
Pr[(@event_const _ p P)]=1 :=
begin
  intro A1,
  rw event_const_true_eq_univ,
  apply Pr_event_univ,
  exact A1,
end

lemma Pr_event_const_false {Ω:Type*} {p:probability_space Ω} (P:Prop):¬P →
Pr[(@event_const _ p P)]=0 :=
begin
  intro A1,
  rw event_const_false_eq_empty,
  apply Pr_event_empty,
  exact A1,
end

--The and of two events.

def measurable_inter {Ω:Type*} {p:measurable_space Ω} (A B:measurable_set_sub p):measurable_set_sub p := {
  val:=A.val ∩ B.val,
  property := measurable_set.inter A.property B.property,
}

@[simp]
lemma measurable_inter_val_def {Ω:Type*} {p:measurable_space Ω} (A B:measurable_set_sub p):
  (measurable_inter A B).val= A.val ∩ B.val := rfl

instance measurable_set_sub_has_inter {Ω:Type*} {p:measurable_space Ω}:has_inter (measurable_set_sub p) := {
  inter := @measurable_inter Ω p,
}

@[simp]
lemma measurable_inter_val_def2 {Ω:Type*} {p:measurable_space Ω} (A B:measurable_set_sub p):
  (A ∩ B).val= A.val ∩ B.val := rfl


def eand {Ω:Type*} {p:probability_space Ω} (A B:event p):event p :=
  measurable_inter A B

infixr `∧` := eand

@[simp]
lemma eand_val_def {Ω:Type*} {p:probability_space Ω} (A B:event p):
  (A ∧ B).val = A.val ∩ B.val :=
begin
  refl,
end

lemma eand_comm {Ω:Type*} {p:probability_space Ω} (A B:event p):
  (A ∧ B) = (B ∧ A) :=
begin
  apply event.eq,
  simp [set.inter_comm],
end

lemma eand_assoc {Ω:Type*} {p:probability_space Ω} (A B C:event p):
  ((A ∧ B) ∧ C) = (A ∧ (B ∧ C)) :=
begin
  apply event.eq,
  simp [set.inter_assoc],
end

lemma eand_eq_self_of_subset_left {Ω:Type*} {p:probability_space Ω} (A B:event p):
  (A.val ⊆ B.val) →
  (A ∧ B) = A :=
begin
  intro A1,
  apply event.eq,
  simp,
  --rw eand_val_def,
  apply set.inter_eq_self_of_subset_left,
  exact A1,
end

lemma eand_eq_self_of_subset_right {Ω:Type*} {p:probability_space Ω} (A B:event p):
  (B.val ⊆ A.val) →
  (A ∧ B) = B :=
begin
  intro A1,
  rw eand_comm,
  apply eand_eq_self_of_subset_left,
  exact A1,
end

lemma Pr_eand_le_left {Ω:Type*} {p:probability_space Ω} (A B:event p):
  Pr[A ∧ B]≤ Pr[A] :=
begin
  apply event_prob_mono2,
  rw eand_val_def,
  apply set.inter_subset_left,
end

lemma Pr_eand_le_right {Ω:Type*} {p:probability_space Ω} (A B:event p):
  Pr[A ∧ B]≤ Pr[B] :=
begin
  rw eand_comm,
  apply Pr_eand_le_left,
end

lemma Pr_eand_le_min {Ω:Type*} {p:probability_space Ω} (A B:event p):
  Pr[A ∧ B]≤ min Pr[A]  Pr[B] :=
begin
  apply le_min,
  {
    apply Pr_eand_le_left,
  },
  {
    apply Pr_eand_le_right,
  }
end

def measurable_union {Ω:Type*} {p:measurable_space Ω} (A B:measurable_set_sub p):measurable_set_sub p := {
  val:=A.val ∪  B.val,
  property := measurable_set.union A.property B.property,
}

@[simp]
lemma measurable_union_val_def {Ω:Type*} {p:measurable_space Ω} (A B:measurable_set_sub p):
  (measurable_union A B).val=A.val ∪ B.val := rfl

instance measurable_set_sub_has_union {Ω:Type*} {p:measurable_space Ω}:has_union (measurable_set_sub p) := {
  union := @measurable_union Ω p,
}

@[simp]
lemma measurable_union_val_def2 {Ω:Type*} {p:measurable_space Ω} (A B:measurable_set_sub p):
  (A ∪ B).val = A.val ∪ B.val := rfl


def eor {Ω:Type*} {p:probability_space Ω} (A B:event p):event p := measurable_union A B

infixr `∨` := eor

@[simp]
lemma eor_val_def {Ω:Type*} {p:probability_space Ω} (A B:event p):
  (A ∨ B).val = A.val ∪ B.val :=
begin
  refl,
end

lemma eor_comm {Ω:Type*} {p:probability_space Ω} (A B:event p):
  (A ∨ B) = (B ∨ A) :=
begin
  apply event.eq,
  simp [set.union_comm],
end

lemma Pr_le_eor_left {Ω:Type*} {p:probability_space Ω} (A B:event p):
  Pr[A] ≤ Pr[A ∨ B] :=
begin
  apply event_prob_mono2,
  simp,
end

lemma Pr_le_eor_right {Ω:Type*} {p:probability_space Ω} (A B:event p):
   Pr[B] ≤ Pr[A ∨ B] :=
begin
  rw eor_comm,
  apply Pr_le_eor_left,
end

lemma Pr_le_eor_sum {Ω:Type*} {p:probability_space Ω} (A B:event p):
  Pr[A ∨ B]≤ Pr[A] + Pr[B] :=
begin
  have A1:↑(Pr[A ∨ B])≤ (Pr[A]:ennreal) + (Pr[B]:ennreal),
  {
    repeat {rw event_prob_def},
    simp,
    apply measure_theory.outer_measure.union,
  },
  have A2:↑(Pr[A ∨ B])≤ ((Pr[A] + Pr[B]):ennreal) → Pr[A ∨ B]≤ Pr[A] + Pr[B],
  {
    apply to_nnreal_almost_monotonic,
    {
      rw event_prob_def,
      apply prob_not_infinite,
    },
    {
      apply add_finite,
      rw event_prob_def,
      apply prob_not_infinite,
      rw event_prob_def,
      apply prob_not_infinite,
    }
  },
  apply A2,
  apply A1,
end

lemma Pr_disjoint_eor {Ω:Type*} {p:probability_space Ω} (A B:event p):
  disjoint A.val B.val →
  Pr[A ∨ B] =  Pr[A] + Pr[B] :=
begin
  intro A1,
  have A2:↑(Pr[A ∨ B])= (Pr[A]:ennreal) + (Pr[B]:ennreal),
  {
    repeat {rw event_prob_def},
    simp,
    apply measure_theory.measure_union,
    apply A1,
    apply A.property,
    apply B.property,
  },
  have A3:((Pr[A ∨ B]):ennreal).to_nnreal= ((Pr[A]:ennreal) + (Pr[B]:ennreal)).to_nnreal,
  {
    rw A2,
  },
  simp at A3,
  apply A3,
end

def enot {Ω:Type*} {p:probability_space Ω} (A:event p):event p := {
  val:=(A).valᶜ,
  property := measurable_set.compl A.property,
}

prefix `¬ₑ` :100 := enot

@[simp]
lemma enot_val_def {Ω:Type*} {p:probability_space Ω} (A:event p):
  (¬ₑ A).val = (A.val)ᶜ :=
begin
  refl,
end

/-
  Double negation elimination. However, it is hard to avoid in measure theory.
-/
@[simp]
lemma enot_enot_eq_self {Ω:Type*} {p:probability_space Ω} (A:event p):
  (¬ₑ (¬ₑ A)) = (A) :=
begin
  apply event.eq,
  simp,
end

instance measurable_set_sub_has_compl {α:Type*} [M:measurable_space α]:has_compl (@measurable_set_sub α M) := {
  compl := λ E, ⟨ E.valᶜ, measurable_set.compl E.property⟩,
}

instance has_sdiff.measurable_set_sub {α:Type*} {M:measurable_space α}:
  has_sdiff (measurable_set_sub M) := ⟨λ E F, E ∩ Fᶜ⟩

instance has_sdiff.event {α:Type*} {M:probability_space α}:
  has_sdiff (event M) := ⟨λ E F, E ∧ ¬ₑ F⟩

@[simp]
lemma has_sdiff_measurable_set_sub_val {α:Type*} {M:measurable_space α} (E F:measurable_set_sub M):
  (E \ F).val = E.val \ F.val := rfl

@[simp]
lemma has_sdiff_event_val {α:Type*} {P:probability_space α} (E F:event P):
  (E \ F).val = E.val \ F.val := rfl

instance measurable_set_sub_subtype_has_neg {α:Type*} [M:measurable_space α]:has_neg (subtype (@measurable_set α M)) := {
  neg := λ E, ⟨ E.valᶜ, measurable_set.compl E.property⟩,
}

lemma measurable_set_sub_neg_def {α:Type*} [M:measurable_space α] {E:@measurable_set_sub α M}:
    Eᶜ = ⟨ E.valᶜ, measurable_set.compl E.property⟩ :=rfl

@[simp]
lemma measurable_set_sub_compl_val_def {α:Type*} [M:measurable_space α] {E:@measurable_set_sub α M}:
    (Eᶜ).val = (E.val)ᶜ  :=rfl

instance event_has_compl {α:Type*} [M:probability_space α]:has_compl (@event α M) := {
  compl := λ E, ⟨E.valᶜ, measurable_set.compl E.property⟩,
}

lemma event_neg_def {α:Type*} [M:probability_space α] {E:@event α M}:
    Eᶜ = ⟨ E.valᶜ, measurable_set.compl E.property⟩ :=rfl

@[simp]
lemma event_neg_val_def {α:Type*} [M:probability_space α] {E:@event α M}:
    (Eᶜ).val = (E.val)ᶜ := rfl

@[simp]
lemma em_event {Ω:Type*} {p:probability_space Ω} (A:event p):
    (A ∨ (¬ₑ A))=event_univ :=
begin
  apply event.eq,
  simp,
end

lemma compl_eor_eq_compl_eand_compl {Ω:Type*} {p:probability_space Ω} (A B:event p):
  (A ∨ B)ᶜ = (Aᶜ ∧ Bᶜ) := begin
  apply event.eq,
  simp,
end

lemma Pr_add_enot_eq_1 {Ω:Type*} {p:probability_space Ω} (A:event p):
  Pr[A] + Pr[¬ₑ A] = 1 :=
begin
  have A1:disjoint (A.val) (enot A).val,
  {
    unfold disjoint,
    rw enot_val_def,
    simp,
  },
  have A2:(A∨ (¬ₑ A)) = event_univ,
  {
    apply em_event,
  },
  have A3:Pr[A∨ (¬ₑ A)] = Pr[event_univ],
  {
    rw A2,
  },
  rw Pr_event_univ at A3,
  rw Pr_disjoint_eor at A3,
  apply A3,
  apply A1,
end

end probability_theory
