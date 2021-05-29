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
Author: Martin Zinkevich (modified for mathlib by Hunter Monroe)
 -/

import measure_theory.measurable_space

/-- The smallest σ-algebra containing a collection `s` of basic sets -/
inductive generate_measurable {α : Type*} (s : set (set α)) : set α → Prop
| basic : ∀ u ∈ s, generate_measurable u
| empty : generate_measurable ∅
| compl : ∀ s, generate_measurable s → generate_measurable sᶜ
| union : ∀ f : ℕ → set α, (∀ n, generate_measurable (f n)) → generate_measurable (⋃ i, f i)

lemma generate_from_self {α:Type*}
  (M:measurable_space α):
  M = measurable_space.generate_from {s : set α|measurable_space.measurable_set' M s} :=
begin
  ext,
  split;intros a,
    apply measurable_space.generate_measurable.basic,
    apply a,
    induction a,
      apply a_H,
      apply measurable_space.measurable_set_empty,
      apply measurable_space.measurable_set_compl,
      apply a_ih,
      apply measurable_space.measurable_set_Union,
      apply a_ih,
end

lemma measurable_fun_comap_def {α β:Type*}
  [M2:measurable_space β]  (f:α → β):
  measurable_space.comap f M2 = measurable_space.generate_from
  {s : set α|∃ (s' : set β), measurable_space.measurable_set' M2 s' ∧ f ⁻¹' s' = s} :=
begin
  unfold measurable_space.comap,
  apply generate_from_self,
end

def finset_fintype {α:Type*} (S:finset α):fintype {a:α|a∈ S} := {
  elems := finset.attach S,
  complete :=  S.mem_attach,
}

lemma finite_finset {α:Type*} (S:finset α):set.finite {a:α| a∈ S} :=
begin
  unfold set.finite,
  apply nonempty.intro (finset_fintype S),
end

lemma finset_inter_measurable {α:Type*} {T:finset α} {β:Type*} [measurable_space β] {U:α → set β}:
  (∀ t∈ T, measurable_set (U t)) →
  measurable_set (⋂ x ∈ T, U x) :=
begin
  intros a,
  have A1:(set.sInter (set.image U ({a|a∈ T}:set α))) = (⋂ x ∈ T, U x),
  {
    simp,
  },
  rw ← A1,
  apply measurable_set.sInter,
  {
    apply set.countable.image,
    apply set.finite.countable,
    apply finite_finset,
  },
  {
    intros,
    simp at H,
    cases H with x H,
    cases H with A2 A3,
    subst t,
    apply a,
    exact A2,
  }
end

lemma finset_union_measurable {α:Type*} {T:finset α} {β:Type*} [measurable_space β] {U:α → set β}:
  (∀ t∈ T, measurable_set (U t)) →
  measurable_set (⋃ x ∈ T, U x) :=
begin
  intros a,
  have A1:(set.sUnion (set.image U ({a|a∈ T}:set α))) = (⋃ x ∈ T, U x),
    simp,
  rw ← A1,
  apply measurable_set.sUnion,
    apply set.countable.image,
    apply set.finite.countable,
    apply finite_finset,
    intros,
    simp at H,
    cases H with x H,
    cases H with A2 A3,
    subst t,
    apply a,
    exact A2,
end

lemma measurable_def {α β:Type*}
  [M1:measurable_space α] [M2:measurable_space β] (f:α → β):
  (∀ B:(set β), (measurable_set B) → measurable_set (f ⁻¹' B))
  ↔ (measurable f) :=
begin
  unfold measurable,
end

lemma measurable_elim {α β:Type*}
  [measurable_space α] [measurable_space β] (f:α → β) (B:set β):
  (measurable f)→ (measurable_set B) → (measurable_set (f ⁻¹' B)) :=
begin
  intros a a_1,
  apply (measurable_def _).mpr,
  apply a,
  apply a_1,
end
