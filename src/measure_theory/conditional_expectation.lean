/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import analysis.normed_space.inner_product
import measure_theory.l1_space

/-! # Conditional expectation

-/

noncomputable theory
open topological_space measure_theory measure_theory.Lp filter
open_locale nnreal ennreal topological_space

namespace measure_theory

variables {α E F G 𝕜 : Type*} [is_R_or_C 𝕜] {p : ℝ≥0∞}
  [measurable_space E] [inner_product_space 𝕜 E] [borel_space E] [second_countable_topology E]
  [normed_group F] [measurable_space F] [borel_space F] [second_countable_topology F]
  [normed_group G]

/-- ae_measurable with mk being m-measurable -/
def ae_measurable_sub {α β} (m : measurable_space α) [measurable_space α] [measurable_space β]
  (f : α → β) (μ : measure α . measure_theory.volume_tac) : Prop :=
∃ g : α → β, (@measurable α β m _ g) ∧ f =ᵐ[μ] g

lemma ae_measurable.sub_self {α β} [m0 : measurable_space α] [measurable_space β]
  {f : α → β} {μ : measure α} (hf : ae_measurable f μ) :
  ae_measurable_sub m0 f μ :=
hf

lemma ae_measurable_sub.add {α β} (m : measurable_space α) [measurable_space α] [measurable_space β]
  [topological_space β] [borel_space β] [has_add β] [has_continuous_add β]
  [second_countable_topology β]
  {f g : α → β} {μ : measure α} (hf : ae_measurable_sub m f μ) (hg : ae_measurable_sub m g μ) :
  ae_measurable_sub m (f + g) μ :=
sorry

lemma ae_measurable_sub.smul {α} (m : measurable_space α) [measurable_space α]
  {f : α → E} {μ : measure α} (hf : ae_measurable_sub m f μ) (c : 𝕜) :
  ae_measurable_sub m (c • f) μ :=
sorry

lemma ae_measurable_sub_congr {α β} (m : measurable_space α) [measurable_space α]
  [measurable_space β] [topological_space β] [borel_space β] [has_add β] [has_continuous_add β]
  [second_countable_topology β]
  {f g : α → β} {μ : measure α} (hf : ae_measurable_sub m f μ) (hfg : f =ᵐ[μ] g) :
  ae_measurable_sub m g μ :=
sorry

def Lp_sub {α} (m : measurable_space α) {m0 : measurable_space α} (𝕜 E) [is_R_or_C 𝕜]
  [measurable_space E] [inner_product_space 𝕜 E] [borel_space E] [second_countable_topology E]
  (p : ℝ≥0∞) (μ : measure α) :
  subspace 𝕜 (Lp E p μ) :=
{ carrier := {f : (Lp E p μ) | ae_measurable_sub m f μ} ,
  zero_mem' := ⟨(0 : α → E),@measurable_zero _ α _ m _, Lp.coe_fn_zero _ _ _,⟩,
  add_mem' := λ f g hf hg,
    ae_measurable_sub_congr m (ae_measurable_sub.add m hf hg) (Lp.coe_fn_add f g).symm,
  smul_mem':= λ c f hf,
    ae_measurable_sub_congr m (ae_measurable_sub.smul m hf c) (Lp.coe_fn_smul c f).symm, }

lemma mem_Lp_sub_iff_ae_measurable_sub {α} (m : measurable_space α) {m0 : measurable_space α} {𝕜 E}
  [is_R_or_C 𝕜] [measurable_space E] [inner_product_space 𝕜 E] [borel_space E]
  [second_countable_topology E] {p : ℝ≥0∞} {μ : measure α} (f : Lp E p μ) :
  f ∈ Lp_sub m 𝕜 E p μ ↔ ae_measurable_sub m f μ :=
begin
  rw [← submodule.mem_coe, ← submodule.mem_carrier],
end

lemma mem_Lp_sub_self {α} {m0 : measurable_space α} (𝕜 E) [is_R_or_C 𝕜]
  [measurable_space E] [inner_product_space 𝕜 E] [borel_space E] [second_countable_topology E]
  (p : ℝ≥0∞) (μ : measure α) (f : Lp E p μ) :
  f ∈ Lp_sub m0 𝕜 E p μ :=
begin
  rw [← submodule.mem_coe, ← submodule.mem_carrier],
  simp [Lp_sub, ae_measurable.sub_self (Lp.ae_measurable f)],
end

lemma ae_measurable_sub.lim_at_top {α β} {m : measurable_space α} [measurable_space α]
  [measurable_space β] [topological_space β] [nonempty (α → β)] {μ : measure α} {f : ℕ → α → β} (hf : ∀ n, ae_measurable_sub m (f n) μ) :
  ae_measurable_sub m (lim at_top f) μ :=
sorry

instance {α} (m : measurable_space α) {m0 : measurable_space α} {μ : measure α}
  [complete_space E] [hp : fact(1 ≤ p)] : complete_space (Lp_sub m 𝕜 E p μ) :=
begin
  refine metric.complete_of_cauchy_seq_tendsto _,
  intros f hf_cau,
  let f' := λ n, (f n : Lp E p μ),
  have hf'_cau : cauchy_seq f',
  { sorry},
  have h_lim' := cauchy_seq.tendsto_lim hf'_cau,
  suffices h_sub : lim at_top f' ∈ Lp_sub m 𝕜 E p μ,
  { have h_lim : tendsto f at_top (𝓝 ⟨lim at_top f', h_sub⟩),
    { sorry},
    exact ⟨⟨lim at_top f', h_sub⟩, h_lim⟩, },

end

/-- Conditional expectation of a function in L2 with respect to a sigma-algebra -/
def condexp_L2 (m : measurable_space α) [m0 : measurable_space α] {μ : measure α} (f : Lp E 2 μ) :
  Lp_sub m 𝕜 E 2 μ :=
begin
  sorry
end


end measure_theory
