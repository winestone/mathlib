/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import analysis.normed_space.inner_product
import measure_theory.set_integral

/-! # Conditional expectation

-/

noncomputable theory
open topological_space measure_theory measure_theory.Lp filter
open_locale nnreal ennreal topological_space

namespace measure_theory

variables {α E F G 𝕜 : Type*} [is_R_or_C 𝕜] {p : ℝ≥0∞}
  [measurable_space E] [inner_product_space 𝕜 E] [borel_space E] [second_countable_topology E]
  [normed_group F] [measurable_space F] [borel_space F] [second_countable_topology F]
  [normed_group G] [measurable_space 𝕜] [borel_space 𝕜]

lemma ae_measurable'.add {α β} (m : measurable_space α) [measurable_space α] [measurable_space β]
  [topological_space β] [borel_space β] [has_add β] [has_continuous_add β]
  [second_countable_topology β]
  {f g : α → β} {μ : measure α} (hf : ae_measurable' m f μ) (hg : ae_measurable' m g μ) :
  ae_measurable' m (f + g) μ :=
begin
  refine ⟨hf.mk f + hg.mk g, _, _⟩,
  exact @measurable.add _ _ _ _ _ m _ _ _ _ _ hf.measurable_mk hg.measurable_mk,
  exact eventually_eq.comp₂ hf.ae_eq_mk (+) hg.ae_eq_mk,
end

lemma ae_measurable'.smul {α} (m : measurable_space α) [measurable_space α]
  {f : α → E} {μ : measure α} (hf : ae_measurable' m f μ) (c : 𝕜) :
  ae_measurable' m (c • f) μ :=
begin
  refine ⟨c • hf.mk f, _, _⟩,
  exact @measurable.const_smul _ m _ _ _ _ _ _ _ _ _ _ _ hf.measurable_mk c,
  exact eventually_eq.fun_comp hf.ae_eq_mk (λ x, c • x),
end

def Lp_sub {α} (m : measurable_space α) {m0 : measurable_space α} (𝕜 E) [is_R_or_C 𝕜]
  [measurable_space 𝕜] [borel_space 𝕜]
  [measurable_space E] [inner_product_space 𝕜 E] [borel_space E] [second_countable_topology E]
  (p : ℝ≥0∞) (μ : measure α) :
  submodule 𝕜 (Lp E p μ) :=
{ carrier := {f : (Lp E p μ) | ae_measurable' m f μ} ,
  zero_mem' := ⟨(0 : α → E),@measurable_zero _ α _ m _, Lp.coe_fn_zero _ _ _,⟩,
  add_mem' := λ f g hf hg,
    ae_measurable'.congr (ae_measurable'.add m hf hg) (Lp.coe_fn_add f g).symm,
  smul_mem':= λ c f hf,
    ae_measurable'.congr (ae_measurable'.smul m hf c) (Lp.coe_fn_smul c f).symm, }

lemma mem_Lp_sub_iff_ae_measurable' {α} {m m0 : measurable_space α} {𝕜 E}
  [is_R_or_C 𝕜] [measurable_space 𝕜] [borel_space 𝕜]
  [measurable_space E] [inner_product_space 𝕜 E] [borel_space E]
  [second_countable_topology E] {p : ℝ≥0∞} {μ : measure α} {f : Lp E p μ} :
  f ∈ Lp_sub m 𝕜 E p μ ↔ ae_measurable' m f μ :=
by simp_rw [← submodule.mem_coe, ← submodule.mem_carrier, Lp_sub, set.mem_set_of_eq]

lemma Lp_sub.ae_measurable' {α} {m m0 : measurable_space α} {𝕜 E}
  [is_R_or_C 𝕜] [measurable_space 𝕜] [borel_space 𝕜]
  [measurable_space E] [inner_product_space 𝕜 E] [borel_space E]
  [second_countable_topology E] {p : ℝ≥0∞} {μ : measure α} (f : Lp_sub m 𝕜 E p μ) :
  ae_measurable' m f μ :=
mem_Lp_sub_iff_ae_measurable'.mp f.mem

lemma mem_Lp_sub_self {α} {m0 : measurable_space α} (𝕜 E) [is_R_or_C 𝕜]
  [measurable_space 𝕜] [borel_space 𝕜] [measurable_space E] [inner_product_space 𝕜 E]
  [borel_space E] [second_countable_topology E] (p : ℝ≥0∞) (μ : measure α) (f : Lp E p μ) :
  f ∈ Lp_sub m0 𝕜 E p μ :=
by { rw mem_Lp_sub_iff_ae_measurable', exact (Lp.ae_measurable f), }

lemma Lp_sub_coe {α 𝕜 E} {m m0 : measurable_space α} [is_R_or_C 𝕜] [measurable_space 𝕜]
  [borel_space 𝕜] [measurable_space E] [inner_product_space 𝕜 E] [borel_space E]
  [second_countable_topology E]
  {p : ℝ≥0∞} {μ : measure α} {f : Lp_sub m 𝕜 E p μ} :
  ⇑f = (f : Lp E p μ) :=
coe_fn_coe_base f

lemma ae_measurable'.tendsto {α β} {m : measurable_space α} [measurable_space α]
  [measurable_space β] [topological_space β] {μ : measure α} {f : ℕ → α → β}
  (hf : ∀ n, ae_measurable' m (f n) μ) {f_lim : α → β} (h_lim : tendsto f at_top (𝓝 f_lim)) :
  ae_measurable' m f_lim μ :=
sorry

lemma ae_measurable'.tendsto_Lp [hp : fact(1 ≤ p)] {α 𝕜 E} {m : measurable_space α}
  [measurable_space α] {μ : measure α} [is_R_or_C 𝕜]
  [measurable_space E] [inner_product_space 𝕜 E] [borel_space E] [second_countable_topology E]
  {f : ℕ → Lp E p μ}
  (hf : ∀ n, ae_measurable' m (f n) μ) {f_lim : Lp E p μ} (h_lim : tendsto f at_top (𝓝 f_lim)) :
  ae_measurable' m f_lim μ :=
sorry

instance {α} (m : measurable_space α) {m0 : measurable_space α} {μ : measure α}
  [complete_space E] [hp : fact(1 ≤ p)] : complete_space (Lp_sub m 𝕜 E p μ) :=
begin
  refine metric.complete_of_cauchy_seq_tendsto (λ f hf_cau, _),
  let f' := λ n, (f n : Lp E p μ),
  have hf'_cau : cauchy_seq f',
  { rw cauchy_seq_iff_tendsto_dist_at_top_0 at hf_cau ⊢,
    have hff' : ∀ n : ℕ × ℕ, dist (f' n.fst) (f' n.snd) = dist (f n.fst) (f n.snd),
    { rw [prod.forall],
      intros n m,
      simp_rw [dist_eq_norm, f', ← submodule.coe_sub, submodule.norm_coe], },
    simp_rw hff',
    exact hf_cau, },
  obtain ⟨f_lim, h_lim'⟩ := cauchy_seq_tendsto_of_complete hf'_cau,
  suffices h_sub : f_lim ∈ Lp_sub m 𝕜 E p μ,
  { have h_lim : tendsto f at_top (𝓝 ⟨f_lim, h_sub⟩),
    { rw tendsto_iff_dist_tendsto_zero at h_lim' ⊢,
      have h_lim_coe : ∀ b, dist (f b) ⟨f_lim, h_sub⟩ = dist (f' b) f_lim,
      { intro b,
        have h_dist_coe : dist (f' b) f_lim = dist (f' b) (⟨f_lim, h_sub⟩ : Lp_sub m 𝕜 E p μ),
          by congr,
        simp_rw [h_dist_coe, dist_eq_norm, f', ← submodule.coe_sub, submodule.norm_coe], },
      simp_rw h_lim_coe,
      exact h_lim', },
    exact ⟨⟨f_lim, h_sub⟩, h_lim⟩, },
  rw mem_Lp_sub_iff_ae_measurable',
  refine ae_measurable'.tendsto_Lp (λ n, _) h_lim',
  simp_rw [f', ← Lp_sub_coe],
  exact Lp_sub.ae_measurable' (f n),
end

def is_conditional_expectation (m : measurable_space α) [m0 : measurable_space α] {μ : measure α}
  [normed_group E] [borel_space E] [second_countable_topology E] [complete_space E]
  [normed_space ℝ E]
  (f : α →ₘ[μ] E) (g : α →ₘ[μ] E) (hg : integrable g μ) : Prop :=
integrable f μ ∧ ae_measurable' m f μ
  ∧ ∀ s (hs : @measurable_set α m s), ∫ a in s, f a ∂μ = ∫ a in s, g a ∂μ

/-- Conditional expectation of a function in L2 with respect to a sigma-algebra -/
def condexp_L2 [complete_space E] (m : measurable_space α) [m0 : measurable_space α] {μ : measure α}
  (f : Lp E 2 μ) :
  Lp_sub m 𝕜 E 2 μ :=
begin
  haveI ips : inner_product_space 𝕜 (Lp E 2 μ) := sorry,
  let proj := @orthogonal_projection 𝕜 (Lp E 2 μ) _ ips (Lp_sub m 𝕜 E 2 μ) _,
  exact proj f,
end


end measure_theory
