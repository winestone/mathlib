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
  [normed_group G]
  [measurable_space 𝕜] [borel_space 𝕜]

private lemma add_mem' {α 𝕜 E} {m m0 : measurable_space α} (hm : m ≤ m0) [is_R_or_C 𝕜]
  [measurable_space 𝕜] [borel_space 𝕜]
  [measurable_space E] [inner_product_space 𝕜 E] [borel_space E] [second_countable_topology E]
  {p : ℝ≥0∞} {μ : measure α} (f g : Lp E p μ)
  (hf : ∃ f' : α → E, @measurable α _ m _ f' ∧ f =ᵐ[μ] f')
  (hg : ∃ g' : α → E, @measurable α _ m _ g' ∧ g =ᵐ[μ] g') :
  ∃ f_add : α → E, @measurable α _ m _ f_add ∧ ⇑(f+g) =ᵐ[μ] f_add :=
begin
  rcases hf with ⟨f', h_f'_meas, hff'⟩,
  rcases hg with ⟨g', h_g'_meas, hgg'⟩,
  refine ⟨f'+g', @measurable.add _ α _ _ _ m _ _ _ f' g' h_f'_meas h_g'_meas, _⟩,
  exact eventually_eq.trans (Lp.coe_fn_add f g) (eventually_eq.comp₂ hff' (+) hgg'),
end

private lemma smul_mem' {α 𝕜 E} {m m0 : measurable_space α} (hm : m ≤ m0) [is_R_or_C 𝕜]
  [measurable_space 𝕜] [borel_space 𝕜]
  [measurable_space E] [inner_product_space 𝕜 E] [borel_space E] [second_countable_topology E]
  {p : ℝ≥0∞} {μ : measure α} (c : 𝕜) (f : Lp E p μ)
  (hf : ∃ f' : α → E, @measurable α _ m _ f' ∧ f =ᵐ[μ] f') :
  ∃ f_add : α → E, @measurable α _ m _ f_add ∧ ⇑(c • f) =ᵐ[μ] f_add :=
begin
  rcases hf with ⟨f', h_f'_meas, hff'⟩,
  refine ⟨c • f', @measurable.const_smul α m _ _ _ _ _ _ _ _ _ _ f' h_f'_meas c, _⟩,
  exact eventually_eq.trans (Lp.coe_fn_smul c f) (eventually_eq.fun_comp hff' (λ x, c • x)),
end

def Lp_sub {α} {m m0 : measurable_space α} (hm : m ≤ m0) (𝕜 E) [is_R_or_C 𝕜]
  [measurable_space 𝕜] [borel_space 𝕜]
  [measurable_space E] [inner_product_space 𝕜 E] [borel_space E] [second_countable_topology E]
  (p : ℝ≥0∞) (μ : measure α) :
  submodule 𝕜 (Lp E p μ) :=
{ carrier := {f : (Lp E p μ) | ∃ g : α → E, @measurable α _ m _ g ∧ f =ᵐ[μ] g} ,
  zero_mem' := ⟨(0 : α → E), @measurable_zero _ α _ m _, Lp.coe_fn_zero _ _ _⟩,
  add_mem' := add_mem' hm,
  smul_mem':= smul_mem' hm, }

lemma mem_Lp_sub_iff_ae_eq_measurable {α} {m m0 : measurable_space α} {hm : m ≤ m0} {𝕜 E}
  [is_R_or_C 𝕜] [measurable_space 𝕜] [borel_space 𝕜]
  [measurable_space E] [inner_product_space 𝕜 E] [borel_space E]
  [second_countable_topology E] {p : ℝ≥0∞} {μ : measure α} {f : Lp E p μ} :
  f ∈ Lp_sub hm 𝕜 E p μ ↔ ∃ g : α → E, @measurable α _ m _ g ∧ f =ᵐ[μ] g :=
by simp_rw [← submodule.mem_coe, ← submodule.mem_carrier, Lp_sub, set.mem_set_of_eq]

lemma Lp_sub.ae_eq_measurable {α} {m m0 : measurable_space α} {hm : m ≤ m0} {𝕜 E}
  [is_R_or_C 𝕜] [measurable_space 𝕜] [borel_space 𝕜]
  [measurable_space E] [inner_product_space 𝕜 E] [borel_space E]
  [second_countable_topology E] {p : ℝ≥0∞} {μ : measure α} (f : Lp_sub hm 𝕜 E p μ) :
  ∃ g : α → E, @measurable α _ m _ g ∧ f =ᵐ[μ] g :=
mem_Lp_sub_iff_ae_eq_measurable.mp f.mem

lemma mem_Lp_sub_self {α} {m0 : measurable_space α} (𝕜 E) [is_R_or_C 𝕜]
  [measurable_space 𝕜] [borel_space 𝕜] [measurable_space E] [inner_product_space 𝕜 E]
  [borel_space E] [second_countable_topology E] (p : ℝ≥0∞) (μ : measure α) (f : Lp E p μ) :
  f ∈ Lp_sub le_rfl 𝕜 E p μ :=
by { rw mem_Lp_sub_iff_ae_eq_measurable, exact (Lp.ae_measurable f), }

lemma Lp_sub_coe {α 𝕜 E} {m m0 : measurable_space α} (hm : m ≤ m0) [is_R_or_C 𝕜]
  [measurable_space 𝕜] [borel_space 𝕜] [measurable_space E] [inner_product_space 𝕜 E]
  [borel_space E] [second_countable_topology E]
  {p : ℝ≥0∞} {μ : measure α} {f : Lp_sub hm 𝕜 E p μ} :
  ⇑f = (f : Lp E p μ) :=
coe_fn_coe_base f

include 𝕜
lemma ae_eq_measurable_of_tendsto {α} {m m0 : measurable_space α} (hm : m ≤ m0) {μ : measure α}
  {ι} [nonempty ι] [linear_order ι] [hp : fact (1 ≤ p)] [complete_space E]
  (f : ι → Lp E p μ) (g : ι → α → E)
  (f_lim : Lp E p μ) (hfg : ∀ n, f n =ᵐ[μ] g n) (hg : ∀ n, @measurable α _ m _ (g n))
  (h_tendsto : filter.at_top.tendsto f (𝓝 f_lim)) :
  ∃ f_lim_m (h_lim_m : @measurable α _ m _ f_lim_m), f_lim =ᵐ[μ] f_lim_m :=
begin
  have hg_m0 : ∀ n, measurable (g n), from λ n, measurable.mono (hg n) hm le_rfl,
  have h_cauchy_seq := h_tendsto.cauchy_seq,
  rw cauchy_seq_iff_tendsto_dist_at_top_0 at h_cauchy_seq,
  simp_rw dist_def at h_cauchy_seq,
  have h_cau_g : tendsto (λ (n : ι × ι), snorm (g n.fst - g n.snd) p μ) at_top (𝓝 0),
  { have h_cauchy_seq' : tendsto (λ (n : ι × ι), snorm (⇑(f n.fst) - ⇑(f n.snd)) p μ) at_top (𝓝 0),
    { have h_real : (λ (n : ι × ι), snorm (⇑(f n.fst) - ⇑(f n.snd)) p μ)
        = λ (n : ι × ι), ennreal.of_real (snorm (⇑(f n.fst) - ⇑(f n.snd)) p μ).to_real,
      { ext1 n,
        rw ennreal.of_real_to_real,
        rw snorm_congr_ae (Lp.coe_fn_sub _ _).symm,
        exact Lp.snorm_ne_top _, },
      rw h_real,
      rw ← ennreal.of_real_to_real ennreal.zero_ne_top,
      refine ennreal.tendsto_of_real _,
      rwa ennreal.zero_to_real, },
    suffices h_snorm_eq : ∀ n : ι × ι, snorm (⇑(f n.fst) - ⇑(f n.snd)) p μ
      = snorm (g n.fst - g n.snd) p μ,
    { simp_rw h_snorm_eq at h_cauchy_seq',
      exact h_cauchy_seq', },
    refine λ n, snorm_congr_ae _,
    exact eventually_eq.comp₂ (hfg n.fst) (λ x y, x - y) (hfg n.snd), },
  have h_cau_g_m' : tendsto
    (λ (n : ι × ι), (@snorm α _ m _ (g n.fst - g n.snd) p (μ.trim hm)).to_real) at_top (𝓝 0),
  { have h_cau_g_m : tendsto (λ (n : ι × ι), @snorm α _ m _ (g n.fst - g n.snd) p (μ.trim hm))
      at_top (𝓝 0),
    { suffices h_snorm_trim : ∀ n : ι × ι, @snorm α _ m _ (g n.fst - g n.snd) p (μ.trim hm)
        = snorm (g n.fst - g n.snd) p μ,
      { simp_rw h_snorm_trim, exact h_cau_g, },
      refine λ n, snorm_trim _ _,
      exact @measurable.sub _ α _ _ _ m _ _ _ (g n.fst) (g n.snd) (hg n.fst) (hg n.snd), },
    rw ← ennreal.zero_to_real,
    exact tendsto.comp (ennreal.tendsto_to_real ennreal.zero_ne_top) h_cau_g_m, },
  have mem_Lp_g : ∀ n, @mem_ℒp α E m _ _ (g n) p (μ.trim hm),
  { refine λ n, ⟨@measurable.ae_measurable α _ m _ _ _ (hg n), _⟩,
    have h_snorm_fg : @snorm α _ m _ (g n) p (μ.trim hm) = snorm (f n) p μ,
    { rw snorm_trim hm (hg n), exact snorm_congr_ae (hfg n).symm, },
    rw h_snorm_fg,
    exact Lp.snorm_lt_top (f n), },
  let g_Lp := λ n, @mem_ℒp.to_Lp α E m p _ _ _ _ _ (g n) (mem_Lp_g n),
  have h_cau_seq_g_Lp : cauchy_seq g_Lp,
  { rw cauchy_seq_iff_tendsto_dist_at_top_0,
    simp_rw dist_def,
    suffices h_eq : ∀ n : ι × ι, @snorm α _ m _ ((g_Lp n.fst) - (g_Lp n.snd)) p (μ.trim hm)
      = @snorm α _ m _ (g n.fst - g n.snd) p (μ.trim hm),
    { simp_rw h_eq,
      exact h_cau_g_m', },
    refine λ n, @snorm_congr_ae α _ m _ _ _ _ _ _,
    exact eventually_eq.comp₂ (@mem_ℒp.coe_fn_to_Lp α E m p _ _ _ _ _ _ (mem_Lp_g n.fst))
      (λ x y, x - y) (@mem_ℒp.coe_fn_to_Lp α E m p _ _ _ _ _ _ (mem_Lp_g n.snd)), },
  obtain ⟨g_Lp_lim, g_tendsto⟩ := cauchy_seq_tendsto_of_complete h_cau_seq_g_Lp,
  refine ⟨g_Lp_lim, @Lp.measurable α E m p (μ.trim hm) _ _ _ _ g_Lp_lim, _⟩,
  have h_g_lim_meas_m : @measurable α _ m _ g_Lp_lim,
    from @Lp.measurable α E m p (μ.trim hm) _ _ _ _ g_Lp_lim,
  have h_g_lim_meas : measurable g_Lp_lim,
    from measurable.mono h_g_lim_meas_m hm le_rfl,
  rw tendsto_Lp_iff_tendsto_ℒp' at g_tendsto h_tendsto,
  suffices h_snorm_zero : snorm (⇑f_lim - ⇑g_Lp_lim) p μ = 0,
  { rw @snorm_eq_zero_iff α E m0 p μ _ _ _ _ _ (ennreal.zero_lt_one.trans_le hp.elim).ne.symm
      at h_snorm_zero,
    { have h_add_sub : ⇑f_lim - ⇑g_Lp_lim + ⇑g_Lp_lim =ᵐ[μ] 0 + ⇑g_Lp_lim,
        from eventually_eq.comp₂ h_snorm_zero (+) eventually_eq.rfl,
      simpa using h_add_sub, },
    { refine ae_measurable.sub (Lp.ae_measurable f_lim) (measurable.ae_measurable _),
      exact h_g_lim_meas, }, },
  have h_tendsto' : tendsto (λ (n : ι), snorm (g n - ⇑f_lim) p μ) at_top (𝓝 0),
  { suffices h_eq : ∀ (n : ι), snorm (g n - ⇑f_lim) p μ = snorm (⇑(f n) - ⇑f_lim) p μ,
    { simp_rw h_eq, exact h_tendsto, },
    refine λ n, snorm_congr_ae _,
    exact eventually_eq.comp₂ (hfg n).symm (λ x y, x - y) (eventually_eq.refl μ.ae (⇑f_lim)), },
  have g_tendsto' : tendsto (λ (n : ι), snorm (g n - ⇑g_Lp_lim) p μ) at_top (𝓝 0),
  { suffices h_eq : ∀ (n : ι), snorm (g n - ⇑g_Lp_lim) p μ
      = @snorm α _ m _ (⇑(g_Lp n) - ⇑g_Lp_lim) p (μ.trim hm),
    { simp_rw h_eq, exact g_tendsto, },
    intro n,
    have h_eq_g : snorm (g n - ⇑g_Lp_lim) p μ = snorm (⇑(g_Lp n) - ⇑g_Lp_lim) p μ,
    { refine snorm_congr_ae _,
      refine eventually_eq.comp₂ _ (λ x y, x - y) (eventually_eq.refl μ.ae (⇑g_Lp_lim)),
      rw eventually_eq, rw ae_iff,
      refine ae_eq_null_of_trim hm _,
      exact (@mem_ℒp.coe_fn_to_Lp α E m p _ _ _ _ _ _ (mem_Lp_g n)).symm, },
    rw h_eq_g,
    refine (snorm_trim hm _).symm,
    refine @measurable.sub _ α _ _ _ m _ _ _ (g_Lp n) g_Lp_lim _ h_g_lim_meas_m,
    exact @Lp.measurable α E m p (μ.trim hm) _ _ _ _ (g_Lp n), },
  have sub_tendsto : tendsto (λ (n : ι), snorm (⇑f_lim - ⇑g_Lp_lim) p μ) at_top (𝓝 0),
  { let snorm_add := λ (n : ι), snorm (g n - ⇑f_lim) p μ + snorm (g n - ⇑g_Lp_lim) p μ,
    have h_add_tendsto : tendsto snorm_add at_top (𝓝 0),
    { rw ← add_zero (0 : ℝ≥0∞),
      refine tendsto.add h_tendsto' g_tendsto', },
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_add_tendsto
      (λ n, zero_le _) _,
      have h_add : (λ n, snorm (⇑f_lim - ⇑g_Lp_lim) p μ)
        = λ n, snorm (⇑f_lim - g n + (g n - ⇑g_Lp_lim)) p μ,
      { ext1 n, congr, abel, },
      simp_rw [h_add, snorm_add],
      intro n,
      dsimp only,
      refine le_trans (snorm_add_le _ _ hp.elim) _,
      { exact ((Lp.measurable f_lim).sub (hg_m0 n)).ae_measurable, },
      { exact ((hg_m0 n).sub h_g_lim_meas).ae_measurable, },
      refine add_le_add_right (le_of_eq _) _,
      rw ← neg_sub,
      rw snorm_neg, },
  have sub_tendsto' : tendsto (λ (n : ι), snorm (⇑f_lim - ⇑g_Lp_lim) p μ) at_top
    (𝓝 (snorm (⇑f_lim - ⇑g_Lp_lim) p μ)),
  { exact tendsto_const_nhds, },
  exact tendsto_nhds_unique sub_tendsto' sub_tendsto,
end

instance {α} {m m0 : measurable_space α} (hm : m ≤ m0) {μ : measure α}
  [complete_space E] [hp : fact(1 ≤ p)] : complete_space (Lp_sub hm 𝕜 E p μ) :=
begin
  refine metric.complete_of_cauchy_seq_tendsto (λ f hf_cau, _),
  let g := λ n, (Lp_sub.ae_eq_measurable (f n)).some,
  have h_g_meas := λ n, (Lp_sub.ae_eq_measurable (f n)).some_spec.1,
  have h_fg : ∀ n, f n =ᵐ[μ] g n := λ n, (Lp_sub.ae_eq_measurable (f n)).some_spec.2,
  let f' := λ n, (f n : Lp E p μ),
  have h_f'g : ∀ n, f' n =ᵐ[μ] g n, by { intro n, simp_rw [f', ← Lp_sub_coe], exact h_fg n, },
  have hf'_cau : cauchy_seq f',
  { rw cauchy_seq_iff_tendsto_dist_at_top_0 at hf_cau ⊢,
    have hff' : ∀ n : ℕ × ℕ, dist (f' n.fst) (f' n.snd) = dist (f n.fst) (f n.snd),
    { rw [prod.forall],
      intros n m,
      simp_rw [dist_eq_norm, f', ← submodule.coe_sub, submodule.norm_coe], },
    simp_rw hff',
    exact hf_cau, },
  obtain ⟨f_lim, h_lim'⟩ := cauchy_seq_tendsto_of_complete hf'_cau,
  suffices h_sub : f_lim ∈ Lp_sub hm 𝕜 E p μ,
  { have h_lim : tendsto f at_top (𝓝 ⟨f_lim, h_sub⟩),
    { rw tendsto_iff_dist_tendsto_zero at h_lim' ⊢,
      have h_lim_coe : ∀ b, dist (f b) ⟨f_lim, h_sub⟩ = dist (f' b) f_lim,
      { intro b,
        have h_dist_coe : dist (f' b) f_lim = dist (f' b) (⟨f_lim, h_sub⟩ : Lp_sub hm 𝕜 E p μ),
          by congr,
        simp_rw [h_dist_coe, dist_eq_norm, f', ← submodule.coe_sub, submodule.norm_coe], },
      simp_rw h_lim_coe,
      exact h_lim', },
    exact ⟨⟨f_lim, h_sub⟩, h_lim⟩, },
  obtain ⟨f_lim_m, h_lim_m, h_ae_eq⟩ := ae_eq_measurable_of_tendsto hm f' g f_lim h_f'g h_g_meas
    h_lim',
  exact ⟨f_lim_m, h_lim_m, h_ae_eq⟩,
end

def is_conditional_expectation (m : measurable_space α) [m0 : measurable_space α] {μ : measure α}
  [normed_group E] [borel_space E] [second_countable_topology E] [complete_space E]
  [normed_space ℝ E]
  (f : α →ₘ[μ] E) (g : α →ₘ[μ] E) (hg : integrable g μ) : Prop :=
integrable f μ ∧ (∃ g : α → E, @measurable α _ m _ g ∧ f =ᵐ[μ] g)
  ∧ ∀ s (hs : @measurable_set α m s), ∫ a in s, f a ∂μ = ∫ a in s, g a ∂μ

/-- Conditional expectation of a function in L2 with respect to a sigma-algebra -/
def condexp_L2 [complete_space E] {m m0 : measurable_space α} (hm : m ≤ m0) {μ : measure α}
  (f : Lp E 2 μ) :
  Lp_sub hm 𝕜 E 2 μ :=
begin
  haveI ips : inner_product_space 𝕜 (Lp E 2 μ) := sorry,
  let proj := @orthogonal_projection 𝕜 (Lp E 2 μ) _ ips (Lp_sub hm 𝕜 E 2 μ) _,
  exact proj f,
end


end measure_theory
