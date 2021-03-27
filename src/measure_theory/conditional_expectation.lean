/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import analysis.normed_space.inner_product
import measure_theory.l2_space

/-! # Conditional expectation

-/

noncomputable theory
open topological_space measure_theory measure_theory.Lp filter
open_locale nnreal ennreal topological_space big_operators

namespace measure_theory

variables {α E F G 𝕜 : Type*} [is_R_or_C 𝕜] {p : ℝ≥0∞}
  [measurable_space E] [inner_product_space 𝕜 E] [borel_space E] [second_countable_topology E]
  [normed_group F] [measurable_space F] [borel_space F] [second_countable_topology F]
  [normed_group G]
  [measurable_space 𝕜] [borel_space 𝕜]

notation α ` →₂[`:25 μ `] ` E := measure_theory.Lp E 2 μ

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
  [measurable_space E] [inner_product_space 𝕜 E] [borel_space E] [second_countable_topology E]
  [measurable_space 𝕜] [borel_space 𝕜]
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

lemma ae_eq_measurable_of_tendsto {α} {m m0 : measurable_space α} (hm : m ≤ m0) {μ : measure α}
  {ι} [nonempty ι] [linear_order ι] [hp : fact (1 ≤ p)] [normed_group E] [borel_space E]
  [second_countable_topology E] [complete_space E]
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
    exact λ n, snorm_congr_ae (eventually_eq.comp₂ (hfg n.fst) (λ x y, x - y) (hfg n.snd)), },
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
  have h_g_ae_m := λ n, @mem_ℒp.coe_fn_to_Lp α E m p _ _ _ _ _ _ (mem_Lp_g n),
  have h_cau_seq_g_Lp : cauchy_seq g_Lp,
  { rw cauchy_seq_iff_tendsto_dist_at_top_0,
    simp_rw dist_def,
    suffices h_eq : ∀ n : ι × ι, @snorm α _ m _ ((g_Lp n.fst) - (g_Lp n.snd)) p (μ.trim hm)
      = @snorm α _ m _ (g n.fst - g n.snd) p (μ.trim hm),
    { simp_rw h_eq,
      exact h_cau_g_m', },
    refine λ n, @snorm_congr_ae α _ m _ _ _ _ _ _,
    exact eventually_eq.comp₂ (h_g_ae_m n.fst) (λ x y, x - y) (h_g_ae_m n.snd), },
  obtain ⟨g_Lp_lim, g_tendsto⟩ := cauchy_seq_tendsto_of_complete h_cau_seq_g_Lp,
  have h_g_lim_meas_m : @measurable α _ m _ g_Lp_lim,
    from @Lp.measurable α E m p (μ.trim hm) _ _ _ _ g_Lp_lim,
  refine ⟨g_Lp_lim, h_g_lim_meas_m, _⟩,
  have h_g_lim_meas : measurable g_Lp_lim, from measurable.mono h_g_lim_meas_m hm le_rfl,
  rw tendsto_Lp_iff_tendsto_ℒp' at g_tendsto h_tendsto,
  suffices h_snorm_zero : snorm (⇑f_lim - ⇑g_Lp_lim) p μ = 0,
  { rw @snorm_eq_zero_iff α E m0 p μ _ _ _ _ _ (ennreal.zero_lt_one.trans_le hp.elim).ne.symm
      at h_snorm_zero,
    { have h_add_sub : ⇑f_lim - ⇑g_Lp_lim + ⇑g_Lp_lim =ᵐ[μ] 0 + ⇑g_Lp_lim,
        from eventually_eq.comp₂ h_snorm_zero (+) eventually_eq.rfl,
      simpa using h_add_sub, },
    { exact (Lp.ae_measurable f_lim).sub h_g_lim_meas.ae_measurable, }, },
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
      exact (h_g_ae_m n).symm, },
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
  exact tendsto_nhds_unique tendsto_const_nhds sub_tendsto,
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

variables [normed_space ℝ E] [is_scalar_tower ℝ 𝕜 E]

def is_condexp_L1_sub {m m0 : measurable_space α} {hm : m ≤ m0} {μ : measure α} [complete_space E]
  (f : Lp_sub hm 𝕜 E 1 μ) (g : α → E) :
  Prop :=
∀ s (hs : @measurable_set α m s), ∫ a in s, f a ∂μ = ∫ a in s, g a ∂μ

def is_condexp (m : measurable_space α) [m0 : measurable_space α]
  [normed_group E] [borel_space E] [second_countable_topology E] [complete_space E]
  [normed_space ℝ E] (f : α → E) (g : α → E) (μ : measure α) :
  Prop :=
integrable f μ ∧ (∃ f' : α → E, @measurable α _ m _ f' ∧ f =ᵐ[μ] f')
  ∧ ∀ s (hs : @measurable_set α m s), ∫ a in s, f a ∂μ = ∫ a in s, g a ∂μ

lemma is_condexp_congr_ae' {m m0 : measurable_space α} (hm : m ≤ m0) {μ : measure α}
  [normed_group E] [borel_space E] [second_countable_topology E] [complete_space E]
  [normed_space ℝ E] {f₁ f₂ g : α → E} (hf12 : f₁ =ᵐ[μ] f₂) (hf₁ : is_condexp m f₁ g μ) :
  is_condexp m f₂ g μ :=
begin
  rcases hf₁ with ⟨h_int, ⟨f, h_meas, h_eq⟩, h_int_eq⟩,
  refine ⟨(integrable_congr hf12).mp h_int, ⟨f, h_meas, hf12.symm.trans h_eq⟩, λ s hs, _⟩,
  have h_to_f1 : ∫ (a : α) in s, f₂ a ∂μ = ∫ (a : α) in s, f₁ a ∂μ,
    from set_integral_congr_ae (hm s hs) (hf12.mono (λ x hx hxs, hx.symm)),
  rw h_to_f1,
  exact h_int_eq s hs,
end

lemma is_condexp_congr_ae {m m0 : measurable_space α} (hm : m ≤ m0) {μ : measure α}
  [normed_group E] [borel_space E] [second_countable_topology E] [complete_space E]
  [normed_space ℝ E] {f₁ f₂ g : α → E} (hf12 : f₁ =ᵐ[μ] f₂) :
  is_condexp m f₁ g μ ↔ is_condexp m f₂ g μ :=
⟨λ h, is_condexp_congr_ae' hm hf12 h, λ h, is_condexp_congr_ae' hm hf12.symm h⟩

lemma is_condexp_congr_ae_right' {m m0 : measurable_space α} (hm : m ≤ m0) {μ : measure α}
  [normed_group E] [borel_space E] [second_countable_topology E] [complete_space E]
  [normed_space ℝ E] {f g₁ g₂ : α → E} (hg12 : g₁ =ᵐ[μ] g₂) (hf₁ : is_condexp m f g₁ μ) :
  is_condexp m f g₂ μ :=
begin
  rcases hf₁ with ⟨h_int, h_meas, h_int_eq⟩,
  refine ⟨h_int, h_meas, λ s hs, _⟩,
  have h_to_g1 : ∫ (a : α) in s, g₂ a ∂μ = ∫ (a : α) in s, g₁ a ∂μ,
    from set_integral_congr_ae (hm s hs) (hg12.mono (λ x hx hxs, hx.symm)),
  rw h_to_g1,
  exact h_int_eq s hs,
end

lemma is_condexp_congr_ae_right {m m0 : measurable_space α} (hm : m ≤ m0) {μ : measure α}
  [normed_group E] [borel_space E] [second_countable_topology E] [complete_space E]
  [normed_space ℝ E] {f g₁ g₂ : α → E} (hg12 : g₁ =ᵐ[μ] g₂) :
  is_condexp m f g₁ μ ↔ is_condexp m f g₂ μ :=
⟨λ h, is_condexp_congr_ae_right' hm hg12 h, λ h, is_condexp_congr_ae_right' hm hg12.symm h⟩

lemma is_condexp_iff_is_condexp_L1_sub {m m0 : measurable_space α} (hm : m ≤ m0) {μ : measure α}
  [complete_space E] (f : Lp_sub hm 𝕜 E 1 μ) (g : α → E) :
  is_condexp m (f : α → E) g μ ↔ is_condexp_L1_sub f g :=
begin
  have h_mem : mem_ℒp f 1 μ, from Lp.mem_ℒp (f : α →₁[μ] E),
  simp_rw [is_condexp, is_condexp_L1_sub, ← mem_ℒp_one_iff_integrable, h_mem,
    Lp_sub.ae_eq_measurable f, true_and],
end

lemma is_condexp_unique {m m0 : measurable_space α} (hm : m ≤ m0) {μ : measure α}
  [normed_group E] [borel_space E] [second_countable_topology E] [complete_space E]
  [normed_space ℝ E] {f₁ f₂ : α → E} (g : α → E) (hf₁ : is_condexp m f₁ g μ)
  (hf₂ : is_condexp m f₂ g μ) :
  f₁ =ᵐ[μ] f₂ :=
begin
  rcases hf₁ with ⟨h_int₁, ⟨f₁', h_meas₁, hff'₁⟩, h_int_eq₁⟩,
  rcases hf₂ with ⟨h_int₂, ⟨f₂', h_meas₂, hff'₂⟩, h_int_eq₂⟩,
  sorry
end

/-- Conditional expectation of a function in L2 with respect to a sigma-algebra -/
variables (𝕜)
def condexp_L2_clm [complete_space E] {m m0 : measurable_space α} (hm : m ≤ m0) {μ : measure α} :
  (α →₂[μ] E) →L[𝕜] (Lp_sub hm 𝕜 E 2 μ) :=
orthogonal_projection (Lp_sub hm 𝕜 E 2 μ)
variables {𝕜}

def indicator_ae (α) {E} [measurable_space α] [measurable_space E] [normed_group E]
  (μ : measure α) {s : set α} (hs : measurable_set s) (c : E) :
  α →ₘ[μ] E :=
ae_eq_fun.mk (s.indicator (λ x, c)) ((ae_measurable_indicator_iff hs).mp ae_measurable_const)

lemma ae_measurable_indicator_ae [measurable_space α] [normed_group E]
  (μ : measure α) {s : set α} (hs : measurable_set s) {c : E} :
  ae_measurable (s.indicator (λ _, c)) μ :=
(ae_measurable_indicator_iff hs).mp ae_measurable_const

lemma indicator_ae_coe [measurable_space α] [normed_group E]
  {μ : measure α} {s : set α} {hs : measurable_set s} {c : E} :
  ⇑(indicator_ae α μ hs c) =ᵐ[μ] s.indicator (λ _, c) :=
ae_eq_fun.coe_fn_mk (s.indicator (λ _, c)) (ae_measurable_indicator_ae μ hs)

lemma snorm_indicator_const [measurable_space α] [normed_group E]
  {μ : measure α} {s : set α} {c : E} (hp : 0 < p) (hp_top : p ≠ ∞) :
  snorm (s.indicator (λ x, c)) p μ = (nnnorm c) * (μ s) ^ (1 / p.to_real) :=
begin
  sorry
  --by_cases hp_top : p = ∞,
  --{ simp [hp], },
end

lemma mem_ℒ0_iff_ae_measurable [measurable_space α] [normed_group E] {μ : measure α} {f : α → E} :
  mem_ℒp f 0 μ ↔ ae_measurable f μ :=
begin
  simp_rw mem_ℒp,
  refine and_iff_left _,
  simp,
end

lemma mem_ℒp_of_norm_le (p : ℝ≥0∞) [measurable_space α] [normed_group E] {μ : measure α}
  {f : α → E} (hf : ae_measurable f μ) (hμf : μ {x | f x ≠ 0} < ∞) (c : ℝ)
  (hf_bounded : ∀ᵐ x ∂μ, ∥f x∥ ≤ c) :
  mem_ℒp f p μ :=
begin
  refine ⟨hf, _⟩,
  have hf_bounded_indicator : ∀ᵐ x ∂μ, ∥f x∥ ≤ ∥{x | f x ≠ 0}.indicator (λ x : α, c) x∥,
  { sorry},
  refine (snorm_mono_ae hf_bounded_indicator).trans_lt _,
  by_cases hp0 : p = 0,
  { simp [hp0], },
  by_cases hp_top : p = ∞,
  { rw hp_top, sorry, },
  rw snorm_eq_snorm' hp0 hp_top,
  simp_rw snorm',
  refine ennreal.rpow_lt_top_of_nonneg sorry _,
  simp_rw nnnorm_indicator_eq_indicator_nnnorm,
  simp_rw ennreal.coe_indicator,
  have h_rpow_indicator : ∀ a, {x : α | f x ≠ 0}.indicator (λ x, (nnnorm c : ℝ≥0∞)) a ^ p.to_real
    = {x : α | f x ≠ 0}.indicator (λ x, (nnnorm c : ℝ≥0∞)^ p.to_real) a,
  { sorry, },
  simp_rw h_rpow_indicator,
  rw lintegral_indicator,
  change ∫⁻ (a : α) in {x : α | f x ≠ 0}, (nnnorm c : ℝ≥0∞) ^ p.to_real ∂μ ≠ ⊤,
  rw lintegral_const,
  sorry,
  sorry,
end

lemma mem_ℒp_indicator_ae {α E} [measurable_space α] [measurable_space E] [normed_group E]
  {μ : measure α} {s : set α} (hs : measurable_set s) (hμs : μ s < ∞) (c : E) :
  mem_ℒp (indicator_ae α μ hs c) p μ :=
begin
  by_cases hp0 : p = 0,
  { rw [hp0, mem_ℒ0_iff_ae_measurable],
    rw ae_measurable_congr indicator_ae_coe,
    exact ae_measurable_indicator_ae μ hs, },
  by_cases hp_top : p = ∞,
  { rw hp_top,
    refine mem_ℒp_of_norm_le ∞ (indicator_ae α μ hs c).ae_measurable _ (∥c∥) _,
    sorry,
    refine (@indicator_ae_coe α E _ _ _ μ s hs c).mono (λ x hx, _),
    rw hx,
    exact norm_indicator_le_norm_self _ x, },
  rw ← ne.def at hp0,
  have hp : 0 < p, from lt_of_le_of_ne (zero_le _) hp0.symm,
  refine ⟨(indicator_ae α μ hs c).ae_measurable, _⟩,
  rw snorm_congr_ae (indicator_ae_coe),
  rw snorm_indicator_const hp hp_top,
  refine ennreal.mul_lt_top ennreal.coe_lt_top _,
  exact ennreal.rpow_lt_top_of_nonneg (by simp) (lt_top_iff_ne_top.mp hμs),
  assumption,
end

local notation `⟪`x`, `y`⟫` := @inner 𝕜 E _ x y

section indicator_Lp
variables [measurable_space α] [normed_group E] [borel_space E] [second_countable_topology E]
  {μ : measure α} {s : set α} {hs : measurable_set s} {hμs : μ s < ∞} {c : E}

def indicator_Lp (p : ℝ≥0∞) (hs : measurable_set s) (hμs : μ s < ∞) (c : E) : Lp E p μ :=
mem_ℒp.to_Lp (indicator_ae α μ hs c) (mem_ℒp_indicator_ae hs hμs c)

lemma indicator_Lp_coe : ⇑(indicator_Lp p hs hμs c) =ᵐ[μ] indicator_ae α μ hs c :=
mem_ℒp.coe_fn_to_Lp (mem_ℒp_indicator_ae hs hμs c)

lemma indicator_Lp_coe_fn (hs : measurable_set s) (hμs : μ s < ∞) (c : E) :
  ⇑(indicator_Lp p hs hμs c) =ᵐ[μ] s.indicator (λ _, c) :=
indicator_Lp_coe.trans indicator_ae_coe

lemma indicator_Lp_coe_fn_mem : ∀ᵐ (x : α) ∂μ, x ∈ s → (indicator_Lp p hs hμs c x) = c :=
(indicator_Lp_coe_fn hs hμs c).mono (λ x hx hxs, hx.trans (set.indicator_of_mem hxs _))

lemma indicator_Lp_coe_fn_nmem : ∀ᵐ (x : α) ∂μ, x ∉ s → (indicator_Lp p hs hμs c x) = 0 :=
(indicator_Lp_coe_fn hs hμs c).mono (λ x hx hxs, hx.trans (set.indicator_of_not_mem hxs _))

lemma norm_indicator_Lp (hp_pos : 0 < p) (hp_ne_top : p ≠ ∞) :
  ∥indicator_Lp p hs hμs c∥ = ∥c∥ * (μ s).to_real ^ (1 / p.to_real) :=
begin
  rw norm_def,
  rw snorm_congr_ae (indicator_Lp_coe_fn hs hμs c),
  rw snorm_indicator_const hp_pos hp_ne_top,
  rw ennreal.to_real_mul,
  rw ennreal.to_real_rpow,
  congr,
  assumption,
end

end indicator_Lp

lemma mem_Lp_sub_indicator_Lp {m m0 : measurable_space α} (hm : m ≤ m0) {μ : measure α} {s : set α}
  (hs : @measurable_set α m s)
  {hμs : μ s < ∞} {c : E} :
  indicator_Lp p (hm s hs) hμs c ∈ Lp_sub hm 𝕜 E p μ :=
begin
  rw mem_Lp_sub_iff_ae_eq_measurable,
  refine ⟨s.indicator (λ x : α, c), _, indicator_Lp_coe_fn (hm s hs) hμs c⟩,
  exact @measurable.indicator α _ m _ _ s (λ x, c) (@measurable_const _ α _ m _) hs,
end

lemma inner_indicator_Lp [measurable_space α] [complete_space E] {μ : measure α} (f : Lp E 2 μ)
  {s : set α} (hs : measurable_set s) (hμs : μ s < ∞) (c : E) :
  inner (indicator_Lp 2 hs hμs c) f = ∫ x in s, ⟪c, f x⟫ ∂μ :=
begin
  simp_rw L2.inner_def,
  rw ← integral_add_compl hs (L2.integrable_inner _ f),
  have h_left : ∫ x in s, ⟪(indicator_Lp 2 hs hμs c) x, f x⟫ ∂μ = ∫ x in s, ⟪c, f x⟫ ∂μ,
  { suffices h_ae_eq : ∀ᵐ x ∂μ, x ∈ s → ⟪indicator_Lp 2 hs hμs c x, f x⟫ = ⟪c, f x⟫,
      from set_integral_congr_ae hs h_ae_eq,
    have h_indicator : ∀ᵐ (x : α) ∂μ, x ∈ s → (indicator_Lp 2 hs hμs c x) = c,
      from indicator_Lp_coe_fn_mem,
    refine h_indicator.mono (λ x hx hxs, _),
    congr,
    exact hx hxs, },
  have h_right : ∫ x in sᶜ, ⟪(indicator_Lp 2 hs hμs c) x, f x⟫ ∂μ = 0,
  { suffices h_ae_eq : ∀ᵐ x ∂μ, x ∉ s → ⟪indicator_Lp 2 hs hμs c x, f x⟫ = 0,
    { simp_rw ← set.mem_compl_iff at h_ae_eq,
      suffices h_int_zero : ∫ x in sᶜ, inner (indicator_Lp 2 hs hμs c x) (f x) ∂μ
        = ∫ x in sᶜ, (0 : 𝕜) ∂μ,
      { rw h_int_zero,
        simp, },
      exact set_integral_congr_ae hs.compl h_ae_eq, },
    have h_indicator : ∀ᵐ (x : α) ∂μ, x ∉ s → (indicator_Lp 2 hs hμs c x) = 0,
      from indicator_Lp_coe_fn_nmem,
    refine h_indicator.mono (λ x hx hxs, _),
    rw hx hxs,
    exact inner_zero_left, },
  rw [h_left, h_right, add_zero],
end

lemma integral_inner [measurable_space α] [complete_space E] {μ : measure α} {f : α → E}
  (hf : integrable f μ) (c : E)  :
  ∫ x, ⟪c, f x⟫ ∂μ = ⟪c, ∫ x, f x ∂μ⟫ :=
continuous_linear_map.integral_comp_comm
  (continuous_linear_map.restrict_scalars ℝ (@inner_right 𝕜 E _ _ c)) hf

lemma integral_zero_of_forall_integral_inner_zero [measurable_space α] [complete_space E]
  {μ : measure α} (f : α → E) (hf : integrable f μ)
  (hf_int : ∀ (c : E), ∫ x, ⟪c, f x⟫ ∂μ = (0 : 𝕜)) :
  ∫ x, f x ∂μ = 0 :=
begin
  specialize hf_int (∫ x, f x ∂μ),
  rwa [integral_inner hf, inner_self_eq_zero] at hf_int,
end

lemma Lp.integrable [measurable_space α] {μ : measure α} [finite_measure μ] [normed_group E]
  [borel_space E] [second_countable_topology E] (f : Lp E p μ) (hp : 1 ≤ p) :
  integrable f μ :=
mem_ℒp_one_iff_integrable.mp (mem_ℒp.mem_ℒp_of_exponent_le (Lp.mem_ℒp f) hp)

lemma integrable.restrict [measurable_space α] [normed_group E] {μ : measure α} {f : α → E}
  (hf : integrable f μ) (s : set α) :
  integrable f (μ.restrict s) :=
integrable_on.integrable (integrable.integrable_on hf)

include 𝕜
lemma is_condexp_condexp_L2 [complete_space E] {m m0 : measurable_space α} (hm : m ≤ m0)
  {μ : measure α} [finite_measure μ] (f : Lp E 2 μ) :
  is_condexp m ((condexp_L2_clm 𝕜 hm f) : α → E) f μ :=
begin
  have h_one_le_two : (1 : ℝ≥0∞) ≤ 2,
    from ennreal.coe_le_coe.2 (show (1 : ℝ≥0) ≤ 2, by norm_num),
  refine ⟨_, Lp_sub.ae_eq_measurable (condexp_L2_clm 𝕜 hm f), _⟩,
  { exact Lp.integrable (condexp_L2_clm 𝕜 hm f) h_one_le_two, },
  intros s hs,
  have h_inner_zero : ∀ (g : Lp E 2 μ) (hg : g ∈ Lp_sub hm 𝕜 E 2 μ),
      inner (f - (condexp_L2_clm 𝕜 hm f)) g = (0 : 𝕜),
    from λ g hg, orthogonal_projection_inner_eq_zero f g hg,
  suffices h_sub : ∫ a in s, (f a - condexp_L2_clm 𝕜 hm f a) ∂μ = 0,
  { rw integral_sub at h_sub,
    { rw sub_eq_zero at h_sub,
      exact h_sub.symm, },
    { exact integrable.restrict (Lp.integrable f h_one_le_two) s, },
    { exact integrable.restrict (Lp.integrable (condexp_L2_clm 𝕜 hm f) h_one_le_two) s,}, },
  refine integral_zero_of_forall_integral_inner_zero _ _ _,
  { refine integrable.restrict _ s,
    refine integrable.sub _ _,
    { exact Lp.integrable f h_one_le_two, },
    { exact Lp.integrable (condexp_L2_clm 𝕜 hm f) h_one_le_two, }, },
  { intro c,
    specialize h_inner_zero (indicator_Lp 2 (hm s hs) (measure_lt_top μ s) c)
      (mem_Lp_sub_indicator_Lp hm hs),
    rw [inner_eq_zero_sym, inner_indicator_Lp] at h_inner_zero,
    rw ← h_inner_zero,
    refine set_integral_congr_ae (hm s hs) _,
    refine (Lp.coe_fn_sub f (condexp_L2_clm 𝕜 hm f)).mono (λ x hx hxs, _),
    congr,
    rw [hx, pi.sub_apply, Lp_sub_coe], },
end
omit 𝕜

lemma ennreal.one_le_two : (1 : ℝ≥0∞) ≤ 2 := ennreal.coe_le_coe.2 (show (1 : ℝ≥0) ≤ 2, by norm_num)

lemma mem_ℒ2_simple_func [measurable_space α] [normed_group E] {μ : measure α} [finite_measure μ]
  (f : simple_func α E) :
  mem_ℒp f 2 μ :=
begin
  refine mem_ℒp_of_norm_le 2 f.ae_measurable (measure_lt_top μ _) _ _,
  sorry,
  sorry,
end

lemma mem_ℒ2_simple_func_L1 [measurable_space α] [normed_group E] [borel_space E]
  [second_countable_topology E] {μ : measure α} [finite_measure μ] (f : α →₁ₛ[μ] E) :
  mem_ℒp f 2 μ :=
(mem_ℒp_congr_ae (L1.simple_func.to_simple_func_eq_to_fun f).symm).mpr (mem_ℒ2_simple_func _)

lemma L1s_to_L2_add [measurable_space α] [normed_group E] [borel_space E]
  [second_countable_topology E] {μ : measure α} [finite_measure μ] (f g : α →₁ₛ[μ] E) :
  mem_ℒp.to_Lp ⇑(f+g) (mem_ℒ2_simple_func_L1 (f+g))
    = mem_ℒp.to_Lp f (mem_ℒ2_simple_func_L1 f) + mem_ℒp.to_Lp g (mem_ℒ2_simple_func_L1 g) :=
begin
  ext1,
  refine (mem_ℒp.coe_fn_to_Lp _).trans (eventually_eq.trans _ (Lp.coe_fn_add _ _).symm),
  refine (Lp.coe_fn_add _ _).trans _,
  have hf : f.val =ᵐ[μ] mem_ℒp.to_Lp f (mem_ℒ2_simple_func_L1 f),
  { refine eventually_eq.trans _ (mem_ℒp.coe_fn_to_Lp _).symm,
    simp only [L1.simple_func.coe_coe, subtype.val_eq_coe], },
  have hg : g.val =ᵐ[μ] mem_ℒp.to_Lp g (mem_ℒ2_simple_func_L1 g),
  { refine eventually_eq.trans _ (mem_ℒp.coe_fn_to_Lp _).symm,
    simp only [L1.simple_func.coe_coe, subtype.val_eq_coe], },
  exact eventually_eq.comp₂ hf (+) hg,
end

lemma L1s_to_L2_smul [measurable_space α] {μ : measure α} [finite_measure μ] (c : 𝕜)
  (f : α →₁ₛ[μ] E) :
  mem_ℒp.to_Lp ⇑(@has_scalar.smul _ _ L1.simple_func.has_scalar c f)
      (mem_ℒ2_simple_func_L1 (@has_scalar.smul _ _ L1.simple_func.has_scalar c f))
    = c • (mem_ℒp.to_Lp f (mem_ℒ2_simple_func_L1 f)) :=
begin
  ext1,
  refine (mem_ℒp.coe_fn_to_Lp _).trans (eventually_eq.trans _ (Lp.coe_fn_smul _ _).symm),
  refine (Lp.coe_fn_smul _ _).trans _,
  suffices h : ⇑(f : Lp E 1 μ) =ᵐ[μ] (mem_ℒp.to_Lp ⇑f _),
    from eventually_eq.fun_comp h (λ x : E, c • x),
  refine eventually_eq.trans _ (mem_ℒp.coe_fn_to_Lp _).symm,
  simp,
end

def L1s_to_L2_lm [measurable_space α] {μ : measure α} [finite_measure μ] :
  (α →₁ₛ[μ] E) →ₗ[𝕜] (α →₂[μ] E) :=
{ to_fun := λ f, mem_ℒp.to_Lp f (mem_ℒ2_simple_func_L1 f),
  map_add' := L1s_to_L2_add,
  map_smul' := L1s_to_L2_smul, }

include 𝕜
lemma L1s_to_L2_coe_fn [measurable_space α] {μ : measure α} [finite_measure μ] (f : α →₁ₛ[μ] E) :
  L1s_to_L2_lm f =ᵐ[μ] f :=
mem_ℒp.coe_fn_to_Lp _
omit 𝕜

lemma L2_to_L1_add [measurable_space α] [normed_group E] [borel_space E]
  [second_countable_topology E] {μ : measure α} [finite_measure μ] (f g : α →₂[μ] E) :
  (mem_ℒp.mem_ℒp_of_exponent_le (Lp.mem_ℒp (f+g)) ennreal.one_le_two).to_Lp ⇑(f+g)
    = (mem_ℒp.mem_ℒp_of_exponent_le (Lp.mem_ℒp f) ennreal.one_le_two).to_Lp f
      + (mem_ℒp.mem_ℒp_of_exponent_le (Lp.mem_ℒp g) ennreal.one_le_two).to_Lp g :=
begin
  ext1,
  refine (mem_ℒp.coe_fn_to_Lp _).trans (eventually_eq.trans _ (Lp.coe_fn_add _ _).symm),
  refine (Lp.coe_fn_add _ _).trans _,
  have hf : ⇑f =ᵐ[μ] mem_ℒp.to_Lp f
    (mem_ℒp.mem_ℒp_of_exponent_le (Lp.mem_ℒp f) ennreal.one_le_two),
  { exact (mem_ℒp.coe_fn_to_Lp _).symm, },
  have hg : g.val =ᵐ[μ] mem_ℒp.to_Lp g
    (mem_ℒp.mem_ℒp_of_exponent_le (Lp.mem_ℒp g) ennreal.one_le_two),
  { exact (mem_ℒp.coe_fn_to_Lp _).symm, },
  exact eventually_eq.comp₂ hf (+) hg,
end

lemma L2_to_L1_smul [measurable_space α] {μ : measure α} [finite_measure μ] (c : 𝕜)
  (f : α →₂[μ] E) :
  (mem_ℒp.mem_ℒp_of_exponent_le (Lp.mem_ℒp (c • f)) ennreal.one_le_two).to_Lp ⇑(c • f)
    = c • ((mem_ℒp.mem_ℒp_of_exponent_le (Lp.mem_ℒp f) ennreal.one_le_two).to_Lp f) :=
begin
  ext1,
  refine (mem_ℒp.coe_fn_to_Lp _).trans (eventually_eq.trans _ (Lp.coe_fn_smul _ _).symm),
  refine (Lp.coe_fn_smul _ _).trans _,
  suffices h : ⇑f =ᵐ[μ] (mem_ℒp.to_Lp ⇑f _),
    from eventually_eq.fun_comp h (λ x : E, c • x),
  exact (mem_ℒp.coe_fn_to_Lp _).symm,
end

lemma continuous_L2_to_L1 [measurable_space α] [normed_group E] [borel_space E]
  [second_countable_topology E] {μ : measure α} [probability_measure μ] :
  continuous (λ (f : α →₂[μ] E),
    (mem_ℒp.mem_ℒp_of_exponent_le (Lp.mem_ℒp f) ennreal.one_le_two).to_Lp f) :=
begin
  rw metric.continuous_iff,
  intros f ε hε_pos,
  simp_rw dist_def,
  refine ⟨ε, hε_pos, λ g hfg, _⟩,
  refine lt_of_le_of_lt _ hfg,
  rw ennreal.to_real_le_to_real _ _,
  swap, { rw snorm_congr_ae (Lp.coe_fn_sub _ _).symm, exact Lp.snorm_ne_top _, },
  swap, { rw snorm_congr_ae (Lp.coe_fn_sub _ _).symm, exact Lp.snorm_ne_top _, },
  refine (le_of_eq _).trans (snorm_le_snorm_of_exponent_le (ennreal.one_le_two)
    ((Lp.ae_measurable g).sub (Lp.ae_measurable f))),
  refine snorm_congr_ae _,
  exact eventually_eq.comp₂
    (mem_ℒp.coe_fn_to_Lp (mem_ℒp.mem_ℒp_of_exponent_le (Lp.mem_ℒp g) ennreal.one_le_two))
    (λ x y, x - y)
    (mem_ℒp.coe_fn_to_Lp (mem_ℒp.mem_ℒp_of_exponent_le (Lp.mem_ℒp f) ennreal.one_le_two)),
end

def L2_to_L1_clm [measurable_space α] {μ : measure α} [probability_measure μ] :
  (α →₂[μ] E) →L[𝕜] (α →₁[μ] E) :=
{ to_fun := λ f, (mem_ℒp.mem_ℒp_of_exponent_le (Lp.mem_ℒp f) ennreal.one_le_two).to_Lp f,
  map_add' := L2_to_L1_add,
  map_smul' := L2_to_L1_smul,
  cont := continuous_L2_to_L1, }

include 𝕜
lemma L2_to_L1_coe_fn [measurable_space α] {μ : measure α} [probability_measure μ] (f : α →₂[μ] E) :
  L2_to_L1_clm f =ᵐ[μ] f :=
mem_ℒp.coe_fn_to_Lp _
omit 𝕜

def indicator_simple_func [measurable_space α] [has_zero E] (s : set α) (hs : measurable_set s)
  (c : E) :
  simple_func α E :=
simple_func.piecewise s hs (simple_func.const α c) (simple_func.const α 0)

lemma indicator_simple_func_coe [measurable_space α] [has_zero E] {μ : measure α} {s : set α}
  {hs : measurable_set s} {c : E} :
  (indicator_simple_func s hs c) =ᵐ[μ] s.indicator (λ (_x : α), c) :=
by simp only [indicator_simple_func, simple_func.coe_const, simple_func.const_zero,
  simple_func.coe_zero, set.piecewise_eq_indicator, simple_func.coe_piecewise]

lemma simple_func.coe_finset_sum {ι} [measurable_space α] [normed_group E]
  (f : ι → simple_func α E) (s : finset ι) (x : α) :
  (∑ i in s, f i) x = ∑ i in s, f i x :=
sorry

lemma simple_func_eq_sum_indicator [measurable_space α] [normed_group E] {μ : measure α}
  (f : simple_func α E) :
  f = ∑ y in f.range,
    indicator_simple_func (f ⁻¹' ({y} : set E)) (simple_func.measurable_set_fiber f y) y :=
begin
  ext,
  simp [indicator_simple_func],
  rw simple_func.coe_finset_sum,
  simp_rw simple_func.piecewise_apply,
  simp only [simple_func.coe_const, function.const_apply, set.mem_preimage, set.mem_singleton_iff,
    pi.zero_apply, simple_func.coe_zero],
  haveI : decidable_eq E := classical.dec_eq E,
  have hfa : f a = ite (f a ∈ f.range) (f a) (0 : E), by simp [simple_func.mem_range_self],
  have h := (finset.sum_ite_eq f.range (f a) (λ i, i)).symm,
  dsimp only at h,
  rw ← hfa at h,
  convert h,
  ext1,
  congr,
end

section indicator_L1s
variables [measurable_space α] [normed_group E] [borel_space E] [second_countable_topology E]
  [complete_space E] {μ : measure α} [probability_measure μ] {s : set α} {hs : measurable_set s}

lemma is_simple_func_indicator_ae (hs : measurable_set s) (hμs : μ s < ∞) (c : E) :
  ∃ (s : simple_func α E), (ae_eq_fun.mk s s.ae_measurable : α →ₘ[μ] E) = indicator_Lp 1 hs hμs c :=
⟨indicator_simple_func s hs c, ae_eq_fun.ext ((ae_eq_fun.coe_fn_mk _ _).trans
    ((indicator_simple_func_coe).trans (indicator_Lp_coe_fn _ _ _).symm))⟩

def indicator_L1s (hs : measurable_set s) (hμs : μ s < ∞) (c : E) : α →₁ₛ[μ] E :=
⟨indicator_Lp 1 hs hμs c, is_simple_func_indicator_ae hs hμs c⟩

lemma indicator_L1s_coe {hμs : μ s < ∞} {c : E} :
  (indicator_L1s hs hμs c : α →₁[μ] E) = indicator_Lp 1 hs hμs c :=
rfl

lemma indicator_L1s_coe_fn {hμs : μ s < ∞} {c : E} :
  ⇑(indicator_L1s hs hμs c) =ᵐ[μ] s.indicator (λ _, c) :=
by { rw [(L1.simple_func.coe_coe _).symm, indicator_L1s_coe], exact indicator_Lp_coe_fn hs hμs c, }

lemma to_simple_func_indicator_L1s {hμs : μ s < ∞} {c : E} :
  L1.simple_func.to_simple_func (indicator_L1s hs hμs c) =ᵐ[μ] indicator_simple_func s hs c :=
(L1.simple_func.to_simple_func_eq_to_fun _).trans
  (indicator_L1s_coe_fn.trans indicator_simple_func_coe.symm)

end indicator_L1s

lemma L1.simple_func.sum_to_simple_func {ι} [measurable_space α] [normed_group E] [borel_space E]
  [second_countable_topology E] {μ : measure α} (f : ι → α →₁ₛ[μ] E) (s : finset ι) :
  L1.simple_func.to_simple_func (∑ i in s, f i)
    =ᵐ[μ] ∑ i in s, L1.simple_func.to_simple_func (f i) :=
begin
  sorry,
end

lemma L1.simple_func_eq_sum_indicator_L1s [measurable_space α] [normed_group E] [borel_space E]
  [second_countable_topology E] [complete_space E] {μ : measure α} [probability_measure μ]
  (f : α →₁ₛ[μ] E) :
  f = ∑ y in (L1.simple_func.to_simple_func f).range,
    indicator_L1s (L1.simple_func.measurable f (measurable_set_singleton y))
    (measure_lt_top μ _) y :=
begin
  rw ← L1.simple_func.to_L1_to_simple_func (∑ y in (L1.simple_func.to_simple_func f).range,
    indicator_L1s (L1.simple_func.measurable f (measurable_set_singleton y))
    (measure_lt_top μ _) y),
  ext1,
  ext1,
  simp only [L1.simple_func.coe_coe, subtype.coe_mk],
  refine eventually_eq.trans _ (integrable.coe_fn_to_L1 _).symm,
  refine eventually_eq.trans _ (L1.simple_func.sum_to_simple_func _ _).symm,
  have h_sum_eq : ∑ y in (L1.simple_func.to_simple_func f).range, (L1.simple_func.to_simple_func
    (indicator_L1s (L1.simple_func.measurable f (measurable_set_singleton y))
    (measure_lt_top μ _) y))
    =ᵐ[μ] ∑ y in (L1.simple_func.to_simple_func f).range, indicator_simple_func _
      (L1.simple_func.measurable f (measurable_set_singleton y)) y,
  { sorry},
  refine eventually_eq.trans _ h_sum_eq.symm,
  nth_rewrite 0 ← L1.simple_func.to_L1_to_simple_func f,
  sorry
end

lemma simple_func.integrable [measurable_space α] [normed_group E] [borel_space E]
  [second_countable_topology E]
  {μ : measure α} [finite_measure μ] (f : simple_func α E) :
  integrable f μ :=
begin
  sorry,
end

def L1.simple_func.map [measurable_space α] [normed_group E] [borel_space E]
  [second_countable_topology E]
  {μ : measure α} [finite_measure μ] (g : E → F) (f : α →₁ₛ[μ] E) :
  (α →₁ₛ[μ] F) :=
L1.simple_func.to_L1 ((L1.simple_func.to_simple_func f).map g) (simple_func.integrable _)

lemma L1.simple_func.map_coe [measurable_space α] [normed_group E] [borel_space E]
  [second_countable_topology E]
  {μ : measure α} [finite_measure μ] (g : E → F) (f : α →₁ₛ[μ] E) :
  ⇑(L1.simple_func.map g f) =ᵐ[μ] g ∘ f :=
begin
  sorry,
end

variables (𝕜)
def condexp_L1s_lm {m m0 : measurable_space α} (hm : m ≤ m0) [complete_space E]
  {μ : measure α} [probability_measure μ] :
  (α →₁ₛ[μ] E) →ₗ[𝕜] (α →₁[μ] E) :=
L2_to_L1_clm.to_linear_map.comp ((Lp_sub hm 𝕜 E 2 μ).subtype.comp
  ((condexp_L2_clm 𝕜 hm).to_linear_map.comp L1s_to_L2_lm))
variables {𝕜}

lemma continuous_linear_map.to_linear_map_apply {R : Type*} [semiring R] {M₁ M₂ : Type*}
  [topological_space M₁] [add_comm_monoid M₁] [topological_space M₂] [add_comm_monoid M₂]
  [semimodule R M₁] [semimodule R M₂] (f : M₁ →L[R] M₂) (x : M₁) :
  f.to_linear_map x = f x :=
rfl

lemma condexp_L1s_ae_eq_condexp_L2 {m m0 : measurable_space α} (hm : m ≤ m0) [complete_space E]
  {μ : measure α} [probability_measure μ] (f : α →₁ₛ[μ] E) :
  condexp_L1s_lm 𝕜 hm f =ᵐ[μ] condexp_L2_clm 𝕜 hm (L1s_to_L2_lm f) :=
(L2_to_L1_coe_fn _).trans (by refl)

lemma is_condexp_condexp_L2_L1s_to_L2 [complete_space E] {m m0 : measurable_space α} (hm : m ≤ m0)
  {μ : measure α} [probability_measure μ] (f : α →₁ₛ[μ] E) :
  is_condexp m (condexp_L2_clm 𝕜 hm (L1s_to_L2_lm f) : α → E) f μ :=
is_condexp_congr_ae_right' hm (L1s_to_L2_coe_fn f) (is_condexp_condexp_L2 hm _)

variables (𝕜)
lemma is_condexp_condexp_L1s [complete_space E] {m m0 : measurable_space α} (hm : m ≤ m0)
  {μ : measure α} [probability_measure μ] (f : α →₁ₛ[μ] E) :
  is_condexp m ((condexp_L1s_lm 𝕜 hm f) : α → E) f μ :=
is_condexp_congr_ae' hm (condexp_L1s_ae_eq_condexp_L2 hm _).symm
  (is_condexp_condexp_L2_L1s_to_L2 hm f)
variables {𝕜}

variables (𝕜)
lemma integral_condexp_L1s [complete_space E] {m m0 : measurable_space α} (hm : m ≤ m0)
  {μ : measure α} [probability_measure μ] (f : α →₁ₛ[μ] E) {s : set α} (hs : @measurable_set α m s) :
  ∫ a in s, (condexp_L1s_lm 𝕜 hm f) a ∂μ = ∫ a in s, f a ∂μ :=
(is_condexp_condexp_L1s 𝕜 hm f).2.2 s hs
variables {𝕜}

lemma ae_le_iff_forall_lt_measure_zero [measurable_space α] {μ : measure α} (f : α → ℝ) (c : ℝ) :
  (∀ᵐ x ∂μ, c ≤ f x) ↔ ∀ b < c, μ {x | f x ≤ b} = 0 :=
begin
  rw ae_iff,
  push_neg,
  have h_le : {x | f x < c} = ⋃ (r : ℚ) (hr : ↑r < c), {x | f x ≤ r},
  { sorry, },
  rw h_le,
  rw measure_Union_null_iff,
  split; intros h b,
  { intro hbc,
    obtain ⟨r, hr⟩ := exists_rat_btwn hbc,
    specialize h r,
    simp only [hr.right, set.Union_pos] at h,
    refine measure_mono_null (λ x hx, _) h,
    rw set.mem_set_of_eq at hx ⊢,
    exact hx.trans hr.1.le, },
  { by_cases hbc : ↑b < c,
    { simp only [hbc, set.Union_pos],
      exact h _ hbc, },
    { simp [hbc], }, },
end

lemma condexp_L1s_const_le {m m0 : measurable_space α} (hm : m ≤ m0)
  {μ : measure α} [probability_measure μ] (f : α →₁ₛ[μ] ℝ) (c : ℝ) (hf : ∀ᵐ x ∂μ, c ≤ f x) :
  ∀ᵐ x ∂μ, c ≤ condexp_L1s_lm ℝ hm f x :=
begin
  refine (ae_le_iff_forall_lt_measure_zero _ c).mpr (λ b hb, _),
  obtain ⟨h_int, ⟨f', h_meas, hff'⟩, h_int_eq⟩ := is_condexp_condexp_L1s ℝ hm f,
  have h_int' : integrable f' μ := (integrable_congr hff').mp h_int,
  let s := {x | f' x ≤ b},
  have hsm : @measurable_set _ m s,
    from @measurable_set_le _ _ _ _ _ m _ _ _ _ _ h_meas (@measurable_const _ _ _ m _),
  have hs : measurable_set s, from hm s hsm,
  have hf's : ∀ x ∈ s, f' x ≤ b, from λ x hx, hx,
  specialize h_int_eq s hsm,
  rw set_integral_congr_ae hs (hff'.mono (λ x hx hxs, hx)) at h_int_eq,
  have h_int_le : c * (μ s).to_real ≤ ∫ x in s, f' x ∂μ,
  { rw h_int_eq,
    have h_const_le : ∫ x in s, c ∂μ ≤ ∫ x in s, f x ∂μ,
      from set_integral_mono_ae_restrict (integrable_on_const.mpr (or.inr (measure_lt_top _ _)))
        (Lp.integrable _ le_rfl).integrable_on (ae_restrict_of_ae hf),
    refine le_trans _ h_const_le,
    rw [set_integral_const, smul_eq_mul, mul_comm], },
  have h_int_lt : (μ s).to_real ≠ 0 → ∫ x in s, f' x ∂μ < c * (μ s).to_real,
  { intro h_ne_zero,
    suffices h_le_b : ∫ (x : α) in s, f' x ∂μ ≤ b * (μ s).to_real,
    { refine h_le_b.trans_lt _,
      sorry, },
    have h_const_le : ∫ x in s, f' x ∂μ ≤ ∫ x in s, b ∂μ,
    { refine set_integral_mono_ae_restrict h_int'.integrable_on
        (integrable_on_const.mpr (or.inr (measure_lt_top _ _))) _,
      sorry, },
    refine h_const_le.trans _,
    rw [set_integral_const, smul_eq_mul, mul_comm], },
  have hμs_eq_zero : μ s = 0,
  { suffices hμs0 : (μ s).to_real = 0,
    { cases (ennreal.to_real_eq_zero_iff _).mp hμs0,
      { exact h, },
      { exact absurd h (measure_ne_top _ _), }, },
    by_contra,
    exact (lt_self_iff_false (c * (μ s).to_real)).mp (h_int_le.trans_lt (h_int_lt h)), },
  rw ← hμs_eq_zero,
  refine measure_congr _,
  sorry,
end

lemma condexp_L1s_le_const {m m0 : measurable_space α} (hm : m ≤ m0)
  {μ : measure α} [probability_measure μ] (f : α →₁ₛ[μ] ℝ) (c : ℝ) (hf : ∀ᵐ x ∂μ, f x ≤ c) :
  ∀ᵐ x ∂μ, condexp_L1s_lm ℝ hm f x ≤ c :=
begin
  have h_neg := condexp_L1s_const_le hm (-f) (-c) _,
  swap, { sorry, },
  rw linear_map.map_neg at h_neg,
  refine (Lp.coe_fn_neg ((condexp_L1s_lm ℝ hm) f)).mp (h_neg.mono (λ x hx hx_neg, _)),
  rw [hx_neg, pi.neg_apply] at hx,
  exact le_of_neg_le_neg hx,
end

lemma condexp_L1s_nonneg {m m0 : measurable_space α} (hm : m ≤ m0)
  {μ : measure α} [probability_measure μ] (f : α →₁ₛ[μ] ℝ) (hf : 0 ≤ᵐ[μ] f) :
  0 ≤ᵐ[μ] condexp_L1s_lm ℝ hm f :=
sorry

lemma condexp_L1s_R_jensen {m m0 : measurable_space α} (hm : m ≤ m0) {μ : measure α}
  [probability_measure μ] (f : α →₁ₛ[μ] ℝ) (F : ℝ → ℝ) (hF : convex_on (set.univ : set ℝ) F) :
  ∀ᵐ x ∂μ, F (condexp_L1s_lm ℝ hm f x) ≤ condexp_L1s_lm ℝ hm (L1.simple_func.map F f) x :=
begin
  sorry
end

lemma norm_condexp_L1s_le_R {m m0 : measurable_space α} (hm : m ≤ m0)
  {μ : measure α} [probability_measure μ] (f : α →₁ₛ[μ] ℝ) :
  ∥condexp_L1s_lm ℝ hm f∥ ≤ ∥f∥ :=
begin
  simp_rw [L1.simple_func.norm_eq, norm_def],
  rw ennreal.to_real_le_to_real (Lp.snorm_ne_top _) (Lp.snorm_ne_top _),
  simp_rw [snorm_eq_snorm' ennreal.zero_lt_one.ne.symm ennreal.coe_ne_top, ennreal.one_to_real,
    snorm', div_one, ennreal.rpow_one],
  let F := λ x : ℝ, ∥x∥,
  have hF : convex_on (set.univ : set ℝ) F,
  { sorry},
  have h_left : ∫⁻ a, (nnnorm (((condexp_L1s_lm ℝ hm) f) a) : ℝ≥0∞) ∂μ
      = ∫⁻ a, ennreal.of_real (∥((condexp_L1s_lm ℝ hm) f) a∥) ∂μ,
    by { congr, ext1 x, rw ← of_real_norm_eq_coe_nnnorm, },
  have h_right : ∫⁻ a, (nnnorm ((f : Lp ℝ 1 μ) a) : ℝ≥0∞) ∂μ
      = ∫⁻ a, ennreal.of_real (∥(f : Lp ℝ 1 μ) a∥) ∂μ,
    by { congr, ext1 x, rw ← of_real_norm_eq_coe_nnnorm, },
  rw [h_left, h_right],
  refine le_trans _ _,
  exact (∫⁻ a, ennreal.of_real (condexp_L1s_lm ℝ hm (L1.simple_func.map F f) a) ∂μ),
  { refine lintegral_mono_ae ((condexp_L1s_R_jensen hm f F hF).mono (λ x hx, _)),
    rwa ennreal.of_real_le_of_real_iff ((norm_nonneg _).trans hx), },
  { have h_integral_eq := integral_condexp_L1s ℝ hm (L1.simple_func.map F f)
      (@measurable_set.univ α m),
    rw [integral_univ, integral_univ] at h_integral_eq,
    rw [← (ennreal.to_real_le_to_real _ _), ← integral_eq_lintegral_of_nonneg_ae,
      ← integral_eq_lintegral_of_nonneg_ae, h_integral_eq,
      integral_congr_ae (L1.simple_func.map_coe F f)],
    simp,
    { exact eventually_of_forall (by simp [norm_nonneg]), },
    { exact measurable.comp_ae_measurable measurable_norm (Lp.ae_measurable _), },
    { refine condexp_L1s_nonneg hm (L1.simple_func.map F f) _,
      refine (L1.simple_func.map_coe F f).mono (λ x hx, _),
      rw [hx, pi.zero_apply],
      simp [F, norm_nonneg], },
    { exact Lp.ae_measurable _, },
    { sorry, },
    { sorry, }, },
end

lemma norm_indicator_L1s [normed_group E] [borel_space E] [second_countable_topology E]
  [complete_space E] {m m0 : measurable_space α} (hm : m ≤ m0) {μ : measure α}
  [probability_measure μ] {s : set α} {hs : measurable_set s} {hμs : μ s < ∞} {c : E} :
  ∥indicator_L1s hs hμs c∥ = ∥c∥ * (μ s).to_real :=
by rw [L1.simple_func.norm_eq, indicator_L1s_coe,
  norm_indicator_Lp ennreal.zero_lt_one ennreal.coe_ne_top, ennreal.one_to_real, div_one,
  real.rpow_one]

lemma norm_condexp_L1s_indicator_L1s_R_le {m m0 : measurable_space α} (hm : m ≤ m0) {μ : measure α}
  [probability_measure μ] {s : set α} (hs : measurable_set s) (hμs : μ s < ∞) (c : ℝ) :
  ∥condexp_L1s_lm ℝ hm (indicator_L1s hs hμs c)∥ ≤ ∥c∥ * (μ s).to_real :=
(norm_condexp_L1s_le_R hm _).trans (norm_indicator_L1s hm).le

variables (𝕜)
include 𝕜
lemma indicator_L1s_eq_smul [measurable_space α] {μ : measure α} [probability_measure μ]
  [complete_space E] {s : set α} (hs : measurable_set s) (hμs : μ s < ∞) (c : E) :
  indicator_L1s hs hμs c =ᵐ[μ] λ x, ((@indicator_L1s α ℝ _ _ _ _ _ _ μ _ s hs hμs 1) x) • c :=
begin
  have h : (λ (x : α), (indicator_L1s hs hμs (1:ℝ)) x • c) =ᵐ[μ] λ x,
    (s.indicator (λ _, (1:ℝ)) x) • c,
  { change (λ x, x • c) ∘ (indicator_L1s hs hμs (1:ℝ))
      =ᵐ[μ] λ (x : α), s.indicator (λ x, (1:ℝ)) x • c,
    exact eventually_eq.fun_comp indicator_L1s_coe_fn (λ x, x • c), },
  refine (indicator_L1s_coe_fn).trans (eventually_eq.trans _ h.symm),
  refine eventually_of_forall (λ x, _),
  by_cases h_mem : x ∈ s; simp [h_mem],
end
omit 𝕜
variables {𝕜}

--lemma condexp_L1s_smul_const {m m0 : measurable_space α} (hm : m ≤ m0) [complete_space E]
--  {μ : measure α} [probability_measure μ] (f : α →₁ₛ[μ] ℝ)
--  (c : E) :
--  condexp_L1s_lm 𝕜 hm (λ x, (f x) • c) =ᵐ[μ] λ x, (condexp_L1s_lm ℝ hm f x) • c :=

lemma indicator_L1s_coe_ae_le [measurable_space α] {μ : measure α} [probability_measure μ]
  {s : set α} (hs : measurable_set s) (hμs : μ s < ∞) (c : ℝ) :
  ∀ᵐ x ∂μ, abs (indicator_L1s hs hμs c x) ≤ abs c :=
begin
  refine (@indicator_L1s_coe_fn α ℝ _ _ _ _ _ _ μ _ s hs hμs c).mono (λ x hx, _),
  rw hx,
  by_cases hx_mem : x ∈ s; simp [hx_mem, abs_nonneg c],
end

lemma condexp_L1s_indicator_L1s_eq {m m0 : measurable_space α} (hm : m ≤ m0) [complete_space E]
  {μ : measure α} [probability_measure μ] {s : set α} (hs : measurable_set s) (hμs : μ s < ∞)
  (c : E) :
  condexp_L1s_lm 𝕜 hm (indicator_L1s hs hμs c) =ᵐ[μ]
    λ x, (condexp_L1s_lm ℝ hm (@indicator_L1s α ℝ _ _ _ _ _ _ μ _ s hs hμs 1) x) • c :=
begin
  refine is_condexp_unique hm (indicator_L1s hs hμs c) _ _,
  exact is_condexp_condexp_L1s 𝕜 hm _,
  obtain ⟨h_int₁, ⟨f₁', h_meas₁, hff'₁⟩, h_int_eq₁⟩ := is_condexp_condexp_L1s ℝ hm
    (@indicator_L1s α ℝ _ _ _ _ _ _ μ _ s hs hμs 1),
  refine ⟨_, _, _⟩,
  { refine integrable.mono (integrable_const c) _ _,
    { exact ae_measurable.smul (Lp.ae_measurable _) ae_measurable_const, },
    { simp_rw norm_smul _ _,
      suffices h_le_1 : ∀ᵐ a ∂μ, ∥((condexp_L1s_lm ℝ hm) (indicator_L1s hs hμs (1:ℝ))) a∥ ≤ 1,
      { refine h_le_1.mono (λ x hx, _),
        nth_rewrite 1 ← one_mul (∥c∥),
        exact mul_le_mul hx le_rfl (norm_nonneg _) zero_le_one, },
      simp_rw real.norm_eq_abs,
      simp_rw abs_le,
      refine eventually.and _ _,
      { refine condexp_L1s_const_le hm _ (-1 : ℝ) _,
        refine (indicator_L1s_coe_ae_le hs hμs (1 : ℝ)).mono (λ x hx, _),
        refine neg_le_of_abs_le _,
        exact hx.trans (le_of_eq abs_one), },
      { refine condexp_L1s_le_const hm _ (1 : ℝ) _,
        refine (indicator_L1s_coe_ae_le hs hμs (1 : ℝ)).mono (λ x hx, _),
        refine le_of_abs_le _,
        exact hx.trans (le_of_eq abs_one), }, }, },
  { refine ⟨λ x, (f₁' x) • c, _, _⟩,
    { exact @measurable.smul _ _ _ _ _ _ _ _ _ m _ _ _ _ _ _ f₁' _ h_meas₁
        (@measurable_const _ _ _ m c), },
    { exact eventually_eq.fun_comp hff'₁ (λ x, x • c), }, },
  { intros t ht,
    have h_smul : ∫ a in t, (indicator_L1s hs hμs c) a ∂μ
        = ∫ a in t, ((indicator_L1s hs hμs (1 : ℝ)) a) • c ∂μ,
      from set_integral_congr_ae (hm t ht)  ((indicator_L1s_eq_smul 𝕜 _ _ c).mono (λ x hx hxs, hx)),
    refine eq.trans _ h_smul.symm,
    rw [integral_smul_const, integral_smul_const, h_int_eq₁ t ht], },
end

lemma norm_condexp_L1s_indicator_L1s {m m0 : measurable_space α} (hm : m ≤ m0) [complete_space E]
  {μ : measure α} [probability_measure μ] {s : set α} (hs : measurable_set s) (hμs : μ s < ∞)
  (c : E) :
  ∥condexp_L1s_lm 𝕜 hm (indicator_L1s hs hμs c)∥ ≤ ∥indicator_L1s hs hμs c∥ :=
begin
  rw [L1.simple_func.norm_eq, indicator_L1s_coe,
    norm_indicator_Lp ennreal.zero_lt_one ennreal.coe_ne_top, norm_def,
    snorm_congr_ae (condexp_L1s_indicator_L1s_eq hm hs hμs c),
    snorm_eq_snorm' ennreal.zero_lt_one.ne.symm ennreal.coe_ne_top, snorm'],
  simp_rw [ennreal.one_to_real, div_one, ennreal.rpow_one, nnnorm_smul, ennreal.coe_mul,
    real.rpow_one],
  rw [lintegral_mul_const _ (Lp.measurable _).nnnorm.ennreal_coe, ennreal.to_real_mul, mul_comm,
    ← of_real_norm_eq_coe_nnnorm, ennreal.to_real_of_real (norm_nonneg _)],
  swap, { apply_instance, },
  refine mul_le_mul le_rfl _ ennreal.to_real_nonneg (norm_nonneg _),
  suffices h_norm : ∥(condexp_L1s_lm ℝ hm) (indicator_L1s hs hμs (1 : ℝ))∥ ≤ (μ s).to_real,
  { rw [norm_def, snorm_eq_snorm' ennreal.zero_lt_one.ne.symm ennreal.coe_ne_top,
      snorm', ennreal.one_to_real, div_one] at h_norm,
    simp_rw ennreal.rpow_one at h_norm,
    exact h_norm, },
  refine (norm_condexp_L1s_indicator_L1s_R_le hm hs hμs (1 : ℝ)).trans _,
  simp only [one_mul, norm_one],
end

lemma norm_condexp_L1s_le {m m0 : measurable_space α} (hm : m ≤ m0) [complete_space E]
  {μ : measure α} [probability_measure μ] (f : α →₁ₛ[μ] E) :
  ∥condexp_L1s_lm 𝕜 hm f∥ ≤ ∥f∥ :=
begin
  rw L1.simple_func.norm_eq_integral,
  rw simple_func.map_integral _ _ (L1.simple_func.integrable _) norm_zero,
  nth_rewrite 0 L1.simple_func_eq_sum_indicator_L1s f,
  rw linear_map.map_sum,
  refine (norm_sum_le _ _).trans _,
  refine finset.sum_le_sum (λ x hxf, (norm_condexp_L1s_indicator_L1s hm _ _ x).trans _),
  rw [smul_eq_mul, mul_comm, norm_indicator_L1s hm],
end

lemma continuous_condexp_L1s {m m0 : measurable_space α} (hm : m ≤ m0) [complete_space E]
  {μ : measure α} [probability_measure μ] :
  continuous (@condexp_L1s_lm α E 𝕜 _ _ _ _ _ _ _ _ _ m m0 hm _ μ _) :=
linear_map.continuous_of_bound _ 1 (λ f, (norm_condexp_L1s_le hm f).trans (one_mul _).symm.le)

variables (𝕜)
def condexp_L1s_clm {m m0 : measurable_space α} (hm : m ≤ m0) [complete_space E] {μ : measure α}
  [probability_measure μ] :
  (α →₁ₛ[μ] E) →L[𝕜] (α →₁[μ] E) :=
{ to_linear_map := condexp_L1s_lm 𝕜 hm,
  cont := continuous_condexp_L1s hm, }

def condexp {m m0 : measurable_space α} (hm : m ≤ m0) [complete_space E] {μ : measure α}
  [probability_measure μ] :
  (α →₁[μ] E) →L[𝕜] (α →₁[μ] E) :=
@continuous_linear_map.extend 𝕜 (α →₁ₛ[μ] E) (α →₁[μ] E) (α →₁[μ] E) _ _ _
  _ _ _ _ (condexp_L1s_clm 𝕜 hm) _ (L1.simple_func.coe_to_L1 α E 𝕜)
  L1.simple_func.dense_range L1.simple_func.uniform_inducing
variables {𝕜}

end measure_theory
