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
open_locale nnreal ennreal topological_space big_operators measure_theory

namespace measure_theory

variables {α E F 𝕜 : Type*} [is_R_or_C 𝕜] {p : ℝ≥0∞}
  [measurable_space E] [inner_product_space 𝕜 E] [borel_space E] [second_countable_topology E]
  [normed_group F] [measurable_space F] [borel_space F] [second_countable_topology F]
  [measurable_space 𝕜] [borel_space 𝕜]

notation α ` →₂[`:25 μ `] ` E := measure_theory.Lp E 2 μ

include 𝕜
private lemma add_mem' {m m0 : measurable_space α} (hm : m ≤ m0) {p : ℝ≥0∞} {μ : measure α}
  (f g : Lp E p μ) (hf : ∃ f' : α → E, @measurable α _ m _ f' ∧ f =ᵐ[μ] f')
  (hg : ∃ g' : α → E, @measurable α _ m _ g' ∧ g =ᵐ[μ] g') :
  ∃ f_add : α → E, @measurable α _ m _ f_add ∧ ⇑(f+g) =ᵐ[μ] f_add :=
begin
  rcases hf with ⟨f', h_f'_meas, hff'⟩,
  rcases hg with ⟨g', h_g'_meas, hgg'⟩,
  refine ⟨f'+g', @measurable.add α m _ _ _ _ f' g' h_f'_meas h_g'_meas, _⟩,
  exact eventually_eq.trans (Lp.coe_fn_add f g) (eventually_eq.comp₂ hff' (+) hgg'),
end
omit 𝕜

private lemma smul_mem' {m m0 : measurable_space α} (hm : m ≤ m0)
  {p : ℝ≥0∞} {μ : measure α} (c : 𝕜) (f : Lp E p μ)
  (hf : ∃ f' : α → E, @measurable α _ m _ f' ∧ f =ᵐ[μ] f') :
  ∃ f_add : α → E, @measurable α _ m _ f_add ∧ ⇑(c • f) =ᵐ[μ] f_add :=
begin
  rcases hf with ⟨f', h_f'_meas, hff'⟩,
  refine ⟨c • f', @measurable.const_smul α m _ _ _ _ _ _ f' h_f'_meas c, _⟩,
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

lemma mem_Lp_sub_iff_ae_eq_measurable {m m0 : measurable_space α} {hm : m ≤ m0} {p : ℝ≥0∞}
  {μ : measure α} {f : Lp E p μ} :
  f ∈ Lp_sub hm 𝕜 E p μ ↔ ∃ g : α → E, @measurable α _ m _ g ∧ f =ᵐ[μ] g :=
by simp_rw [← set_like.mem_coe, ← submodule.mem_carrier, Lp_sub, set.mem_set_of_eq]

lemma Lp_sub.ae_eq_measurable {m m0 : measurable_space α} {hm : m ≤ m0}
  {p : ℝ≥0∞} {μ : measure α} (f : Lp_sub hm 𝕜 E p μ) :
  ∃ g : α → E, @measurable α _ m _ g ∧ f =ᵐ[μ] g :=
mem_Lp_sub_iff_ae_eq_measurable.mp f.mem

variables (𝕜 E)
lemma mem_Lp_sub_self {m0 : measurable_space α} (p : ℝ≥0∞) (μ : measure α) (f : Lp E p μ) :
  f ∈ Lp_sub le_rfl 𝕜 E p μ :=
by { rw mem_Lp_sub_iff_ae_eq_measurable, exact (Lp.ae_measurable f), }
variables {𝕜 E}

lemma Lp_sub_coe {m m0 : measurable_space α} (hm : m ≤ m0) {p : ℝ≥0∞} {μ : measure α}
  {f : Lp_sub hm 𝕜 E p μ} :
  ⇑f = (f : Lp E p μ) :=
coe_fn_coe_base f

lemma ae_eq_measurable_of_tendsto {α E} {m m0 : measurable_space α} (hm : m ≤ m0) {μ : measure α}
  {ι} [nonempty ι] [linear_order ι] [hp : fact (1 ≤ p)] [normed_group E] [measurable_space E]
  [borel_space E] [second_countable_topology E] [complete_space E]
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
      exact @measurable.sub α m _ _ _ _ (g n.fst) (g n.snd) (hg n.fst) (hg n.snd), },
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
    refine @measurable.sub α m _ _ _ _ (g_Lp n) g_Lp_lim _ h_g_lim_meas_m,
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

instance {m m0 : measurable_space α} (hm : m ≤ m0) {μ : measure α} [complete_space E]
  [hp : fact(1 ≤ p)] : complete_space (Lp_sub hm 𝕜 E p μ) :=
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

section is_condexp

variables {G : Type*} [measurable_space G] [normed_group G] [borel_space G]
  [second_countable_topology G] [complete_space G] [normed_space ℝ G]

def is_condexp_L1_sub {m m0 : measurable_space α} {hm : m ≤ m0} {μ : measure α} [complete_space E]
  (f : Lp_sub hm 𝕜 E 1 μ) (g : α → E) :
  Prop :=
∀ s (hs : @measurable_set α m s), ∫ a in s, f a ∂μ = ∫ a in s, g a ∂μ

/-- `f` is a conditional expectation of `g` with respect to the measurable space structure `m`. -/
def is_condexp (m : measurable_space α) [m0 : measurable_space α] (f g : α → G) (μ : measure α) :
  Prop :=
integrable f μ ∧ (∃ f' : α → G, @measurable α _ m _ f' ∧ f =ᵐ[μ] f')
  ∧ ∀ s (hs : @measurable_set α m s), ∫ a in s, f a ∂μ = ∫ a in s, g a ∂μ

variables {m m0 : measurable_space α} {μ : measure α} {f f₁ f₂ g g₁ g₂ : α → G}

lemma is_condexp_congr_ae' (hm : m ≤ m0) (hf12 : f₁ =ᵐ[μ] f₂) (hf₁ : is_condexp m f₁ g μ) :
  is_condexp m f₂ g μ :=
begin
  rcases hf₁ with ⟨h_int, ⟨f, h_meas, h_eq⟩, h_int_eq⟩,
  refine ⟨(integrable_congr hf12).mp h_int, ⟨f, h_meas, hf12.symm.trans h_eq⟩, λ s hs, _⟩,
  have h_to_f1 : ∫ (a : α) in s, f₂ a ∂μ = ∫ (a : α) in s, f₁ a ∂μ,
    from set_integral_congr_ae (hm s hs) (hf12.mono (λ x hx hxs, hx.symm)),
  rw h_to_f1,
  exact h_int_eq s hs,
end

lemma is_condexp_congr_ae (hm : m ≤ m0) (hf12 : f₁ =ᵐ[μ] f₂) :
  is_condexp m f₁ g μ ↔ is_condexp m f₂ g μ :=
⟨λ h, is_condexp_congr_ae' hm hf12 h, λ h, is_condexp_congr_ae' hm hf12.symm h⟩

lemma is_condexp_congr_ae_right' (hm : m ≤ m0) (hg12 : g₁ =ᵐ[μ] g₂) (hf₁ : is_condexp m f g₁ μ) :
  is_condexp m f g₂ μ :=
begin
  rcases hf₁ with ⟨h_int, h_meas, h_int_eq⟩,
  refine ⟨h_int, h_meas, λ s hs, _⟩,
  have h_to_g1 : ∫ (a : α) in s, g₂ a ∂μ = ∫ (a : α) in s, g₁ a ∂μ,
    from set_integral_congr_ae (hm s hs) (hg12.mono (λ x hx hxs, hx.symm)),
  rw h_to_g1,
  exact h_int_eq s hs,
end

lemma is_condexp_congr_ae_right (hm : m ≤ m0) (hg12 : g₁ =ᵐ[μ] g₂) :
  is_condexp m f g₁ μ ↔ is_condexp m f g₂ μ :=
⟨λ h, is_condexp_congr_ae_right' hm hg12 h, λ h, is_condexp_congr_ae_right' hm hg12.symm h⟩

lemma is_condexp_iff_is_condexp_L1_sub (hm : m ≤ m0) [complete_space E] (f : Lp_sub hm 𝕜 E 1 μ)
  (g : α → E) :
  is_condexp m (f : α → E) g μ ↔ is_condexp_L1_sub f g :=
begin
  have h_mem : mem_ℒp f 1 μ, from Lp.mem_ℒp (f : α →₁[μ] E),
  simp_rw [is_condexp, is_condexp_L1_sub, ← mem_ℒp_one_iff_integrable, h_mem,
    Lp_sub.ae_eq_measurable f, true_and],
end

end is_condexp

section ae_eq_of_forall_set_integral_eq
variables [measurable_space α] {μ : measure α}

lemma ae_const_le_iff_forall_lt_measure_zero (f : α → ℝ) (c : ℝ) :
  (∀ᵐ x ∂μ, c ≤ f x) ↔ ∀ b < c, μ {x | f x ≤ b} = 0 :=
begin
  rw ae_iff,
  push_neg,
  have h_Union : {x | f x < c} = ⋃ (r : ℚ) (hr : ↑r < c), {x | f x ≤ r},
  { ext1 x,
    simp_rw [set.mem_Union, set.mem_set_of_eq],
    split; intro h,
    { obtain ⟨q, lt_q, q_lt⟩ := exists_rat_btwn h, exact ⟨q, q_lt, lt_q.le⟩, },
    { obtain ⟨q, q_lt, q_le⟩ := h, exact q_le.trans_lt q_lt, }, },
  rw h_Union,
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

lemma ae_nonneg_of_forall_set_ℝ_measurable [finite_measure μ] (f : α → ℝ) (hf : integrable f μ)
  (hfm : measurable f) (hf_zero : ∀ s : set α, measurable_set s → 0 ≤ ∫ x in s, f x ∂μ) :
  0 ≤ᵐ[μ] f :=
begin
  simp_rw [eventually_le, pi.zero_apply],
  rw ae_const_le_iff_forall_lt_measure_zero,
  intros b hb_neg,
  let s := {x | f x ≤ b},
  have hs : measurable_set s, from measurable_set_le hfm measurable_const,
  have hfs : ∀ x ∈ s, f x ≤ b, from λ x hxs, hxs,
  have h_int_gt : μ s ≠ 0 → ∫ x in s, f x ∂μ ≤ b * (μ s).to_real,
  { intro h_ne_zero,
    have h_const_le : ∫ x in s, f x ∂μ ≤ ∫ x in s, b ∂μ,
    { refine set_integral_mono_ae_restrict hf.integrable_on
        (integrable_on_const.mpr (or.inr (measure_lt_top _ _))) _,
      rw [eventually_le, ae_restrict_iff hs],
      exact eventually_of_forall hfs, },
    rwa [set_integral_const, smul_eq_mul, mul_comm] at h_const_le, },
  by_contra,
  specialize h_int_gt h,
  refine (lt_self_iff_false (∫ x in s, f x ∂μ)).mp (h_int_gt.trans_lt _),
  refine lt_of_lt_of_le _ (hf_zero s hs),
  refine mul_neg_iff.mpr (or.inr _),
  refine ⟨hb_neg, (ennreal.to_real_nonneg).lt_of_ne (λ h_eq, h _)⟩,
  have hμs_to_real := (ennreal.to_real_eq_zero_iff _).mp h_eq.symm,
  cases hμs_to_real,
  { exact hμs_to_real, },
  { exact absurd hμs_to_real (measure_ne_top _ _), },
end

lemma ae_nonneg_of_forall_set_ℝ [finite_measure μ] (f : α → ℝ) (hf : integrable f μ)
  (hf_zero : ∀ s : set α, measurable_set s → 0 ≤ ∫ x in s, f x ∂μ) :
  0 ≤ᵐ[μ] f :=
begin
  rcases hf with ⟨⟨f', hf'_meas, hf_ae⟩, hf_finite_int⟩,
  have hf'_integrable : integrable f' μ,
  { exact integrable.congr ⟨⟨f', hf'_meas, hf_ae⟩, hf_finite_int⟩ hf_ae, },
  have hf'_zero : ∀ (s : set α), measurable_set s → 0 ≤ ∫ (x : α) in s, f' x ∂μ,
  { intros s hs,
    rw set_integral_congr_ae hs (hf_ae.mono (λ x hx hxs, hx.symm)),
    exact hf_zero s hs, },
  exact (ae_nonneg_of_forall_set_ℝ_measurable f' hf'_integrable hf'_meas hf'_zero).trans
    hf_ae.symm.le,
end

lemma ae_eq_zero_of_forall_set_ℝ [finite_measure μ] (f : α → ℝ) (hf : integrable f μ)
  (hf_zero : ∀ s : set α, measurable_set s → ∫ x in s, f x ∂μ = 0) :
  f =ᵐ[μ] 0 :=
begin
  have hf_nonneg :  ∀ s : set α, measurable_set s → 0 ≤ ∫ x in s, f x ∂μ,
    from λ s hs, (hf_zero s hs).symm.le,
  suffices h_and : f ≤ᵐ[μ] 0 ∧ 0 ≤ᵐ[μ] f,
  { refine h_and.1.mp (h_and.2.mono (λ x hx1 hx2, _)),
    exact le_antisymm hx2 hx1, },
  refine ⟨_, ae_nonneg_of_forall_set_ℝ f hf hf_nonneg⟩,
  suffices h_neg : 0 ≤ᵐ[μ] -f,
  { refine h_neg.mono (λ x hx, _),
    rw pi.neg_apply at hx,
    refine le_of_neg_le_neg _,
    simpa using hx, },
  have hf_neg : integrable (-f) μ, from hf.neg,
  have hf_nonneg_neg :  ∀ (s : set α), measurable_set s → 0 ≤ ∫ (x : α) in s, (-f) x ∂μ,
  { intros s hs,
    simp_rw pi.neg_apply,
    rw [integral_neg, neg_nonneg],
    exact (hf_zero s hs).le, },
  exact ae_nonneg_of_forall_set_ℝ (-f) hf_neg hf_nonneg_neg,
end

lemma forall_inner_eq_zero_iff (x : E) : (∀ c : E, inner c x = (0 : 𝕜)) ↔ x = 0 :=
⟨λ hx, inner_self_eq_zero.mp (hx x), λ hx, by simp [hx]⟩

lemma ae_eq_zero_of_forall_inner_ae_eq_zero (μ : measure α) (f : α → E)
  (hf : ∀ c : E, ∀ᵐ x ∂μ, inner c (f x) = (0 : 𝕜)) :
  f =ᵐ[μ] 0 :=
begin
  let s := dense_seq E,
  have hs : dense_range s := dense_range_dense_seq E,
  have hfs : ∀ n : ℕ, ∀ᵐ x ∂μ, inner (s n) (f x) = (0 : 𝕜),
  { exact λ n, hf (s n), },
  have hf' : ∀ᵐ x ∂μ, ∀ n : ℕ, inner (s n) (f x) = (0 : 𝕜),
  { rwa ae_all_iff, },
  refine hf'.mono (λ x hx, _),
  rw pi.zero_apply,
  rw ← inner_self_eq_zero,
  have h_closed : is_closed {c : E | inner c (f x) = (0 : 𝕜)},
  { refine is_closed_eq _ continuous_const,
    exact continuous.inner continuous_id continuous_const, },
  exact @is_closed_property ℕ E _ s (λ c, inner c (f x) = (0 : 𝕜)) hs h_closed (λ n, hx n) _,
end

lemma ae_measurable.re {f : α → 𝕜} (hf : ae_measurable f μ) :
  ae_measurable (λ x, is_R_or_C.re (f x)) μ :=
measurable.comp_ae_measurable is_R_or_C.continuous_re.measurable hf

lemma ae_measurable.im {f : α → 𝕜} (hf : ae_measurable f μ) :
  ae_measurable (λ x, is_R_or_C.im (f x)) μ :=
measurable.comp_ae_measurable is_R_or_C.continuous_im.measurable hf

lemma integrable.re {f : α → 𝕜} (hf : integrable f μ) :
  integrable (λ x, is_R_or_C.re (f x)) μ :=
begin
  have h_norm_le : ∀ a, ∥is_R_or_C.re (f a)∥ ≤ ∥f a∥,
  { intro a,
    rw [is_R_or_C.norm_eq_abs, is_R_or_C.norm_eq_abs, is_R_or_C.abs_to_real],
    exact is_R_or_C.abs_re_le_abs _, },
  exact integrable.mono hf (ae_measurable.re hf.1) (eventually_of_forall h_norm_le),
end

lemma integrable.im {f : α → 𝕜} (hf : integrable f μ) :
  integrable (λ x, is_R_or_C.im (f x)) μ :=
begin
  have h_norm_le : ∀ a, ∥is_R_or_C.im (f a)∥ ≤ ∥f a∥,
  { intro a,
    rw [is_R_or_C.norm_eq_abs, is_R_or_C.norm_eq_abs, is_R_or_C.abs_to_real],
    exact is_R_or_C.abs_im_le_abs _, },
  exact integrable.mono hf (ae_measurable.im hf.1) (eventually_of_forall h_norm_le),
end

include 𝕜
lemma integrable.const_inner {f : α → E} (hf : integrable f μ)
  (c : E) :
  integrable (λ x, (inner c (f x) : 𝕜)) μ :=
begin
  have hf_const_mul : integrable (λ x, ∥c∥ * ∥f x∥) μ, from integrable.const_mul hf.norm (∥c∥),
  refine integrable.mono hf_const_mul (ae_measurable.inner ae_measurable_const hf.1) _,
  refine eventually_of_forall (λ x, _),
  rw is_R_or_C.norm_eq_abs,
  refine (abs_inner_le_norm _ _).trans _,
  simp,
end

lemma integral_const_inner [complete_space E] {f : α → E} (hf : integrable f μ) (c : E) :
  ∫ x, (inner c (f x) : 𝕜) ∂μ = inner c (∫ x, f x ∂μ) :=
@continuous_linear_map.integral_comp_comm α E 𝕜 _ _ _ μ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  (inner_right c) _ hf

lemma ae_eq_zero_of_forall_set [finite_measure μ] [complete_space E] (f : α → E)
  (hf : integrable f μ) (hf_zero : ∀ s : set α, measurable_set s → ∫ x in s, f x ∂μ = 0) :
  f =ᵐ[μ] 0 :=
begin
  refine ae_eq_zero_of_forall_inner_ae_eq_zero μ f (λ c, _),
  suffices h_re_im : (∀ᵐ (x : α) ∂μ, is_R_or_C.re (inner c (f x) : 𝕜) = 0)
    ∧ ∀ᵐ (x : α) ∂μ, is_R_or_C.im (inner c (f x) : 𝕜) = 0,
  { rw ← eventually_and at h_re_im,
    refine h_re_im.mono (λ x hx, _),
    rw is_R_or_C.ext_iff,
    simpa using hx, },
  have hf_inner_re : integrable (λ x, is_R_or_C.re (inner c (f x) : 𝕜)) μ,
  { refine integrable.re _,
    exact integrable.const_inner hf c, },
  have hf_inner_im : integrable (λ x, is_R_or_C.im (inner c (f x) : 𝕜)) μ,
  { refine integrable.im _,
    exact integrable.const_inner hf c, },
  have hf_zero_inner : ∀ s, measurable_set s → ∫ (x : α) in s, (inner c (f x) : 𝕜) ∂μ = 0,
  { intros s hs,
    rw integral_const_inner hf.integrable_on c,
    simp [hf_zero s hs], },
  have hf_zero_inner_re : ∀ s, measurable_set s → ∫ x in s, is_R_or_C.re (inner c (f x) : 𝕜) ∂μ = 0,
  { intros s hs,
    rw integral_re (integrable.const_inner hf c).integrable_on,
    rw hf_zero_inner s hs,
    simp, },
  have hf_zero_inner_im : ∀ s, measurable_set s → ∫ x in s, is_R_or_C.im (inner c (f x) : 𝕜) ∂μ = 0,
  { intros s hs,
    rw integral_im (integrable.const_inner hf c).integrable_on,
    rw hf_zero_inner s hs,
    simp, },
  have h_zero_re : ∀ᵐ (x : α) ∂μ, is_R_or_C.re (inner c (f x) : 𝕜) = 0,
    from ae_eq_zero_of_forall_set_ℝ _ hf_inner_re hf_zero_inner_re,
  have h_zero_im : ∀ᵐ (x : α) ∂μ, is_R_or_C.im (inner c (f x) : 𝕜) = 0,
    from ae_eq_zero_of_forall_set_ℝ _ hf_inner_im hf_zero_inner_im,
  exact ⟨h_zero_re, h_zero_im⟩,
end

lemma ae_eq_of_forall_set_integral_eq [finite_measure μ] [complete_space E] (f g : α → E)
  (hf : integrable f μ) (hg : integrable g μ)
  (hfg : ∀ s : set α, measurable_set s → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ) :
  f =ᵐ[μ] g :=
begin
  suffices h_sub : f-g =ᵐ[μ] 0,
  { refine h_sub.mono (λ x hx, _),
    rw [pi.sub_apply, pi.zero_apply] at hx,
    exact sub_eq_zero.mp hx, },
  have hfg' : ∀ s : set α, measurable_set s → ∫ x in s, (f - g) x ∂μ = 0,
  { intros s hs,
    rw integral_sub' hf.integrable_on hg.integrable_on,
    exact sub_eq_zero.mpr (hfg s hs), },
  exact ae_eq_zero_of_forall_set (f-g) (hf.sub hg) hfg',
end
omit 𝕜

end ae_eq_of_forall_set_integral_eq

lemma measurable_set_eq_fun [measurable_space α] [normed_group E] [measurable_space E]
  [borel_space E] [second_countable_topology E] {f g : α → E} (hf : measurable f)
  (hg : measurable g) :
  measurable_set {x | f x = g x} :=
begin
  let s := {x | (f-g) x = (0 : E)},
  have hs : measurable_set s, from (hf.sub hg) measurable_set_eq,
  have h_set_eq : {x : α | f x = g x} = s,
  { ext, simp_rw [set.mem_set_of_eq, pi.sub_apply, sub_eq_zero], },
  rwa h_set_eq,
end

section integral_trim

variables {m m0 : measurable_space α} {μ : measure α}

lemma trim_restrict (hm : m ≤ m0) (μ : measure α) {s : set α} (hs : @measurable_set α m s) :
  @measure.restrict α m (μ.trim hm) s = (μ.restrict s).trim hm :=
begin
  ext1 t ht,
  rw [@measure.restrict_apply α m _ _ _ ht, trim_measurable hm ht,
    measure.restrict_apply (hm t ht), trim_measurable hm (@measurable_set.inter α m t s ht hs)],
end

lemma integrable_trim_of_measurable (hm : m ≤ m0) [normed_group E] [opens_measurable_space E]
  {f : α → E} (hf : @measurable α E m _ f) (hf_int : integrable f μ) :
  @integrable α E m _ _ f (μ.trim hm) :=
begin
  refine ⟨@measurable.ae_measurable α E m _ f (μ.trim hm) hf, _⟩,
  rw [has_finite_integral, lintegral_trim hm _],
  { exact hf_int.2, },
  refine @measurable.ennreal_coe α m _ _,
  exact @measurable.nnnorm E α _ _ _ m _ hf,
end

variables [normed_group E] [borel_space E] [second_countable_topology E] [complete_space E]
  [normed_space ℝ E]

def simple_func_larger_space (hm : m ≤ m0) (f : @simple_func α m E) : simple_func α E :=
⟨@simple_func.to_fun α m E f, λ x, hm _ (@simple_func.measurable_set_fiber α E m f x),
  @simple_func.finite_range α E m f⟩

lemma simple_func_larger_space_eq (hm : m ≤ m0) (f : @simple_func α m E) :
  ⇑(simple_func_larger_space hm f) = f :=
rfl

lemma integral_simple_func' {α} [measurable_space α] {μ : measure α}
  (f : simple_func α E) (hf_int : integrable f μ) :
  ∫ x, f x ∂μ = ∑ x in f.range, (ennreal.to_real (μ (f ⁻¹' {x}))) • x :=
begin
  rw [← simple_func.integral, integral_eq f hf_int, ← L1.simple_func.to_L1_eq_to_L1,
    L1.simple_func.integral_L1_eq_integral, L1.simple_func.integral_eq_integral],
  refine simple_func.integral_congr _ (L1.simple_func.to_simple_func_to_L1 _ _),
  exact L1.simple_func.integrable _,
end

lemma integral_simple_func (hm : m ≤ m0) (f : @simple_func α m E) (hf_int : integrable f μ) :
  ∫ x, f x ∂μ = ∑ x in (@simple_func.range α E m f), (ennreal.to_real (μ (f ⁻¹' {x}))) • x :=
begin
  let f0 := simple_func_larger_space hm f,
  simp_rw ← simple_func_larger_space_eq hm f,
  have hf0_int : integrable f0 μ, by rwa simple_func_larger_space_eq,
  rw integral_simple_func' _ hf0_int,
  congr,
end

lemma integral_trim_simple_func (hm : m ≤ m0) (f : @simple_func α m E) (hf_int : integrable f μ) :
  ∫ x, f x ∂μ = @integral α E m _ _ _ _ _ _ (μ.trim hm) f :=
begin
  have hf : @measurable _ _ m _ f, from @simple_func.measurable α E m _ f,
  have hf_int_m := integrable_trim_of_measurable hm hf hf_int,
  rw [integral_simple_func le_rfl f hf_int_m, integral_simple_func hm f hf_int],
  congr,
  ext1 x,
  congr,
  exact (trim_measurable hm (@simple_func.measurable_set_fiber α E m f x)).symm,
end

lemma integral_trim (hm : m ≤ m0) (f : α → E) (hf : @measurable α E m _ f)
  (hf_int : integrable f μ) :
  ∫ x, f x ∂μ = @integral α E m _ _ _ _ _ _ (μ.trim hm) f :=
begin
  let F := @simple_func.approx_on E α _ _ _ m _ hf set.univ 0 (set.mem_univ 0) _,
  have hF_meas : ∀ n, @measurable _ _ m _ (F n), from λ n, @simple_func.measurable α E m _ (F n),
  have hF_int : ∀ n, integrable (F n) μ,
    from simple_func.integrable_approx_on_univ (hf.mono hm le_rfl) hf_int,
  have hF_int_m : ∀ n, @integrable α E m _ _ (F n) (μ.trim hm),
    from λ n, integrable_trim_of_measurable hm (hF_meas n) (hF_int n),
  have hF_eq : ∀ n, ∫ x, F n x ∂μ = @integral α E m _ _ _ _ _ _ (μ.trim hm) (F n),
    from λ n, integral_trim_simple_func hm (F n) (hF_int n),
  have h_lim_1 : at_top.tendsto (λ n, ∫ x, F n x ∂μ) (𝓝 (∫ x, f x ∂μ)),
  { refine tendsto_integral_of_L1 f hf_int (eventually_of_forall hF_int) _,
    exact simple_func.tendsto_approx_on_univ_L1_edist (hf.mono hm le_rfl) hf_int, },
  have h_lim_2 :  at_top.tendsto (λ n, ∫ x, F n x ∂μ)
    (𝓝 (@integral α E m _ _ _ _ _ _ (μ.trim hm) f)),
  { simp_rw hF_eq,
    refine @tendsto_integral_of_L1 α E m _ _ _ _ _ _ (μ.trim hm) _ f
      (integrable_trim_of_measurable hm hf hf_int) _ _ (eventually_of_forall hF_int_m) _,
    exact @simple_func.tendsto_approx_on_univ_L1_edist α E m _ _ _ _ f _ hf
      (integrable_trim_of_measurable hm hf hf_int), },
  exact tendsto_nhds_unique h_lim_1 h_lim_2,
end

lemma ae_eq_trim_of_measurable {E} [normed_group E] [measurable_space E] [borel_space E]
  [second_countable_topology E] (hm : m ≤ m0)
  {f g : α → E} (hf : @measurable α E m _ f) (hg : @measurable α E m _ g) (hfg : f =ᵐ[μ] g) :
  eventually_eq (@measure.ae α m (μ.trim hm)) f g :=
begin
  rw [eventually_eq, ae_iff, trim_measurable hm _],
  { exact hfg, },
  { exact @measurable_set.compl α _ m (@measurable_set_eq_fun α E _ m _ _ _ _ _ _ hf hg), },
end

lemma ae_eq_of_ae_eq_trim {E} (hm : m ≤ m0) {f₁ f₂ : α → E}
  (h12 : eventually_eq (@measure.ae α m (μ.trim hm)) f₁ f₂) :
  f₁ =ᵐ[μ] f₂ :=
ae_eq_null_of_trim hm h12

lemma ae_eq_trim_iff {E} [normed_group E] [measurable_space E] [borel_space E]
  [second_countable_topology E] (hm : m ≤ m0)
  {f g : α → E} (hf : @measurable α E m _ f) (hg : @measurable α E m _ g) :
  (eventually_eq (@measure.ae α m (μ.trim hm)) f g) ↔ f =ᵐ[μ] g :=
⟨ae_eq_of_ae_eq_trim hm, ae_eq_trim_of_measurable hm hf hg⟩

instance finite_measure_trim (hm : m ≤ m0) [finite_measure μ] : @finite_measure α m (μ.trim hm) :=
{ measure_univ_lt_top :=
    by { rw trim_measurable hm (@measurable_set.univ _ m), exact measure_lt_top _ _, } }

end integral_trim

variables (𝕜)
include 𝕜
lemma is_condexp_unique {m m0 : measurable_space α} (hm : m ≤ m0) {μ : measure α} [finite_measure μ]
  [complete_space E] {f₁ f₂ : α → E} (g : α → E) (hf₁ : is_condexp m f₁ g μ)
  (hf₂ : is_condexp m f₂ g μ) :
  f₁ =ᵐ[μ] f₂ :=
begin
  rcases hf₁ with ⟨h_int₁, ⟨f₁', h_meas₁, hff'₁⟩, h_int_eq₁⟩,
  rcases hf₂ with ⟨h_int₂, ⟨f₂', h_meas₂, hff'₂⟩, h_int_eq₂⟩,
  refine hff'₁.trans (eventually_eq.trans _ hff'₂.symm),
  have h : ∀ s : set α, @measurable_set α m s → ∫ x in s, f₁' x ∂μ = ∫ x in s, f₂' x ∂μ,
  { intros s hsm,
    have h₁ : ∫ x in s, f₁' x ∂μ = ∫ x in s, g x ∂μ,
    { rw ← h_int_eq₁ s hsm,
      exact set_integral_congr_ae (hm s hsm) (hff'₁.mono (λ x hx hxs, hx.symm)), },
    rw [h₁, ← h_int_eq₂ s hsm],
    exact set_integral_congr_ae (hm s hsm) (hff'₂.mono (λ x hx hxs, hx)), },
  refine ae_eq_of_ae_eq_trim hm _,
  have h_int₁' : integrable f₁' μ, from (integrable_congr hff'₁).mp h_int₁,
  have h_int₂' : integrable f₂' μ, from (integrable_congr hff'₂).mp h_int₂,
  refine @ae_eq_of_forall_set_integral_eq α E 𝕜 _ _ _ _ _ _ _ _ _ m _ _ _ _ _ _ _ _,
  { exact integrable_trim_of_measurable hm h_meas₁ h_int₁', },
  { exact integrable_trim_of_measurable hm h_meas₂ h_int₂', },
  { intros s hs,
    specialize h s hs,
    rw integral_trim hm _ h_meas₁ h_int₁'.integrable_on at h,
    rw integral_trim hm _ h_meas₂ h_int₂'.integrable_on at h,
    rwa ← trim_restrict hm μ hs at h, },
end
omit 𝕜

/-- Conditional expectation of a function in L2 with respect to a sigma-algebra -/
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

lemma mem_ℒ0_iff_ae_measurable [measurable_space α] [normed_group E] {μ : measure α} {f : α → E} :
  mem_ℒp f 0 μ ↔ ae_measurable f μ :=
by { simp_rw mem_ℒp, refine and_iff_left _, simp, }

lemma indicator_comp {E F} [has_zero E] [has_zero F] (s : set α) (c : E) (f : E → F) (g : α → E)
  (hf : f 0 = 0) :
  (λ x, f (s.indicator g x)) = s.indicator (f ∘ g) :=
by { ext1 x, by_cases hx : x ∈ s; simp [hx, hf] }

lemma indicator_const_comp {E F} [has_zero E] [has_zero F] (s : set α) (c : E) (f : E → F)
  (hf : f 0 = 0) :
  (λ x, f (s.indicator (λ x, c) x)) = s.indicator (λ x, f c) :=
indicator_comp s c f (λ x, c) hf

lemma snorm_ess_sup_indicator_le [measurable_space α] [normed_group E] {μ : measure α}
  (s : set α) (f : α → E) :
  snorm_ess_sup (s.indicator f) μ ≤ snorm_ess_sup f μ :=
begin
  refine ess_sup_mono_ae (eventually_of_forall (λ x, _)),
  rw [ennreal.coe_le_coe, nnnorm_indicator_eq_indicator_nnnorm],
  exact set.indicator_le_self s _ x,
end

lemma snorm_ess_sup_indicator_const_le [measurable_space α] [normed_group E] {μ : measure α}
  (s : set α) (c : E) :
  snorm_ess_sup (s.indicator (λ x : α , c)) μ ≤ (nnnorm c : ℝ≥0∞) :=
begin
  refine (snorm_ess_sup_indicator_le s (λ x, c)).trans _,
  by_cases hμ0 : μ = 0,
  { simp [hμ0], },
  rw snorm_ess_sup_const c hμ0,
  exact le_rfl,
end

lemma snorm_indicator_const [measurable_space α] [normed_group E]
  {μ : measure α} {s : set α} {c : E} (hs : measurable_set s) (hp : 0 < p) (hp_top : p ≠ ∞) :
  snorm (s.indicator (λ x, c)) p μ = (nnnorm c) * (μ s) ^ (1 / p.to_real) :=
begin
  have hp_pos : 0 < p.to_real, from ennreal.to_real_pos_iff.mpr ⟨hp, hp_top⟩,
  rw snorm_eq_snorm' hp.ne.symm hp_top,
  rw snorm',
  simp_rw [nnnorm_indicator_eq_indicator_nnnorm, ennreal.coe_indicator],
  have h_indicator_pow : (λ a : α, s.indicator (λ (x : α), (nnnorm c : ℝ≥0∞)) a ^ p.to_real)
    = s.indicator (λ (x : α), ↑(nnnorm c) ^ p.to_real),
  { rw indicator_const_comp s (nnnorm c : ℝ≥0∞) (λ x, x ^ p.to_real) _, simp [hp_pos], },
  rw [h_indicator_pow, lintegral_indicator _ hs, set_lintegral_const, ennreal.mul_rpow_of_nonneg],
  swap, { simp [hp_pos.le], },
  rw [← ennreal.rpow_mul, mul_one_div_cancel hp_pos.ne.symm, ennreal.rpow_one],
end

lemma mem_ℒp_indicator_const (p : ℝ≥0∞) [measurable_space α] [normed_group E] {μ : measure α}
  {s : set α} (hs : measurable_set s) (hμs : μ s < ∞) (c : E) :
  mem_ℒp (s.indicator (λ x : α , c)) p μ :=
begin
  refine ⟨(ae_measurable_indicator_iff hs).mp ae_measurable_const, _⟩,
  by_cases hp0 : p = 0,
  { simp [hp0], },
  rw ← ne.def at hp0,
  by_cases hp_top : p = ∞,
  { rw [hp_top, snorm_exponent_top],
    exact (snorm_ess_sup_indicator_const_le s c).trans_lt ennreal.coe_lt_top, },
  have hp_pos : 0 < p.to_real,
    from ennreal.to_real_pos_iff.mpr ⟨lt_of_le_of_ne (zero_le _) hp0.symm, hp_top⟩,
  rw snorm_eq_snorm' hp0 hp_top,
  simp_rw snorm',
  refine ennreal.rpow_lt_top_of_nonneg _ _,
  { simp only [hp_pos.le, one_div, inv_nonneg], },
  simp_rw [nnnorm_indicator_eq_indicator_nnnorm, ennreal.coe_indicator],
  have h_indicator_pow : (λ a : α, s.indicator (λ (x : α), (nnnorm c : ℝ≥0∞)) a ^ p.to_real)
    = s.indicator (λ (x : α), ↑(nnnorm c) ^ p.to_real),
  { rw indicator_const_comp s (nnnorm c : ℝ≥0∞) (λ x, x ^ p.to_real) _, simp [hp_pos], },
  rw [h_indicator_pow, lintegral_indicator _ hs],
  simp [hp_pos, hμs.ne, not_le.mpr hp_pos, not_lt.mpr hp_pos.le],
end

lemma mem_ℒp_indicator_ae {α E} [measurable_space α] [measurable_space E] [normed_group E]
  {μ : measure α} {s : set α} (hs : measurable_set s) (hμs : μ s < ∞) (c : E) :
  mem_ℒp (indicator_ae α μ hs c) p μ :=
by { rw mem_ℒp_congr_ae indicator_ae_coe, exact mem_ℒp_indicator_const p hs hμs c }

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
  rw [norm_def, snorm_congr_ae (indicator_Lp_coe_fn hs hμs c),
    snorm_indicator_const hs hp_pos hp_ne_top, ennreal.to_real_mul, ennreal.to_real_rpow],
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
by { specialize hf_int (∫ x, f x ∂μ), rwa [integral_inner hf, inner_self_eq_zero] at hf_int }

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

lemma simple_func.exists_forall_norm_le {α β} [measurable_space α] [has_norm β]
  (f : simple_func α β) :
  ∃ C, ∀ x, ∥f x∥ ≤ C :=
simple_func.exists_forall_le (simple_func.map (λ x, ∥x∥) f)

lemma mem_ℒp_top_simple_func [measurable_space α] [normed_group E] [borel_space E]
  (f : simple_func α E) (μ : measure α) [finite_measure μ] :
  mem_ℒp f ∞ μ :=
begin
  obtain ⟨C, hfC⟩ := simple_func.exists_forall_norm_le f,
  exact mem_ℒp.of_bound (simple_func.ae_measurable f) C (eventually_of_forall hfC),
end

lemma mem_ℒp_simple_func (p : ℝ≥0∞) [measurable_space α] [normed_group E] [borel_space E]
  {μ : measure α} [finite_measure μ] (f : simple_func α E) :
  mem_ℒp f p μ :=
mem_ℒp.mem_ℒp_of_exponent_le (mem_ℒp_top_simple_func f μ) le_top

lemma mem_ℒ2_simple_func_L1 [measurable_space α] [normed_group E] [borel_space E]
  [second_countable_topology E] {μ : measure α} [finite_measure μ] (f : α →₁ₛ[μ] E) :
  mem_ℒp f 2 μ :=
(mem_ℒp_congr_ae (L1.simple_func.to_simple_func_eq_to_fun f).symm).mpr (mem_ℒp_simple_func 2 _)

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
  [second_countable_topology E] {μ : measure α} [finite_measure μ] :
  continuous (λ (f : α →₂[μ] E),
    (mem_ℒp.mem_ℒp_of_exponent_le (Lp.mem_ℒp f) ennreal.one_le_two).to_Lp f) :=
begin
  rw metric.continuous_iff,
  intros f ε hε_pos,
  simp_rw dist_def,
  by_cases hμ0 : μ = 0,
  { simp only [hμ0, exists_prop, forall_const, gt_iff_lt, ennreal.zero_to_real, snorm_measure_zero],
    exact ⟨ε, hε_pos, λ h, h⟩, },
  have h_univ_pow_pos : 0 < (μ set.univ ^ (1/(2 : ℝ))).to_real,
  { refine ennreal.to_real_pos_iff.mpr ⟨_, _⟩,
    { have hμ_univ_pos : 0 < μ set.univ,
      { refine lt_of_le_of_ne (zero_le _) (ne.symm _),
        rwa [ne.def, measure_theory.measure.measure_univ_eq_zero], },
      exact ennreal.rpow_pos hμ_univ_pos (measure_ne_top μ set.univ), },
    { refine ennreal.rpow_ne_top_of_nonneg _ (measure_ne_top μ set.univ),
      simp [zero_le_one], }, },
  refine ⟨ε / (μ set.univ ^ (1/(2 : ℝ))).to_real, div_pos hε_pos h_univ_pow_pos, λ g hfg, _⟩,
  rw lt_div_iff h_univ_pow_pos at hfg,
  refine lt_of_le_of_lt _ hfg,
  rw ← ennreal.to_real_mul,
  rw ennreal.to_real_le_to_real _ _,
  swap, { rw snorm_congr_ae (Lp.coe_fn_sub _ _).symm, exact Lp.snorm_ne_top _, },
  swap, { rw snorm_congr_ae (Lp.coe_fn_sub _ _).symm,
    refine ennreal.mul_ne_top _ _,
    exact Lp.snorm_ne_top _,
    refine ennreal.rpow_ne_top_of_nonneg _ _,
    simp [zero_le_one],
    exact measure_ne_top μ set.univ, },
  refine (le_of_eq _).trans ((snorm_le_snorm_mul_rpow_measure_univ (ennreal.one_le_two)
    ((Lp.ae_measurable g).sub (Lp.ae_measurable f))).trans (le_of_eq _)),
  { refine snorm_congr_ae _,
    exact eventually_eq.comp₂
      (mem_ℒp.coe_fn_to_Lp (mem_ℒp.mem_ℒp_of_exponent_le (Lp.mem_ℒp g) ennreal.one_le_two))
      (λ x y, x - y)
      (mem_ℒp.coe_fn_to_Lp (mem_ℒp.mem_ℒp_of_exponent_le (Lp.mem_ℒp f) ennreal.one_le_two)), },
  { congr,
    simp only [ennreal.one_to_real, ennreal.to_real_bit0, div_one],
    norm_num, },
end

def L2_to_L1_clm [measurable_space α] {μ : measure α} [finite_measure μ] :
  (α →₂[μ] E) →L[𝕜] (α →₁[μ] E) :=
{ to_fun := λ f, (mem_ℒp.mem_ℒp_of_exponent_le (Lp.mem_ℒp f) ennreal.one_le_two).to_Lp f,
  map_add' := L2_to_L1_add,
  map_smul' := L2_to_L1_smul,
  cont := continuous_L2_to_L1, }

include 𝕜
lemma L2_to_L1_coe_fn [measurable_space α] {μ : measure α} [finite_measure μ] (f : α →₂[μ] E) :
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

lemma simple_func.coe_finset_sum_apply {ι} [measurable_space α] [normed_group E]
  (f : ι → simple_func α E) (s : finset ι) (x : α) :
  (∑ i in s, f i) x = ∑ i in s, f i x :=
begin
  haveI : decidable_eq ι := classical.dec_eq ι,
  refine finset.induction _ _ s,
  { simp, },
  intros j s hjs h_sum,
  rw [finset.sum_insert hjs, simple_func.coe_add, pi.add_apply, h_sum, ← finset.sum_insert hjs],
end

lemma simple_func.coe_finset_sum {ι} [measurable_space α] [normed_group E]
  (f : ι → simple_func α E) (s : finset ι) :
  ⇑(∑ i in s, f i) = ∑ i in s, f i :=
begin
  ext1 x,
  simp_rw finset.sum_apply,
  exact simple_func.coe_finset_sum_apply f s x,
end

lemma L1.simple_func.coe_finset_sum {ι} [measurable_space α] {μ : measure α} [normed_group E]
  [borel_space E] [second_countable_topology E] (f : ι → (α →₁ₛ[μ] E)) (s : finset ι) :
  ⇑(∑ i in s, f i) =ᵐ[μ] ∑ i in s, f i :=
begin
  haveI : decidable_eq ι := classical.dec_eq ι,
  refine finset.induction _ _ s,
  { simp only [finset.sum_empty],
    rw ← L1.simple_func.coe_coe,
    rw L1.simple_func.coe_zero,
    exact Lp.coe_fn_zero _ _ _, },
  intros j s hjs h_sum,
  rw finset.sum_insert hjs,
  rw ← L1.simple_func.coe_coe,
  rw L1.simple_func.coe_add,
  refine (Lp.coe_fn_add _ _).trans _,
  rw L1.simple_func.coe_coe,
  rw L1.simple_func.coe_coe,
  have h : ⇑(f j) + ⇑∑ (x : ι) in s, f x =ᵐ[μ] ⇑(f j) + ∑ (x : ι) in s, ⇑(f x),
  { refine h_sum.mono (λ x hx, _),
    rw [pi.add_apply, pi.add_apply, hx], },
  refine h.trans _,
  rw ← finset.sum_insert hjs,
end

lemma simple_func_eq_sum_indicator [measurable_space α] [normed_group E] (f : simple_func α E) :
  f = ∑ y in f.range,
    indicator_simple_func (f ⁻¹' ({y} : set E)) (simple_func.measurable_set_fiber f y) y :=
begin
  ext,
  simp [indicator_simple_func],
  rw simple_func.coe_finset_sum_apply,
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
  [complete_space E] {μ : measure α} [finite_measure μ] {s : set α} {hs : measurable_set s}

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

lemma ae_all_finset {ι} [measurable_space α] {μ : measure α} (p : ι → α → Prop) (s : finset ι) :
  (∀ᵐ x ∂μ, ∀ i ∈ s, p i x) ↔ ∀ i ∈ s, ∀ᵐ x ∂μ, p i x :=
begin
  refine ⟨λ h i hi, h.mono (λ x hx, hx i hi), _⟩,
  haveI : decidable_eq ι := classical.dec_eq ι,
  refine finset.induction _ _ s,
  { simp only [eventually_true, finset.not_mem_empty, forall_false_left, implies_true_iff], },
  intros i s his hs h_insert,
  have h : ∀ (i : ι), i ∈ s → (∀ᵐ (x : α) ∂μ, p i x),
    from λ j hj, h_insert j (finset.mem_insert_of_mem hj),
  specialize hs h,
  specialize h_insert i (finset.mem_insert_self i s),
  refine h_insert.mp (hs.mono (λ x hx1 hx2, _)),
  intros j hj,
  rw finset.mem_insert at hj,
  cases hj with hji hjs,
  { rwa hji, },
  { exact hx1 j hjs, },
end

lemma eventually_eq.finset_sum {ι} [measurable_space α] [normed_group E] [borel_space E]
  [second_countable_topology E] {μ : measure α} (f g : ι → α → E) (s : finset ι)
  (hf : ∀ i ∈ s, f i =ᵐ[μ] g i) :
  ∑ i in s, f i =ᵐ[μ] ∑ i in s, g i :=
begin
  simp_rw eventually_eq at hf,
  rw ← ae_all_finset _ s at hf,
  refine hf.mono (λ x hx, _),
  rw [finset.sum_apply, finset.sum_apply],
  exact finset.sum_congr rfl hx,
end

lemma L1.simple_func.sum_to_simple_func_coe {ι} [measurable_space α] [normed_group E]
  [borel_space E] [second_countable_topology E] {μ : measure α} (f : ι → α →₁ₛ[μ] E) (s : finset ι) :
  L1.simple_func.to_simple_func (∑ i in s, f i)
    =ᵐ[μ] ∑ i in s, L1.simple_func.to_simple_func (f i) :=
begin
  refine (L1.simple_func.to_simple_func_eq_to_fun _).trans _,
  refine (L1.simple_func.coe_finset_sum _ s).trans _,
  refine eventually_eq.finset_sum _ _ s (λ i his, _),
  exact (L1.simple_func.to_simple_func_eq_to_fun _).symm,
end

lemma L1.simple_func.to_L1_coe_fn [measurable_space α] [normed_group E] [borel_space E]
  [second_countable_topology E] {μ : measure α} (f : simple_func α E) (hf : integrable f μ) :
  L1.simple_func.to_L1 f hf =ᵐ[μ] f :=
by { rw [←L1.simple_func.coe_coe, L1.simple_func.to_L1_eq_to_L1], exact integrable.coe_fn_to_L1 _, }

lemma L1.simple_func_eq_sum_indicator_L1s [measurable_space α] [normed_group E] [borel_space E]
  [second_countable_topology E] [complete_space E] {μ : measure α} [finite_measure μ]
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
  refine eventually_eq.trans _ (L1.simple_func.sum_to_simple_func_coe _ _).symm,
  have h_sum_eq : ∑ y in (L1.simple_func.to_simple_func f).range, (L1.simple_func.to_simple_func
    (indicator_L1s (L1.simple_func.measurable f (measurable_set_singleton y))
    (measure_lt_top μ _) y))
    =ᵐ[μ] ∑ y in (L1.simple_func.to_simple_func f).range, indicator_simple_func _
      (L1.simple_func.measurable f (measurable_set_singleton y)) y,
  { refine eventually_eq.finset_sum _ _ (L1.simple_func.to_simple_func f).range (λ i hi_mem, _),
    exact (to_simple_func_indicator_L1s), },
  refine eventually_eq.trans _ h_sum_eq.symm,
  nth_rewrite 0 ← L1.simple_func.to_L1_to_simple_func f,
  refine (L1.simple_func.to_L1_coe_fn _ _).trans _,
  have h_to_sum := simple_func_eq_sum_indicator (L1.simple_func.to_simple_func f),
  refine eventually_of_forall (λ x, _),
  apply_fun (λ f : simple_func α E, f.to_fun x) at h_to_sum,
  convert h_to_sum,
  rw ← simple_func.coe_finset_sum,
  refl,
end

lemma simple_func.integrable [measurable_space α] [normed_group E] [borel_space E]
  [second_countable_topology E] {μ : measure α} [finite_measure μ] (f : simple_func α E) :
  integrable f μ :=
mem_ℒp_one_iff_integrable.mp (mem_ℒp_simple_func 1 f)

def L1.simple_func.map [measurable_space α] [normed_group E] [borel_space E]
  [second_countable_topology E]
  {μ : measure α} [finite_measure μ] (g : E → F) (f : α →₁ₛ[μ] E) :
  (α →₁ₛ[μ] F) :=
L1.simple_func.to_L1 ((L1.simple_func.to_simple_func f).map g) (simple_func.integrable _)

@[ext] lemma L1.simple_func.ext [measurable_space α] [normed_group E] [borel_space E]
  [second_countable_topology E]
  {μ : measure α} [finite_measure μ] (f g : α →₁ₛ[μ] E) :
  ⇑f =ᵐ[μ] g → f = g :=
by { intro h, ext1, ext1, rwa [L1.simple_func.coe_coe, L1.simple_func.coe_coe], }

lemma L1.simple_func.map_coe [measurable_space α] [normed_group E] [borel_space E]
  [second_countable_topology E]
  {μ : measure α} [finite_measure μ] (g : E → F) (f : α →₁ₛ[μ] E) :
  ⇑(L1.simple_func.map g f) =ᵐ[μ] g ∘ f :=
begin
  rw L1.simple_func.map,
  refine (L1.simple_func.to_L1_coe_fn _ _).trans _,
  rw simple_func.coe_map,
  exact eventually_eq.fun_comp (L1.simple_func.to_simple_func_eq_to_fun _) g,
end

lemma continuous_linear_map.to_linear_map_apply {R : Type*} [semiring R] {M₁ M₂ : Type*}
  [topological_space M₁] [add_comm_monoid M₁] [topological_space M₂] [add_comm_monoid M₂]
  [semimodule R M₁] [semimodule R M₂] (f : M₁ →L[R] M₂) (x : M₁) :
  f.to_linear_map x = f x :=
rfl

section condexp_L1s

variables {m m0 : measurable_space α} (hm : m ≤ m0) [complete_space E] {μ : measure α}
  [finite_measure μ]

variables (𝕜)
def condexp_L1s_lm : (α →₁ₛ[μ] E) →ₗ[𝕜] (α →₁[μ] E) :=
L2_to_L1_clm.to_linear_map.comp ((Lp_sub hm 𝕜 E 2 μ).subtype.comp
  ((condexp_L2_clm 𝕜 hm).to_linear_map.comp L1s_to_L2_lm))

lemma condexp_L1s_lm_neg (f : α →₁ₛ[μ] E) : condexp_L1s_lm 𝕜 hm (-f) = -condexp_L1s_lm 𝕜 hm f :=
linear_map.map_neg (condexp_L1s_lm 𝕜 hm) f
variables {𝕜}

lemma condexp_L1s_ae_eq_condexp_L2 (f : α →₁ₛ[μ] E) :
  condexp_L1s_lm 𝕜 hm f =ᵐ[μ] condexp_L2_clm 𝕜 hm (L1s_to_L2_lm f) :=
(L2_to_L1_coe_fn _).trans (by refl)

lemma is_condexp_condexp_L2_L1s_to_L2 (f : α →₁ₛ[μ] E) :
  is_condexp m (condexp_L2_clm 𝕜 hm (L1s_to_L2_lm f) : α → E) f μ :=
is_condexp_congr_ae_right' hm (L1s_to_L2_coe_fn f) (is_condexp_condexp_L2 hm _)

variables (𝕜)
lemma is_condexp_condexp_L1s (f : α →₁ₛ[μ] E) :
  is_condexp m ((condexp_L1s_lm 𝕜 hm f) : α → E) f μ :=
is_condexp_congr_ae' hm (condexp_L1s_ae_eq_condexp_L2 hm _).symm
  (is_condexp_condexp_L2_L1s_to_L2 hm f)

lemma integral_condexp_L1s (f : α →₁ₛ[μ] E) {s : set α} (hs : @measurable_set α m s) :
  ∫ a in s, (condexp_L1s_lm 𝕜 hm f) a ∂μ = ∫ a in s, f a ∂μ :=
(is_condexp_condexp_L1s 𝕜 hm f).2.2 s hs
variables {𝕜}

end condexp_L1s

lemma condexp_L1s_const_le {m m0 : measurable_space α} (hm : m ≤ m0)
  {μ : measure α} [finite_measure μ] (f : α →₁ₛ[μ] ℝ) (c : ℝ) (hf : ∀ᵐ x ∂μ, c ≤ f x) :
  ∀ᵐ x ∂μ, c ≤ condexp_L1s_lm ℝ hm f x :=
begin
  refine (ae_const_le_iff_forall_lt_measure_zero _ c).mpr (λ b hb, _),
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
      exact mul_lt_mul_of_pos_right hb (ennreal.to_real_nonneg.lt_of_ne h_ne_zero.symm), },
    have h_const_le : ∫ x in s, f' x ∂μ ≤ ∫ x in s, b ∂μ,
    { refine set_integral_mono_ae_restrict h_int'.integrable_on
        (integrable_on_const.mpr (or.inr (measure_lt_top _ _))) _,
      rw [eventually_le, ae_restrict_iff hs],
      exact eventually_of_forall hf's, },
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
  refine hff'.mono (λ x hx, _),
  rw [← @set.mem_def _ x {x : α | ((condexp_L1s_lm ℝ hm) f) x ≤ b}, ← @set.mem_def _ x s],
  simp only [eq_iff_iff, set.mem_set_of_eq],
  rw hx,
end

lemma condexp_L1s_le_const {m m0 : measurable_space α} (hm : m ≤ m0)
  {μ : measure α} [finite_measure μ] (f : α →₁ₛ[μ] ℝ) (c : ℝ) (hf : ∀ᵐ x ∂μ, f x ≤ c) :
  ∀ᵐ x ∂μ, condexp_L1s_lm ℝ hm f x ≤ c :=
begin
  have h_neg := condexp_L1s_const_le hm (-f) (-c) _,
  swap,
  { rw [← L1.simple_func.coe_coe, L1.simple_func.coe_neg],
    refine (Lp.coe_fn_neg (f : Lp ℝ 1 μ)).mp (hf.mono (λ x hx hfx, _)),
    rw [hfx, pi.neg_apply],
    exact neg_le_neg hx, },
  rw linear_map.map_neg at h_neg,
  refine (Lp.coe_fn_neg ((condexp_L1s_lm ℝ hm) f)).mp (h_neg.mono (λ x hx hx_neg, _)),
  rw [hx_neg, pi.neg_apply] at hx,
  exact le_of_neg_le_neg hx,
end

lemma condexp_L1s_nonneg {m m0 : measurable_space α} (hm : m ≤ m0)
  {μ : measure α} [finite_measure μ] (f : α →₁ₛ[μ] ℝ) (hf : 0 ≤ᵐ[μ] f) :
  0 ≤ᵐ[μ] condexp_L1s_lm ℝ hm f :=
condexp_L1s_const_le hm f 0 hf

lemma condexp_L1s_mono {m m0 : measurable_space α} (hm : m ≤ m0)
  {μ : measure α} [finite_measure μ] (f g : α →₁ₛ[μ] ℝ) (hfg : f ≤ᵐ[μ] g) :
  condexp_L1s_lm ℝ hm f ≤ᵐ[μ] condexp_L1s_lm ℝ hm g :=
begin
  suffices h_sub : condexp_L1s_lm ℝ hm (f-g) ≤ᵐ[μ] 0,
  { rw linear_map.map_sub at h_sub,
    refine (Lp.coe_fn_sub (condexp_L1s_lm ℝ hm f) (condexp_L1s_lm ℝ hm g)).mp
      (h_sub.mono (λ x hx h_sub_fg, _)),
    rw [h_sub_fg, pi.zero_apply] at hx,
    rwa ← sub_nonpos, },
  have h_sub_fg : ⇑(f - g) ≤ᵐ[μ] 0,
  { rw ← L1.simple_func.coe_coe,
    rw L1.simple_func.coe_sub,
    refine (Lp.coe_fn_sub (f : α→₁[μ] ℝ) (g: α→₁[μ] ℝ)).mp (hfg.mono (λ x hx h_sub_fg, _)),
    rwa [h_sub_fg, L1.simple_func.coe_coe, L1.simple_func.coe_coe, pi.sub_apply, pi.zero_apply,
      sub_nonpos], },
  exact condexp_L1s_le_const hm (f-g) 0 h_sub_fg,
end

lemma condexp_L1s_R_le_abs {m m0 : measurable_space α} (hm : m ≤ m0) {μ : measure α}
  [finite_measure μ] (f : α →₁ₛ[μ] ℝ) :
  condexp_L1s_lm ℝ hm f ≤ᵐ[μ] condexp_L1s_lm ℝ hm (L1.simple_func.map abs f) :=
begin
  refine condexp_L1s_mono hm f (L1.simple_func.map abs f) _,
  refine (L1.simple_func.map_coe abs f).mono (λ x hx, _),
  rw hx,
  exact le_abs_self _,
end

lemma L1.simple_func.coe_fn_neg [measurable_space α] [normed_group E] [borel_space E]
  [second_countable_topology E] {μ : measure α} (f : α →₁ₛ[μ] E) :
  ⇑(-f) =ᵐ[μ] -f :=
begin
  rw [← L1.simple_func.coe_coe, ← L1.simple_func.coe_coe, L1.simple_func.coe_neg],
  exact Lp.coe_fn_neg _,
end

lemma condexp_L1s_R_jensen_norm {m m0 : measurable_space α} (hm : m ≤ m0) {μ : measure α}
  [finite_measure μ] (f : α →₁ₛ[μ] ℝ) :
  ∀ᵐ x ∂μ, ∥condexp_L1s_lm ℝ hm f x∥ ≤ condexp_L1s_lm ℝ hm (L1.simple_func.map (λ x, ∥x∥) f) x :=
begin
  simp_rw real.norm_eq_abs,
  simp_rw abs_le,
  refine eventually.and _ _,
  { have h := condexp_L1s_R_le_abs hm (-f),
    have h_abs_neg : L1.simple_func.map abs (-f) = L1.simple_func.map abs f,
    { ext1,
      refine (L1.simple_func.coe_fn_neg f).mp ((L1.simple_func.map_coe abs (-f)).mp
        ((L1.simple_func.map_coe abs f).mono (λ x hx1 hx2 hx3, _))),
      rw [hx1, hx2, function.comp_app, hx3, pi.neg_apply, function.comp_app, abs_neg], },
    simp_rw h_abs_neg at h,
    simp_rw neg_le,
    rw condexp_L1s_lm_neg ℝ hm f at h,
    refine h.mp ((Lp.coe_fn_neg (condexp_L1s_lm ℝ hm f)).mono (λ x hx hxh, _)),
    rwa [← pi.neg_apply, ← hx], },
  { exact condexp_L1s_R_le_abs hm f, },
end

--lemma condexp_L1s_R_jensen {m m0 : measurable_space α} (hm : m ≤ m0) {μ : measure α}
--  [finite_measure μ] (f : α →₁ₛ[μ] ℝ) (F : ℝ → ℝ) (hF : convex_on (set.univ : set ℝ) F) :
--  ∀ᵐ x ∂μ, F (condexp_L1s_lm ℝ hm f x) ≤ condexp_L1s_lm ℝ hm (L1.simple_func.map F f) x :=
--begin
--  sorry
--end

lemma norm_condexp_L1s_le_R {m m0 : measurable_space α} (hm : m ≤ m0)
  {μ : measure α} [finite_measure μ] (f : α →₁ₛ[μ] ℝ) :
  ∥condexp_L1s_lm ℝ hm f∥ ≤ ∥f∥ :=
begin
  simp_rw [L1.simple_func.norm_eq, norm_def],
  rw ennreal.to_real_le_to_real (Lp.snorm_ne_top _) (Lp.snorm_ne_top _),
  simp_rw [snorm_eq_snorm' ennreal.zero_lt_one.ne.symm ennreal.coe_ne_top, ennreal.one_to_real,
    snorm', div_one, ennreal.rpow_one],
  let F := λ x : ℝ, ∥x∥,
  have h_left : ∫⁻ a, (nnnorm (((condexp_L1s_lm ℝ hm) f) a) : ℝ≥0∞) ∂μ
      = ∫⁻ a, ennreal.of_real (∥((condexp_L1s_lm ℝ hm) f) a∥) ∂μ,
    by { congr, ext1 x, rw ← of_real_norm_eq_coe_nnnorm, },
  have h_right : ∫⁻ a, (nnnorm ((f : Lp ℝ 1 μ) a) : ℝ≥0∞) ∂μ
      = ∫⁻ a, ennreal.of_real (∥(f : Lp ℝ 1 μ) a∥) ∂μ,
    by { congr, ext1 x, rw ← of_real_norm_eq_coe_nnnorm, },
  rw [h_left, h_right],
  have h_le : ∫⁻ a, ennreal.of_real (∥((condexp_L1s_lm ℝ hm) f) a∥) ∂μ
    ≤ ∫⁻ a, ennreal.of_real (condexp_L1s_lm ℝ hm (L1.simple_func.map F f) a) ∂μ,
  { refine lintegral_mono_ae ((condexp_L1s_R_jensen_norm hm f).mono (λ x hx, _)),
    rwa ennreal.of_real_le_of_real_iff ((norm_nonneg _).trans hx), },
  refine h_le.trans _,
  have h_integral_eq := integral_condexp_L1s ℝ hm (L1.simple_func.map F f)
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
  { sorry, },
end

lemma norm_indicator_L1s [normed_group E] [borel_space E] [second_countable_topology E]
  [complete_space E] {m m0 : measurable_space α} (hm : m ≤ m0) {μ : measure α}
  [finite_measure μ] {s : set α} {hs : measurable_set s} {hμs : μ s < ∞} {c : E} :
  ∥indicator_L1s hs hμs c∥ = ∥c∥ * (μ s).to_real :=
by rw [L1.simple_func.norm_eq, indicator_L1s_coe,
  norm_indicator_Lp ennreal.zero_lt_one ennreal.coe_ne_top, ennreal.one_to_real, div_one,
  real.rpow_one]

lemma norm_condexp_L1s_indicator_L1s_R_le {m m0 : measurable_space α} (hm : m ≤ m0) {μ : measure α}
  [finite_measure μ] {s : set α} (hs : measurable_set s) (hμs : μ s < ∞) (c : ℝ) :
  ∥condexp_L1s_lm ℝ hm (indicator_L1s hs hμs c)∥ ≤ ∥c∥ * (μ s).to_real :=
(norm_condexp_L1s_le_R hm _).trans (norm_indicator_L1s hm).le

lemma indicator_const_eq_smul {α E} [add_comm_monoid E] [semimodule ℝ E] (s : set α) (c : E) :
  s.indicator (λ (_x : α), c) = λ (x : α), s.indicator (λ (_x : α), (1 : ℝ)) x • c :=
by { ext1 x, by_cases h_mem : x ∈ s; simp [h_mem], }

variables (𝕜)
include 𝕜
lemma indicator_L1s_eq_smul [measurable_space α] {μ : measure α} [finite_measure μ]
  [complete_space E] {s : set α} (hs : measurable_set s) (hμs : μ s < ∞) (c : E) :
  indicator_L1s hs hμs c =ᵐ[μ] λ x, ((@indicator_L1s α ℝ _ _ _ _ _ _ μ _ s hs hμs 1) x) • c :=
begin
  have h : (λ (x : α), (indicator_L1s hs hμs (1:ℝ)) x • c) =ᵐ[μ] λ x,
    (s.indicator (λ _, (1:ℝ)) x) • c,
  { change (λ x, x • c) ∘ (indicator_L1s hs hμs (1:ℝ))
      =ᵐ[μ] λ (x : α), s.indicator (λ x, (1:ℝ)) x • c,
    exact eventually_eq.fun_comp indicator_L1s_coe_fn (λ x, x • c), },
  refine (indicator_L1s_coe_fn).trans (eventually_eq.trans _ h.symm),
  exact eventually_of_forall (λ x, by rw indicator_const_eq_smul s c),
end
omit 𝕜
variables {𝕜}

lemma indicator_L1s_coe_ae_le [measurable_space α] {μ : measure α} [finite_measure μ]
  {s : set α} (hs : measurable_set s) (hμs : μ s < ∞) (c : ℝ) :
  ∀ᵐ x ∂μ, abs (indicator_L1s hs hμs c x) ≤ abs c :=
begin
  refine (@indicator_L1s_coe_fn α ℝ _ _ _ _ _ _ μ _ s hs hμs c).mono (λ x hx, _),
  rw hx,
  by_cases hx_mem : x ∈ s; simp [hx_mem, abs_nonneg c],
end

lemma condexp_L1s_indicator_L1s_eq {m m0 : measurable_space α} (hm : m ≤ m0) [complete_space E]
  {μ : measure α} [finite_measure μ] {s : set α} (hs : measurable_set s) (hμs : μ s < ∞)
  (c : E) :
  condexp_L1s_lm 𝕜 hm (indicator_L1s hs hμs c) =ᵐ[μ]
    λ x, (condexp_L1s_lm ℝ hm (@indicator_L1s α ℝ _ _ _ _ _ _ μ _ s hs hμs 1) x) • c :=
begin
  refine is_condexp_unique 𝕜 hm (indicator_L1s hs hμs c) _ _,
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
      simp_rw [real.norm_eq_abs, abs_le],
      refine eventually.and _ _,
      { refine condexp_L1s_const_le hm _ (-1 : ℝ) _,
        refine (indicator_L1s_coe_ae_le hs hμs (1 : ℝ)).mono (λ x hx, _),
        exact neg_le_of_abs_le (hx.trans (le_of_eq abs_one)), },
      { refine condexp_L1s_le_const hm _ (1 : ℝ) _,
        refine (indicator_L1s_coe_ae_le hs hμs (1 : ℝ)).mono (λ x hx, _),
        exact le_of_abs_le (hx.trans (le_of_eq abs_one)), }, }, },
  { refine ⟨λ x, (f₁' x) • c, _, _⟩,
    { exact @measurable.smul _ m _ _ _ _ _ _ f₁' _ h_meas₁ (@measurable_const _ _ _ m c), },
    { exact eventually_eq.fun_comp hff'₁ (λ x, x • c), }, },
  { intros t ht,
    have h_smul : ∫ a in t, (indicator_L1s hs hμs c) a ∂μ
        = ∫ a in t, ((indicator_L1s hs hμs (1 : ℝ)) a) • c ∂μ,
      from set_integral_congr_ae (hm t ht)  ((indicator_L1s_eq_smul 𝕜 _ _ c).mono (λ x hx hxs, hx)),
    refine eq.trans _ h_smul.symm,
    rw [integral_smul_const, integral_smul_const, h_int_eq₁ t ht], },
end

lemma norm_condexp_L1s_indicator_L1s {m m0 : measurable_space α} (hm : m ≤ m0) [complete_space E]
  {μ : measure α} [finite_measure μ] {s : set α} (hs : measurable_set s) (hμs : μ s < ∞)
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
  {μ : measure α} [finite_measure μ] (f : α →₁ₛ[μ] E) :
  ∥condexp_L1s_lm 𝕜 hm f∥ ≤ ∥f∥ :=
begin
  rw L1.simple_func.norm_eq_integral,
  rw simple_func.map_integral _ _ (L1.simple_func.integrable _),
  swap, { exact norm_zero, },
  nth_rewrite 0 L1.simple_func_eq_sum_indicator_L1s f,
  rw linear_map.map_sum,
  refine (norm_sum_le _ _).trans _,
  refine finset.sum_le_sum (λ x hxf, (norm_condexp_L1s_indicator_L1s hm _ _ x).trans _),
  rw [smul_eq_mul, mul_comm, norm_indicator_L1s hm],
end

section continuous_set_integral

lemma snorm'_mono_measure {q : ℝ} [normed_group E] [measurable_space α] {μ ν : measure α}
  {f : α → E} (hμν : ν ≤ μ) (hq : 0 ≤ q) :
  snorm' f q ν ≤ snorm' f q μ :=
begin
  simp_rw snorm',
  suffices h_integral_mono : (∫⁻ a, (nnnorm (f a) : ℝ≥0∞) ^ q ∂ν) ≤ ∫⁻ a, (nnnorm (f a)) ^ q ∂μ,
    from ennreal.rpow_le_rpow h_integral_mono (by simp [hq]),
  exact lintegral_mono' hμν le_rfl,
end

lemma limsup_le_limsup_of_le {α β} [conditionally_complete_lattice β] {f g : filter α} (h : f ≤ g)
  {u : α → β} (hf : f.is_cobounded_under (≤) u . is_bounded_default)
  (hg : g.is_bounded_under (≤) u . is_bounded_default) :
  f.limsup u ≤ g.limsup u :=
Limsup_le_Limsup_of_le (map_mono h) hf hg

lemma ess_sup_mono_measure [measurable_space α] {μ ν : measure α} {f : α → ℝ≥0∞} (hμν : ν ≪ μ) :
  ess_sup f ν ≤ ess_sup f μ :=
begin
  refine limsup_le_limsup_of_le (measure.ae_le_iff_absolutely_continuous.mpr hμν) _ _,
  all_goals {is_bounded_default, },
end

lemma snorm_ess_sup_mono_measure [normed_group E]
  [measurable_space α] {μ ν : measure α} {f : α → E} (hμν : ν ≪ μ) :
  snorm_ess_sup f ν ≤ snorm_ess_sup f μ :=
by { simp_rw snorm_ess_sup, exact ess_sup_mono_measure hμν, }

lemma snorm_mono_measure [normed_group E]
  [measurable_space α] {μ ν : measure α} {f : α → E} (hμν : ν ≤ μ) :
  snorm f p ν ≤ snorm f p μ :=
begin
  by_cases hp0 : p = 0,
  { simp [hp0], },
  by_cases hp_top : p = ∞,
  { simp [hp_top, snorm_ess_sup_mono_measure (measure.absolutely_continuous_of_le hμν)], },
  simp_rw snorm_eq_snorm' hp0 hp_top,
  exact snorm'_mono_measure hμν ennreal.to_real_nonneg,
end

lemma mem_ℒp.mono_measure [normed_group E]
  [measurable_space α] {μ ν : measure α} {f : α → E} (hμν : ν ≤ μ) (hf : mem_ℒp f p μ) :
  mem_ℒp f p ν :=
⟨hf.1.mono_measure hμν, (snorm_mono_measure hμν).trans_lt hf.2⟩

lemma mem_ℒp.restrict [normed_group E]
  [measurable_space α] {μ : measure α} (s : set α) {f : α → E} (hf : mem_ℒp f p μ) :
  mem_ℒp f p (μ.restrict s) :=
hf.mono_measure measure.restrict_le_self

variables {α} [measurable_space α] {μ : measure α}

lemma Lp_to_Lp_restrict_add (p : ℝ≥0∞) [normed_group E] [borel_space E]
  [second_countable_topology E] (f g : Lp E p μ) (s : set α) :
  mem_ℒp.to_Lp ⇑(f+g) ((Lp.mem_ℒp (f+g)).restrict s)
    = mem_ℒp.to_Lp f ((Lp.mem_ℒp f).restrict s) + mem_ℒp.to_Lp g ((Lp.mem_ℒp g).restrict s) :=
begin
  ext1,
  refine (ae_restrict_of_ae (Lp.coe_fn_add f g)).mp _,
  refine (Lp.coe_fn_add (mem_ℒp.to_Lp f ((Lp.mem_ℒp f).restrict s))
    (mem_ℒp.to_Lp g ((Lp.mem_ℒp g).restrict s))).mp _,
  refine (mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp f).restrict s)).mp _,
  refine (mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp g).restrict s)).mp _,
  refine (mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp (f+g)).restrict s)).mono (λ x hx1 hx2 hx3 hx4 hx5, _),
  rw [hx4, hx1, pi.add_apply, hx2, hx3, hx5, pi.add_apply],
end

variables (𝕜)
lemma Lp_to_Lp_restrict_smul {E} [measurable_space E] [normed_group E] [borel_space E]
  [second_countable_topology E] [normed_space 𝕜 E] (p : ℝ≥0∞) (c : 𝕜) (f : Lp E p μ) (s : set α) :
  mem_ℒp.to_Lp ⇑(c • f) ((Lp.mem_ℒp (c • f)).restrict s)
    = c • (mem_ℒp.to_Lp f ((Lp.mem_ℒp f).restrict s)) :=
begin
  ext1,
  refine (ae_restrict_of_ae (Lp.coe_fn_smul c f)).mp _,
  refine (mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp f).restrict s)).mp _,
  refine (mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp (c • f)).restrict s)).mp _,
  refine (Lp.coe_fn_smul c (mem_ℒp.to_Lp f ((Lp.mem_ℒp f).restrict s))).mono
    (λ x hx1 hx2 hx3 hx4, _),
  rw [hx2, hx1, pi.smul_apply, hx3, hx4, pi.smul_apply],
end
variables {𝕜}

def Lp_to_Lp_restrict_lm (α E 𝕜) [is_R_or_C 𝕜] [measurable_space α] (μ : measure α)
  [measurable_space E] [normed_group E] [normed_space 𝕜 E] [borel_space E]
  [second_countable_topology E]
  [measurable_space 𝕜] [borel_space 𝕜] (p : ℝ≥0∞)  (s : set α) :
  (Lp E p μ) →ₗ (Lp E p (μ.restrict s)) :=
{ to_fun := λ f, mem_ℒp.to_Lp f ((Lp.mem_ℒp f).restrict s),
  map_add' := λ f g, Lp_to_Lp_restrict_add p f g s,
  map_smul' := λ c f, Lp_to_Lp_restrict_smul 𝕜 p c f s, }

lemma norm_Lp_to_Lp_restrict_le (α E) [measurable_space α] {μ : measure α}
  [measurable_space E] [normed_group E] [borel_space E]
  [second_countable_topology E] (p : ℝ≥0∞)  (s : set α) (f : Lp E p μ) :
  ∥mem_ℒp.to_Lp f ((Lp.mem_ℒp f).restrict s)∥ ≤ ∥f∥ :=
begin
  rw [norm_def, norm_def, ennreal.to_real_le_to_real (snorm_ne_top _) (snorm_ne_top _)],
  refine (le_of_eq _).trans (snorm_mono_measure measure.restrict_le_self),
  { exact s, },
  exact snorm_congr_ae (mem_ℒp.coe_fn_to_Lp _),
end

def Lp_to_Lp_restrict_clm (α E 𝕜) [is_R_or_C 𝕜] [measurable_space α] (μ : measure α)
  [measurable_space E] [normed_group E] [normed_space 𝕜 E] [borel_space E]
  [second_countable_topology E] [measurable_space 𝕜] [borel_space 𝕜]
  (p : ℝ≥0∞) [hp : fact(1 ≤ p)] (s : set α) :
  @continuous_linear_map 𝕜 _ (Lp E p μ) _ _ (Lp E p (μ.restrict s)) _ _ _ _ :=
@linear_map.mk_continuous 𝕜 (Lp E p μ) (Lp E p (μ.restrict s)) _ _ _ _ _
  (Lp_to_Lp_restrict_lm α E 𝕜 μ p s) 1
  (by { intro f, rw one_mul, exact norm_Lp_to_Lp_restrict_le α E p s f, })

@[continuity]
lemma continuous_Lp_to_Lp_restrict (α E 𝕜) [is_R_or_C 𝕜] [measurable_space α] {μ : measure α}
  [measurable_space E] [normed_group E] [normed_space 𝕜 E] [borel_space E]
  [second_countable_topology E] [measurable_space 𝕜] [borel_space 𝕜]
  (p : ℝ≥0∞) [hp : fact(1 ≤ p)] (s : set α) :
  continuous (Lp_to_Lp_restrict_clm α E 𝕜 μ p s) :=
continuous_linear_map.continuous _

lemma Lp_to_Lp_restrict_clm_coe_fn {α E} (𝕜) [is_R_or_C 𝕜] [measurable_space α] {μ : measure α}
  [measurable_space E] [normed_group E] [normed_space 𝕜 E] [borel_space E]
  [second_countable_topology E] [measurable_space 𝕜] [borel_space 𝕜]
  {p : ℝ≥0∞} [hp : fact(1 ≤ p)] (s : set α) (f : Lp E p μ) :
  Lp_to_Lp_restrict_clm α E 𝕜 μ p s f =ᵐ[μ.restrict s] f :=
mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp f).restrict s)

@[continuity]
lemma continuous_set_integral {E} [measurable_space E] [normed_group E] [borel_space E]
  [second_countable_topology E] [normed_space ℝ E] [complete_space E] {s : set α}
  (hs : measurable_set s) [finite_measure μ] :
  continuous (λ f : α →₁[μ] E, ∫ x in s, f x ∂μ) :=
begin
  haveI : fact((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩,
  have h_comp : (λ f : α →₁[μ] E, ∫ x in s, f x ∂μ)
    = (integral (μ.restrict s)) ∘ (λ f, Lp_to_Lp_restrict_clm α E ℝ μ 1 s f),
  { ext1 f,
    rw [function.comp_apply, integral_congr_ae (Lp_to_Lp_restrict_clm_coe_fn ℝ s f)], },
  rw h_comp,
  exact continuous_integral.comp (continuous_Lp_to_Lp_restrict α E ℝ 1 s),
end

end continuous_set_integral

section condexp_def
variables {m m0 : measurable_space α} (hm : m ≤ m0) [complete_space E]
  {μ : measure α} [finite_measure μ]

lemma continuous_condexp_L1s : continuous (@condexp_L1s_lm α E 𝕜 _ _ _ _ _ _ _ _ _ m m0 hm _ μ _) :=
linear_map.continuous_of_bound _ 1 (λ f, (norm_condexp_L1s_le hm f).trans (one_mul _).symm.le)

variables (𝕜)
/-- Conditional expectation as a continuous linear map from the simple functions in L1 to L1. -/
def condexp_L1s_clm : (α →₁ₛ[μ] E) →L[𝕜] (α →₁[μ] E) :=
{ to_linear_map := condexp_L1s_lm 𝕜 hm,
  cont := continuous_condexp_L1s hm, }

/-- Conditional expectation as a continuous linear map from L1 to L1. -/
def condexp_L1 : (α →₁[μ] E) →L[𝕜] (α →₁[μ] E) :=
@continuous_linear_map.extend 𝕜 (α →₁ₛ[μ] E) (α →₁[μ] E) (α →₁[μ] E) _ _ _ _ _ _ _
  (condexp_L1s_clm 𝕜 hm) _ (L1.simple_func.coe_to_L1 α E 𝕜) L1.simple_func.dense_range
  L1.simple_func.uniform_inducing

lemma condexp_L1_eq_condexp_L1s (f : α →₁ₛ[μ] E) :
  condexp_L1 𝕜 hm (f : α →₁[μ] E) = condexp_L1s_clm 𝕜 hm f :=
begin
  refine uniformly_extend_of_ind L1.simple_func.uniform_inducing L1.simple_func.dense_range _ _,
  exact @continuous_linear_map.uniform_continuous 𝕜 (α →₁ₛ[μ] E) (α →₁[μ] E) _ _ _ _ _
    (@condexp_L1s_clm α E 𝕜 _ _ _ _ _ _ _ _ _ _ _ hm _ μ _),
end

lemma integrable_condexp_L1 (f : α →₁[μ] E) : integrable (condexp_L1 𝕜 hm f) μ :=
L1.integrable_coe_fn _

lemma ae_measurable_condexp_L1 (f : α →₁[μ] E) :
  ∃ (f' : α → E), @measurable _ _ m _ f' ∧ (condexp_L1 𝕜 hm f) =ᵐ[μ] f' :=
begin
  refine @is_closed_property _ (α →₁[μ] E) _ _ _ L1.simple_func.dense_range _ _ f,
  { change is_closed ((condexp_L1 𝕜 hm) ⁻¹'
      {x : ↥(Lp E 1 μ) | ∃ f', @measurable _ _ m _ f' ∧ x =ᵐ[μ] f'}),
    refine is_closed.preimage (continuous_linear_map.continuous _) _,
    rw ← is_seq_closed_iff_is_closed,
    refine is_seq_closed_of_def (λ F f F_mem F_tendsto_f, _),
    rw set.mem_set_of_eq,
    change ∀ n, ∃ f', @measurable _ _ m _ f' ∧ ⇑(F n) =ᵐ[μ] f' at F_mem,
    let G := λ n, (F_mem n).some,
    have hG_meas : ∀ n, @measurable _ _ m _ (G n), from λ n, (F_mem n).some_spec.1,
    have hF_eq_G : ∀ n, F n =ᵐ[μ] G n, from λ n, (F_mem n).some_spec.2,
    haveI : fact (1 ≤ (1 : ℝ≥0∞)) := ⟨le_rfl⟩,
    obtain ⟨f_lim, h_meas, h⟩ := ae_eq_measurable_of_tendsto hm F G f hF_eq_G hG_meas F_tendsto_f,
    exact ⟨f_lim, h_meas, h⟩, },
  { intro fs,
    rw condexp_L1_eq_condexp_L1s,
    obtain ⟨f', hf'_meas, hf'⟩ := (is_condexp_condexp_L1s 𝕜 hm fs).2.1,
    refine ⟨f', hf'_meas, _⟩,
    refine eventually_eq.trans (eventually_of_forall (λ x, _)) hf',
    refl, },
end

lemma integral_eq_condexp_L1 (f : α →₁[μ] E) (s : set α) (hs : @measurable_set α m s) :
  ∫ a in s, (condexp_L1 𝕜 hm f) a ∂μ = ∫ a in s, f a ∂μ :=
begin
  refine @is_closed_property _ (α →₁[μ] E) _ _ _ L1.simple_func.dense_range _ _ f,
  { have hs' : measurable_set s, from hm s hs,
    refine is_closed_eq _ _,
    { change continuous ((λ (x : ↥(Lp E 1 μ)), ∫ (a : α) in s, x a ∂μ) ∘ (condexp_L1 𝕜 hm)),
      continuity, },
    { continuity, }, },
  { intro fs,
    rw condexp_L1_eq_condexp_L1s,
    exact (is_condexp_condexp_L1s 𝕜 hm fs).2.2 s hs, },
end

lemma is_condexp_condexp_L1 (f : α →₁[μ] E) : is_condexp m (condexp_L1 𝕜 hm f) f μ :=
⟨integrable_condexp_L1 𝕜 hm f, ae_measurable_condexp_L1 𝕜 hm f, integral_eq_condexp_L1 𝕜 hm f⟩

include 𝕜 hm
/-- Conditional expectation of an integrable function. -/
def condexp (f : α → E) (hf : integrable f μ) : α → E :=
(is_condexp_condexp_L1 𝕜 hm (hf.to_L1 f)).2.1.some
omit 𝕜 hm

lemma measurable_condexp (f : α → E) (hf : integrable f μ) :
  @measurable _ _ m _ (condexp 𝕜 hm f hf) :=
(is_condexp_condexp_L1 𝕜 hm (hf.to_L1 f)).2.1.some_spec.1

lemma condexp_ae_eq_condexp_L1 (f : α → E) (hf : integrable f μ) :
  condexp 𝕜 hm f hf =ᵐ[μ] condexp_L1 𝕜 hm (hf.to_L1 f) :=
(is_condexp_condexp_L1 𝕜 hm (hf.to_L1 f)).2.1.some_spec.2.symm

lemma is_condexp_condexp {f : α → E} (hf : integrable f μ) :
  is_condexp m (condexp 𝕜 hm f hf) f μ :=
begin
  refine is_condexp_congr_ae_right' hm (integrable.coe_fn_to_L1 hf) _,
  refine is_condexp_congr_ae' hm (condexp_ae_eq_condexp_L1 𝕜 hm f hf).symm _,
  exact is_condexp_condexp_L1 𝕜 hm (hf.to_L1 f),
end
variables {𝕜}

lemma integrable_condexp (f : α → E) (hf : integrable f μ) : integrable (condexp 𝕜 hm f hf) μ :=
(is_condexp_condexp 𝕜 hm hf).1

lemma condexp_integral_eq {f : α → E} (hf : integrable f μ) {s : set α}
  (hs : @measurable_set α m s) :
  ∫ x in s, condexp 𝕜 hm f hf x ∂μ = ∫ x in s, f x ∂μ :=
(is_condexp_condexp 𝕜 hm hf).2.2 s hs

end condexp_def

end measure_theory
