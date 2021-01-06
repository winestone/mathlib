import measure_theory.set_integral
import measure_theory.pi
import analysis.normed_space.box_subadditive

open measure_theory set topological_space

section measure

variables {ι α : Type*} [decidable_eq ι] [measurable_space α]
  [linear_order α] [topological_space α] [order_closed_topology α] [opens_measurable_space α]

theorem box_additive_on_measure_pi_Ioc [encodable ι] (μ : measure (ι → α)) (s : set (ι → α)) :
  box_additive_on (λ l r, μ (pi univ (λ i, Ioc (l i) (r i)))) s :=
begin
  intros l u hsub m hm i,
  rw [← measure_union disjoint_pi_univ_Ioc_update_left_right,
    pi_univ_Ioc_update_union l u i (m i) ⟨hm.1 i, hm.2 i⟩];
    exact is_measurable.pi (countable_encodable _) (λ _ _, is_measurable_Ioc)
end

theorem box_additive_on_measure_Icc [fintype ι] (μ : ι → measure α) (s : set (ι → α))
  [∀ i, sigma_finite (μ i)] [∀ i, has_no_atoms (μ i)] :
  box_additive_on (λ l r : ι → α, (measure.pi μ) (Icc l r)) s :=
begin
  letI := encodable.fintype.encodable ι,
  refine (box_additive_on_measure_pi_Ioc _ s).congr (λ l u hle hsub, measure_congr _),
  exact measure.univ_pi_Ioc_ae_eq_Icc
end

end measure

variables {ι α β E : Type*} [decidable_eq ι] [normed_group E] [normed_space ℝ E]
  [measurable_space E] [borel_space E] [complete_space E] [second_countable_topology E]
  [linear_order β] [measurable_space β] [topological_space β] [opens_measurable_space β]
  [order_closed_topology β]

theorem box_additive_on_integral_preimage_pi_Ioc [encodable ι] [measurable_space α]
  {f : α → ι → β} (hf : measurable f)
  {μ : measure α} {g : α → E} {s : set (ι → β)} (hg : integrable_on g (f ⁻¹' s) μ) :
  box_additive_on (λ l r, ∫ x in f ⁻¹' (pi univ (λ i, Ioc (l i) (r i))), g x ∂μ) s :=
begin
  intros l u hsub m hm i,
  rw [← integral_union, ← preimage_union, pi_univ_Ioc_update_union l u i (m i) ⟨hm.1 i, hm.2 i⟩],
  { exact disjoint_pi_univ_Ioc_update_left_right.preimage _ },
  { apply hf,
    exact is_measurable.pi (countable_encodable univ) (λ _ _, is_measurable_Ioc) },
  { apply hf,
    exact is_measurable.pi (countable_encodable univ) (λ _ _, is_measurable_Ioc) },
  { refine hg.mono_set (preimage_mono (subset.trans _ hsub)),
    rw [pi_univ_Ioc_update_right, ← pi_univ_Icc],
    exacts [(trans (inter_subset_right _ _) $ pi_mono $ λ i hi, Ioc_subset_Icc_self), hm.2 i] },
  { refine hg.mono_set (preimage_mono (subset.trans _ hsub)),
    rw [pi_univ_Ioc_update_left, ← pi_univ_Icc],
    exacts [(trans (inter_subset_right _ _) $ pi_mono $ λ i hi, Ioc_subset_Icc_self), hm.1 i] }
end

theorem box_additive_on_integral_pi_Ioc [encodable ι] {μ : measure (ι → β)}
  {g : (ι → β) → E} {s : set (ι → β)} (hg : integrable_on g s μ) :
  box_additive_on (λ l r, ∫ x in pi univ (λ i, Ioc (l i) (r i)), g x ∂μ) s :=
box_additive_on_integral_preimage_pi_Ioc measurable_id hg

theorem box_additive_on_integral_Icc [fintype ι] (μ : ι → measure β)
  [∀ i, has_no_atoms (μ i)] [∀ i, sigma_finite (μ i)]
  {g : (ι → β) → E} {s : set (ι → β)} (hg : integrable_on g s (measure.pi μ)) :
  box_additive_on (λ l r, ∫ x in Icc l r, g x ∂measure.pi μ) s :=
begin
  letI := encodable.fintype.encodable ι,
  refine (box_additive_on_integral_pi_Ioc hg).congr (λ l u hle hsub, _),
  rw restrict_congr_set,
  exact measure.univ_pi_Ioc_ae_eq_Icc
end
