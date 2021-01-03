import analysis.normed_space.box_subadditive
import measure_theory.set_integral

variables {ι α : Type*} [decidable_eq ι] [encodable ι] [measurable_space α]

open measure_theory set topological_space (second_countable_topology) filter function
open_locale nnreal topological_space filter big_operators

namespace measure_theory

theorem measure.box_additive_pi_Ioc (μ : measure (ι → ℝ)) (s : set (ι → ℝ)) :
  box_additive_on (λ l r, μ (pi univ (λ i, Ioc (l i) (r i)))) s :=
begin
  intros l u hsub m hm i,
  rw [← measure_union disjoint_pi_univ_Ioc_update_left_right,
    pi_univ_Ioc_update_union l u i (m i) ⟨hm.1 i, hm.2 i⟩];
    exact is_measurable.pi (countable_encodable _) (λ _ _, is_measurable_Ioc)
end

variables {E : Type*} [normed_group E] [normed_space ℝ E]
  [measurable_space E] [borel_space E] [complete_space E] [second_countable_topology E]

theorem box_additive_on_set_integral_preimage {f : α → ι → ℝ} (hf : measurable f)
  {μ : measure α} {g : α → E} {s : set (ι → ℝ)} (hg : integrable_on g (f ⁻¹' s) μ) :
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

theorem box_additive_on_set_integral {μ : measure (ι → ℝ)} {g : (ι → ℝ) → E} {s : set (ι → ℝ)}
  (hg : integrable_on g s μ) :
  box_additive_on (λ l r, ∫ x in pi univ (λ i, Ioc (l i) (r i)), g x ∂μ) s :=
box_additive_on_set_integral_preimage measurable_id hg

theorem pi_univ_Ioo_ae_eq_Icc {μ : measure (ι → ℝ)}
  (h : ∀ (x y : ι → ℝ) (i : ι), x i = y i → μ (Icc x y) = 0) (x y : ι → ℝ) :
  pi univ (λ i, Ioo (x i) (y i)) =ᵐ[μ] Icc x y :=
begin
  refine eventually_le.antisymm (eventually_of_forall _) _,
  { exact pi_univ_Icc x y ▸ pi_mono (λ _ _, Ioo_subset_Icc_self) },
  { rw [ae_le_set],
    refine measure_mono_null (Icc_diff_pi_univ_Ioo_subset x y x y)
      (measure_union_null (measure_Union_null _) (measure_Union_null _)),
    exacts [λ i, h _ _ i (by simp), λ i, h _ _ i (by simp)] }
end

theorem pi_univ_Ioc_ae_eq_Icc {μ : measure (ι → ℝ)}
  (h : ∀ (x y : ι → ℝ) (i : ι), x i = y i → μ (Icc x y) = 0) (x y : ι → ℝ) :
  pi univ (λ i, Ioc (x i) (y i)) =ᵐ[μ] Icc x y :=
begin
  refine eventually_le.antisymm (eventually_of_forall _) _,
  { exact pi_univ_Icc x y ▸ pi_mono (λ _ _, Ioc_subset_Icc_self) },
  { rw [ae_le_set],
    refine measure_mono_null (Icc_diff_pi_univ_Ioc_subset x x y) (measure_Union_null _),
    refine λ i, h _ _ i _,
    simp }
end

theorem box_additive_on_set_integral_Icc {μ : measure (ι → ℝ)}
  (hμ : ∀ (x y : ι → ℝ) (i : ι), x i = y i → μ (Icc x y) = 0) {g : (ι → ℝ) → E} {s : set (ι → ℝ)}
  (hg : integrable_on g s μ) :
  box_additive_on (λ l r, ∫ x in Icc l r, g x ∂μ) s :=
by simpa only [restrict_congr_set (pi_univ_Ioc_ae_eq_Icc hμ _ _)]
  using box_additive_on_set_integral hg

theorem box_additive_on_set_integral_Icc' [fintype ι] {μ : measure (ι → ℝ)}
  (hμ : ∀ x y, μ (Icc x y) = ∏ i, ennreal.of_real (y i - x i)) {g : (ι → ℝ) → E} {s : set (ι → ℝ)}
  (hg : integrable_on g s μ) :
  box_additive_on (λ l r, ∫ x in Icc l r, g x ∂μ) s :=
begin
  refine box_additive_on_set_integral_Icc (λ x y i hi, _) hg,
  rw [hμ],
  refine finset.prod_eq_zero (finset.mem_univ i) _,
  simp [hi.ge]
end

theorem locally_finite_of_measure_Icc [fintype ι] {μ : measure (ι → ℝ)}
  (hμ : ∀ x y, μ (Icc x y) = ∏ i, ennreal.of_real (y i - x i)) :
  locally_finite_measure μ :=
begin
  refine ⟨λ x, ⟨Icc (x - 1) (x + 1), _, _⟩⟩,
  { exact pi_Icc_mem_nhds' (λ i, sub_lt_self _ zero_lt_one)
      (λ i, lt_add_of_pos_right _ zero_lt_one) },
  simp [hμ, ennreal.pow_lt_top]
end

end measure_theory
