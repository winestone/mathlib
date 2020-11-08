import measure_theory.ext_is_o
import analysis.calculus.fderiv

open measure_theory set function topological_space asymptotics
open_locale big_operators topological_space filter

noncomputable theory

def divergence (𝕜 : Type*) {E : Type*} [nondiscrete_normed_field 𝕜] [normed_group E]
  [normed_space 𝕜 E] (f : E → E) (x : E) :=
linear_map.trace 𝕜 _ (fderiv 𝕜 f x : E →ₗ[𝕜] E)

lemma fin.divergence_eq {𝕜 : Type*} [nondiscrete_normed_field 𝕜] {n : ℕ}
  (f : (fin n → 𝕜) → fin n → 𝕜) (x : fin n → 𝕜) (hx : differentiable_at 𝕜 f x) :
  divergence 𝕜 f x = ∑ i : fin n, fderiv 𝕜 f x (update 0 i 1) i :=
begin
  rw [divergence, linear_map.trace_eq_sum 𝕜 (pi.is_basis_fun _ _)];
    try { apply_instance },
  refine finset.sum_congr rfl (λ i hi, _),
  simp_rw [pi.fun_basis_repr_apply, continuous_linear_map.coe_coe, linear_map.std_basis_apply],
  congr
end

variables {E : Type*} [normed_group E] [normed_space ℝ E] [second_countable_topology E]
  [complete_space E] [measurable_space E] [borel_space E] {n : ℕ}
  {μ : measure (fin n → ℝ)} {ν : measure (fin (n + 1) → ℝ)}
  (hμ : ∀ x y, μ (Icc x y) = ∏ i, ennreal.of_real (y i - x i))
  (hν : ∀ x y, ν (Icc x y) = ∏ i, ennreal.of_real (y i - x i))
  (f : (fin (n + 1) → ℝ) → fin (n + 1) → E)

include hμ hν

theorem integral_sum_pderiveq_sum_faces_integral {x y : fin (n + 1) → ℝ}
  (hxy : x ≤ y) (hdiv : continuous_on (λ z, ∑ i, fderiv ℝ f z (update 0 i 1) i) (Icc x y))
  (hd : differentiable_on ℝ f (Icc x y)) :
  ∫ z in Icc x y, ∑ i, fderiv ℝ f z (update 0 i 1) i ∂ν =
   ∑ i : fin (n + 1),
     (∫ z in Icc (x ∘ i.succ_above) (y ∘ i.succ_above), f (fin.insert_nth i (y i) z) i ∂μ -
     ∫ z in Icc (x ∘ i.succ_above) (y ∘ i.succ_above), f (fin.insert_nth i (x i) z) i ∂μ) :=
begin
  haveI := locally_finite_of_measure_Icc hμ,
  haveI := locally_finite_of_measure_Icc hν,
  rw ← sub_eq_zero,
  apply box_subadditive_on.eq_zero_of_forall_is_o_prod' hxy,
  { refine ((box_additive_on_set_integral_Icc' hν _).sub _).norm_subadditive_on,
    { refine hdiv.integrable_on_compact compact_pi_Icc (finset.measurable_sum _ $ λ i, _),
      letI : measurable_space ((fin (n + 1) → ℝ) →L[ℝ] (fin (n + 1) → E)) := borel _,
      haveI : borel_space ((fin (n + 1) → ℝ) →L[ℝ] (fin (n + 1) → E)) := ⟨rfl⟩,
      suffices : measurable (fderiv ℝ f),
      { have := (continuous_linear_map.apply ℝ _ (update 0 i 1)).continuous.measurable.comp this,
        have := (measurable_pi_apply i).comp this,
        simpa [(∘)] },
      sorry },
    { refine box_additive_on_sum_faces_fin (Icc x y) (λ (i : fin (n + 1)) c (l r : fin n → ℝ),
        ∫ z in Icc l r, f (i.insert_nth c z) i ∂μ) (λ i c, box_additive_on_set_integral_Icc' hμ _),
      apply continuous_on.integrable_on_compact,
      { sorry },
      { 
        sorry },
      { sorry } } },
  { intros b hb,
 }
end
