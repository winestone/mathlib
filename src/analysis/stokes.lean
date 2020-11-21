import measure_theory.ext_is_o
import analysis.calculus.measurable_deriv

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

def stokes_sum (x y : fin (n + 1) → ℝ) (μ : measure (fin n → ℝ)) (ν : measure (fin (n + 1) → ℝ))
  (f : (fin (n + 1) → ℝ) → fin (n + 1) → E) : E :=
∫ z in Icc x y, ∑ i, fderiv ℝ f z (update 0 i 1) i ∂ν -
  ∑ i : fin (n + 1),
     (∫ z in Icc (x ∘ i.succ_above) (y ∘ i.succ_above), f (fin.insert_nth i (y i) z) i ∂μ -
     ∫ z in Icc (x ∘ i.succ_above) (y ∘ i.succ_above), f (fin.insert_nth i (x i) z) i ∂μ)

lemma stokes_sum_const (x y : fin (n + 1) → ℝ) (μ : measure (fin n → ℝ))
  (ν : measure (fin (n + 1) → ℝ)) (c : fin (n + 1) → E) :
  stokes_sum x y μ ν (λ _, c) = 0 :=
by simp only [stokes_sum, continuous_linear_map.zero_apply, pi.zero_apply, integral_const,
  finset.sum_const_zero, fderiv_const, smul_zero, sub_self]

@[simp] lemma edist_insert_nth (i : fin (n + 1)) (cx cy : ℝ) (x y : fin n → ℝ) :
  edist (i.insert_nth cx x) (i.insert_nth cy y) = max (edist cx cy) (edist x y) :=
by simp [edist_pi_def, fin.univ_succ_above _ i, (∘)]

@[simp] lemma nndist_insert_nth (i : fin (n + 1)) (cx cy : ℝ) (x y : fin n → ℝ) :
  nndist (i.insert_nth cx x) (i.insert_nth cy y) = max (nndist cx cy) (nndist x y) :=
by { rw ← ennreal.coe_eq_coe, push_cast, exact edist_insert_nth i cx cy x y }

@[simp] lemma dist_insert_nth (i : fin (n + 1)) (cx cy : ℝ) (x y : fin n → ℝ) :
  dist (i.insert_nth cx x) (i.insert_nth cy y) = max (dist cx cy) (dist x y) :=
by { simp only [dist_nndist], exact_mod_cast nndist_insert_nth i cx cy x y }

lemma isometry_insert_nth (i : fin (n + 1)) (c : ℝ) :
  isometry (i.insert_nth c : (fin n → ℝ) → (fin (n + 1) → ℝ)) :=
λ x y, by simp

lemma continuous_insert_nth (i : fin (n + 1)) (c : ℝ) :
  continuous (i.insert_nth c : (fin n → ℝ) → (fin (n + 1) → ℝ)) :=
(isometry_insert_nth i c).continuous

lemma op_insert_nth (i : fin (n + 1)) (c₁ c₂ : ℝ) (x₁ x₂ : fin n → ℝ) (op : ℝ → ℝ → ℝ) :
  (λ j, op (i.insert_nth c₁ x₁ j) (i.insert_nth c₂ x₂ j)) =
    i.insert_nth (op c₁ c₂) (λ j, op (x₁ j) (x₂ j)) :=
fin.eq_insert_nth_iff.2 $ by simp

@[simp] lemma insert_nth_sub_insert_nth (i : fin (n + 1)) (c₁ c₂ : ℝ) (x₁ x₂ : fin n → ℝ) :
  i.insert_nth c₁ x₁ - i.insert_nth c₂ x₂ = i.insert_nth (c₁ - c₂) (x₁ - x₂) :=
op_insert_nth i c₁ c₂ x₁ x₂ has_sub.sub

@[simp] lemma insert_nth_zero (i : fin (n + 1)) (c : ℝ) : i.insert_nth c 0 = update 0 i c :=
fin.insert_nth_eq_iff.2 $ by simp [fin.succ_above_ne, pi.zero_def]

lemma smul_update (i : fin (n + 1)) (c y : ℝ) (x : fin (n + 1) → ℝ) :
  c • update x i y = update (c • x) i (c • y) :=
funext $ apply_update (λ _ z, c • z) x i _

include hμ hν

lemma stokes_sum_clm {x y : fin (n + 1) → ℝ} (hxy : x ≤ y)
  (f : (fin (n + 1) → ℝ) →L[ℝ] (fin (n + 1) → E)) :
  stokes_sum x y μ ν f = 0 :=
begin
  haveI := locally_finite_of_measure_Icc hμ,
  replace hμ : ∀ ⦃x y⦄, x ≤ y → (μ (Icc x y)).to_real = ∏ i, (y i - x i) :=
    λ x y h, by simp [hμ, ennreal.to_real_prod, ennreal.to_real_of_real (sub_nonneg.2 $ h _)],
  replace hν : ∀ ⦃x y⦄, x ≤ y → (ν (Icc x y)).to_real = ∏ i, (y i - x i) :=
    λ x y h, by simp [hν, ennreal.to_real_prod, ennreal.to_real_of_real (sub_nonneg.2 $ h _)],
  have : ∀ (i j : fin (n + 1)) x' y' c,
    integrable_on (λ z, f (i.insert_nth c z) j) (Icc x' y') μ :=
    λ i j x' y' c, continuous.integrable_on_compact compact_pi_Icc $
      (continuous_apply j).comp $ f.continuous.comp (continuous_insert_nth _ _),
  simp only [stokes_sum, hν, integral_const, measure.restrict_apply, continuous_linear_map.fderiv,
    univ_inter, is_measurable.univ, hν hxy],
  conv_lhs { congr, skip, congr, skip, funext,
    rw [← integral_sub (this _ _ _ _ _) (this _ _ _ _ _)] },
  have : ∀ (i : fin (n + 1)) z,
    f (i.insert_nth (y i) z) i - f (i.insert_nth (x i) z) i = (y i - x i) • f (update 0 i 1) i,
  { intros i z,
    calc (f (i.insert_nth (y i) z) - f (i.insert_nth (x i) z)) i =
      f (i.insert_nth (y i) z - i.insert_nth (x i) z) i : by simp only [f.map_sub, pi.sub_apply]
    ... = f (update 0 i (y i - x i)) i : by simp
    ... = ((y i - x i) • f (update 0 i 1)) i : by simp [← f.map_smul (y i - x i), smul_update] },
  simp only [this],
  have : ∀ i : fin (n + 1), x ∘ i.succ_above ≤ y ∘ i.succ_above := λ i j, hxy _,
  simp only [hμ (this _), integral_const, comp_app, measure.restrict_apply, univ_inter,
    is_measurable.univ, smul_smul],
  have : ∀ i : fin (n + 1), (∏ j, (y (i.succ_above j) - x (i.succ_above j))) * (y i - x i) =
    ∏ j, (y j - x j),
  { intro i,
    rw [fin.prod_univ_succ_above _ i, mul_comm] },
  simp [this, finset.smul_sum]
end

theorem box_additive_on_stokes_sum {x y : fin (n + 1) → ℝ}
  (hdiv : continuous_on (λ z, ∑ i, fderiv ℝ f z (update 0 i 1) i) (Icc x y))
  (hd : differentiable_on ℝ f (Icc x y)) (hfm : measurable f) :
  box_additive_on (λ x' y', stokes_sum x' y' μ ν f) (Icc x y) :=
begin
  haveI := locally_finite_of_measure_Icc hμ,
  haveI := locally_finite_of_measure_Icc hν,
  refine (box_additive_on_set_integral_Icc' hν _).sub _,
  { refine hdiv.integrable_on_compact compact_pi_Icc (finset.measurable_sum _ $ λ i, _),
    have := measurable_fderiv_apply_const ℝ f (update 0 i 1),
    convert (measurable_pi_apply i).comp this },
  { refine box_additive_on_sum_faces_fin (Icc x y) (λ (i : fin (n + 1)) c (l r : fin n → ℝ),
      ∫ z in Icc l r, f (i.insert_nth c z) i ∂μ) (λ i c, box_additive_on_set_integral_Icc' hμ _),
    have : measurable (λ z, f (fin.insert_nth i c z) i),
    { suffices : measurable (f ∘ fin.insert_nth i c),
      { simpa only using (measurable_pi_apply i).comp this },
      exact hfm.comp (continuous_insert_nth _ _).measurable },
    by_cases hc : c ∈ Icc (x i) (y i),
    { rw [fin.preimage_insert_nth_Icc_of_mem hc],
      refine continuous_on.integrable_on_compact compact_pi_Icc this _,
      { suffices : continuous_on (f ∘ fin.insert_nth i c) _,
        { simpa only using (continuous_apply i).comp_continuous_on this },
        refine hd.continuous_on.comp (continuous_insert_nth _ _).continuous_on _,
        rw [fin.preimage_insert_nth_Icc_of_mem hc] } },
    { rw [fin.preimage_insert_nth_Icc_of_not_mem hc],
      exact integrable_on_empty this } }
end

theorem stokes_sum_add {x y : fin (n + 1) → ℝ} {g : (fin (n + 1) → ℝ) → fin (n + 1) → E}
  (hf_div : continuous_on (λ z, ∑ i, fderiv ℝ f z (update 0 i 1) i) (Icc x y))
  (hfd : differentiable_on ℝ f (Icc x y)) (hfm : measurable f)
  (hg_div : continuous_on (λ z, ∑ i, fderiv ℝ g z (update 0 i 1) i) (Icc x y))
  (hgd : differentiable_on ℝ g (Icc x y)) (hgm : measurable g) :
  stokes_sum x y μ ν (λ z, f z + g z) = stokes_sum x y μ ν f + stokes_sum x y μ ν g :=
begin
  simp only [stokes_sum],
  
end
