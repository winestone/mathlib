import measure_theory.lebesgue_measure
import measure_theory.box_additive
import analysis.calculus.fderiv_measurable

open measure_theory set function topological_space asymptotics filter
open_locale big_operators topological_space filter

noncomputable theory

variables {E : Type*} [normed_group E] [normed_space ℝ E] [second_countable_topology E]
  [complete_space E] [measurable_space E] [borel_space E] {n : ℕ}
  {f g : (fin (n + 1) → ℝ) → fin (n + 1) → E}
  {f' g' : (fin (n + 1) → ℝ) → ((fin (n + 1) → ℝ) →L[ℝ] fin (n + 1) → E)}
  {x y : fin (n + 1) → ℝ}

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

def box_boundary_integral (f : (fin (n + 1) → ℝ) → fin (n + 1) → E) (x y : fin (n + 1) → ℝ) : E :=
∑ i : fin (n + 1),
  ((∫ z in Icc (x ∘ i.succ_above) (y ∘ i.succ_above), f (fin.insert_nth i (y i) z) i) -
    ∫ z in Icc (x ∘ i.succ_above) (y ∘ i.succ_above), f (fin.insert_nth i (x i) z) i)

lemma integrable_on_face_aux (h : continuous_on f (Icc x y)) {i j : fin (n + 1)}
  {m} (hm : m ∈ Icc (x i) (y i)) :
  integrable_on (λ z, f (fin.insert_nth i m z) j) (Icc (x ∘ i.succ_above) (y ∘ i.succ_above)) :=
begin
  refine continuous_on.integrable_on_compact compact_pi_Icc _,
  refine (continuous_apply j).comp_continuous_on
    (h.comp (continuous_insert_nth _ _).continuous_on _),
  exact (λ z hz, ⟨fin.le_insert_nth_iff.2 ⟨hm.1, hz.1⟩, fin.insert_nth_le_iff.2 ⟨hm.2, hz.2⟩⟩)
end

lemma integrable_on_face_right (hle : x ≤ y) (h : continuous_on f (Icc x y)) (i : fin (n + 1)) :
  integrable_on (λ z, f (fin.insert_nth i (y i) z) i) (Icc (x ∘ i.succ_above) (y ∘ i.succ_above)) :=
integrable_on_face_aux h (right_mem_Icc.2 (hle i))

lemma integrable_on_face_left (hle : x ≤ y) (h : continuous_on f (Icc x y)) (i : fin (n + 1)) :
  integrable_on (λ z, f (fin.insert_nth i (x i) z) i) (Icc (x ∘ i.succ_above) (y ∘ i.succ_above)) :=
integrable_on_face_aux h (left_mem_Icc.2 (hle i))

/-- Divergence theorem for an affine map. -/
lemma affine_map.box_boundary_integral (hxy : x ≤ y)
  (f : (fin (n + 1) → ℝ) →ᵃ[ℝ] (fin (n + 1) → E)) :
  box_boundary_integral f x y = (∏ i, (y i - x i)) • ∑ i, f.linear (update 0 i 1) i :=
begin
  have hf : continuous f := f.continuous_of_finite_dimensional,
  rw finset.smul_sum,
  refine finset.sum_congr rfl (λ i hi, _),
  rw [← integral_sub (integrable_on_face_right hxy hf.continuous_on i)
    (integrable_on_face_left hxy hf.continuous_on i)],
  have : ∀ (i : fin (n + 1)) z, f (i.insert_nth (y i) z) i - f (i.insert_nth (x i) z) i =
    (y i - x i) • f.linear (update 0 i 1) i,
  { intros i z,
    calc (f (i.insert_nth (y i) z) - f (i.insert_nth (x i) z)) i
        = f.linear (i.insert_nth (y i) z -ᵥ i.insert_nth (x i) z) i :
          by rw [f.linear_map_vsub, vsub_eq_sub]
    ... = f.linear (update 0 i ((y i - x i) • (1 : ℝ))) i : by simp
    ... = ((y i - x i) • f.linear (update 0 i 1)) i :
          by simp [← f.linear.map_smul (y i - x i), smul_update] },
  simp only [this, set_integral_const],
  rw [real.volume_Icc_pi_to_real, fin.prod_univ_succ_above _ i, smul_smul, mul_comm],
  exact λ j, hxy _
end

theorem box_additive_on_box_boundary_integral {x y : fin (n + 1) → ℝ}
  (hf : continuous_on f (Icc x y)) :
  box_additive_on (box_boundary_integral f) (Icc x y) :=
begin
  refine box_additive_on_sum_faces_fin (Icc x y)
    (λ (i : fin (n + 1)) c (l r : fin n → ℝ), ∫ z in Icc l r, f (i.insert_nth c z) i) (λ i c, _),
  simp only [volume_pi],
  refine box_additive_on_integral_Icc (λ _, volume) _,
  by_cases hc : c ∈ Icc (x i) (y i),
  { rw [fin.preimage_insert_nth_Icc_of_mem hc],
    exact integrable_on_face_aux hf hc },
  { rw [fin.preimage_insert_nth_Icc_of_not_mem hc],
    exact integrable_on_empty }
end

theorem box_boundary_integral_sub {x y : fin (n + 1) → ℝ} (h : x ≤ y)
  (hfc : continuous_on f (Icc x y)) (hgc : continuous_on g (Icc x y)) :
  box_boundary_integral (λ z, f z - g z) x y =
    box_boundary_integral f x y - box_boundary_integral g x y :=
begin
  have H : ∀ {i} (m ∈ Icc (x i) (y i)),
    ∫ z in Icc (x ∘ i.succ_above) (y ∘ i.succ_above),
      f (i.insert_nth m z) i - g (i.insert_nth m z) i =
    (∫ z in Icc (x ∘ i.succ_above) (y ∘ i.succ_above), f (i.insert_nth m z) i) -
      ∫ z in Icc (x ∘ i.succ_above) (y ∘ i.succ_above), g (i.insert_nth m z) i,
    from λ i m hm, integral_sub (integrable_on_face_aux hfc hm) (integrable_on_face_aux hgc hm),
  simp only [box_boundary_integral, H (x _) (left_mem_Icc.mpr (h _)),
    H (y _) (right_mem_Icc.mpr (h _)), pi.sub_apply, finset.sum_sub_distrib],
  abel
end

theorem box_boundary_integral_eq_of_has_fderiv_within_at (h : x ≤ y)
  (hf'c : continuous_on (λ z, ∑ i, f' z (update 0 i 1) i) (Icc x y))
  (hd : ∀ z ∈ Icc x y, has_fderiv_within_at f (f' z) (Icc x y) z) :
  box_boundary_integral f x y = ∫ z in Icc x y, ∑ i, f' z (update 0 i 1) i :=
begin
  have hfc : continuous_on f (Icc x y) := λ z hz, (hd z hz).continuous_within_at,
  set divf := λ z, ∑ i, f' z (update 0 i 1) i,
  have : box_additive_on (λ l u, (∫ z in Icc l u, divf z) - box_boundary_integral f l u) (Icc x y),
    from (box_additive_on_integral_Icc _ (hf'c.integrable_on_compact compact_pi_Icc)).sub
      (box_additive_on_box_boundary_integral hfc),
  rw [eq_comm, ← sub_eq_zero],
  rcases em (∃ i, x i = y i) with ⟨i, hi⟩ | hne, from this.eq_zero_of_eq h (subset.refl _) hi,
  push_neg at hne,
  have dxy_pos : 0 < dist x y, from dist_pos.2 (mt (λ h, congr_fun h 0) (hne 0)),
  have hlt : ∀ i, x i < y i := λ i, (h i).lt_of_ne (hne i), clear hne,
  set V := ∏ i, (y i - x i),
  have Vpos : 0 < V, from finset.prod_pos (λ i hi, sub_pos.2 (hlt _)),
  refine this.norm_subadditive_on.eq_zero_of_forall_is_o_prod h (λ b hb, _), clear this,
  set T := ((fin (n + 1) → ℝ) × (fin (n + 1) → ℝ)) × ℝ,
  set L : filter T := (𝓝[Icc x b] b ×ᶠ 𝓝[Icc b y] b ×ᶠ 𝓝[Ioi (0 : ℝ)] 0) ⊓
    𝓟 {p | p.fst.snd - p.fst.fst = p.snd • (y - x)},
  simp only [uncurry],
  have H1'' : ∀ᶠ p : T in L, p.1.1 ∈ Icc x b ∧ p.1.2 ∈ Icc b y ∧ 0 < p.2,
  { have A : ∀ᶠ z in 𝓝[Icc x b] b, z ∈ Icc x b := self_mem_nhds_within,
    have B : ∀ᶠ z in 𝓝[Icc b y] b, z ∈ Icc b y := self_mem_nhds_within,
    have C : ∀ᶠ ε : ℝ in 𝓝[Ioi 0] 0, 0 < ε := self_mem_nhds_within,
    simpa only [and.assoc] using (inf_le_left : L ≤ _) ((A.prod_mk B).prod_mk C) },
  have H1 : ∀ᶠ p : T in L, p.1.1 ∈ Icc x b ∧ p.1.2 ∈ Icc b y,
    from H1''.mono (λ p hp, ⟨hp.1, hp.2.1⟩),
  have H1' : ∀ᶠ p : T in L, p.1.1 ≤ p.1.2 := H1.mono (λ p hp, hp.1.2.trans hp.2.1),
  have H2 : tendsto (λ p : T, p.1.1) L (𝓝[Icc x b] b),
    from (tendsto_fst.comp tendsto_fst).mono_left inf_le_left,
  have H2' : tendsto (λ p : T, p.1.1) L (𝓝[Icc x y] b),
    from H2.mono_right (nhds_within_mono _ $ Icc_subset_Icc_right hb.2),
  have H3 : tendsto (λ p : T, p.1.2) L (𝓝[Icc b y] b),
    from (tendsto_snd.comp tendsto_fst).mono_left inf_le_left,
  have H3' : tendsto (λ p : T, p.1.2) L (𝓝[Icc x y] b),
    from H3.mono_right (nhds_within_mono _ $ Icc_subset_Icc_left hb.1),
  have H4 : tendsto (λ p : T, Icc p.1.1 p.1.2) L ((𝓝[Icc x y] b).lift' powerset), from H2'.Icc H3',
  have H5 : (λ p : T, (volume (Icc p.1.1 p.1.2)).to_real) =ᶠ[L] (λ p, ∏ i, (p.1.2 i - p.1.1 i)),
    from H1'.mono (λ p, real.volume_Icc_pi_to_real),
  have H6 : ∀ᶠ p : T in L, ∀ i, p.1.2 i - p.1.1 i = p.2 * (y i - x i),
    from eventually_inf_principal.2 (eventually_of_forall (λ p hp, congr_fun hp)),
  have H7 : (λ p : T, ∏ i, (p.1.2 i - p.1.1 i)) =ᶠ[L] (λ p, V • p.2 ^ (n + 1)),
  { refine H6.mono (λ p hp, (finset.prod_congr rfl (λ i _, hp i)).trans _),
    simp [finset.prod_mul_distrib, mul_comm, V] },
  refine (hf'c.integral_sub_linear_is_o_ae hb compact_pi_Icc.is_measurable H4 _ H5).triangle _,
  suffices : is_o _ _ L, from this.congr' (eventually_eq.refl _ _) H7.symm,
  set df : (fin (n + 1) → ℝ) →ᵃ[ℝ] (fin (n + 1) → E) :=
    (affine_equiv.const_vadd ℝ (fin (n + 1) → E) (f b)).to_affine_map.comp
      ((f' b).to_linear_map.to_affine_map.comp (affine_equiv.vadd_const ℝ b).symm.to_affine_map),
  have hdf : ∀ z, df z = f b + f' b (z - b), from λ z, rfl,
  have hdfc : continuous df,
    from continuous_const.add ((f' b).continuous.comp (continuous_id.sub continuous_const)),
  have H8 :
    is_o (λ p : T, (∏ i, (p.1.2 i - p.1.1 i)) • divf b - box_boundary_integral df p.1.1 p.1.2)
      (λ p, V • p.2 ^ (n + 1)) L,
  { refine (is_o_zero _ _).congr' (H1'.mono $ λ p hp, _) (eventually_eq.refl _ _),
    refine (sub_eq_zero.2 _).symm,
    simpa using (df.box_boundary_integral hp hdfc).symm },
  refine H8.triangle (is_o.symm _), clear H8,
  have H9 : (λ p : T, box_boundary_integral (λ z, f z - f b - f' b (z - b)) p.1.1 p.1.2) =ᶠ[L]
    (λ p : T, box_boundary_integral f p.1.1 p.1.2 - box_boundary_integral df p.1.1 p.1.2),
  { refine H1.mono (λ p hp, _),
    simp only [← box_boundary_integral_sub (hp.1.2.trans hp.2.1)
      (hfc.mono $ Icc_subset_Icc hp.1.1 hp.2.2) hdfc.continuous_on],
    simp only [hdf, sub_sub] },
  refine is_o.congr' H9 (eventually_eq.refl _ _) (is_o.sum $ λ i hi, _), clear hi,
  set g := λ z, f z - f b - (f' b) (z - b),
  have hg : is_o g (λ z, z - b) (𝓝[Icc x y] b) := hd b hb,
  suffices : ∀ m : T → ℝ, (∀ᶠ p in L, m p ∈ Icc (p.1.1 i) (p.1.2 i)) →
    is_o (λ p : T,
      ∫ z in Icc (p.1.1 ∘ i.succ_above) (p.1.2 ∘ i.succ_above), g (i.insert_nth (m p) z) i)
      (λ p, V • p.2 ^ (n + 1)) L,
  { refine (this (λ p, p.1.2 i) _).sub (this (λ p, p.1.1 i) _),
    exacts [H1'.mono (λ p hp, right_mem_Icc.2 (hp i)), H1'.mono (λ p hp, left_mem_Icc.2 (hp i))] },
  refine λ m hm, is_o_iff.2 (λ C Cpos, _),
  set Ci := C * (y i - x i),
  have Cipos : 0 < Ci, from mul_pos Cpos (sub_pos.2 $ hlt i),
  filter_upwards [H1'', H6, hm,
    tendsto_lift'.1 H4 _ (hg.def (div_pos Cipos dxy_pos))],
  rintro ⟨⟨l, u⟩, ε⟩ ⟨⟨hxl, hlb⟩, ⟨hbu, huy⟩, ε0⟩ hsub_eq hlmu hC,
  dsimp only at *,
  have : ∀ z ∈ Icc (l ∘ i.succ_above) (u ∘ i.succ_above),
    ∥g (i.insert_nth (m ((l, u), ε)) z) i∥ ≤ Ci * ε,
  { rintros z hz,
    set m' := m ((l, u), ε),
    have : i.insert_nth m' z ∈ Icc l u, from fin.insert_nth_mem_Icc.2 ⟨hlmu, hz⟩,
    calc ∥g (i.insert_nth m' z) i∥ ≤ ∥g (i.insert_nth m' z)∥ : norm_le_pi_norm _ _
    ... ≤ Ci / dist x y * ∥(i.insert_nth m' z) - b∥ : hC this
    ... ≤ Ci * ε : _,
    rw [div_eq_mul_inv, mul_assoc, ← div_eq_inv_mul, mul_le_mul_left Cipos, div_le_iff dxy_pos,
      ← dist_eq_norm],
    calc dist (i.insert_nth m' z) b ≤ dist l u : real.dist_pi_le_of_mem_Icc this ⟨hlb, hbu⟩
    ... ≤ ε * dist x y : (dist_pi_le_iff (mul_nonneg ε0.le dist_nonneg)).2 (λ j, _),
    simp only [dist_eq_norm', real.norm_eq_abs, hsub_eq, abs_mul, abs_of_pos ε0],
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm (y - x) j) ε0.le },
  refine (norm_set_integral_le_of_norm_le_const' _ compact_pi_Icc.is_measurable this).trans _,
  { rw [real.volume_Icc_pi], exact ennreal.prod_lt_top (λ i hi, ennreal.of_real_lt_top) },
  simp only [Ci, mul_assoc],
  rw [real.volume_Icc_pi_to_real, mul_le_mul_left Cpos], swap, exact λ j, (hlb.trans hbu) _,
  calc _ = _ : _
  ... ≤ _ : le_abs_self _,
  simp only [hsub_eq, finset.prod_mul_distrib, finset.prod_const, finset.card_fin,
    fin.prod_univ_succ_above _ i, V, pow_succ, smul_eq_mul],
  ac_refl
end

theorem box_boundary_integral_eq_fderiv_within (h : x ≤ y)
  (hd : differentiable_on ℝ f (Icc x y))
  (hf'c : continuous_on (λ z, ∑ i, fderiv_within ℝ f (Icc x y) z (update 0 i 1) i) (Icc x y)) :
  box_boundary_integral f x y =
    ∫ z in Icc x y, ∑ i, fderiv_within ℝ f (Icc x y) z (update 0 i 1) i :=
box_boundary_integral_eq_of_has_fderiv_within_at h hf'c $ λ z hz, (hd z hz).has_fderiv_within_at

theorem box_boundary_integral_eq_fderiv (h : x ≤ y)
  (hd : ∀ z ∈ Icc x y, differentiable_at ℝ f z)
  (hf'c : continuous_on (λ z, ∑ i, fderiv ℝ f z (update 0 i 1) i) (Icc x y)) :
  box_boundary_integral f x y = ∫ z in Icc x y, ∑ i, fderiv ℝ f z (update 0 i 1) i :=
box_boundary_integral_eq_of_has_fderiv_within_at h hf'c $
  λ z hz, (hd z hz).has_fderiv_at.has_fderiv_within_at
