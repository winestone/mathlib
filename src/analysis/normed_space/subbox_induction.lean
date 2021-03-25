/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yury G. Kudryashov
-/
import data.real.ennreal
import topology.metric_space.basic
import linear_algebra.affine_space.ordered
import analysis.normed_space.add_torsor
import analysis.specific_limits
import analysis.asymptotics.asymptotics

variables {ι : Type*} [fintype ι]

open set function filter
open_locale topological_space filter

lemma subbox_induction_seq  [Π (i : ι) (s : set ι), decidable (i ∈ s)]
  {p : (ι → ℝ) → (ι → ℝ) → Prop} (l u : ι → ℝ) (hle : l ≤ u)
  (H_ind : ∀ (x ∈ Icc l u) (y ∈ Icc l u), x ≤ y →
    (∀ s : set ι, p (s.piecewise (midpoint ℝ x y) x) (s.piecewise y (midpoint ℝ x y))) → p x y) :
  ∃ (x y : ℕ → ι → ℝ), x 0 = l ∧ y 0 = u ∧ (∀ n, x n ≤ y n) ∧ (∀ n, x n ≤ x (n + 1)) ∧
    (∀ n, y (n + 1) ≤ y n) ∧ (∀ n, x n ∈ Icc l u) ∧ (∀ n, y n ∈ Icc l u) ∧
    (∀ n, y n - x n = (2⁻¹ : ℝ) ^ n • (u - l)) ∧ ∀ n, p (x n) (y n) → p l u :=
begin
  /- Step 1: turn `H_ind` into a function that takes a box `[x, y]` and returns one of `2^|ι|` twice
  smaller boxes `[x', y']` such that `p x' y' → p x y`. -/
  replace H_ind := λ x hx y hy hxy, forall_imp_iff_exists_imp.1 (H_ind x hx y hy hxy),
  choose! s hs using H_ind,
  set next : (ι → ℝ) × (ι → ℝ) → (ι → ℝ) × (ι → ℝ) :=
    λ xy, ((s xy.1 xy.2).piecewise (midpoint ℝ xy.1 xy.2) xy.1,
      (s xy.1 xy.2).piecewise xy.2 (midpoint ℝ xy.1 xy.2)),
  have le_next : ∀ xy : (ι → ℝ) × (ι → ℝ), xy.1 ≤ xy.2 → xy.1 ≤ (next xy).1,
    from λ xy hle, le_piecewise (λ i _, left_le_midpoint.2 hle i) (λ i _, le_rfl),
  have next_le_next : ∀ xy : (ι → ℝ) × (ι → ℝ), xy.1 ≤ xy.2 → (next xy).1 ≤ (next xy).2,
    from λ xy hle, piecewise_le_piecewise (λ i _, midpoint_le_right.2 hle i)
      (λ i _, left_le_midpoint.2 hle i),
  have next_le : ∀ xy : (ι → ℝ) × (ι → ℝ), xy.1 ≤ xy.2 → (next xy).2 ≤ xy.2,
    from λ xy hle, piecewise_le (λ _ _, le_rfl) (λ i _, midpoint_le_right.2 hle i),
  have next_sub : ∀ xy : (ι → ℝ) × (ι → ℝ), (next xy).2 - (next xy).1 = (2⁻¹ : ℝ) • (xy.2 - xy.1),
  { intro xy,
    rw [← pi.piecewise_sub, right_sub_midpoint, midpoint_sub_left, set.piecewise_same,
      inv_of_eq_inv] },
  have next_p : ∀ xy : (ι → ℝ) × (ι → ℝ), xy.1 ∈ Icc l u → xy.2 ∈ Icc l u → xy.1 ≤ xy.2 →
    p (next xy).1 (next xy).2 → p xy.1 xy.2, 
    from λ xy mem₁ mem₂ hle, (hs _ mem₁ _ mem₂ hle),
  clear_value next, clear hs s,
  /- Step 2: iterate `next` to get a sequence of boxes. For readability we use separate variables
  for the lower and upper bounds of the boxes. -/
  set x : ℕ → ι → ℝ := λ n, (next^[n] (l, u)).1,
  set y : ℕ → ι → ℝ := λ n, (next^[n] (l, u)).2,
  have x0 : x 0 = l := rfl, have y0 : y 0 = u := rfl,
  have x_succ : ∀ n, x (n + 1) = (next (x n, y n)).1,
  { intro n, simp only [*, prod.mk.eta], rw iterate_succ_apply' },
  have y_succ : ∀ n, y (n + 1) = (next (x n, y n)).2,
  { intro n, simp only [*, prod.mk.eta], rw iterate_succ_apply' },
  clear_value x y,
  have x_le_y : ∀ n, x n ≤ y n,
  { intro n,
    induction n with n ihn,
    { rwa [x0, y0] },
    { rw [x_succ, y_succ], exact next_le_next (x n, y n) ihn } },
  have x_le_succ : ∀ n, x n ≤ x (n + 1),
  { intro n, rw x_succ, exact le_next (x n, y n) (x_le_y n) },
  have succ_le_y : ∀ n, y (n + 1) ≤ y n,
  { intro n, rw y_succ, exact next_le (x n, y n) (x_le_y n) },
  choose x_mem y_mem using show ∀ n, x n ∈ Icc l u ∧ y n ∈ Icc l u,
  { intro n,
    induction n with n ihn,
    { rw [x0, y0], exact ⟨left_mem_Icc.2 hle, right_mem_Icc.2 hle⟩ },
    { have h₁ : l ≤ x (n + 1) := ihn.1.1.trans (x_le_succ n),
      have h₂ : y (n + 1) ≤ u := (succ_le_y n).trans ihn.2.2,
      exact ⟨⟨h₁, (x_le_y _).trans h₂⟩, ⟨h₁.trans (x_le_y _), h₂⟩⟩ } },
  have y_sub_x : ∀ n, y n - x n = (2⁻¹ : ℝ) ^ n • (u - l),
  { intro n,
    induction n with n ihn,
    { simp [x0, y0] },
    { rw [x_succ, y_succ, next_sub, ihn, smul_smul, pow_succ] } },
  have hp : ∀ n, p (x n) (y n) → p l u,
  { intro n,
    induction n with n ihn,
    { rw [x0, y0], exact id },
    { rw [x_succ, y_succ],
      exact ihn ∘ (next_p (x n, y n) (x_mem _) (y_mem _) (x_le_y _)) } },
  exact ⟨x, y, x0, y0, x_le_y, x_le_succ, succ_le_y, x_mem, y_mem, y_sub_x, hp⟩
end

lemma subbox_induction [fintype ι]  [Π (i : ι) (s : set ι), decidable (i ∈ s)]
  {p : (ι → ℝ) → (ι → ℝ) → Prop} (l u : ι → ℝ) (hle : l ≤ u)
  (H_ind : ∀ (x ∈ Icc l u) (y ∈ Icc l u), x ≤ y →
    (∀ s : set ι, p (s.piecewise (midpoint ℝ x y) x) (s.piecewise y (midpoint ℝ x y))) → p x y)
  (H_nhds : ∀ z ∈ Icc l u, ∃ (U ∈ 𝓝[Icc l u] z) (N : ℕ), ∀ (x ∈ Icc l z) (y ∈ Icc z u) (n ≥ N),
    Icc (x : ι → ℝ) y ⊆ U → (y - x = (2⁻¹ : ℝ) ^ n • (u - l)) → p x y) :
  p l u :=
begin
  rcases subbox_induction_seq l u hle H_ind
    with ⟨x, y, x0, y0, x_le_y, x_le_succ, succ_le_y, x_mem, y_mem, y_sub_x, hp⟩,
  clear H_ind,
  have xy_succ_subset : ∀ n, Icc (x (n + 1)) (y (n + 1)) ⊆ Icc (x n) (y n),
    from λ n, Icc_subset_Icc (x_le_succ n) (succ_le_y n),
  have x_mono : ∀ i, monotone (λ n, x n i),
    from λ i, monotone_of_monotone_nat (λ n, x_le_succ n i),
  have y_mono : ∀ i ⦃m n⦄, m ≤ n → y n i ≤ y m i,
    from λ i, @monotone_of_monotone_nat (order_dual ℝ) _ (λ n, y n i) (λ n, succ_le_y n i),
  set z : ι → ℝ := ⨆ n, x n,
  have hz : z ∈ ⋂ n, Icc (x n) (y n),
    from csupr_mem_Inter_Icc_of_mono_decr_Icc_nat xy_succ_subset x_le_y,
  rw [mem_Inter] at hz,
  have hz' : z ∈ Icc l u, by convert ← hz 0,
  have tendsto_x : tendsto x at_top (𝓝 z),
  { refine tendsto_pi.2 (λ i, _),
    simp only [z, supr_apply],
    exact tendsto_at_top_csupr (x_mono i) ⟨u i, forall_range_iff.2 $ λ n, (x_mem n).2 i⟩ },
  have tendsto_y : tendsto y at_top (𝓝 z),
  { suffices : tendsto (λ n, y n - x n) at_top (𝓝 ((0 : ℝ) • (u - l))),
      by simpa using tendsto_x.add this,
    simp only [y_sub_x],
    refine (tendsto_pow_at_top_nhds_0_of_lt_1 _ _).smul tendsto_const_nhds,
    exacts [inv_nonneg.2 zero_le_two, inv_lt_one one_lt_two] },
  replace tendsto_x := tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _
    tendsto_x (eventually_of_forall x_mem),
  replace tendsto_y := tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _
    tendsto_y (eventually_of_forall y_mem),
  rcases H_nhds z hz' with ⟨U, zU, N, hN⟩,
  have : ∀ᶠ n in at_top, Icc (x n) (y n) ⊆ U :=
    tendsto_lift'.1 (tendsto_x.Icc tendsto_y) U zU,
  rcases (this.and (eventually_ge_at_top N)).exists with ⟨n, hn, hNn⟩,
  exact hp n (hN (x n) ⟨(x_mem n).1, (hz n).1⟩ (y n) ⟨(hz n).2, (y_mem n).2⟩ n hNn hn (y_sub_x n))
end
