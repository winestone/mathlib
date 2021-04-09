import algebra.big_operators.finprod
import topology.urysohns_lemma
import topology.paracompact
import topology.continuous_function.algebra

universes u v
variables (X : Type u) [topological_space X]

open function set filter
open_locale big_operators topological_space classical

noncomputable theory

/-- Continuous partition of unity. -/
structure partition_of_unity (s : set X := univ) :=
(ι : Type u)
(to_fun : ι → C(X, ℝ))
(locally_finite' : locally_finite (λ i, support (to_fun i)))
(nonneg' : 0 ≤ to_fun)
(sum_eq_one' : ∀ x ∈ s, ∑ᶠ i, to_fun i x = 1)
(sum_le_one' : ∀ x, ∑ᶠ i, to_fun i x ≤ 1)

structure bump_covering (s : set X := univ) :=
(ι : Type u)
(to_fun : ι → C(X, ℝ))
(locally_finite' : locally_finite (λ i, support (to_fun i)))
(nonneg' : 0 ≤ to_fun)
(le_one' : to_fun ≤ 1)
(eventually_eq_one' : ∀ x ∈ s, ∃ i, to_fun i =ᶠ[𝓝 x] 1)

variable {X}

namespace partition_of_unity

variables {s : set X} (fs : partition_of_unity X s)

instance : has_coe_to_fun (partition_of_unity X s) :=
⟨_, to_fun⟩

protected lemma locally_finite : locally_finite (λ i, support (fs i)) :=
fs.locally_finite'

lemma nonneg (i : fs.ι) (x : X) : 0 ≤ fs i x := fs.nonneg' i x

lemma sum_eq_one {x : X} (hx : x ∈ s) : ∑ᶠ i, fs i x = 1 := fs.sum_eq_one' x hx

lemma sum_le_one (x : X) : ∑ᶠ i, fs i x ≤ 1 := fs.sum_le_one' x

def is_subordinate (fs : partition_of_unity X s) (S : set (set X)) : Prop :=
∀ i, ∃ s ∈ S, closure (support (fs i)) ⊆ s

end partition_of_unity

namespace bump_covering

variables {s : set X} (fs : bump_covering X s) (f : bump_covering X)

instance : has_coe_to_fun (bump_covering X s) := ⟨_, to_fun⟩

protected lemma locally_finite : locally_finite (λ i, support (fs i)) :=
fs.locally_finite'

protected lemma point_finite (x : X) : finite {i | fs i x ≠ 0} :=
fs.locally_finite.point_finite x

lemma nonneg (i : fs.ι) (x : X) : 0 ≤ fs i x := fs.nonneg' i x

lemma le_one (i : fs.ι) (x : X) : fs i x ≤ 1 := fs.le_one' i x

def is_subordinate (S : set (set X)) : Prop :=
∀ i, ∃ s ∈ S, closure (support (fs i)) ⊆ s

lemma exists_is_subordinate_of_locally_finite {ι : Type u} [normal_space X] (hs : is_closed s)
  (U : ι → set X) (ho : ∀ i, is_open (U i)) (hf : locally_finite U)
  (hU : s ⊆ ⋃ i, U i) : ∃ f : bump_covering X s, f.is_subordinate (range U) :=
begin
  rcases exists_subset_Union_closure_subset hs ho (λ x _, hf.point_finite x) hU
    with ⟨V, hsV, hVo, hVU⟩,
  have hVU' : ∀ i, V i ⊆ U i, from λ i, subset.trans subset_closure (hVU i),
  rcases exists_subset_Union_closure_subset hs hVo
    (λ x _, (hf.subset hVU').point_finite x) hsV with ⟨W, hsW, hWo, hWV⟩,
  choose f hfc hf0 hf1 hf01
    using λ i, exists_continuous_zero_one_of_closed (is_closed_compl_iff.2 $ hVo i)
      is_closed_closure (disjoint_right.2 $ λ x hx, not_not.2 (hWV i hx)),
  have hsupp : ∀ i, support (f i) ⊆ V i,
    from λ i, support_subset_iff'.2 (hf0 i),
  refine ⟨⟨ι, λ i, ⟨f i, hfc i⟩, hf.subset (λ i, subset.trans (hsupp i) (hVU' i)),
    λ i x, (hf01 i x).1, λ i x, (hf01 i x).2, λ x hx, _⟩, λ i, _⟩,
  { rcases mem_Union.1 (hsW hx) with ⟨i, hi⟩,
    exact ⟨i, ((hf1 i).mono subset_closure).eventually_eq_of_mem (mem_nhds_sets (hWo i) hi)⟩ },
  { exact ⟨U i, mem_range_self _, subset.trans (closure_mono (hsupp i)) (hVU i)⟩ }
end

lemma exists_is_subordinate [normal_space X] [paracompact_space X]
  (hs : is_closed s) (U : set (set X)) (ho : ∀ s ∈ U, is_open s) (hU : s ⊆ ⋃₀ U) :
  ∃ f : bump_covering X s, f.is_subordinate U :=
begin
  rw [sUnion_eq_Union] at hU, rw [set_coe.forall'] at ho,
  rcases precise_refinement_set hs _ ho hU with ⟨V, hVo, hsV, hVf, hVU⟩,
  rcases exists_is_subordinate_of_locally_finite hs V hVo hVf hsV with ⟨f, hf⟩,
  refine ⟨f, λ i, _⟩,
  rcases hf i with ⟨_, ⟨t, rfl⟩, ht⟩,
  exact ⟨t, t.2, subset.trans ht (hVU t)⟩
end

/-- Index of a bump function such that `fs i =ᶠ[𝓝 x] 1`. -/
def ind (x : X) (hx : x ∈ s) : fs.ι := (fs.eventually_eq_one' x hx).some

lemma eventually_eq_one (x : X) (hx : x ∈ s) : fs (fs.ind x hx) =ᶠ[𝓝 x] 1 :=
(fs.eventually_eq_one' x hx).some_spec

lemma ind_apply (x : X) (hx : x ∈ s) : fs (fs.ind x hx) x = 1 :=
(fs.eventually_eq_one x hx).eq_of_nhds

instance : linear_order fs.ι := linear_order_of_STO' well_ordering_rel

def to_pou_fun (i : fs.ι) (x : X) : ℝ :=
fs i x * ∏ᶠ j < i, (1 - fs j x)

lemma to_pou_fun_zero_of_zero {i : fs.ι} {x : X} (h : fs i x = 0) :
  to_pou_fun fs i x = 0 :=
by rw [to_pou_fun, h, zero_mul]

lemma support_to_pou_fun_subset (i : fs.ι) :
  support (to_pou_fun fs i) ⊆ support (fs i) :=
 λ x, mt $ fs.to_pou_fun_zero_of_zero

lemma to_pou_fun_eq_mul_prod (i : fs.ι) (x : X) (t : finset fs.ι)
  (ht : ∀ j < i, fs j x ≠ 0 → j ∈ t) :
  fs.to_pou_fun i x = fs i x * ∏ j in t.filter (< i), (1 - fs j x) :=
begin
  refine congr_arg _ (finprod_cond_eq_prod_of_cond_iff _ (λ j hj, _)),
  rw [ne.def, sub_eq_self] at hj,
  rw [finset.mem_filter, iff.comm, and_iff_right_iff_imp],
  exact flip (ht j) hj
end

lemma sum_to_pou_fun_eq (x : X) :
  ∑ᶠ i, to_pou_fun fs i x = 1 - ∏ᶠ i, (1 - fs i x) :=
begin
  set s := (fs.point_finite x).to_finset,
  have hs : (s : set fs.ι) = {i | fs i x ≠ 0} := finite.coe_to_finset _,
  have A : support (λ i, to_pou_fun fs i x) ⊆ s,
  { rw hs,
    exact λ i hi, fs.support_to_pou_fun_subset i hi },
  have B : mul_support (λ i, 1 - fs i x) ⊆ s,
  { rw [hs, mul_support_one_sub], exact λ i, id },
  rw [finsum_eq_sum_of_support_subset _ A, finprod_eq_prod_of_mul_support_subset _ B,
    finset.prod_one_sub_ordered, sub_sub_cancel],
  refine finset.sum_congr rfl (λ i hi, fs.to_pou_fun_eq_mul_prod _ _ _ (λ j hji hj, _)),
  rwa finite.mem_to_finset
end

lemma exists_finset_to_pou_fun_eventually_eq (i : fs.ι) (x : X) :
  ∃ t : finset fs.ι, fs.to_pou_fun i =ᶠ[𝓝 x] fs i * ∏ j in t.filter (< i), (1 - fs j) :=
begin
  rcases fs.locally_finite x with ⟨U, hU, hf⟩,
  use hf.to_finset,
  filter_upwards [hU],
  intros y hyU,
  simp only [pi.mul_apply, finset.prod_apply],
  apply to_pou_fun_eq_mul_prod,
  intros j hji hj,
  exact hf.mem_to_finset.2 ⟨y, ⟨hj, hyU⟩⟩
end

lemma continuous_to_pou_fun (i : fs.ι) : continuous (fs.to_pou_fun i) :=
begin
  refine ((fs i).continuous.mul $
    continuous_finprod_cond (λ j _, continuous_const.sub (fs j).continuous) _),
  simp only [mul_support_one_sub],
  exact fs.locally_finite
end

def to_partition_of_unity : partition_of_unity X s :=
{ ι := fs.ι,
  to_fun := λ i, ⟨fs.to_pou_fun i, fs.continuous_to_pou_fun i⟩,
  locally_finite' := fs.locally_finite.subset fs.support_to_pou_fun_subset,
  nonneg' := λ i x, mul_nonneg (fs.nonneg i x)
    (finprod_cond_nonneg $ λ j hj, sub_nonneg.2 $ fs.le_one j x),
  sum_eq_one' := λ x hx,
    begin
      simp only [continuous_map.coe_mk, sum_to_pou_fun_eq, sub_eq_self],
      apply finprod_eq_zero (λ i, 1 - fs i x) (fs.ind x hx),
      { simp only [fs.ind_apply x hx, sub_self] },
      { rw mul_support_one_sub, exact fs.point_finite x }
    end,
  sum_le_one' := λ x,
    begin
      simp only [continuous_map.coe_mk, sum_to_pou_fun_eq, sub_le_self_iff],
      exact finprod_nonneg (λ i, sub_nonneg.2 $ fs.le_one i x)
    end }

lemma to_partition_of_unity_apply (i : fs.ι) (x : X) :
  fs.to_partition_of_unity i x = fs i x * ∏ᶠ j < i, (1 - fs j x) :=
rfl

lemma to_partition_of_unity_eq_mul_prod (i : fs.ι) (x : X) (t : finset fs.ι)
  (ht : ∀ j < i, fs j x ≠ 0 → j ∈ t) :
  fs.to_partition_of_unity i x = fs i x * ∏ j in t.filter (< i), (1 - fs j x) :=
fs.to_pou_fun_eq_mul_prod i x t ht

lemma exists_finset_to_partition_of_unity_eventually_eq (i : fs.ι) (x : X) :
  ∃ t : finset fs.ι, fs.to_partition_of_unity i =ᶠ[𝓝 x] fs i * ∏ j in t.filter (< i), (1 - fs j) :=
fs.exists_finset_to_pou_fun_eventually_eq i x

lemma support_to_partition_of_unity_subset (i : fs.ι) :
  support (fs.to_partition_of_unity i) ⊆ support (fs i) :=
 λ x, mt $ fs.to_pou_fun_zero_of_zero

lemma sum_to_partition_of_unity_eq (x : X) :
  ∑ᶠ i, fs.to_partition_of_unity i x = 1 - ∏ᶠ i, (1 - fs i x) :=
fs.sum_to_pou_fun_eq x

lemma is_subordinate.to_partition_of_unity {S : set (set X)} {fs : bump_covering X s}
  (h : fs.is_subordinate S) : fs.to_partition_of_unity.is_subordinate S :=
λ i, (h i).imp $ λ s hs,
  ⟨hs.fst, subset.trans (closure_mono $ fs.support_to_partition_of_unity_subset i) hs.snd⟩

end bump_covering

namespace partition_of_unity

variables {s : set X}

lemma exists_is_subordinate_of_locally_finite {ι : Type u} [normal_space X] (hs : is_closed s)
  (U : ι → set X) (ho : ∀ i, is_open (U i)) (hf : locally_finite U)
  (hU : s ⊆ ⋃ i, U i) : ∃ f : partition_of_unity X s, f.is_subordinate (range U) :=
let ⟨f, hf⟩ := bump_covering.exists_is_subordinate_of_locally_finite hs U ho hf hU
in ⟨f.to_partition_of_unity, hf.to_partition_of_unity⟩

lemma exists_is_subordinate [normal_space X] [paracompact_space X]
  (hs : is_closed s) (U : set (set X)) (ho : ∀ s ∈ U, is_open s) (hU : s ⊆ ⋃₀ U) :
  ∃ f : partition_of_unity X s, f.is_subordinate U :=
let ⟨f, hf⟩ := bump_covering.exists_is_subordinate hs U ho hU
in ⟨f.to_partition_of_unity, hf.to_partition_of_unity⟩

end partition_of_unity
