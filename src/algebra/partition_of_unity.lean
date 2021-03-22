import algebra.big_operators.finprod

universes u v
variables {α : Type u} (R : Type v) [ordered_comm_ring R]

open function set
open_locale big_operators

section finprod

variable {R}

lemma finprod_nonneg {α : Sort*} {f : α → R} (hf : ∀ x, 0 ≤ f x) :
  0 ≤ ∏ᶠ x, f x :=
begin
  rw finprod,
  split_ifs,
  { exact finset.prod_nonneg (λ x _, hf _) },
  { exact zero_le_one }
end

lemma finprod_in_nonneg {p : α → Prop} {f : α → R} (hf : ∀ x, p x → 0 ≤ f x) :
  0 ≤ ∏ᶠ x (h : p x), f x :=
finprod_nonneg $ λ x, finprod_nonneg $ hf x

lemma finprod_eq_zero {f : α → R} {x : α}
  (hx : f x = 0) (hf : finite (mul_support f)) :
  ∏ᶠ x, f x = 0 :=
begin
  nontriviality,
  rw [finprod_eq_prod f hf],
  refine finset.prod_eq_zero (hf.mem_to_finset.2 _) hx,
  simp [hx]
end

end finprod

noncomputable theory

structure partition_of_unity (s : set α) :=
(ι : Type u)
(to_fun : ι → α → R)
(point_finite' : ∀ x, finite {i | to_fun i x ≠ 0})
(nonneg' : ∀ i x, 0 ≤ to_fun i x)
(sum_eq_one' : ∀ x ∈ s, ∑ᶠ i, to_fun i x = 1)
(sum_le_one' : ∀ x, ∑ᶠ i, to_fun i x ≤ 1)

namespace partition_of_unity

section gen

variables {R} {ι : Type u} [linear_order ι]

def gen_fun (f : ι → α → R) (i : ι) (x : α) : R :=
f i x * ∏ᶠ j < i, (1 - f j x)

lemma gen_fun_nonneg (f : ι → α → R) (h₀ : ∀ i, 0 ≤ f i) (h₁ : ∀ i, f i ≤ 1) (i : ι) (x : α) :
  0 ≤ gen_fun f i x :=
mul_nonneg (h₀ i x) $ finprod_in_nonneg $ λ j hj, sub_nonneg.2 $ h₁ _ _

lemma gen_fun_zero_of_zero (f : ι → α → R) {i : ι} {x : α} (h : f i x = 0) :
  gen_fun f i x = 0 :=
by rw [gen_fun, h, zero_mul]

lemma sum_gen_fun_eq (f : ι → α → R) (x : α) (h : finite {j | f j x ≠ 0}) :
  ∑ᶠ i, gen_fun f i x = 1 - ∏ᶠ i, (1 - f i x) :=
begin
  set s := h.to_finset,
  have A : support (λ i, gen_fun f i x) ⊆ s,
  { rw h.coe_to_finset,
    exact λ i, mt (gen_fun_zero_of_zero f) },
  have B : mul_support (λ i, 1 - f i x) ⊆ s,
  { rw [h.coe_to_finset, mul_support_one_sub],
    exact λ i, id },
  rw [finsum_eq_sum_of_support_subset _ A, finprod_eq_prod_of_mul_support_subset _ B,
    finset.prod_one_sub_ordered, sub_sub_cancel],
  refine finset.sum_congr rfl (λ i hi, _),
  simp only [gen_fun],
  refine congr_arg _ (finprod_in_eq_prod_of_mem_iff _ _),
  simp { contextual := tt }
end

lemma sum_gen_fun_of_eq_one (f : ι → α → R) (x : α) (h : finite {j | f j x ≠ 0})
  (h₁ : ∃ i, f i x = 1) :
  ∑ᶠ i, gen_fun f i x = 1 :=
begin
  rcases h₁ with ⟨i, hi⟩,
  rw [sum_gen_fun_eq f x h, sub_eq_self],
  exact finprod_eq_zero (sub_eq_zero.2 hi.symm) (h.subset (mul_support_one_sub (λ i, f i x)).le)
end

lemma sum_gen_fun_le_one (f : ι → α → R) (x : α) (h : finite {j | f j x ≠ 0}) (h₁ : f ≤ 1) :
  ∑ᶠ i, gen_fun f i x ≤ 1 :=
begin
  rw [sum_gen_fun_eq f x h, sub_le_self_iff],
  exact finprod_nonneg (λ i, sub_nonneg.2 (h₁ _ _))
end

def of_gen_fun (f : ι → α → R) (h₀ : 0 ≤ f) (h₁ : f ≤ 1) (h : ∀ x, finite {i | f i x ≠ 0}) (s : set α) (hs : ∀ x ∈ s, ∃ i, f i x = 1) :
  partition_of_unity R s :=
{ ι := ι,
  to_fun := gen_fun f,
  point_finite' := λ x, (h x).subset $ λ i, mt (gen_fun_zero_of_zero _),
  nonneg' := gen_fun_nonneg _ h₀ h₁,
  sum_eq_one' := λ x hx, sum_gen_fun_of_eq_one _ _ (h _) (hs x hx),
  sum_le_one' := λ x, sum_gen_fun_le_one _ _ (h _) h₁ }

end gen

end partition_of_unity
