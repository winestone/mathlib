import data.polynomial.ring_division
import algebra.big_operators.nat_antidiagonal
import analysis.complex.polynomial

namespace polynomial

variables {R : Type*} [semiring R] (p : polynomial R)

noncomputable def reverse' := p.reverse * X ^ p.nat_trailing_degree

lemma reverse'_zero : (0 : polynomial R).reverse' = 0 := rfl

lemma reverse'_nat_degree : p.reverse'.nat_degree = p.nat_degree :=
begin
  by_cases hp : p = 0,
  { rw [hp, reverse'_zero] },
  by_cases hR : nontrivial R,
  { haveI := hR,
    rw [reverse', nat_degree_mul', reverse_nat_degree, nat_degree_X_pow,
        nat.sub_add_cancel p.nat_trailing_degree_le_nat_degree],
    rwa [leading_coeff_X_pow, mul_one, reverse_leading_coeff, ne, trailing_coeff_eq_zero] },
  { haveI := not_nontrivial_iff_subsingleton.mp hR,
    exact congr_arg nat_degree (subsingleton.elim p.reverse' p) },
end

lemma coeff_mul_X_pow' {R : Type*} [semiring R] (p : polynomial R) (n : ℕ) (d : ℕ) :
  (p * X ^ n).coeff d = ite (n ≤ d) (p.coeff (d - n)) 0 :=
begin
  by_cases h : n ≤ d,
  { rw [if_pos h, ←@nat.sub_add_cancel d n h, coeff_mul_X_pow, nat.add_sub_cancel] },
  { rw [if_neg h, coeff_mul],
    refine finset.sum_eq_zero (λ x hx, _),
    rw [coeff_X_pow, if_neg, mul_zero],
    exact ne_of_lt (lt_of_le_of_lt (nat.le_of_add_le_right
      (le_of_eq (finset.nat.mem_antidiagonal.mp hx))) (not_le.mp h)) },
end

lemma nat_trailing_degree_mul_X_pow {p : polynomial R} (hp : p ≠ 0) (n : ℕ) :
  (p * X ^ n).nat_trailing_degree = p.nat_trailing_degree + n :=
begin
  apply le_antisymm,
  { apply nat_trailing_degree_le_of_ne_zero,
    intro h,
    apply mt trailing_coeff_eq_zero.mp hp,
    rwa [trailing_coeff, ←coeff_mul_X_pow] },
  { rw [nat_trailing_degree_eq_support_min' (λ h, hp (mul_X_pow_eq_zero h)), finset.le_min'_iff],
    intros y hy,
    have key : n ≤ y,
    { rw [mem_support_iff_coeff_ne_zero, coeff_mul_X_pow'] at hy,
      exact by_contra (λ h, hy (if_neg h)) },
    rw [mem_support_iff_coeff_ne_zero, coeff_mul_X_pow', if_pos key] at hy,
    exact (nat.add_le_to_le_sub _ key).mpr (nat_trailing_degree_le_of_ne_zero hy) },
end

lemma reverse'_nat_trailing_degree : p.reverse'.nat_trailing_degree = p.nat_trailing_degree :=
begin
  by_cases hp : p = 0,
  { rw [hp, reverse'_zero] },
  { rw [reverse', nat_trailing_degree_mul_X_pow ((mt reverse_eq_zero.mp) hp),
        reverse_nat_trailing_degree, zero_add] },
end

lemma coeff_reverse' (n : ℕ) :
  p.reverse'.coeff n = p.coeff (rev_at (p.nat_degree + p.nat_trailing_degree) n) :=
begin
  by_cases h2 : p.nat_degree < n,
  { rw [coeff_eq_zero_of_nat_degree_lt (by rwa reverse'_nat_degree)],
    by_cases h1 : n ≤ p.nat_degree + p.nat_trailing_degree,
    { rw [rev_at_le h1, coeff_eq_zero_of_lt_nat_trailing_degree],
      exact (nat.sub_lt_left_iff_lt_add h1).mpr (nat.add_lt_add_right h2 _) },
    { rw [←rev_at_fun_eq, rev_at_fun, if_neg h1, coeff_eq_zero_of_nat_degree_lt h2] } },
  rw not_lt at h2,
  rw [rev_at_le (h2.trans (nat.le_add_right _ _))],
  by_cases h3 : p.nat_trailing_degree ≤ n,
  { rw [←nat.sub_add_eq_add_sub h2, ←nat.sub_sub_assoc h2 h3, reverse', coeff_mul_X_pow',
        if_pos h3, coeff_reverse, rev_at_le ((nat.sub_le_self _ _).trans h2)] },
  rw not_le at h3,
  rw coeff_eq_zero_of_nat_degree_lt (nat.lt_sub_right_iff_add_lt.mpr (nat.add_lt_add_left h3 _)),
  exact coeff_eq_zero_of_lt_nat_trailing_degree (by rwa reverse'_nat_trailing_degree),
end

lemma reverse'_reverse' : p.reverse'.reverse' = p :=
polynomial.ext (λ n, by rw [coeff_reverse', coeff_reverse',
  reverse'_nat_degree, reverse'_nat_trailing_degree, rev_at_invol])

lemma reverse'_eq_zero : p.reverse' = 0 ↔ p = 0 :=
⟨λ h, by rw [←p.reverse'_reverse', h, reverse'_zero], λ h, by rw [h, reverse'_zero]⟩

lemma reverse'_trailing_coeff : p.reverse'.trailing_coeff = p.leading_coeff :=
by rw [leading_coeff, trailing_coeff, reverse'_nat_trailing_degree, coeff_reverse',
  rev_at_le (nat.le_add_left _ _), nat.add_sub_cancel]

lemma reverse'_leading_coeff : p.reverse'.leading_coeff = p.trailing_coeff :=
by rw [←p.reverse'_reverse', reverse'_trailing_coeff, p.reverse'_reverse']

lemma reverse'_mul_of_domain {R : Type*} [integral_domain R] (p q : polynomial R) :
  (p * q).reverse' = p.reverse' * q.reverse' :=
begin
  by_cases hp : p = 0,
  { rw [hp, zero_mul, reverse'_zero, zero_mul] },
  by_cases hq : q = 0,
  { rw [hq, mul_zero, reverse'_zero, mul_zero] },
  rw [reverse', reverse', reverse', reverse_mul_of_domain, nat_trailing_degree_mul hp hq, pow_add],
  ring,
end

lemma reverse'_neg {R : Type*} [ring R] (p : polynomial R) : (-p).reverse' = -(p.reverse') :=
by rw [reverse', reverse', reverse_neg, nat_trailing_degree_neg, neg_mul_eq_neg_mul]

lemma reverse'_irreducible_test {R : Type*} [integral_domain R] {f : polynomial R}
  (h1 : ¬ is_unit f)
  (h2 : ∀ k, f * f.reverse' = k * k.reverse' → k = f ∨ k = -f ∨ k = f.reverse' ∨ k = -f.reverse')
  (h3 : ∀ g, g ∣ f → g ∣ f.reverse' → is_unit g) : irreducible f :=
begin
  split,
  { exact h1 },
  { intros g h fgh,
    let k := g * h.reverse',
    have key : f * f.reverse' = k * k.reverse',
    { rw [fgh, reverse'_mul_of_domain, reverse'_mul_of_domain, reverse'_reverse',
          mul_assoc, mul_comm h, mul_comm g.reverse', mul_assoc, ←mul_assoc] },
    have g_dvd_f : g ∣ f,
    { rw fgh,
      exact dvd_mul_right g h },
    have h_dvd_f : h ∣ f,
    { rw fgh,
      exact dvd_mul_left h g },
    have g_dvd_k : g ∣ k,
    { exact dvd_mul_right g h.reverse' },
    have h_dvd_k_rev : h ∣ k.reverse',
    { rw [reverse'_mul_of_domain, reverse'_reverse'],
      exact dvd_mul_left h g.reverse' },
    have hk := h2 k key,
    rcases hk with hk | hk | hk | hk,
    { exact or.inr (h3 h h_dvd_f (by rwa ← hk)) },
    { exact or.inr (h3 h h_dvd_f (by rwa [eq_neg_iff_eq_neg.mp hk, reverse'_neg, dvd_neg])) },
    { exact or.inl (h3 g g_dvd_f (by rwa ← hk)) },
    { exact or.inl (h3 g g_dvd_f (by rwa [eq_neg_iff_eq_neg.mp hk, dvd_neg])) } },
end

def norm2 := p.support.sum (λ k, (p.coeff k) ^ 2)

lemma norm2_eq_sum_of_support {s : finset ℕ}
  (h : p.support ⊆ s) : p.norm2 = s.sum (λ k, (p.coeff k) ^ 2) :=
finset.sum_subset h (λ k h1 h2, by rw [not_mem_support_iff_coeff_zero.mp h2, pow_two, zero_mul])

lemma norm2_eq_mul_reverse_coeff :
  p.norm2 = (p * p.reverse').coeff (p.nat_degree + p.nat_trailing_degree) :=
begin
  have h : p.support ⊆ finset.range (p.nat_degree + p.nat_trailing_degree).succ :=
  λ x hx, finset.mem_range_succ_iff.mpr ((le_nat_degree_of_ne_zero
    (mem_support_iff_coeff_ne_zero.mp hx)).trans (nat.le_add_right _ _)),
  rw [eq_comm, p.norm2_eq_sum_of_support h, coeff_mul,
      finset.nat.sum_antidiagonal_eq_sum_range_succ_mk],
  apply finset.sum_congr rfl,
  intros k hk,
  rw [pow_two, coeff_reverse', ←rev_at_le (finset.mem_range_succ_iff.mp hk), rev_at_invol],
end

lemma nat_degree_mul_reverse' {R : Type*} [integral_domain R] (p : polynomial R) :
  (p * p.reverse').nat_degree = 2 * p.nat_degree :=
begin
  by_cases hp : p = 0,
  { rw [hp, zero_mul, nat_degree_zero, mul_zero] },
  { rw [nat_degree_mul hp (mt p.reverse'_eq_zero.mp hp), reverse'_nat_degree, two_mul] },
end

lemma nat_trailing_degree_mul_reverse' {R : Type*} [integral_domain R] (p : polynomial R) :
  (p * p.reverse').nat_trailing_degree = 2 * p.nat_trailing_degree :=
begin
  by_cases hp : p = 0,
  { rw [hp, zero_mul, nat_trailing_degree_zero, mul_zero] },
  { rw [nat_trailing_degree_mul hp (mt p.reverse'_eq_zero.mp hp),
        reverse'_nat_trailing_degree, two_mul] },
end

lemma the_key {p : polynomial ℤ} (hp : p.norm2 ≤ 3) :
  ∀ q, p * p.reverse' = q * q.reverse' → p = q ∨ p = -q ∨ p = q.reverse' ∨ p = -(q.reverse') :=
begin
  intros q hpq,
  have hpq1 : p.nat_degree = q.nat_degree,
  { refine mul_left_cancel' two_ne_zero _,
    rw [←nat_degree_mul_reverse', ←nat_degree_mul_reverse', hpq] },
  have hpq2 : p.nat_trailing_degree = q.nat_trailing_degree,
  { refine mul_left_cancel' two_ne_zero _,
    rw [←nat_trailing_degree_mul_reverse', ←nat_trailing_degree_mul_reverse', hpq] },
  have hpq3 : p.norm2 = q.norm2,
  { rw [norm2_eq_mul_reverse_coeff, norm2_eq_mul_reverse_coeff, hpq, hpq1, hpq2] },
  have hq : q.norm2 ≤ 3,
  { rwa ← hpq3 },
  have hpq4 : p.leading_coeff * p.trailing_coeff = q.leading_coeff * q.trailing_coeff,
  { rw [←reverse'_leading_coeff, ←reverse'_leading_coeff,
        ←leading_coeff_mul, ←leading_coeff_mul, hpq] },
  --step 1' : show that `p.leading_coeff = q.leading_coeff` (negate `q` if necessary)
  --step 2' : show that `p.trailing_coeff = q.trailing_coeff` (follows from previous)
  --step 3' : reduce to the case of a trinomial
  --step 4' : show that the degree of the middle term matches (reverse `q` if necessary)
  --step 5' : finish the proof

  --step 1 : show that `p.norm2 ≤ 3` implies that `p.coeff k ^ 2 ≤ 1`
  --step 2 : show that if `p.coeff k ^ 2 ≤ 1` then `p.norm2 = p.support.card`
  --step 3 : we have `p.support.card = q.support.card ≤ 3`, so do proceed case-by-case
end

/- OLD STUFF -/

lemma norm2_zero : (0 : polynomial R).norm2 = 0 := rfl

lemma norm2_monomial (k : ℕ) (a : R) : (monomial k a).norm2 = a ^ 2 :=
by rw [norm2_eq_sum_of_support _ (support_monomial' k a), finset.sum_singleton,
  coeff_monomial, if_pos rfl]

lemma norm2_eq_zero {R : Type*} [linear_ordered_ring R] [no_zero_divisors R] {p : polynomial R} :
  norm2 p = 0 ↔ p = 0 :=
begin
  split,
  { rw [norm2, finset.sum_eq_zero_iff_of_nonneg (λ k hk, pow_two_nonneg (p.coeff k))],
    simp_rw [pow_eq_zero_iff zero_lt_two, mem_support_iff_coeff_ne_zero, not_imp_self],
    rw polynomial.ext_iff,
    exact id },
  { intro p,
    rw [p, norm2_zero] },
end

lemma card_support_le_norm2 (p : polynomial ℤ) : ↑p.support.card ≤ p.norm2 :=
begin
  rw [←int.nat_cast_eq_coe_nat, ←ring_hom.eq_nat_cast (nat.cast_ring_hom ℤ),
      finset.card_eq_sum_ones, ring_hom.map_sum],
  apply finset.sum_le_sum,
  intros x hx,
  rw [ring_hom.map_one, ←int.sub_one_lt_iff, sub_self, lt_iff_le_and_ne],
  exact ⟨pow_two_nonneg (p.coeff x), (pow_ne_zero 2 (mem_support_iff_coeff_ne_zero.mp hx)).symm⟩,
end

lemma int_lemma {a : ℤ} (h1 : a ≠ 0) (h2 : a ^ 2 ≤ 3) : a ^ 2 = 1 :=
begin
  rw [←int.nat_abs_pow_two a, ←int.coe_nat_pow, ←int.coe_nat_one, int.coe_nat_inj',
      pow_eq_one_iff two_ne_zero],
  apply le_antisymm,
  { rwa [←nat.lt_succ_iff, ←nat.pow_lt_iff_lt_left one_le_two, ←int.coe_nat_lt_coe_nat_iff,
        int.coe_nat_pow, int.nat_abs_pow_two, ←int.le_sub_one_iff] },
  { apply nat.one_le_of_lt,
    rwa [zero_lt_iff, ne, int.nat_abs_eq_zero] },
end

lemma norm2_nonneg {R : Type*} [linear_ordered_ring R] (p : polynomial R) :
  0 ≤ norm2 p :=
finset.sum_nonneg (λ _ _, pow_two_nonneg _)

/- could probably clean up proof -/
lemma coeff_sq_le_norm2 {R : Type*} [linear_ordered_ring R] (p : polynomial R) (k : ℕ) :
  p.coeff k ^ 2 ≤ p.norm2 :=
begin
  rw [norm2, ←finset.sum_insert_of_eq_zero_if_not_mem],
  exact le_trans (le_of_eq (finset.sum_singleton.symm)) (finset.sum_le_sum_of_subset_of_nonneg
    (finset.singleton_subset_iff.mpr (finset.mem_insert_self k p.support))
    (λ j _ _, pow_two_nonneg (p.coeff j))),
  exact λ h, (pow_eq_zero_iff zero_lt_two).mpr (not_mem_support_iff_coeff_zero.mp h),
end

lemma coeff_sq_le_one_of_norm2_le_three {p : polynomial ℤ} (hp : p.norm2 ≤ 3) {k : ℕ}
  (hk : k ∈ p.support) : p.coeff k ^ 2 = 1 :=
int_lemma (mem_support_iff_coeff_ne_zero.mp hk) (ge_trans hp (le_trans
  (le_of_eq finset.sum_singleton.symm) (finset.sum_le_sum_of_subset_of_nonneg
  (finset.singleton_subset_iff.mpr hk) (λ j _ _, pow_two_nonneg (p.coeff j)))))

end polynomial
