import data.polynomial.reverse
import field_theory.polynomial_galois_group
import analysis.complex.polynomial
import algebra.big_operators.nat_antidiagonal

namespace polynomial

lemma reverse_nat_degree_le {R : Type*} [semiring R] (p : polynomial R) :
  p.reverse.nat_degree ≤ p.nat_degree :=
begin
  rw [nat_degree_le_iff_degree_le, degree_le_iff_coeff_zero],
  intros n hn,
  rw with_bot.coe_lt_coe at hn,
  rw [reverse, coeff_reflect, rev_at, function.embedding.coe_fn_mk,
      if_neg ((lt_iff_not_ge _ _).mp hn), coeff_eq_zero_of_nat_degree_lt hn],
end

lemma reverse_nat_degree_eq {R : Type*} [semiring R] {p : polynomial R} (hp : p.coeff 0 ≠ 0) :
  p.reverse.nat_degree = p.nat_degree :=
begin
  apply le_antisymm,
  { exact reverse_nat_degree_le p },
  { refine not_lt.mp (mt coeff_eq_zero_of_nat_degree_lt _),
    rwa [reverse, coeff_reflect, rev_at_le (le_refl p.nat_degree), nat.sub_self] },
end

lemma reverse_reverse {R : Type*} [semiring R] {p : polynomial R} (hp : p.coeff 0 ≠ 0) :
  p.reverse.reverse = p :=
begin
  ext n,
  rw [reverse, reverse_nat_degree_eq hp, reverse, coeff_reflect, coeff_reflect, rev_at_invol],
end

lemma reverse_X {R : Type*} [semiring R] : (X : polynomial R).reverse = 1 :=
begin
  by_cases h : nontrivial R,
  { haveI := h,
    rw [reverse, nat_degree_X, ←pow_one X, reflect_monomial,
        rev_at_le (le_refl 1), nat.sub_self, pow_zero] },
  haveI := (not_nontrivial_iff_subsingleton.mp h),
  exact polynomial.ext (λ n, subsingleton.elim _ _),
end

lemma reverse_coeff_zero {R : Type*} [semiring R] (p : polynomial R) :
  p.reverse.coeff 0 = p.leading_coeff :=
by rw [reverse, coeff_reflect, rev_at_le (zero_le _), nat.sub_zero, leading_coeff]

lemma reverse_eval_zero {R : Type*} [semiring R] (p : polynomial R) :
  p.reverse.eval 0 = p.leading_coeff :=
by rw [←coeff_zero_eq_eval_zero, reverse_coeff_zero]

lemma reverse_leading_coeff {R : Type*} [semiring R] {p : polynomial R} (hp : p.coeff 0 ≠ 0) :
  p.reverse.leading_coeff = p.coeff 0 :=
by rw [leading_coeff, reverse_nat_degree_eq hp, reverse, coeff_reflect,
  rev_at_le (le_refl _), nat.sub_self]

lemma key_lemma {R : Type*} [integral_domain R] {f : polynomial R}
  (h1 : f.eval 0 ≠ 0)
  (h2 : ¬ is_unit f)
  (h3 : ∀ k, f * f.reverse = k * k.reverse → k = f ∨ k = -f ∨ k = f.reverse ∨ k = -(f.reverse))
  (h4 : ∀ g, g ∣ f → g ∣ f.reverse → is_unit g) : irreducible f :=
begin
  split,
  { exact h2 },
  { intros g h fgh,
    rw [fgh, eval_mul, ←coeff_zero_eq_eval_zero, ←coeff_zero_eq_eval_zero, mul_ne_zero_iff] at h1,
    let k := g * h.reverse,
    have key : f * f.reverse = k * k.reverse,
    { rw [fgh, reverse_mul_of_domain, reverse_mul_of_domain, mul_assoc, mul_comm h,
          mul_comm g.reverse, mul_assoc, ←mul_assoc, reverse_reverse h1.2] },
    have g_dvd_f : g ∣ f,
    { rw fgh,
      exact dvd_mul_right g h },
    have g_dvd_k : g ∣ k,
    { exact dvd_mul_right g h.reverse },
    have h_dvd_f : h ∣ f,
    { rw fgh,
      exact dvd_mul_left h g },
    have h_dvd_k_rev : h ∣ k.reverse,
    { rw [reverse_mul_of_domain, reverse_reverse h1.2],
      exact dvd_mul_left h g.reverse },
    have hk := h3 k key,
    rcases hk with hk | hk | hk | hk,
    { exact or.inr (h4 h h_dvd_f (by rwa ← hk)) },
    { exact or.inr (h4 h h_dvd_f (by rwa [eq_neg_iff_eq_neg.mp hk, reverse_neg, dvd_neg])) },
    { exact or.inl (h4 g g_dvd_f (by rwa ← hk)) },
    { exact or.inl (h4 g g_dvd_f (by rwa [eq_neg_iff_eq_neg.mp hk, dvd_neg])) } },
end

lemma is_unit_neg {R : Type*} [ring R] (u : R) : is_unit (-u) ↔ is_unit u :=
⟨λ h, Exists.cases_on h (λ v hv, ⟨-v, v.coe_neg.trans (neg_eq_iff_neg_eq.mp hv.symm)⟩),
  λ h, Exists.cases_on h (λ v hv, ⟨-v, v.coe_neg.trans (congr_arg _ hv)⟩)⟩

lemma monomial_eq_zero {R : Type*} [semiring R] {n : ℕ} {a : R} :
  monomial n a = 0 ↔ a = 0 :=
⟨λ h, by rw [←leading_coeff_monomial a n, h, leading_coeff_zero],
  λ h, by rw [h, monomial_zero_right]⟩

section unit_trinomial

def norm2 {R : Type*} [semiring R] (p : polynomial R) : R :=
p.support.sum (λ k, (p.coeff k) ^ 2)

lemma norm2_zero {R : Type*} [semiring R] : (0 : polynomial R).norm2 = 0 :=
by rw [norm2, support_zero, finset.sum_empty]

lemma norm2_eq_sum_of_support {R : Type*} [semiring R] {p : polynomial R} {s : finset ℕ}
  (h : p.support ⊆ s) : p.norm2 = s.sum (λ k, (p.coeff k) ^ 2) :=
finset.sum_subset h (λ k h1 h2, by rw [not_mem_support_iff_coeff_zero.mp h2, pow_two, zero_mul])

lemma norm2_monomial {R : Type*} [semiring R] {k : ℕ} {a : R} :
  (monomial k a).norm2 = a ^ 2 :=
by rw [norm2_eq_sum_of_support (support_monomial' k a),
  finset.sum_singleton, coeff_monomial, if_pos rfl]

lemma norm2_eq_sum_range {R : Type*} [semiring R] (p : polynomial R) :
  p.norm2 = (finset.range p.nat_degree.succ).sum (λ k, (p.coeff k) ^ 2) :=
@sum_over_range R _ _ _ p (λ _ a, a ^ 2) (λ n, zero_pow zero_lt_two)

lemma norm2_eq_mul_reverse_coeff {R : Type*} [semiring R] (p : polynomial R) :
  p.norm2 = (p * p.reverse).coeff p.nat_degree :=
begin
  rw [eq_comm, norm2_eq_sum_range, coeff_mul, finset.nat.sum_antidiagonal_eq_sum_range_succ_mk],
  apply finset.sum_congr rfl,
  intros k hk,
  rw [pow_two, reverse, coeff_reflect, rev_at_le (nat.sub_le_self _ _),
      nat.sub_sub_self (finset.mem_range_succ_iff.mp hk)],
end

/-lemma support_card_le_one {R : Type*} [semiring R] {p : polynomial R} :
  p.support.card ≤ 1 ↔ ∃ k a, p = monomial k a :=
begin
  split,
  { intro hp,
    interval_cases p.support.card with h,
    { exact ⟨0, 0, (finsupp.card_support_eq_zero.mp h).trans (monomial_zero_right 0).symm⟩ },
    { cases (finsupp.card_support_eq_one.mp h) with k hk,
      exact ⟨k, p.coeff k, hk.2⟩ } },
  { intro hp,
    obtain ⟨k, a, rfl⟩ := hp,
    exact finset.card_le_of_subset (support_monomial' k a) },
end-/

lemma norm2_induction {R : Type*} [semiring R] (p : polynomial R) :
  norm2 p = p.leading_coeff ^ 2 + norm2 p.erase_lead :=
begin
  by_cases hp : p = 0,
  { rw [hp, erase_lead_zero, norm2_zero, add_zero, leading_coeff_zero, pow_two, mul_zero] },
  { rw [norm2, ←finset.insert_erase (nat_degree_mem_support_of_nonzero hp), norm2,
        finset.sum_insert (finset.not_mem_erase p.nat_degree p.support), erase_lead_support],
    exact congr_arg (has_add.add _) (finset.sum_congr rfl (λ k hk, congr_arg (λ a, a ^ 2)
      (erase_lead_coeff_of_ne k (finset.ne_of_mem_erase hk)).symm)) },
end

lemma norm2_nonneg {R : Type*} [linear_ordered_ring R] (p : polynomial R) :
  0 ≤ norm2 p :=
finset.sum_nonneg (λ _ _, pow_two_nonneg _)

example (P : Prop) : (¬ P → P) → P := not_imp_self.mp

lemma norm2_eq_zero {R : Type*} [linear_ordered_ring R] [no_zero_divisors R] {p : polynomial R} :
  norm2 p = 0 ↔ p = 0 :=
begin
  split,
  { rw [norm2, finset.sum_eq_zero_iff_of_nonneg (λ k hk, pow_two_nonneg (p.coeff k))],
    simp only [not_imp_self, pow_eq_zero_iff zero_lt_two, mem_support_iff_coeff_ne_zero],
    simp only [polynomial.ext_iff],
    exact id },
  { intro p,
    rw [p, norm2_zero] },
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

lemma norm2_le_three {p : polynomial ℤ} (h1 : p.norm2 ≠ 0) (h2 : p.norm2 ≤ 3) :
  p.erase_lead.norm2 = p.norm2 - 1 ∧
  ∃ (u : units ℤ), p = p.erase_lead + monomial p.nat_degree ↑u :=
begin
  have key := p.norm2_induction,
  have key' : p.leading_coeff ^ 2 = 1,
  { apply int_lemma (mt leading_coeff_eq_zero.mp (mt norm2_eq_zero.mpr h1)),
    rw key at h2,
    exact (le_add_of_nonneg_right p.erase_lead.norm2_nonneg).trans h2 },
  split,
  { rw [key, key', add_sub_cancel'] },
  { rw [pow_two] at key',
    exact ⟨units.mk _ _ key' key', p.erase_lead_add_monomial_nat_degree_leading_coeff.symm⟩ },
end

lemma norm2_eq_one {p : polynomial ℤ} :
  norm2 p = 1 ↔ ∃ k (u : units ℤ), p = monomial k ↑u :=
begin
  split,
  { intro h,
    obtain ⟨h1, u, h2⟩ :=
      norm2_le_three (ne_of_eq_of_ne h (by norm_num)) (h.trans_le (by norm_num)),
    rw [h, show (1 : ℤ) - (1 : ℤ) = (0 : ℤ), by norm_num, norm2_eq_zero] at h1,
    rw [h1, zero_add] at h2,
    exact ⟨p.nat_degree, u, h2⟩ },
  { rintros ⟨k, u, rfl⟩,
    rw [norm2_monomial, ←units.coe_pow, int.units_pow_two, units.coe_one] },
end

example {i j : ℕ} {a b : ℤ} : (monomial i a + monomial j b).support ⊆ {i, j} :=
begin
  refine finset.subset.trans finsupp.support_add _,
  have key := finset.union_subset_union (support_monomial' i a) (support_monomial' j b),
  -- this doesn't work: apply finset.subset.trans key,
  -- this doesn't work: refine finset.subset.trans key _,
  have key' : ({i} : finset ℕ) ∪ ({j} : finset ℕ) ⊆ ({i, j} : finset ℕ),
  { apply finset.union_subset,
    all_goals { rw [finset.singleton_subset_iff, finset.mem_insert] },
    exact or.inl rfl,
    exact or.inr (finset.mem_singleton_self j) },
  have key'' := finset.subset.trans key key',
  exact key'',
end

lemma norm2_eq_two {p : polynomial ℤ} :
  norm2 p = 2 ↔ ∃ k m (u v : units ℤ), k < m ∧ p = monomial k ↑u + monomial m ↑v :=
begin
  split,
  { intro h,
    obtain ⟨h1, v, h2⟩ :=
      norm2_le_three (ne_of_eq_of_ne h (by norm_num)) (h.trans_le (by norm_num)),
    rw [h, show (2 : ℤ) - (1 : ℤ) = (1 : ℤ), by norm_num, norm2_eq_one] at h1,
    obtain ⟨k, u, h1⟩ := h1,
    rw h1 at h2,
    refine ⟨k, p.nat_degree, u, v, _, h2⟩,
    apply lt_of_le_of_ne,
    { rw [←nat_degree_monomial k ↑u u.ne_zero, ←h1],
      exact erase_lead_nat_degree_le },
    { intro h3,
      rw [←h3, ←monomial_add] at h2,
      rw [h2, erase_lead_monomial, eq_comm, monomial_eq_zero] at h1,
      exact u.ne_zero h1 } },
  { rintros ⟨k, m, u, v, h, rfl⟩,
    have key : (monomial k ↑u + monomial m ↑v).support ⊆ ({k, m} : finset ℕ),
    { --refine finset.subset.trans finsupp.support_add _,
      have key''' : ({k} : finset ℕ) ∪ ({m} : finset ℕ) ⊆ ({k, m} : finset ℕ),
      { apply finset.union_subset,
        all_goals { rw [finset.singleton_subset_iff, finset.mem_insert] },
        exact or.inl rfl,
        exact or.inr (finset.mem_singleton_self m) },
      have key'' := finset.subset.trans (finset.union_subset_union
        (support_monomial' k (↑u : ℤ)) (support_monomial' m (↑v : ℤ))) key''',
      exact finset.subset.trans finsupp.support_add key'',
      --convert key'',
       },
    rw [norm2_eq_sum_of_support key, finset.sum_insert, finset.sum_singleton],
    simp only [coeff_add, coeff_monomial],
    rw [if_neg (ne_of_lt h), if_neg (ne_of_gt h), if_pos rfl, if_pos rfl, add_zero, zero_add],
    rw [←units.coe_pow, ←units.coe_pow, int.units_pow_two, int.units_pow_two],
    refl,
    exact mt finset.mem_singleton.mp (ne_of_lt h) },
end


lemma norm2_eq_three {p : polynomial ℤ} :
  norm2 p = 3 ↔
  ∃ k m n (u v w : units ℤ), k < m ∧ m < n ∧ p = monomial k ↑u + monomial m ↑v + monomial n ↑w :=
begin
  split,
  { intro h,
    obtain ⟨h1, w, h2⟩ :=
      norm2_le_three (ne_of_eq_of_ne h (by norm_num)) (h.trans_le (by norm_num)),
    rw [h, show (3 : ℤ) - (1 : ℤ) = (2 : ℤ), by norm_num, norm2_eq_two] at h1,
    obtain ⟨k, m, u, v, h0, h1⟩ := h1,
    rw h1 at h2,
    refine ⟨k, m, p.nat_degree, u, v, w, h0, _, h2⟩,
    apply lt_of_le_of_ne,
    { have key : (monomial k ↑u + monomial m ↑v).nat_degree = m,
      { apply nat_degree_eq_of_degree_eq_some,
        rw [degree_add_eq_right_of_degree_lt, degree_monomial m v.ne_zero],
        rwa [degree_monomial k u.ne_zero, degree_monomial m v.ne_zero, with_bot.coe_lt_coe] },
      rw [←key, ←h1],
      exact erase_lead_nat_degree_le },
    { intro h3,
      rw [←h3, add_assoc, ←monomial_add] at h2,
      rw [h2] at h1,
      sorry, } },
  { rintros ⟨k, m, n, u, v, w, h1, h2, rfl⟩,
    sorry, },
end

lemma the_key {p : polynomial ℤ} (hp : p.norm2 ≤ 3) :
  ∀ q, p * p.reverse = q * q.reverse → p = q ∨ p = -q ∨ p = q.reverse ∨ p = -(q.reverse) :=
begin
  rw ← int.lt_add_one_iff at hp,
  have hp' := norm2_nonneg p,
  interval_cases using hp' hp,
  { intros q hq, },
end

end unit_trinomial

noncomputable def selmer (n : ℕ) : polynomial ℤ := X ^ n - X - 1

lemma selmer.zero : selmer 0 = -X :=
by rw [selmer, pow_zero, sub_sub, add_comm, ←sub_sub, sub_self, zero_sub]

lemma selmer.one : selmer 1 = -1 :=
by rw [selmer, pow_one, sub_self, zero_sub]

lemma selmer.degree {n : ℕ} (hn : 1 < n) : (selmer n).degree = n :=
begin
  rw [selmer, sub_sub, degree_sub_eq_left_of_degree_lt, degree_X_pow],
  rwa [degree_X_pow, ←C_1, degree_X_add_C, ←with_bot.coe_one, with_bot.coe_lt_coe],
end

lemma selmer.nat_degree {n : ℕ} (hn : 1 < n) : (selmer n).nat_degree = n :=
by rwa [←degree_eq_iff_nat_degree_eq_of_pos (zero_lt_one.trans hn), selmer.degree]

lemma selmer.leading_coeff {n : ℕ} (hn : 1 < n) : (selmer n).leading_coeff = 1 :=
by rw [leading_coeff, selmer.nat_degree hn, selmer, coeff_sub, coeff_sub, coeff_X_pow_self,
  coeff_X, coeff_one, if_neg (ne_of_lt hn), if_neg (ne_zero_of_lt hn).symm, sub_zero, sub_zero]

lemma selmer.monic {n : ℕ} (hn : 1 < n) : (selmer n).monic :=
selmer.leading_coeff hn

lemma selmer.ne_zero (n : ℕ) : selmer n ≠ 0 :=
begin
  by_cases hn0 : n = 0,
  { rw [hn0, selmer.zero, neg_ne_zero],
    exact X_ne_zero },
  by_cases hn1 : n = 1,
  { rw [hn1, selmer.one, neg_ne_zero],
    exact one_ne_zero },
  exact (selmer.monic (nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn0, hn1⟩)).ne_zero,
end

lemma selmer.eval_zero {n : ℕ} (hn : 0 < n) : (selmer n).eval 0 = -1 :=
by rw [selmer, eval_sub, eval_sub, eval_one, eval_pow, eval_X, zero_pow hn, sub_self, zero_sub]

lemma selmer.coeff_zero {n : ℕ} (hn : 0 < n) : (selmer n).coeff 0 = -1 :=
by rw [coeff_zero_eq_eval_zero, selmer.eval_zero hn]

lemma selmer.coeff_zero_ne_zero {n : ℕ} (hn : 0 < n) : (selmer n).coeff 0 ≠ 0 :=
by { rw [selmer.coeff_zero hn, neg_ne_zero], exact one_ne_zero }

lemma selmer.not_is_unit {n : ℕ} (hn1 : n ≠ 1) : ¬ is_unit (selmer n) :=
begin
  by_cases hn0 : n = 0,
  { rw [hn0, selmer.zero, is_unit_neg],
    exact not_is_unit_X },
  apply mt degree_eq_zero_of_is_unit,
  rwa [selmer.degree (nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn0, hn1⟩), with_bot.coe_eq_zero],
end

lemma selmer.reverse {n : ℕ} (hn : 1 < n) : (selmer n).reverse = 1 - X ^ (n - 1) - X ^ n :=
by rw [reverse, selmer.nat_degree hn, selmer,
  (show X ^ n - X - (1 : polynomial ℤ) = X ^ n - X ^ 1 - X ^ 0, by rw [pow_zero, pow_one]),
  reflect_sub, reflect_sub, reflect_monomial, reflect_monomial, reflect_monomial,
  rev_at_le (le_refl n), rev_at_le (le_of_lt hn), rev_at_le (nat.zero_le n),
  nat.sub_self, pow_zero, nat.sub_zero]

lemma selmer.reverse_eval_zero {n : ℕ} (hn : 1 < n) : (selmer n).reverse.eval 0 = 1 :=
by { rw reverse_eval_zero, exact selmer.leading_coeff hn }

lemma selmer.reverse_coeff_zero {n : ℕ} (hn : 1 < n) : (selmer n).reverse.coeff 0 = 1 :=
by rw [coeff_zero_eq_eval_zero, selmer.reverse_eval_zero hn]

lemma selmer.reverse_nat_degree {n : ℕ} (hn : 1 < n) : (selmer n).reverse.nat_degree = n :=
begin
  rw [reverse_nat_degree_eq, selmer.nat_degree hn],
  exact selmer.coeff_zero_ne_zero (zero_lt_one.trans hn),
end

lemma selmer.reverse_leading_coeff {n : ℕ} (hn : 0 < n) : (selmer n).reverse.leading_coeff = -1 :=
by rw [reverse_leading_coeff (selmer.coeff_zero_ne_zero hn), selmer.coeff_zero hn]

lemma sub_lemma (n : ℕ) (z : ℂ) : ¬ (z ^ n = z + 1 ∧ z ^ n + z ^ 2 = 0) :=
begin
  rintros ⟨h1, h2⟩,
  rw h1 at h2,
  have h3 : (z - 1) * (z + 1 + z ^ 2) = 0,
  { rw [h2, mul_zero] },
  replace h3 : z ^ 3 = 1,
  { rw [←sub_eq_zero, ←h3],
    ring },
  have key : z ^ n = 1 ∨ z ^ n = z ∨ z ^ n = z ^ 2,
  { rw [←nat.mod_add_div n 3, pow_add, pow_mul, h3, one_pow, mul_one],
    have : n % 3 < 3 := nat.mod_lt n zero_lt_three,
    interval_cases n % 3,
    all_goals { rw h },
    { exact or.inl (pow_zero z) },
    { exact or.inr (or.inl (pow_one z)) },
    { exact or.inr (or.inr rfl) } },
  have z_ne_zero : z ≠ 0,
  { intro h,
    rw [h, zero_pow (zero_lt_three)] at h3,
    exact zero_ne_one h3 },
  rcases key with key | key | key,
  { rw [key, right_eq_add_iff] at h1,
    exact z_ne_zero h1 },
  { rw [key, left_eq_add_iff] at h1,
    exact one_ne_zero h1 },
  { rw [←key, h1, add_self_eq_zero, ←h1] at h2,
    exact z_ne_zero (pow_eq_zero h2) },
end

lemma selmer.coprime_reverse {n : ℕ} {g : polynomial ℤ}
  (hg1 : g ∣ selmer n) (hg2 : g ∣ (selmer n).reverse) : is_unit g :=
begin
  by_cases hn0 : n = 0,
  { rw [hn0, selmer.zero, reverse_neg, reverse_X, dvd_neg] at hg2,
    exact is_unit_of_dvd_one g hg2 },
  by_cases hn1 : n = 1,
  { rw [hn1, selmer.one, dvd_neg] at hg1,
    exact is_unit_of_dvd_one g hg1 },
  have hn := nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn0, hn1⟩,
  have hn' := zero_lt_one.trans hn,
  suffices : ¬ (0 < g.nat_degree),
  { cases hg1 with h fgh,
    have key : is_unit (g.coeff 0 * h.eval 0),
    { rw [coeff_zero_eq_eval_zero, ←eval_mul, ←fgh, selmer.eval_zero hn', is_unit_neg],
      exact is_unit_one },
    rw [eq_C_of_nat_degree_eq_zero (not_not.mp (mt zero_lt_iff.mpr this)), is_unit_C],
    exact is_unit_of_mul_is_unit_left key },
  intro h,
  have inj : function.injective (algebra_map ℤ ℂ) := int.cast_injective,
  rw [lt_iff_not_ge, ge_iff_le, nat_degree_le_iff_degree_le, ←ge_iff_le, ←lt_iff_not_ge,
      with_bot.coe_zero, ←degree_map' inj] at h,
  cases complex.exists_root h with z hz,
  rw [is_root, eval_map, ←aeval_def] at hz,
  replace hg1 : aeval z (selmer n) = 0,
  { cases hg1 with g' hg',
    rw [hg', aeval_mul, hz, zero_mul] },
  replace hg2 : aeval z (selmer n).reverse = 0,
  { cases hg2 with g' hg',
    rw [hg', aeval_mul, hz, zero_mul] },
  rw [selmer, alg_hom.map_sub, alg_hom.map_sub, alg_hom.map_pow, aeval_X, aeval_one,
      sub_sub, sub_eq_zero] at hg1,
  rw [selmer.reverse hn, alg_hom.map_sub, alg_hom.map_sub, alg_hom.map_pow, alg_hom.map_pow,
      aeval_X, aeval_one, sub_sub, sub_eq_zero, hg1, ←add_assoc, right_eq_add_iff] at hg2,
  replace hg2 : z ^ n + z ^ 2 = 0,
  { rw [←nat.sub_add_cancel (nat.succ_le_of_lt hn'), pow_succ, pow_two, ←mul_add, hg2, mul_zero] },
  exact sub_lemma n z ⟨hg1, hg2⟩,
end

lemma int.mul_eq_one_iff {a b : ℤ} : (a * b = 1) ↔ (a = 1 ∧ b = 1) ∨ (a = -1 ∧ b = -1) :=
begin
  split,
  { intro hab,
    cases int.units_eq_one_or (units.mk_of_mul_eq_one a b hab) with h h,
    { have ha : a = 1 := units.ext_iff.mp h,
      rw [ha, one_mul] at hab,
      exact or.inl ⟨ha, hab⟩ },
    { have ha : a = -1 := units.ext_iff.mp h,
      rw [ha, neg_one_mul, neg_eq_iff_neg_eq, eq_comm] at hab,
      exact or.inr ⟨ha, hab⟩ } },
  { rintros (⟨ha, hb⟩ | ⟨ha, hb⟩),
    rw [ha, hb, one_mul],
    rw [ha, hb, neg_mul_neg, one_mul] },
end

lemma int.mul_eq_neg_one_iff {a b : ℤ} : (a * b = -1) ↔ (a = 1 ∧ b = -1) ∨ (a = -1 ∧ b = 1) :=
by rw [eq_neg_iff_eq_neg, eq_comm, neg_mul_eq_neg_mul, int.mul_eq_one_iff, neg_inj,
  neg_eq_iff_neg_eq, eq_comm, or_comm]

lemma leading_coeff_neg {R : Type*} [ring R] (f : polynomial R) :
  leading_coeff (-f) = - (leading_coeff f) :=
by rw [leading_coeff, leading_coeff, coeff_neg, nat_degree_neg]

theorem selmer.irreducible (n : ℕ) (hn1 : n ≠ 1) : irreducible (selmer n) :=
begin
  by_cases hn0 : n = 0,
  { exact irreducible_of_associated
      ⟨-1, by rw [units.coe_neg_one, mul_neg_one, hn0, selmer.zero]⟩ irreducible_X },
  have hn := nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn0, hn1⟩,
  have hn' := zero_lt_one.trans hn,
  refine key_lemma (ne_of_eq_of_ne (selmer.eval_zero hn') (neg_ne_zero.mpr one_ne_zero))
    (selmer.not_is_unit hn1) _ (λ _, selmer.coprime_reverse),
  suffices : ∀ k : polynomial ℤ, (selmer n) * (selmer n).reverse = k * k.reverse → k.monic
    → k = selmer n ∨ k = -((selmer n).reverse),
  { intros k hk,
    have key := congr_arg leading_coeff hk,
    rw [leading_coeff_mul, leading_coeff_mul, selmer.leading_coeff hn,
        selmer.reverse_leading_coeff hn', one_mul, eq_comm, int.mul_eq_neg_one_iff] at key,
    rcases key with (⟨h1, h2⟩ | ⟨h1, h2⟩),
    exact or.elim (this k hk h1) (λ h, or.inl h) (λ h, or.inr (or.inr (or.inr h))),
    have key := this (-k) (by rwa [reverse_neg, neg_mul_neg])
      (by rw [monic, leading_coeff_neg, h1, neg_neg]),
    rw [neg_inj, neg_eq_iff_neg_eq, eq_comm] at key,
    exact or.elim key (λ h, or.inr (or.inl h)) (λ h, or.inr (or.inr (or.inl h))) },
  intros k hk1 hk2,
  have hk3 : k.reverse.coeff 0 = 1 := k.reverse_coeff_zero.trans hk2,
  have hk4 : k.coeff 0 = -1,
  { replace hk1 := congr_arg (eval 0) hk1,
    rwa [eval_mul, eval_mul, selmer.eval_zero hn', selmer.reverse_eval_zero hn, mul_one,
        ←coeff_zero_eq_eval_zero, ←coeff_zero_eq_eval_zero, hk3, mul_one, eq_comm] at hk1 },
  have hk5 : k.nat_degree = n,
  { replace hk1 := congr_arg nat_degree hk1,
    rw [nat_degree_mul, nat_degree_mul] at hk1, },
  have hk5 : false,
  { replace hk1 := congr_arg (coeff n) hk1,
    have key := mul_reverse_coeff, },
  have hk5 := mul_reverse_coeff,
  sorry,
end

--https://math.stackexchange.com/a/800835

lemma selmer_irreducible {n : ℕ} (hn : 1 < n) : irreducible (selmer n) :=
begin
  split,
  { exact λ h, ne_zero_of_lt hn ((selmer.nat_degree hn).symm.trans
      (nat_degree_eq_zero_iff_degree_le_zero.mpr (le_of_eq (degree_eq_zero_of_is_unit h)))) },
  suffices : ∀ f g : polynomial ℤ, selmer n = f * g → f.monic → g.monic → is_unit f ∨ is_unit g,
  { intros f g hfg,
    have key : f.leading_coeff * g.leading_coeff = 1,
    { rw [←leading_coeff_mul, ←hfg],
      exact selmer.monic hn },
    cases int.mul_eq_one_iff key with h h,
    { exact this f g hfg h.1 h.2 },
    { have key := this (-f) (-g) (hfg.trans (neg_mul_neg f g).symm)
        (f.leading_coeff_neg.trans (neg_eq_iff_neg_eq.mp h.1.symm))
        (g.leading_coeff_neg.trans (neg_eq_iff_neg_eq.mp h.2.symm)),
      exact or.imp (is_unit_neg f).mp (is_unit_neg g).mp key } },
  suffices : ∀ f g : polynomial ℤ, selmer n = f * g → f.monic → g.monic →
    f.eval 0 = 1 → g.eval 0 = -1 → f = 1 ∨ g = -1,
  { intros f g hfg hf hg,
    have key := selmer.eval_zero (zero_lt_one.trans hn),
    rw [hfg, eval_mul] at key,
    cases int.mul_eq_neg_one_iff key with h h,
    { refine or.imp _ _ (this f g hfg hf hg h.1 h.2),
      exact (λ h', (congr_arg is_unit h').mpr is_unit_one),
      exact (λ h', (congr_arg is_unit h').mpr ((is_unit_neg 1).mpr is_unit_one)) },
    { refine or.imp _ _ (this g f (hfg.trans (mul_comm f g)) hg hf h.2 h.1).symm,
      exact (λ h', (congr_arg is_unit h').mpr ((is_unit_neg 1).mpr is_unit_one)),
      exact (λ h', (congr_arg is_unit h').mpr is_unit_one) } },
  intros f g hfg hf1 hg1 hf2 hg2,
  let k := f.reverse * g,
  have h1 : k.monic := sorry,
  have h2 : k.eval 0 = -1 := sorry,
  have h3 : k * k.reverse = (selmer n) * (selmer n).reverse,
end

end polynomial
