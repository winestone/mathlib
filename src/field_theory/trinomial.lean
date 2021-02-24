import field_theory.reverse'

namespace polynomial

/-- bundled trinomial -/
structure trinomial (R : Type*) [semiring R] :=
(a b c : R) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (i j k : ℕ) (hij : i < j) (hjk : j < k)

namespace trinomial

variables {R : Type*} [semiring R] (t : trinomial R)

lemma hik : t.i < t.k := t.hij.trans t.hjk

@[ext] lemma ext {s t : trinomial R} (ha : s.a = t.a) (hb : s.b = t.b) (hc : s.c = t.c)
  (hi : s.i = t.i) (hj : s.j = t.j) (hk : s.k = t.k) : s = t :=
begin
  cases s,
  cases t,
  exact mk.inj_eq.mpr ⟨ha, hb, hc, hi, hj, hk⟩,
end

/-- unbundle a trinomial -/
noncomputable def to_polynomial : polynomial R :=
(monomial t.i t.a) + (monomial t.j t.b) + (monomial t.k t.c)

lemma coeff_i : t.to_polynomial.coeff t.i = t.a :=
by rw [to_polynomial, coeff_add, coeff_add,
  coeff_monomial, coeff_monomial, coeff_monomial,
  if_neg (ne_of_gt t.hij), add_zero, if_neg (ne_of_gt t.hik), add_zero, if_pos rfl]

lemma coeff_j : t.to_polynomial.coeff t.j = t.b :=
by rw [to_polynomial, coeff_add, coeff_add,
  coeff_monomial, coeff_monomial, coeff_monomial,
  if_neg (ne_of_lt t.hij), zero_add, if_neg (ne_of_gt t.hjk), add_zero, if_pos rfl]

lemma coeff_k : t.to_polynomial.coeff t.k = t.c :=
by rw [to_polynomial, coeff_add, coeff_add,
  coeff_monomial, coeff_monomial, coeff_monomial,
  if_neg (ne_of_lt t.hik), zero_add, if_neg (ne_of_lt t.hjk), zero_add, if_pos rfl]

lemma support : t.to_polynomial.support = {t.i, t.j, t.k} :=
begin
  apply finset.subset.antisymm,
  { rw to_polynomial,
    refine finset.subset.trans finsupp.support_add (finset.union_subset
      (finset.subset.trans finsupp.support_add (finset.union_subset _ _)) _),
    all_goals
    { apply finset.subset.trans (support_monomial' _ _) (finset.singleton_subset_iff.mpr _),
      rw [finset.mem_insert, finset.mem_insert, finset.mem_singleton] },
    { exact or.inl rfl },
    { exact or.inr (or.inl rfl) },
    { exact or.inr (or.inr rfl) } },
  { rw [finset.insert_subset, finset.insert_subset, finset.singleton_subset_iff,
        mem_support_iff_coeff_ne_zero, t.coeff_i, mem_support_iff_coeff_ne_zero, t.coeff_j,
        mem_support_iff_coeff_ne_zero, t.coeff_k],
    exact ⟨t.ha, t.hb, t.hc⟩ },
end

lemma norm2 : t.to_polynomial.norm2 = t.a ^ 2 + t.b ^ 2 + t.c ^ 2 :=
by rw [norm2, support, finset.sum_insert (mt finset.mem_insert.mp (not_or (ne_of_lt t.hij)
  (mt finset.mem_singleton.mp (ne_of_lt t.hik)))), finset.sum_insert (mt finset.mem_singleton.mp
  (ne_of_lt t.hjk)), finset.sum_singleton, t.coeff_i, t.coeff_j, t.coeff_k, add_assoc]

lemma card_support : t.to_polynomial.support.card = 3 :=
by rw [t.support, finset.card_insert_of_not_mem (mt finset.mem_insert.mp (not_or (ne_of_lt t.hij)
  (mt finset.mem_singleton.mp (ne_of_lt t.hik)))), finset.card_insert_of_not_mem
  (mt finset.mem_singleton.mp (ne_of_lt t.hjk)), finset.card_singleton]

lemma ne_zero (t : trinomial R) : t.to_polynomial ≠ 0 :=
λ h, nat.bit1_ne_zero 1 (t.card_support.symm.trans (finsupp.card_support_eq_zero.mpr h))

/-- turn a polynomial into a trinomial -/
noncomputable def of_polynomial {p : polynomial R} (h0 : p.support.card = 3) :
  trinomial R :=
let h1 := erase_lead_card_support h0,
  h2 := erase_lead_card_support h1,
  h3 := erase_lead_card_support h2,
  h0' := λ h, nat.bit1_ne_zero 1 (h0.symm.trans (finsupp.card_support_eq_zero.mpr h)),
  h1' := λ h, two_ne_zero (h1.symm.trans (finsupp.card_support_eq_zero.mpr h)),
  h2' := λ h, one_ne_zero (h2.symm.trans (finsupp.card_support_eq_zero.mpr h)),
  h3' := finsupp.card_support_eq_zero.mp h3 in
{ a := p.erase_lead.erase_lead.leading_coeff,
  b := p.erase_lead.leading_coeff,
  c := p.leading_coeff,
  ha := mt leading_coeff_eq_zero.mp h2',
  hb := mt leading_coeff_eq_zero.mp h1',
  hc := mt leading_coeff_eq_zero.mp h0',
  i := p.erase_lead.erase_lead.nat_degree,
  j := p.erase_lead.nat_degree,
  k := p.nat_degree,
  hij := erase_lead_nat_degree_lt (ge_of_eq h1),
  hjk := erase_lead_nat_degree_lt ((nat.le_succ 2).trans (ge_of_eq h0)) }

lemma of_polynomial_to_polynomial {p : polynomial R} (h0 : p.support.card = 3) :
  (of_polynomial h0).to_polynomial = p :=
begin
  conv_rhs
  { rw ← p.erase_lead_add_monomial_nat_degree_leading_coeff,
    rw ← p.erase_lead.erase_lead_add_monomial_nat_degree_leading_coeff,
    rw ← p.erase_lead.erase_lead.erase_lead_add_monomial_nat_degree_leading_coeff,
    rw [finsupp.card_support_eq_zero.mp (erase_lead_card_support
        (erase_lead_card_support (erase_lead_card_support h0))), zero_add] },
  refl,
end

lemma to_polynomial_of_polynomial : of_polynomial t.card_support = t :=
begin
  have h1 : t.to_polynomial = (monomial t.i t.a) + (monomial t.j t.b) + (monomial t.k t.c) := rfl,
  have h2 : t.to_polynomial.nat_degree = t.k,
  { simp_rw [nat_degree_eq_support_max' t.ne_zero, t.support],
    rw [finset.max'_insert, finset.max'_insert, finset.max'_singleton],
    rw [max_eq_left (le_of_lt t.hjk), max_eq_left (le_of_lt t.hik)] },
  have h3 : t.to_polynomial.leading_coeff = t.c,
  { rw [leading_coeff, h2, h1, coeff_add, coeff_add,
        coeff_monomial, coeff_monomial, coeff_monomial,
        if_neg (ne_of_lt t.hik), if_neg (ne_of_lt t.hjk), if_pos rfl, zero_add, zero_add] },
  have h4 : t.to_polynomial.erase_lead = (monomial t.i t.a) + (monomial t.j t.b),
  { rw [erase_lead, h2, h1, monomial_def, monomial_def, monomial_def, finsupp.erase_add,
        finsupp.erase_add, finsupp.erase_single_ne (ne_of_gt t.hik),
        finsupp.erase_single_ne (ne_of_gt t.hjk), finsupp.erase_single, add_zero] },
  have h5 : t.to_polynomial.erase_lead.nat_degree = t.j,
  { rw [h4, ←degree_eq_iff_nat_degree_eq_of_pos (lt_of_le_of_lt t.i.zero_le t.hij),
        degree_add_eq_right_of_degree_lt, degree_monomial t.j t.hb],
    rw [degree_monomial t.i t.ha, degree_monomial t.j t.hb],
    exact with_bot.coe_lt_coe.mpr t.hij },
  have h6 : t.to_polynomial.erase_lead.leading_coeff = t.b,
  { rw [leading_coeff, h5, h4, coeff_add, coeff_monomial, coeff_monomial,
        if_neg (ne_of_lt t.hij), if_pos rfl, zero_add] },
  have h7 : t.to_polynomial.erase_lead.erase_lead = (monomial t.i t.a),
  { rw [erase_lead, h5, h4, monomial_def, monomial_def, finsupp.erase_add,
        finsupp.erase_single_ne (ne_of_gt t.hij), finsupp.erase_single, add_zero] },
  have h8 : t.to_polynomial.erase_lead.erase_lead.nat_degree = t.i,
  { rw [h7, nat_degree_monomial t.i t.a t.ha] },
  have h9 : t.to_polynomial.erase_lead.erase_lead.leading_coeff = t.a,
  { rw [leading_coeff, h8, h7, coeff_monomial, if_pos rfl] },
  exact ext h9 h6 h3 h8 h5 h2,
end

lemma to_polynomial_inj {s t : trinomial R} :
  s.to_polynomial = t.to_polynomial ↔ s = t :=
begin
  split,
  { intro h,
    rw [←s.to_polynomial_of_polynomial, ←t.to_polynomial_of_polynomial],
    simp_rw h },
  { intro h,
    rw h }
end

lemma support_card_eq_three_iff {p : polynomial R} :
  p.support.card = 3 ↔ ∃ t : trinomial R, p = t.to_polynomial :=
begin
  split,
  { exact λ h, ⟨of_polynomial h, (of_polynomial_to_polynomial h).symm⟩ },
  { rintros ⟨t, rfl⟩,
    exact t.card_support },
end

lemma nat_degree : t.to_polynomial.nat_degree = t.k :=
congr_arg k t.to_polynomial_of_polynomial

lemma leading_coeff : t.to_polynomial.leading_coeff = t.c :=
congr_arg c t.to_polynomial_of_polynomial

lemma nat_trailing_degree : t.to_polynomial.nat_trailing_degree = t.i :=
begin
  simp_rw [nat_trailing_degree_eq_support_min' t.ne_zero, t.support],
  rw [finset.min'_insert, finset.min'_insert, finset.min'_singleton],
  rw [min_eq_right (le_of_lt t.hjk), min_eq_right (le_of_lt t.hij)],
end

lemma trailing_coeff : t.to_polynomial.trailing_coeff = t.a :=
by rw [trailing_coeff, nat_trailing_degree, to_polynomial, coeff_add, coeff_add,
  coeff_monomial, coeff_monomial, coeff_monomial,
  if_pos rfl, if_neg (ne_of_gt t.hik), if_neg (ne_of_gt t.hij), add_zero, add_zero]

def twist (u : units R) : trinomial R :=
{ a := u * t.a,
  b := u * t.b,
  c := u * t.c,
  ha := mt u.mul_right_eq_zero.mp t.ha,
  hb := mt u.mul_right_eq_zero.mp t.hb,
  hc := mt u.mul_right_eq_zero.mp t.hc,
  i := t.i,
  j := t.j,
  k := t.k,
  hij := t.hij,
  hjk := t.hjk }

lemma twist_one : t.twist 1 = t :=
ext (one_mul _) (one_mul _) (one_mul _) rfl rfl rfl

lemma twist_twist (u v : units R) : (t.twist v).twist u = t.twist (u * v) :=
ext (mul_assoc _ _ _).symm (mul_assoc _ _ _).symm (mul_assoc _ _ _).symm rfl rfl rfl

instance twist_action : mul_action (units R) (trinomial R) :=
{ smul := λ u t, t.twist u,
  one_smul := twist_one,
  mul_smul := λ u v t, (t.twist_twist u v).symm }

lemma smul_to_polynomial (u : units R) : (u • t).to_polynomial = (u : R) • t.to_polynomial :=
begin
  simp_rw [to_polynomial, smul_add, smul_monomial],
  refl,
end

/-- reverse a trinomial -/
def reverse : trinomial R :=
{ a := t.c,
  b := t.b,
  c := t.a,
  ha := t.hc,
  hb := t.hb,
  hc := t.ha,
  i := t.i,
  j := t.i + t.k - t.j,
  k := t.k,
  hij := nat.lt_sub_right_of_add_lt (nat.add_lt_add_left t.hjk t.i),
  hjk := (nat.sub_lt_left_iff_lt_add ((le_of_lt t.hjk).trans (nat.le_add_left t.k t.i))).mpr
    (nat.add_lt_add_right t.hij t.k) }

lemma reverse_smul (u : units R) : (u • t).reverse = u • t.reverse := rfl

lemma reverse_to_polynomial : t.reverse.to_polynomial = t.to_polynomial.reverse' :=
begin
  rw [reverse', t.nat_trailing_degree, polynomial.reverse, t.nat_degree],
  simp_rw [to_polynomial, reflect_add, ←C_mul_X_pow_eq_monomial, reflect_C_mul_X_pow,
    C_mul_X_pow_eq_monomial, X_pow_eq_monomial t.i, add_mul, monomial_mul_monomial, mul_one],
  rw [rev_at_le (le_of_lt t.hik), nat.sub_add_cancel (le_of_lt t.hik)],
  rw [rev_at_le (le_of_lt t.hjk), nat.sub_add_eq_add_sub (le_of_lt t.hjk), nat.add_comm t.k t.i],
  rw [rev_at_le (le_refl t.k), nat.sub_self, zero_add],
  rw [add_assoc (monomial t.k t.a), add_comm (monomial t.k t.a), add_comm _ (monomial t.i t.c)],
  refl,
end

lemma reverse_reverse : t.reverse.reverse = t :=
by rw [←to_polynomial_inj, reverse_to_polynomial, reverse_to_polynomial, reverse'_reverse']

lemma key_lemma_aux1 {R : Type*} [integral_domain R] (p q : trinomial R) (hpqa : p.a = q.a)
  (hpq : p.to_polynomial * p.to_polynomial.reverse' = q.to_polynomial * q.to_polynomial.reverse') :
  ∃ u : units R, q = u • p ∨ q = u • p.reverse :=
begin
  have hpqc : p.c = q.c,
  { replace hpq := congr_arg polynomial.leading_coeff hpq,
    simp_rw [leading_coeff_mul, reverse'_leading_coeff, leading_coeff, trailing_coeff] at hpq,
    rwa [hpqa, mul_eq_mul_right_iff, or_iff_not_imp_right, imp_iff_right q.ha] at hpq },
  have hpqk : p.i = q.i,
  { replace hpq := congr_arg polynomial.nat_trailing_degree hpq,
    rw [nat_trailing_degree_mul_reverse', nat_trailing_degree_mul_reverse',
        nat_trailing_degree, nat_trailing_degree] at hpq,
    exact mul_left_cancel' two_ne_zero hpq },
  have hpqk : p.k = q.k,
  { replace hpq := congr_arg polynomial.nat_degree hpq,
    rw [nat_degree_mul_reverse', nat_degree_mul_reverse', nat_degree, nat_degree] at hpq,
    exact mul_left_cancel' two_ne_zero hpq },
  -- next step: reduce to p.b = q.b, by looking at norm2 and at `(p * p.reverse).eval 1` (sum of coeffs!)
  sorry,
end

lemma mini_lemma {R : Type*} [comm_semiring R] (r s : R) (p q : polynomial R) :
  (r • p) * (s • q) = (r * s) • (p * q) :=
begin
  rw [←C_mul', ←C_mul', ←C_mul', C_mul, ←mul_assoc, ←mul_assoc,
      mul_assoc (C r), mul_comm p, ←mul_assoc],
end

lemma key_lemma {p q : trinomial ℤ}
  (hp : is_unit (p.a * p.c) ∨ irreducible (p.a * p.c))
  (hpq : p.to_polynomial * p.to_polynomial.reverse' = q.to_polynomial * q.to_polynomial.reverse') :
  ∃ u : units ℤ, q = u • p ∨ q = u • p.reverse :=
begin
  have hp' : ∀ x y, p.a * p.c = x * y → is_unit x ∨ is_unit y := or.elim hp (λ h1 x y h2, or.inl
    (is_unit_of_mul_is_unit_left ((congr_arg is_unit h2).mp h1))) irreducible.is_unit_or_is_unit,
  have key : p.a * p.c = q.a * q.c,
  { replace hpq := congr_arg polynomial.leading_coeff hpq,
    simp_rw [leading_coeff_mul, reverse'_leading_coeff, leading_coeff, trailing_coeff] at hpq,
    rwa [mul_comm p.a p.c, mul_comm q.a q.c] },
  rcases (hp' p.a p.c rfl) with ⟨u1, hu1⟩ | ⟨u1, hu1⟩,
  { rcases (hp' q.a q.c key) with ⟨u2, hu2⟩ | ⟨u2, hu2⟩,
    { obtain ⟨u, hu⟩ := key_lemma_aux1 (u2 • p) (u1 • q)
        ((mul_comm _ _).trans (congr (congr_arg has_mul.mul hu1.symm) hu2))
        (by simp_rw [smul_to_polynomial, reverse'_smul, mini_lemma, int.units_coe_mul_self, hpq]),
      simp_rw [reverse_smul, ←eq_inv_smul_iff, smul_smul] at hu,
      exact ⟨_, hu⟩ },
    { obtain ⟨u, hu⟩ := key_lemma_aux1 (u1 • p.reverse) (u2 • q)
        (by rwa [←hu1, ←hu2, mul_comm q.a] at key)
        (by simp_rw [smul_to_polynomial, reverse_to_polynomial, reverse'_smul, reverse'_reverse',
          mini_lemma, int.units_coe_mul_self, mul_comm, hpq]),
      simp_rw [reverse_smul, reverse_reverse, ←eq_inv_smul_iff, smul_smul, or_comm] at hu,
      exact ⟨_, hu⟩ } },
  { rcases (hp' q.a q.c key) with ⟨u2, hu2⟩ | ⟨u2, hu2⟩,
    { obtain ⟨u, hu⟩ := key_lemma_aux1 (u2 • p.reverse) (u1 • q)
        ((mul_comm _ _).trans (congr (congr_arg has_mul.mul hu1.symm) hu2))
        (by simp_rw [smul_to_polynomial, reverse_to_polynomial, reverse'_smul, reverse'_reverse',
          mini_lemma, int.units_coe_mul_self, mul_comm, hpq]),
      simp_rw [reverse_smul, reverse_reverse, ←eq_inv_smul_iff, smul_smul, or_comm] at hu,
      exact ⟨_, hu⟩ },
    { obtain ⟨u, hu⟩ := key_lemma_aux1 (u1 • p) (u2 • q)
        (by rwa [←hu1, ←hu2, mul_comm p.a, mul_comm q.a] at key)
        (by simp_rw [smul_to_polynomial, reverse'_smul, mini_lemma, int.units_coe_mul_self, hpq]),
      simp_rw [reverse_smul, ←eq_inv_smul_iff, smul_smul] at hu,
      exact ⟨_, hu⟩ } },
end

end trinomial

lemma reverse'_irreducible_test' {f : polynomial ℤ}
  (h1 : f.norm2 = 3)
  (h2 : ∀ g, g ∣ f → g ∣ f.reverse' → is_unit g) : irreducible f :=
begin
  obtain ⟨t, rfl⟩ := trinomial.support_card_eq_three_iff.mp
    (f.card_support_eq_three_of_norm2_eq_three h1),
  refine reverse'_irreducible_test (λ h3, _) _ h2,
  { obtain ⟨r, ⟨u, rfl⟩, h4⟩ := is_unit_iff.mp h3,
    rw [←h4, norm2_C, ←units.coe_pow, int.units_pow_two, units.coe_one] at h1,
    exact ne_of_lt (int.add_lt_add zero_lt_one one_lt_two) h1 },
  { intros g hg,
    obtain ⟨s, rfl⟩ := trinomial.support_card_eq_three_iff.mp
      (g.card_support_eq_three_of_norm2_eq_three begin
        rw [norm2_eq_mul_reverse_coeff, ←hg],
        -- swap out nat_degree and nat_trailing_degree...
        -- (use those fancy div by 2 lemmas)
        sorry,
      end),
    have key := trinomial.key_lemma _ hg,
    sorry,
    { apply or.inl,
      sorry },},
end

lemma selmer_irreducible {n : ℕ} (hn1 : n ≠ 1) : irreducible (X ^ n - X - 1 : polynomial ℤ) :=
begin
  by_cases hn0 : n = 0,
  { rw [hn0, pow_zero, sub_sub, add_comm, ←sub_sub, sub_self, zero_sub],
    exact irreducible_of_associated ⟨-1, mul_neg_one X⟩ irreducible_X },
  have hn : 1 < n := nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn0, hn1⟩,
  let p := trinomial.mk (-(1 : ℤ)) (-(1 : ℤ)) (1 : ℤ) (neg_ne_zero.mpr one_ne_zero)
    (neg_ne_zero.mpr one_ne_zero) (one_ne_zero) 0 1 n zero_lt_one hn,
  have h1 : p.to_polynomial = X ^ n - X - 1,
  { simp_rw [trinomial.to_polynomial, ←C_mul_X_pow_eq_monomial, C_neg, C_1],
    ring },
  rw ← h1,
  apply reverse'_irreducible_test',
  { rw p.norm2,
    norm_num },
  { rw ← p.reverse_to_polynomial, sorry },
end

end polynomial

/-
lemma selmer_support_subset (n : ℕ) : (X ^ n - X - 1 : polynomial ℤ).support ⊆ {0, 1, n} :=
begin
  have h1 : (-1 : polynomial ℤ).support ⊆ {0},
  { convert support_monomial' 0 (-1 : ℤ),
    rw [single_eq_C_mul_X, C_neg, C_1, neg_one_mul, pow_zero] },
  have h2 : (-X : polynomial ℤ).support ⊆ {1},
  { convert support_monomial' 1 (-1 : ℤ),
    rw [single_eq_C_mul_X, C_neg, C_1, neg_one_mul, pow_one] },
  have h3 : (X ^ n : polynomial ℤ).support ⊆ {n},
  { convert support_monomial' n (1 : ℤ),
    rw [single_eq_C_mul_X, C_1, one_mul] },
  rw [sub_eq_add_neg, sub_eq_add_neg],
  refine finset.subset.trans finsupp.support_add (finset.union_subset
    (finset.subset.trans finsupp.support_add (finset.union_subset
    (finset.subset.trans h3 _) (finset.subset.trans h2 _))) (finset.subset.trans h1 _)),
  all_goals { simp only [finset.singleton_subset_iff, finset.mem_insert, finset.mem_singleton] },
  { exact or.inr (or.inr rfl) },
  { exact or.inr (or.inl rfl) },
  { exact or.inl rfl }
end

lemma selmer_norm2 {n : ℕ} (hn : 1 < n) : (X ^ n - X - 1 : polynomial ℤ).norm2 = 3 :=
begin
  rw [norm2_eq_sum_of_support _ (selmer_support_subset n),
      finset.sum_insert (mt finset.mem_insert.mp (not_or zero_ne_one
        (mt finset.mem_singleton.mp (ne_of_lt (zero_lt_one.trans hn))))),
      finset.sum_insert (mt finset.mem_singleton.mp (ne_of_lt hn)), finset.sum_singleton],
  simp only [coeff_sub, coeff_one, coeff_X, coeff_X_pow],
  rw [if_neg (ne_of_lt hn), if_neg (ne_of_lt (zero_lt_one.trans hn))],
  norm_num,
end
-/
