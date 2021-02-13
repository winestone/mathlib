import data.polynomial.reverse
import field_theory.polynomial_galois_group
import analysis.complex.polynomial

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
    cases hk with hk hk,
    { exact or.inr (h4 h h_dvd_f (by rwa ← hk)) },
    cases hk with hk hk,
    { exact or.inr (h4 h h_dvd_f (by rwa [eq_neg_iff_eq_neg.mp hk, reverse_neg, dvd_neg])) },
    cases hk with hk hk,
    { exact or.inl (h4 g g_dvd_f (by rwa ← hk)) },
    { exact or.inl (h4 g g_dvd_f (by rwa [eq_neg_iff_eq_neg.mp hk, dvd_neg])) } },
end

lemma is_unit_neg {R : Type*} [ring R] (u : R) : is_unit (-u) ↔ is_unit u :=
⟨λ h, Exists.cases_on h (λ v hv, ⟨-v, v.coe_neg.trans (neg_eq_iff_neg_eq.mp hv.symm)⟩),
  λ h, Exists.cases_on h (λ v hv, ⟨-v, v.coe_neg.trans (congr_arg _ hv)⟩)⟩

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

lemma selmer.monic {n : ℕ} (hn : 1 < n) : (selmer n).monic :=
by rw [monic, leading_coeff, selmer.nat_degree hn, selmer, coeff_sub, coeff_sub, coeff_X_pow_self,
  coeff_X, coeff_one, if_neg (ne_of_lt hn), if_neg (ne_zero_of_lt hn).symm, sub_zero, sub_zero]

lemma selmer.eval_zero {n : ℕ} (hn : 0 < n) : (selmer n).eval 0 = -1 :=
by rw [selmer, eval_sub, eval_sub, eval_one, eval_pow, eval_X, zero_pow hn, sub_self, zero_sub]

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

lemma cases_mod_three (n : ℕ) : (n % 3 = 0) ∨ (n % 3 = 1) ∨ (n % 3 = 2) :=
begin
  induction n with n hn,
  exact or.inl (nat.zero_mod 3),
  rw [nat.succ_eq_add_one, nat.add_mod],
  cases hn with hn hn,
  { rw hn,
    exact or.inr (or.inl rfl) },
  cases hn with hn hn,
  { rw hn,
    exact or.inr (or.inr rfl) },
  { rw hn,
    exact or.inl rfl },
end

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
    refine or.elim3 (cases_mod_three n) _ _ _,
    all_goals { intro h, rw h },
    { exact or.inl (pow_zero z) },
    { exact or.inr (or.inl (pow_one z)) },
    { exact or.inr (or.inr rfl) } },
  have z_ne_zero : z ≠ 0,
  { intro h,
    rw [h, zero_pow (zero_lt_three)] at h3,
    exact zero_ne_one h3 },
  refine or.elim3 key _ _ _,
  { intro h,
    rw [h, right_eq_add_iff] at h1,
    exact z_ne_zero h1 },
  { intro h,
    rw [h, left_eq_add_iff] at h1,
    exact one_ne_zero h1 },
  { intro h,
    rw [←h, h1, add_self_eq_zero, ←h1] at h2,
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

theorem selmer.irreducible (n : ℕ) (hn1 : n ≠ 1) : irreducible (selmer n) :=
begin
  by_cases hn0 : n = 0,
  { exact irreducible_of_associated
      ⟨-1, by rw [units.coe_neg_one, mul_neg_one, hn0, selmer.zero]⟩ irreducible_X },
  have hn := nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hn0, hn1⟩,
  have hn' := zero_lt_one.trans hn,
  refine key_lemma (ne_of_eq_of_ne (selmer.eval_zero hn') (neg_ne_zero.mpr one_ne_zero))
    (selmer.not_is_unit hn1) _ (λ _, selmer.coprime_reverse),
  intros k hk,
  sorry,
end

--https://math.stackexchange.com/a/800835

noncomputable def selmer (n : ℕ) : polynomial ℤ := X ^ n - X - 1

lemma selmer_nat_degree {n : ℕ} (hn : 1 < n) : (selmer n).nat_degree = n :=
begin
  rw [selmer, sub_sub, ←degree_eq_iff_nat_degree_eq_of_pos (zero_lt_one.trans hn)],
  refine eq.trans (degree_sub_eq_left_of_degree_lt _) (degree_X_pow n),
  rwa [degree_X_pow, ←C_1, degree_X_add_C, ←with_bot.coe_one, with_bot.coe_lt_coe],
end

lemma selmer_monic {n : ℕ} (hn : 1 < n) : (selmer n).monic :=
by rw [monic, leading_coeff, selmer_nat_degree hn, selmer, coeff_sub, coeff_sub, coeff_X_pow_self,
  coeff_X, coeff_one, if_neg (ne_of_lt hn), if_neg (ne_zero_of_lt hn).symm, sub_zero, sub_zero]

lemma selmer_eval_zero {n : ℕ} (hn : 0 < n) : (selmer n).eval 0 = -1 :=
by rw [selmer, eval_sub, eval_sub, eval_one, eval_pow, eval_X, zero_pow hn, sub_self, zero_sub]

lemma selmer_reverse {n : ℕ} (hn : 1 < n) : (selmer n).reverse = 1 - X ^ (n - 1) - X ^ n :=
by rw [reverse, selmer_nat_degree hn, selmer,
  (show X ^ n - X - (1 : polynomial ℤ) = X ^ n - X ^ 1 - X ^ 0, by rw [pow_zero, pow_one]),
  reflect_sub, reflect_sub, reflect_monomial, reflect_monomial, reflect_monomial,
  rev_at_le (le_refl n), rev_at_le (le_of_lt hn), rev_at_le (nat.zero_le n),
  nat.sub_self, pow_zero, nat.sub_zero]

lemma int.mul_eq_one_iff {a b : ℤ} (hab : a * b = 1) : (a = 1 ∧ b = 1) ∨ (a = -1 ∧ b = -1) :=
begin
  cases int.units_eq_one_or (units.mk_of_mul_eq_one a b hab) with h h,
  { have ha : a = 1 := units.ext_iff.mp h,
    rw [ha, one_mul] at hab,
    exact or.inl ⟨ha, hab⟩ },
  { have ha : a = -1 := units.ext_iff.mp h,
    rw [ha, neg_one_mul, neg_eq_iff_neg_eq, eq_comm] at hab,
    exact or.inr ⟨ha, hab⟩ },
end

lemma int.mul_eq_neg_one_iff {a b : ℤ} (hab : a * b = -1) : (a = 1 ∧ b = -1) ∨ (a = -1 ∧ b = 1) :=
begin
  have key : (-a) * b = 1 := by rw [neg_mul_eq_neg_mul_symm, hab, neg_neg],
  cases int.mul_eq_one_iff key with h h,
  { exact or.inr ⟨eq_neg_iff_eq_neg.mp h.1.symm, h.2⟩ },
  { exact or.inl ⟨neg_inj.mp h.1, h.2⟩ },
end

lemma leading_coeff_neg {R : Type*} [ring R] (f : polynomial R) : leading_coeff (-f) = - (leading_coeff f) :=
by rw [leading_coeff, leading_coeff, coeff_neg, nat_degree_neg]

lemma selmer_irreducible {n : ℕ} (hn : 1 < n) : irreducible (selmer n) :=
begin
  split,
  { exact λ h, ne_zero_of_lt hn ((selmer_nat_degree hn).symm.trans
      (nat_degree_eq_zero_iff_degree_le_zero.mpr (le_of_eq (degree_eq_zero_of_is_unit h)))) },
  suffices : ∀ f g : polynomial ℤ, selmer n = f * g → f.monic → g.monic → is_unit f ∨ is_unit g,
  { intros f g hfg,
    have key : f.leading_coeff * g.leading_coeff = 1,
    { rw [←leading_coeff_mul, ←hfg],
      exact selmer_monic hn },
    cases int.mul_eq_one_iff key with h h,
    { exact this f g hfg h.1 h.2 },
    { have key := this (-f) (-g) (hfg.trans (neg_mul_neg f g).symm)
        (f.leading_coeff_neg.trans (neg_eq_iff_neg_eq.mp h.1.symm))
        (g.leading_coeff_neg.trans (neg_eq_iff_neg_eq.mp h.2.symm)),
      exact or.imp (is_unit_neg f).mp (is_unit_neg g).mp key } },
  suffices : ∀ f g : polynomial ℤ, selmer n = f * g → f.monic → g.monic →
    f.eval 0 = 1 → g.eval 0 = -1 → f = 1 ∨ g = -1,
  { intros f g hfg hf hg,
    have key := selmer_eval_zero (zero_lt_one.trans hn),
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
