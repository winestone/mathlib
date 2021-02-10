import data.polynomial.reverse
import field_theory.polynomial_galois_group

namespace polynomial

--https://math.stackexchange.com/a/800835

lemma key_lemma (f g h : polynomial ℤ) (h1 : f.eval 0 ≠ 0) (h2 : is_coprime f f.reverse)
  (h3 : f = g * h) (h4 : nat_degree g ≠ 0) (h5 : nat_degree h ≠ 0) :
∃ k : polynomial ℤ, k.nat_degree = f.nat_degree ∧ f * f.reverse = k * k.reverse
∧ k ≠ f ∧ k ≠ - f ∧ k ≠ f.reverse ∧ k ≠ - f.reverse :=
begin
end

noncomputable def selmer (n : ℕ) : polynomial ℤ := X ^ n - X - 1

lemma nat_degree_selmer {n : ℕ} (hn : 1 < n) : (selmer n).nat_degree = n :=
begin
  rw [selmer, sub_sub, ←degree_eq_iff_nat_degree_eq_of_pos (zero_lt_one.trans hn)],
  refine eq.trans (degree_sub_eq_left_of_degree_lt _) (degree_X_pow n),
  rwa [degree_X_pow, ←C_1, degree_X_add_C, ←with_bot.coe_one, with_bot.coe_lt_coe],
end

lemma reverse_selmer {n : ℕ} (hn : 1 < n) : (selmer n).reverse = 1 - X ^ (n - 1) - X ^ n :=
begin
  rw [reverse, nat_degree_selmer hn, selmer],
  sorry,
end
