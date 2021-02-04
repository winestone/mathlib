/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import analysis.transcendental.liouville
import data.nat.factorial

/-!
# Liouville constants

This files contains a construction of a family of Liouville number.
The most important property is that they are examples of transcendental real numbers.
This fact is recorded in `is_liouville.is_transcendental_of_liouville_constant`.
-/

namespace is_liouville

noncomputable theory
open_locale nat big_operators classical
open set real finset

section m_is_real

variable {m : ℝ}

section lemmas_about_summability_and_sums

@[simp] lemma tsum_ite_eq' (i : ℕ) (a : ℝ) :
  ∑' n, (ite (n = i) a 0) = a :=
begin
  convert tsum_ite_eq i a,
  funext, congr,
end

lemma tsum_ite_eq_add {f : ℕ → ℝ} (hf : summable f) (i : ℕ) (a : ℝ) :
  ∑' n, ((ite (n = i) a 0) + f n) = a + ∑' n, f n :=
begin
  rw [tsum_add ⟨a, _⟩ hf, @tsum_eq_single ℝ _ _ _ _ _ i],
  { split_ifs; refl },
  { exact λ (j : ℕ) (ji : ¬ j = i), @if_neg _ _ ji _ _ _ },
  { convert has_sum_ite_eq i a,
    refine funext (λ x, _),
    congr }
end

lemma tsum_congr {f g : ℕ → ℝ} (hfg : ∀ n, f n = g n) :
  ∑' n, f n = ∑' n, g n :=
congr_arg tsum (funext hfg)

lemma tsum_ite_eq_extract {f : ℕ → ℝ} (hf : summable f) (i : ℕ) :
  ∑' n, f n = f i + ∑' n, ite (n ≠ i) (f n) 0 :=
by rw [← tsum_ite_eq_add (hf.summable_of_eq_zero_or_self (λ j, _)) i, tsum_congr (λ j, _)];
  by_cases ji : j = i; simp [ji]

lemma tsum_lt {f g : ℕ → ℝ} (h : ∀ (b : ℕ), f b ≤ g b)
  (hf: summable f) (hg: summable g) {i : ℕ} (hi : f i < g i) :
  ∑' n, f n < ∑' n, g n :=
begin
  rw [tsum_ite_eq_extract hf i, tsum_ite_eq_extract hg i],
  refine add_lt_add_of_lt_of_le hi (tsum_le_tsum (λ j, _) _ _),
  by_cases ji : j = i; simp [ji]; exact h j,
  { refine hf.summable_of_eq_zero_or_self (λ j, _),
    by_cases ji : j = i; simp [ji] },
  { refine hg.summable_of_eq_zero_or_self (λ j, _),
    by_cases ji : j = i; simp [ji] }
end

lemma tsum_lt_of_nonneg {f g : ℕ → ℝ} (h0 : ∀ (b : ℕ), 0 ≤ f b) (h : ∀ (b : ℕ), f b ≤ g b)
  (hg: summable g) {i : ℕ} (hi : f i < g i) :
  ∑' n, f n < ∑' n, g n :=
tsum_lt h (summable_of_nonneg_of_le h0 h hg) hg hi

variable (hm : 1 < m)

include hm

/-- An easy criterion for convergence of a series. -/
lemma summable_inv_pow_ge {ex : ℕ → ℕ} (exi : ∀ i, i ≤ ex i) :
  summable (λ i, 1 / (m : ℝ) ^ ex i) :=
begin
  refine summable_of_nonneg_of_le
    (λ a, one_div_nonneg.mpr (pow_nonneg (zero_le_one.trans hm.le) _)) (λ a, _)
    (summable_geometric_of_lt_1 (one_div_nonneg.mpr (zero_le_one.trans hm.le))
      ((one_div_lt (zero_lt_one.trans hm) zero_lt_one).mpr (by rwa one_div_one))),
  rw [div_pow, one_pow],
  refine (one_div_le_one_div _ _).mpr (pow_le_pow hm.le (exi a)),
  repeat { exact pow_pos (zero_lt_one.trans hm) _ }
end

/-- This series is explicitly proven, since it is used twice in the remaining lemmas. -/
lemma summable_inv_pow_n_add_fact (n : ℕ) :
  summable (λ i, 1 / (m : ℝ) ^ (i + (n + 1))!) :=
summable_inv_pow_ge hm (λ i, (nat.self_le_factorial _).trans (nat.factorial_le (nat.le.intro rfl)))

omit hm

section natural
open nat

-- the next two lemmas about factorials are in a PR from comm_semiring
lemma lt_factorial_self {n : ℕ} (hi : 3 ≤ n) : n < n! :=
begin
  rw [← succ_pred_eq_of_pos (lt_of_lt_of_le (zero_lt_two.trans (lt.base 2)) hi), factorial_succ],
  exact lt_mul_of_one_lt_right ((pred n).succ_pos) (lt_of_lt_of_le (lt_of_lt_of_le one_lt_two
    (le_pred_of_lt (succ_le_iff.mp hi))) (self_le_factorial _)),
end

lemma add_factorial_lt_factorial_add {i : ℕ} (n : ℕ) (hi : 2 ≤ i) :
  i + n.succ! < (i + n.succ)! :=
begin
  rw [succ_eq_add_one, ← add_assoc, factorial_succ (i + _), succ_eq_add_one, add_mul, one_mul],
  have : i ≤ i + n := le.intro rfl,
  exact add_lt_add_of_lt_of_le (lt_of_le_of_lt this ((lt_mul_iff_one_lt_right (lt_of_lt_of_le
    zero_lt_two (hi.trans this))).mpr (lt_iff_le_and_ne.mpr ⟨(i + n).factorial_pos, λ g,
    nat.not_succ_le_self 1 ((hi.trans this).trans (factorial_eq_one.mp g.symm))⟩))) (factorial_le
    ((le_of_eq (add_comm n 1)).trans ((add_le_add_iff_right n).mpr (one_le_two.trans hi)))),
end

lemma add_le_mul_two_add {R : Type*} [ordered_semiring R] [nontrivial R] {a b : R}
  (a2 : 2 ≤ a) (b0 : 0 ≤ b) : a + (2 + b) ≤ a * (2 + b) :=
calc a + (2 + b) ≤ a + (a + a * b) :
      add_le_add_left (add_le_add a2 (le_mul_of_one_le_left b0 (one_le_two.trans a2))) a
             ... ≤ a * (2 + b) :
      le_trans (le_trans (le_of_eq (add_assoc a a _).symm) (le_trans rfl.ge (add_le_add_right
      (le_of_eq (mul_two a).symm) _))) (le_of_eq (mul_add a 2 b).symm)

lemma add_le_mul {a b : ℕ} (a2 : 2 ≤ a) (b2 : 2 ≤ b) : a + b ≤ a * b :=
begin
  rcases le_iff_exists_add.mp b2 with ⟨k, rfl⟩,
  exact add_le_mul_two_add a2 k.zero_le
end

end natural

/-
omit hm
-/

theorem pow_le_pow_of_le_r {a : ℝ} {n m : ℕ} (a0 : 0 ≤ a) (a1 : a ≤ 1) (h : n ≤ m) : a ^ m ≤ a ^ n :=
pow_le_pow_of_le_one a0 a1 h

lemma calc_liou_one_le_no_calc_ep {ε : ℝ} (e0 : 0 ≤ ε) (e1 : ε ≤ 1) (n i : ℕ) :
ε ^ (i + (n + 1))! ≤ ε ^ i * ε ^ (n + 1)! :=
(pow_le_pow_of_le_one e0 e1 (i.add_factorial_le_factorial_add n.succ n.succ_ne_zero)).trans
  (le_of_eq (pow_add ε i (n + 1)!))

lemma one_div_pow_le_one_div_pow {R : Type*} [linear_ordered_field R] {a : R} (a1 : 1 ≤ a) {n m : ℕ} (h : n ≤ m) :
  1 / a ^ m ≤ 1 / a ^ n :=
(one_div_le_one_div (pow_pos (zero_lt_one.trans_le a1) _)
  (pow_pos (zero_lt_one.trans_le a1) _)).mpr (pow_mono a1 h)

lemma calc_liou_one_le_no_calc (m1 : 1 ≤ m) (n : ℕ) (i : ℕ) :
1 / m ^ (i + (n + 1))! ≤ 1 / m ^ i * 1 / m ^ (n + 1)! :=
begin
  refine (le_of_eq (one_div_pow (i + (n + 1))!).symm).trans ((calc_liou_one_le_no_calc_ep
    (one_div_nonneg.mpr (zero_le_one.trans m1)) ((one_div_le ((@zero_lt_one ℝ _ _).trans_le
      m1) zero_lt_one).mpr ((le_of_eq one_div_one).trans m1)) n i).trans
      (le_trans _ (le_of_eq (mul_div_assoc).symm))),
    rw ← one_div_pow,
    exact (mul_le_mul_left (pow_pos (one_div_pos.mpr
      ((@zero_lt_one ℝ _ _).trans_le m1)) i)).mpr (le_of_eq (one_div_pow _))
end

lemma calc_liou_one_le (m1 : 1 ≤ m) (n : ℕ) (i : ℕ) :
1 / m ^ (i + (n + 1))! ≤ (1 / m) ^ i * 1 / m ^ (n + 1)! :=
begin
  rw [one_div_pow],
  exact calc_liou_one_le_no_calc m1 n i,
end

lemma calc_liou_one_lt (m1 : 1 < m) (n : ℕ) (i : ℕ) (hi : 2 ≤ i) :
1 / m ^ (i + (n + 1))! < 1 / m ^ i * 1 / m ^ (n + 1)! :=
begin
  rw [mul_div_assoc, one_div_mul_one_div, ← pow_add],
  refine (one_div_lt_one_div _ _).mpr (pow_lt_pow m1 (add_factorial_lt_factorial_add n hi)),
  repeat { exact pow_pos (zero_lt_one.trans m1) _ },
end

--#exit

/--  Partial inequality, works with `m ∈ ℝ` and satisfying `1 < m`. -/
lemma calc_liou_one (m1 : 1 < m) (n : ℕ) :
∑' (i : ℕ), 1 / m ^ (i + (n + 1))! < m / (m - 1) * (1 / m ^ (n + 1)!) :=
begin
  have m0 : 0 < m := (lt_trans zero_lt_one m1),
  have mi : abs (1 / m) < 1,
  { rw abs_of_pos (one_div_pos.mpr m0),
    exact (div_lt_one m0).mpr m1 },

  have : (∑' (i : ℕ), (1 / m) ^ i) * (1 / m ^ (n + 1)!) = m / (m - 1) * (1 / m ^ (n + 1)!),
  { refine (mul_left_inj' (ne_of_gt (one_div_pos.mpr (pow_pos m0 _)))).mpr _,
    rw [tsum_geometric_of_abs_lt_1 mi, inv_eq_one_div],
    refine (div_eq_iff (ne_of_gt (sub_pos.mpr ((one_div_lt m0 zero_lt_one).mpr
      ((le_of_eq (div_one 1)).trans_lt m1))))).mpr _,
    rw [div_mul_eq_mul_div, mul_sub, mul_one, mul_one_div_cancel (ne_of_gt m0),
      div_self (ne_of_gt (sub_pos.mpr m1))] },
calc (∑' i, 1 / m ^ (i + (n + 1))!)
    < ∑' i, 1 / m ^ (i + (n + 1)!) : tsum_lt_of_nonneg
      (λ b, one_div_nonneg.mpr (pow_nonneg m0.le _))
      (λ b, (one_div_le_one_div (pow_pos m0 _) (pow_pos m0 _)).mpr
        (pow_le_pow m1.le (nat.add_factorial_le_factorial_add _ _ (nat.succ_ne_zero _))))
      (summable_inv_pow_ge m1 (λ j, nat.le.intro rfl))
      ((one_div_lt_one_div (pow_pos m0 _) (pow_pos m0 _)).mpr
        (pow_lt_pow m1 (add_factorial_lt_factorial_add n rfl.le)))
... = ∑' i, (1 / m) ^ i * (1 / m ^ (n + 1)!) :
    by { congr, ext i, rw [pow_add, div_pow, one_pow, ←div_div_eq_div_mul, div_eq_mul_one_div] }
... = (∑' i, (1 / m) ^ i) * (1 / m ^ (n + 1)!) : tsum_mul_right
... = m / (m - 1) * (1 / m ^ (n + 1)!) :
    begin
      rw [tsum_geometric_of_abs_lt_1 mi, show (m / (m - 1)) = ((m - 1) / m)⁻¹,
        by rw inv_div, sub_div, div_self (ne_of_gt m0)]
    end,
end

lemma le_pow_self {a : ℝ} {n : ℕ} (n0 : 0 < n) (a1 : 1 ≤ a) : a ≤ a ^ n :=
(le_of_eq (pow_one a).symm).trans (pow_mono a1 (nat.succ_le_iff.mpr n0))

lemma calc_liou_two_zero (n : ℕ) (hm : 2 ≤ m) :
  m / (m - 1) * (1 / m ^ (n + 1)!) ≤ 1 / (m ^ n!) ^ n :=
begin
  calc m / (m - 1) * (1 / m ^ (n + 1)!) ≤ 2 * (1 / m ^ (n + 1)!) :
    mul_le_mul ((div_le_iff (sub_pos.mpr ((@one_lt_two ℝ _ _).trans_le hm))).mpr
    (le_trans (le_sub.mpr ((le_of_eq (mul_one 2)).trans (has_le.le.trans hm (le_of_eq
    (eq_sub_iff_add_eq.mpr (two_mul m).symm))))) (le_of_eq (mul_sub 2 m 1).symm))) rfl.le
    (one_div_nonneg.mpr (le_of_lt (pow_pos (zero_lt_two.trans_le hm) (n + 1)!))) zero_le_two
  ... = 2 / m ^ (n + 1)! : mul_one_div 2 _
  ... = 2 / m ^ (n! * (n + 1)) : by rw [nat.factorial_succ, mul_comm]
  ... ≤ 1 / m ^ (n! * n) :
    begin
      rw [div_le_div_iff, one_mul],
      conv_rhs { rw [mul_add, pow_add, mul_one, pow_mul, mul_comm] },
      refine mul_le_mul (hm.trans (le_pow_self (nat.factorial_pos n) (one_le_two.trans hm)))
        (le_of_eq (pow_mul _ _ _)) (le_of_lt _) (le_of_lt _),
      any_goals { exact pow_pos (zero_lt_two.trans_le hm) _ },
    end
  ... = 1 / (m ^ n!) ^ n : by rw pow_mul
end

--strict inequality in the statement, but does not allow m = 2
lemma calc_liou_two (n : ℕ) (hm : 2 < m) :
  m / (m - 1) * (1 / m ^ (n + 1)!) < 1 / (m ^ n!) ^ n :=
calc m / (m - 1) * (1 / m ^ (n + 1)!) < 2 * (1 / m ^ (n + 1)!) :
  begin
    refine mul_lt_mul _ le_rfl (one_div_pos.mpr (pow_pos (zero_lt_two.trans hm) _)) zero_le_two,
    rwa [div_lt_iff, mul_sub, mul_one, lt_sub_iff_add_lt, two_mul, real.add_lt_add_iff_left],
    exact lt_sub_iff_add_lt.mpr (by { rw zero_add, exact (one_lt_two.trans hm) })
  end
  ... = 2 / m ^ (n + 1)! : mul_one_div 2 _
  ... = 2 / m ^ (n! * (n + 1)) : by rw [nat.factorial_succ, mul_comm]
  ... < 1 / m ^ (n! * n) :
  begin
    rw [div_lt_div_iff, one_mul],
    conv_rhs { rw [mul_add, pow_add, mul_one, pow_mul, mul_comm] },
    apply mul_lt_mul,
    { refine hm.trans_le _,
      conv_lhs { rw ← pow_one m },
      exact pow_le_pow (one_le_two.trans hm.le) (nat.factorial_pos _) },
    { rw pow_mul },
    any_goals { try {refine le_of_lt _}, exact pow_pos (zero_lt_two.trans hm) _ }
  end
  ... = 1 / (m ^ n!) ^ n : by rw pow_mul

end lemmas_about_summability_and_sums

/--
liouville constant is
$$
\sum_{i=0}^\infty\frac{1}{m^{i!}}
$$
where `2 < m`
-/
def liouville_constant (m : ℝ) := ∑' (i : ℕ), 1 / m ^ i!
/--
`liouville_constant_first_k_terms` is the first `k` terms of the liouville constant, i.e
$$
\sum_{i=0}^k\frac{1}{m^{i!}}
$$
where `2 < m`
-/
def liouville_constant_first_k_terms (m : ℝ) (k : ℕ) := ∑ i in range (k+1), 1 / m ^ i!
/--
`liouville_constant_terms_after_k` is all the terms start from `k+1` of the liouville constant, i.e
$$
\sum_{i=k+1}^\infty\frac{1}{m^{i!}}
$$
where `2 < m`
-/
def liouville_constant_terms_after_k (m : ℝ) (k : ℕ) :=  ∑' i, 1 / m ^ (i + (k+1))!

lemma liouville_constant_terms_after_pos (hm : 1 < m) :
  ∀ k, 0 < liouville_constant_terms_after_k m k := λ n,
calc 0 < 1 / (m : ℝ) ^ (n + 1)! : one_div_pos.mpr (pow_pos (lt_trans zero_lt_one hm) _)
  ... = 1 / (m : ℝ) ^ (0 + (n + 1))! : by rw zero_add
  ... ≤ ∑' (i : ℕ), 1 / (m : ℝ) ^ (i + (n + 1))! :
      le_tsum (summable_inv_pow_n_add_fact hm _) 0
        (λ i i0, one_div_nonneg.mpr (pow_nonneg (zero_le_one.trans hm.le) _))

lemma liouville_constant_eq_first_k_terms_add_rest (hm : 1 < m) (k : ℕ):
  liouville_constant m = liouville_constant_first_k_terms m k +
  liouville_constant_terms_after_k m k :=
(sum_add_tsum_nat_add _ (summable_inv_pow_ge hm (λ i, nat.self_le_factorial i))).symm

end m_is_real


section m_is_natural

variable {m : ℕ}

lemma rat_of_liouville_constant_first_k_terms (hm : 1 < m) (k : ℕ) :
∃ p : ℕ, liouville_constant_first_k_terms m k = p / (m ^ k!) :=
begin
  induction k with k h,
  { exact ⟨1, by rw [liouville_constant_first_k_terms, range_one, sum_singleton, nat.cast_one]⟩ },
  { rcases h with ⟨p_k, h_k⟩,
    use p_k * (m ^ ((k + 1)! - k!)) + 1,
    unfold liouville_constant_first_k_terms at h_k ⊢,
    rw [sum_range_succ, h_k, div_add_div, div_eq_div_iff, one_mul, add_mul],
    { norm_cast,
      rw [add_mul, one_mul, nat.factorial_succ, show k.succ * k! - k! = (k.succ - 1) * k!,
        by rw [nat.mul_sub_right_distrib, one_mul], nat.succ_sub_one, nat.succ_eq_add_one, add_mul,
        one_mul, pow_add], ring },
    refine mul_ne_zero_iff.mpr ⟨_, _⟩,
    all_goals { refine pow_ne_zero _ _, exact_mod_cast ne_of_gt (lt_trans zero_lt_one hm), } }
end

theorem is_liouville_liouville_constant (hm : 2 ≤ m) :
  is_liouville (liouville_constant m) :=
begin
  have mZ1 : 1 < (m : ℤ) := lt_of_le_of_lt (le_of_eq nat.cast_one.symm)
    (lt_of_lt_of_le one_lt_two ((le_of_eq nat.cast_two.symm).trans (int.to_nat_le.mp hm))),
  have m1 : 1 < (m : ℝ) :=
    lt_of_lt_of_le one_lt_two ((le_of_eq nat.cast_two.symm).trans (nat.cast_le.mpr hm)),
  intro n,
  have h_truncation_wd := liouville_constant_eq_first_k_terms_add_rest m1 n,
  rcases rat_of_liouville_constant_first_k_terms (lt_of_lt_of_le one_lt_two hm) n with ⟨p, hp⟩,
  refine ⟨p, m ^ n!, one_lt_pow mZ1 (nat.factorial_pos n), _⟩,
  push_cast,
  rw [← hp, h_truncation_wd, add_sub_cancel', abs_of_pos (liouville_constant_terms_after_pos m1 _)],
  exact ⟨ne_of_gt ((lt_add_iff_pos_right _).mpr (liouville_constant_terms_after_pos m1 n)),
    lt_of_lt_of_le (calc_liou_one m1 n) (calc_liou_two_zero _ ((le_of_eq nat.cast_two.symm).trans
      (nat.cast_le.mpr hm)))⟩
end

lemma is_transcendental_liouville_constant (hm : 2 ≤ m) :
  is_transcendental ℤ (liouville_constant m) :=
transcendental_of_is_liouville (is_liouville_liouville_constant hm)

end m_is_natural

end is_liouville
