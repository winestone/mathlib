import analysis.complex.automorphisms_half_plane
import analysis.complex.basic
import data.matrix.notation
--import data.int.basic
import data.int.parity
--import data.nat.gcd
import algebra.ordered_ring
--import ring_theory.int.basic
import data.real.sqrt
import linear_algebra.affine_space.affine_subspace

open complex
open matrix
open matrix.special_linear_group
noncomputable theory


local notation `|` x `|` := _root_.abs x
local notation `SL(` n `,` R `)`:= special_linear_group (fin n) R

local attribute [instance] fintype.card_fin_even

open_locale upper_half_plane
open upper_half_plane

-- special linear group over ℤ

/-- The action of `SL(2, ℤ)` on the upper half-plane, as a restriction of the `SL(2, ℝ)`-action. -/
instance SL2Z_action : mul_action SL(2, ℤ) ℍ :=
mul_action.comp_hom ℍ (SL_n_insertion (int.cast_ring_hom ℝ))

@[simp]
lemma smul_def_int (g : SL(2,ℤ)) (z : ℍ) : g • z = smul_aux g z :=
begin
  refl,
end

lemma smul_neg_SL2_int (g : SL(2,ℤ)) (z : ℍ) : -g • z = g • z :=
by simpa [← special_linear_group.has_neg_cast g] using smul_neg_SL2 ↑g z

@[simp] lemma bottom_def_int {g : SL(2,ℤ)} {z : ℍ} : bottom g z = g 1 0 * z + g 1 1 :=
begin
  simp [bottom],
  congr' 1,
  { congr' 1,
    norm_cast },
  { norm_cast },
end

@[simp] lemma top_def_int {g : SL(2,ℤ)} {z : ℍ} : top g z = g.1 0 0 * z + g.1 0 1 :=
begin
  simp [top],
  congr' 1,
  { congr' 1,
    norm_cast },
  { norm_cast },
end

lemma matrix.special_linear_group.im_smul_int (g : SL(2, ℤ)) (z : ℍ) :
  (g • z).im = z.im / (complex.norm_sq (bottom g z)) :=
by simpa using matrix.special_linear_group.im_smul g z
--lemma im_smul_SL'' (g : SL(2, ℤ)) (z : ℍ) :
--(g • z).val.im = z.val.im / (complex.norm_sq (bottom g z)) :=
--im_smul_mat_complex

lemma bottom_ne_zero_int (g : SL(2, ℤ)) (z : ℍ) : bottom g z ≠ 0 :=
bottom_ne_zero g z

@[simp] lemma smul_coe {g : SL(2,ℤ)} {z : ℍ} : (g : SL(2,ℝ)) • z = g • z := rfl


/-! It is useful to develop basic theory for an object `coprime_ints`, consisting of two integers
and a proof that they satisfy `is_coprime`. -/

class coprime_ints :=
(c' : ℤ)
(d' : ℤ)
(is_coprime' : is_coprime c' d')

namespace coprime_ints

def c (p : coprime_ints) : ℤ := p.c'
def d (p : coprime_ints) : ℤ := p.d'

lemma is_coprime (p : coprime_ints) : is_coprime p.c p.d  := p.is_coprime'

instance : has_coe coprime_ints (ℤ × ℤ) := ⟨λ p, (p.c, p.d)⟩

instance : nonempty coprime_ints := ⟨⟨1, 1, is_coprime_one_left⟩⟩

@[simp] lemma fst_coe (p : coprime_ints) : (p : ℤ × ℤ).1 = p.c := rfl
@[simp] lemma snd_coe (p : coprime_ints) : (p : ℤ × ℤ).2 = p.d := rfl

@[ext] lemma ext {p q : coprime_ints} (h : (p : ℤ × ℤ) = q) : p = q :=
begin
  tactic.unfreeze_local_instances,
  cases p,
  cases q,
  cases h,
  refl,
end

lemma coe_injective : function.injective (coe : coprime_ints → (ℤ × ℤ)) :=
λ p q, ext

lemma ne_zero (p : coprime_ints) : p.c ≠ 0 ∨ p.d ≠ 0 :=
begin
  rw ← not_and_distrib,
  rintros ⟨c_eq_zero, d_eq_zero⟩,
  simpa [c_eq_zero, d_eq_zero] using p.is_coprime
end

lemma sum_sq_ne_zero (p : coprime_ints) : p.c ^ 2 + p.d ^ 2 ≠ 0 :=
begin
  intros h,
  have c_eq_zero : p.c = 0 := by nlinarith,
  have d_eq_zero : p.d = 0 := by nlinarith,
  cases p.ne_zero with hc hd; contradiction
end

end coprime_ints


lemma bottom_row_coprime (g : SL(2, ℤ)) : is_coprime (g 1 0) (g 1 1) :=
begin
  rw is_coprime,
  use [( - g 0 1), (g 0 0)],
  calc _ = matrix.det g : _
  ... = 1 : by rw g.det_coe_fun,
  simp [matrix.det_succ_row_zero, fin.sum_univ_succ],
  ring,
end

def bottom_row : SL(2, ℤ) → coprime_ints := λ g, ⟨g 1 0, g 1 1, bottom_row_coprime g⟩

lemma bottom_row_surj : function.surjective bottom_row :=
begin
  intros cd,
  obtain ⟨b₀, a, gcd_eqn⟩ := cd.is_coprime,
  let A := ![![a ,-b₀ ], ![cd.c, cd.d]],
  have det_A_1 : det A = 1,
  {

    sorry,
  },
  use ⟨ A, det_A_1⟩ ,
  rw bottom_row,
  simp [A],
  ext,
  simp, -- classic explicit-matrix-in-SL casting problem
  repeat {sorry},
  -- ext,
end




section finite_pairs

open filter continuous_linear_map

-- where should this lemma live?
/-- The `norm_sq` function on `ℂ` is proper. -/
lemma tendsto_at_top_norm_sq : tendsto norm_sq (cocompact ℂ) at_top :=
begin
  convert tendsto_norm_cocompact_at_top.at_top_mul_at_top tendsto_norm_cocompact_at_top,
  { simp [mul_self_abs] },
  { apply_instance },
  { apply_instance }
end


lemma finite_pairs (z : ℍ) :
  filter.tendsto (λ p : coprime_ints , ((p.c : ℂ) * z + p.d).norm_sq)
  cofinite at_top :=
begin
  let f : ℝ × ℝ →ₗ[ℝ] ℂ := (linear_map.fst ℝ ℝ ℝ).smul_right (z:ℂ)
    + (linear_map.snd ℝ ℝ ℝ).smul_right 1,
  have hf : f.ker = ⊥,
  { let g : ℂ →ₗ[ℝ] ℝ × ℝ := im_lm.prod (im_lm.comp (((z:ℂ) • conj_lm ))),
    suffices : ((z:ℂ).im⁻¹ • g).comp f = linear_map.id,
    { exact linear_map.ker_eq_bot_of_inverse this },
    apply linear_map.ext,
    rintros ⟨c₁, c₂⟩,
    have hz : 0 < (z:ℂ).im := z.2,
    have : (z:ℂ).im ≠ 0 := hz.ne.symm,
    field_simp,
    ring },
  have h₁ := (linear_equiv.closed_embedding_of_injective hf).tendsto_cocompact,
  have h₂ : tendsto (λ p : ℤ × ℤ, ((p.1 : ℝ), (p.2 : ℝ))) cofinite (cocompact _),
  { convert int.tendsto_coe_cofinite.prod_map_coprod int.tendsto_coe_cofinite;
    simp [coprod_cocompact, coprod_cofinite] },
  convert tendsto_at_top_norm_sq.comp (h₁.comp (h₂.comp coprime_ints.coe_injective.tendsto_cofinite)),
  ext,
  simp [f],
end

end finite_pairs



section
/-! This is an attempt to do the maximin argument using more abstract existence theory. -/

open filter

instance {α : Type*} [normed_ring α] {n m : Type*} [fintype n] [fintype m] :
  normed_group (matrix n m α) :=
pi.normed_group

instance {α : Type*} [normed_field α] {n m : Type*} [fintype n] [fintype m] :
  normed_space α (matrix n m α) :=
pi.normed_space


/- Non-crap lemma but put it elsewhere ?  Maybe cocompact in discrete is cofinite -/
lemma cocompact_ℝ_to_cofinite_ℤ (ι : Type*) [fintype ι] :
  tendsto ((λ (p : ι → ℤ), (coe : ℤ → ℝ) ∘ p)) cofinite (cocompact (ι → ℝ)) :=
by simpa [←Coprod_cofinite,←Coprod_cocompact]
  using tendsto.pi_map_Coprod (λ i, int.tendsto_coe_cofinite)


/- Non-crap lemma: ℤ -matrices are cofinite inside comcompact ℝ matrices -/
lemma cocompact_ℝ_to_cofinite_ℤ_matrix {ι ι' : Type*} [fintype ι] [fintype ι']  :
  tendsto (λ m, matrix.map m (coe : ℤ → ℝ)) cofinite (cocompact (matrix ι ι' ℝ)) :=
begin
  convert tendsto.pi_map_Coprod (λ i, cocompact_ℝ_to_cofinite_ℤ ι'),
  { exact Coprod_cofinite.symm },
  { exact Coprod_cocompact.symm }
end


/- generalize to arbitrary matrix index sets and move to matrix file -/
def matrix.coord (i j : fin 2) : (matrix (fin 2) (fin 2) ℝ) →ₗ[ℝ] ℝ :=
(linear_map.proj j : (fin 2 → ℝ) →ₗ[ℝ] _).comp (linear_map.proj i)

def acbd (p : coprime_ints) : (matrix (fin 2) (fin 2) ℝ) →ₗ[ℝ] ℝ :=
p.c • matrix.coord 0 0 + p.d • matrix.coord 0 1

def useful_matrix (cd : coprime_ints) : (matrix (fin 2) (fin 2) ℝ) := ![![(cd.c:ℝ), cd.d],![cd.d,-cd.c]]

/-- map sending the matrix [a b; c d] to `(ac₀+bd₀ , ad₀ - bc₀, c, d)`, for some fixed `(c₀, d₀)` -/
def line_map (cd : coprime_ints) : (matrix (fin 2) (fin 2) ℝ) →ₗ[ℝ] ((fin 2 → ℝ) × (fin 2 → ℝ)) :=
((useful_matrix cd).mul_vec_lin.comp (linear_map.proj 0 : (matrix (fin 2) (fin 2) ℝ) →ₗ[ℝ] _)).prod (linear_map.proj 1)
  --((acbd cd).prod ((cd.d : ℝ) • matrix.coord 0 0 - (cd.c : ℝ) • matrix.coord 0 1)).prod (linear_map.proj 1)

lemma lin_indep_acbd (cd : coprime_ints) : (line_map cd).ker = ⊥ :=
begin
  rw linear_map.ker_eq_bot,
--  apply function.left_inverse.injective,
  -- let g : (ℝ × ℝ) → ℝ := λ
  let g : matrix (fin 2) (fin 2) ℝ := ((cd.c)^2+(cd.d)^2:ℝ)⁻¹ • ![![-cd.c, -cd.d],![-cd.d,cd.c]],

  let f₁ : (fin 2 → ℝ) → (fin 2 → ℝ) := g.mul_vec_lin,
  --(ℝ × ℝ) → (fin 2 → ℝ) := sorry,
  -- λ ⟨ x,y⟩,
  let f : (fin 2 → ℝ) × (fin 2 → ℝ) → matrix (fin 2) (fin 2) ℝ := λ ⟨ x , cd⟩  , λ i, ite (i=0) (f₁ x) (cd),
  have : function.left_inverse f (line_map cd),
  {
    sorry,
  },
  exact this.injective,
end

/-- Big filter theorem -/
theorem big_thm (cd : coprime_ints) :
  tendsto (λ g : bottom_row ⁻¹' {cd}, acbd cd ↑g) cofinite (cocompact ℝ) :=
begin
  let cd' : fin 2 → ℤ :=  λ i, if i = 0 then cd.c else cd.d,
  let mB : ℝ → ((fin 2 → ℝ) × (fin 2 → ℝ)) := λ t, ((t, 1), coe ∘ cd'),
  have hmB : continuous mB := (continuous_id.prod_mk continuous_const).prod_mk continuous_const,
  convert filter.tendsto.of_tendsto_comp _ (comap_cocompact hmB),
  let f₁ : SL(2, ℤ) → matrix (fin 2) (fin 2) ℝ := λ g, matrix.map (↑g : matrix _ _ ℤ) (coe : ℤ → ℝ),
  have hf₁ : tendsto f₁ cofinite (cocompact _) :=
    cocompact_ℝ_to_cofinite_ℤ_matrix.comp subtype.coe_injective.tendsto_cofinite,
  have hf₂ := (linear_equiv.closed_embedding_of_injective (lin_indep_acbd cd)).tendsto_cocompact,
  convert hf₂.comp (hf₁.comp subtype.coe_injective.tendsto_cofinite) using 1,
  funext g,
  obtain ⟨g, hg⟩ := g,
  simp [mB, f₁, cd', line_map, matrix.coord],
  simp [bottom_row] at hg,
  split,
  { norm_cast,
    rw ← g.det_coe_matrix,
    sorry }, -- both of these are just algebra: ALEX HOMEWORK
  { ext i,
    fin_cases i,
    simp [←hg],
    simp [hg],
  sorry }
end


lemma something2 (p : coprime_ints) (z : ℍ) :
  ∃ (w : ℂ), ∀ g : bottom_row ⁻¹' {p},
  ↑((g : SL(2, ℤ)) • z) = ((acbd p ↑g) : ℂ ) / (p.c ^ 2 + p.d ^ 2) + w :=
begin
  use (((p.d:ℂ )* z - p.c)*(p.c * (z:ℂ).conj + p.d) ) /
    ((p.c ^ 2 + p.d ^ 2) * (((p.c : ℂ) * z + p.d) * ((p.c : ℂ) * (z:ℂ).conj + p.d))),
  have nonZ1 : (((p.c : ℂ) * z + p.d) * ((p.c : ℂ) * (z:ℂ).conj + p.d))  ≠ 0 := sorry,
  have nonZ2 : (p.c : ℂ) ^ 2 + (p.d) ^ 2 ≠ 0 := sorry,
  intro g,
  field_simp [nonZ1,nonZ2],
  simp [acbd, smul_aux, smul_aux'],
  change ((top _ _) / (bottom _ _) * _) = _,
  field_simp [bottom_ne_zero],
  simp [top, bottom, matrix.coord],
  -- Heather homework :)
  sorry,
end


lemma junk11 (z w u :ℂ) (h: z=w+u) : z.re=w.re+u.re :=
begin
  sorry,
end

lemma something1 (p : coprime_ints) (z : ℍ) :
  ∃ w, ∀ g : bottom_row ⁻¹' {p},
  ((g : SL(2, ℤ)) • z).re = (acbd p ↑g) / (p.c ^ 2 + p.d ^ 2) + w :=
begin
  obtain ⟨w, hw⟩ := something2 p z,
  use w.re,
  intros g,
  convert junk11 _ _ _ (hw g),
  norm_cast,
end



/-- Add simp lemma to topology.algebra.group -/
@[simp] lemma homeomorph.add_right_apply {G : Type*} [topological_space G] [add_group G]
[has_continuous_add G] (a : G) (g : G) :
--⇑(homeomorph.add_right g h) = λ (x : α), x * c
homeomorph.add_right a g = g + a := rfl

/-- Add to topology.homeomorph -/
@[simp] theorem homeomorph.trans_apply {α : Type*} {β : Type*} {γ : Type*} [topological_space α]
[topological_space β] [topological_space γ] (h₁ : α ≃ₜ β) (h₂ : β ≃ₜ γ) (a : α) :
h₁.trans h₂ a = h₂ (h₁ a) := rfl


/- final filter lemma, deduce from previous two results -/
lemma something' (z:ℍ) (p : coprime_ints) :
  tendsto (λ g : bottom_row ⁻¹' {p}, _root_.abs (((g : SL(2, ℤ)) • z).re)) cofinite at_top :=
begin
  suffices : tendsto (λ g : bottom_row ⁻¹' {p}, (((g : SL(2, ℤ)) • z).re)) cofinite (cocompact ℝ),
  { exact tendsto_norm_cocompact_at_top.comp this },
  obtain ⟨w, hw⟩ := something1 p z,
  have : ((p.c : ℝ) ^ 2 + p.d ^ 2)⁻¹ ≠ 0,
  { apply inv_ne_zero,
    exact_mod_cast p.sum_sq_ne_zero },
  let f := homeomorph.mul_right' _ this,
  let ff := homeomorph.add_right w,
  convert ((f.trans ff).closed_embedding.tendsto_cocompact).comp (big_thm p),
  ext g,
  convert hw g,
end

/- the upshot of all the filter stuff -/
lemma exists_g_with_given_cd_and_min_re (z:ℍ) (cd : coprime_ints) :
  ∃ g : SL(2,ℤ), bottom_row g = cd ∧ (∀ g' : SL(2,ℤ), bottom_row g = bottom_row g' →
  _root_.abs ((g • z).re) ≤ _root_.abs ((g' • z).re)) :=
begin
  haveI cdNonEmpt :  (bottom_row ⁻¹' {cd}).nonempty :=
  begin
    convert set.nonempty.preimage _ bottom_row_surj,
    exact set.singleton_nonempty cd,
  end,
  haveI cdNonEmpt2 : nonempty (bottom_row ⁻¹' {cd}) :=
  begin
--    have :=  nonempty.map _ cdNonEmpt,
    convert cdNonEmpt,
    simp,
--    split,
 --   intros,
    sorry, -- COME ON!!! -- HEATHER HELP
  end,
  obtain ⟨g, hg⟩  := filter.tendsto.exists_forall_le (something' z cd),
  use g,
  split,
  { exact g.2 },
  { intros g1 hg1,
    have : g1 ∈ (bottom_row ⁻¹' {cd}),
    {
      rw [set.mem_preimage, set.mem_singleton_iff],
      exact eq.trans hg1.symm (set.mem_singleton_iff.mp (set.mem_preimage.mp g.2)),
    },
    exact hg ⟨g1, this⟩ },
end


lemma exists_g_with_min_bottom (z : ℍ) :
  ∃ g : SL(2,ℤ), ∀ g' : SL(2,ℤ), (bottom g z).norm_sq ≤ (bottom g' z).norm_sq  :=
begin
  obtain ⟨p, hp⟩ := (finite_pairs z).exists_forall_le,
  obtain ⟨g, hg⟩ := bottom_row_surj p,
  use g,
  intros g',
  convert hp (bottom_row g'),
  { simp [bottom_row] at hg,
    simp [bottom, ← hg],
    sorry, -- HEATHER HELP
  },
  simp [bottom_row, bottom], -- HEATHER HELP
  sorry,-- classic explicit-matrix-in-SL casting problem
end

lemma exists_g_with_max_Im (z : ℍ) :
  ∃ g : SL(2,ℤ), ∀ g' : SL(2,ℤ), (g' • z).im ≤ (g • z).im :=
begin
  obtain ⟨g, hg⟩ := exists_g_with_min_bottom z,
  use g,
  intros g',
  rw [matrix.special_linear_group.im_smul_int, matrix.special_linear_group.im_smul_int,
    div_le_div_left],
  { exact hg g' },
  { exact z.im_pos },
  { exact normsq_bottom_pos g' z },
  { exact normsq_bottom_pos g z },
end



-- T and S

def T : SL(2,ℤ) := { val := ![![1, 1], ![0, 1]], property :=
by simp [matrix.det_succ_row_zero, fin.sum_univ_succ] }

def T' : SL(2,ℤ) := { val := ![![1, -1], ![0, 1]], property :=
by simp [matrix.det_succ_row_zero, fin.sum_univ_succ] }

def S : SL(2,ℤ) := { val := ![![0, -1], ![1, 0]], property :=
by simp [matrix.det_succ_row_zero, fin.sum_univ_succ] }


def fundamental_domain : set ℍ :=
{ z | 1 ≤ (complex.norm_sq z) ∧ |(complex.re z)| ≤ (1 :ℝ)/ 2 }

def fundamental_domain_open : set ℍ :=
{ z | 1 < (complex.norm_sq z) ∧ |(complex.re z)| < (1 :ℝ)/ 2 }

notation `𝒟` := fundamental_domain

notation `𝒟ᵒ` := fundamental_domain_open


lemma whatever : 𝒟 = closure 𝒟ᵒ :=
begin

  sorry,
end

lemma S_bottom (z : ℍ) : bottom S z = (z:ℂ) :=
begin
  rw [bottom, S],
  simp,
  sorry, --- HEATHER HELP?
end

lemma S_action_im (z : ℍ) : (S • z).im = z.im / norm_sq z :=
begin
  rw matrix.special_linear_group.im_smul_int,
  have nonZ1 : norm_sq (bottom S z) ≠ 0 := normsq_bottom_ne_zero S z,
  have nonZ2 : norm_sq z ≠ 0 := norm_sq_nonzero z,

  field_simp [nonZ1, nonZ2],
  left,
  rw ← S_bottom z,
  congr,
end

lemma im_lt_im_S {z : ℍ} (h: norm_sq z < 1) : z.im < (S • z).im :=
begin
  have : z.im < z.im / norm_sq (z:ℂ),
  { have imz : 0 < z.im := im_pos z,
    apply (lt_div_iff z.norm_sq_pos).mpr,
    nlinarith },
  convert this,
  exact S_action_im z,
end


lemma T_action_re (z : ℍ) : (T • z).re = z.re + 1 :=
begin
  sorry, --- HEATHER HELP?
--  convert @smul_sound T z, -- WHat is `smul_sound`???
  simp only [smul_aux_def, top, bottom, T, has_coe_SL_apply, subtype.coe_mk, map_cons],
  simp [special_linear_group.cons_apply_zero, special_linear_group.cons_apply_one],
end

lemma T'_action_re (z : ℍ) : (T' • z).re = z.re - 1 :=
begin
  sorry, --- HEATHER HELP?
--  convert @smul_sound T z, -- WHat is `smul_sound`???
  simp only [smul_aux_def, top, bottom, T, has_coe_SL_apply, subtype.coe_mk, map_cons],
  simp [special_linear_group.cons_apply_zero, special_linear_group.cons_apply_one],
end

lemma half_ge_x_T_inv (z : ℍ) (h : 1/2 < z.re) : |(T' • z).re| < |z.re| :=
begin
  have : |z.re - 1| < |z.re|,
  { rw [(abs_eq_self.mpr (by linarith : 0 ≤ z.re)), abs_lt],
    split; linarith, },
  convert this,
  exact T'_action_re z,
end

lemma half_le_neg_x_T (z : ℍ) (h : 1/2 < - z.re) : |(T • z).re| < |z.re| :=
begin
  have : |z.re + 1| < |z.re|,
  { rw [(abs_eq_neg_self.mpr (by linarith : z.re ≤ 0)), abs_lt],
    split; linarith, },
  convert this,
  exact T_action_re z,
end

lemma bottom_row_eq_bottom_eq_int (g h : SL(2,ℤ)) (z : ℍ) (bot_eq : bottom_row g = bottom_row h) :
  (bottom g z) = (bottom h z) :=
begin
  rw bottom,
  rw bottom,
  rw bottom_row at bot_eq,
  sorry, --- HEATHER HELP?
end

lemma bottom_row_T (g : SL(2,ℤ)) : bottom_row g = bottom_row (T * g) :=
begin
  rw bottom_row,
  rw T,
  sorry, --- HEATHER HELP?
end

lemma bottom_row_T' (g : SL(2,ℤ)) : bottom_row g = bottom_row (T' * g) :=
begin
  rw bottom_row,
  rw T', --- HEATHER HELP?
  sorry,
end

lemma trivial_ineq1 (x:ℝ) (h₁ : x < -((1:ℝ) / 2)) : |x+1| < |x| :=
begin
  have : x < 0 := by linarith,
  rw abs_of_neg this,
  by_cases (x < -1),
  { have : x+1 <0 := by linarith,
    rw abs_of_neg this,
    linarith },
  { push_neg at h,
    have : 0 ≤ x+1  := by linarith,
    rw _root_.abs_of_nonneg this,
    linarith },
end

lemma trivial_ineq2 (x:ℝ) (h₁ : ((1:ℝ) / 2)< x ) : |x-1| < |x| :=
begin
  have : 0 < x := by linarith,
  rw abs_of_pos this,
  by_cases (1 < x),
  { have : 0 < x-1 := by linarith,
    rw abs_of_pos this,
    linarith },
  { push_neg at h,
    have : x-1 ≤ 0 := by linarith,
    rw _root_.abs_of_nonpos this,
    linarith },
end


lemma fun_dom_lemma₁ (z:ℍ) : ∃ (g: SL(2,ℤ)), (g • z) ∈ 𝒟 :=
begin
/-
  human argument:

  filtery stuff tells us that we maximize im,
  implies |gz|>=1
  -- argument is: if |gz|<1, then S increases im.
  -- contrapos: if S does not increase im, then |gz|>=1

   then among those, minimize re
  -- contrapos: if neither T nor T' decrease |re|, then |re|<=1/2

-/
  obtain ⟨g₀, hg₀ ⟩ := exists_g_with_max_Im z,
  obtain ⟨g, hg, hg'⟩ := exists_g_with_given_cd_and_min_re z (bottom_row g₀),
  use g,
  have hg₀' : ∀ (g' : SL(2,ℤ)), (g' • z).im ≤ (g • z).im,
  {
    have hg'' : (g • z).im = (g₀ • z).im,
    {
      rw matrix.special_linear_group.im_smul_int g z,
      rw matrix.special_linear_group.im_smul_int g₀ z,
      have nonZ1 : norm_sq (bottom g z) ≠ 0 := normsq_bottom_ne_zero g z,
      have nonZ2 : norm_sq (bottom g₀ z) ≠ 0 := normsq_bottom_ne_zero g₀ z,
      field_simp [nonZ1, nonZ2],
      left,
      exact congr_arg norm_sq (bottom_row_eq_bottom_eq_int g₀ g z hg.symm),
    },
    intros g',
    have := hg₀ g',
    linarith,
  },
  split,
  {
    contrapose! hg₀',
    have := im_lt_im_S hg₀',
    use S * g,
    convert this using 2,
    exact mul_smul S g z,
  },
  {
    rw abs_le,
    split,
    {
      contrapose! hg',
      use T*g,
      split,
      {
        exact bottom_row_T g,
      },
      {
        convert trivial_ineq1 ((g • z).re) hg',
        convert T_action_re (g • z) using 1,
        simp [mul_action.mul_smul],
      },
    },
    {
      contrapose! hg',
      use T'*g,
      split,
      {
        exact bottom_row_T' g,
      },
      {
        convert trivial_ineq2 ((g • z).re) hg',
        convert T'_action_re (g • z) using 1,
        simp [mul_action.mul_smul],
      },
    },
  },
end

lemma fun_dom_lemma₂ (z : ℍ) (g : SL(2,ℤ)) (hz : z ∈ 𝒟ᵒ) (hg : g • z ∈ 𝒟ᵒ) : z = g • z :=
begin
/-
  either c=0 in which case, translation, in which case translation by 0
  or im (y) > Sqrt(3)/2 -> c=±1 and compute...

-/
  sorry,
end

----- THE REST is superfluous ??
/-
lemma fun_dom_lemma (z:ℍ) (h: z∉𝒟) : ∃ (g: SL(2,ℤ)),
(|(g • z).re| < |z.re|) ∨ (complex.abs ↑(g • z) > complex.abs z) :=
begin
  have : 1/2 < |z.re| ∨
end


-- keep contents but not lemma
lemma re_ge_half_of_act_T {z : ℍ}
(h: 1/2 < |(z:ℂ).re|
:
(|(T • z).re| < |z.re|) ∨
(|(T' • z).re| < |z.re|)
:=
begin
  rw T_action,
  rw T_inv_action,
  let x := z.val.re,
  simp,
  rw lt_abs at h,
  cases h,
  { right,
    convert (half_ge_x_T_inv ((z:ℂ).re) h),
    exact _root_.abs_of_nonneg (by linarith) },
  { left,
    exact half_le_neg_x_T (z:ℂ).re h },
end
------------------------------------

lemma find_g_with_min_re (z:ℍ) (cd : coprime_ints) :
∃ g : SL(2,ℤ), bottom_row g = cd ∧ (∀ g' : SL(2,ℤ),  bottom_row g = bottom_row g' →
_root_.abs ((g • z).val.re) ≤ _root_.abs ((g' • z).val.re)) :=
begin
-  -- Argh this is all wrong;
-- Need to look somehow at the set of all preimages of cd
-- among those, choose g with minimal real part
-- the rest is tautological
  obtain ⟨g, hg⟩ := bottom_row_surj cd,
  use g,
  split,
  exact hg,
  intros g' hg',
  by_contradiction hcontra,
  push_neg at hcontra,
  obtain ⟨n, hn⟩ := bot_row_eq_diff_by_T_n g g' hg',
  rw hn at hcontra,
  -
  sorry,
end



lemma is_fundom {z : ℍ} : ∃ g : SL(2,ℤ), g • z ∈ 𝒟 :=
begin
  obtain ⟨g, hg2⟩ := exists_g_with_max_Im z,
  obtain ⟨n, hn⟩ := find_appropriate_T ((g : SL(2,ℤ)) • z),
  use (T^n * g),
  have hS : S ∈ G' := by {apply subgroup.mem_closure', simp},
  have hT : T ∈ G' := by {apply subgroup.mem_closure', simp},
  have hTn : T^n ∈ G' := by {apply subgroup.gpow_mem G' hT},
--  have hTng : T^n * g ∈ G' := G'.mul_mem hTn hg1,
--  have hSTg : S * T^n * g ∈ G' := G'.mul_mem (G'.mul_mem hS hTn) hg1,
  replace hg2 := hg2 (S * T^n * g), -- hSTg,
  set z' := (T^n * g) • z with z'df,
  have imz' : z'.val.im = ((g : SL(2,ℤ)) • z).val.im,
  { rw [z'df, ← smul_smul, im_Tn_z] },
  rw smul_smul at hn,
  change |z'.val.re| ≤ 1 / 2 at hn,
  suffices : 1 ≤ z'.1.norm_sq,
  -- by exact ⟨hTn,⟨this, hn⟩⟩,
  {
    exact ⟨this, hn⟩,
  },

  set w := (S * T^n * g) • z with hw,
  apply norm_sq_ge_one_of_act_S,
  replace hw : w = S•z',
  {rw [hw, z'df, smul_smul, mul_assoc]},
  rw [imz', ← hw],
  exact hg2,
end

@[simp]
lemma fundom_aux_1 {z : ℍ} (hz : z ∈ 𝒟) (h' : T • z ∈ 𝒟) : z.val.re = -1/2 := sorry

@[simp]
lemma fundom_aux_2 {z : ℍ} (hz : z ∈ 𝒟) (h' : T⁻¹ • z ∈ 𝒟) : z.val.re = 1/2 := sorry

@[simp]
lemma fundom_aux_3 {z : ℍ} (hz : z ∈ 𝒟) (h' : S • z ∈ 𝒟) : z.val.abs = 1 := sorry

- Why is this not doable by linarith directly? -
example {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : a ≤ a / b) : b ≤ 1 :=
begin
  suffices: a * b ≤ a, nlinarith,
  rw le_div_iff hb at h,
  exact h,
end

lemma namedIs (c :ℕ ) (h: c≤ 1) :  c=0 ∨ c=1 :=
begin
  cases nat.of_le_succ h,
  {
    left,
    exact le_zero_iff.mp h_1,
  },
  right,
  exact h_1,
end

-
lemma namedIsZ (c :ℤ  ) (h: c≤ 1) (h2: 0≤ c) :  c=0 ∨ c=1 :=
begin
  --lift n to ℕ using hn
  lift c to ℕ using h2,
  norm_cast,
  refine namedIs _ _ ,
  exact_mod_cast h,
end

-- Describe closure of D as union of boundary segments and interior.
-- Then the lemma goes by cases on where z and z'

lemma fundom_no_repeats' (z z' : H) (h : ∃ g : SL(2,ℤ), z' = g • z) (hz : z ∈ 𝒟') (hz' : z' ∈ 𝒟') :
  (z = z') :=
begin
  sorry,
end

lemma is_fundom'' {z : H} : ∃ g : SL(2,ℤ), g • z ∈ closure fundamental_domain' :=
begin
  sorry,
end


lemma fundom_no_repeats (z z' : H) (h : ∃ g : SL(2,ℤ), z' = g • z) (hz : z ∈ 𝒟) (hz' : z' ∈ 𝒟) :
  (z = z') ∨
  (z.val.re = -1/2 ∧ z' = T • z) ∨
  (z'.val.re = -1/2 ∧ z = T • z') ∨
  (z.val.abs = 1 ∧ z'.val.abs = 1 ∧ z' = S • z ∧ z = S • z') :=
begin
  wlog hwlog : z.val.im ≤ z'.val.im,
  {
    by_cases hne : z = z', tauto,
    right,
    replace h := sign_coef h,
    obtain ⟨g, hcpos, hac, hg⟩ := h,
    set a := g.1 0 0,
    set b := g.1 0 1,
    set c := g.1 1 0 with ←cdf,
    set d := g.1 1 1 with ←ddf,
    have hcd : complex.norm_sq (c * z + d) ≤ 1,
    {
      have himzpos : 0 < z.val.im := im_pos_of_in_H',
      have hnz : 0 < complex.norm_sq (c * z + d),
      {
        rw norm_sq_pos,
        intro hcontra,
        rw [← cdf, ← ddf, ← bottom_def] at hcontra,
        exact czPd_nonZ_CP (ne.symm (ne_of_lt himzpos)) hcontra,
      },
      suffices: z.val.im * complex.norm_sq (c * z + d) ≤ z.val.im, nlinarith,
      rw [hg, im_smul_SL',cdf,ddf, le_div_iff hnz] at hwlog,
      exact hwlog,
    },
    have hc : _root_.abs c ≤ 1,
    {
      sorry
    },
    replace hc : c = 0 ∨ c = 1,
    {

      rw abs_le at hc,
      exact namedIsZ c hc.2 hcpos,
    },
    rcases hc with  hc | hc ,
    { -- case c = 0
      have ha : a = 1 := (hac hc).2,
      have hd : d = 1 := (hac hc).1,
      have hgT : g = T^b,
      {
        rw T_pow,
        apply subtype.eq,
        simp,
        tauto,
      },
      have hb : _root_.abs c ≤ 1,
      {
        sorry
      },
      replace hb : b = -1 ∨ b = 0 ∨ b = 1,
      {
        sorry
      },
      rcases hb with hb | hb | hb,
      all_goals {rw hb at hgT, rw hgT at hg, clear hb, clear hgT, simp at hg},
      {
        right, left,
        rw ←inv_smul_eq_iff at hg,
        rw ←hg at hz,
        rw fundom_aux_1 hz' hz,
        tauto,
      },
      { tauto },
      {
        left,
        rw hg at hz',
        rw fundom_aux_1 hz hz',
        tauto,
      }
    },
    { -- case c = 1
      sorry
    }
  },
  obtain ⟨g, hg⟩ := h,
  have hh : ∃ g : SL(2,ℤ), z = g • z' := ⟨g⁻¹, by {simp [eq_inv_smul_iff, hg]}⟩,
  specialize this hh hz' hz,
  tauto,
end


-- define fundamental domain
-- open region, g.z=w -> g=1
-- all z in H, exists g in G such that g.z in closure F

-- define std domain {|z|>1, |z.re| <1/2}

-- proof std domain is a fund dom for G

-- define modular form1

-- define Eisenstein series

-- prove E-sereis are modular

-- E(z,k):= sum _{(c,d)∈ Z^2\ {0,0}} 1/(cz+d)^k

-
  human:
  d/ dz E(z,k):= sum _{(c,d)∈ Z^2\ {0,0}}  d/ dz 1/(cz+d)^k

  OR

  E(z,k) - E(w,k)
  =
  sum _{(c,d)∈ Z^2\ {0,0}}  ( 1/(cz+d)^k -  1/(cw+d)^k)
=
(z-w)   *
  sum _{(c,d)∈ Z^2\ {0,0}}  ( 1/(cz+d)^k -  1/(cw+d)^k)

-

- define Ramanujan delta

-


-- @[simp]
-- lemma coeff_coe {g : SL(2,ℤ)} {i j : fin 2} : (g : SL(2,ℝ)).val i j = ((g.val i j) : ℝ) := by refl

-- @[simp]
-- lemma coeff_coe' {g : SL(2,ℤ)} {i j : fin 2} : (g : SL(2,ℝ)) i j = ((g i j) : ℝ) := by refl

-- lemma div_eq_mul_conj_div_norm_sq {z w : ℂ} : z / w = (z * (w.conj)) / complex.norm_sq w :=
-- begin
--   rw [div_eq_mul_inv, inv_def, div_eq_mul_inv, mul_assoc],
--   norm_num,
-- end


-- @[simp]
-- lemma mul_congr { x y : SL(2,ℤ)} : x * y = 1 ↔ x.1 * y.1 = 1 := by simp




-- lemma e14 : at_top ≤ cocompact ℝ :=
-- begin
--   intros s hs,
--   simp only [mem_at_top_sets],
--   simp only [mem_cocompact] at hs,
--   obtain ⟨t, ht, hts⟩ := hs,
--   obtain ⟨r, hr⟩ := e7 ht.bounded,
--   use r + 1,
--   intros b hb,
--   apply hts,
--   intros hb',
--   have := hr _ hb',
--   simp only [real.norm_eq_abs, abs_le] at this,
--   linarith
-- end

-- lemma e16 {E : Type*} [normed_group E] [normed_space ℝ E] [proper_space E] [nontrivial E] (s : set ℝ) :
--   norm ⁻¹' s ∈ cocompact E ↔ s ∈ (at_top : filter ℝ) :=
-- begin
--   rw [mem_at_top_sets, mem_cocompact],
--   split,
--   { rintros ⟨t, ht, hts⟩,
--     obtain ⟨r, hr⟩ := e7 ht.bounded,
--     use r + 1,
--     intros b hb,
--     obtain ⟨x, hx⟩ : ∃ x : E, x ≠ 0 := exists_ne 0,
--     have h_norm : ∥b • (∥x∥)⁻¹ • x∥ = b := sorry,
--     have : b • (∥x∥)⁻¹ • x ∈ tᶜ,
--     { have := mt (hr (b • (∥x∥)⁻¹ • x)),
--       apply this,
--       linarith },
--     simpa [h_norm] using hts this },
--   { rintros ⟨r, hr⟩,
--     refine ⟨metric.closed_ball 0 r, proper_space.compact_ball 0 r, _⟩,
--     intros x hx,
--     simp at hx,
--     exact hr (∥x∥) hx.le },
-- end

-- lemma e17 {E : Type*} [normed_group E] [normed_space ℝ E] [proper_space E] [nontrivial E] :
--   map norm (cocompact E) = (at_top : filter ℝ) :=
-- begin
--   ext s,
--   exact e16 s
-- end

-- lemma e15 {α : Type*} {E : Type*} [normed_group E] [normed_space ℝ E] [proper_space E] [nontrivial E] (l : filter α) {f : α → E} :
--   tendsto f l (cocompact E) ↔ tendsto (norm ∘ f) l at_top :=
-- begin
--   split,
--   { exact tendsto_norm_cocompact_at_top.comp },
--   sorry
-- end


-- lemma finite_integers {M : ℝ} :
--   set.finite {c : ℤ | |(c : ℝ)| ≤ M } :=
-- begin
--     let s:= finset.Ico_ℤ (⌊-M⌋) (⌊M⌋+1),
--     suffices : {c : ℤ | |↑c| ≤ M} ⊆  s,
--     {
--       refine set.finite.subset s.finite_to_set this,
--     },
--     intros c,
--     simp [s],
--     intros h,
--     rw abs_le at h,
--     have h1 := h.1,
--     have h2 := h.2,
--     split,
--     {
--       have : (⌊-M⌋ :ℝ ) ≤ -M :=  floor_le (-M),
--       have := le_trans this h1,
--       exact_mod_cast this,
--     },
--     {
--       have : (c:ℝ ) < (⌊M⌋:ℝ) + 1,
--       {
--         calc
--         (c:ℝ) ≤ M           : h2
--         ...   < (⌊M⌋:ℝ) + 1 : M_lt_Mp1 M,
--       },

--       norm_cast at this,
--       exact this,
--     },
-- end

-- -- for `normed_space.basic`
-- lemma metric.bounded.exists_norm_le {α : Type*} [normed_group α] {s : set α} (hs : metric.bounded s) :
--   ∃ R, ∀ x ∈ s, ∥x∥ ≤ R :=
-- begin
--   rcases s.eq_empty_or_nonempty with (rfl | hs'),
--   { simp },
--   obtain ⟨R₁, hR₁⟩ := hs,
--   obtain ⟨x, hx⟩ := hs',
--   use ∥x∥ + R₁,
--   intros y hy,
--   have : ∥x - y∥ ≤ R₁ := by simpa [dist_eq_norm] using hR₁ x y hx hy,
--   have := norm_le_insert x y,
--   linarith
-- end

-- -- for `order.filter.basic`
-- lemma e9 {α : Type*} (l : filter α) {s t : set α} (hst : s ∪ tᶜ ∈ l) (ht : t ∈ l) : s ∈ l :=
-- begin
--   refine mem_sets_of_superset _ (s.inter_subset_left t),
--   convert inter_mem_sets hst ht using 1,
--   ext,
--   simp only [set.mem_inter_eq, set.mem_union_eq, set.mem_compl_eq],
--   finish
-- end


-- lemma e10 {α : Type*} {l : filter α} {E F : Type*} [normed_group E] [normed_group F] [proper_space E]
--   {f : α → E} {g : α → F} (h : asymptotics.is_O f g l) (hf : tendsto f l (cocompact E)) :
--   tendsto g l (cocompact F) :=
-- begin
--   rw tendsto_def at ⊢ hf,
--   intros s hs,
--   simp [filter.mem_cocompact'] at hs,
--   obtain ⟨t, ht, hts⟩ := hs,
--   obtain ⟨r, hr⟩ : ∃ r, ∀ p ∈ sᶜ, ∥p∥ ≤ r := (ht.bounded.subset hts).exists_norm_le,
--   rw asymptotics.is_O_iff at h,
--   obtain ⟨c, hc⟩ := h,
--   rw eventually_iff_exists_mem at hc,
--   obtain ⟨v, hv, hvfg⟩ := hc,
--   have : ∀ x ∈ v ∩ g ⁻¹' sᶜ, x ∈ f ⁻¹' metric.closed_ball (0:E) (c * r),
--   { rintros x ⟨hxv, hxgs⟩,
--     have := hr (g x) hxgs,
--     have := hvfg x hxv,
--     simp,
--     sorry },
--   have h₂ : f ⁻¹' (metric.closed_ball (0:E) (c * r))ᶜ ⊆ g ⁻¹' s ∪ vᶜ,
--   { intros x,
--     have := this x,
--     simp only [set.mem_preimage, set.mem_inter_eq, set.mem_compl_eq] at this,
--     simp only [set.mem_preimage, set.mem_union_eq, set.mem_compl_eq],
--     contrapose!,
--     finish },
--   have h₃ : f ⁻¹' (metric.closed_ball 0 (c * r))ᶜ ∈ l,
--   { apply hf (metric.closed_ball (0:E) (c * r))ᶜ,
--     simp only [mem_cocompact'],
--     refine ⟨metric.closed_ball (0:E) (c * r), proper_space.compact_ball 0 (c * r), _⟩,
--     simp },
--   have : g ⁻¹' s ∪ vᶜ ∈ l := mem_sets_of_superset h₃ h₂,
--   refine e9 l this hv
-- end


-- lemma tendsto_cocompact_of_antilipschitz {α β : Type*} [metric_space α] [proper_space α]
--   [metric_space β] {c : nnreal} {f : α → β} (hf : antilipschitz_with c f) :
--   tendsto f (cocompact α) (cocompact β) :=
-- begin
--   rw tendsto_iff_eventually,
--   simp only [mem_cocompact, eventually_iff_exists_mem],
--   rintros p ⟨v, hv, hvp⟩,
--   rw mem_cocompact' at hv,
--   obtain ⟨t, ht, htv⟩ := hv,
--   obtain ⟨r, hr⟩ := ht.bounded,
--   -- have := hf.bounded_preimage ht.bounded,
--   by_cases h : ∃ x, ¬ p (f x),
--   { obtain ⟨x, hx⟩ := h,
--     have hxt : f x ∈ t := htv (mt (hvp (f x)) hx),
--     refine ⟨(metric.closed_ball x (c * r))ᶜ, _, _⟩,
--     { rw mem_cocompact,
--       refine ⟨metric.closed_ball x (c * r), proper_space.compact_ball x (↑c * r), rfl.subset⟩ },
--     intros x' hx',
--     have hxx'r : r < dist (f x) (f x'),
--     { simp at hx',
--       rw dist_comm at hx',
--       rw antilipschitz_with_iff_le_mul_dist at hf,
--       have : dist x x' ≤ c * dist (f x) (f x') := hf x x',
--       have := lt_of_lt_of_le hx' this,
--       sorry }, -- this follows from the previous line except with a special case for `c = 0`
--     have := mt (hr (f x) (f x') hxt),
--     push_neg at this,
--     have := (mt (@htv (f x'))) (this hxx'r),
--     apply hvp,
--     simpa using this },
--   { push_neg at h,
--     refine ⟨set.univ, univ_mem_sets, _⟩,
--     intros x hx,
--     exact h x },
-- end

-- lemma tendsto_at_top_sum_sq :
--   tendsto (λ x : ℝ × ℝ, x.1 ^ 2 + x.2 ^ 2) (cocompact (ℝ × ℝ)) at_top :=
-- begin
--   refine tendsto_at_top_mono _
--     (tendsto_norm_cocompact_at_top.at_top_mul_at_top tendsto_norm_cocompact_at_top),
--   rintros ⟨x₁, x₂⟩,
--   simp only [prod.norm_def, real.norm_eq_abs],
--   cases max_choice (|x₁|) (|x₂|) with h h;
--   { rw [h, abs_mul_abs_self],
--     nlinarith },
-- end

-- @[simp] lemma expand_sum_01 {R : Type*} [ring R] (f : fin 2 → R ) :
-- (∑ (x : fin 2), f x) = f 0 + f 1 :=
-- by simp [fin.sum_univ_succ]


-- -- method 1 -
-- def line (cd : coprime_ints) : set (matrix (fin 2) (fin 2) ℝ) :=
--   {g | g 1 0 = (cd : ℤ × ℤ).1 ∧ g 1 1 = (cd : ℤ × ℤ).2 ∧ det g = 1}

- Do we need this? Maybe delete
lemma line_proper (cd : coprime_ints) :
  map coe (cocompact (line cd)) = cocompact (matrix (fin 2) (fin 2) ℝ) :=
begin

  sorry
end
-


-- -- make `line` an affine subspace of 2x2 matrices, using the following lemma
-- lemma line_det (cd : coprime_ints) {g : matrix _ _ ℝ} (hg : g ∈ line cd) :
--   g 0 0 * cd.d - g 0 1 * cd.c = 1 :=
-- begin
--   convert hg.2.2,
--   rw [det2, hg.1, hg.2.1],
--   ring,
-- end

-- lemma in_line (cd : coprime_ints) {g : SL(2, ℤ)} (hg : bottom_row g = cd) :
--   ↑(g : SL(2, ℝ)) ∈ line cd :=
-- begin
--   rw line,
--   rw set.mem_set_of_eq,
--   rw bottom_row at hg,
--   simp only [subtype.val_eq_coe] at hg,
--   split,
--   simp [hg],
--   sorry,
--   split,
--   simp [hg],
--   sorry,
--   exact (g: SL(2,ℝ)).2,
-- end

-- def to_line (cd : coprime_ints) (g : bottom_row ⁻¹' {cd}) : line cd :=
-- ⟨↑(g : SL(2, ℝ)), in_line cd g.2⟩




-- lemma sddsf (cd : coprime_ints) (z : ℂ) :
--   tendsto (λ g : lattice_intersect (line cd), _root_.abs (smul_aux' ↑(lattice_intersect_fun _ g) z).re)
--     cofinite at_top :=
-- (tendsto_at_top_abs.comp (tendsto_action cd z)).comp (tendsto_lattice_intersect_fun (line cd))

-- -- method 2 -
-- def line' (cd : coprime_ints) : set (ℝ × ℝ) :=
--   {ab | ab.1 * (cd : ℤ × ℤ).2 - ab.2 * (cd : ℤ × ℤ).1 = 1}

-- def in_line' (cd : coprime_ints) {g : SL(2, ℤ)} (hg : bottom_row g = cd) :
--   (↑(g 0 0), ↑(g 0 1)) ∈ line' cd :=
-- sorry

-- def to_line' (cd : coprime_ints) (g : bottom_row ⁻¹' {cd}) : line' cd :=
-- ⟨(g 0 0, g 0 1), in_line' cd g.2⟩

-- lemma tendsto_line' (cd : coprime_ints) : tendsto (to_line' cd) cofinite (cocompact _) := sorry

-- lemma inv_image_eq_line (cd : coprime_ints) :
--   bottom_row ⁻¹' {cd} = (prod.map coe coe : ℤ × ℤ → ℝ × ℝ) ⁻¹' line cd :=
-- sorry

-- end




-- lemma tendsto_acbd (cd : coprime_ints):
--   tendsto (λ g, acbd (↑g)) (cocompact (line cd)) (cocompact ℝ) :=
-- begin
--   let cabs := _root_.abs cd.c,
--   let dabs := _root_.abs cd.d,
--   let maxCD := max cabs dabs,
--   intros K hK ,
--   rw mem_cocompact at hK,

--   obtain ⟨ K1, hK1, hK2⟩  := hK,

--   obtain ⟨ t, ht⟩  := (metric.bounded_iff_subset_ball 0).mp (is_compact.bounded hK1),
--   rw mem_map,
--   rw mem_cocompact,
--   refine ⟨
--   ((coe : line cd → (matrix (fin 2) (fin 2) ℝ)) ⁻¹'
--    (metric.closed_ball (0: matrix (fin 2) (fin 2) ℝ) (max (2*(_root_.abs t)+1) maxCD) )),
--    sorry, _⟩ ,
--    --simp,
--   rw set.compl_subset_comm,
--   rw set.compl_subset_comm at hK2,
--   intros g hg,
--   simp [dist_eq_norm] at hg,
--   simp only [set.mem_preimage, metric.mem_closed_ball,  int_cast_abs, subtype.val_eq_coe],
--   have : acbd ↑g ∈ metric.closed_ball (0:ℝ) t,
--   {
--     apply ht,
--     apply hK2,
--     exact hg,
--   },
--   rw dist_pi_def,
--   let a : nnreal := nnreal.of_real (max (2 * |t| + 1) ↑maxCD),
--   rw ← nnreal.coe_of_real (max (2 * |t| + 1) ↑maxCD),
--   norm_cast,
--   have : (∀ (b : fin 2), b ∈ finset.univ → (λ (b : fin 2), nndist ((↑g: matrix _ _ ℝ) b) 0) b ≤ a) := sorry,
--   refine @finset.sup_le nnreal (fin 2) _ (finset.univ) ((λ (b : fin 2), nndist ((↑g: matrix _ _ ℝ) b) (0))) a _,

--   sorry
-- end

-- - Is this non-crap? (More elegant phrasing?...) We know that $ℤ$ matrices are discrete in $ℝ$; so intersection of $Z$ matrices is discrete in line -
-- lemma tendsto_inverse_image_fun' {α β : Type*} [topological_space β] (A : set α) (B : set β)
--   {f : α → β} (hf₁ : ∀ x ∈ A, f x ∈ B ) (hf₂ : tendsto f cofinite (cocompact _)) :
--   tendsto (subtype.map f (λ x h, set.mem_def.mp (hf₁ x h))) cofinite (cocompact _) :=
-- begin
-- --  refine tendsto_inverse_image_fun subtype.coe_injective continuous_subtype_coe _ hf₂,
--   refine filter.tendsto.of_tendsto_comp _ (comap_cocompact continuous_subtype_coe),
--   simpa [hf₁] using hf₂.comp subtype.coe_injective.tendsto_cofinite,
-- end


-- -- Big filter theorem -
-- theorem big_thm' (cd : coprime_ints) (w : ℝ) :
--   tendsto (λ A : bottom_row ⁻¹' {cd}, acbd cd ↑A + w) cofinite (cocompact ℝ) :=
-- begin
--   let cd' : fin 2 → ℤ :=  λ i, if i = 0 then cd.c else cd.d,
--   let l := bottom_row ⁻¹' {cd},
--   let f : SL(2, ℤ) → matrix (fin 2) (fin 2) ℝ := λ g, matrix.map (↑g : matrix _ _ ℤ) (coe : ℤ → ℝ),
--   have hf : tendsto f cofinite (cocompact _) :=
--     cocompact_ℝ_to_cofinite_ℤ_matrix.comp subtype.coe_injective.tendsto_cofinite,
--   have hl : ∀ g ∈ l, f g ∈ new_line_def cd,
--   { intros g hg,
--     simp [new_line_def, line_map, matrix.coord, f],
--     split,
--     { norm_cast,
--       convert g.det_coe_matrix using 1,
--       sorry },
--     { sorry } },
--   let f' : l → new_line_def cd := subtype.map f hl,
--   have h₁ : tendsto f' cofinite (cocompact _),
--   { refine filter.tendsto.of_tendsto_comp _ (comap_cocompact continuous_subtype_coe),
--     simpa [hl] using hf.comp subtype.coe_injective.tendsto_cofinite },
--   have h₂ : tendsto (λ A, acbd cd ↑A + w) (cocompact (new_line_def cd)) (cocompact ℝ),
--   { let hf := linear_equiv.closed_embedding_of_injective (lin_indep_acbd cd),
--     let p : ℝ × (fin 2 → ℝ) := (1, λ i, if i = 0 then cd.c else cd.d),
--     let hs : is_closed (prod.snd ⁻¹' {p} : set (ℝ × (ℝ × (fin 2 → ℝ)))) :=
--       is_closed_singleton.preimage continuous_snd,
--     have := (hf.comp (closed_embedding_subtype_coe (hs.preimage hf.continuous))).cod_restrict hs (by simp),
--     have := ((fibre_embed_homeomorph p).trans (homeomorph.add_right w)).closed_embedding.comp this,
--     exact this.tendsto_cocompact },
--   have := h₂.comp h₁,
--   convert this,
-- end




-- example : T⁻¹ * T = 1 := inv_mul_self T

-- example { R : SL(2,ℤ) } : R * T = 1 → R = T⁻¹ := eq_inv_of_mul_eq_one

-- example { R : SL(2,ℤ) } : T * R = 1 → T⁻¹ = R := inv_eq_of_mul_eq_one

-- example { x y : SL(2,ℤ)} (ℍ : x.1 = y.1) : x = y := subtype.eq h

-- @[simp]
-- lemma mat_congr_SL { x y : SL(2,ℤ) } : x = y ↔ x.val = y.val := subtype.ext_iff_val

-- @[simp]
-- lemma mat_ext_iff  {F : Type*} [comm_ring F] (x y : matrix (fin 2) (fin 2) F) :
--   x = y ↔ x 0 0 = y 0 0 ∧ x 0 1 = y 0 1 ∧ x 1 0 = y 1 0 ∧ x 1 1 = y 1 1 :=
-- begin
--   rw ←matrix.ext_iff,
--   split,
--   {
--     intro h,
--     rw h,
--     tauto },
--   {
--     rintros ⟨h1, h2, h3, h4⟩ i j,
--     fin_cases i; fin_cases j; assumption,
--   }
-- end

-- @[simp]
-- lemma mat_one {F : Type*} [comm_ring F] : (![![1,0], ![0,1]] : matrix (fin 2) (fin 2) F)
--   = (1 : matrix (fin 2) (fin 2) F) := by {simp}


-- lemma T_inv : T⁻¹ = { val := ![![1, -1], ![0, 1]], property := by simp [det2] } :=
-- begin
--   suffices : T * { val := ![![1, -1], ![0, 1]], property := by simp [det2] } = 1,
--   { exact inv_eq_of_mul_eq_one this},
--   simp [T],
-- end

-- lemma T_n_def {n : ℤ} :  T^(-n) = (T⁻¹)^n := by {simp [inv_gpow, gpow_neg]}

-- lemma T_pow_ℕ {n : ℕ} : T ^ n = { val := ![![1, n], ![0, 1]], property := by simp [det2] } :=
-- begin
--   induction n with n hn,
--   { simp },
--   { rw [pow_succ', hn, T],
--     simp [add_comm] }
-- end

-- lemma T_inv_pow_ℕ {n : ℕ} : (T⁻¹)^n = { val := ![![1, -n], ![0, 1]], property := by simp [det2] } :=
-- begin
--   induction n with n hn,
--   simp,
--   have : (T⁻¹) ^ n.succ = ((T⁻¹)^n)* (T⁻¹),
--   {
--     exact pow_succ' (T⁻¹) n,
--   },
--   rw this,
--   rw hn,
--   rw T_inv,
--   simp,
-- end


-- lemma T_pow {n : ℤ} : T^n = { val := ![![1, n], ![0, 1]], property := by simp [det2] } :=
-- begin
--   by_cases n_ge_0 : 0 ≤ n,
--   lift n to ℕ with n_ge_0,
--   refine T_pow_ℕ,
--   exact n_ge_0,
--   have : T ^ n = T ^ (- (-n)) := by simp,
--   rw this,
--   rw T_n_def,
--   generalize' hk : -n=k,
--   have k_ge_0 : 0 ≤ k,
--   {
--     rw ← hk,
--     linarith,
--   },
--   have : n = -k,
--   {
--     rw ← hk,
--     ring,
--   },
--   rw this,
--   lift k to ℕ using k_ge_0,
--   rw gpow_coe_nat,
--   norm_cast,
--   rw T_inv_pow_ℕ,
-- end

-- lemma T_action {z : ℍ} : (T • z).1 = z + 1 :=
-- begin
--   convert @smul_sound T z,
--   simp only [smul_aux_def, top, bottom, T, has_coe_SL_apply, subtype.coe_mk, map_cons],
--   simp [special_linear_group.cons_apply_zero, special_linear_group.cons_apply_one],
-- end


-- lemma Tn_action {z : ℍ} {n : ℤ} : (T^n • z).1 = z + n :=
-- begin
--   have := @smul_sound (T^n) z,
--   convert this,
--   rw smul_aux,
--   rw T_pow,
--   rw top,
--   rw bottom,
--   simp,
-- end

-- lemma S_action (z : ℍ) : (S • z).1 = -z⁻¹ :=
-- begin
--   convert @smul_sound S z,
--   simp only [smul_aux_def, top, bottom, S, has_coe_SL_apply, subtype.coe_mk, map_cons],
--   simp [special_linear_group.cons_apply_zero, special_linear_group.cons_apply_one],
--   ring,
-- end

lemma norm_sq_ge_one_of_act_S {z : ℍ} (h : (S • z).im ≤ z.im) : 1 ≤ norm_sq z :=
begin
  by_contradiction hcontra,
  push_neg at hcontra,
  have := im_lt_im_S hcontra,
  linarith,
end



lemma T_inv_action {z : ℍ} : (T⁻¹ • z).1 = z - 1 :=
begin
  convert @smul_sound (T⁻¹) z,
  rw smul_aux,
  rw T_inv,
  simp,
  ring,
end


lemma bot_row_eq_diff_by_unipotent (g g' : SL(2,ℝ)) (h : bottom_row g = bottom_row g') :
∃ (x:ℝ), g = (![![1,x],![0,1]],_) * g' :=
begin
  -- human proof: g= a,b,c,d, g' = a' b' c d (same c d!)
  -- then g*g⁻¹ = (a b c d)(d -b' -c a') = (1 * 0 1)

--  let ![![a,b],![c,d]] := g.1,
  let Tn := g * g'⁻¹,
  sorry,

end
-/
