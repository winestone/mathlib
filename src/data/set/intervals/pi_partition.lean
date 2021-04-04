import analysis.normed_space.basic
import algebra.big_operators.finprod

open_locale classical filter topological_space
open filter
noncomputable theory

variables {ι : Type*}

open set function

structure partition_box (ι : Type*) :=
(lower upper : ι → ℝ)
(lower_lt_upper : ∀ i, lower i < upper i)

namespace partition_box

variables (I J : partition_box ι) {x y : ι → ℝ}

protected def Icc : set (ι → ℝ) := Icc I.lower I.upper
protected def Ioc : set (ι → ℝ) := {x | ∀ i, x i ∈ Ioc (I.lower i) (I.upper i)}

lemma Icc_def : I.Icc = Icc I.lower I.upper := rfl

lemma Ioc_def : I.Ioc = {x | ∀ i, x i ∈ Ioc (I.lower i) (I.upper i)} := rfl

lemma Icc_eq_pi : I.Icc = pi univ (λ i, Icc (I.lower i) (I.upper i)) := (pi_univ_Icc _ _).symm
lemma Ioc_eq_pi : I.Ioc = pi univ (λ i, Ioc (I.lower i) (I.upper i)) :=
by simp only [Ioc_def, pi, mem_univ, forall_true_left]

lemma lower_le_upper : I.lower ≤ I.upper := λ i, (I.lower_lt_upper i).le

@[simp] lemma upper_mem_Icc : I.upper ∈ I.Icc := right_mem_Icc.2 I.lower_le_upper
@[simp] lemma lower_mem_Icc : I.lower ∈ I.Icc := left_mem_Icc.2 I.lower_le_upper
@[simp] lemma upper_mem_Ioc : I.upper ∈ I.Ioc := λ i, right_mem_Ioc.2 $ I.lower_lt_upper i

protected lemma closure_Ioc : closure I.Ioc = I.Icc :=


instance : has_le (partition_box ι) := ⟨λ I J, I.Ioc ⊆ J.Ioc⟩

@[simp] lemma Ioc_subset : I.Ioc ⊆ J.Ioc ↔ I ≤ J := iff.rfl

lemma le_iff : I ≤ J ↔ J.lower ≤ I.lower ∧ I.upper ≤ J.upper :=
begin
  refine ⟨λ h, ⟨λ i, _, λ i, _⟩, λ h x hx i, Ioc_subset_Ioc (h.1 i) (h.2 i) (hx i)⟩;
    by_contra hi; rw not_le at hi,
  { set p := update I.upper i (min (I.upper i) (J.lower i)),
    have : p ∈ I.Ioc,
    { intros j, rcases em (j = i) with rfl | hj; simp [*, I.lower_lt_upper, le_refl] },
    simpa [p, lt_irrefl] using (h this i).1, },
  { exact (h I.upper_mem_Ioc i).2.not_lt hi }
end

lemma ext' (hl : I.lower = J.lower) (hr : I.upper = J.upper) : I = J :=
by { cases I, cases J, congr; assumption }

lemma ext'_iff : I = J ↔ I.lower = J.lower ∧ I.upper = J.upper :=
⟨λ h, h ▸ ⟨rfl, rfl⟩, λ h, ext' h.1 h.2⟩

instance : partial_order (partition_box ι) :=
{ le := (≤),
  le_antisymm := λ I J hIJ hJI, ext' (le_antisymm (le_iff.1 hJI).1 (le_iff.1 hIJ).1)
    (le_antisymm (le_iff.1 hIJ).2 (le_iff.1 hJI).2),
  .. preorder.lift (coe : partition_box ι → set (ι → ℝ)) }

end partition_box

open finset

@[protect_proj]
structure pi_partition (I : partition_box ι) :=
(boxes : finset (partition_box ι))
(le_total' : ∀ J ∈ boxes, J ≤ I)
(exists_unique' : ∀ x ∈ I, ∃! J ∈ boxes, x ∈ J)

namespace pi_partition

variables {I J J' : partition_box ι} (π : pi_partition I) {x : ι → ℝ}

instance : has_mem (partition_box ι) (pi_partition I) := ⟨λ J π, J ∈ π.boxes⟩

@[simp] lemma mem_boxes_eq_mem : (J ∈ π.boxes) = (J ∈ π) := rfl

@[simp] lemma mem_mk {b : finset (partition_box ι)} {h h'} :
  J ∈ (mk b h h' : pi_partition I) ↔ J ∈ b := iff.rfl

lemma le_total (hJ : J ∈ π) : J ≤ I := π.le_total' J hJ

lemma lower_le_lower (hJ : J ∈ π) : I.lower ≤ J.lower :=
(partition_box.le_iff.1 (π.le_total hJ)).1

lemma upper_le_upper (hJ : J ∈ π) : J.upper ≤ I.upper :=
(partition_box.le_iff.1 (π.le_total hJ)).2

@[ext] lemma ext {π π' : pi_partition I} (h : ∀ J, J ∈ π ↔ J ∈ π') : π = π' :=
by { cases π, cases π', simp only at *, exact finset.ext h }

protected lemma exists_unique (hx : x ∈ I) : ∃! J ∈ π, x ∈ J := π.exists_unique' x hx

lemma exists_mem (hx : x ∈ I) : ∃ J ∈ π, x ∈ J := (π.exists_unique hx).exists2

lemma eq_of_mem_of_mem (h : J ∈ π) (h' : J' ∈ π) (hx : x ∈ J) (hx' : x ∈ J') :
  J = J' :=
(π.exists_unique (π.le_total h hx)).unique2 h hx h' hx'

lemma eq_of_le (h : J ∈ π) (h' : J' ∈ π) (hle : J ≤ J') : J = J' :=
π.eq_of_mem_of_mem h h' J.upper_mem (hle J.upper_mem)

instance : has_le (pi_partition I) := ⟨λ π π', ∀ ⦃I⦄, I ∈ π → ∃ I' ∈ π', I ≤ I'⟩

instance : partial_order (pi_partition I) :=
{ le := (≤),
  le_refl := λ π I hI, ⟨I, hI, le_rfl⟩,
  le_trans := λ π₁ π₂ π₃ h₁₂ h₂₃ I₁ hI₁,
    let ⟨I₂, hI₂, hI₁₂⟩ := h₁₂ hI₁, ⟨I₃, hI₃, hI₂₃⟩ := h₂₃ hI₂ in ⟨I₃, hI₃, hI₁₂.trans hI₂₃⟩,
  le_antisymm :=
    begin
      suffices : ∀ ⦃π₁ π₂ : pi_partition I⦄, π₁ ≤ π₂ → π₂ ≤ π₁ → ∀ ⦃J⦄, J ∈ π₁ → J ∈ π₂,
        from λ π₁ π₂ h₁₂ h₂₁, ext (λ x, ⟨λ hx, this h₁₂ h₂₁ hx, λ hx, this h₂₁ h₁₂ hx⟩),
      intros π₁ π₂ h₁₂ h₂₁ J hJ,
      rcases h₁₂ hJ with ⟨J', hJ', hle⟩, rcases h₂₁ hJ' with ⟨J'', hJ'', hle'⟩,
      obtain rfl : J = J'', from π₁.eq_of_le hJ hJ'' (hle.trans hle'),
      obtain rfl : J' = J, from le_antisymm ‹_› ‹_›,
      assumption
    end}

instance : has_top (pi_partition I) :=
⟨⟨{I}, λ J hJ, finset.mem_singleton.1 hJ ▸ le_rfl,
  λ x hx, exists_unique.intro2 I (finset.mem_singleton_self _) hx $
    λ y hy _, finset.mem_singleton.1 hy⟩⟩

@[simp] lemma mem_top_boxes : J ∈ (⊤ : pi_partition I) ↔ J = I := finset.mem_singleton

private def inf_boxes (π π' : pi_partition I) : finset (partition_box ι) :=
(π.boxes.product π'.boxes).bUnion $ λ J,
  if h : ∀ i, max (J.1.lower i) (J.2.lower i) < min (J.1.upper i) (J.2.upper i)
  then {⟨_, _, h⟩} else ∅

private lemma mem_inf_boxes' {π π' : pi_partition I} {J'' : partition_box ι} :
  J'' ∈ inf_boxes π π' ↔ ∃ (J : partition_box ι) (hJ: J ∈ π) (J' : partition_box ι) (hJ' : J' ∈ π')
    (h : ∀ i, max (J.lower i) (J'.lower i) < min (J.upper i) (J'.upper i)),
    J'' = ⟨_, _, h⟩ :=
begin
  simp only [inf_boxes, exists_prop, finset.mem_bUnion, mem_product, prod.exists, and_assoc,
    exists_and_distrib_left],
  refine exists_congr (λ J, and_congr_right $ λ hJ, exists_congr $
    λ J', and_congr_right $ λ hJ', _),
  split_ifs; simp only [*, exists_prop_of_true, finset.mem_singleton, forall_true_iff,
    finset.not_mem_empty, false_iff, not_exists],
  exact λ H, (h H).elim
end

instance : has_inf (pi_partition I) :=
⟨λ π π',
  { boxes := inf_boxes π π',
    le_total' := λ J'' hJ'',
      begin
        rcases mem_inf_boxes'.1 hJ'' with ⟨J, hJ, J', hJ', h, rfl⟩,
        rw partition_box.le_iff,
        exact ⟨λ i, le_max_iff.2 (or.inl $ π.lower_le_lower hJ i),
          λ i, min_le_iff.2 $ or.inl $ π.upper_le_upper hJ i⟩,
      end,
    exists_unique' := λ x hxI,
      begin
        rcases (π.exists_unique hxI).exists2 with ⟨J, hJ, hx⟩,
        rcases (π'.exists_unique hxI).exists2 with ⟨J', hJ', hx'⟩,
        have A : ∀ i, x i ∈ Ioc (max (J.lower i) (J'.lower i)) (min (J.upper i) (J'.upper i)),
          from λ i, ⟨max_lt (hx i).1 (hx' i).1, le_min (hx i).2 (hx' i).2⟩,
        have B : ∀ i, _ < _ := λ i, (A i).1.trans_le (A i).2,
        set J'' : partition_box ι := ⟨_, _, B⟩,
        refine exists_unique.intro2 J'' _ A _; simp only [mem_inf_boxes'],
        { refine ⟨J, hJ, J', hJ', B, rfl⟩ },
        { rintros J₁'' ⟨J₁, hJ₁, J₁', hJ₁', h, rfl⟩ H,
          simp only [mem_Ioc, partition_box.mem_mk, max_lt_iff, le_min_iff] at H,
          obtain rfl : J = J₁, from π.eq_of_mem_of_mem hJ hJ₁ hx (λ i, ⟨(H i).1.1, (H i).2.1⟩),
          obtain rfl : J' = J₁',
            from π'.eq_of_mem_of_mem hJ' hJ₁' hx' (λ i, ⟨(H i).1.2, (H i).2.2⟩),
          refl }
      end }⟩

lemma mem_inf_boxes {π π' : pi_partition I} {J'' : partition_box ι} :
  J'' ∈ π ⊓ π' ↔ ∃ (J : partition_box ι) (hJ: J ∈ π) (J' : partition_box ι) (hJ' : J' ∈ π')
    (h : ∀ i, max (J.lower i) (J'.lower i) < min (J.upper i) (J'.upper i)),
    J'' = ⟨_, _, h⟩ :=
mem_inf_boxes'

instance : semilattice_inf_top (pi_partition I) :=
{ le := (≤),
  top := ⊤,
  le_top := λ π J hJ, ⟨I, finset.mem_singleton_self _, π.le_total hJ⟩,
  inf := (⊓),
  inf_le_left := λ π π' J'' hJ'',
    begin
      rcases mem_inf_boxes.1 hJ'' with ⟨J, hJ, J', hJ', H, rfl⟩, clear hJ'',
      exact ⟨J, hJ, partition_box.le_iff.2 ⟨λ i, le_max_left _ _, λ i, min_le_left _ _⟩⟩
    end,
  inf_le_right := λ π π' J'' hJ'',
    begin
      rcases mem_inf_boxes.1 hJ'' with ⟨J, hJ, J', hJ', H, rfl⟩, clear hJ'',
      exact ⟨J', hJ', partition_box.le_iff.2 ⟨λ i, le_max_right _ _, λ i, min_le_right _ _⟩⟩
    end,
  le_inf := λ π π₁ π₂ h₁ h₂ J hJ,
    begin
      rcases h₁ hJ with ⟨J₁, mem₁, le₁⟩, rcases h₂ hJ with ⟨J₂, mem₂, le₂⟩,
      simp only [exists_prop, mem_inf_boxes],
      refine ⟨_, ⟨J₁, mem₁, J₂, mem₂, λ i, _, rfl⟩, _⟩;
        simp only [partition_box.le_iff] at *,
      calc max (J₁.lower i) (J₂.lower i) ≤ J.lower i : max_le (le₁.1 i) (le₂.1 i)
      ... < J.upper i : J.lower_lt_upper i
      ... ≤ min (J₁.upper i) (J₂.upper i) : le_min (le₁.2 i) (le₂.2 i),
      exact ⟨λ i, max_le (le₁.1 i) (le₂.1 i), λ i, le_min (le₁.2 i) (le₂.2 i)⟩
    end,
  .. pi_partition.partial_order }

private def split_each_boxes (πi : Π J ∈ π, pi_partition J) : finset (partition_box ι) :=
π.boxes.attach.bUnion (λ J, (πi J J.2).boxes)

private lemma mem_split_each_boxes' {πi : Π J ∈ π, pi_partition J} :
  J ∈ split_each_boxes π πi ↔ ∃ J' ∈ π, J ∈ πi J' ‹_› :=
by { simp [split_each_boxes], refl }

def split_each (πi : Π J ∈ π, pi_partition J) : pi_partition I :=
{ boxes := split_each_boxes π πi,
  le_total' := λ J hJ, let ⟨I, hI, hJI⟩ := (mem_split_each_boxes' π).1 hJ in
    ((πi I hI).le_total hJI).trans (π.le_total hI),
  exists_unique' := λ x hx,
    begin
      rcases π.exists_mem hx with ⟨J, hJ, hxJ⟩,
      rcases (πi J hJ).exists_mem hxJ with ⟨J', hJ', hxJ'⟩,
      refine exists_unique.intro2 J' ((mem_split_each_boxes' π).2 ⟨J, hJ, hJ'⟩) hxJ' _,
      simp only [mem_split_each_boxes'],
      rintro J₁' ⟨J₁, hJ₁, hJ₁'⟩ hxJ₁',
      obtain rfl : J = J₁, from π.eq_of_mem_of_mem hJ hJ₁ hxJ ((πi J₁ hJ₁).le_total hJ₁' hxJ₁'),
      exact (πi J hJ).eq_of_mem_of_mem hJ₁' hJ' hxJ₁' hxJ'
    end }

lemma mem_split_each_boxes {πi : Π J ∈ π, pi_partition J} :
  J ∈ split_each π πi ↔ ∃ J' ∈ π, J ∈ πi J' ‹_› :=
mem_split_each_boxes' π

def is_homothetic (π : pi_partition I) : Prop :=
∀ (J ∈ π), ∃ ε : ℝ, (J : partition_box ι).upper - J.lower = ε • (I.upper - I.lower)

end pi_partition

structure marked_pi_partition (I : partition_box ι) extends pi_partition I :=
(mark : Π (J ∈ boxes) (i : ι), ℝ)
(mark_mem' : ∀ J ∈ boxes, mark J ‹_› ∈ Icc I.lower I.upper)

namespace marked_pi_partition

section

variables {I : partition_box ι} (π : marked_pi_partition I)

instance : has_mem (partition_box ι) (marked_pi_partition I) := ⟨λ J π, J ∈ π.boxes⟩

lemma mark_mem {J : partition_box ι} (hJ : J ∈ π) : π.mark J hJ ∈ Icc I.lower I.upper :=
π.mark_mem' J hJ

def is_Henstock : Prop := ∀ J ∈ π, π.mark J ‹_› ∈ Icc J.lower J.upper

end

variables [fintype ι] {I : partition_box ι} (π : marked_pi_partition I)

def is_subordinate (π : marked_pi_partition I) (r : Π x ∈ I, ennreal) :=
∀ (J ∈ π.boxes) (x ∈ J), edist x (π.mark J ‹_›) ≤ r (π.mark J ‹_›) (π.mark_mem _)

lemma exists_is_subordinate (r : Π x ∈ I, ennreal) (hr : ∀ x hx, 0 < r x hx) :
  ∃ π : marked_pi_partition I, π.is_subordinate r ∧ π.is_homothetic ∧ π.is_Henstock :=
sorry

lemma is_subordinate.mono {π : marked_pi_partition I} {r r' : Π x ∈ I, ennreal}
  (h : ∀ x hx, r x hx ≤ r' x hx) (hr : π.is_subordinate r) :
  π.is_subordinate r' :=
λ J hJ x hx, (hr J hJ x hx).trans (h _ _)

lemma is_subordinate.ediam_le {π : marked_pi_partition I} {r : Π x ∈ I, ennreal}
  (h : π.is_subordinate r) {J : partition_box ι} (hJ : J ∈ π) :
  emetric.diam (J : set (ι → ℝ)) ≤ 2 * r (π.center J hJ ) (π.center_mem _) :=
emetric.diam_le_of_forall_edist_le $ λ x hx y hy,
calc edist x y ≤ edist x (π.center J hJ) + edist y (π.center J hJ) : edist_triangle_right _ _ _
... ≤ r (π.center J hJ ) (π.center_mem _) + r (π.center J hJ ) (π.center_mem _) :
  add_le_add (h _ _ _ hx) (h _ _ _ hy)
... = 2 * r (π.center J hJ ) (π.center_mem _) : (two_mul _).symm

end marked_pi_partition

namespace box_integral

variables {E F : Type*} [normed_group E] [normed_space ℝ E] [normed_group F] [normed_space ℝ F]
  [fintype ι] {I : partition_box ι} {π : marked_pi_partition I}

open marked_pi_partition

def Riemann : filter (marked_pi_partition I) :=
(⨅ (r : ennreal) (hr : 0 < r), 𝓟 {π | ∀ J ∈ π, emetric.diam (↑J : set (ι → ℝ)) ≤ r}) ⊓
  𝓟 {π | is_Henstock π}

def McShane : filter (marked_pi_partition I) :=
⨅ (r : Π x ∈ I, ennreal) (hr : ∀ x hx, 0 < r x hx), 𝓟 {π | is_subordinate π r}

def Henstock : filter (marked_pi_partition I) :=
McShane ⊓ 𝓟 {π | is_Henstock π}

def Henstock' : filter (marked_pi_partition I) :=
McShane ⊓ 𝓟 {π | π.is_homothetic ∧ is_Henstock π}

lemma has_basis_McShane :
  (@McShane _ _ I).has_basis (λ r : Π x ∈ I, ennreal, ∀ x hx, 0 < r x hx)
    (λ r, {π | π.is_subordinate r}) :=
has_basis_binfi_principal'
  (λ r hr r' hr', ⟨λ x hx, min (r x hx) (r' x hx), λ x hx, lt_min (hr x hx) (hr' x hx),
    λ π hπ, hπ.mono $ λ x hx, min_le_left _ _, λ π hπ, hπ.mono $ λ x hx, min_le_right _ _⟩)
  ⟨λ x hx, 1, λ _ _, ennreal.zero_lt_one⟩

lemma has_basis_Henstock :
  (@Henstock _ _ I).has_basis (λ r : Π x ∈ I, ennreal, ∀ x hx, 0 < r x hx)
    (λ r, {π | π.is_subordinate r ∧ π.is_Henstock }) :=
has_basis_McShane.inf_principal _

lemma has_basis_Henstock' :
  (@Henstock' _ _ I).has_basis (λ r : Π x ∈ I, ennreal, ∀ x hx, 0 < r x hx)
    (λ r, {π | π.is_subordinate r ∧ π.is_homothetic ∧ π.is_Henstock}) :=
has_basis_McShane.inf_principal _

lemma has_basis_Riemann :
  (@Riemann _ _ I).has_basis (λ r : ennreal, 0 < r)
    (λ r, {π | (∀ J ∈ π, emetric.diam (↑J : set (ι → ℝ)) ≤ r) ∧ π.is_Henstock}) :=
begin
  refine (has_basis_binfi_principal' _ _).inf_principal _,
  exact λ r hr r' hr', ⟨min r r', lt_min hr hr',
    λ π hπ J hJ, (hπ J hJ).trans $ min_le_left _ _,
    λ π hπ J hJ, (hπ J hJ).trans $ min_le_right _ _⟩,
  exact ⟨1, ennreal.zero_lt_one⟩
end

lemma Henstock_le_McShane : @Henstock _ _ I ≤ McShane := inf_le_left

lemma Henstock_le_Riemann : @Henstock _ _ I ≤ Riemann :=
begin
  refine (inf_le_inf_right _ $ le_binfi $ λ r hr, _),
  refine binfi_le_of_le (λ _ _, r / 2) (λ _ _, ennreal.half_pos hr) _,
  refine (principal_mono.2 $ λ π hπ J hJ, _),
  simpa only [two_mul, ennreal.add_halves] using hπ.ediam_le hJ
end

lemma Henstock'_le_Henstock : @Henstock' _ _ I ≤ Henstock :=
inf_le_inf_left _ $ principal_mono.2 $ inter_subset_right _ _

instance Henstock'_ne_bot : (@Henstock' _ _ I).ne_bot :=
has_basis_Henstock'.ne_bot_iff.2 $ λ r hr, exists_is_subordinate _ hr

instance Henstock_ne_bot : (@Henstock _ _ I).ne_bot := ne_bot_of_le Henstock'_le_Henstock
instance McShane_ne_bot : (@McShane _ _ I).ne_bot := ne_bot_of_le Henstock_le_McShane
instance Riemann_ne_bot : (@Riemann _ _ I).ne_bot := ne_bot_of_le Henstock_le_Riemann

def integral_sum (f : (ι → ℝ) → E) (vol : partition_box ι → (E →L[ℝ] F))
  (π : marked_pi_partition I) : F :=
π.boxes.attach.sum $ λ J, vol J $ f $ π.center J J.coe_prop

@[simp] lemma integral_sum_add (f g : (ι → ℝ) → E) (vol : partition_box ι → (E →L[ℝ] F))
  (π : marked_pi_partition I) :
  integral_sum (f + g) vol π = integral_sum f vol π + integral_sum g vol π :=
by simp only [integral_sum, finset.sum_add_distrib, pi.add_apply, (vol _).map_add]

@[simp] lemma integral_sum_neg (f : (ι → ℝ) → E) (vol : partition_box ι → (E →L[ℝ] F))
  (π : marked_pi_partition I) :
  integral_sum (-f) vol π = -integral_sum f vol π :=
by simp only [integral_sum, finset.sum_neg_distrib, pi.neg_apply, (vol _).map_neg]

@[simp] lemma integral_sum_smul (c : ℝ) (f : (ι → ℝ) → E) (vol : partition_box ι → (E →L[ℝ] F))
  (π : marked_pi_partition I) :
  integral_sum (c • f) vol π = c • integral_sum f vol π :=
by simp only [integral_sum, finset.smul_sum, pi.smul_apply, continuous_linear_map.map_smul]

def has_integral (I : partition_box ι) (l : filter (marked_pi_partition I)) (f : (ι → ℝ) → E)
  (vol : partition_box ι → (E →L[ℝ] F)) (y : F) : Prop :=
tendsto (integral_sum f vol) l (𝓝 y)

def integrable (I : partition_box ι) (l : filter (marked_pi_partition I)) (f : (ι → ℝ) → E)
  (vol : partition_box ι → (E →L[ℝ] F)) : Prop :=
∃ y, has_integral I l f vol y

def integral (I : partition_box ι) (l : filter (marked_pi_partition I)) (f : (ι → ℝ) → E)
  (vol : partition_box ι → (E →L[ℝ] F)) : F :=
if h : integrable I l f vol then classical.some h else 0

variables {l : filter (marked_pi_partition I)}
  {f g : (ι → ℝ) → E} {vol : partition_box ι → (E →L[ℝ] F)} {y y' : F}

lemma integrable_iff_Cauchy [complete_space F] [ne_bot l] :
  integrable I l f vol ↔ cauchy (l.map (integral_sum f vol)) :=
cauchy_map_iff_exists_tendsto.symm

lemma has_integral.R_to_H (h : has_integral I Riemann f vol y) :
  has_integral I Henstock f vol y :=
h.mono_left Henstock_le_Riemann

lemma has_integral.MS_to_H (h : has_integral I McShane f vol y) :
  has_integral I Henstock f vol y :=
h.mono_left Henstock_le_McShane

lemma integrable.has_integral (h : integrable I l f vol) :
  has_integral I l f vol (integral I l f vol) :=
by { rw [integral, dif_pos h], exact classical.some_spec h }

lemma has_integral.unique [ne_bot l] (h : has_integral I l f vol y)
  (h' : has_integral I l f vol y') :
  y = y' :=
tendsto_nhds_unique h h'

lemma has_integral.integrable (h : has_integral I l f vol y) : integrable I l f vol := ⟨_, h⟩

lemma has_integral.integral_eq [ne_bot l] (h : has_integral I l f vol y) :
  integral I l f vol = y :=
h.integrable.has_integral.unique h

lemma has_integral.add (h : has_integral I l f vol y) (h' : has_integral I l g vol y') :
  has_integral I l (f + g) vol (y + y') :=
by simpa only [has_integral, ← integral_sum_add] using h.add h'

lemma integrable.add (hf : integrable I l f vol) (hg : integrable I l g vol) :
  integrable I l (f + g) vol :=
(hf.has_integral.add hg.has_integral).integrable

lemma integral_add [ne_bot l] (hf : integrable I l f vol) (hg : integrable I l g vol) :
  integral I l (f + g) vol = integral I l f vol + integral I l g vol :=
(hf.has_integral.add hg.has_integral).integral_eq

lemma has_integral.neg (hf : has_integral I l f vol y) : has_integral I l (-f) vol (-y) :=
by simpa only [has_integral, ← integral_sum_neg] using hf.neg

lemma integrable.neg (hf : integrable I l f vol) : integrable I l (-f) vol :=
hf.has_integral.neg.integrable

lemma integrable.of_neg (hf : integrable I l (-f) vol) : integrable I l f vol := neg_neg f ▸ hf.neg

@[simp] lemma integrable_neg : integrable I l (-f) vol ↔ integrable I l f vol :=
⟨λ h, h.of_neg, λ h, h.neg⟩

@[simp] lemma integral_neg [ne_bot l] : integral I l (-f) vol = -integral I l f vol :=
if h : integrable I l f vol then h.has_integral.neg.integral_eq
else by rw [integral, integral, dif_neg h, dif_neg (mt integrable.of_neg h), neg_zero]

lemma has_integral.sub (h : has_integral I l f vol y) (h' : has_integral I l g vol y') :
  has_integral I l (f - g) vol (y - y') :=
by simpa only [sub_eq_add_neg] using h.add h'.neg

lemma integrable.sub (hf : integrable I l f vol) (hg : integrable I l g vol) :
  integrable I l (f - g) vol :=
(hf.has_integral.sub hg.has_integral).integrable

lemma integral_sub [ne_bot l] (hf : integrable I l f vol) (hg : integrable I l g vol) :
  integral I l (f - g) vol = integral I l f vol - integral I l g vol :=
(hf.has_integral.sub hg.has_integral).integral_eq

lemma has_integral_zero : has_integral I l (λ _, (0:E)) vol 0 :=
by { dunfold has_integral, convert tendsto_const_nhds, ext π, simp [integral_sum] }

lemma integrable_zero : integrable I l (λ _, (0:E)) vol := ⟨0, has_integral_zero⟩

@[simp] lemma integral_zero [ne_bot l] : integral I l (λ _, (0:E)) vol = 0 :=
has_integral_zero.integral_eq

lemma has_integral.smul (hf : has_integral I l f vol y) (c : ℝ) :
  has_integral I l (c • f) vol (c • y) :=
by simpa only [has_integral, ← integral_sum_smul]
  using (tendsto_const_nhds : tendsto _ _ (𝓝 c)).smul hf

lemma integrable.smul (hf : integrable I l f vol) (c : ℝ) :
  integrable I l (c • f) vol :=
(hf.has_integral.smul c).integrable

lemma integrable.of_smul {c : ℝ} (hf : integrable I l (c • f) vol) (hc : c ≠ 0) :
  integrable I l f vol :=
by { convert hf.smul c⁻¹, ext x, simp only [pi.smul_apply, inv_smul_smul' hc] }

@[simp] lemma integral_smul [ne_bot l] (c : ℝ) :
  integral I l (λ x, c • f x) vol = c • integral I l f vol :=
begin
  rcases em (c = 0) with rfl | hc, { simp },
  by_cases hf : integrable I l f vol,
  { exact (hf.has_integral.smul c).integral_eq },
  { have : ¬integrable I l (λ x, c • f x) vol, from mt (λ h, h.of_smul hc) hf,
    rw [integral, integral, dif_neg hf, dif_neg this, smul_zero] }
end

lemma Riemann_integrable_of_continuous_on (h : continuous_on f (Icc I.lower I.upper))

end box_integral
