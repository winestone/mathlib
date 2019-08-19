/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Mario Carneiro, Reid Barton
-/
import topology.Top.opens
import category_theory.whiskering
import category_theory.limits.functor_category

universes v u

open category_theory
open category_theory.limits
open topological_space
open opposite

variables (C : Type u) [𝒞 : category.{v+1} C]
include 𝒞

namespace Top

def presheaf (X : Top.{v}) := (opens X)ᵒᵖ ⥤ C

instance category_presheaf (X : Top.{v}) : category (X.presheaf C) :=
by dsimp [presheaf]; apply_instance

instance (X : Top.{v}) {J : Type v} [small_category J] [has_limits_of_shape.{v} J C] :
  has_limits_of_shape.{v} J (X.presheaf C) :=
by { dsimp [presheaf], apply_instance }

instance (X : Top.{v}) {J : Type v} [small_category J] [has_colimits_of_shape.{v} J C] :
  has_colimits_of_shape.{v} J (X.presheaf C) :=
by { dsimp [presheaf], apply_instance }

namespace presheaf
variables {C}

def pushforward {X Y : Top.{v}} (f : X ⟶ Y) (ℱ : X.presheaf C) : Y.presheaf C :=
(opens.map f).op ⋙ ℱ

infix ` _* `: 80 := pushforward

@[simp] lemma pushforward_obj {X Y : Top.{v}} (f : X ⟶ Y) (ℱ : X.presheaf C) (U : (opens Y)ᵒᵖ) :
  (f _* ℱ).obj U = ℱ.obj ((opens.map f).op.obj U) := rfl

def pushforward_map {X Y : Top.{v}} (f : X ⟶ Y) {ℱ 𝒢 : X.presheaf C} (α : ℱ ⟶ 𝒢) : f _* ℱ ⟶ f _* 𝒢 :=
whisker_left (opens.map f).op α

def pushforward_eq {X Y : Top.{v}} {f g : X ⟶ Y} (h : f = g) (ℱ : X.presheaf C) :
  f _* ℱ ≅ g _* ℱ :=
iso_whisker_right (nat_iso.op (opens.map_iso f g h).symm) ℱ
lemma pushforward_eq_eq {X Y : Top.{v}} {f g : X ⟶ Y} (h₁ h₂ : f = g) (ℱ : X.presheaf C) :
  ℱ.pushforward_eq h₁ = ℱ.pushforward_eq h₂ :=
rfl

namespace pushforward
variables {X : Top.{v}} (ℱ : X.presheaf C)

def id : (𝟙 X) _* ℱ ≅ ℱ :=
(iso_whisker_right (nat_iso.op (opens.map_id X).symm) ℱ) ≪≫ functor.left_unitor _

@[simp] lemma id_hom_app' (U) (p) :
  (id ℱ).hom.app (op ⟨U, p⟩) = ℱ.map (𝟙 (op ⟨U, p⟩)) :=
by { dsimp [id], simp, }

local attribute [tidy] tactic.op_induction'

@[simp] lemma id_hom_app (U) :
  (id ℱ).hom.app U = ℱ.map (eq_to_hom (opens.op_map_id_obj U)) := by tidy

@[simp] lemma id_inv_app' (U) (p) : (id ℱ).inv.app (op ⟨U, p⟩) = ℱ.map (𝟙 (op ⟨U, p⟩)) :=
by { dsimp [id], simp, }

def comp {Y Z : Top.{v}} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g) _* ℱ ≅ g _* (f _* ℱ) :=
iso_whisker_right (nat_iso.op (opens.map_comp f g).symm) ℱ

@[simp] lemma comp_hom_app {Y Z : Top.{v}} (f : X ⟶ Y) (g : Y ⟶ Z) (U) : (comp ℱ f g).hom.app U = 𝟙 _ :=
begin
  dsimp [pushforward, comp],
  tidy,
end

@[simp] lemma comp_inv_app {Y Z : Top.{v}} (f : X ⟶ Y) (g : Y ⟶ Z) (U) : (comp ℱ f g).inv.app U = 𝟙 _ :=
begin
  dsimp [pushforward, comp],
  tidy,
end

end pushforward

end presheaf

end Top
