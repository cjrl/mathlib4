/-
Copyright (c) 2025 Christopher J. R. Lloyd All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher J. R. Lloyd
-/
import Mathlib.Topology.Defs.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.CategoryTheory.ConcreteCategory.Bundled
import Mathlib.Topology.ContinuousMap.Defs
import Mathlib

/-!
# Basic definitions about equivarant topological spaces

This file contains contains the basic definitions of the Category of Equivariant Topological Spaces,
that is, spaces with G-action.

https://ncatlab.org/nlab/show/topological+G-space

This follows the treatment of Tammo tom Dieck, Transformation Groups, de Gruyter 1987
(doi:10.1515/9783110858372).
-/

namespace Equivariant

universe u v

open CategoryTheory

class LeftEquivariantSpace (G : Type u) (X : Type v)
[Group G] [TopologicalSpace G] extends
  TopologicalSpace X,
  MulAction G X where
  is_continuous : Continuous smul

structure GTopCat (G : Type u) [Group G] [TopologicalSpace G] where
  private mk ::
  /-- The underlying type. -/
  carrier : Type v
  [carrier_top : TopologicalSpace carrier]
  [action : LeftEquivariantSpace G carrier]

variable {G : Type u} [Group G] [TopologicalSpace G]

instance : CoeSort (GTopCat G) (Type v) :=
  ⟨GTopCat.carrier⟩

attribute [coe] GTopCat.carrier

instance instTopologicalSpace (X : GTopCat G) : TopologicalSpace X :=
  X.carrier_top

instance instLeftEquivariantSpace (X : GTopCat G) : LeftEquivariantSpace G X :=
  X.action

class GMap (G : Type u) [Group G] [TopologicalSpace G]
  (X Y : Type v) [LeftEquivariantSpace G X] [LeftEquivariantSpace G Y]
  extends ContinuousMap X Y where
  equivariant : ∀ (g : G) (x : X), g • toFun (x) = toFun (g • x)

notation "C("G ", " X ", " Y ")" => GMap G X Y

class GMapClass (F : Type*) (X Y : outParam Type*) [Group G] [TopologicalSpace G]
    [LeftEquivariantSpace G X] [LeftEquivariantSpace G Y] [FunLike F X Y] : Prop where
  /-- Continuity -/
  map_continuous (f : F) : Continuous f
  /-- Equivariance -/
  equivariant (f : F) : ∀ (g : G) (x : X), g • f (x) = f (g • x)

/-- The type of morphisms in `GTopCat`. -/
@[ext]
structure Hom (X Y : GTopCat G) where
  private mk ::
  /-- The underlying `ContinuousMap`. -/
  hom' : C(G, X, Y)

abbrev of (X : Type v) [LeftEquivariantSpace G X] : GTopCat G :=
  ⟨X⟩

lemma coe_of (X : Type v) [LeftEquivariantSpace G X] : (of X (G := G) : Type v) = X :=
  rfl

variable {X : Type v} [LeftEquivariantSpace G X]

protected def id : C(G, X, X) where
  toFun := id
  equivariant := by
    simp

variable {α β γ δ : Type v} [LeftEquivariantSpace G α] [LeftEquivariantSpace G β]
  [LeftEquivariantSpace G γ] [LeftEquivariantSpace G δ]

def comp (f : C(G, β, γ)) (g : C(G, α, β)) : C(G, α, γ) where
  toFun := f.toFun ∘ g.toFun
  equivariant := by
    intro h x
    unfold Function.comp
    rw [<- g.equivariant]
    rw [<- f.equivariant]

instance : Category (GTopCat G) where
  Hom X Y := Hom X Y
  id X := ⟨Equivariant.id⟩
  comp f g := ⟨Equivariant.comp g.hom' f.hom'⟩

end Equivariant
