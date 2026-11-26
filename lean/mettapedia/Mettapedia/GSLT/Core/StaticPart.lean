import Mettapedia.GSLT.Core.IndexedOperational
import Mettapedia.GSLT.Core.StepFree
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# The static part of an operational GSLT

For forward operational maps, forgetting directed reductions gives the
right adjoint to the inclusion of step-free theories. Terms and equations
are retained. A translation from a static source into a running theory
factors uniquely through the static part. This identifies the commuting
square associated with a chosen translation on syntax.

The comparison into a running theory is a forward map. It covers the
target's steps precisely when the target is itself step-free.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.IndexedOperational.StaticPart

open _root_.CategoryTheory
open scoped _root_.CategoryTheory
open Mettapedia.GSLT.Ultrainfinite (StepCover)

universe u

def StepFree : ObjectProperty OperationalTheory.{u} :=
  fun X => ∀ s t, ¬ X.theory.Step s t

abbrev StaticTheory := StepFree.{u}.FullSubcategory

abbrev includeStatic : StaticTheory.{u} ⥤ OperationalTheory.{u} := StepFree.ι

/-- Retain the terms and equations of a theory and remove its reductions. -/
def erase (X : OperationalTheory.{u}) : StaticTheory.{u} :=
  ⟨⟨GSLT.equationOnly X.theory.Term X.theory.equations⟩, fun _ _ h => h⟩

/-- Rules are forgotten functorially along equation-preserving term maps. -/
def forgetSteps : OperationalTheory.{u} ⥤ StaticTheory.{u} where
  obj := erase
  map f := ObjectProperty.homMk
    { mapTerm := f.mapTerm, mapEquiv := f.mapEquiv, mapStep := fun h => h.elim }
  map_id _ := by
    apply ObjectProperty.hom_ext
    apply OperationalTranslation.ext
    rfl
  map_comp _ _ := by
    apply ObjectProperty.hom_ext
    apply OperationalTranslation.ext
    rfl

def homEquiv (A : StaticTheory.{u}) (X : OperationalTheory.{u}) :
    (includeStatic.obj A ⟶ X) ≃ (A ⟶ forgetSteps.obj X) where
  toFun f := ObjectProperty.homMk
    { mapTerm := f.mapTerm, mapEquiv := f.mapEquiv,
      mapStep := fun {s t} moved => (A.property s t moved).elim }
  invFun f :=
    { mapTerm := f.hom.mapTerm, mapEquiv := f.hom.mapEquiv,
      mapStep := fun {s t} moved => (A.property s t moved).elim }
  left_inv f := OperationalTranslation.ext rfl
  right_inv f := by
    apply ObjectProperty.hom_ext
    apply OperationalTranslation.ext
    rfl

/-- The static subcategory is coreflective in the forward operational
category. This adjunction keeps all the authored equations. -/
def adjunction : includeStatic.{u} ⊣ forgetSteps.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv
      homEquiv_naturality_left_symm := by
        intros
        apply OperationalTranslation.ext
        rfl
      homEquiv_naturality_right := by
        intros
        apply ObjectProperty.hom_ext
        apply OperationalTranslation.ext
        rfl }

/-- The inclusion of the static part changes no term. -/
def inclusion (X : OperationalTheory.{u}) : (erase X).obj ⟶ X where
  mapTerm := id
  mapEquiv := fun h => h
  mapStep := fun h => h.elim

theorem counit_eq_inclusion (X : OperationalTheory.{u}) :
    adjunction.counit.app X = inclusion X := by
  apply OperationalTranslation.ext
  rfl

/-- The authored term map commutes with forgetting the rules. -/
theorem inclusion_natural {X Y : OperationalTheory.{u}} (f : X ⟶ Y) :
    (forgetSteps.map f).hom ≫ inclusion Y = inclusion X ≫ f :=
  OperationalTranslation.ext rfl

/-- Any implementation of a static source through a running target admits
a unique factorization through the target's static part. -/
theorem factors_uniquely (A : StaticTheory.{u}) (X : OperationalTheory.{u})
    (f : includeStatic.obj A ⟶ X) :
    ∃! g : A ⟶ forgetSteps.obj X, g.hom ≫ inclusion X = f := by
  refine ⟨homEquiv A X f, ?_, ?_⟩
  · apply OperationalTranslation.ext
    rfl
  intro g same
  apply ObjectProperty.hom_ext
  apply OperationalTranslation.ext
  have underlying := congrArg
    (fun h : OperationalTranslation A.obj.theory X.theory => h.mapTerm) same
  exact underlying

/-- A forward inclusion of syntax covers target steps exactly when
there are no target steps to lift. -/
theorem covers_iff (X : OperationalTheory.{u}) :
    Nonempty (StepCover (erase X).obj.theory X.theory (inclusion X).mapTerm) ↔ StepFree X := by
  constructor
  · rintro ⟨cover⟩ s t moved
    obtain ⟨_, impossible, _⟩ := cover.liftStep (sourceTerm := s) moved
    exact impossible
  · intro quiet
    exact ⟨⟨fun h => h.elim, fun {s t} moved => (quiet s t moved).elim⟩⟩

end Mettapedia.GSLT.IndexedOperational.StaticPart

#print axioms Mettapedia.GSLT.IndexedOperational.StaticPart.adjunction
#print axioms Mettapedia.GSLT.IndexedOperational.StaticPart.factors_uniquely
#print axioms Mettapedia.GSLT.IndexedOperational.StaticPart.covers_iff
