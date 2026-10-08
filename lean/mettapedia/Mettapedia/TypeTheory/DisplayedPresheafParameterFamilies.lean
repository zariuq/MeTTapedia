import Mettapedia.TypeTheory.DisplayedPresheafCwf

/-!
# External parameter families in a presheaf context

A parameter context supplies a displayed family by retaining its value at
the underlying syntax world. Natural sections of this family are exactly
natural maps into that parameter context. The correspondence retains the
map's action at every world and commutes with arbitrary context substitution.
This construction does not posit an internal universe.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafParameterFamilies

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open DisplayedPresheafTransport DisplayedPresheafComprehension

universe u
variable {C : Type u} [Category.{u} C]
variable {P Q R : Face.{u, u, u} C}

def parameterFamily (base parameters : Face.{u, u, u} C) :
    DisplayedFamily.{u, u, u, u} base where
  obj point := parameters.obj point.1
  map arrow := parameters.map arrow.val
  map_id _ := parameters.map_id _
  map_comp first second := parameters.map_comp first.val second.val

def parameterSection (name : P ⟶ Q) : (parameterFamily P Q).sections where
  val point := name.app point.1 point.2
  property := by
    intro source target arrow
    change Q.map arrow.val (name.app source.1 source.2) = name.app target.1 target.2
    rw [← name.naturality_apply arrow.val source.2, arrow.property]

def parameterName (witness : (parameterFamily P Q).sections) : P ⟶ Q where
  app world := TypeCat.ofHom fun value => witness.val ⟨world, value⟩
  naturality := by
    intro source target arrow
    apply ConcreteCategory.hom_ext
    intro value
    exact (witness.property (CategoryOfElements.homMk
      (F := P) ⟨source, value⟩ ⟨target, P.map arrow value⟩ arrow rfl)).symm

theorem parameterName_section (name : P ⟶ Q) :
    parameterName (parameterSection name) = name := by
  ext world value
  rfl

theorem parameterSection_name (witness : (parameterFamily P Q).sections) :
    parameterSection (parameterName witness) = witness := by
  apply Subtype.ext
  rfl

def parameterSectionEquiv (base parameters : Face.{u, u, u} C) :
    (base ⟶ parameters) ≃ (parameterFamily base parameters).sections where
  toFun := parameterSection
  invFun := parameterName
  left_inv := parameterName_section
  right_inv := parameterSection_name

theorem parameterFamily_reindex (substitution : R ⟶ P) :
    reindexDisplayed substitution (parameterFamily P Q) = parameterFamily R Q := by
  rfl

theorem parameterSection_substitution (substitution : R ⟶ P) (name : P ⟶ Q) :
    reindexDisplayedSection substitution (parameterFamily P Q)
        (parameterSection name) = parameterSection (substitution ≫ name) := by
  rfl

theorem parameterName_substitution (substitution : R ⟶ P)
    (witness : (parameterFamily P Q).sections) :
    parameterName (reindexDisplayedSection substitution (parameterFamily P Q) witness) =
      substitution ≫ parameterName witness := by
  ext world value
  rfl

/-- The parameter section records the supplied map, rather than merely the
existence of a value at each object. -/
theorem parameterSection_injective :
    Function.Injective (parameterSection (P := P) (Q := Q)) :=
  (parameterSectionEquiv P Q).injective

end Mettapedia.TypeTheory.DisplayedPresheafParameterFamilies
