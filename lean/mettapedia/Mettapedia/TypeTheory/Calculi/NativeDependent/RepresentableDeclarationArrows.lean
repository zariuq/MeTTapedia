import Mettapedia.TypeTheory.Calculi.NativeDependent.RepresentableDeclarationConservativity
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualQuotient

/-!
# Generated substitutions between represented source contexts

The objects retain the supplied category objects. Their arrows are the
actual well-typed generated substitutions between the corresponding unary
native contexts; every dependent and logical constructor remains available
inside those arrows. Evaluation uses the earned soundness theorem at the
independently supplied representable scopes.

This is the category on the represented context image, not the whole native
context category or a closed dependent classifying category.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableDeclarations

open _root_.CategoryTheory Opposite
open ContextualModelTelescopes NativeLocalTypeFormers

universe u
variable {C : Type u} [Category.{u} C]

noncomputable section

abbrev representedContext (object : C) : Contextual.Context (signature C) :=
  ⟨1, objectContext object, .snoc .nil ⟨objectFormed object emptyFormed⟩⟩

/-- Original objects remain distinct raw objects; generated substitutions
form their arrow carrier. -/
structure RepresentedContext (C : Type u) where
  object : C

instance : Category (RepresentedContext C) where
  Hom source target := representedContext source.object ⟶ representedContext target.object
  id source := 𝟙 (representedContext source.object)
  comp earlier later := earlier ≫ later
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

def originalArrow {source target : C} (arrow : source ⟶ target) :
    (⟨source⟩ : RepresentedContext C) ⟶ ⟨target⟩ :=
  ⟨singletonArgument (arrowTerm arrow (.var 0)),
    ⟨objectArguments target (objectContextFormed source)
      (arrowFormed arrow (objectContextFormed source) (variableFormed source))⟩⟩

def readArrow {source target : RepresentedContext C} (arrow : source ⟶ target) :
    (objectScope source.object).1 ⟶ (objectScope target.object).1 :=
  Derivation.substitutionArrow (model C) (realization C)
    (NativeLocalTypeOperations.products_substitution C)
    (NativeLocalTypeOperations.products_beta C) (NativeLocalPiEta.products_eta C)
    (Classical.choice arrow.admitted) (objectScope source.object) (objectScope target.object)
    (object_context_read source.object) (object_context_read target.object)

theorem readArrow_readout {source target : RepresentedContext C} (arrow : source ⟶ target) :
    (model C).evaluateSubstitution (objectScope source.object) (objectScope target.object)
      arrow.substitution = some (readArrow arrow) :=
  Derivation.substitutionArrow_readout (model C) (realization C)
    (NativeLocalTypeOperations.products_substitution C)
    (NativeLocalTypeOperations.products_beta C) (NativeLocalPiEta.products_eta C)
    (Classical.choice arrow.admitted) _ _ _ _

theorem readArrow_unique {source target : RepresentedContext C} (arrow : source ⟶ target)
    (value : (objectScope source.object).1 ⟶ (objectScope target.object).1)
    (readout : (model C).evaluateSubstitution (objectScope source.object) (objectScope target.object)
      arrow.substitution = some value) : readArrow arrow = value :=
  Option.some.inj ((readArrow_readout arrow).symm.trans readout)

theorem readArrow_identity (source : RepresentedContext C) :
    readArrow (𝟙 source) = 𝟙 (objectScope source.object).1 :=
  readArrow_unique (𝟙 source) _ ((model C).evaluateSubstitution_identity _)

theorem readArrow_composition {source middle target : RepresentedContext C}
    (earlier : source ⟶ middle) (later : middle ⟶ target) :
    readArrow (earlier ≫ later) = readArrow earlier ≫ readArrow later :=
  readArrow_unique (earlier ≫ later) _
    ((model C).evaluateSubstitution_composition
      (NativeLocalTypeOperations.products_substitution C)
      (objectScope middle.object) (objectScope target.object) (objectScope source.object)
      later.substitution earlier.substitution (readArrow later) (readArrow earlier)
      (readArrow_readout later) (readArrow_readout earlier))

def representedReadout : RepresentedContext C ⥤ Cᵒᵖ ⥤ Type u where
  obj source := (objectScope source.object).1
  map := readArrow
  map_id := readArrow_identity
  map_comp := readArrow_composition

theorem readArrow_generated_equation {source target : RepresentedContext C}
    {first second : source ⟶ target}
    (equation : Contextual.homEquality (signature C) first second) :
    readArrow first = readArrow second :=
  Derivation.substitutionArrow_equation (model C) (realization C)
    (NativeLocalTypeOperations.products_substitution C)
    (NativeLocalTypeOperations.products_beta C) (NativeLocalPiEta.products_eta C)
    (Classical.choice first.admitted) (Classical.choice second.admitted)
    (Classical.choice equation) _ _ _ _

/-- The complete source name and every original arrow determine this
presheaf map independently of the generated substitution parser. -/
def originalPresheafArrow {source target : C} (arrow : source ⟶ target) :
    (objectScope source).1 ⟶ (objectScope target).1 :=
  (NativeModel C).toCwf.pair ((NativeModel C).toCwf.wk (objectMeaning source))
    (objectMeaning target) (arrowValue ⟨source, target, arrow⟩)

theorem originalPresheafArrow_name {source target : C} (arrow : source ⟶ target) :
    originalPresheafArrow arrow =
      objectName source ≫ yoneda.map arrow ≫ objectNameInverse target := by
  ext world value
  rcases value with ⟨singleton, value⟩
  cases singleton
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem original_component {source target : C} (arrow : source ⟶ target) :
    (objectScope target).2.components (originalPresheafArrow arrow) 0 =
      ⟨arrowMeaning ⟨source, target, arrow⟩, arrowValue ⟨source, target, arrow⟩⟩ := by
  exact ScopeData.components_pair_zero (emptyScope (C := C)).2 (objectMeaning target)
    ((NativeModel C).toCwf.wk (objectMeaning source)) (arrowValue ⟨source, target, arrow⟩)

theorem readArrow_original {source target : C} (arrow : source ⟶ target) :
    readArrow (originalArrow arrow) = originalPresheafArrow arrow := by
  apply readArrow_unique
  apply ((model C).evaluateSubstitution_eq_some_iff _ _ _ _).2
  intro position
  cases position using Fin.cases with
  | zero =>
      change (model C).evaluateTerm (objectScope source) (arrowTerm arrow (.var 0)) = _
      rw [original_component]
      exact arrow_read arrow
  | succ impossible => exact Fin.elim0 impossible

theorem originalPresheafArrow_identity (object : C) :
    originalPresheafArrow (𝟙 object) = 𝟙 (objectScope object).1 := by
  rw [originalPresheafArrow_name, _root_.CategoryTheory.Functor.map_id, Category.id_comp]
  exact (objectScopeIso object).hom_inv_id

theorem originalPresheafArrow_composition {source middle target : C}
    (earlier : source ⟶ middle) (later : middle ⟶ target) :
    originalPresheafArrow (earlier ≫ later) =
      originalPresheafArrow earlier ≫ originalPresheafArrow later := by
  rw [originalPresheafArrow_name, originalPresheafArrow_name, originalPresheafArrow_name,
    _root_.CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  have cancellation : objectNameInverse middle ≫ objectName middle = 𝟙 (yoneda.obj middle) :=
    (objectScopeIso middle).inv_hom_id
  rw [← Category.assoc (objectNameInverse middle), cancellation]
  simp only [Category.id_comp]

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableDeclarations
