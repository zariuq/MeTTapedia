import Mettapedia.TypeTheory.Calculi.NativeDependent.RepresentableIndexedDeclarations
import Mettapedia.TypeTheory.Calculi.NativeDependent.RepresentableDeclarationInterpretation

/-!
# Original-arrow fibres interpret generated dependent declarations

An indexed declaration receives the actual fibre of the original Yoneda
map, pulled back to the generated target-object scope. The forgetful term
retains the whole original source arrow. Raw header evaluation earns the
declaration realization; soundness is not supplied as model data.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableIndexedDeclarations

open _root_.CategoryTheory Opposite
open ContextualModelTelescopes ContextualLocalUniverses NativeLocalTypeFormers
open DisplayedPresheafTransport DisplayedPresheafComprehension

universe u
variable {C : Type u} [Category.{u} C]

noncomputable section

abbrev emptyScope : Scope C 0 := RepresentableDeclarations.emptyScope
abbrev objectMeaning (object : C) := RepresentableDeclarations.objectMeaning object
abbrev objectScope (object : C) := RepresentableDeclarations.objectScope object
abbrev objectName (object : C) := RepresentableDeclarations.objectName object
abbrev objectNameInverse (object : C) := RepresentableDeclarations.objectNameInverse object
abbrev objectScopeIso (object : C) := RepresentableDeclarations.objectScopeIso object

def fibreFamily (arrow : ArrowSymbol C) : DisplayedFamily (objectScope arrow.target).1 :=
  reindexDisplayed (objectName arrow.target) (observationFibreFamily (yoneda.map arrow.arrow))

def fibreMeaning (arrow : ArrowSymbol C) : NativeType (objectScope arrow.target).1 :=
  LocalType.present (fibreFamily arrow)

abbrev fibreScope (arrow : ArrowSymbol C) : Scope C 2 :=
  (objectScope arrow.target).snoc (fibreMeaning arrow)

def fibreName (arrow : ArrowSymbol C) : (fibreScope arrow).1 ⟶ yoneda.obj arrow.source where
  app _ := TypeCat.ofHom fun value => value.2.val
  naturality _ _ _ := by ext value; rfl

def forgetType (arrow : ArrowSymbol C) : NativeType (fibreScope arrow).1 :=
  (objectMeaning arrow.source).reindex ((NativeModel C).toEmpty (fibreScope arrow).1)

def forgetValue (arrow : ArrowSymbol C) : (forgetType arrow).decoded.sections :=
  RepresentableDeclarations.representedSection (fibreName arrow)

def model (C : Type u) [Category.{u} C] : ModelData (symbols C) C where
  typeParameters := fun symbol => match symbol with
    | .object _ => emptyScope
    | .fibre arrow => objectScope arrow.target
  typeFamily := fun symbol => match symbol with
    | .object object => objectMeaning object
    | .fibre arrow => fibreMeaning arrow
  termParameters := fun symbol => match symbol with
    | .ordinary arrow => objectScope arrow.source
    | .forget arrow => fibreScope arrow
  termType := fun symbol => match symbol with
    | .ordinary arrow => RepresentableDeclarations.arrowMeaning arrow
    | .forget arrow => forgetType arrow
  termValue := fun symbol => match symbol with
    | .ordinary arrow => RepresentableDeclarations.arrowValue arrow
    | .forget arrow => forgetValue arrow
  predicateParameters := fun symbol => objectScope symbol.domain
  predicateValue := fun symbol => symbol.predicate.preimage (objectName symbol.domain)

theorem object_read (object : C) {n : Nat} (scope : Scope C n) :
    (model C).evaluateType scope (objectType object n) =
      some ((objectMeaning object).reindex ((NativeModel C).toEmpty scope.1)) :=
  (model C).evaluate_family scope (.object object) Fin.elim0 ((NativeModel C).toEmpty scope.1)
    (fun position => Fin.elim0 position)

set_option backward.isDefEq.respectTransparency false in
theorem object_empty_read (object : C) :
    (model C).evaluateType emptyScope (objectType object 0) = some (objectMeaning object) := by
  have read := object_read object emptyScope
  have identity : (NativeModel C).toEmpty emptyScope.1 = (NativeModel C).toCwf.idS emptyScope.1 :=
    ((NativeModel C).toEmpty_unique _ _).symm
  change (model C).evaluateType emptyScope (objectType object 0) =
    some ((NativeModel C).toCwf.tySub (objectMeaning object) ((NativeModel C).toEmpty emptyScope.1)) at read
  rw [identity, (NativeModel C).toCwf.tySub_id] at read
  exact read

theorem object_context_read (object : C) :
    (model C).evaluateContext (objectContext object) = some (objectScope object) :=
  (model C).evaluateContext_snoc .nil (objectType object 0) emptyScope
    (objectMeaning object) rfl (object_empty_read object)

theorem variable_identity (object : C) :
    (model C).evaluateTerm (objectScope object) (.var 0) =
      some (((objectScope object).2.lookup 0).substitute
        ((NativeModel C).toCwf.idS (objectScope object).1)) := by
  rw [Value.substitute_identity]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem generic_fibre_read (arrow : ArrowSymbol C) :
    (model C).evaluateType (objectScope arrow.target) (fibreType arrow (.var 0)) =
      some (fibreMeaning arrow) := by
  have read := (model C).evaluate_family (objectScope arrow.target) (.fibre arrow)
    (singletonArgument (.var 0)) (𝟙 (objectScope arrow.target).1) (by
      intro position
      cases position using Fin.cases with
      | zero => exact variable_identity arrow.target
      | succ impossible => exact Fin.elim0 impossible)
  change (model C).evaluateType (objectScope arrow.target) (fibreType arrow (.var 0)) =
    some ((NativeModel C).toCwf.tySub (fibreMeaning arrow)
      ((NativeModel C).toCwf.idS (objectScope arrow.target).1)) at read
  rw [(NativeModel C).toCwf.tySub_id] at read
  exact read

theorem fibre_context_read (arrow : ArrowSymbol C) :
    (model C).evaluateContext (fibreContext arrow) = some (fibreScope arrow) :=
  (model C).evaluateContext_snoc (objectContext arrow.target) (fibreType arrow (.var 0))
    (objectScope arrow.target) (fibreMeaning arrow)
    (object_context_read arrow.target) (generic_fibre_read arrow)

set_option backward.isDefEq.respectTransparency false in
theorem ordinary_result_read (arrow : ArrowSymbol C) :
    (model C).evaluateType (objectScope arrow.source) (objectType arrow.target 1) =
      some (RepresentableDeclarations.arrowMeaning arrow) := by
  have read := object_read arrow.target (objectScope arrow.source)
  have projection : (NativeModel C).toEmpty (objectScope arrow.source).1 =
      (NativeModel C).toCwf.wk (objectMeaning arrow.source) :=
    ((NativeModel C).toEmpty_unique _ _).symm
  rw [projection] at read
  exact read

theorem realization (C : Type u) [Category.{u} C] :
    SignatureRealization (model C) (signature C) where
  typeHeader := by
    intro symbol
    cases symbol with
    | object => rfl
    | fibre arrow => exact object_context_read arrow.target
  termHeader := by
    intro symbol
    cases symbol with
    | ordinary arrow => exact object_context_read arrow.source
    | forget arrow => exact fibre_context_read arrow
  termResult := by
    intro symbol
    cases symbol with
    | ordinary arrow => exact ordinary_result_read arrow
    | forget arrow => exact object_read arrow.source (fibreScope arrow)
  predicateHeader := fun symbol => object_context_read symbol.domain

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableIndexedDeclarations
