import Mettapedia.TypeTheory.Calculi.NativeDependent.RepresentableDeclarations
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementEvidenceExtraction

/-!
# Actual presheaf meanings of representable native declarations

The object declarations receive representable presheaf families. A unary
arrow acts by postcomposition on every generalized element, and a predicate
receives the inverse image of its actual subfunctor. Header realization is
proved by evaluating the independently authored contexts and types.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableDeclarations

open _root_.CategoryTheory Opposite
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualModelTelescopes ContextualLocalUniverses NativeLocalTypeFormers
open DisplayedPresheafTransport DisplayedPresheafComprehension

universe u
variable {C : Type u} [Category.{u} C]

noncomputable section

abbrev emptyScope : Scope C 0 := Scope.nil C

def representedFamily (object : C) (base : Cᵒᵖ ⥤ Type u) : DisplayedFamily base :=
  CategoryOfElements.π base ⋙ yoneda.obj object

def objectMeaning (object : C) : NativeType (emptyScope (C := C)).1 :=
  LocalType.present (representedFamily object emptyScope.1)

abbrev objectScope (object : C) : Scope C 1 := emptyScope.snoc (objectMeaning object)

def objectName (object : C) : (objectScope object).1 ⟶ yoneda.obj object where
  app _ := TypeCat.ofHom fun value => value.2
  naturality _ _ _ := by ext value; rfl

def objectNameInverse (object : C) : yoneda.obj object ⟶ (objectScope object).1 where
  app _ := TypeCat.ofHom fun value => ⟨PUnit.unit, value⟩
  naturality _ _ _ := by ext value; rfl

def objectScopeIso (object : C) : (objectScope object).1 ≅ yoneda.obj object where
  hom := objectName object
  inv := objectNameInverse object
  hom_inv_id := by
    ext world value
    rcases value with ⟨singleton, value⟩
    cases singleton
    rfl
  inv_hom_id := by ext world value; rfl

def representedSection {base : Cᵒᵖ ⥤ Type u} {object : C}
    (arrow : base ⟶ yoneda.obj object) : (representedFamily object base).sections where
  val point := arrow.app point.1 point.2
  property := by
    intro first second change
    change (yoneda.obj object).map change.val (arrow.app first.1 first.2) =
      arrow.app second.1 second.2
    rw [← arrow.naturality_apply change.val first.2]
    exact congrArg (arrow.app second.1) change.property

def arrowMeaning (symbol : ArrowSymbol C) : NativeType (objectScope symbol.source).1 :=
  (objectMeaning symbol.target).reindex
    ((NativeModel C).toCwf.wk (objectMeaning symbol.source))

def arrowValue (symbol : ArrowSymbol C) : (arrowMeaning symbol).decoded.sections :=
  representedSection (objectName symbol.source ≫ yoneda.map symbol.arrow)

def model (C : Type u) [Category.{u} C] : ModelData (symbols C) C where
  typeParameters := fun _ => emptyScope
  typeFamily := fun object => objectMeaning (C := C) object
  termParameters := fun symbol => objectScope symbol.source
  termType := arrowMeaning
  termValue := arrowValue
  predicateParameters := fun symbol => objectScope symbol.domain
  predicateValue := fun symbol => symbol.predicate.preimage (objectName symbol.domain)

theorem object_read (object : C) {n : Nat} (scope : Scope C n) :
    (model C).evaluateType scope (objectType object n) =
      some ((objectMeaning object).reindex ((NativeModel C).toEmpty scope.1)) :=
  (model C).evaluate_family scope object Fin.elim0 ((NativeModel C).toEmpty scope.1)
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

set_option backward.isDefEq.respectTransparency false in
theorem object_in_scope_read (source target : C) :
    (model C).evaluateType (objectScope source) (objectType target 1) =
      some ((objectMeaning target).reindex ((NativeModel C).toCwf.wk (objectMeaning source))) := by
  have read := object_read target (objectScope source)
  have projection : (NativeModel C).toEmpty (objectScope source).1 =
      (NativeModel C).toCwf.wk (objectMeaning source) :=
    ((NativeModel C).toEmpty_unique _ _).symm
  rw [projection] at read
  exact read

/-- No declaration-interpretation theorem is supplied as model data. Each
header and result readout is earned from the raw evaluator. -/
theorem realization (C : Type u) [Category.{u} C] :
    SignatureRealization (model C) (signature C) where
  typeHeader := fun _ => rfl
  termHeader := fun symbol => object_context_read symbol.source
  predicateHeader := fun symbol => object_context_read symbol.domain
  termResult := fun symbol => object_in_scope_read symbol.source symbol.target

theorem variable_read (object : C) :
    (model C).evaluateTerm (objectScope object) (.var 0) =
      some ((objectScope object).2.lookup 0) := rfl

theorem variable_identity (object : C) :
    (model C).evaluateTerm (objectScope object) (.var 0) =
      some (((objectScope object).2.lookup 0).substitute
        ((NativeModel C).toCwf.idS (objectScope object).1)) := by
  rw [Value.substitute_identity]
  exact variable_read object

theorem arrow_read {source target : C} (arrow : source ⟶ target) :
    (model C).evaluateTerm (objectScope source) (arrowTerm arrow (.var 0)) =
      some ⟨arrowMeaning ⟨source, target, arrow⟩, arrowValue ⟨source, target, arrow⟩⟩ := by
  have read := (model C).evaluate_primitive (objectScope source) ⟨source, target, arrow⟩
    (singletonArgument (.var 0)) (𝟙 (objectScope source).1) (by
      intro position
      cases position using Fin.cases with
      | zero => exact variable_identity source
      | succ impossible => exact Fin.elim0 impossible)
  change (model C).evaluateTerm (objectScope source) (arrowTerm arrow (.var 0)) =
    some (Value.substitute (K := (NativeModel C).toCwf)
      (⟨arrowMeaning ⟨source, target, arrow⟩, arrowValue ⟨source, target, arrow⟩⟩ :
        NativeValue (objectScope source).1) (𝟙 (objectScope source).1)) at read
  exact read.trans (congrArg some
    (Value.substitute_identity (K := (NativeModel C).toCwf)
      ⟨arrowMeaning ⟨source, target, arrow⟩, arrowValue ⟨source, target, arrow⟩⟩))

theorem predicate_read {object : C} (predicate : Subfunctor (yoneda.obj object)) :
    (model C).evaluatePredicate (objectScope object) (predicateTerm predicate (.var 0)) =
      some (predicate.preimage (objectName object)) := by
  have read := (model C).evaluate_predicateAtom (objectScope object) ⟨object, predicate⟩
    (singletonArgument (.var 0)) (𝟙 (objectScope object).1) (by
      intro position
      cases position using Fin.cases with
      | zero => exact variable_identity object
      | succ impossible => exact Fin.elim0 impossible)
  change (model C).evaluatePredicate (objectScope object) (predicateTerm predicate (.var 0)) =
    some ((predicate.preimage (objectName object)).preimage (𝟙 (objectScope object).1)) at read
  rw [Subfunctor.preimage_id] at read
  exact read

theorem arrow_value_readout {source target : C} (arrow : source ⟶ target)
    (world : C) (argument : world ⟶ source) :
    (arrowValue ⟨source, target, arrow⟩).val
      ⟨op world, (objectNameInverse source).app (op world) argument⟩ = argument ≫ arrow := rfl

theorem predicate_value_readout {object world : C} (predicate : Subfunctor (yoneda.obj object))
    (argument : world ⟶ object) :
    (objectNameInverse object).app (op world) argument ∈
      (predicate.preimage (objectName object)).obj (op world) ↔
        argument ∈ predicate.obj (op world) := Iff.rfl

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableDeclarations
