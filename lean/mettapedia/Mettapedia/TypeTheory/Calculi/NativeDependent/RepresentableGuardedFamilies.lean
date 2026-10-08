import Mettapedia.TypeTheory.Calculi.NativeDependent.RepresentableDeclarationSubstitution

/-!
# Generated dependent families guarded by original predicates

An original representable predicate is tested on the retained outer
argument. The generated comprehension family contains a complete supplied
inhabitant exactly when that argument belongs to the predicate. Its decoder
and restriction maps are the actual native comprehension constructions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableDeclarations.GuardedObject

open _root_.CategoryTheory Opposite
open ContextualModelTelescopes NativeLocalTypeFormers
open DisplayedPresheafTransport DisplayedPresheafComprehension

universe u
variable {C : Type u} [Category.{u} C]

noncomputable section

def baseType (source target : C) : NativeType (objectScope source).1 :=
  (objectMeaning target).reindex ((NativeModel C).toCwf.wk (objectMeaning source))

abbrev innerScope (source target : C) : Scope C 2 :=
  (objectScope source).snoc (baseType source target)

def predicateCode {source : C} (predicate : Subfunctor (yoneda.obj source)) :
    PropExpr (symbols C) 2 := predicateTerm predicate (.var 1)

def typeCode {source : C} (target : C) (predicate : Subfunctor (yoneda.obj source)) :
    TypeExpr (symbols C) 1 := .comprehension (objectType target 1) (predicateCode predicate)

def innerContext (source target : C) : ContextExpr (symbols C) 2 :=
  .snoc (objectContext source) (objectType target 1)

def innerContextFormed (source target : C) :
    Derivation (signature C) (.context (innerContext source target)) :=
  deriveList (.contextExtend (objectContext source) (objectType target 1))
    (.cons (objectContextFormed source)
      (.cons (objectFormed target (objectContextFormed source)) .nil))

def outerVariableFormed (source target : C) :
    Derivation (signature C) (.term (innerContext source target) (.var 1) (objectType source 2)) := by
  have tree := deriveList (.variable (innerContext source target) 1)
    (.cons (innerContextFormed source target) .nil)
  change Derivation (signature C) (.term (innerContext source target) (.var 1)
    (((objectType source 0).rename Fin.succ).rename Fin.succ)) at tree
  simpa only [objectType_rename] using tree

def typeFormed {source : C} (target : C) (predicate : Subfunctor (yoneda.obj source)) :
    Derivation (signature C) (.type (objectContext source) (typeCode target predicate)) :=
  deriveList (.comprehensionFormation (objectContext source) (objectType target 1) (predicateCode predicate))
    (.cons (objectContextFormed source)
      (.cons (objectFormed target (objectContextFormed source))
        (.cons (predicateFormed predicate (innerContextFormed source target)
          (outerVariableFormed source target)) .nil)))

def predicateMeaning {source : C} (target : C) (predicate : Subfunctor (yoneda.obj source)) :
    Subfunctor (innerScope source target).1 :=
  predicate.preimage ((NativeModel C).toCwf.wk (baseType source target) ≫ objectName source)

def typeMeaning {source : C} (target : C) (predicate : Subfunctor (yoneda.obj source)) :
    NativeType (objectScope source).1 :=
  PresheafNativeStableRefinement.chosen (baseType source target) (predicateMeaning target predicate)

theorem predicate_read {source : C} (target : C) (predicate : Subfunctor (yoneda.obj source)) :
    (model C).evaluatePredicate (innerScope source target) (predicateCode predicate) =
      some (predicateMeaning target predicate) := by
  have read := (model C).evaluate_predicateAtom (innerScope source target) ⟨source, predicate⟩
    (singletonArgument (.var 1)) ((NativeModel C).toCwf.wk (baseType source target)) (by
      intro position
      cases position using Fin.cases with
      | zero => rfl
      | succ impossible => exact Fin.elim0 impossible)
  change (model C).evaluatePredicate (innerScope source target) (predicateCode predicate) =
    some ((predicate.preimage (objectName source)).preimage
      ((NativeModel C).toCwf.wk (baseType source target))) at read
  rw [← Subfunctor.preimage_comp] at read
  exact read

theorem type_read {source : C} (target : C) (predicate : Subfunctor (yoneda.obj source)) :
    (model C).evaluateType (objectScope source) (typeCode target predicate) =
      some (typeMeaning target predicate) :=
  (model C).evaluate_comprehension (objectScope source) (objectType target 1)
    (predicateCode predicate) (baseType source target) (predicateMeaning target predicate)
    (object_in_scope_read source target) (predicate_read target predicate)

/-- Complete inhabitants are compared with the independently formed
subtype. Only the membership proof is proposition-valued. -/
def fibreEquiv {source : C} (target : C) (predicate : Subfunctor (yoneda.obj source))
    (world : Cᵒᵖ) (argument : (objectScope source).1.obj world) :
    (typeMeaning target predicate).decoded.obj ⟨world, argument⟩ ≃
      {_value : world.unop ⟶ target | (objectName source).app world argument ∈ predicate.obj world} :=
  ((PresheafNativeStableRefinement.decodeIso (baseType source target)
    (predicateMeaning target predicate)).app ⟨world, argument⟩).toEquiv

def suppliedInhabitant {source : C} (target : C) (predicate : Subfunctor (yoneda.obj source))
    (world : Cᵒᵖ) (argument : (objectScope source).1.obj world) (value : world.unop ⟶ target)
    (accepted : (objectName source).app world argument ∈ predicate.obj world) :
    (typeMeaning target predicate).decoded.obj ⟨world, argument⟩ :=
  (fibreEquiv target predicate world argument).symm ⟨value, accepted⟩

theorem suppliedInhabitant_complete_readout {source : C} (target : C)
    (predicate : Subfunctor (yoneda.obj source)) (world : Cᵒᵖ)
    (argument : (objectScope source).1.obj world) (value : world.unop ⟶ target)
    (accepted : (objectName source).app world argument ∈ predicate.obj world) :
    (fibreEquiv target predicate world argument
      (suppliedInhabitant target predicate world argument value accepted)).val = value :=
  congrArg Subtype.val ((fibreEquiv target predicate world argument).apply_symm_apply ⟨value, accepted⟩)

theorem failed_argument_has_no_inhabitant {source : C} (target : C)
    (predicate : Subfunctor (yoneda.obj source)) (world : Cᵒᵖ)
    (argument : (objectScope source).1.obj world)
    (failed : (objectName source).app world argument ∉ predicate.obj world) :
    IsEmpty ((typeMeaning target predicate).decoded.obj ⟨world, argument⟩) :=
  ⟨fun value => failed (fibreEquiv target predicate world argument value).property⟩

theorem restriction_retains_inhabitant {source : C} (target : C)
    (predicate : Subfunctor (yoneda.obj source)) {world future : Cᵒᵖ}
    (before : world ⟶ future) (argument : (objectScope source).1.obj world)
    (value : (typeMeaning target predicate).decoded.obj ⟨world, argument⟩) :
    (fibreEquiv target predicate future ((objectScope source).1.map before argument)
      ((typeMeaning target predicate).decoded.map ⟨before, rfl⟩ value)).val =
        before.unop ≫ (fibreEquiv target predicate world argument value).val := by
  have read := (PresheafNativeStableRefinement.decodeIso (baseType source target)
    (predicateMeaning target predicate)).hom.naturality_apply
      (CategoryOfElements.homMk (F := (objectScope source).1) ⟨world, argument⟩
        ⟨future, (objectScope source).1.map before argument⟩ before rfl) value
  exact congrArg Subtype.val read

theorem original_substitution {source target valueObject : C} (before : source ⟶ target)
    (predicate : Subfunctor (yoneda.obj target)) :
    (model C).evaluateType (objectScope source)
      ((typeCode valueObject predicate).substitute (originalArrow before).substitution) =
        some ((typeMeaning valueObject predicate).reindex (originalPresheafArrow before)) := by
  have read := complete_type_substitution (originalArrow before) (typeCode valueObject predicate)
    (typeMeaning valueObject predicate) (type_read valueObject predicate)
  rw [readArrow_original] at read
  exact read

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableDeclarations.GuardedObject
