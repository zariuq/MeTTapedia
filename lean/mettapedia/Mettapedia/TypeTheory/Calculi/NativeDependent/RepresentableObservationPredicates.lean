import Mettapedia.TypeTheory.Calculi.NativeDependent.RepresentableGuardedFamilies

/-!
# Native declarations of predicates on generalized observations

A supplied presheaf value determines its actual Yoneda observation map.
Testing an independently supplied contextual predicate along that map
gives an original representable predicate, hence generated native predicate
and comprehension declarations. Their readouts retain the actual future
restriction of the observed value and the complete supplied inhabitant.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableDeclarations.Observed

open _root_.CategoryTheory Opposite
open ContextualModelTelescopes NativeLocalTypeFormers

universe u
variable {C : Type u} [Category.{u} C]
variable {observations : Cᵒᵖ ⥤ Type u}

noncomputable section

def observation {source : C} (supplied : observations.obj (op source)) :
    yoneda.obj source ⟶ observations := yonedaEquiv.symm supplied

def predicate (scope : Subfunctor observations) {source : C}
    (supplied : observations.obj (op source)) : Subfunctor (yoneda.obj source) :=
  scope.preimage (observation supplied)

theorem complete_generalized_readout (scope : Subfunctor observations) {source world : C}
    (supplied : observations.obj (op source)) (argument : world ⟶ source) :
    argument ∈ (predicate scope supplied).obj (op world) ↔
      observations.map argument.op supplied ∈ scope.obj (op world) := Iff.rfl

theorem current_readout (scope : Subfunctor observations) {source : C}
    (supplied : observations.obj (op source)) :
    (𝟙 source) ∈ (predicate scope supplied).obj (op source) ↔
      supplied ∈ scope.obj (op source) := by
  rw [complete_generalized_readout]
  rw [op_id, observations.map_id]
  rfl

theorem observation_substitution {source future : C} (before : future ⟶ source)
    (supplied : observations.obj (op source)) :
    yoneda.map before ≫ observation supplied = observation (observations.map before.op supplied) :=
  yonedaEquiv_symm_naturality_left before observations supplied

theorem predicate_substitution (scope : Subfunctor observations) {source future : C}
    (before : future ⟶ source) (supplied : observations.obj (op source)) :
    (predicate scope supplied).preimage (yoneda.map before) =
      predicate scope (observations.map before.op supplied) := by
  unfold predicate
  rw [← Subfunctor.preimage_comp, observation_substitution]

def formedPredicate (scope : Subfunctor observations) {source : C}
    (supplied : observations.obj (op source)) :
    Derivation (signature C) (.predicate (objectContext source)
      (predicateTerm (predicate scope supplied) (.var 0))) :=
  predicateFormed (predicate scope supplied) (objectContextFormed source) (variableFormed source)

def formedType (scope : Subfunctor observations) {source : C}
    (supplied : observations.obj (op source)) (valueObject : C) :
    Derivation (signature C) (.type (objectContext source)
      (GuardedObject.typeCode valueObject (predicate scope supplied))) :=
  GuardedObject.typeFormed valueObject (predicate scope supplied)

theorem actual_generated_predicate_substitution (scope : Subfunctor observations)
    {source future : C} (before : future ⟶ source)
    (supplied : observations.obj (op source)) :
    (model C).evaluatePredicate (objectScope future)
      ((predicateTerm (predicate scope supplied) (.var 0)).substitute
        (originalArrow before).substitution) =
      some ((predicate scope (observations.map before.op supplied)).preimage (objectName future)) := by
  have read := complete_original_predicate_substitution before (predicate scope supplied)
  rw [predicate_substitution] at read
  exact read

theorem actual_generated_type_substitution (scope : Subfunctor observations)
    {source future : C} (before : future ⟶ source)
    (supplied : observations.obj (op source)) (valueObject : C) :
    (model C).evaluateType (objectScope future)
      ((GuardedObject.typeCode valueObject (predicate scope supplied)).substitute
        (originalArrow before).substitution) =
      some ((GuardedObject.typeMeaning valueObject (predicate scope supplied)).reindex
        (originalPresheafArrow before)) :=
  GuardedObject.original_substitution before (predicate scope supplied)

/-- The value coordinate remains a complete generalized arrow. The scope
proof tests the independently supplied observed value in the same world. -/
def fibreEquiv (scope : Subfunctor observations) {source : C}
    (supplied : observations.obj (op source)) (valueObject : C)
    (world : C) (argument : world ⟶ source) :
    (GuardedObject.typeMeaning valueObject (predicate scope supplied)).decoded.obj
      ⟨op world, (objectNameInverse source).app (op world) argument⟩ ≃
        {_value : world ⟶ valueObject |
          observations.map argument.op supplied ∈ scope.obj (op world)} :=
  GuardedObject.fibreEquiv valueObject (predicate scope supplied) (op world)
    ((objectNameInverse source).app (op world) argument)

theorem inhabited_iff_actual_value_and_scope (scope : Subfunctor observations) {source : C}
    (supplied : observations.obj (op source)) (valueObject : C)
    (world : C) (argument : world ⟶ source) :
    Nonempty ((GuardedObject.typeMeaning valueObject (predicate scope supplied)).decoded.obj
      ⟨op world, (objectNameInverse source).app (op world) argument⟩) ↔
        ∃ _value : world ⟶ valueObject,
          observations.map argument.op supplied ∈ scope.obj (op world) := by
  constructor
  · rintro ⟨value⟩
    exact ⟨(fibreEquiv scope supplied valueObject world argument value).val,
      (fibreEquiv scope supplied valueObject world argument value).property⟩
  · rintro ⟨value, admitted⟩
    exact ⟨(fibreEquiv scope supplied valueObject world argument).symm ⟨value, admitted⟩⟩

theorem failed_current_scope_prevents_every_generated_entailment
    (scope : Subfunctor observations) {source : C}
    (supplied : observations.obj (op source)) (rejected : supplied ∉ scope.obj (op source)) :
    ¬Nonempty (Derivation (signature C) (.entails (objectContext source)
      (predicateTerm (predicate scope supplied) (.var 0)))) :=
  failed_test_prevents_generated_entailment (predicate scope supplied) (𝟙 source)
    (fun accepted => rejected ((current_readout scope supplied).mp accepted))

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableDeclarations.Observed
