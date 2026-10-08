import Mettapedia.TypeTheory.Calculi.NativeDependent.RepresentableDeclarationInterpretation

/-!
# Conservativity of represented primitive arrows and predicates

Every generated dependent judgment over the constructed declarations has
an interpretation in the actual native presheaf model. Reading an arrow at
its generic argument recovers the complete original arrow. Reading a
predicate at all generalized arguments recovers the complete original
subfunctor. Generated equality therefore cannot collapse either carrier.

These results include all generated logical and dependent rules; they do
not assert that arbitrary semantic equality is derivable or that the
primitive arrow names already form a functor from the original category.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableDeclarations

open _root_.CategoryTheory Opposite
open ContextualModelTelescopes
open NativeLocalTypeFormers

universe u
variable {C : Type u} [Category.{u} C]

noncomputable section

/-- Complete judgment soundness is instantiated only after local header
realization and the actual native dependent laws have been earned. -/
theorem generated_sound {judgment : Judgment (symbols C)}
    (derivation : Derivation (signature C) judgment) : Interprets (model C) judgment :=
  derivation.sound (model C) (realization C)
    (NativeLocalTypeOperations.products_substitution C)
    (NativeLocalTypeOperations.products_beta C) (NativeLocalPiEta.products_eta C)

theorem generated_arrow_equality_reflects {source target : C} (first second : source ⟶ target)
    (equation : Derivation (signature C) (.termEq (objectContext source)
      (arrowTerm first (.var 0)) (arrowTerm second (.var 0)) (objectType target 1))) : first = second := by
  obtain ⟨value, firstRead, secondRead⟩ := (generated_sound equation).termEqAt
    (objectScope source) (arrowMeaning ⟨source, target, first⟩)
    (object_context_read source) (object_in_scope_read source target)
  have values := Option.some.inj ((arrow_read first).symm.trans
    (firstRead.trans (secondRead.symm.trans (arrow_read second))))
  have sections : arrowValue ⟨source, target, first⟩ = arrowValue ⟨source, target, second⟩ :=
    eq_of_heq (Sigma.mk.inj values).2
  have reading := congrArg (fun supplied : (arrowMeaning ⟨source, target, first⟩).decoded.sections =>
    supplied.val ⟨op source, (objectNameInverse source).app (op source) (𝟙 source)⟩) sections
  change (𝟙 source) ≫ first = (𝟙 source) ≫ second at reading
  simpa only [Category.id_comp] using reading

theorem generated_arrow_equality_iff {source target : C} (first second : source ⟶ target) :
    Nonempty (Derivation (signature C) (.termEq (objectContext source)
      (arrowTerm first (.var 0)) (arrowTerm second (.var 0)) (objectType target 1))) ↔ first = second := by
  constructor
  · rintro ⟨equation⟩
    exact generated_arrow_equality_reflects first second equation
  · rintro rfl
    exact ⟨deriveList (.termReflexivity (objectContext source)
      (arrowTerm first (.var 0)) (objectType target 1))
      (.cons (arrowFormed first (objectContextFormed source) (variableFormed source)) .nil)⟩

theorem generated_predicate_equality_reflects {object : C}
    (first second : Subfunctor (yoneda.obj object))
    (equation : Derivation (signature C) (.predicateEq (objectContext object)
      (predicateTerm first (.var 0)) (predicateTerm second (.var 0)))) : first = second := by
  have secondRead := (generated_sound equation).predicateEqAt (objectScope object)
    (first.preimage (objectName object)) (object_context_read object) (predicate_read first)
  have predicates := Option.some.inj ((predicate_read second).symm.trans secondRead)
  apply Subfunctor.ext
  funext world
  ext argument
  rw [← predicate_value_readout first argument, ← predicate_value_readout second argument, predicates]

theorem generated_predicate_equality_iff {object : C}
    (first second : Subfunctor (yoneda.obj object)) :
    Nonempty (Derivation (signature C) (.predicateEq (objectContext object)
      (predicateTerm first (.var 0)) (predicateTerm second (.var 0)))) ↔ first = second := by
  constructor
  · rintro ⟨equation⟩
    exact generated_predicate_equality_reflects first second equation
  · rintro rfl
    exact ⟨deriveList (.predicateReflexivity (objectContext object)
      (predicateTerm first (.var 0)))
      (.cons (predicateFormed first (objectContextFormed object) (variableFormed object)) .nil)⟩

theorem generated_truth_reflects {object : C} (predicate : Subfunctor (yoneda.obj object))
    (entailment : Derivation (signature C) (.entails (objectContext object)
      (predicateTerm predicate (.var 0)))) : predicate = ⊤ := by
  have read := (generated_sound entailment).entailsAt (objectScope object) (object_context_read object)
  have equality := Option.some.inj ((predicate_read predicate).symm.trans read)
  apply Subfunctor.ext
  funext world
  ext argument
  rw [← predicate_value_readout predicate argument, equality]
  exact iff_of_true (Set.mem_univ _) (Set.mem_univ _)

/-- A failed generalized test rules out every generated entailment tree,
including trees that pass through dependent functions or refinements. -/
theorem failed_test_prevents_generated_entailment {object world : C}
    (predicate : Subfunctor (yoneda.obj object)) (argument : world ⟶ object)
    (failed : argument ∉ predicate.obj (op world)) :
    ¬Nonempty (Derivation (signature C) (.entails (objectContext object)
      (predicateTerm predicate (.var 0)))) := by
  rintro ⟨entailment⟩
  have equality := generated_truth_reflects predicate entailment
  exact failed (equality ▸ Set.mem_univ argument)

end

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.RepresentableDeclarations
