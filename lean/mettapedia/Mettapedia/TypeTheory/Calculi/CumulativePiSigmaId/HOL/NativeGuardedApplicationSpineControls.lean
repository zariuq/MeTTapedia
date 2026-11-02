import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeGuardedRealizabilityControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.GuardedApplicationSpines

/-!
# Retained application of an open two-argument method

The method returns its first argument in an arbitrary guarded source type.
Both argument occurrences survive in the source application. Its membership
proof is constructed from the existing open context and two abstractions.
Missing, extra and prematurely supplied arguments are separate controls.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeGuardedApplicationSpineControls

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated AnnotatedPredicateReading
open NativeNaturalVectorFamilies
open NativeGuardedRealizability.Controls
local infixr:60 " ⇒ " => HOL.Ty.arr

def secondContext := valueContext.snoc variableValue.predicate variableValue.typeRead family_formed

def firstVariable := GuardedRealizer.ofVariable roots secondContext
  (.vs .vz : HOL.Var [number, number, predicateType] number)

theorem second_family_formed : CIsType (Programs.Annotated.church profile)
    secondContext.source (.var 2) :=
  ⟨universeHead, by decide +kernel, .var 2⟩

def innerMethod := GuardedRealizer.abstraction (Programs.Annotated.levelModel profile)
  variableValue.predicate variableValue.typeRead family_formed second_family_formed firstVariable

theorem outer_family_formed : CIsType (Programs.Annotated.church profile)
    valueContext.source (.pi (.var 1) (.var 2)) :=
  CIsType.pi (Programs.Annotated.levelModel profile) family_formed second_family_formed

def method := GuardedRealizer.abstraction (Programs.Annotated.levelModel profile)
  predicate domain_read domain_formed outer_family_formed innerMethod

def openMethod := method.substitute weakening

def firstArguments : SuppliedArguments roots valueContext [(.var 0 : CTm Tower.Head 2)]
    (.pi (.var 1) (.pi (.var 2) (.var 3))) (number ⇒ number ⇒ number)
    (.pi (.var 1) (.var 2)) (number ⇒ number) :=
  .cons variableValue (.nil _ _)

def secondArguments : SuppliedArguments roots valueContext [(.var 0 : CTm Tower.Head 2)]
    (.pi (.var 1) (.var 2)) (number ⇒ number) (.var 1) number :=
  .cons variableValue (.nil _ _)

def completeArguments : SuppliedArguments roots valueContext [(.var 0 : CTm Tower.Head 2), .var 0]
    (.pi (.var 1) (.pi (.var 2) (.var 3))) (number ⇒ number ⇒ number) (.var 1) number :=
  .cons variableValue (.cons variableValue (.nil _ _))

def firstApplication := firstArguments.apply openMethod
def completed := secondArguments.apply firstApplication
def completedTogether := completeArguments.apply openMethod

theorem method_free : method.Free :=
  GuardedRealizer.abstraction_free _ _ _ _ _ _
    (GuardedRealizer.abstraction_free _ _ _ _ _ _ (GuardedRealizer.ofVariable_free roots secondContext _))

theorem open_method_free : openMethod.Free :=
  GuardedRealizer.substitute_free method weakening method_free weakening_free

theorem completed_free : completed.Free :=
  secondArguments.apply_free _ ⟨variable_free, True.intro⟩
    (firstArguments.apply_free _ ⟨variable_free, True.intro⟩ open_method_free)

theorem completed_together_free : completedTogether.Free :=
  completeArguments.apply_free _ ⟨variable_free, variable_free, True.intro⟩ open_method_free

theorem source_argument_occurrences_retained :
    CTm.appSpine (CTm.appSpine
      (.lam (.var 1) (.lam (.var 2) (.var 1)) : CTm Tower.Head 2) [.var 0]) [.var 0] =
      .app (.app (.lam (.var 1) (.lam (.var 2) (.var 1))) (.var 0)) (.var 0) := rfl

theorem complete_source_typed : CTyped (Programs.Annotated.church profile) valueContext.source
    (.app (.app (.lam (.var 1) (.lam (.var 2) (.var 1))) (.var 0)) (.var 0)) (.var 1) :=
  completed.typed

theorem residual_type_exact : instantiateProducts [(.var 0 : CTm Tower.Head 2)]
    (.pi (.var 1) (.pi (.var 2) (.var 3))) = some (.pi (.var 1) (.var 2)) :=
  firstArguments.instantiate

theorem complete_type_exact : instantiateProducts [(.var 0 : CTm Tower.Head 2), .var 0]
    (.pi (.var 1) (.pi (.var 2) (.var 3))) = some (.var 1) :=
  completeArguments.instantiate

theorem missing_argument_refused : instantiateProducts [(.var 0 : CTm Tower.Head 2)]
    (.pi (.var 1) (.pi (.var 2) (.var 3))) ≠ some (.var 1) := by decide +kernel

theorem extra_argument_refused : instantiateProducts [(.var 0 : CTm Tower.Head 2), .var 0, .var 0]
    (.pi (.var 1) (.pi (.var 2) (.var 3))) = none := rfl

theorem result_domain_not_a_function : instantiateProducts [(.var 0 : CTm Tower.Head 2)] (.var 1) = none := rfl

theorem completed_valid (chosen : Nat) :
    (model.denote (.app completed.predicate completed.term) (values chosen)).down :=
  completed.satisfies model
    (model.functionsRespectEqv_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _))
    (values chosen) (fun _ => trivial) (background_holds chosen)

theorem result_is_original_argument (chosen : Nat) :
    model.denote completed.term (values chosen) = ULift.up chosen := rfl

def secondVariable := GuardedRealizer.ofVariable roots secondContext
  (.vz : HOL.Var [number, number, predicateType] number)

def secondWeakening := GuardedSubstitution.weakening roots valueContext
  variableValue.predicate variableValue.typeRead family_formed

def twiceOpenMethod := openMethod.substitute secondWeakening

def orderedArguments : SuppliedArguments roots secondContext [(.var 1 : CTm Tower.Head 3), .var 0]
    (.pi (.var 2) (.pi (.var 3) (.var 4))) (number ⇒ number ⇒ number) (.var 2) number :=
  .cons firstVariable (.cons secondVariable (.nil _ _))

def reversedArguments : SuppliedArguments roots secondContext [(.var 0 : CTm Tower.Head 3), .var 1]
    (.pi (.var 2) (.pi (.var 3) (.var 4))) (number ⇒ number ⇒ number) (.var 2) number :=
  .cons secondVariable (.cons firstVariable (.nil _ _))

def orderedResult := orderedArguments.apply twiceOpenMethod
def reversedResult := reversedArguments.apply twiceOpenMethod

noncomputable def twoValues : model.Valuation [number, number, predicateType] :=
  model.extend (σ := number)
    (model.extend (σ := number)
      (model.extend (σ := predicateType) emptyValues (fun _ => ULift.up True)) (ULift.up 2)) (ULift.up 3)

theorem two_values_keep_order : model.denote orderedResult.term twoValues = ULift.up 2 ∧
    model.denote reversedResult.term twoValues = ULift.up 3 := ⟨rfl, rfl⟩

theorem reversing_arguments_changes_result :
    model.denote orderedResult.term twoValues ≠ model.denote reversedResult.term twoValues := by
  change (ULift.up (2 : Nat) : ULift.{1} Nat) ≠ ULift.up 3
  decide

#print axioms complete_source_typed
#print axioms completed_free
#print axioms completed_valid
#print axioms missing_argument_refused
#print axioms reversing_arguments_changes_result

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeGuardedApplicationSpineControls
