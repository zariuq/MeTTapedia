import Mettapedia.TypeTheory.Calculi.NativeDependent.RepresentableObservationPredicates
import Mettapedia.OSLF.Framework.FindingMindNativeInteraction

/-!
# Generated dependent judgments for a future-sensitive rho scope

The existing occurrence's channel is observed through its actual Yoneda
map. Its original scope predicate becomes an independently formed native
predicate and comprehension type. The same generated type has an empty
initial fibre and an inhabited later fibre. The original context arrow's
syntactic substitution reads that actual native change.

Joint values keep the scope inhabitant and the separately constructed
actual event certificate. Distinct selected occurrences retain distinct
certificates even when their channel, guard and final result agree.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.Framework.FindingMindRepresentableScopeJudgments

open _root_.CategoryTheory Opposite
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open RepresentableDeclarations
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open FindingMindNativeInteraction

noncomputable section

abbrev initial : Stages := op 0
abbrev later : Stages := op 1

def suppliedName : names.obj (world 0) := HeaderInversionControls.channel

def scopePredicate : Subfunctor (yoneda.obj initial) :=
  Observed.predicate openScope suppliedName

def initialArgument : (objectScope initial).1.obj (world 0) :=
  (objectNameInverse initial).app (world 0) (𝟙 initial)

def futureArgument : (objectScope initial).1.obj (world 1) :=
  (objectNameInverse initial).app (world 1) (advance 0).unop

def formedPredicate : Derivation (signature Stages)
    (.predicate (objectContext initial) (predicateTerm scopePredicate (.var 0))) :=
  Observed.formedPredicate openScope suppliedName

def formedType : Derivation (signature Stages)
    (.type (objectContext initial) (GuardedObject.typeCode initial scopePredicate)) :=
  Observed.formedType openScope suppliedName initial

abbrev scopeFamily := GuardedObject.typeMeaning initial scopePredicate

theorem generated_type_reads_the_actual_scope_family :
    (model Stages).evaluateType (objectScope initial)
      (GuardedObject.typeCode initial scopePredicate) = some scopeFamily :=
  GuardedObject.type_read initial scopePredicate

theorem initial_argument_is_rejected :
    (objectName initial).app (world 0) initialArgument ∉ scopePredicate.obj (world 0) := by
  change ¬(suppliedName = HeaderInversionControls.channel ∧ 0 < 0)
  exact fun admitted => Nat.not_lt_zero 0 admitted.2

theorem the_actual_future_argument_is_accepted :
    (objectName initial).app (world 1) futureArgument ∈ scopePredicate.obj (world 1) :=
  ⟨rfl, Nat.zero_lt_one⟩

theorem initial_native_fibre_is_empty :
    IsEmpty (scopeFamily.decoded.obj ⟨world 0, initialArgument⟩) :=
  GuardedObject.failed_argument_has_no_inhabitant initial scopePredicate
    (world 0) initialArgument initial_argument_is_rejected

def futureScopeValue : scopeFamily.decoded.obj ⟨world 1, futureArgument⟩ :=
  GuardedObject.suppliedInhabitant initial scopePredicate (world 1)
    futureArgument (advance 0).unop the_actual_future_argument_is_accepted

theorem later_native_fibre_is_inhabited :
    Nonempty (scopeFamily.decoded.obj ⟨world 1, futureArgument⟩) := ⟨futureScopeValue⟩

theorem the_same_generated_family_changes_admission :
    IsEmpty (scopeFamily.decoded.obj ⟨world 0, initialArgument⟩) ∧
      Nonempty (scopeFamily.decoded.obj ⟨world 1, futureArgument⟩) :=
  ⟨initial_native_fibre_is_empty, later_native_fibre_is_inhabited⟩

theorem supplied_future_arrow_is_retained :
    (GuardedObject.fibreEquiv initial scopePredicate (world 1) futureArgument
      futureScopeValue).val = (advance 0).unop :=
  GuardedObject.suppliedInhabitant_complete_readout initial scopePredicate (world 1)
    futureArgument (advance 0).unop the_actual_future_argument_is_accepted

theorem actual_context_substitution_reads_the_native_family :
    (model Stages).evaluateType (objectScope later)
      ((GuardedObject.typeCode initial scopePredicate).substitute
        (originalArrow (advance 0).unop).substitution) =
      some (scopeFamily.reindex (originalPresheafArrow (advance 0).unop)) :=
  GuardedObject.original_substitution (advance 0).unop scopePredicate

theorem initial_failure_rules_out_every_generated_entailment :
    ¬Nonempty (Derivation (signature Stages)
      (.entails (objectContext initial) (predicateTerm scopePredicate (.var 0)))) :=
  failed_test_prevents_generated_entailment scopePredicate (𝟙 initial)
    initial_argument_is_rejected

def secondOpenedCertificate :
    (scopedEvents.certificates postcondition).obj ⟨world 1, source⟩ :=
  scopedEvents.introduce postcondition (world 1)
    ⟨⟨source, secondEvent⟩, ⟨rfl, Nat.zero_lt_one⟩⟩ ⟨⟨rfl⟩, ⟨0, Nat.zero_lt_succ 1⟩⟩

abbrev JointValue := scopeFamily.decoded.obj ⟨world 1, futureArgument⟩ ×
  (scopedEvents.certificates postcondition).obj ⟨world 1, source⟩

def firstJoint : JointValue := ⟨futureScopeValue, openedCertificate⟩
def secondJoint : JointValue := ⟨futureScopeValue, secondOpenedCertificate⟩

theorem joint_values_retain_the_same_actual_endpoint :
    (scopedEvents.resultReadout postcondition).app (world 1) ⟨source, firstJoint.2⟩ =
      (scopedEvents.resultReadout postcondition).app (world 1) ⟨source, secondJoint.2⟩ := rfl

theorem distinct_actual_occurrences_survive_the_scope_join : firstJoint ≠ secondJoint := by
  intro same
  have positions := congrArg (fun value : JointValue =>
    value.2.val.1.val.2.evidence.selected.outputIndex) same
  exact Nat.zero_ne_one positions

end

end Mettapedia.OSLF.Framework.FindingMindRepresentableScopeJudgments
