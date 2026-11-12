import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationExecution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.TransitionMaps

/-!
# Existing OSLF change of base for typed publications

Source transitions quantify over typed matching arguments. Native transitions
are events of the checked publication step. Their two-sided correspondence
supplies the hypotheses of the existing modal change-of-base theorems.

The state map retains the whole state, including raw labels. It is not an
agreement quotient on code, nor an assertion of fairness or divergence
reflection for a language evaluator.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Program

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull
open FragmentsOfTheStep.TransitionMaps
open Mettapedia.OSLF.Framework.DerivedModalities

variable {Head : Type} {rules : Rules Head}
variable {L : Type} [UniverseLevel.LevelOrder L] {levels : LevelModel rules L}
  {O : Type} [DecidableEq O] (program : Program levels O)
  (permission : {state : State rules O} → Candidate program state → Prop)

def nativeTransition (source target : State rules O) : Prop :=
  Nonempty ((program.toStep permission).effectCore.Event
    (program.toStep permission).eventAdmission source target)

/-- Equality of state representations does not identify the two transition
definitions: forward and backward laws use the source admission/result proof. -/
theorem publication_bisimulation :
    FunctionalBisimulation (program.Transition permission) (program.nativeTransition permission) id := by
  constructor
  · intro source target transition
    exact (program.transition_iff_event permission).mp transition
  · intro source target event
    exact ⟨target, (program.transition_iff_event permission).mpr event, rfl⟩

theorem possibility_preserved (predicate : State rules O → Prop) :
    derivedDiamond (span (program.nativeTransition permission)) predicate =
      derivedDiamond (span (program.Transition permission)) predicate :=
  pb_diamond (program.publication_bisimulation permission) predicate

theorem successor_necessity_preserved (predicate : State rules O → Prop) :
    derivedForwardBox (span (program.nativeTransition permission)) predicate =
      derivedForwardBox (span (program.Transition permission)) predicate :=
  pb_forwardBox (program.publication_bisimulation permission) predicate

theorem every_native_path_lifts {source target : State rules O}
    (path : Relation.ReflTransGen (program.nativeTransition permission) source target) :
    Relation.ReflTransGen (program.Transition permission) source target := by
  obtain ⟨endpoint, sourcePath, same⟩ :=
    Zag.path (program.publication_bisimulation permission).zag path source rfl
  exact same ▸ sourcePath

theorem every_source_path_realizes {source target : State rules O}
    (path : Relation.ReflTransGen (program.Transition permission) source target) :
    Relation.ReflTransGen (program.nativeTransition permission) source target :=
  Zig.path (stepX := program.Transition permission) (stepY := program.nativeTransition permission)
    (map := id) (program.publication_bisimulation permission).zig path

/-- Turning off permission disables the real native events as well as the
source transitions; the interpretation does not erase access control. -/
theorem disabled_has_no_native_transition (source target : State rules O) :
    ¬ program.nativeTransition (fun _ => False) source target := by
  rintro ⟨event⟩
  exact ((program.admits_iff (fun _ => False) event.firing).mp event.permitted).2

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Program

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Program.publication_bisimulation
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Program.possibility_preserved
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Program.successor_necessity_preserved
