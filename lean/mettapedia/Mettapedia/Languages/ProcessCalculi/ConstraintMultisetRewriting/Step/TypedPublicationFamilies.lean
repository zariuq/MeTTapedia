import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationSolver
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.ComputableSettler

/-!
# Decided solver families feed source publication

The family is an explicit argument. Its actual settled certificate creates
a ready application; refutation stays refutation. A family that declines
retains the entire original problem as a pending update. No family order,
round budget or default admission profile is installed by this adapter.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Schema

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull

variable {Head : Type} {rules : Rules Head}
variable {L : Type} [UniverseLevel.LevelOrder L] {levels : LevelModel rules L}
  {O : Type} {state : State rules O} (schema : Schema levels O state.frame) (pick : Pick schema)

def resolveFamilyDecision : NativeTypesOnTheStep.Decision levels (schema.compile pick).information →
    Resolution schema pick
  | .settled target answer initial =>
      .ready target answer (NativeTypesOnTheStep.principal_of_initial levels initial)
  | .refuted absent => .refuted absent
  | .undecided => .suspended .declined (ContextualDependentUpdate.Update.pending levels _)

def resolveFamily (family : NativeTypesOnTheStep.Family levels) : Resolution schema pick :=
  schema.resolveFamilyDecision pick (family (schema.compile pick).information)

theorem declining_keeps_original :
    schema.resolveFamilyDecision pick .undecided =
      .suspended .declined (ContextualDependentUpdate.Update.pending levels (schema.compile pick).information) := rfl

theorem declining_is_not_refutation :
    ∀ absent, schema.resolveFamilyDecision pick .undecided ≠ Resolution.refuted absent := by
  intro absent same
  cases same

theorem declining_creates_no_application :
    (schema.resolveFamilyDecision pick .undecided).application? = none := rfl

theorem settled_ready_is_source_exact [DecidableEq O] {target : Context rules}
    (answer : target ⟶ schema.helpers.frame)
    (initial : UnificationWithLevels.InitialSolution (frames levels) (schema.compile pick).information answer) :
    let application : Application levels O state :=
      ⟨schema, pick, target, answer, .principal (NativeTypesOnTheStep.principal_of_initial levels initial)⟩
    (schema.resolveFamilyDecision pick (.settled target answer initial)).application? = some application ∧
      ((realizationStep levels O).Admits application ↔ schema.Admits pick) :=
  ⟨rfl, realization_admits_iff _⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Schema

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Schema.settled_ready_is_source_exact
