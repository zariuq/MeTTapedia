import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationReplaySyntax
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationRunAnswers

/-!
# Checked finite instructions and original-code provenance on actual runs

A submission is decoded by the maintained finite replay checker and aligned
with the active row's literal source. The target typing and full-step
admission are derived afterwards. An invalid submission is not a refutation
of the underlying program. Run certificates retain every submitted code,
including original table ordinals, even if their native resource effects agree.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationReplay

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull
open AlgebraicSchema AlgebraicParallel NativeTypesOnTheStep.Computing
open ComputationProfile

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
  (presentation : SchemaPresentation S.R) (table : SchemaTable Head)
  (same : ∀ {arity : Nat} (left right : Tm Head arity), presentation.schema left right ↔ table.family left right)
  [DecidableRel S.R.headEq]

abbrev Code (n : Nat) := StructuralConversionCode.StepCode Head (SchemaTableConversionCode.Code Head) n

structure Submission (configuration : ComputationProfile.Configuration (S := S)) where
  code : Code (Head := Head) configuration.state.frame.arity
  event : ComputationSyntax.Event presentation configuration.state.frame.arity
  parsed : ComputationReplaySyntax.decodeEvent presentation table same code = some event
  source : event.source = configuration.code

def Submission.instruction {configuration : ComputationProfile.Configuration (S := S)}
    (submission : Submission presentation table same configuration) : Instruction presentation configuration :=
  ⟨submission.event, submission.source⟩

theorem Submission.decoded {configuration : ComputationProfile.Configuration (S := S)}
    (submission : Submission presentation table same configuration) :
    StructuralConversionCode.StepCode.decode S.R.headEq
      (ComputationReplaySyntax.decoder presentation table same).decode submission.code =
        some (configuration.code, submission.event.target) :=
  (ComputationReplaySyntax.decoded_iff presentation table same _).mpr
    ⟨submission.event, submission.parsed, submission.source, rfl⟩

def read? [DecidableEq Head] (configuration : ComputationProfile.Configuration (S := S))
    (code : Code (Head := Head) configuration.state.frame.arity) : Option (Submission presentation table same configuration) :=
  match parsed : ComputationReplaySyntax.decodeEvent presentation table same code with
  | none => none
  | some event => if source : event.source = configuration.code then some ⟨code, event, parsed, source⟩ else none

theorem read_retains_code [DecidableEq Head] {configuration : ComputationProfile.Configuration (S := S)}
    {code : Code (Head := Head) configuration.state.frame.arity} {submission : Submission presentation table same configuration}
    (accepted : read? presentation table same configuration code = some submission) : submission.code = code := by
  unfold read? at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · obtain rfl := Option.some.inj accepted
      rfl
    · cases accepted

theorem read_complete [DecidableEq Head] {configuration : ComputationProfile.Configuration (S := S)}
    {code : Code (Head := Head) configuration.state.frame.arity} {target : Tm Head configuration.state.frame.arity}
    (decoded : StructuralConversionCode.StepCode.decode S.R.headEq
      (ComputationReplaySyntax.decoder presentation table same).decode code = some (configuration.code, target)) :
    ∃ submission, read? presentation table same configuration code = some submission ∧ submission.event.target = target := by
  obtain ⟨event, parsed, source, endpoint⟩ :=
    (ComputationReplaySyntax.decoded_iff presentation table same code).mp decoded
  refine ⟨⟨code, event, parsed, source⟩, ?_, endpoint⟩
  unfold read?
  split
  · rename_i rejected
    rw [rejected] at parsed
    cases parsed
  · rename_i event' decoded'
    have equal : event' = event := Option.some.inj (decoded'.symm.trans parsed)
    subst event'
    rw [dif_pos source]

theorem source_has_submission [DecidableEq Head] {configuration : ComputationProfile.Configuration (S := S)}
    {target : Tm Head configuration.state.frame.arity}
    (reduction : StepCore S.R.computation S.R.headEq configuration.code target) :
    ∃ code submission, read? presentation table same configuration code = some submission ∧
      submission.event.target = target := by
  obtain ⟨code, decoded⟩ := StructuralConversionCode.StepCode.decode_complete
    (ComputationReplaySyntax.decoder presentation table same) reduction
  obtain ⟨submission, accepted, endpoint⟩ := read_complete presentation table same decoded
  exact ⟨code, submission, accepted, endpoint⟩

variable (qualified : Qualified S)

inductive Profile : (configuration : ComputationProfile.Configuration (S := S)) →
    (step S.levels Nat).toStep.Run configuration.state → Type
  | nil (configuration : ComputationProfile.Configuration (S := S)) : Profile configuration (.nil configuration.state)
  | cons {configuration : ComputationProfile.Configuration (S := S)} (submission : Submission presentation table same configuration)
      (target : Nat) (fresh : target ∉ configuration.state.present)
      {rest : (step S.levels Nat).toStep.Run (submission.instruction.next qualified target fresh).state}
      (later : Profile (submission.instruction.next qualified target fresh) rest) :
      Profile configuration
        (.cons (submission.instruction.compile qualified target)
          ((submission.instruction.admitted_iff qualified target).mpr fresh) rest)

namespace Profile

variable {presentation table same qualified}

def forget : {configuration : ComputationProfile.Configuration (S := S)} →
    {run : (step S.levels Nat).toStep.Run configuration.state} →
    Profile presentation table same qualified configuration run → RunProfile qualified presentation configuration run
  | _, _, .nil configuration => .nil configuration
  | _, _, .cons submission target fresh later => .cons submission.instruction target fresh later.forget

def codes : {configuration : ComputationProfile.Configuration (S := S)} →
    {run : (step S.levels Nat).toStep.Run configuration.state} →
    Profile presentation table same qualified configuration run → List (Σ n : Nat, Code (Head := Head) n)
  | _, _, .nil _ => []
  | _, _, .cons submission _ _ later => ⟨_, submission.code⟩ :: later.codes

theorem every_code_retained {configuration : ComputationProfile.Configuration (S := S)}
    {run : (step S.levels Nat).toStep.Run configuration.state}
    (profile : Profile presentation table same qualified configuration run) : profile.codes.length = run.word.length := by
  induction profile with
  | nil => rfl
  | cons _ _ _ _ ih => exact congrArg (· + 1) ih

theorem reduction {configuration : ComputationProfile.Configuration (S := S)}
    {run : (step S.levels Nat).toStep.Run configuration.state}
    (profile : Profile presentation table same qualified configuration run) :
    ConversionCoherence.StepStar S.R configuration.code profile.forget.execution.term :=
  profile.forget.source_reduction

end Profile

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationReplay

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationReplay.source_has_submission
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationReplay.Profile.every_code_retained
