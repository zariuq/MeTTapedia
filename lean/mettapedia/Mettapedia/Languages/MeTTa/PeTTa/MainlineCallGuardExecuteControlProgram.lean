import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardControl

/-!
# Inspectable control program for hot PeTTa call guards

`executeGSLT` is the semantic authority for completed-call guard execution, but
the rewrite relation of an arbitrary `GSLT` is not inspectable data.  This
module supplies a finite control program whose instructions partition the
constructors and decisions of `ExecuteControl`.  Its interpreter is defined
independently of `executeStep?`, and the principal theorem proves exact
agreement for every control state.

The instruction inventory is intended to be consumed twice: by the source
interpreter below and by a structural lowering to target control.  Removing a
load-bearing instruction makes the corresponding source state unhandled, as
the negative canaries demonstrate.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteControlProgram

open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardControl
open Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT

set_option autoImplicit false

/-- A finite, inspectable partition of the hot executor decision tree. -/
inductive Instruction where
  | halted
  | requestOutsideFragment
  | requestForeignOwner
  | requestStaleRevision
  | requestWrongHead
  | requestWrongArity
  | requestCurrent
  | plansFinished
  | planHeadMismatch
  | planHeadMatches
  | argumentsFinished
  | argumentRaw
  | argumentUnchecked
  | argumentChecked
  | argumentShapeMismatch
  | resultUnchecked
  | resultChecked
deriving DecidableEq, Repr

/-- `none` means that an instruction does not apply.  `some none` means that
the instruction applies and establishes that the state is terminal. -/
def applyInstruction :
    Instruction -> ExecuteControl -> Option (Option ExecuteControl)
  | .halted, .halted _ => some none
  | .requestOutsideFragment, .request _ _ .outsideFragment =>
      some (some (.halted
        <| .mk (.fallback .outsideFragment) [.fallback .outsideFragment]))
  | .requestForeignOwner, .request current _ (.compiled family) =>
      if family.owner = current.owner then none
      else some (some (.halted
        <| .mk (.fallback .foreignOwner) [.fallback .foreignOwner]))
  | .requestStaleRevision, .request current _ (.compiled family) =>
      if family.owner = current.owner then
        if family.revision = current.snapshot.revision then none
        else some (some (.halted
          <| .mk (.fallback .staleRevision) [.fallback .staleRevision]))
      else none
  | .requestWrongHead, .request current call (.compiled family) =>
      if family.owner = current.owner then
        if family.revision = current.snapshot.revision then
          if family.head = call.function then none
          else some (some (.halted
            <| .mk (.fallback .wrongHead) [.fallback .wrongHead]))
        else none
      else none
  | .requestWrongArity, .request current call (.compiled family) =>
      if family.owner = current.owner then
        if family.revision = current.snapshot.revision then
          if family.head = call.function then
            if family.arity = call.sourceArguments.length then none
            else some (some (.halted
              <| .mk (.fallback .wrongArity) [.fallback .wrongArity]))
          else none
        else none
      else none
  | .requestCurrent, .request current call (.compiled family) =>
      if family.owner = current.owner then
        if family.revision = current.snapshot.revision then
          if family.head = call.function then
            if family.arity = call.sourceArguments.length then
              some (some (.plans current.snapshot call family.plans [] []))
            else none
          else none
        else none
      else none
  | .plansFinished, .plans _ _ [] accepted events =>
      some (some (.halted <| .mk (.executed accepted) events))
  | .planHeadMismatch,
      .plans snapshot call (plan :: remaining) accepted events =>
      if plan.declaration.function = call.function then none
      else
        let begun := events ++ [.beginPlan plan.declarationOccurrence]
        some (some (.plans snapshot call remaining accepted
          (begun ++ [.rejectOccurrence plan.declarationOccurrence])))
  | .planHeadMatches,
      .plans snapshot call (plan :: remaining) accepted events =>
      if plan.declaration.function = call.function then
        let begun := events ++ [.beginPlan plan.declarationOccurrence]
        some (some (.arguments snapshot call plan remaining 0
          plan.argumentModes call.sourceArguments call.evaluatedArguments
          accepted begun))
      else none
  | .argumentsFinished,
      .arguments snapshot call plan remaining _ [] [] [] accepted events =>
      some (some (.result snapshot call plan remaining accepted
        (events ++ [.evaluateCall plan.declarationOccurrence])))
  | .argumentRaw,
      .arguments snapshot call plan remaining index
        (.rawAtom :: modes) (source :: sources) (value :: values)
        accepted events =>
      let current := runArgMode snapshot index .rawAtom source value
      if current.accepted then
        some (some (.arguments snapshot call plan remaining (index + 1)
          modes sources values accepted (events ++ current.events)))
      else
        some (some (.plans snapshot call remaining accepted
          (events ++ current.events ++
            [.rejectOccurrence plan.declarationOccurrence])))
  | .argumentUnchecked,
      .arguments snapshot call plan remaining index
        (.evalUnchecked :: modes) (source :: sources) (value :: values)
        accepted events =>
      let current := runArgMode snapshot index .evalUnchecked source value
      if current.accepted then
        some (some (.arguments snapshot call plan remaining (index + 1)
          modes sources values accepted (events ++ current.events)))
      else
        some (some (.plans snapshot call remaining accepted
          (events ++ current.events ++
            [.rejectOccurrence plan.declarationOccurrence])))
  | .argumentChecked,
      .arguments snapshot call plan remaining index
        (.evalSoftcutType expected :: modes)
        (source :: sources) (value :: values) accepted events =>
      let mode := ArgMode.evalSoftcutType expected
      let current := runArgMode snapshot index mode source value
      if current.accepted then
        some (some (.arguments snapshot call plan remaining (index + 1)
          modes sources values accepted (events ++ current.events)))
      else
        some (some (.plans snapshot call remaining accepted
          (events ++ current.events ++
            [.rejectOccurrence plan.declarationOccurrence])))
  | .argumentShapeMismatch,
      .arguments snapshot call plan remaining index modes sources values
        accepted events =>
      match modes, sources, values with
      | [], [], [] => none
      | _ :: _, _ :: _, _ :: _ => none
      | _, _, _ =>
          some (some (.plans snapshot call remaining accepted
            (events ++ [.argumentShapeMismatch index,
              .rejectOccurrence plan.declarationOccurrence])))
  | .resultUnchecked,
      .result snapshot call plan remaining accepted events =>
      match plan.resultMode with
      | .resultUnchecked =>
          let checked := runResultMode snapshot .resultUnchecked call.result
          some (some (.plans snapshot call remaining
            (accepted ++ [plan.declaration])
            (events ++ checked.events ++
              [.installOccurrence plan.declarationOccurrence])))
      | .resultSoftcutType _ => none
  | .resultChecked,
      .result snapshot call plan remaining accepted events =>
      match plan.resultMode with
      | .resultUnchecked => none
      | .resultSoftcutType expected =>
          let mode := ResultMode.resultSoftcutType expected
          let checked := runResultMode snapshot mode call.result
          if checked.accepted then
            some (some (.plans snapshot call remaining
              (accepted ++ [plan.declaration])
              (events ++ checked.events ++
                [.installOccurrence plan.declarationOccurrence])))
          else
            some (some (.plans snapshot call remaining accepted
              (events ++ checked.events ++
                [.rejectOccurrence plan.declarationOccurrence])))
  | _, _ => none

/-- Interpret the first applicable instruction. -/
def run : List Instruction -> ExecuteControl -> Option ExecuteControl
  | [], _ => none
  | instruction :: instructions, state =>
      match applyInstruction instruction state with
      | none => run instructions state
      | some result => result

/-- The complete, ordered hot-control inventory. -/
def program : List Instruction := [
  .halted,
  .requestOutsideFragment,
  .requestForeignOwner,
  .requestStaleRevision,
  .requestWrongHead,
  .requestWrongArity,
  .requestCurrent,
  .plansFinished,
  .planHeadMismatch,
  .planHeadMatches,
  .argumentsFinished,
  .argumentRaw,
  .argumentUnchecked,
  .argumentChecked,
  .argumentShapeMismatch,
  .resultUnchecked,
  .resultChecked]

theorem program_nodup : program.Nodup := by
  decide

/-- The inspectable decision program determines exactly the authentic hot
executor transition for every source state. -/
theorem run_program_exact (state : ExecuteControl) :
    run program state = executeStep? state := by
  cases state with
  | halted observation => rfl
  | request current call compilation =>
      cases compilation with
      | outsideFragment => rfl
      | compiled family =>
          by_cases ownerCurrent : family.owner = current.owner
          · by_cases revisionCurrent :
                family.revision = current.snapshot.revision
            · by_cases headMatches : family.head = call.function
              · by_cases arityMatches :
                    family.arity = call.sourceArguments.length
                · simp [run, program, applyInstruction, executeStep?,
                    ownerCurrent, revisionCurrent, headMatches, arityMatches]
                · simp [run, program, applyInstruction, executeStep?,
                    ownerCurrent, revisionCurrent, headMatches, arityMatches]
              · simp [run, program, applyInstruction, executeStep?,
                  ownerCurrent, revisionCurrent, headMatches]
            · simp [run, program, applyInstruction, executeStep?,
                ownerCurrent, revisionCurrent]
          · simp [run, program, applyInstruction, executeStep?, ownerCurrent]
  | plans snapshot call remaining accepted events =>
      cases remaining with
      | nil => rfl
      | cons plan remaining =>
          by_cases headMatches : plan.declaration.function = call.function
          · simp [run, program, applyInstruction, executeStep?, headMatches]
          · simp [run, program, applyInstruction, executeStep?, headMatches]
  | arguments snapshot call plan remaining index modes sources values
      accepted events =>
      cases modes <;> cases sources <;> cases values <;>
        simp [run, program, applyInstruction, executeStep?]
      case cons.cons.cons mode modes source sources value values =>
        cases mode with
        | rawAtom =>
            by_cases modeAccepted :
                (runArgMode snapshot index .rawAtom source value).accepted = true
            · simp [modeAccepted]
            · simp [modeAccepted]
        | evalUnchecked =>
            by_cases modeAccepted :
                (runArgMode snapshot index .evalUnchecked source value).accepted = true
            · simp [modeAccepted]
            · simp [modeAccepted]
        | evalSoftcutType expected =>
            by_cases modeAccepted :
                (runArgMode snapshot index (.evalSoftcutType expected)
                  source value).accepted = true
            · simp [modeAccepted]
            · simp [modeAccepted]
  | result snapshot call plan remaining accepted events =>
      rcases plan with ⟨occurrence, argumentModes, resultMode, declaration⟩
      cases resultMode with
      | resultUnchecked =>
          simp [run, program, applyInstruction, executeStep?, runResultMode]
      | resultSoftcutType expected =>
          by_cases resultAccepted :
              (runResultMode snapshot (.resultSoftcutType expected)
                call.result).accepted = true
          · simp [run, program, applyInstruction, executeStep?, resultAccepted]
          · simp [run, program, applyInstruction, executeStep?, resultAccepted]

/-- The program can be used directly as a GSLT rewrite relation without
changing the operational theory. -/
def programGSLT : Mettapedia.GSLT.GSLT where
  Term := ExecuteControl
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target => run program source = some target
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

theorem programGSLT_step_iff_executeGSLT_step
    (source target : ExecuteControl) :
    programGSLT.Step source target ↔ executeGSLT.Step source target := by
  change run program source = some target ↔
    executeStep? source = some target
  rw [run_program_exact]

namespace Canary

open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan.Canary

def checkedPlan : GuardPlan :=
  { declarationOccurrence := exactTypeDeclaration.occurrence
    argumentModes := [.evalSoftcutType numberType]
    resultMode := .resultSoftcutType numberType
    declaration := exactTypeDeclaration }

def checkedArgumentState : ExecuteControl :=
  .arguments exactTypeSnapshot exactTypeCall checkedPlan [] 0
    checkedPlan.argumentModes exactTypeCall.sourceArguments
    exactTypeCall.evaluatedArguments [] []

theorem checked_argument_is_handled :
    (run program checkedArgumentState).isSome = true := by
  decide

theorem removing_checked_instruction_strands_checked_argument :
    run (program.filter (. != .argumentChecked)) checkedArgumentState = none := by
  decide

def currentRequestState : ExecuteControl :=
  .request (owned exactTypeSnapshot) exactTypeCall
    (.compiled <| .mk owner exactTypeSnapshot.revision "n" 1 [checkedPlan])

theorem removing_current_request_strands_valid_family :
    run (program.filter (. != .requestCurrent)) currentRequestState = none := by
  decide

theorem halted_is_normal_for_program
    (observation : ControlObservation) :
    run program (.halted observation) = none := by
  rfl

end Canary

#print axioms run_program_exact
#print axioms programGSLT_step_iff_executeGSLT_step
#print axioms Canary.checked_argument_is_handled
#print axioms Canary.removing_checked_instruction_strands_checked_argument
#print axioms Canary.removing_current_request_strands_valid_family
#print axioms Canary.halted_is_normal_for_program

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardExecuteControlProgram
