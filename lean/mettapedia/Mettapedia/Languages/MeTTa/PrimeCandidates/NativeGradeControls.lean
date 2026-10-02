import Mettapedia.Languages.MeTTa.PrimeCandidates.NativeGradeAttachment

/-!
# Binding, sharing and zero-role controls for native grades

These controls execute authored atoms through the Need machine. They exercise
physical duplicate rows, a score using one lazy argument twice, source/body
closure while a recursive score remains live, and the distinction between a
zero priority and a semantic zero. Numeric advice is not an optimality
certificate, especially when a score itself branches over an unforced cell.
-/

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 5000000

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.NativeGradeControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines.BranchLocalNeed
open NeedReference
open Mettapedia.GSLT.Core
open BranchingTemporal
open InferenceControl (Controller WorkOccurrence)
open WeightedMuScheduler
open NativeEquationNeed NativeCandidateGrades NativeDerivationGrades

def integer (value : Int) : Atom := .grounded (.int value)
def call (head : String) (arguments : List Atom := []) : Atom :=
  .expression (.symbol head :: arguments)

def sharedProgram : Program :=
  [⟨"coin", [], integer 0⟩, ⟨"coin", [], integer 1⟩,
   ⟨"twice", ["x"], call "Pair" [.var "x", .var "x"]⟩,
   ⟨"twice", ["x"], call "Pair" [.var "x", .var "x"]⟩]

def argumentCell : CellId := ⟨1, [], 1, 0⟩

def sharedInput : NativeMachine where
  world :=
    { lineage := 1, path := [],
      heap :=
        { current := fun cell =>
            if cell = rootCell then some ⟨.application "twice" [argumentCell], .suspended⟩
            else if cell = argumentCell then some ⟨.expression (call "coin") [], .suspended⟩
            else none
          spine := [.allocate argumentCell (.expression (call "coin") []),
            .allocate rootCell (.application "twice" [argumentCell])] }
      receipts := ReceiptGraph.empty, nextCell := 2, nextEvaluator := 1 }
  control := .force rootCell []

def sharedRow : Row := ⟨2, call "Pair" [.var "x", .var "x"], [("x", argumentCell)]⟩

def sharedCapture : Captured :=
  captureOne sharedInput { sharedInput.world with nextEvaluator := 2 }
    rootCell ⟨.application "twice" [argumentCell], .suspended⟩ 1 [] 0 sharedRow

def sharedGrade : Atom := call "+" [.var "x", .var "x"]

def resultValues (outcomes : List Outcome) : List Atom :=
  outcomes.filterMap fun outcome => match outcome with
    | .value value => some value
    | _ => none

theorem duplicate_rows_retained :
    (captureApplication sharedProgram "twice" [argumentCell] sharedInput rootCell []).map
      (fun capture => capture.row.index) = [2, 3] := by decide +kernel

theorem actual_shared_binding :
    lookup sharedCapture.row.environment "x" = some argumentCell ∧
    lookup (sharedCapture.score sharedGrade).origin.row.environment "x" = some argumentCell := by
  decide +kernel

/-- Neither the argument nor the right-hand side was forced by capture. -/
theorem before_body_argument_suspended :
    (sharedCapture.world.heap.lookup argumentCell).map CellRecord.cache = some .suspended := by
  decide +kernel

theorem body_shares_choice :
    resultValues (answers (specification sharedProgram) 250 sharedCapture.body) =
      [call "Pair" [integer 0, integer 0], call "Pair" [integer 1, integer 1]] := by
  decide +kernel

/-- Two references in the score share the captured cell. Copying the argument
expression at each reference would incorrectly introduce scores 1 and 1. -/
theorem score_shares_choice :
    resultValues (answers (specification sharedProgram) 250
      (sharedCapture.score sharedGrade).machine) = [integer 0, integer 2] := by
  decide +kernel

theorem score_not_eager : priorityProposal (sharedCapture.score sharedGrade) = none := rfl

def loopProgram : Program :=
  [⟨"answer", [], integer 7⟩, ⟨"loop", [], call "loop"⟩]

def loopInput : NativeMachine :=
  { sharedInput with
    world :=
      { sharedInput.world with
        heap :=
          { current := fun cell =>
              if cell = rootCell then some ⟨.application "answer" [], .suspended⟩ else none
            spine := [.allocate rootCell (.application "answer" [])] }
        nextCell := 1 } }

def answerCapture : Captured :=
  captureOne loopInput { loopInput.world with nextEvaluator := 2 }
    rootCell ⟨.application "answer" [], .suspended⟩ 1 [] 0 ⟨0, integer 7, []⟩

def fifo : Controller NativeCandidateGrades.Task NativeCandidateGrades.Answer Unit :=
  .fixed Scheduler.breadthFirst

def recursiveAdviceRun :=
  InferenceControl.Snapshot.run (NativeCandidateGrades.system loopProgram) fifo 300
    (InferenceControl.Snapshot.initial fifo
      (NativeCandidateGrades.admit [answerCapture] (fun _ => call "loop")))

/-- The recursive scoring expression is still running after source closure.
The universal body-projection theorem does not require it to terminate. -/
theorem recursive_score_does_not_block_body :
    resultValues (recursiveAdviceRun.search.events.map (fun event => event.value.1)) =
      [integer 7] ∧
    (AdvisoryWork.bodies recursiveAdviceRun.search.frontier).isEmpty = true ∧
    recursiveAdviceRun.search.frontier.isEmpty = false := by decide +kernel

def zeroAdviceRun :=
  InferenceControl.Snapshot.run (NativeCandidateGrades.system loopProgram) fifo 100
    (InferenceControl.Snapshot.initial fifo
      (NativeCandidateGrades.admit [answerCapture] (fun _ => integer 0)))

theorem zero_priority_does_not_prune :
    resultValues (zeroAdviceRun.search.events.map (fun event => event.value.1)) = [integer 7] := by
  decide +kernel

def finishedZeroScore : Score :=
  let score := answerCapture.score (integer 0)
  match runFrontier (specification loopProgram) 100 [score.machine] with
  | machine :: _ => { score with machine := machine }
  | [] => score

theorem zero_is_a_priority_proposal : priorityProposal finishedZeroScore = some 0 := by decide +kernel

theorem semantic_zero_disables_captured_edge :
    edgeGrade (.scalar (0 : Nat)) loopInput answerCapture.body = 0 := by decide +kernel

theorem semantic_unit_keeps_captured_edge :
    edgeGrade (.scalar (1 : Nat)) loopInput answerCapture.body = 1 := by decide +kernel

theorem physical_row_is_actual_cause : newRow sharedInput sharedCapture.body = some sharedRow :=
  captured_choice _ _ _ _ _ _ _ _ rfl

def secondSharedRow : Row := { sharedRow with index := 3 }
def physicalWeights : WeighClause Nat Row := .observe fun row => row.index + 1

theorem duplicate_rows_have_distinct_weights :
    interpret physicalWeights [sharedRow] = 3 ∧
    interpret physicalWeights [secondSharedRow] = 4 ∧
    aggregate physicalWeights [[sharedRow], [secondSharedRow]] = 7 := by decide +kernel

theorem repeated_row_is_repeated_cause :
    interpret physicalWeights [sharedRow, sharedRow] = 9 := by decide +kernel

/-- Equality of returned values cannot justify quotienting physical causes. -/
theorem deduplicating_rows_changes_weight :
    aggregate physicalWeights [[sharedRow], [secondSharedRow]] ≠
      aggregate physicalWeights [[sharedRow]] := by decide +kernel

theorem score_resume_carries_entire_state :
    NativeCandidateGrades.execute loopProgram fifo (DemandExecution.atLeast 1) (10 + 90)
      (InferenceControl.Snapshot.initial fifo
        (NativeCandidateGrades.admit [answerCapture] (fun _ => call "loop"))) =
    NativeCandidateGrades.execute loopProgram fifo (DemandExecution.atLeast 1) 90
      (NativeCandidateGrades.execute loopProgram fifo (DemandExecution.atLeast 1) 10
        (InferenceControl.Snapshot.initial fifo
          (NativeCandidateGrades.admit [answerCapture] (fun _ => call "loop")))) :=
  resume_exact _ _ _ _ _ _

def automaticSharedRun :=
  InferenceControl.Snapshot.run
    (NativeGradeAttachment.nativeSystem sharedProgram
      (fun row => if row.index < 2 then integer 0 else sharedGrade)) fifo 1200
    (InferenceControl.Snapshot.initial fifo
      (NativeGradeAttachment.roots (call "twice" [call "coin"])))

def automaticSharedValues :=
  resultValues (automaticSharedRun.search.events.map (fun event => event.value.1))

/-- Scores are attached at recursive admissions, including the later forcing
of the shared argument. The two physical `twice` rows still contribute two
occurrences of each result. -/
theorem automatic_advice_preserves_duplicates :
    automaticSharedValues.length = 4 ∧
    automaticSharedValues.count (call "Pair" [integer 0, integer 0]) = 2 ∧
    automaticSharedValues.count (call "Pair" [integer 1, integer 1]) = 2 := by decide +kernel

def automaticRecursiveAdvice :=
  InferenceControl.Snapshot.run
    (NativeGradeAttachment.nativeSystem loopProgram (fun _ => call "loop")) fifo 300
    (InferenceControl.Snapshot.initial fifo (NativeGradeAttachment.roots (call "answer")))

theorem automatic_recursive_score_source_closed :
    resultValues (automaticRecursiveAdvice.search.events.map (fun event => event.value.1)) =
      [integer 7] ∧
    (AdvisoryWork.bodies automaticRecursiveAdvice.search.frontier).isEmpty = true ∧
    automaticRecursiveAdvice.search.frontier.isEmpty = false := by decide +kernel

/-- An advisory evaluation may choose a different branch of an initially
unforced cell. Its numeric result alone cannot certify the body's cost. -/
theorem nondeterministic_advice_is_not_a_cost_certificate :
    integer 0 ∈ resultValues (answers (specification sharedProgram) 250
      (sharedCapture.score sharedGrade).machine) ∧
    call "Pair" [integer 1, integer 1] ∈
      resultValues (answers (specification sharedProgram) 250 sharedCapture.body) := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PrimeCandidates.NativeGradeControls
