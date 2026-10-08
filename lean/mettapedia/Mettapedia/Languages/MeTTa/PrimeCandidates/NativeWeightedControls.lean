import Mettapedia.Languages.MeTTa.PrimeCandidates.NativeWeightedHandler
import Mettapedia.Languages.MeTTa.PrimeCandidates.NativeGradeControls
import Mettapedia.GSLT.Scope.ReadoutDescent
import Mathlib.Algebra.FreeMonoid.Basic
import Mettapedia.Algebra.RationalComplexAmplitude
import Mettapedia.Algebra.FiniteCoordinateBuffer
import Mettapedia.GSLT.Dynamics.WeightedResumptionControls

/-!
# Native weighted occurrence and sharing controls

These authored programs use the actual Need successor list. Per-row
coefficients coexist with retained lazy cells, distinct physical choices and
complete residuals. Coefficient erasure is checked against ordinary execution;
zero coefficients are retained before any declared support observation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.NativeWeightedControls

open Mettapedia.Machines.BranchLocalNeed
open NeedReference
open Mettapedia.GSLT.Core.InferenceControl
open Mettapedia.GSLT.Core.WeightedMuScheduler
open Mettapedia.GSLT.Dynamics
open NativeEquationNeed NativeCandidateGrades NativeWeightedHandler
open NativeGradeControls
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

def firstCaptures :=
  WeightedBranchingResumption.contributions (source sharedProgram physicalWeights) 1
    (WorkOccurrence.root sharedInput)

theorem first_capture_coefficients : firstCaptures.map Prod.snd = [3, 4] := by decide +kernel

theorem first_capture_occurrence_paths :
    firstCaptures.map (fun leaf => (NeedWeightedResumption.retained leaf.1).trace) =
      [[0], [1]] := by decide +kernel

/-- Capturing either physical equation leaves the shared argument suspended. -/
theorem first_capture_preserves_lazy_argument :
    firstCaptures.map (fun leaf =>
      ((NeedWeightedResumption.retained leaf.1).state.world.heap.lookup argumentCell).map
        CellRecord.cache) = [some .suspended, some .suspended] := by decide +kernel

theorem first_capture_costs :
    firstCaptures.map (fun leaf =>
      (NeedWeightedResumption.retained leaf.1).state.work.transitions) = [1, 1] := by
  decide +kernel

def zeroCaptures :=
  WeightedBranchingResumption.contributions (source sharedProgram (.scalar (0 : Nat))) 1
    (WorkOccurrence.root sharedInput)

/-- A coefficient of zero does not erase its physical capture or owned world. -/
theorem zero_capture_retains_occurrences :
    zeroCaptures.length = 2 ∧ zeroCaptures.map Prod.snd = [0, 0] := by decide +kernel

section Histories

open Mettapedia.GSLT.Causality.OccurrenceMachineHistory

def firstSharedHistory : History (capturePathMachine sharedProgram sharedInput)
    sharedInput sharedCapture.body :=
  ofTrace _ [0] rfl

def secondSharedCapture : Captured :=
  captureOne sharedInput { sharedInput.world with nextEvaluator := 2 }
    rootCell ⟨.application "twice" [argumentCell], .suspended⟩ 1 [] 1 secondSharedRow

def secondSharedHistory : History (capturePathMachine sharedProgram sharedInput)
    sharedInput secondSharedCapture.body :=
  ofTrace _ [1] rfl

/-- Equal authored bodies still produce distinct row and successor occurrences. -/
theorem duplicate_bodies_keep_distinct_history_rows :
    FreeMonoid.toList ((authoredRowAccount sharedProgram sharedInput).of firstSharedHistory) =
        [sharedRow] ∧
    FreeMonoid.toList ((authoredRowAccount sharedProgram sharedInput).of secondSharedHistory) =
        [secondSharedRow] ∧
    indices (capturePathMachine sharedProgram sharedInput) firstSharedHistory = [0] ∧
    indices (capturePathMachine sharedProgram sharedInput) secondSharedHistory = [1] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Erasing a physical duplicate changes the native provenance observation. -/
theorem duplicate_history_row_erasure_rejected :
    ((authoredRowAccount sharedProgram sharedInput).of firstSharedHistory) ≠
      ((authoredRowAccount sharedProgram sharedInput).of secondSharedHistory) := by
  intro equal
  have rowIndices := congrArg (fun word => (FreeMonoid.toList word).map Row.index) equal
  have impossible : ([2] : List Nat) = [3] := rowIndices
  cases impossible

/-- A zero grade cannot justify dropping an authored event from its history. -/
theorem zero_history_keeps_authored_row :
    (NeedWeightedResumption.coefficientAccount (specification sharedProgram)
      (NativeDerivationGrades.edgeGrade (.scalar (0 : Nat))) sharedInput).of firstSharedHistory = 0 ∧
    FreeMonoid.toList ((authoredRowAccount sharedProgram sharedInput).of firstSharedHistory) =
      [sharedRow] := by
  exact ⟨rfl, rfl⟩

/-- Coverage retains the actual zero-weight producer in the executable
weighted frontier, rather than proving only that an existing leaf is valid. -/
theorem zero_history_is_retained :
    (.inr ⟨sharedCapture.body, [0]⟩, (0 : Nat)) ∈
      WeightedBranchingResumption.contributions (source sharedProgram (.scalar (0 : Nat)))
        1 (WorkOccurrence.root sharedInput) :=
  NeedWeightedResumption.history_pending_contribution (specification sharedProgram)
    (NativeDerivationGrades.edgeGrade (.scalar (0 : Nat))) sharedInput firstSharedHistory []

/-- A real one-step occurrence is absent from the zero-step cut. This is a
budget boundary, not a refutation of the occurrence or its authored row. -/
theorem zero_budget_does_not_cover_first_event :
    ¬ ∃ value : Nat,
      (.inr ⟨sharedCapture.body, [0]⟩, value) ∈
        WeightedBranchingResumption.contributions (source sharedProgram (.scalar (0 : Nat)))
          0 (WorkOccurrence.root sharedInput) := by
  rintro ⟨value, member⟩
  have equal := List.mem_singleton.mp member
  have impossible : ([0] : List Nat) = [] :=
    congrArg (fun leaf => (NeedWeightedResumption.retained leaf.1).trace) equal
  cases impossible

def administrativeInput : NativeMachine :=
  { sharedInput with control := .run (.output (.value (integer 7))) [] }

def administrativeOutput : NativeMachine :=
  finished administrativeInput administrativeInput.world (.returned (.value (integer 7)) [])
    0 0 0 0

def administrativeHistory : History (capturePathMachine sharedProgram administrativeInput)
    administrativeInput administrativeOutput :=
  ofTrace _ [0] rfl

/-- Authored-row provenance omits an administrative transition. It therefore
cannot replace the full occurrence history for replay or instruction cost. -/
theorem authored_rows_do_not_reconstruct_machine_history :
    FreeMonoid.toList
        ((authoredRowAccount sharedProgram administrativeInput).of administrativeHistory) = [] ∧
    indices (capturePathMachine sharedProgram administrativeInput) administrativeHistory = [0] ∧
    administrativeOutput.work.transitions = administrativeInput.work.transitions + 1 := by
  exact ⟨rfl, rfl, rfl⟩

/-- A plausible receipt body does not license a row absent from the program. -/
theorem forged_authored_row_rejected :
    ¬ ∃ after ∈ NeedReference.step (specification sharedProgram) sharedInput,
      NativeDerivationGrades.newRow sharedInput after =
        some { sharedRow with index := 99 } := by
  rintro ⟨after, member, chosen⟩
  obtain ⟨_, _, _, _, _, _, admitted⟩ :=
    NativeDerivationGrades.native_row_has_activation sharedProgram sharedInput after
      { sharedRow with index := 99 } member chosen
  generalize stateEq : Local.evaluate sharedRow.body sharedRow.environment = state at admitted
  cases admitted with
  | row located _ _ _ => simp [sharedProgram] at located

end Histories

def sharedRecordingController : Controller WorkState (Outcome × List Nat) Unit :=
  Controller.fixed Mettapedia.GSLT.Core.BranchingTemporal.Scheduler.breadthFirst

def sharedRecording (capacity : Nat) (fuel : Nat) :=
  Snapshot.run (occurrenceSystem sharedProgram)
    (Recording.controller sharedRecordingController (fun _ selected _ _ => selected) (some capacity))
    fuel (Recording.start
      (Snapshot.initial sharedRecordingController [WorkOccurrence.root sharedInput]) (some capacity))

/-- The recorder observes both physical captures of equal authored bodies,
while the argument cells in those captures remain suspended. -/
theorem recording_keeps_duplicate_rows_and_lazy_cells :
    (sharedRecording 3 3).memory.2.map
      (fun record => record.items.map WorkOccurrence.trace) = some [[], [0], [1]] ∧
    (sharedRecording 3 3).memory.2.map
      (fun record => record.items.filterMap
        (fun node => NativeDerivationGrades.newRow sharedInput node.state)) =
        some [sharedRow, secondSharedRow] ∧
    (sharedRecording 3 3).memory.2.map
      (fun record => record.items.tail.map
        (fun node => (node.state.world.heap.lookup argumentCell).map CellRecord.cache)) =
        some [some .suspended, some .suspended] := by
  exact ⟨rfl, rfl, rfl⟩

theorem recording_bound_does_not_prune_captures :
    (sharedRecording 1 3).search = (sharedRecording 3 3).search ∧
      (sharedRecording 1 3).memory.2.map Recording.Prefix.omitted = some 2 ∧
      (sharedRecording 1 3).memory.2.bind Recording.Prefix.complete? = none := by
  refine ⟨rfl, rfl, rfl⟩

theorem recording_resume_preserves_native_snapshot :
    Snapshot.run (occurrenceSystem sharedProgram)
      (Recording.controller sharedRecordingController (fun _ selected _ _ => selected) (some 3))
      2 (sharedRecording 3 1) = sharedRecording 3 3 := by
  exact (Recording.run_split _ _ _ _ 1 2 _).symm

theorem shared_body_agrees_with_unweighted_answers :
    resultValues
      (((WeightedBranchingResumption.contributions (source sharedProgram physicalWeights) 250
        (WorkOccurrence.root sharedCapture.body)).map
          (fun leaf => (NeedWeightedResumption.retained leaf.1).state)).filterMap haltedOutcome) =
      [call "Pair" [integer 0, integer 0], call "Pair" [integer 1, integer 1]] := by
  rw [native_answers_erasure]
  exact body_shares_choice

/-- Coefficient decoration cannot turn one shared choice into independent draws. -/
theorem no_mixed_shared_answer :
    call "Pair" [integer 0, integer 1] ∉ resultValues
      (((WeightedBranchingResumption.contributions (source sharedProgram physicalWeights) 250
        (WorkOccurrence.root sharedCapture.body)).map
          (fun leaf => (NeedWeightedResumption.retained leaf.1).state)).filterMap haltedOutcome) := by
  rw [shared_body_agrees_with_unweighted_answers]
  decide +kernel

def weightedValues :=
  (WeightedBranchingResumption.contributions (source sharedProgram physicalWeights) 250
    (WorkOccurrence.root sharedInput)).filterMap fun leaf =>
      match (NeedWeightedResumption.retained leaf.1).state.control with
      | .halted (.value value) => some (value, leaf.2)
      | _ => none

/-- Duplicate equations remain separate contributions; the selected argument
equation is charged once despite the two references to its shared cell. -/
theorem weighted_shared_values : weightedValues =
    [(call "Pair" [integer 0, integer 0], 3),
     (call "Pair" [integer 1, integer 1], 6),
     (call "Pair" [integer 0, integer 0], 4),
     (call "Pair" [integer 1, integer 1], 8)] := by decide +kernel

theorem weighted_shared_total : WeightedResumption.total weightedValues = 21 := by decide +kernel

/-- Coefficients on the two physical outer rows force the same captured lazy
argument subsequently used twice by the body. The coin equations are plain. -/
def sharedAnnotation (row : Row) : Option Mettapedia.Languages.MeTTa.OSLFCore.Atom :=
  if 2 ≤ row.index then some sharedGrade else none

def naturalCoefficient : Outcome → Option Nat
  | .value (.grounded (.int value)) => if 0 ≤ value then some value.toNat else none
  | _ => none

def pendingFirstCaptures :=
  WeightedBranchingResumption.contributions
    (pendingSource sharedProgram sharedAnnotation naturalCoefficient) 1
    (.inl (WorkOccurrence.root sharedInput))

/-- Admission retains each physical occurrence and starts its coefficient.
Neither an unsettled coefficient nor an RHS instruction has been executed. -/
theorem pending_capture_keeps_unforced_bodies :
    pendingFirstCaptures.map (fun leaf => match leaf.1 with
      | .inr (.inr (body, score)) =>
          some (body.trace, (scoreResult score).isNone,
            (body.state.world.heap.lookup argumentCell).map CellRecord.cache)
      | _ => none) =
      [some ([0], true, some .suspended), some ([1], true, some .suspended)] ∧
    pendingFirstCaptures.map Prod.snd = [1, 1] := by decide +kernel

def pendingValues {V Retained Work : Type} (leaves : WeightedResumption.Contributions
    ((WorkState ⊕ Retained) ⊕ Work) V) := completedValues leaves

def sharedPendingRun := WeightedBranchingResumption.contributions
  (pendingSource sharedProgram sharedAnnotation naturalCoefficient) 300
  (.inl (WorkOccurrence.root sharedInput))

/-- A score chooses the lazy value once and the resumed body reuses it.
Zero coefficients remain physical contributions before a support readout. -/
theorem pending_coefficient_and_body_share_choice : pendingValues sharedPendingRun =
    [(call "Pair" [integer 0, integer 0], 0),
     (call "Pair" [integer 1, integer 1], 2),
     (call "Pair" [integer 0, integer 0], 0),
     (call "Pair" [integer 1, integer 1], 2)] := by decide +kernel

def detachedCoefficientRun := WeightedBranchingResumption.contributions
  (WeightedBranchingResumption.pendingSource
    (NeedWeightedResumption.source (specification sharedProgram) (coefficientJob sharedAnnotation))
    (coefficientSource sharedProgram) (coefficientReadout naturalCoefficient) (fun body _ => body))
  300 (.inl (WorkOccurrence.root sharedInput))

/-- Returning to the pre-score world incorrectly permits the body to choose
its argument again. Agreement of the score's value alone would miss this. -/
theorem detached_coefficient_world_changes_contributions :
    (call "Pair" [integer 1, integer 1], 0) ∈ pendingValues detachedCoefficientRun ∧
    (call "Pair" [integer 1, integer 1], 0) ∉ pendingValues sharedPendingRun := by
  rw [pending_coefficient_and_body_share_choice]
  decide +kernel

def loopingPendingCoefficient := WeightedBranchingResumption.contributions
  (pendingSource loopProgram (fun _ => none) naturalCoefficient) 50
  (.inr (WorkOccurrence.root answerCapture.body, answerCapture.score (call "loop")))

/-- An unfinished semantic coefficient retains the body instead of emitting
the answer that detached scheduling advice is allowed to emit. -/
theorem looping_coefficient_does_not_complete_body :
    pendingValues loopingPendingCoefficient = [] ∧
    loopingPendingCoefficient.isEmpty = false := by decide +kernel

/-- The support profile tests the computed coefficient before the body.
Both duplicate outer rows remain, and the admitted coin choice is shared by
the two references in their continuations. -/
def guardedSharedPendingRun := WeightedBranchingResumption.contributions
  (pendingAdmittedSource sharedProgram sharedAnnotation naturalCoefficient
    (fun value => decide (value ≠ 0))) 300
  (.inl (WorkOccurrence.root sharedInput))

theorem guarded_coefficient_and_body_share_choice :
    pendingValues guardedSharedPendingRun =
      [(call "Pair" [integer 1, integer 1], 2),
       (call "Pair" [integer 1, integer 1], 2)] := by
  decide +kernel

/-- Attachment keeps a zero-weight body answer. Guard admission excludes
that body's execution rather than identifying it with an admitted duplicate. -/
theorem zero_attachment_is_not_guard_admission :
    (call "Pair" [integer 0, integer 0], 0) ∈ pendingValues sharedPendingRun ∧
    ∀ value, (call "Pair" [integer 0, integer 0], value) ∉
      pendingValues guardedSharedPendingRun := by
  rw [pending_coefficient_and_body_share_choice, guarded_coefficient_and_body_share_choice]
  constructor
  · simp
  · intro value
    simp [call, integer]

def guardedLoopingCoefficient := WeightedBranchingResumption.contributions
  (pendingAdmittedSource loopProgram (fun _ => none) naturalCoefficient
    (fun value => decide (value ≠ 0))) 50
  (.inr (WorkOccurrence.root answerCapture.body, answerCapture.score (call "loop")))

/-- A score that has not returned is retained as pending work. Neither zero
rejection nor a closed empty answer set can be inferred from its budget. -/
theorem guarded_looping_coefficient_remains_open :
    pendingValues guardedLoopingCoefficient = [] ∧
      guardedLoopingCoefficient.isEmpty = false := by
  decide +kernel

/-- Boolean guards use the OR/AND algebra, separately from Mathlib's XOR
ring on `Bool`. The interpretation recognizes actual native value returns. -/
def booleanCoefficient : Outcome → Option Mettapedia.GSLT.GradedSupport.OrBool
  | .value (.symbol "True") => some 1
  | .value (.symbol "False") => some 0
  | _ => none

def booleanGuardRun (expression : Mettapedia.Languages.MeTTa.OSLFCore.Atom) :=
  WeightedBranchingResumption.contributions
    (pendingAdmittedSource sharedProgram
      (fun row => if 2 ≤ row.index then some expression else none)
      booleanCoefficient (fun value => value.val)) 300
    (.inl (WorkOccurrence.root sharedInput))

/-- False prevents every captured outer body. True preserves all four
physical body outcomes with the Boolean unit, including duplicate answers. -/
theorem boolean_guard_controls :
    booleanGuardRun (.symbol "False") = [] ∧
    pendingValues (booleanGuardRun (.symbol "True")) =
      [(call "Pair" [integer 0, integer 0], 1),
       (call "Pair" [integer 1, integer 1], 1),
       (call "Pair" [integer 0, integer 0], 1),
       (call "Pair" [integer 1, integer 1], 1)] := by
  decide +kernel

/-- A value outside the Boolean interpretation is retained with its body
and actual score result. It is neither a false guard nor a body answer. -/
theorem uninterpreted_guard_does_not_execute_body :
    pendingValues (booleanGuardRun (.symbol "Maybe")) = [] ∧
      (booleanGuardRun (.symbol "Maybe")).length = 2 := by
  decide +kernel

/-! ## Graded identity and nested coefficient continuations -/

def identityProgram : Program :=
  [⟨"coin", [], integer 0⟩, ⟨"coin", [], integer 1⟩,
   ⟨"id", ["x"], .var "x"⟩,
   ⟨"constant", ["x"], integer 7⟩]

def identityAnnotation (expression : Mettapedia.Languages.MeTTa.OSLFCore.Atom)
    (row : Row) : Option Mettapedia.Languages.MeTTa.OSLFCore.Atom :=
  if row.index = 2 then some expression else none

def identityRun (annotation : Row → Option Mettapedia.Languages.MeTTa.OSLFCore.Atom)
    (term : Mettapedia.Languages.MeTTa.OSLFCore.Atom) (fuel : Nat := 300) :=
  WeightedBranchingResumption.contributions
    (nestedSource identityProgram annotation naturalCoefficient) fuel
    (.inl (WorkOccurrence.root (initial term)))

theorem graded_identity_unit :
    pendingValues (identityRun (identityAnnotation (integer 1))
      (call "id" [integer 7])) = [(integer 7, 1)] := by
  decide +kernel

/-- Each actual invocation contributes its literal factor, rather than
attaching a coefficient once to the printed function name. -/
theorem graded_identity_constant_composes :
    pendingValues (identityRun (identityAnnotation (integer 2))
      (call "id" [call "id" [integer 7]])) = [(integer 7, 4)] := by
  decide +kernel

/-- A parameter used only by the grade retains its captured binding even
when the function body ignores it. -/
theorem grade_only_binding_survives :
    pendingValues (identityRun
      (fun row => if row.index = 3 then some (.var "x") else none)
      (call "constant" [integer 9])) = [(integer 7, 9)] := by
  decide +kernel

def nestedIdentityTerm := call "id" [call "id" [integer 7]]

def onlyTwoAdmittedRun
    (annotation : Row → Option Mettapedia.Languages.MeTTa.OSLFCore.Atom) :=
  WeightedBranchingResumption.contributions
    (nestedAdmittedSource identityProgram annotation naturalCoefficient (fun value => value == 2))
    300 (.inl (WorkOccurrence.root (initial nestedIdentityTerm)))

/-- An authored predicate that rejects one still allows administrative work
and plain equations. Each authored two is checked before its caller resumes. -/
theorem authored_admission_tests_only_returned_grades :
    pendingValues (onlyTwoAdmittedRun (identityAnnotation (integer 2))) = [(integer 7, 4)] ∧
    pendingValues (onlyTwoAdmittedRun (fun _ => none)) = [(integer 7, 1)] ∧
    onlyTwoAdmittedRun (identityAnnotation (integer 1)) = [] := by
  decide +kernel

/-- Filtering every weighted edge rejects the first neutral instruction.
It is a different policy from a guard on an authored coefficient return. -/
theorem whole_edge_filter_is_not_authored_guard :
    WeightedBranchingResumption.contributions
      (WeightedBranchingResumption.admittingSource
        (nestedSource identityProgram (identityAnnotation (integer 2)) naturalCoefficient)
        (fun value => value == 2))
      300 (.inl (WorkOccurrence.root (initial nestedIdentityTerm))) = [] ∧
    pendingValues (onlyTwoAdmittedRun (identityAnnotation (integer 2))) ≠ [] := by
  rw [authored_admission_tests_only_returned_grades.1]
  decide +kernel

/-- The outer coefficient forces the inner annotated argument. Both
physical factors remain when the outer body reuses the completed cell. -/
theorem nested_grade_forcing_retains_inner_factor :
    pendingValues (identityRun (identityAnnotation (.var "x")) nestedIdentityTerm) =
      [(integer 7, 49)] := by
  decide +kernel

/-- A one-level adapter with ordinary scoring steps misses that inner
factor. Equality of the returned value alone would conceal the scope gap. -/
theorem ordinary_scoring_loses_nested_factor :
    pendingValues (WeightedBranchingResumption.contributions
      (pendingSource identityProgram (identityAnnotation (.var "x")) naturalCoefficient)
      300 (.inl (WorkOccurrence.root (initial nestedIdentityTerm)))) = [(integer 7, 7)] ∧
    pendingValues (identityRun (identityAnnotation (.var "x")) nestedIdentityTerm) ≠
      [(integer 7, 7)] := by
  rw [nested_grade_forcing_retains_inner_factor]
  decide +kernel

def gradedCoinAnnotation (row : Row) : Option Mettapedia.Languages.MeTTa.OSLFCore.Atom :=
  if row.index = 1 then some (integer 3) else identityAnnotation (.var "x") row

/-- Scoring may select a lazy argument once. Its selected equation's
factor and the outer factor both survive; the body does not select again. -/
theorem nested_grade_keeps_argument_factor :
    pendingValues (identityRun gradedCoinAnnotation (call "id" [call "coin"])) =
      [(integer 0, 0), (integer 1, 3)] := by
  decide +kernel

/-- Duplicate physical alternatives pass through a true graded identity
before its caller uses the returned cell twice. -/
def sharedIdentityProgram : Program :=
  [⟨"coin", [], integer 2⟩, ⟨"coin", [], integer 2⟩,
   ⟨"coin", [], integer 5⟩, ⟨"weigh-by-self", ["x"], .var "x"⟩,
   ⟨"paired", ["x"], call "Pair" [.var "x", .var "x"]⟩]

def sharedIdentityAnnotation (row : Row) :
    Option Mettapedia.Languages.MeTTa.OSLFCore.Atom :=
  if row.index < 2 then some (integer 3)
  else if row.index = 2 then some (integer 7)
  else if row.index = 3 then some (.var "x")
  else none

def sharedIdentityTerm := call "paired" [call "weigh-by-self" [call "coin"]]

def sharedIdentityRun (fuel : Nat) :=
  WeightedBranchingResumption.contributions
    (nestedSource sharedIdentityProgram sharedIdentityAnnotation naturalCoefficient) fuel
    (.inl (WorkOccurrence.root (initial sharedIdentityTerm)))

/-- The identity returns the same selected cell. Two uses of that cell
retain the three source choices, rather than forming nine independent pairs. -/
theorem shared_identity_values : pendingValues (sharedIdentityRun 400) =
    [(call "Pair" [integer 2, integer 2], 6),
     (call "Pair" [integer 2, integer 2], 6),
     (call "Pair" [integer 5, integer 5], 35)] := by
  decide +kernel

theorem shared_identity_factors_charged_once :
    (pendingValues (sharedIdentityRun 400)).map Prod.snd = [6, 6, 35] := by
  rw [shared_identity_values]
  rfl

theorem shared_identity_excludes_mixed_pairs :
    ∀ coefficient,
      (call "Pair" [integer 2, integer 5], coefficient) ∉
        pendingValues (sharedIdentityRun 400) ∧
      (call "Pair" [integer 5, integer 2], coefficient) ∉
        pendingValues (sharedIdentityRun 400) := by
  intro coefficient
  rw [shared_identity_values]
  simp [call, integer]

/-- Every split retains the exact whole machine, selected choice and pending
grade; the agreement is not limited to the cut used by a fixture. -/
theorem shared_identity_resume_exact (first second : Nat) :
    sharedIdentityRun (first + second) = WeightedResumption.sequence
      (sharedIdentityRun first)
      (fun leaf => match leaf with
        | .inl answer => [(Sum.inl answer, (1 : Nat))]
        | .inr pending => WeightedBranchingResumption.contributions
            (nestedSource sharedIdentityProgram sharedIdentityAnnotation naturalCoefficient)
            second pending) :=
  native_nested_resume_exact _ _ _ _ _ _

theorem nested_identity_resume_exact :
    identityRun (identityAnnotation (.var "x")) nestedIdentityTerm (20 + 280) =
      WeightedResumption.sequence
        (identityRun (identityAnnotation (.var "x")) nestedIdentityTerm 20)
        (fun leaf => match leaf with
          | .inl answer => [(Sum.inl answer, (1 : Nat))]
          | .inr pending => WeightedBranchingResumption.contributions
              (nestedSource identityProgram (identityAnnotation (.var "x")) naturalCoefficient)
              280 pending) :=
  native_nested_resume_exact _ _ _ _ _ _

/-- The same authored row can own distinct nested invocations. The inner
score and its suspended outer score are both present at this actual cut. -/
theorem nested_identity_checkpoint_has_two_captures :
    (identityRun (identityAnnotation (.var "x")) nestedIdentityTerm 14).map
      (fun leaf => match leaf.1 with
        | .inr (.inr (_, score, parents)) =>
            some (score.origin.row.index,
              parents.map (fun (parent : Score) => parent.origin.row.index))
        | _ => none) = [some (2, [2])] := by
  decide +kernel

theorem nested_identity_checkpoint_captures_valid :
    ∀ leaf ∈ identityRun (identityAnnotation (.var "x")) nestedIdentityTerm 14,
      Sum.elim (nestedResultValid identityProgram (identityAnnotation (.var "x")))
        (nestedValid identityProgram (identityAnnotation (.var "x"))) leaf.1 :=
  native_nested_valid _ _ _ _ _ True.intro

/-- A different return instruction cannot be substituted for the retained
parent, although both invocations use the same equation index. -/
theorem nested_identity_parent_replacement_refused :
    ∀ leaf ∈ identityRun (identityAnnotation (.var "x")) nestedIdentityTerm 14,
      match leaf.1 with
      | .inr (.inr (body, child, parent :: parents)) =>
          ¬ NestedCapturedCoefficient identityProgram (identityAnnotation (.var "x"))
            body child
            ({ parent with machine :=
              { parent.machine with control := .halted (.value (integer 999)) } } :: parents)
      | _ => False := by
  have live : (identityRun (identityAnnotation (.var "x")) nestedIdentityTerm 14).all
      (fun leaf => match leaf.1 with
        | .inr (.inr (_, child, _ :: _)) => !isHalted child.origin.body
        | _ => false) = true := by decide +kernel
  intro leaf member
  have checked := List.all_eq_true.mp live leaf member
  rcases leaf with ⟨state, coefficient⟩
  cases state with
  | inl answer => simp at checked
  | inr pending =>
      cases pending with
      | inl body => simp at checked
      | inr held =>
          rcases held with ⟨body, child, parents⟩
          cases parents with
          | nil => simp at checked
          | cons parent rest =>
              have running : isHalted child.origin.body = false := by simpa using checked
              apply nested_capture_wrong_parent_refused
              intro same
              have finished : isHalted child.origin.body = true := by
                unfold isHalted
                rw [same]
              simp [running] at finished

/-- Free words expose factor order without imposing commutativity. -/
local instance : DecidableEq (FreeMonoid String) :=
  inferInstanceAs (DecidableEq (List String))

/-- The tag interpretation is shared by every coefficient algebra below. -/
def demandOrderedCoefficient {V : Type} (inner outer : V) : Outcome → Option V
  | .value (.grounded (.int 2)) => some inner
  | .value (.grounded (.int 7)) => some outer
  | _ => none

def orderedCoefficient : Outcome → Option (FreeMonoid String) :=
  demandOrderedCoefficient (FreeMonoid.of "inner") (FreeMonoid.of "outer")

def orderedIdentityProgram : Program :=
  identityProgram ++ [⟨"outer", ["x"], .var "x"⟩]

/-- One native continuation construction admits literal or binding-local grades.
The body, lazy cells, parents and physical occurrences remain the same. -/
def orderedIdentityWithGrades {V : Type} [Monoid V] (inner outer : Atom)
    (interpretation : Outcome → Option V) :=
  WeightedBranchingResumption.contributions
    (nestedSource orderedIdentityProgram
      (fun row => if row.index = 2 then some inner
        else if row.index = 4 then some outer else none) interpretation)
    300 (.inl (WorkOccurrence.root (initial (call "outer" [call "id" [integer 7]]))))

def orderedIdentityRun (forceArgument : Bool) :=
  orderedIdentityWithGrades (integer 2) (if forceArgument then .var "x" else integer 7)
    orderedCoefficient

/-- Forcing the argument in the outer grade completes the inner factor
first. A literal outer grade completes first instead. The retained execution
order is observable for noncommutative coefficients. -/
theorem graded_identity_keeps_factor_completion_order :
    pendingValues (orderedIdentityRun true) =
      [(integer 7, FreeMonoid.of "inner" * FreeMonoid.of "outer")] ∧
    pendingValues (orderedIdentityRun false) =
      [(integer 7, FreeMonoid.of "outer" * FreeMonoid.of "inner")] := by
  decide +kernel

theorem grading_demand_order_is_not_silently_commutative :
    pendingValues (orderedIdentityRun true) ≠ pendingValues (orderedIdentityRun false) := by
  rw [graded_identity_keeps_factor_completion_order.1,
    graded_identity_keeps_factor_completion_order.2]
  decide +kernel

def nestedUnknownRun := WeightedBranchingResumption.contributions
  (nestedAdmittedSource orderedIdentityProgram
    (fun row => if row.index = 2 then some (.symbol "unknown-grade")
      else if row.index = 4 then some (.var "x") else none)
    naturalCoefficient (fun value => value != 0))
  300 (.inl (WorkOccurrence.root (initial (call "outer" [call "id" [integer 7]]))))

/-- An inner result outside the declared algebra retains the original body
and the suspended outer grade. It is neither an answer nor a failed guard. -/
theorem nested_unknown_grade_keeps_parent :
    pendingValues nestedUnknownRun = [] ∧
    nestedUnknownRun.map (fun leaf => match leaf.1 with
      | .inl (.inr (body, score, parents)) =>
          some (score.origin.row.index,
            parents.map (fun (parent : Score) => parent.origin.row.index),
            resultValues (scoreResult score).toList, isHalted body.state)
      | _ => none) = [some (2, [4], [.symbol "unknown-grade"], false)] := by
  decide +kernel

def nestedZeroRun (guarded : Bool) := WeightedBranchingResumption.contributions
  (nestedAdmittedSource orderedIdentityProgram
    (fun row => if row.index = 2 then some (integer 0)
      else if row.index = 4 then some (.var "x") else none)
    naturalCoefficient (fun value => !guarded || value != 0))
  300 (.inl (WorkOccurrence.root (initial (call "outer" [call "id" [integer 7]]))))

/-- Attaching an inner zero still yields a physical contribution. Declared
zero admission refuses that inner return before executing its caller. -/
theorem nested_zero_attachment_and_guard_differ :
    pendingValues (nestedZeroRun false) = [(integer 7, 0)] ∧
    nestedZeroRun true = [] := by
  decide +kernel

/-! ## Completed values, parked results and pending instructions -/

/-- A grade query has one unknown result, two physical True rows and a False
row. The actual equation capture, shared score world and native body are used. -/
def mixedGradeProgram : Program := identityProgram ++
  [⟨"verdict", [], .symbol "Maybe"⟩,
   ⟨"verdict", [], .symbol "True"⟩,
   ⟨"verdict", [], .symbol "True"⟩,
   ⟨"verdict", [], .symbol "False"⟩]

def mixedGradeRun (fuel : Nat := 300) :=
  WeightedBranchingResumption.contributions
    (nestedAdmittedSource mixedGradeProgram
      (identityAnnotation (call "verdict" [])) booleanCoefficient (fun value => value.val))
    fuel (.inl (WorkOccurrence.root (initial (call "id" [integer 7]))))

/-- A parked unknown is not a body answer and not runnable. It also cannot
close the two successful physical occurrences or certify a third is absent. -/
theorem mixed_grade_occurrences_and_status :
    completedValues (mixedGradeRun) = [(integer 7, 1), (integer 7, 1)] ∧
    (WeightedBranchingResumption.parkedGrades
      (WeightedBranchingResumption.nestedObligations (mixedGradeRun))).length = 1 ∧
    WeightedBranchingResumption.pendingInstructions
      (WeightedBranchingResumption.nestedObligations (mixedGradeRun)) = [] ∧
    nestedValueOutcome 2 (mixedGradeRun) = .established ∧
    nestedValueOutcome 3 (mixedGradeRun) = .incomplete := by
  decide +kernel

/-- The same empty value list has different completion meanings. Unknown
retains a parked stack; a declared false guard closes its only branch. -/
theorem unknown_is_not_closed_shortage :
    completedValues nestedUnknownRun = [] ∧
    WeightedBranchingResumption.pendingInstructions
      (WeightedBranchingResumption.nestedObligations nestedUnknownRun) = [] ∧
    nestedValueOutcome 1 nestedUnknownRun = .incomplete ∧
    completedValues (nestedZeroRun true) = [] ∧
    nestedValueOutcome 1 (nestedZeroRun true) = .saturated := by
  decide +kernel

/-- Satisfaction counts physical answers independently of their algebraic
support: a zero-weight answer still satisfies a one-occurrence request. -/
theorem zero_grade_value_satisfies_occurrence_demand :
    nestedValueOutcome 1 (nestedZeroRun false) = .established ∧
    nestedValueOutcome 2 (nestedZeroRun false) = .saturated := by
  decide +kernel

/-- A slice ending with live nested grade instructions is incomplete. Running
out of allowance neither emits the retained body nor proves shortage. -/
theorem nested_cut_is_incomplete :
    nestedValueOutcome 1
      (identityRun (identityAnnotation (.var "x")) nestedIdentityTerm 14) = .incomplete ∧
    nestedValueOutcome 1
      (identityRun (identityAnnotation (.var "x")) nestedIdentityTerm) = .established := by
  decide +kernel

/-- Once every executable branch has finished, another slice leaves the
complete mixed cut unchanged, including its parked result and work accounts. -/
theorem mixed_parked_cut_needs_no_polling :
    WeightedResumption.sequence (mixedGradeRun) (fun leaf => match leaf with
      | .inl answer => [(Sum.inl answer, 1)]
      | .inr pending => WeightedBranchingResumption.contributions
          (nestedAdmittedSource mixedGradeProgram
            (identityAnnotation (call "verdict" [])) booleanCoefficient (fun value => value.val))
          50 pending) = mixedGradeRun := by
  exact WeightedBranchingResumption.continue_without_pending
    (nestedAdmittedSource mixedGradeProgram
      (identityAnnotation (call "verdict" [])) booleanCoefficient (fun value => value.val))
    50 mixedGradeRun (by decide +kernel)

def identityPendingCut (fuel : Nat) : List NestedWork :=
  (identityRun (identityAnnotation (.var "x")) nestedIdentityTerm fuel).filterMap
    (fun leaf => match leaf.1 with | .inr pending => some pending | _ => none)

def identityCut14 : NestedWork := (identityPendingCut 14)[0]'(by decide +kernel)
def identityCut20 : NestedWork := (identityPendingCut 20)[0]'(by decide +kernel)

def retainedBodyView : NestedWork → WorkState :=
  WeightedBranchingResumption.pendingBody (Job := Score × List Score)

/-- The list of owned instruction accounts is a sufficient declared view.
It need not retain the heap, coefficient values or authored terms. -/
theorem owned_instruction_meter_factors_accounts :
    Mettapedia.GSLT.Core.NonFactorization.Factors
      nestedInstructionAccounts nestedInstructionCount :=
  ⟨List.sum, nested_instruction_accounts_sum⟩

set_option cbv.warning false in
/-- The body is suspended at both cuts while its nested grade advances. Its
complete retained machine agrees; the owned instruction totals differ. -/
theorem same_body_different_owned_instruction_count :
    retainedBodyView identityCut14 = retainedBodyView identityCut20 ∧
    nestedInstructionCount identityCut14 = 14 ∧
    nestedInstructionCount identityCut20 = 20 := by
  refine ⟨?_, ?_⟩
  · cbv
  · decide +kernel

/-- The shared readout boundary rejects a body-only meter. Forgetting the
active score and its parents loses information needed by this observation. -/
theorem owned_instruction_meter_not_factors_body_view :
    ¬ Mettapedia.GSLT.Core.NonFactorization.Factors retainedBodyView nestedInstructionCount := by
  apply Mettapedia.GSLT.Core.NonFactorization.NonTrivialFiber.not_factors
  refine ⟨identityCut14, identityCut20, same_body_different_owned_instruction_count.1, ?_⟩
  rw [same_body_different_owned_instruction_count.2.1,
    same_body_different_owned_instruction_count.2.2]
  decide +kernel

/-- The completed meter includes actual inner and outer scoring work, with
each child imported once. The full residual comparison covers split runs. -/
theorem nested_completed_instruction_meter :
    (identityRun (identityAnnotation (.var "x")) nestedIdentityTerm).map
      (fun leaf => Sum.elim nestedResultInstructionCount nestedInstructionCount leaf.1) = [62] := by
  decide +kernel

/-! ## Predicates evaluated by the same native weighted continuation -/

def predicateProgram (verdict : Mettapedia.Languages.MeTTa.OSLFCore.Atom) : Program :=
  identityProgram ++ [⟨"accept", ["w"], verdict⟩]

def predicateAnnotation (row : Row) : Option AuthoredClause :=
  if row.index = 2 then some ⟨integer 2, some (.symbol "accept")⟩
  else if row.index = 4 then some ⟨integer 3, none⟩
  else none

def predicateRun (verdict : Mettapedia.Languages.MeTTa.OSLFCore.Atom)
    (fuel : Nat := 300) :=
  WeightedBranchingResumption.contributions
    (authoredSource (predicateProgram verdict) predicateAnnotation naturalCoefficient)
    fuel (.inl (WorkOccurrence.root (initial (call "id" [integer 7]))))

/-- Admission executes an authored predicate; its own grade is included
before the accepted equation's coefficient. -/
theorem authored_predicate_contributes_its_grade :
    pendingValues (predicateRun (.symbol "True")) = [(integer 7, 6)] := by
  decide +kernel

def predicateOrderedCoefficient : Outcome → Option (FreeMonoid String)
  | .value (.grounded (.int 2)) => some (FreeMonoid.of "outer")
  | .value (.grounded (.int 3)) => some (FreeMonoid.of "predicate")
  | _ => none

def predicateOrderedRun := WeightedBranchingResumption.contributions
  (authoredSource (predicateProgram (.symbol "True")) predicateAnnotation
    predicateOrderedCoefficient) 300
  (.inl (WorkOccurrence.root (initial (call "id" [integer 7]))))

theorem authored_predicate_preserves_noncommutative_order :
    pendingValues predicateOrderedRun =
      [(integer 7, FreeMonoid.of "predicate" * FreeMonoid.of "outer")] := by
  decide +kernel

theorem authored_predicate_reversed_order_is_wrong :
    pendingValues predicateOrderedRun ≠
      [(integer 7, FreeMonoid.of "outer" * FreeMonoid.of "predicate")] := by
  rw [authored_predicate_preserves_noncommutative_order]
  decide +kernel

theorem authored_predicate_false_refuses_body :
    predicateRun (.symbol "False") = [] := by
  decide +kernel

/-- An unresolved verdict retains its completed coefficient and world. The
outer coefficient has not been appended and no body value has been emitted. -/
theorem authored_predicate_unknown_is_not_false :
    pendingValues (predicateRun (.symbol "Maybe")) = [] ∧
      (predicateRun (.symbol "Maybe")).map Prod.snd = [3] ∧
      (predicateRun (.symbol "Maybe")).length = 1 := by
  decide +kernel

def predicateSavedCoefficients {V : Type}
    (leaves : WeightedResumption.Contributions (AuthoredResult ⊕ AuthoredWork) V) :
    List (Option Outcome) :=
  leaves.filterMap fun leaf => match leaf.1 with
    | .inl (.inr (_, job, _)) =>
        match job.phase with
        | .predicate completed => some (scoreResult completed)
        | .coefficient => none
    | _ => none

theorem authored_predicate_unknown_keeps_completed_score :
    predicateSavedCoefficients (predicateRun (.symbol "Maybe")) =
      [some (.value (integer 2))] := by
  decide +kernel

def predicateSharedProgram : Program :=
  [⟨"coin", [], integer 2⟩, ⟨"coin", [], integer 2⟩,
   ⟨"coin", [], integer 5⟩,
   ⟨"pair", ["x"], call "Pair" [.var "x", .var "x"]⟩,
   ⟨"accept", ["w"], .symbol "True"⟩]

def predicateSharedAnnotation (row : Row) : Option AuthoredClause :=
  if row.index < 3 then some ⟨integer 5, none⟩
  else if row.index = 3 then some ⟨.var "x", some (.symbol "accept")⟩
  else if row.index = 4 then some ⟨integer 3, none⟩
  else none

def predicateSharedRun := WeightedBranchingResumption.contributions
  (authoredSource predicateSharedProgram predicateSharedAnnotation naturalCoefficient)
  350 (.inl (WorkOccurrence.root (initial (call "pair" [call "coin" []]))))

/-- Predicate execution retains the coefficient's shared choice. Equal coin
rows stay distinct; the body cannot draw an independent mixed pair. -/
theorem authored_predicate_preserves_shared_choice_and_duplicates :
    pendingValues predicateSharedRun =
      [(call "Pair" [integer 2, integer 2], 30),
       (call "Pair" [integer 2, integer 2], 30),
       (call "Pair" [integer 5, integer 5], 75)] := by
  decide +kernel

theorem authored_predicate_no_mixed_pair :
    ∀ coefficient, (call "Pair" [integer 2, integer 5], coefficient) ∉
      pendingValues predicateSharedRun := by
  intro coefficient
  rw [authored_predicate_preserves_shared_choice_and_duplicates]
  simp [call, integer]

def predicateMixedProgram : Program :=
  identityProgram ++ [⟨"accept", ["w"], .symbol "Maybe"⟩,
    ⟨"accept", ["w"], .symbol "True"⟩]

def predicateMixedAnnotation (row : Row) : Option AuthoredClause :=
  if row.index = 2 then some ⟨integer 2, some (.symbol "accept")⟩
  else if row.index = 4 then some ⟨integer 3, none⟩
  else if row.index = 5 then some ⟨integer 5, none⟩
  else none

def predicateMixedRun := WeightedBranchingResumption.contributions
  (authoredSource predicateMixedProgram predicateMixedAnnotation naturalCoefficient)
  350 (.inl (WorkOccurrence.root (initial (call "id" [integer 7]))))

/-- One uninterpreted predicate occurrence cannot suppress the Boolean
return of a different physical predicate rule. -/
theorem authored_predicate_mixed_verdicts_keep_alternatives :
    pendingValues predicateMixedRun = [(integer 7, 10)] ∧
      (predicateMixedRun.map Prod.snd) = [3, 10] ∧
      predicateSavedCoefficients predicateMixedRun = [some (.value (integer 2))] := by
  decide +kernel

theorem authored_predicate_shared_resume_exact :
    predicateSharedRun = WeightedResumption.sequence
      (WeightedBranchingResumption.contributions
        (authoredSource predicateSharedProgram predicateSharedAnnotation naturalCoefficient)
        17 (.inl (WorkOccurrence.root (initial (call "pair" [call "coin" []])))))
      (fun leaf => match leaf with
        | .inl answer => [(Sum.inl answer, (1 : Nat))]
        | .inr pending => WeightedBranchingResumption.contributions
            (authoredSource predicateSharedProgram predicateSharedAnnotation naturalCoefficient)
            333 pending) := by
  exact native_authored_resume_exact predicateSharedProgram predicateSharedAnnotation
    naturalCoefficient 17 333 _

/-! ## Authored completion and owned instruction observations -/

/-- An unresolved predicate is an obligation, while a proved false predicate
is a finished rejection. Neither is reported as a successful body value. -/
theorem authored_predicate_completion_distinguishes_unknown_false :
    nestedValueOutcome 1 (predicateRun (.symbol "Maybe")) = .incomplete ∧
    nestedValueOutcome 1 (predicateRun (.symbol "False")) = .saturated ∧
    nestedValueOutcome 1 (predicateRun (.symbol "True") 0) = .incomplete := by
  decide +kernel

/-- A sufficient answer can coexist with an unresolved alternative. Asking
for a second answer does not turn that alternative into an exhaustion proof. -/
theorem authored_predicate_mixed_completion_keeps_obligation :
    nestedValueOutcome 1 predicateMixedRun = .established ∧
    nestedValueOutcome 2 predicateMixedRun = .incomplete ∧
    nestedValueOutcome 2 (predicateRun (.symbol "True")) = .saturated := by
  decide +kernel

def predicatePendingCut (fuel : Nat) : List AuthoredWork :=
  (predicateRun (.symbol "True") fuel).filterMap
    (fun leaf => match leaf.1 with | .inr pending => some pending | _ => none)

def predicateCut13 : AuthoredWork := (predicatePendingCut 13)[0]'(by decide +kernel)
def predicateCut14 : AuthoredWork := (predicatePendingCut 14)[0]'(by decide +kernel)
def predicateCut29 : AuthoredWork := (predicatePendingCut 29)[0]'(by decide +kernel)
def predicateCut30 : AuthoredWork := (predicatePendingCut 30)[0]'(by decide +kernel)

set_option cbv.warning false in
/-- The actual phase edge changes control without adding a Need instruction.
Both observations retain the body's five and the coefficient's eight steps. -/
theorem authored_predicate_actual_phase_edge_has_zero_instruction_charge :
    authoredSource (predicateProgram (.symbol "True")) predicateAnnotation naturalCoefficient
      predicateCut13 = .inr [(predicateCut14, 1)] ∧
    authoredInstructionAccounts predicateCut13 = [5, 8] ∧
    authoredInstructionAccounts predicateCut14 = [5, 8] ∧
    authoredInstructionCount predicateCut13 = 13 ∧
    authoredInstructionCount predicateCut14 = 13 := by
  refine ⟨?_, ?_⟩
  · cbv
  · decide +kernel

/-- A completed nested grade transfers its eight steps to the suspended
parent once. The body and complete parent stack survive that transfer. -/
theorem authored_predicate_actual_child_return_transfers_work_once :
    authoredInstructionAccounts predicateCut29 = [5, 8, 15] ∧
    authoredInstructionAccounts predicateCut30 = [5, 23] ∧
    authoredInstructionCount predicateCut29 = 28 ∧
    authoredInstructionCount predicateCut30 = 28 := by
  decide +kernel

def authoredRetainedBodyView : AuthoredWork → WorkState :=
  WeightedBranchingResumption.pendingBody (Job := AuthoredJob × List AuthoredJob)

set_option cbv.warning false in
/-- Keeping only the body loses work performed by its predicate. Both cuts
retain that same complete body, with different owned instruction accounts. -/
theorem authored_predicate_same_body_different_instruction_account :
    authoredRetainedBodyView predicateCut14 = authoredRetainedBodyView predicateCut30 ∧
    authoredInstructionCount predicateCut14 = 13 ∧
    authoredInstructionCount predicateCut30 = 28 := by
  refine ⟨?_, ?_⟩
  · cbv
  · decide +kernel

theorem authored_instruction_meter_factors_accounts :
    Mettapedia.GSLT.Core.NonFactorization.Factors
      authoredInstructionAccounts authoredInstructionCount :=
  ⟨List.sum, authored_instruction_accounts_sum⟩

theorem authored_instruction_meter_not_factors_body_view :
    ¬ Mettapedia.GSLT.Core.NonFactorization.Factors
      authoredRetainedBodyView authoredInstructionCount := by
  apply Mettapedia.GSLT.Core.NonFactorization.NonTrivialFiber.not_factors
  refine ⟨predicateCut14, predicateCut30,
    authored_predicate_same_body_different_instruction_account.1, ?_⟩
  rw [authored_predicate_same_body_different_instruction_account.2.1,
    authored_predicate_same_body_different_instruction_account.2.2]
  decide +kernel

/-- These are per-contribution Need instruction observations, retaining the
unknown branch and three separate shared-choice occurrences. They are not
cumulative whole-search or C runtime-event receipts. -/
theorem authored_predicate_completed_instruction_accounts :
    (predicateRun (.symbol "True")).map
      (fun leaf => Sum.elim authoredResultInstructionCount authoredInstructionCount leaf.1) =
        [59] ∧
    (predicateRun (.symbol "Maybe")).map
      (fun leaf => Sum.elim authoredResultInstructionCount authoredInstructionCount leaf.1) =
        [42] ∧
    predicateMixedRun.map
      (fun leaf => Sum.elim authoredResultInstructionCount authoredInstructionCount leaf.1) =
        [42, 59] ∧
    predicateSharedRun.map
      (fun leaf => Sum.elim authoredResultInstructionCount authoredInstructionCount leaf.1) =
        [97, 97, 97] := by
  decide +kernel

set_option cbv.warning false in
/-- Both administrative phase changes and actual nested returns preserve
agreement with every retained caller in this concrete native program. -/
theorem authored_predicate_actual_callers_agree :
    authoredCallerAgreement predicateCut13 ∧
    authoredCallerAgreement predicateCut14 ∧
    authoredCallerAgreement predicateCut29 ∧
    authoredCallerAgreement predicateCut30 := by
  repeat constructor <;> cbv

/-- The same source theorem covers an uninterpreted predicate, retaining
its caller agreement even when that occurrence cannot be published. -/
theorem authored_predicate_unknown_keeps_caller
    (leaf : AuthoredResult ⊕ AuthoredWork) (coefficient : Nat)
    (member : (leaf, coefficient) ∈ predicateRun (.symbol "Maybe")) :
    Sum.elim authoredResultCallerAgreement authoredCallerAgreement leaf :=
  native_authored_root_caller_agreement (predicateProgram (.symbol "Maybe"))
    predicateAnnotation naturalCoefficient 300 _ (leaf, coefficient) member

def predicateWrongCaller : AuthoredWork :=
  match predicateCut14 with
  | .inl body => .inl body
  | .inr (body, job, parents) =>
      .inr ({ body with state := { body.state with
        work := { body.state.work with transitions := body.state.work.transitions + 1 } } },
        job, parents)

set_option cbv.warning false in
/-- A job with the correct coefficient and predicate still cannot be moved
onto a caller with a different actual state. -/
theorem authored_predicate_wrong_caller_refused :
    ¬ authoredCallerAgreement predicateWrongCaller := by
  intro agreement
  have count := congrArg (fun machine : NativeMachine => machine.work.transitions) agreement
  cbv at count


/-! ## Lawful interpretations of the same native execution -/

def demandOrderedIdentityRun {V : Type} [Monoid V] (inner outer : V)
    (forceArgument : Bool) :=
  orderedIdentityWithGrades (integer 2) (if forceArgument then .var "x" else integer 7)
    (demandOrderedCoefficient inner outer)

def interpretOrderedFactors {V : Type} [Monoid V] (inner outer : V) : FreeMonoid String →* V :=
  FreeMonoid.lift (fun name => if name = "inner" then inner else outer)

theorem demand_ordered_interpretation {V : Type} [Monoid V] (inner outer : V) :
    demandOrderedCoefficient inner outer =
      fun outcome => (orderedCoefficient outcome).map (interpretOrderedFactors inner outer) := by
  funext outcome
  unfold orderedCoefficient demandOrderedCoefficient
  split <;> simp [interpretOrderedFactors, FreeMonoid.lift_eval_of]

theorem demand_ordered_native_run {V : Type} [Monoid V]
    (inner outer : V) (forceArgument : Bool) :
    demandOrderedIdentityRun inner outer forceArgument =
      WeightedResumption.mapCoefficients (interpretOrderedFactors inner outer)
        (orderedIdentityRun forceArgument) := by
  rw [demandOrderedIdentityRun, orderedIdentityWithGrades, demand_ordered_interpretation]
  exact native_nested_change_coefficients _ _ _ _ _ _

theorem demand_ordered_values {V : Type} [Monoid V] (inner outer : V) :
    pendingValues (demandOrderedIdentityRun inner outer true) = [(integer 7, inner * outer)] ∧
    pendingValues (demandOrderedIdentityRun inner outer false) = [(integer 7, outer * inner)] := by
  constructor
  · rw [demand_ordered_native_run]
    change WeightedBranchingResumption.nestedSelected completedValue _ = _
    rw [WeightedBranchingResumption.nested_selected_change_coefficients]
    change WeightedResumption.mapCoefficients (interpretOrderedFactors inner outer)
      (pendingValues (orderedIdentityRun true)) = _
    rw [graded_identity_keeps_factor_completion_order.1]
    simp [WeightedResumption.mapCoefficients, interpretOrderedFactors]
  · rw [demand_ordered_native_run]
    change WeightedBranchingResumption.nestedSelected completedValue _ = _
    rw [WeightedBranchingResumption.nested_selected_change_coefficients]
    change WeightedResumption.mapCoefficients (interpretOrderedFactors inner outer)
      (pendingValues (orderedIdentityRun false)) = _
    rw [graded_identity_keeps_factor_completion_order.2]
    simp [WeightedResumption.mapCoefficients, interpretOrderedFactors]

theorem matrix_native_demand_changes_coefficients :
    pendingValues (demandOrderedIdentityRun WeightedResumptionControls.upper
      WeightedResumptionControls.lower true) ≠
    pendingValues (demandOrderedIdentityRun WeightedResumptionControls.upper
      WeightedResumptionControls.lower false) := by
  rw [(demand_ordered_values _ _).1, (demand_ordered_values _ _).2]
  simp only [ne_eq, List.cons.injEq, Prod.mk.injEq, and_true, true_and]
  exact WeightedResumptionControls.matrix_composition_is_ordered

theorem vector_native_zero_divisors :
    pendingValues (demandOrderedIdentityRun WeightedResumptionControls.firstObjective
      WeightedResumptionControls.secondObjective true) = [(integer 7, 0)] := by
  rw [(demand_ordered_values _ _).1,
    WeightedResumptionControls.vector_zero_divisors.2.2]

open Mettapedia.Algebra.RationalComplexAmplitude

theorem amplitude_native_sequential_square :
    pendingValues (demandOrderedIdentityRun (fromPair (0, 1)) (fromPair (0, 1)) true) =
      [(integer 7, (-1 : Amplitude))] := by
  rw [(demand_ordered_values _ _).1, imaginary_square]

theorem amplitude_native_born_per_contribution (forceArgument : Bool) :
    WeightedResumption.mapCoefficients born
      (demandOrderedIdentityRun (fromPair (0, 1)) (fromPair (0, 1)) forceArgument) =
      demandOrderedIdentityRun (born (fromPair (0, 1)))
        (born (fromPair (0, 1))) forceArgument := by
  have change := native_nested_change_coefficients born orderedIdentityProgram
    (fun row => if row.index = 2 then some (integer 2)
      else if row.index = 4 then some (if forceArgument then .var "x" else integer 7)
      else none) (demandOrderedCoefficient (fromPair (0, 1)) (fromPair (0, 1))) 300
    (.inl (WorkOccurrence.root (initial (call "outer" [call "id" [integer 7]]))))
  have interpretation :
      (fun outcome =>
        (demandOrderedCoefficient (fromPair (0, 1)) (fromPair (0, 1)) outcome).map born) =
      demandOrderedCoefficient (born (fromPair (0, 1))) (born (fromPair (0, 1))) := by
    funext outcome
    unfold demandOrderedCoefficient
    split <;> rfl
  simpa [demandOrderedIdentityRun, orderedIdentityWithGrades, interpretation] using change.symm

/-! ## Literal vector, matrix and amplitude grades -/

/-- A two-coordinate natural profile; negative or malformed returns remain
outside the interpretation instead of being silently coerced. -/
def naturalVectorCoefficient : Outcome → Option (Fin 2 → Nat)
  | .value (.expression [.symbol "Vector", .expression
      [.grounded (.int a), .grounded (.int b)]]) =>
      if 0 ≤ a ∧ 0 ≤ b then some ![a.toNat, b.toNat] else none
  | _ => none

def vectorLiteral (left right : Int) : Atom :=
  .expression [.symbol "Vector", .expression [integer left, integer right]]

theorem literal_vector_zero_divisors :
    pendingValues (orderedIdentityWithGrades (vectorLiteral 1 0) (vectorLiteral 0 1)
      naturalVectorCoefficient) = [(integer 7, 0)] ∧
    naturalVectorCoefficient (.value (vectorLiteral 1 0)) ≠ some 0 ∧
    naturalVectorCoefficient (.value (vectorLiteral 0 1)) ≠ some 0 := by
  decide +kernel

theorem literal_vector_coefficient_keeps_shape_and_sign :
    naturalVectorCoefficient (.value (.expression [.symbol "Vector",
      .expression [integer 1]])) = none ∧
    naturalVectorCoefficient (.value (vectorLiteral (-1) 0)) = none := by
  decide +kernel



abbrev IntegerMatrix := Matrix (Fin 2) (Fin 2) Int

def integerMatrixCoefficient : Outcome → Option IntegerMatrix
  | .value (.expression [.symbol "Matrix", .grounded (.int 2), .grounded (.int 2),
      .expression [.grounded (.int a), .grounded (.int b),
        .grounded (.int c), .grounded (.int d)]]) =>
      some (Mettapedia.Algebra.FiniteCoordinateBuffer.toMatrix 2 2 [a, b, c, d])
  | _ => none

def complexLiteralCoefficient : Outcome → Option Amplitude
  | .value (.expression [.symbol "Complex", .grounded (.int real),
      .grounded (.int imaginary)]) => some (fromPair (real, imaginary))
  | _ => none

def matrixLiteral (a b c d : Int) : Atom :=
  .expression [.symbol "Matrix", integer 2, integer 2,
    .expression [integer a, integer b, integer c, integer d]]

def complexLiteral (real imaginary : Int) : Atom :=
  .expression [.symbol "Complex", integer real, integer imaginary]

theorem literal_matrix_coefficients_follow_native_order :
    pendingValues (orderedIdentityWithGrades (matrixLiteral 1 1 0 1) (matrixLiteral 1 0 1 1)
      integerMatrixCoefficient) = [(integer 7, (!![1, 1; 1, 2] : IntegerMatrix))] := by
  decide +kernel

theorem literal_matrix_coefficient_keeps_shape :
    integerMatrixCoefficient (.value (.expression [.symbol "Matrix", integer 1, integer 4,
      .expression [integer 1, integer 1, integer 0, integer 1]])) = none ∧
    integerMatrixCoefficient (.value (.expression [.symbol "Matrix", integer 2, integer 2,
      .expression [integer 1, integer 1, integer 0]])) = none := by decide +kernel

theorem literal_amplitude_native_composition :
    pendingValues (orderedIdentityWithGrades (complexLiteral 0 1) (complexLiteral 0 1)
      complexLiteralCoefficient) = [(integer 7, (-1 : Amplitude))] := by
  decide +kernel

theorem literal_amplitude_unknown_is_retained :
    pendingValues (orderedIdentityWithGrades (.symbol "UnknownPhase") (complexLiteral 0 1)
      complexLiteralCoefficient) = [] ∧
    (WeightedBranchingResumption.nestedObligations
      (orderedIdentityWithGrades (.symbol "UnknownPhase") (complexLiteral 0 1)
        complexLiteralCoefficient)).length = 1 := by decide +kernel

/-! ## Authored jobs on the shared stateful agenda -/

namespace ScheduledAuthored

open Mettapedia.GSLT.Core.BranchingTemporal (Scheduler)

def agenda {V : Type} : Controller (AuthoredWork × V) (AuthoredResult × V) Unit :=
  .fixed Scheduler.breadthFirst

def run (program : Program) (annotation : Row → Option AuthoredClause)
    (input : Atom) (fuel : Nat) :=
  Snapshot.run (authoredSystem program annotation naturalCoefficient) agenda fuel
    (Snapshot.initial agenda [(.inl (WorkOccurrence.root (initial input)), 1)])

def observed (program : Program) (annotation : Row → Option AuthoredClause)
    (input : Atom) (fuel : Nat) :=
  WeightedBranchingResumption.Scheduled.observeSnapshot
    (run program annotation input fuel).search

def predicate (verdict : Atom) (fuel : Nat := 300) :=
  observed (predicateProgram verdict) predicateAnnotation (call "id" [integer 7]) fuel

theorem scheduled_predicate_uses_native_grade :
    pendingValues (predicate (.symbol "True")) = [(integer 7, 6)] := by
  decide +kernel

/-- The certificate builder unfolds the actual authored predicate and nested
grade computation. It is not a supplied global normalization assumption. -/
theorem predicate_source_certificate :
    Mettapedia.GSLT.Core.FiniteSearchCertificate.Certified
      (authoredSystem (predicateProgram (.symbol "True")) predicateAnnotation naturalCoefficient)
      64 (.inl (WorkOccurrence.root (initial (call "id" [integer 7]))), 1) := by
  have complete : (Mettapedia.GSLT.Core.FiniteSearchCertificate.build
      (authoredSystem (predicateProgram (.symbol "True")) predicateAnnotation naturalCoefficient)
      64 (.inl (WorkOccurrence.root (initial (call "id" [integer 7]))), 1)).isSome = true := by
    decide +kernel
  unfold Mettapedia.GSLT.Core.FiniteSearchCertificate.Certified
  cases found : Mettapedia.GSLT.Core.FiniteSearchCertificate.build
      (authoredSystem (predicateProgram (.symbol "True")) predicateAnnotation naturalCoefficient)
      64 (.inl (WorkOccurrence.root (initial (call "id" [integer 7]))), 1) with
  | none => simp [found] at complete
  | some tree => exact ⟨tree, rfl⟩

/-- A shorter unfolding allowance retains an unresolved computation; it does
not certify an empty answer bag. -/
theorem predicate_short_certificate_refused :
    Mettapedia.GSLT.Core.FiniteSearchCertificate.build
      (authoredSystem (predicateProgram (.symbol "True")) predicateAnnotation naturalCoefficient)
      16 (.inl (WorkOccurrence.root (initial (call "id" [integer 7]))), 1) = none := by
  decide +kernel

/-- Every lawful stateful controller completes this actual native source at
the independently counted finite work allowance and emits its source bag. -/
theorem predicate_any_controller_source_bag {Memory : Type}
    (controller : Controller (AuthoredWork × Nat) (AuthoredResult × Nat) Memory) :
    let system := authoredSystem (predicateProgram (.symbol "True"))
      predicateAnnotation naturalCoefficient
    let roots : List (AuthoredWork × Nat) :=
      [(Sum.inl (WorkOccurrence.root (initial (call "id" [integer 7]))), 1)]
    let fuel := Mettapedia.GSLT.Core.BranchingTemporal.foldRanks
      (Mettapedia.GSLT.Core.FiniteSearchCertificate.finiteWork system 64) roots
    let result := Snapshot.run system controller fuel (Snapshot.initial controller roots)
    result.search.frontier = [] ∧
      Mettapedia.GSLT.Core.BranchingTemporal.eventBag result.search.events =
        Mettapedia.GSLT.Core.BranchingTemporal.foldValues
          (Mettapedia.GSLT.Core.FiniteSearchCertificate.finiteBag system 64) roots := by
  apply Mettapedia.GSLT.Core.FiniteSearchCertificate.observation_at_work
  intro root member
  obtain rfl := List.mem_singleton.mp member
  exact predicate_source_certificate

/-- A declared interpretation reads two and three as the exact confidence
coefficients one-half and one-quarter. This is an explicit change of algebra,
not an implicit cast of the ordinary natural-count interpretation. -/
def confidenceCoefficient : Outcome → Option WeightedResumptionControls.Scheduling.Confidence
  | .value (.grounded (.int 2)) => some WeightedResumptionControls.Scheduling.half
  | .value (.grounded (.int 3)) => some WeightedResumptionControls.Scheduling.quarter
  | _ => none

def confidenceSnapshot :=
  Snapshot.run (authoredSystem (predicateProgram (.symbol "True"))
    predicateAnnotation confidenceCoefficient) agenda 300
    (Snapshot.initial agenda [(.inl (WorkOccurrence.root
      (initial (call "id" [integer 7]))), 1)])

/-- The actual native coefficient and predicate computations retain their
factors through the unit-interval interpretation. -/
theorem native_confidence_factors :
    pendingValues (WeightedBranchingResumption.Scheduled.observeSnapshot
      confidenceSnapshot.search) =
      [(integer 7, WeightedResumptionControls.Scheduling.half *
        WeightedResumptionControls.Scheduling.quarter)] := by
  decide +kernel

/-- The same executable native source inhabits the superior-law premise.
This is not a claim that every natural or complex coefficient has that law. -/
theorem native_confidence_stopping_law :
    Mettapedia.GSLT.Core.WeightOrderedSelection.Realized
      (authoredSystem (predicateProgram (.symbol "True")) predicateAnnotation confidenceCoefficient)
      (Mettapedia.GSLT.Core.WeightOrderedSelection.unitIntervalMul ℚ) Prod.snd :=
  authored_coefficient_realized _ _ _
    (Mettapedia.GSLT.Core.WeightOrderedSelection.unitIntervalMul ℚ) (fun _ _ => rfl)

/-- The same declared factor interpretation can use an unrestricted rational
carrier. Its factors stay bounded; an incoming coefficient need not do so. -/
def scaledConfidenceCoefficient (outcome : Outcome) : Option ℚ :=
  (confidenceCoefficient outcome).map fun value => value.val

theorem scaled_confidence_interpretation (outcome : Outcome) (value : ℚ)
    (decoded : scaledConfidenceCoefficient outcome = some value) :
    0 ≤ value ∧ value ≤ 1 := by
  simp only [scaledConfidenceCoefficient, Option.map_eq_some_iff] at decoded
  obtain ⟨bounded, _, rfl⟩ := decoded
  exact bounded.property

theorem native_scaled_confidence_step_bound :
    Mettapedia.GSLT.Core.WeightOrderedSelection.StepBound
      (authoredSystem (predicateProgram (.symbol "True"))
        predicateAnnotation scaledConfidenceCoefficient)
      (fun node => OrderDual.toDual node.2) (fun node => 0 ≤ node.2) :=
  authored_product_step_bound _ _ _ scaled_confidence_interpretation

def scaledConfidenceSnapshot :=
  Snapshot.run (authoredSystem (predicateProgram (.symbol "True"))
    predicateAnnotation scaledConfidenceCoefficient) agenda 300
    (Snapshot.initial agenda [(.inl (WorkOccurrence.root
      (initial (call "id" [integer 7]))), 4)])

/-- Native coefficient and predicate execution consumes the actual factors
one-half and one-quarter from an initial coefficient of four. -/
theorem native_confidence_seed_above_one :
    pendingValues (WeightedBranchingResumption.Scheduled.observeSnapshot
      scaledConfidenceSnapshot.search) = [(integer 7, (1 / 2 : ℚ))] := by
  decide +kernel

/-- Every generated native continuation stays in the nonnegative domain and
below its initial coefficient, including intermediate nested grade jobs. -/
theorem native_scaled_confidence_generated {node : AuthoredWork × ℚ}
    (generated : Mettapedia.GSLT.Core.BranchingTemporal.Generated
      (authoredSystem (predicateProgram (.symbol "True"))
        predicateAnnotation scaledConfidenceCoefficient)
      [(.inl (WorkOccurrence.root (initial (call "id" [integer 7]))), 4)] node) :
    0 ≤ node.2 ∧ node.2 ≤ 4 := by
  apply native_scaled_confidence_step_bound.generated (bound := OrderDual.toDual 4)
    ?_ ?_ generated
  · intro item member
    obtain rfl := List.mem_singleton.mp member
    norm_num
  · intro item member
    obtain rfl := List.mem_singleton.mp member
    exact le_rfl

/-- The global agenda retains the same shared coin choice and both duplicate
physical equations while running coefficient and predicate jobs. -/
theorem scheduled_shared_choices_and_duplicates :
    pendingValues (observed predicateSharedProgram predicateSharedAnnotation
      (call "pair" [call "coin" []]) 350) =
      [(call "Pair" [integer 2, integer 2], 30),
       (call "Pair" [integer 2, integer 2], 30),
       (call "Pair" [integer 5, integer 5], 75)] := by
  decide +kernel

/-- No runnable instruction remains, but an unknown predicate still owns its
parked result. Scheduler exhaustion alone is not an answer-shortage proof. -/
theorem scheduled_unknown_is_not_saturation :
    (run (predicateProgram (.symbol "Maybe")) predicateAnnotation
      (call "id" [integer 7]) 300).search.frontier = [] ∧
    nestedValueOutcome 1 (predicate (.symbol "Maybe")) = .incomplete ∧
    predicateSavedCoefficients (predicate (.symbol "Maybe")) =
      [some (.value (integer 2))] := by
  refine ⟨?_, ?_, ?_⟩
  · have exhausted : (run (predicateProgram (.symbol "Maybe")) predicateAnnotation
        (call "id" [integer 7]) 64).search.frontier = [] := by
      decide +kernel
    dsimp only [run] at exhausted
    change (Snapshot.run (authoredSystem (predicateProgram (.symbol "Maybe"))
      predicateAnnotation naturalCoefficient) agenda (64 + 236)
      (Snapshot.initial agenda
        [(.inl (WorkOccurrence.root (initial (call "id" [integer 7]))), 1)])).search.frontier = []
    rw [Snapshot.run_add,
      Snapshot.run_eq_self_of_frontier_nil _ _ _ exhausted]
    exact exhausted
  · decide +kernel
  · decide +kernel

/-- The native saturation characterization rejects this actual parked
predicate even though its runnable frontier is exhausted. -/
theorem parked_predicate_refuses_saturation :
    ¬ nestedValueOutcome 1 (predicate (.symbol "Maybe")) = .saturated := by
  intro saturated
  have closed := (authored_saturation_iff completedValue 1
    (run (predicateProgram (.symbol "Maybe")) predicateAnnotation
      (call "id" [integer 7]) 300)).mp saturated
  have parked :
      ((run (predicateProgram (.symbol "Maybe")) predicateAnnotation
        (call "id" [integer 7]) 300).search.events.filterMap
        (fun event => match event.value.1 with
          | .inl _ => none
          | .inr saved => some (saved, event.value.2))) ≠ [] := by
    decide +kernel
  exact parked closed.2.1

theorem scheduled_false_is_completed_rejection :
    nestedValueOutcome 1 (predicate (.symbol "False")) = .saturated := by
  decide +kernel

/-- The complete inherited snapshot resumes; no grade or captured choice is
recomputed by rebuilding the agenda from the original expression. -/
theorem scheduled_native_resume :
    Snapshot.run (authoredSystem predicateSharedProgram predicateSharedAnnotation
      naturalCoefficient) agenda 333
      (run predicateSharedProgram predicateSharedAnnotation
        (call "pair" [call "coin" []]) 17) =
    run predicateSharedProgram predicateSharedAnnotation
      (call "pair" [call "coin" []]) 350 :=
  (Snapshot.run_add _ agenda 17 333 _).symm

def record (capacity : Option Nat) (fuel : Nat) :=
  Snapshot.run (authoredSystem (predicateProgram (.symbol "True"))
    predicateAnnotation naturalCoefficient)
    (Recording.controller agenda (fun _ node _ _ => node) capacity) fuel
    (Recording.start (Snapshot.initial agenda
      [(.inl (WorkOccurrence.root (initial (call "id" [integer 7]))), 1)]) capacity)

/-- A one-node recording cannot prune the pending grade computation or change
the final six-unit contribution. Its omitted selections remain visible. -/
theorem scheduled_recording_preserves_weighted_result :
    (record (some 1) 300).search =
      (run (predicateProgram (.symbol "True")) predicateAnnotation
        (call "id" [integer 7]) 300).search ∧
    pendingValues (WeightedBranchingResumption.Scheduled.observeSnapshot
      (record (some 1) 300).search) = [(integer 7, 6)] := by
  constructor
  · unfold record run
    have same := authored_recording_erasure
      (predicateProgram (.symbol "True")) predicateAnnotation naturalCoefficient
      agenda (fun _ node _ _ => node) (some 1) 300
      (Recording.start (Snapshot.initial agenda
        [(.inl (WorkOccurrence.root (initial (call "id" [integer 7]))), 1)]) (some 1))
    simpa only [Recording.erase, Recording.start, Snapshot.mapMemory] using
      congrArg Snapshot.search same
  · decide +kernel

theorem scheduled_recording_reports_omission :
    ((record (some 1) 300).memory.2).map (fun saved =>
      (saved.items.length, decide (saved.omitted > 0), saved.complete?.isNone)) =
      some (1, true, true) := by
  decide +kernel

theorem scheduled_recording_resume :
    Snapshot.run (authoredSystem (predicateProgram (.symbol "True"))
      predicateAnnotation naturalCoefficient)
      (Recording.controller agenda (fun _ node _ _ => node) (some 1)) 283
      (record (some 1) 17) = record (some 1) 300 :=
  (Snapshot.run_add _ _ 17 283 _).symm

def tracedRecord (capacity fuel : Nat) :=
  Snapshot.run (authoredOccurrenceSystem (predicateProgram (.symbol "True"))
    predicateAnnotation naturalCoefficient)
    (Recording.controller (Controller.fixed Scheduler.breadthFirst)
      (fun _ node _ _ => node) (some capacity)) fuel
    (Recording.start (Snapshot.initial (Controller.fixed Scheduler.breadthFirst)
      [WorkOccurrence.root
        (.inl (WorkOccurrence.root (initial (call "id" [integer 7]))), 1)]) (some capacity))

/-- The recorded path extends across actual nested parent suspensions; its
last selected source state carries the completed six-unit coefficient. -/
theorem trace_covers_nested_parent_and_final_coefficient :
    ((tracedRecord 300 300).memory.2).map (fun saved =>
      saved.items.any (fun node => match node.state.1 with
        | .inr (_, _, _ :: _) => true
        | _ => false)) = some true ∧
    ((tracedRecord 300 300).memory.2).bind (fun saved =>
      saved.items.getLast?.map (fun node => node.state.2)) = some 6 ∧
    ((tracedRecord 300 300).memory.2).map (fun saved => saved.complete?.isSome) = some true := by
  decide +kernel

/-- Truncating the source trace leaves the native weighted execution and its
complete retained worlds untouched, but cannot claim a complete history. -/
theorem truncated_trace_preserves_native_completion :
    (tracedRecord 1 300).search = (tracedRecord 300 300).search ∧
    ((tracedRecord 1 300).memory.2).bind Recording.Prefix.complete? = none := by
  constructor
  · let unrecorded : Snapshot (WorkOccurrence (AuthoredWork × Nat))
        ((AuthoredResult × Nat) × List Nat) Unit :=
      Snapshot.initial (Controller.fixed Scheduler.breadthFirst)
      [WorkOccurrence.root
        (.inl (WorkOccurrence.root (initial (call "id" [integer 7]))), (1 : Nat))]
    have same (capacity : Nat) := Recording.run_erasure
      (authoredOccurrenceSystem (predicateProgram (.symbol "True"))
        predicateAnnotation naturalCoefficient)
      (Controller.fixed Scheduler.breadthFirst) (fun _ node _ _ => node) (some capacity)
      300 (Recording.start unrecorded (some capacity))
    have one := congrArg Snapshot.search (same 1)
    have full := congrArg Snapshot.search (same 300)
    simpa only [tracedRecord, unrecorded, Recording.erase, Recording.start,
      Snapshot.mapMemory] using one.trans full.symm
  · apply Option.isNone_iff_eq_none.mp
    decide +kernel

end ScheduledAuthored


namespace RecordedNative

open Mettapedia.GSLT.Core.BranchingTemporal

def system := recordedAuthoredOccurrenceSystem (predicateProgram (.symbol "True"))
  predicateAnnotation naturalCoefficient

def agenda : Controller (WorkOccurrence (RecordedAuthoredWork × Nat))
    ((RecordedAuthoredResult × Nat) × List Nat) Unit := Controller.fixed Scheduler.breadthFirst

def point := Snapshot.initial agenda
  [WorkOccurrence.root (recordedAuthoredRoot (call "id" [integer 7]), (1 : Nat))]

def cut := Snapshot.run system agenda 22 point

def frame := Preparation.capture system
  (cut.search.frontier.headD (WorkOccurrence.root (recordedAuthoredRoot (integer 0), 1)))

def changedParent (parent : AuthoredJob) : AuthoredJob :=
  { parent with score := { parent.score with origin := { parent.score.origin with
      world := { parent.score.origin.world with
        nextCell := parent.score.origin.world.nextCell + 1 } } } }

def changedParents (held : RecordedAuthoredWork) : RecordedAuthoredWork :=
  match held with
  | ⟨.inl body, valid⟩ => ⟨.inl body, valid⟩
  | ⟨.inr (body, job, parents), valid⟩ =>
      ⟨.inr (body, job, parents.map changedParent), by
        refine ⟨valid.1, valid.2.1, ?_⟩
        intro parent member
        obtain ⟨before, beforeMember, rfl⟩ := List.mem_map.mp member
        exact valid.2.2 before beforeMember⟩

def changedFrame := { frame with input :=
  { frame.input with state := (changedParents frame.input.state.1, frame.input.state.2) } }

/-- This is an actual nested native suspension with a retained scoring parent. -/
theorem checkpoint_has_parent :
    (match frame.input.state.1.val with
      | .inl _ => 0
      | .inr (_, _, parents) => parents.length) = 1 := by decide +kernel

def currentView (held : RecordedAuthoredWork) :
    RecordedWorkView ⊕ (RecordedWorkView × AuthoredJob.RecordedView) :=
  match held.val with
  | .inl body => .inl (workRecordedView body)
  | .inr (body, job, _) => .inr (workRecordedView body, job.recordedView)

/-- A finite native comparison notices a change confined to a parent's
captured allocator, while the body and current job retain identical finite representations. -/
theorem parent_mutation_visible :
    currentView frame.input.state.1 = currentView changedFrame.input.state.1 ∧
      frame.input ≠ changedFrame.input := by
  decide +kernel

theorem unchanged_native_frame_accepted :
    (Recording.Replay.step? system agenda cut frame).isSome = true := by decide +kernel

theorem changed_native_parent_refused :
    Recording.Replay.step? system agenda cut changedFrame = none := by decide +kernel

/-- Refusal leaves the owned checkpoint and the complete unconsumed frame. -/
theorem changed_native_parent_keeps_residual :
    Recording.Replay.run system agenda [changedFrame, frame] cut =
      .error (cut, [changedFrame, frame]) := by
  simp only [Recording.Replay.run, changed_native_parent_refused]


/-- A whole nested coefficient/predicate run replays with its six-unit
coefficient and no lost or invented residual work. -/
theorem nested_native_replay_finishes :
    (match Recording.Replay.run system agenda
        (Recording.stream system agenda Recording.Replay.observe 300 point) point with
      | .ok replayed => some (replayed.search.events.map (fun event => event.value.1.2),
          replayed.search.frontier.length)
      | .error _ => none) = some ([6], 0) := by
  decide +kernel

end RecordedNative

end Mettapedia.Languages.MeTTa.PrimeCandidates.NativeWeightedControls
