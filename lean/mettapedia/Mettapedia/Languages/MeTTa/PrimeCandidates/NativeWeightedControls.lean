import Mettapedia.Languages.MeTTa.PrimeCandidates.NativeWeightedHandler
import Mettapedia.Languages.MeTTa.PrimeCandidates.NativeGradeControls
import Mettapedia.GSLT.Scope.ReadoutDescent
import Mathlib.Algebra.FreeMonoid.Basic

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

def orderedCoefficient : Outcome → Option (FreeMonoid String)
  | .value (.grounded (.int 2)) => some (FreeMonoid.of "inner")
  | .value (.grounded (.int 7)) => some (FreeMonoid.of "outer")
  | _ => none

def orderedIdentityProgram : Program :=
  identityProgram ++ [⟨"outer", ["x"], .var "x"⟩]

def orderedIdentityRun (forceArgument : Bool) :=
  WeightedBranchingResumption.contributions
    (nestedSource orderedIdentityProgram
      (fun row => if row.index = 2 then some (integer 2)
        else if row.index = 4 then some (if forceArgument then .var "x" else integer 7)
        else none) orderedCoefficient)
    300 (.inl (WorkOccurrence.root (initial (call "outer" [call "id" [integer 7]]))))

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

end Mettapedia.Languages.MeTTa.PrimeCandidates.NativeWeightedControls
