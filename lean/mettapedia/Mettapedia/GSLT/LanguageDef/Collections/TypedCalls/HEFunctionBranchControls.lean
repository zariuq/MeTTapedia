import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFunctionBranchComposition

/-!
# Operator branches with distinct real binding records

The fixtures retain nonempty records, rather than using one empty frame for
every operator alternative. Independent presentation certificates and the
actual native readout establish the frame relation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFunctionBranchControls

open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open RecursiveTasks FirstSuccessRecursiveExecution FirstSuccessSourceExecution
open Spec.Eval Spec.Eval.Completed Spec.Type.Presentation Spec.Type.Presentation.BindingTheory
open Spec.Type.RuntimeRefinement Spec.Match.Merge Spec.Match.ModelTheory
open FirstSuccessScopedAdequacy FirstSuccessScopedAdequacy.ScopedRetainedRelation
open FirstSuccessScopedAdequacy.ScopedPolymorphicCompletion
open FirstSuccessScopedAdequacy.UniversalScopedPolymorphicApplication
open HEFunctionBranchComposition

def num (n : Int) : Atom := .grounded (.int n)
def bindings (n : Int) : Bindings := ⟨[("x", num n)], []⟩

def frame (n : Int) : Completed.Frame where
  bindings := bindings n
  environment := [("x", .grounded (.int n))]
  certified := by
    have present := single_assignment_presentation "x" (num n) (by simp [num, Spec.Type.Presentation.TypeSubst.typeVars])
    simpa only [bindings, num, Entry.Value.eraseEnvironment, List.map_cons, List.map_nil, Entry.Value.erase]
      using ReadoutCertificate.of_fold present

theorem principal (n : Int) : PrincipalBindingFrame (bindings n) := by
  have loopFree : SemanticLoopFree (bindings n) :=
    (hasLoop_eq_false_iff_semanticLoopFree _).mp (by cbv)
  have nonvariable : AssignmentsNonVariable (bindings n) := by
    intro key value present
    simp only [bindings, List.mem_singleton] at present
    cases present
    simp [num, isVariableB]
  refine ⟨loopFree, nonvariable, ?_⟩
  apply Spec.Match.StructuralModel.canonicalClassCoherent_of_structurallySolved
  intro left right leftValue rightValue leftMem rightMem equivalent
  simp only [bindings, List.mem_singleton] at leftMem rightMem
  cases leftMem
  cases rightMem
  exact Spec.Match.StructuralModel.AtomSolved.refl _ _

theorem activation (n : Int) : ScopedActivationRel (bindings n) (frame n) := by
  have invariant := principal n
  have table : QueryBindingProjection.nativeReadoutPresentation (bindings n) = [("x", num n)] := by cbv
  refine SourceBindingComparison.FrameRelated.semantic (BindingSourceAgreement.refl _) (frame n).certified ?_
  intro atom depth covered
  have materialized := QueryBindingProjection.nativeReadoutPresentation_apply invariant.loopFree invariant.nonvariable
    invariant.coherent atom depth covered
  simpa only [table, frame, num, Entry.Value.eraseEnvironment, List.map_cons, List.map_nil, Entry.Value.erase] using materialized.symm

theorem empty_arguments (head : Atom) (n : Int) (live : List Atom) (scope : List String)
    (wStack : List RecursiveTasks.Frame) (cStack : List RecursiveTasks.Contextual.Continuation)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result) :
    ScopedTaskRun Space.empty HE.GroundedDispatch.none Completed.Controls.typedDispatch Policy.unmarked
      (.args [] [] (bindings n) 1 (head :: live)) (.arguments (head :: live) scope [] (frame n))
      wStack cStack wEmitted cEmitted 1 [(argumentPacket [], bindings n)]
      [(Entry.Value.argumentPacket [], frame n)] := by
  have stepped : (Checked.machine HE.GroundedDispatch.none scopedTypes).step
      ⟨Space.empty, .work (.args [] [] (bindings n) 1 (head :: live)), wStack, wEmitted⟩ =
      some (.silent ⟨Space.empty, .returning [(argumentPacket [], bindings n)], wStack, wEmitted⟩) := rfl
  refine ⟨by decide, .cons ⟨?_, activation n⟩ .nil, ?_,
    RecursiveExecution.Contextual.arguments_complete
      (Completed.ArgumentsRel.nil (space := Space.empty) (dispatch := Completed.Controls.typedDispatch)
        (lookup := Completed.scopedLookup) (live := head :: live) (scope := scope) (frame := frame n)
        (policy := Policy.unmarked)) cStack⟩
  · simp [Entry.Value.argumentPacket, Entry.Value.erase, argumentPacket]
  · intro budget
    rw [Nat.add_comm 1 budget, (Checked.machine HE.GroundedDispatch.none scopedTypes).run_succ_silent stepped]

def arrow : Atom := .expression [.symbol "->", .symbol "Number"]

theorem simple_cons (name : String) (n : Int)
    {live : List Atom} {scope : List String} {wStack : List RecursiveTasks.Frame}
    {cStack : List RecursiveTasks.Contextual.Continuation} {wEmitted : ResultSet} {cEmitted : List Completed.Result}
    {heads results : ResultSet} {cHeads cResults : List Completed.Result} {steps : Nat}
    (running : isEmptyOrError (.symbol name) = false)
    (tail : Heads Space.empty HE.GroundedDispatch.none Completed.Controls.typedDispatch Policy.unmarked
      wEmitted cEmitted arrow [] [] [] 1 live scope heads cHeads
      (.prepend [(.expression [.symbol name], bindings n)] :: wStack)
      (.prepend [(.expression .active [.symbol name], frame n)] :: cStack) steps results cResults) :
    Heads Space.empty HE.GroundedDispatch.none Completed.Controls.typedDispatch Policy.unmarked
      wEmitted cEmitted arrow [] [] [] 1 live scope
      ((.symbol name, bindings n) :: heads) ((.symbol name, frame n) :: cHeads) wStack cStack
      (steps + 5) ((.expression [.symbol name], bindings n) :: results)
      ((.expression .active [.symbol name], frame n) :: cResults) := by
  have child := empty_arguments (.symbol name) n live scope
    (.functionTail (.symbol name) :: .append (.heads arrow [] 1 heads live) :: wStack)
    (.functionAssemble (.symbol name) :: .append (.functionBranches live scope [] cHeads) :: cStack)
    wEmitted cEmitted
  have built := Heads.continuing (operatorType := arrow) (arguments := []) (types := []) (requests := [])
    (fuel := 1) (live := live) (scope := scope) (.symbol name, bindings n) (.symbol name, frame n) heads cHeads wStack cStack
    1 steps [(argumentPacket [], bindings n)] results [(Entry.Value.argumentPacket [], frame n)] cResults
    ⟨by simp only [Entry.Value.erase], activation n⟩ running
    (by decide : getFunctionArgTypes arrow = some ([] : List Atom)) (Completed.ArgumentsRel.nil)
    (by simpa only [Entry.Value.erase] using child)
  simpa [RecursiveTasks.functionTail, argumentsSucceeded, argumentValues, unpackArguments, argumentPacket,
    Completed.functionAssemble, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using built tail

def heads : ResultSet :=
  [(.symbol "f", bindings 1), (.symbol "Empty", bindings 9), (.symbol "f", bindings 2),
    (.symbol "f", bindings 1), (.symbol "g", bindings 3)]
def cHeads : List Completed.Result :=
  [(.symbol "f", frame 1), (.symbol "Empty", frame 9), (.symbol "f", frame 2),
    (.symbol "f", frame 1), (.symbol "g", frame 3)]
def results : ResultSet :=
  [(.expression [.symbol "f"], bindings 1), (.symbol "Empty", bindings 9), (.expression [.symbol "f"], bindings 2),
    (.expression [.symbol "f"], bindings 1), (.expression [.symbol "g"], bindings 3)]
def cResults : List Completed.Result :=
  [(.expression .active [.symbol "f"], frame 1), (.symbol "Empty", frame 9), (.expression .active [.symbol "f"], frame 2),
    (.expression .active [.symbol "f"], frame 1), (.expression .active [.symbol "g"], frame 3)]

theorem branch_spine (live : List Atom) (scope : List String) (wStack : List RecursiveTasks.Frame)
    (cStack : List RecursiveTasks.Contextual.Continuation) (wEmitted : ResultSet) (cEmitted : List Completed.Result) :
    Heads Space.empty HE.GroundedDispatch.none Completed.Controls.typedDispatch Policy.unmarked
      wEmitted cEmitted arrow [] [] [] 1 live scope heads cHeads wStack cStack 24 results cResults := by
  dsimp only [heads, cHeads, results, cResults]
  apply simple_cons "f" 1 (steps := 19) (by decide)
  refine Heads.stopped (.symbol "Empty", bindings 9) (.symbol "Empty", frame 9) _ _ _ _ 16 _ _
    ⟨by simp only [Entry.Value.erase], activation 9⟩ (by decide) ?_
  apply simple_cons "f" 2 (steps := 11) (by decide)
  apply simple_cons "f" 1 (steps := 6) (by decide)
  apply simple_cons "g" 3 (steps := 1) (by decide)
  exact .nil _ _

theorem arbitrary_saved_callers_receive_the_exact_branch_batch (live : List Atom) (scope : List String)
    (wStack : List RecursiveTasks.Frame) (cStack : List RecursiveTasks.Contextual.Continuation)
    (wEmitted : ResultSet) (cEmitted : List Completed.Result) :
    ScopedTaskRun Space.empty HE.GroundedDispatch.none Completed.Controls.typedDispatch Policy.unmarked
      (.heads arrow [] 1 heads live) (.functionBranches live scope [] cHeads)
      wStack cStack wEmitted cEmitted 24 results cResults :=
  (branch_spine live scope wStack cStack wEmitted cEmitted).task_run

def emittedPrefix : ResultSet := [(.symbol "already", Bindings.empty)]
def actualRows : Option ResultSet :=
  match (Checked.machine HE.GroundedDispatch.none scopedTypes).run 24
      ⟨Space.empty, .work (.heads arrow [] 1 heads []), [], emittedPrefix⟩ with
  | ([], .exhausted final) => match final.control with
      | .returning rows => if final.emitted == emittedPrefix then some rows else none
      | _ => none
  | _ => none

theorem actual_worker_retains_order_duplicates_records_and_emitted_prefix : actualRows = some results := by cbv

theorem actual_branch_reads_distinguish_the_reached_records :
    actualRows.map (fun rows => rows.map (fun row => row.2.applyFull (.var "x") 3)) =
      some [num 1, num 9, num 2, num 1, num 3] := by cbv

theorem value_only_deduplication_loses_required_occurrences :
    actualRows.map (fun rows => (rows.map Prod.fst).eraseDups) =
      some [.expression [.symbol "f"], .symbol "Empty", .expression [.symbol "g"]] ∧
    actualRows.map List.length = some 5 := by cbv

theorem reusing_the_first_record_changes_later_branch_reads :
    actualRows.map (fun rows => rows.map (fun _ => (bindings 1).applyFull (.var "x") 3)) =
      some [num 1, num 1, num 1, num 1, num 1] ∧
    actualRows.map (fun rows => rows.map (fun row => row.2.applyFull (.var "x") 3)) ≠
      some [num 1, num 1, num 1, num 1, num 1] := by cbv; simp

theorem a_stopped_head_is_not_an_assembled_nullary_call :
    actualRows.map (fun rows => (rows.map Prod.fst)[1]?) = some (some (.symbol "Empty")) ∧
      actualRows.map (fun rows => (rows.map Prod.fst)[1]?) ≠ some (some (.expression [.symbol "Empty"])) := by cbv; simp

theorem omitting_arrow_admission_loses_the_continuing_branches :
    (Checked.machine HE.GroundedDispatch.none scopedTypes).run 16
      ⟨Space.empty, .work (.heads (.symbol "bad-arrow") [] 1 heads []), [], emittedPrefix⟩ =
      ([], .exhausted ⟨Space.empty, .returning [(.symbol "Empty", bindings 9)], [], emittedPrefix⟩) := by cbv

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFunctionBranchControls
