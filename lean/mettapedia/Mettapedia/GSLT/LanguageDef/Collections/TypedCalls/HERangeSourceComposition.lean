import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeUntypedEntry
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeWorldEntry

/-!
# Composing actual range and conditional source calls

These two composition rules earn complete source frontiers and fresh frames.
Their induction premises concern the reached branch/body under that frame,
never a successful run of the enclosing call or a supplied result array.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeSourceComposition

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Eval.Steps
open Spec.Type.Presentation
open HERangeSourceProgram (space environment)
open HERangeSuperposeSource (NumericOrEmpty)
open HEIfSourceSelection (signature)
open HEIfSourceSelection.Range (yes no)
open HEFreshEquationFrames.Range (number bodyAt)

def body (lower upper : Int) : Entry.Value := Entry.Value.ofAtom (bodyAt (number lower) (number upper))
def branch (lower upper : Int) : Entry.Value :=
  if lower ≥ upper then Entry.Value.ofAtom yes else Entry.Value.ofAtom (no lower upper)

theorem body_read (policy : Policy) (before : Frame) (lower upper : Int) :
    before.read policy (body lower upper) = body lower upper := by
  apply HEFreshSyntaxBinding.ground_substitution
  simp [body, Entry.Value.erase_ofAtom, bodyAt, number, TypeSubst.typeVars, TypeSubst.typeVarsList]

theorem if_source_of_branch_world {World : Type} (ports : HERangeWorldProtocol.Ports World) (world : World) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (lower upper : Int) (expected : Atom)
    (demand : expected = .symbol "Number" ∨ expected = Atom.undefinedType) (values : List Entry.Value)
    (branchRun : ∀ (name : String) (frame : Frame), ∃ rows : List Result,
      Stateful.AtomRel ports.environment ports.label world live scope (branch lower upper) (.var name) frame rows world (policy := policy) ∧
      (∀ row ∈ rows, NumericOrEmpty row.1) ∧ rows.map Prod.fst = values) :
    ∃ rows : List Result,
      Stateful.AtomRel ports.environment ports.label world live scope (body lower upper) expected before rows world (policy := policy) ∧
      (∀ row ∈ rows, NumericOrEmpty row.1) ∧ rows.map Prod.fst = values := by
  obtain ⟨name, selected, callFrame, selectedRun, functionRun⟩ :=
    ports.conditional world policy before live scope lower upper expected demand
  have returnedType : invocationReturnType (signature name) = .var name := by
    simp [signature, invocationReturnType, Atom.expressionType]
  obtain ⟨work, branchFrame, frontier, bound, unified, read⟩ :=
    ports.conditionalFrontier world policy (.var name :: live) callFrame (decide (lower ≥ upper))
      (Entry.Value.ofAtom yes) (Entry.Value.ofAtom (no lower upper))
      (by simp [Entry.Value.erase_ofAtom, yes, TypeSubst.typeVars, TypeSubst.typeVarsList])
      (by simp [Entry.Value.erase_ofAtom, no, number, TypeSubst.typeVars, TypeSubst.typeVarsList])
  have bodyRead : branchFrame.read policy (Entry.Value.ofAtom work.body) = branch lower upper := by
    simpa only [branch, decide_eq_true_eq] using read
  obtain ⟨rows, branchSource, numeric, observed⟩ := branchRun name branchFrame
  have producer : Stateful.BoundaryRel ports.environment ports.label world (.var name :: live) scope
      (some (HEIfSourceActivation.reachedCall lower upper).erase) .producer
      (branchFrame.read policy (Entry.Value.ofAtom work.body)) branchFrame [(branch lower upper, branchFrame)] world
      (policy := policy) := by
    rw [bodyRead]
    apply Stateful.BoundaryRel.producerRaw
    by_cases test : lower ≥ upper <;>
      simp [branch, test, yes, no, FunctionPending, Minimal.IsFunction, Entry.Value.erase_ofAtom]
  have returned : Stateful.BoundaryBatchRel ports.environment ports.label world live scope none
      (.returned (HEIfSourceActivation.reachedCall lower upper) (.var name))
      [(branch lower upper, branchFrame)] rows world (policy := policy) := by
    apply Stateful.BoundaryBatchRel.single_iff.mpr
    apply Stateful.BoundaryRel.returned
    apply Stateful.ReturnRel.evaluate
    · by_cases test : lower ≥ upper <;> simp [branch, test, yes, no, Entry.Value.erase_ofAtom, Atom.notReducible]
    · by_cases test : lower ≥ upper <;> simp [branch, test, yes, no, Entry.Value.erase_ofAtom, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
    · exact branchSource
  have called : Stateful.CallRel ports.environment ports.label world live scope (HEIfSourceActivation.reachedCall lower upper)
      (.var name) callFrame rows world (policy := policy) := by
    apply Stateful.CallRel.equations (works := [work])
    · simp [HEIfSourceActivation.reachedCall, Entry.Value.erase, IsErrorRel]
    · simpa only [HEIfSourceActivation.reachedCall, Entry.Value.erase, Entry.Value.erase_ofAtom, List.map_cons, List.map_nil] using
        ports.ordinary "if" [.grounded (.bool (decide (lower ≥ upper))), yes, no lower upper] (by simp)
    · simpa only [HEIfSourceActivation.reachedCall, HEConditionalEquationFrames.query] using frontier
    · simp
    · simpa only [List.append_nil, HEIfSourceActivation.reachedCall, HEConditionalEquationFrames.query] using
        Stateful.EquationBodiesRel.cons bound unified producer returned Stateful.EquationBodiesRel.nil
  have calls : Stateful.CallsRel ports.environment ports.label world live scope (invocationReturnType (signature name))
      [(HEIfSourceActivation.reachedCall lower upper, callFrame)] rows world (policy := policy) := by
    rw [returnedType]
    simpa only [List.append_nil] using Stateful.CallsRel.cons called Stateful.CallsRel.nil
  have invocations : Stateful.InvocationsRel ports.environment ports.label world live scope expected (signature name)
      (.symbol "if") (HEIfSourceActivation.operands lower upper) [selected] rows world (policy := policy) := by
    simpa only [List.append_nil] using Stateful.InvocationsRel.cons functionRun calls Stateful.InvocationsRel.nil
  have priority : Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
      (fun row : Result => isErrorAtom row.1.erase) (rows.map (readResult policy)) rows := by
    rw [HERangeSuperposeSource.numeric_reads policy _ numeric]
    exact HERangeSuperposeSource.numeric_priority _ numeric
  have complete : Stateful.AtomRel ports.environment ports.label world live scope (body lower upper) expected before
      (rows.map (publishResult policy (before.read policy (body lower upper)).erase)) world (policy := policy) := by
    apply Stateful.AtomRel.function (operator := .symbol "if") (arguments := HEIfSourceActivation.operands lower upper)
      (signature := signature name) (frames := [selected]) (raw := rows) (readiness := .active)
    · rw [body_read]
      simp only [body, bodyAt, Entry.Value.ofAtom, List.map_cons, List.map_nil, Entry.Value.status, Entry.Value.erase]
      apply Entry.Rel.expression
      · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
      · rcases demand with rfl | rfl <;> decide
      · exact Or.inr rfl
    · rw [body_read]
      simp [body, bodyAt, HEIfSourceActivation.operands, HEIfSourceSelection.Range.condition, yes, no, Entry.Value.ofAtom]
    · rw [body_read]
      simpa only [body, Entry.Value.erase_ofAtom, Entry.Value.erase] using selectedRun
    · exact invocations
    · exact priority
  exact ⟨rows, by simpa only [HERangeSuperposeSource.numeric_publishes policy _ _ numeric] using complete, numeric, observed⟩

theorem if_source_of_branch_for (ports : HERangeSourceProtocol.Ports) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (lower upper : Int) (expected : Atom)
    (demand : expected = .symbol "Number" ∨ expected = Atom.undefinedType) (values : List Entry.Value)
    (branchRun : ∀ (name : String) (frame : Frame), ∃ rows : List Result,
      Stateful.AtomRel ports.environment space () live scope (branch lower upper) (.var name) frame rows () (policy := policy) ∧
      (∀ row ∈ rows, NumericOrEmpty row.1) ∧ rows.map Prod.fst = values) :
    ∃ rows : List Result,
      Stateful.AtomRel ports.environment space () live scope (body lower upper) expected before rows () (policy := policy) ∧
      (∀ row ∈ rows, NumericOrEmpty row.1) ∧ rows.map Prod.fst = values :=
  if_source_of_branch_world (HERangeWorldProtocol.ofIsolated ports) () policy before live scope lower upper expected demand values branchRun

theorem if_source_of_branch (minimal : Minimal.Services) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (lower upper : Int) (expected : Atom)
    (demand : expected = .symbol "Number" ∨ expected = Atom.undefinedType) (values : List Entry.Value)
    (branchRun : ∀ (name : String) (frame : Frame), ∃ rows : List Result,
      Stateful.AtomRel (environment minimal) space () live scope (branch lower upper) (.var name) frame rows () (policy := policy) ∧
      (∀ row ∈ rows, NumericOrEmpty row.1) ∧ rows.map Prod.fst = values) :
    ∃ rows : List Result,
      Stateful.AtomRel (environment minimal) space () live scope (body lower upper) expected before rows () (policy := policy) ∧
      (∀ row ∈ rows, NumericOrEmpty row.1) ∧ rows.map Prod.fst = values :=
  if_source_of_branch_for (HERangeSourceProtocol.historical minimal) policy before live scope lower upper expected demand values branchRun

theorem range_call_of_body_world {World : Type} (ports : HERangeWorldProtocol.Ports World) (world : World) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (lower upper : Int) (expected : Atom) (values : List Entry.Value)
    (bodyRun : ∀ frame : Frame, ∃ rows : List Result,
      Stateful.AtomRel ports.environment ports.label world live scope (body lower upper) expected frame rows world (policy := policy) ∧
      (∀ row ∈ rows, NumericOrEmpty row.1) ∧ rows.map Prod.fst = values) :
    ∃ rows : List Result,
      Stateful.CallRel ports.environment ports.label world live scope (HERangeUntypedEntry.rangeCall lower upper) expected before rows world
        (policy := policy) ∧ (∀ row ∈ rows, NumericOrEmpty row.1) ∧ rows.map Prod.fst = values := by
  obtain ⟨work, after, frontier, bound, unified, read⟩ :=
    ports.rangeFrontier world policy (expected :: live) before lower upper
  obtain ⟨rows, evaluated, numeric, observed⟩ := bodyRun after
  have producer : Stateful.BoundaryRel ports.environment ports.label world (expected :: live) scope
      (some (HERangeUntypedEntry.rangeCall lower upper).erase) .producer
      (after.read policy (Entry.Value.ofAtom work.body)) after [(body lower upper, after)] world (policy := policy) := by
    rw [read]
    apply Stateful.BoundaryRel.producerRaw
    simp [FunctionPending, Minimal.IsFunction, bodyAt, Entry.Value.erase_ofAtom]
  have returned : Stateful.BoundaryBatchRel ports.environment ports.label world live scope none
      (.returned (HERangeUntypedEntry.rangeCall lower upper) expected) [(body lower upper, after)] rows world (policy := policy) := by
    apply Stateful.BoundaryBatchRel.single_iff.mpr
    exact .returned (.evaluate (by simp [body, bodyAt, Entry.Value.erase_ofAtom, Atom.notReducible])
      (by simp [body, bodyAt, Entry.Value.erase_ofAtom, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) evaluated)
  refine ⟨rows, ?_, numeric, observed⟩
  apply Stateful.CallRel.equations (works := [work])
  · simp [HERangeUntypedEntry.rangeCall, Entry.Value.erase, IsErrorRel]
  · simpa only [HERangeUntypedEntry.rangeCall, Entry.Value.erase, List.map_cons, List.map_nil, number] using
      ports.ordinary "range" [number lower, number upper] (by simp)
  · simpa only [HERangeUntypedEntry.rangeCall, Entry.Value.erase,
      List.map_cons, List.map_nil, HEFreshEquationFrames.Range.call, number] using frontier
  · simp
  · have unified' : Entry.Value.UnifyRel policy.rebuilding before.environment (HERangeUntypedEntry.rangeCall lower upper)
        (Entry.Value.ofAtom work.pattern) after.environment := by
      simpa only [HERangeUntypedEntry.rangeCall, HEFreshEquationFrames.Range.call, number, Entry.Value.ofAtom, List.map_cons, List.map_nil] using unified
    simpa only [List.append_nil] using
      Stateful.EquationBodiesRel.cons bound unified' producer returned Stateful.EquationBodiesRel.nil

theorem range_call_of_body_for (ports : HERangeSourceProtocol.Ports) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (lower upper : Int) (expected : Atom) (values : List Entry.Value)
    (bodyRun : ∀ frame : Frame, ∃ rows : List Result,
      Stateful.AtomRel ports.environment space () live scope (body lower upper) expected frame rows () (policy := policy) ∧
      (∀ row ∈ rows, NumericOrEmpty row.1) ∧ rows.map Prod.fst = values) :
    ∃ rows : List Result,
      Stateful.CallRel ports.environment space () live scope (HERangeUntypedEntry.rangeCall lower upper) expected before rows ()
        (policy := policy) ∧ (∀ row ∈ rows, NumericOrEmpty row.1) ∧ rows.map Prod.fst = values :=
  range_call_of_body_world (HERangeWorldProtocol.ofIsolated ports) () policy before live scope lower upper expected values bodyRun

theorem range_call_of_body (minimal : Minimal.Services) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (lower upper : Int) (expected : Atom) (values : List Entry.Value)
    (bodyRun : ∀ frame : Frame, ∃ rows : List Result,
      Stateful.AtomRel (environment minimal) space () live scope (body lower upper) expected frame rows () (policy := policy) ∧
      (∀ row ∈ rows, NumericOrEmpty row.1) ∧ rows.map Prod.fst = values) :
    ∃ rows : List Result,
      Stateful.CallRel (environment minimal) space () live scope (HERangeUntypedEntry.rangeCall lower upper) expected before rows ()
        (policy := policy) ∧ (∀ row ∈ rows, NumericOrEmpty row.1) ∧ rows.map Prod.fst = values :=
  range_call_of_body_for (HERangeSourceProtocol.historical minimal) policy before live scope lower upper expected values bodyRun

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeSourceComposition
