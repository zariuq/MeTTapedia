import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeSourceComposition

/-!
# Authored recursive range source-to-frontier adequacy

The reference observation is an ordinary finite integer interval followed by
the terminal Empty occurrence. Source recursion, fresh equation/type frames,
arithmetic, conditional selection and Undefined-demanded superpose children
are all derived. No successful body or finished frontier is assumed.

One induction consumes earned local source ports, never a recursive result
or a completed body oracle. Historical wrappers retain the stored-type
profile; other checked type-service instances use the same induction.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeSourceAdequacy

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed
open Spec.Type.Presentation
open HERangeSourceProgram (space environment)
open HERangeSuperposeSource (NumericOrEmpty)
open HERangeSourceComposition (body branch)

def values (lower : Int) (count : Nat) : List Entry.Value :=
  (List.range count).map fun (index : Nat) => .grounded (.int (lower + (index : Int)))

theorem values_zero (lower : Int) : values lower 0 = [] := rfl

theorem values_succ (lower : Int) (count : Nat) :
    values lower (count + 1) = .grounded (.int lower) :: values (lower + 1) count := by
  simp [values, List.range_succ_eq_map, Function.comp_def, Int.add_left_comm, Int.add_comm]

theorem empty_range_world {World : Type} (ports : HERangeWorldProtocol.Ports World) (world : World) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (lower upper : Int) (expected : Atom)
    (demand : expected = .symbol "Number" ∨ expected = Atom.undefinedType) (stopped : upper ≤ lower) :
    ∃ rows : List Result,
      Stateful.CallRel ports.environment ports.label world live scope (HERangeUntypedEntry.rangeCall lower upper) expected before rows world
        (policy := policy) ∧ (∀ row ∈ rows, NumericOrEmpty row.1) ∧ rows.map Prod.fst = [.symbol "Empty"] := by
  apply HERangeSourceComposition.range_call_of_body_world ports world policy before live scope lower upper expected [.symbol "Empty"]
  intro after
  apply HERangeSourceComposition.if_source_of_branch_world ports world policy after live scope lower upper expected demand [.symbol "Empty"]
  intro name frame
  refine ⟨[(.symbol "Empty", frame)], ?_, ?_, rfl⟩
  · simpa [branch, stopped, HERangeEquationFrontiers.emptyCall, HERangeSourceProgram.emptyPattern,
      HEIfSourceSelection.Range.yes] using
      HERangeWorldEntry.empty_atom ports world policy frame live scope (.var name)
        (by simp [Atom.atomType]) (by simp [Atom.expressionType])
  · intro row member
    cases List.mem_singleton.mp member
    exact .empty

theorem empty_range_for (ports : HERangeSourceProtocol.Ports) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (lower upper : Int) (expected : Atom)
    (demand : expected = .symbol "Number" ∨ expected = Atom.undefinedType) (stopped : upper ≤ lower) :
    ∃ rows : List Result,
      Stateful.CallRel ports.environment space () live scope (HERangeUntypedEntry.rangeCall lower upper) expected before rows ()
        (policy := policy) ∧ (∀ row ∈ rows, NumericOrEmpty row.1) ∧ rows.map Prod.fst = [.symbol "Empty"] :=
  empty_range_world (HERangeWorldProtocol.ofIsolated ports) () policy before live scope lower upper expected demand stopped

theorem empty_range (minimal : Minimal.Services) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (lower upper : Int) (expected : Atom)
    (demand : expected = .symbol "Number" ∨ expected = Atom.undefinedType) (stopped : upper ≤ lower) :
    ∃ rows : List Result,
      Stateful.CallRel (environment minimal) space () live scope (HERangeUntypedEntry.rangeCall lower upper) expected before rows ()
        (policy := policy) ∧ (∀ row ∈ rows, NumericOrEmpty row.1) ∧ rows.map Prod.fst = [.symbol "Empty"] :=
  empty_range_for (HERangeSourceProtocol.historical minimal) policy before live scope lower upper expected demand stopped

/-- The induction parameter is the mathematical interval length, not an
assumption that the program terminates or that its body implements range. -/
theorem counted_range_world {World : Type} (ports : HERangeWorldProtocol.Ports World) (world : World) (policy : Policy) (count : Nat)
    (before : Frame) (live : List Atom) (scope : List String) (lower : Int) (expected : Atom)
    (demand : expected = .symbol "Number" ∨ expected = Atom.undefinedType) :
    ∃ rows : List Result,
      Stateful.CallRel ports.environment ports.label world live scope
        (HERangeUntypedEntry.rangeCall lower (lower + (count : Int))) expected before rows world (policy := policy) ∧
      (∀ row ∈ rows, NumericOrEmpty row.1) ∧ rows.map Prod.fst = values lower count ++ [.symbol "Empty"] := by
  induction count generalizing before live scope lower expected with
  | zero =>
      simpa [values] using empty_range_world ports world policy before live scope lower lower expected demand (le_refl lower)
  | succ count ih =>
      let upper : Int := lower + ((count + 1 : Nat) : Int)
      have progressing : ¬lower ≥ upper := by dsimp [upper]; omega
      change ∃ rows : List Result,
        Stateful.CallRel ports.environment ports.label world live scope
          (HERangeUntypedEntry.rangeCall lower upper) expected before rows world (policy := policy) ∧
        (∀ row ∈ rows, NumericOrEmpty row.1) ∧ rows.map Prod.fst = values lower (count + 1) ++ [Entry.Value.symbol "Empty"]
      apply HERangeSourceComposition.range_call_of_body_world ports world policy before live scope lower upper expected
        (values lower (count + 1) ++ [Entry.Value.symbol "Empty"])
      intro after
      apply HERangeSourceComposition.if_source_of_branch_world ports world policy after live scope lower upper expected demand
        (values lower (count + 1) ++ [Entry.Value.symbol "Empty"])
      intro name frame
      have upperEq : (lower + 1) + (count : Int) = upper := by dsimp [upper]; omega
      obtain ⟨rest, recurred, restNumeric, restObserved⟩ := ih frame live scope (lower + 1) Atom.undefinedType (Or.inr rfl)
      rw [upperEq] at recurred
      let next := HERangeUntypedEntry.rangeInput (HEBinaryNumericSource.addition.call lower 1) upper
      have recursiveSource : Stateful.AtomRel ports.environment ports.label world live scope next Atom.undefinedType frame rest world
          (policy := policy) :=
        HERangeWorldEntry.incremented_range_atom ports world policy frame live scope lower upper rest recurred restNumeric
      have numeric : ∀ row ∈ (Entry.Value.grounded (.int lower), frame) :: rest, NumericOrEmpty row.1 := by
        intro row member
        rcases List.mem_cons.mp member with rfl | later
        · exact .number lower
        · exact restNumeric row later
      have children : List.Forall₂ (fun item rows =>
          ¬FunctionPending policy item ∧ item.erase ≠ Atom.notReducible ∧ ¬IsEmptyOrErrorRel item.erase ∧
          Stateful.AtomRel ports.environment ports.label world live scope item Atom.undefinedType frame rows world (policy := policy))
          [.grounded (.int lower), next] [[(.grounded (.int lower), frame)], rest] := by
        refine .cons ⟨?_, ?_, ?_, ports.number world policy frame live scope lower⟩
          (.cons ⟨?_, ?_, ?_, recursiveSource⟩ .nil)
        all_goals simp [next, HERangeUntypedEntry.rangeInput, FunctionPending, Minimal.IsFunction,
          Entry.Value.erase, Atom.notReducible, IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
      have combined := ports.superpose world policy frame live scope
        [.grounded (.int lower), next] [[(.grounded (.int lower), frame)], rest] (.var name)
        (by simp [Atom.atomType]) (by simp [Atom.expressionType])
        (by simp [next, HERangeUntypedEntry.rangeInput, HEBinaryNumericSource.Operation.call,
          Entry.Value.erase, TypeSubst.typeVarsList, TypeSubst.typeVars])
        (by simp) children (by simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, List.singleton_append] using numeric)
      refine ⟨(.grounded (.int lower), frame) :: rest, ?_, numeric, ?_⟩
      · simpa [branch, progressing, HEIfSourceSelection.Range.no, HEFreshEquationFrames.Range.number,
          HERangeSuperposeSource.call, next, HERangeUntypedEntry.rangeInput, HEBinaryNumericSource.Operation.call,
          HEBinaryNumericSource.addition, Entry.Value.ofAtom] using combined
      · rw [List.map_cons, restObserved, values_succ]
        rfl

theorem counted_range_for (ports : HERangeSourceProtocol.Ports) (policy : Policy) (count : Nat)
    (before : Frame) (live : List Atom) (scope : List String) (lower : Int) (expected : Atom)
    (demand : expected = .symbol "Number" ∨ expected = Atom.undefinedType) :
    ∃ rows : List Result,
      Stateful.CallRel ports.environment space () live scope
        (HERangeUntypedEntry.rangeCall lower (lower + (count : Int))) expected before rows () (policy := policy) ∧
      (∀ row ∈ rows, NumericOrEmpty row.1) ∧ rows.map Prod.fst = values lower count ++ [.symbol "Empty"] :=
  counted_range_world (HERangeWorldProtocol.ofIsolated ports) () policy count before live scope lower expected demand

theorem counted_range (minimal : Minimal.Services) (policy : Policy) (count : Nat)
    (before : Frame) (live : List Atom) (scope : List String) (lower : Int) (expected : Atom)
    (demand : expected = .symbol "Number" ∨ expected = Atom.undefinedType) :
    ∃ rows : List Result,
      Stateful.CallRel (environment minimal) space () live scope
        (HERangeUntypedEntry.rangeCall lower (lower + (count : Int))) expected before rows () (policy := policy) ∧
      (∀ row ∈ rows, NumericOrEmpty row.1) ∧ rows.map Prod.fst = values lower count ++ [.symbol "Empty"] :=
  counted_range_for (HERangeSourceProtocol.historical minimal) policy count before live scope lower expected demand

/-- Arbitrary finite integer bounds, including descending and empty
intervals. Frame identities are not erased from the actual source result. -/
theorem range_call_world {World : Type} (ports : HERangeWorldProtocol.Ports World) (world : World) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (lower upper : Int) (expected : Atom)
    (demand : expected = .symbol "Number" ∨ expected = Atom.undefinedType) :
    ∃ rows : List Result,
      Stateful.CallRel ports.environment ports.label world live scope (HERangeUntypedEntry.rangeCall lower upper) expected before rows world
        (policy := policy) ∧ (∀ row ∈ rows, NumericOrEmpty row.1) ∧
      rows.map Prod.fst = values lower (upper - lower).toNat ++ [.symbol "Empty"] := by
  by_cases stopped : upper ≤ lower
  · have zero : (upper - lower).toNat = 0 := by omega
    simpa only [zero, values_zero, List.nil_append] using empty_range_world ports world policy before live scope lower upper expected demand stopped
  · have upperEq : lower + ((upper - lower).toNat : Int) = upper := by omega
    simpa only [upperEq] using counted_range_world ports world policy (upper - lower).toNat before live scope lower expected demand

theorem range_call_for (ports : HERangeSourceProtocol.Ports) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (lower upper : Int) (expected : Atom)
    (demand : expected = .symbol "Number" ∨ expected = Atom.undefinedType) :
    ∃ rows : List Result,
      Stateful.CallRel ports.environment space () live scope (HERangeUntypedEntry.rangeCall lower upper) expected before rows ()
        (policy := policy) ∧ (∀ row ∈ rows, NumericOrEmpty row.1) ∧
      rows.map Prod.fst = values lower (upper - lower).toNat ++ [.symbol "Empty"] :=
  range_call_world (HERangeWorldProtocol.ofIsolated ports) () policy before live scope lower upper expected demand

theorem range_call (minimal : Minimal.Services) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (lower upper : Int) (expected : Atom)
    (demand : expected = .symbol "Number" ∨ expected = Atom.undefinedType) :
    ∃ rows : List Result,
      Stateful.CallRel (environment minimal) space () live scope (HERangeUntypedEntry.rangeCall lower upper) expected before rows ()
        (policy := policy) ∧ (∀ row ∈ rows, NumericOrEmpty row.1) ∧
      rows.map Prod.fst = values lower (upper - lower).toNat ++ [.symbol "Empty"] :=
  range_call_for (HERangeSourceProtocol.historical minimal) policy before live scope lower upper expected demand

theorem range_source_world {World : Type} (ports : HERangeWorldProtocol.Ports World) (world : World) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (lower upper : Int) (expected : Atom)
    (demand : expected = .symbol "Number" ∨ expected = Atom.undefinedType) :
    ∃ rows : List Result,
      Stateful.AtomRel ports.environment ports.label world live scope (HERangeUntypedEntry.rangeCall lower upper) expected before rows world
        (policy := policy) ∧ (∀ row ∈ rows, NumericOrEmpty row.1) ∧
      rows.map Prod.fst = values lower (upper - lower).toNat ++ [.symbol "Empty"] := by
  obtain ⟨rows, called, numeric, observed⟩ := range_call_world ports world policy before live scope lower upper expected demand
  have notAtom : expected ≠ Atom.atomType := by rcases demand with rfl | rfl <;> decide
  have notExpression : expected ≠ Atom.expressionType := by rcases demand with rfl | rfl <;> decide
  exact ⟨rows, HERangeWorldEntry.ground_range_atom ports world policy before live scope lower upper expected rows
    notAtom notExpression called numeric, numeric, observed⟩

theorem range_source_for (ports : HERangeSourceProtocol.Ports) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (lower upper : Int) (expected : Atom)
    (demand : expected = .symbol "Number" ∨ expected = Atom.undefinedType) :
    ∃ rows : List Result,
      Stateful.AtomRel ports.environment space () live scope (HERangeUntypedEntry.rangeCall lower upper) expected before rows ()
        (policy := policy) ∧ (∀ row ∈ rows, NumericOrEmpty row.1) ∧
      rows.map Prod.fst = values lower (upper - lower).toNat ++ [.symbol "Empty"] :=
  range_source_world (HERangeWorldProtocol.ofIsolated ports) () policy before live scope lower upper expected demand

theorem range_source (minimal : Minimal.Services) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (lower upper : Int) (expected : Atom)
    (demand : expected = .symbol "Number" ∨ expected = Atom.undefinedType) :
    ∃ rows : List Result,
      Stateful.AtomRel (environment minimal) space () live scope (HERangeUntypedEntry.rangeCall lower upper) expected before rows ()
        (policy := policy) ∧ (∀ row ∈ rows, NumericOrEmpty row.1) ∧
      rows.map Prod.fst = values lower (upper - lower).toNat ++ [.symbol "Empty"] :=
  range_source_for (HERangeSourceProtocol.historical minimal) policy before live scope lower upper expected demand

/-- The actual source derivation reaches the existing contextual worker's
return boundary, with the caller stack and already emitted prefix retained. -/
theorem retained_run_world {World : Type} (ports : HERangeWorldProtocol.Ports World) (world : World) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (lower upper : Int) (expected : Atom)
    (demand : expected = .symbol "Number" ∨ expected = Atom.undefinedType)
    (stack : List RecursiveTasks.Contextual.Continuation) (emitted : List Result) :
    ∃ rows : List Result,
      RecursiveMachine.Contextual.WorldSteps (admission := ports.environment.arguments) ports.environment.view ports.environment.services
        ports.environment.dispatch ports.environment.lookup policy
        ⟨world, ports.label, .work (.atom live scope (HERangeUntypedEntry.rangeCall lower upper) expected before), stack, emitted⟩
        ⟨world, ports.label, .returning rows, stack, emitted⟩ ∧
      rows.map Prod.fst = values lower (upper - lower).toNat ++ [.symbol "Empty"] ∧
      (∀ row ∈ rows, isErrorAtom row.1.erase = false) ∧ rows.length = (upper - lower).toNat + 1 := by
  obtain ⟨rows, source, numeric, observed⟩ := range_source_world ports world policy before live scope lower upper expected demand
  refine ⟨rows, RecursiveExecution.Contextual.Stateful.local_steps_lift
    (RecursiveExecution.Contextual.Stateful.task_complete
      (task := .atom live scope (HERangeUntypedEntry.rangeCall lower upper) expected before) source stack) emitted,
    observed, fun row member => HERangeSuperposeSource.no_error (numeric row member), ?_⟩
  have length := congrArg List.length observed
  simpa [values] using length

theorem retained_run_for (ports : HERangeSourceProtocol.Ports) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (lower upper : Int) (expected : Atom)
    (demand : expected = .symbol "Number" ∨ expected = Atom.undefinedType)
    (stack : List RecursiveTasks.Contextual.Continuation) (emitted : List Result) :
    ∃ rows : List Result,
      RecursiveMachine.Contextual.WorldSteps (admission := ports.environment.arguments) ports.environment.view ports.environment.services
        ports.environment.dispatch ports.environment.lookup policy
        ⟨(), space, .work (.atom live scope (HERangeUntypedEntry.rangeCall lower upper) expected before), stack, emitted⟩
        ⟨(), space, .returning rows, stack, emitted⟩ ∧
      rows.map Prod.fst = values lower (upper - lower).toNat ++ [.symbol "Empty"] ∧
      (∀ row ∈ rows, isErrorAtom row.1.erase = false) ∧ rows.length = (upper - lower).toNat + 1 :=
  retained_run_world (HERangeWorldProtocol.ofIsolated ports) () policy before live scope lower upper expected demand stack emitted

theorem retained_run (minimal : Minimal.Services) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (lower upper : Int) (expected : Atom)
    (demand : expected = .symbol "Number" ∨ expected = Atom.undefinedType)
    (stack : List RecursiveTasks.Contextual.Continuation) (emitted : List Result) :
    ∃ rows : List Result,
      RecursiveMachine.Contextual.WorldSteps (environment minimal).view (environment minimal).services
        (environment minimal).dispatch (environment minimal).lookup policy
        ⟨(), space, .work (.atom live scope (HERangeUntypedEntry.rangeCall lower upper) expected before), stack, emitted⟩
        ⟨(), space, .returning rows, stack, emitted⟩ ∧
      rows.map Prod.fst = values lower (upper - lower).toNat ++ [.symbol "Empty"] ∧
      (∀ row ∈ rows, isErrorAtom row.1.erase = false) ∧ rows.length = (upper - lower).toNat + 1 :=
  retained_run_for (HERangeSourceProtocol.historical minimal) policy before live scope lower upper expected demand stack emitted

theorem surviving_readout (rows : List Result) :
    (survivingRows rows).map Prod.fst = (rows.map Prod.fst).filter (fun value => value.erase != Atom.empty) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [survivingRows] at ih
      by_cases missing : row.1.erase = Atom.empty <;> simp [survivingRows, missing, ih]

/-- This is the existing capture observer's exact visible value list.
It is not a claim that the standard-library collapse fold has been lowered. -/
theorem capture_values (lower : Int) (count : Nat) (rows : List Result)
    (observed : rows.map Prod.fst = values lower count ++ [.symbol "Empty"]) :
    (survivingRows rows).map Prod.fst = values lower count := by
  rw [surviving_readout, observed, List.filter_append]
  have keep : (values lower count).filter (fun value => value.erase != Atom.empty) = values lower count := by
    apply List.filter_eq_self.mpr
    intro value member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    simp [Entry.Value.erase, Atom.empty]
  rw [keep]
  simp [Entry.Value.erase, Atom.empty]

theorem capture_source (minimal : Minimal.Services) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (lower upper : Int) (expected : Atom)
    (demand : expected = .symbol "Number" ∨ expected = Atom.undefinedType) :
    ∃ rows : List Result,
      Stateful.AtomRel (environment minimal) space () live scope (HERangeUntypedEntry.rangeCall lower upper) expected before rows ()
        (policy := policy) ∧ rows.map Prod.fst = values lower (upper - lower).toNat ++ [.symbol "Empty"] ∧
      (survivingRows rows).map Prod.fst = values lower (upper - lower).toNat := by
  obtain ⟨rows, source, _, observed⟩ := range_source minimal policy before live scope lower upper expected demand
  exact ⟨rows, source, observed, capture_values _ _ _ observed⟩

namespace Controls

theorem crosses_zero_with_saved_alias (minimal : Minimal.Services) (policy : Policy) :
    ∃ rows : List Result,
      Stateful.AtomRel (environment minimal) space () [.var "x", .var "y"] ["x", "y"]
        (HERangeUntypedEntry.rangeCall (-2) 2) Atom.undefinedType Completed.Controls.argumentAliasFrame rows () (policy := policy) ∧
      rows.map Prod.fst = [.grounded (.int (-2)), .grounded (.int (-1)), .grounded (.int 0), .grounded (.int 1), .symbol "Empty"] := by
  obtain ⟨rows, source, _, observed⟩ := range_source minimal policy Completed.Controls.argumentAliasFrame
    [.var "x", .var "y"] ["x", "y"] (-2) 2 Atom.undefinedType (Or.inr rfl)
  exact ⟨rows, source, by simpa [values, List.range_succ] using observed⟩

theorem terminal_empty_is_not_no_result (lower : Int) (count : Nat) :
    values lower count ++ [Entry.Value.symbol "Empty"] ≠ values lower count := by
  intro same
  have length := congrArg List.length same
  simp at length

/-- Actual mutated branch: replacing the recursive child by the real empty
call yields just the first number and Empty, not the full interval. -/
theorem cut_recursion_source (minimal : Minimal.Services) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (lower : Int) :
    Stateful.AtomRel (environment minimal) space () live scope
      (HERangeSuperposeSource.call [.grounded (.int lower), HERangeEquationFrontiers.emptyCall]) Atom.undefinedType before
      [(.grounded (.int lower), before), (.symbol "Empty", before)] () (policy := policy) := by
  have children : List.Forall₂ (fun item rows =>
      ¬FunctionPending policy item ∧ item.erase ≠ Atom.notReducible ∧ ¬IsEmptyOrErrorRel item.erase ∧
      Stateful.AtomRel (environment minimal) space () live scope item Atom.undefinedType before rows () (policy := policy))
      [.grounded (.int lower), HERangeEquationFrontiers.emptyCall]
      [[(.grounded (.int lower), before)], [(.symbol "Empty", before)]] := by
    refine .cons ⟨?_, ?_, ?_, HERangeSuperposeSource.number_undefined minimal policy before live scope lower⟩
      (.cons ⟨?_, ?_, ?_, HERangeUntypedEntry.empty_atom minimal policy before live scope Atom.undefinedType (by decide) (by decide)⟩ .nil)
    all_goals simp [HERangeEquationFrontiers.emptyCall, HERangeSourceProgram.emptyPattern,
      Entry.Value.erase_ofAtom, Entry.Value.erase, FunctionPending, Minimal.IsFunction, Atom.notReducible,
      IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
  simpa only [List.flatten_cons, List.flatten_nil, List.append_nil, List.singleton_append] using
    HERangeSuperposeSource.source minimal policy before live scope
      [.grounded (.int lower), HERangeEquationFrontiers.emptyCall]
      [[(.grounded (.int lower), before)], [(.symbol "Empty", before)]] Atom.undefinedType (by decide) (by decide)
      (by simp [HERangeEquationFrontiers.emptyCall, HERangeSourceProgram.emptyPattern, Entry.Value.erase_ofAtom,
        Entry.Value.erase, TypeSubst.typeVarsList, TypeSubst.typeVars]) (by simp) children
      (by
        intro row member
        simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.singleton_append,
          List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact .number lower
        · exact .empty)

theorem cut_recursion_loses_second_number (lower : Int) :
    values lower 2 ++ [Entry.Value.symbol "Empty"] ≠
      [Entry.Value.grounded (.int lower), Entry.Value.symbol "Empty"] := by
  intro same
  have length := congrArg List.length same
  simp [values] at length

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeSourceAdequacy
