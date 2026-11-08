import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeSuperposeSource
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeEquationFrontiers
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeSourceProtocol
import Mettapedia.Languages.MeTTa.HE.ArgumentAdmission

/-!
# Actual untyped entry into the authored range equations

The head and operands follow the existing tuple fallback, including the real
addition in a recursive call. Only the reached ground equation-call derivation
is supplied by recursive induction; the authored call is not replaced by it.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeUntypedEntry

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed
open Spec.Type Spec.Type.Presentation
open HERangeSourceProgram (space environment)
open HERangeSuperposeSource (NumericOrEmpty)
open HERangeSourceProtocol (Ports)

theorem symbol_undefined_of_query {World : Type} (current : WorldEnvironment Space World)
    (label : Space) (world : World) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (name : String) (notEmpty : name ≠ "Empty")
    (queried : current.lookup (invocationTypeScope scope live (.symbol name) Atom.undefinedType before.bindings)
      (current.view world label) before.bindings (.symbol name) Atom.undefinedType [Atom.undefinedType]) :
    Stateful.AtomRel current label world live scope (.symbol name) Atom.undefinedType before
      [(.symbol name, before)] world (policy := policy) := by
  have read : before.read policy (.symbol name) = .symbol name := by simp [Frame.read, Entry.Value.substitute]
  apply Stateful.AtomRel.cast (raw := [(.symbol name, before.bindings)])
  · rw [read]
    apply Entry.Rel.cast (metaType := Atom.symbolType)
    · simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty, notEmpty]
    · simpa only [Entry.Value.erase] using MetaTypeRel.symbol name
    · decide
    · exact Or.inl ⟨name, by simp [Entry.Value.erase]⟩
    · simp [Entry.Value.erase, Atom.unit]
  · rw [read]
    simp only [Entry.Value.erase]
    exact TypeCastBatchRel.success (earlierTypes := []) (laterTypes := [])
      queried rfl (by simp)
      (before.preserved_type_match policy (.undefinedLeft _ _))
  · rw [read]
    exact .cons ⟨by simp [rawResult, Entry.Value.erase], .same before, by simp [Entry.Value.erase]⟩ .nil

theorem symbol_undefined (minimal : Minimal.Services) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (name : String) (notEmpty : name ≠ "Empty")
    (declared : getAtomTypes space (.symbol name) = [Atom.undefinedType]) :
    Stateful.AtomRel (environment minimal) space () live scope (.symbol name) Atom.undefinedType before
      [(.symbol name, before)] () (policy := policy) :=
  symbol_undefined_of_query (environment minimal) space () policy before live scope name notEmpty
    (HEIfSourceSelection.unknown_lookup _ _ before _ _ declared)

def rangeCall (lower upper : Int) : Entry.Value :=
  .expression .active [.symbol "range", .grounded (.int lower), .grounded (.int upper)]

def rangeInput (first : Entry.Value) (upper : Int) : Entry.Value :=
  .expression .active [.symbol "range", first, .grounded (.int upper)]

/-- A real source derivation for the first operand is composed with head
lookup and the second literal. The operand may be the authored addition call. -/
theorem range_tuple_of_sources {World : Type} (current : WorldEnvironment Space World)
    (label : Space) (world : World) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (first : Entry.Value) (lower upper : Int)
    (firstRun : ∀ childLive, Stateful.AtomRel current label world childLive scope first
      Atom.undefinedType before [(.grounded (.int lower), before)] world (policy := policy))
    (headRun : ∀ childLive, Stateful.AtomRel current label world childLive scope (.symbol "range") Atom.undefinedType before
      [(.symbol "range", before)] world (policy := policy))
    (lastRun : ∀ childLive, Stateful.AtomRel current label world childLive scope (.grounded (.int upper)) Atom.undefinedType before
      [(.grounded (.int upper), before)] world (policy := policy)) :
    Stateful.TupleRel current label world live scope
      [.symbol "range", first, .grounded (.int upper)] before [(rangeCall lower upper, before)] world (policy := policy) := by
  have finish : ∀ childLive, Stateful.TupleRel current label world childLive scope
      [.grounded (.int upper)] before [(.expression .active [.grounded (.int upper)], before)] world (policy := policy) := by
    intro childLive
    simpa [Completed.tupleSingleton, Entry.Value.erase, isEmptyOrError, isEmptyAtom, isErrorAtom, Atom.empty] using
      (Stateful.TupleRel.singleton (lastRun childLive))
  have tail : ∀ childLive, Stateful.TupleRel current label world childLive scope
      [first, .grounded (.int upper)] before
      [(.expression .active [.grounded (.int lower), .grounded (.int upper)], before)] world (policy := policy) := by
    intro childLive
    apply Stateful.TupleRel.cons (firstRun _)
    simpa [tuplePrepend, Entry.Value.erase, isEmptyOrError, isEmptyAtom, isErrorAtom, Atom.empty] using
      (Stateful.TupleBranchesRel.continuing (head := (Entry.Value.grounded (.int lower), before))
        (by simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
        (finish ((Entry.Value.grounded (.int lower)).erase :: childLive)) Stateful.TupleBranchesRel.nil)
  apply Stateful.TupleRel.cons (headRun _)
  simpa [tuplePrepend, rangeCall, Entry.Value.erase, isEmptyOrError, isEmptyAtom, isErrorAtom, Atom.empty] using
    (Stateful.TupleBranchesRel.continuing (head := (Entry.Value.symbol "range", before))
      (by simp [Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
      (tail ((Entry.Value.symbol "range").erase :: live)) Stateful.TupleBranchesRel.nil)

theorem range_tuple_for (ports : Ports) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (first : Entry.Value) (lower upper : Int)
    (firstRun : ∀ childLive, Stateful.AtomRel ports.environment space () childLive scope first
      Atom.undefinedType before [(.grounded (.int lower), before)] () (policy := policy)) :
    Stateful.TupleRel ports.environment space () live scope
      [.symbol "range", first, .grounded (.int upper)] before [(rangeCall lower upper, before)] () (policy := policy) :=
  range_tuple_of_sources ports.environment space () policy before live scope first lower upper firstRun
    (fun childLive => symbol_undefined_of_query ports.environment space () policy before childLive scope "range" (by decide)
      (by simpa only [ports.view] using ports.undefinedHead _ before "range" (Or.inl rfl)))
    (fun childLive => ports.number policy before childLive scope upper)

theorem range_tuple (minimal : Minimal.Services) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (first : Entry.Value) (lower upper : Int)
    (firstRun : ∀ childLive, Stateful.AtomRel (environment minimal) space () childLive scope first
      Atom.undefinedType before [(.grounded (.int lower), before)] () (policy := policy)) :
    Stateful.TupleRel (environment minimal) space () live scope
      [.symbol "range", first, .grounded (.int upper)] before [(rangeCall lower upper, before)] () (policy := policy) :=
  range_tuple_for (HERangeSourceProtocol.historical minimal) policy before live scope first lower upper firstRun

theorem atom_of_call_in {World : Type} (current : WorldEnvironment Space World)
    (label : Space) (world : World) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (name : String) (arguments : List Entry.Value)
    (normalized : Entry.Value) (expected : Atom) (rows : List Result)
    (notError : name ≠ "Error") (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (closed : TypeSubst.typeVarsList (arguments.map Entry.Value.erase) = [])
    (queried : current.lookup (invocationTypeScope scope live
      (.expression (.symbol name :: arguments.map Entry.Value.erase)) expected before.bindings)
      (current.view world label) before.bindings (.symbol name) Atom.undefinedType [Atom.undefinedType])
    (tuple : Stateful.TupleRel current label world (expected :: live) scope
      (.symbol name :: arguments) before [(normalized, before)] world (policy := policy))
    (called : Stateful.CallRel current label world live scope normalized expected before rows world (policy := policy))
    (numeric : ∀ row ∈ rows, NumericOrEmpty row.1) :
    Stateful.AtomRel current label world live scope (.expression .active (.symbol name :: arguments))
      expected before rows world (policy := policy) := by
  have read : before.read policy (.expression .active (.symbol name :: arguments)) =
      .expression .active (.symbol name :: arguments) := by
    apply HEFreshSyntaxBinding.ground_substitution
    simpa only [Entry.Value.erase, List.map_cons, TypeSubst.typeVars, TypeSubst.typeVarsList, List.nil_append] using closed
  have calls : Stateful.CallsRel current label world live scope expected [(normalized, before)] rows world (policy := policy) := by
    simpa only [List.append_nil] using Stateful.CallsRel.cons called Stateful.CallsRel.nil
  have priority : Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
      (fun row : Result => isErrorAtom row.1.erase) (rows.map (readResult policy)) rows := by
    rw [HERangeSuperposeSource.numeric_reads policy _ numeric]
    exact HERangeSuperposeSource.numeric_priority _ numeric
  have complete : Stateful.AtomRel current label world live scope
      (.expression .active (.symbol name :: arguments)) expected before
      (rows.map (publishResult policy (before.read policy (.expression .active (.symbol name :: arguments))).erase)) world
      (policy := policy) := by
    apply Stateful.AtomRel.fallback (operator := .symbol name) (arguments := arguments) (errors := [])
      (rows := [(normalized, before)]) (raw := rows)
    · rw [read]
      simp only [Entry.Value.status, Entry.Value.erase, List.map_cons]
      apply Entry.Rel.expression
      · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty, notError]
      · rintro (asAtom | asExpression | impossible)
        · exact notAtom asAtom
        · exact notExpression asExpression
        · exact (by decide : Atom.expressionType ≠ Atom.variableType) impossible
      · exact Or.inr rfl
    · exact read
    · rw [read]
      simp only [Entry.Value.erase, List.map_cons]
      exact current.arguments.single_nonfunction queried
        (by rintro ⟨domains, returned, impossible⟩; cases impossible)
    · exact tuple
    · exact calls
    · simpa only [diagnosticResults, List.map_nil, List.append_nil] using priority
  simpa only [HERangeSuperposeSource.numeric_publishes policy _ _ numeric] using complete

theorem atom_of_call (minimal : Minimal.Services) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (name : String) (arguments : List Entry.Value)
    (normalized : Entry.Value) (expected : Atom) (rows : List Result)
    (notError : name ≠ "Error") (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (closed : TypeSubst.typeVarsList (arguments.map Entry.Value.erase) = [])
    (declared : getAtomTypes space (.symbol name) = [Atom.undefinedType])
    (tuple : Stateful.TupleRel (environment minimal) space () (expected :: live) scope
      (.symbol name :: arguments) before [(normalized, before)] () (policy := policy))
    (called : Stateful.CallRel (environment minimal) space () live scope normalized expected before rows () (policy := policy))
    (numeric : ∀ row ∈ rows, NumericOrEmpty row.1) :
    Stateful.AtomRel (environment minimal) space () live scope (.expression .active (.symbol name :: arguments))
      expected before rows () (policy := policy) :=
  atom_of_call_in (environment minimal) space () policy before live scope name arguments normalized expected rows
    notError notAtom notExpression closed (HEIfSourceSelection.unknown_lookup _ _ before _ _ declared)
    tuple called numeric

theorem ground_range_atom_for (ports : Ports) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (lower upper : Int) (expected : Atom) (rows : List Result)
    (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (called : Stateful.CallRel ports.environment space () live scope (rangeCall lower upper) expected before rows () (policy := policy))
    (numeric : ∀ row ∈ rows, NumericOrEmpty row.1) :
    Stateful.AtomRel ports.environment space () live scope (rangeCall lower upper) expected before rows () (policy := policy) :=
  atom_of_call_in ports.environment space () policy before live scope "range" [.grounded (.int lower), .grounded (.int upper)]
    (rangeCall lower upper) expected rows (by decide) notAtom notExpression
    (by simp [Entry.Value.erase, TypeSubst.typeVarsList, TypeSubst.typeVars]) (by simpa only [ports.view] using ports.undefinedHead _ before "range" (Or.inl rfl))
    (range_tuple_for ports policy before (expected :: live) scope (.grounded (.int lower)) lower upper
      (fun childLive => ports.number policy before childLive scope lower)) called numeric

theorem ground_range_atom (minimal : Minimal.Services) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (lower upper : Int) (expected : Atom) (rows : List Result)
    (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    (called : Stateful.CallRel (environment minimal) space () live scope (rangeCall lower upper) expected before rows () (policy := policy))
    (numeric : ∀ row ∈ rows, NumericOrEmpty row.1) :
    Stateful.AtomRel (environment minimal) space () live scope (rangeCall lower upper) expected before rows () (policy := policy) :=
  ground_range_atom_for (HERangeSourceProtocol.historical minimal) policy before live scope lower upper expected rows notAtom notExpression called numeric

theorem incremented_range_atom_for (ports : Ports) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (lower upper : Int) (rows : List Result)
    (called : Stateful.CallRel ports.environment space () live scope (rangeCall (lower + 1) upper) Atom.undefinedType before rows () (policy := policy))
    (numeric : ∀ row ∈ rows, NumericOrEmpty row.1) :
    Stateful.AtomRel ports.environment space () live scope
      (rangeInput (HEBinaryNumericSource.addition.call lower 1) upper) Atom.undefinedType before rows () (policy := policy) :=
  atom_of_call_in ports.environment space () policy before live scope "range" [HEBinaryNumericSource.addition.call lower 1, .grounded (.int upper)]
    (rangeCall (lower + 1) upper) Atom.undefinedType rows (by decide) (by decide) (by decide)
    (by simp [HEBinaryNumericSource.Operation.call, Entry.Value.erase, TypeSubst.typeVarsList, TypeSubst.typeVars])
    (by simpa only [ports.view] using ports.undefinedHead _ before "range" (Or.inl rfl))
    (range_tuple_for ports policy before (Atom.undefinedType :: live) scope (HEBinaryNumericSource.addition.call lower 1) (lower + 1) upper
      (fun childLive => ports.addition policy before childLive scope lower 1)) called numeric

theorem incremented_range_atom (minimal : Minimal.Services) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (lower upper : Int) (rows : List Result)
    (called : Stateful.CallRel (environment minimal) space () live scope (rangeCall (lower + 1) upper) Atom.undefinedType before rows () (policy := policy))
    (numeric : ∀ row ∈ rows, NumericOrEmpty row.1) :
    Stateful.AtomRel (environment minimal) space () live scope
      (rangeInput (HEBinaryNumericSource.addition.call lower 1) upper) Atom.undefinedType before rows () (policy := policy) :=
  incremented_range_atom_for (HERangeSourceProtocol.historical minimal) policy before live scope lower upper rows called numeric

theorem empty_atom_for (ports : Ports) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (expected : Atom)
    (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType) :
    Stateful.AtomRel ports.environment space () live scope HERangeEquationFrontiers.emptyCall expected before
      [(.symbol "Empty", before)] () (policy := policy) := by
  have tuple : Stateful.TupleRel ports.environment space () (expected :: live) scope [.symbol "empty"] before
      [(HERangeEquationFrontiers.emptyCall, before)] () (policy := policy) := by
    simpa [Completed.tupleSingleton, HERangeEquationFrontiers.emptyCall, HERangeSourceProgram.emptyPattern, Entry.Value.ofAtom,
      Entry.Value.erase, isEmptyOrError, isEmptyAtom, isErrorAtom, Atom.empty] using
      (Stateful.TupleRel.singleton (symbol_undefined_of_query ports.environment space () policy before (expected :: live) scope "empty"
        (by decide) (by simpa only [ports.view] using ports.undefinedHead _ before "empty" (Or.inr rfl))))
  have result := atom_of_call_in ports.environment space () policy before live scope "empty" [] HERangeEquationFrontiers.emptyCall expected
    [(.symbol "Empty", before)] (by decide) notAtom notExpression rfl (by simpa only [ports.view] using ports.undefinedHead _ before "empty" (Or.inr rfl)) tuple
    (HERangeEquationFrontiers.empty_call_in ports.environment ports.view ports.dispatch policy before live scope expected)
    (by intro row member; cases List.mem_singleton.mp member; exact .empty)
  simpa [HERangeEquationFrontiers.emptyCall, HERangeSourceProgram.emptyPattern, Entry.Value.ofAtom] using result

theorem empty_atom (minimal : Minimal.Services) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (expected : Atom)
    (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType) :
    Stateful.AtomRel (environment minimal) space () live scope HERangeEquationFrontiers.emptyCall expected before
      [(.symbol "Empty", before)] () (policy := policy) :=
  empty_atom_for (HERangeSourceProtocol.historical minimal) policy before live scope expected notAtom notExpression

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeUntypedEntry
