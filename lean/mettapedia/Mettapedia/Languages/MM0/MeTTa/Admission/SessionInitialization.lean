import Mettapedia.Languages.MM0.MeTTa.Kernel.Proof
import Mettapedia.Languages.MM0.MeTTa.Formation.SortFormation
import Mathlib.Tactic.IntervalCases

/-!
# Allocation and ownership established by the retained session driver

The pinned `mm0:start` allocates separate cache, proof, sort, term, definition
and theorem spaces and installs its three owned cells. The expected store
below uses the existing allocation and cell operations. Execution agreement
is proved against the retained source equation, not a replacement driver.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.SessionInitialization

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean handleValue)
open NamedSpaces (Handle)

/-- The six capabilities created by one start request. -/
structure Spaces where
  cache : Handle
  proofs : Handle
  sorts : Handle
  terms : Handle
  definitions : Handle
  theorems : Handle

def allocatedSpaces (before : State) : Spaces :=
  { cache := .privateSpace before.next
    proofs := .privateSpace (before.next + 1)
    sorts := .privateSpace (before.next + 2)
    terms := .privateSpace (before.next + 3)
    definitions := .privateSpace (before.next + 4)
    theorems := .privateSpace (before.next + 5) }

def theoryValue (spaces : Spaces) : Atom :=
  ListAccess.listValue [.symbol "MM0:Theory", TableAccess.tableValue spaces.sorts,
    TableAccess.tableValue spaces.terms, TableAccess.tableValue spaces.definitions,
    TableAccess.tableValue spaces.theorems]

def stateValue (spaces : Spaces) (pending : Atom) : Atom :=
  ListAccess.listValue [.symbol "MM0:SpecificationState", theoryValue spaces, pending]

def sessionValue (spaces : Spaces) (specification : Atom) : Atom :=
  .expression [.symbol "Some", stateValue spaces specification]

private def stage (before : State) (specification : Atom) : Nat → State
  | 0 => before
  | 1 => (before.allocate []).2
  | 2 => (stage before specification 1).putCell InferenceCache.cell
      (handleValue (allocatedSpaces before).cache)
  | 3 => ((stage before specification 2).allocate []).2
  | 4 => (stage before specification 3).putCell "mm0-proof-store"
      (handleValue (allocatedSpaces before).proofs)
  | 5 => ((stage before specification 4).allocate []).2
  | 6 => ((stage before specification 5).allocate []).2
  | 7 => ((stage before specification 6).allocate []).2
  | 8 => ((stage before specification 7).allocate []).2
  | 9 => (stage before specification 8).putCell "mm0-session"
      (sessionValue (allocatedSpaces before) specification)
  | _ => before

def startState (before : State) (specification : Atom) : State :=
  stage before specification 9

def Spaces.handles (spaces : Spaces) : List Handle :=
  [spaces.cache, spaces.proofs, spaces.sorts, spaces.terms, spaces.definitions, spaces.theorems]

/-- Separation is earned by the six actual consecutive allocations. -/
theorem allocated_spaces_distinct (before : State) :
    (allocatedSpaces before).handles.Nodup := by
  simp [Spaces.handles, allocatedSpaces]

theorem start_next (before : State) (specification : Atom) :
    (startState before specification).next = before.next + 6 := by
  simp [startState, stage, NamedSpaces.Store.allocate, NamedSpaces.Store.putCell, Nat.add_assoc]

theorem start_owns_cells (before : State) (specification : Atom) :
    (startState before specification).cells InferenceCache.cell =
        some (handleValue (allocatedSpaces before).cache) ∧
      (startState before specification).cells "mm0-proof-store" =
        some (handleValue (allocatedSpaces before).proofs) ∧
      (startState before specification).cells "mm0-session" =
        some (sessionValue (allocatedSpaces before) specification) := by
  simp [startState, stage, NamedSpaces.Store.allocate, NamedSpaces.Store.putCell, InferenceCache.cell]

theorem start_preserves_other_cells (before : State) (specification : Atom) (name : String)
    (notCache : name ≠ InferenceCache.cell) (notProofs : name ≠ "mm0-proof-store")
    (notSession : name ≠ "mm0-session") :
    (startState before specification).cells name = before.cells name := by
  simp [startState, stage, NamedSpaces.Store.allocate, NamedSpaces.Store.putCell,
    notCache, notProofs, notSession]

theorem allocated_spaces_empty (before : State) (specification : Atom) (handle : Handle)
    (member : handle ∈ (allocatedSpaces before).handles) :
    (startState before specification).read handle = some [] := by
  simp only [Spaces.handles, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [startState, stage, allocatedSpaces, NamedSpaces.Store.allocate,
      NamedSpaces.Store.putCell, NamedSpaces.Store.read, Nat.add_assoc]

theorem start_preserves_allocated_space (before : State) (specification : Atom)
    (handle : Handle) (rows : List Atom) (allocated : before.read handle = some rows) :
    (startState before specification).read handle = before.read handle := by
  cases handle with
  | self =>
    simp [startState, stage, NamedSpaces.Store.allocate,
      NamedSpaces.Store.putCell, NamedSpaces.Store.read]
  | privateSpace index =>
    have bound : index < before.next := by
      by_contra absent
      simp [NamedSpaces.Store.read, absent] at allocated
    have different : ∀ offset, index ≠ before.next + offset := by intro offset; omega
    have notBase : index ≠ before.next := by omega
    have bounded : index < before.next + 6 := by omega
    simp [startState, stage, allocatedSpaces, NamedSpaces.Store.allocate,
      NamedSpaces.Store.putCell, NamedSpaces.Store.read, Nat.add_assoc,
      different, notBase, bound, bounded]

private def equation : SpaceSemantics.Equation := serviceSource.program.equations[3]'(by decide)

private def tail : Atom → Atom
  | .expression [_, _, _, body] => body
  | _ => .expression []

private def suffix : Nat → Atom
  | 0 => equation.body
  | n + 1 => tail (suffix n)

private def bindingRows (before : State) : List (String × Atom) :=
  [("cache", handleValue (allocatedSpaces before).cache), ("set", boolean true),
   ("proofs", handleValue (allocatedSpaces before).proofs), ("setProofs", boolean true),
   ("sorts", handleValue (allocatedSpaces before).sorts),
   ("terms", handleValue (allocatedSpaces before).terms),
   ("defs", handleValue (allocatedSpaces before).definitions),
   ("thms", handleValue (allocatedSpaces before).theorems), ("done", boolean true)]

private def environment (before : State) (specification : Atom) (index : Nat) : Subst :=
  (bindingRows before |>.take index).reverse ++ [("spec", specification)]

private def binding (before : State) (index : Nat) : String × Atom :=
  ((bindingRows before)[index]?).getD ("", .expression [])

private def operation (index : Nat) : Atom :=
  match suffix index with
  | .expression [_, _, expression, _] => expression
  | _ => .expression []

private theorem binding_shape (before : State) (index : Nat) (bounded : index < 9) :
    suffix index = .expression [.symbol "let", .var (binding before index).1,
      operation index, suffix (index + 1)] := by
  interval_cases index <;> simp [binding, bindingRows] <;> decide +kernel

private theorem binding_match (before : State) (specification : Atom) (index : Nat)
    (bounded : index < 9) :
    SpaceSemantics.matchValue (environment before specification index)
      (.var (binding before index).1) (binding before index).2 =
        some (environment before specification (index + 1)) := by
  interval_cases index <;>
    simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup,
      environment, binding, bindingRows]

private theorem equation_unique :
    program.equations.filter (fun row => row.head == "mm0:start") = [equation] := by decide +kernel

private theorem equation_formals : equation.arguments = [.var "spec"] := by decide +kernel

private theorem suffix_end : suffix 9 = boolean true := by decide +kernel

private theorem allocation_operation (index : Nat) (member : index ∈ [0, 2, 4, 5, 6, 7]) :
    operation index = .expression [.symbol "new-space"] := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private theorem cache_operation : operation 1 =
    .expression [.symbol "change-state!", .symbol "mm0-inference-cache", .var "cache"] := by
  decide +kernel

private theorem proofs_operation : operation 3 =
    .expression [.symbol "change-state!", .symbol "mm0-proof-store", .var "proofs"] := by
  decide +kernel

private theorem session_operation : operation 8 =
    .expression [.symbol "change-state!", .symbol "mm0-session",
      .expression [.symbol "Some", ListAccess.listValue
        [.symbol "MM0:SpecificationState", ListAccess.listValue
          [.symbol "MM0:Theory", .expression [.symbol "MM0:Table", .var "sorts"],
            .expression [.symbol "MM0:Table", .var "terms"],
            .expression [.symbol "MM0:Table", .var "defs"],
            .expression [.symbol "MM0:Table", .var "thms"]], .var "spec"]]] := by
  decide +kernel

private theorem start_clause (before : State) (specification : Atom) :
    clauses program "mm0:start" [specification] =
      [.evaluate (environment before specification 0) equation.body] := by
  rw [clauses_use_only_the_named_equations, equation_unique]
  simp [equation_formals, environment, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

private theorem new_space_returns (bindings : Subst) (before : State) :
    PureReturns program bindings before (.expression [.symbol "new-space"])
      (before.allocate []).2 (handleValue (before.allocate []).1) := by
  apply native_variable_call_returns program bindings before (before.allocate []).2
    "new-space" [] _ (by decide) (by decide) _ (by decide)
  simp [StdLib.apply]

private theorem put_cell_returns (bindings : Subst) (before : State)
    (name : String) (expression value : Atom)
    (captured : applySubst bindings expression = value) :
    PureReturns program bindings before
      (.expression [.symbol "change-state!", .symbol name, expression])
      (before.putCell name value) (boolean true) := by
  apply call_returns program bindings before (before.putCell name value)
    "change-state!" _ _ (by decide) _ (by decide)
  apply evaluated_argument_returns program bindings before before (before.putCell name value)
    (.function "change-state!") (.symbol name) (.symbol name) _ [expression] [] 0
    (by decide) (symbol_returns program bindings before name)
  apply raw_arguments_return program bindings before (before.putCell name value)
    "change-state!" [expression] [.symbol name] 1 _
  · intro index bounded
    have zero : index = 0 := by simp only [List.length_cons, List.length_nil] at bounded; omega
    subst index
    decide +kernel
  · simp only [List.map_cons, List.map_nil, captured, List.cons_append, List.nil_append]
    exact native_function_arguments_return program bindings before (before.putCell name value)
      "change-state!" [.symbol name, value] 2 (boolean true)
      (by decide) (by decide) rfl

private theorem operation_returns (before : State) (specification : Atom) (index : Nat)
    (bounded : index < 9) :
    PureReturns program (environment before specification index)
      (stage before specification index) (operation index)
      (stage before specification (index + 1)) (binding before index).2 := by
  interval_cases index
  · rw [allocation_operation 0 (by decide)]
    simpa [stage, binding, bindingRows, allocatedSpaces, NamedSpaces.Store.allocate] using
      new_space_returns (environment before specification 0) before
  · rw [cache_operation]
    simp [stage, binding, bindingRows]
    apply put_cell_returns
    simp [environment, bindingRows, allocatedSpaces,
      applySubst, Subst.lookup]
  · rw [allocation_operation 2 (by decide)]
    simpa [stage, binding, bindingRows, allocatedSpaces, NamedSpaces.Store.allocate,
      NamedSpaces.Store.putCell, Nat.add_assoc] using
      new_space_returns (environment before specification 2) (stage before specification 2)
  · rw [proofs_operation]
    simp [stage, binding, bindingRows]
    apply put_cell_returns
    simp [environment, bindingRows, allocatedSpaces, applySubst, Subst.lookup]
  · rw [allocation_operation 4 (by decide)]
    simpa [stage, binding, bindingRows, allocatedSpaces, NamedSpaces.Store.allocate,
      NamedSpaces.Store.putCell, Nat.add_assoc] using
      new_space_returns (environment before specification 4) (stage before specification 4)
  · rw [allocation_operation 5 (by decide)]
    simpa [stage, binding, bindingRows, allocatedSpaces, NamedSpaces.Store.allocate,
      NamedSpaces.Store.putCell, Nat.add_assoc] using
      new_space_returns (environment before specification 5) (stage before specification 5)
  · rw [allocation_operation 6 (by decide)]
    simpa [stage, binding, bindingRows, allocatedSpaces, NamedSpaces.Store.allocate,
      NamedSpaces.Store.putCell, Nat.add_assoc] using
      new_space_returns (environment before specification 6) (stage before specification 6)
  · rw [allocation_operation 7 (by decide)]
    simpa [stage, binding, bindingRows, allocatedSpaces, NamedSpaces.Store.allocate,
      NamedSpaces.Store.putCell, Nat.add_assoc] using
      new_space_returns (environment before specification 7) (stage before specification 7)
  · rw [session_operation]
    simp [stage, binding, bindingRows]
    apply put_cell_returns
    simp [environment, bindingRows, allocatedSpaces, sessionValue, stateValue,
      theoryValue, ListAccess.listValue, TableAccess.tableValue,
      applySubst, applySubst.applySubstList, Subst.lookup]

private theorem suffix_returns (before : State) (specification : Atom) (index : Nat)
    (bounded : index ≤ 9) :
    PureReturns program (environment before specification index)
      (stage before specification index) (suffix index)
      (startState before specification) (boolean true) := by
  induction remaining : 9 - index generalizing index with
  | zero =>
    have last : index = 9 := by omega
    subst index
    rw [suffix_end]
    simpa only [startState, boolean] using
      grounded_returns program (environment before specification 9)
        (stage before specification 9) (.bool true)
  | succ count ih =>
    have inRange : index < 9 := by omega
    rw [binding_shape before index inRange]
    exact let_returns program _ _ _ _ _ _ _ _ _ _
      (operation_returns before specification index inRange)
      (binding_match before specification index inRange)
      (ih (index + 1) (by omega) (by omega))

/-- Starting a session executes the retained equation, with the exact six
allocations and owned-cell updates above, for an arbitrary incoming store. -/
theorem returns (bindings : Subst) (before : State) (specification : Atom)
    (name : String) (captured : applySubst bindings (.var name) = specification) :
    PureReturns program bindings before (.expression [.symbol "mm0:start", .var name])
      (startState before specification) (boolean true) := by
  have body := suffix_returns before specification 0 (by omega)
  simp only [stage, suffix] at body
  apply authored_variable_call_returns program bindings (environment before specification 0)
    before (startState before specification) "mm0:start" [name] equation.body _
    (by decide) (by decide) (by decide) _ body
    (by decide)
  simpa [captured] using start_clause before specification

/-- The empty logical tables refer to the capabilities created by the
retained start call; they are not a separately allocated checker state. -/
def initialTables (before : State) : Proof.Tables :=
  { terms := (allocatedSpaces before).terms
    definitions := (allocatedSpaces before).definitions
    theorems := (allocatedSpaces before).theorems
    hypotheses := (allocatedSpaces before).proofs
    cache := (allocatedSpaces before).cache
    entries := []
    bodies := []
    declarations := []
    values := []
    uniqueTerms := by intro index; simp
    uniqueDefinitions := by intro index; simp
    uniqueTheorems := by intro index; simp
    separateTerms := by simp [allocatedSpaces]
    separateDefinitions := by simp [allocatedSpaces]
    separateTheorems := by simp [allocatedSpaces]
    separateHypotheses := by simp [allocatedSpaces] }

/-- The proof-checker's concrete premises are established by start, including
the owned cache cell and the empty coherent scope. -/
theorem start_ready (before : State) (specification : Atom) :
    Proof.Ready (initialTables before) (startState before specification) := by
  constructor
  · simpa [initialTables, TableAccess.declarationRows, Store.rows] using
      allocated_spaces_empty before specification (allocatedSpaces before).terms
        (by simp [Spaces.handles])
  · simpa [initialTables, Unfolding.definitionRows, Store.rows] using
      allocated_spaces_empty before specification (allocatedSpaces before).definitions
        (by simp [Spaces.handles])
  · simpa [initialTables, Proof.theoremRows, Store.rows] using
      allocated_spaces_empty before specification (allocatedSpaces before).theorems
        (by simp [Spaces.handles])
  · apply Hypothesis.Ready.vector
    simpa [initialTables, Store.Represents, Store.enumerate, Store.rows] using
      allocated_spaces_empty before specification (allocatedSpaces before).proofs
        (by simp [Spaces.handles])
  · refine ⟨(start_owns_cells before specification).1, [], ?_,
      InferenceCache.empty_valid _ _⟩
    exact allocated_spaces_empty before specification (allocatedSpaces before).cache
      (by simp [Spaces.handles])

theorem start_sort_table (before : State) (specification : Atom) :
    (startState before specification).read (allocatedSpaces before).sorts =
      some (SortFormation.rows []) := by
  simpa [SortFormation.rows, Store.rows] using
    allocated_spaces_empty before specification (allocatedSpaces before).sorts
      (by simp [Spaces.handles])

/-- Each capability was unallocated before this particular start request. -/
theorem start_fresh (before : State) (handle : Handle)
    (member : handle ∈ (allocatedSpaces before).handles) : before.read handle = none := by
  simp only [Spaces.handles, List.mem_cons, List.mem_nil_iff, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [allocatedSpaces, NamedSpaces.Store.read]

/-- Restarting earns another distinct block rather than reusing an earlier
cache or proof-store capability. Earlier stores themselves remain readable. -/
theorem restart_separates_spaces (before : State) (specification : Atom) :
    List.Disjoint (allocatedSpaces before).handles
      (allocatedSpaces (startState before specification)).handles := by
  simp [List.disjoint_left, Spaces.handles, allocatedSpaces, start_next]
  omega

def requestConfiguration (bindings : Subst) (before : State) (name : String) : Configuration :=
  { state := before, control := .evaluate bindings (.expression [.symbol "mm0:start", .var name]) }

theorem sufficient_fuel (bindings : Subst) (before : State) (specification : Atom)
    (name : String) (captured : applySubst bindings (.var name) = specification) :
    ∃ fuel, run program fuel (requestConfiguration bindings before name) =
      .complete (startState before specification) [boolean true] [] [] :=
  pure_returns_has_sufficient_fuel program bindings before (startState before specification)
    _ _ (returns bindings before specification name captured)

theorem start_judgment (bindings : Subst) (before : State) (specification : Atom)
    (name : String) (captured : applySubst bindings (.var name) = specification) :
    DeclarativeSpec.Runs program (requestConfiguration bindings before name)
      (.complete (startState before specification) [boolean true] [] []) :=
  (completed_run_iff_derivation program _ _ _ [] []).mp
    (sufficient_fuel bindings before specification name captured)

/-- The session's initial table invariant is earned along a path in the
existing PeTTa GSLT, which is generated from its operational judgment. -/
theorem start_path_and_ready (bindings : Subst) (before : State) (specification : Atom)
    (name : String) (captured : applySubst bindings (.var name) = specification) :
    (theory program).MultiStep (requestConfiguration bindings before name)
        (finished (startState before specification) [boolean true] [] []) ∧
      Proof.Ready (initialTables before) (startState before specification) :=
  ⟨returns bindings before specification name captured, start_ready before specification⟩

/-- Every observed completed start has the same store and observations as
the source execution proved above, so its premises need not be supplied. -/
theorem completed_start_establishes_ready (bindings : Subst) (before : State)
    (specification : Atom) (name : String)
    (captured : applySubst bindings (.var name) = specification)
    (fuel : Nat) (after : State) (answers input output : List Atom)
    (completed : run program fuel (requestConfiguration bindings before name) =
      .complete after answers input output) :
    after = startState before specification ∧ answers = [boolean true] ∧
      input = [] ∧ output = [] ∧ Proof.Ready (initialTables before) after := by
  obtain ⟨referenceFuel, reference⟩ := sufficient_fuel bindings before specification name captured
  have same := completed_result_unique program fuel referenceFuel _ after
    (startState before specification) answers input output [boolean true] [] [] completed reference
  exact ⟨same.1, same.2.1, same.2.2.1, same.2.2.2,
    same.1 ▸ start_ready before specification⟩

end Mettapedia.Languages.MM0.MeTTa.SessionInitialization
