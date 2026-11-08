import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypedSquareSource

/-!
# A typed square source and ordered collection

The example uses the existing HE evaluator, its scoped equation matcher,
and the existing integer multiplication service. Collection is ordered and
retains the original typed return boundary rather than treating a native
value as permission to forget that boundary.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypedSquareCollection

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.CompletedDelivery
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue executeGroundedOp)

theorem square_query_live (n : Int) (k : Nat) (live : List Atom)
    (closed : atomListVariables live = []) :
    rawQueryResults squareSpace (apply "sq" [num n]) number Bindings.empty (k + 12) live =
      [(apply "*" [num n, num n], squareBindings n)] := by
  calc
    _ = rawQueryResults squareSpace (apply "sq" [num n]) number Bindings.empty (k + 12) [] := by
      simp only [rawQueryResults, equationScope, closed, atomListVariables]
    _ = _ := square_query n k

theorem multiplication_invoked (n : Int) (k : Nat) (live : List Atom) :
    invoke squareSpace multiplication (.ordinary number) (apply "*" [num n, num n])
      (squareBindings n) (k + 10) live = [(num (n * n), squareBindings n)] := by
  have merged : ([(num (n * n), Bindings.empty)] : ResultSet).flatMap
      (fun reply => (mergeBindings reply.2 (squareBindings n) (k + 9)).map
        fun bindings => (bindings.applyFull reply.1 (k + 9), bindings)) =
      [(num (n * n), squareBindings n)] := by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [show k + 9 = (k + 7) + 2 by omega, squareBindings, mergeBindings_empty_single_assign]
    rw [List.map_cons, List.map_nil, applyFull_ground _ _ _ rfl]
  rw [show k + 10 = (k + 9) + 1 by omega]
  change invoke squareSpace multiplication (.ordinary number)
    (.expression [.symbol "*", num n, num n]) (squareBindings n) ((k + 9) + 1) live = _
  rw [invoke]
  simp only [InvocationMode.errorPassthrough,
    show isErrorAtom (.expression [.symbol "*", num n, num n]) = false from rfl,
    Bool.false_eq_true, if_false,
    show multiplication.isExecutable (.symbol "*") = true from rfl,
    if_true, multiplication_integer, merged, List.isEmpty_cons,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [invocationResult_plain (by intro body; simp [num])]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simp only [num]
  rw [HEReturns.ordinaryCallReturn_grounded]
  have returned := HEReturns.evalAtom_grounded (space := squareSpace) (dispatch := multiplication)
    (.int (n * n)) (type_ := number) rfl (by decide) (by decide) (squareBindings n)
    (fuel := k + 8) (by change 1 ≤ k + 8; omega) live
  simpa only [num, show accepts number (getGroundedType (.int (n * n))) = true from rfl,
    if_true] using returned

/-- The actual typed native call, including argument checking and the
ordinary result boundary, preserves the equation's fresh binding. -/
theorem multiplication_call (n : Int) (k : Nat) (live : List Atom) :
    evalAtom squareSpace multiplication (apply "*" [num n, num n]) number
      (squareBindings n) (k + 12) live = [(num (n * n), squareBindings n)] := by
  have classes : ∀ param ∈ [number, number], HEReturns.ValueClass param := by
    intro param member
    have same : param = number := by simpa using member
    subst param
    exact Or.inl rfl
  have checks : List.Forall₂ (ArgumentChecked squareSpace) [number, number] [num n, num n] :=
    .cons (HEReturns.argumentChecked_grounded squareSpace (.int n) rfl)
      (.cons (HEReturns.argumentChecked_grounded squareSpace (.int n) rfl) .nil)
  have arguments := HEReturns.interpretArgs_values (space := squareSpace) (dispatch := multiplication)
    (bindings := squareBindings n) [number, number] [.int n, .int n] classes
      (.cons rfl (.cons rfl .nil)) (k + 8) (by simp)
  have interpreted := interpretExpression_typed (space := squareSpace) (dispatch := multiplication)
    (head := "*") (params := [number, number]) (args := [num n, num n])
    (range := number) (expected := number) (copies := 0) (by decide) rfl (by decide)
    checks rfl (squareBindings n) (fuel := k + 8) (by change 6 ≤ k + 8; omega)
    arguments (multiplication_invoked n k live)
  simp only [List.replicate_succ, List.replicate_zero, List.flatten_cons, List.flatten_nil,
    List.append_nil] at interpreted
  exact evalAtom_of_interpretExpression ⟨.symbol "*", [num n, num n], rfl⟩ rfl rfl interpreted
    (by intro reply member; rw [List.mem_singleton] at member; subst reply; rfl)

theorem square_call (n : Int) (k : Nat) (live : List Atom) (closed : atomListVariables live = [])
    (expected : Atom) (acceptsRange : accepts expected number = true)
    (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType) :
    evalAtom squareSpace multiplication (apply "sq" [num n]) expected Bindings.empty (k + 30) live =
      [(num (n * n), squareBindings n)] := by
  have classes : ∀ position ∈ number :: [number], HEReturns.ValueClass position := by
    intro position member
    have same : position = number := by simpa using member
    subst position
    exact Or.inl rfl
  have query := square_query_live n (k + 15) live closed
  have called := HEReturns.value_call (space := squareSpace) (dispatch := multiplication)
    (head := "sq") (params := [number]) (values := [.int n]) (range := number)
    (expected := expected) (by decide) classes (by decide) (by decide) rfl rfl rfl acceptsRange
    notAtom notExpression Bindings.empty (fuel := k + 26)
    (by change 5 ≤ k + 26; omega) (live := live) query (by simp)
    (by intro reply member body; simp only [List.mem_singleton] at member; subst reply; simp [apply])
  refine called.trans ?_
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [ordinaryCallReturn_evaluate _ _ _ _ (by simp [apply, Atom.notReducible]) rfl]
  rw [multiplication_call n (k + 15) live]
  simp [HEReturns.keep, num, isErrorAtom]

structure Context where
  slack : Nat
  live : List Atom
  closed : atomListVariables live = []
  expected : Atom
  acceptsRange : accepts expected number = true
  notAtom : expected ≠ Atom.atomType
  notExpression : expected ≠ Atom.expressionType

def sourceCall (context : Context) (n : Int) : ResultSet :=
  evalAtom squareSpace multiplication (apply "sq" [num n]) context.expected Bindings.empty
    (context.slack + 30) context.live

def squareResult (n : Int) : ResultPair := (num (n * n), squareBindings n)

theorem sourceCall_exact (context : Context) (n : Int) :
    sourceCall context n = [squareResult n] :=
  square_call n context.slack context.live context.closed context.expected
    context.acceptsRange context.notAtom context.notExpression

def sourceBatch (context : Context) (inputs : List Int) : ResultSet :=
  inputs.flatMap (sourceCall context)

theorem sourceBatch_exact (context : Context) (inputs : List Int) :
    sourceBatch context inputs = inputs.map squareResult := by
  unfold sourceBatch
  rw [List.map_eq_flatMap]
  exact List.flatMap_congr fun n _ => sourceCall_exact context n

def returnFrame (context : Context) (n : Int) : OrderedHEBoundary.ReturnFrame :=
  ⟨apply "sq" [num n], number, squareBindings n, context.slack + 27, context.live⟩

/-- The retained return frame runs the actual substituted multiplication
body at its owed range, not at a fresh caller's expected type. -/
theorem returnFrame_correct (context : Context) (n : Int) :
    (returnFrame context n).resume squareSpace multiplication (apply "*" [num n, num n]) =
      sourceCall context n := by
  rw [sourceCall_exact]
  unfold returnFrame OrderedHEBoundary.ReturnFrame.resume
  rw [ordinaryCallReturn_evaluate _ _ _ _ (by simp [apply, Atom.notReducible]) rfl]
  exact multiplication_call n (context.slack + 15) context.live

/-- A pending admitted region carries its full return record. The invariant
is established when the actual typed source call is entered. -/
structure Pending (context : Context) where
  input : Int
  frame : OrderedHEBoundary.ReturnFrame
  retained : frame = returnFrame context input

def Pending.enter (context : Context) (n : Int) : Pending context :=
  ⟨n, returnFrame context n, rfl⟩

/-- The specialized arithmetic result keeps the actual equation record. -/
def Pending.native {context : Context} (pending : Pending context) : ResultSet :=
  [(num (pending.input * pending.input), pending.frame.bindings)]

theorem Pending.native_correct (context : Context) (pending : Pending context) :
    pending.native =
      pending.frame.resume squareSpace multiplication (apply "*" [num pending.input, num pending.input]) := by
  unfold Pending.native
  rw [pending.retained, returnFrame_correct, sourceCall_exact]
  rfl

def pendingSource {context : Context} : Option (Pending context) → ResultSet
  | none => []
  | some pending =>
      pending.frame.resume squareSpace multiplication (apply "*" [num pending.input, num pending.input])

structure Cursor (context : Context) where
  collection : ProducerCompletion.Frame
  pending : Option (Pending context)
  inputs : List Int

def initial (context : Context) (inputs : List Int) : Cursor context :=
  ⟨⟨[], []⟩, none, inputs⟩

/-- The ordered residual includes saved returns, current uncollected
returns, the retained typed call, and every source call not yet entered. -/
def residual (context : Context) (cursor : Cursor context) : ResultSet :=
  ProducerCompletion.reference (cursor.collection.savedRev.reverse ++ cursor.collection.remaining ++
    pendingSource cursor.pending ++ sourceBatch context cursor.inputs)

inductive Step (context : Context) where
  | next : Cursor context → Step context
  | complete : ResultSet → Step context

/-- The arithmetic shortcut occurs only in an admitted Pending state.
Existing producer completion performs collection and final selection. -/
def step (context : Context) (cursor : Cursor context) : Step context :=
  match cursor.collection.remaining with
  | _ :: _ => match ProducerCompletion.step cursor.collection with
      | .collect collected => .next {cursor with collection := collected}
      | .complete answers => .complete answers
  | [] => match cursor.pending with
      | some pending => .next {cursor with
          collection := {cursor.collection with remaining := pending.native}, pending := none}
      | none => match cursor.inputs with
          | n :: rest => .next {cursor with pending := some (Pending.enter context n), inputs := rest}
          | [] => match ProducerCompletion.step cursor.collection with
              | .collect collected => .next {cursor with collection := collected}
              | .complete answers => .complete answers

theorem step_preserves (context : Context) (cursor : Cursor context) :
    match step context cursor with
    | .next next => residual context next = residual context cursor
    | .complete answers => answers = residual context cursor := by
  rcases cursor with ⟨⟨saved, queued⟩, pending, inputs⟩
  cases queued with
  | cons result rest => simp [step, ProducerCompletion.step, residual, List.reverse_cons, List.append_assoc]
  | nil =>
      cases pending with
      | some call => simp [step, residual, pendingSource, Pending.native_correct]
      | none =>
          cases inputs with
          | nil => simp [step, ProducerCompletion.step, residual, pendingSource, sourceBatch]
          | cons n inputs =>
              simp [step, residual, pendingSource, Pending.enter, returnFrame_correct,
                sourceBatch, List.append_assoc]

def drive (context : Context) : Nat → Cursor context → Option ResultSet × Option (Cursor context)
  | 0, cursor => (none, some cursor)
  | budget + 1, cursor => match step context cursor with
      | .next next => drive context budget next
      | .complete answers => (some answers, none)

/-- Pausing keeps the exact ordered residual; only full completion publishes
the producer result. The budget counts these administrative transitions. -/
theorem drive_preserves (context : Context) (budget : Nat) (cursor : Cursor context) :
    match drive context budget cursor with
    | (some answers, none) => answers = residual context cursor
    | (none, some next) => residual context next = residual context cursor
    | _ => False := by
  induction budget generalizing cursor with
  | zero => rfl
  | succ budget ih =>
      have law := step_preserves context cursor
      cases hs : step context cursor with
      | next next =>
          simp only [hs] at law
          simpa only [drive, hs, law] using ih next
      | complete answers =>
          simp only [hs] at law
          simpa only [drive, hs] using law

theorem sourceBatch_clean (context : Context) (inputs : List Int) :
    ProducerCompletion.reference (sourceBatch context inputs) = sourceBatch context inputs := by
  rw [← OrderedHEBoundary.keep_eq_completion]
  apply HEReturns.keep_clean
  intro answer member
  rw [sourceBatch_exact] at member
  obtain ⟨n, _, rfl⟩ := List.mem_map.mp member
  rfl

theorem initial_residual (context : Context) (inputs : List Int) :
    residual context (initial context inputs) = inputs.map squareResult := by
  simp only [residual, initial, List.reverse_nil, List.nil_append, pendingSource]
  rw [sourceBatch_clean, sourceBatch_exact]

def ready (context : Context) (saved : ResultSet) (inputs : List Int) : Cursor context :=
  ⟨⟨saved, []⟩, none, inputs⟩

/-- Entering a typed call, executing its admitted arithmetic, and collecting
its one return are three distinct transitions. -/
theorem drive_three (context : Context) (budget : Nat) (saved : ResultSet)
    (n : Int) (rest : List Int) :
    drive context (budget + 3) (ready context saved (n :: rest)) =
      drive context budget (ready context (squareResult n :: saved) rest) := rfl

theorem drive_complete_saved (context : Context) (inputs : List Int) (saved : ResultSet) :
    drive context (3 * inputs.length + 1) (ready context saved inputs) =
      (some (ProducerCompletion.reference (saved.reverse ++ inputs.map squareResult)), none) := by
  induction inputs generalizing saved with
  | nil => simp [drive, step, ready, ProducerCompletion.step]
  | cons n rest ih =>
      rw [show 3 * (n :: rest).length + 1 = (3 * rest.length + 1) + 3 by simp; omega,
        drive_three, ih]
      simp only [List.reverse_cons, List.map_cons, List.append_assoc, List.singleton_append]

/-- The complete retained realization returns the source square calls in
their original order, including duplicate values and their binding records.
The count is administrative transitions, not native instruction cost. -/
theorem drive_complete (context : Context) (inputs : List Int) :
    drive context (3 * inputs.length + 1) (initial context inputs) =
      (some (inputs.map squareResult), none) := by
  change drive context (3 * inputs.length + 1) (ready context [] inputs) = _
  rw [drive_complete_saved]
  simp only [List.reverse_nil, List.nil_append]
  rw [← sourceBatch_exact context inputs, sourceBatch_clean, sourceBatch_exact]

/-- Every partial run retains exactly the still-owed source result. -/
theorem drive_initial_preserves (context : Context) (budget : Nat) (inputs : List Int) :
    match drive context budget (initial context inputs) with
    | (some answers, none) => answers = inputs.map squareResult
    | (none, some next) => residual context next = inputs.map squareResult
    | _ => False := by
  have law := drive_preserves context budget (initial context inputs)
  rw [initial_residual] at law
  exact law

namespace Controls

/-- An ordinary collection requests an evaluated value at the undefined
expected type; the typed sq head still owes its declared Number range. -/
def collectionContext : Context :=
  ⟨0, [], rfl, Atom.undefinedType, by decide, by decide, by decide⟩

theorem three_source_inputs :
    sourceBatch collectionContext [2, -2, 3] =
      [(num 4, squareBindings 2), (num 4, squareBindings (-2)), (num 9, squareBindings 3)] := by
  rw [sourceBatch_exact]
  rfl

theorem retained_collection :
    drive collectionContext 10 (initial collectionContext [2, -2, 3]) =
      (some [(num 4, squareBindings 2), (num 4, squareBindings (-2)),
        (num 9, squareBindings 3)], none) :=
  drive_complete collectionContext [2, -2, 3]

/-- Having consumed the last arithmetic answer is not yet producer
completion: the ordered prefix remains retained until publication. -/
theorem budget_three_is_not_complete :
    drive collectionContext 3 (initial collectionContext [2]) =
      (none, some (ready collectionContext [squareResult 2] [])) ∧
    drive collectionContext 4 (initial collectionContext [2]) =
      (some [squareResult 2], none) := by
  constructor <;> rfl

/-- Distinct producer occurrences with the same numeric value keep their
separate equation records. Deduplicating them would lose source results. -/
theorem equal_values_distinct_records :
    (squareResult 2).1 = (squareResult (-2)).1 ∧
      (squareResult 2).2 ≠ (squareResult (-2)).2 := by
  constructor <;> decide

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypedSquareCollection
