import Mettapedia.Languages.MeTTa.PeTTa.FoldSource

/-!
# Operand preparation and the host-fold boundary

The source list expression is evaluated before the initial accumulator, using
the existing PeTTa evaluator. A ready receipt preserves both actual evaluation
paths and the resulting world. Specialization occurs only after this boundary.
It may not replay operand effects if callback admission subsequently fails.

Unsupported shapes, non-singleton operands, I/O, faults and exhaustion are
handed off with the current outcome and phase. No post-evaluation refusal is
encoded as a fresh invocation of the original source. These are formal host
adapter semantics, not a change to the general evaluator's primitive table.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.FoldSourceBoundary

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Eval SpaceSemantics

inductive Code
  | named (items initial : Atom) (head : String)
  | inline (items initial : Atom) (accumulatorName itemName : String) (body : Atom)
  deriving DecidableEq

def Code.items : Code → Atom
  | .named items _ _ | .inline items _ _ _ _ => items

def Code.initial : Code → Atom
  | .named _ initial _ | .inline _ initial _ _ _ => initial

def Code.source : Code → Atom
  | .named items initial head => .expression [.symbol "foldl-atom", items, initial, .symbol head]
  | .inline items initial accumulatorName itemName body =>
      .expression [.symbol "foldl-atom", items, initial, .var accumulatorName, .var itemName, body]

def Code.callback (caller : Subst) : Code → FoldSource.Callback
  | .named _ _ head => .named head
  | .inline _ _ accumulatorName itemName body => .inline caller accumulatorName itemName body

def parse : Atom → Option Code
  | .expression [.symbol "foldl-atom", items, initial, .symbol head] => some (.named items initial head)
  | .expression [.symbol "foldl-atom", items, initial, .var accumulatorName, .var itemName, body] =>
      some (.inline items initial accumulatorName itemName body)
  | _ => none

theorem parse_source (code : Code) : parse code.source = some code := by cases code <;> rfl

theorem parse_exact (source : Atom) (code : Code) (parsed : parse source = some code) :
    code.source = source := by
  unfold parse at parsed
  split at parsed <;> cases parsed <;> rfl

def Scoped (caller : Subst) : Code → Prop
  | .named _ _ _ => True
  | .inline _ _ accumulatorName itemName _ => accumulatorName ≠ itemName ∧
      caller.lookup accumulatorName = none ∧ caller.lookup itemName = none

instance (caller : Subst) (code : Code) : Decidable (Scoped caller code) := by
  cases code <;> unfold Scoped <;> infer_instance

/-- Source sequencing is independent of the aggregate or native worker. -/
inductive Evaluates (program : Program) (caller : Subst) (code : Code) :
    Effects.State → Effects.State → Atom → Prop
  | intro {before middle after : Effects.State} {items : List Atom} {initial result : Atom}
      (scopeOK : Scoped caller code)
      (listReturns : PureReturns program caller before code.items middle (.expression items))
      (initialReturns : PureReturns program caller middle code.initial after initial)
      (fold : FoldSource.Evaluates program (code.callback caller) after items initial result) :
      Evaluates program caller code before after result

structure Captured (program : Program) (caller : Subst) (code : Code) (before : Effects.State) where
  items : List Atom
  initial : Atom
  middle : Effects.State
  after : Effects.State
  scopeOK : Scoped caller code
  listReturns : PureReturns program caller before code.items middle (.expression items)
  initialReturns : PureReturns program caller middle code.initial after initial

theorem Captured.finish {program : Program} {caller : Subst} {code : Code} {before : Effects.State}
    (captured : Captured program caller code before) (result : Atom)
    (fold : FoldSource.Evaluates program (code.callback caller) captured.after captured.items captured.initial result) :
    Evaluates program caller code before captured.after result :=
  .intro captured.scopeOK captured.listReturns captured.initialReturns fold

private theorem returns_unique {program : Program} {caller : Subst} {before first second : Effects.State}
    {source one two : Atom} (left : PureReturns program caller before source first one)
    (right : PureReturns program caller before source second two) : first = second ∧ one = two := by
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program caller before second source two right
  obtain ⟨stateEq, answersEq, _, _⟩ :=
    (pure_returns_completed_iff program caller before first source one left second [two] [] []).mp ⟨fuel, completed⟩
  exact ⟨stateEq.symm, (List.cons.inj answersEq).1.symm⟩

theorem evaluates_unique {program : Program} {caller : Subst} {code : Code}
    {before first second : Effects.State} {one two : Atom}
    (left : Evaluates program caller code before first one)
    (right : Evaluates program caller code before second two) : first = second ∧ one = two := by
  cases left with
  | intro scopeOK listReturns initialReturns fold =>
      cases right with
      | intro otherScope otherList otherInitial otherFold =>
          obtain ⟨rfl, sameItems⟩ := returns_unique listReturns otherList
          cases Atom.expression.inj sameItems
          obtain ⟨rfl, rfl⟩ := returns_unique initialReturns otherInitial
          exact ⟨rfl, FoldSource.evaluates_unique fold otherFold⟩

/-- Handoffs retain the exact evaluator outcome at its own phase. In the
second phase the list operand has already been captured and must not run again. -/
inductive Handoff
  | listOperand (outcome : Outcome)
  | initialOperand (items : List Atom) (middle : Effects.State) (outcome : Outcome)

inductive Preparation (program : Program) (caller : Subst) (code : Code) (before : Effects.State)
  | reference
  | handoff (saved : Handoff)
  | ready (captured : Captured program caller code before)

def prepare (listFuel initialFuel : Nat) (program : Program) (caller : Subst)
    (code : Code) (before : Effects.State) : Preparation program caller code before :=
  if scopeOK : Scoped caller code then
    match first : run program listFuel {state := before, control := .evaluate caller code.items} with
    | .complete middle [.expression items] [] [] =>
        match second : run program initialFuel {state := middle, control := .evaluate caller code.initial} with
        | .complete after [initial] [] [] =>
            .ready ⟨items, initial, middle, after, scopeOK,
              completed_run_has_path program listFuel _ _ _ _ _ first,
              completed_run_has_path program initialFuel _ _ _ _ _ second⟩
        | outcome => .handoff (.initialOperand items middle outcome)
    | outcome => .handoff (.listOperand outcome)
  else .reference

theorem invalid_scope_uses_reference (listFuel initialFuel : Nat) (program : Program)
    (caller : Subst) (code : Code) (before : Effects.State) (invalid : ¬Scoped caller code) :
    prepare listFuel initialFuel program caller code before = .reference := by simp [prepare, invalid]

/-- Once source operand evaluation has begun, refusal cannot advertise an
untouched entrance. It must carry the exact phase/outcome or a ready receipt. -/
theorem scoped_ne_reference (listFuel initialFuel : Nat) (program : Program)
    (caller : Subst) (code : Code) (before : Effects.State) (scopeOK : Scoped caller code) :
    prepare listFuel initialFuel program caller code before ≠ .reference := by
  simp only [prepare, dif_pos scopeOK]
  split
  · split <;> simp
  · simp

/-- The retained entrance is runtime data, not merely erased certificate
indices. This is a logical holder inventory, not a native tracing-GC proof. -/
structure Request where
  program : Program
  caller : Subst
  code : Code
  before : Effects.State

structure Envelope where
  saved : Request
  phase : Preparation saved.program saved.caller saved.code saved.before

def retainAndPrepare (listFuel initialFuel : Nat) (request : Request) : Envelope :=
  ⟨request, prepare listFuel initialFuel request.program request.caller request.code request.before⟩

theorem preparation_retains_entrance (listFuel initialFuel : Nat) (request : Request) :
    (retainAndPrepare listFuel initialFuel request).saved = request := rfl

end Mettapedia.Languages.MeTTa.PeTTa.FoldSourceBoundary
