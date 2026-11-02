import Mettapedia.Languages.MeTTa.PeTTa.Eval

/-!
# Captured-input PeTTa fold driver

The named host procedure returns its accumulator on an empty list and calls
the reducer on `(accumulator, item)` before recursively processing the tail.
The five-argument source form supplies a body with two local parameter slots.
This module specifies that driver for pure, single-answer callbacks using the
existing PeTTa operational judgment for every callback body.

The driver is separate from `Eval`, whose current closed primitive table does
not contain foldl-atom. The captured surface rules below do not assert that
the old evaluator already dispatches this host operation. Evaluating arbitrary
outer argument expressions, effectful/nondeterministic host folds, callback
exceptions and native dispatch correspondence remain separate boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.FoldSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Eval SpaceSemantics

inductive Callback
  | named (head : String)
  | inline (captured : Subst) (accumulatorName itemName : String) (body : Atom)

def bindings : Callback → Atom → Atom → Subst
  | .named _, accumulator, item => [("fold-accumulator", accumulator), ("fold-item", item)]
  | .inline captured accumulatorName itemName _, accumulator, item =>
      (accumulatorName, accumulator) :: (itemName, item) :: captured

def expression : Callback → Atom
  | .named head => .expression [.symbol head, .var "fold-accumulator", .var "fold-item"]
  | .inline _ _ _ body => body

def Invokes (program : Program) (callback : Callback) (state : Effects.State)
    (accumulator item value : Atom) : Prop :=
  PureReturns program (bindings callback accumulator item) state (expression callback) state value

theorem invokes_unique {program : Program} {callback : Callback} {state : Effects.State}
    {accumulator item first second : Atom}
    (one : Invokes program callback state accumulator item first)
    (two : Invokes program callback state accumulator item second) : first = second := by
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program _ state state _ second two
  have answers := (pure_returns_completed_iff program _ state state _ first one
    state [second] [] []).mp ⟨fuel, completed⟩
  exact (List.cons.inj answers.2.1).1.symm

/-- This is the reference driver relation, not an optimizer's transition
equality premise. Each iteration contains an actual source callback derivation. -/
inductive Evaluates (program : Program) (callback : Callback) (state : Effects.State) :
    List Atom → Atom → Atom → Prop
  | nil (accumulator : Atom) : Evaluates program callback state [] accumulator accumulator
  | cons {item : Atom} {rest : List Atom} {accumulator next result : Atom} :
      Invokes program callback state accumulator item next →
      Evaluates program callback state rest next result →
      Evaluates program callback state (item :: rest) accumulator result

theorem evaluates_unique {program : Program} {callback : Callback} {state : Effects.State}
    {items : List Atom} {initial first second : Atom}
    (one : Evaluates program callback state items initial first)
    (two : Evaluates program callback state items initial second) : first = second := by
  induction one generalizing second with
  | nil accumulator => cases two; rfl
  | cons invoked rest ih =>
      cases two with
      | cons other later =>
          have same := invokes_unique invoked other
          subst same
          exact ih later

theorem evaluates_append {program : Program} {callback : Callback} {state : Effects.State}
    {first later : List Atom} {initial middle result : Atom}
    (one : Evaluates program callback state first initial middle)
    (two : Evaluates program callback state later middle result) :
    Evaluates program callback state (first ++ later) initial result := by
  induction one with
  | nil => exact two
  | cons invoked rest ih => exact .cons invoked (ih two)

theorem evaluates_append_iff {program : Program} {callback : Callback} {state : Effects.State}
    (first later : List Atom) (initial result : Atom) :
    Evaluates program callback state (first ++ later) initial result ↔
      ∃ middle, Evaluates program callback state first initial middle ∧
        Evaluates program callback state later middle result := by
  constructor
  · intro evaluated
    induction first generalizing initial with
    | nil => exact ⟨initial, .nil _, evaluated⟩
    | cons item rest ih =>
        cases evaluated with
        | cons invoked laterRun =>
            obtain ⟨middle, prefixRun, suffixRun⟩ := ih _ laterRun
            exact ⟨middle, .cons invoked prefixRun, suffixRun⟩
  · rintro ⟨middle, one, two⟩
    exact evaluates_append one two

/-- The accumulator after each callback is a stronger observation than the
final accumulator. It is retained explicitly when this observation is chosen. -/
inductive Trace (program : Program) (callback : Callback) (state : Effects.State) :
    List Atom → Atom → List Atom → Prop
  | nil (accumulator : Atom) : Trace program callback state [] accumulator []
  | cons {item : Atom} {rest : List Atom} {accumulator next : Atom} {states : List Atom} :
      Invokes program callback state accumulator item next →
      Trace program callback state rest next states →
      Trace program callback state (item :: rest) accumulator (next :: states)

theorem trace_length {program : Program} {callback : Callback} {state : Effects.State}
    {items : List Atom} {initial : Atom} {states : List Atom}
    (trace : Trace program callback state items initial states) : states.length = items.length := by
  induction trace with
  | nil => rfl
  | cons _ _ ih => simpa using congrArg Nat.succ ih

theorem trace_final {program : Program} {callback : Callback} {state : Effects.State}
    {items : List Atom} {initial : Atom} {states : List Atom}
    (trace : Trace program callback state items initial states) :
    Evaluates program callback state items initial (states.getLast?.getD initial) := by
  induction trace with
  | nil => exact .nil _
  | cons invoked later ih =>
      convert Evaluates.cons invoked ih using 1
      simp only [List.getLast?_cons, Option.getD_some]

def namedSurface (listName initialName head : String) : Atom :=
  .expression [.symbol "foldl-atom", .var listName, .var initialName, .symbol head]

def inlineSurface (listName initialName accumulatorName itemName : String) (body : Atom) : Atom :=
  .expression [.symbol "foldl-atom", .var listName, .var initialName,
    .var accumulatorName, .var itemName, body]

/-- Captured outer values are read exactly once. Local binder admission is
explicit; this rule does not overwrite an already captured caller variable. -/
inductive SurfaceEvaluates (program : Program) (caller : Subst) (state : Effects.State) :
    Atom → Atom → Prop
  | named (listName initialName head : String) (items : List Atom) (initial result : Atom)
      (listFound : caller.lookup listName = some (.expression items))
      (initialFound : caller.lookup initialName = some initial)
      (fold : Evaluates program (.named head) state items initial result) :
      SurfaceEvaluates program caller state (namedSurface listName initialName head) result
  | inline (listName initialName accumulatorName itemName : String) (body : Atom)
      (items : List Atom) (initial result : Atom)
      (listFound : caller.lookup listName = some (.expression items))
      (initialFound : caller.lookup initialName = some initial)
      (distinct : accumulatorName ≠ itemName)
      (freshAccumulator : caller.lookup accumulatorName = none)
      (freshItem : caller.lookup itemName = none)
      (fold : Evaluates program (.inline caller accumulatorName itemName body) state items initial result) :
      SurfaceEvaluates program caller state (inlineSurface listName initialName accumulatorName itemName body) result

theorem surface_unique {program : Program} {caller : Subst} {state : Effects.State}
    {source first second : Atom}
    (one : SurfaceEvaluates program caller state source first)
    (two : SurfaceEvaluates program caller state source second) : first = second := by
  cases one with
  | named listName initialName head items initial result listFound initialFound fold =>
      cases two with
      | named _ _ _ otherItems otherInitial _ otherList otherInitialFound otherFold =>
          have rowsEq := Atom.expression.inj (Option.some.inj (listFound.symm.trans otherList))
          have initialEq := Option.some.inj (initialFound.symm.trans otherInitialFound)
          subst otherItems
          subst otherInitial
          exact evaluates_unique fold otherFold
  | inline listName initialName accumulatorName itemName body items initial result listFound initialFound distinct freshAcc freshItem fold =>
      cases two with
      | inline _ _ _ _ _ otherItems otherInitial _ otherList otherInitialFound _ _ _ otherFold =>
          have rowsEq := Atom.expression.inj (Option.some.inj (listFound.symm.trans otherList))
          have initialEq := Option.some.inj (initialFound.symm.trans otherInitialFound)
          subst otherItems
          subst otherInitial
          exact evaluates_unique fold otherFold

namespace Controls

def sumProgram : Program := {equations := [], declarations := []}

theorem empty_never_calls_callback (state : Effects.State) :
    Evaluates sumProgram (.named "unknown-effectful-function") state []
      (.symbol "held") (.symbol "held") := .nil _

theorem local_parameters_have_distinct_cells (captured : Subst) (accumulator item : Atom) :
    (bindings (.inline captured "a" "x" (.var "a")) accumulator item).lookup "a" = some accumulator ∧
    (bindings (.inline captured "a" "x" (.var "a")) accumulator item).lookup "x" = some item := by
  simp [bindings, Subst.lookup]

theorem aliasing_parameters_loses_the_item (captured : Subst) :
    (bindings (.inline captured "x" "x" (.var "x")) (.symbol "acc") (.symbol "item")).lookup "x" =
      some (.symbol "acc") := by simp [bindings, Subst.lookup]

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.FoldSource
