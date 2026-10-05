import Mettapedia.Languages.Chaitin.Expressions
import Mettapedia.Languages.TuringMachine.Configurations

/-!
# A Turing-table interpreter written in Chaitin's Lisp

The program below uses the proper lists, quoted lambdas, dynamic bindings,
and primitive operations of Chaitin's 1997 interpreter. A transition table
is data: its first applicable row is found by recursive `car`/`cdr` search.
There is no table-lookup or Turing-step primitive in the object language.

Configurations retain both finite half-tapes, including their trailing blank
cells. The data lemmas compare this representation with the existing table
semantics. Operational correctness belongs to the evaluator comparison.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Chaitin.TuringPrograms

open Expressions

/-- Tape cells are unsigned Lisp integers, in nearest-cell-first order. -/
def encodeCells (cells : List Nat) : SExpr := .list (cells.map .number)

def decodeNumerals : List SExpr → Option (List Nat)
  | [] => some []
  | .number value :: rest => (decodeNumerals rest).map (value :: ·)
  | _ :: _ => none

def decodeCells : SExpr → Option (List Nat)
  | .list values => decodeNumerals values
  | _ => none

/-- Direction is a word, so it cannot be confused with a state or tape symbol. -/
def encodeMove : TuringMachine.Move → SExpr
  | .left => .symbol "left"
  | .right => .symbol "right"

def decodeMove : SExpr → Option TuringMachine.Move
  | .symbol "left" => some .left
  | .symbol "right" => some .right
  | _ => none

/-- A row has fields `(state scanned write direction next)`. -/
def encodeTransition (entry : TuringMachine.Transition) : SExpr :=
  .list [.number entry.state, .number entry.read, .number entry.write,
    encodeMove entry.move, .number entry.next]

def decodeTransition : SExpr → Option TuringMachine.Transition
  | .list [.number state, .number scanned, .number write, move, .number next] =>
      (decodeMove move).map (fun direction => ⟨state, scanned, write, direction, next⟩)
  | _ => none

/-- A complete configuration has fields `(state left scanned right)`. -/
def encodeConfiguration (configuration : TuringMachine.Configuration) : SExpr :=
  .list [.number configuration.state, encodeCells configuration.left,
    .number configuration.scanned, encodeCells configuration.right]

def decodeConfiguration : SExpr → Option TuringMachine.Configuration
  | .list [.number state, left, .number scanned, right] => do
      let leftCells ← decodeCells left
      let rightCells ← decodeCells right
      pure ⟨state, leftCells, scanned, rightCells⟩
  | _ => none

/-- The order of the table is retained, including duplicate rows. -/
def encodeTable (entries : List TuringMachine.Transition) : SExpr :=
  .list (entries.map encodeTransition)

@[simp] theorem decodeNumerals_map_number (cells : List Nat) :
    decodeNumerals (cells.map .number) = some cells := by
  induction cells with
  | nil => rfl
  | cons value rest recurse => simp [decodeNumerals, recurse]

@[simp] theorem decodeCells_encodeCells (cells : List Nat) :
    decodeCells (encodeCells cells) = some cells := by
  simp [decodeCells, encodeCells]

@[simp] theorem decodeMove_encodeMove (move : TuringMachine.Move) :
    decodeMove (encodeMove move) = some move := by
  cases move <;> rfl

@[simp] theorem decodeTransition_encodeTransition (entry : TuringMachine.Transition) :
    decodeTransition (encodeTransition entry) = some entry := by
  cases entry with
  | mk state scanned write move next => cases move <;> rfl

@[simp] theorem decodeConfiguration_encodeConfiguration (configuration : TuringMachine.Configuration) :
    decodeConfiguration (encodeConfiguration configuration) = some configuration := by
  cases configuration
  simp [decodeConfiguration, encodeConfiguration]

theorem encodeCells_injective : Function.Injective encodeCells := by
  intro first second same
  have decoded := congrArg decodeCells same
  simpa using decoded

theorem encodeMove_injective : Function.Injective encodeMove := by
  intro first second same
  have decoded := congrArg decodeMove same
  simpa using decoded

theorem encodeTransition_injective : Function.Injective encodeTransition := by
  intro first second same
  have decoded := congrArg decodeTransition same
  simpa using decoded

theorem encodeConfiguration_injective : Function.Injective encodeConfiguration := by
  intro first second same
  have decoded := congrArg decodeConfiguration same
  simpa using decoded

theorem encodeTable_injective : Function.Injective encodeTable := by
  intro first second same
  apply List.map_injective_iff.mpr encodeTransition_injective
  exact SExpr.list.inj same

@[simp] theorem field_transition_state (entry : TuringMachine.Transition) :
    SExpr.field 0 (encodeTransition entry) = .number entry.state := rfl
@[simp] theorem field_transition_scanned (entry : TuringMachine.Transition) :
    SExpr.field 1 (encodeTransition entry) = .number entry.read := rfl
@[simp] theorem field_transition_write (entry : TuringMachine.Transition) :
    SExpr.field 2 (encodeTransition entry) = .number entry.write := rfl
@[simp] theorem field_transition_move (entry : TuringMachine.Transition) :
    SExpr.field 3 (encodeTransition entry) = encodeMove entry.move := rfl
@[simp] theorem field_transition_next (entry : TuringMachine.Transition) :
    SExpr.field 4 (encodeTransition entry) = .number entry.next := rfl

@[simp] theorem field_configuration_state (configuration : TuringMachine.Configuration) :
    SExpr.field 0 (encodeConfiguration configuration) = .number configuration.state := rfl
@[simp] theorem field_configuration_left (configuration : TuringMachine.Configuration) :
    SExpr.field 1 (encodeConfiguration configuration) = encodeCells configuration.left := rfl
@[simp] theorem field_configuration_scanned (configuration : TuringMachine.Configuration) :
    SExpr.field 2 (encodeConfiguration configuration) = .number configuration.scanned := rfl
@[simp] theorem field_configuration_right (configuration : TuringMachine.Configuration) :
    SExpr.field 3 (encodeConfiguration configuration) = encodeCells configuration.right := rfl

@[simp] theorem encodeCells_nil : encodeCells [] = SExpr.nil := rfl
@[simp] theorem encodeCells_cons (value : Nat) (rest : List Nat) :
    encodeCells (value :: rest) = SExpr.cons (.number value) (encodeCells rest) := rfl

/-- Moving beyond a represented half-tape reads blank zero. -/
def headOrBlank (cells : SExpr) : SExpr :=
  if cells = SExpr.nil then .number 0 else cells.car

@[simp] theorem headOrBlank_encodeCells (cells : List Nat) :
    headOrBlank (encodeCells cells) = .number (cells.headD 0) := by
  cases cells <;> simp [headOrBlank, encodeCells, SExpr.nil, SExpr.car]

@[simp] theorem cdr_encodeCells (cells : List Nat) :
    (encodeCells cells).cdr = encodeCells cells.tail := by
  cases cells <;> rfl

/-- Primitive list operations producing the data of one write-then-move step. -/
def moveData (entry configuration : SExpr) : SExpr :=
  let left := SExpr.field 1 configuration
  let right := SExpr.field 3 configuration
  let write := SExpr.field 2 entry
  if SExpr.field 3 entry = .symbol "right" then
    .list [SExpr.field 4 entry, SExpr.cons write left, headOrBlank right, right.cdr]
  else
    .list [SExpr.field 4 entry, left.cdr, headOrBlank left, SExpr.cons write right]

theorem moveData_encode (entry : TuringMachine.Transition) (configuration : TuringMachine.Configuration) :
    moveData (encodeTransition entry) (encodeConfiguration configuration) =
      encodeConfiguration (configuration.after entry) := by
  simp only [moveData, field_configuration_left, field_configuration_right,
    field_transition_write, field_transition_move, field_transition_next]
  rcases entry with ⟨state, scanned, write, move, next⟩
  rcases configuration with ⟨control, left, current, right⟩
  cases move with
  | left =>
      cases left <;>
        simp [encodeMove, TuringMachine.Configuration.after,
          encodeConfiguration, encodeCells, headOrBlank, SExpr.car, SExpr.cdr,
          SExpr.cons, SExpr.nil]
  | right =>
      cases right <;>
        simp [encodeMove, TuringMachine.Configuration.after,
          encodeConfiguration, encodeCells, headOrBlank, SExpr.car, SExpr.cdr,
          SExpr.cons, SExpr.nil]

/-- Recursive first-match search on row values. `nil` marks absence of a row. -/
def lookupRows (state scanned : SExpr) : List SExpr → SExpr
  | [] => SExpr.nil
  | row :: rest =>
      if SExpr.field 0 row = state then
        if SExpr.field 1 row = scanned then row else lookupRows state scanned rest
      else lookupRows state scanned rest

theorem lookupRows_encode (entries : List TuringMachine.Transition) (state scanned : Nat) :
    lookupRows (.number state) (.number scanned) (entries.map encodeTransition) =
      ((entries.find? (fun entry => entry.state == state && entry.read == scanned)).map
        encodeTransition).getD SExpr.nil := by
  induction entries with
  | nil => rfl
  | cons entry rest recurse =>
      by_cases states : entry.state = state
      · by_cases symbols : entry.read = scanned
        · simp [lookupRows, states, symbols]
        · simp [lookupRows, states, symbols, recurse]
      · simp [lookupRows, states, recurse]

theorem lookupRows_eq_entryFor (machine : TuringMachine.Machine) (configuration : TuringMachine.Configuration) :
    lookupRows (.number configuration.state) (.number configuration.scanned)
      (machine.transitions.map encodeTransition) =
      ((machine.entryFor configuration).map encodeTransition).getD SExpr.nil :=
  lookupRows_encode machine.transitions configuration.state configuration.scanned

theorem lookupRows_nil_iff (machine : TuringMachine.Machine) (configuration : TuringMachine.Configuration) :
    lookupRows (.number configuration.state) (.number configuration.scanned)
      (machine.transitions.map encodeTransition) = SExpr.nil ↔
        machine.entryFor configuration = none := by
  rw [lookupRows_eq_entryFor]
  cases machine.entryFor configuration with
  | none => simp
  | some entry => simp [encodeTransition, SExpr.nil]

/-! ## The historical object program -/

/-- A shared recursive call used by both failed comparisons. -/
def lookupRestExpr : SExpr :=
  call "find-row" [call "cdr" [.symbol "rows"], .symbol "state", .symbol "scanned"]

/-- Search a table left-to-right, comparing both state and scanned symbol. -/
def lookupBody : SExpr :=
  let row := call "car" [.symbol "rows"]
  ifExpr (equalExpr (.symbol "rows") (.symbol "nil")) (.symbol "nil")
    (ifExpr (equalExpr (fieldExpr 0 row) (.symbol "state"))
      (ifExpr (equalExpr (fieldExpr 1 row) (.symbol "scanned")) row lookupRestExpr)
      lookupRestExpr)

def lookupProgram : SExpr := quotedLambda ["rows", "state", "scanned"] lookupBody

def blankHeadExpr (cells : SExpr) : SExpr :=
  ifExpr (equalExpr cells (.symbol "nil")) (.number 0) (call "car" [cells])

/-- One step writes before moving, preserving every represented tape cell. -/
def transitionBody : SExpr :=
  let entry := .symbol "entry"
  let configuration := .symbol "configuration"
  let left := fieldExpr 1 configuration
  let right := fieldExpr 3 configuration
  let write := fieldExpr 2 entry
  let next := fieldExpr 4 entry
  ifExpr (equalExpr (fieldExpr 3 entry) (quote (.symbol "right")))
    (listExpr [next, consExpr write left, blankHeadExpr right, call "cdr" [right]])
    (listExpr [next, call "cdr" [left], blankHeadExpr left, consExpr write right])

def transitionProgram : SExpr := quotedLambda ["entry", "configuration"] transitionBody

/-- A missing row halts; otherwise the interpreter recurs on the stepped configuration. -/
def interpreterBody : SExpr :=
  let configuration := .symbol "configuration"
  letValue "selected"
    (call "find-row" [.symbol "table", fieldExpr 0 configuration, fieldExpr 2 configuration])
    (ifExpr (equalExpr (.symbol "selected") (.symbol "nil")) configuration
      (call "run-table" [.symbol "table",
        call "move-row" [.symbol "selected", configuration]]))

def loopProgram : SExpr := quotedLambda ["table", "configuration"] interpreterBody

/-- A single source expression interprets any finite table and complete configuration. -/
def interpreterProgram (table configuration : SExpr) : SExpr :=
  letValue "find-row" lookupProgram
    (letValue "move-row" transitionProgram
      (letValue "run-table" loopProgram
        (call "run-table" [table, configuration])))

/-- The closed, ordinary Lisp program for a particular machine and input. -/
def machineProgram (machine : TuringMachine.Machine) (configuration : TuringMachine.Configuration) : SExpr :=
  interpreterProgram (quote (encodeTable machine.transitions))
    (quote (encodeConfiguration configuration))

/-! ## Separating data controls -/

theorem distinct_move_words : encodeMove .left ≠ encodeMove .right := by decide

theorem malformed_configuration_rejected :
    decodeConfiguration (.list [.number 0, .symbol "bad", .number 0, SExpr.nil]) = none := rfl

theorem write_precedes_right_move :
    moveData (encodeTransition ⟨3, 7, 9, .right, 4⟩)
      (encodeConfiguration ⟨3, [8], 7, [6, 5]⟩) =
        encodeConfiguration ⟨4, [9, 8], 6, [5]⟩ := by
  exact moveData_encode _ _

theorem right_edge_supplies_blank :
    moveData (encodeTransition ⟨3, 7, 9, .right, 4⟩)
      (encodeConfiguration ⟨3, [8], 7, []⟩) =
        encodeConfiguration ⟨4, [9, 8], 0, []⟩ := by
  exact moveData_encode _ _

theorem wrong_symbol_does_not_match :
    lookupRows (.number 3) (.number 7)
      [encodeTransition ⟨3, 6, 9, .right, 4⟩] = SExpr.nil := by decide

theorem first_matching_row_wins :
    lookupRows (.number 3) (.number 7)
      [encodeTransition ⟨3, 7, 9, .right, 4⟩,
        encodeTransition ⟨3, 7, 8, .left, 5⟩] =
          encodeTransition ⟨3, 7, 9, .right, 4⟩ := by decide

end Mettapedia.Languages.Chaitin.TuringPrograms
