import Mettapedia.OSLF.MeTTaIL.GeneratedRuleValidation
import Mettapedia.OSLF.MeTTaIL.DecimalNames
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# Turing machines as language definitions

A Turing machine is authored here in the plainest way its definition allows.
The sorts are states, tape symbols, half-tapes, tapes with a scanned cell, and
configurations.  The constructor `Run` builds a configuration from the state
of the finite control and the tape; the rewrites are the transition table,
one pair of rules for every entry, together with the movement of the head.

States and tape symbols are numbered, and are written as unary numerals of
their own sorts, so the signature is the same for every machine and only the
rewrites depend on the table.  Symbol zero is the blank: moving past the last
written cell of a half-tape scans a blank.

Every rewrite is premise-free and is headed by `Run`.  The two operands of
`Run` have different sorts, a state and a tape, and neither is the sort of
configurations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.TuringMachine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL

/-- The direction in which the head moves after writing. -/
inductive Move where
  | left
  | right
deriving DecidableEq, Repr

/-- One entry of a transition table: in state `state`, scanning `read`, the
machine writes `write`, moves the head, and enters state `next`. -/
structure Transition where
  state : Nat
  read : Nat
  write : Nat
  move : Move
  next : Nat
deriving DecidableEq, Repr

/-- A Turing machine, given by its finite transition table over numbered
states and numbered tape symbols.  Symbol zero is the blank. -/
structure Machine where
  transitions : List Transition
deriving Repr

/-- The state numbered `index`, as a term of sort `State`. -/
def stateTerm (index : Nat) : Pattern := Pattern.unary "QZero" "QSucc" index

/-- The tape symbol numbered `index`, as a term of sort `Symbol`. -/
def symbolTerm (index : Nat) : Pattern := Pattern.unary "SZero" "SSucc" index

/-- The constructors: unary numerals for states and symbols, half-tapes as
lists of symbols, a tape as the two half-tapes around the scanned symbol, and
a configuration as a state running on a tape. -/
def terms : List GrammarRule := [
    { label := "QZero", category := "State", params := [], syntaxPattern := [] },
    { label := "QSucc", category := "State",
      params := [.simple "state" (.base "State")],
      syntaxPattern := [.nonTerminal "state"] },
    { label := "SZero", category := "Symbol", params := [], syntaxPattern := [] },
    { label := "SSucc", category := "Symbol",
      params := [.simple "symbol" (.base "Symbol")],
      syntaxPattern := [.nonTerminal "symbol"] },
    { label := "Empty", category := "Cells", params := [], syntaxPattern := [] },
    { label := "Cell", category := "Cells",
      params := [.simple "symbol" (.base "Symbol"), .simple "rest" (.base "Cells")],
      syntaxPattern := [.nonTerminal "symbol", .nonTerminal "rest"] },
    { label := "At", category := "Tape",
      params := [.simple "left" (.base "Cells"), .simple "scanned" (.base "Symbol"),
        .simple "right" (.base "Cells")],
      syntaxPattern := [.nonTerminal "left", .nonTerminal "scanned", .nonTerminal "right"] },
    { label := "Run", category := "Config",
      params := [.simple "control" (.base "State"), .simple "tape" (.base "Tape")],
      syntaxPattern := [.nonTerminal "control", .nonTerminal "tape"] }
  ]

/-- A configuration pattern: a control state running on a tape. -/
def run (control tape : Pattern) : Pattern := .apply "Run" [control, tape]

/-- A tape pattern: the cells to the left of the head (nearest first), the
scanned symbol, and the cells to the right. -/
def tapeAt (left scanned right : Pattern) : Pattern :=
  .apply "At" [left, scanned, right]

/-- One written cell in front of a half-tape. -/
def cell (symbol rest : Pattern) : Pattern := .apply "Cell" [symbol, rest]

/-- The half-tape with no written cell. -/
def emptyCells : Pattern := .apply "Empty" []

/-- The rule for a table entry when the cell the head moves onto has been
written. -/
def interiorRule (index : Nat) (entry : Transition) : RewriteRule :=
  match entry.move with
  | .right =>
      { name := "Interior" ++ toString index
        typeContext := [("l", .base "Cells"), ("c", .base "Symbol"), ("r", .base "Cells")]
        premises := []
        left := run (stateTerm entry.state)
          (tapeAt (.fvar "l") (symbolTerm entry.read) (cell (.fvar "c") (.fvar "r")))
        right := run (stateTerm entry.next)
          (tapeAt (cell (symbolTerm entry.write) (.fvar "l")) (.fvar "c") (.fvar "r")) }
  | .left =>
      { name := "Interior" ++ toString index
        typeContext := [("l", .base "Cells"), ("c", .base "Symbol"), ("r", .base "Cells")]
        premises := []
        left := run (stateTerm entry.state)
          (tapeAt (cell (.fvar "c") (.fvar "l")) (symbolTerm entry.read) (.fvar "r"))
        right := run (stateTerm entry.next)
          (tapeAt (.fvar "l") (.fvar "c") (cell (symbolTerm entry.write) (.fvar "r"))) }

/-- The rule for a table entry when the head moves past the last written
cell: the newly scanned symbol is the blank. -/
def edgeRule (index : Nat) (entry : Transition) : RewriteRule :=
  match entry.move with
  | .right =>
      { name := "Edge" ++ toString index
        typeContext := [("l", .base "Cells")]
        premises := []
        left := run (stateTerm entry.state)
          (tapeAt (.fvar "l") (symbolTerm entry.read) emptyCells)
        right := run (stateTerm entry.next)
          (tapeAt (cell (symbolTerm entry.write) (.fvar "l")) (symbolTerm 0) emptyCells) }
  | .left =>
      { name := "Edge" ++ toString index
        typeContext := [("r", .base "Cells")]
        premises := []
        left := run (stateTerm entry.state)
          (tapeAt emptyCells (symbolTerm entry.read) (.fvar "r"))
        right := run (stateTerm entry.next)
          (tapeAt emptyCells (symbolTerm 0) (cell (symbolTerm entry.write) (.fvar "r"))) }

/-- The rewrites of a machine: for each table entry, in order, its interior
rule; then, for each entry, its edge rule. -/
def rewrites (machine : Machine) : List RewriteRule :=
  machine.transitions.mapIdx interiorRule ++ machine.transitions.mapIdx edgeRule

/-- The naive presentation of a Turing machine. -/
def turingMachine (machine : Machine) : LanguageDef :=
  { name := "TuringMachine"
    types := ["State", "Symbol", "Cells", "Tape", "Config"]
    terms := terms
    equations := []
    rewrites := rewrites machine }

@[simp] theorem interiorRule_name (index : Nat) (entry : Transition) :
    (interiorRule index entry).name = "Interior" ++ toString index := by
  unfold interiorRule
  split <;> rfl

@[simp] theorem edgeRule_name (index : Nat) (entry : Transition) :
    (edgeRule index entry).name = "Edge" ++ toString index := by
  unfold edgeRule
  split <;> rfl

/-! ## Validation -/

/-- The constructors of the signature with their arities. -/
def signatureReferences : List (String × Nat) :=
  [("QZero", 0), ("QSucc", 1), ("SZero", 0), ("SSucc", 1), ("Empty", 0),
    ("Cell", 2), ("At", 3), ("Run", 2)]

theorem signatureReferences_declared :
    ∀ reference ∈ signatureReferences,
      LanguageDef.referenceDeclared terms reference = true := by
  decide

/-- Discharge the four obligations of a generated premise-free rule whose
sides are built from the signature, numerals and metavariables. -/
local macro "validate_generated_rule" : tactic =>
  `(tactic|
    (apply LanguageDef.validateRewrite_eq_nil_of_premiseFree
     · rfl
     · simp [turingMachine, LanguageDef.typeNames, TypeExpr.baseNames, TypeDecl.plain]
     · intro reference membership
       apply signatureReferences_declared
       simp [run, tapeAt, cell, emptyCells, stateTerm, symbolTerm, Pattern.constructorRefs,
         Pattern.constructorRefsList, Pattern.constructorRefs_unary] at membership
       simp only [signatureReferences, List.mem_cons, List.not_mem_nil, or_false]
       tauto
     · intro reference membership
       apply signatureReferences_declared
       simp [run, tapeAt, cell, emptyCells, stateTerm, symbolTerm, Pattern.constructorRefs,
         Pattern.constructorRefsList, Pattern.constructorRefs_unary] at membership
       simp only [signatureReferences, List.mem_cons, List.not_mem_nil, or_false]
       tauto
     · intro context
       simp [turingMachine, terms, run, tapeAt, cell, emptyCells, stateTerm, symbolTerm,
         LanguageDef.validateRulePatterns, Pattern.isWellScoped, Pattern.isWellScopedAt,
         Pattern.isWellScopedListAt, LanguageDef.patternFvarNames, Pattern.freeFvarNames,
         LanguageDef.patternBinderNames]))

theorem interiorRule_validates (machine : Machine) (index : Nat) (entry : Transition) :
    LanguageDef.validateRewrite (turingMachine machine) (interiorRule index entry) = [] := by
  unfold interiorRule
  split
  · validate_generated_rule
  · validate_generated_rule

theorem edgeRule_validates (machine : Machine) (index : Nat) (entry : Transition) :
    LanguageDef.validateRewrite (turingMachine machine) (edgeRule index entry) = [] := by
  unfold edgeRule
  split
  · validate_generated_rule
  · validate_generated_rule

/-- The names of the rewrites: one interior and one edge name per table
index. -/
theorem rewrites_names (machine : Machine) :
    (rewrites machine).map (·.name) =
      (List.range machine.transitions.length).map (fun index => "Interior" ++ toString index) ++
        (List.range machine.transitions.length).map (fun index => "Edge" ++ toString index) := by
  unfold rewrites
  rw [List.map_append]
  congr 1
  · apply List.ext_getElem
    · simp
    · intro index first second
      simp
  · apply List.ext_getElem
    · simp
    · intro index first second
      simp

theorem rewrites_names_nodup (machine : Machine) :
    ((rewrites machine).map (·.name)).Nodup := by
  rw [rewrites_names]
  refine List.nodup_append.mpr
    ⟨DecimalNames.prefixed_range_nodup _ _, DecimalNames.prefixed_range_nodup _ _, ?_⟩
  intro interior interiorMember edge edgeMember
  obtain ⟨first, -, rfl⟩ := List.mem_map.mp interiorMember
  obtain ⟨second, -, rfl⟩ := List.mem_map.mp edgeMember
  apply DecimalNames.literal_ne (leftChars := "Interior".toList)
    (rightChars := "Edge".toList) rfl rfl
  intro leftTail rightTail same
  simp at same

/-- Every rewrite of a machine validates against its presentation. -/
theorem rewrites_validate (machine : Machine) :
    ∀ rewrite ∈ (turingMachine machine).rewrites,
      LanguageDef.validateRewrite (turingMachine machine) rewrite = [] := by
  intro rewrite membership
  rcases List.mem_append.mp membership with interior | edge
  · obtain ⟨index, bound, rfl⟩ := List.mem_mapIdx.mp interior
    exact interiorRule_validates machine index _
  · obtain ⟨index, bound, rfl⟩ := List.mem_mapIdx.mp edge
    exact edgeRule_validates machine index _

/-- The naive presentation of every machine passes the declaration gate. -/
theorem turingMachine_validate_eq_nil (machine : Machine) :
    (turingMachine machine).validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  · rfl
  · show (["State", "Symbol", "Cells", "Tape", "Config"] : List String).Nodup
    decide
  · show (terms.map (·.label)).Nodup
    decide
  · exact rewrites_names_nodup machine
  · show ∀ term ∈ terms,
      term.category ∈ (["State", "Symbol", "Cells", "Tape", "Config"] : List String)
    decide
  · show ∀ term ∈ terms, ∀ param ∈ term.params,
      ∀ typeName ∈ (TermParam.typeExpr param).baseNames,
        typeName ∈ (["State", "Symbol", "Cells", "Tape", "Config"] : List String)
    decide
  · show ∀ term ∈ terms, term.syntaxPattern = [] ∨
      term.syntaxPattern = term.params.map (fun param =>
        SyntaxItem.nonTerminal (TermParam.bodyName param))
    decide +kernel
  · exact rewrites_validate machine

/-! ## The shape of the rules -/

/-- Every rewrite of a machine is premise-free. -/
theorem rewrites_premiseFree (machine : Machine) :
    ∀ rewrite ∈ (turingMachine machine).rewrites, rewrite.premises = [] := by
  intro rewrite membership
  rcases List.mem_append.mp membership with interior | edge
  · obtain ⟨index, bound, rfl⟩ := List.mem_mapIdx.mp interior
    unfold interiorRule
    split <;> rfl
  · obtain ⟨index, bound, rfl⟩ := List.mem_mapIdx.mp edge
    unfold edgeRule
    split <;> rfl

/-- Every rewrite of a machine is headed by `Run`, applied to the control
state and the tape. -/
theorem rewrites_headed_by_run (machine : Machine) :
    ∀ rewrite ∈ (turingMachine machine).rewrites,
      ∃ control tape, rewrite.left = .apply "Run" [control, tape] := by
  intro rewrite membership
  rcases List.mem_append.mp membership with interior | edge
  · obtain ⟨index, bound, rfl⟩ := List.mem_mapIdx.mp interior
    unfold interiorRule
    split <;> exact ⟨_, _, rfl⟩
  · obtain ⟨index, bound, rfl⟩ := List.mem_mapIdx.mp edge
    unfold edgeRule
    split <;> exact ⟨_, _, rfl⟩

/-! ## A machine that runs

The machine below walks right over a block of ones and appends a one at the
first blank.  State zero walks; state one has no entry and so halts. -/

/-- Append a one to a block of ones. -/
def appendOne : Machine where
  transitions :=
    [ { state := 0, read := 1, write := 1, move := .right, next := 0 },
      { state := 0, read := 0, write := 1, move := .right, next := 1 } ]

/-- The engine with no external relations. -/
abbrev base : BasePremiseEvaluator := engineBasePremises RelationEnv.empty

/-- State zero scanning the first of two ones. -/
def appendOneStart : Pattern :=
  run (stateTerm 0) (tapeAt emptyCells (symbolTerm 1) (cell (symbolTerm 1) emptyCells))

/-- The head has moved onto the second one. -/
def appendOneSecond : Pattern :=
  run (stateTerm 0) (tapeAt (cell (symbolTerm 1) emptyCells) (symbolTerm 1) emptyCells)

/-- The head has moved past the block and scans a blank. -/
def appendOneBlank : Pattern :=
  run (stateTerm 0)
    (tapeAt (cell (symbolTerm 1) (cell (symbolTerm 1) emptyCells)) (symbolTerm 0) emptyCells)

/-- The one is written and the machine is in its halting state. -/
def appendOneDone : Pattern :=
  run (stateTerm 1)
    (tapeAt (cell (symbolTerm 1) (cell (symbolTerm 1) (cell (symbolTerm 1) emptyCells)))
      (symbolTerm 0) emptyCells)

/-- An interior rule fires: the head moves right onto a written cell. -/
theorem appendOne_first_step :
    Step base (turingMachine appendOne) appendOneStart appendOneSecond :=
  exists_mem_rewriteAt_iff_step.mp ⟨1, by decide +kernel⟩

/-- An edge rule fires: the head moves past the last written cell. -/
theorem appendOne_second_step :
    Step base (turingMachine appendOne) appendOneSecond appendOneBlank :=
  exists_mem_rewriteAt_iff_step.mp ⟨1, by decide +kernel⟩

/-- The table entry for the blank fires and the machine enters state one. -/
theorem appendOne_third_step :
    Step base (turingMachine appendOne) appendOneBlank appendOneDone :=
  exists_mem_rewriteAt_iff_step.mp ⟨1, by decide +kernel⟩

/-- State one has no table entry: the machine has halted. -/
theorem appendOne_halted (target : Pattern) :
    ¬ Step base (turingMachine appendOne) appendOneDone target := by
  apply not_step_of_matchPatternForRule_eq_nil
  have none : (turingMachine appendOne).rewrites.all (fun rule =>
      matchPatternForRule (turingMachine appendOne) rule appendOneDone == []) = true := by
    decide +kernel
  intro rule member
  exact beq_iff_eq.mp (List.all_eq_true.mp none rule member)

end Mettapedia.Languages.TuringMachine
