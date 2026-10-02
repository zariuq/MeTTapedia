import Mettapedia.Languages.TuringMachine.NativeTypes
import Mettapedia.OSLF.Framework.BagPairRuleSteps
import Mettapedia.GSLT.LanguageDef.BagNormalFormTyping
import Mathlib.Data.List.Perm.Basic

/-!
# One language definition that runs every Turing machine

The language definition of a machine has its table in its rewrites: a
different table is a different theory.  Turing's universal machine instead
receives the table as data, the standard description of the machine.  This
module authors that idea as one language definition, `universalTheory`, with
four rewrites that mention no table.

A term of the theory is a bag.  Its members are rows of a table and
configurations, and both are terms of one sort.  A rewrite selects a row and
a configuration in the bag.  The two patterns share the variables for the
state and the scanned symbol, so only a row for that state and symbol is
selected; the configuration is rewritten as the row says, and the row stays.
The four rewrites are the four shapes of a step: the head moves right or
left, onto a written cell or past the last written cell.

The members of a bag commute.  That is the one static law of the theory
(`universalTheory_bagTheory`), it identifies the bags of a machine that differ
in the order of their members (`TableWith.equiv`, `reordered_bag`), and the
statements below are about the GSLT generated from the theory, whose steps
are taken modulo that law.

* **Every machine runs in the theory, step for step.**  The bag of a
  configuration and the rows of a machine steps exactly to the terms equal to
  the bag of a next configuration and the rows (`withTable_step_iff`).  A term
  holds at most one configuration (`hosts_unique`).  The machine halts from
  the configuration exactly when the bag reaches a term with no step
  (`haltsFrom_iff_universal`).  Before the law of the bag is taken into
  account, the same correspondence of steps holds with any pattern in place
  of the configuration (`tableWith_forward`, `tableWith_backward`).
* **The map is a morphism of GSLTs.**  From the machine on its
  configurations it is a map of terms that preserves bisimilarity, and it
  reflects bisimilarity as well (`intoUniversal`, `bisimilar_withTable_iff`).
* **The universal theory is interactive and no machine is.**  In the theory a
  row and a configuration are two things of one sort that meet in a bag.  In
  the language definition of a machine the only contact is between a state
  and a tape (`universalTheory_isInteractive`, `machine_versus_universal`).
* **Every machine is a type of the universal theory**, and on the terms of
  that type the `◇` of the theory is the `◇` of the machine (`holding`,
  `diamond_holding`).

What is not shown here is Turing's theorem itself, that some *table* is
universal.  Here the row is found by the matcher, in one step, in a bag; a
table has to find it on a tape, cell by cell.

## References

* Turing (1936). "On computable numbers, with an application to the
  Entscheidungsproblem", §§5–7: standard descriptions and the universal
  machine.
* Berry and Boudol (1990). "The chemical abstract machine": terms as
  solutions in which molecules react.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.TuringMachine

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Substitution (freeVars)
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.PredFiniteSufficient
open Mettapedia.GSLT.LanguageDef

/-! ## Rows and bags -/

/-- A direction as a term. -/
def moveTerm : Move → Pattern
  | .left => .apply "Left" []
  | .right => .apply "Right" []

theorem moveTerm_injective : Function.Injective moveTerm := by
  intro first second same
  cases first <;> cases second <;> first | rfl | simp [moveTerm] at same

/-- A row: in a state, scanning a symbol, write, move and enter a state. -/
def row (state read write move next : Pattern) : Pattern :=
  .apply "Row" [state, read, write, move, next]

/-- The row of a table entry. -/
def rowTerm (entry : Transition) : Pattern :=
  row (stateTerm entry.state) (symbolTerm entry.read) (symbolTerm entry.write)
    (moveTerm entry.move) (stateTerm entry.next)

/-- Distinct entries have distinct rows. -/
theorem rowTerm_injective : Function.Injective rowTerm := by
  rintro ⟨state, read, write, move, next⟩ ⟨otherState, otherRead, otherWrite, otherMove,
    otherNext⟩ same
  simp only [rowTerm, row, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] at same
  obtain ⟨states, reads, writes, moves, nexts⟩ := same
  rw [stateTerm_injective states, symbolTerm_injective reads, symbolTerm_injective writes,
    moveTerm_injective moves, stateTerm_injective nexts]

/-- A bag of rows and configurations. -/
def soup (members : List Pattern) : Pattern := .collection .hashBag members none

/-- The standard description of a machine: its rows. -/
def description (machine : Machine) : List Pattern := machine.transitions.map rowTerm

/-- A pattern in a bag with the rows of a machine. -/
def withTable (machine : Machine) (pattern : Pattern) : Pattern :=
  soup (pattern :: description machine)

@[simp] theorem applyBindings_row (bindings : Bindings) (state read write move next : Pattern) :
    applyBindings bindings (row state read write move next) =
      row (applyBindings bindings state) (applyBindings bindings read)
        (applyBindings bindings write) (applyBindings bindings move)
        (applyBindings bindings next) := by
  simp [row, applyBindings]

@[simp] theorem applyBindings_moveTerm (bindings : Bindings) (move : Move) :
    applyBindings bindings (moveTerm move) = moveTerm move := by
  cases move <;> simp [moveTerm, applyBindings]

theorem row_ne_run (state read write move next control tape : Pattern) :
    row state read write move next ≠ run control tape := by
  simp [row, run]

theorem rowTerm_ne_run (entry : Transition) (control tape : Pattern) :
    rowTerm entry ≠ run control tape :=
  row_ne_run _ _ _ _ _ _ _

theorem rowTerm_ne_term (entry : Transition) (configuration : Configuration) :
    rowTerm entry ≠ configuration.term :=
  row_ne_run _ _ _ _ _ _ _

/-! ## The theory -/

/-- The bag constructor of the theory: a bag of terms of its own sort. -/
def mixConstructor : GrammarRule :=
  { label := "Mix", category := "Soup",
    params := [.simple "members" (TypeExpr.bag (.base "Soup"))],
    syntaxPattern := [.nonTerminal "members"] }

/-- The constructors: those of a machine other than `Run`; the two
directions; rows and configurations, both of the sort of bags; and the bag
itself. -/
def universalTerms : List GrammarRule := [
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
    { label := "Left", category := "Move", params := [], syntaxPattern := [] },
    { label := "Right", category := "Move", params := [], syntaxPattern := [] },
    { label := "Row", category := "Soup",
      params := [.simple "state" (.base "State"), .simple "read" (.base "Symbol"),
        .simple "write" (.base "Symbol"), .simple "move" (.base "Move"),
        .simple "next" (.base "State")],
      syntaxPattern := [.nonTerminal "state", .nonTerminal "read", .nonTerminal "write",
        .nonTerminal "move", .nonTerminal "next"] },
    { label := "Run", category := "Soup",
      params := [.simple "control" (.base "State"), .simple "tape" (.base "Tape")],
      syntaxPattern := [.nonTerminal "control", .nonTerminal "tape"] },
    mixConstructor ]

/-- The first seven constructors are those of a machine other than `Run`. -/
theorem universalTerms_take : universalTerms.take 7 = terms.dropLast := by
  decide +kernel

theorem universalTerms_labels :
    universalTerms.map (·.label) =
      ["QZero", "QSucc", "SZero", "SSucc", "Empty", "Cell", "At", "Left", "Right", "Row",
        "Run", "Mix"] := by
  decide

/-- The row that the rules select: any state, symbols and next state, with a
given direction. -/
def rowPattern (move : Move) : Pattern :=
  row (.fvar "q") (.fvar "s") (.fvar "w") (moveTerm move) (.fvar "n")

/-- The variables of the rules and their sorts. -/
def ruleContext : List (String × TypeExpr) :=
  [("q", .base "State"), ("s", .base "Symbol"), ("w", .base "Symbol"), ("n", .base "State"),
    ("l", .base "Cells"), ("c", .base "Symbol"), ("r", .base "Cells")]

/-- The head moves right onto a written cell. -/
def interiorRightRule : RewriteRule where
  name := "InteriorRight"
  typeContext := ruleContext
  premises := []
  left := .collection .hashBag
    [rowPattern .right,
      run (.fvar "q") (tapeAt (.fvar "l") (.fvar "s") (cell (.fvar "c") (.fvar "r")))]
    (some "rest")
  right := .collection .hashBag
    [rowPattern .right,
      run (.fvar "n") (tapeAt (cell (.fvar "w") (.fvar "l")) (.fvar "c") (.fvar "r"))]
    (some "rest")

/-- The head moves left onto a written cell. -/
def interiorLeftRule : RewriteRule where
  name := "InteriorLeft"
  typeContext := ruleContext
  premises := []
  left := .collection .hashBag
    [rowPattern .left,
      run (.fvar "q") (tapeAt (cell (.fvar "c") (.fvar "l")) (.fvar "s") (.fvar "r"))]
    (some "rest")
  right := .collection .hashBag
    [rowPattern .left,
      run (.fvar "n") (tapeAt (.fvar "l") (.fvar "c") (cell (.fvar "w") (.fvar "r")))]
    (some "rest")

/-- The head moves right past the last written cell. -/
def edgeRightRule : RewriteRule where
  name := "EdgeRight"
  typeContext := ruleContext
  premises := []
  left := .collection .hashBag
    [rowPattern .right, run (.fvar "q") (tapeAt (.fvar "l") (.fvar "s") emptyCells)]
    (some "rest")
  right := .collection .hashBag
    [rowPattern .right,
      run (.fvar "n") (tapeAt (cell (.fvar "w") (.fvar "l")) (symbolTerm 0) emptyCells)]
    (some "rest")

/-- The head moves left past the last written cell. -/
def edgeLeftRule : RewriteRule where
  name := "EdgeLeft"
  typeContext := ruleContext
  premises := []
  left := .collection .hashBag
    [rowPattern .left, run (.fvar "q") (tapeAt emptyCells (.fvar "s") (.fvar "r"))]
    (some "rest")
  right := .collection .hashBag
    [rowPattern .left,
      run (.fvar "n") (tapeAt emptyCells (symbolTerm 0) (cell (.fvar "w") (.fvar "r")))]
    (some "rest")

/-- **The universal theory.**  Its rewrites mention no table. -/
def universalTheory : LanguageDef :=
  { name := "UniversalTuringMachine"
    types := ["State", "Symbol", "Cells", "Tape", "Move", "Soup"]
    terms := universalTerms
    equations := []
    rewrites := [interiorRightRule, interiorLeftRule, edgeRightRule, edgeLeftRule] }

/-- The constructors that the rules mention, with their arities. -/
def universalReferences : List (String × Nat) :=
  [("QZero", 0), ("QSucc", 1), ("SZero", 0), ("SSucc", 1), ("Empty", 0), ("Cell", 2),
    ("At", 3), ("Left", 0), ("Right", 0), ("Row", 5), ("Run", 2)]

theorem universalReferences_declared :
    ∀ reference ∈ universalReferences,
      LanguageDef.referenceDeclared universalTerms reference = true := by
  decide

/-- Discharge the obligations of one of the four rules. -/
local macro "validate_universal_rule" : tactic =>
  `(tactic|
    (apply LanguageDef.validateRewrite_eq_nil_of_premiseFree
     · rfl
     · simp [universalTheory, ruleContext, LanguageDef.typeNames, TypeExpr.baseNames,
         TypeDecl.plain]
     · intro reference membership
       apply universalReferences_declared
       simp [rowPattern, row, run, tapeAt, cell, emptyCells, moveTerm, symbolTerm,
         Pattern.constructorRefs, Pattern.constructorRefsList] at membership
       simp only [universalReferences, List.mem_cons, List.not_mem_nil, or_false]
       tauto
     · intro reference membership
       apply universalReferences_declared
       simp [rowPattern, row, run, tapeAt, cell, emptyCells, moveTerm, symbolTerm,
         Pattern.constructorRefs, Pattern.constructorRefsList] at membership
       simp only [universalReferences, List.mem_cons, List.not_mem_nil, or_false]
       tauto
     · intro context
       simp [universalTheory, universalTerms, mixConstructor, ruleContext, rowPattern, row,
         run, tapeAt, cell, emptyCells, moveTerm, symbolTerm, LanguageDef.validateRulePatterns,
         Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
         LanguageDef.patternFvarNames, Pattern.freeFvarNames,
         LanguageDef.patternBinderNames]))

/-- The theory passes the declaration gate. -/
theorem universalTheory_validate_eq_nil : universalTheory.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  · rfl
  · show (["State", "Symbol", "Cells", "Tape", "Move", "Soup"] : List String).Nodup
    decide
  · show (universalTerms.map (·.label)).Nodup
    decide
  · show (["InteriorRight", "InteriorLeft", "EdgeRight", "EdgeLeft"] : List String).Nodup
    decide
  · show ∀ term ∈ universalTerms,
      term.category ∈ (["State", "Symbol", "Cells", "Tape", "Move", "Soup"] : List String)
    decide
  · show ∀ term ∈ universalTerms, ∀ param ∈ term.params,
      ∀ typeName ∈ (TermParam.typeExpr param).baseNames,
        typeName ∈ (["State", "Symbol", "Cells", "Tape", "Move", "Soup"] : List String)
    decide
  · show ∀ term ∈ universalTerms, term.syntaxPattern = [] ∨
      term.syntaxPattern = term.params.map (fun param =>
        SyntaxItem.nonTerminal (TermParam.bodyName param))
    decide +kernel
  · intro rewrite membership
    simp only [universalTheory, List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl
    · unfold interiorRightRule
      validate_universal_rule
    · unfold interiorLeftRule
      validate_universal_rule
    · unfold edgeRightRule
      validate_universal_rule
    · unfold edgeLeftRule
      validate_universal_rule

theorem interiorRightRule_mem : interiorRightRule ∈ universalTheory.rewrites :=
  List.Mem.head _

theorem interiorLeftRule_mem : interiorLeftRule ∈ universalTheory.rewrites :=
  List.Mem.tail _ (List.Mem.head _)

theorem edgeRightRule_mem : edgeRightRule ∈ universalTheory.rewrites :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))

theorem edgeLeftRule_mem : edgeLeftRule ∈ universalTheory.rewrites :=
  List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

/-- Its rules carry no premise and bind nothing. -/
theorem universalTheory_plain : PlainRules universalTheory := by
  intro rule member
  simp only [universalTheory, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;>
    exact ⟨rfl, ruleDepthAligned_of_binderFree _
      (by simp [interiorRightRule, interiorLeftRule, edgeRightRule, edgeLeftRule, rowPattern,
        row, run, tapeAt, cell, emptyCells, moveTerm, symbolTerm, binderFree, binderFreeList])
      (by simp [interiorRightRule, interiorLeftRule, edgeRightRule, edgeLeftRule, rowPattern,
        row, run, tapeAt, cell, emptyCells, moveTerm, symbolTerm, binderFree, binderFreeList])⟩

/-! ## The reaction of a row with a configuration -/

/-- A row takes a configuration to another: the four shapes of a step, with
the row as a term. -/
inductive Reaction : Pattern → Pattern → Pattern → Prop where
  /-- The head moves right onto a written cell. -/
  | interiorRight (state read write next left current right : Pattern) :
      Reaction (row state read write (moveTerm .right) next)
        (run state (tapeAt left read (cell current right)))
        (run next (tapeAt (cell write left) current right))
  /-- The head moves left onto a written cell. -/
  | interiorLeft (state read write next left current right : Pattern) :
      Reaction (row state read write (moveTerm .left) next)
        (run state (tapeAt (cell current left) read right))
        (run next (tapeAt left current (cell write right)))
  /-- The head moves right past the last written cell. -/
  | edgeRight (state read write next left : Pattern) :
      Reaction (row state read write (moveTerm .right) next)
        (run state (tapeAt left read emptyCells))
        (run next (tapeAt (cell write left) (symbolTerm 0) emptyCells))
  /-- The head moves left past the last written cell. -/
  | edgeLeft (state read write next right : Pattern) :
      Reaction (row state read write (moveTerm .left) next)
        (run state (tapeAt emptyCells read right))
        (run next (tapeAt emptyCells (symbolTerm 0) (cell write right)))

/-- The first operand of a reaction is a row and the second a configuration. -/
theorem Reaction.shapes {rowMember source target : Pattern}
    (reaction : Reaction rowMember source target) :
    (∃ state read write move next, rowMember = row state read write move next) ∧
      ∃ control tape, source = run control tape := by
  cases reaction <;> exact ⟨⟨_, _, _, _, _, rfl⟩, ⟨_, _, rfl⟩⟩

/-- **The steps of a machine are the reactions with its rows.** -/
theorem machineStep_iff_reaction {machine : Machine} {source target : Pattern} :
    MachineStep machine source target ↔
      ∃ entry ∈ machine.transitions, Reaction (rowTerm entry) source target := by
  constructor
  · intro shape
    cases shape with
    | @interiorRight entry member move left current right =>
        refine ⟨entry, member, ?_⟩
        rw [rowTerm, move]
        exact .interiorRight _ _ _ _ _ _ _
    | @interiorLeft entry member move left current right =>
        refine ⟨entry, member, ?_⟩
        rw [rowTerm, move]
        exact .interiorLeft _ _ _ _ _ _ _
    | @edgeRight entry member move left =>
        refine ⟨entry, member, ?_⟩
        rw [rowTerm, move]
        exact .edgeRight _ _ _ _ _
    | @edgeLeft entry member move right =>
        refine ⟨entry, member, ?_⟩
        rw [rowTerm, move]
        exact .edgeLeft _ _ _ _ _
  · rintro ⟨entry, member, reaction⟩
    generalize rowEq : rowTerm entry = rowMember at reaction
    cases reaction with
    | interiorRight state read write next left current right =>
        simp only [rowTerm, row, Pattern.apply.injEq, List.cons.injEq, and_true, true_and]
          at rowEq
        obtain ⟨rfl, rfl, rfl, moves, rfl⟩ := rowEq
        exact .interiorRight member (moveTerm_injective moves) _ _ _
    | interiorLeft state read write next left current right =>
        simp only [rowTerm, row, Pattern.apply.injEq, List.cons.injEq, and_true, true_and]
          at rowEq
        obtain ⟨rfl, rfl, rfl, moves, rfl⟩ := rowEq
        exact .interiorLeft member (moveTerm_injective moves) _ _ _
    | edgeRight state read write next left =>
        simp only [rowTerm, row, Pattern.apply.injEq, List.cons.injEq, and_true, true_and]
          at rowEq
        obtain ⟨rfl, rfl, rfl, moves, rfl⟩ := rowEq
        exact .edgeRight member (moveTerm_injective moves) _
    | edgeLeft state read write next right =>
        simp only [rowTerm, row, Pattern.apply.injEq, List.cons.injEq, and_true, true_and]
          at rowEq
        obtain ⟨rfl, rfl, rfl, moves, rfl⟩ := rowEq
        exact .edgeLeft member (moveTerm_injective moves) _

/-! ## The steps of the theory -/

/-- Bindings for the variables of the rules. -/
def ruleBindings (state read write next left current right : Pattern)
    (others : List Pattern) : Bindings :=
  [("q", state), ("s", read), ("w", write), ("n", next), ("l", left), ("c", current),
    ("r", right), ("rest", .collection .hashBag others none)]

section RuleBindings

variable (state read write next left current right : Pattern) (others : List Pattern)

@[simp] theorem ruleBindings_q :
    applyBindings (ruleBindings state read write next left current right others) (.fvar "q") =
      state := by
  simp [applyBindings, ruleBindings]

@[simp] theorem ruleBindings_s :
    applyBindings (ruleBindings state read write next left current right others) (.fvar "s") =
      read := by
  simp [applyBindings, ruleBindings]

@[simp] theorem ruleBindings_w :
    applyBindings (ruleBindings state read write next left current right others) (.fvar "w") =
      write := by
  simp [applyBindings, ruleBindings]

@[simp] theorem ruleBindings_n :
    applyBindings (ruleBindings state read write next left current right others) (.fvar "n") =
      next := by
  simp [applyBindings, ruleBindings]

@[simp] theorem ruleBindings_l :
    applyBindings (ruleBindings state read write next left current right others) (.fvar "l") =
      left := by
  simp [applyBindings, ruleBindings]

@[simp] theorem ruleBindings_c :
    applyBindings (ruleBindings state read write next left current right others) (.fvar "c") =
      current := by
  simp [applyBindings, ruleBindings]

@[simp] theorem ruleBindings_r :
    applyBindings (ruleBindings state read write next left current right others) (.fvar "r") =
      right := by
  simp [applyBindings, ruleBindings]

theorem ruleBindings_rest :
    lookupOrFvar (ruleBindings state read write next left current right others) "rest" =
      .collection .hashBag others none := by
  simp [lookupOrFvar, applyBindings, ruleBindings]

end RuleBindings

/-- **A step of the theory is a reaction of two members of the bag.**  The
reduct has the row first, then the new configuration, then the others. -/
theorem universal_step_iff {members : List Pattern} {target : Pattern} :
    Step base universalTheory (soup members) target ↔
      ∃ (i : Nat) (hi : i < members.length) (j : Nat) (hj : j < (members.eraseIdx i).length)
        (next : Pattern),
        Reaction members[i] (members.eraseIdx i)[j] next ∧
          target = soup (members[i] :: next :: (members.eraseIdx i).eraseIdx j) := by
  constructor
  · intro step
    obtain ⟨rule, member, bindings, matched, rfl⟩ :=
      (step_iff_exists_match universalTheory_plain).mp step
    simp only [universalTheory, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · obtain ⟨i, hi, j, hj, atRow, atRun, restBound⟩ :=
        bagPair_of_mem_matchPattern (by decide) (by decide) matched
      refine ⟨i, hi, j, hj, applyBindings bindings
        (run (.fvar "n") (tapeAt (cell (.fvar "w") (.fvar "l")) (.fvar "c") (.fvar "r"))),
        ?_, ?_⟩
      · rw [← atRow, ← atRun]
        simp only [rowPattern, applyBindings_row, applyBindings_run, applyBindings_tapeAt,
          applyBindings_cell, applyBindings_moveTerm]
        exact .interiorRight _ _ _ _ _ _ _
      · show applyBindings bindings interiorRightRule.right = _
        rw [interiorRightRule, applyBindings_bagPair restBound, atRow]
        rfl
    · obtain ⟨i, hi, j, hj, atRow, atRun, restBound⟩ :=
        bagPair_of_mem_matchPattern (by decide) (by decide) matched
      refine ⟨i, hi, j, hj, applyBindings bindings
        (run (.fvar "n") (tapeAt (.fvar "l") (.fvar "c") (cell (.fvar "w") (.fvar "r")))),
        ?_, ?_⟩
      · rw [← atRow, ← atRun]
        simp only [rowPattern, applyBindings_row, applyBindings_run, applyBindings_tapeAt,
          applyBindings_cell, applyBindings_moveTerm]
        exact .interiorLeft _ _ _ _ _ _ _
      · show applyBindings bindings interiorLeftRule.right = _
        rw [interiorLeftRule, applyBindings_bagPair restBound, atRow]
        rfl
    · obtain ⟨i, hi, j, hj, atRow, atRun, restBound⟩ :=
        bagPair_of_mem_matchPattern (by decide) (by decide) matched
      refine ⟨i, hi, j, hj, applyBindings bindings
        (run (.fvar "n") (tapeAt (cell (.fvar "w") (.fvar "l")) (symbolTerm 0) emptyCells)),
        ?_, ?_⟩
      · rw [← atRow, ← atRun]
        simp only [rowPattern, applyBindings_row, applyBindings_run, applyBindings_tapeAt,
          applyBindings_cell, applyBindings_emptyCells, applyBindings_moveTerm,
          applyBindings_symbolTerm]
        exact .edgeRight _ _ _ _ _
      · show applyBindings bindings edgeRightRule.right = _
        rw [edgeRightRule, applyBindings_bagPair restBound, atRow]
        rfl
    · obtain ⟨i, hi, j, hj, atRow, atRun, restBound⟩ :=
        bagPair_of_mem_matchPattern (by decide) (by decide) matched
      refine ⟨i, hi, j, hj, applyBindings bindings
        (run (.fvar "n") (tapeAt emptyCells (symbolTerm 0) (cell (.fvar "w") (.fvar "r")))),
        ?_, ?_⟩
      · rw [← atRow, ← atRun]
        simp only [rowPattern, applyBindings_row, applyBindings_run, applyBindings_tapeAt,
          applyBindings_cell, applyBindings_emptyCells, applyBindings_moveTerm,
          applyBindings_symbolTerm]
        exact .edgeLeft _ _ _ _ _
      · show applyBindings bindings edgeLeftRule.right = _
        rw [edgeLeftRule, applyBindings_bagPair restBound, atRow]
        rfl
  · rintro ⟨i, hi, j, hj, next, reaction, rfl⟩
    generalize rowEq : members[i] = rowMember at reaction ⊢
    generalize runEq : (members.eraseIdx i)[j] = runMember at reaction
    cases reaction with
    | interiorRight state read write next left current right =>
        have step := step_of_bagPair (relEnv := RelationEnv.empty) universalTheory_plain
          (rule := interiorRightRule) interiorRightRule_mem rfl rfl (by decide) (by decide)
          (by decide) (by decide) (by
            intro name
            simp [freeVars, rowPattern, row, run, tapeAt, cell, moveTerm]
            tauto)
          (ruleBindings state read write next left current right
            ((members.eraseIdx i).eraseIdx j)) hi hj
          (by simp [rowPattern, rowEq]) (by simp [runEq]) (ruleBindings_rest ..)
        simpa [soup, rowPattern] using step
    | interiorLeft state read write next left current right =>
        have step := step_of_bagPair (relEnv := RelationEnv.empty) universalTheory_plain
          (rule := interiorLeftRule) interiorLeftRule_mem rfl rfl (by decide) (by decide)
          (by decide) (by decide) (by
            intro name
            simp [freeVars, rowPattern, row, run, tapeAt, cell, moveTerm]
            tauto)
          (ruleBindings state read write next left current right
            ((members.eraseIdx i).eraseIdx j)) hi hj
          (by simp [rowPattern, rowEq]) (by simp [runEq]) (ruleBindings_rest ..)
        simpa [soup, rowPattern] using step
    | edgeRight state read write next left =>
        have step := step_of_bagPair (relEnv := RelationEnv.empty) universalTheory_plain
          (rule := edgeRightRule) edgeRightRule_mem rfl rfl (by decide) (by decide)
          (by decide) (by decide) (by
            intro name
            simp [freeVars, rowPattern, row, run, tapeAt, cell, emptyCells, moveTerm,
              symbolTerm]
            tauto)
          (ruleBindings state read write next left emptyCells emptyCells
            ((members.eraseIdx i).eraseIdx j)) hi hj
          (by simp [rowPattern, rowEq]) (by simp [runEq]) (ruleBindings_rest ..)
        simpa [soup, rowPattern] using step
    | edgeLeft state read write next right =>
        have step := step_of_bagPair (relEnv := RelationEnv.empty) universalTheory_plain
          (rule := edgeLeftRule) edgeLeftRule_mem rfl rfl (by decide) (by decide)
          (by decide) (by decide) (by
            intro name
            simp [freeVars, rowPattern, row, run, tapeAt, cell, emptyCells, moveTerm,
              symbolTerm]
            tauto)
          (ruleBindings state read write next emptyCells emptyCells right
            ((members.eraseIdx i).eraseIdx j)) hi hj
          (by simp [rowPattern, rowEq]) (by simp [runEq]) (ruleBindings_rest ..)
        simpa [soup, rowPattern] using step

/-! ## A machine inside the theory: the bag as a list -/

/-- The members of a bag are the rows of the machine and one more pattern. -/
def TableWith (machine : Machine) (pattern : Pattern) (members : List Pattern) : Prop :=
  members.Perm (pattern :: description machine)

/-- After a reaction the bag again consists of the rows and one pattern. -/
private theorem perm_after {table members : List Pattern} {pattern next : Pattern} {i j : Nat}
    (hi : i < members.length) (hj : j < (members.eraseIdx i).length)
    (perm : members.Perm (pattern :: table)) (patternAt : (members.eraseIdx i)[j] = pattern) :
    (members[i] :: next :: (members.eraseIdx i).eraseIdx j).Perm (next :: table) := by
  have first : (members[i] :: members.eraseIdx i).Perm members :=
    List.getElem_cons_eraseIdx_perm hi
  have second : ((members.eraseIdx i)[j] :: (members.eraseIdx i).eraseIdx j).Perm
      (members.eraseIdx i) := List.getElem_cons_eraseIdx_perm hj
  rw [patternAt] at second
  have all : (members[i] :: pattern :: (members.eraseIdx i).eraseIdx j).Perm
      (pattern :: table) := ((second.cons members[i]).trans first).trans perm
  have rows : (members[i] :: (members.eraseIdx i).eraseIdx j).Perm table :=
    ((List.Perm.swap _ _ _).trans all).cons_inv
  exact (List.Perm.swap _ _ _).trans (rows.cons next)

/-- **Every step of the machine is a step of the bag.** -/
theorem tableWith_forward {machine : Machine} {pattern next : Pattern} {members : List Pattern}
    (holds : TableWith machine pattern members)
    (step : Step base (turingMachine machine) pattern next) :
    ∃ after, Step base universalTheory (soup members) (soup after) ∧
      TableWith machine next after := by
  obtain ⟨entry, member, reaction⟩ := machineStep_iff_reaction.mp (machineStep_of_step step)
  have rowMember : rowTerm entry ∈ members :=
    holds.mem_iff.mpr (List.mem_cons_of_mem _ (List.mem_map_of_mem member))
  obtain ⟨i, hi, rowAt⟩ := List.getElem_of_mem rowMember
  have patternMember : pattern ∈ members.eraseIdx i := by
    have inAll : pattern ∈ members[i] :: members.eraseIdx i :=
      (List.getElem_cons_eraseIdx_perm hi).mem_iff.mpr
        (holds.mem_iff.mpr (List.mem_cons_self ..))
    rcases List.mem_cons.mp inAll with same | inRest
    · obtain ⟨-, control, tape, isRun⟩ := reaction.shapes
      rw [same, rowAt] at isRun
      exact absurd isRun (rowTerm_ne_run _ _ _)
    · exact inRest
  obtain ⟨j, hj, patternAt⟩ := List.getElem_of_mem patternMember
  refine ⟨_, universal_step_iff.mpr ⟨i, hi, j, hj, next, ?_, rfl⟩,
    perm_after hi hj holds patternAt⟩
  rw [rowAt, patternAt]
  exact reaction

/-- **Every step of the bag is a step of the machine.** -/
theorem tableWith_backward {machine : Machine} {pattern target : Pattern}
    {members : List Pattern} (holds : TableWith machine pattern members)
    (step : Step base universalTheory (soup members) target) :
    ∃ next after, Step base (turingMachine machine) pattern next ∧ target = soup after ∧
      TableWith machine next after := by
  obtain ⟨i, hi, j, hj, next, reaction, rfl⟩ := universal_step_iff.mp step
  obtain ⟨⟨state, read, write, move, nextState, isRow⟩, control, tape, isRun⟩ := reaction.shapes
  have patternAt : (members.eraseIdx i)[j] = pattern := by
    have runMember : (members.eraseIdx i)[j] ∈ pattern :: description machine :=
      holds.mem_iff.mp (List.mem_of_mem_eraseIdx (List.getElem_mem hj))
    rcases List.mem_cons.mp runMember with same | inTable
    · exact same
    · obtain ⟨entry, -, isEntry⟩ := List.mem_map.mp inTable
      rw [isRun] at isEntry
      exact absurd isEntry (rowTerm_ne_run _ _ _)
  have rowMember : members[i] ∈ pattern :: description machine :=
    holds.mem_iff.mp (List.getElem_mem hi)
  have rowAt : ∃ entry ∈ machine.transitions, rowTerm entry = members[i] := by
    rcases List.mem_cons.mp rowMember with same | inTable
    · rw [isRow, ← patternAt, isRun] at same
      exact absurd same (row_ne_run _ _ _ _ _ _ _)
    · exact List.mem_map.mp inTable
  obtain ⟨entry, member, isEntry⟩ := rowAt
  refine ⟨next, _, step_of_machineStep (machineStep_iff_reaction.mpr ⟨entry, member, ?_⟩), rfl,
    perm_after hi hj holds patternAt⟩
  rw [isEntry, ← patternAt]
  exact reaction

/-! ## The laws of the bag -/

open Mettapedia.GSLT.LanguageDef.BagNormalForm
open Mettapedia.GSLT.LanguageDef.EquationSemantics

theorem mixConstructor_mem : mixConstructor ∈ universalTerms :=
  List.getElem_mem (l := universalTerms) (n := 11) (by decide)

/-- **The static laws of the theory are those of one bag**: its members
commute, and nothing else is identified. -/
theorem universalTheory_bagTheory : BagTheory universalTheory mixConstructor none :=
  bagTheory_of_check (by decide +kernel)

/-- A pattern built from constructors alone: no variable, binder or bag. -/
inductive ConstructorTerm : Pattern → Prop where
  | apply (label : String) (arguments : List Pattern) :
      (∀ argument ∈ arguments, ConstructorTerm argument) →
        ConstructorTerm (.apply label arguments)

/-- A constructor term is its own normal form. -/
theorem ConstructorTerm.normalForm_eq {pattern : Pattern} (isTerm : ConstructorTerm pattern)
    (unit : Option String) : normalForm unit pattern = pattern := by
  induction isTerm with
  | apply label arguments _ recurse =>
      have fixed : arguments.map (normalForm unit) = arguments.map id :=
        List.map_congr_left recurse
      rw [normalForm_apply, fixed, List.map_id]

/-- Only a constructor term has a constructor term as its normal form: the
laws of the bag identify it with nothing else. -/
theorem ConstructorTerm.eq_of_normalForm_eq {target : Pattern}
    (isTerm : ConstructorTerm target) :
    ∀ pattern, normalForm none pattern = target → pattern = target := by
  induction isTerm with
  | apply label arguments _ recurse =>
      intro pattern same
      cases pattern with
      | apply otherLabel otherArguments =>
          rw [normalForm_apply] at same
          simp only [Pattern.apply.injEq] at same
          obtain ⟨rfl, mapped⟩ := same
          subst mapped
          have fixed : otherArguments.map (normalForm none) = otherArguments.map id :=
            List.map_congr_left fun argument member =>
              (recurse _ (List.mem_map_of_mem member) argument rfl).symm
          rw [fixed, List.map_id]
      | collection kind elements rest =>
          simp only [normalForm] at same
          split at same <;> simp [normalizeBag] at same
      | bvar index => simp [normalForm] at same
      | fvar name => simp [normalForm] at same
      | lambda binder body => simp [normalForm] at same
      | multiLambda arity binders body => simp [normalForm] at same
      | subst body replacement => simp [normalForm] at same

theorem constructorTerm_unary (zero succ : String) (count : Nat) :
    ConstructorTerm (Pattern.unary zero succ count) := by
  induction count with
  | zero => exact .apply _ _ (by simp)
  | succ count recurse => exact .apply _ _ (by simpa using recurse)

theorem constructorTerm_cellsTerm (cells : List Nat) : ConstructorTerm (cellsTerm cells) := by
  induction cells with
  | nil => exact .apply _ _ (by simp)
  | cons symbol rest recurse =>
      exact .apply _ _ (by simpa using ⟨constructorTerm_unary _ _ symbol, recurse⟩)

theorem constructorTerm_term (configuration : Configuration) :
    ConstructorTerm configuration.term :=
  .apply _ _ (by
    simpa using ⟨constructorTerm_unary _ _ configuration.state,
      ConstructorTerm.apply _ _ (by
        simpa using ⟨constructorTerm_cellsTerm configuration.left,
          constructorTerm_unary _ _ configuration.scanned,
          constructorTerm_cellsTerm configuration.right⟩)⟩)

theorem constructorTerm_rowTerm (entry : Transition) : ConstructorTerm (rowTerm entry) :=
  .apply _ _ (by
    have direction : ConstructorTerm (moveTerm entry.move) := by
      cases entry.move <;> exact .apply _ _ (by simp)
    simpa using ⟨constructorTerm_unary _ _ entry.state, constructorTerm_unary _ _ entry.read,
      constructorTerm_unary _ _ entry.write, direction, constructorTerm_unary _ _ entry.next⟩)

/-- The members of a bag of rows and a configuration are constructor terms. -/
theorem TableWith.constructorTerm {machine : Machine} {configuration : Configuration}
    {members : List Pattern} (holds : TableWith machine configuration.term members) :
    ∀ member ∈ members, ConstructorTerm member := by
  intro member inMembers
  rcases List.mem_cons.mp (holds.mem_iff.mp inMembers) with rfl | inTable
  · exact constructorTerm_term configuration
  · obtain ⟨entry, -, rfl⟩ := List.mem_map.mp inTable
    exact constructorTerm_rowTerm entry

/-- A term that steps in the theory is a bag. -/
theorem exists_collection_of_step {redex contractum : Pattern}
    (step : Step base universalTheory redex contractum) :
    ∃ elements tail, redex = .collection .hashBag elements tail := by
  obtain ⟨rule, member, bindings, matched, -⟩ :=
    (step_iff_exists_match universalTheory_plain).mp step
  simp only [universalTheory, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;>
    · have relation := matchPattern_iff_matchRel.mp matched
      cases relation with
      | collection notVector bagRelation => exact ⟨_, _, rfl⟩

/-- **What is equal to a bag of rows and a configuration, and steps, is such
a bag**: the laws of the bag only reorder it. -/
theorem tableWith_of_equiv_redex {machine : Machine} {configuration : Configuration}
    {members : List Pattern} (holds : TableWith machine configuration.term members)
    {redex contractum : Pattern}
    (equivalent : EquationEquiv base universalTheory (soup members) redex)
    (step : Step base universalTheory redex contractum) :
    ∃ others, redex = soup others ∧ TableWith machine configuration.term others := by
  obtain ⟨elements, tail, rfl⟩ := exists_collection_of_step step
  have same := normalForm_eq_of_equationEquiv universalTheory_bagTheory equivalent
  have membersFixed : members.map (normalForm none) = members := by
    have fixed : members.map (normalForm none) = members.map id :=
      List.map_congr_left fun member inMembers =>
        (holds.constructorTerm member inMembers).normalForm_eq none
    rw [fixed, List.map_id]
  rw [soup, normalForm_bag, membersFixed] at same
  cases tail with
  | some name => simp [normalForm, normalizeBag] at same
  | none =>
      rw [normalForm_bag] at same
      simp only [normalizeBag, Pattern.collection.injEq, true_and, and_true] at same
      have images : (elements.map (normalForm none)).Perm members :=
        ((sortPatterns_perm _).symm.trans (same ▸ sortPatterns_perm members))
      have elementsFixed : elements.map (normalForm none) = elements := by
        have fixed : elements.map (normalForm none) = elements.map id :=
          List.map_congr_left fun element inElements =>
            ((holds.constructorTerm _
              (images.mem_iff.mp (List.mem_map_of_mem inElements))).eq_of_normalForm_eq
                element rfl).symm
        rw [fixed, List.map_id]
      rw [elementsFixed] at images
      exact ⟨elements, rfl, images.trans holds⟩

/-! ## The bags of a machine are sorted, so their members commute -/

open Mettapedia.GSLT.LanguageDef.WellSorted

section Sorting

variable {free : FreeTypeContext} {bound : List TypeExpr}

/-- A constructor other than the bag is applied as its label. -/
private theorem not_bare {rule : GrammarRule}
    (shape : ∀ name kind element,
      rule.params ≠ [.simple name (.collection kind element)]) :
    ¬ UsesBareCollection rule := by
  rintro ⟨name, kind, element, same⟩
  exact shape name kind element same

theorem universal_hasType_stateTerm (index : Nat) :
    HasType universalTheory free bound (stateTerm index) (.base "State") :=
  hasType_unary (language := universalTheory) (zeroRule := universalTerms[0])
    (succRule := universalTerms[1]) (List.getElem_mem (l := universalTerms) (by decide))
    (List.getElem_mem (l := universalTerms) (by decide)) rfl rfl rfl free bound index

theorem universal_hasType_symbolTerm (index : Nat) :
    HasType universalTheory free bound (symbolTerm index) (.base "Symbol") :=
  hasType_unary (language := universalTheory) (zeroRule := universalTerms[2])
    (succRule := universalTerms[3]) (List.getElem_mem (l := universalTerms) (by decide))
    (List.getElem_mem (l := universalTerms) (by decide)) rfl rfl rfl free bound index

theorem universal_hasType_cellsTerm (cells : List Nat) :
    HasType universalTheory free bound (cellsTerm cells) (.base "Cells") := by
  induction cells with
  | nil =>
      exact HasType.constructor (rule := universalTerms[4])
        (List.getElem_mem (l := universalTerms) (by decide))
        (not_bare fun _ _ _ shape => by cases shape) .nil
  | cons symbol rest recurse =>
      exact HasType.constructor (rule := universalTerms[5])
        (List.getElem_mem (l := universalTerms) (by decide))
        (not_bare fun _ _ _ shape => by cases shape)
        (.cons trivial rfl (universal_hasType_symbolTerm symbol) (.cons trivial rfl recurse .nil))

theorem universal_hasType_moveTerm (move : Move) :
    HasType universalTheory free bound (moveTerm move) (.base "Move") := by
  cases move
  · exact HasType.constructor (rule := universalTerms[7])
      (List.getElem_mem (l := universalTerms) (by decide))
      (not_bare fun _ _ _ shape => by cases shape) .nil
  · exact HasType.constructor (rule := universalTerms[8])
      (List.getElem_mem (l := universalTerms) (by decide))
      (not_bare fun _ _ _ shape => by cases shape) .nil

/-- A configuration is a term of the sort of bags. -/
theorem universal_hasType_term (configuration : Configuration) :
    HasType universalTheory free bound configuration.term (.base "Soup") :=
  HasType.constructor (rule := universalTerms[10])
    (List.getElem_mem (l := universalTerms) (by decide))
    (not_bare fun _ _ _ shape => by cases shape)
    (.cons trivial rfl (universal_hasType_stateTerm configuration.state)
      (.cons trivial rfl
        (HasType.constructor (rule := universalTerms[6])
          (List.getElem_mem (l := universalTerms) (by decide))
          (not_bare fun _ _ _ shape => by cases shape)
          (.cons trivial rfl (universal_hasType_cellsTerm configuration.left)
            (.cons trivial rfl (universal_hasType_symbolTerm configuration.scanned)
              (.cons trivial rfl (universal_hasType_cellsTerm configuration.right) .nil))))
        .nil))

/-- So is a row. -/
theorem universal_hasType_rowTerm (entry : Transition) :
    HasType universalTheory free bound (rowTerm entry) (.base "Soup") :=
  HasType.constructor (rule := universalTerms[9])
    (List.getElem_mem (l := universalTerms) (by decide))
    (not_bare fun _ _ _ shape => by cases shape)
    (.cons trivial rfl (universal_hasType_stateTerm entry.state)
      (.cons trivial rfl (universal_hasType_symbolTerm entry.read)
        (.cons trivial rfl (universal_hasType_symbolTerm entry.write)
          (.cons trivial rfl (universal_hasType_moveTerm entry.move)
            (.cons trivial rfl (universal_hasType_stateTerm entry.next) .nil)))))

/-- A bag of terms of the sort of bags is a term of that sort. -/
theorem universal_hasType_soup {members : List Pattern}
    (typed : ∀ member ∈ members, HasType universalTheory free bound member (.base "Soup")) :
    HasType universalTheory free bound (soup members) (.base "Soup") :=
  HasType.collectionConstructor (rule := mixConstructor) mixConstructor_mem rfl
    (elementsHaveType_iff.mpr typed)

end Sorting

/-- The bag of the rows of a machine and a configuration is sorted. -/
theorem TableWith.sortedAt {machine : Machine} {configuration : Configuration}
    {members : List Pattern} (holds : TableWith machine configuration.term members) :
    SortedAt universalTheory (soup members) "Soup" :=
  ⟨FreeTypeContext.empty, [], universal_hasType_soup fun member inMembers => by
    rcases List.mem_cons.mp (holds.mem_iff.mp inMembers) with rfl | inTable
    · exact universal_hasType_term configuration
    · obtain ⟨entry, -, rfl⟩ := List.mem_map.mp inTable
      exact universal_hasType_rowTerm entry⟩

/-- **The members of the bag of a machine commute**: two bags of the same
rows and the same configuration are equal in the generated theory. -/
theorem TableWith.equiv {machine : Machine} {configuration : Configuration}
    {members others : List Pattern} (holds : TableWith machine configuration.term members)
    (othersHold : TableWith machine configuration.term others) :
    EquationEquiv base universalTheory (soup members) (soup others) :=
  equationEquiv_bag_perm (rule := mixConstructor)
    ⟨mixConstructor_mem, "members", .base "Soup", rfl⟩ holds.sortedAt
    (holds.trans othersHold.symm)

/-- The law is at work: the bag with the configuration after the rows is
another term, and it is equal to the bag with the configuration first. -/
theorem reordered_bag (machine : Machine) (configuration : Configuration)
    (nonempty : machine.transitions ≠ []) :
    soup (description machine ++ [configuration.term]) ≠ withTable machine configuration.term ∧
      EquationEquiv base universalTheory
        (soup (description machine ++ [configuration.term]))
        (withTable machine configuration.term) := by
  constructor
  · obtain ⟨entry, rest, shape⟩ := List.exists_cons_of_ne_nil nonempty
    intro same
    simp only [soup, withTable, description, shape, List.map_cons, List.cons_append,
      Pattern.collection.injEq, List.cons.injEq, true_and, and_true] at same
    exact rowTerm_ne_term entry configuration same.1
  · exact TableWith.equiv (machine := machine) (configuration := configuration)
      List.perm_append_comm (List.Perm.refl _)

/-! ## A machine inside the generated GSLT -/

/-- A term of the theory holds a pattern with the table of a machine: by the
laws of the bag it is equal to a bag of the rows and the pattern. -/
def Hosts (machine : Machine) (pattern term : Pattern) : Prop :=
  ∃ members, TableWith machine pattern members ∧
    EquationEquiv base universalTheory term (soup members)

theorem hosts_withTable (machine : Machine) (pattern : Pattern) :
    Hosts machine pattern (withTable machine pattern) :=
  ⟨_, List.Perm.refl _, Relation.EqvGen.refl _⟩

/-- Holding a pattern respects the laws of the bag. -/
theorem Hosts.of_equiv {machine : Machine} {pattern term other : Pattern}
    (hosts : Hosts machine pattern term)
    (equivalent : EquationEquiv base universalTheory other term) :
    Hosts machine pattern other := by
  obtain ⟨members, holds, toSoup⟩ := hosts
  exact ⟨members, holds, Relation.EqvGen.trans _ _ _ equivalent toSoup⟩

/-- **A term holds at most one configuration.** -/
theorem hosts_unique {machine : Machine} {first second : Configuration} {term : Pattern}
    (firstHosts : Hosts machine first.term term) (secondHosts : Hosts machine second.term term) :
    first = second := by
  obtain ⟨members, holds, toSoup⟩ := firstHosts
  obtain ⟨others, othersHold, toOthers⟩ := secondHosts
  have same := normalForm_eq_of_equationEquiv universalTheory_bagTheory
    (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ toSoup) toOthers)
  have fixed : ∀ {configuration : Configuration} {list : List Pattern},
      TableWith machine configuration.term list → list.map (normalForm none) = list := by
    intro configuration list listHolds
    have mapped : list.map (normalForm none) = list.map id :=
      List.map_congr_left fun member inList =>
        (listHolds.constructorTerm member inList).normalForm_eq none
    rw [mapped, List.map_id]
  rw [soup, soup, normalForm_bag, normalForm_bag, fixed holds, fixed othersHold] at same
  simp only [normalizeBag, Pattern.collection.injEq, true_and, and_true] at same
  have perm : (first.term :: description machine).Perm (second.term :: description machine) :=
    holds.symm.trans (((sortPatterns_perm members).symm.trans
      (same ▸ sortPatterns_perm others)).trans othersHold)
  rcases List.mem_cons.mp (perm.mem_iff.mp (List.mem_cons_self ..)) with equal | inTable
  · exact Configuration.term_injective equal
  · obtain ⟨entry, -, isEntry⟩ := List.mem_map.mp inTable
    exact absurd isEntry (rowTerm_ne_term _ _)

/-- **Forward.**  A step of the machine is a step of every term that holds
its source, into a term that holds its target. -/
theorem hosts_forward {machine : Machine} {pattern next term : Pattern}
    (hosts : Hosts machine pattern term)
    (step : Step base (turingMachine machine) pattern next) :
    ∃ after, (langGSLT universalTheory).Step term after ∧ Hosts machine next after := by
  obtain ⟨members, holds, toSoup⟩ := hosts
  obtain ⟨after, engineStep, afterHolds⟩ := tableWith_forward holds step
  exact ⟨soup after, ⟨soup members, soup after, toSoup, engineStep, Relation.EqvGen.refl _⟩,
    after, afterHolds, Relation.EqvGen.refl _⟩

/-- **Backward.**  A step of a term that holds a configuration is a step of
the machine from that configuration, and the reduct holds its target. -/
theorem hosts_backward {machine : Machine} {configuration : Configuration}
    {term after : Pattern} (hosts : Hosts machine configuration.term term)
    (step : (langGSLT universalTheory).Step term after) :
    ∃ next : Configuration,
      Step base (turingMachine machine) configuration.term next.term ∧
        Hosts machine next.term after := by
  obtain ⟨members, holds, toSoup⟩ := hosts
  obtain ⟨redex, contractum, toRedex, engineStep, toAfter⟩ := step
  obtain ⟨others, rfl, othersHold⟩ := tableWith_of_equiv_redex holds
    (Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ toSoup) toRedex) engineStep
  obtain ⟨next, afterMembers, machineStep, rfl, afterHold⟩ :=
    tableWith_backward othersHold engineStep
  obtain ⟨entry, member, applies, rfl⟩ := step_term_iff.mp machineStep
  exact ⟨configuration.after entry, machineStep, afterMembers, afterHold,
    Relation.EqvGen.symm _ _ toAfter⟩

/-- For a configuration, a term holds it exactly when the term is equal, in
the generated theory, to the bag of the configuration and the rows. -/
theorem hosts_iff_equiv {machine : Machine} {configuration : Configuration} {term : Pattern} :
    Hosts machine configuration.term term ↔
      (langGSLT universalTheory).Equiv term (withTable machine configuration.term) := by
  constructor
  · rintro ⟨members, holds, toSoup⟩
    exact Relation.EqvGen.trans _ _ _ toSoup (holds.equiv (List.Perm.refl _))
  · exact fun equivalent => ⟨_, List.Perm.refl _, equivalent⟩

/-- **The steps of the bag of a machine are the steps of the machine.**  In
the GSLT generated from the universal theory, the bag of a configuration and
the rows steps exactly to the terms equal to the bag of a next configuration
and the rows. -/
theorem withTable_step_iff (machine : Machine) (configuration : Configuration)
    (target : Pattern) :
    (langGSLT universalTheory).Step (withTable machine configuration.term) target ↔
      ∃ next : Configuration,
        Step base (turingMachine machine) configuration.term next.term ∧
          (langGSLT universalTheory).Equiv target (withTable machine next.term) := by
  constructor
  · intro step
    obtain ⟨next, machineStep, nextHosts⟩ :=
      hosts_backward (hosts_withTable machine configuration.term) step
    exact ⟨next, machineStep, hosts_iff_equiv.mp nextHosts⟩
  · rintro ⟨next, machineStep, equivalent⟩
    obtain ⟨after, step, afterHosts⟩ :=
      hosts_forward (hosts_withTable machine configuration.term) machineStep
    exact (langGSLT universalTheory).rewrites_resp_right step
      (Relation.EqvGen.trans _ _ _ (hosts_iff_equiv.mp afterHosts)
        (Relation.EqvGen.symm _ _ equivalent))

/-- A configuration is halted exactly when a term that holds it has no step
in the theory. -/
theorem halted_iff_isNormalForm {machine : Machine} {configuration : Configuration}
    {term : Pattern} (hosts : Hosts machine configuration.term term) :
    Halted machine configuration.term ↔ (langGSLT universalTheory).IsNormalForm term := by
  constructor
  · rintro halted ⟨after, step⟩
    obtain ⟨next, machineStep, -⟩ := hosts_backward hosts step
    exact halted _ machineStep
  · intro normal target machineStep
    obtain ⟨after, step, -⟩ := hosts_forward hosts machineStep
    exact normal ⟨after, step⟩

/-- A run of the machine is a run of every term that holds its start. -/
theorem multiStep_of_reaches {machine : Machine} {source target : Pattern}
    (reaches : Reaches machine source target) :
    ∀ term, Hosts machine source term →
      ∃ after, (langGSLT universalTheory).MultiStep term after ∧ Hosts machine target after := by
  induction reaches using Relation.ReflTransGen.head_induction_on with
  | refl =>
      exact fun term hosts =>
        ⟨term, Mettapedia.GSLT.GSLT.MultiStep.refl (S := langGSLT universalTheory) term, hosts⟩
  | head step _ recurse =>
      intro term hosts
      obtain ⟨middle, first, middleHosts⟩ := hosts_forward hosts step
      obtain ⟨after, rest, afterHosts⟩ := recurse middle middleHosts
      exact ⟨after,
        Mettapedia.GSLT.GSLT.MultiStep.step (S := langGSLT universalTheory) first rest,
        afterHosts⟩

/-- A run of a term that holds a configuration, ending where the theory has
no step, is a halting run of the machine. -/
theorem haltsFrom_of_multiStep {machine : Machine}
    {term final : (langGSLT universalTheory).Term}
    (run : (langGSLT universalTheory).MultiStep term final)
    (normal : (langGSLT universalTheory).IsNormalForm final) :
    ∀ configuration : Configuration, Hosts machine configuration.term term →
      ∃ last : Configuration, Reaches machine configuration.term last.term ∧
        Halted machine last.term ∧ Hosts machine last.term final := by
  induction run with
  | refl term =>
      intro configuration hosts
      exact ⟨configuration, .refl, (halted_iff_isNormalForm hosts).mpr normal, hosts⟩
  | step first _ recurse =>
      intro configuration hosts
      obtain ⟨next, machineStep, nextHosts⟩ := hosts_backward hosts first
      obtain ⟨last, reaches, halted, lastHosts⟩ := recurse normal next nextHosts
      exact ⟨last, .head machineStep reaches, halted, lastHosts⟩

/-- **The theory runs every machine.**  A machine halts from a configuration
exactly when the bag of its rows and that configuration reaches a term with
no step. -/
theorem haltsFrom_iff_universal (machine : Machine) (configuration : Configuration) :
    HaltsFrom machine configuration.term ↔
      ∃ final, (langGSLT universalTheory).MultiStep (withTable machine configuration.term)
        final ∧ (langGSLT universalTheory).IsNormalForm final := by
  constructor
  · rintro ⟨last, reaches, halted⟩
    obtain ⟨lastConfiguration, rfl, -⟩ :=
      reaches_term_invariant (fun _ => True) (fun _ _ _ _ _ => trivial) trivial reaches
    obtain ⟨final, run, finalHosts⟩ :=
      multiStep_of_reaches reaches _ (hosts_withTable machine configuration.term)
    exact ⟨final, run, (halted_iff_isNormalForm finalHosts).mp halted⟩
  · rintro ⟨final, run, normal⟩
    obtain ⟨last, reaches, halted, -⟩ :=
      haltsFrom_of_multiStep run normal configuration (hosts_withTable machine _)
    exact ⟨last.term, reaches, halted⟩

/-- And the term it stops at holds the configuration the machine stops at. -/
theorem universal_final_hosts {machine : Machine} {configuration : Configuration}
    {final : Pattern}
    (run : (langGSLT universalTheory).MultiStep (withTable machine configuration.term) final)
    (normal : (langGSLT universalTheory).IsNormalForm final) :
    ∃ last : Configuration, Reaches machine configuration.term last.term ∧
      Halted machine last.term ∧ Hosts machine last.term final :=
  haltsFrom_of_multiStep run normal configuration (hosts_withTable machine _)

/-! ## A morphism of GSLTs -/

/-- The machine as a GSLT on its configurations. -/
def configurationGSLT (machine : Machine) : Mettapedia.GSLT.GSLT :=
  Mettapedia.OSLF.Framework.GSLTTypeSynthesis.equalityGSLT Configuration
    fun configuration next =>
      Step base (turingMachine machine) configuration.term next.term

/-- The relation "the two terms hold related configurations" is a
bisimulation of the theory whenever the relation on configurations is one of
the machine. -/
private theorem lifted_isBisimulation {machine : Machine}
    {relation : Configuration → Configuration → Prop}
    (bisimulation : (configurationGSLT machine).IsBisimulation relation) :
    (langGSLT universalTheory).IsBisimulation fun left right =>
      ∃ first second : Configuration, relation first second ∧
        Hosts machine first.term left ∧ Hosts machine second.term right := by
  obtain ⟨forward, backward⟩ := bisimulation
  constructor
  · rintro left right ⟨first, second, related, leftHosts, rightHosts⟩ leftNext leftStep
    obtain ⟨firstNext, firstStep, leftNextHosts⟩ := hosts_backward leftHosts leftStep
    obtain ⟨secondNext, secondStep, nextRelated⟩ := forward related firstStep
    obtain ⟨rightNext, rightStep, rightNextHosts⟩ := hosts_forward rightHosts secondStep
    exact ⟨rightNext, rightStep, firstNext, secondNext, nextRelated, leftNextHosts,
      rightNextHosts⟩
  · rintro left right ⟨first, second, related, leftHosts, rightHosts⟩ rightNext rightStep
    obtain ⟨secondNext, secondStep, rightNextHosts⟩ := hosts_backward rightHosts rightStep
    obtain ⟨firstNext, firstStep, nextRelated⟩ := backward related secondStep
    obtain ⟨leftNext, leftStep, leftNextHosts⟩ := hosts_forward leftHosts firstStep
    exact ⟨leftNext, leftStep, firstNext, secondNext, nextRelated, leftNextHosts,
      rightNextHosts⟩

/-- **The map from a machine into the universal theory is a morphism of
GSLTs**: it preserves bisimilarity. -/
def intoUniversal (machine : Machine) :
    Mettapedia.GSLT.GSLT.Morphism (configurationGSLT machine) (langGSLT universalTheory) where
  toFun configuration := withTable machine configuration.term
  preserves_bisim := by
    rintro first second ⟨relation, bisimulation, related⟩
    exact ⟨_, lifted_isBisimulation bisimulation, first, second, related,
      hosts_withTable machine _, hosts_withTable machine _⟩

/-- **It reflects bisimilarity as well.**  Two configurations of a machine
are bisimilar exactly when their bags are bisimilar in the universal
theory. -/
theorem bisimilar_withTable_iff (machine : Machine) (first second : Configuration) :
    (configurationGSLT machine).Bisimilar first second ↔
      (langGSLT universalTheory).Bisimilar (withTable machine first.term)
        (withTable machine second.term) := by
  constructor
  · exact fun bisimilar => (intoUniversal machine).preserves_bisim bisimilar
  · rintro ⟨relation, ⟨forward, backward⟩, related⟩
    refine ⟨fun left right => ∃ leftTerm rightTerm, relation leftTerm rightTerm ∧
      Hosts machine left.term leftTerm ∧ Hosts machine right.term rightTerm, ⟨?_, ?_⟩,
      _, _, related, hosts_withTable machine _, hosts_withTable machine _⟩
    · rintro left right ⟨leftTerm, rightTerm, inRelation, leftHosts, rightHosts⟩ leftNext
        leftStep
      obtain ⟨leftAfter, leftTermStep, leftAfterHosts⟩ := hosts_forward leftHosts leftStep
      obtain ⟨rightAfter, rightTermStep, afterRelated⟩ := forward inRelation leftTermStep
      obtain ⟨rightNext, rightStep, rightAfterHosts⟩ := hosts_backward rightHosts rightTermStep
      exact ⟨rightNext, rightStep, leftAfter, rightAfter, afterRelated, leftAfterHosts,
        rightAfterHosts⟩
    · rintro left right ⟨leftTerm, rightTerm, inRelation, leftHosts, rightHosts⟩ rightNext
        rightStep
      obtain ⟨rightAfter, rightTermStep, rightAfterHosts⟩ := hosts_forward rightHosts rightStep
      obtain ⟨leftAfter, leftTermStep, afterRelated⟩ := backward inRelation rightTermStep
      obtain ⟨leftNext, leftStep, leftAfterHosts⟩ := hosts_backward leftHosts leftTermStep
      exact ⟨leftNext, leftStep, leftAfter, rightAfter, afterRelated, leftAfterHosts,
        rightAfterHosts⟩

/-! ## Interaction -/

/-- The validated universal theory. -/
def universal : ValidatedLanguageDef := ⟨universalTheory, universalTheory_validate_eq_nil⟩

/-- The bag is a contact between things of one sort. -/
theorem mix_is_same_sort_contact :
    contactRepresentation? (TypeDecl.plain "Soup") mixConstructor =
      some (.collection .hashBag) := by
  rfl

/-- **The universal theory is interactive**: a row and a configuration, two
terms of one sort, meet in the bag at the head of a rewrite. -/
theorem universalTheory_isInteractive : IsInteractive universalTheory :=
  ⟨{ presentation := universal
     interactingSort := ⟨TypeDecl.plain "Soup",
       .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))⟩
     contactConstructor := ⟨mixConstructor, mixConstructor_mem⟩
     interactionRewrite := ⟨interiorRightRule, interiorRightRule_mem⟩
     contactRepresentation := .collection .hashBag
     representsContact := mix_is_same_sort_contact
     interactionHeaded := ⟨rfl, by decide⟩ },
    rfl, isBaseRewrite_of_premises_eq_nil rfl⟩

/-- **No machine is interactive; the theory that runs them all is.**  A
machine has its table in its rules, and its only contact is between a state
and a tape.  The universal theory has the table in its terms, and there a row
meets a configuration as one term of the sort of bags meets another. -/
theorem machine_versus_universal (machine : Machine) :
    ¬ AdmitsInteractivePresentation (turingMachine machine) ∧
      IsInteractive universalTheory :=
  ⟨turingMachine_not_interactive machine, universalTheory_isInteractive⟩

/-! ## The types of the universal theory -/

open Mettapedia.OSLF.Framework.GSLTTypeSynthesis in
/-- The terms that hold, with the table of a machine, a configuration with a
given property.  It respects the laws of the bag, so it is a predicate of the
type system generated from the universal theory: every machine is a type
there, and so is every property of its configurations. -/
def holding (machine : Machine) (property : Configuration → Prop) :
    EquationPredicate (langGSLT universalTheory) :=
  ⟨fun term => ∃ configuration, property configuration ∧ Hosts machine configuration.term term,
    by
      intro left right equivalent
      have forward : EquationEquiv base universalTheory left right := equivalent
      constructor
      · rintro ⟨configuration, holds, hosts⟩
        exact ⟨configuration, holds, hosts.of_equiv (Relation.EqvGen.symm _ _ forward)⟩
      · rintro ⟨configuration, holds, hosts⟩
        exact ⟨configuration, holds, hosts.of_equiv forward⟩⟩

/-- **On the terms of a machine, `◇` of the universal theory is `◇` of the
machine.** -/
theorem diamond_holding {machine : Machine} (property : Configuration → Prop)
    {configuration : Configuration} {term : Pattern}
    (hosts : Hosts machine configuration.term term) :
    langDiamond universalTheory (holding machine property) term ↔
      ∃ next : Configuration,
        Step base (turingMachine machine) configuration.term next.term ∧ property next := by
  rw [langDiamond_spec]
  constructor
  · rintro ⟨after, step, held, holds, heldHosts⟩
    obtain ⟨next, machineStep, nextHosts⟩ := hosts_backward hosts step
    obtain rfl := hosts_unique heldHosts nextHosts
    exact ⟨held, machineStep, holds⟩
  · rintro ⟨next, machineStep, holds⟩
    obtain ⟨after, step, afterHosts⟩ := hosts_forward hosts machineStep
    exact ⟨after, step, next, holds, afterHosts⟩

/-- The type of a machine is closed under the steps of the theory. -/
theorem holding_step {machine : Machine} {term after : Pattern}
    (held : holding machine (fun _ => True) term)
    (step : (langGSLT universalTheory).Step term after) :
    holding machine (fun _ => True) after := by
  obtain ⟨configuration, -, hosts⟩ := held
  obtain ⟨next, -, nextHosts⟩ := hosts_backward hosts step
  exact ⟨next, trivial, nextHosts⟩

/-! ## The classic machines inside the theory -/

/-- Radó's table in the theory: from the blank tape the bag reaches a term
with no step, and that term holds the configuration with four ones. -/
theorem busyBeaver2_in_universal :
    ∃ final,
      (langGSLT universalTheory).MultiStep (withTable busyBeaver2 Configuration.blank.term)
        final ∧
      (langGSLT universalTheory).IsNormalForm final ∧
      Hosts busyBeaver2 busyBeaver2Final.term final := by
  obtain ⟨final, run, finalHosts⟩ := multiStep_of_reaches busyBeaver2_run.1 _
    (hosts_withTable busyBeaver2 Configuration.blank.term)
  exact ⟨final, run, (halted_iff_isNormalForm finalHosts).mp busyBeaver2_run.2, finalHosts⟩

/-- Turing's first example in the theory: the bag never reaches a term with
no step. -/
theorem alternating_in_universal :
    ¬ ∃ final,
      (langGSLT universalTheory).MultiStep (withTable alternating Configuration.blank.term)
        final ∧ (langGSLT universalTheory).IsNormalForm final :=
  fun halts => alternating_never_halts
    ((haltsFrom_iff_universal alternating Configuration.blank).mpr halts)

end Mettapedia.Languages.TuringMachine
