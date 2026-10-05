import Mettapedia.Languages.Chaitin.TuringPrograms
import Mettapedia.Languages.Chaitin.EnvironmentLaws
import Mettapedia.Languages.Chaitin.ExpressionLaws

/-!
# Semantic correctness of the historical row-search program

The recursive Lisp procedure selects the first row matching both state and
scanned symbol. Its proof follows the finite row list and composes evaluation
derivations. The binding contract tracks the primitive and recursive names
that the dynamically scoped procedure actually uses.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Chaitin.TuringPrograms

open PureEvaluation Expressions

def lookupFunction : SExpr := lambda ["rows", "state", "scanned"] lookupBody

/-- The exact function and primitive bindings used by the row procedure. -/
structure RowLookupEnvironment (environment : Environment) : Prop where
  conditional : lookup environment (.symbol "if") = .symbol "if"
  car : lookup environment (.symbol "car") = .symbol "car"
  cdr : lookup environment (.symbol "cdr") = .symbol "cdr"
  equal : lookup environment (.symbol "=") = .symbol "="
  nil : lookup environment (.symbol "nil") = SExpr.nil
  procedure : lookup environment (.symbol "find-row") = lookupFunction

def rowScope (environment : Environment) (rows : List SExpr) (state scanned : SExpr) :
    Environment :=
  bindNames [.symbol "rows", .symbol "state", .symbol "scanned"]
    [.list rows, state, scanned] environment

theorem rowScope_preserves (environment : Environment) (rows : List SExpr)
    (state scanned : SExpr) (name : String)
    (absent : SExpr.symbol name ∉ ([.symbol "rows", .symbol "state", .symbol "scanned"] : List SExpr)) :
    lookup (rowScope environment rows state scanned) (.symbol name) =
      lookup environment (.symbol name) :=
  EnvironmentLaws.lookup_bindNames_of_not_mem _ _ _ _ absent

theorem RowLookupEnvironment.rowScope {environment : Environment}
    (bindings : RowLookupEnvironment environment) (rows : List SExpr)
    (state scanned : SExpr) :
    RowLookupEnvironment (rowScope environment rows state scanned) := by
  exact ⟨
    (rowScope_preserves environment rows state scanned "if" (by decide)).trans
      bindings.conditional,
    (rowScope_preserves environment rows state scanned "car" (by decide)).trans bindings.car,
    (rowScope_preserves environment rows state scanned "cdr" (by decide)).trans bindings.cdr,
    (rowScope_preserves environment rows state scanned "=" (by decide)).trans bindings.equal,
    (rowScope_preserves environment rows state scanned "nil" (by decide)).trans bindings.nil,
    (rowScope_preserves environment rows state scanned "find-row" (by decide)).trans
      bindings.procedure⟩

theorem rowScope_rows (environment : Environment) (rows : List SExpr)
    (state scanned : SExpr) :
    lookup (rowScope environment rows state scanned) (.symbol "rows") = .list rows :=
  EnvironmentLaws.lookup_bindNames_index 0 _ _ _ _ rfl (by decide)

theorem rowScope_state (environment : Environment) (rows : List SExpr)
    (state scanned : SExpr) :
    lookup (rowScope environment rows state scanned) (.symbol "state") = state :=
  EnvironmentLaws.lookup_bindNames_index 1 _ _ _ _ rfl (by decide)

theorem rowScope_scanned (environment : Environment) (rows : List SExpr)
    (state scanned : SExpr) :
    lookup (rowScope environment rows state scanned) (.symbol "scanned") = scanned :=
  EnvironmentLaws.lookup_bindNames_index 2 _ _ _ _ rfl (by decide)

/-- Actual evaluation of the historical recursive row search. This statement
is stronger than the encoded-table case: rows and both compared values may
be arbitrary historical Lisp data. -/
theorem lookup_apply (rows : List SExpr) (state scanned : SExpr)
    (environment : Environment) (bindings : RowLookupEnvironment environment) :
    PureApply environment lookupFunction [.list rows, state, scanned]
      (lookupRows state scanned rows) := by
  induction rows generalizing environment with
  | nil =>
      apply PureEvaluation.apply_lambda _ _ _
      change PureEval (rowScope environment [] state scanned) lookupBody SExpr.nil
      let scope := rowScope environment [] state scanned
      have localBindings : RowLookupEnvironment scope := bindings.rowScope [] state scanned
      have rowsRun : PureEval scope (.symbol "rows") SExpr.nil :=
        eval_word (rowScope_rows environment [] state scanned)
      have nilRun : PureEval scope (.symbol "nil") SExpr.nil := eval_word localBindings.nil
      unfold lookupBody
      apply eval_if localBindings.conditional (eval_equal localBindings.equal rowsRun nilRun)
      simpa [SExpr.truth_boolean] using nilRun
  | cons row rest recurse =>
      apply PureEvaluation.apply_lambda _ _ _
      change PureEval (rowScope environment (row :: rest) state scanned) lookupBody
        (lookupRows state scanned (row :: rest))
      let scope := rowScope environment (row :: rest) state scanned
      have localBindings : RowLookupEnvironment scope := bindings.rowScope (row :: rest) state scanned
      have rowsRun : PureEval scope (.symbol "rows") (.list (row :: rest)) :=
        eval_word (rowScope_rows environment (row :: rest) state scanned)
      have stateRun : PureEval scope (.symbol "state") state :=
        eval_word (rowScope_state environment (row :: rest) state scanned)
      have scannedRun : PureEval scope (.symbol "scanned") scanned :=
        eval_word (rowScope_scanned environment (row :: rest) state scanned)
      have nilRun : PureEval scope (.symbol "nil") SExpr.nil := eval_word localBindings.nil
      have restRun : PureEval scope (call "cdr" [.symbol "rows"]) (.list rest) :=
        eval_cdr localBindings.cdr rowsRun
      have recursiveRun : PureEval scope lookupRestExpr (lookupRows state scanned rest) := by
        exact PureEval.application (eval_word localBindings.procedure)
          (by intro same; cases same) (by intro same; cases same)
          (.cons restRun (.cons stateRun (.cons scannedRun (.nil scope))))
          (recurse scope localBindings)
      have rowRun : PureEval scope (call "car" [.symbol "rows"]) row :=
        eval_car localBindings.car rowsRun
      have stateFieldRun := eval_field localBindings.car localBindings.cdr 0 rowRun
      have scannedFieldRun := eval_field localBindings.car localBindings.cdr 1 rowRun
      have symbolBranch := eval_if_equal_branches localBindings.conditional localBindings.equal
        scannedFieldRun scannedRun rowRun recursiveRun
      have stateBranch := eval_if_equal_branches localBindings.conditional localBindings.equal
        stateFieldRun stateRun symbolBranch recursiveRun
      have nonempty : (.list (row :: rest) : SExpr) ≠ SExpr.nil := by
        simp [SExpr.nil]
      unfold lookupBody
      apply eval_if localBindings.conditional (eval_equal localBindings.equal rowsRun nilRun)
      simpa only [SExpr.truth_boolean, nonempty, decide_false, Bool.false_eq_true, ↓reduceIte,
        lookupRows] using stateBranch

theorem lookup_encoded_apply (entries : List TuringMachine.Transition) (state scanned : Nat)
    (environment : Environment) (bindings : RowLookupEnvironment environment) :
    PureApply environment lookupFunction
      [encodeTable entries, .number state, .number scanned]
      (((entries.find? (fun entry => entry.state == state && entry.read == scanned)).map
        encodeTransition).getD SExpr.nil) := by
  rw [← lookupRows_encode]
  exact lookup_apply (entries.map encodeTransition) (.number state) (.number scanned)
    environment bindings

/-- This is the environment created by the actual outer `let`. -/
def rowBaseEnvironment : Environment :=
  bindNames [.symbol "find-row"] [lookupFunction] cleanEnvironment

theorem rowBaseEnvironment_preserves (name : String) (different : name ≠ "find-row") :
    lookup rowBaseEnvironment (.symbol name) = lookup cleanEnvironment (.symbol name) := by
  apply EnvironmentLaws.lookup_bindNames_of_not_mem
  intro member
  exact different (SExpr.symbol.inj (List.mem_singleton.mp member))

theorem rowBaseEnvironment_contract : RowLookupEnvironment rowBaseEnvironment := by
  exact ⟨
    (rowBaseEnvironment_preserves "if" (by decide)).trans (by decide),
    (rowBaseEnvironment_preserves "car" (by decide)).trans (by decide),
    (rowBaseEnvironment_preserves "cdr" (by decide)).trans (by decide),
    (rowBaseEnvironment_preserves "=" (by decide)).trans (by decide),
    (rowBaseEnvironment_preserves "nil" (by decide)).trans lookup_clean_nil,
    EnvironmentLaws.lookup_bindNames_head "find-row" [] [lookupFunction] cleanEnvironment⟩

theorem rowBaseEnvironment_quote :
    lookup rowBaseEnvironment (.symbol "'") = .symbol "'" :=
  (rowBaseEnvironment_preserves "'" (by decide)).trans (by decide)

/-- A closed historical Lisp expression performing the row search. -/
def rowSearchProgram (rows : List SExpr) (state scanned : SExpr) : SExpr :=
  letValue "find-row" lookupProgram
    (call "find-row" [quote (.list rows), quote state, quote scanned])

theorem rowSearchProgram_eval (rows : List SExpr) (state scanned : SExpr) :
    PureEval cleanEnvironment (rowSearchProgram rows state scanned)
      (lookupRows state scanned rows) := by
  apply eval_letValue (by decide)
    (eval_quote (by decide) (lambda ["rows", "state", "scanned"] lookupBody))
  change PureEval rowBaseEnvironment
    (call "find-row" [quote (.list rows), quote state, quote scanned])
    (lookupRows state scanned rows)
  exact PureEval.application (eval_word rowBaseEnvironment_contract.procedure)
    (by intro same; cases same) (by intro same; cases same)
    (.cons (eval_quote rowBaseEnvironment_quote (.list rows))
      (.cons (eval_quote rowBaseEnvironment_quote state)
        (.cons (eval_quote rowBaseEnvironment_quote scanned) (.nil rowBaseEnvironment))))
    (lookup_apply rows state scanned rowBaseEnvironment rowBaseEnvironment_contract)

/-- The closed Lisp search has exactly the specified value and preserves
all outer input, output, and debug observations. -/
theorem rowSearchProgram_evaluates (rows : List SExpr) (state scanned : SExpr)
    (input : List Bool) :
    Evaluates (rowSearchProgram rows state scanned) input
      ⟨.success (lookupRows state scanned rows), [], []⟩ input :=
  (rowSearchProgram_eval rows state scanned).evaluates input

theorem rowSearchProgram_value_iff (rows : List SExpr) (state scanned : SExpr)
    (input rest : List Bool) (value : SExpr) :
    Evaluates (rowSearchProgram rows state scanned) input ⟨.success value, [], []⟩ rest ↔
      value = lookupRows state scanned rows ∧ rest = input := by
  constructor
  · intro run
    have same := run.deterministic (rowSearchProgram_evaluates rows state scanned input)
    exact ⟨Result.success.inj (congrArg Observation.result same.1), same.2⟩
  · rintro ⟨rfl, sameRest⟩
    rw [sameRest]
    exact rowSearchProgram_evaluates rows state scanned input

theorem rowSearchProgram_executable (rows : List SExpr) (state scanned : SExpr)
    (input : List Bool) :
    ∃ fuel, execute fuel (rowSearchProgram rows state scanned) input =
      some (⟨.success (lookupRows state scanned rows), [], []⟩, input) :=
  (rowSearchProgram_eval rows state scanned).executable input

theorem rowSearchProgram_encoded (machine : TuringMachine.Machine)
    (configuration : TuringMachine.Configuration) (input : List Bool) :
    Evaluates (rowSearchProgram (machine.transitions.map encodeTransition)
      (.number configuration.state) (.number configuration.scanned)) input
      ⟨.success (((machine.entryFor configuration).map encodeTransition).getD SExpr.nil), [], []⟩
      input := by
  simpa only [lookupRows_eq_entryFor] using
    rowSearchProgram_evaluates (machine.transitions.map encodeTransition)
      (.number configuration.state) (.number configuration.scanned) input

/-- A matching state is insufficient when the scanned symbol differs. -/
theorem different_scanned_symbol_runtime (input : List Bool) :
    Evaluates (rowSearchProgram [encodeTransition ⟨3, 6, 9, .right, 4⟩]
      (.number 3) (.number 7)) input ⟨.success SExpr.nil, [], []⟩ input := by
  simpa only [wrong_symbol_does_not_match] using
    rowSearchProgram_evaluates [encodeTransition ⟨3, 6, 9, .right, 4⟩]
      (.number 3) (.number 7) input

/-- Duplicate matching rows retain the historical first-row priority. -/
theorem first_matching_row_runtime (input : List Bool) :
    Evaluates (rowSearchProgram
      [encodeTransition ⟨3, 7, 9, .right, 4⟩, encodeTransition ⟨3, 7, 8, .left, 5⟩]
      (.number 3) (.number 7)) input
      ⟨.success (encodeTransition ⟨3, 7, 9, .right, 4⟩), [], []⟩ input := by
  simpa only [first_matching_row_wins] using
    rowSearchProgram_evaluates
      [encodeTransition ⟨3, 7, 9, .right, 4⟩, encodeTransition ⟨3, 7, 8, .left, 5⟩]
      (.number 3) (.number 7) input

theorem second_matching_row_is_not_the_result (input rest : List Bool) :
    ¬ Evaluates (rowSearchProgram
      [encodeTransition ⟨3, 7, 9, .right, 4⟩, encodeTransition ⟨3, 7, 8, .left, 5⟩]
      (.number 3) (.number 7)) input
      ⟨.success (encodeTransition ⟨3, 7, 8, .left, 5⟩), [], []⟩ rest := by
  intro run
  have same := run.deterministic (first_matching_row_runtime input)
  have result := Result.success.inj (congrArg Observation.result same.1)
  have row := encodeTransition_injective result
  cases row

end Mettapedia.Languages.Chaitin.TuringPrograms
