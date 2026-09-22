import Mettapedia.GSLT.Parsing.PlainBnfGeneratedPeTTaSyntax
import Mettapedia.GSLT.Parsing.GeneratedPeTTaEquationDispatch

/-!
# Dispatch isolation in the whole generated plain-BNF program

The actual generated fixture discharges the literal-head condition for the
existing raw-equation scan. This proves no body-execution or dynamic-extension
claim and retains all ordered source occurrences.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfGeneratedPeTTaDispatch

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open GeneratedPeTTaResultBinding (variableToken)
open GeneratedPeTTaEquationDispatch
open PlainBnfGeneratedPeTTaSyntax (generatedProgram generatedWorkers hasLiteralEquationHead)

private theorem literal_symbol_not_variable (symbol : String)
    (literal : (match symbol.toList with | [] | '$' :: _ => false | _ => true) = true) :
    variableToken symbol = false := by
  have noDollar : symbol.startsWith "$" = false := by
    rw [String.startsWith_string_eq_false_iff]
    cases chars : symbol.toList with
    | nil => simp [chars] at literal
    | cons first rest =>
        by_cases dollar : first = '$'
        · simp [chars, dollar] at literal
        · simp [Ne.symm dollar]
  simp [variableToken, noDollar]

theorem parsed_literal_head (source head body : SExpr)
    (parsed : equation? source = some (head, body))
    (literal : hasLiteralEquationHead source = true) :
    ∃ symbol schemas, head = .list (.atom symbol :: schemas) ∧ variableToken symbol = false := by
  have shape := (equation?_eq_some_iff source head body).mp parsed
  subst source
  cases head with
  | atom token => simp [hasLiteralEquationHead] at literal
  | list schemas =>
      cases schemas with
      | nil => simp [hasLiteralEquationHead] at literal
      | cons first rest =>
          cases first with
          | list terms => simp [hasLiteralEquationHead] at literal
          | atom symbol =>
              exact ⟨symbol, rest, rfl, literal_symbol_not_variable symbol literal⟩

private theorem worker_symbol_is_worker (relation : String) (inputs outputs : Nat) (source : SExpr)
    (symbol : equationSymbol? source =
      some (PlainBnfGeneratedPeTTaSyntax.workerName relation inputs outputs)) :
    PlainBnfGeneratedPeTTaSyntax.isWorkerEquation source = true := by
  cases parsed : equation? source with
  | none => simp [equationSymbol?, parsed] at symbol
  | some pair =>
      rcases pair with ⟨head, body⟩
      have shape := (equation?_eq_some_iff source head body).mp parsed
      subst source
      cases head with
      | atom token => simp [equationSymbol?, equation?] at symbol
      | list schemas =>
          cases schemas with
          | nil => simp [equationSymbol?, equation?] at symbol
          | cons first rest =>
              cases first with
              | list terms => simp [equationSymbol?, equation?] at symbol
              | atom actual =>
                  have same : actual = PlainBnfGeneratedPeTTaSyntax.workerName relation inputs outputs := by
                    simpa [equationSymbol?, equation?] using symbol
                  subst actual
                  simp [PlainBnfGeneratedPeTTaSyntax.isWorkerEquation,
                    PlainBnfGeneratedPeTTaSyntax.workerName, String.toList_append]

theorem equationsFor_worker_filter (relation : String) (inputs outputs : Nat)
    (rows : List (Nat × SExpr)) :
    equationsFor (PlainBnfGeneratedPeTTaSyntax.workerName relation inputs outputs)
      (rows.filter (fun row => PlainBnfGeneratedPeTTaSyntax.isWorkerEquation row.2)) =
      equationsFor (PlainBnfGeneratedPeTTaSyntax.workerName relation inputs outputs) rows := by
  unfold equationsFor
  rw [List.filter_filter]
  apply List.filter_congr
  intro row _
  by_cases same : equationSymbol? row.2 =
      some (PlainBnfGeneratedPeTTaSyntax.workerName relation inputs outputs)
  · simp [same, worker_symbol_is_worker relation inputs outputs row.2 same]
  · simp [same]

/-- The whole generated fixture is scanned. Its literal-head theorem licenses
discarding every unrelated equation, with no restriction on ground payloads. -/
theorem generated_dispatch_filter (env : Bindings) (symbol : String) (arguments : List SExpr) :
    dispatch env (.list (.atom symbol :: arguments)) generatedProgram =
      dispatch env (.list (.atom symbol :: arguments)) (equationsFor symbol generatedProgram) :=
  dispatch_literal_filter env symbol arguments generatedProgram
    (fun row member head body parsed => parsed_literal_head row.2 head body parsed
      (List.all_eq_true.mp PlainBnfGeneratedPeTTaSyntax.generated_equations_have_literal_heads row member))

/-- For a generated worker call, the full program scan is exactly the scan of
that worker's ordered occurrences. No distinct-value or duplicate quotient is
applied, and the conclusion does not cover later-installed broad equations. -/
theorem generated_worker_dispatch (env : Bindings) (relation : String) (inputs outputs : Nat)
    (arguments : List SExpr) :
    let symbol := PlainBnfGeneratedPeTTaSyntax.workerName relation inputs outputs
    dispatch env (.list (.atom symbol :: arguments)) generatedProgram =
      dispatch env (.list (.atom symbol :: arguments)) (equationsFor symbol generatedWorkers) := by
  dsimp only
  have rows :
      equationsFor (PlainBnfGeneratedPeTTaSyntax.workerName relation inputs outputs) generatedProgram =
        equationsFor (PlainBnfGeneratedPeTTaSyntax.workerName relation inputs outputs) generatedWorkers :=
    (equationsFor_worker_filter relation inputs outputs generatedProgram).symm
  exact (generated_dispatch_filter env _ arguments).trans
    (congrArg (dispatch env (.list (.atom
      (PlainBnfGeneratedPeTTaSyntax.workerName relation inputs outputs) :: arguments))) rows)

end Mettapedia.GSLT.Parsing.PlainBnfGeneratedPeTTaDispatch
