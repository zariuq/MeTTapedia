import Mettapedia.Languages.MeTTa.PeTTa.MachineClauseReads
import Mettapedia.Languages.MeTTa.PeTTa.MachineConditionSyntax

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MachineClauseReads.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.UnifyingConstraintPresentation (presentation)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison (atomAction)
open GSLTBindingPatterns ListView Unifying UnifyingDisequality

private def integer (value : Int) : Atom := .grounded (.int value)
private def literal (value : Atom) : Atom := .expression [.symbol "pm:lit", value]
private def arguments (first second : Atom) : Atom := .expression [first, second]
private def clause : Atom := row (.symbol "f") (integer 0)
  (head (arguments (.var "x") (.var "x"))) (literal (.var "x"))
private def query (first second : Atom) : Atom := row (.symbol "f") (integer 0)
  (head (arguments first second)) (.var "out")
private def opened : Atom := LibTransformStep.rename 0 clause

private def resolved (result : Unified) (names : List String) : Option (List Atom) :=
  match result with
  | .ok bindings => some (names.map fun name => resolve bindings (.var name))
  | _ => none

theorem head_and_body_share_the_same_binding :
    resolved (unifyBinding [] (quoted opened) (query (integer 7) (integer 7))) ["out"] =
      some [literal (integer 7)] := by decide +kernel

theorem repeated_parameter_rejects_conflicting_call :
    unifyBinding [] (quoted opened) (query (integer 7) (integer 8)) = .clash := by decide +kernel

theorem incoming_caller_binding_survives :
    resolved (unifyBinding [("x", integer 42)] (quoted opened) (query (integer 7) (integer 7)))
      ["x", "out"] = some [integer 42, literal (integer 7)] := by decide +kernel

theorem skipping_clause_opening_captures_the_caller :
    unifyBinding [("x", integer 42)] (quoted clause) (query (integer 7) (integer 7)) = .clash := by
  decide +kernel

theorem open_call_preserves_variable_sharing :
    let result := unifyBinding [] (quoted opened) (query (.var "u") (.var "v"))
    resolved result ["u", "v", "out"] = some [.var "v", .var "v", literal (.var "v")] := by
  decide +kernel

theorem operation_named_constructor_remains_data :
    resolved (unifyBinding [] (quoted opened)
      (query (.expression [.symbol "cons", .symbol "a", .expression [.symbol "b"]])
        (.expression [.symbol "cons", .symbol "a", .expression [.symbol "b"]]))) ["out"] =
      some [literal (.expression [.symbol "cons", .symbol "a", .expression [.symbol "b"]])] := by
  decide +kernel

theorem printed_string_is_not_the_symbol :
    unifyBinding [] (quoted opened)
      (query (.symbol "a") (.grounded (.string "a"))) = .clash := by decide +kernel

private def isClause : Atom → Bool
  | .expression (.symbol "pm:clause" :: _) => true
  | _ => false

private def sourcePatterns : List Atom := MachineConditionSyntax.conditions.filterMap fun condition =>
  match condition with
  | .bare pattern | .unary _ pattern => if isClause pattern then some pattern else none
  | _ => none

private def hasClauseLayout : Atom → Bool
  | .expression [.symbol "pm:clause", _, _, .expression [.symbol "pm:head", _], _] => true
  | _ => false

/-- These are the actual pinned table's clause reads and negative probes. -/
theorem all_production_clause_conditions_are_present : sourcePatterns.length = 10 := by decide +kernel

theorem production_clause_conditions_have_the_joint_layout :
    sourcePatterns.all hasClauseLayout = true := by decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.MachineClauseReads.Controls
