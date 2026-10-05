import Mettapedia.Languages.Chaitin.RowSearch
import Mettapedia.Languages.Chaitin.TransitionEvaluation
import Mettapedia.Languages.Chaitin.OperationalLaws

/-!
# The historical interpreter's dynamic environment

The contract mentions precisely the names read by the three ordinary Lisp
procedures. Rebinding their local parameters preserves the contract. The
closed interpreter establishes it through the same nested lets as its source.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Chaitin.TuringInterpreter

open TuringPrograms PureEvaluation Expressions

def loopFunction : SExpr := lambda ["table", "configuration"] interpreterBody

def names : List String :=
  ["if", "car", "cdr", "cons", "=", "'", "nil", "find-row", "move-row", "run-table"]

structure EnvironmentContract (environment : Environment) : Prop extends MoveEnvironment environment where
  findRow : lookup environment (.symbol "find-row") = lookupFunction
  moveRow : lookup environment (.symbol "move-row") = transitionFunction
  runTable : lookup environment (.symbol "run-table") = loopFunction

theorem EnvironmentContract.rowLookup {environment : Environment}
    (contract : EnvironmentContract environment) : RowLookupEnvironment environment :=
  ⟨contract.conditional, contract.car, contract.cdr, contract.equal, contract.nil, contract.findRow⟩

theorem EnvironmentContract.bindNames {environment : Environment}
    (contract : EnvironmentContract environment) (parameters arguments : List SExpr)
    (fresh : ∀ name ∈ names, SExpr.symbol name ∉ parameters) :
    EnvironmentContract (Chaitin.bindNames parameters arguments environment) := by
  have preserved (name : String) (member : name ∈ names) :
      lookup (Chaitin.bindNames parameters arguments environment) (.symbol name) =
        lookup environment (.symbol name) :=
    EnvironmentLaws.lookup_bindNames_of_not_mem _ _ _ _ (fresh name member)
  exact ⟨⟨
    (preserved "if" (by decide)).trans contract.conditional,
    (preserved "car" (by decide)).trans contract.car,
    (preserved "cdr" (by decide)).trans contract.cdr,
    (preserved "cons" (by decide)).trans contract.cons,
    (preserved "=" (by decide)).trans contract.equal,
    (preserved "'" (by decide)).trans contract.quote,
    (preserved "nil" (by decide)).trans contract.nil⟩,
    (preserved "find-row" (by decide)).trans contract.findRow,
    (preserved "move-row" (by decide)).trans contract.moveRow,
    (preserved "run-table" (by decide)).trans contract.runTable⟩

def loopScope (environment : Environment) (table configuration : SExpr) : Environment :=
  bindNames [.symbol "table", .symbol "configuration"] [table, configuration] environment

def selectedScope (environment : Environment) (selected : SExpr) : Environment :=
  bindNames [.symbol "selected"] [selected] environment

theorem EnvironmentContract.loopScope {environment : Environment}
    (contract : EnvironmentContract environment) (table configuration : SExpr) :
    EnvironmentContract (loopScope environment table configuration) :=
  contract.bindNames _ _ (by decide)

theorem EnvironmentContract.selectedScope {environment : Environment}
    (contract : EnvironmentContract environment) (selected : SExpr) :
    EnvironmentContract (selectedScope environment selected) :=
  contract.bindNames _ _ (by decide)

theorem loopScope_table (environment : Environment) (table configuration : SExpr) :
    lookup (loopScope environment table configuration) (.symbol "table") = table :=
  EnvironmentLaws.lookup_bindNames_index 0 _ _ _ _ rfl (by decide)

theorem loopScope_configuration (environment : Environment) (table configuration : SExpr) :
    lookup (loopScope environment table configuration) (.symbol "configuration") = configuration :=
  EnvironmentLaws.lookup_bindNames_index 1 _ _ _ _ rfl (by decide)

theorem selectedScope_selected (environment : Environment) (selected : SExpr) :
    lookup (selectedScope environment selected) (.symbol "selected") = selected := by
  exact EnvironmentLaws.lookup_bindNames_head _ _ _ _

theorem selectedScope_preserves (environment : Environment) (selected : SExpr)
    (name : String) (different : name ≠ "selected") :
    lookup (selectedScope environment selected) (.symbol name) =
      lookup environment (.symbol name) := by
  apply EnvironmentLaws.lookup_bindNames_of_not_mem
  intro member
  exact different (SExpr.symbol.inj (List.mem_singleton.mp member))

def moveBaseEnvironment : Environment :=
  bindNames [.symbol "move-row"] [transitionFunction] rowBaseEnvironment

def baseEnvironment : Environment :=
  bindNames [.symbol "run-table"] [loopFunction] moveBaseEnvironment

theorem baseEnvironment_contract : EnvironmentContract baseEnvironment := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor <;> rfl
  all_goals rfl

theorem moveBase_quote :
    lookup moveBaseEnvironment (.symbol "'") = .symbol "'" := rfl

theorem rowBase_quote :
    lookup rowBaseEnvironment (.symbol "'") = .symbol "'" := rfl

end Mettapedia.Languages.Chaitin.TuringInterpreter
