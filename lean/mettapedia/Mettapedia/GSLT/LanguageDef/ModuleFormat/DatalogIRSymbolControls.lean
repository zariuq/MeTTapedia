import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRExecutable

/-! Ordered symbol guards are admitted, with lexical rather than insertion
order. Mixed scalar types and unbound guard operands remain rejected. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.SymbolControls

open Mettapedia.Languages.Datalog

def clause (operator : ComparisonOperator) : Clause :=
  ⟨⟨["Result"],[.var "X",.var "Y"]⟩,
    [.atom ⟨["Word"],[.var "X"]⟩,.atom ⟨["Word"],[.var "Y"]⟩,
     .comparison ⟨operator,.var "X",.var "Y"⟩]⟩

def program (operator : ComparisonOperator) : Program := ⟨[
  .declaration ⟨["Word"],[⟨"value",.symbol⟩]⟩,
  .declaration ⟨["Result"],[⟨"left",.symbol⟩,⟨"right",.symbol⟩]⟩,
  .rule (clause operator),.output ["Result"]]⟩

def seeds : List GroundFact := [⟨["Word"],[.symbol "z"]⟩,⟨["Word"],[.symbol "a"]⟩]

theorem all_ordered_guards_admitted :
    ([.less,.lessEqual,.greater,.greaterEqual] : List ComparisonOperator).all
      (fun operator => (Executable.prepare (program operator) seeds).toOption.isSome) = true := by
  decide +kernel

theorem strict_and_nonstrict :
    Executable.compare .less (.symbol "a") (.symbol "z") = true ∧
    Executable.compare .greater (.symbol "z") (.symbol "a") = true ∧
    Executable.compare .lessEqual (.symbol "a") (.symbol "a") = true ∧
    Executable.compare .greaterEqual (.symbol "a") (.symbol "a") = true ∧
    Executable.compare .less (.symbol "a") (.symbol "a") = false ∧
    Executable.compare .greater (.symbol "a") (.symbol "z") = false := by decide +kernel

theorem empty_prefix_unicode :
    Executable.compare .less (.symbol "") (.symbol "a") = true ∧
    Executable.compare .less (.symbol "a") (.symbol "aa") = true ∧
    Executable.compare .less (.symbol "é") (.symbol "λ") = true ∧
    Executable.compare .less (.symbol "λ") (.symbol "🙂") = true ∧
    Executable.compare .less (.symbol "10") (.symbol "2") = true := by decide +kernel

theorem mixed_values_do_not_order :
    Executable.compare .less (.symbol "1") (.number 2) = false := by decide +kernel

theorem bad_input_type_refused :
    (Executable.prepare (program .less) [⟨["Word"],[.number 1]⟩]).toOption.isNone = true := by
  decide +kernel

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.SymbolControls
