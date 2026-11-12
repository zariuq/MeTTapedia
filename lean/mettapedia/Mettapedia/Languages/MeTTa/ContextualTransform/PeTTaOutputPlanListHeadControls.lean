import Mettapedia.Languages.MeTTa.PeTTa.OutputPlanProgramFormation
import Lean.Elab.Tactic.Cbv

/-! Static list heads are data, while a head needing another call/dispatch
cannot use that emission. The source's unsupported regions keep their meaning
outside this compiler component rather than becoming empty answers. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaOutputPlanListHeadControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa

def program : SpaceSemantics.Program := {equations := [],declarations := []}
def context : OutputPlan.Context := OutputPlan.Context.ofProgram program
def pair (left right : Atom) : Atom := .expression [.symbol "pair",left,right]
def pattern : Atom := .expression [pair (.var "a") (.var "b"),pair (.var "c") (.var "d")]

theorem nested_list_pattern_admitted : (OutputPlan.compileExpression context pattern).isSome = true := by decide +kernel

theorem empty_list_head_admitted :
    (OutputPlan.compileExpression context (.expression [.expression [],.symbol "value"])).isSome = true := by decide +kernel

def callList : Atom := .expression [.symbol "+",.grounded (.int 1),.grounded (.int 2)]

theorem known_call_is_not_static_data : OutputPlan.staticData context callList = false := by decide

theorem quoted_known_call_head_still_requires_evaluation :
    OutputPlan.compileExpression context
      (.expression [.expression [.symbol "quote",callList],.symbol "value"]) = none := by decide +kernel

theorem variable_head_still_requires_dispatch :
    OutputPlan.compileExpression context (.expression [.var "function",.symbol "value"]) = none := by decide +kernel

end Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaOutputPlanListHeadControls
