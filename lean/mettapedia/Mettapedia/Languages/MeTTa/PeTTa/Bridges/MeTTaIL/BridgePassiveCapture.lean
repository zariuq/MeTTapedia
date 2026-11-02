import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.BridgeEval

/-! Calls whose arguments are captured variables or literals preserve
declared demand while reusing an execution proved at their captured values.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WireKit

open Eval
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)

theorem passive_values_capture (program : SpaceSemantics.Program) (caller : Subst) (state : State)
    (head : String) (values arguments : List Atom) (answer : Atom)
    (dispatch : (ioHead head || StdLib.known head || program.equations.any (·.head == head)) = true)
    (ordinary : head ∉ BridgeKit.specialForms)
    (sourcePassive : ∀ (index : Nat) (item : Atom), values[index]? = some item → passiveArgument item = true)
    (targetPassive : ∀ (index : Nat) (item : Atom), arguments[index]? = some item → passiveArgument item = true)
    (same : values.map (applySubst []) = arguments.map (applySubst caller))
    (returned : PureReturns program [] state (.expression (.symbol head :: values)) state answer) :
    PureReturns program caller state (.expression (.symbol head :: arguments)) state answer :=
  captured_call_returns program [] caller state state head values arguments answer dispatch ordinary
    (fun index item found => Or.inr (sourcePassive index item found))
    (fun index item found => Or.inr (targetPassive index item found)) same returned

#print axioms passive_values_capture

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WireKit
