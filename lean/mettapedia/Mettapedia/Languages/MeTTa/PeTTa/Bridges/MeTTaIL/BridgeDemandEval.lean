import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.BridgeEval
import Mettapedia.Languages.MeTTa.PeTTa.BridgeDemandLibrary

/-! Body execution at actual numeric argument values composes through
the checked mixed-demand library bridge. No runtime demand is altered.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WireKit

open Mettapedia.Languages.MeTTa.PeTTa.BridgeKit
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval

theorem demanded_body_returns {library : Library} {head : String} {row : SpaceSemantics.Equation}
    (checked : library.check = true) (found : library.equationOf head = some row)
    (ready : Library.demandReady library row = true) (state : State)
    (arguments values : List Atom) (answer : Atom)
    (length : values.length = (library.formals head).length)
    (collected : ArgumentsReturn library.runtime [] head 0 state arguments state values)
    (body : PureReturns library.runtime (Library.bind (library.formals head) values) state (library.body head) state answer) :
    PureReturns library.runtime [] state (.expression (.symbol head :: arguments)) state answer :=
  Library.demand_call checked found ready [] state state state arguments values answer length collected body

#print axioms demanded_body_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WireKit
