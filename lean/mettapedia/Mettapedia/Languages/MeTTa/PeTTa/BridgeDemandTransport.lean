import Mettapedia.Languages.MeTTa.PeTTa.BridgeDemandLibrary
import Mettapedia.Languages.MeTTa.PeTTa.BridgeTransport

/-! A library's numeric call metadata can be read from its own source while
the actual execution takes place in a larger agreeing loaded program.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.BridgeKit.Library

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open SpaceSemantics (Program Equation)
open Eval

theorem demand_call_in {L : Library} {allowed : String → Bool} {program : Program}
    (checked : L.check = true) (agreement : ProgramAgreementOn allowed L.runtime program)
    {head : String} {equation : Equation} (supported : allowed head = true)
    (found : L.equationOf head = some equation) (ready : demandReady L equation = true)
    (caller : Subst) (before middle after : State) (arguments values : List Atom) (answer : Atom)
    (length : values.length = (L.formals head).length)
    (collected : ArgumentsReturn program caller head 0 before arguments middle values)
    (bodyReturned : PureReturns program (bind (L.formals head) values) middle (L.body head) after answer) :
    PureReturns program caller before (.expression (.symbol head :: arguments)) after answer := by
  obtain ⟨rows, formals, distinct, ordinary, notIO, notNative⟩ := demanded_rows checked found ready
  have body : L.body head = equation.body := by simp [Library.body, found]
  have member : equation ∈ L.runtime.equations.filter (·.head == head) := by rw [rows]; simp
  have registered : (ioHead head || StdLib.known head || program.equations.any (·.head == head)) = true := by
    rw [← agreement.dispatch head supported]
    simp only [notIO, notNative, Bool.false_or]
    exact List.any_eq_true.mpr ⟨equation, (List.mem_filter.mp member).1, (List.mem_filter.mp member).2⟩
  have selected : clauses program head values = [.evaluate (bind (L.formals head) values) equation.body] := by
    apply PureData.selected_clause_agreement agreement supported
    exact PureData.named_equation_clause L.runtime head equation (L.formals head) values rows formals distinct length
  exact authored_demand_call_returns program caller (bind (L.formals head) values) before middle after head arguments values
    equation.body answer notIO notNative (by simpa only [notIO, notNative, Bool.false_or] using registered) ordinary collected
    selected (body ▸ bodyReturned)

#print axioms demand_call_in

end Mettapedia.Languages.MeTTa.PeTTa.BridgeKit.Library
