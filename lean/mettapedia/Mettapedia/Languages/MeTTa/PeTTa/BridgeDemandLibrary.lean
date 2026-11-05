import Mettapedia.Languages.MeTTa.PeTTa.BridgeDemand

/-! Literal library functions with evaluated numeric arguments use the
same checked ownership discipline as raw functions. Argument collection is
proved independently according to the actual target declarations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.BridgeKit.Library

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open SpaceSemantics (Program Equation)
open _root_.Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval

def demandReady (L : Library) (equation : Equation) : Bool :=
  equation.arguments == (formalNames equation).map Atom.var && decide (formalNames equation).Nodup &&
    (L.source.equations.filter (·.head == equation.head)).length == 1 &&
    !specialForms.contains equation.head && !ioHead equation.head && !StdLib.known equation.head

theorem demanded_rows {L : Library} (checked : L.check = true) {head : String} {equation : Equation}
    (found : L.equationOf head = some equation) (ready : demandReady L equation = true) :
    L.runtime.equations.filter (·.head == head) = [equation] ∧
      equation.arguments = (L.formals head).map Atom.var ∧ (L.formals head).Nodup ∧
      head ∉ specialForms ∧ ioHead head = false ∧ StdLib.known head = false := by
  have checkParts := checked
  simp only [Library.check, Bool.and_eq_true] at checkParts
  have same : equation.head = head := by simpa using List.find?_some found
  have member := List.mem_of_find?_eq_some found
  have owned := List.all_eq_true.mp checkParts.1.2 equation member
  have fields := ready
  simp only [demandReady, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true'] at fields
  obtain ⟨⟨⟨⟨⟨arguments, distinct⟩, single⟩, ordinary⟩, notIO⟩, notNative⟩ := fields
  subst same
  have formals : L.formals equation.head = formalNames equation := by simp [Library.formals, found]
  rw [formals]
  refine ⟨?_, arguments, distinct, by simpa using ordinary, notIO, notNative⟩
  have own : L.source.equations.filter (·.head == equation.head) = [equation] := by
    obtain ⟨only, rows⟩ := List.length_eq_one_iff.mp single
    have present : equation ∈ L.source.equations.filter (·.head == equation.head) := List.mem_filter.mpr ⟨member, by simp⟩
    rw [rows] at present ⊢
    rw [List.mem_singleton.mp present]
  rw [owned_equations checked owned]
  exact own

theorem demand_call {L : Library} (checked : L.check = true) {head : String} {equation : Equation}
    (found : L.equationOf head = some equation) (ready : demandReady L equation = true)
    (caller : Subst) (before middle after : State) (arguments values : List Atom) (answer : Atom)
    (length : values.length = (L.formals head).length)
    (collected : ArgumentsReturn L.runtime caller head 0 before arguments middle values)
    (bodyReturned : PureReturns L.runtime (bind (L.formals head) values) middle (L.body head) after answer) :
    PureReturns L.runtime caller before (.expression (.symbol head :: arguments)) after answer := by
  obtain ⟨rows, formals, distinct, ordinary, notIO, notNative⟩ := demanded_rows checked found ready
  have body : L.body head = equation.body := by simp [Library.body, found]
  have member : equation ∈ L.runtime.equations.filter (·.head == head) := by rw [rows]; simp
  have registered : L.runtime.equations.any (·.head == head) = true :=
    List.any_eq_true.mpr ⟨equation, (List.mem_filter.mp member).1, (List.mem_filter.mp member).2⟩
  exact authored_demand_call_returns L.runtime caller (bind (L.formals head) values) before middle after
    head arguments values equation.body answer notIO notNative registered ordinary collected
    (PureData.named_equation_clause L.runtime head equation (L.formals head) values rows formals distinct length)
    (body ▸ bodyReturned)

#print axioms demanded_rows
#print axioms demand_call

end Mettapedia.Languages.MeTTa.PeTTa.BridgeKit.Library
