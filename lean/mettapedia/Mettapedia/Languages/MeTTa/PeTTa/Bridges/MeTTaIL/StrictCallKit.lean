import Mettapedia.Languages.MeTTa.PeTTa.BridgeKit
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.WireKit

/-! Call-by-value evaluation in bridge proofs. An ordinary source passes
evaluated arguments: each argument returns one value and keeps the state,
and an owned head of one equation of distinct variables runs its body under
its formals bound to those values. Inert constructors evaluate their
arguments the same way. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.StrictCallKit

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics (Program Equation)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Mettapedia.Languages.MeTTa.PeTTa.Eval
open Mettapedia.Languages.MeTTa.PeTTa.BridgeKit

/-- Whether the argument at a position is passed raw. -/
def demands (program : Program) : Target → Nat → Bool
  | .function head, index => argumentIsRaw program head index
  | .data, _ => false

/-- Arguments evaluated in order, each to one value, keeping the state. -/
theorem evaluated_arguments (program : Program) (caller : Subst) (state : State) (target : Target) :
    ∀ (arguments values prior : List Atom) (index : Nat) (answers : List Atom),
      List.Forall₂ (fun argument value => PureReturns program caller state argument state value)
        arguments values →
      (∀ offset < arguments.length, demands program target (index + offset) = false) →
      (theory program).MultiStep
        { state, control := .arguments caller target [] (prior ++ values) (index + arguments.length) }
        (finished state answers [] []) →
      (theory program).MultiStep
        { state, control := .arguments caller target arguments prior index }
        (finished state answers [] [])
  | [], [], prior, index, answers, .nil, _, rest => by simpa using rest
  | argument :: arguments, value :: values, prior, index, answers, .cons first later, demand, rest => by
    have here := demand 0 (by simp)
    apply evaluated_argument_answers program caller state state state target argument value answers arguments
      prior index (by cases target with | function head => simpa [demands] using here | data => rfl) first
    apply evaluated_arguments program caller state target arguments values (prior ++ [value]) (index + 1) answers
      later
    · intro offset bounded
      have shifted := demand (offset + 1) (by simp only [List.length_cons]; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1] using shifted
    · simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm 1] using rest

/-- An inert constructor at evaluated arguments returns the constructor of their values. -/
theorem constructor_returns (program : Program) (caller : Subst) (state : State) (head : String)
    (arguments values : List Atom)
    (inert : (ioHead head || StdLib.known head || program.equations.any (·.head == head)) = false)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique"])
    (returns : List.Forall₂ (fun argument value => PureReturns program caller state argument state value)
      arguments values) :
    PureReturns program caller state (.expression (.symbol head :: arguments)) state
      (.expression (.symbol head :: values)) := by
  apply data_call_returns program caller state state head arguments _ inert _ ordinary
  exact evaluated_arguments program caller state .data (.symbol head :: arguments) (.symbol head :: values) [] 0
    [.expression (.symbol head :: values)] (.cons (symbol_returns program caller state head) returns)
    (fun _ _ => rfl) (data_arguments_values_return program caller state _ _)

/-- An owned head that a call-by-value proof may call: one source equation
of distinct variables, not special, input/output or native, and no argument
declared raw anywhere in the runtime. -/
def strictReady (L : Library) (head : String) : Bool :=
  match L.equationOf head with
  | none => false
  | some equation =>
    equation.head == head &&
    equation.arguments == (Library.formalNames equation).map Atom.var &&
    decide (Library.formalNames equation).Nodup &&
    (L.source.equations.filter (·.head == head)).length == 1 &&
    !specialForms.contains head && !ioHead head && !StdLib.known head &&
    (List.range (Library.formalNames equation).length).all fun index => !argumentIsRaw L.runtime head index

/-- **A call by value to an owned head** runs its body under its formals
bound to the arguments' values. -/
theorem strict_call (L : Library) (checked : L.check = true) {head : String}
    (ready : strictReady L head = true)
    (caller : Subst) (state : State) (arguments values : List Atom) (answer : Atom)
    (returns : List.Forall₂ (fun argument value => PureReturns L.runtime caller state argument state value)
      arguments values)
    (length : values.length = (L.formals head).length)
    (returned : PureReturns L.runtime (Library.bind (L.formals head) values) state (L.body head) state answer) :
    PureReturns L.runtime caller state (.expression (.symbol head :: arguments)) state answer := by
  unfold strictReady at ready
  cases found : L.equationOf head with
  | none => rw [found] at ready; cases ready
  | some equation =>
    rw [found] at ready
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.not_eq_true', List.all_eq_true,
      List.mem_range] at ready
    obtain ⟨⟨⟨⟨⟨⟨⟨same, shape⟩, distinct⟩, single⟩, ordinary⟩, notIO⟩, notNative⟩, strict⟩ := ready
    have formals : L.formals head = Library.formalNames equation := by simp [Library.formals, found]
    have bodyEq : L.body head = equation.body := by simp [Library.body, found]
    rw [formals] at length returned
    rw [bodyEq] at returned
    have member : equation ∈ L.source.equations := List.mem_of_find?_eq_some found
    have owned : L.owns head = true := by
      have sources : (L.source.equations.all fun equation => L.owns equation.head) = true := by
        simp only [Library.check, Bool.and_eq_true] at checked
        exact checked.1.2
      have row := List.all_eq_true.mp sources equation member
      rwa [same] at row
    have rows : L.runtime.equations.filter (·.head == head) = [equation] := by
      rw [Library.owned_equations checked owned]
      obtain ⟨only, onlyRows⟩ := List.length_eq_one_iff.mp single
      have present : equation ∈ L.source.equations.filter (·.head == head) :=
        List.mem_filter.mpr ⟨member, by simp [same]⟩
      rw [onlyRows] at present ⊢
      rw [List.mem_singleton.mp present]
    have selected := PureData.named_equation_clause L.runtime head equation (Library.formalNames equation) values
      rows shape distinct length
    have argumentsLength : arguments.length = values.length := returns.length_eq
    apply call_returns L.runtime caller state state head arguments answer
    · have present : equation ∈ L.runtime.equations.filter (·.head == head) := by rw [rows]; simp
      simp only [Bool.or_eq_true, List.any_eq_true, beq_iff_eq]
      exact .inr ⟨equation, (List.mem_filter.mp present).1, by simpa using (List.mem_filter.mp present).2⟩
    · apply evaluated_arguments L.runtime caller state (.function head) arguments values [] 0 [answer] returns
      · intro offset bounded
        have raw := strict offset (by omega)
        simpa [demands] using raw
      · simp only [List.nil_append, Nat.zero_add]
        exact authored_function_arguments_return L.runtime caller (Library.bind (Library.formalNames equation) values)
          state state head values arguments.length equation.body answer notIO notNative selected returned
    · intro special
      have contains : specialForms.contains head = true := by simpa [specialForms] using special
      rw [contains] at ordinary
      cases ordinary

#print axioms evaluated_arguments
#print axioms constructor_returns
#print axioms strict_call

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.StrictCallKit
