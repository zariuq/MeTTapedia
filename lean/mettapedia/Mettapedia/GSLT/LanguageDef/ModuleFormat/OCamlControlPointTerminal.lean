import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlControlPointReadout
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlValueReading

/-! A terminal target at a source control point has zero administrative rank
and reads back to precisely the same independent source result. Pending
requests cannot be mistaken for completed values or faults.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem fault_injective : Function.Injective fault := by
  intro first second same
  cases first <;> cases second <;> simp_all [fault, node]

theorem halted_encoding_injective (pool : List OCaml.MatchPattern) (first second : OCaml.Result)
    (same : state? pool (.halted first) = state? pool (.halted second)) : first = second := by
  cases first with
  | ok first =>
    cases second with
    | ok second =>
      have encoded : value first = value second := by
        simpa only [state?, Option.pure_def, Option.some.injEq, node, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] using same
      exact congrArg Except.ok (value_injective encoded)
    | error second => simp [state?, node] at same
  | error first =>
    cases second with
    | ok second => simp [state?, node] at same
    | error second =>
      have encoded : fault first = fault second := by
        simpa only [state?, Option.pure_def, Option.some.injEq, node, Pattern.apply.injEq, List.cons.injEq, and_true, true_and] using same
      exact congrArg Except.error (fault_injective encoded)

theorem state_terminal_readback (pool : List OCaml.MatchPattern) (source : OCaml.MachineState)
    (result : OCaml.Result) (config : Pattern)
    (encoded : state? pool source = some config) (terminal : state? pool (.halted result) = some config) :
    source = .halted result := by
  have same := encoded.trans terminal.symm
  cases source with
  | halted actual => exact congrArg OCaml.MachineState.halted (halted_encoding_injective pool actual result same)
  | evaluate reference captured rest =>
    cases result <;> cases resolved : continuation? pool rest <;> simp [state?, resolved, node] at same
  | returned actual rest =>
    cases result <;> cases resolved : continuation? pool rest <;> simp [state?, resolved, node] at same

theorem control_point_terminal_readback (program : OCaml.Program) {source : OCaml.MachineState}
    {config : Pattern} {rank : Nat} (result : OCaml.Result)
    (point : ControlPoint program source config rank)
    (terminal : state? (patterns program) (.halted result) = some config) :
    rank = 0 ∧ source = .halted result := by
  cases point with
  | state encoded => exact ⟨rfl, state_terminal_readback _ _ _ _ encoded terminal⟩
  | _ => cases result <;> simp [state?, node] at terminal

#print axioms fault_injective
#print axioms halted_encoding_injective
#print axioms state_terminal_readback
#print axioms control_point_terminal_readback

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
