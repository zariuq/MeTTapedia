import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEmittedEntrySource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlFiniteEvaluationExecution
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.BridgeMixedCapture

/-! The three controller calls retain their actual bodies and argument
demands after loading an admitted emitted O0 module. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEmittedControllerCalls

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.OCamlCompilation
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit OCamlEmittedEntrySource

theorem begin_lift (state : State) {prepared : Prepared} {name : String} {emitted : SpaceSemantics.Program}
    (built : ExecutionData.emit? prepared name = .ok emitted) (first second third answer : Atom)
    (returned : PureReturns OCamlControllerSource.runtime [] state
      (apply "gslt:ml:begin" [first, second, third]) state answer) :
    PureReturns (moduleRuntime prepared name) [] state (apply "gslt:ml:begin" [first, second, third]) state answer := by
  apply Library.lift_call (checked built) (inherited_of_registered built (by decide +kernel))
    (by decide) (by change (ioHead "gslt:ml:begin" || StdLib.known "gslt:ml:begin" ||
      OCamlControllerSource.runtime.equations.any (·.head == "gslt:ml:begin")) = true; decide +kernel)
    (by decide) ["plan", "standard", "initial"] (by decide)
    (by rfl) _ returned
  intro index bounded
  change index < 3 at bounded
  change argumentIsRaw OCamlControllerSource.runtime "gslt:ml:begin" index = true
  interval_cases index <;> decide +kernel

theorem advance_lift (state : State) {prepared : Prepared} {name : String} {emitted : SpaceSemantics.Program}
    (built : ExecutionData.emit? prepared name = .ok emitted) (ticks quantum : Nat) (input answer : Term)
    (returned : PureReturns OCamlControllerSource.runtime [] state
      (apply "gslt:ml:advance" [number ticks, number quantum, encoded input]) state (encoded answer)) :
    PureReturns (moduleRuntime prepared name) [] state
      (apply "gslt:ml:advance" [number ticks, number quantum, encoded input]) state (encoded answer) := by
  apply captured_call_in_extension (Library.closed (checked built)) (Library.agreement (checked built))
    [] [("ticks", number ticks), ("quantum", number quantum), ("machine", encoded input)] state state "gslt:ml:advance"
    [number ticks, number quantum, encoded input] ["ticks", "quantum", "machine"] _
    (inherited_of_registered built (by decide +kernel)) (by decide)
    (by change (ioHead "gslt:ml:advance" || StdLib.known "gslt:ml:advance" ||
      OCamlControllerSource.runtime.equations.any (·.head == "gslt:ml:advance")) = true; decide +kernel) (by decide)
  · intro index argument found
    obtain ⟨bounded, _⟩ := List.getElem?_eq_some_iff.mp found
    simp only [List.length_cons, List.length_nil] at bounded
    interval_cases index
    all_goals
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at found
      subst argument
      first | exact Or.inr rfl | exact Or.inl (by
        change argumentIsRaw OCamlControllerSource.runtime "gslt:ml:advance" 2 = true
        decide +kernel)
  · simp [applySubst, Subst.lookup]
  · exact returned

theorem result_lift (state : State) {prepared : Prepared} {name : String} {emitted : SpaceSemantics.Program}
    (built : ExecutionData.emit? prepared name = .ok emitted) (input answer : Atom)
    (returned : PureReturns OCamlControllerSource.runtime [] state (apply "gslt:ml:result" [input]) state answer) :
    PureReturns (moduleRuntime prepared name) [] state (apply "gslt:ml:result" [input]) state answer := by
  apply Library.lift_call (checked built) (inherited_of_registered built (by decide +kernel))
    (by decide) (by change (ioHead "gslt:ml:result" || StdLib.known "gslt:ml:result" ||
      OCamlControllerSource.runtime.equations.any (·.head == "gslt:ml:result")) = true; decide +kernel)
    (by decide) ["machine"] (by decide) (by rfl) _ returned
  intro index bounded
  change index < 1 at bounded
  change argumentIsRaw OCamlControllerSource.runtime "gslt:ml:result" index = true
  interval_cases index
  decide +kernel

theorem capture_controller (state : State) {prepared : Prepared} {name : String} {emitted : SpaceSemantics.Program}
    (built : ExecutionData.emit? prepared name = .ok emitted) (head : String) (caller : Subst)
    (values arguments : List Atom) (answer : Atom)
    (registered : OCamlControllerSource.runtime.equations.any (·.head == head) = true)
    (ordinary : head ∉ specialForms)
    (valuesAdmitted : values.zipIdx.all (fun pair =>
      argumentIsRaw OCamlControllerSource.runtime head pair.2 || passiveArgument pair.1) = true)
    (argumentsAdmitted : arguments.zipIdx.all (fun pair => passiveArgument pair.1) = true)
    (captured : values.map (applySubst []) = arguments.map (applySubst caller))
    (returned : PureReturns (moduleRuntime prepared name) [] state (apply head values) state answer) :
    PureReturns (moduleRuntime prepared name) caller state (apply head arguments) state answer := by
  have inherited := inherited_of_registered built registered
  have agreement := Library.agreement (checked built)
  apply captured_call_returns _ [] caller state state head values arguments answer _ ordinary _ _ captured returned
  · change (ioHead head || StdLib.known head ||
      (ExecutionData.library prepared name).runtime.equations.any (·.head == head)) = true
    rw [← agreement.dispatch head inherited]
    change (ioHead head || StdLib.known head ||
      OCamlControllerSource.runtime.equations.any (·.head == head)) = true
    simp only [registered, Bool.or_true]
  · intro index argument found
    change argumentIsRaw (ExecutionData.library prepared name).runtime head index = true ∨ passiveArgument argument = true
    rw [← agreement.demand head index inherited]
    exact capture_arguments_of_check OCamlControllerSource.runtime head values valuesAdmitted index argument found
  · intro index argument found
    have member := List.mk_mem_zipIdx_iff_getElem?.mpr found
    exact Or.inr (List.all_eq_true.mp argumentsAdmitted (argument, index) member)

#print axioms begin_lift
#print axioms advance_lift
#print axioms result_lift
#print axioms capture_controller

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.OCamlEmittedControllerCalls
