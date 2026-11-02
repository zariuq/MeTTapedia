import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedFunctionSteps

/-! Every successful independent closure application has a prepared dispatch
step. Lambda and recursive-group declarations are recovered from the source
application, including the selected recursive slot.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

theorem prepared_application_can_step (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (function argument : OCaml.Value) (rest : OCaml.Continuation) (encodedRest : Pattern) (next : OCaml.MachineState)
    (built : prepare program = .ok prepared) (signatures : table.signatures = provider.signatures)
    (resolved : continuation? (patterns program) rest = some encodedRest)
    (applied : OCaml.applyClosure program function argument rest = .ok next) :
    ∃ target, (GeneralOccurrenceSemantics.gslt (epochPlan prepared table) [] (.base "MlConfig")).Step
      (node "MlApply" [value function, value argument, encodedRest]) target := by
  cases function with
  | closure function captured =>
    cases function with
    | lambda reference =>
      cases declared : program.instruction? reference with
      | none => simp [OCaml.applyClosure, declared] at applied
      | some instruction =>
        cases instruction with
        | lambda parameter body =>
          obtain ⟨index, _, _, step⟩ := prepared_lambda_dispatch_step program prepared table reference body parameter captured
            argument rest encodedRest built signatures declared resolved
          exact ⟨_, step⟩
        | _ => simp [OCaml.applyClosure, declared] at applied
    | recursive group slot =>
      cases declaredGroup : program.instruction? group with
      | none => simp [OCaml.applyClosure, declaredGroup] at applied
      | some instruction =>
        cases instruction with
        | letRecursive definitions groupBody =>
          cases declaredSlot : definitions[slot]? with
          | none => simp [OCaml.applyClosure, declaredGroup, declaredSlot] at applied
          | some reference =>
            cases declaredFunction : program.instruction? reference with
            | none => simp [OCaml.applyClosure, declaredGroup, declaredSlot, declaredFunction] at applied
            | some functionInstruction =>
              cases functionInstruction with
              | lambda parameter body =>
                obtain ⟨index, _, _, step⟩ := prepared_recursive_dispatch_step program prepared table group groupBody slot reference body
                  definitions parameter captured argument rest encodedRest built signatures declaredGroup declaredSlot declaredFunction resolved
                exact ⟨_, step⟩
              | _ => simp [OCaml.applyClosure, declaredGroup, declaredSlot, declaredFunction] at applied
        | _ => simp [OCaml.applyClosure, declaredGroup] at applied
  | _ => simp [OCaml.applyClosure] at applied

#print axioms prepared_application_can_step

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
