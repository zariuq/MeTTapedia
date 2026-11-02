import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedControlFlow

/-! A closed capture example separates argument order, captured values
and retained outer continuation. The GSLT path theorem uses the actual
prepared program; executable checks establish nonvacuous preparation and
independent source results.
-/

set_option autoImplicit false
set_option maxRecDepth 32768

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.ControlFlowControls

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax

def number (value : Int) : OCaml.Value := .literal (.integer value)

def captureProgram : OCaml.Program where
  code := #[.literal (.integer 42), .variable 1, .lambda .bind 1, .literal (.integer 7),
    .apply 2 3, .letValue .bind 0 4, .literal .nil, .cons 5 6]
  entry := 7

def rest : OCaml.Continuation := [.consHead (.literal .nil)]
def encodedRest : Pattern := node "MlKConsHead" [value (.literal .nil), node "MlKDone"]
def stepTarget (source : OCaml.MachineState) : Option OCaml.MachineState :=
  match OCaml.machineStep captureProgram source with
  | .ok target => target
  | .error _ => none

#guard captureProgram.checkScope
#guard (prepare captureProgram).toOption.isSome
#guard OCaml.run captureProgram 100 (OCaml.begin captureProgram) ==
  .complete (.ok (.cons (number 42) (.literal .nil)))
#guard !(OCaml.run captureProgram 100 (OCaml.begin captureProgram) ==
  .complete (.ok (.cons (number 7) (.literal .nil))))
#guard stepTarget (.returned (.closure (.lambda 2) [number 42]) (.function (number 7) :: rest)) ==
  some (.evaluate 1 [number 7, number 42] rest)
#guard !(stepTarget (.returned (.closure (.lambda 2) [number 42]) (.function (number 7) :: rest)) ==
  some (.evaluate 1 [number 42, number 7] rest))
#guard !(stepTarget (.returned (.closure (.lambda 2) [number 42]) (.function (number 7) :: rest)) ==
  some (.evaluate 1 [number 7, number 42] []))

theorem captured_call_has_actual_path (prepared : Prepared) (built : prepare captureProgram = .ok prepared) :
    Relation.ReflTransGen (GeneralOccurrenceSemantics.gslt (plan prepared) [] (.base "MlConfig")).Step
      (node "MlReturn" [value (.closure (.lambda 2) [number 42]), node "MlKFunction" [value (number 7), encodedRest]])
      (node "MlEvaluate" [code 1, environment [number 7, number 42], encodedRest]) := by
  have actual := prepared_lambda_return_success_path captureProgram prepared provider 2 1 .bind [number 42]
    (number 7) [number 7] rest encodedRest built rfl (by rfl) (by rfl) (by rfl)
  have initialPlan : epochPlan prepared provider = plan prepared := by rfl
  rw [initialPlan] at actual
  simpa only [OCaml.extend, List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append] using actual.2.2

theorem dropped_continuation_is_distinct :
    node "MlEvaluate" [code 1, environment [number 7, number 42], encodedRest] ≠
      node "MlEvaluate" [code 1, environment [number 7, number 42], node "MlKDone"] := by
  intro same
  have arguments := (Pattern.apply.inj same).2
  have finalArgument := (List.cons.inj (List.cons.inj (List.cons.inj arguments).2).2).1
  have impossible : ("MlKConsHead" : String) = "MlKDone" :=
    congrArg (fun term => match term with | .apply label _ => label | _ => "") finalArgument
  exact (by decide +kernel : ("MlKConsHead" : String) ≠ "MlKDone") impossible

#print axioms captured_call_has_actual_path
#print axioms dropped_continuation_is_distinct

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.ControlFlowControls
