import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlControlPointReadout
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPreparedServiceControls

/-! A source value persists across request, answer and ordinary encoding.
A known source fault can still have pending administrative work; only the
zero-rank point supplies the ordinary source-state readout.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.ControlPointControls

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open ServiceControls

theorem value_across_three_phases :
    ControlPoint primitiveProgram (.returned (number 42) rest)
      (node "MlPrimitiveRequest" [primitive .add, valueList [number 40, number 2], encodedRest]) 2 ∧
    ControlPoint primitiveProgram (.returned (number 42) rest)
      (node "MlPrimitiveReturned" [primitiveResult (.ok (number 42)), encodedRest]) 1 ∧
    ControlPoint primitiveProgram (.returned (number 42) rest) (node "MlReturn" [value (number 42), encodedRest]) 0 :=
  ⟨.primitive (result := .ok (number 42)) rfl rfl,
    .answer (result := .ok (number 42)) (rest := rest) rfl, .state rfl⟩

theorem source_fault_still_has_pending_match :
    ControlPoint lambdaProgram (.halted (.error .matchFailure))
      (node "MlMatchOne" [patternId 0, value (number 42), code 1, environment [number 99], encodedRest]) 1 :=
  .matchOne (program := lambdaProgram) (index := 0) (parameter := .literal (.integer 0))
    (argument := number 42) (body := 1) (captured := [number 99]) (rest := rest) rfl rfl

theorem pending_match_is_not_terminal :
    node "MlMatchOne" [patternId 0, value (number 42), code 1, environment [number 99], encodedRest] ≠
      node "MlFault" [fault .matchFailure] := by decide +kernel

theorem primitive_request_cannot_skip_administration :
    ¬ ControlPoint primitiveProgram (.returned (number 42) rest)
      (node "MlPrimitiveRequest" [primitive .add, valueList [number 40, number 2], encodedRest]) 0 :=
  primitive_request_rank_not_zero

#print axioms value_across_three_phases
#print axioms source_fault_still_has_pending_match
#print axioms pending_match_is_not_terminal
#print axioms primitive_request_cannot_skip_administration

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.ControlPointControls
