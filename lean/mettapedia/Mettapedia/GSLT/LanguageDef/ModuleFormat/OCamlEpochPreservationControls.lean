import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlEpochResultPreservation
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlControlPointControls

/-! A source value remains pending across a real cache append and normalized
restart. Values and faults are distinct, terminal faults cannot react, and
a finite source result constrains every observed runner prefix.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.EpochPreservationControls

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Machines.ResumableSearchRunner
open ServiceControls

theorem addition_restart_preserves_pending_work (prepared : Prepared) (built : prepare primitiveProgram = .ok prepared) :
    let config := node "MlPrimitiveRequest" [primitive .add, valueList [number 40, number 2], encodedRest]
    let fresh := Machine.begin (Complete.Normalized.search (epochPlan prepared addition) [] (.base "MlConfig") .canonical)
      (Complete.Normalized.commit (epochPlan prepared addition) .canonical config)
    SourceEpochInvariant primitiveProgram prepared addition ∧
      Reached (Complete.Normalized.search (epochPlan prepared addition) [] (.base "MlConfig") .canonical) fresh ∧
      ControlPoint primitiveProgram (.returned (number 42) rest) fresh.state 2 := by
  have invariant := (initial_source_epoch_invariant primitiveProgram prepared).primitive built .add [number 40, number 2]
    (.ok (number 42)) rfl
  have restarted := control_point_epoch_restart primitiveProgram prepared addition built ControlPointControls.value_across_three_phases.1
  exact ⟨invariant, restarted⟩

theorem value_is_not_match_failure :
    state? [] (.halted (.ok (number 42))) ≠ state? [] (.halted (.error .matchFailure)) := by
  intro same
  have impossible := halted_encoding_injective [] (.ok (number 42)) (.error .matchFailure) same
  cases impossible

theorem terminal_fault_cannot_fire (program : OCaml.Program) (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (built : prepare program = .ok prepared) (target : Pattern) :
    ¬ Complete.Normalized.NormalizedStep (epochPlan prepared table) [] (.base "MlConfig") .canonical
      (node "MlFault" [fault .divisionByZero]) target :=
  prepared_terminal_no_normalized_step program prepared table (.error .divisionByZero) _ target built rfl

theorem addition_prefix_cannot_invent_result (prepared : Prepared) (table : GeneralPremise.ProviderSnapshot)
    (ticks quantum : Nat) (observed : OCaml.Result) (built : prepare primitiveProgram = .ok prepared)
    (invariant : SourceEpochInvariant primitiveProgram prepared table)
    (terminal : state? (patterns primitiveProgram) (.halted observed) = some
      (Machine.advance (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) ticks quantum
        (Machine.begin (Complete.Normalized.search (epochPlan prepared table) [] (.base "MlConfig") .canonical) (initial primitiveProgram))).state) :
    observed = .ok (number 42) := by
  apply runner_terminal_result_unique primitiveProgram prepared table ticks quantum _ built invariant.source
    (begin_reached _) (initial_control_point primitiveProgram) (budget := 100) (by rfl) terminal

#print axioms addition_restart_preserves_pending_work
#print axioms value_is_not_match_failure
#print axioms terminal_fault_cannot_fire
#print axioms addition_prefix_cannot_invent_result

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation.EpochPreservationControls
