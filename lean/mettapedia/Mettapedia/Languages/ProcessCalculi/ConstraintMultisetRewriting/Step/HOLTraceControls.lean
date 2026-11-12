import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLTraceModel
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.InterchangeTraceControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperTensorInterchangeControls

/-!
# Loaded traces on higher-order native runs and separating controls

The higher-order runs introduce helpers at changing declaration frames.
They have different raw schedules and one loaded trace. Preparation, complete
words and the trace use the same received source model. Other controls keep
transport similarity separate from canonical interchange and reject an
invalid sentinel or an empty generating relation as substitutes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLTraceControls

open Mettapedia.Languages.OpenTheory.TypeFamilySemantics

variable (input : HOLTraceModel.Input)

namespace HigherOrder

open Helpers
open Helpers.TensorInterchangeControls (sequential combined)

variable (other : OperatorFamilies.{1}) (prior : Assignment.{1})

abbrev program := (helperStep (S := Consumer.tiny) (O := Nat)).toStep

theorem loaded_interchange :
    input.relates program ContextResultControls.placed.state other prior helperTransport sequential combined :=
  (input.native_trace_iff program ContextResultControls.placed.state other prior helperTransport _ _).mpr
    TensorInterchangeControls.native_interchange

theorem histories_remain_distinct :
    input.relates program ContextResultControls.placed.state other prior helperTransport sequential combined ∧
      sequential ≠ combined :=
  ⟨loaded_interchange input other prior, TensorInterchangeControls.raw_histories_distinct⟩

theorem invalid_run_refused :
    ¬(input.operations.signature.traceValue (input.model program ContextResultControls.placed.state other prior)
      (HOLNativeTrace.generatorValue helperTransport input.operations.signature
        (input.model program ContextResultControls.placed.state other prior)
        (input.coding program ContextResultControls.placed.state other prior))
      ((input.coding program ContextResultControls.placed.state other prior).symm none)
      ((input.coding program ContextResultControls.placed.state other prior).symm (some sequential))).down :=
  input.invalid_separated program ContextResultControls.placed.state other prior helperTransport sequential

theorem generators_cannot_be_dropped :
    ¬(input.operations.signature.traceValue (input.model program ContextResultControls.placed.state other prior)
      (fun _ _ => .up False)
      ((input.coding program ContextResultControls.placed.state other prior).symm (some sequential))
      ((input.coding program ContextResultControls.placed.state other prior).symm (some combined))).down := by
  intro related
  have raw := (input.operations.signature.trace_iff_eqvGen _
    (input.fullDomains program ContextResultControls.placed.state other prior)
    (input.meanings program ContextResultControls.placed.state other prior)
    (input.meaning program ContextResultControls.placed.state other prior) _ _ _).mp related
  have same := (HOLTraceSemantics.eqvGen_false_iff _ _).mp raw
  have runs := Option.some.inj
    ((input.coding program ContextResultControls.placed.state other prior).symm.injective same)
  exact TensorInterchangeControls.raw_histories_distinct runs

theorem complete_word_in_same_model :
    let effect := program.effectCore
    let assigned := HOLTraceModel.Input.tracePrior program ContextResultControls.placed.state prior
    let code := input.words.coding effect other assigned
    let agreement := input.words.agreement effect other assigned
    (input.words.operations.signature.domainValue
      (input.model program ContextResultControls.placed.state other prior)
      (HOLPreparedWordSpecialization.preparationValue effect _ _ code)
      (HOLPreparedWordSpecialization.resultValue effect _ _ code)
      (HOLPreparedWordSpecialization.permissionValue effect _ _ code program.eventAdmission)
      (HOLPreparedWordSpecialization.wordValue effect _ _ code agreement
        (HOLPreparedRunEncoding.word effect program.eventAdmission (sequential.eventPath program)))
      (code.states.symm (some ContextResultControls.placed.state))).down := by
  dsimp only
  exact (input.words.domain_iff_native_path program.effectCore other
    (HOLTraceModel.Input.tracePrior program ContextResultControls.placed.state prior)
    program.eventAdmission _ _).mpr ⟨sequential.last, sequential.eventPath program, rfl⟩

end HigherOrder

variable (other : OperatorFamilies.{0}) (prior : Assignment.{0})

theorem similarity_is_required :
    input.relates InterchangeTraceControls.P EventTraceControls.start other prior InterchangeTraceControls.T
      (EventTraceControls.run true) (EventTraceControls.run false) ∧
    ¬InterchangeTraceControls.T.InterchangeClosure EventTraceControls.start
      (EventTraceControls.run true) (EventTraceControls.run false) :=
  ⟨(input.native_trace_iff InterchangeTraceControls.P EventTraceControls.start other prior
    InterchangeTraceControls.T _ _).mpr InterchangeTraceControls.old_trace_has_extra_identifications.1,
    InterchangeTraceControls.old_trace_has_extra_identifications.2⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLTraceControls
