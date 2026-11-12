import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationInference
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationTemplateControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.TemplateInferenceControls

/-!
# A computed template becomes an admitted source application

The actual neutral-term checker produces the certificate for f a. The
generated code, rather than the manually supplied reference template, is
used by a schema and realized as a transform step. A different requested
result type is refused while the matching information remains solvable.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.InferenceControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull DependentFull.Controls
open NativeTypesOnTheStep.TemplateControls
open NativeTypesOnTheStep.TemplateInference (templated?)

theorem inferred_positive : templated? gapAnswer gapRow = some true := by decide +kernel

def generated : {code : Code gapFrame // code.raw = gapRow ∧ code.At gapAnswer} :=
  Inference.codeFromCheck gapAnswer gapRow inferred_positive

def schema : Schema setting.levels Nat emptyState.frame :=
  { TemplateControls.schema with outputs := [generated.val] }

def pick : Pick schema := ⟨⟨[], [], [1]⟩, rfl⟩

def application : Application setting.levels Nat emptyState :=
  ⟨schema, pick, gapTarget, gapAnswer, .principal gapAnswer_principal⟩

theorem source_admitted : schema.Admits (state := emptyState) pick := by
  apply application.basis.native_checks_iff.mp
  have existing := gap_templated
  refine ⟨⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl⟩,
    existing.2.1, existing.2.2.1, existing.2.2.2, ?_⟩
  intro output member
  obtain rfl := List.mem_singleton.mp member
  exact generated.property.2

theorem native_admitted : (realizationStep setting.levels Nat).Admits application :=
  (realization_admits_iff application).mpr source_admitted

theorem compiled_row_is_original : (schema.compile (state := emptyState) pick).makes = gapFiring.makes := by
  change [(1, generated.val.raw)] = [(1, gapRow)]
  exact congrArg (fun row => [(1, row)]) generated.property.1

theorem computed_source_has_exact_result :
    (realizationStep setting.levels Nat).result application native_admitted =
      application.sourceResult source_admitted := realization_result application source_admitted

theorem different_result_type_refused :
    templated? gapAnswer NativeTypesOnTheStep.TemplateInference.Controls.groundRow = some false := by
  decide +kernel

theorem refusal_is_not_constraint_refutation :
    templated? gapAnswer NativeTypesOnTheStep.TemplateInference.Controls.groundRow = some false ∧
      (frames setting.levels).Solvable gapFiring.information :=
  ⟨different_result_type_refused, ⟨gapTarget, gapAnswer, gapAnswer_solves⟩⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.InferenceControls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.InferenceControls.source_admitted
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.InferenceControls.refusal_is_not_constraint_refutation
