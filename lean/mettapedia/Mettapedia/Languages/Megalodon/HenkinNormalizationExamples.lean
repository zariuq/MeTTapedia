import Mettapedia.Languages.Megalodon.HenkinNormalizationSemantics
import Mettapedia.Languages.Megalodon.NativeDefinitionModel

/-!
# Native normalization: beta/eta execution and the definition-model boundary

The first specimen performs beta reduction underneath an eta redex in one
bottom-up native pass. The second executes the full native delta/beta/eta
pipeline in a mixed plain/prefix environment. Satisfying declaration equations
preserves meaning; changing only the defined proposition's interpretation
retains the native checks and execution but changes the resulting meaning.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.HenkinNormalizationExamples

open MathdataKernel
open Mettapedia.Logic.HOL
open HenkinTermInterpretation

universe w

/-- In a context containing `f`, the term is `fun x => f ((fun y => y) x)`. -/
def betaEtaSource : Term (Constant {}) [.prop ⇒ .prop] (.prop ⇒ .prop) :=
  .lam (.app (.var (.vs .vz)) (.app (.lam (.var .vz)) (.var .vz)))

def betaEtaRaw : Tm :=
  .lam .prop (.app (.db 1) (.app (.lam .prop (.db 0)) (.db 0)))

theorem betaEtaSource_erased : erase betaEtaSource = some betaEtaRaw := rfl

theorem beta_eta_normalizes : Tm.normalize 1 betaEtaRaw = some (.db 0) := rfl

/-- A genuine contraction is not stable yet at zero fuel. -/
theorem zero_fuel_rejects_beta_eta : Tm.normalize 0 betaEtaRaw = none := rfl

theorem beta_eta_preserves_every_model
    (M : HenkinModel.{0, 0, w} Base (Constant {}))
    (valuation : M.Valuation [.prop ⇒ .prop]) :
    M.denote (.var .vz) valuation = M.denote betaEtaSource valuation :=
  denote_betaEtaNormalize M betaEtaSource (.var .vz) betaEtaSource_erased rfl
    beta_eta_normalizes valuation

open HenkinTermInterpretation.DeltaTypingExamples

def pipelineResult : Tm := .lam (.var 0) (.named "p")

def pipelineResultTerm : ClosedTerm NativeDefinitionModel.NativeConstant (.base (.inl 0) ⇒ .prop) :=
  .lam (.const NativeDefinitionModel.parameterConstant)

theorem pipelineResultTerm_erased : erase pipelineResultTerm = some pipelineResult := rfl

/-- Delta unfolds `q := id p` and `id`; beta then removes the identity redex
underneath the outer binder. The unrelated prefix declaration stays present. -/
theorem native_pipeline_normalizes :
    MathdataKernel.normalize environment 2 source = some pipelineResult := by
  change (deltaNormalize environment 2 source).bind (Tm.normalize 2) = _
  rw [two_definition_depth]
  rfl

theorem native_pipeline_infers :
    inferTerm environment 1 [] source = some (.arr (.var 0) .prop) ∧
      inferTerm environment 1 [] pipelineResult = some (.arr (.var 0) .prop) :=
  ⟨source_inferred, by decide⟩

theorem native_pipeline_preserves_meaning (parameter : Prop) :
    (NativeDefinitionModel.model parameter parameter).denote pipelineResultTerm
        (fun v => nomatch v) =
      (NativeDefinitionModel.model parameter parameter).denote NativeDefinitionModel.sourceTerm
        (fun v => nomatch v) :=
  denote_nativeNormalize checkedDefinitions (NativeDefinitionModel.model parameter parameter)
    (NativeDefinitionModel.definitionEquations parameter)
    NativeDefinitionModel.sourceTerm pipelineResultTerm NativeDefinitionModel.erase_sourceTerm
    pipelineResultTerm_erased native_pipeline_normalizes (fun v => nomatch v)

/-- The same successful native run changes meaning when the independent
definition equation is violated. Native typing does not discharge that premise. -/
theorem altered_model_changes_pipeline_meaning :
    (NativeDefinitionModel.model True False).denote pipelineResultTerm (fun v => nomatch v) ≠
      (NativeDefinitionModel.model True False).denote NativeDefinitionModel.sourceTerm
        (fun v => nomatch v) := by
  intro equal
  have true_eq_false : True = False :=
    congrArg (fun function => (function (ULift.up ())).down) equal
  exact true_eq_false.mp trivial

theorem native_success_does_not_supply_definition_equations :
    MathdataKernel.normalize environment 2 source = some pipelineResult ∧
      CheckedPlainDefinitions environment ∧
      ¬ DefinitionEquations checkedDefinitions (NativeDefinitionModel.model True False) :=
  ⟨native_pipeline_normalizes, checkedDefinitions,
    NativeDefinitionModel.altered_meaning_refutes_equations⟩

#print axioms beta_eta_preserves_every_model
#print axioms native_pipeline_normalizes
#print axioms native_pipeline_preserves_meaning
#print axioms altered_model_changes_pipeline_meaning
#print axioms native_success_does_not_supply_definition_equations

end Mettapedia.Languages.Megalodon.HenkinNormalizationExamples
