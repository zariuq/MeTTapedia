import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationCodes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.TemplateInference

/-!
# Positive template checks construct source certificates

This adapter extracts the actual finite template computed by the existing
neutral-term checker. Its computational fields come from the check's fill
and synthesis results; no choice from a semantic existence theorem is used.
The negative and declined checker outcomes retain their existing meanings.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Inference

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta DependentFull
open NativeTypesOnTheStep
open NativeTypesOnTheStep.TemplateInference
open DependentFull.Controls (setting)

def templateFromCheck {target source : Context Tower.rules} (answer : target ⟶ source) (row : Make source)
    (accepted : templated? answer row = some true) :
    {template : Template row // template.Holds answer} := by
  unfold templated? at accepted
  split at accepted
  · cases accepted
  · rename_i fill foundFill
    split at accepted
    · rename_i filled
      split at accepted
      · rename_i synthesized foundType
        have principal := Synth.principal (S := setting) TowerModel.facts TowerModel.algebra
          ContextualDependentNormalCheckingTower.head_typing_unique synthesized.property target.formed
        have below := (usable?_sound target.formed (Typed.isType (S := setting) principal.1 target.formed)
          (row.type.reindex answer).isType accepted).mp rfl
        have typed : Typed Tower.rules target.raw (subst answer.substitution row.code)
            (row.type.reindex answer).code := Derivable.sub principal.1 below
        exact ⟨inferredTemplate answer row fill.val typed filled, inferred_holds answer row fill typed filled⟩
      · cases accepted
    · cases accepted

/-- A computed positive check yields source code with the original raw row
and a proved license at the checked answer. -/
def codeFromCheck {target source : Context Tower.rules} (answer : target ⟶ source) (row : Make source)
    (accepted : templated? answer row = some true) :
    {code : Code source // code.raw = row ∧ code.At answer} := by
  let inferred := templateFromCheck answer row accepted
  refine ⟨Code.template source row inferred.val (𝟙 source),
    NativeTypesOnTheStep.Make.reindex_id' row, ?_⟩
  change inferred.val.Holds (answer ≫ 𝟙 source)
  exact Eq.mpr (congrArg (fun substitution : target ⟶ source => inferred.val.Holds substitution)
    (Category.comp_id answer)) inferred.property

theorem source_uniform_of_computed_check {target source : Context Tower.rules}
    (answer : target ⟶ source) (row : Make source) {information : EquationStore (TotalTerm source)}
    (principal : (frames setting.levels).Principal information answer)
    (accepted : templated? answer row = some true) :
    (codeFromCheck answer row accepted).val.Uniform setting.levels information :=
  ((codeFromCheck answer row accepted).val.uniform_iff_at_principal setting.levels principal).mpr
    (codeFromCheck answer row accepted).property.2

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Inference

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Inference.codeFromCheck
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.Inference.source_uniform_of_computed_check
