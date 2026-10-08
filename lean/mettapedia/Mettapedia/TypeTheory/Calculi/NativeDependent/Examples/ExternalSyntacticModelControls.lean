import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalSyntacticQualification
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.ExternalRankedModelControls
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.ExternalContextualInterpretationControls

/-!
# Complete source-model realization controls

The ordered declarations have a function-valued parameter, an indexed second
component and a motive receiving the complete pair. The source model recovers
the closed generated function's complete typed class and evaluates an actual
exchange of two assumptions after normalization. The exchange is distinct
from identity; partial realization of earlier declarations also cannot replace
the complete local qualifier.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.SyntacticModelControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Contextual Contextual.SyntacticModel Contextual.SyntacticReification

noncomputable abbrev sourceModel := qualified Controls.headers
noncomputable abbrev sourceData := data Controls.headers

theorem function_parameter_realized :
    sourceData.evaluateContext (Controls.signature.typeParameters .fibre) =
      some (sourceData.typeParameters .fibre) := sourceModel.realization.typeHeader .fibre

theorem full_pair_header_realized :
    sourceData.evaluateContext (Controls.signature.typeParameters .pairMotive) =
      some (sourceData.typeParameters .pairMotive) := sourceModel.realization.typeHeader .pairMotive

theorem complete_branch_result_realized :
    sourceData.evaluateType (sourceData.termParameters .fullBranch)
      (Controls.signature.termResult .fullBranch) = some (sourceData.termType .fullBranch) :=
  sourceModel.realization.termResult .fullBranch

def closedFunctionType : TypeOver (empty Controls.signature) where
  code := .pi (Controls.sum 0) (Controls.motive 0)
  formed := conclude (.piFormation .nil (Controls.sum 0) (Controls.motive 0))
    ⟨⟨Controls.sumFormed Controls.emptyContext⟩,
      ⟨Controls.pairContextMotiveFormed Controls.emptyContext⟩, trivial⟩

def closedFunction : Term (empty Controls.signature) closedFunctionType :=
  ⟨Controls.fullMotiveFunction, ⟨Controls.fullMotiveFunctionTyped⟩⟩

theorem complete_generated_function_type_read :
    sourceData.evaluateType (Scope.nil Controls.signature).semantic closedFunctionType.code =
      some (QType.mk closedFunctionType) :=
  scope_type_read Controls.headers (Scope.nil Controls.signature) closedFunctionType

theorem complete_generated_function_class_read :
    sourceData.evaluateTerm (Scope.nil Controls.signature).semantic Controls.fullMotiveFunction =
      some (⟨QType.mk closedFunctionType, ⟨QTerm.mk closedFunction, rfl⟩⟩ :
        Value (QuotientCwf.cwf Controls.signature)
          ((quotientProjection Controls.signature).obj (empty Controls.signature))) :=
  scope_term_read Controls.headers (Scope.nil Controls.signature) closedFunction

noncomputable def assumptionScope : Scope Controls.signature 2 where
  raw := (Presentation.select Controls.duplicateContext
    InterpretationControls.assumptionContext.formed).selected
  formed := (Presentation.select Controls.duplicateContext
    InterpretationControls.assumptionContext.formed).formed
  telescope := Presentation.selectedTelescope InterpretationControls.assumptionContext

noncomputable def exchanged : assumptionScope.source ⟶ assumptionScope.source :=
  (Presentation.comparison InterpretationControls.assumptionContext).hom ≫
    InterpretationControls.exchange ≫
      (Presentation.comparison InterpretationControls.assumptionContext).inv

set_option backward.isDefEq.respectTransparency false in
theorem exchanged_retains_positions : exchanged.substitution = ModelControls.exchangeRaw := by
  change composeSubstitution
    (Presentation.comparison InterpretationControls.assumptionContext).inv.substitution
    (composeSubstitution InterpretationControls.exchange.substitution
      (Presentation.comparison InterpretationControls.assumptionContext).hom.substitution) = _
  rw [Presentation.comparison_hom_substitution, Presentation.comparison_inv_substitution,
    composeSubstitution_identity, identity_composeSubstitution]
  rfl

theorem actual_normalized_exchange_read :
    sourceData.evaluateSubstitution assumptionScope.semantic assumptionScope.semantic
      ModelControls.exchangeRaw = some ((quotientProjection Controls.signature).map exchanged) := by
  rw [← exchanged_retains_positions]
  exact scope_substitution_read Controls.headers assumptionScope assumptionScope exchanged

set_option backward.isDefEq.respectTransparency false in
theorem normalized_exchange_is_nonidentity :
    (quotientProjection Controls.signature).map exchanged ≠
      𝟙 ((quotientProjection Controls.signature).obj assumptionScope.source) := by
  intro same
  let comparison := (quotientProjection Controls.signature).mapIso
    (Presentation.comparison InterpretationControls.assumptionContext)
  have restored := congrArg (fun arrow => comparison.inv ≫ arrow ≫ comparison.hom) same
  change comparison.inv ≫
    ((quotientProjection Controls.signature).map
      ((Presentation.comparison InterpretationControls.assumptionContext).hom ≫
        InterpretationControls.exchange ≫
          (Presentation.comparison InterpretationControls.assumptionContext).inv)) ≫
    comparison.hom = _ at restored
  rw [Functor.map_comp, Functor.map_comp] at restored
  change comparison.inv ≫ (comparison.hom ≫
    (quotientProjection Controls.signature).map InterpretationControls.exchange ≫ comparison.inv) ≫
      comparison.hom = comparison.inv ≫ 𝟙 _ ≫ comparison.hom at restored
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id, Category.id_comp] at restored
  apply InterpretationControls.quotient_exchange_is_nonidentity
  exact restored.trans ((quotientProjection Controls.signature).map_id
    InterpretationControls.assumptionContext).symm

theorem earlier_realization_cannot_replace_complete_realization :
    ¬ SignatureRealization RankedModelControls.partialModel Controls.signature :=
  RankedModelControls.later_header_realization_fails

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.SyntacticModelControls
