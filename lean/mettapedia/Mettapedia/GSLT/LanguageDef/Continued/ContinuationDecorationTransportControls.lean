import Mettapedia.GSLT.LanguageDef.Continued.ContinuationDecorationTransport
import Mettapedia.GSLT.LanguageDef.LambdaContinuedInteraction
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.SynchronousDecoration

/-!
# Finite continuation transport controls

The actual lambda application keeps its argument decorated and its function
position undecorated under every continued morphism. Synchronous rho's extra
sent-process slot retains its distinct parameter and schema variable under
the more general operand transport, without requiring a synchronous CIGSLT
instance that has not yet been constructed.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ContinuationDecorationTransportControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open StructuralMorphism LambdaContinuedInteraction
open Mettapedia.OSLF.Framework.LambdaInstance

def lambdaProfile : ContinuationDecorationProfile lambdaCIGSLT.cut :=
  .ofRetypingPlan lambdaCIGSLT.continuationRetyping

/-- Transport neither loses the argument continuation nor invents one in the
application's function position. The conclusion covers arbitrary targets. -/
theorem lambda_application_positions {target : CIGSLT}
    (morphism : lambdaCIGSLT.Morphism target) :
    (lambdaProfile.map morphism).selectedParameter
        (mapGrammarRule morphism.underlying.structural.structural.symbols lambdaCalc.terms[0]) 1 = true ∧
      (lambdaProfile.map morphism).selectedParameter
        (mapGrammarRule morphism.underlying.structural.structural.symbols lambdaCalc.terms[0]) 0 = false := by
  rw [ContinuationDecorationProfile.map_selectedParameter,
    ContinuationDecorationProfile.map_selectedParameter]
  decide +kernel

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Synchronous

/-- The general reindexing operation applies to the actual three-payload
synchronous profile without requiring the stronger two-slot CIGSLT record. -/
theorem synchronous_reindex_identity :
    communicationDecoration.mapAlong (InteractiveMorphism.id rhoSyncIGSLT.presentation)
      (StructuralMorphism.mapConstructor_id _ _) (StructuralMorphism.mapConstructor_id _ _)
      (mapPattern_id _) (mapPattern_id _) = communicationDecoration :=
  communicationDecoration.mapAlong_id

/-- The sent process remains the additional middle parameter, separate from
the primary output continuation, through every declared operand transport. -/
theorem synchronous_extra_slot {target : InteractivePresentation}
    (operand : InteractionOperandProfile target) (symbols : LanguageDefSymbolMap)
    (constructorMap : mapGrammarRule symbols rhoSyncInteractionCut.environment.constructor.1 =
      operand.constructor.1)
    (sortMap : symbols.sort rhoSyncIGSLT.presentation.interactingSort.1.name =
      target.interactingSort.1.name)
    (schemaMap : mapPattern symbols rhoSyncInteractionCut.environment.schemaTerm = operand.schemaTerm) :
    let mapped := sentProcessSlot.map symbols constructorMap sortMap schemaMap
    mapped.position.index = 1 ∧ mapped.schemaVariable.name = "q" ∧
      mapped.pattern = .fvar "q" := by
  exact ⟨rfl, rfl, rfl⟩

end Mettapedia.GSLT.LanguageDef.ContinuationDecorationTransportControls
