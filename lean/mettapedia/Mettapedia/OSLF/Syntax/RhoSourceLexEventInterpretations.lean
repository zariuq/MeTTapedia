import Mettapedia.OSLF.Syntax.CartesianModelLexEventInterpretations
import Mettapedia.OSLF.Syntax.PresheafEventGraphTransport
import Mettapedia.OSLF.Syntax.EventGraphSlice
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

/-!
# The source rho firing graph as a finite-limit interpretation

The actual source equations identify substitution arrows on which retained
firing occurrences still differ. We therefore interpret the equation-context
theory in presheaves on raw clone contexts, where both its program object and
the COMM/Drop event presheaf live. The resulting event-equipped model is an
object of the general operational interpretation category, and the relative
finite-limit equivalence restricts it back to authored contexts without
erasing firing witnesses.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoSourceLexEventInterpretations

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open Mettapedia.OSLF.CartesianContextModels
open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.RhoSourceEquationLexClassification
open Mettapedia.OSLF.Binding.PresheafEventGraphTransport.RhoExample
open Mettapedia.OSLF.Binding.EventGraphSlice

private instance : HasFiniteProducts SourceContexts :=
  hasFiniteProducts_of_has_binary_and_terminal

abbrev RawCloneContexts := ContextObject (termClone sig)
abbrev RawPresheaves := RawCloneContextsᵒᵖ ⥤ Type

/-- Interpret a source-equation presheaf on the raw clone substitutions
used by the actual firing events. -/
noncomputable def rawContextRestriction :
    (SourceContextsᵒᵖ ⥤ Type) ⥤ RawPresheaves :=
  (Functor.whiskeringLeft RawCloneContextsᵒᵖ SourceContextsᵒᵖ Type).obj
    (termCloneToSemanticContextFunctor sig ⋙
      quotientContextFunctor rhoSourceE).op

private instance rawContextRestriction_preservesFiniteLimits :
    PreservesFiniteLimits rawContextRestriction := by
  unfold rawContextRestriction
  infer_instance

/-- The left-exact source equation interpretation in a target that can still
index the individual COMM and Drop events. -/
noncomputable def rawSourceLexModel :
    LeftExactTargetInterpretations SourceContexts RawPresheaves :=
  (changeLeftExactTarget SourceContexts
    (SourceContextsᵒᵖ ⥤ Type) RawPresheaves
    rawContextRestriction).obj sourceYonedaExtension

/-- The program object of the raw-indexed classifier is definitionally the
carrier used by the transported authored event graph. -/
theorem rawSourceProgram_eq_generatedStates :
    rawSourceLexModel.1.obj
      ((authoredContext SourceContexts).obj program) = generatedStates := rfl

/-- A concrete object of the general event-equipped finite-limit
interpretation category: source rho equations, the actual COMM/Drop event
presheaf, and both endpoint maps. -/
noncomputable def sourceOperationalInterpretation :
    LeftExactEventInterpretations SourceContexts RawPresheaves program where
  left := generatedEventGraph.edge
  right := rawSourceLexModel
  hom := ((graphProductSliceEquivalence generatedStates).functor.obj
    generatedEventGraph).hom

/-- Restriction to the authored source-equation contexts preserves the
entire event object and its endpoint incidence as an object of the comma
category. -/
noncomputable def authoredSourceOperationalInterpretation :
    AuthoredEventInterpretations SourceContexts RawPresheaves program :=
  (presheafEventInterpretationEquivalence
    SourceContexts RawCloneContexts program).functor.obj
      sourceOperationalInterpretation

/-- Restriction does not quotient or discard an authored firing witness. -/
theorem authoredSource_event_object :
    authoredSourceOperationalInterpretation.left =
      rawCloneIndex ⋙
        Mettapedia.OSLF.Binding.RhoFreePresheafEvents.sourceEvents.edge := by
  exact generated_events_unchanged

/-- The general equivalence also preserves the event endpoint assignment,
not merely the resulting binary relation. -/
theorem authoredSource_endpointMap :
    authoredSourceOperationalInterpretation.hom =
      sourceOperationalInterpretation.hom := rfl

/-- The actual source event presheaf still cannot descend to the quotient
substitution category. The raw-context target in this construction is
therefore mathematically necessary for retaining individual firings. -/
theorem sourceOperational_events_do_not_descend :
    ¬ ∃ (events : SourceContextsᵒᵖ ⥤ Type),
      Nonempty (sourceOperationalInterpretation.left ≅
        (termCloneToSemanticContextFunctor sig ⋙
          quotientContextFunctor rhoSourceE).op ⋙ events) := by
  exact generated_events_do_not_descend

/-- The closed raw context used to inspect actual source rule firings. -/
def closedRawContext : RawCloneContextsᵒᵖ :=
  Opposite.op (ContextObject.ofList (termClone sig) [])

/-- A source Drop firing is present in the interpreted event object. This
is an actual witness, not just inhabitedness of an abstract graph type. -/
theorem authoredSource_has_drop_event :
    Nonempty (authoredSourceOperationalInterpretation.left.obj
      closedRawContext) := by
  obtain ⟨event, _, _⟩ :=
    Mettapedia.OSLF.Binding.RhoSourceEventComparison.source_drop_has_class_event
  exact ⟨event⟩

/-- The inverse comparison recovers this specific operational model up to
the coherent unit isomorphism, including its event map. -/
noncomputable def sourceOperational_roundtrip :
    sourceOperationalInterpretation ≅
      (presheafEventInterpretationEquivalence
        SourceContexts RawCloneContexts program).inverse.obj
          authoredSourceOperationalInterpretation :=
  (presheafEventInterpretationEquivalence
    SourceContexts RawCloneContexts program).unitIso.app
      sourceOperationalInterpretation

end Mettapedia.OSLF.Binding.RhoSourceLexEventInterpretations
