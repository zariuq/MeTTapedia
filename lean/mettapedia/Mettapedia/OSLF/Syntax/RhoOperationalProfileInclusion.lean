import Mettapedia.OSLF.Syntax.RhoSourceLexEventInterpretations
import Mettapedia.OSLF.Syntax.RhoSourceEventComparison
import Mettapedia.OSLF.Syntax.FreePresheafEventGeneratorMaps
import Mettapedia.OSLF.Syntax.RhoRuleListPolynomialFunctor

/-!
# The rho COMM profile includes into the COMM-and-Drop interpretation

The two operational profiles share the complete source equation model. Their
map therefore fixes the interpreted states and includes individual COMM
firings. The event-equipped finite-limit classifier carries this map without
identifying it with an equality of endpoint predicates.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoOperationalProfileInclusion

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.RhoSourceEventComparison
open Mettapedia.OSLF.Binding.ContextualEquationClassEvents
open Mettapedia.OSLF.Binding.RhoFreePresheafEvents
open Mettapedia.OSLF.Binding.RhoSourceEquationLexClassification
open Mettapedia.OSLF.Binding.RhoSourceLexEventInterpretations
open Mettapedia.OSLF.Binding.FreePresheafEventExtension
open Mettapedia.OSLF.Binding.FreePresheafEventGeneratorMaps
open Mettapedia.OSLF.Binding.PresheafEventGraphTransport
open Mettapedia.OSLF.Binding.PresheafEventGraphTransport.RhoExample
open Mettapedia.OSLF.Binding.EventGraphSlice
open Mettapedia.OSLF.Binding.EventGraphNullaryPolynomial
open Mettapedia.OSLF.Binding.EventGraphNullaryPresentationFunctor
open Mettapedia.OSLF.Binding.RuleListEventEmbedding
open Mettapedia.OSLF.Binding.RhoRuleListPolynomialFunctor
open Mettapedia.OSLF.CartesianContextModels

/-- The COMM-only firing graph has the same source-equation state object as
the larger profile. -/
def commEvents : Graph states where
  edge := presentationEventPresheaf rhoSourceComm.toUnpositioned Srt.pr
  source := presentationSourceNatural rhoSourceComm.toUnpositioned Srt.pr
  target := presentationTargetNatural rhoSourceComm.toUnpositioned Srt.pr

/-- The rule-list inclusion acts on actual firing occurrences and fixes the
equation-class state object. -/
def commInclusion : Hom commEvents sourceEvents where
  edgeMap := eventEmbedding Srt.pr
  source_comm := by
    change eventEmbedding Srt.pr ≫
      presentationSourceNatural rhoSourceWithDrop.toUnpositioned Srt.pr =
      presentationSourceNatural rhoSourceComm.toUnpositioned Srt.pr
    exact eventEmbedding_source Srt.pr
  target_comm := by
    change eventEmbedding Srt.pr ≫
      presentationTargetNatural rhoSourceWithDrop.toUnpositioned Srt.pr =
      presentationTargetNatural rhoSourceComm.toUnpositioned Srt.pr
    exact eventEmbedding_target Srt.pr

/-- The event map used by the finite-limit interpretation is exactly the
map produced from the authored rule-list morphism for the nullary rule
polynomial. Both semantic routes therefore retain the same occurrence. -/
theorem commInclusion_is_authoredRuleMap :
    commInclusion =
      graphMap sourceCommRuleEmbedding rhoSourceE Srt.pr := by
  apply Hom.ext
  exact (sourceCommGraphMap_agrees Srt.pr).symm

/-- Interpreting an authored COMM occurrence through the freely generated
rule tree and reading its root returns precisely the event sent by the
categorical operational profile map, at the same equation-class endpoints. -/
theorem commTree_event_agrees
    {X : base} {pair : states.obj X × states.obj X}
    (event : EndpointFiber
      Mettapedia.OSLF.Binding.RhoEventPolynomialComparison.commEvents X pair) :
    treeEvent sourceEvents
        (commToDrop.rules.mapFix () ⟨X, pair⟩
          (eventTree _ event)) =
      mapEvent commInclusion event := by
  rw [commToDrop_event]
  change mapEvent
      (graphMap sourceCommRuleEmbedding rhoSourceE Srt.pr) event =
    mapEvent commInclusion event
  rw [commInclusion_is_authoredRuleMap]
  rfl

/-- The free graph-model comparison and the free nullary rule-algebra map
send the same authored COMM firing to the same retained target occurrence.
The tree route keeps its endpoint-indexed proof witness; the graph route
keeps its presheaf-natural edge. -/
theorem freeSourceComparison_matches_commTree
    {X : base} {pair : states.obj X × states.obj X}
    (event : EndpointFiber
      Mettapedia.OSLF.Binding.RhoEventPolynomialComparison.commEvents X pair) :
    ((freeComparison commInclusion).app (emptyGraph states)).graphMap.edgeMap.app X
        (Sum.inr event.1) =
      Sum.inr (treeEvent sourceEvents
        (commToDrop.rules.mapFix () ⟨X, pair⟩
          (eventTree _ event))).1 := by
  rw [commInclusion_is_authoredRuleMap]
  exact mapGenerator_matches_treeEvent (emptyGraph states)
    (graphMap sourceCommRuleEmbedding rhoSourceE Srt.pr) event

/-- Carry the COMM-only graph to the generated program object, retaining
the raw substitution contexts needed by individual firing events. -/
noncomputable def generatedCommEvents : Graph generatedStates :=
  changeVertex generatedProgramAsOperationalStatesIso
    (reindex rawCloneIndex commEvents)

noncomputable def generatedCommInclusion :
    Hom generatedCommEvents generatedEventGraph :=
  changeVertexHom generatedProgramAsOperationalStatesIso
    (reindexHom rawCloneIndex commInclusion)

/-- The COMM-only profile is an object of the same relative finite-limit
interpretation category as the combined COMM/Drop source profile. -/
noncomputable def commOperationalInterpretation :
    LeftExactEventInterpretations SourceContexts RawPresheaves program where
  left := generatedCommEvents.edge
  right := rawSourceLexModel
  hom := ((graphProductSliceEquivalence generatedStates).functor.obj
    generatedCommEvents).hom

/-- Profile inclusion is a morphism of interpreted models: the state
interpretation is fixed and the event component includes exactly the old
COMM occurrences. -/
noncomputable def operationalInclusion :
    commOperationalInterpretation ⟶ sourceOperationalInterpretation := by
  let graphMap := (graphProductSliceEquivalence generatedStates).functor.map
    generatedCommInclusion
  exact
    { left := graphMap.left
      right := 𝟙 rawSourceLexModel
      w := by
        change (𝟭 RawPresheaves).map graphMap.left ≫
            ((graphProductSliceEquivalence generatedStates).functor.obj
              generatedEventGraph).hom =
          ((graphProductSliceEquivalence generatedStates).functor.obj
              generatedCommEvents).hom ≫
            (restrictLeftExactTarget SourceContexts RawPresheaves ⋙
              authoredProgramPair SourceContexts RawPresheaves program).map
                (𝟙 rawSourceLexModel)
        rw [Functor.id_map]
        rw [(restrictLeftExactTarget SourceContexts RawPresheaves ⋙
          authoredProgramPair SourceContexts RawPresheaves program).map_id
            rawSourceLexModel]
        change graphMap.left ≫
            ((graphProductSliceEquivalence generatedStates).functor.obj
              generatedEventGraph).hom =
          ((graphProductSliceEquivalence generatedStates).functor.obj
              generatedCommEvents).hom ≫ 𝟙 (generatedStates ⨯ generatedStates)
        rw [Category.comp_id]
        exact graphMap.w }

/-- Restricting the classifier to authored contexts retains the profile
map as a morphism, including its individual event action. -/
noncomputable def authoredOperationalInclusion :
    (presheafEventInterpretationEquivalence SourceContexts RawCloneContexts
        program).functor.obj commOperationalInterpretation ⟶
      authoredSourceOperationalInterpretation :=
  (presheafEventInterpretationEquivalence SourceContexts RawCloneContexts
    program).functor.map operationalInclusion

/-- Restriction of the relative classifier uses the concrete rule-occurrence
embedding, not a quotient of its endpoint relation. -/
theorem authoredOperationalInclusion_eventMap :
    authoredOperationalInclusion.left = generatedCommInclusion.edgeMap := by
  rfl

/-- The inclusion is genuinely proper. Drop supplies an event in the larger
profile which no COMM event can map to, even though both profiles interpret
the same equation-class states. -/
theorem commInclusion_not_surjective_closed :
    ¬ Function.Surjective
      (commInclusion.edgeMap.app closedContext) := by
  intro surjective
  obtain ⟨dropEvent, before, after⟩ := source_drop_has_class_event
  obtain ⟨commEvent, imageEq⟩ := surjective dropEvent
  change PresentationInstance rhoSourceComm.toUnpositioned [] Srt.pr at commEvent
  change embedCommEvent commEvent = dropEvent at imageEq
  rw [← imageEq] at before after
  rw [embedCommEvent_source] at before
  rw [embedCommEvent_target] at after
  exact source_drop_has_no_comm_event ⟨commEvent, before, after⟩

/-- The same profile inclusion acts on freely generated histories over any
prior event graph on the interpreted program states. -/
noncomputable def freeGeneratedInclusion (prior : Graph generatedStates) :
    Hom (graphSum prior generatedCommEvents)
      (graphSum prior generatedEventGraph) :=
  mapGenerator prior generatedCommInclusion

/-- The authored COMM-to-COMM/Drop map induces one coherent comparison of
free event-model functors for every prior history, including the model maps
that interpret the authored generators. -/
noncomputable def freeGeneratedComparison :
    free generatedCommEvents ⟶
      free generatedEventGraph ⋙ restrictModels generatedCommInclusion :=
  freeComparison generatedCommInclusion

theorem freeGeneratedComparison_component (prior : Graph generatedStates) :
    (freeGeneratedComparison.app prior).graphMap =
      freeGeneratedInclusion prior := by
  rfl

/-- Previously recorded events are unchanged when Drop is added. -/
theorem freeGeneratedInclusion_old (prior : Graph generatedStates) :
    Hom.comp (graphInl prior generatedCommEvents)
      (freeGeneratedInclusion prior) =
        graphInl prior generatedEventGraph :=
  mapGenerator_old prior generatedCommInclusion

/-- Newly generated COMM events follow the exact authored profile map. -/
theorem freeGeneratedInclusion_new (prior : Graph generatedStates) :
    Hom.comp (graphInr prior generatedCommEvents)
      (freeGeneratedInclusion prior) =
        Hom.comp generatedCommInclusion
          (graphInr prior generatedEventGraph) :=
  mapGenerator_new prior generatedCommInclusion

/-- Even the free extension from no prior events cannot turn a COMM firing
into the additional closed Drop firing. -/
theorem freeSourceInclusion_not_surjective_closed :
    ¬ Function.Surjective
      ((mapGenerator (emptyGraph states) commInclusion).edgeMap.app
        closedContext) := by
  exact mapGenerator_empty_not_surjective_at commInclusion closedContext
    commInclusion_not_surjective_closed

end Mettapedia.OSLF.Binding.RhoOperationalProfileInclusion
