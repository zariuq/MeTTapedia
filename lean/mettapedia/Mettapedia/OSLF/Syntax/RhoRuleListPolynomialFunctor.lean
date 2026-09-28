import Mettapedia.OSLF.Syntax.EventGraphNullaryPresentationFunctor
import Mettapedia.OSLF.Syntax.RhoEventPolynomialComparison

/-!
# The authored rho rule inclusion acts on retained firing trees

The Chapter 7 COMM-only rule catalogue embeds into the COMM-plus-Drop
catalogue. The general event-graph functor maps that inclusion to a cartesian
map of nullary rule presentations. Its action on a communication firing tree
retains the original event occurrence and both equation-class endpoints. The
Drop endpoint has a tree only in the larger profile.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoRuleListPolynomialFunctor

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.RhoFreePresheafEvents
open Mettapedia.OSLF.Binding.RhoEventPolynomialComparison
open Mettapedia.OSLF.Binding.RhoSourceEventComparison
open Mettapedia.OSLF.Binding.RuleListEventEmbedding
open Mettapedia.OSLF.Binding.ContextualEquationClassEvents
open Mettapedia.OSLF.Binding.EventGraphNullaryPolynomial
open Mettapedia.OSLF.Binding.EventGraphNullaryPresentationFunctor

/-- The two concrete authored rule catalogues share their binding signature
and source equation list. -/
def commCatalogue : Catalogue sig metas :=
  ⟨rhoSourceComm.toUnpositioned.rules⟩

def commDropCatalogue : Catalogue sig metas :=
  ⟨rhoSourceWithDrop.toUnpositioned.rules⟩

/-- The source COMM inclusion is a morphism of the authored catalogues. -/
def authoredInclusion : commCatalogue ⟶ commDropCatalogue :=
  sourceCommRuleEmbedding

/-- The concrete rho profile extension is the image of its authored
rule-occurrence inclusion under the general event-to-polynomial functor. -/
def commToDrop :
    presentation commEvents ⟶ presentation sourceEvents :=
  presentationMap
    (graphMap sourceCommRuleEmbedding rhoSourceE Srt.pr)

/-- The concrete map is exactly the functorial interpretation of the authored
catalogue morphism. -/
theorem commToDrop_is_authoredRuleFunctor :
    commToDrop =
      (authoredRuleFunctor rhoSourceE Srt.pr).map authoredInclusion := by
  rfl

/-- The same authored inclusion acts on the freely generated operational
model by the tree interpretation of the concrete presentation map. -/
theorem commToDrop_is_freeOperationalMap :
    (authoredFreeOperationalFunctor rhoSourceE Srt.pr).map
        authoredInclusion =
      Mettapedia.OSLF.Binding.IndexedOperationalPresentationCategory.freeMap
        commToDrop := by
  rfl

/-- Each retained communication tree maps to the tree of the same embedded
authored occurrence, at exactly the same equation-class endpoint pair. -/
theorem commToDrop_event
    {X : base} {pair : states.obj X × states.obj X}
    (event : EndpointFiber commEvents X pair) :
    commToDrop.rules.mapFix () ⟨X, pair⟩
        (eventTree commEvents event) =
      eventTree sourceEvents
        (mapEvent (graphMap sourceCommRuleEmbedding rhoSourceE Srt.pr) event) :=
  presentationMap_event
    (graphMap sourceCommRuleEmbedding rhoSourceE Srt.pr) event

/-- This transport sends each source COMM occurrence to its literal
rule-index embedding; it does not reconstruct an arbitrary event having
the same endpoints. -/
theorem commToDrop_retains_occurrence
    {X : base} {pair : states.obj X × states.obj X}
    (event : EndpointFiber commEvents X pair) :
    (mapEvent (graphMap sourceCommRuleEmbedding rhoSourceE Srt.pr) event).1 =
      embedEvent sourceCommRuleEmbedding event.1 := by
  rfl

/-- The actual authored rule inclusion preserves distinct closed or open
COMM firing histories, including distinct structural firing locations. -/
theorem commToDrop_tree_injective
    {X : base} {pair : states.obj X × states.obj X} :
    Function.Injective (commToDrop.rules.mapFix () ⟨X, pair⟩) :=
  presentationMap_tree_injective
    (graphMap sourceCommRuleEmbedding rhoSourceE Srt.pr)
    (eventNatural_injective sourceCommRuleEmbedding rhoSourceE Srt.pr)

/-- The rho profile extension also respects every substitution of its
intrinsic context, including those represented below binders. -/
theorem commToDrop_reindexTree
    {X Y : base} (sigma : X ⟶ Y)
    {pair : states.obj X × states.obj X}
    (tree : (rules commEvents).Fix () ⟨X, pair⟩) :
    commToDrop.rules.mapFix ()
        ⟨Y, reindexPair sigma pair⟩
        (reindexTree commEvents sigma tree) =
      reindexTree sourceEvents sigma
        (commToDrop.rules.mapFix () ⟨X, pair⟩ tree) :=
  presentationMap_reindexTree
    (graphMap sourceCommRuleEmbedding rhoSourceE Srt.pr) sigma tree

/-- The source-order communication gives a concrete constructor in the
COMM-only catalogue, and its transport gives one in the combined catalogue. -/
theorem source_comm_tree_exists :
    ∃ pair : states.obj closedContext × states.obj closedContext,
      Nonempty ((rules commEvents).Fix () ⟨closedContext, pair⟩) ∧
      Nonempty ((rules sourceEvents).Fix () ⟨closedContext, pair⟩) := by
  let source := parT commInput commOutput
  let pair : states.obj closedContext × states.obj closedContext :=
    (Quotient.mk _ source, Quotient.mk _ commTarget)
  have step : rhoSourceComm.toUnpositioned.StepModE source commTarget :=
    (rhoSourceComm.stepModE_iff_toUnpositioned).mp
      (rho_step_in_sourceComm input_output_communicates)
  obtain ⟨event, before, after⟩ :=
    (authored_class_endpoints_iff_stepModE
      rhoSourceComm.toUnpositioned Srt.pr source commTarget).mpr step
  let fibre : EndpointFiber commEvents closedContext pair :=
    ⟨event, before, after⟩
  exact ⟨pair, ⟨eventTree commEvents fibre⟩,
    ⟨commToDrop.rules.mapFix () ⟨closedContext, pair⟩
      (eventTree commEvents fibre)⟩⟩

/-- Drop cannot be the transported image of a COMM tree at its endpoints,
because the source catalogue has no event there. -/
theorem drop_tree_not_from_comm :
    ¬ ∃ tree : (rules commEvents).Fix () ⟨closedContext, dropPair⟩,
      commToDrop.rules.mapFix () ⟨closedContext, dropPair⟩ tree =
        (Classical.choice source_drop_tree_exists) := by
  rintro ⟨tree, _⟩
  exact comm_only_has_no_drop_tree ⟨tree⟩

#print axioms commToDrop_event
#print axioms commToDrop_is_authoredRuleFunctor
#print axioms commToDrop_is_freeOperationalMap
#print axioms commToDrop_retains_occurrence
#print axioms commToDrop_tree_injective
#print axioms commToDrop_reindexTree
#print axioms source_comm_tree_exists
#print axioms drop_tree_not_from_comm

end Mettapedia.OSLF.Binding.RhoRuleListPolynomialFunctor
