import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedReceiptFamilies
import Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedAntiFoundation
import Mettapedia.GSLT.Logic.ObservationSpans

/-!
# Reduction-span occurrence families in the realized material model

The actual reduction span is interpreted as a small incidence graph:
state, event, target state. An outgoing material root receipt decodes to
its precise authored event, including its source equality. Reversing the
span supplies incoming receipts without recovering them from future
behaviour. Arbitrary event-dependent graph families then use the actual
constructed small dependent sums and products.

Span maps carry the retained events with both endpoint laws. Product
pullback along a span map acts on its actual event function and satisfies
the decoded evaluation law. No inverse event lift is chosen from a modal
endpoint-lifting proposition.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedSpanFamilies

open GraphBisimulationRealizers GraphSetRealization GraphRealizedReceiptFamilies
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.GSLT.ObservationSpans

universe u
variable {State Other Third : Type u}

abbrev Nodes (span : ReductionSpan.{u,u} State) : Type u := State ⊕ span.Edge

def incidence (span : ReductionSpan.{u,u} State) : Nodes span → Nodes span → Prop
  | .inl state, .inr event => span.source event = state
  | .inr event, .inl state => span.target event = state
  | _, _ => False

def outgoingGraph (span : ReductionSpan.{u,u} State) (state : State) : Graph.{u} :=
  GraphRealizedAntiFoundation.canonical (incidence span) (.inl state)

abbrev Outgoing (span : ReductionSpan.{u,u} State) (state : State) : Type u :=
  {event : span.Edge // span.source event = state}

def eventOfReceipt (span : ReductionSpan.{u,u} State) (state : State)
    (receipt : Receipts (outgoingGraph span state)) : Outgoing span state :=
  match targetSame : receipt.val.val with
  | .inl _ => False.elim (by simpa [outgoingGraph, GraphRealizedAntiFoundation.canonical, incidence,
      AccessiblePointedGraph.generated, targetSame] using receipt.property)
  | .inr event => ⟨event, by simpa [outgoingGraph, GraphRealizedAntiFoundation.canonical, incidence,
      AccessiblePointedGraph.generated, targetSame] using receipt.property⟩

def receiptOfEvent (span : ReductionSpan.{u,u} State) (state : State) (event : Outgoing span state) :
    Receipts (outgoingGraph span state) :=
  ⟨⟨.inr event.val, Relation.ReflTransGen.refl.tail event.property⟩, event.property⟩

def outgoingDecode (span : ReductionSpan.{u,u} State) (state : State) :
    Receipts (outgoingGraph span state) ≃ Outgoing span state where
  toFun := eventOfReceipt span state
  invFun := receiptOfEvent span state
  left_inv receipt := by
    rcases receipt with ⟨⟨node, reachable⟩, edge⟩
    cases node with
    | inl state => exact False.elim edge
    | inr event => rfl
  right_inv event := by
    apply Subtype.ext
    rfl

def reverse (span : ReductionSpan.{u,u} State) : ReductionSpan.{u,u} State where
  Edge := span.Edge
  source := span.target
  target := span.source

def incomingGraph (span : ReductionSpan.{u,u} State) (state : State) : Graph.{u} :=
  outgoingGraph (reverse span) state

def incomingDecode (span : ReductionSpan.{u,u} State) (state : State) :
    Receipts (incomingGraph span state) ≃ {event : span.Edge // span.target event = state} :=
  outgoingDecode (reverse span) state

def bodyAtReceipt (span : ReductionSpan.{u,u} State)
    (body : (state : State) → Outgoing span state → Graph.{u}) (state : State)
    (receipt : Receipts (outgoingGraph span state)) : Graph.{u} :=
  body state (outgoingDecode span state receipt)

def eventProduct (span : ReductionSpan.{u,u} State)
    (body : (state : State) → Outgoing span state → Graph.{u}) (state : State) : Graph.{u} :=
  piGraph (outgoingGraph span state) (bodyAtReceipt span body state)

def eventSum (span : ReductionSpan.{u,u} State)
    (body : (state : State) → Outgoing span state → Graph.{u}) (state : State) : Graph.{u} :=
  sigmaGraph (outgoingGraph span state) (bodyAtReceipt span body state)

theorem dependentValue_heq {Index : Type u} {values : Index → Type u}
    (value : (index : Index) → values index) {first second : Index} (same : first = second) :
    HEq (value first) (value second) := by
  cases same
  rfl

/-- Explicit dependent reindexing uses only the supplied inverse and
transport along its proved equations. -/
def dependentReindex {First Second : Type u} (values : Second → Type u)
    (comparison : First ≃ Second) :
    ((argument : First) → values (comparison argument)) ≃ ((argument : Second) → values argument) where
  toFun function argument := (comparison.apply_symm_apply argument) ▸ function (comparison.symm argument)
  invFun function argument := function (comparison argument)
  left_inv function := by
    funext argument
    apply eq_of_heq
    exact (eqRec_heq (comparison.apply_symm_apply (comparison argument))
      (function (comparison.symm (comparison argument)))).trans
        (dependentValue_heq function (comparison.symm_apply_apply argument))
  right_inv function := by
    funext argument
    apply eq_of_heq
    exact (eqRec_heq (comparison.apply_symm_apply argument)
      (function (comparison (comparison.symm argument)))).trans
        (dependentValue_heq function (comparison.apply_symm_apply argument))

def eventProductDecode (span : ReductionSpan.{u,u} State)
    (body : (state : State) → Outgoing span state → Graph.{u}) (state : State) :
    Receipts (eventProduct span body state) ≃ ((event : Outgoing span state) → Receipts (body state event)) :=
  (piDecode _ _).trans (dependentReindex (fun event => Receipts (body state event)) (outgoingDecode span state))

variable {first : ReductionSpan.{u,u} State} {second : ReductionSpan.{u,u} Other}
variable {third : ReductionSpan.{u,u} Third}

def mapEvent (map : SpanMap first second) (state : State) (event : Outgoing first state) :
    Outgoing second (map.states state) :=
  ⟨map.events event.val, (map.source_comm event.val).trans (congrArg map.states event.property)⟩

theorem mapEvent_target (map : SpanMap first second) (state : State) (event : Outgoing first state) :
    second.target (mapEvent map state event).val = map.states (first.target event.val) :=
  map.target_comm event.val

theorem mapEvent_identity (state : State) (event : Outgoing first state) :
    mapEvent (SpanMap.identity first) state event = event := rfl

theorem mapEvent_composition (earlier : SpanMap first second) (later : SpanMap second third)
    (state : State) (event : Outgoing first state) :
    mapEvent (later.comp earlier) state event = mapEvent later (earlier.states state) (mapEvent earlier state event) := rfl

def pullBody (map : SpanMap first second)
    (body : (state : Other) → Outgoing second state → Graph.{u}) :
    (state : State) → Outgoing first state → Graph.{u} :=
  fun state event => body (map.states state) (mapEvent map state event)

/-- Pullback evaluates at the computed event image, retaining both endpoint
equalities in the source and target occurrence fibres. -/
def productPullback (map : SpanMap first second)
    (body : (state : Other) → Outgoing second state → Graph.{u}) (state : State)
    (function : Receipts (eventProduct second body (map.states state))) :
    Receipts (eventProduct first (pullBody map body) state) :=
  (eventProductDecode first (pullBody map body) state).symm
    (fun event => eventProductDecode second body (map.states state) function (mapEvent map state event))

theorem productPullback_evaluation (map : SpanMap first second)
    (body : (state : Other) → Outgoing second state → Graph.{u}) (state : State)
    (function : Receipts (eventProduct second body (map.states state))) (event : Outgoing first state) :
    eventProductDecode first (pullBody map body) state (productPullback map body state function) event =
      eventProductDecode second body (map.states state) function (mapEvent map state event) :=
  congrFun ((eventProductDecode first (pullBody map body) state).apply_symm_apply _) event

end Mettapedia.TypeTheory.MaterialSets.Hypersets.GraphRealizedSpanFamilies
