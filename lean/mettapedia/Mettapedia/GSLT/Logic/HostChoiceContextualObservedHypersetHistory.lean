import Mettapedia.GSLT.Logic.HostChoiceContextualObservedHypersetSpans
import Mettapedia.GSLT.Logic.HostChoiceContextualObservedHypersetReceipts
import Mettapedia.GSLT.Distinction.HistoryContextControls

/-!
# Authored histories in the structured observed set interpretation

Every deterministic context event and admitted future child event has an
actual typed receipt. Child receipts retain the written and actual entries,
result configuration, residual script, future arrow and duplicate copy tag.
The packed span preserves all these data and both endpoints.

Current child receipts also form a genuine presheaf: contextual substitution
transports both placed endpoints, renames both entries and the residual
script, appends the authored future script, and preserves the copy tag.
The predecessor counterexample uses the explicitly atom-forgetting,
future-only profile; it does not identify distinct declared result atoms.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace Mettapedia.GSLT.HostChoiceContextualObservedHypersetHistory

open _root_.CategoryTheory
open Mettapedia.TypeTheory ContextualWitnessCover
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open HennessyMilner ObservedMaterialization ObservationSpans
open Mettapedia.OSLF.Framework.DerivedModalities
open Distinction.HistoryGrammar Distinction.HistoryContextCategory Distinction.HistoryContextTwoSided
open HostChoiceContextualObservedHypersetTriangle HostChoiceContextualObservedHypersetSpans

variable {V : Type} {G : Grammar V} (profile : Profile G)

private theorem span_ext {X Y : Type*} {first : ReductionSpan X} {second : ReductionSpan Y}
    {left right : SpanMap first second} (states : left.states = right.states) (events : left.events = right.events) :
    left = right := by
  cases left
  cases right
  cases states
  cases events
  rfl

private theorem context_map_identity (F : World G ⥤ Type*) (point : World G) :
    (fun value : F.obj point => F.map (inContext point (Context.one G)) value) = id := by
  funext value
  exact F.map_id_apply point value

private theorem context_map_composition (F : World G ⥤ Type*) (point : World G) (earlier later : Context G) :
    (fun value : F.obj point => F.map (inContext point (earlier.andThen later)) value) =
      (fun value : F.obj point => F.map (inContext point later) (F.map (inContext point earlier) value)) := by
  funext value
  change F.map (contextArrow point (earlier.andThen later)) value = _
  rw [contextArrow_andThen]
  exact F.map_comp_apply _ _ value

def authoredOccurrences {Atom : Type} (atoms : Atom → ContextualCoalgebraLabelledGraph.State (placed G) → Prop) :
    ActionOccurrences (ContextualObservedCoalgebra.system (coalgebra profile) atoms) where
  Occurrence label first second :=
    match label with
    | .context point target arrow =>
      {state : Placed point // first = ⟨point, state⟩ ∧ second = ⟨target, transport arrow state⟩} × Bool
    | .child point target arrow =>
      ((state : Placed point) ×
        {receipt : (receipts profile point state).Carrier ⟨target, arrow⟩ //
          first = ⟨point, state⟩ ∧ second = ⟨target, (receipts profile point state).value ⟨target, arrow⟩ receipt⟩}) × Bool
  erases label first second := by
    cases label with
    | context point target arrow =>
      constructor
      · rintro ⟨⟨receipt, _⟩⟩
        exact ⟨receipt.val, receipt.property⟩
      · rintro ⟨state, starts, ends⟩
        exact ⟨⟨⟨state, starts, ends⟩, false⟩⟩
    | child point target arrow =>
      constructor
      · rintro ⟨⟨⟨state, receipt, starts, ends⟩, _⟩⟩
        exact ⟨state, (receipts profile point state).value ⟨target, arrow⟩ receipt, starts, ends,
          ((receipts profile point state).covered ⟨target, arrow⟩ _).mpr ⟨receipt, rfl⟩⟩
      · rintro ⟨state, child, starts, ends, admitted⟩
        obtain ⟨receipt, same⟩ := ((receipts profile point state).covered ⟨target, arrow⟩ child).mp admitted
        exact ⟨⟨⟨state, receipt, starts, ends.trans (congrArg (Sigma.mk target) same.symm)⟩, false⟩⟩

def occurrenceCopy {Atom : Type} (atoms : Atom → ContextualCoalgebraLabelledGraph.State (placed G) → Prop)
    (event : ActionOccurrences.Event (authoredOccurrences profile atoms)) : Bool :=
  match event with
  | ⟨.context _ _ _, _, _, (_, copy)⟩ => copy
  | ⟨.child _ _ _, _, _, (_, copy)⟩ => copy

/-- These fields retain the authored child receipt, rather than an endpoint
relation with its witnesses erased. Logical validity fields are propositions;
the copy tag and all script/configuration fields are ordinary data. -/
structure Receipt (point : World G) where
  source : Placed point
  target : Placed point
  written : Entry V
  actual : Entry V
  rest : List (Entry V)
  copy : Bool
  script : source.script = written :: rest
  admitted : profile.admits written actual
  moves : Moves G actual source.live target.live
  origin : target.origin = source.origin + 1
  residual : target.script = rest

theorem Receipt.ext' {point : World G} {first second : Receipt profile point}
    (starts : first.source = second.source) (ends : first.target = second.target)
    (written : first.written = second.written) (actual : first.actual = second.actual)
    (rest : first.rest = second.rest) (copy : first.copy = second.copy) : first = second := by
  rcases first with ⟨_, _, _, _, _, _, _, _, _, _, _⟩
  rcases second with ⟨_, _, _, _, _, _, _, _, _, _, _⟩
  cases starts
  cases ends
  cases written
  cases actual
  cases rest
  cases copy
  rfl

def restrict {first second : World G} (arrow : first ⟶ second) (receipt : Receipt profile first) :
    Receipt profile second where
  source := transport arrow receipt.source
  target := transport arrow receipt.target
  written := (Arrow.context arrow).entry receipt.written
  actual := (Arrow.context arrow).entry receipt.actual
  rest := (Arrow.context arrow).script receipt.rest ++ Arrow.script arrow
  copy := receipt.copy
  script := by rw [transport_script, receipt.script]; rfl
  admitted := profile.admits_context _ receipt.admitted
  moves := moves_apply G (Arrow.context arrow) receipt.moves
  origin := receipt.origin
  residual := by rw [transport_script, receipt.residual]

theorem restrict_identity (point : World G) (receipt : Receipt profile point) :
    restrict profile (𝟙 point) receipt = receipt :=
  Receipt.ext' profile (transport_id _) (transport_id _)
    (Context.entry_one _) (Context.entry_one _)
    ((congrArg (fun script => script ++ []) (Context.script_one receipt.rest)).trans (List.append_nil _)) rfl

theorem restrict_composition {first middle last : World G}
    (earlier : first ⟶ middle) (later : middle ⟶ last) (receipt : Receipt profile first) :
    restrict profile (earlier ≫ later) receipt = restrict profile later (restrict profile earlier receipt) := by
  apply Receipt.ext' profile (transport_comp earlier later _) (transport_comp earlier later _)
    (Context.entry_andThen _ _ _) (Context.entry_andThen _ _ _)
  · change ((Arrow.context earlier).andThen (Arrow.context later)).script receipt.rest ++
        ((Arrow.context later).script (Arrow.script earlier) ++ Arrow.script later) =
      (Arrow.context later).script ((Arrow.context earlier).script receipt.rest ++ Arrow.script earlier) ++ Arrow.script later
    rw [Context.script_andThen, Context.script_append, List.append_assoc]
  · rfl

def eventFamily : World G ⥤ Type where
  obj := Receipt profile
  map arrow := TypeCat.ofHom (restrict profile arrow)
  map_id point := by
    apply ConcreteCategory.hom_ext
    exact restrict_identity profile point
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    exact restrict_composition profile earlier later

def sourceEndpoint : NaturalHom (eventFamily profile) (placed G) where
  app _ receipt := receipt.source
  naturality _ _ := rfl

def targetEndpoint : NaturalHom (eventFamily profile) (placed G) where
  app _ receipt := receipt.target
  naturality _ _ := rfl

theorem receipt_action (point : World G) (receipt : Receipt profile point) :
    ContextualCoalgebraLabelledGraph.Step (coalgebra profile) ⟨point, receipt.source⟩
      (.child point point (𝟙 point)) ⟨point, receipt.target⟩ := by
  refine ⟨receipt.source, receipt.target, rfl, rfl, ?_⟩
  change Advances profile (transport (𝟙 point) receipt.source) receipt.target
  rw [transport_id]
  exact ⟨receipt.written, receipt.actual, receipt.rest, receipt.script, receipt.admitted,
    receipt.moves, receipt.origin, receipt.residual⟩

theorem receipt_action_realized (point : World G) (first second : Placed point)
    (action : ContextualCoalgebraLabelledGraph.Step (coalgebra profile) ⟨point, first⟩
      (.child point point (𝟙 point)) ⟨point, second⟩) :
    ∃ receipt : Receipt profile point, receipt.source = first ∧ receipt.target = second := by
  obtain ⟨state, child, starts, ends, advances⟩ := action
  have states : first = state := eq_of_heq (Sigma.mk.inj_iff.mp starts).2
  have children : second = child := eq_of_heq (Sigma.mk.inj_iff.mp ends).2
  subst state
  subst child
  change Emits profile first (𝟙 point) second at advances
  rw [show Emits profile first (𝟙 point) second = Advances profile first second from
    congrArg (fun moved => Advances profile moved second) (transport_id first)] at advances
  obtain ⟨written, actual, rest, script, admitted, moves, origin, residual⟩ := advances
  exact ⟨⟨first, second, written, actual, rest, false, script, admitted, moves, origin, residual⟩, rfl, rfl⟩

def copyFamily : World G ⥤ Type where
  obj _ := Bool
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def copyReading : NaturalHom (eventFamily profile) (copyFamily (G := G)) where
  app _ receipt := receipt.copy
  naturality _ _ := rfl

section Structured

variable {Atom : Type} (atoms : Atom → ContextualCoalgebraLabelledGraph.State (placed G) → Prop)
variable (nodes : ArgumentCoding V) (listing : Distinction.HistoryObserver.Listing V)
variable (atomCoding : ArgumentCoding Atom)

noncomputable abbrev structuredRead := structuredReadout (coalgebra profile) atoms (worldCoding G)
  (arrowCoding nodes listing) atomCoding

noncomputable abbrev structuredReceiptFamily :=
  HostChoiceContextualObservedHypersetReceipts.family (coalgebra profile) atoms (worldCoding G)
    (arrowCoding nodes listing) atomCoding (sourceEndpoint profile) (targetEndpoint profile)

include nodes listing in
/-- This outgoing law is proved from the actual history receipt realization
and original HM bisimulation, rather than supplied as a modal interface. -/
theorem outgoing_matches : HostChoiceContextualObservedHypersetReceipts.OutgoingMatches
    (coalgebra profile) atoms (sourceEndpoint profile) (targetEndpoint profile) := by
  intro point state event related
  have packed := (ContextualObservedCoalgebra.system_bisimilar_iff (coalgebra profile) atoms
    (worldCoding G) (arrowCoding nodes listing) point event.source state).mpr related
  obtain ⟨relation, bisimulation, relates⟩ := packed
  obtain ⟨matched, action, targets⟩ := bisimulation.1 relates
    (.child point point (𝟙 point)) (receipt_action profile point event)
  rcases matched with ⟨target, child⟩
  change ContextualCoalgebraLabelledGraph.Step (coalgebra profile) ⟨point, state⟩
    (.child point point (𝟙 point)) ⟨target, child⟩ at action
  have atPoint := ContextualCoalgebraLabelledGraph.step_target (coalgebra profile) action
  change target = point at atPoint
  subst target
  obtain ⟨receipt, starts, ends⟩ := receipt_action_realized profile point state child action
  refine ⟨receipt, starts, ?_⟩
  change ContextualObservedCoalgebra.ObservedBisimilar (coalgebra profile) atoms point receipt.target event.target
  rw [ends]
  exact (ContextualObservedCoalgebra.system_bisimilar_iff (coalgebra profile) atoms
    (worldCoding G) (arrowCoding nodes listing) point child event.target).mp
      ((ContextualObservedCoalgebra.system (coalgebra profile) atoms).bisimilar_symm
        ⟨relation, bisimulation, targets⟩)

theorem structured_receipts_decode : ContextualSmallFamilyUniverse.decodedFamily
    (ContextualSmallFamilyUniverse.classifier (structuredReceiptFamily profile atoms nodes listing atomCoding)) =
      structuredReceiptFamily profile atoms nodes listing atomCoding := ContextualSmallFamilyUniverse.decoded_classifier_eq _

theorem receipt_parameter_natural {first second : World G} (step : first ⟶ second) (receipt : Receipt profile first) :
    (HostChoiceContextualObservedHypersetReceipts.endpointPairs (coalgebra profile) atoms (worldCoding G)
      (arrowCoding nodes listing) atomCoding).map step
      ((HostChoiceContextualObservedHypersetReceipts.endpoints (coalgebra profile) atoms (worldCoding G)
        (arrowCoding nodes listing) atomCoding (sourceEndpoint profile) (targetEndpoint profile)).app first receipt) =
    (HostChoiceContextualObservedHypersetReceipts.endpoints (coalgebra profile) atoms (worldCoding G)
      (arrowCoding nodes listing) atomCoding (sourceEndpoint profile) (targetEndpoint profile)).app second
      (restrict profile step receipt) :=
  (HostChoiceContextualObservedHypersetReceipts.endpoints (coalgebra profile) atoms (worldCoding G)
    (arrowCoding nodes listing) atomCoding (sourceEndpoint profile) (targetEndpoint profile)).naturality step receipt

theorem contextual_diamond (predicate : Subfunctor (structured (coalgebra profile) atoms (worldCoding G)
    (arrowCoding nodes listing) atomCoding)) (point : World G) (state : Placed point) :
    (structuredRead profile atoms nodes listing atomCoding).app point state ∈
        (Mettapedia.GSLT.Topos.PresheafEventModalities.diamond
          (HostChoiceContextualObservedHypersetReceipts.observedGraph (coalgebra profile) atoms (worldCoding G)
            (arrowCoding nodes listing) atomCoding (sourceEndpoint profile) (targetEndpoint profile)) predicate).obj point ↔
      (ULift.up state : (HostChoiceContextualObservedHypersetReceipts.raise (placed G)).obj point) ∈
        (Mettapedia.GSLT.Topos.PresheafEventModalities.diamond
          (HostChoiceContextualObservedHypersetReceipts.sourceGraph (sourceEndpoint profile) (targetEndpoint profile))
          (Mettapedia.GSLT.Topos.ConstructivePresheaf.preimage
            (HostChoiceContextualObservedHypersetReceipts.eventObservation (coalgebra profile) atoms (worldCoding G)
              (arrowCoding nodes listing) atomCoding (sourceEndpoint profile) (targetEndpoint profile)).states predicate)).obj point :=
  HostChoiceContextualObservedHypersetReceipts.contextual_diamond_square _ _ _ _ _ _ _
    (outgoing_matches profile atoms nodes listing) predicate point state

noncomputable def freshRead (point : World G) (live : Multiset V) :
    (structured (coalgebra profile) atoms (worldCoding G) (arrowCoding nodes listing) atomCoding).obj point :=
  (structuredRead profile atoms nodes listing atomCoding).app point (fresh point live)

theorem fresh_kernel (point : World G) (first second : Multiset V) :
    freshRead profile atoms nodes listing atomCoding point first =
      freshRead profile atoms nodes listing atomCoding point second ↔
        ContextualObservedCoalgebra.ObservedBisimilar (coalgebra profile) atoms point (fresh point first) (fresh point second) :=
  structured_kernel (coalgebra profile) atoms (worldCoding G) (arrowCoding nodes listing) atomCoding point _ _

theorem fresh_context_natural (point : World G) (context : Context G) (live : Multiset V) :
    (structured (coalgebra profile) atoms (worldCoding G) (arrowCoding nodes listing) atomCoding).map
        (inContext point context) (freshRead profile atoms nodes listing atomCoding point live) =
      freshRead profile atoms nodes listing atomCoding point (context.apply live) := by
  have freshEq : transport (inContext point context) (fresh point live) = fresh point (context.apply live) :=
    Placed.ext' rfl rfl rfl
  exact ((structuredRead profile atoms nodes listing atomCoding).naturality (inContext point context) (fresh point live)).trans
    (congrArg ((structuredRead profile atoms nodes listing atomCoding).app point) freshEq)

/-- This span is the authored executable configuration span. It is kept
separate from the packed system's context and admitted-child actions. -/
noncomputable def freshSpan (point : World G) : ReductionSpan
    ((structured (coalgebra profile) atoms (worldCoding G) (arrowCoding nodes listing) atomCoding).obj point) :=
  Retained.span (eventSpan G) (freshRead profile atoms nodes listing atomCoding point)

noncomputable def freshSpanMap (point : World G) : SpanMap (eventSpan G)
    (freshSpan profile atoms nodes listing atomCoding point) := Retained.map _ _

noncomputable def contextSpanMap (point : World G) (context : Context G) :
    SpanMap (freshSpan profile atoms nodes listing atomCoding point)
      (freshSpan profile atoms nodes listing atomCoding point) where
  states := (structured (coalgebra profile) atoms (worldCoding G) (arrowCoding nodes listing) atomCoding).map
    (inContext point context)
  events := (contextSpan G context).events
  source_comm event := (fresh_context_natural profile atoms nodes listing atomCoding point context event.source).symm
  target_comm event := (fresh_context_natural profile atoms nodes listing atomCoding point context event.target).symm

theorem context_span_identity (point : World G) :
    contextSpanMap profile atoms nodes listing atomCoding point (Context.one G) =
      SpanMap.identity (freshSpan profile atoms nodes listing atomCoding point) := by
  apply span_ext
  · exact context_map_identity
      (structured (coalgebra profile) atoms (worldCoding G) (arrowCoding nodes listing) atomCoding) point
  · exact congrArg (fun map : SpanMap (eventSpan G) (eventSpan G) => map.events) (contextSpan_one G)

theorem context_span_composition (point : World G) (earlier later : Context G) :
    contextSpanMap profile atoms nodes listing atomCoding point (earlier.andThen later) =
      (contextSpanMap profile atoms nodes listing atomCoding point later).comp
        (contextSpanMap profile atoms nodes listing atomCoding point earlier) := by
  apply span_ext
  · exact context_map_composition
      (structured (coalgebra profile) atoms (worldCoding G) (arrowCoding nodes listing) atomCoding) point earlier later
  · exact congrArg (fun map : SpanMap (eventSpan G) (eventSpan G) => map.events) (contextSpan_andThen G earlier later)

theorem context_span_square (point : World G) (context : Context G) :
    (contextSpanMap profile atoms nodes listing atomCoding point context).comp
        (freshSpanMap profile atoms nodes listing atomCoding point) =
      (freshSpanMap profile atoms nodes listing atomCoding point).comp (contextSpan G context) := by
  apply span_ext
  · exact funext (fresh_context_natural profile atoms nodes listing atomCoding point context)
  · rfl

section NaturalModalities

variable [DecidableEq V] (point : World G) (context : Context G)
variable (predicate : (structured (coalgebra profile) atoms (worldCoding G)
  (arrowCoding nodes listing) atomCoding).obj point → Prop)

theorem diamond_context_square (emptyFrame : context.frame = []) (live : Multiset V) :
    derivedDiamond (eventSpan G) (predicate ∘ freshRead profile atoms nodes listing atomCoding point) (context.apply live) ↔
      derivedDiamond (eventSpan G)
        (fun next => predicate ((contextSpanMap profile atoms nodes listing atomCoding point context).states
          (freshRead profile atoms nodes listing atomCoding point next))) live := by
  have square := (contextSpan G context).diamond_pullback
    ((contextSpan_sourceLifts_iff listing context).mpr emptyFrame)
    (predicate ∘ freshRead profile atoms nodes listing atomCoding point) live
  change derivedDiamond (eventSpan G) (predicate ∘ freshRead profile atoms nodes listing atomCoding point) (context.apply live) ↔
    derivedDiamond (eventSpan G) ((predicate ∘ freshRead profile atoms nodes listing atomCoding point) ∘ context.apply) live at square
  have same : (predicate ∘ freshRead profile atoms nodes listing atomCoding point) ∘ context.apply =
      fun next => predicate ((contextSpanMap profile atoms nodes listing atomCoding point context).states
        (freshRead profile atoms nodes listing atomCoding point next)) :=
    funext fun next => congrArg predicate (fresh_context_natural profile atoms nodes listing atomCoding point context next).symm
  rw [same] at square
  exact square

theorem box_context_square (conditions : context.frame = [] ∧ Function.Surjective context.rename.map) (live : Multiset V) :
    derivedBox (eventSpan G) (predicate ∘ freshRead profile atoms nodes listing atomCoding point) (context.apply live) ↔
      derivedBox (eventSpan G)
        (fun next => predicate ((contextSpanMap profile atoms nodes listing atomCoding point context).states
          (freshRead profile atoms nodes listing atomCoding point next))) live := by
  have square := (contextSpan G context).box_pullback
    ((contextSpan_targetLifts_iff listing context).mpr conditions)
    (predicate ∘ freshRead profile atoms nodes listing atomCoding point) live
  change derivedBox (eventSpan G) (predicate ∘ freshRead profile atoms nodes listing atomCoding point) (context.apply live) ↔
    derivedBox (eventSpan G) ((predicate ∘ freshRead profile atoms nodes listing atomCoding point) ∘ context.apply) live at square
  have same : (predicate ∘ freshRead profile atoms nodes listing atomCoding point) ∘ context.apply =
      fun next => predicate ((contextSpanMap profile atoms nodes listing atomCoding point context).states
        (freshRead profile atoms nodes listing atomCoding point next)) :=
    funext fun next => congrArg predicate (fresh_context_natural profile atoms nodes listing atomCoding point context next).symm
  rw [same] at square
  exact square

end NaturalModalities

end Structured

end Mettapedia.GSLT.HostChoiceContextualObservedHypersetHistory
