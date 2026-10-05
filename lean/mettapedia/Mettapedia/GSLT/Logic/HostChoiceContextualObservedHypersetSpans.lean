import Mettapedia.GSLT.Logic.HostChoiceContextualObservedHypersetTriangle
import Mettapedia.GSLT.Logic.ObservedMaterialization
import Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes

/-!
# Authored reduction spans through the structured observed set readout

The complete event carrier is retained. Its two endpoints are interpreted
in the constructed observed-class/set product, whose packed equality kernel
is the original labelled, atom-preserving bisimulation. Context actions and
admitted child actions remain distinct labels of that original system.

Outgoing endpoint matching follows constructively from this kernel. Incoming
matching has a separate exact criterion; OSLF's predecessor box uses it.
Neither endpoint matching nor equality of state observations reconstructs
an authored receipt. The optional material event fingerprint records labels,
declared receipt identifiers, and both observed endpoints explicitly.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.HostChoiceContextualObservedHypersetSpans

open _root_.CategoryTheory
open Mettapedia.TypeTheory ContextualWitnessCover
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualCoalgebraLabelledGraph ContextualObservedCoalgebra
open HostChoiceContextualObservedHypersetTriangle
open ObservationSpans Mettapedia.OSLF.Framework.DerivedModalities
open HennessyMilner ObservedMaterialization

universe u v e

namespace Retained

variable {X : Type u} {Y : Type v}

def span (source : ReductionSpan.{u,e} X) (observe : X → Y) : ReductionSpan.{v,e} Y where
  Edge := source.Edge
  source event := observe (source.source event)
  target event := observe (source.target event)

def map (source : ReductionSpan.{u,e} X) (observe : X → Y) : SpanMap source (span source observe) where
  states := observe
  events := id
  source_comm _ := rfl
  target_comm _ := rfl

def kernel (observe : X → Y) : Setoid X where
  r first second := observe first = observe second
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

theorem sourceLifts_iff (source : ReductionSpan.{u,e} X) (observe : X → Y) :
    (map source observe).SourceLifts ↔ FutureMatching source (kernel observe) := by
  constructor
  · intro lifts left right same event starts
    obtain ⟨matched, starts', ends⟩ := lifts right event
      ((congrArg observe starts).trans same)
    exact ⟨matched, starts', ends.symm⟩
  · intro matching state event same
    obtain ⟨matched, starts, related⟩ := matching same event rfl
    exact ⟨matched, starts, related.symm⟩

theorem targetLifts_iff (source : ReductionSpan.{u,e} X) (observe : X → Y) :
    (map source observe).TargetLifts ↔ PastMatching source (kernel observe) := by
  constructor
  · intro lifts left right same event ends
    obtain ⟨matched, ends', starts⟩ := lifts right event
      ((congrArg observe ends).trans same)
    exact ⟨matched, ends', starts.symm⟩
  · intro matching state event same
    obtain ⟨matched, ends, related⟩ := matching same event rfl
    exact ⟨matched, ends, related.symm⟩

/-- Retaining each event makes the stronger occurrence law expose precisely
whether changing an endpoint representative can keep that exact event. -/
theorem sourceOccurrenceLifts_iff (source : ReductionSpan.{u,e} X) (observe : X → Y) :
    (map source observe).SourceOccurrenceLifts ↔
      ∀ state event, observe (source.source event) = observe state → source.source event = state := by
  constructor
  · intro lifts state event same
    obtain ⟨matched, starts, identical⟩ := lifts state event same
    exact (congrArg source.source identical).symm.trans starts
  · intro faithful state event same
    exact ⟨event, faithful state event same, rfl⟩

theorem targetOccurrenceLifts_iff (source : ReductionSpan.{u,e} X) (observe : X → Y) :
    (map source observe).TargetOccurrenceLifts ↔
      ∀ state event, observe (source.target event) = observe state → source.target event = state := by
  constructor
  · intro lifts state event same
    obtain ⟨matched, ends, identical⟩ := lifts state event same
    exact (congrArg source.target identical).symm.trans ends
  · intro faithful state event same
    exact ⟨event, faithful state event same, rfl⟩

end Retained

variable {D : Type u} [Category.{u} D] {A : D ⥤ Type u}
variable (source : NaturalHom A (CoveredFuturePowerFamilies.family A))
variable {Atom : Type u} (atoms : Atom → State A → Prop)
variable (worlds : ArgumentCoding D)
variable (arrows : (first second : D) → ArgumentCoding (first ⟶ second))
variable (atomCoding : ArgumentCoding Atom)

abbrev StructuredState := (point : D) × (structured source atoms worlds arrows atomCoding).obj point

noncomputable def packedReadout (state : State A) : StructuredState source atoms worlds arrows atomCoding :=
  ⟨state.1, (structuredReadout source atoms worlds arrows atomCoding).app state.1 state.2⟩

theorem packed_kernel (left right : State A) :
    packedReadout source atoms worlds arrows atomCoding left =
      packedReadout source atoms worlds arrows atomCoding right ↔
        (system source atoms).Bisimilar left right := by
  rcases left with ⟨point, left⟩
  rcases right with ⟨other, right⟩
  constructor
  · intro same
    have contexts : point = other := congrArg Sigma.fst same
    subst other
    have values := Sigma.mk.inj_iff.mp same
    exact (system_bisimilar_iff source atoms worlds arrows point left right).mpr
      ((structured_kernel source atoms worlds arrows atomCoding point left right).mp (eq_of_heq values.2))
  · intro related
    have contexts := system_bisimilar_contexts_eq source atoms worlds arrows related
    change point = other at contexts
    subst other
    exact congrArg (Sigma.mk point)
      ((structured_kernel source atoms worlds arrows atomCoding point left right).mpr
        ((system_bisimilar_iff source atoms worlds arrows point left right).mp related))

theorem predicate_descends_iff (predicate : State A → Prop) :
    PredicateDescends (packedReadout source atoms worlds arrows atomCoding) predicate ↔
      ∀ ⦃left right⦄, (system source atoms).Bisimilar left right → (predicate left ↔ predicate right) := by
  rw [predicateDescends_iff]
  constructor
  · intro constant left right related
    exact Mettapedia.GSLT.Scope.ConstantOnFibers.iff constant
      ((packed_kernel source atoms worlds arrows atomCoding left right).mpr related)
  · intro invariant left right same
    exact propext (invariant ((packed_kernel source atoms worlds arrows atomCoding left right).mp same))

/-- Full HML denotations descend by the constructive forward theorem. No
image-finiteness or modal-characterization converse is used here. -/
theorem formula_descends (formula : Formula Atom (Label D)) :
    PredicateDescends (packedReadout source atoms worlds arrows atomCoding) ((system source atoms).sat formula) :=
  (predicate_descends_iff source atoms worlds arrows atomCoding _).mpr
    (fun {_ _} related => (system source atoms).logicallyEquivalent_of_bisimilar related formula)

theorem native_formula_descends (formula : Formula Atom (Label D)) :
    PredicateDescends (packedReadout source atoms worlds arrows atomCoding)
      (Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes.formulaPredicate (system source atoms) formula) :=
  formula_descends source atoms worlds arrows atomCoding formula

variable (occurrences : ActionOccurrences (system source atoms))

noncomputable def structuredSpan : ReductionSpan (StructuredState source atoms worlds arrows atomCoding) :=
  Retained.span occurrences.sourceSpan (packedReadout source atoms worlds arrows atomCoding)

noncomputable def spanReadout : SpanMap occurrences.sourceSpan
    (structuredSpan source atoms worlds arrows atomCoding occurrences) :=
  Retained.map occurrences.sourceSpan (packedReadout source atoms worlds arrows atomCoding)

theorem event_retained (event : ActionOccurrences.Event occurrences) :
    (spanReadout source atoms worlds arrows atomCoding occurrences).events event = event := rfl

theorem source_lifts : (spanReadout source atoms worlds arrows atomCoding occurrences).SourceLifts := by
  intro state event same
  have action := (occurrences.erases event.label event.source event.target).mp ⟨event.occurrence⟩
  have related := (packed_kernel source atoms worlds arrows atomCoding state event.source).mp same.symm
  obtain ⟨relation, bisimulation, relates⟩ := related
  obtain ⟨target, reduction, relatedTargets⟩ := bisimulation.2.1 relates event.label action
  obtain ⟨receipt⟩ := (occurrences.erases event.label state target).mpr reduction
  refine ⟨⟨event.label, state, target, receipt⟩, rfl, ?_⟩
  exact (packed_kernel source atoms worlds arrows atomCoding target event.target).mpr
    ⟨relation, bisimulation, relatedTargets⟩

theorem diamond_square (predicate : StructuredState source atoms worlds arrows atomCoding → Prop) (state : State A) :
    derivedDiamond (structuredSpan source atoms worlds arrows atomCoding occurrences) predicate
        (packedReadout source atoms worlds arrows atomCoding state) ↔
      derivedDiamond occurrences.sourceSpan (predicate ∘ packedReadout source atoms worlds arrows atomCoding) state :=
  (spanReadout source atoms worlds arrows atomCoding occurrences).diamond_pullback
    (source_lifts source atoms worlds arrows atomCoding occurrences) predicate state

theorem incoming_iff : (spanReadout source atoms worlds arrows atomCoding occurrences).TargetLifts ↔
    PastMatching occurrences.sourceSpan (Retained.kernel (packedReadout source atoms worlds arrows atomCoding)) :=
  Retained.targetLifts_iff _ _

theorem box_square_iff :
    (∀ (predicate : StructuredState source atoms worlds arrows atomCoding → Prop) (state : State A),
      derivedBox (structuredSpan source atoms worlds arrows atomCoding occurrences) predicate
          (packedReadout source atoms worlds arrows atomCoding state) ↔
        derivedBox occurrences.sourceSpan (predicate ∘ packedReadout source atoms worlds arrows atomCoding) state) ↔
      PastMatching occurrences.sourceSpan (Retained.kernel (packedReadout source atoms worlds arrows atomCoding)) :=
  (SpanMap.targetLifts_iff_box (spanReadout source atoms worlds arrows atomCoding occurrences)).symm.trans
    (incoming_iff source atoms worlds arrows atomCoding occurrences)

theorem diamond_predicate_descends (predicate : State A → Prop)
    (descends : PredicateDescends (packedReadout source atoms worlds arrows atomCoding) predicate) :
    PredicateDescends (packedReadout source atoms worlds arrows atomCoding) (derivedDiamond occurrences.sourceSpan predicate) :=
  (spanReadout source atoms worlds arrows atomCoding occurrences).diamond_descends
    (source_lifts source atoms worlds arrows atomCoding occurrences) predicate descends

theorem box_predicate_descends
    (incoming : PastMatching occurrences.sourceSpan (Retained.kernel (packedReadout source atoms worlds arrows atomCoding)))
    (predicate : State A → Prop)
    (descends : PredicateDescends (packedReadout source atoms worlds arrows atomCoding) predicate) :
    PredicateDescends (packedReadout source atoms worlds arrows atomCoding) (derivedBox occurrences.sourceSpan predicate) :=
  (spanReadout source atoms worlds arrows atomCoding occurrences).box_descends
    ((incoming_iff source atoms worlds arrows atomCoding occurrences).mpr incoming) predicate descends

theorem occurrence_step_iff (first second : State A) :
    (∃ event : ActionOccurrences.Event occurrences,
      occurrences.sourceSpan.source event = first ∧ occurrences.sourceSpan.target event = second) ↔
        (theory source).Step first second := by
  constructor
  · rintro ⟨event, starts, ends⟩
    have action := (occurrences.erases event.label event.source event.target).mp ⟨event.occurrence⟩
    change ∃ label, ContextualCoalgebraLabelledGraph.Step source first label second
    exact ⟨event.label, starts ▸ ends ▸ action⟩
  · rintro ⟨label, action⟩
    obtain ⟨receipt⟩ := (occurrences.erases label first second).mpr action
    exact ⟨⟨label, first, second, receipt⟩, rfl, rfl⟩

/-- The event carrier presents the actual step relation used by the sole
GSLT-to-OSLF construction, including its separate context/child labels. -/
theorem native_diamond_iff
    (predicate : Mettapedia.OSLF.Framework.GSLTTypeSynthesis.EquationPredicate (theory source)) (state : State A) :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.semanticDiamond (theory source) predicate) state ↔
      derivedDiamond occurrences.sourceSpan (fun next => predicate next) state := by
  refine (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltDiamond_spec
    (theory source) (fun next => predicate next) state).trans ?_
  constructor
  · rintro ⟨next, action, holds⟩
    obtain ⟨event, starts, ends⟩ := (occurrence_step_iff source atoms occurrences state next).mpr action
    refine ⟨event, starts, ?_⟩
    change predicate event.target
    exact (Iff.of_eq (congrArg (fun value : State A => predicate value) ends)).mpr holds
  · rintro ⟨event, starts, holds⟩
    exact ⟨event.target, (occurrence_step_iff source atoms occurrences state event.target).mp ⟨event, starts, rfl⟩, holds⟩

theorem native_box_iff
    (predicate : Mettapedia.OSLF.Framework.GSLTTypeSynthesis.EquationPredicate (theory source)) (state : State A) :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.semanticBox (theory source) predicate) state ↔
      derivedBox occurrences.sourceSpan (fun next => predicate next) state := by
  refine (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltBox_spec
    (theory source) (fun next => predicate next) state).trans ?_
  constructor
  · intro all event ends
    exact all event.source ((occurrence_step_iff source atoms occurrences event.source state).mp ⟨event, rfl, ends⟩)
  · intro all previous action
    obtain ⟨event, starts, ends⟩ := (occurrence_step_iff source atoms occurrences previous state).mpr action
    exact starts ▸ all event ends

include occurrences in
theorem native_diamond_descends
    (predicate : Mettapedia.OSLF.Framework.GSLTTypeSynthesis.EquationPredicate (theory source))
    (descends : PredicateDescends (packedReadout source atoms worlds arrows atomCoding) (fun state => predicate state)) :
    PredicateDescends (packedReadout source atoms worlds arrows atomCoding)
      (fun state => (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.semanticDiamond (theory source) predicate) state) := by
  obtain ⟨observed, truth⟩ := diamond_predicate_descends source atoms worlds arrows atomCoding occurrences _ descends
  exact ⟨observed, fun state => (truth state).trans (native_diamond_iff source atoms occurrences predicate state).symm⟩

theorem native_box_descends
    (incoming : PastMatching occurrences.sourceSpan (Retained.kernel (packedReadout source atoms worlds arrows atomCoding)))
    (predicate : Mettapedia.OSLF.Framework.GSLTTypeSynthesis.EquationPredicate (theory source))
    (descends : PredicateDescends (packedReadout source atoms worlds arrows atomCoding) (fun state => predicate state)) :
    PredicateDescends (packedReadout source atoms worlds arrows atomCoding)
      (fun state => (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.semanticBox (theory source) predicate) state) := by
  obtain ⟨observed, truth⟩ := box_predicate_descends source atoms worlds arrows atomCoding occurrences incoming _ descends
  exact ⟨observed, fun state => (truth state).trans (native_box_iff source atoms occurrences predicate state).symm⟩

variable {ID : Type u} (identifier : ActionOccurrences.Event occurrences → ID) (ids : ArgumentCoding ID)

/-- Labels and declared identifiers are encoded explicitly alongside both
actual observed graph values. State atoms alone do not encode these data. -/
def eventFingerprint (event : ActionOccurrences.Event occurrences) : HSet.{u} :=
  HSet.kpair ((ContextualCoalgebraMaterialReadout.labels worlds arrows).reading event.label)
    (HSet.kpair (ids.reading (identifier event))
      (HSet.kpair (ContextualObservedCoalgebra.value source atoms worlds arrows atomCoding event.source)
        (ContextualObservedCoalgebra.value source atoms worlds arrows atomCoding event.target)))

theorem eventFingerprint_kernel (first second : ActionOccurrences.Event occurrences) :
    eventFingerprint source atoms worlds arrows atomCoding occurrences identifier ids first =
      eventFingerprint source atoms worlds arrows atomCoding occurrences identifier ids second ↔
        first.label = second.label ∧ identifier first = identifier second ∧
          (system source atoms).Bisimilar first.source second.source ∧
          (system source atoms).Bisimilar first.target second.target := by
  unfold eventFingerprint
  rw [HSet.kpair_inj, HSet.kpair_inj, HSet.kpair_inj]
  exact and_congr (ContextualCoalgebraMaterialReadout.labels worlds arrows).injective.eq_iff
    (and_congr ids.injective.eq_iff
      (and_congr ((readings source atoms worlds arrows atomCoding).value_eq_iff_bisimilar
          (faithful source atoms worlds arrows atomCoding) _ _)
        ((readings source atoms worlds arrows atomCoding).value_eq_iff_bisimilar
          (faithful source atoms worlds arrows atomCoding) _ _)))

theorem fingerprint_consumer_descends_iff (predicate : ActionOccurrences.Event occurrences → Prop) :
    PredicateDescends (eventFingerprint source atoms worlds arrows atomCoding occurrences identifier ids) predicate ↔
      ∀ ⦃first second⦄, first.label = second.label → identifier first = identifier second →
        (system source atoms).Bisimilar first.source second.source →
          (system source atoms).Bisimilar first.target second.target → (predicate first ↔ predicate second) := by
  rw [predicateDescends_iff]
  constructor
  · intro constant first second labels identifiers sources targets
    exact Mettapedia.GSLT.Scope.ConstantOnFibers.iff constant
      ((eventFingerprint_kernel source atoms worlds arrows atomCoding occurrences identifier ids first second).mpr
        ⟨labels, identifiers, sources, targets⟩)
  · intro invariant first second same
    obtain ⟨labels, identifiers, sources, targets⟩ :=
      (eventFingerprint_kernel source atoms worlds arrows atomCoding occurrences identifier ids first second).mp same
    exact propext (invariant labels identifiers sources targets)

end Mettapedia.GSLT.HostChoiceContextualObservedHypersetSpans
