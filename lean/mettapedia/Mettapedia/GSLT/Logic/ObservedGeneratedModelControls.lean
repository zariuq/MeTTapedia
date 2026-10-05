import Mettapedia.GSLT.Logic.ObservedGeneratedModel

/-!
# Infinite labelled contexts for the observed generated model

Context arrows retain ordered extension histories. The operational system
is the genuine two-phase cyclic process at each growing position; its
context action depends on extension length. Distinct parallel histories
therefore have the same operational action while their future-function
labels remain distinct. The material family grows a cyclic alternative.

The operational pullback constructs all functor and material transport
laws from the authored system. Occurrence provenance is transported beside
the observed value readout.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ObservedGeneratedModelControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory.MaterialSets
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualObservedFamilyEnclosure
open PowerClassPresheafDescent

universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable (profile : ContextualSystem C) (along : Dᵒᵖ ⥤ Cᵒᵖ)

def pullback : ContextualSystem D where
  theory X := profile.theory (along.obj X)
  system X := profile.system (along.obj X)
  readings X := profile.readings (along.obj X)
  faithful X := profile.faithful (along.obj X)
  restrict step := profile.restrict (along.map step)
  restrict_id X term := by rw [along.map_id]; exact profile.restrict_id _ term
  restrict_comp first second term := by
    rw [along.map_comp]
    exact profile.restrict_comp _ _ term
  bisim_restrict := by
    intro X Y step left right related
    exact profile.bisim_restrict (along.map step) related

variable (graphs : profile.sourceFace.Elements → AccessiblePointedGraph.{u})
variable (transport : MaterialTransport profile.sourceFace profile.classFace profile.observation graphs)

def graphsUnder (point : (pullback profile along).sourceFace.Elements) : AccessiblePointedGraph.{u} :=
  graphs ⟨along.obj point.1, point.2⟩

/-- The operational pullback derives material transport, including its
exact fibre law, from the existing authored restriction action. -/
def transportUnder : MaterialTransport (pullback profile along).sourceFace
    (pullback profile along).classFace (pullback profile along).observation (graphsUnder profile along graphs) where
  invariant X := transport.invariant (along.obj X)
  map step := transport.map (along.map step)
  map_id_value X value member := by
    change (transport.map (along.map (𝟙 X)) value member).1 = member.1
    rw [along.map_id]
    exact transport.map_id_value _ value member
  map_comp_value first second value member := by
    change (transport.map (along.map (first ≫ second)) value member).1 =
      (transport.map (along.map second) (profile.sourceFace.map (along.map first) value)
        (transport.map (along.map first) value member)).1
    rw [along.map_comp]
    exact transport.map_comp_value _ _ value member
  compatible step := transport.compatible (along.map step)

def sectionUnder (term : RawSection profile.sourceFace graphs) :
    RawSection (pullback profile along).sourceFace (graphsUnder profile along graphs) :=
  fun point => term ⟨along.obj point.1, point.2⟩

theorem sectionUnder_compatible (term : RawSection profile.sourceFace graphs)
    (compatible : ContextualCompatible profile.sourceFace profile.classFace profile.observation graphs transport term) :
    ContextualCompatible (pullback profile along).sourceFace (pullback profile along).classFace
      (pullback profile along).observation (graphsUnder profile along graphs)
      (transportUnder profile along graphs transport) (sectionUnder profile along graphs term) :=
  ⟨fun X => compatible.1 (along.obj X), fun step source => compatible.2 (along.map step) source⟩

variable (occurrences : ∀ X, ObservedMaterialization.ActionOccurrences (profile.system X))
variable (action : Events.EventAction profile occurrences)

def occurrencesUnder (X : Dᵒᵖ) :
    ObservedMaterialization.ActionOccurrences ((pullback profile along).system X) :=
  occurrences (along.obj X)

def eventActionUnder : Events.EventAction (pullback profile along) (occurrencesUnder profile along occurrences) where
  restrict step := action.restrict (along.map step)
  source_comm step := action.source_comm (along.map step)
  target_comm step := action.target_comm (along.map step)
  restrict_id X event := by rw [along.map_id]; exact action.restrict_id _ event
  restrict_comp first second event := by
    rw [along.map_comp]
    exact action.restrict_comp _ _ event

namespace Paths

open LabelledContextPaths
open PowerClassPresheafDescent.Controls
open ObservedGeneratedModel

abbrev Site := Worldᵒᵖ

/-- Length forgets the path labels for this declared operational observer.
The source context category still retains those actual arrows. -/
def lengthMap : Siteᵒᵖ ⥤ Stagesᵒᵖ where
  obj X := world X.unop.unop.length
  map {X Y} step := (homOfLE (show X.unop.unop.length ≤ Y.unop.unop.length from
    (Nat.le_add_right X.unop.unop.length step.unop.unop.val.length).trans_eq step.unop.unop.property)).op.op
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

def model : ContextualSystem Site := pullback GrowthControls.profile lengthMap

def worldCoding : ArgumentCoding Siteᵒᵖ where
  graph point := LabelledContextPaths.worlds.graph point.unop.unop
  injective := by
    intro first second same
    exact Opposite.unop_injective (Opposite.unop_injective (LabelledContextPaths.worlds.injective same))

def arrowCoding (first second : Siteᵒᵖ) : ArgumentCoding (first ⟶ second) where
  graph arrow := (LabelledContextPaths.arrows first.unop.unop second.unop.unop).graph arrow.unop.unop
  injective := by
    intro firstArrow secondArrow same
    have original := (LabelledContextPaths.arrows first.unop.unop second.unop.unop).injective same
    exact congrArg (fun step : first.unop.unop ⟶ second.unop.unop => step.op.op) original

def familyGraphs := graphsUnder GrowthControls.profile lengthMap GrowthControls.positiveGraphs

def familyTransport := transportUnder GrowthControls.profile lengthMap
  GrowthControls.positiveGraphs GrowthControls.positiveTransport

def positiveTerm := sectionUnder GrowthControls.profile lengthMap GrowthControls.positiveGraphs GrowthControls.positiveTerm

theorem positiveTerm_compatible : ContextualCompatible model.sourceFace model.classFace
    model.observation familyGraphs familyTransport positiveTerm :=
  sectionUnder_compatible GrowthControls.profile lengthMap GrowthControls.positiveGraphs
    GrowthControls.positiveTransport GrowthControls.positiveTerm GrowthControls.positiveTerm_compatible

def initial : Siteᵒᵖ := Opposite.op (Opposite.op LabelledContextPaths.initial)
def next : Siteᵒᵖ := Opposite.op (Opposite.op LabelledContextPaths.next)
def extension (label : Nat) : initial ⟶ next := (LabelledContextPaths.extension label).op.op

def oldRaw : model.sourceFace.Elements := ⟨initial, stageValue 0 0 (by decide) false⟩
def newRaw : model.sourceFace.Elements := ⟨next, stageValue 1 1 (by decide) true⟩

def observedInput := input model worldCoding familyGraphs familyTransport

def positiveSection := (sourceSectionEquiv model worldCoding familyGraphs familyTransport).symm
  ⟨positiveTerm, positiveTerm_compatible⟩

theorem old_section_value :
    (observedInput.model (observedPoint model worldCoding oldRaw)).value
      (positiveSection.val (observedPoint model worldCoding oldRaw)) = ∅ :=
  sourceSectionEquiv_inverse_value model worldCoding familyGraphs familyTransport positiveTerm positiveTerm_compatible oldRaw

theorem new_section_value :
    (observedInput.model (observedPoint model worldCoding newRaw)).value
      (positiveSection.val (observedPoint model worldCoding newRaw)) = HSet.quineAtom :=
  sourceSectionEquiv_inverse_value model worldCoding familyGraphs familyTransport positiveTerm positiveTerm_compatible newRaw

theorem section_values_differ :
    (observedInput.model (observedPoint model worldCoding oldRaw)).value
      (positiveSection.val (observedPoint model worldCoding oldRaw)) ≠
        (observedInput.model (observedPoint model worldCoding newRaw)).value
          (positiveSection.val (observedPoint model worldCoding newRaw)) := by
  rw [old_section_value, new_section_value]
  exact HSet.empty_ne_quineAtom

theorem parallel_actions_equal (first second : Nat) (state : model.sourceFace.obj initial) :
    model.restrict (extension first) state = model.restrict (extension second) state :=
  congrArg (fun step => GrowthControls.profile.restrict step state)
    (Subsingleton.elim (lengthMap.map (extension first)) (lengthMap.map (extension second)))

theorem parallel_labels_distinct {first second : Nat} (different : first ≠ second) :
    (arrowCoding initial next).reading (extension first) ≠
      (arrowCoding initial next).reading (extension second) := by
  intro same
  have paths := congrArg (fun step : initial ⟶ next => step.unop.unop.val)
    ((arrowCoding initial next).injective same)
  exact different (List.singleton_injective paths)

def events : ∀ X, ObservedMaterialization.ActionOccurrences (model.system X) :=
  occurrencesUnder GrowthControls.profile lengthMap GrowthControls.occurrences

def eventAction : Events.EventAction model events :=
  eventActionUnder GrowthControls.profile lengthMap GrowthControls.occurrences GrowthControls.eventAction

def event (provenance : Bool) : ObservedMaterialization.ActionOccurrences.Event (events initial) where
  label := Unit.unit
  source := oldRaw.2
  target := GrowthControls.flip oldRaw.2
  occurrence := ⟨provenance, PLift.up rfl⟩

theorem event_provenance_distinct : event false ≠ event true := by
  intro same
  have labels := congrArg (fun occurrence : ObservedMaterialization.ActionOccurrences.Event (events initial) =>
    occurrence.occurrence.1) same
  exact Bool.false_ne_true labels

theorem event_provenance_preserved (label : Nat) (provenance : Bool) :
    (eventAction.restrict (extension label) (event provenance)).occurrence.1 = provenance := rfl

theorem generated_pi_sigma_w (point : (context model worldCoding).base.Elements) :
    HSet.lift ((observedInput.pi (body model worldCoding familyGraphs familyTransport) arrowCoding).model point).carrier ∈
        ContextualGeneratedUniverse.enclosure (Seeds model worldCoding)
          (seedModel model worldCoding familyGraphs familyTransport) arrowCoding (context model worldCoding) point ∧
    HSet.lift ((observedInput.sigma (body model worldCoding familyGraphs familyTransport)).model point).carrier ∈
        ContextualGeneratedUniverse.enclosure (Seeds model worldCoding)
          (seedModel model worldCoding familyGraphs familyTransport) arrowCoding (context model worldCoding) point ∧
    HSet.lift ((observedInput.w (body model worldCoding familyGraphs familyTransport) arrowCoding).model point).carrier ∈
        ContextualGeneratedUniverse.enclosure (Seeds model worldCoding)
          (seedModel model worldCoding familyGraphs familyTransport) arrowCoding (context model worldCoding) point :=
  pi_sigma_w_enclosed model worldCoding arrowCoding familyGraphs familyTransport point

def phaseGraphs (_point : model.sourceFace.Elements) : AccessiblePointedGraph := GrowthControls.nonWfChoices

def phaseTransport : MaterialTransport model.sourceFace model.classFace model.observation phaseGraphs where
  invariant _ := by intro _ _ _; rfl
  map _ _ member := member
  map_id_value _ _ _ := rfl
  map_comp_value _ _ _ _ := rfl
  compatible _ := by intro _ _ _ _ _ same; exact same

def phaseTerm (point : model.sourceFace.Elements) : El (· ∈ ·) (HSet.mk (phaseGraphs point)) :=
  ⟨if point.2.2 then HSet.quineAtom else ∅, by
    change (if point.2.2 then HSet.quineAtom else ∅) ∈
      HSet.range (fun tag : Bool => if tag then HSet.loop else AccessiblePointedGraph.empty)
    apply HSet.mem_range.mpr
    refine ⟨point.2.2, ?_⟩
    cases point.2.2
    · exact HSet.mk_empty
    · exact HSet.mk_loop⟩

theorem phaseTerm_natural {X Y : Siteᵒᵖ} (step : X ⟶ Y) (state : model.sourceFace.obj X) :
    (phaseTransport.map step state (phaseTerm ⟨X, state⟩)).1 =
      (phaseTerm ⟨Y, model.sourceFace.map step state⟩).1 := rfl

theorem phaseTerm_not_compatible :
    ¬ ContextualCompatible model.sourceFace model.classFace model.observation phaseGraphs phaseTransport phaseTerm := by
  intro compatible
  let left := stageValue 0 0 (by decide) false
  let right := stageValue 0 0 (by decide) true
  have related : (model.system initial).Bisimilar left right :=
    (GrowthControls.bisimilar_iff_position (world 0) left right).mpr rfl
  have same := compatible.1 initial ((model.observation_eq_iff initial left right).mpr related)
  exact HSet.empty_ne_quineAtom same

def fullSourcePredicate : Subfunctor model.sourceFace where
  obj _ _ := True
  map _ _ _ := True.intro

/-- A supported source family can have a natural material section which
fails the observation-fibre law and therefore has no observed section. -/
theorem phase_support_full :
    Mettapedia.GSLT.Topos.support (nativeSourceDisplayed model.sourceFace model.classFace
      model.observation phaseGraphs phaseTransport) = fullSourcePredicate := by
  ext X state
  constructor
  · intro _
    trivial
  · intro _
    refine ⟨(sourceMaterialMemberEquiv model.sourceFace phaseGraphs ⟨X, state⟩).symm ⟨∅, ?_⟩⟩
    exact HSet.mem_range.mpr ⟨false, HSet.mk_empty⟩

theorem phaseTerm_no_observed_section :
    ¬ ∃ chosen : (input model worldCoding phaseGraphs phaseTransport).family.sections,
      ∀ source, ((input model worldCoding phaseGraphs phaseTransport).model
        (observedPoint model worldCoding source)).value
        (chosen.val (observedPoint model worldCoding source)) = (phaseTerm source).1 := by
  rintro ⟨chosen, values⟩
  have sourceEquality : (sourceSectionEquiv model worldCoding phaseGraphs phaseTransport chosen).val = phaseTerm := by
    funext source
    apply El.ext HSet.propositional
    exact (sourceSectionEquiv_value model worldCoding phaseGraphs phaseTransport chosen source).symm.trans
      (values source)
  have compatible := (sourceSectionEquiv model worldCoding phaseGraphs phaseTransport chosen).property
  rw [sourceEquality] at compatible
  exact phaseTerm_not_compatible compatible

def emptyTerm := sectionUnder GrowthControls.profile lengthMap GrowthControls.positiveGraphs
  GrowthControls.FutureArguments.emptyTerm

theorem emptyTerm_compatible : ContextualCompatible model.sourceFace model.classFace
    model.observation familyGraphs familyTransport emptyTerm :=
  sectionUnder_compatible GrowthControls.profile lengthMap GrowthControls.positiveGraphs
    GrowthControls.positiveTransport GrowthControls.FutureArguments.emptyTerm
    GrowthControls.FutureArguments.emptyTerm_compatible

def emptySection := (sourceSectionEquiv model worldCoding familyGraphs familyTransport).symm
  ⟨emptyTerm, emptyTerm_compatible⟩

theorem emptySection_value (source : model.sourceFace.Elements) :
    (observedInput.model (observedPoint model worldCoding source)).value
      (emptySection.val (observedPoint model worldCoding source)) = ∅ :=
  sourceSectionEquiv_inverse_value model worldCoding familyGraphs familyTransport emptyTerm emptyTerm_compatible source

/-- The last argument determines whether this generated body has a material
inhabitant. Its formation uses discrete identity over the actual input. -/
def argumentBody : ContextualGeneratedUniverse.MaterialFamily observedInput.extension :=
  (body model worldCoding familyGraphs familyTransport).identity
    (PowerClassPresheafProducts.lastVariable observedInput.family)
    (PowerClassPresheafProducts.reindexSection (PowerClassPresheafProducts.projection observedInput.family)
      observedInput.family emptySection)

def argumentBodyGenerated : ContextualGeneratedUniverse.Generation (Seeds model worldCoding)
    (seedModel model worldCoding familyGraphs familyTransport) arrowCoding argumentBody :=
  .identity (bodyGenerated model worldCoding arrowCoding familyGraphs familyTransport) _ _

def emptyPoint : observedInput.extension.base.Elements :=
  ⟨next, ⟨(observedPoint model worldCoding newRaw).2,
    emptySection.val (observedPoint model worldCoding newRaw)⟩⟩

def cyclicPoint : observedInput.extension.base.Elements :=
  ⟨next, ⟨(observedPoint model worldCoding newRaw).2,
    positiveSection.val (observedPoint model worldCoding newRaw)⟩⟩

theorem empty_positions : (argumentBody.model emptyPoint).carrier = {∅} :=
  PresheafIdentityWitness.graph_reflexive _

theorem cyclic_positions : (argumentBody.model cyclicPoint).carrier = ∅ := by
  have different : positiveSection.val (observedPoint model worldCoding newRaw) ≠
      emptySection.val (observedPoint model worldCoding newRaw) := by
    intro same
    exact HSet.empty_ne_quineAtom ((emptySection_value newRaw).symm.trans
      ((congrArg (observedInput.model (observedPoint model worldCoding newRaw)).value same.symm).trans new_section_value))
  exact PresheafIdentityWitness.graph_empty_of_distinct different

theorem argument_body_nonconstant :
    (argumentBody.model emptyPoint).carrier ≠ (argumentBody.model cyclicPoint).carrier := by
  rw [empty_positions, cyclic_positions]
  exact (HSet.empty_ne_singleton_empty).symm

theorem dependent_operations_enclosed (point : (context model worldCoding).base.Elements) :
    HSet.lift ((observedInput.pi argumentBody arrowCoding).model point).carrier ∈
        ContextualGeneratedUniverse.enclosure (Seeds model worldCoding)
          (seedModel model worldCoding familyGraphs familyTransport) arrowCoding (context model worldCoding) point ∧
    HSet.lift ((observedInput.sigma argumentBody).model point).carrier ∈
        ContextualGeneratedUniverse.enclosure (Seeds model worldCoding)
          (seedModel model worldCoding familyGraphs familyTransport) arrowCoding (context model worldCoding) point ∧
    HSet.lift ((observedInput.w argumentBody arrowCoding).model point).carrier ∈
        ContextualGeneratedUniverse.enclosure (Seeds model worldCoding)
          (seedModel model worldCoding familyGraphs familyTransport) arrowCoding (context model worldCoding) point :=
  ⟨ContextualGeneratedUniverse.generated_mem_enclosure _ _ _
    (.pi (inputGenerated model worldCoding arrowCoding familyGraphs familyTransport) argumentBodyGenerated) point,
    ContextualGeneratedUniverse.generated_mem_enclosure _ _ _
      (.sigma (inputGenerated model worldCoding arrowCoding familyGraphs familyTransport) argumentBodyGenerated) point,
    ContextualGeneratedUniverse.generated_mem_enclosure _ _ _
      (.w (inputGenerated model worldCoding arrowCoding familyGraphs familyTransport) argumentBodyGenerated) point⟩

def futureRaw : model.sourceFace.Elements := ⟨next, model.sourceFace.map (extension 0) oldRaw.2⟩

def futureArgument : observedInput.family.obj (observedPoint model worldCoding futureRaw) :=
  (observedInput.model (observedPoint model worldCoding futureRaw)).decode ⟨HSet.quineAtom, by
    change HSet.quineAtom ∈ ((input model worldCoding familyGraphs familyTransport).model
      (observedPoint model worldCoding futureRaw)).carrier
    rw [input_source_carrier model worldCoding familyGraphs familyTransport futureRaw]
    exact HSet.mem_range.mpr ⟨true, HSet.mk_loop⟩⟩

theorem futureArgument_value :
    (observedInput.model (observedPoint model worldCoding futureRaw)).value futureArgument = HSet.quineAtom :=
  (observedInput.model (observedPoint model worldCoding futureRaw)).value_decode _

def futureArrow : observedPoint model worldCoding oldRaw ⟶ observedPoint model worldCoding futureRaw :=
  (classElements model.sourceFace model.classFace model.observation).map
    (CategoryOfElements.homMk oldRaw futureRaw (extension 0) rfl)

theorem initial_results_inhabited
    (argument : observedInput.family.obj (observedPoint model worldCoding oldRaw)) :
    Nonempty (argumentBody.family.obj ⟨oldRaw.1, ⟨(observedPoint model worldCoding oldRaw).2, argument⟩⟩) := by
  have carrier : (observedInput.model (observedPoint model worldCoding oldRaw)).carrier = {∅} :=
    (input_source_carrier model worldCoding familyGraphs familyTransport oldRaw).trans
      (OutcomeLabels.mk_chainGraph 1)
  have value : (observedInput.model (observedPoint model worldCoding oldRaw)).value argument = ∅ :=
    HSet.mem_singleton.mp (carrier ▸ (observedInput.model (observedPoint model worldCoding oldRaw)).value_mem argument)
  have same : argument = emptySection.val (observedPoint model worldCoding oldRaw) :=
    (observedInput.model (observedPoint model worldCoding oldRaw)).value_injective
      (value.trans (emptySection_value oldRaw).symm)
  exact ⟨PresheafIdentityWitness.encode same⟩

/-- Present support does not supply the all-future dependent product. The
new cyclic argument has an empty result fibre. -/
theorem dependent_pi_empty_initial :
    ((observedInput.pi argumentBody arrowCoding).model (observedPoint model worldCoding oldRaw)).carrier = ∅ := by
  apply HSet.ext
  intro value
  constructor
  · intro belongs
    let function := ((observedInput.pi argumentBody arrowCoding).model
      (observedPoint model worldCoding oldRaw)).decode ⟨value, belongs⟩
    let witness : PresheafIdentityWitness.Witness futureArgument
        (emptySection.val (observedPoint model worldCoding futureRaw)) :=
      function.app (observedPoint model worldCoding futureRaw) futureArrow futureArgument
    have same := congrArg (observedInput.model (observedPoint model worldCoding futureRaw)).value
      (PresheafIdentityWitness.decode witness)
    exact (HSet.empty_ne_quineAtom ((emptySection_value futureRaw).symm.trans
      (same.symm.trans futureArgument_value))).elim
  · intro belongs
    exact (HSet.notMem_empty value belongs).elim

end Paths

end Mettapedia.GSLT.ObservedGeneratedModelControls
