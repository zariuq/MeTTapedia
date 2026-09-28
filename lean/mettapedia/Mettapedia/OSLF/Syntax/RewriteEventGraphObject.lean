import Mettapedia.OSLF.Syntax.RewriteClassEventHistory

/-!
# The event graph and its endpoint subobject

A retained operational graph has an object of events with source and target
maps to equation-class states.  The proposition-valued reduction subobject is
the image of the paired endpoint map.  The factorization is explicit here in
`Type`: the map onto the step subtype is surjective, and that subtype embeds
into the product of states.  Parallel authored occurrences need not be
identified by the event object, though the endpoint subobject identifies them.

This does not assert that the larger classifying theory of a conditional GSLT
has already been constructed or is cartesian closed.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RewriteEventGraphObject

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Binding.RewriteClassEventHistory

universe u

section General

variable (system : Mettapedia.GSLT.ProofRelevant.ProofRelevantGSLT.{u})

/-- The edge object of the retained graph over equation-class states. -/
structure EventObject where
  source : ClassState system
  target : ClassState system
  occurrence : ClassEvent system source target

/-- Paired source and target maps of the event graph. -/
def endpoints (event : EventObject system) :
    ClassState system × ClassState system :=
  (event.source, event.target)

/-- The extensional reduction relation as a subtype of the product of
equation-class states. -/
def StepSubobject :=
  { pair : ClassState system × ClassState system //
    SemanticStep system.theory pair.1.term pair.2.term }

/-- Every retained event supplies a point of the endpoint-step subobject. -/
def incidence (event : EventObject system) : StepSubobject system :=
  ⟨endpoints system event,
    (classEvent_iff_semanticStep system event.source event.target).mp
      ⟨event.occurrence⟩⟩

/-- The subobject inclusion is injective. -/
def inclusion : StepSubobject system →
    ClassState system × ClassState system :=
  Subtype.val

theorem inclusion_injective : Function.Injective (inclusion system) :=
  Subtype.val_injective

/-- The retained event graph maps onto every semantic one-step pair. -/
theorem incidence_surjective : Function.Surjective (incidence system) := by
  rintro ⟨⟨source, target⟩, step⟩
  obtain ⟨event⟩ :=
    (classEvent_iff_semanticStep system source target).mpr step
  exact ⟨⟨source, target, event⟩, rfl⟩

/-- The endpoint map factors through the step subobject. -/
theorem endpoints_factorization :
    inclusion system ∘ incidence system = endpoints system :=
  rfl

/-- The image of paired source/target is exactly the extensional semantic
step relation. -/
theorem in_endpoint_image_iff (source target : ClassState system) :
    (source, target) ∈ Set.range (endpoints system) ↔
      SemanticStep system.theory source.term target.term := by
  constructor
  · rintro ⟨event, endpointsEqual⟩
    have sourceEqual : event.source = source :=
      congrArg Prod.fst endpointsEqual
    have targetEqual : event.target = target :=
      congrArg Prod.snd endpointsEqual
    subst source
    subst target
    exact (classEvent_iff_semanticStep system _ _).mp ⟨event.occurrence⟩
  · intro step
    obtain ⟨event⟩ :=
      (classEvent_iff_semanticStep system source target).mpr step
    exact ⟨⟨source, target, event⟩, rfl⟩

/-- The actual range of the paired endpoint map is equivalent to the
semantic-step subobject. This identifies the latter with the categorical
image in `Type`, whose image objects are ranges of functions. -/
def imageEquivStepSubobject :
    { pair : ClassState system × ClassState system //
      pair ∈ Set.range (endpoints system) } ≃ StepSubobject system where
  toFun pair :=
    ⟨pair.1,
      (in_endpoint_image_iff system pair.1.1 pair.1.2).mp pair.2⟩
  invFun pair :=
    ⟨pair.1,
      (in_endpoint_image_iff system pair.1.1 pair.1.2).mpr pair.2⟩
  left_inv := by
    intro pair
    cases pair
    rfl
  right_inv := by
    intro pair
    cases pair
    rfl

end General

namespace RhoExample

open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.RewriteClassEventHistory.RhoExample

private abbrev rhoSystem :=
  Mettapedia.OSLF.Binding.RewriteClassEventHistory.RhoExample.system

private def first : EventObject rhoSystem :=
  ⟨classSource, classTarget, firstClassEvent⟩

private def second : EventObject rhoSystem :=
  ⟨classSource, classTarget, secondClassEvent⟩

private def ruleIndex (event : EventObject rhoSystem) :
    Fin duplicatedCommunication.rules.length :=
  event.occurrence.occurrence.1

/-- Two authored COMM events survive as different points of the edge object. -/
theorem graph_events_distinct : first ≠ second := by
  intro equal
  have indices := congrArg ruleIndex equal
  have impossible : (0 : Fin 2) = 1 := indices
  cases impossible

/-- The paired endpoint map forgets which COMM occurrence was authored. -/
theorem endpoints_not_injective :
    ¬ Function.Injective (endpoints rhoSystem) := by
  intro injective
  exact graph_events_distinct (injective rfl)

end RhoExample

end Mettapedia.OSLF.Binding.RewriteEventGraphObject
