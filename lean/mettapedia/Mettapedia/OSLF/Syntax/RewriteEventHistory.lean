import Mathlib.CategoryTheory.PathCategory.Basic
import Mettapedia.OSLF.Syntax.PresentationSemantics
import Mettapedia.OSLF.Syntax.RhoEventMultiplicity

/-!
# Free histories of retained rewrite events

An extensional rewrite relation records which endpoint pairs are connected.
An authored presentation can retain more: the occurrence of a rule, its
context and substitution, and representatives chosen modulo equations.  The
free path category on that event graph records finite histories without
identifying parallel events.  Its universal property is inherited from the
path-category construction and is stated here for this operational graph.

This construction covers closed, unconditional authored presentations at a
chosen sort.  It is an event-history category, not the full classifying
category for conditional GSLTs or their dependent internal languages.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RewriteEventHistory

open CategoryTheory
open Mettapedia.GSLT.ProofRelevant

universe u

/-- A vertex of the proof-relevant operational graph. -/
@[ext]
structure State (system : ProofRelevantGSLT.{u}) where
  term : system.theory.Term

/-- An arrow is one retained occurrence, not merely a proposition that a
rewrite with these endpoints exists. -/
instance (system : ProofRelevantGSLT.{u}) : Quiver (State system) where
  Hom source target := system.steps.Evidence source.term target.term

/-- Finite authored event histories, including the empty history. -/
abbrev History (system : ProofRelevantGSLT.{u})
    (source target : State system) := Quiver.Path source target

/-- The free category of event histories. -/
abbrev HistoryCategory (system : ProofRelevantGSLT.{u}) :=
  Paths (State system)

/-- The graph of endpoint steps, whose arrows carry no event identity. -/
@[ext]
structure ExtensionalState (theory : Mettapedia.GSLT.GSLT.{u}) where
  term : theory.Term

instance (theory : Mettapedia.GSLT.GSLT.{u}) :
    Quiver (ExtensionalState theory) where
  Hom source target := PLift (theory.Step source.term target.term)

instance (theory : Mettapedia.GSLT.GSLT.{u})
    (source target : ExtensionalState theory) :
    Subsingleton (source ⟶ target) := by
  refine ⟨?_⟩
  intro first second
  cases first
  cases second
  rfl

/-- Forget an occurrence only when passing from the event graph to the
endpoint-step graph. -/
def eraseEvents (system : ProofRelevantGSLT.{u}) :
    State system ⥤q ExtensionalState system.theory where
  obj state := ⟨state.term⟩
  map event := ⟨system.steps.erase event⟩

/-- Every interpretation of primitive events in a category extends to all
finite histories. -/
def interpret (system : ProofRelevantGSLT.{u})
    {C : Type*} [Category C] (generators : State system ⥤q C) :
    HistoryCategory system ⥤ C :=
  Paths.lift generators

/-- The interpretation acts on one-event histories as specified. -/
theorem interpret_generator (system : ProofRelevantGSLT.{u})
    {C : Type*} [Category C] (generators : State system ⥤q C)
    {source target : State system} (event : source ⟶ target) :
    (interpret system generators).map event.toPath = generators.map event :=
  Paths.lift_toPath generators event

/-- The event interpretation is the unique functor with its prescribed
action on all generating events and states. -/
theorem interpret_unique (system : ProofRelevantGSLT.{u})
    {C : Type*} [Category C] (generators : State system ⥤q C)
    (candidate : HistoryCategory system ⥤ C)
    (agrees : Paths.of (State system) ⋙q candidate.toPrefunctor = generators) :
    candidate = interpret system generators :=
  Paths.lift_unique generators candidate agrees

/-- An operational translation acts on vertices and retained generators.
This uses its forward evidence map, not its separate event-lifting condition. -/
def mapGenerators {source target : ProofRelevantGSLT.{u}}
    (translation : Translation source target) :
    State source ⥤q State target where
  obj state := ⟨translation.mapTerm state.term⟩
  map event := translation.mapEvidence event

/-- Extend the action on operational generators to whole histories. -/
def mapHistories {source target : ProofRelevantGSLT.{u}}
    (translation : Translation source target) :
    HistoryCategory source ⥤ HistoryCategory target :=
  Paths.lift (mapGenerators translation ⋙q Paths.of (State target))

/-- A translated singleton history is the singleton translated occurrence. -/
theorem mapHistories_generator {source target : ProofRelevantGSLT.{u}}
    (translation : Translation source target)
    {a b : State source} (event : a ⟶ b) :
    (mapHistories translation).map event.toPath =
      Quiver.Hom.toPath (translation.mapEvidence event) :=
  Paths.lift_toPath _ event

/-- Identity translation acts as identity on every event history. -/
theorem mapHistories_id (system : ProofRelevantGSLT.{u}) :
    mapHistories (Translation.id system) =
      𝟭 (HistoryCategory system) := by
  symm
  apply Paths.lift_unique
  fapply Prefunctor.ext
  · intro state
    rfl
  · intro a b event
    rfl

/-- Composing translations composes their action on histories. -/
theorem mapHistories_comp {first middle last : ProofRelevantGSLT.{u}}
    (earlier : Translation first middle)
    (later : Translation middle last) :
    mapHistories (earlier.comp later) =
      mapHistories earlier ⋙ mapHistories later := by
  symm
  apply Paths.lift_unique
  fapply Prefunctor.ext
  · intro state
    rfl
  · intro a b event
    rfl

/-- Erasing event identity extends uniquely to a functor on histories. It
retains history length and endpoint-step sequence. -/
def eraseHistory (system : ProofRelevantGSLT.{u}) :
    HistoryCategory system ⥤ Paths (ExtensionalState system.theory) :=
  Paths.lift (eraseEvents system ⋙q Paths.of (ExtensionalState system.theory))

/-- A concrete unconditional presentation supplies the proof-relevant
operational graph at each closed sort. -/
def authoredSystem {S : Signature} (presentation : UnpositionedPresentation S)
    (sort : S.Srt) : ProofRelevantGSLT where
  theory := presentation.toExtensionalGSLTAt sort
  steps := presentation.stepEvidenceAt sort

namespace RhoExample

open Mettapedia.OSLF.Binding.RhoSchema

private abbrev system : ProofRelevantGSLT :=
  authoredSystem duplicatedCommunication Srt.pr

private def source : State system := ⟨parT commInput commOutput⟩
private def target : State system := ⟨commTarget⟩

private def firstEdge : source ⟶ target := firstCommunicationEvent
private def secondEdge : source ⟶ target := secondCommunicationEvent

/-- The two copies of COMM give different one-event histories. -/
theorem distinct_authored_histories :
    firstEdge.toPath ≠ secondEdge.toPath := by
  intro equal
  have eventEqual : firstCommunicationEvent = secondCommunicationEvent := by
    exact eq_of_heq (Quiver.Path.cons.inj equal).2.2
  exact communication_events_distinct eventEqual

/-- Endpoint erasure identifies the two one-event histories. -/
theorem same_extensional_history :
    (eraseHistory system).map firstEdge.toPath =
      (eraseHistory system).map secondEdge.toPath := by
  simp only [eraseHistory, Paths.lift_toPath]
  exact congrArg Quiver.Hom.toPath
    (Subsingleton.elim ((eraseEvents system).map firstEdge)
      ((eraseEvents system).map secondEdge))

/-- The rho event-history erasure is not injective on this hom set. Thus an
endpoint-only graph cannot recover authorship of a communication occurrence. -/
theorem eraseHistory_not_injective :
    ¬ Function.Injective
      (fun history : History system source target =>
        (eraseHistory system).map history) := by
  intro injective
  exact distinct_authored_histories
    (injective same_extensional_history)

end RhoExample

end Mettapedia.OSLF.Binding.RewriteEventHistory
