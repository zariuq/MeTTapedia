import Mettapedia.OSLF.Syntax.RewriteEventHistory

/-!
# Rewrite histories over equation classes

Equations identify states, but they need not identify rule occurrences.  A
class event therefore records the raw representatives at which a rule fired,
their equation-class endpoints, and the retained firing evidence.  Its
inhabitedness is exactly the semantic step relation on equation classes.
Free paths on this graph compose events whenever their intermediate classes
agree, even when their raw representatives differ.

This is the operational graph and its free history category.  The stronger
finite-limit/cartesian-closed classifying construction of Chapter 7 requires
additional structure and remains separate.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RewriteClassEventHistory

open CategoryTheory
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Binding.RewriteEventHistory

universe u

/-- One equation-class state of a proof-relevant GSLT. -/
@[ext]
structure ClassState (system : Mettapedia.GSLT.ProofRelevant.ProofRelevantGSLT.{u}) where
  term : SemanticTerm system.theory

/-- A retained step between equation classes, with the representatives on
which its authored occurrence actually fired. -/
structure ClassEvent
    (system : Mettapedia.GSLT.ProofRelevant.ProofRelevantGSLT.{u})
    (source target : ClassState system) where
  rawSource : system.theory.Term
  rawTarget : system.theory.Term
  sourceClass : Quotient.mk system.theory.equations rawSource = source.term
  occurrence : system.steps.Evidence rawSource rawTarget
  targetClass : Quotient.mk system.theory.equations rawTarget = target.term

instance (system : Mettapedia.GSLT.ProofRelevant.ProofRelevantGSLT.{u}) :
    Quiver (ClassState system) where
  Hom := ClassEvent system

/-- Occurrence-bearing histories whose vertices are equation classes. -/
abbrev ClassHistory
    (system : Mettapedia.GSLT.ProofRelevant.ProofRelevantGSLT.{u})
    (source target : ClassState system) := Quiver.Path source target

/-- The free category on class events. -/
abbrev ClassHistoryCategory
    (system : Mettapedia.GSLT.ProofRelevant.ProofRelevantGSLT.{u}) :=
  Paths (ClassState system)

/-- A semantic quotient step exists precisely when it has a retained class
event. The quotient adds no operational edge without an authored witness. -/
theorem classEvent_iff_semanticStep
    (system : Mettapedia.GSLT.ProofRelevant.ProofRelevantGSLT.{u})
    (source target : ClassState system) :
    Nonempty (ClassEvent system source target) ↔
      SemanticStep system.theory source.term target.term := by
  constructor
  · rintro ⟨event⟩
    exact ⟨event.rawSource, event.rawTarget, event.sourceClass,
      system.steps.erase event.occurrence, event.targetClass⟩
  · rintro ⟨rawSource, rawTarget, sourceClass, step, targetClass⟩
    obtain ⟨occurrence⟩ := system.steps.witness step
    exact ⟨⟨rawSource, rawTarget, sourceClass, occurrence, targetClass⟩⟩

/-- The free category extends any interpretation of class events. -/
def interpret (system : Mettapedia.GSLT.ProofRelevant.ProofRelevantGSLT.{u})
    {C : Type*} [Category C] (generators : ClassState system ⥤q C) :
    ClassHistoryCategory system ⥤ C :=
  Paths.lift generators

theorem interpret_generator
    (system : Mettapedia.GSLT.ProofRelevant.ProofRelevantGSLT.{u})
    {C : Type*} [Category C] (generators : ClassState system ⥤q C)
    {source target : ClassState system} (event : source ⟶ target) :
    (interpret system generators).map event.toPath = generators.map event :=
  Paths.lift_toPath generators event

theorem interpret_unique
    (system : Mettapedia.GSLT.ProofRelevant.ProofRelevantGSLT.{u})
    {C : Type*} [Category C] (generators : ClassState system ⥤q C)
    (candidate : ClassHistoryCategory system ⥤ C)
    (agrees : Paths.of (ClassState system) ⋙q candidate.toPrefunctor =
      generators) :
    candidate = interpret system generators :=
  Paths.lift_unique generators candidate agrees

/-- Quotient the vertices of a raw event without discarding the firing that
made it. -/
def quotientGenerators
    (system : Mettapedia.GSLT.ProofRelevant.ProofRelevantGSLT.{u}) :
    State system ⥤q ClassState system where
  obj state := ⟨Quotient.mk system.theory.equations state.term⟩
  map {source target} event :=
    { rawSource := source.term
      rawTarget := target.term
      sourceClass := rfl
      occurrence := event
      targetClass := rfl }

/-- The induced functor sends raw histories to class histories and can make
more event sequences composable by identifying equation-equivalent vertices. -/
def quotientHistories
    (system : Mettapedia.GSLT.ProofRelevant.ProofRelevantGSLT.{u}) :
    HistoryCategory system ⥤ ClassHistoryCategory system :=
  Paths.lift (quotientGenerators system ⋙q Paths.of (ClassState system))

theorem quotientHistories_generator
    (system : Mettapedia.GSLT.ProofRelevant.ProofRelevantGSLT.{u})
    {source target : State system} (event : source ⟶ target) :
    (quotientHistories system).map event.toPath =
      Quiver.Hom.toPath ((quotientGenerators system).map event) :=
  Paths.lift_toPath _ event

/-- For an authored unconditional presentation, class-event inhabitation at
chosen representatives is exactly its equation-closed operational relation. -/
theorem authored_classEvent_mk_iff_step {S : Signature}
    (presentation : UnpositionedPresentation S) (sort : S.Srt)
    (source target : Term S [] sort) :
    Nonempty (ClassEvent (authoredSystem presentation sort)
      ⟨Quotient.mk (eqSetoid presentation.eqs [] sort) source⟩
      ⟨Quotient.mk (eqSetoid presentation.eqs [] sort) target⟩) ↔
      presentation.StepModE source target := by
  exact (classEvent_iff_semanticStep (authoredSystem presentation sort) _ _).trans
    (semanticStep_mk_iff_step (presentation.toExtensionalGSLTAt sort) source target)

/-- Equations with no authored reduction rule create no class event. -/
theorem no_authored_classEvent_of_empty_rules {S : Signature}
    (presentation : UnpositionedPresentation S)
    (empty : presentation.rules = []) (sort : S.Srt)
    (source target : ClassState (authoredSystem presentation sort)) :
    ¬ Nonempty (ClassEvent (authoredSystem presentation sort) source target) := by
  intro event
  obtain ⟨rawSource, rawTarget, _, step, _⟩ :=
    (classEvent_iff_semanticStep (authoredSystem presentation sort)
      source target).mp event
  exact presentation.no_step_of_empty_rules empty rawSource rawTarget step

namespace RhoExample

open Mettapedia.OSLF.Binding.RhoSchema

abbrev system : Mettapedia.GSLT.ProofRelevant.ProofRelevantGSLT :=
  authoredSystem duplicatedCommunication Srt.pr

private def rawSource : State system := ⟨parT commInput commOutput⟩
private def rawTarget : State system := ⟨commTarget⟩

def classSource : ClassState system :=
  (quotientGenerators system).obj rawSource
def classTarget : ClassState system :=
  (quotientGenerators system).obj rawTarget

def firstClassEvent : classSource ⟶ classTarget :=
  (quotientGenerators system).map
    (show rawSource ⟶ rawTarget from firstCommunicationEvent)

def secondClassEvent : classSource ⟶ classTarget :=
  (quotientGenerators system).map
    (show rawSource ⟶ rawTarget from secondCommunicationEvent)

private def ruleIndex (event : classSource ⟶ classTarget) :
    Fin duplicatedCommunication.rules.length :=
  event.occurrence.1

/-- Quotienting equation-equivalent states does not erase the two authored
COMM occurrences. -/
theorem class_events_distinct : firstClassEvent ≠ secondClassEvent := by
  intro equal
  have indices := congrArg ruleIndex equal
  have impossible : (0 : Fin 2) = 1 := indices
  cases impossible

/-- Their one-step histories remain distinct in the free category over
equation classes. -/
theorem class_histories_distinct :
    firstClassEvent.toPath ≠ secondClassEvent.toPath := by
  intro equal
  exact class_events_distinct (eq_of_heq (Quiver.Path.cons.inj equal).2.2)

end RhoExample

end Mettapedia.OSLF.Binding.RewriteClassEventHistory
