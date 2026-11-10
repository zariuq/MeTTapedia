import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationSource
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.PresentationRuns

/-! # Source events, explicit parse policy, and finite-run correspondence

A source event retains scalar input, CST spans and the actual derivation's
production choices. Its execution evidence is an authored root reduction
following checked argument routing and representation lowering. Erasure
constructs the authorized abstract event; it does not assume one in the
source record. Distinct source representations are kept before erasure.

Parse policy is fixed in the quiver. Reflection of all abstract runs requires
coverage of canonical requests by that policy, proved here for explicit
retention of all parses. No such coverage is required or claimed for an
arbitrary policy, which may reject every candidate.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Source

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.GSLT.Parsing
open PresentationExprSemantics
open Interface Payloads OccurrenceProfile

abbrev ParsePolicy := (input : List Nat) → (tree : CST) → Parses "Proc" input tree → Bool

def allParses : ParsePolicy := fun _ _ _ => true

def noParses : ParsePolicy := fun _ _ _ => false

variable (label : Nat → Term) (decision : Decisions (effect label) (admission label))

structure ParsedEvent (source target : State) where
  input : List Nat
  tree : CST
  parsed : Parses "Proc" input tree
  body : Pattern
  erased : LanguageDefScalarStructural.tree? tree = some body
  routed : ConstructorArgumentRouting.Routed authoredLanguage body body
  candidate : Candidate
  lowered : lowerRequest body = some (request (statePattern source) (firingPattern ⟨source, candidate⟩))
  executed : atState (statePattern target) ∈ rewriteStepWithPremisesUsing (queries label decision).relations
    authoredLanguage (request (statePattern source) (firingPattern ⟨source, candidate⟩))

structure SelectedEvent (keep : ParsePolicy) (source target : State) extends ParsedEvent label decision source target where
  selected : keep input tree parsed = true

/-- Source selection adds permission; it is not inferred from knowledge preservation. -/
def SelectedEvent.abstract {keep : ParsePolicy} {source target : State}
    (event : SelectedEvent label decision keep source target) :
    (effect label).Event (admission label) source target := by
  have facts := (OccurrenceProfile.execution_iff label decision source target
    event.candidate.1 event.candidate.2).mp event.executed
  have admitted := (Execution.admits_iff label event.candidate.1 event.candidate.2 source).mpr facts.1
  exact ⟨event.candidate, (Execution.step label).prepares admitted, admitted, facts.2⟩

@[simp] theorem abstract_firing {keep : ParsePolicy} {source target : State}
    (event : SelectedEvent label decision keep source target) :
    (event.abstract label decision).firing = event.candidate := rfl

structure Object (_label : Nat → Term)
    (_decision : Decisions (effect _label) (admission _label)) (_keep : ParsePolicy) where
  state : State

instance sourceQuiver (keep : ParsePolicy) : Quiver (Object label decision keep) where
  Hom source target := SelectedEvent label decision keep source.state target.state

def erase (keep : ParsePolicy) : Object label decision keep ⥤q
    EffectCore.EventObject (effect label) (admission label) where
  obj source := source.state
  map event := event.abstract label decision

/-- A policy's coverage obligation concerns only admitted abstract events.
The source witness and its acceptance are both explicit. -/
def CanonicalCoverage (keep : ParsePolicy) : Prop :=
  ∀ {source target : State} (event : (effect label).Event (admission label) source target),
    ∃ (tree : CST) (parsed : Parses "Proc" (requestInput source event.firing) tree),
      LanguageDefScalarStructural.tree? tree =
        some (request (statePattern source) (firingPattern ⟨source, event.firing⟩)) ∧
      keep (requestInput source event.firing) tree parsed = true

theorem allParses_coverage : CanonicalCoverage label allParses := by
  intro source target event
  obtain ⟨tree, erased, ⟨parsed⟩⟩ := canonical_request_source source event.firing
  exact ⟨tree, parsed, erased, rfl⟩

/-- The canonical source is an actual parse and actual root reduction. -/
theorem lift_event {keep : ParsePolicy} (coverage : CanonicalCoverage label keep)
    {source target : State} (event : (effect label).Event (admission label) source target) :
    ∃ lifted : SelectedEvent label decision keep source target,
      lifted.abstract label decision = event ∧ lifted.input = requestInput source event.firing := by
  obtain ⟨tree, parsed, erased, kept⟩ := coverage event
  have valid := (Execution.admits_iff label event.firing.1 event.firing.2 source).mp event.permitted
  let lifted : SelectedEvent label decision keep source target := {
    input := requestInput source event.firing
    tree := tree
    parsed := parsed
    body := request (statePattern source) (firingPattern ⟨source, event.firing⟩)
    erased := erased
    routed := source_arguments_routed parsed erased
    candidate := event.firing
    lowered := lower_canonical source event.firing
    executed := (OccurrenceProfile.execution_iff label decision source target
      event.firing.1 event.firing.2).mpr ⟨valid, event.target_eq⟩
    selected := kept }
  refine ⟨lifted, ?_, rfl⟩
  cases event
  rfl

theorem erase_star_surjective {keep : ParsePolicy} (coverage : CanonicalCoverage label keep)
    (source : Object label decision keep) :
    Function.Surjective ((erase label decision keep).star source) := by
  rintro ⟨target, event⟩
  obtain ⟨lifted, same, _⟩ := lift_event label decision coverage event
  refine ⟨⟨⟨target⟩, lifted⟩, ?_⟩
  change Sigma.mk target (lifted.abstract label decision) = Sigma.mk target event
  rw [same]

/-- Every admitted finite run has a source realization under a policy that
covers canonical requests. Erasure preserves every event in its original order. -/
theorem erase_paths_surjective {keep : ParsePolicy} (coverage : CanonicalCoverage label keep)
    (source : Object label decision keep) :
    Function.Surjective ((erase label decision keep).pathStar source) :=
  Prefunctor.pathStar_surjective _ (erase_star_surjective label decision coverage) source

theorem all_source_runs (source : Object label decision allParses) :
    Function.Surjective ((erase label decision allParses).pathStar source) :=
  erase_paths_surjective label decision (allParses_coverage label) source

theorem erase_composition {keep : ParsePolicy} {source middle target : Object label decision keep}
    (first : Quiver.Path source middle) (second : Quiver.Path middle target) :
    (erase label decision keep).mapPath (first.comp second) =
      ((erase label decision keep).mapPath first).comp ((erase label decision keep).mapPath second) :=
  Prefunctor.mapPath_comp _ first second

theorem noParses_no_event (source target : State) :
    ¬ Nonempty (SelectedEvent label decision noParses source target) := by
  rintro ⟨event⟩
  cases event.selected

#print axioms SelectedEvent.abstract
#print axioms lift_event
#print axioms erase_paths_surjective
#print axioms all_source_runs
#print axioms noParses_no_event

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Source
