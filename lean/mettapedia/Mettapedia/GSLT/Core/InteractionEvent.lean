import Mettapedia.GSLT.Core.GSLT

/-!
# Proof-relevant interaction events

A semantic step records only its endpoints.  An interaction event additionally
records the authored site and the evidence for the particular occurrence that
fired.  Controllers consume these events; they do not manufacture semantic
steps.

Completeness is deliberately separate.  A presentation may soundly expose
only the interactions relevant to one observer or physical profile.  Cost is
also separate: it decorates an event and erases without changing the step that
the event authorizes.
-/

namespace Mettapedia.GSLT.Core.InteractionEvent

open Mettapedia.GSLT

universe uSite uEvent uRevision uMemory uCost

/-- An open family of authored interaction sites over one GSLT.  Evidence is
`Type`-valued so distinct occurrences with equal endpoints remain distinct. -/
structure InteractionPresentation (theory : GSLT) where
  Site : Type uSite
  Event : Site → theory.Term → theory.Term → Type uEvent
  sound : ∀ {site source target}, Event site source target →
    theory.Step source target

namespace InteractionPresentation

variable {theory : GSLT}

/-- Every semantic step has at least one presented interaction event.  This is
not part of sound presentation: partial, observer-indexed presentations remain
useful and honest. -/
def Complete (presentation : InteractionPresentation.{uSite, uEvent} theory) :
    Prop :=
  ∀ {source target}, theory.Step source target →
    Nonempty (Σ site, presentation.Event site source target)

/-- One enabled, occurrence-specific event at a fixed source. -/
structure Enabled
    (presentation : InteractionPresentation.{uSite, uEvent} theory)
    (source : theory.Term) where
  site : presentation.Site
  target : theory.Term
  evidence : presentation.Event site source target

namespace Enabled

variable {presentation : InteractionPresentation.{uSite, uEvent} theory}
  {source : theory.Term}

/-- Endpoint erasure forgets site and occurrence evidence, but retains a
genuine semantic step. -/
def erase (event : presentation.Enabled source) : theory.LabeledStep where
  source := source
  target := event.target
  step := presentation.sound event.evidence

@[simp] theorem erase_source (event : presentation.Enabled source) :
    event.erase.source = source := rfl

@[simp] theorem erase_target (event : presentation.Enabled source) :
    event.erase.target = event.target := rfl

theorem step (event : presentation.Enabled source) :
    theory.Step source event.target :=
  presentation.sound event.evidence

end Enabled

/-- A versioned catalog makes the authority against which an event was
checked explicit.  Revisions select presentations; they are not mutable
global state hidden behind the checker. -/
structure Catalog (theory : GSLT) where
  Revision : Type uRevision
  presentationAt : Revision → InteractionPresentation.{uSite, uEvent} theory

namespace Catalog

variable (catalog : Catalog.{uRevision, uSite, uEvent} theory)

/-- An enabled event tied to one exact authority revision. -/
structure EnabledAt (revision : catalog.Revision) (source : theory.Term) where
  event : (catalog.presentationAt revision).Enabled source

namespace EnabledAt

variable {catalog : Catalog.{uRevision, uSite, uEvent} theory}
  {revision : catalog.Revision} {source : theory.Term}

def erase (event : catalog.EnabledAt revision source) : theory.LabeledStep :=
  event.event.erase

theorem step (event : catalog.EnabledAt revision source) :
    theory.Step source event.event.target :=
  event.event.step

end EnabledAt

end Catalog

/-! ## Continuations and controllers -/

/-- A control state keeps policy memory beside the current semantic term. -/
structure ControlState (theory : GSLT) (Memory : Type uMemory) where
  term : theory.Term
  memory : Memory

/-- A selector may inspect memory and the current term, but its result must be
an authenticated event of the cited revision.  Its type therefore prevents it
from proposing an unauthorized endpoint. -/
structure Selector
    (catalog : Catalog.{uRevision, uSite, uEvent} theory)
    (Memory : Type uMemory) where
  choose : (revision : catalog.Revision) → (memory : Memory) →
    (source : theory.Term) → Option (catalog.EnabledAt revision source)

/-- A handler decides only how memory continues after an authenticated event.
The semantic target is supplied by the event, never by the handler. -/
structure Handler
    (catalog : Catalog.{uRevision, uSite, uEvent} theory)
    (Memory : Type uMemory) where
  resume : {revision : catalog.Revision} → {source : theory.Term} →
    Memory → catalog.EnabledAt revision source → Memory

/-- One selected interaction followed by its authored continuation. -/
def tick
    {catalog : Catalog.{uRevision, uSite, uEvent} theory}
    {Memory : Type uMemory}
    (selector : Selector catalog Memory) (handler : Handler catalog Memory)
    (revision : catalog.Revision) (state : ControlState theory Memory) :
    Option (ControlState theory Memory) :=
  (selector.choose revision state.memory state.term).map fun selected =>
    { term := selected.event.target
      memory := handler.resume state.memory selected }

/-- Every successful controlled tick is authorized by the cited semantic
presentation.  The selector and handler contribute no step authority. -/
theorem tick_sound
    {catalog : Catalog.{uRevision, uSite, uEvent} theory}
    {Memory : Type uMemory}
    (selector : Selector catalog Memory) (handler : Handler catalog Memory)
    (revision : catalog.Revision) (state next : ControlState theory Memory)
    (result : tick selector handler revision state = some next) :
    theory.Step state.term next.term := by
  unfold tick at result
  cases chosen : selector.choose revision state.memory state.term with
  | none => simp [chosen] at result
  | some selected =>
      simp only [chosen, Option.map_some, Option.some.injEq] at result
      rw [← result]
      exact selected.step

/-! ## Event-indexed cost -/

/-- A cost assignment is indexed by occurrence evidence, not merely by step
endpoints.  Equal-endpoint events may therefore carry different costs. -/
structure EventCost
    (presentation : InteractionPresentation.{uSite, uEvent} theory)
    (Cost : Type uCost) where
  cost : {site : presentation.Site} → {source target : theory.Term} →
    presentation.Event site source target → Cost

namespace EventCost

variable {presentation : InteractionPresentation.{uSite, uEvent} theory}
  {Cost : Type uCost}

/-- Endpoint-only accounting would factor every event cost through source and
target. -/
def FactorsThroughEndpoints (valuation : EventCost presentation Cost) : Prop :=
  ∃ endpointCost : theory.Term → theory.Term → Cost,
    ∀ {site source target}
      (event : presentation.Event site source target),
      endpointCost source target = valuation.cost event

/-- Parallel occurrences with the same endpoints and different costs refute
endpoint-only accounting. -/
theorem not_factorsThroughEndpoints_of_parallel_costs
    (valuation : EventCost presentation Cost)
    {firstSite secondSite : presentation.Site}
    {source target : theory.Term}
    (first : presentation.Event firstSite source target)
    (second : presentation.Event secondSite source target)
    (different : valuation.cost first ≠ valuation.cost second) :
    ¬ valuation.FactorsThroughEndpoints := by
  rintro ⟨endpointCost, factors⟩
  apply different
  exact (factors first).symm.trans (factors second)

/-- Cost observation erases to precisely the same authorized step. -/
theorem erasure_preserves_step
    (_valuation : EventCost presentation Cost)
    {source : theory.Term} (event : presentation.Enabled source) :
    theory.Step source event.target := by
  exact event.step

end EventCost

end InteractionPresentation

/-! ## Separating canaries -/

namespace Canary

/-- A one-state theory with two occurrence-distinct self-loop sites. -/
def loopTheory : GSLT where
  Term := Unit
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun _ _ => True
  rewrites_resp_left := by
    intro source source' target _ _
    exact ⟨target, trivial, rfl⟩
  rewrites_resp_right := by
    intro source target target' _ _
    trivial

/-- Two names for sites with the same endpoints. -/
inductive LoopSite where
  | cheap
  | dear

def loopPresentation : InteractionPresentation loopTheory where
  Site := LoopSite
  Event := fun _ _ _ => Unit
  sound := fun _ => trivial

def loopCost : InteractionPresentation.EventCost loopPresentation Nat where
  cost := fun {site} {_source _target} _ =>
    match site with
    | .cheap => 1
    | .dear => 2

def cheapEvent : loopPresentation.Enabled () where
  site := .cheap
  target := ()
  evidence := ()

def dearEvent : loopPresentation.Enabled () where
  site := .dear
  target := ()
  evidence := ()

theorem parallel_events_authorize_same_step :
    cheapEvent.erase.target = dearEvent.erase.target ∧
      loopTheory.Step cheapEvent.erase.source cheapEvent.erase.target ∧
      loopTheory.Step dearEvent.erase.source dearEvent.erase.target := by
  exact ⟨rfl, trivial, trivial⟩

theorem parallel_event_costs_are_not_endpoint_costs :
    ¬ loopCost.FactorsThroughEndpoints := by
  apply loopCost.not_factorsThroughEndpoints_of_parallel_costs
    (first := cheapEvent.evidence) (second := dearEvent.evidence)
  decide

def loopCatalog : InteractionPresentation.Catalog loopTheory where
  Revision := Unit
  presentationAt := fun _ => loopPresentation

def cheapSelector : InteractionPresentation.Selector loopCatalog Nat where
  choose := fun _ _ _ => some ⟨cheapEvent⟩

def countingHandler : InteractionPresentation.Handler loopCatalog Nat where
  resume := fun memory _ => memory + 1

theorem selected_continuation_is_authorized :
    InteractionPresentation.tick cheapSelector countingHandler ()
        ⟨(), 0⟩ = some ⟨(), 1⟩ ∧
      loopTheory.Step () () := by
  exact ⟨rfl, trivial⟩

end Canary

end Mettapedia.GSLT.Core.InteractionEvent
