import Mettapedia.GSLT.Core.GSLT
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic

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

-- Site and event carriers have independent bounds, as in a large category.
set_option linter.checkUnivs false in
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

-- Revisions, sites and occurrence evidence need not have equal universe bounds.
set_option linter.checkUnivs false in
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

/-! ## Interactive theories and cuts as sites

Kernel iGSLT is a GSLT together with a named meeting site. A cut is extra
combinators plus a contraction *step*; combinators alone are not a site.
Meredith's `InteractionCutPresentation` is those four combinators. LanguageDef
`IGSLT` is a spelling of this object, not a second theory.
-/

/-- A rewrite theory with a named family of meeting sites. Completeness of
the site is optional. -/
structure Interactive where
  theory : GSLT
  site : InteractionPresentation theory

namespace Interactive

/-- Forget the site; the underlying rewrite theory remains. -/
def erase (I : Interactive) : GSLT := I.theory

@[simp] theorem erase_theory (I : Interactive) : I.erase = I.theory := rfl

/-- A map of interactive theories: a bisimilarity-preserving term map
together with a site map and an event map lying over it. Parallel sites
with equal endpoints remain distinct if the event map says so. -/
structure Morphism (source target : Interactive) where
  base : GSLT.Morphism source.theory target.theory
  mapSite : source.site.Site → target.site.Site
  mapEvent :
    ∀ {site : source.site.Site} {s t : source.theory.Term},
      source.site.Event site s t →
        target.site.Event (mapSite site) (base.toFun s) (base.toFun t)

namespace Morphism

def id (I : Interactive) : Morphism I I where
  base := GSLT.Morphism.id I.theory
  mapSite := _root_.id
  mapEvent := fun event => event

def comp {first second third : Interactive}
    (left : Morphism first second) (right : Morphism second third) :
    Morphism first third where
  base := GSLT.Morphism.comp right.base left.base
  mapSite := right.mapSite ∘ left.mapSite
  mapEvent := fun event => right.mapEvent (left.mapEvent event)

theorem id_comp {source target : Interactive} (f : Morphism source target) :
    comp (id source) f = f := by
  cases f
  rfl

theorem comp_id {source target : Interactive} (f : Morphism source target) :
    comp f (id target) = f := by
  cases f
  rfl

theorem assoc {I J K L : Interactive}
    (f : Morphism I J) (g : Morphism J K) (h : Morphism K L) :
    comp (comp f g) h = comp f (comp g h) :=
  rfl

end Morphism

instance : CategoryTheory.Category Interactive where
  Hom := Morphism
  id := Morphism.id
  comp := fun f g => Morphism.comp f g
  id_comp := fun f => Morphism.id_comp f
  comp_id := fun f => Morphism.comp_id f
  assoc := fun f g h => Morphism.assoc f g h

/-- Forgetting the site is functorial. The term map is the underlying
behavioral GSLT morphism. -/
def eraseFunctor : CategoryTheory.Functor Interactive GSLT where
  obj := erase
  map := fun f => f.base
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

end Interactive

/-- Cut combinators: contact, two co-introductions, and a residual pair.
This is Meredith's interaction-cut presentation. It is not yet a site. -/
structure CutCombinators (theory : GSLT) where
  contact : theory.Term → theory.Term → theory.Term
  leftIntro : theory.Term → theory.Term → theory.Term
  rightIntro : theory.Term → theory.Term → theory.Term
  contract : theory.Term → theory.Term → theory.Term → theory.Term →
    theory.Term × theory.Term

/-- A cut is combinators together with a contraction step. The residual is
determined by the two continuations; no extra binder name is quantified
outside the introductions. Meredith's four-field presentation is the
combinator shadow (`toCombinators`). -/
structure SoundCut (theory : GSLT) extends CutCombinators theory where
  residual : theory.Term → theory.Term → theory.Term
  contract_determines_residual :
    ∀ subject name body payload,
      (contract subject name body payload).1 = residual body payload
  contract_step :
    ∀ subject body payload,
      theory.Step
        (contact (rightIntro subject payload) (leftIntro subject body))
        (residual body payload)

namespace SoundCut

variable {theory : GSLT}

/-- Witness that a source/target pair is a contraction of a particular cut. -/
structure Witness (c : SoundCut theory) (source target : theory.Term) where
  subject : theory.Term
  body : theory.Term
  payload : theory.Term
  source_eq :
    source = c.contact (c.rightIntro subject payload) (c.leftIntro subject body)
  target_eq : target = c.residual body payload

/-- A sound cut *is* an interaction site: one named meeting, evidence the
particular introductions that contracted. -/
def asPresentation (c : SoundCut theory) : InteractionPresentation theory where
  Site := Unit
  Event := fun _ source target => Witness c source target
  sound := by
    intro _ source target w
    have step := c.contract_step w.subject w.body w.payload
    rw [← w.source_eq, ← w.target_eq] at step
    exact step

/-- The kernel iGSLT of a sound cut. -/
def toInteractive (c : SoundCut theory) : Interactive where
  theory := theory
  site := c.asPresentation

@[simp] theorem toInteractive_erase (c : SoundCut theory) :
    c.toInteractive.erase = theory :=
  rfl

/-- Meredith's four combinators, with the extra name argument unused. -/
def toCombinators (c : SoundCut theory) : CutCombinators theory :=
  c.toCutCombinators

/-- The enabled contraction at a concrete cut redex. -/
def enable (c : SoundCut theory)
    (subject body payload : theory.Term) :
    (c.asPresentation).Enabled
      (c.contact (c.rightIntro subject payload) (c.leftIntro subject body)) where
  site := ()
  target := c.residual body payload
  evidence := {
    subject := subject
    body := body
    payload := payload
    source_eq := rfl
    target_eq := rfl
  }

theorem enable_steps (c : SoundCut theory)
    (subject body payload : theory.Term) :
    theory.Step
      (c.contact (c.rightIntro subject payload) (c.leftIntro subject body))
      (c.residual body payload) :=
  (c.enable subject body payload).step

theorem enable_erases (c : SoundCut theory)
    (subject body payload : theory.Term) :
    (c.enable subject body payload).erase.target =
      c.residual body payload :=
  rfl

end SoundCut

/-! ## Kernel cut theories

A distinguished cut site on an interactive theory. Morphisms must preserve
that site. This is the semantic image of a LanguageDef `CIGSLT` cut.
-/

structure KernelCut where
  host : Interactive
  cutSite : host.site.Site

namespace KernelCut

def forget (C : KernelCut) : Interactive := C.host

structure Morphism (source target : KernelCut) where
  host : Interactive.Morphism source.host target.host
  preservesCut : host.mapSite source.cutSite = target.cutSite

namespace Morphism

def id (C : KernelCut) : Morphism C C where
  host := Interactive.Morphism.id C.host
  preservesCut := rfl

def comp {I J K : KernelCut} (left : Morphism I J) (right : Morphism J K) :
    Morphism I K where
  host := Interactive.Morphism.comp left.host right.host
  preservesCut := by
    change right.host.mapSite (left.host.mapSite I.cutSite) = K.cutSite
    rw [left.preservesCut, right.preservesCut]

end Morphism

instance : CategoryTheory.Category KernelCut where
  Hom := Morphism
  id := Morphism.id
  comp := fun f g => Morphism.comp f g
  id_comp := fun f => by
    cases f
    rfl
  comp_id := fun f => by
    cases f
    rfl
  assoc := fun f g h => by
    cases f; cases g; cases h
    rfl

def forgetFunctor : CategoryTheory.Functor KernelCut Interactive where
  obj := forget
  map := fun f => f.host
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

end KernelCut

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

/-! A contraction is a site only once it is a step. -/

inductive MeetTerm where
  | send
  | recv
  | meet
  | done

def meetTheory : GSLT where
  Term := MeetTerm
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target => source = .meet ∧ target = .done
  rewrites_resp_left := by
    intro source source' target related step
    exact ⟨target, related ▸ step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step related
    exact related ▸ step

def meetCut : SoundCut meetTheory where
  contact := fun _ _ => .meet
  leftIntro := fun _ _ => .recv
  rightIntro := fun _ _ => .send
  contract := fun _ _ _ _ => (.done, .done)
  residual := fun _ _ => .done
  contract_determines_residual := fun _ _ _ _ => rfl
  contract_step := fun _ _ _ => ⟨rfl, rfl⟩

theorem meet_cut_erases_to_theory :
    meetCut.toInteractive.erase = meetTheory :=
  rfl

theorem meet_cut_enables_contraction :
    (meetCut.enable .send .recv .send).erase.target = .done ∧
      meetTheory.Step .meet .done :=
  ⟨rfl, meetCut.contract_step .send .recv .send⟩

def loopInteractive : Interactive where
  theory := loopTheory
  site := loopPresentation

def swapParallelSites : Interactive.Morphism loopInteractive loopInteractive where
  base := GSLT.Morphism.id loopTheory
  mapSite := fun
    | .cheap => .dear
    | .dear => .cheap
  mapEvent := fun _ => ()

theorem swap_parallel_sites_changes_cost :
    loopCost.cost (site := .cheap) (source := ()) (target := ()) () ≠
      loopCost.cost (site := swapParallelSites.mapSite .cheap)
        (source := ()) (target := ()) () := by
  decide

/-- Combinators without `contract_step` are not a `SoundCut`; the type
boundary is the negative. -/
def meetCombinators : CutCombinators meetTheory :=
  meetCut.toCombinators

#print axioms meet_cut_erases_to_theory
#print axioms meet_cut_enables_contraction
#print axioms SoundCut.enable_steps
#print axioms Interactive.eraseFunctor
#print axioms KernelCut.forgetFunctor
#print axioms swap_parallel_sites_changes_cost

end Canary

end Mettapedia.GSLT.Core.InteractionEvent
