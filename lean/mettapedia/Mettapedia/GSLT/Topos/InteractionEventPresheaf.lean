import Mettapedia.GSLT.Core.InteractionEvent
import Mettapedia.TypeTheory.PresheafEventNativeLogic

/-!
# Native certificates for authored interaction presentations

An authored interaction presentation embeds into contextual presheaves with
its actual event carrier and endpoint maps. Dependent postcondition families
may vary with the context, even when the underlying operational theory is
fixed. Certificates return a genuine operational edge and the supplied
witness at its actual target. Completeness is inherited only when the
authored presentation proves event coverage.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.InteractionEvent

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open Mettapedia.TypeTheory.PresheafEventCertificates

universe u
variable {C : Type u} [Category.{u} C] {theory : GSLT.{u}}

namespace InteractionPresentation

variable (presentation : InteractionPresentation.{u, u} theory)

/-- All actual enabled occurrences, indexed by their source states. -/
abbrev eventCarrier := Σ source : theory.Term, presentation.Enabled source

/-- The fixed operational carrier at every observer context. -/
def states (_presentation : InteractionPresentation.{u, u} theory) : Cᵒᵖ ⥤ Type u :=
  (Functor.const Cᵒᵖ).obj theory.Term

/-- The authored events and endpoints, without replacing an event by its
propositional support or inventing an operational edge. -/
def eventSpan : EventSpan (presentation.states (C := C)) (presentation.states (C := C)) where
  events := (Functor.const Cᵒᵖ).obj presentation.eventCarrier
  source :=
    { app _ := TypeCat.ofHom (fun event => event.1)
      naturality _ _ _ := rfl }
  target :=
    { app _ := TypeCat.ofHom (fun event => event.2.target)
      naturality _ _ _ := rfl }

/-- A complete current-state evidence readout, retaining its target. -/
structure CertifiedStep (A : DisplayedFamily (presentation.states (C := C)))
    (world : Cᵒᵖ) (source : theory.Term) where
  target : theory.Term
  event : presentation.Enabled source
  endpoint : event.target = target
  evidence : A.obj ⟨world, target⟩

theorem CertifiedStep.step {A : DisplayedFamily (presentation.states (C := C))}
    {world : Cᵒᵖ} {source : theory.Term}
    (certificate : presentation.CertifiedStep A world source) :
    theory.Step source certificate.target :=
  certificate.endpoint ▸ certificate.event.step

/-- Elimination extracts the actual occurrence and its target certificate
from the native source-indexed sum. -/
def readCertificate (A : DisplayedFamily (presentation.states (C := C)))
    (world : Cᵒᵖ) (source : theory.Term)
    (receipt : ((presentation.eventSpan (C := C)).certificates A).obj ⟨world, source⟩) :
    presentation.CertifiedStep A world source := by
  rcases receipt with ⟨⟨⟨initial, event⟩, evidence⟩, same⟩
  change initial = source at same
  subst initial
  exact ⟨event.target, event, rfl, evidence⟩

/-- Every native certificate supplies a real step and an actual target
witness, independently of event completeness. -/
theorem certificate_sound (A : DisplayedFamily (presentation.states (C := C)))
    (world : Cᵒᵖ) (source : theory.Term)
    (receipt : ((presentation.eventSpan (C := C)).certificates A).obj ⟨world, source⟩) :
    ∃ target : theory.Term, theory.Step source target ∧ Nonempty (A.obj ⟨world, target⟩) := by
  let actual := presentation.readCertificate A world source receipt
  exact ⟨actual.target, actual.step, ⟨actual.evidence⟩⟩

/-- Completeness joins the exact native event support to the independently
defined may-step predicate of the operational theory. -/
theorem certificate_nonempty_iff
    (complete : presentation.Complete)
    (A : DisplayedFamily (presentation.states (C := C)))
    (world : Cᵒᵖ) (source : theory.Term) :
    Nonempty (((presentation.eventSpan (C := C)).certificates A).obj ⟨world, source⟩) ↔
      ∃ target : theory.Term, theory.Step source target ∧ Nonempty (A.obj ⟨world, target⟩) := by
  constructor
  · rintro ⟨receipt⟩
    exact presentation.certificate_sound A world source receipt
  · rintro ⟨target, step, ⟨evidence⟩⟩
    obtain ⟨⟨site, occurrence⟩⟩ := complete step
    let event : presentation.Enabled source := ⟨site, target, occurrence⟩
    exact ⟨(presentation.eventSpan (C := C)).introduce A world ⟨source, event⟩ evidence⟩

end InteractionPresentation

end Mettapedia.GSLT.Core.InteractionEvent
