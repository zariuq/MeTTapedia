import Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderExecution
import Mettapedia.GSLT.Topos.InteractionEventPresheaf

/-!
# Native certificates for selected rho communication occurrences

Each site is an actual parallel header inventory. An event retains the
selected input and output positions, sorting and scope evidence, and both
supplied endpoint equations. Header execution constructs the corresponding
step in the existing authored rho theory. A native postcondition certificate
retains all this event data beside the witness at the actual target.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderInteractionCertificates

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open HeaderInversion HeaderExecution ParameterizedRewriteSystem

variable (free : FreeSortContext)

/-- A positional authored communication occurrence between supplied sorted
representatives; equal endpoint processes need not give equal selections. -/
structure Occurrence (heads : List Header) (source target : Process free) where
  typed : ∀ head ∈ heads, head.Typed free
  safe : ∀ head ∈ heads, head.Safe
  selected : Selection heads
  sourceEquation : StructuralCongruence source.val (parallel heads)
  targetEquation : StructuralCongruence selected.contractum target.val

/-- The selected positions generate the operational edge independently of
any dependent specification or native evidence family. -/
theorem Occurrence.step {free : FreeSortContext} {heads : List Header}
    {source target : Process free} (event : Occurrence free heads source target) :
    (theory free).Step source target :=
  supplied_selection_step heads event.typed event.safe event.selected source target
    event.sourceEquation event.targetEquation

/-- The communication presentation is occurrence sensitive and sound. It
selects the header profile; no whole-theory coverage is assumed. -/
def presentation : InteractionPresentation (theory free) where
  Site := List Header
  Event := Occurrence free
  sound := Occurrence.step

/-- Any supplied selection and its native sorted endpoints produce an
enabled event whose positional readout is exactly the supplied selection. -/
def selectedEvent (heads : List Header)
    (typed : ∀ head ∈ heads, head.Typed free) (safe : ∀ head ∈ heads, head.Safe)
    (selected : Selection heads) :
    (presentation free).Enabled (headerProcess heads typed safe) where
  site := heads
  target := contractumProcess heads typed safe selected
  evidence :=
    { typed := typed
      safe := safe
      selected := selected
      sourceEquation := .refl _
      targetEquation := .refl _ }

theorem selectedEvent_occurrence (heads : List Header)
    (typed : ∀ head ∈ heads, head.Typed free) (safe : ∀ head ∈ heads, head.Safe)
    (selected : Selection heads) :
    (selectedEvent free heads typed safe selected).evidence.selected = selected := rfl

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderInteractionCertificates
