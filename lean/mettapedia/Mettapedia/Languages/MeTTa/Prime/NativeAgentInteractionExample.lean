import Mettapedia.Languages.MeTTa.Prime.NativeInteractionInterpretation
import Mettapedia.Languages.MeTTa.MeTTaInteractionBind

/-!
# Prime-native revisioned agent interaction

This worked example internalizes the existing revisioned MeTTa interaction
theory in Prime.  Native typing structures the protocol over communication:
the authority revision selects the interaction presentation, exact catalog
occurrences survive as computation inhabitants, and cost/provenance remain
observable even when two events have identical endpoints.

No runtime implementation is assumed.  The example is a Lean-checked
semantic contract for a future Prime/CeTTa interaction provider.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeAgentInteractionExample

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionComposition
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Dynamics.InteractionEventValuation
open Mettapedia.Languages.MeTTa.MeTTaInteraction
open Mettapedia.Languages.MeTTa.MeTTaInteraction.Canary
open Mettapedia.Languages.MeTTa.MeTTaInteractionBind.Canary
open Mettapedia.Languages.MeTTa.StagedReflective
open Mettapedia.Languages.MeTTa.Prime.NativeInteraction
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionInterpretation
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- At one fixed authority revision, first-class native patterns lower to the
corresponding revisioned site theory.  Other native constructors remain
uninterpreted. -/
def siteInterpretation (revision : Bool) :
    EndpointInterpretation (siteGSLT model authorityWorld revision) where
  lower?
    | .pattern pattern => some pattern
    | _ => none

def siteEndpoint (revision : Bool) (pattern : Pattern) :
    (siteInterpretation revision).Endpoint (.pattern pattern) :=
  ⟨pattern, rfl⟩

/-- The revision-indexed Prime computation type for catalog interactions. -/
def siteComputationTy (revision : Bool)
    (source target : StagedReflectiveTm 0 0) : familiesCwF.Ty PrimeContext :=
  (siteInterpretation revision).computationTy
    (presentation model authorityWorld revision) source target

/-- An exact catalog occurrence enters Prime without losing its declaration,
occurrence number, bindings, revision, or endpoints. -/
def internalSiteEvent {revision : Bool}
    {declaration : SiteDecl Bool String Nat} {source target : Pattern}
    (event : SiteEvent model authorityWorld revision declaration source target) :
    familiesCwF.Tm PrimeContext
      (siteComputationTy revision (.pattern source) (.pattern target)) :=
  fun _ =>
    ⟨siteEndpoint revision source, siteEndpoint revision target,
      .cons (site := declaration) event
        (.nil (siteEndpoint revision target).1)⟩

/-- Two Prime computations with equal endpoints but distinct authority
occurrences and costs. -/
def cheapNative : familiesCwF.Tm PrimeContext
    (siteComputationTy false (.pattern a) (.pattern b)) :=
  internalSiteEvent cheapEvent

def dearNative : familiesCwF.Tm PrimeContext
    (siteComputationTy false (.pattern a) (.pattern b)) :=
  internalSiteEvent dearEvent

/-- Prime retains the cheap occurrence's cost and provenance. -/
theorem cheapNative_cost_and_provenance :
    EventPath.grade (presentation model authorityWorld false)
      costAndNameValuation (cheapNative PUnit.unit).2.2 =
        some (1, ["cheap"]) :=
  rfl

/-- The same endpoint type can contain a distinct, dear occurrence. -/
theorem dearNative_cost_and_provenance :
    EventPath.grade (presentation model authorityWorld false)
      costAndNameValuation (dearNative PUnit.unit).2.2 =
        some (2, ["dear"]) :=
  rfl

/-- Endpoint observation alone cannot identify these computations' costs. -/
theorem equal_native_endpoints_do_not_determine_cost :
    (cheapNative PUnit.unit).1.1 = (dearNative PUnit.unit).1.1 ∧
      (cheapNative PUnit.unit).2.1.1 = (dearNative PUnit.unit).2.1.1 ∧
      (1 : Nat) ≠ 2 :=
  ⟨rfl, rfl, by decide⟩

/-! ## Revision-indexed protocol -/

/-- A request may carry only a revision proven to be authorized for the
current catalog.  The equality is data in the native dependent domain, not a
runtime Boolean convention. -/
structure AuthorizedRevision where
  revision : Bool
  authorized : revision = false

def currentRevision : AuthorizedRevision := ⟨false, rfl⟩

/-- The protocol body selects its interaction theory from the revision in
the dependent input. -/
def revisionedAgentBodyTy :
    familiesCwF.Ty
      (familiesCwF.ext PrimeContext (fun _ => AuthorizedRevision)) :=
  fun indexed =>
    (siteComputationTy indexed.2.revision (.pattern a) (.pattern b)) indexed.1

/-- A Prime protocol type whose input proof fixes the authority revision of
the communication it returns. -/
def revisionedAgentTy : familiesCwF.Ty PrimeContext :=
  familiesCwF.pi (fun _ => AuthorizedRevision) revisionedAgentBodyTy

/-- The catalog-backed handler is an inhabitant of the dependent protocol.
Transport along the authorization proof selects the exact false-revision
event presentation. -/
def revisionedAgent : familiesCwF.Tm PrimeContext revisionedAgentTy :=
  fun context revision =>
    match revision with
    | ⟨false, _⟩ => cheapNative context
    | ⟨true, impossible⟩ => nomatch impossible

@[simp] theorem revisionedAgent_uses_authorized_revision :
    EventPath.grade (presentation model authorityWorld false)
      costAndNameValuation
      (revisionedAgent PUnit.unit currentRevision).2.2 =
        some (1, ["cheap"]) :=
  rfl

/-- Negative control: no input can claim that `true` is the authorized
revision of this catalog. -/
theorem true_revision_not_authorized :
    ¬ ∃ authorization : AuthorizedRevision, authorization.revision = true := by
  rintro ⟨authorization, revisionEq⟩
  have impossible : true = false :=
    revisionEq.symm.trans authorization.authorized
  exact Bool.noConfusion impossible

/-- The negative result is semantic too: at revision `true`, this catalog has
no endpoint step at all. -/
theorem true_revision_has_no_step (source target : Pattern) :
    ¬ (siteGSLT model authorityWorld true).Step source target := by
  change ¬ SiteStep model authorityWorld true source target
  simp [SiteStep, authorityWorld, cheap, dear]

/-- A presentation with no semantic steps has no nontrivial exact event
path. -/
private theorem noEventPath_of_noSteps {theory : GSLT}
    (presentation : InteractionPresentation theory)
    (noSteps : ∀ source target, ¬ theory.Step source target)
    {source target : theory.Term} (distinct : source ≠ target) :
    ¬ Nonempty (EventPath presentation source target) := by
  rintro ⟨path⟩
  cases path with
  | nil => exact distinct rfl
  | cons event _ => exact noSteps _ _ (presentation.sound event)

/-- Therefore the same native endpoint pair has no nonempty exact interaction
path at the wrong revision. -/
theorem true_revision_has_no_a_to_b_computation :
    ¬ Nonempty
      ((siteComputationTy true (.pattern a) (.pattern b)) PUnit.unit) := by
  rintro ⟨sourceEndpoint, targetEndpoint, path⟩
  have sourceEndpointEq : sourceEndpoint = siteEndpoint true a :=
    Subsingleton.elim _ _
  have targetEndpointEq : targetEndpoint = siteEndpoint true b :=
    Subsingleton.elim _ _
  subst sourceEndpoint
  subst targetEndpoint
  exact noEventPath_of_noSteps (presentation model authorityWorld true)
    true_revision_has_no_step (by
      change a ≠ b
      simp [a, b]) ⟨path⟩

#print axioms cheapNative_cost_and_provenance
#print axioms dearNative_cost_and_provenance
#print axioms revisionedAgent_uses_authorized_revision
#print axioms true_revision_not_authorized
#print axioms true_revision_has_no_a_to_b_computation

end Mettapedia.Languages.MeTTa.Prime.NativeAgentInteractionExample
