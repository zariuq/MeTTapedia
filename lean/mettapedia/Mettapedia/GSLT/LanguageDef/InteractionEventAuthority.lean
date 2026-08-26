import Mettapedia.GSLT.Core.InteractionEvent
import Mettapedia.GSLT.LanguageDef.CertificateGSLTFiniteTraceAuthority

/-!
# NIK authorities generated from proof-relevant interaction events

An interaction presentation exposes occurrence-specific evidence for semantic
steps.  This module turns that evidence into the local authority expected by
the generic finite-trace checker.  The construction is independent of Need,
MeTTa, MM2, or any controller.

The certificate stores the source together with one enabled event.  Replay
checks that both submitted endpoints equal the endpoints carried by that
event.  Controllers therefore remain evidence producers: neither selection
nor scheduling contributes semantic authority.
-/

namespace Mettapedia.GSLT.LanguageDef.InteractionEventAuthority

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.Core.InteractionEvent.InteractionPresentation
open Mettapedia.GSLT.LanguageDef.CertificateGSLT

universe uAuthority uSite uEvent uIdentity

/-- A local certificate carries one occurrence-specific enabled event and the
source at which its evidence is indexed. -/
structure EventCertificate {theory : GSLT}
    (presentation : InteractionPresentation.{uSite, uEvent} theory) where
  source : theory.Term
  event : presentation.Enabled source

/-! ## Exact executable endpoint identity -/

/-- An executable identity for semantic terms whose equality is exact rather
than hash-assumed.  A serialized realization may use canonical bytes, a
collision-free structural key, or another finite representation, but it must
prove that equal identities imply equal semantic terms. -/
structure ExactEndpointIdentity (Term : Type*) where
  Identity : Type uIdentity
  decEq : DecidableEq Identity
  identify : Term -> Identity
  identify_injective : Function.Injective identify

namespace ExactEndpointIdentity

variable {Term : Type*}

/-- Exact endpoint identity induces executable equality on semantic terms. -/
def termDecidableEq (identity : ExactEndpointIdentity.{uIdentity} Term) :
    DecidableEq Term := by
  intro left right
  letI := identity.decEq
  by_cases same : identity.identify left = identity.identify right
  · exact isTrue (identity.identify_injective same)
  · exact isFalse fun equal => same (congrArg identity.identify equal)

end ExactEndpointIdentity

/-- Replay endpoint equality through an admitted exact identity.  This form
is useful when semantic states contain functions or other fields whose raw
Lean equality is not executable. -/
def checkEventCertificateByIdentity {theory : GSLT}
    (identity : ExactEndpointIdentity.{uIdentity} theory.Term)
    {presentation : InteractionPresentation.{uSite, uEvent} theory}
    (claim : StepClaim theory) (certificate : EventCertificate presentation) :
    Bool := by
  letI := identity.decEq
  exact decide
    (identity.identify claim.source = identity.identify certificate.source ∧
      identity.identify claim.target =
        identity.identify certificate.event.target)

/-- Exact identity checking plus occurrence evidence is sound. -/
theorem checkEventCertificateByIdentity_sound {theory : GSLT}
    (identity : ExactEndpointIdentity.{uIdentity} theory.Term)
    {presentation : InteractionPresentation.{uSite, uEvent} theory}
    {claim : StepClaim theory} {certificate : EventCertificate presentation}
    (accepted :
      checkEventCertificateByIdentity identity claim certificate = true) :
    claim.Meaning := by
  letI := identity.decEq
  have endpointIdentities :
      identity.identify claim.source =
          identity.identify certificate.source ∧
        identity.identify claim.target =
          identity.identify certificate.event.target :=
    of_decide_eq_true accepted
  have sourceEqual := identity.identify_injective endpointIdentities.1
  have targetEqual := identity.identify_injective endpointIdentities.2
  unfold StepClaim.Meaning
  rw [sourceEqual, targetEqual]
  exact certificate.event.step

/-- Check that the submitted claim is exactly the edge carried by the event.
The occurrence evidence itself already authorizes that edge. -/
def checkEventCertificate {theory : GSLT} [DecidableEq theory.Term]
    {presentation : InteractionPresentation.{uSite, uEvent} theory}
    (claim : StepClaim theory) (certificate : EventCertificate presentation) :
    Bool :=
  decide (claim.source = certificate.source ∧
    claim.target = certificate.event.target)

/-- Endpoint checking plus occurrence evidence is sound for the admitted
GSLT step relation. -/
theorem checkEventCertificate_sound {theory : GSLT}
    [DecidableEq theory.Term]
    {presentation : InteractionPresentation.{uSite, uEvent} theory}
    {claim : StepClaim theory} {certificate : EventCertificate presentation}
    (accepted : checkEventCertificate claim certificate = true) :
    claim.Meaning := by
  have endpoints : claim.source = certificate.source ∧
      claim.target = certificate.event.target :=
    of_decide_eq_true accepted
  unfold StepClaim.Meaning
  rw [endpoints.1, endpoints.2]
  exact certificate.event.step

/-- Every proof-relevant interaction presentation induces a local NIK step
authority. -/
def stepAuthority {AuthorityId : Type uAuthority} (authorityId : AuthorityId)
    {theory : GSLT} [DecidableEq theory.Term]
    (presentation : InteractionPresentation.{uSite, uEvent} theory) :
    StepAuthority AuthorityId theory where
  id := authorityId
  Certificate := EventCertificate presentation
  check := checkEventCertificate
  sound := checkEventCertificate_sound

/-- Every interaction presentation also induces a local authority from an
admitted exact endpoint identity, without requiring raw term equality to be
decidable. -/
def stepAuthorityByIdentity {AuthorityId : Type uAuthority}
    (authorityId : AuthorityId) {theory : GSLT}
    (identity : ExactEndpointIdentity.{uIdentity} theory.Term)
    (presentation : InteractionPresentation.{uSite, uEvent} theory) :
    StepAuthority AuthorityId theory where
  id := authorityId
  Certificate := EventCertificate presentation
  check := checkEventCertificateByIdentity identity
  sound := checkEventCertificateByIdentity_sound identity

/-- Presentation completeness is exactly what makes the generated local
authority certificate-complete. -/
theorem stepAuthority_complete {AuthorityId : Type uAuthority}
    (authorityId : AuthorityId) {theory : GSLT} [DecidableEq theory.Term]
    {presentation : InteractionPresentation.{uSite, uEvent} theory}
    (complete : presentation.Complete) :
    (stepAuthority authorityId presentation).Complete := by
  intro claim meaningful
  obtain ⟨⟨site, evidence⟩⟩ := complete meaningful
  let certificate : EventCertificate presentation :=
    { source := claim.source
      event :=
        { site := site
          target := claim.target
          evidence := evidence } }
  exact ⟨certificate, by simp [stepAuthority, checkEventCertificate, certificate]⟩

/-- Complete interaction presentation gives certificate completeness for the
identity-keyed authority as well. -/
theorem stepAuthorityByIdentity_complete {AuthorityId : Type uAuthority}
    (authorityId : AuthorityId) {theory : GSLT}
    (identity : ExactEndpointIdentity.{uIdentity} theory.Term)
    {presentation : InteractionPresentation.{uSite, uEvent} theory}
    (complete : presentation.Complete) :
    (stepAuthorityByIdentity authorityId identity presentation).Complete := by
  intro claim meaningful
  obtain ⟨⟨site, evidence⟩⟩ := complete meaningful
  let certificate : EventCertificate presentation :=
    { source := claim.source
      event :=
        { site := site
          target := claim.target
          evidence := evidence } }
  letI := identity.decEq
  exact ⟨certificate, by
    simp [stepAuthorityByIdentity, checkEventCertificateByIdentity,
      certificate]⟩

/-- Free finite-trace closure of the event authority. -/
def finiteTraceAuthority {AuthorityId : Type uAuthority}
    (authorityId : AuthorityId) {theory : GSLT} [DecidableEq theory.Term]
    (presentation : InteractionPresentation.{uSite, uEvent} theory) :=
  CertificateGSLT.finiteTraceAuthority (stepAuthority authorityId presentation)

/-- Free finite-trace closure using exact endpoint identity for both local
links and the final endpoint check. -/
def finiteTraceAuthorityByIdentity {AuthorityId : Type uAuthority}
    (authorityId : AuthorityId) {theory : GSLT}
    (identity : ExactEndpointIdentity.{uIdentity} theory.Term)
    (presentation : InteractionPresentation.{uSite, uEvent} theory) := by
  letI := identity.termDecidableEq
  exact CertificateGSLT.finiteTraceAuthority
    (stepAuthorityByIdentity authorityId identity presentation)

/-- For a complete presentation, certificate existence is exactly finite
reachability in the admitted GSLT. -/
theorem finiteTraceAuthority_correspondence
    {AuthorityId : Type uAuthority} (authorityId : AuthorityId)
    {theory : GSLT} [DecidableEq theory.Term]
    {presentation : InteractionPresentation.{uSite, uEvent} theory}
    (complete : presentation.Complete) (claim : TraceClaim theory) :
    (Exists fun certificate :
        (finiteTraceAuthority authorityId presentation).Certificate =>
      (finiteTraceAuthority authorityId presentation).check claim certificate =
        true) ↔ claim.Meaning := by
  exact CertificateGSLT.finiteTraceAuthority_correspondence
    (stepAuthority authorityId presentation)
    (stepAuthority_complete authorityId complete) claim

/-- With exact endpoint identity, certificate existence is again precisely
finite reachability. -/
theorem finiteTraceAuthorityByIdentity_correspondence
    {AuthorityId : Type uAuthority} (authorityId : AuthorityId)
    {theory : GSLT}
    (identity : ExactEndpointIdentity.{uIdentity} theory.Term)
    {presentation : InteractionPresentation.{uSite, uEvent} theory}
    (complete : presentation.Complete) (claim : TraceClaim theory) :
    (Exists fun certificate :
        (finiteTraceAuthorityByIdentity authorityId identity
          presentation).Certificate =>
      (finiteTraceAuthorityByIdentity authorityId identity presentation).check
        claim certificate = true) ↔ claim.Meaning := by
  letI := identity.termDecidableEq
  exact CertificateGSLT.finiteTraceAuthority_correspondence
    (stepAuthorityByIdentity authorityId identity presentation)
    (stepAuthorityByIdentity_complete authorityId identity complete) claim

/-! ## Separating canaries -/

namespace Canary

open Mettapedia.GSLT.Core.InteractionEvent.Canary

inductive AuthorityId where
  | loop
deriving DecidableEq, Repr

local instance loopTermDecidableEq : DecidableEq loopTheory.Term := by
  change DecidableEq Unit
  infer_instance

def cheapCertificate : EventCertificate loopPresentation where
  source := ()
  event := cheapEvent

theorem cheap_event_is_accepted :
    (stepAuthority AuthorityId.loop loopPresentation).check
      { source := (), target := () } cheapCertificate = true := by
  decide

/-- A two-state theory used to ensure that claim endpoints are replayed rather
than inferred from the mere presence of evidence. -/
def oneWayTheory : GSLT where
  Term := Bool
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target => source = false ∧ target = true
  rewrites_resp_left := by
    intro source source' target equal rewrite
    subst source'
    exact ⟨target, rewrite, rfl⟩
  rewrites_resp_right := by
    intro source target target' rewrite equal
    subst target'
    exact rewrite

structure OneWayEvidence (source target : Bool) : Type where
  source_false : source = false
  target_true : target = true

def oneWayPresentation : InteractionPresentation oneWayTheory where
  Site := Unit
  Event := fun _ source target => OneWayEvidence source target
  sound := fun evidence => ⟨evidence.source_false, evidence.target_true⟩

local instance oneWayTermDecidableEq : DecidableEq oneWayTheory.Term := by
  change DecidableEq Bool
  infer_instance

def oneWayCertificate : EventCertificate oneWayPresentation where
  source := false
  event :=
    { site := ()
      target := true
      evidence := ⟨rfl, rfl⟩ }

def boolEndpointIdentity : ExactEndpointIdentity Bool where
  Identity := Bool
  decEq := inferInstance
  identify := id
  identify_injective := Function.injective_id

theorem identity_keyed_edge_is_accepted :
    (stepAuthorityByIdentity AuthorityId.loop boolEndpointIdentity
      oneWayPresentation).check
      { source := false, target := true } oneWayCertificate = true := by
  decide

/-- Negative canary: occurrence evidence for one endpoint cannot be replayed
as a different submitted endpoint. -/
theorem wrong_endpoint_is_rejected :
    (stepAuthority AuthorityId.loop oneWayPresentation).check
      { source := false, target := false } oneWayCertificate = false := by
  decide

theorem identity_keyed_wrong_endpoint_is_rejected :
    (stepAuthorityByIdentity AuthorityId.loop boolEndpointIdentity
      oneWayPresentation).check
      { source := false, target := false } oneWayCertificate = false := by
  decide

end Canary

end Mettapedia.GSLT.LanguageDef.InteractionEventAuthority
