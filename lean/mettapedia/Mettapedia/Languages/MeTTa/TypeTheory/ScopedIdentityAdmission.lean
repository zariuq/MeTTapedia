import Mettapedia.GSLT.LanguageDef.GSLTILObservationSelection
import Mettapedia.GSLT.LanguageDef.NIKMetalogic
import Mettapedia.TypeTheory.UnityIsNotUIP

/-!
# Scoped proof irrelevance and observer-indexed elaboration admission

This module states the boundary that a layered MeTTa type theory needs from
NIK.  Exact Boolean checking, exact preservation of native proof objects, and
proof-irrelevance of a selected proof fibre are three different properties.

An exact NIK certificate boundary transports proof-fibre thinness in both
directions.  It does not manufacture thinness.  In particular:

* a computable theoremhood decision may coexist with two native proofs;
* decidable equality of route objects does not collapse an arbitrary route
  language; and
* an elaborator may select one of several authored worlds only relative to an
  observation which is invariant across those worlds.

For an actual intensional identity type, a future object-theoretic Hedberg
construction may supply the required thin-fibre evidence from identity
elimination plus decidable equality.  This file deliberately does not infer
that evidence from decidable syntax, proposition-valued support, or a Boolean
checker.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.ScopedIdentityAdmission

open Mettapedia.Cybernetics
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.GSLTIL
open Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax
open Mettapedia.GSLT.LanguageDef.GSLTIL.ElaborationSelection
open Mettapedia.GSLT.LanguageDef.GSLTIL.ObservationSelection
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.TypeTheory.ScopedIdentity
open Mettapedia.TypeTheory.UnityIsNotUIP

universe uClaim uCertificate uProof

/-! ## Exact certificate boundaries transport, but do not create, thinness -/

/-- Native proof fibres are proof-irrelevant only for claims in the declared
scope. -/
def NativeThinAt {Claim : Type uClaim}
    (guest : NativeProofSystem.{uClaim, uProof} Claim)
    (inside : Set Claim) : Prop :=
  forall claim, claim ∈ inside -> Subsingleton (guest.ProofFibre claim)

/-- Accepted certificate fibres are proof-irrelevant only for claims in the
declared scope. -/
def AcceptedThinAt {Claim : Type uClaim} {Certificate : Type uCertificate}
    (checker : Checker Claim Certificate) (inside : Set Claim) : Prop :=
  forall claim, claim ∈ inside ->
    Subsingleton (AcceptedCertificateFibre checker claim)

/-- Exact proof-fibre parity transports scoped proof irrelevance in both
directions.  Decode-only boundaries are intentionally insufficient here. -/
theorem acceptedThinAt_iff_nativeThinAt
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    {checker : Checker Claim Certificate}
    {guest : NativeProofSystem.{uClaim, uProof} Claim}
    (boundary : CertificateEquivalence checker guest)
    (inside : Set Claim) :
    AcceptedThinAt checker inside <-> NativeThinAt guest inside := by
  constructor
  · intro acceptedThin claim member
    let fibreEquiv := boundary.fibreEquiv claim
    refine ⟨?_⟩
    intro first second
    apply fibreEquiv.symm.injective
    exact (acceptedThin claim member).allEq
      (fibreEquiv.symm first) (fibreEquiv.symm second)
  · intro nativeThin claim member
    let fibreEquiv := boundary.fibreEquiv claim
    refine ⟨?_⟩
    intro first second
    apply fibreEquiv.injective
    exact (nativeThin claim member).allEq
      (fibreEquiv first) (fibreEquiv second)

/-- The complete evidence needed to expose one NIK proof boundary as a
proof-irrelevant bubble.  Exact proof-fibre correspondence and native
thinness are separate fields because neither implies the other. -/
structure ScopedProofIrrelevanceAdmission
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    (checker : Checker Claim Certificate)
    (guest : NativeProofSystem.{uClaim, uProof} Claim) where
  inside : Set Claim
  boundary : CertificateEquivalence checker guest
  nativeThin : NativeThinAt guest inside

namespace ScopedProofIrrelevanceAdmission

/-- An admitted native-thin scope is equally thin at its exact NIK
certificate boundary. -/
theorem acceptedThin
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    {checker : Checker Claim Certificate}
    {guest : NativeProofSystem.{uClaim, uProof} Claim}
    (admission : ScopedProofIrrelevanceAdmission checker guest) :
    AcceptedThinAt checker admission.inside :=
  (acceptedThinAt_iff_nativeThinAt admission.boundary admission.inside).mpr
    admission.nativeThin

end ScopedProofIrrelevanceAdmission

/-! ## A real positive NIK bubble -/

namespace ThinBoundaryCanary

/-- One native proof object, but a nontrivial claim language with an accepted
and a rejected claim. -/
def guest : NativeProofSystem Bool where
  ProofObject := Unit
  Judges := fun _ claim => claim = true

def kernel : NativeProofKernel guest where
  decide := fun claim _ => claim
  correct := by
    intro claim proof
    cases claim <;> simp [guest]

def inside : Set Bool := Set.univ

theorem nativeThin : NativeThinAt guest inside := by
  intro claim member
  refine ⟨?_⟩
  intro first second
  apply Subtype.ext
  cases first.1
  cases second.1
  rfl

def admission : ScopedProofIrrelevanceAdmission kernel.toChecker guest where
  inside := inside
  boundary := kernel.certificateEquivalence
  nativeThin := nativeThin

theorem acceptedBoundaryThin :
    AcceptedThinAt kernel.toChecker inside :=
  admission.acceptedThin

/-- Nondegeneracy: the bubble accepts the true claim and rejects the false
claim; thinness was not obtained by a reject-all checker. -/
theorem accepted_and_rejected_canaries :
    kernel.toChecker.check true () = true /\
      kernel.toChecker.check false () = false :=
  ⟨rfl, rfl⟩

end ThinBoundaryCanary

/-! ## Decidability alone is not a K certificate -/

/-- The existing decidable-theoremhood guest has two native proofs of its
single theorem, so its proof fibre is not thin. -/
theorem decisionProofGuest_not_nativeThin :
    Not (NativeThinAt DecisionProofCanary.guest Set.univ) := by
  intro alleged
  have thin := alleged () (Set.mem_univ ())
  let first : DecisionProofCanary.guest.ProofFibre () := ⟨false, trivial⟩
  let second : DecisionProofCanary.guest.ProofFibre () := ⟨true, trivial⟩
  have same : first = second := thin.allEq first second
  have false_eq_true : (false : Bool) = true :=
    congrArg (fun proof => proof.1) same
  exact Bool.false_ne_true false_eq_true

/-- Even a directly computable and exact theoremhood decision does not make
native proof objects proof-irrelevant. -/
theorem decidable_theoremhood_does_not_imply_thin_proof_fibres :
    Computable DecisionProofCanary.decisionKernel.decide /\
      Not (NativeThinAt DecisionProofCanary.guest Set.univ) :=
  ⟨DecisionProofCanary.decisionKernel_computable,
    decisionProofGuest_not_nativeThin⟩

/-- Decidable equality of the carrier of an arbitrary route layer is also
insufficient.  The one-object two-loop layer has decidable object equality
and a nontrivial self-route.  Hedberg applies only after the routes are known
to be the identity family with the required eliminator. -/
theorem decidable_object_equality_without_identity_induction_does_not_give_uip :
    Nonempty (DecidableEq Unit) /\ Not (RouteUIP twoLoop) :=
  ⟨⟨inferInstance⟩, twoLoop_not_routeUIP⟩

/-! ## The elaboration side of the same scoping law -/

/-- One GSLT-IL elaboration profile admits deterministic selection at a
coarse observer while refusing it at the identity observer.  The authored
elaboration worlds are retained rather than globally identified. -/
theorem elaboration_selection_is_observer_scoped :
    exists (program : Program) (profile : Profile program),
      Nonempty (ObservationalSelection profile constantPatternObserver) /\
      Not (Nonempty
        (ObservationalSelection profile (Observer.identity Pattern))) /\
      Not (Nonempty (ExactSelection profile)) :=
  ambiguity_is_admissible_coarsely_but_not_finely

/-! ## Axiom audit -/

#print axioms acceptedThinAt_iff_nativeThinAt
#print axioms ScopedProofIrrelevanceAdmission.acceptedThin
#print axioms ThinBoundaryCanary.acceptedBoundaryThin
#print axioms ThinBoundaryCanary.accepted_and_rejected_canaries
#print axioms decisionProofGuest_not_nativeThin
#print axioms decidable_theoremhood_does_not_imply_thin_proof_fibres
#print axioms decidable_object_equality_without_identity_induction_does_not_give_uip
#print axioms elaboration_selection_is_observer_scoped

end Mettapedia.Languages.MeTTa.TypeTheory.ScopedIdentityAdmission
