import Mettapedia.Languages.SUMO.Native.ProofSearch
import Mettapedia.GSLT.LanguageDef.NIKGSLT

/-!
# Direct NIK authority for the native SUMO calculus

This module exposes closed native SUMO derivability as one exact NIK authority
fibre.  Its executable checker is the native certificate checker: it
reconstructs a scoped derivation and compares the reconstructed conclusion
with the submitted claim.  The generic NIK machine supplies fail-closed
dispatch, while accepted evidence also expands into the rule-by-rule native
proof-search GSLT.

The broader meaning is validity in the unityped world semantics.  Exactness is
claimed for native derivability, not for semantic validity; no completeness
theorem for the model class is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.SUMO.Native.NIKAuthority

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKGSLT
open Mettapedia.Languages.SUMO.Native

universe uModel

/-- Closed native SUMO formulas are the claims checked by this authority. -/
abbrev Claim := Sentence String String

/-- Native proof trees, with no asserted conclusion field, are the untrusted
evidence accepted by this authority. -/
abbrev Evidence := Certificate String String 0 0

/-- Native derivability from the empty assumption context. -/
def Certified (claim : Claim) : Prop :=
  Derivation String String [] claim

/-- Validity in every small unityped native SUMO model.  The separate
universe-polymorphic theorem below covers arbitrary model levels. -/
def Meaning (claim : Claim) : Prop :=
  forall model : Model.{0, 0, 0} String String,
    model.ValidSentence claim

/-- The executable native SUMO checker exposed at the NIK boundary. -/
def checker : Checker Claim Evidence where
  check := fun claim certificate =>
    decide (Certificate.infer [] certificate = some claim)

@[simp] theorem checker_accepts_iff
    (claim : Claim) (certificate : Evidence) :
    checker.check claim certificate = true <->
      Certificate.infer [] certificate = some claim := by
  simp [checker]

/-- The checker is exact for the full native derivability judgment. -/
theorem checker_authority : checker.Authority Certified where
  sound := by
    intro claim certificate accepted
    exact Certificate.infer_sound
      ((checker_accepts_iff claim certificate).mp accepted)
  complete := by
    intro claim derivable
    obtain ⟨certificate, accepted⟩ := Certificate.infer_complete derivable
    exact ⟨certificate, (checker_accepts_iff claim certificate).mpr accepted⟩

/-- Native derivability projects into the independently defined world
semantics. -/
theorem checker_projection :
    checker.AuthorityProjection Certified Meaning where
  authority := checker_authority
  project := by
    intro claim derivable model
    exact derivable.theorem_valid model

/-- The direct SUMO authority occupies one explicitly named NIK fibre. -/
def family : AuthorityFamily Unit where
  Claim := fun _ => Claim
  Certificate := fun _ => Evidence
  checker := fun _ => checker
  Certified := fun _ => Certified
  Meaning := fun _ => Meaning
  projection := fun _ => checker_projection

/-- Proof-relevant NIK evidence for a closed native SUMO claim. -/
abbrev NIKEvidence (claim : Claim) :=
  { certificate : Evidence // checker.check claim certificate = true }

theorem nonempty_nikEvidence_iff_derivable (claim : Claim) :
    Nonempty (NIKEvidence claim) <-> Certified claim := by
  constructor
  · rintro ⟨⟨certificate, accepted⟩⟩
    exact checker_authority.sound claim certificate accepted
  · intro derivable
    obtain ⟨certificate, accepted⟩ := checker_authority.complete claim derivable
    exact ⟨⟨certificate, accepted⟩⟩

theorem nonempty_nikEvidence_implies_valid (claim : Claim) :
    Nonempty (NIKEvidence claim) -> Meaning claim := by
  intro evidence
  exact checker_projection.project claim
    ((nonempty_nikEvidence_iff_derivable claim).mp evidence)

/-- NIK evidence is sound in a native SUMO model at any universe level. -/
theorem nonempty_nikEvidence_valid_in_model
    (claim : Claim)
    (evidence : Nonempty (NIKEvidence claim))
    (model : Model.{0, 0, uModel} String String) :
    model.ValidSentence claim := by
  have derivable := (nonempty_nikEvidence_iff_derivable claim).mp evidence
  exact derivable.theorem_valid model

/-- The public fail-closed NIK invocation GSLT for native SUMO claims. -/
abbrev invocationGSLT : GSLT := Atomic.theory checker

theorem invocation_accepts_iff
    (claim : Claim) (certificate : Evidence) :
    invocationGSLT.MultiStep
        (.submitted claim certificate) (.accepted claim) <->
      Certificate.infer [] certificate = some claim := by
  rw [Atomic.submitted_multiStep_accepted_iff]
  exact checker_accepts_iff claim certificate

/-- Public NIK acceptance exposes a complete rule-by-rule route through the
native SUMO proof-search GSLT; the atomic invocation layer does not replace
the guest calculus. -/
theorem invocation_acceptance_reaches_native_empty
    {claim : Claim} {certificate : Evidence}
    (accepted : invocationGSLT.MultiStep
      (.submitted claim certificate) (.accepted claim)) :
    (ProofSearch.nativeProofSearchGSLT String String).MultiStep
      [ProofSearch.Sequent.of [] claim] [] :=
  ProofSearch.accepted_certificate_reaches_empty
    ((invocation_accepts_iff claim certificate).mp accepted)

/-! ## Theory-relative native consequence -/

/-- A native ontology judgment retains its exact finite assumption context
and the conclusion to be checked. -/
structure EntailmentClaim where
  assumptions : List Claim
  conclusion : Claim
  deriving DecidableEq, Repr

/-- Native derivability relative to the submitted ontology context. -/
def EntailmentCertified (claim : EntailmentClaim) : Prop :=
  Derivation String String claim.assumptions claim.conclusion

/-- Local semantic consequence in every small unityped native SUMO model. -/
def EntailmentMeaning (claim : EntailmentClaim) : Prop :=
  forall (model : Model.{0, 0, 0} String String) (world : model.World),
    SatisfiesAssumptions model model.emptyObjects model.emptyRows world
      claim.assumptions ->
    model.satisfies model.emptyObjects model.emptyRows claim.conclusion world

/-- The contextual native checker reconstructs a conclusion under exactly the
assumption list carried by the claim. -/
def entailmentChecker : Checker EntailmentClaim Evidence where
  check := fun claim certificate =>
    decide (Certificate.infer claim.assumptions certificate =
      some claim.conclusion)

@[simp] theorem entailmentChecker_accepts_iff
    (claim : EntailmentClaim) (certificate : Evidence) :
    entailmentChecker.check claim certificate = true <->
      Certificate.infer claim.assumptions certificate =
        some claim.conclusion := by
  simp [entailmentChecker]

/-- The contextual checker is exact for native theory-relative consequence. -/
theorem entailmentChecker_authority :
    entailmentChecker.Authority EntailmentCertified where
  sound := by
    intro claim certificate accepted
    exact Certificate.infer_sound
      ((entailmentChecker_accepts_iff claim certificate).mp accepted)
  complete := by
    intro claim derivable
    obtain ⟨certificate, accepted⟩ := Certificate.infer_complete derivable
    exact ⟨certificate,
      (entailmentChecker_accepts_iff claim certificate).mpr accepted⟩

/-- Contextual native derivability projects to local semantic consequence. -/
theorem entailmentChecker_projection :
    entailmentChecker.AuthorityProjection
      EntailmentCertified EntailmentMeaning where
  authority := entailmentChecker_authority
  project := by
    intro claim derivable model world assumptionsHold
    exact derivable.sound model model.emptyObjects model.emptyRows world
      assumptionsHold

/-- The actual ontology-consequence authority as a NIK family. -/
def entailmentFamily : AuthorityFamily Unit where
  Claim := fun _ => EntailmentClaim
  Certificate := fun _ => Evidence
  checker := fun _ => entailmentChecker
  Certified := fun _ => EntailmentCertified
  Meaning := fun _ => EntailmentMeaning
  projection := fun _ => entailmentChecker_projection

abbrev EntailmentNIKEvidence (claim : EntailmentClaim) :=
  { certificate : Evidence //
    entailmentChecker.check claim certificate = true }

theorem nonempty_entailmentEvidence_iff_derivable
    (claim : EntailmentClaim) :
    Nonempty (EntailmentNIKEvidence claim) <-> EntailmentCertified claim := by
  constructor
  · rintro ⟨⟨certificate, accepted⟩⟩
    exact entailmentChecker_authority.sound claim certificate accepted
  · intro derivable
    obtain ⟨certificate, accepted⟩ :=
      entailmentChecker_authority.complete claim derivable
    exact ⟨⟨certificate, accepted⟩⟩

/-- Contextual NIK evidence is sound in a native SUMO model at any universe
level. -/
theorem nonempty_entailmentEvidence_valid_in_model
    (claim : EntailmentClaim)
    (evidence : Nonempty (EntailmentNIKEvidence claim))
    (model : Model.{0, 0, uModel} String String) (world : model.World)
    (assumptionsHold :
      SatisfiesAssumptions model model.emptyObjects model.emptyRows world
        claim.assumptions) :
    model.satisfies model.emptyObjects model.emptyRows claim.conclusion world := by
  have derivable :=
    (nonempty_entailmentEvidence_iff_derivable claim).mp evidence
  exact derivable.sound model model.emptyObjects model.emptyRows world
    assumptionsHold

/-- The fail-closed public invocation machine for ontology consequences. -/
abbrev entailmentInvocationGSLT : GSLT := Atomic.theory entailmentChecker

theorem entailmentInvocation_accepts_iff
    (claim : EntailmentClaim) (certificate : Evidence) :
    entailmentInvocationGSLT.MultiStep
        (.submitted claim certificate) (.accepted claim) <->
      Certificate.infer claim.assumptions certificate =
        some claim.conclusion := by
  rw [Atomic.submitted_multiStep_accepted_iff]
  exact entailmentChecker_accepts_iff claim certificate

theorem entailmentInvocation_acceptance_reaches_native_empty
    {claim : EntailmentClaim} {certificate : Evidence}
    (accepted : entailmentInvocationGSLT.MultiStep
      (.submitted claim certificate) (.accepted claim)) :
    (ProofSearch.nativeProofSearchGSLT String String).MultiStep
      [ProofSearch.Sequent.of claim.assumptions claim.conclusion] [] :=
  ProofSearch.accepted_certificate_reaches_empty
    ((entailmentInvocation_accepts_iff claim certificate).mp accepted)

/-! ## Positive and negative controls -/

def identityAtom : Claim :=
  .atom (.constant "instance")
    (.term (.constant "instance")
      (.term (.constant "BinaryPredicate") .nil))

def identityClaim : Claim := .implies identityAtom identityAtom

def identityCertificate : Evidence :=
  .implicationIntroduction identityAtom (.hypothesis 0)

theorem identity_accepted :
    checker.check identityClaim identityCertificate = true := by
  decide

def identityNIKEvidence : NIKEvidence identityClaim :=
  ⟨identityCertificate, identity_accepted⟩

theorem identity_reaches_native_empty :
    (ProofSearch.nativeProofSearchGSLT String String).MultiStep
      [ProofSearch.Sequent.of [] identityClaim] [] := by
  apply ProofSearch.accepted_certificate_reaches_empty
  exact (checker_accepts_iff identityClaim identityCertificate).mp identity_accepted

/-- A proof of truth is not accepted as evidence for implication identity. -/
theorem wrong_conclusion_rejected :
    checker.check identityClaim (.topIntroduction : Evidence) = false := by
  decide

def mortalAtom : Claim :=
  .atom (.constant "mortal") (.singleton (.constant "Socrates"))

def mortalEntailment : EntailmentClaim :=
  { assumptions := [.implies identityAtom mortalAtom, identityAtom]
    conclusion := mortalAtom }

def mortalCertificate : Evidence :=
  .implicationElimination (.hypothesis 0) (.hypothesis 1)

theorem mortalEntailment_accepted :
    entailmentChecker.check mortalEntailment mortalCertificate = true := by
  decide

/-- Reversing the two premise certificates is rejected because the first
premise is no longer an implication. -/
theorem reversed_modus_ponens_rejected :
    entailmentChecker.check mortalEntailment
      (.implicationElimination (.hypothesis 1) (.hypothesis 0)) = false := by
  decide

end Mettapedia.Languages.SUMO.Native.NIKAuthority
