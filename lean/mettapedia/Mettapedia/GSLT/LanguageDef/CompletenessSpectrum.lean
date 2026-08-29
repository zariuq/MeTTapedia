import Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
import Mettapedia.GSLT.LanguageDef.CertificateGSLTCheckerCapabilities

/-!
# Completeness properties at the proof-kernel boundary

The word "complete" names several independent properties.  This module keeps
their domains explicit.

* `Checker.CertificateComplete` is completeness of a certificate language for
  a named predicate.
* `CalculusComplete` is completeness of an independently defined derivability
  predicate for an independently defined semantic meaning.
* `FragmentAuthority` is exact replay on a declared fragment, without a claim
  outside that fragment.
* `SyntacticallyCompleteTheory` says that a theory proves each sentence or its
  declared negation.  It is not model-theoretic completeness.
* `CompleteJudgmentAuthority` combines exact derivation replay with a
  sound-and-complete calculus/semantics bridge.

Search and decision remain separate.  They are already represented by
`Checker.CompleteProducer` and `Checker.DecisionKernel` in
`KernelAuthority`.
-/

namespace Mettapedia.GSLT.LanguageDef.CompletenessSpectrum

open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.CheckerAuthorityFamily
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.CheckerCapabilities

universe uKind uClaim uCertificate

/-! ## Derivability versus semantic meaning -/

/-- Every derivable claim has its intended semantic meaning. -/
def CalculusSound {Claim : Type uClaim}
    (Derivable Meaning : Claim -> Prop) : Prop :=
  forall claim, Derivable claim -> Meaning claim

/-- Every semantically meaningful claim is derivable in the calculus. -/
def CalculusComplete {Claim : Type uClaim}
    (Derivable Meaning : Claim -> Prop) : Prop :=
  forall claim, Meaning claim -> Derivable claim

/-- A two-sided calculus/semantics correspondence. -/
structure CalculusExact {Claim : Type uClaim}
    (Derivable Meaning : Claim -> Prop) : Prop where
  sound : CalculusSound Derivable Meaning
  complete : CalculusComplete Derivable Meaning

theorem CalculusExact.iff
    {Claim : Type uClaim} {Derivable Meaning : Claim -> Prop}
    (exactness : CalculusExact Derivable Meaning) (claim : Claim) :
    Derivable claim <-> Meaning claim :=
  ⟨exactness.sound claim, exactness.complete claim⟩

/-- Exact replay for derivations plus calculus soundness gives an exact
derivational authority that projects soundly to the model meaning. -/
def derivationalProjection
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    {checker : Checker Claim Certificate}
    {Derivable Meaning : Claim -> Prop}
    (replay : checker.Authority Derivable)
    (sound : CalculusSound Derivable Meaning) :
    checker.AuthorityProjection Derivable Meaning where
  authority := replay
  project := sound

/-- Exact replay and a two-sided calculus/semantics theorem give exact
semantic certificate authority. -/
theorem semanticAuthority_of_replay_and_calculus
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    {checker : Checker Claim Certificate}
    {Derivable Meaning : Claim -> Prop}
    (replay : checker.Authority Derivable)
    (calculus : CalculusExact Derivable Meaning) :
    checker.Authority Meaning where
  sound := replay.sound.map calculus.sound
  complete := by
    intro claim meaningful
    exact replay.complete claim (calculus.complete claim meaningful)

/-- If semantic meaning contains a claim not derivable by the replayed
calculus, derivational exactness and semantic soundness cannot be promoted to
semantic authority. -/
theorem not_semanticAuthority_of_calculus_gap
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    {checker : Checker Claim Certificate}
    {Derivable Meaning : Claim -> Prop}
    (replay : checker.Authority Derivable)
    (sound : CalculusSound Derivable Meaning)
    {claim : Claim} (meaningful : Meaning claim)
    (notDerivable : Not (Derivable claim)) :
    Not (checker.Authority Meaning) :=
  (derivationalProjection replay sound).not_target_authority_of_gap
    meaningful notDerivable

/-- If one checker is exact both for derivability and for semantic meaning,
then the calculus is necessarily sound and complete for that meaning. -/
theorem calculusExact_of_two_authorities
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    {checker : Checker Claim Certificate}
    {Derivable Meaning : Claim -> Prop}
    (derivational : checker.Authority Derivable)
    (semantic : checker.Authority Meaning) :
    CalculusExact Derivable Meaning where
  sound := by
    intro claim derivable
    obtain ⟨certificate, accepted⟩ :=
      derivational.complete claim derivable
    exact semantic.sound claim certificate accepted
  complete := by
    intro claim meaningful
    obtain ⟨certificate, accepted⟩ := semantic.complete claim meaningful
    exact derivational.sound claim certificate accepted

/-! ## Honest fragment completeness -/

/-- Certificate completeness restricted to explicitly selected claims. -/
def CertificateCompleteOn
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    (checker : Checker Claim Certificate)
    (Fragment Meaning : Claim -> Prop) : Prop :=
  forall claim, Fragment claim -> Meaning claim ->
    exists certificate, checker.check claim certificate = true

/-- Restrict a checker to claims carrying a proof that they lie in a declared
fragment. -/
def restrictClaims
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    (checker : Checker Claim Certificate) (Fragment : Claim -> Prop) :
    Checker {claim : Claim // Fragment claim} Certificate where
  check claim certificate := checker.check claim.1 certificate

/-- Sound replay everywhere and certificate completeness on one named
fragment.  The resulting restricted checker is an exact authority; no claim
is made about certificate existence outside the fragment. -/
structure FragmentAuthority
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    (checker : Checker Claim Certificate)
    (Fragment Meaning : Claim -> Prop) : Prop where
  sound : checker.Sound Meaning
  completeOn : CertificateCompleteOn checker Fragment Meaning

theorem FragmentAuthority.restrictedAuthority
    {Claim : Type uClaim} {Certificate : Type uCertificate}
    {checker : Checker Claim Certificate}
    {Fragment Meaning : Claim -> Prop}
    (authority : FragmentAuthority checker Fragment Meaning) :
    (restrictClaims checker Fragment).Authority
      (fun claim => Meaning claim.1) where
  sound := by
    intro claim certificate accepted
    exact authority.sound claim.1 certificate accepted
  complete := by
    intro claim meaningful
    exact authority.completeOn claim.1 claim.2 meaningful

/-! ## A complete judgment authority -/

/-- A complete proof authority names both the syntactic derivability relation
replayed by its checker and the independently stated semantic meaning. -/
structure CompleteJudgmentAuthority
    (Claim : Type uClaim) (Certificate : Type uCertificate) where
  checker : Checker Claim Certificate
  Derivable : Claim -> Prop
  Meaning : Claim -> Prop
  replay : checker.Authority Derivable
  calculus : CalculusExact Derivable Meaning

namespace CompleteJudgmentAuthority

variable {Claim : Type uClaim} {Certificate : Type uCertificate}
    (authority : CompleteJudgmentAuthority Claim Certificate)

/-- The complete judgment package gives exact authority for its independent
semantic meaning. -/
theorem semanticAuthority :
    authority.checker.Authority authority.Meaning :=
  semanticAuthority_of_replay_and_calculus
    authority.replay authority.calculus

/-- The derivational view remains available when proof structure rather than
only semantic truth is the desired observation. -/
def derivationalAuthorityProjection :
    authority.checker.AuthorityProjection
      authority.Derivable authority.Meaning :=
  derivationalProjection authority.replay authority.calculus.sound

end CompleteJudgmentAuthority

/-! ## CertificateGSLT instances and per-language admission -/

/-- A CertificateGSLT definition with a two-sided adequacy theorem for an
independently stated meaning.  This is the unambiguous complete CertificateGSLT
class: completeness is semantic, not merely completeness for its own
inductive derivation type. -/
structure SemanticallyCompleteCertificateGSLT
    (Claim : Type uClaim) (Meaning : Claim -> Prop) where
  definition : ValidatedCalculusLanguageDef
  adequacy : ExactJudgmentEncoding Claim Meaning definition

namespace SemanticallyCompleteCertificateGSLT

variable {Claim : Type uClaim} {Meaning : Claim -> Prop}
    (system : SemanticallyCompleteCertificateGSLT Claim Meaning)

/-- The ordinary CertificateGSLT wire replay checker interpreted through the
system's semantic adequacy theorem. -/
def checker {AuthorityId : Type uKind} (authorityId : AuthorityId) :=
  semanticChecker
    (judgmentWireAuthority authorityId
      system.adequacy.toJudgmentEncodingAdequacy)

/-- A semantically complete CertificateGSLT has exact wire-certificate authority
for the named model meaning. -/
theorem checker_authority {AuthorityId : Type uKind}
    (authorityId : AuthorityId) :
    (system.checker authorityId).Authority Meaning where
  sound := semanticChecker_sound
    (judgmentWireAuthority authorityId
      system.adequacy.toJudgmentEncodingAdequacy)
  complete := by
    intro claim meaningful
    exact (judgmentWireAuthority_correspondence
      authorityId system.adequacy claim).mpr meaningful

end SemanticallyCompleteCertificateGSLT

/-- A language implementation normally admits one complete CertificateGSLT per
judgment kind, not one checker for all judgments by representation accident.
The index may itself be a pair of language and judgment identifiers. -/
structure ExactCertificateGSLTFamily (Kind : Type uKind) where
  Claim : Kind -> Type uClaim
  Meaning : (kind : Kind) -> Claim kind -> Prop
  system : (kind : Kind) ->
    SemanticallyCompleteCertificateGSLT (Claim kind) (Meaning kind)

namespace ExactCertificateGSLTFamily

variable {Kind : Type uKind} (family : ExactCertificateGSLTFamily Kind)

/-- Exact per-kind CertificateGSLT admissions assemble into the generic dependent
NIK authority family. -/
def toAuthorityFamily : AuthorityFamily Kind where
  Claim := family.Claim
  Certificate := fun _ => WireArticle
  checker := fun kind => (family.system kind).checker kind
  Certified := family.Meaning
  Meaning := family.Meaning
  projection := by
    intro kind
    exact ((family.system kind).checker_authority kind).toProjection

end ExactCertificateGSLTFamily

/-! ## Model completeness is not theory completeness -/

/-- A syntactically complete theory decides every sentence up to its declared
negation.  This is independent of completeness of a calculus for a class of
models. -/
def SyntacticallyCompleteTheory {Sentence : Type uClaim}
    (Provable : Sentence -> Prop) (neg : Sentence -> Sentence) : Prop :=
  forall sentence, Provable sentence \/ Provable (neg sentence)

namespace Canary

/-- A small theory with one theorem and one undecided atom/negated-atom pair. -/
inductive Sentence where
  | theorem
  | atom
  | negAtom
deriving DecidableEq

def neg : Sentence -> Sentence
  | .theorem => .theorem
  | .atom => .negAtom
  | .negAtom => .atom

def Provable : Sentence -> Prop
  | .theorem => True
  | .atom | .negAtom => False

private instance provableDecidable (sentence : Sentence) :
    Decidable (Provable sentence) := by
  cases sentence <;> unfold Provable <;> infer_instance

def sentenceChecker : Checker Sentence Unit where
  check sentence _ := decide (Provable sentence)

theorem sentenceChecker_authority :
    sentenceChecker.Authority Provable where
  sound := by
    intro sentence _ accepted
    exact of_decide_eq_true accepted
  complete := by
    intro sentence provable
    exact ⟨(), decide_eq_true provable⟩

/-- The calculus and model meaning may coincide exactly while the underlying
theory still leaves a sentence and its negation undecided. -/
theorem exact_calculus_does_not_imply_syntactically_complete_theory :
    CalculusExact Provable Provable /\
      Not (SyntacticallyCompleteTheory Provable neg) := by
  constructor
  · exact
      { sound := fun _ proof => proof
        complete := fun _ proof => proof }
  · intro complete
    simpa [Provable, neg] using complete Sentence.atom

/-- A nontrivial derivational checker that accepts exactly `false`. -/
def falseOnlyChecker : Checker Bool Unit where
  check claim _ := decide (claim = false)

def FalseDerivable (claim : Bool) : Prop := claim = false

def BothMeaningful (_ : Bool) : Prop := True

theorem falseOnlyChecker_replay :
    falseOnlyChecker.Authority FalseDerivable where
  sound := by
    intro claim _ accepted
    change decide (claim = false) = true at accepted
    change claim = false
    exact of_decide_eq_true accepted
  complete := by
    intro claim derivable
    change claim = false at derivable
    exact ⟨(), decide_eq_true derivable⟩

theorem falseOnly_calculusSound :
    CalculusSound FalseDerivable BothMeaningful := by
  intro _ _
  trivial

theorem falseOnly_not_calculusComplete :
    Not (CalculusComplete FalseDerivable BothMeaningful) := by
  intro complete
  have impossible : true = false := complete true trivial
  cases impossible

/-- Replay exactness plus calculus soundness is only a projection when model
completeness fails; it cannot be relabelled as semantic authority. -/
theorem falseOnly_not_semanticAuthority :
    Not (falseOnlyChecker.Authority BothMeaningful) :=
  not_semanticAuthority_of_calculus_gap (claim := true)
    falseOnlyChecker_replay falseOnly_calculusSound trivial
      (by simp [FalseDerivable])

end Canary

end Mettapedia.GSLT.LanguageDef.CompletenessSpectrum
