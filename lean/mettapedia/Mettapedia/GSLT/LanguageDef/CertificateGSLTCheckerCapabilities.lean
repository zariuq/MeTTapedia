import Mettapedia.GSLT.LanguageDef.KernelAuthority
import Mettapedia.GSLT.LanguageDef.CertificateGSLTRecurrentTraceAuthority
import Mettapedia.GSLT.LanguageDef.CertificateGSLTBuchiAuthority
import Mettapedia.GSLT.LanguageDef.CertificateGSLTCyclic

/-!
# Checker capabilities realized by CertificateGSLT

The generic authority distinctions become concrete at the existing
CertificateGSLT boundary.

* The versioned chronological article checker is an exact certificate
  authority for derivations of an admitted definition.
* Finite trace checking is freely generated from a locally complete edge
  authority; it is a combinator over the local checker rather than a new
  semantic root.
* Recurrent execution combines the same local edge authority with a Buechi
  progress measure.  It is exact for recurrence over the controller's whole
  declared active region and sound for recurrence from the selected root.
  The two meanings differ when an unreachable active component is bad.
* A locally accepted cyclic pre-proof is not a closed proof.  A global
  fixed-point acceptance condition remains mandatory.

Thus the current checked inventory is one exact finite-article nucleus, one
exact finite-trace combinator under local completeness, and one exact Buechi
authority at its explicitly declared uniform scope.  General parity,
alternating fixed points, and higher-cell authority remain separate
obligations.
-/

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT.CheckerCapabilities

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.CertificateGSLT

universe uAuthority uClaim uCertificate

/-! ## Bridge from semantic soundness to exact replay authority -/

/-- Forget an authority identifier while retaining its executable checker. -/
def semanticChecker
    {AuthorityId : Type uAuthority} {Claim : Type uClaim}
    (authority : SemanticAuthority AuthorityId Claim) :
    Checker Claim authority.Certificate where
  check := authority.check

theorem semanticChecker_sound
    {AuthorityId : Type uAuthority} {Claim : Type uClaim}
    (authority : SemanticAuthority AuthorityId Claim) :
    (semanticChecker authority).Sound authority.Meaning := by
  intro claim certificate accepted
  exact authority.sound accepted

/-- Certificate completeness is an additional property of a semantic
authority, not part of trusted replay soundness. -/
def certificateComplete
    {AuthorityId : Type uAuthority} {Claim : Type uClaim}
    (authority : SemanticAuthority AuthorityId Claim) : Prop :=
  (semanticChecker authority).CertificateComplete authority.Meaning

theorem semanticChecker_authority
    {AuthorityId : Type uAuthority} {Claim : Type uClaim}
    (authority : SemanticAuthority AuthorityId Claim)
    (complete : certificateComplete authority) :
    (semanticChecker authority).Authority authority.Meaning where
  sound := semanticChecker_sound authority
  complete := complete

/-! ## Exact finite CertificateGSLT articles -/

/-- The actual versioned article checker, viewed through the generic checker
interface. -/
def wireChecker {AuthorityId : Type uAuthority}
    (authorityId : AuthorityId) (definition : ValidatedCalculusLanguageDef) :=
  semanticChecker (wireArticleAuthority authorityId definition)

/-- CertificateGSLT's chronological wire checker is exact for the derivation family
of the admitted definition. -/
theorem wireChecker_authority
    {AuthorityId : Type uAuthority} (authorityId : AuthorityId)
    (definition : ValidatedCalculusLanguageDef) :
    (wireChecker authorityId definition).Authority
      (fun goal => Nonempty (Derivation definition goal)) where
  sound := semanticChecker_sound (wireArticleAuthority authorityId definition)
  complete := by
    intro goal derivable
    obtain ⟨proof⟩ := derivable
    exact ⟨articleOfDerivation proof,
      wireArticleAuthority_complete authorityId proof⟩

/-! ## Fail-closed wire transport -/

/-- The canonical CertificateGSLT article codec as an instance of the generic
partial-codec boundary. -/
def wireArticleCodec : Checker.PartialCodec WireArticle WireTerm where
  encode := encodeArticle
  decode := decodeArticle
  decode_encode := decodeArticle_encodeArticle

/-- Replay canonical symbolic wire terms rather than already-decoded article
values.  Malformed or noncanonical input fails during decoding. -/
def wireTermChecker {AuthorityId : Type uAuthority}
    (authorityId : AuthorityId) (definition : ValidatedCalculusLanguageDef) :=
  Checker.onWire (wireChecker authorityId definition) wireArticleCodec

/-- The exact derivation authority survives fail-closed wire decoding. -/
theorem wireTermChecker_authority
    {AuthorityId : Type uAuthority} (authorityId : AuthorityId)
    (definition : ValidatedCalculusLanguageDef) :
    (wireTermChecker authorityId definition).Authority
      (fun goal => Nonempty (Derivation definition goal)) :=
  Checker.onWire_authority wireArticleCodec
    (wireChecker_authority authorityId definition)

/-! ## Exact finite GSLT traces -/

def finiteTraceChecker
    {AuthorityId : Type uAuthority} {theory : GSLT}
    [DecidableEq theory.Term]
    (stepAuthority : StepAuthority AuthorityId theory) :=
  semanticChecker (finiteTraceAuthority stepAuthority)

/-- Local certificate completeness lifts compositionally to exact finite
reachability authority. -/
theorem finiteTraceChecker_authority
    {AuthorityId : Type uAuthority} {theory : GSLT}
    [DecidableEq theory.Term]
    (stepAuthority : StepAuthority AuthorityId theory)
    (complete : stepAuthority.Complete) :
    (finiteTraceChecker stepAuthority).Authority TraceClaim.Meaning where
  sound := semanticChecker_sound (finiteTraceAuthority stepAuthority)
  complete := by
    intro claim meaning
    exact (finiteTraceAuthority_correspondence
      stepAuthority complete claim).2 meaning

/-! ## Infinitary recurrence needs global evidence -/

def recurrentChecker
    {AuthorityId : Type uAuthority} {theory : GSLT}
    [Fintype theory.Term] [DecidableEq theory.Term]
    (authorityId : AuthorityId)
    (stepAuthority : StepAuthority.{uAuthority, uCertificate}
      AuthorityId theory)
    (accepting : theory.Term -> Bool) :=
  semanticChecker
    (recurrentTraceAuthority authorityId stepAuthority accepting)

/-- The current recurrent checker is sound for genuine GSLT execution plus
Buechi recurrence.  Completeness is intentionally not inferred from this
result. -/
theorem recurrentChecker_sound
    {AuthorityId : Type uAuthority} {theory : GSLT}
    [Fintype theory.Term] [DecidableEq theory.Term]
    (authorityId : AuthorityId)
    (stepAuthority : StepAuthority.{uAuthority, uCertificate}
      AuthorityId theory)
    (accepting : theory.Term -> Bool) :
    (recurrentChecker authorityId stepAuthority accepting).Sound
      (RecurrentTraceClaim.Meaning accepting) :=
  semanticChecker_sound
    (recurrentTraceAuthority authorityId stepAuthority accepting)

/-! ## Exact Buechi authority at the declared active-region scope -/

/-- The semantic scope exactly characterized by the progress certificate:
all controller actions in the declared active region replay successfully and
every active starting state satisfies Buechi recurrence. -/
def RecurrentTraceClaim.UniformMeaning
    {AuthorityId : Type uAuthority} {theory : GSLT}
    [Fintype theory.Term] [DecidableEq theory.Term]
    (stepAuthority : StepAuthority.{uAuthority, uCertificate}
      AuthorityId theory)
    (accepting : theory.Term -> Bool)
    (claim : RecurrentTraceClaim theory stepAuthority.Certificate) : Prop :=
  claim.controller.UniformBuchiWinning
    (auditedLabeledSystem stepAuthority accepting) claim.root

/-- The recurrent checker is an exact authority for uniform recurrence over
the declared active region.  Completeness is the finite deterministic Buechi
progress theorem, not a definition by certificate existence. -/
theorem recurrentChecker_uniformAuthority
    {AuthorityId : Type uAuthority} {theory : GSLT}
    [Fintype theory.Term] [DecidableEq theory.Term]
    (authorityId : AuthorityId)
    (stepAuthority : StepAuthority.{uAuthority, uCertificate}
      AuthorityId theory)
    (accepting : theory.Term -> Bool) :
    (recurrentChecker authorityId stepAuthority accepting).Authority
      (RecurrentTraceClaim.UniformMeaning stepAuthority accepting) where
  sound := by
    intro claim measure accepted
    exact ProgressMeasure.uniformBuchi_sound
      ((ProgressMeasure.check_eq_true_iff
        (auditedLabeledSystem stepAuthority accepting)
        claim.controller measure claim.root).mp accepted)
  complete := by
    intro claim uniform
    obtain ⟨measure, valid⟩ :=
      (ProgressMeasure.exists_valid_iff_uniformBuchi).mpr uniform
    exact ⟨measure,
      (ProgressMeasure.check_eq_true_iff
        (auditedLabeledSystem stepAuthority accepting)
        claim.controller measure claim.root).mpr valid⟩

/-- Uniform audited recurrence projects to genuine recurrent GSLT execution
from the selected root.  The reverse implication is false in general because
the active region may contain unreachable states. -/
theorem recurrentUniformMeaning_implies_rootMeaning
    {AuthorityId : Type uAuthority} {theory : GSLT}
    [Fintype theory.Term] [DecidableEq theory.Term]
    (authorityId : AuthorityId)
    (stepAuthority : StepAuthority.{uAuthority, uCertificate}
      AuthorityId theory)
    (accepting : theory.Term -> Bool)
    (claim : RecurrentTraceClaim theory stepAuthority.Certificate) :
    RecurrentTraceClaim.UniformMeaning stepAuthority accepting claim ->
      claim.Meaning accepting := by
  intro uniform
  obtain ⟨measure, accepted⟩ :=
    (recurrentChecker_uniformAuthority authorityId stepAuthority accepting).complete
      claim uniform
  exact recurrentChecker_sound authorityId stepAuthority accepting
    claim measure accepted

/-- The recurrent component packaged at the generic checker waist: exact for
uniform audited recurrence and sound, by projection, for the selected-root
GSLT meaning. -/
def recurrentChecker_authorityProjection
    {AuthorityId : Type uAuthority} {theory : GSLT}
    [Fintype theory.Term] [DecidableEq theory.Term]
    (authorityId : AuthorityId)
    (stepAuthority : StepAuthority.{uAuthority, uCertificate}
      AuthorityId theory)
    (accepting : theory.Term -> Bool) :
    (recurrentChecker authorityId stepAuthority accepting).AuthorityProjection
      (RecurrentTraceClaim.UniformMeaning stepAuthority accepting)
      (RecurrentTraceClaim.Meaning accepting) where
  authority := recurrentChecker_uniformAuthority
    authorityId stepAuthority accepting
  project := recurrentUniformMeaning_implies_rootMeaning
    authorityId stepAuthority accepting

/-- Local circular replay cannot be promoted to closed authority merely from
the existence of a cyclic pre-proof. -/
theorem localCycleExistence_not_closedAuthority :
    ¬ forall goal,
      (exists proof,
        checkOpenRaw Cyclic.cyclicValidated [goal] goal proof = true) ->
      Nonempty (Derivation Cyclic.cyclicValidated goal) :=
  Cyclic.discharge_cannot_factor_through_provability

end Mettapedia.GSLT.LanguageDef.CertificateGSLT.CheckerCapabilities
