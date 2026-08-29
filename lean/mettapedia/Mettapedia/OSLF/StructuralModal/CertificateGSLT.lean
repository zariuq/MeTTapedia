import Mettapedia.OSLF.StructuralModal.Formula
import Mettapedia.OSLF.Framework.OSLFCertificateGSLTAuthority
import Mettapedia.OSLF.Framework.ReductionSpanTypeSynthesis

/-!
# CertificateGSLT replay for structural-modal claims

OSLF supplies the semantic meaning of a structural-modal formula.
CertificateGSLT supplies the finite, versioned article checker.  This module states
the exact bridge required before a native inference kernel may treat an
accepted article as evidence of structural-modal satisfaction.

The bridge is deliberately parameterized by a proved language-adequacy map.
A language definition that merely spells a judgment `NativeSat` gains no
authority: its derivations must be proved sound for the OSLF reduction span.
Once that theorem exists, the existing `WireArticle` authority and
`CheckedLowering` machinery provide the MIK and NIK boundaries without a
second checker semantics.
-/

namespace Mettapedia.OSLF.StructuralModal.CertificateGSLT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.StructuralModal
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.OSLF.Framework.OSLFCertificateGSLTAuthority
open Mettapedia.OSLF.Framework.ReductionSpanTypeSynthesis

universe uAuthority uNative

/-- One semantic structural-modal judgment, before choosing its proof syntax. -/
structure Claim where
  term : Pattern
  formula : Formula
deriving Repr

/-- Meaning of a structural-modal claim in one OSLF-derived reduction span. -/
def Claim.Meaning (span : ReductionSpan Pattern) (claim : Claim) : Prop :=
  satisfiesOver span claim.formula claim.term

/-- Interpret the readable finitary native syntax as a rich predicate-valued
OSLF native judgment over the same reduction span. -/
def Claim.toRichClaim (claim : Claim) (span : ReductionSpan Pattern) :
    NativeClaim (spanOSLF span) where
  nativeType :=
    predicateNativeType span (satisfiesOver span claim.formula)
  term := claim.term

/-- The readable native syntax is a denotational fragment of the rich OSLF
system, not a second structural-modal semantics. -/
theorem Claim.meaning_iff_richClaim (span : ReductionSpan Pattern)
    (claim : Claim) :
    claim.Meaning span ↔ (claim.toRichClaim span).Meaning :=
  Iff.rfl

/-- The substantive theorem required of a CertificateGSLT language for native
types.  `encode` may choose any readable judgment syntax, but every derivation
of that syntax must denote OSLF structural-modal satisfaction. -/
structure LanguageAdequacy (span : ReductionSpan Pattern)
    (definition : ValidatedCalculusLanguageDef) where
  encode : Claim → Pattern
  derivation_sound : ∀ claim,
    Nonempty (Derivation definition (encode claim)) → claim.Meaning span

/-- Adequacy of the readable syntax also proves the corresponding rich OSLF
native judgment. -/
theorem LanguageAdequacy.derivation_sound_rich
    {span : ReductionSpan Pattern} {definition : ValidatedCalculusLanguageDef}
    (adequacy : LanguageAdequacy span definition) (claim : Claim)
    (derivation : Nonempty (Derivation definition (adequacy.encode claim))) :
    (claim.toRichClaim span).Meaning :=
  (claim.meaning_iff_richClaim span).mp
    (adequacy.derivation_sound claim derivation)

/-- Structural-modal adequacy is the generic CertificateGSLT judgment adequacy theorem
specialized to OSLF structural-modal satisfaction. -/
def LanguageAdequacy.toJudgmentEncodingAdequacy
    {span : ReductionSpan Pattern} {definition : ValidatedCalculusLanguageDef}
    (adequacy : LanguageAdequacy span definition) :
    JudgmentEncodingAdequacy Claim (Claim.Meaning span) definition where
  encode := adequacy.encode
  derivation_sound := adequacy.derivation_sound

/-- A validated CertificateGSLT language with its OSLF semantic theorem becomes
the MIK authority for native spatial-behavioral claims. -/
def wireAuthority {AuthorityId : Type uAuthority}
    (authorityId : AuthorityId) {span : ReductionSpan Pattern}
    {definition : ValidatedCalculusLanguageDef}
    (adequacy : LanguageAdequacy span definition) :
    SemanticAuthority AuthorityId Claim :=
  judgmentWireAuthority authorityId
    adequacy.toJudgmentEncodingAdequacy

@[simp] theorem wireAuthority_check {AuthorityId : Type uAuthority}
    (authorityId : AuthorityId) {span : ReductionSpan Pattern}
    {definition : ValidatedCalculusLanguageDef}
    (adequacy : LanguageAdequacy span definition)
    (claim : Claim) (article : WireArticle) :
    (wireAuthority authorityId adequacy).check claim article =
      ((wireArticleAuthority authorityId definition).check
        (adequacy.encode claim) article) :=
  rfl

/-- A native checker is a NIK for native types only when each native
acceptance lowers to an article accepted by the MIK authority above. -/
abbrev NativeCheckedLowering {AuthorityId : Type uAuthority}
    (authorityId : AuthorityId) {span : ReductionSpan Pattern}
    {definition : ValidatedCalculusLanguageDef}
    (adequacy : LanguageAdequacy span definition)
    (NativeEvidence : Type uNative) :=
  CheckedLowering (wireAuthority authorityId adequacy) NativeEvidence

/-- Native acceptance entails the OSLF structural-modal meaning solely through
replay at the CertificateGSLT authority. -/
theorem NativeCheckedLowering.satisfies
    {AuthorityId : Type uAuthority} {authorityId : AuthorityId}
    {span : ReductionSpan Pattern}
    {definition : ValidatedCalculusLanguageDef}
    {adequacy : LanguageAdequacy span definition}
    {NativeEvidence : Type uNative}
    (lowering : NativeCheckedLowering authorityId adequacy NativeEvidence)
    {claim : Claim} {evidence : NativeEvidence}
    (accepted : lowering.nativeCheck claim evidence = true) :
    satisfiesOver span claim.formula claim.term :=
  lowering.sound accepted

/-- The same native acceptance entails the corresponding judgment in the
full predicate-valued OSLF system. -/
theorem NativeCheckedLowering.satisfiesRich
    {AuthorityId : Type uAuthority} {authorityId : AuthorityId}
    {span : ReductionSpan Pattern}
    {definition : ValidatedCalculusLanguageDef}
    {adequacy : LanguageAdequacy span definition}
    {NativeEvidence : Type uNative}
    (lowering : NativeCheckedLowering authorityId adequacy NativeEvidence)
    {claim : Claim} {evidence : NativeEvidence}
    (accepted : lowering.nativeCheck claim evidence = true) :
    (claim.toRichClaim span).Meaning :=
  (claim.meaning_iff_richClaim span).mp (lowering.satisfies accepted)

/-! ## Open articles for relation- and capability-backed steps

Zero and other reflective languages may derive a behavioral step from a
checked query row or capability receipt.  Those obligations belong in an
article's ordered premise context; they must not be turned into unconditional
leaf rules.  CertificateGSLT's open DAG already has exactly that representation. -/

/-- Adequacy of an open structural-modal language.  The semantic meaning of
every premise kind is explicit, and an open derivation becomes authoritative
only after all supplied premises have that meaning. -/
structure OpenLanguageAdequacy (span : ReductionSpan Pattern)
    (definition : ValidatedCalculusLanguageDef) where
  encode : Claim → Pattern
  premiseMeaning : Pattern → Prop
  derivation_sound : ∀ (context : List Pattern) (claim : Claim),
    (∀ premise ∈ context, premiseMeaning premise) →
      Nonempty (OpenDerivation definition context (encode claim)) →
        claim.Meaning span

/-- Open structural-modal adequacy is the generic open-judgment theorem
specialized to OSLF structural-modal satisfaction and the same ordered premise meaning. -/
def OpenLanguageAdequacy.toOpenJudgmentEncodingAdequacy
    {span : ReductionSpan Pattern} {definition : ValidatedCalculusLanguageDef}
    (adequacy : OpenLanguageAdequacy span definition) :
    OpenJudgmentEncodingAdequacy Claim (Claim.Meaning span) definition
    where
  encode := adequacy.encode
  premiseMeaning := adequacy.premiseMeaning
  derivation_sound := adequacy.derivation_sound

/-- A native claim together with the ordered semantic obligations on which
its open proof depends. -/
structure OpenClaim where
  context : List Pattern
  claim : Claim
deriving Repr

/-- Forget the native wrapper and expose the shared open-judgment claim. -/
def OpenClaim.toOpenJudgmentClaim (claim : OpenClaim) :
    OpenJudgmentClaim Claim :=
  ⟨claim.context, claim.claim⟩

/-- Meaning of an open claim: valid premises entail the structural-modal claim. -/
def OpenClaim.Meaning {span : ReductionSpan Pattern}
    {definition : ValidatedCalculusLanguageDef}
    (adequacy : OpenLanguageAdequacy span definition)
    (claim : OpenClaim) : Prop :=
  (∀ premise ∈ claim.context, adequacy.premiseMeaning premise) →
    claim.claim.Meaning span

/-- The existing versioned `WireArticle` carrier interpreted as an open
chronological DAG.  Premise references are checked against the claim's exact
ordered context; the same node, rule-instance, and target codecs are reused. -/
def openWireAuthority {AuthorityId : Type uAuthority}
    (authorityId : AuthorityId) {span : ReductionSpan Pattern}
    {definition : ValidatedCalculusLanguageDef}
    (adequacy : OpenLanguageAdequacy span definition) :
    SemanticAuthority AuthorityId OpenClaim where
  id := authorityId
  Certificate := WireArticle
  check := fun claim article =>
    (openJudgmentWireAuthority authorityId
      adequacy.toOpenJudgmentEncodingAdequacy).check
        claim.toOpenJudgmentClaim article
  Meaning := OpenClaim.Meaning adequacy
  sound := by
    intro claim article accepted
    exact (openJudgmentWireAuthority authorityId
      adequacy.toOpenJudgmentEncodingAdequacy).sound accepted

@[simp] theorem openWireAuthority_check
    {AuthorityId : Type uAuthority} (authorityId : AuthorityId)
    {span : ReductionSpan Pattern}
    {definition : ValidatedCalculusLanguageDef}
    (adequacy : OpenLanguageAdequacy span definition)
    (claim : OpenClaim) (article : WireArticle) :
    (openWireAuthority authorityId adequacy).check claim article =
      (decide (article.version = wireArticleVersion) &&
        decide (article.target = adequacy.encode claim.claim) &&
          checkOpenDAGBlocks definition claim.context article.target
            article.rootId [article.nodes]) :=
  rfl

/-- A NIK for an open structural-modal article must replay its native evidence at
the same CertificateGSLT open-DAG authority. -/
abbrev OpenNativeCheckedLowering {AuthorityId : Type uAuthority}
    (authorityId : AuthorityId) {span : ReductionSpan Pattern}
    {definition : ValidatedCalculusLanguageDef}
    (adequacy : OpenLanguageAdequacy span definition)
    (NativeEvidence : Type uNative) :=
  CheckedLowering (openWireAuthority authorityId adequacy) NativeEvidence

/-- Native acceptance of an open article preserves every declared premise
obligation and yields the OSLF claim when those obligations are discharged. -/
theorem OpenNativeCheckedLowering.satisfies
    {AuthorityId : Type uAuthority} {authorityId : AuthorityId}
    {span : ReductionSpan Pattern}
    {definition : ValidatedCalculusLanguageDef}
    {adequacy : OpenLanguageAdequacy span definition}
    {NativeEvidence : Type uNative}
    (lowering : OpenNativeCheckedLowering authorityId adequacy NativeEvidence)
    {claim : OpenClaim} {evidence : NativeEvidence}
    (accepted : lowering.nativeCheck claim evidence = true)
    (premisesValid :
      ∀ premise ∈ claim.context, adequacy.premiseMeaning premise) :
    satisfiesOver span claim.claim.formula claim.claim.term :=
  lowering.sound accepted premisesValid

/-- Discharging the open obligations also yields the corresponding judgment
in the full predicate-valued OSLF system. -/
theorem OpenNativeCheckedLowering.satisfiesRich
    {AuthorityId : Type uAuthority} {authorityId : AuthorityId}
    {span : ReductionSpan Pattern}
    {definition : ValidatedCalculusLanguageDef}
    {adequacy : OpenLanguageAdequacy span definition}
    {NativeEvidence : Type uNative}
    (lowering : OpenNativeCheckedLowering authorityId adequacy NativeEvidence)
    {claim : OpenClaim} {evidence : NativeEvidence}
    (accepted : lowering.nativeCheck claim evidence = true)
    (premisesValid :
      ∀ premise ∈ claim.context, adequacy.premiseMeaning premise) :
    (claim.claim.toRichClaim span).Meaning :=
  (claim.claim.meaning_iff_richClaim span).mp
    (lowering.satisfies accepted premisesValid)

end Mettapedia.OSLF.StructuralModal.CertificateGSLT
