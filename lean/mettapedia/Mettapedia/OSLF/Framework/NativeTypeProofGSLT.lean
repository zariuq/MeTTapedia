import Mettapedia.OSLF.Framework.NativeTypeTheory
import Mettapedia.OSLF.Framework.OSLFProofGSLTAuthority
import Mettapedia.OSLF.Framework.ReductionSpanTypeSynthesis

/-!
# ProofGSLT replay for OSLF native-type claims

OSLF supplies the semantic meaning of a native spatial-behavioral type.
ProofGSLT supplies the finite, versioned article checker.  This module states
the exact bridge required before a native inference kernel may treat an
accepted article as evidence of native inhabitation.

The bridge is deliberately parameterized by a proved presentation adequacy
map.  A presentation that merely spells a judgment `NativeSat` gains no
authority: its derivations must be proved sound for the OSLF reduction span.
Once that theorem exists, the existing `WireArticle` authority and
`CheckedLowering` machinery provide the MIK and NIK boundaries without a
second checker semantics.
-/

namespace Mettapedia.OSLF.Framework.NativeTypeProofGSLT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Framework.NativeTypeTheory
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.ProofGSLT
open Mettapedia.OSLF.Framework.OSLFProofGSLTAuthority
open Mettapedia.OSLF.Framework.ReductionSpanTypeSynthesis

universe uAuthority uNative

/-- One semantic native-type judgment, before choosing its proof syntax. -/
structure Claim where
  term : Pattern
  nativeType : NativeType
deriving Repr

/-- Meaning of a native-type claim in one OSLF-derived reduction span. -/
def Claim.Meaning (span : ReductionSpan Pattern) (claim : Claim) : Prop :=
  satisfiesOver span claim.nativeType claim.term

/-- Interpret the readable finitary native syntax as a rich predicate-valued
OSLF native judgment over the same reduction span. -/
def Claim.toRichClaim (claim : Claim) (span : ReductionSpan Pattern) :
    NativeClaim (spanOSLF span) where
  nativeType :=
    predicateNativeType span (satisfiesOver span claim.nativeType)
  term := claim.term

/-- The readable native syntax is a denotational fragment of the rich OSLF
system, not a second native-type semantics. -/
theorem Claim.meaning_iff_richClaim (span : ReductionSpan Pattern)
    (claim : Claim) :
    claim.Meaning span ↔ (claim.toRichClaim span).Meaning :=
  Iff.rfl

/-- The substantive theorem required of a ProofGSLT presentation for native
types.  `encode` may choose any readable judgment syntax, but every derivation
of that syntax must denote OSLF native inhabitation. -/
structure PresentationAdequacy (span : ReductionSpan Pattern)
    (presentation : ValidatedPresentation) where
  encode : Claim → Pattern
  derivation_sound : ∀ claim,
    Nonempty (Derivation presentation (encode claim)) → claim.Meaning span

/-- Adequacy of the readable syntax also proves the corresponding rich OSLF
native judgment. -/
theorem PresentationAdequacy.derivation_sound_rich
    {span : ReductionSpan Pattern} {presentation : ValidatedPresentation}
    (adequacy : PresentationAdequacy span presentation) (claim : Claim)
    (derivation : Nonempty (Derivation presentation (adequacy.encode claim))) :
    (claim.toRichClaim span).Meaning :=
  (claim.meaning_iff_richClaim span).mp
    (adequacy.derivation_sound claim derivation)

/-- Native-type adequacy is the generic ProofGSLT judgment adequacy theorem
specialized to OSLF native inhabitation. -/
def PresentationAdequacy.toJudgmentPresentationAdequacy
    {span : ReductionSpan Pattern} {presentation : ValidatedPresentation}
    (adequacy : PresentationAdequacy span presentation) :
    JudgmentPresentationAdequacy Claim (Claim.Meaning span) presentation where
  encode := adequacy.encode
  derivation_sound := adequacy.derivation_sound

/-- A validated ProofGSLT presentation with its OSLF semantic theorem becomes
the MIK authority for native spatial-behavioral claims. -/
def wireAuthority {AuthorityId : Type uAuthority}
    (authorityId : AuthorityId) {span : ReductionSpan Pattern}
    {presentation : ValidatedPresentation}
    (adequacy : PresentationAdequacy span presentation) :
    SemanticAuthority AuthorityId Claim :=
  judgmentWireAuthority authorityId
    adequacy.toJudgmentPresentationAdequacy

@[simp] theorem wireAuthority_check {AuthorityId : Type uAuthority}
    (authorityId : AuthorityId) {span : ReductionSpan Pattern}
    {presentation : ValidatedPresentation}
    (adequacy : PresentationAdequacy span presentation)
    (claim : Claim) (article : WireArticle) :
    (wireAuthority authorityId adequacy).check claim article =
      ((wireArticleAuthority authorityId presentation).check
        (adequacy.encode claim) article) :=
  rfl

/-- A native checker is a NIK for native types only when each native
acceptance lowers to an article accepted by the MIK authority above. -/
abbrev NativeCheckedLowering {AuthorityId : Type uAuthority}
    (authorityId : AuthorityId) {span : ReductionSpan Pattern}
    {presentation : ValidatedPresentation}
    (adequacy : PresentationAdequacy span presentation)
    (NativeEvidence : Type uNative) :=
  CheckedLowering (wireAuthority authorityId adequacy) NativeEvidence

/-- Native acceptance entails the OSLF native-type meaning solely through
replay at the ProofGSLT authority. -/
theorem NativeCheckedLowering.satisfies
    {AuthorityId : Type uAuthority} {authorityId : AuthorityId}
    {span : ReductionSpan Pattern}
    {presentation : ValidatedPresentation}
    {adequacy : PresentationAdequacy span presentation}
    {NativeEvidence : Type uNative}
    (lowering : NativeCheckedLowering authorityId adequacy NativeEvidence)
    {claim : Claim} {evidence : NativeEvidence}
    (accepted : lowering.nativeCheck claim evidence = true) :
    satisfiesOver span claim.nativeType claim.term :=
  lowering.sound accepted

/-- The same native acceptance entails the corresponding judgment in the
full predicate-valued OSLF system. -/
theorem NativeCheckedLowering.satisfiesRich
    {AuthorityId : Type uAuthority} {authorityId : AuthorityId}
    {span : ReductionSpan Pattern}
    {presentation : ValidatedPresentation}
    {adequacy : PresentationAdequacy span presentation}
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
leaf rules.  ProofGSLT's open DAG already has exactly that representation. -/

/-- Adequacy of an open native-type presentation.  The semantic meaning of
every premise kind is explicit, and an open derivation becomes authoritative
only after all supplied premises have that meaning. -/
structure OpenPresentationAdequacy (span : ReductionSpan Pattern)
    (presentation : ValidatedPresentation) where
  encode : Claim → Pattern
  premiseMeaning : Pattern → Prop
  derivation_sound : ∀ (context : List Pattern) (claim : Claim),
    (∀ premise ∈ context, premiseMeaning premise) →
      Nonempty (OpenDerivation presentation context (encode claim)) →
        claim.Meaning span

/-- Open native-type adequacy is the generic open-judgment theorem
specialized to OSLF native inhabitation and the same ordered premise meaning. -/
def OpenPresentationAdequacy.toOpenJudgmentPresentationAdequacy
    {span : ReductionSpan Pattern} {presentation : ValidatedPresentation}
    (adequacy : OpenPresentationAdequacy span presentation) :
    OpenJudgmentPresentationAdequacy Claim (Claim.Meaning span) presentation
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

/-- Meaning of an open claim: valid premises entail the native-type claim. -/
def OpenClaim.Meaning {span : ReductionSpan Pattern}
    {presentation : ValidatedPresentation}
    (adequacy : OpenPresentationAdequacy span presentation)
    (claim : OpenClaim) : Prop :=
  (∀ premise ∈ claim.context, adequacy.premiseMeaning premise) →
    claim.claim.Meaning span

/-- The existing versioned `WireArticle` carrier interpreted as an open
chronological DAG.  Premise references are checked against the claim's exact
ordered context; the same node, rule-instance, and target codecs are reused. -/
def openWireAuthority {AuthorityId : Type uAuthority}
    (authorityId : AuthorityId) {span : ReductionSpan Pattern}
    {presentation : ValidatedPresentation}
    (adequacy : OpenPresentationAdequacy span presentation) :
    SemanticAuthority AuthorityId OpenClaim where
  id := authorityId
  Certificate := WireArticle
  check := fun claim article =>
    (openJudgmentWireAuthority authorityId
      adequacy.toOpenJudgmentPresentationAdequacy).check
        claim.toOpenJudgmentClaim article
  Meaning := OpenClaim.Meaning adequacy
  sound := by
    intro claim article accepted
    exact (openJudgmentWireAuthority authorityId
      adequacy.toOpenJudgmentPresentationAdequacy).sound accepted

@[simp] theorem openWireAuthority_check
    {AuthorityId : Type uAuthority} (authorityId : AuthorityId)
    {span : ReductionSpan Pattern}
    {presentation : ValidatedPresentation}
    (adequacy : OpenPresentationAdequacy span presentation)
    (claim : OpenClaim) (article : WireArticle) :
    (openWireAuthority authorityId adequacy).check claim article =
      (decide (article.version = wireArticleVersion) &&
        decide (article.target = adequacy.encode claim.claim) &&
          checkOpenDAGBlocks presentation claim.context article.target
            article.rootId [article.nodes]) :=
  rfl

/-- A NIK for an open native-type article must replay its native evidence at
the same ProofGSLT open-DAG authority. -/
abbrev OpenNativeCheckedLowering {AuthorityId : Type uAuthority}
    (authorityId : AuthorityId) {span : ReductionSpan Pattern}
    {presentation : ValidatedPresentation}
    (adequacy : OpenPresentationAdequacy span presentation)
    (NativeEvidence : Type uNative) :=
  CheckedLowering (openWireAuthority authorityId adequacy) NativeEvidence

/-- Native acceptance of an open article preserves every declared premise
obligation and yields the OSLF claim when those obligations are discharged. -/
theorem OpenNativeCheckedLowering.satisfies
    {AuthorityId : Type uAuthority} {authorityId : AuthorityId}
    {span : ReductionSpan Pattern}
    {presentation : ValidatedPresentation}
    {adequacy : OpenPresentationAdequacy span presentation}
    {NativeEvidence : Type uNative}
    (lowering : OpenNativeCheckedLowering authorityId adequacy NativeEvidence)
    {claim : OpenClaim} {evidence : NativeEvidence}
    (accepted : lowering.nativeCheck claim evidence = true)
    (premisesValid :
      ∀ premise ∈ claim.context, adequacy.premiseMeaning premise) :
    satisfiesOver span claim.claim.nativeType claim.claim.term :=
  lowering.sound accepted premisesValid

/-- Discharging the open obligations also yields the corresponding judgment
in the full predicate-valued OSLF system. -/
theorem OpenNativeCheckedLowering.satisfiesRich
    {AuthorityId : Type uAuthority} {authorityId : AuthorityId}
    {span : ReductionSpan Pattern}
    {presentation : ValidatedPresentation}
    {adequacy : OpenPresentationAdequacy span presentation}
    {NativeEvidence : Type uNative}
    (lowering : OpenNativeCheckedLowering authorityId adequacy NativeEvidence)
    {claim : OpenClaim} {evidence : NativeEvidence}
    (accepted : lowering.nativeCheck claim evidence = true)
    (premisesValid :
      ∀ premise ∈ claim.context, adequacy.premiseMeaning premise) :
    (claim.claim.toRichClaim span).Meaning :=
  (claim.claim.meaning_iff_richClaim span).mp
    (lowering.satisfies accepted premisesValid)

end Mettapedia.OSLF.Framework.NativeTypeProofGSLT
