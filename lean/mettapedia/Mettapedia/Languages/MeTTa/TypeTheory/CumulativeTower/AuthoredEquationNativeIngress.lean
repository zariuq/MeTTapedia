import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.AuthoredEquationInference
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.NativeIndexedFamilySource

/-!
# Authored equations as native typed construction

The finite inference layer authenticates an exact equation occurrence in an
authored source document.  Authentication alone is not typing: object-level
substitution, endpoint formation, and preservation belong to the hosted
dependent calculus.

This module joins those layers without making either impersonate the other.
An authenticated schema is instantiated by Prime's native simultaneous
substitution.  Endpoint typings then construct the existing proof-relevant
`TypedOccurrence`; when a presented family carries uniform preservation,
typing the source endpoint is sufficient.  The resulting native conversion
contains no checker and its receipt reflects to the exact authenticated source
occurrence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace AuthoredEquationNativeIngress

open AuthoredDeclarationSignature
open AuthoredEquationInference
open AuthoredIndexedFamilyPresentation
open AuthoredIndexedFamilyTypedConversion
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open NativeIndexedFamilies.Intrinsic
open NativeIndexedFamilySource
open Presentation
open Presentation.Declaration

/-! ## Native instantiation of authenticated source -/

/-- Instantiate an authenticated authored schema with Prime's object-level
simultaneous substitution.  This is deliberately distinct from generic
`Pattern` schema instantiation. -/
def instantiateAuthenticated
    {presented : PresentedCandidate} {claim : EquationClaim}
    (evidence : EquationEvidence (elaborate presented.source) claim)
    {ambient : Nat} (substitution : Sub Tower.Head claim.arity ambient) :
    EquationOccurrence
      (equationSchemas (elaborate presented.source))
      (Presentation.subst substitution claim.left)
      (Presentation.subst substitution claim.right) :=
  evidence.canonicalOccurrence.substitute substitution

/-- Complete endpoint evidence promotes an authenticated, natively
instantiated equation into the existing typed computation fibre. -/
def typedInstantiation
    (presented : PresentedCandidate) {claim : EquationClaim}
    (evidence : EquationEvidence (elaborate presented.source) claim)
    {ambient : Nat} (substitution : Sub Tower.Head claim.arity ambient)
    (context : Tower.Ctx ambient) (type : Tower.Tm ambient)
    (sourceTyping :
      HasType (extendRules Tower.rules presented.candidate.signature)
        context (Presentation.subst substitution claim.left) type)
    (targetTyping :
      HasType (extendRules Tower.rules presented.candidate.signature)
        context (Presentation.subst substitution claim.right) type) :
    TypedOccurrence presented context
      (Presentation.subst substitution claim.left)
      (Presentation.subst substitution claim.right) type where
  authored := instantiateAuthenticated evidence substitution
  sourceTyping := sourceTyping
  targetTyping := targetTyping

/-- Uniform preservation is the stronger native capability: after source
typing, target typing is constructed by the declaration law rather than
rechecked. -/
def typedInstantiationOfPreservation
    (authorized : PreservingPresentedCandidate) {claim : EquationClaim}
    (evidence : EquationEvidence
      (elaborate authorized.presented.source) claim)
    {ambient : Nat} (substitution : Sub Tower.Head claim.arity ambient)
    (context : Tower.Ctx ambient) (type : Tower.Tm ambient)
    (sourceTyping :
      HasType
        (extendRules Tower.rules authorized.presented.candidate.signature)
        context (Presentation.subst substitution claim.left) type) :
    TypedOccurrence authorized.presented context
      (Presentation.subst substitution claim.left)
      (Presentation.subst substitution claim.right) type :=
  authorized.typedOccurrence
    (instantiateAuthenticated evidence substitution) sourceTyping

@[simp] theorem typedInstantiation_authored
    (presented : PresentedCandidate) {claim : EquationClaim}
    (evidence : EquationEvidence (elaborate presented.source) claim)
    {ambient : Nat} (substitution : Sub Tower.Head claim.arity ambient)
    (context : Tower.Ctx ambient) (type : Tower.Tm ambient)
    (sourceTyping :
      HasType (extendRules Tower.rules presented.candidate.signature)
        context (Presentation.subst substitution claim.left) type)
    (targetTyping :
      HasType (extendRules Tower.rules presented.candidate.signature)
        context (Presentation.subst substitution claim.right) type) :
    (typedInstantiation presented evidence substitution context type
      sourceTyping targetTyping).authored =
      instantiateAuthenticated evidence substitution :=
  rfl

/-- The native receipt can be decoded back to the exact source occurrence and
object-level substitution that created it. -/
theorem typedInstantiation_nativeEvidence_reflects_source
    (presented : PresentedCandidate) {claim : EquationClaim}
    (evidence : EquationEvidence (elaborate presented.source) claim)
    {ambient : Nat} (substitution : Sub Tower.Head claim.arity ambient)
    (context : Tower.Ctx ambient) (type : Tower.Tm ambient)
    (sourceTyping :
      HasType (extendRules Tower.rules presented.candidate.signature)
        context (Presentation.subst substitution claim.left) type)
    (targetTyping :
      HasType (extendRules Tower.rules presented.candidate.signature)
        context (Presentation.subst substitution claim.right) type) :
    presented.receiptEquiv.symm
        (typedInstantiation presented evidence substitution context type
          sourceTyping targetTyping).nativeEvidence =
      instantiateAuthenticated evidence substitution := by
  exact TypedOccurrence.authored_of_nativeEvidence _

/-! ## Check-once boundary, construction thereafter -/

/-- A finite raw proof authenticates source membership once.  Given native
endpoint typings, it constructs a proof-relevant typed occurrence.  The
returned object is a native judgment and carries no checker invocation. -/
theorem checkedFact_constructs_typedInstantiation
    (presented : PresentedCandidate)
    (admitted : AdmittedFacts presented.source)
    {claim : EquationClaim} (proof : RawProof)
    (accepted :
      Mettapedia.GSLT.LanguageDef.InferenceChecker.checkRaw
        admitted.extension.target (encodeEquationClaim claim) proof = true)
    {ambient : Nat} (substitution : Sub Tower.Head claim.arity ambient)
    (context : Tower.Ctx ambient) (type : Tower.Tm ambient)
    (sourceTyping :
      HasType (extendRules Tower.rules presented.candidate.signature)
        context (Presentation.subst substitution claim.left) type)
    (targetTyping :
      HasType (extendRules Tower.rules presented.candidate.signature)
        context (Presentation.subst substitution claim.right) type) :
    Nonempty
      (TypedOccurrence presented context
        (Presentation.subst substitution claim.left)
        (Presentation.subst substitution claim.right) type) := by
  rcases checkRaw_reflects_equation_source admitted accepted with ⟨evidence⟩
  exact ⟨typedInstantiation presented evidence substitution context type
    sourceTyping targetTyping⟩

/-- Under a preservation capability, the same check-once boundary needs only
source typing; the native declaration law constructs the target judgment. -/
theorem checkedFact_constructs_typedInstantiationOfPreservation
    (authorized : PreservingPresentedCandidate)
    (admitted : AdmittedFacts authorized.presented.source)
    {claim : EquationClaim} (proof : RawProof)
    (accepted :
      Mettapedia.GSLT.LanguageDef.InferenceChecker.checkRaw
        admitted.extension.target (encodeEquationClaim claim) proof = true)
    {ambient : Nat} (substitution : Sub Tower.Head claim.arity ambient)
    (context : Tower.Ctx ambient) (type : Tower.Tm ambient)
    (sourceTyping :
      HasType
        (extendRules Tower.rules authorized.presented.candidate.signature)
        context (Presentation.subst substitution claim.left) type) :
    Nonempty
      (TypedOccurrence authorized.presented context
        (Presentation.subst substitution claim.left)
        (Presentation.subst substitution claim.right) type) := by
  rcases checkRaw_reflects_equation_source admitted accepted with ⟨evidence⟩
  exact ⟨typedInstantiationOfPreservation authorized evidence substitution
    context type sourceTyping⟩

/-! ## Native List positive and negative controls -/

private def nilSourceEquationRaw :
    SourceEquation authoredDeclarations nilEquation := by
  unfold authoredDeclarations
  exact
    .afterConstant listName { type := listType }
      (.afterConstant nilName { type := nilType }
        (.afterConstant consName { type := consType }
          (.afterConstant eliminateName { type := eliminateType }
            (.afterConstant identityEliminateName
              { type := identityEliminateType }
              (.here nilEquation
                [.equation consEquation, .equation identityEquation])))))

private def nilSourceEquation :
    SourceEquation (elaborate source) nilEquation := by
  rw [source_elaborates_exactly]
  exact nilSourceEquationRaw

private def nilLocated : LocatedEquation (elaborate source) where
  schema := nilEquation
  occurrence := nilSourceEquation

private def nilClaim : EquationClaim := nilLocated.claim

private def nilEvidence :
    EquationEvidence (elaborate source) nilClaim :=
  nilLocated.evidence

private theorem nativeListPresented_signature :
    nativeListPresentedCandidate.candidate.signature = rawSignature := by
  rfl

/-- The canonical List computation is constructed from authenticated source,
native substitution, and its two intrinsic endpoint typings. -/
noncomputable def canonicalNilTypedFromSource :
    TypedOccurrence nativeListPresentedCandidate contextAPZS
      (Presentation.subst ids nilClaim.left)
      (Presentation.subst ids nilClaim.right) nilIotaResultType :=
  typedInstantiation nativeListPresentedCandidate nilEvidence ids contextAPZS
    nilIotaResultType
    (by rw [nativeListPresented_signature]
        simpa [nilClaim, nilLocated, LocatedEquation.claim, nilEquation] using
      nilIotaReceipt.sourceTyping)
    (by rw [nativeListPresented_signature]
        simpa [nilClaim, nilLocated, LocatedEquation.claim, nilEquation] using
      nilIotaReceipt.targetTyping)

/-- Native execution follows directly from the constructed typed occurrence;
the checker is absent from the conversion object. -/
noncomputable def canonicalNilNativeConversionFromSource :=
  canonicalNilTypedFromSource.toNativeConversion

/-- The positive receipt round-trip retains the exact source position and
identity substitution. -/
theorem canonicalNilNativeReceipt_reflects_source :
    nativeListPresentedCandidate.receiptEquiv.symm
        canonicalNilTypedFromSource.nativeEvidence =
      instantiateAuthenticated
        (presented := nativeListPresentedCandidate) (claim := nilClaim)
        nilEvidence (ids : Sub Tower.Head nilClaim.arity 4) := by
  calc
    nativeListPresentedCandidate.receiptEquiv.symm
        canonicalNilTypedFromSource.nativeEvidence =
        canonicalNilTypedFromSource.authored :=
      TypedOccurrence.authored_of_nativeEvidence _
    _ = instantiateAuthenticated
        (presented := nativeListPresentedCandidate) (claim := nilClaim)
        nilEvidence (ids : Sub Tower.Head nilClaim.arity 4) := rfl

/-- The raw ill-typed nil instance and its authenticated source schema coexist,
but no typed occurrence can be constructed.  Authentication therefore cannot
be confused with native computational authority. -/
theorem authenticated_schema_does_not_type_raw_instance :
    Nonempty (EquationEvidence (elaborate source) nilClaim) ∧
      Nonempty
        (EquationOccurrence nativeSchemas untypedNilLeft undeclaredElement) ∧
      ∀ type : Tower.Tm 0,
        IsEmpty
          (TypedOccurrence nativeListPresentedCandidate (.nil : Tower.Ctx 0)
            untypedNilLeft undeclaredElement type) :=
  ⟨⟨nilEvidence⟩, ⟨untypedNilOccurrence⟩, untypedNil_has_no_typedOccurrence⟩

/-! ## Axiom audit -/

#print axioms instantiateAuthenticated
#print axioms typedInstantiation
#print axioms typedInstantiationOfPreservation
#print axioms typedInstantiation_nativeEvidence_reflects_source
#print axioms checkedFact_constructs_typedInstantiation
#print axioms checkedFact_constructs_typedInstantiationOfPreservation
#print axioms canonicalNilTypedFromSource
#print axioms canonicalNilNativeReceipt_reflects_source
#print axioms authenticated_schema_does_not_type_raw_instance

end AuthoredEquationNativeIngress
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
