import Mettapedia.Languages.MeTTa.Prime.NativeIndexedFamilyGradualGuarantee

/-!
# Typed substitution transport for gradual constructional families

A typed contextual substitution is itself part of the raw transport request.
It maps the complete authored source request and, when exact construction
evidence is present, composes the retained schema substitution and transports
both endpoint derivations.  The resulting construction step erases to exactly
the substituted raw request.

This produces an instance of Prime's existing constructional `ExactMap`.
Exact evidence therefore remains exact; suspension remains suspension; and
local blame is safely invalidated unless a separate reflection theorem is
available.  Revision invalidation commutes with the same map.  No second
gradual semantics, checker, or native-family dispatcher is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime
namespace NativeIndexedFamilyGradualTransport

open Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability
open Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.State
open Mettapedia.Languages.MeTTa.Prime.NativeGradualDependentGuarantee
open Mettapedia.Languages.MeTTa.Prime.NativeIndexedFamilyConstructionNIKSelection
open Mettapedia.Languages.MeTTa.Prime.NativeIndexedFamilyGradualGuarantee
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.AuthoredDeclarationSignature
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.AuthoredIndexedFamilyConstruction
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.AuthoredIndexedFamilyPresentation
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.AuthoredIndexedFamilyTypedConversion
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation.Declaration
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation.Declaration.ComputationAuthority

noncomputable section

/-! ## Typed raw-request substitution -/

/-- A contextual substitution applicable to one complete raw family request.
Its typing derivation is retained as data required to transport the source
judgment; arbitrary untyped substitutions cannot inhabit this structure. -/
structure RequestSubstitution {presented : PresentedCandidate}
    (request : RawSourceRequest presented) where
  targetArity : Nat
  targetContext : Tower.Ctx targetArity
  substitution : Sub Tower.Head request.arity targetArity
  typed : CtxMor
    (extendRules Tower.rules presented.candidate.signature)
    request.context targetContext substitution

/-- Apply a typed contextual substitution to every component of the raw
request, preserving the authored occurrence identity and source derivation. -/
def substituteRequest {presented : PresentedCandidate}
    (request : RawSourceRequest presented)
    (transport : RequestSubstitution request) : RawSourceRequest presented where
  arity := transport.targetArity
  context := transport.targetContext
  left := Presentation.subst transport.substitution request.left
  right := Presentation.subst transport.substitution request.right
  type := Presentation.subst transport.substitution request.type
  authored := request.authored.substitute transport.substitution
  sourceTyping := request.sourceTyping.substitute transport.typed

namespace RequestSubstitution

/-- Identity contextual transport for one complete request. -/
def identity {presented : PresentedCandidate}
    (request : RawSourceRequest presented) : RequestSubstitution request where
  targetArity := request.arity
  targetContext := request.context
  substitution := ids
  typed := CtxMor.identity _ _

/-- Composition of typed contextual transports.  The later transport is
indexed by the raw request produced by the earlier one. -/
def comp {presented : PresentedCandidate}
    {request : RawSourceRequest presented}
    (earlier : RequestSubstitution request)
    (later : RequestSubstitution (substituteRequest request earlier)) :
    RequestSubstitution request where
  targetArity := later.targetArity
  targetContext := later.targetContext
  substitution := Presentation.subComp later.substitution earlier.substitution
  typed := CtxMor.comp earlier.typed later.typed

end RequestSubstitution

/-- Heterogeneous extensionality for authored occurrences whose endpoint terms
are propositionally equal.  Occurrence identity is still determined by the
schema position and retained substitution. -/
theorem equationOccurrence_heq_of_fields
    {schemas : List EquationSchema} {n : Nat}
    {firstSource firstTarget secondSource secondTarget : Tower.Tm n}
    (sourceEquation : firstSource = secondSource)
    (targetEquation : firstTarget = secondTarget)
    (first : EquationOccurrence schemas firstSource firstTarget)
    (second : EquationOccurrence schemas secondSource secondTarget)
    (indexEquation : first.index = second.index)
    (substitutionEquation : HEq first.substitution second.substitution) :
    HEq first second := by
  subst secondSource
  subst secondTarget
  exact heq_of_eq
    (EquationOccurrence.ext first second indexEquation substitutionEquation)

/-- Raw request transport has a genuine identity law. -/
@[simp] theorem substituteRequest_identity
    {presented : PresentedCandidate}
    (request : RawSourceRequest presented) :
    substituteRequest request (RequestSubstitution.identity request) =
      request := by
  rcases request with
    ⟨arity, context, left, right, type, authored, sourceTyping⟩
  simp [substituteRequest, RequestSubstitution.identity]
  apply equationOccurrence_heq_of_fields
      (Presentation.subst_ids left) (Presentation.subst_ids right)
  · rfl
  · apply heq_of_eq
    funext index
    exact Presentation.subst_ids _

/-- Sequential typed substitutions equal their composed transport on the
complete raw request, including the retained authored occurrence. -/
theorem substituteRequest_comp
    {presented : PresentedCandidate}
    (request : RawSourceRequest presented)
    (earlier : RequestSubstitution request)
    (later : RequestSubstitution (substituteRequest request earlier)) :
    substituteRequest (substituteRequest request earlier) later =
      substituteRequest request (RequestSubstitution.comp earlier later) := by
  rcases request with
    ⟨arity, context, left, right, type, authored, sourceTyping⟩
  rcases earlier with
    ⟨middleArity, middleContext, earlierSubstitution, earlierTyped⟩
  rcases later with
    ⟨targetArity, targetContext, laterSubstitution, laterTyped⟩
  simp [substituteRequest, RequestSubstitution.comp]
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  apply equationOccurrence_heq_of_fields
      (Presentation.subst_subComp laterSubstitution earlierSubstitution left)
      (Presentation.subst_subComp laterSubstitution earlierSubstitution right)
  · rfl
  · apply heq_of_eq
    funext index
    exact Presentation.subst_subComp _ _ _

/-! ## Construction evidence is natural under typed substitution -/

/-- The raw erasure of a substituted construction step is the substituted raw
erasure of the original step.  This is equality of the complete structured
request, including authored occurrence identity. -/
theorem substitute_ofConstructed
    {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented}
    {index : TypingIndex Tower.Head}
    {source target : NativeIndexedState presented index}
    (step : TypedNativePresentation.ConstructedStep typed source target)
    (transport : RequestSubstitution (RawSourceRequest.ofConstructed step)) :
    substituteRequest (RawSourceRequest.ofConstructed step) transport =
      RawSourceRequest.ofConstructed
        (step.substitute transport.targetContext transport.substitution
          transport.typed) := by
  rcases source with ⟨sourceTerm, sourceTyping⟩
  rcases target with ⟨targetTerm, targetTyping⟩
  rcases step with
    ⟨schemaIndex, innerSubstitution, innerTyped, sourceEquation,
      targetEquation, adjustment⟩
  dsimp at sourceEquation targetEquation
  subst sourceTerm
  subst targetTerm
  cases transport
  simp [substituteRequest, RawSourceRequest.ofConstructed,
    TypedNativePresentation.ConstructedStep.substitute,
    TypedNativePresentation.ConstructedStep.toTypedOccurrence_authored]
  apply EquationOccurrence.ext <;> rfl

namespace ConstructedEvidence

/-- Transport exact construction evidence along a typed contextual
substitution.  The proof that evidence lies over the new raw request is the
erasure naturality theorem above. -/
def substitute {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented}
    {request : RawSourceRequest presented}
    (evidence : ConstructedEvidence typed request)
    (transport : RequestSubstitution request) :
    ConstructedEvidence typed (substituteRequest request transport) := by
  rcases evidence with ⟨index, source, target, step, request_eq⟩
  subst request
  let substitutedStep := step.substitute transport.targetContext
    transport.substitution transport.typed
  exact
    { index := _
      source := _
      target := _
      step := substitutedStep
      request_eq := (substitute_ofConstructed step transport).symm }

end ConstructedEvidence

/-! ## The existing gradual exact-map interface -/

/-- Raw inputs to contextual transport retain both the family request and the
typed substitution to apply to it. -/
def substitutionSourceFibre {presented : PresentedCandidate}
    (typed : TypedNativePresentation presented) : Fibre where
  Raw := Sigma fun request : RawSourceRequest presented =>
    RequestSubstitution request
  Exact := fun command => ConstructedEvidence typed command.1

/-- Typed contextual substitution as a constructional gradual map. -/
def substitutionMap {presented : PresentedCandidate}
    (typed : TypedNativePresentation presented) :
    ExactMap (substitutionSourceFibre typed) (constructionFibre typed) where
  mapRaw command := substituteRequest command.1 command.2
  mapExact evidence := ConstructedEvidence.substitute evidence _

/-- Typed substitution earns the complete forward-safe gradual law package. -/
def substitutionSafeTransportLaws {presented : PresentedCandidate}
    (typed : TypedNativePresentation presented) :
    SafeTransportLaws (substitutionMap typed) :=
  safeTransportLaws _

@[simp] theorem substitute_exact {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented}
    (command : (substitutionSourceFibre typed).Raw)
    (evidence : ConstructedEvidence typed command.1) :
    mapSafe (substitutionMap typed)
        (.exact evidence : State (substitutionSourceFibre typed) command) =
      .exact (ConstructedEvidence.substitute evidence command.2) :=
  rfl

@[simp] theorem substitute_suspended {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented}
    (command : (substitutionSourceFibre typed).Raw) :
    mapSafe (substitutionMap typed)
        (.suspended : State (substitutionSourceFibre typed) command) =
      .suspended :=
  rfl

/-- Negative evidence cannot be transported merely from forward
constructionality; it is invalidated to suspension. -/
@[simp] theorem substitute_refuted {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented}
    (command : (substitutionSourceFibre typed).Raw)
    (blame : Refutation (substitutionSourceFibre typed) command) :
    mapSafe (substitutionMap typed) (.refuted blame) = .suspended :=
  rfl

/-- Revision invalidation and typed family substitution commute. -/
theorem substitute_activateAt {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented}
    (command : (substitutionSourceFibre typed).Raw)
    {Revision : Type} [DecidableEq Revision]
    (cached current : Revision)
    (state : State (substitutionSourceFibre typed) command) :
    mapSafe (substitutionMap typed) (state.activateAt cached current) =
      (mapSafe (substitutionMap typed) state).activateAt cached current :=
  mapSafe_activateAt _ cached current state

/-- After supported exact transport, the existing constructional runner
realizes the substituted step directly. -/
theorem run_substituted_exact_is_realized
    {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented}
    (command : (substitutionSourceFibre typed).Raw)
    (evidence : ConstructedEvidence typed command.1) :
    Outcome.IsRealized
      (runState typed
        (mapSafe (substitutionMap typed)
          (.exact evidence : State (substitutionSourceFibre typed) command))).outcome := by
  rw [substitute_exact]
  exact run_exact_is_realized
    (ConstructedEvidence.substitute evidence command.2)

/-- Unsupported gradual transport remains raw fallback after the target
request has been transformed; absence of evidence is not rejection. -/
theorem run_substituted_suspended_is_fallback
    {presented : PresentedCandidate}
    {typed : TypedNativePresentation presented}
    (command : (substitutionSourceFibre typed).Raw) :
    Outcome.IsFallback
      (runState typed
        (mapSafe (substitutionMap typed)
          (.suspended : State (substitutionSourceFibre typed) command))).outcome := by
  rw [substitute_suspended]
  exact run_suspended_is_fallback (substituteRequest command.1 command.2)

/-! ## Nonidentity List weakening control -/

namespace Canary

open AuthoredIndexedFamilyConstruction.NativeList

def nilWeakening : RequestSubstitution
    (RawSourceRequest.ofConstructed canonicalNilConstructedStep) where
  targetArity := _ + 1
  targetContext := .snoc
    (RawSourceRequest.ofConstructed canonicalNilConstructedStep).context
    (RawSourceRequest.ofConstructed canonicalNilConstructedStep).type
  substitution := renSub wk
  typed := CtxRen.toCtxMor (by
    intro index
    rfl)

def nilWeakeningCommand : (substitutionSourceFibre typedNativePresentation).Raw :=
  ⟨RawSourceRequest.ofConstructed canonicalNilConstructedStep, nilWeakening⟩

noncomputable def nilWeakeningEvidence :
    ConstructedEvidence typedNativePresentation nilWeakeningCommand.1 :=
  ConstructedEvidence.ofStep canonicalNilConstructedStep

/-- Positive control: nonidentity context weakening transports the exact
List-nil construction and the shared runner realizes it natively. -/
theorem weakened_nil_is_realized :
    Outcome.IsRealized
      (runState typedNativePresentation
        (mapSafe (substitutionMap typedNativePresentation)
          (.exact nilWeakeningEvidence))).outcome :=
  run_substituted_exact_is_realized nilWeakeningCommand nilWeakeningEvidence

/-- Negative control: the same nonidentity weakening without exact evidence
retains the substituted request and falls back. -/
theorem weakened_nil_without_evidence_is_fallback :
    Outcome.IsFallback
      (runState typedNativePresentation
        (mapSafe (substitutionMap typedNativePresentation)
          (.suspended : State (substitutionSourceFibre typedNativePresentation)
            nilWeakeningCommand))).outcome :=
  run_substituted_suspended_is_fallback nilWeakeningCommand

end Canary

/-! ## Axiom audit -/

#print axioms substitute_ofConstructed
#print axioms equationOccurrence_heq_of_fields
#print axioms substituteRequest_identity
#print axioms substituteRequest_comp
#print axioms ConstructedEvidence.substitute
#print axioms substitutionMap
#print axioms substitutionSafeTransportLaws
#print axioms substitute_exact
#print axioms substitute_suspended
#print axioms substitute_refuted
#print axioms substitute_activateAt
#print axioms run_substituted_exact_is_realized
#print axioms run_substituted_suspended_is_fallback
#print axioms Canary.weakened_nil_is_realized
#print axioms Canary.weakened_nil_without_evidence_is_fallback

end

end NativeIndexedFamilyGradualTransport
end Mettapedia.Languages.MeTTa.Prime
