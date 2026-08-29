import Mettapedia.Languages.MeTTa.Prime.NativeConversionPathNIKSelection
import Mettapedia.Languages.MeTTa.Prime.NativeGradualDependentGuarantee

/-!
# Gradual typed transport for complete native conversion paths

Complete authored indexed-family conversions retain every intermediate typed
state, occurrence, symmetry, and composition node.  Their native realization
is the exact free structural lift of the primitive receipt equivalence.  This
module displays that realization over the unchanged authored path and connects
it to Prime's existing gradual-dependent state discipline.

Typed substitution transports both the authored and native trees.  Receipt
naturality proves that the transported native tree is exactly the structural
lift of the transported authored tree.  Exact evidence therefore remains
exact, while suspension and unsupported local blame remain ordinary fallback.
Revision staleness forgets only the optional native realization.

The exact branch agrees with the complete-path face already selected by NIK.
No checker, certificate replay, endpoint quotient, or second conversion
semantics is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime
namespace NativeConversionPathGradualTransport

open Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability
open Mettapedia.Languages.MeTTa.Prime.GradualDependentCapability.State
open Mettapedia.Languages.MeTTa.Prime.NativeConversionPathNIKSelection
open Mettapedia.Languages.MeTTa.Prime.NativeGradualDependentGuarantee
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.AuthoredDeclarationSignature
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.AuthoredIndexedFamilyConversionPath
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.AuthoredIndexedFamilyPresentation
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.AuthoredIndexedFamilyReceiptNaturality
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.AuthoredIndexedFamilyTypedConversion
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation.Declaration
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.Presentation.Declaration.ComputationAuthority

noncomputable section

/-! ## Native path evidence displayed over an authored path -/

/-- Exact native evidence for one complete authored conversion.  Equality to
the established structural lift prevents a cache from replacing the retained
conversion tree by an endpoint-equivalent but provenance-distinct path. -/
structure NativePathEvidence (presented : PresentedCandidate)
    {index : TypingIndex Tower.Head}
    (source target : NativeIndexedState presented index)
    (path : AuthoredConversion presented source target) where
  native : NativeConversion presented source target
  native_eq : native = authoredToNativePath presented path

namespace NativePathEvidence

/-- The structural lift itself supplies exact evidence without replaying a
checker. -/
def ofPath (presented : PresentedCandidate)
    {index : TypingIndex Tower.Head}
    {source target : NativeIndexedState presented index}
    (path : AuthoredConversion presented source target) :
    NativePathEvidence presented source target path where
  native := authoredToNativePath presented path
  native_eq := rfl

/-- Exact path evidence is already a complete-face receipt.  Its inverse law
recovers the whole authored tree, not just its endpoints. -/
def toReceipt {presented : PresentedCandidate}
    {index : TypingIndex Tower.Head}
    {source target : NativeIndexedState presented index}
    {path : AuthoredConversion presented source target}
    (evidence : NativePathEvidence presented source target path) :
    Generic.Receipt
      (AuthoredConversion presented source target)
      (NativeConversion presented source target)
      (nativeToAuthoredPath presented) where
  face := .completePath
  source := path
  outcome := .realized evidence.native
  exact := by
    rw [evidence.native_eq]
    exact authored_native_path_roundtrip presented path

end NativePathEvidence

/-- The complete authored conversion remains the raw value.  Exactness is an
identified native realization of that very tree. -/
def pathFibre (presented : PresentedCandidate)
    {index : TypingIndex Tower.Head}
    (source target : NativeIndexedState presented index) : Fibre where
  Raw := AuthoredConversion presented source target
  Exact := NativePathEvidence presented source target

/-- Fallback retains the complete authored path verbatim. -/
def fallbackReceipt {presented : PresentedCandidate}
    {index : TypingIndex Tower.Head}
    {source target : NativeIndexedState presented index}
    (path : AuthoredConversion presented source target) :
    Generic.Receipt
      (AuthoredConversion presented source target)
      (NativeConversion presented source target)
      (nativeToAuthoredPath presented) where
  face := .primitiveStep
  source := path
  outcome := .outsideFragment
  exact := trivial

/-- Interpret gradual path evidence through the existing complete-path
receipt contract.  Exact evidence is projected directly; every other state
retains the authored tree for ordinary fallback. -/
def runState {presented : PresentedCandidate}
    {index : TypingIndex Tower.Head}
    {source target : NativeIndexedState presented index}
    {path : AuthoredConversion presented source target} :
    State (pathFibre presented source target) path ->
      Generic.Receipt
        (AuthoredConversion presented source target)
        (NativeConversion presented source target)
        (nativeToAuthoredPath presented)
  | .suspended => fallbackReceipt path
  | .exact evidence => evidence.toReceipt
  | .refuted _ => fallbackReceipt path

@[simp] theorem runState_source {presented : PresentedCandidate}
    {index : TypingIndex Tower.Head}
    {source target : NativeIndexedState presented index}
    {path : AuthoredConversion presented source target}
    (state : State (pathFibre presented source target) path) :
    (runState state).source = path := by
  cases state <;> rfl

@[simp] theorem run_exact_outcome {presented : PresentedCandidate}
    {index : TypingIndex Tower.Head}
    {source target : NativeIndexedState presented index}
    {path : AuthoredConversion presented source target}
    (evidence : NativePathEvidence presented source target path) :
    (runState (.exact evidence)).outcome = .realized evidence.native :=
  rfl

@[simp] theorem run_suspended_outcome {presented : PresentedCandidate}
    {index : TypingIndex Tower.Head}
    {source target : NativeIndexedState presented index}
    (path : AuthoredConversion presented source target) :
    (runState
      (.suspended : State (pathFibre presented source target) path)).outcome =
        .outsideFragment :=
  rfl

@[simp] theorem run_refuted_outcome {presented : PresentedCandidate}
    {index : TypingIndex Tower.Head}
    {source target : NativeIndexedState presented index}
    {path : AuthoredConversion presented source target}
    (blame : Refutation (pathFibre presented source target) path) :
    (runState (.refuted blame)).outcome = .outsideFragment :=
  rfl

/-- Exact gradual execution is the same structural result as the existing
complete-path native face. -/
theorem exact_outcome_agrees_with_complete_face
    {presented : PresentedCandidate}
    {index : TypingIndex Tower.Head}
    {source target : NativeIndexedState presented index}
    (path : AuthoredConversion presented source target) :
    (runState (.exact (NativePathEvidence.ofPath presented path))).outcome =
      (Generic.completeReceipt
        (State := NativeIndexedState presented)
        (AuthoredStep := AuthoredIndexedStep presented)
        (NativeStep := NativeIndexedStep presented)
        (fun source target => authoredNativeStepEquiv presented source target)
        path).outcome :=
  rfl

/-- A structurally valid authored path cannot carry sound negative evidence:
its complete native lift is constructible. -/
theorem authored_path_not_refutable {presented : PresentedCandidate}
    {index : TypingIndex Tower.Head}
    {source target : NativeIndexedState presented index}
    (path : AuthoredConversion presented source target)
    (blame : Refutation (pathFibre presented source target) path) : False :=
  blame.refutes (NativePathEvidence.ofPath presented path)

/-! ## Typed substitution of exact path evidence -/

namespace NativePathEvidence

/-- Transport exact path evidence through a typed contextual substitution.
Receipt naturality identifies the transported native tree with the structural
lift of the transported authored tree. -/
def substitute {presented : PresentedCandidate}
    (naturality : ReceiptNaturality presented)
    {n m : Nat}
    {sourceContext : Tower.Ctx n} {targetContext : Tower.Ctx m}
    {type : Tower.Tm n}
    (substitution : Sub Tower.Head n m)
    (typed : CtxMor
      (extendRules Tower.rules presented.candidate.signature)
      sourceContext targetContext substitution)
    {source target : NativeIndexedState presented
      ⟨n, sourceContext, type⟩}
    {path : AuthoredConversion presented source target}
    (evidence : NativePathEvidence presented source target path) :
    NativePathEvidence presented
      (substituteState presented substitution typed source)
      (substituteState presented substitution typed target)
      (substituteAuthoredPath presented substitution typed path) where
  native := substituteNativePath presented substitution typed evidence.native
  native_eq := by
    rw [evidence.native_eq]
    exact (authoredToNativePath_substitute naturality substitution typed path).symm

end NativePathEvidence

/-- Typed substitution as an exact map between complete conversion-path
fibres. -/
def pathSubstitutionMap {presented : PresentedCandidate}
    (naturality : ReceiptNaturality presented)
    {n m : Nat}
    {sourceContext : Tower.Ctx n} {targetContext : Tower.Ctx m}
    {type : Tower.Tm n}
    (substitution : Sub Tower.Head n m)
    (typed : CtxMor
      (extendRules Tower.rules presented.candidate.signature)
      sourceContext targetContext substitution)
    (source target : NativeIndexedState presented
      ⟨n, sourceContext, type⟩) :
    ExactMap
      (pathFibre presented source target)
      (pathFibre presented
        (substituteState presented substitution typed source)
        (substituteState presented substitution typed target)) where
  mapRaw := substituteAuthoredPath presented substitution typed
  mapExact := NativePathEvidence.substitute naturality substitution typed

/-- Complete conversion transport earns the common forward-safe gradual law
package. -/
def pathSubstitutionSafeTransportLaws {presented : PresentedCandidate}
    (naturality : ReceiptNaturality presented)
    {n m : Nat}
    {sourceContext : Tower.Ctx n} {targetContext : Tower.Ctx m}
    {type : Tower.Tm n}
    (substitution : Sub Tower.Head n m)
    (typed : CtxMor
      (extendRules Tower.rules presented.candidate.signature)
      sourceContext targetContext substitution)
    (source target : NativeIndexedState presented
      ⟨n, sourceContext, type⟩) :
    SafeTransportLaws
      (pathSubstitutionMap naturality substitution typed source target) :=
  safeTransportLaws _

@[simp] theorem substitute_exact {presented : PresentedCandidate}
    (naturality : ReceiptNaturality presented)
    {n m : Nat}
    {sourceContext : Tower.Ctx n} {targetContext : Tower.Ctx m}
    {type : Tower.Tm n}
    (substitution : Sub Tower.Head n m)
    (typed : CtxMor
      (extendRules Tower.rules presented.candidate.signature)
      sourceContext targetContext substitution)
    {source target : NativeIndexedState presented
      ⟨n, sourceContext, type⟩}
    {path : AuthoredConversion presented source target}
    (evidence : NativePathEvidence presented source target path) :
    mapSafe (pathSubstitutionMap naturality substitution typed source target)
        (.exact evidence) =
      .exact (evidence.substitute naturality substitution typed) :=
  rfl

@[simp] theorem substitute_suspended {presented : PresentedCandidate}
    (naturality : ReceiptNaturality presented)
    {n m : Nat}
    {sourceContext : Tower.Ctx n} {targetContext : Tower.Ctx m}
    {type : Tower.Tm n}
    (substitution : Sub Tower.Head n m)
    (typed : CtxMor
      (extendRules Tower.rules presented.candidate.signature)
      sourceContext targetContext substitution)
    (source target : NativeIndexedState presented
      ⟨n, sourceContext, type⟩)
    (path : AuthoredConversion presented source target) :
    mapSafe (pathSubstitutionMap naturality substitution typed source target)
        (.suspended : State (pathFibre presented source target) path) =
      .suspended :=
  rfl

@[simp] theorem substitute_refuted {presented : PresentedCandidate}
    (naturality : ReceiptNaturality presented)
    {n m : Nat}
    {sourceContext : Tower.Ctx n} {targetContext : Tower.Ctx m}
    {type : Tower.Tm n}
    (substitution : Sub Tower.Head n m)
    (typed : CtxMor
      (extendRules Tower.rules presented.candidate.signature)
      sourceContext targetContext substitution)
    {source target : NativeIndexedState presented
      ⟨n, sourceContext, type⟩}
    {path : AuthoredConversion presented source target}
    (blame : Refutation (pathFibre presented source target) path) :
    mapSafe (pathSubstitutionMap naturality substitution typed source target)
        (.refuted blame) = .suspended :=
  rfl

/-- Revision invalidation commutes with complete path transport. -/
theorem substitute_activateAt {presented : PresentedCandidate}
    (naturality : ReceiptNaturality presented)
    {n m : Nat}
    {sourceContext : Tower.Ctx n} {targetContext : Tower.Ctx m}
    {type : Tower.Tm n}
    (substitution : Sub Tower.Head n m)
    (typed : CtxMor
      (extendRules Tower.rules presented.candidate.signature)
      sourceContext targetContext substitution)
    {source target : NativeIndexedState presented
      ⟨n, sourceContext, type⟩}
    {path : AuthoredConversion presented source target}
    {Revision : Type} [DecidableEq Revision]
    (cached current : Revision)
    (state : State (pathFibre presented source target) path) :
    mapSafe (pathSubstitutionMap naturality substitution typed source target)
        (state.activateAt cached current) =
      (mapSafe
        (pathSubstitutionMap naturality substitution typed source target)
        state).activateAt cached current :=
  mapSafe_activateAt _ cached current state

/-! ## Nonidentity List path controls and the NIK join -/

namespace Canary

open AuthoredIndexedFamilyConversionPath.Canary
open AuthoredIndexedFamilyReceiptNaturality.NativeList
open NativeIndexedFamilies.Intrinsic
open NativeIndexedFamilySource

def targetContext : Tower.Ctx 5 :=
  .snoc contextAPZS nilIotaResultType

def weakening : Sub Tower.Head 4 5 := renSub wk

def weakeningTyped : CtxMor
    (extendRules Tower.rules nativeListPresentedCandidate.candidate.signature)
    contextAPZS targetContext weakening :=
  CtxRen.toCtxMor (by
    intro index
    rfl)

def weakeningMap :=
  pathSubstitutionMap nativeListReceiptNaturality weakening weakeningTyped
    canonicalNilTypedOccurrence.sourceState
    canonicalNilTypedOccurrence.targetState

noncomputable def exactState :
    State
      (pathFibre nativeListPresentedCandidate
        canonicalNilTypedOccurrence.sourceState
        canonicalNilTypedOccurrence.targetState)
      authoredNilLeftAssociated :=
  .exact (NativePathEvidence.ofPath _ authoredNilLeftAssociated)

/-- Positive control: a nonidentity weakening retains the complete native
three-leg conversion tree and realizes it directly. -/
theorem weakened_complete_path_is_realized :
    let transported := mapSafe weakeningMap exactState
    (runState transported).outcome =
      .realized
        (substituteNativePath nativeListPresentedCandidate weakening
          weakeningTyped
          (authoredToNativePath nativeListPresentedCandidate
            authoredNilLeftAssociated)) :=
  rfl

/-- Negative gradual control: the identical transported authored tree without
exact evidence remains fallback rather than rejection or guessed authority. -/
theorem weakened_complete_path_without_evidence_is_fallback :
    let suspendedState : State
        (pathFibre nativeListPresentedCandidate
          canonicalNilTypedOccurrence.sourceState
          canonicalNilTypedOccurrence.targetState)
        authoredNilLeftAssociated := .suspended
    (runState (mapSafe weakeningMap suspendedState)).outcome = .outsideFragment :=
  rfl

/-- The exact gradual face and the current NIK-selected strongest conversion
face produce the same native tree. -/
theorem exact_path_agrees_with_current_nik_selection :
    (runState exactState).outcome =
      (NativeConversionPathNIKSelection.NativeIndexedFamily.Canary.activeNil.run
        authoredNilLeftAssociated).outcome :=
  rfl

/-- Staleness forgets only the optional native path and exposes the retained
authored tree to fallback. -/
theorem stale_complete_path_is_fallback :
    (runState (exactState.activateAt false true)).outcome =
      .outsideFragment := by
  rw [activateAt_stale (by decide) exactState]
  rfl

end Canary

/-! ## Axiom audit -/

#print axioms NativePathEvidence.ofPath
#print axioms NativePathEvidence.toReceipt
#print axioms exact_outcome_agrees_with_complete_face
#print axioms authored_path_not_refutable
#print axioms NativePathEvidence.substitute
#print axioms pathSubstitutionMap
#print axioms pathSubstitutionSafeTransportLaws
#print axioms substitute_exact
#print axioms substitute_suspended
#print axioms substitute_refuted
#print axioms substitute_activateAt
#print axioms Canary.weakened_complete_path_is_realized
#print axioms Canary.weakened_complete_path_without_evidence_is_fallback
#print axioms Canary.exact_path_agrees_with_current_nik_selection
#print axioms Canary.stale_complete_path_is_fallback

end

end NativeConversionPathGradualTransport
end Mettapedia.Languages.MeTTa.Prime
