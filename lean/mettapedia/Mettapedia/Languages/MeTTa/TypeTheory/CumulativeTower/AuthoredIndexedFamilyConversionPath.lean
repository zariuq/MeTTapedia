import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.AuthoredIndexedFamilyReceiptNaturality
import Mettapedia.TypeTheory.FreeConversion

/-!
# Authored and native indexed-family conversion paths

An authored indexed-family presentation and its native realization have the
same judgment-indexed states.  They differ only in their one-step evidence:
the authored side retains the exact source occurrence, while the native side
retains the corresponding computation receipt.  The presentation already
equates those step fibres.

This file lifts that equivalence freely to complete reflexive, symmetric, and
transitive conversion paths.  The lift preserves every intermediate typed
state, every occurrence, and the complete association tree.  It deliberately
does not quotient paths by endpoint equality or by higher coherence; the
negative controls show why such a quotient would lose information.

Typed substitution acts on both path systems and commutes with the lift when
the underlying receipt equivalence is natural.  Thus native execution may
consume a whole constructed conversion derivation without replaying a checker.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace AuthoredIndexedFamilyConversionPath

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.JudgmentalEquality
open AuthoredDeclarationSignature
open AuthoredIndexedFamilyPresentation
open AuthoredIndexedFamilyReceiptNaturality
open AuthoredIndexedFamilyTypedConversion
open Presentation
open Presentation.Declaration
open Presentation.Declaration.ComputationAuthority

noncomputable section

/-! ## Two computations with one typed state family -/

/-- Authored equation-occurrence evidence inside the same typed state fibre
used by the native realization. -/
abbrev AuthoredIndexedStep (presented : PresentedCandidate)
    {index : TypingIndex Tower.Head}
    (source target : NativeIndexedState presented index) :=
  EquationOccurrence (equationSchemas (elaborate presented.source))
    source.1 target.1

/-- The authored computation has exactly the native computation's typed
states.  Its steps retain source occurrence identity rather than native
receipt evidence. -/
def authoredIndexedComputation (presented : PresentedCandidate) :
    JudgmentalComputation (TypingIndex Tower.Head) :=
  FreeConversion.computation
    (NativeIndexedState presented)
    (AuthoredIndexedStep presented)

/-- Each authored step fibre is exactly equivalent to its native receipt
fibre.  The common endpoints already carry their typing derivations. -/
def authoredNativeStepEquiv (presented : PresentedCandidate)
    {index : TypingIndex Tower.Head}
    (source target : (authoredIndexedComputation presented).State index) :
    (authoredIndexedComputation presented).Step source target ≃
      (nativeIndexedComputation presented).Step source target :=
  presented.receiptEquiv

/-- Complete authored conversion with every intermediate typed state and
authored occurrence retained. -/
abbrev AuthoredConversion (presented : PresentedCandidate)
    {index : TypingIndex Tower.Head}
    (source target : (authoredIndexedComputation presented).State index) :=
  FreeConversion.Path (NativeIndexedState presented)
    (AuthoredIndexedStep presented) source target

/-- Complete native conversion with every intermediate typed state and native
receipt retained. -/
abbrev NativeConversion (presented : PresentedCandidate)
    {index : TypingIndex Tower.Head}
    (source target : (nativeIndexedComputation presented).State index) :=
  FreeConversion.Path (NativeIndexedState presented)
    (NativeIndexedStep presented) source target

/-! ## Free proof-relevant path equivalence -/

/-- Lift every authored step to its exact native receipt without changing the
conversion constructor tree. -/
def authoredToNativePath (presented : PresentedCandidate)
    {index : TypingIndex Tower.Head}
    {source target : (authoredIndexedComputation presented).State index} :
    AuthoredConversion presented source target →
      NativeConversion presented source target :=
  FreeConversion.mapSteps
    (State := NativeIndexedState presented)
    (SourceStep := AuthoredIndexedStep presented)
    (TargetStep := NativeIndexedStep presented)
    (fun {_index} {source target} occurrence =>
      authoredNativeStepEquiv presented source target occurrence)

/-- Recover every authored occurrence from its native receipt without changing
the conversion constructor tree. -/
def nativeToAuthoredPath (presented : PresentedCandidate)
    {index : TypingIndex Tower.Head}
    {source target : (nativeIndexedComputation presented).State index} :
    NativeConversion presented source target →
      AuthoredConversion presented source target :=
  FreeConversion.mapSteps
    (State := NativeIndexedState presented)
    (SourceStep := NativeIndexedStep presented)
    (TargetStep := AuthoredIndexedStep presented)
    (fun {_index} {source target} receipt =>
      (authoredNativeStepEquiv presented source target).symm receipt)

@[simp] theorem native_authored_path_roundtrip
    (presented : PresentedCandidate)
    {index : TypingIndex Tower.Head}
    {source target : (nativeIndexedComputation presented).State index}
    (path : NativeConversion presented source target) :
    authoredToNativePath presented (nativeToAuthoredPath presented path) =
      path := by
  simpa [nativeToAuthoredPath, authoredToNativePath] using
    (FreeConversion.mapSteps_inverse
      (State := NativeIndexedState presented)
      (SourceStep := NativeIndexedStep presented)
      (TargetStep := AuthoredIndexedStep presented)
      (forward := fun {index} {source target} receipt =>
        (authoredNativeStepEquiv presented source target).symm receipt)
      (backward := fun {index} {source target} occurrence =>
        authoredNativeStepEquiv presented source target occurrence)
      (inverse := fun {index} {source target} receipt =>
        (authoredNativeStepEquiv presented source target).apply_symm_apply
          receipt)
      path)

@[simp] theorem authored_native_path_roundtrip
    (presented : PresentedCandidate)
    {index : TypingIndex Tower.Head}
    {source target : (authoredIndexedComputation presented).State index}
    (path : AuthoredConversion presented source target) :
    nativeToAuthoredPath presented (authoredToNativePath presented path) =
      path := by
  simpa [nativeToAuthoredPath, authoredToNativePath] using
    (FreeConversion.mapSteps_inverse
      (State := NativeIndexedState presented)
      (SourceStep := AuthoredIndexedStep presented)
      (TargetStep := NativeIndexedStep presented)
      (forward := fun {index} {source target} occurrence =>
        authoredNativeStepEquiv presented source target occurrence)
      (backward := fun {index} {source target} receipt =>
        (authoredNativeStepEquiv presented source target).symm receipt)
      (inverse := fun {index} {source target} occurrence =>
        (authoredNativeStepEquiv presented source target).symm_apply_apply
          occurrence)
      path)

/-- Authored and native conversion receipts are equivalent path-for-path, not
merely after endpoint or support erasure. -/
def authoredNativePathEquiv (presented : PresentedCandidate)
    {index : TypingIndex Tower.Head}
    (source target : (authoredIndexedComputation presented).State index) :
    AuthoredConversion presented source target ≃
      NativeConversion presented source target :=
  FreeConversion.pathEquivOfStepEquiv
    (State := NativeIndexedState presented)
    (SourceStep := AuthoredIndexedStep presented)
    (TargetStep := NativeIndexedStep presented)
    (fun source target => authoredNativeStepEquiv presented source target)
    source target

@[simp] theorem authoredToNativePath_step
    (presented : PresentedCandidate)
    {index : TypingIndex Tower.Head}
    {source target : NativeIndexedState presented index}
    (occurrence : AuthoredIndexedStep presented source target) :
    authoredToNativePath presented
        (ConversionEvidence.step occurrence :
          AuthoredConversion presented source target) =
      (ConversionEvidence.step
        (authoredNativeStepEquiv presented source target occurrence) :
        NativeConversion presented source target) := by
  exact FreeConversion.mapSteps_step
    (State := NativeIndexedState presented)
    (SourceStep := AuthoredIndexedStep presented)
    (TargetStep := NativeIndexedStep presented)
    (fun {index} {source target} evidence =>
      authoredNativeStepEquiv presented source target evidence)
    occurrence

@[simp] theorem authoredToNativePath_refl
    (presented : PresentedCandidate)
    {index : TypingIndex Tower.Head}
    (state : (authoredIndexedComputation presented).State index) :
    authoredToNativePath presented
        (ConversionEvidence.refl
          (computation := authoredIndexedComputation presented) state :
          AuthoredConversion presented state state) =
      (ConversionEvidence.refl
        (computation := nativeIndexedComputation presented) state :
        NativeConversion presented state state) :=
  by
    exact FreeConversion.mapSteps_refl
      (State := NativeIndexedState presented)
      (SourceStep := AuthoredIndexedStep presented)
      (TargetStep := NativeIndexedStep presented)
      (fun {index} {source target} occurrence =>
        authoredNativeStepEquiv presented source target occurrence)
      state

@[simp] theorem authoredToNativePath_symm
    (presented : PresentedCandidate)
    {index : TypingIndex Tower.Head}
    {source target : (authoredIndexedComputation presented).State index}
    (path : AuthoredConversion presented source target) :
    authoredToNativePath presented (.symm path) =
      .symm (authoredToNativePath presented path) :=
  by
    exact FreeConversion.mapSteps_symm
      (State := NativeIndexedState presented)
      (SourceStep := AuthoredIndexedStep presented)
      (TargetStep := NativeIndexedStep presented)
      (fun {index} {source target} occurrence =>
        authoredNativeStepEquiv presented source target occurrence)
      path

@[simp] theorem authoredToNativePath_trans
    (presented : PresentedCandidate)
    {index : TypingIndex Tower.Head}
    {source middle target :
      (authoredIndexedComputation presented).State index}
    (first : AuthoredConversion presented source middle)
    (second : AuthoredConversion presented middle target) :
    authoredToNativePath presented (.trans first second) =
      .trans (authoredToNativePath presented first)
        (authoredToNativePath presented second) :=
  by
    exact FreeConversion.mapSteps_trans
      (State := NativeIndexedState presented)
      (SourceStep := AuthoredIndexedStep presented)
      (TargetStep := NativeIndexedStep presented)
      (fun {index} {source target} occurrence =>
        authoredNativeStepEquiv presented source target occurrence)
      first second

/-! ## Typed substitution on complete paths -/

/-- Transport one typed state along a typed simultaneous substitution. -/
def substituteState (presented : PresentedCandidate)
    {n m : Nat}
    {sourceContext : Tower.Ctx n} {targetContext : Tower.Ctx m}
    {type : Tower.Tm n}
    (substitution : Sub Tower.Head n m)
    (typed : CtxMor
      (extendRules Tower.rules presented.candidate.signature)
      sourceContext targetContext substitution)
    (state : (authoredIndexedComputation presented).State
      ⟨n, sourceContext, type⟩) :
    (authoredIndexedComputation presented).State
      ⟨m, targetContext, Presentation.subst substitution type⟩ :=
  ⟨Presentation.subst substitution state.1,
    ⟨state.2.down.substitute typed⟩⟩

/-- Typed substitution maps a complete authored path, retaining every authored
occurrence and intermediate typed state. -/
def substituteAuthoredPath (presented : PresentedCandidate)
    {n m : Nat}
    {sourceContext : Tower.Ctx n} {targetContext : Tower.Ctx m}
    {type : Tower.Tm n}
    (substitution : Sub Tower.Head n m)
    (typed : CtxMor
      (extendRules Tower.rules presented.candidate.signature)
      sourceContext targetContext substitution)
    {source target : (authoredIndexedComputation presented).State
      ⟨n, sourceContext, type⟩} :
    AuthoredConversion presented source target →
      AuthoredConversion presented
        (substituteState presented substitution typed source)
        (substituteState presented substitution typed target)
  | .step occurrence => .step (occurrence.substitute substitution)
  | .refl state =>
      ConversionEvidence.refl
        (computation := authoredIndexedComputation presented)
        (substituteState presented substitution typed state)
  | .symm path => .symm (substituteAuthoredPath presented substitution typed path)
  | .trans first second =>
      .trans (substituteAuthoredPath presented substitution typed first)
        (substituteAuthoredPath presented substitution typed second)

/-- Typed substitution maps a complete native path, retaining every native
receipt and intermediate typed state. -/
def substituteNativePath (presented : PresentedCandidate)
    {n m : Nat}
    {sourceContext : Tower.Ctx n} {targetContext : Tower.Ctx m}
    {type : Tower.Tm n}
    (substitution : Sub Tower.Head n m)
    (typed : CtxMor
      (extendRules Tower.rules presented.candidate.signature)
      sourceContext targetContext substitution)
    {source target : (nativeIndexedComputation presented).State
      ⟨n, sourceContext, type⟩} :
    NativeConversion presented source target →
      NativeConversion presented
        (substituteState presented substitution typed source)
        (substituteState presented substitution typed target)
  | .step receipt =>
      ConversionEvidence.step
        (computation := nativeIndexedComputation presented)
        (presented.candidate.computation.substitute substitution receipt)
  | .refl state =>
      ConversionEvidence.refl
        (computation := nativeIndexedComputation presented)
        (substituteState presented substitution typed state)
  | .symm path => .symm (substituteNativePath presented substitution typed path)
  | .trans first second =>
      .trans (substituteNativePath presented substitution typed first)
        (substituteNativePath presented substitution typed second)

/-- The exact path equivalence is natural under typed substitution.  This is
path-level naturality: it preserves the complete conversion tree, not only
the endpoints or propositional reachability. -/
theorem authoredToNativePath_substitute
    {presented : PresentedCandidate}
    (naturality : ReceiptNaturality presented)
    {n m : Nat}
    {sourceContext : Tower.Ctx n} {targetContext : Tower.Ctx m}
    {type : Tower.Tm n}
    (substitution : Sub Tower.Head n m)
    (typed : CtxMor
      (extendRules Tower.rules presented.candidate.signature)
      sourceContext targetContext substitution)
    {source target : (authoredIndexedComputation presented).State
      ⟨n, sourceContext, type⟩}
    (path : AuthoredConversion presented source target) :
    authoredToNativePath presented
        (substituteAuthoredPath presented substitution typed path) =
      substituteNativePath presented substitution typed
        (authoredToNativePath presented path) := by
  induction path with
  | @step sourceState targetState occurrence =>
      let substitutedSource :=
        substituteState presented substitution typed sourceState
      let substitutedTarget :=
        substituteState presented substitution typed targetState
      let liftReceipt : NativeIndexedStep presented
          substitutedSource substitutedTarget →
          NativeConversion presented substitutedSource substitutedTarget :=
        fun receipt => .step receipt
      calc
        authoredToNativePath presented
            (substituteAuthoredPath presented substitution typed
              (.step occurrence)) =
            liftReceipt
              (presented.receiptEquiv
                (occurrence.substitute substitution)) := by
          rw [substituteAuthoredPath]
          exact authoredToNativePath_step presented
            (source := substitutedSource) (target := substitutedTarget)
            (occurrence.substitute substitution)
        _ = liftReceipt
            (presented.candidate.computation.substitute substitution
              (presented.receiptEquiv occurrence)) :=
          congrArg liftReceipt
            (naturality.substitute occurrence substitution)
        _ = substituteNativePath presented substitution typed
            (authoredToNativePath presented (.step occurrence)) := by
          rw [authoredToNativePath_step presented
            (source := sourceState) (target := targetState)]
          rfl
  | refl state =>
      change
        authoredToNativePath presented
            (ConversionEvidence.refl
              (computation := authoredIndexedComputation presented)
              (substituteState presented substitution typed state)) =
          substituteNativePath presented substitution typed
            (authoredToNativePath presented
              (ConversionEvidence.refl
                (computation := authoredIndexedComputation presented)
                state))
      rw [authoredToNativePath_refl, authoredToNativePath_refl]
      rfl
  | symm path ih =>
      calc
        authoredToNativePath presented
            (substituteAuthoredPath presented substitution typed
              (.symm path)) =
            .symm (authoredToNativePath presented
              (substituteAuthoredPath presented substitution typed path)) := by
          rw [substituteAuthoredPath, authoredToNativePath_symm]
        _ = .symm (substituteNativePath presented substitution typed
              (authoredToNativePath presented path)) := congrArg _ ih
        _ = substituteNativePath presented substitution typed
            (.symm (authoredToNativePath presented path)) := by rfl
        _ = substituteNativePath presented substitution typed
            (authoredToNativePath presented (.symm path)) := by
          rw [authoredToNativePath_symm]
  | trans first second ihFirst ihSecond =>
      calc
        authoredToNativePath presented
            (substituteAuthoredPath presented substitution typed
              (.trans first second)) =
            .trans
              (authoredToNativePath presented
                (substituteAuthoredPath presented substitution typed first))
              (authoredToNativePath presented
                (substituteAuthoredPath presented substitution typed second)) := by
          rw [substituteAuthoredPath, authoredToNativePath_trans]
        _ = .trans
              (substituteNativePath presented substitution typed
                (authoredToNativePath presented first))
              (substituteNativePath presented substitution typed
                (authoredToNativePath presented second)) := by
          rw [ihFirst, ihSecond]
        _ = substituteNativePath presented substitution typed
            (.trans (authoredToNativePath presented first)
              (authoredToNativePath presented second)) := by rfl
        _ = substituteNativePath presented substitution typed
            (authoredToNativePath presented (.trans first second)) := by
          rw [authoredToNativePath_trans]

/-! ## Positive and negative controls -/

namespace Canary

open AuthoredIndexedFamilyReceiptNaturality.NativeList
open NativeIndexedFamilySource

/-- The authored nil computation as one conversion generator. -/
noncomputable def authoredNilStep :
    AuthoredConversion nativeListPresentedCandidate
      canonicalNilTypedOccurrence.sourceState
      canonicalNilTypedOccurrence.targetState :=
  .step canonicalNilTypedOccurrence.authored

/-- The path lift recovers exactly the previously established native nil
conversion. -/
theorem authored_nil_step_maps_exactly :
    authoredToNativePath nativeListPresentedCandidate authoredNilStep =
      canonicalNilTypedOccurrence.toNativeConversion := by
  change
    authoredToNativePath nativeListPresentedCandidate
        (.step canonicalNilTypedOccurrence.authored) =
      (.step (nativeListPresentedCandidate.receiptEquiv
        canonicalNilTypedOccurrence.authored) :
        NativeConversion nativeListPresentedCandidate
          canonicalNilTypedOccurrence.sourceState
          canonicalNilTypedOccurrence.targetState)
  exact authoredToNativePath_step nativeListPresentedCandidate
    (source := canonicalNilTypedOccurrence.sourceState)
    (target := canonicalNilTypedOccurrence.targetState)
    canonicalNilTypedOccurrence.authored

/-- A two-legged conversion returns to its typed source while retaining both
the forward occurrence and its symmetric use. -/
noncomputable def authoredNilRoundTrip :
    AuthoredConversion nativeListPresentedCandidate
      canonicalNilTypedOccurrence.sourceState
      canonicalNilTypedOccurrence.sourceState :=
  .trans authoredNilStep (.symm authoredNilStep)

/-- Endpoint equality does not identify a witnessed round trip with the empty
path. -/
  theorem authored_nil_roundtrip_ne_refl :
    authoredNilRoundTrip ≠
      (ConversionEvidence.refl
        (computation := authoredIndexedComputation
          nativeListPresentedCandidate)
        canonicalNilTypedOccurrence.sourceState :
        AuthoredConversion nativeListPresentedCandidate
          canonicalNilTypedOccurrence.sourceState
          canonicalNilTypedOccurrence.sourceState) := by
  intro equality
  cases equality

/-- Two association trees with the same three legs and the same endpoints are
kept distinct until an explicit higher-coherence cell relates them. -/
noncomputable def authoredNilLeftAssociated :
    AuthoredConversion nativeListPresentedCandidate
      canonicalNilTypedOccurrence.sourceState
      canonicalNilTypedOccurrence.targetState :=
  .trans (.trans authoredNilStep (.symm authoredNilStep)) authoredNilStep

noncomputable def authoredNilRightAssociated :
    AuthoredConversion nativeListPresentedCandidate
      canonicalNilTypedOccurrence.sourceState
      canonicalNilTypedOccurrence.targetState :=
  .trans authoredNilStep (.trans (.symm authoredNilStep) authoredNilStep)

theorem authored_nil_association_trees_are_distinct :
    authoredNilLeftAssociated ≠ authoredNilRightAssociated := by
  intro equality
  cases equality

/-- Mapping the three-leg path preserves its exact association tree. -/
theorem authored_nil_left_association_maps_structurally :
    authoredToNativePath nativeListPresentedCandidate
        authoredNilLeftAssociated =
      .trans
        (.trans canonicalNilTypedOccurrence.toNativeConversion
          (.symm canonicalNilTypedOccurrence.toNativeConversion))
        canonicalNilTypedOccurrence.toNativeConversion := by
  simp [authoredNilLeftAssociated, authoredNilStep,
    TypedOccurrence.toNativeConversion, TypedOccurrence.toNativeStep,
    TypedOccurrence.nativeEvidence, authoredNativeStepEquiv]
  rfl

end Canary

/-! ## Axiom audit -/

#print axioms authoredNativePathEquiv
#print axioms authoredToNativePath_substitute
#print axioms Canary.authored_nil_step_maps_exactly
#print axioms Canary.authored_nil_roundtrip_ne_refl
#print axioms Canary.authored_nil_association_trees_are_distinct
#print axioms Canary.authored_nil_left_association_maps_structurally

end

end AuthoredIndexedFamilyConversionPath
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
