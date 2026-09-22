import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeJudgmentReplayTransport
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplayCoherence

/-!
# Coherent instantiation of native retained judgment certificates

The native conversion-code action discharges every payload law of structural
certificate coherence. Composition computes the original image proofs under
the later assignment. Its dependent argument checks are derived using the
same checker and telescope fold as individual instantiation.

Identity and composition are equalities of accepted finite evidence trees,
not a quotient identifying every proof of the same judgment. A malformed
source control explains why the source acceptance hypothesis matters.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay

open Presentation StructuralTypingReplay NativeIndexedFamilies

def composeImageCodes {n m k : Nat} (source : Tower.Ctx n) (σ : Sub Tower.Head n m)
    (first : Fin n → Code m) (τ : Sub Tower.Head m k) (second : Fin m → Code k) : Fin n → Code k :=
  StructuralTypingReplay.composeImageCodes NativeRelatorConversionChecking.rename
    NativeRelatorConversionChecking.substitute source σ first τ second

theorem substitute_ids {n : Nat} {source : Tower.Ctx n} {subject type : Tower.Tm n}
    {contextCode : ContextCode n} {code : Code n}
    (accepted : check source subject type contextCode code = true) :
    substitute ids (fun _ => .var) subject type code = code := by
  simp only [check, checkJudgment, Bool.and_eq_true] at accepted
  exact StructuralTypingReplay.Code.substitute_ids_of_checked
    NativeRelatorConversionChecking.rename NativeRelatorConversionChecking.substitute
    IntrinsicRelator.rules NativeRelatorConversionChecking.check
    NativeRelatorConversionChecking.substitute_ids code accepted.2

/-- The exact computed proof is independent of batching two accepted
instantiations into one. The first image proofs themselves are transformed. -/
theorem substitute_comp {n m k : Nat} {source : Tower.Ctx n} {subject type : Tower.Tm n}
    {contextCode : ContextCode n} {code : Code n}
    (accepted : check source subject type contextCode code = true)
    (σ : Sub Tower.Head n m) (first : Fin n → Code m)
    (τ : Sub Tower.Head m k) (second : Fin m → Code k) :
    substitute τ second (subst σ subject) (subst σ type) (substitute σ first subject type code) =
      substitute (subComp τ σ) (composeImageCodes source σ first τ second) subject type code := by
  simp only [check, checkJudgment, Bool.and_eq_true] at accepted
  exact StructuralTypingReplay.Code.substitute_comp_of_checked
    NativeRelatorConversionChecking.rename NativeRelatorConversionChecking.substitute
    NativeRelatorConversionChecking.rename_comp NativeRelatorConversionChecking.rename_substitute
    NativeRelatorConversionChecking.substitute_rename IntrinsicRelator.rules
    NativeRelatorConversionChecking.check NativeRelatorConversionChecking.substitute_comp
    code accepted.2 σ first τ second

/-- The existing dependent telescope checker accepts the computed
composite image certificates, with all expected types composed as terms. -/
theorem composed_arguments_checked {n m k : Nat}
    {source : Tower.Ctx n} {middle : Tower.Ctx m} {target : Tower.Ctx k}
    (σ : Sub Tower.Head n m) (first : Fin n → Code m)
    (τ : Sub Tower.Head m k) (second : Fin m → Code k)
    (firstAccepted : TelescopeArgumentChecking.checkArguments
      (StructuralTypingReplay.check IntrinsicRelator.rules NativeRelatorConversionChecking.check middle)
      source σ first = true)
    (secondAccepted : TelescopeArgumentChecking.checkArguments
      (StructuralTypingReplay.check IntrinsicRelator.rules NativeRelatorConversionChecking.check target)
      middle τ second = true) :
    TelescopeArgumentChecking.checkArguments
      (StructuralTypingReplay.check IntrinsicRelator.rules NativeRelatorConversionChecking.check target)
      source (subComp τ σ) (composeImageCodes source σ first τ second) = true := by
  apply (TelescopeArgumentChecking.checkArguments_eq_true_iff _ _ _ _).mpr
  intro index
  have firstChecked := (TelescopeArgumentChecking.checkArguments_eq_true_iff _ _ _ _).mp
    firstAccepted index
  have transported := check_substitute_of_checked_arguments
    NativeRelatorConversionChecking.rename NativeRelatorConversionChecking.substitute
    IntrinsicRelator.rules NativeRelatorConversionChecking.check
    NativeRelatorConversionChecking.check_rename NativeRelatorConversionChecking.check_substitute
    firstChecked τ second secondAccepted
  simpa only [composeImageCodes, StructuralTypingReplay.composeImageCodes, subst_subComp,
    Presentation.subComp] using transported

/-- Both intermediate and final complete judgments replay, and the final
certificate is exactly the one obtained by a single composite instantiation. -/
theorem checked_two_stage_instantiation {n m k : Nat}
    {source : Tower.Ctx n} {middle : Tower.Ctx m} {target : Tower.Ctx k}
    {subject type : Tower.Tm n} {sourceContextCode : ContextCode n} {code : Code n}
    (accepted : check source subject type sourceContextCode code = true)
    (middleContextCode : ContextCode m) (targetContextCode : ContextCode k)
    (middleFormed : checkContext IntrinsicRelator.rules NativeRelatorConversionChecking.check
      middle middleContextCode = true)
    (targetFormed : checkContext IntrinsicRelator.rules NativeRelatorConversionChecking.check
      target targetContextCode = true)
    (σ : Sub Tower.Head n m) (first : Fin n → Code m)
    (τ : Sub Tower.Head m k) (second : Fin m → Code k)
    (firstAccepted : TelescopeArgumentChecking.checkArguments
      (StructuralTypingReplay.check IntrinsicRelator.rules NativeRelatorConversionChecking.check middle)
      source σ first = true)
    (secondAccepted : TelescopeArgumentChecking.checkArguments
      (StructuralTypingReplay.check IntrinsicRelator.rules NativeRelatorConversionChecking.check target)
      middle τ second = true) :
    check middle (subst σ subject) (subst σ type) middleContextCode
        (substitute σ first subject type code) = true ∧
      check target (subst (subComp τ σ) subject) (subst (subComp τ σ) type) targetContextCode
        (substitute (subComp τ σ) (composeImageCodes source σ first τ second) subject type code) = true ∧
      substitute τ second (subst σ subject) (subst σ type) (substitute σ first subject type code) =
        substitute (subComp τ σ) (composeImageCodes source σ first τ second) subject type code :=
  ⟨check_substitute accepted middleContextCode middleFormed σ first firstAccepted,
    check_substitute accepted targetContextCode targetFormed _ _
      (composed_arguments_checked σ first τ second firstAccepted secondAccepted),
    substitute_comp accepted σ first τ second⟩

namespace CoherenceControls

open NativeRelatorConversionChecking.Examples (ground betaArgument)
open TransportControls

theorem nested_proof_identity :
    substitute ids (fun _ => .var) (.lam (.refl (.var 1))) openFunctionType openFunctionCode =
      openFunctionCode :=
  substitute_ids open_function_checked

theorem nested_proof_composition :
    substitute nonVariable nonVariableCodes
        (subst nonVariable (.lam (.refl (.var 1)))) (subst nonVariable openFunctionType)
        (substitute nonVariable nonVariableCodes (.lam (.refl (.var 1))) openFunctionType openFunctionCode) =
      substitute (subComp nonVariable nonVariable)
        (composeImageCodes Controls.context nonVariable nonVariableCodes nonVariable nonVariableCodes)
        (.lam (.refl (.var 1))) openFunctionType openFunctionCode :=
  substitute_comp open_function_checked nonVariable nonVariableCodes nonVariable nonVariableCodes

theorem twice_instantiated_proof_checked :
    check Controls.context (.lam (.refl (betaArgument (betaArgument (.var 1)))))
      (subst (subComp nonVariable nonVariable) openFunctionType) Controls.contextCode
      (substitute (subComp nonVariable nonVariable)
        (composeImageCodes Controls.context nonVariable nonVariableCodes nonVariable nonVariableCodes)
        (.lam (.refl (.var 1))) openFunctionType openFunctionCode) = true :=
  check_substitute open_function_checked Controls.contextCode (by decide +kernel) _ _
    (composed_arguments_checked nonVariable nonVariableCodes nonVariable nonVariableCodes
      nonvariable_arguments_checked nonvariable_arguments_checked)

def identityType : Tower.Tm 1 := .id ground (.var 0) (.var 0)
def directProof : Code 1 := .reflIntro ground .var
def explicitConversionProof : Code 1 :=
  .convert identityType (.sort Tower.zero) directProof
    (.idForm (.sort Tower.zero) .headType .var .var) (.refl identityType)

theorem distinct_proofs_both_checked :
    check Controls.context (.refl (.var 0)) identityType Controls.contextCode directProof = true ∧
      check Controls.context (.refl (.var 0)) identityType Controls.contextCode explicitConversionProof = true := by
  decide +kernel

/-- Retained certificates remain distinct after instantiation, even when
they establish precisely the same judgment. -/
theorem distinct_proofs_retained :
    substitute nonVariable nonVariableCodes (.refl (.var 0)) identityType directProof ≠
      substitute nonVariable nonVariableCodes (.refl (.var 0)) identityType explicitConversionProof := by
  intro equal
  cases equal

def malformedProof : Code 1 := .piForm (.sort Tower.zero) (.sort Tower.zero) .headType .headType

/-- The total transformation has a fallback on malformed input; it is
not an identity action on every raw code/subject pairing. -/
theorem malformed_source_not_identity :
    check Controls.context (.var 0) ground Controls.contextCode malformedProof = false ∧
      substitute ids (fun _ => .var) (.var 0) ground malformedProof ≠ malformedProof := by
  constructor
  · decide +kernel
  · intro equal
    cases equal

end CoherenceControls

#print axioms substitute_ids
#print axioms substitute_comp
#print axioms composed_arguments_checked
#print axioms checked_two_stage_instantiation
#print axioms CoherenceControls.nested_proof_identity
#print axioms CoherenceControls.nested_proof_composition
#print axioms CoherenceControls.twice_instantiated_proof_checked
#print axioms CoherenceControls.distinct_proofs_both_checked
#print axioms CoherenceControls.distinct_proofs_retained
#print axioms CoherenceControls.malformed_source_not_identity

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay
