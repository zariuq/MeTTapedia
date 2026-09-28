import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayQualifiedTypingControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayIdentityFamilySubstitution

/-!
# A checked non-neutral diagonal family with computed arguments

The endpoint is an application of a lambda, so the identity-family replay
fails the neutral-elimination qualification. Distinct checked arguments can
still be substituted; the generated dependent types have the same interpreted
fibre because both endpoint certificates in each identity former are shared.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayDiagonalFamilyControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay ZFSetReplayInterpretation
open ZFSetTypeExpressionInterpretation (Environment)
open Mettapedia.Logic.HOL.Embedding
open ZFSetReplayQualifiedTypingControls

def computedEndpoint : Tower.Tm 1 := .app (.lam (.var 0)) (.var 0)
def computedEndpointCode : Code Tower.Head NoConversion 1 :=
  .appElim functionType functionType consumerCode .var
def diagonalFamily : Tower.Tm 1 := .id functionType computedEndpoint computedEndpoint
private abbrev familyLevel : Tower.Head :=
  .sort (.max (.succ Tower.zero) (.succ Tower.zero))
def diagonalFamilyCode : Code Tower.Head NoConversion 1 :=
  .idForm familyLevel functionFormation computedEndpointCode computedEndpointCode

theorem family_checks :
    check Tower.rules noConversionCheck (.snoc .nil functionType) diagonalFamily
      (.head familyLevel) diagonalFamilyCode = true := by
  decide +kernel

theorem family_is_not_neutral :
    diagonalFamilyCode.neutralEliminations diagonalFamily
      (.head familyLevel) = false := by
  decide +kernel

theorem instantiated_types_differ :
    inst0 identity diagonalFamily ≠ inst0 computedFunction diagonalFamily := by
  decide +kernel

universe u

/-- The checked substitutions use two different argument programs, one computed.
No equality of their values is needed for this diagonal family. -/
theorem checked_diagonal_instances_agree
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u}) :
    let leftFormation := Code.instantiate noConversionRename noConversionSubstitute
      diagonalFamily (.head familyLevel)
      identity diagonalFamilyCode identityCode
    let rightFormation := Code.instantiate noConversionRename noConversionSubstitute
      diagonalFamily (.head familyLevel)
      computedFunction diagonalFamilyCode computedFunctionCode
    check Tower.rules noConversionCheck .nil (inst0 identity diagonalFamily)
        (.head familyLevel) leftFormation = true ∧
      check Tower.rules noConversionCheck .nil (inst0 computedFunction diagonalFamily)
        (.head familyLevel) rightFormation = true ∧
      ∃ left right,
        assemble heads constants leftFormation (inst0 identity diagonalFamily)
          (.head familyLevel) = some left ∧
        assemble heads constants rightFormation (inst0 computedFunction diagonalFamily)
          (.head familyLevel) = some right ∧
        ∀ env : Environment.{u} 0, left.value env = right.value env := by
  obtain ⟨left, atLeft, _⟩ := accepted_assembles heads constants Tower.rules
    noConversionCheck identityCode functions_checked.1
  obtain ⟨right, atRight, _⟩ := accepted_assembles heads constants Tower.rules
    noConversionCheck computedFunctionCode functions_checked.2.1
  exact computed_arguments_diagonal_identity_family_values heads constants Tower.rules
    identityCode computedFunctionCode left right functions_checked.1
    functions_checked.2.1 atLeft atRight
    functionType computedEndpoint
    familyLevel familyLevel
    functionFormation functionFormation computedEndpointCode computedEndpointCode
    family_checks family_checks

/-- A dependent consumer can use either generated context: the two last
types are syntactically different but admit exactly the same environments. -/
theorem checked_diagonal_contexts_agree
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u}) :
    let leftFormation := Code.instantiate noConversionRename noConversionSubstitute
      diagonalFamily (.head familyLevel) identity diagonalFamilyCode identityCode
    let rightFormation := Code.instantiate noConversionRename noConversionSubstitute
      diagonalFamily (.head familyLevel) computedFunction diagonalFamilyCode computedFunctionCode
    checkContext Tower.rules noConversionCheck (.snoc .nil (inst0 identity diagonalFamily))
      (.snoc .nil familyLevel leftFormation) = true ∧
    checkContext Tower.rules noConversionCheck (.snoc .nil (inst0 computedFunction diagonalFamily))
      (.snoc .nil familyLevel rightFormation) = true ∧
    ∃ leftValid rightValid,
      assembleContext heads constants (.snoc .nil familyLevel leftFormation)
        (.snoc .nil (inst0 identity diagonalFamily)) = some leftValid ∧
      assembleContext heads constants (.snoc .nil familyLevel rightFormation)
        (.snoc .nil (inst0 computedFunction diagonalFamily)) = some rightValid ∧
      leftValid = rightValid := by
  obtain ⟨left, atLeft, _⟩ := accepted_assembles heads constants Tower.rules
    noConversionCheck identityCode functions_checked.1
  obtain ⟨right, atRight, _⟩ := accepted_assembles heads constants Tower.rules
    noConversionCheck computedFunctionCode functions_checked.2.1
  exact computed_arguments_diagonal_identity_family_contexts heads constants Tower.rules
    .nil identityCode computedFunctionCode left right (fun _ => True) rfl rfl
    functions_checked.1 functions_checked.2.1 atLeft atRight
    functionType computedEndpoint familyLevel familyLevel
    (by decide +kernel) (by decide +kernel)
    functionFormation functionFormation computedEndpointCode computedEndpointCode
    family_checks family_checks

/-- A computed argument now drives an actual checked proof term. The proof
inhabits the generated, non-neutral dependent identity type. -/
theorem checked_computed_argument_reflexivity
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u}) :
    let proof := (Tm.refl computedEndpoint : Tower.Tm 1)
    let familyCode := Code.instantiate noConversionRename noConversionSubstitute
      diagonalFamily (.head familyLevel) computedFunction
      diagonalFamilyCode computedFunctionCode
    let proofCode := Code.instantiate noConversionRename noConversionSubstitute
      proof diagonalFamily computedFunction
      (.reflIntro functionType computedEndpointCode) computedFunctionCode
    check Tower.rules noConversionCheck .nil
      (inst0 computedFunction diagonalFamily) (.head familyLevel) familyCode = true ∧
    check Tower.rules noConversionCheck .nil
      (inst0 computedFunction proof) (inst0 computedFunction diagonalFamily) proofCode = true ∧
    ∃ familyMeaning proofMeaning,
      assemble heads constants familyCode (inst0 computedFunction diagonalFamily)
        (.head familyLevel) = some familyMeaning ∧
      assemble heads constants proofCode (inst0 computedFunction proof)
        (inst0 computedFunction diagonalFamily) = some proofMeaning ∧
      ∀ env : Environment.{u} 0,
        proofMeaning.value env ∈ familyMeaning.value env := by
  exact computed_argument_diagonal_reflexivity_membership heads constants Tower.rules
    computedFunctionCode functions_checked.2.1
    functionType computedEndpoint familyLevel functionFormation computedEndpointCode
    family_checks

#print axioms checked_diagonal_instances_agree
#print axioms checked_diagonal_contexts_agree
#print axioms checked_computed_argument_reflexivity

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayDiagonalFamilyControls
