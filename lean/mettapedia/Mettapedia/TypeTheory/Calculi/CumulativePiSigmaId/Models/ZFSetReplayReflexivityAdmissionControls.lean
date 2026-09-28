import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayReflexivityAdmission
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayIdentityComparisonControls

/-!
# Computed reflexivity: exact endpoint-admission boundary

The same accepted proof and independently checked mixed identity formation
contain the proof on every valid environment but reject it on a concrete invalid
one. The general reflexivity-admission theorem extracts the actual endpoint
certificates and identifies their equality as precisely the missing condition.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayReflexivityAdmissionControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay ZFSetReplayInterpretation
open Mettapedia.TypeTheory.UniverseLevel
open ZFSetInterpretation
open ZFSetInterpretation.Controls (twoCode)
open ZFSetTraceUniverseInterpretation (interpretHead)
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetReplayApplicationComparisonControls
open ZFSetReplayIdentityComparisonControls

universe u

private abbrev pairLevel : Tower.Head :=
  .sort (.max (.succ (.succ Tower.zero)) (.succ (.succ Tower.zero)))

/-- The endpoint values extracted from the actual mixed identity certificate
agree exactly where its reflexivity proof is admitted. Their disagreement at
the excluded universe-valued input is therefore a semantic boundary, not a
checker rejection or a duplicate-certificate artefact. -/
theorem endpoint_agreement_valid_and_invalid (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) :
    ∃ leftCode rightCode left right,
      check Tower.rules noConversionCheck context term pairType leftCode = true ∧
      check Tower.rules noConversionCheck context term pairType rightCode = true ∧
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        leftCode term pairType = some left ∧
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        rightCode term pairType = some right ∧
      (∀ env, valid h env → left.value env = right.value env) ∧
      left.value (fun _ => universeSet h ∅ 0) ≠
        right.value (fun _ => universeSet h ∅ 0) := by
  let heads := interpretHead h ∅ (twoCode h).1 (fun _ => 0)
  obtain ⟨proof, identityMeaning, leftCode, rightCode, left, right, atProof,
    atIdentity, leftChecked, rightChecked, atLeft, atRight, admittedIff⟩ :=
      checked_reflexivity_admission_boundary heads constants Tower.rules context
        pairType term pairLevel lowerCode mixedIdentityCode
        reflexivity_checked mixed_identity_checked
  dsimp only [heads] at atProof atIdentity atLeft atRight
  change assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
    proofCode (.refl term) identity = some proof at atProof
  rw [reflexivity_assembles h constants] at atProof
  cases Option.some.inj atProof
  have atMixed : assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
      mixedIdentityCode (.id pairType term term) (.head pairLevel) =
        some (mixedIdentityMeaning h) := mixed_identity_assembles h constants
  rw [atMixed] at atIdentity
  cases Option.some.inj atIdentity
  refine ⟨leftCode, rightCode, left, right, leftChecked, rightChecked,
    atLeft, atRight, ?_, ?_⟩
  · intro env validEnv
    exact (admittedIff env).mp
      (reflexivity_member_independent_formation h constants proofMeaning
        (mixedIdentityMeaning h) (reflexivity_assembles h constants)
        (mixed_identity_assembles h constants) env validEnv)
  · intro equal
    have member := (admittedIff (fun _ => universeSet h ∅ 0)).mpr equal
    rw [(invalid_environment_identity_boundary h).2.2] at member
    exact ZFSet.notMem_empty _ member

#print axioms endpoint_agreement_valid_and_invalid

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayReflexivityAdmissionControls
