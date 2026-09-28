import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayQualifiedTypingControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayIdentityFamilySubstitution

/-!
# Retained reflexivity after a computed universe substitution

A checked source proof of `Id U₁ X X` is instantiated with an accepted
universe-valued beta redex. The resulting endpoint is not in the structural
interpretation fragment. The existing certificate-substitution algorithm
still checks and assembles both the proof and its independent identity
formation, and the proof inhabits that formation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayReflexivitySubstitutionControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay ZFSetReplayInterpretation
open ZFSetTypeExpressionInterpretation (Environment)
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetInterpretation
open ZFSetInterpretation.Controls (twoCode)
open ZFSetTraceUniverseInterpretation (interpretHead)
open ZFSetReplayUniverseModel (universeModel empty_constants_model successor_qualified)
open ZFSetReplayQualifiedTypingControls (computedType computedTypeCode
  computed_type_checked_and_qualified)

universe u

private abbrev one : Tower.Head := .sort (.succ Tower.zero)
private abbrev two : Tower.Head := .sort (.succ (.succ Tower.zero))
private abbrev Replay (n : Nat) := Code Tower.Head NoConversion n

def sourceContext : Tower.Ctx 1 := .snoc .nil (.head one)
def sourceContextCode : ContextCode Tower.Head NoConversion 1 :=
  .snoc .nil two .headType
def sourceIdentity : Tower.Tm 1 := .id (.head one) (.var 0) (.var 0)
def sourceProof : Tower.Tm 1 := .refl (.var 0)
def sourceProofCode : Replay 1 := .reflIntro (.head one) .var
def sourceIdentityCode : Replay 1 := .idForm two .headType .var .var

def image : Sub Tower.Head 1 0 := fun _ => computedType
def imageCode : Fin 1 → Replay 0 := fun _ => computedTypeCode

theorem source_checks :
    checkContext Tower.rules noConversionCheck sourceContext sourceContextCode = true ∧
    check Tower.rules noConversionCheck sourceContext sourceProof sourceIdentity
      sourceProofCode = true ∧
    check Tower.rules noConversionCheck sourceContext sourceIdentity (.head two)
      sourceIdentityCode = true := by
  decide +kernel

theorem target_endpoint_unsupported :
    ZFSetTypeExpressionInterpretation.supported (subst image (.var 0 : Tower.Tm 1)) =
      false := rfl

/-- Erasing the computed image's retained application tree is not a valid
way to obtain its reflexivity proof certificate. -/
theorem erased_image_certificate_rejected :
    check Tower.rules noConversionCheck .nil (subst image sourceProof)
      (subst image sourceIdentity)
      (.reflIntro (.head one) (.var : Replay 0)) = false := by
  decide +kernel

theorem source_endpoint_supported :
    ZFSetTypeExpressionInterpretation.supported (.var 0 : Tower.Tm 1) = true := rfl

/-- Certificate substitution preserves the exact formation extracted from
this proof; the independently transported identity formation is not an
unrelated type assembled only for the membership test. -/
theorem substituted_result_formation_exact :
    (sourceProofCode.substitute noConversionRename noConversionSubstitute
      image imageCode sourceProof sourceIdentity).resultFormation
        noConversionRename noConversionSubstitute TowerDecisions.headTarget .nil
        (subst image sourceProof) (subst image sourceIdentity) =
      some (two, sourceIdentityCode.substitute noConversionRename
        noConversionSubstitute image imageCode sourceIdentity (.head two)) := rfl

/-- The computed image itself is admitted by the interpretation of U₁. This
is the real image-typing premise for substitution, not a fabricated
certificate from the erased beta-redex. -/
theorem computed_image_member (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) :
    ∃ argument : Meaning.{u} 0,
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        computedTypeCode computedType (.head one) = some argument ∧
      ∀ env : Environment.{u} 0, argument.value env ∈ universeSet h ∅ 1 := by
  let heads := interpretHead h ∅ (twoCode h).1 (fun _ => 0)
  obtain ⟨argument, atArgument, _⟩ := accepted_assembles heads constants Tower.rules
    noConversionCheck computedTypeCode computed_type_checked_and_qualified.1
  refine ⟨argument, atArgument, ?_⟩
  intro env
  exact qualified_membership heads constants Tower.rules TowerDecisions.headTarget
    FormationSensitive.towerUniverseRegularity successor_qualified
    (universeModel h ∅ (twoCode h).1 (fun _ => 0) (twoCode h).2)
    (empty_constants_model heads constants) computedTypeCode .nil rfl
    computed_type_checked_and_qualified.1 computed_type_checked_and_qualified.2
    (fun _ => True) argument rfl atArgument two .headType
    (.plain (fun _ => universeSet h ∅ 1)) (by decide) rfl env True.intro

/-- A genuinely computed target endpoint is outside the structural fragment,
yet its checked reflexivity proof survives dependent substitution and remains
a member of the independently checked generated identity formation. -/
theorem computed_identity_proof_substitutes (h : CofinalInaccessibles.{u})
    (constants : DeclName → ZFSet.{u}) :
    let proofCode := sourceProofCode.substitute noConversionRename
      noConversionSubstitute image imageCode sourceProof sourceIdentity
    let formationCode := sourceIdentityCode.substitute noConversionRename
      noConversionSubstitute image imageCode sourceIdentity (.head two)
    proofCode.resultFormation noConversionRename noConversionSubstitute
      TowerDecisions.headTarget .nil (subst image sourceProof)
        (subst image sourceIdentity) = some (two, formationCode) ∧
    check Tower.rules noConversionCheck .nil (subst image sourceProof)
      (subst image sourceIdentity) proofCode = true ∧
    check Tower.rules noConversionCheck .nil (subst image sourceIdentity)
      (.head two) formationCode = true ∧
    ∃ proof identity,
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        proofCode (subst image sourceProof) (subst image sourceIdentity) = some proof ∧
      assemble (interpretHead h ∅ (twoCode h).1 (fun _ => 0)) constants
        formationCode (subst image sourceIdentity) (.head two) = some identity ∧
      ∀ env : Environment.{u} 0, proof.value env ∈ identity.value env := by
  let heads := interpretHead h ∅ (twoCode h).1 (fun _ => 0)
  obtain ⟨argument, atArgument, member⟩ := computed_image_member h constants
  have atContext : assembleContext heads constants sourceContextCode sourceContext =
      some (fun env : Environment.{u} 1 => True ∧ env 0 ∈ universeSet h ∅ 1) := rfl
  refine ⟨substituted_result_formation_exact, ?_⟩
  simpa only [sourceProof, sourceIdentity, sourceProofCode, true_imp_iff] using
    supported_reflexivity_substitute_membership heads constants Tower.rules
    sourceContext sourceContextCode
    (fun env : Environment.{u} 1 => True ∧ env 0 ∈ universeSet h ∅ 1)
    .nil (fun _ : Environment.{u} 0 => True)
    (.head one) (.var 0) two .var sourceIdentityCode
    source_checks.1 atContext source_endpoint_supported source_checks.2.1
    source_checks.2.2 image imageCode (fun _ => argument)
    (fun _ => Meaning.plain (fun _ => universeSet h ∅ 1))
    (fun index => by fin_cases index; exact computed_type_checked_and_qualified.1)
    (fun index => by fin_cases index; exact atArgument)
    (fun index => by fin_cases index; rfl)
    (fun env _ _ => member env)

#print axioms computed_image_member
#print axioms computed_identity_proof_substitutes
#print axioms erased_image_certificate_rejected
#print axioms substituted_result_formation_exact

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayReflexivitySubstitutionControls
