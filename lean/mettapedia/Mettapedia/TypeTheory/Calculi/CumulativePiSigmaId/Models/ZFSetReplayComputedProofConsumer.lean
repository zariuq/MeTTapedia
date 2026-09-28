import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayQualifiedTypingControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayApplicationComparison
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayReflexivityAdmission

/-!
# Consuming an accepted proof with an unqualified typing tree

The argument is reflexivity of a computed function. Its typing tree is
accepted but fails the result-formation-neutral qualification. Two checked
identity functions retain different formation certificates for its domain.
The local proof-membership and application laws, rather than a global
semantic-typing assertion, compare their execution.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayComputedProofConsumer

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay ZFSetReplayInterpretation
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetInterpretation (universeSet)
open ZFSetTraceUniverseInterpretation (interpretHead)
open ZFSetReplayQualifiedTypingControls (functionType functionFormation independentFunction
  lowerIndependentCode upperIndependentCode mixedIdentityType mixedIdentityFormation
  mixedReflexivityCode mixed_identity_checked mixed_reflexivity_not_qualified
  mixed_reflexivity_membership)

universe u

private abbrev identityLevel : Tower.Head :=
  .sort (.max (.succ Tower.zero) (.succ Tower.zero))
private abbrev consumerLevel : Tower.Head :=
  .sort (.max (.max (.succ Tower.zero) (.succ Tower.zero))
    (.max (.succ Tower.zero) (.succ Tower.zero)))
private abbrev Replay (n : Nat) := Code Tower.Head NoConversion n

def exactIdentityFormation : Replay 0 :=
  .idForm identityLevel functionFormation lowerIndependentCode lowerIndependentCode

def exactConsumerFormation : Replay 0 :=
  .piForm identityLevel identityLevel exactIdentityFormation
    (exactIdentityFormation.rename noConversionRename wk)

def mixedConsumerFormation : Replay 0 :=
  .piForm identityLevel identityLevel mixedIdentityFormation
    (mixedIdentityFormation.rename noConversionRename wk)

def program : Tower.Tm 0 := .app (.lam (.var 0)) (.refl independentFunction)

def exactCode : Replay 0 :=
  .appElim mixedIdentityType (rename wk mixedIdentityType)
    (.lamIntro consumerLevel exactConsumerFormation .var) mixedReflexivityCode

def mixedCode : Replay 0 :=
  .appElim mixedIdentityType (rename wk mixedIdentityType)
    (.lamIntro consumerLevel mixedConsumerFormation .var) mixedReflexivityCode

theorem formation_checks :
    check Tower.rules noConversionCheck .nil
      (.pi mixedIdentityType (rename wk mixedIdentityType))
      (.head consumerLevel) exactConsumerFormation = true ∧
    check Tower.rules noConversionCheck .nil
      (.pi mixedIdentityType (rename wk mixedIdentityType))
      (.head consumerLevel) mixedConsumerFormation = true := by
  decide +kernel

theorem programs_check :
    check Tower.rules noConversionCheck .nil program mixedIdentityType exactCode = true ∧
    check Tower.rules noConversionCheck .nil program mixedIdentityType mixedCode = true := by
  decide +kernel

theorem exact_contracts :
    exactCode.contractBeta (.var 0) (.refl independentFunction) mixedIdentityType =
      some mixedReflexivityCode := rfl

theorem mixed_contracts :
    mixedCode.contractBeta (.var 0) (.refl independentFunction) mixedIdentityType =
      some mixedReflexivityCode := rfl

theorem returned_proof_checks :
    check Tower.rules noConversionCheck .nil (.refl independentFunction)
      mixedIdentityType mixedReflexivityCode = true :=
  exactCode.contractBeta_result_checked Tower.rules mixedReflexivityCode
    programs_check.1 exact_contracts

theorem proof_argument_unqualified :
    mixedReflexivityCode.resultFormationsNeutral Tower.rules TowerDecisions.headTarget
      .nil (.refl independentFunction) mixedIdentityType = false :=
  mixed_reflexivity_not_qualified

theorem consumers_outside_qualified_fragment :
    exactCode.resultFormationsNeutral Tower.rules TowerDecisions.headTarget
      .nil program mixedIdentityType = false ∧
    mixedCode.resultFormationsNeutral Tower.rules TowerDecisions.headTarget
      .nil program mixedIdentityType = false := by
  decide +kernel

theorem codes_differ : exactCode ≠ mixedCode := by
  intro equal
  cases equal

theorem exact_identity_checks :
    check Tower.rules noConversionCheck .nil mixedIdentityType
      (.head identityLevel) exactIdentityFormation = true := by
  decide +kernel

theorem independent_result_formation :
    lowerIndependentCode.resultFormation noConversionRename noConversionSubstitute
      TowerDecisions.headTarget .nil independentFunction functionType =
      some (identityLevel, functionFormation) := rfl

/-- The previously proved reflexivity-membership theorem is also valid for
the exact lower/lower identity formation. This is where an accepted but
unqualified argument is admitted without a global semantic-typing axiom. -/
theorem proof_in_exact_domain (heads : Tower.Head → ZFSet.{u})
    (constants : DeclName → ZFSet.{u})
    (proof domain : Meaning.{u} 0)
    (atProof : assemble heads constants mixedReflexivityCode
      (.refl independentFunction) mixedIdentityType = some proof)
    (atDomain : assemble heads constants exactIdentityFormation
      mixedIdentityType (.head identityLevel) = some domain) :
    ∀ env, proof.value env ∈ domain.value env :=
  reflexivity_in_same_endpoint_formation heads constants functionType independentFunction
    identityLevel lowerIndependentCode functionFormation lowerIndependentCode
    proof domain atProof atDomain

/-- An actual higher-order application consumes the unqualified proof value.
The two independently retained identity domains agree where this closed
proof is admitted; both checked applications return that proof, and the
result remains a member of the mixed identity fibre. -/
theorem computed_proof_consumed (h : CofinalInaccessibles.{u})
    (seed ground : ZFSet.{u}) (valuation : Nat → Nat)
    (groundTyped : ground ∈ universeSet h seed 0)
    (constants : DeclName → ZFSet.{u}) :
    ∃ exactResult mixedResult mixedDomain : Meaning.{u} 0,
      assemble (interpretHead h seed ground valuation) constants exactCode program
        mixedIdentityType = some exactResult ∧
      assemble (interpretHead h seed ground valuation) constants mixedCode program
        mixedIdentityType = some mixedResult ∧
      assemble (interpretHead h seed ground valuation) constants mixedIdentityFormation
        mixedIdentityType (.head identityLevel) = some mixedDomain ∧
      ∀ env, exactResult.value env = mixedResult.value env ∧
        mixedResult.value env ∈ mixedDomain.value env := by
  let heads := interpretHead h seed ground valuation
  obtain ⟨proof, mixedDomain, atProof, atMixedDomain, proofMixed⟩ :=
    mixed_reflexivity_membership h seed ground valuation groundTyped constants
  obtain ⟨exactDomain, atExactDomain, _⟩ := accepted_assembles heads constants
    Tower.rules noConversionCheck exactIdentityFormation exact_identity_checks
  obtain ⟨exactFormed, atExactFormed, _⟩ := accepted_assembles heads constants
    Tower.rules noConversionCheck exactConsumerFormation formation_checks.1
  obtain ⟨mixedFormed, atMixedFormed, _⟩ := accepted_assembles heads constants
    Tower.rules noConversionCheck mixedConsumerFormation formation_checks.2
  obtain ⟨exactResult, atExactResult, _⟩ := accepted_assembles heads constants
    Tower.rules noConversionCheck exactCode programs_check.1
  obtain ⟨mixedResult, atMixedResult, _⟩ := accepted_assembles heads constants
    Tower.rules noConversionCheck mixedCode programs_check.2
  obtain ⟨exactA, _, atExactA, _, _, exactRetained⟩ :=
    assemble_piFormation heads constants exactConsumerFormation rfl atExactFormed
  rw [atExactDomain] at atExactA
  cases Option.some.inj atExactA
  obtain ⟨mixedA, _, atMixedA, _, _, mixedRetained⟩ :=
    assemble_piFormation heads constants mixedConsumerFormation rfl atMixedFormed
  rw [atMixedDomain] at atMixedA
  cases Option.some.inj atMixedA
  have proofExact : ∀ env, proof.value env ∈ exactDomain.value env :=
    proof_in_exact_domain heads constants proof exactDomain atProof atExactDomain
  refine ⟨exactResult, mixedResult, mixedDomain, atExactResult, atMixedResult,
    atMixedDomain, ?_⟩
  intro env
  have resultsEqual := application_lambda_related heads constants
    consumerLevel consumerLevel mixedIdentityType mixedIdentityType
    (rename wk mixedIdentityType) (rename wk mixedIdentityType)
    (.var 0) (.var 0) (.refl independentFunction) (.refl independentFunction)
    exactConsumerFormation mixedConsumerFormation mixedReflexivityCode mixedReflexivityCode
    (.var : Replay 1) (.var : Replay 1)
    exactFormed mixedFormed proof proof exactResult mixedResult
    (.plain (fun extension => extension 0)) (.plain (fun extension => extension 0))
    exactDomain.value mixedDomain.value
    atExactFormed atMixedFormed exactRetained mixedRetained rfl rfl
    atProof atProof atExactResult atMixedResult env env Eq Eq
    (proofExact env) (proofMixed env) rfl
    (by intro x _ y _ equal; exact equal)
  have exactReturnsProof := application_lambda_value heads constants consumerLevel
    mixedIdentityType (rename wk mixedIdentityType) (.var 0) (.refl independentFunction)
    exactConsumerFormation mixedReflexivityCode (.var : Replay 1)
    exactFormed proof exactResult (.plain (fun extension => extension 0)) exactDomain.value
    atExactFormed exactRetained rfl atProof atExactResult env (proofExact env)
  exact ⟨resultsEqual, resultsEqual ▸ exactReturnsProof.symm ▸ proofMixed env⟩

/-- The exact retained beta transformer returns the original proof
certificate from both distinct accepted applications. Interpretation of
each source agrees with that checked return on every valid closed
environment, even though the proof argument is not result-qualified. -/
theorem checked_beta_returns_computed_proof (h : CofinalInaccessibles.{u})
    (seed ground : ZFSet.{u}) (valuation : Nat → Nat)
    (groundTyped : ground ∈ universeSet h seed 0)
    (constants : DeclName → ZFSet.{u}) :
    ∃ exactResult mixedResult proof : Meaning.{u} 0,
      assemble (interpretHead h seed ground valuation) constants exactCode program
        mixedIdentityType = some exactResult ∧
      assemble (interpretHead h seed ground valuation) constants mixedCode program
        mixedIdentityType = some mixedResult ∧
      assemble (interpretHead h seed ground valuation) constants mixedReflexivityCode
        (.refl independentFunction) mixedIdentityType = some proof ∧
      exactCode.contractBeta (.var 0) (.refl independentFunction) mixedIdentityType =
        some mixedReflexivityCode ∧
      mixedCode.contractBeta (.var 0) (.refl independentFunction) mixedIdentityType =
        some mixedReflexivityCode ∧
      check Tower.rules noConversionCheck .nil (.refl independentFunction)
        mixedIdentityType mixedReflexivityCode = true ∧
      ∀ env, exactResult.value env = proof.value env ∧
        mixedResult.value env = proof.value env := by
  let heads := interpretHead h seed ground valuation
  obtain ⟨proof, mixedDomain, atProof, atMixedDomain, proofMixed⟩ :=
    mixed_reflexivity_membership h seed ground valuation groundTyped constants
  obtain ⟨exactDomain, atExactDomain, _⟩ := accepted_assembles heads constants
    Tower.rules noConversionCheck exactIdentityFormation exact_identity_checks
  obtain ⟨exactResult, atExactResult, _⟩ := accepted_assembles heads constants
    Tower.rules noConversionCheck exactCode programs_check.1
  obtain ⟨mixedResult, atMixedResult, _⟩ := accepted_assembles heads constants
    Tower.rules noConversionCheck mixedCode programs_check.2
  have proofExact := proof_in_exact_domain heads constants proof exactDomain
    atProof atExactDomain
  refine ⟨exactResult, mixedResult, proof, atExactResult, atMixedResult, atProof,
    exact_contracts, mixed_contracts, returned_proof_checks, ?_⟩
  intro env
  have exactParts : exactConsumerFormation.piFormation =
      some (identityLevel, identityLevel, exactIdentityFormation,
        exactIdentityFormation.rename noConversionRename wk) := rfl
  have mixedParts : mixedConsumerFormation.piFormation =
      some (identityLevel, identityLevel, mixedIdentityFormation,
        mixedIdentityFormation.rename noConversionRename wk) := rfl
  have exactAdmitted := rootBeta_argument_admitted heads constants Tower.rules
    (A := mixedIdentityType) (B := rename wk mixedIdentityType)
    (formation := exactConsumerFormation) (domainCode := exactIdentityFormation)
    (codomainCode := exactIdentityFormation.rename noConversionRename wk)
    programs_check.1 exactParts proof exactDomain atProof atExactDomain env (proofExact env)
  have mixedAdmitted := rootBeta_argument_admitted heads constants Tower.rules
    (A := mixedIdentityType) (B := rename wk mixedIdentityType)
    (formation := mixedConsumerFormation) (domainCode := mixedIdentityFormation)
    (codomainCode := mixedIdentityFormation.rename noConversionRename wk)
    programs_check.2 mixedParts proof mixedDomain atProof atMixedDomain env (proofMixed env)
  obtain ⟨exactTarget, atExactTarget, exactEqual⟩ := contractBeta_value
    heads constants Tower.rules exactCode exactResult programs_check.1
      atExactResult exact_contracts env exactAdmitted
  obtain ⟨mixedTarget, atMixedTarget, mixedEqual⟩ := contractBeta_value
    heads constants Tower.rules mixedCode mixedResult programs_check.2
      atMixedResult mixed_contracts env mixedAdmitted
  change assemble heads constants mixedReflexivityCode (.refl independentFunction)
    mixedIdentityType = some proof at atProof
  change assemble heads constants mixedReflexivityCode (.refl independentFunction)
    mixedIdentityType = some exactTarget at atExactTarget
  change assemble heads constants mixedReflexivityCode (.refl independentFunction)
    mixedIdentityType = some mixedTarget at atMixedTarget
  rw [atProof] at atExactTarget atMixedTarget
  cases Option.some.inj atExactTarget
  cases Option.some.inj atMixedTarget
  exact ⟨exactEqual, mixedEqual⟩

#print axioms formation_checks
#print axioms programs_check
#print axioms exact_contracts
#print axioms mixed_contracts
#print axioms returned_proof_checks
#print axioms proof_argument_unqualified
#print axioms consumers_outside_qualified_fragment
#print axioms codes_differ
#print axioms exact_identity_checks
#print axioms independent_result_formation
#print axioms proof_in_exact_domain
#print axioms computed_proof_consumed
#print axioms checked_beta_returns_computed_proof

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayComputedProofConsumer
