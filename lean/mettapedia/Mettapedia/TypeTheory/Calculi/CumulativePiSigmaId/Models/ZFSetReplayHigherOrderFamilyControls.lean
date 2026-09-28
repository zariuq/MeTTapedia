import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayHigherOrderApplicationControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayQualifiedHigherOrderFamily
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayIdentityFamilySubstitution

/-!
# A dependent family after independently computed function and argument

The source application computes both its function and its argument; the
comparison application uses the original context variables. Qualified paths
to those variables yield equality of the application values on valid
environments. A checked identity family is then instantiated with each
distinct raw application using its retained certificate. A forged function
certificate remains rejected after family instantiation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayHigherOrderFamilyControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay ZFSetReplayInterpretation
open ZFSetTypeExpressionInterpretation (Environment)
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetInterpretation
open ZFSetTraceUniverseInterpretation (interpretHead)
open ZFSetReplayUniverseModel (universeModel empty_constants_model successor_qualified)
open ZFSetReplayQualifiedTypingControls (functionType functionFormation identity)
open ZFSetReplayHigherOrderApplicationControls

universe u

private abbrev u0 : Tower.Head := .sort Tower.zero
private abbrev u1 : Tower.Head := .sort (.succ Tower.zero)
private abbrev familyLevel : Tower.Head := .sort (.succ Tower.zero)
private abbrev Replay (n : Nat) := Code Tower.Head NoConversion n

def family : Tower.Tm 3 := .id (.head u0) (.var 0) (.var 0)
def familyCode : Replay 3 := .idForm familyLevel .headType .var .var

theorem family_checked :
    check Tower.rules noConversionCheck (.snoc context (.head u0)) family
      (.head familyLevel) familyCode = true := by decide +kernel

theorem family_qualified :
    familyCode.neutralEliminations family (.head familyLevel) = true := rfl

theorem raw_family_instances_differ :
    inst0 computedApplication family ≠ inst0 originalApplication family := by
  decide +kernel

/-- Each generated family can be inhabited by a separately checked proof
whose retained evidence contains the corresponding computed application. -/
theorem reflexivity_proofs_checked :
    check Tower.rules noConversionCheck context (.refl computedApplication)
      (inst0 computedApplication family)
      (.reflIntro (.head u0) computedApplicationCode) = true ∧
    check Tower.rules noConversionCheck context (.refl originalApplication)
      (inst0 originalApplication family)
      (.reflIntro (.head u0) originalApplicationCode) = true := by
  decide +kernel

/-- A proof certificate for the computed application cannot be reused for
the different raw application merely because their meanings later agree. -/
theorem crossed_reflexivity_certificate_rejected :
    check Tower.rules noConversionCheck context (.refl originalApplication)
      (inst0 originalApplication family)
      (.reflIntro (.head u0) computedApplicationCode) = false := by
  decide +kernel

/-- Independently computed functions and arguments produce two checked family
instances whose set-code meanings agree in every valid source environment.
The function and argument comparisons are derived from the retained paths,
not supplied as semantic premises. -/
theorem checked_higher_order_family_instances
    (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u}) (valuation : Nat → Nat)
    (groundTyped : ground ∈ universeSet h seed 0) (constants : DeclName → ZFSet.{u}) :
    let heads := interpretHead h seed ground valuation
    let leftInstance := Code.instantiate noConversionRename noConversionSubstitute
      family (.head familyLevel) computedApplication familyCode computedApplicationCode
    let rightInstance := Code.instantiate noConversionRename noConversionSubstitute
      family (.head familyLevel) originalApplication familyCode originalApplicationCode
    ∃ valid : Environment.{u} 2 → Prop,
      assembleContext heads constants contextCode context = some valid ∧
      check Tower.rules noConversionCheck context
        (inst0 computedApplication family) (.head familyLevel) leftInstance = true ∧
      check Tower.rules noConversionCheck context
        (inst0 originalApplication family) (.head familyLevel) rightInstance = true ∧
      ∃ left right,
        assemble heads constants leftInstance (inst0 computedApplication family)
          (.head familyLevel) = some left ∧
        assemble heads constants rightInstance (inst0 originalApplication family)
          (.head familyLevel) = some right ∧
        ∀ env, valid env → left.value env = right.value env := by
  let heads := interpretHead h seed ground valuation
  obtain ⟨valid, atContext⟩ := accepted_context_assembles heads constants
    Tower.rules noConversionCheck contextCode context_checked
  obtain ⟨leftFunction, atLeftFunction, _⟩ := accepted_assembles heads constants
    Tower.rules noConversionCheck computedFunctionCode components_checked.1
  obtain ⟨rightFunction, atRightFunction, _⟩ := accepted_assembles heads constants
    Tower.rules noConversionCheck originalFunctionCode components_checked.2.1
  obtain ⟨leftArgument, atLeftArgument, _⟩ := accepted_assembles heads constants
    Tower.rules noConversionCheck computedArgumentCode components_checked.2.2.1
  obtain ⟨rightArgument, atRightArgument, _⟩ := accepted_assembles heads constants
    Tower.rules noConversionCheck originalArgumentCode components_checked.2.2.2
  let functions : QualifiedImagePaths heads constants Tower.rules
      TowerDecisions.headTarget context contextCode leftFunction rightFunction :=
    QualifiedImagePaths.ofSearch heads constants Tower.rules TowerDecisions.headTarget
      context contextCode leftFunction rightFunction
      functionType functionType computedFunction originalFunction originalFunction
      computedFunctionCode originalFunctionCode originalFunctionCode originalFunctionCode
      2 1 (by rfl) (by rfl) components_checked.1 components_checked.2.1
      atLeftFunction atRightFunction rfl
  let arguments : QualifiedImagePaths heads constants Tower.rules
      TowerDecisions.headTarget context contextCode leftArgument rightArgument :=
    QualifiedImagePaths.ofSearch heads constants Tower.rules TowerDecisions.headTarget
      context contextCode leftArgument rightArgument
      (.head u0) (.head u0) computedArgument originalArgument originalArgument
      computedArgumentCode originalArgumentCode originalArgumentCode originalArgumentCode
      2 1 (by rfl) (by rfl) components_checked.2.2.1 components_checked.2.2.2
      atLeftArgument atRightArgument rfl
  refine ⟨valid, atContext, ?_⟩
  simpa only [functions, arguments, computedApplication, originalApplication,
    computedApplicationCode, originalApplicationCode,
    QualifiedImagePaths.ofSearch] using
    (qualified_higher_order_application_family_values heads constants Tower.rules
      TowerDecisions.headTarget
      (universeModel h seed ground valuation groundTyped)
      (empty_constants_model heads constants)
      FormationSensitive.towerUniverseRegularity successor_qualified
      context contextCode valid context_checked atContext
      (.head u0) (.head u0) (.head u0) (.head u0)
      leftFunction rightFunction leftArgument rightArgument functions arguments
      rfl rfl rfl rfl rfl family familyLevel familyLevel familyCode familyCode
      family_checked family_checked family_qualified)

/-- Both different higher-order applications are subsequently used as
indices of checked identity proofs. Their proof values inhabit the generated
family fibres, and those fibres agree on valid environments. -/
theorem checked_higher_order_dependent_proofs
    (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u}) (valuation : Nat → Nat)
    (groundTyped : ground ∈ universeSet h seed 0) (constants : DeclName → ZFSet.{u}) :
    let heads := interpretHead h seed ground valuation
    let leftFamilyCode := Code.instantiate noConversionRename noConversionSubstitute
      family (.head familyLevel) computedApplication familyCode computedApplicationCode
    let rightFamilyCode := Code.instantiate noConversionRename noConversionSubstitute
      family (.head familyLevel) originalApplication familyCode originalApplicationCode
    let leftProofCode := Code.instantiate noConversionRename noConversionSubstitute
      (.refl (.var 0)) family computedApplication
      (.reflIntro (.head u0) (.var : Replay 3)) computedApplicationCode
    let rightProofCode := Code.instantiate noConversionRename noConversionSubstitute
      (.refl (.var 0)) family originalApplication
      (.reflIntro (.head u0) (.var : Replay 3)) originalApplicationCode
    ∃ valid : Environment.{u} 2 → Prop,
      assembleContext heads constants contextCode context = some valid ∧
      check Tower.rules noConversionCheck context
        (inst0 computedApplication family) (.head familyLevel) leftFamilyCode = true ∧
      check Tower.rules noConversionCheck context
        (inst0 originalApplication family) (.head familyLevel) rightFamilyCode = true ∧
      check Tower.rules noConversionCheck context
        (inst0 computedApplication (.refl (.var 0)))
        (inst0 computedApplication family) leftProofCode = true ∧
      check Tower.rules noConversionCheck context
        (inst0 originalApplication (.refl (.var 0)))
        (inst0 originalApplication family) rightProofCode = true ∧
      ∃ leftFamily leftProof rightFamily rightProof,
        assemble heads constants leftFamilyCode (inst0 computedApplication family)
          (.head familyLevel) = some leftFamily ∧
        assemble heads constants leftProofCode
          (inst0 computedApplication (.refl (.var 0)))
          (inst0 computedApplication family) = some leftProof ∧
        assemble heads constants rightFamilyCode (inst0 originalApplication family)
          (.head familyLevel) = some rightFamily ∧
        assemble heads constants rightProofCode
          (inst0 originalApplication (.refl (.var 0)))
          (inst0 originalApplication family) = some rightProof ∧
        ∀ env, valid env → leftFamily.value env = rightFamily.value env ∧
          leftProof.value env ∈ leftFamily.value env ∧
          rightProof.value env ∈ rightFamily.value env := by
  let heads := interpretHead h seed ground valuation
  obtain ⟨valid, atContext, leftChecked, rightChecked,
      left, right, atLeft, atRight, agree⟩ :=
    checked_higher_order_family_instances h seed ground valuation groundTyped constants
  obtain ⟨leftFamilyChecked, leftProofChecked, leftFamily, leftProof,
      atLeftFamily, atLeftProof, leftMember⟩ :=
    computed_argument_diagonal_reflexivity_membership heads constants Tower.rules
      (context := context) (A := .head u0) (argument := computedApplication)
      computedApplicationCode (by decide +kernel)
      (.head u0) (.var 0) familyLevel .headType .var family_checked
  obtain ⟨rightFamilyChecked, rightProofChecked, rightFamily, rightProof,
      atRightFamily, atRightProof, rightMember⟩ :=
    computed_argument_diagonal_reflexivity_membership heads constants Tower.rules
      (context := context) (A := .head u0) (argument := originalApplication)
      originalApplicationCode (by decide +kernel)
      (.head u0) (.var 0) familyLevel .headType .var family_checked
  have leftSame : leftFamily = left := by
    apply Option.some.inj
    exact atLeftFamily.symm.trans atLeft
  have rightSame : rightFamily = right := by
    apply Option.some.inj
    exact atRightFamily.symm.trans atRight
  refine ⟨valid, atContext, leftFamilyChecked, rightFamilyChecked,
    leftProofChecked, rightProofChecked, leftFamily, leftProof,
    rightFamily, rightProof, atLeftFamily, atLeftProof,
    atRightFamily, atRightProof, ?_⟩
  intro env admitted
  exact ⟨by simpa only [leftSame, rightSame] using agree env admitted,
    leftMember env, rightMember env⟩

def forgedFunctionApplicationCode : Replay 2 :=
  .appElim (.head u0) (.head u0) .headType computedArgumentCode

def forgedFamilyInstance : Replay 2 :=
  Code.instantiate noConversionRename noConversionSubstitute
    family (.head familyLevel) computedApplication familyCode forgedFunctionApplicationCode

/-- Discovering a terminal is not an authority to fabricate the function's
typing tree: the malformed certificate is still rejected after the dependent
family is instantiated. -/
theorem forged_function_family_instance_rejected :
    check Tower.rules noConversionCheck context
      (inst0 computedApplication family) (.head familyLevel)
      forgedFamilyInstance = false := by decide +kernel

#print axioms checked_higher_order_family_instances
#print axioms checked_higher_order_dependent_proofs
#print axioms reflexivity_proofs_checked
#print axioms crossed_reflexivity_certificate_rejected
#print axioms raw_family_instances_differ
#print axioms forged_function_family_instance_rejected

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayHigherOrderFamilyControls
