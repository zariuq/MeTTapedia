import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayMixedIdentityFamilyControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralTypingReplayBetaIdentityConversion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayBetaIdentityAdmission
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayBetaIdentityComparison
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayPairComparison
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayComputation

/-!
# Retained conversion evidence for a computed identity endpoint

Reflexivity at the beta-expanded identity family is not a primitive rule.
The source reflexivity proof is checked at its diagonal identity type; a
separate finite beta-conversion code and an independently checked target
formation admit it at the mixed family. The conversion wrapper retains the
source proof and does not infer a proof from equality of set meanings.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayCheckedMixedIdentityProof

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay ZFSetReplayInterpretation
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetTraceProducts (traceApp traceLam traceApp_graph_beta)
open ZFSetDependentProducts (graph)
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetInterpretation
open ZFSetTraceUniverseInterpretation (interpretHead)
open ZFSetReplayQualifiedTypingControls
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayMixedIdentityFamilyControls
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayUniverseModel

local instance : DecidableRel Tower.rules.headEq := Tower.instDecidableHeadEq

private abbrev familyLevel : Tower.Head :=
  .sort (.max (.succ Tower.zero) (.succ Tower.zero))
private abbrev packageLevel : Tower.Head :=
  .sort (.max
    (.max (.succ Tower.zero) (.succ Tower.zero))
    (.max (.succ Tower.zero) (.succ Tower.zero)))

def emptyDecoder : StructuralConversionCode.RootDecoder Tower.rules.computation :=
  StructuralConversionCode.RootDecoder.ofEmpty Tower.rules.computation rfl

abbrev ConversionCode (n : Nat) :=
  StructuralConversionCode.Code Tower.Head emptyDecoder.Code n

abbrev conversionCheck {n : Nat} (code : ConversionCode n)
    (left right : Tower.Tm n) : Bool :=
  betaConversionCheck Tower.rules emptyDecoder code left right

def includeNoConversion {n : Nat} (code : NoConversion n) : ConversionCode n :=
  nomatch code

def targetFormation : StructuralTypingReplay.Code Tower.Head ConversionCode 0 :=
  (Code.instantiate noConversionRename noConversionSubstitute
    mixedFamily (.head familyLevel) computedFunction mixedFamilyCode
    computedFunctionCode).mapConversion includeNoConversion

def identityPiFormation : StructuralTypingReplay.Code Tower.Head ConversionCode 0 :=
  ((.piForm familyLevel familyLevel functionFormation functionFormation :
    StructuralTypingReplay.Code Tower.Head NoConversion 0).mapConversion includeNoConversion)

/-- A second accepted certificate retains an explicit cumulative step for
the same function type. It is a distinct tree, not a replacement for the
original certificate. -/
def wrappedIdentityPiFormation : StructuralTypingReplay.Code Tower.Head ConversionCode 0 :=
  .cumul packageLevel identityPiFormation

def wrappedTargetFormation : StructuralTypingReplay.Code Tower.Head ConversionCode 0 :=
  betaIdentityLeftFormationCode Tower.rules emptyDecoder familyLevel packageLevel
    functionType (functionFormation.mapConversion includeNoConversion)
    wrappedIdentityPiFormation (computedFunctionCode.mapConversion includeNoConversion)

def wrappedProofCode : StructuralTypingReplay.Code Tower.Head ConversionCode 0 :=
  betaIdentityLeftProof Tower.rules emptyDecoder functionType computedFunction familyLevel
    (computedFunctionCode.mapConversion includeNoConversion) wrappedTargetFormation

theorem targetFormation_eq_generic :
    targetFormation = betaIdentityLeftFormationCode Tower.rules emptyDecoder
      familyLevel packageLevel functionType
      (functionFormation.mapConversion includeNoConversion)
      identityPiFormation
      (computedFunctionCode.mapConversion includeNoConversion) := by
  rfl

private theorem computed_family_instance :
    inst0 computedFunction mixedFamily =
      .id functionType (.app (.lam (.var 0)) computedFunction) computedFunction := by
  simp [mixedFamily, computedLeft, functionType, inst0, subst0, subst]

def proofCode : StructuralTypingReplay.Code Tower.Head ConversionCode 0 :=
  betaIdentityLeftProof Tower.rules emptyDecoder functionType computedFunction familyLevel
    (computedFunctionCode.mapConversion includeNoConversion) targetFormation

theorem checked :
    check Tower.rules conversionCheck .nil (.refl computedFunction)
      (inst0 computedFunction mixedFamily) proofCode = true := by
  change check Tower.rules (betaConversionCheck Tower.rules emptyDecoder) .nil
    (.refl computedFunction)
    (.id functionType (.app (.lam (.var 0)) computedFunction) computedFunction)
    (betaIdentityLeftProof Tower.rules emptyDecoder functionType computedFunction familyLevel
      (computedFunctionCode.mapConversion includeNoConversion) targetFormation) = true
  exact betaIdentityLeftProof_checked Tower.rules emptyDecoder .nil functionType
    computedFunction familyLevel (computedFunctionCode.mapConversion includeNoConversion)
    targetFormation (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- A path with the right constructor but wrong endpoints is not authority
for the cast. In particular, reflexivity of the diagonal type cannot serve
as the beta-expansion certificate. -/
theorem malformed_conversion_rejected :
    check Tower.rules conversionCheck .nil (.refl computedFunction)
      (inst0 computedFunction mixedFamily)
      (.convert (.id functionType computedFunction computedFunction) familyLevel
        (.reflIntro functionType
          (computedFunctionCode.mapConversion includeNoConversion))
        targetFormation (.refl (.id functionType computedFunction computedFunction))) = false := by
  decide +kernel

theorem typing :
    FormationSensitive.Typing Tower.rules .nil (.refl computedFunction)
      (inst0 computedFunction mixedFamily) := by
  exact betaIdentityLeftProof_typing Tower.rules emptyDecoder .nil functionType
    computedFunction familyLevel (computedFunctionCode.mapConversion includeNoConversion)
    targetFormation (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The converted proof is the dependent second component. Its type is the
mixed identity family instantiated at the actual first component. -/
def packageType : Tower.Tm 0 := .sigma functionType mixedFamily

def packageFormation : StructuralTypingReplay.Code Tower.Head ConversionCode 0 :=
  .sigmaForm familyLevel familyLevel
    (functionFormation.mapConversion includeNoConversion)
    (mixedFamilyCode.mapConversion includeNoConversion)

def packageCode : StructuralTypingReplay.Code Tower.Head ConversionCode 0 :=
  .pairIntro packageLevel packageFormation
    (computedFunctionCode.mapConversion includeNoConversion) proofCode

def package : Tower.Tm 0 := .pair computedFunction (.refl computedFunction)

theorem package_checked :
    check Tower.rules conversionCheck .nil package packageType packageCode = true := by
  decide +kernel

def dependentConsumerCode : StructuralTypingReplay.Code Tower.Head ConversionCode 0 :=
  .sndElim functionType mixedFamily packageCode

def wrappedPackageCode : StructuralTypingReplay.Code Tower.Head ConversionCode 0 :=
  .pairIntro packageLevel packageFormation
    (computedFunctionCode.mapConversion includeNoConversion) wrappedProofCode

def wrappedDependentConsumerCode : StructuralTypingReplay.Code Tower.Head ConversionCode 0 :=
  .sndElim functionType mixedFamily wrappedPackageCode

def firstProjectionCode : StructuralTypingReplay.Code Tower.Head ConversionCode 0 :=
  .fstElim mixedFamily packageCode

def consumerEndpointCode : StructuralTypingReplay.Code Tower.Head ConversionCode 0 :=
  .appElim functionType functionType
    (consumerCode.mapConversion includeNoConversion) firstProjectionCode

def consumerFamilyCode : StructuralTypingReplay.Code Tower.Head ConversionCode 0 :=
  .idForm familyLevel (functionFormation.mapConversion includeNoConversion)
    consumerEndpointCode firstProjectionCode

theorem consumer_family_checked :
    check Tower.rules conversionCheck .nil (inst0 (.fst package) mixedFamily)
      (.head familyLevel) consumerFamilyCode = true := by
  decide +kernel

theorem dependent_consumer_checked :
    check Tower.rules conversionCheck .nil (.snd package)
      (inst0 (.fst package) mixedFamily) dependentConsumerCode = true := by
  decide +kernel

theorem wrapped_package_and_consumer_check :
    check Tower.rules conversionCheck .nil package packageType wrappedPackageCode = true ∧
    check Tower.rules conversionCheck .nil (.snd package)
      (inst0 (.fst package) mixedFamily) wrappedDependentConsumerCode = true := by
  decide +kernel

theorem dependent_consumer_typed :
    FormationSensitive.Typing Tower.rules .nil (.snd package)
      (inst0 (.fst package) mixedFamily) := by
  exact check_sound Tower.rules conversionCheck
    (by
      intro n code left right accepted
      change Conv Tower.HeadEq left right Tower.rules.computation
      exact StructuralConversionCode.Code.check_sound
        (headEq := Tower.HeadEq) emptyDecoder accepted)
    dependentConsumerCode dependent_consumer_checked

universe u

/-- The computed first component belongs to the interpreted function domain.
The membership is earned from its retained result-formation certificate. -/
theorem computed_argument_in_function_domain
    (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u}) (valuation : Nat → Nat)
    (groundTyped : ground ∈ universeSet h seed 0)
    (constants : DeclName → ZFSet.{u}) :
    ∃ argument domain,
      assemble (interpretHead h seed ground valuation) constants
        computedFunctionCode computedFunction functionType = some argument ∧
      assemble (interpretHead h seed ground valuation) constants
        functionFormation functionType (.head familyLevel) = some domain ∧
      ∀ env, argument.value env ∈ domain.value env := by
  let heads := interpretHead h seed ground valuation
  obtain ⟨argument, atArgument, _⟩ := accepted_assembles heads constants Tower.rules
    noConversionCheck computedFunctionCode functions_checked.2.1
  obtain ⟨domain, atDomain, _⟩ := accepted_assembles heads constants Tower.rules
    noConversionCheck functionFormation reflexivity_and_type_checked.2
  refine ⟨argument, domain, atArgument, atDomain, ?_⟩
  intro env
  exact qualified_membership heads constants Tower.rules
    TowerDecisions.headTarget FormationSensitive.towerUniverseRegularity
    successor_qualified (universeModel h seed ground valuation groundTyped)
    (empty_constants_model _ constants) computedFunctionCode .nil rfl
    functions_checked.2.1 functions_qualified.2.1 (fun _ => True)
    argument rfl atArgument familyLevel functionFormation domain
    reflexivity_and_type_checked.2 atDomain env True.intro

/-- The outer identity lambda's retained Pi formation fixes the graph's
domain; the body is the bound variable, so its graph sends each member to
itself. -/
theorem consumer_function_graph
    (heads : Tower.Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})
    (domain : Meaning.{u} 0)
    (atDomain : assemble heads constants functionFormation functionType
      (.head familyLevel) = some domain) :
    assemble heads constants (consumerCode.mapConversion includeNoConversion)
      identity (.pi functionType functionType) =
      some (Meaning.plain (fun env =>
        traceLam (graph (domain.value env) (fun x => x)))) := by
  obtain ⟨body, atBody, _⟩ := accepted_assembles heads constants Tower.rules
    noConversionCheck (functionFormation : StructuralTypingReplay.Code Tower.Head NoConversion 1)
    (by decide +kernel : check Tower.rules noConversionCheck (.snoc .nil functionType)
      functionType (.head familyLevel) functionFormation = true)
  rw [assemble_mapConversion]
  simp [consumerCode, identity, assemble, atDomain, atBody]
  rfl

/-- The dependent projection consumes the retained converted proof. Its
denotation is the reflexivity token, independently of the computed first
component's particular set value. -/
theorem dependent_consumer_value
    (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u}) (valuation : Nat → Nat)
    (constants : DeclName → ZFSet.{u}) :
    ∃ result,
      assemble (interpretHead h seed ground valuation) constants dependentConsumerCode
        (.snd package) (inst0 (.fst package) mixedFamily) = some result ∧
      ∀ env, result.value env = (∅ : ZFSet.{u}) := by
  let heads := interpretHead h seed ground valuation
  obtain ⟨argument, atArgument, _⟩ := accepted_assembles heads constants Tower.rules
    noConversionCheck computedFunctionCode functions_checked.2.1
  have atMapped : assemble heads constants
      (computedFunctionCode.mapConversion includeNoConversion)
      computedFunction functionType = some argument := by
    rw [assemble_mapConversion]
    exact atArgument
  have atProof : assemble heads constants proofCode (.refl computedFunction)
      (inst0 computedFunction mixedFamily) =
      some (Meaning.plain (fun _ => (∅ : ZFSet.{u}))) := by rfl
  refine ⟨Meaning.plain (fun env =>
    Mettapedia.SetTheory.ZFSetOrderedPair.second
      (ZFSet.pair (argument.value env) (∅ : ZFSet.{u}))), ?_, ?_⟩
  · simp only [dependentConsumerCode, packageCode, package, assemble]
    rw [atMapped, atProof]
    rfl
  · intro env
    exact Mettapedia.SetTheory.ZFSetOrderedPair.second_pair _ _

/-- The accepted converted proof still denotes the original reflexivity
token; its target fibre is inhabited on every environment admitted by the
empty context. -/
theorem proof_in_computed_family
    (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u}) (valuation : Nat → Nat)
    (groundTyped : ground ∈ universeSet h seed 0)
    (constants : DeclName → ZFSet.{u}) :
    ∃ proof family,
      assemble (interpretHead h seed ground valuation) constants proofCode
        (.refl computedFunction) (inst0 computedFunction mixedFamily) = some proof ∧
      assemble (interpretHead h seed ground valuation) constants targetFormation
        (inst0 computedFunction mixedFamily) (.head familyLevel) = some family ∧
      ∀ env, proof.value env ∈ family.value env := by
  let heads := interpretHead h seed ground valuation
  obtain ⟨argument, domainMeaning, atArgument, atDomain, member⟩ :=
    computed_argument_in_function_domain h seed ground valuation groundTyped constants
  have piChecked : check Tower.rules conversionCheck .nil
      (.pi functionType (rename wk functionType)) (.head packageLevel)
      identityPiFormation = true := by decide +kernel
  obtain ⟨formed, atPi, _⟩ := accepted_assembles heads constants Tower.rules
    conversionCheck identityPiFormation piChecked
  obtain ⟨retained, _, atRetained, _, _, retainedDomain⟩ :=
    assemble_piFormation heads constants identityPiFormation rfl atPi
  have atMappedDomain : assemble heads constants
      (functionFormation.mapConversion includeNoConversion) functionType
      (.head familyLevel) = some domainMeaning := by
    rw [assemble_mapConversion]
    exact atDomain
  rw [atMappedDomain] at atRetained
  cases Option.some.inj atRetained
  have atMappedArgument : assemble heads constants
      (computedFunctionCode.mapConversion includeNoConversion)
      computedFunction functionType = some argument := by
    rw [assemble_mapConversion]
    exact atArgument
  obtain ⟨checked, atProof, family, atFamily, typed⟩ :=
    betaIdentityLeftProof_in_formed_fibre Tower.rules emptyDecoder heads constants
      .nil (fun _ => True) functionType computedFunction familyLevel packageLevel
      (functionFormation.mapConversion includeNoConversion) identityPiFormation
      (computedFunctionCode.mapConversion includeNoConversion) formed argument
      domainMeaning.value atPi retainedDomain atMappedArgument
      (fun env _ => member env) (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  refine ⟨Meaning.plain (fun _ => (∅ : ZFSet.{u})), family, ?_, ?_, ?_⟩
  · simpa only [proofCode, targetFormation_eq_generic, heads, computed_family_instance] using atProof
  · simpa only [targetFormation_eq_generic, heads, computed_family_instance] using atFamily
  · intro env
    exact typed env True.intro

/-- Two distinct accepted retained Π-certificates give checked converted
proofs in the same beta-expanded identity fibre on valid environments. The
general comparison does not require equal intermediate domains or equal
argument values; this concrete instance exercises cumulative replay. -/
theorem cumulative_certificate_fibres_agree
    (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u}) (valuation : Nat → Nat)
    (groundTyped : ground ∈ universeSet h seed 0)
    (constants : DeclName → ZFSet.{u}) :
    identityPiFormation ≠ wrappedIdentityPiFormation ∧
    check Tower.rules conversionCheck .nil (.refl computedFunction)
      (inst0 computedFunction mixedFamily) proofCode = true ∧
    check Tower.rules conversionCheck .nil (.refl computedFunction)
      (inst0 computedFunction mixedFamily) wrappedProofCode = true ∧
    ∃ firstProof secondProof firstFamily secondFamily,
      assemble (interpretHead h seed ground valuation) constants proofCode
        (.refl computedFunction) (inst0 computedFunction mixedFamily) = some firstProof ∧
      assemble (interpretHead h seed ground valuation) constants wrappedProofCode
        (.refl computedFunction) (inst0 computedFunction mixedFamily) = some secondProof ∧
      assemble (interpretHead h seed ground valuation) constants targetFormation
        (inst0 computedFunction mixedFamily) (.head familyLevel) = some firstFamily ∧
      assemble (interpretHead h seed ground valuation) constants wrappedTargetFormation
        (inst0 computedFunction mixedFamily) (.head familyLevel) = some secondFamily ∧
      ∀ env, firstProof.value env = secondProof.value env ∧
        firstProof.value env ∈ firstFamily.value env ∧
        secondProof.value env ∈ secondFamily.value env ∧
        firstFamily.value env = secondFamily.value env := by
  let heads := interpretHead h seed ground valuation
  obtain ⟨argument, domainMeaning, atArgument, atDomain, member⟩ :=
    computed_argument_in_function_domain h seed ground valuation groundTyped constants
  have piChecked : check Tower.rules conversionCheck .nil
      (.pi functionType (rename wk functionType)) (.head packageLevel)
      identityPiFormation = true := by decide +kernel
  obtain ⟨formed, atPi, _⟩ := accepted_assembles heads constants Tower.rules
    conversionCheck identityPiFormation piChecked
  obtain ⟨retained, _, atRetained, _, _, retainedDomain⟩ :=
    assemble_piFormation heads constants identityPiFormation rfl atPi
  have atMappedDomain : assemble heads constants
      (functionFormation.mapConversion includeNoConversion) functionType
      (.head familyLevel) = some domainMeaning := by
    rw [assemble_mapConversion]
    exact atDomain
  rw [atMappedDomain] at atRetained
  cases Option.some.inj atRetained
  have atMappedArgument : assemble heads constants
      (computedFunctionCode.mapConversion includeNoConversion)
      computedFunction functionType = some argument := by
    rw [assemble_mapConversion]
    exact atArgument
  have atWrappedPi : assemble heads constants wrappedIdentityPiFormation
      (.pi functionType (rename wk functionType)) (.head packageLevel) = some formed := by
    exact atPi
  have distinct : identityPiFormation ≠ wrappedIdentityPiFormation := by
    intro equal
    cases equal
  obtain ⟨leftChecked, rightChecked, firstProof, secondProof, firstFamily, secondFamily,
    atFirstProof, atSecondProof, atFirstFamily, atSecondFamily, comparison⟩ :=
    betaIdentityLeft_independent_fibres Tower.rules emptyDecoder heads constants
      .nil (fun _ => True) functionType computedFunction
      familyLevel familyLevel packageLevel packageLevel
      (functionFormation.mapConversion includeNoConversion) identityPiFormation
      (computedFunctionCode.mapConversion includeNoConversion)
      (functionFormation.mapConversion includeNoConversion) wrappedIdentityPiFormation
      (computedFunctionCode.mapConversion includeNoConversion)
      formed formed argument argument domainMeaning.value domainMeaning.value
      atPi atWrappedPi retainedDomain retainedDomain atMappedArgument atMappedArgument
      (fun env _ => member env) (fun env _ => member env)
      (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  refine ⟨distinct, ?_, ?_, firstProof, secondProof, firstFamily, secondFamily,
    ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [proofCode, targetFormation_eq_generic, computed_family_instance] using leftChecked
  · simpa only [wrappedProofCode, wrappedTargetFormation, computed_family_instance, heads] using rightChecked
  · simpa only [proofCode, targetFormation_eq_generic, computed_family_instance] using atFirstProof
  · simpa only [wrappedProofCode, wrappedTargetFormation, computed_family_instance, heads] using atSecondProof
  · simpa only [targetFormation_eq_generic, computed_family_instance] using atFirstFamily
  · simpa only [wrappedTargetFormation, computed_family_instance, heads] using atSecondFamily
  · intro env
    exact comparison env True.intro

/-- The second retained proof is used by the same dependent second-projection
program. Its result agrees with the original consumer, not merely with an
unused proof certificate. -/
theorem cumulative_certificate_dependent_consumers_agree
    (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u}) (valuation : Nat → Nat)
    (groundTyped : ground ∈ universeSet h seed 0)
    (constants : DeclName → ZFSet.{u}) :
    ∃ first second,
      assemble (interpretHead h seed ground valuation) constants dependentConsumerCode
        (.snd package) (inst0 (.fst package) mixedFamily) = some first ∧
      assemble (interpretHead h seed ground valuation) constants wrappedDependentConsumerCode
        (.snd package) (inst0 (.fst package) mixedFamily) = some second ∧
      ∀ env, first.value env = second.value env := by
  let heads := interpretHead h seed ground valuation
  obtain ⟨_, _, _, firstProof, secondProof, _, _, atFirstProof, atSecondProof,
    _, _, comparison⟩ :=
    cumulative_certificate_fibres_agree h seed ground valuation groundTyped constants
  obtain ⟨argument, atArgument, _⟩ := accepted_assembles heads constants Tower.rules
    noConversionCheck computedFunctionCode functions_checked.2.1
  have atMappedArgument : assemble heads constants
      (computedFunctionCode.mapConversion includeNoConversion)
      computedFunction functionType = some argument := by
    rw [assemble_mapConversion]
    exact atArgument
  have related := checked_second_projections_related heads constants Tower.rules
    conversionCheck .nil packageLevel packageLevel functionType computedFunction
    (.refl computedFunction) mixedFamily packageFormation packageFormation
    (computedFunctionCode.mapConversion includeNoConversion)
    (computedFunctionCode.mapConversion includeNoConversion) proofCode wrappedProofCode
    argument argument firstProof secondProof atMappedArgument atMappedArgument
    atFirstProof atSecondProof dependent_consumer_checked
    wrapped_package_and_consumer_check.2 (fun _ => True) Eq
    (fun env _ => (comparison env).1)
  obtain ⟨first, second, atFirst, atSecond, values⟩ := related
  exact ⟨first, second, atFirst, atSecond, fun env => values env True.intro⟩

/-- The dependent consumer's *projected* fibre is inhabited. The first
projection has the computed argument's value, and the retained identity
lambda acts on that value because the argument's typing certificate supplies
domain membership. This closes the semantic typing square at the actual
displayed type of the second projection. -/
theorem dependent_consumer_fibre
    (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u}) (valuation : Nat → Nat)
    (groundTyped : ground ∈ universeSet h seed 0)
    (constants : DeclName → ZFSet.{u}) :
    ∃ result family,
      assemble (interpretHead h seed ground valuation) constants dependentConsumerCode
        (.snd package) (inst0 (.fst package) mixedFamily) = some result ∧
      assemble (interpretHead h seed ground valuation) constants consumerFamilyCode
        (inst0 (.fst package) mixedFamily) (.head familyLevel) = some family ∧
      ∀ env, result.value env ∈ family.value env := by
  let heads := interpretHead h seed ground valuation
  obtain ⟨argument, domain, atArgument, atDomain, argumentMember⟩ :=
    computed_argument_in_function_domain h seed ground valuation groundTyped constants
  have atMappedArgument : assemble heads constants
      (computedFunctionCode.mapConversion includeNoConversion)
      computedFunction functionType = some argument := by
    rw [assemble_mapConversion]
    exact atArgument
  have atProof : assemble heads constants proofCode (.refl computedFunction)
      (inst0 computedFunction mixedFamily) =
      some (Meaning.plain (fun _ => (∅ : ZFSet.{u}))) := by rfl
  have firstChecked : check Tower.rules conversionCheck .nil (.fst package)
      functionType firstProjectionCode = true := by decide +kernel
  obtain ⟨first, atFirst, _⟩ := accepted_assembles heads constants Tower.rules
    conversionCheck firstProjectionCode firstChecked
  have firstValue (env) : first.value env = argument.value env :=
    first_pair_value heads constants packageLevel functionType computedFunction
      (.refl computedFunction) mixedFamily packageFormation
      (computedFunctionCode.mapConversion includeNoConversion) proofCode
      argument (Meaning.plain (fun _ => (∅ : ZFSet.{u}))) first
      atMappedArgument atProof atFirst env
  let functionMeaning : Meaning.{u} 0 :=
    Meaning.plain (fun env => traceLam (graph (domain.value env) (fun x => x)))
  have atFunction : assemble heads constants
      (consumerCode.mapConversion includeNoConversion) identity
      (.pi functionType functionType) = some functionMeaning :=
    consumer_function_graph heads constants domain atDomain
  let endpoint : Meaning.{u} 0 :=
    Meaning.plain (fun env => traceApp (functionMeaning.value env) (first.value env))
  have atEndpoint : assemble heads constants consumerEndpointCode
      (.app identity (.fst package)) functionType = some endpoint := by
    simp [consumerEndpointCode, endpoint, assemble, atFunction, atFirst]
  let family : Meaning.{u} 0 :=
    Meaning.plain (fun env =>
      ZFSetTraceProofDecoding.truthCode (endpoint.value env = first.value env))
  have atFamily : assemble heads constants consumerFamilyCode
      (inst0 (.fst package) mixedFamily) (.head familyLevel) = some family := by
    change (do
      let x' ← assemble heads constants consumerEndpointCode
        (.app identity (.fst package)) functionType
      let y' ← assemble heads constants firstProjectionCode (.fst package) functionType
      some (Meaning.plain (fun env =>
        ZFSetTraceProofDecoding.truthCode (x'.value env = y'.value env)))) = some family
    rw [atEndpoint, atFirst]
    rfl
  obtain ⟨result, atResult, resultValue⟩ :=
    dependent_consumer_value h seed ground valuation constants
  refine ⟨result, family, atResult, atFamily, ?_⟩
  intro env
  rw [resultValue env]
  change (∅ : ZFSet.{u}) ∈
    ZFSetTraceProofDecoding.truthCode (endpoint.value env = first.value env)
  apply (ZFSetTraceProofDecoding.mem_truthCode _ _).mpr
  refine ⟨rfl, ?_⟩
  change traceApp (traceLam (graph (domain.value env) (fun x => x)))
    (first.value env) = first.value env
  rw [firstValue env]
  exact traceApp_graph_beta (fun x => x) (argumentMember env)

#print axioms checked
#print axioms targetFormation_eq_generic
#print axioms malformed_conversion_rejected
#print axioms typing
#print axioms package_checked
#print axioms dependent_consumer_checked
#print axioms consumer_family_checked
#print axioms dependent_consumer_typed
#print axioms dependent_consumer_value
#print axioms proof_in_computed_family
#print axioms cumulative_certificate_fibres_agree
#print axioms cumulative_certificate_dependent_consumers_agree
#print axioms dependent_consumer_fibre

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayCheckedMixedIdentityProof
