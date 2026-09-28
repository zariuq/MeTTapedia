import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetReplayQualifiedTypingControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplayComputedFamilyComparison

/-!
# A computed higher-order argument in a dependent family

One independently certified function is computed by an application whose
unused parameter is a universe-valued computation. The other function is an
explicit lambda. Instantiating an identity family at these two different raw
expressions yields different raw types, but checked formation certificates
with equal set meanings. The two family certificates also use different
cumulative universe levels.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayComputedFamilyControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open StructuralTypingReplay
open ZFSetReplayInterpretation
open ZFSetTypeExpressionInterpretation (Environment)
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure (CofinalInaccessibles)
open ZFSetInterpretation
open ZFSetTraceUniverseInterpretation (interpretHead)
open ZFSetReplayQualifiedTypingControls
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayUniverseModel

private abbrev u1 : Tower.Head := .sort (.succ Tower.zero)
private abbrev u2 : Tower.Head := .sort (.succ (.succ Tower.zero))
private abbrev functionLevel : Tower.Head := .sort (.max (.succ Tower.zero) (.succ Tower.zero))

def identityFamily : Tower.Tm 1 := .id functionType (.var 0) identity
def lowerFamily : Code Tower.Head NoConversion 1 :=
  .idForm functionLevel functionFormation .var identityCode
def upperFamily : Code Tower.Head NoConversion 1 := .cumul functionLevel lowerFamily

theorem family_checked :
    check Tower.rules noConversionCheck (.snoc .nil functionType) identityFamily
      (.head functionLevel) lowerFamily = true ∧
    check Tower.rules noConversionCheck (.snoc .nil functionType) identityFamily
      (.head u2) upperFamily = true ∧
    lowerFamily.neutralEliminations identityFamily (.head functionLevel) = true := by
  decide +kernel

theorem source_contracts_to_identity :
    lowerIndependentCode.contractBeta identity computedType functionType = some identityCode := by
  rfl

universe u

/-- The source and the normal lambda agree because the checked source
contracts to that very lambda certificate. -/
theorem computed_equals_normal
    (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u}) (valuation : Nat → Nat)
    (groundTyped : ground ∈ universeSet h seed 0) (constants : DeclName → ZFSet.{u}) :
    ∃ computed normal,
      assemble (interpretHead h seed ground valuation) constants lowerIndependentCode
        independentFunction functionType = some computed ∧
      assemble (interpretHead h seed ground valuation) constants identityCode
        identity functionType = some normal ∧
      ∀ env : Environment.{u} 0, computed.value env = normal.value env := by
  obtain ⟨computed, atComputed, _⟩ := accepted_assembles
    (interpretHead h seed ground valuation) constants Tower.rules noConversionCheck
    lowerIndependentCode independent_functions_checked_and_qualified.1
  obtain ⟨normal, atNormal, _⟩ := accepted_assembles
    (interpretHead h seed ground valuation) constants Tower.rules noConversionCheck
    identityCode functions_checked.1
  obtain ⟨resultCode, result, contraction, _, atResult, equal⟩ :=
    qualified_contractBeta (interpretHead h seed ground valuation) constants Tower.rules
      TowerDecisions.headTarget FormationSensitive.towerUniverseRegularity successor_qualified
      (ZFSetReplayUniverseModel.universeModel h seed ground valuation groundTyped)
      (empty_constants_model _ constants) .nil lowerIndependentCode computed
      (valid := fun _ => True) rfl independent_functions_checked_and_qualified.1
      independent_functions_checked_and_qualified.2.2.1 rfl atComputed
  rw [source_contracts_to_identity] at contraction
  cases Option.some.inj contraction
  change assemble _ constants identityCode identity functionType = some result at atResult
  rw [atNormal] at atResult
  cases Option.some.inj atResult
  exact ⟨computed, normal, atComputed, atNormal, fun env => equal env True.intro⟩

/-- A genuine dependent family distinguishes the two raw argument expressions.
Semantic equality below therefore cannot be syntactic certificate identity. -/
theorem family_instances_differ :
    inst0 independentFunction identityFamily ≠ inst0 identity identityFamily := by
  decide +kernel

/-- Both generated family formations check, and their interpretations agree
on the valid empty context. The original family is qualified; its computed
instance is not required to be. -/
theorem computed_family_values
    (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u}) (valuation : Nat → Nat)
    (groundTyped : ground ∈ universeSet h seed 0) (constants : DeclName → ZFSet.{u}) :
    let leftFormation := Code.instantiate noConversionRename noConversionSubstitute
      identityFamily (.head functionLevel) independentFunction lowerFamily lowerIndependentCode
    let rightFormation := Code.instantiate noConversionRename noConversionSubstitute
      identityFamily (.head u2) identity upperFamily identityCode
    check Tower.rules noConversionCheck .nil (inst0 independentFunction identityFamily)
      (.head functionLevel) leftFormation = true ∧
    check Tower.rules noConversionCheck .nil (inst0 identity identityFamily)
      (.head u2) rightFormation = true ∧
    ∃ left right,
      assemble (interpretHead h seed ground valuation) constants leftFormation
        (inst0 independentFunction identityFamily) (.head functionLevel) = some left ∧
      assemble (interpretHead h seed ground valuation) constants rightFormation
        (inst0 identity identityFamily) (.head u2) = some right ∧
      ∀ env : Environment.{u} 0, left.value env = right.value env := by
  obtain ⟨computed, normal, atComputed, atNormal, equal⟩ :=
    computed_equals_normal h seed ground valuation groundTyped constants
  simpa only [true_imp_iff] using
    (computed_arguments_family_values (interpretHead h seed ground valuation) constants
    Tower.rules lowerIndependentCode identityCode computed normal
    independent_functions_checked_and_qualified.1 functions_checked.1 atComputed atNormal
    (valid := fun _ => True) (fun env _ => equal env)
    identityFamily functionLevel u2 lowerFamily upperFamily family_checked.1
    family_checked.2.1 family_checked.2.2)

/-- Distinct accepted certificates for the same computed source, with
different hidden universe domains, also remain comparable after insertion
into independently formed family certificates. -/
theorem independent_source_family_values
    (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u}) (valuation : Nat → Nat)
    (groundTyped : ground ∈ universeSet h seed 0) (constants : DeclName → ZFSet.{u}) :
    let leftFormation := Code.instantiate noConversionRename noConversionSubstitute
      identityFamily (.head functionLevel) independentFunction lowerFamily lowerIndependentCode
    let rightFormation := Code.instantiate noConversionRename noConversionSubstitute
      identityFamily (.head u2) independentFunction upperFamily upperIndependentCode
    check Tower.rules noConversionCheck .nil (inst0 independentFunction identityFamily)
      (.head functionLevel) leftFormation = true ∧
    check Tower.rules noConversionCheck .nil (inst0 independentFunction identityFamily)
      (.head u2) rightFormation = true ∧
    ∃ left right,
      assemble (interpretHead h seed ground valuation) constants leftFormation
        (inst0 independentFunction identityFamily) (.head functionLevel) = some left ∧
      assemble (interpretHead h seed ground valuation) constants rightFormation
        (inst0 independentFunction identityFamily) (.head u2) = some right ∧
      ∀ env : Environment.{u} 0, left.value env = right.value env := by
  obtain ⟨left, atLeft, _⟩ := accepted_assembles
    (interpretHead h seed ground valuation) constants Tower.rules noConversionCheck
    lowerIndependentCode independent_functions_checked_and_qualified.1
  obtain ⟨right, atRight, _⟩ := accepted_assembles
    (interpretHead h seed ground valuation) constants Tower.rules noConversionCheck
    upperIndependentCode independent_functions_checked_and_qualified.2.1
  obtain ⟨normal, atNormal, _⟩ := accepted_assembles
    (interpretHead h seed ground valuation) constants Tower.rules noConversionCheck
    identityCode functions_checked.1
  simpa only [true_imp_iff, independentFunction] using
    (qualified_rootBeta_family_values (interpretHead h seed ground valuation) constants
      Tower.rules TowerDecisions.headTarget FormationSensitive.towerUniverseRegularity
      successor_qualified (ZFSetReplayUniverseModel.universeModel h seed ground valuation groundTyped)
      (empty_constants_model _ constants) .nil lowerIndependentCode upperIndependentCode
      identityCode left right normal (valid := fun _ => True) rfl
      independent_functions_checked_and_qualified.1
      independent_functions_checked_and_qualified.2.1
      independent_functions_checked_and_qualified.2.2.1
      independent_functions_checked_and_qualified.2.2.2
      rfl atLeft atRight functions_checked.1 (by decide +kernel) atNormal
      identityFamily functionLevel u2 lowerFamily upperFamily
      family_checked.1 family_checked.2.1 family_checked.2.2)

/-- The syntactically different dependent last types define the same set of
admissible extensions of the empty context. -/
theorem computed_family_contexts
    (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u}) (valuation : Nat → Nat)
    (groundTyped : ground ∈ universeSet h seed 0) (constants : DeclName → ZFSet.{u}) :
    let leftFormation := Code.instantiate noConversionRename noConversionSubstitute
      identityFamily (.head functionLevel) independentFunction lowerFamily lowerIndependentCode
    let rightFormation := Code.instantiate noConversionRename noConversionSubstitute
      identityFamily (.head u2) identity upperFamily identityCode
    checkContext Tower.rules noConversionCheck (.snoc .nil (inst0 independentFunction identityFamily))
      (.snoc .nil functionLevel leftFormation) = true ∧
    checkContext Tower.rules noConversionCheck (.snoc .nil (inst0 identity identityFamily))
      (.snoc .nil u2 rightFormation) = true ∧
    ∃ leftValid rightValid,
      assembleContext (interpretHead h seed ground valuation) constants
        (.snoc .nil functionLevel leftFormation)
        (.snoc .nil (inst0 independentFunction identityFamily)) = some leftValid ∧
      assembleContext (interpretHead h seed ground valuation) constants
        (.snoc .nil u2 rightFormation)
        (.snoc .nil (inst0 identity identityFamily)) = some rightValid ∧
      leftValid = rightValid := by
  obtain ⟨computed, normal, atComputed, atNormal, equal⟩ :=
    computed_equals_normal h seed ground valuation groundTyped constants
  exact computed_arguments_family_contexts (interpretHead h seed ground valuation) constants
    Tower.rules .nil lowerIndependentCode identityCode computed normal
    (valid := fun _ => True) rfl rfl
    independent_functions_checked_and_qualified.1 functions_checked.1 atComputed atNormal
    (fun env _ => equal env) identityFamily functionLevel u2
    (by decide +kernel) (by decide +kernel)
    lowerFamily upperFamily family_checked.1 family_checked.2.1 family_checked.2.2

/-- The compared fibre is inhabited, not merely equal to an empty fibre.
The normal-side witness is the empty-set proof code for reflexive equality;
the computed side receives it through the proved family comparison. -/
theorem computed_family_inhabited
    (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u}) (valuation : Nat → Nat)
    (groundTyped : ground ∈ universeSet h seed 0) (constants : DeclName → ZFSet.{u}) :
    ∃ left right,
      assemble (interpretHead h seed ground valuation) constants
        (Code.instantiate noConversionRename noConversionSubstitute
          identityFamily (.head functionLevel) independentFunction lowerFamily lowerIndependentCode)
        (inst0 independentFunction identityFamily) (.head functionLevel) = some left ∧
      assemble (interpretHead h seed ground valuation) constants
        (Code.instantiate noConversionRename noConversionSubstitute
          identityFamily (.head u2) identity upperFamily identityCode)
        (inst0 identity identityFamily) (.head u2) = some right ∧
      ∀ env : Environment.{u} 0, ∅ ∈ left.value env ∧ ∅ ∈ right.value env := by
  obtain ⟨_, _, left, right, atLeft, atRight, equal⟩ :=
    computed_family_values h seed ground valuation groundTyped constants
  refine ⟨left, right, atLeft, atRight, ?_⟩
  intro env
  have rightMember : ∅ ∈ right.value env := by
    simp [Code.instantiate, Code.substitute, upperFamily, lowerFamily,
      identityFamily, functionType, identity, identityCode, assemble] at atRight
    cases Option.some.inj atRight
    exact (ZFSetTraceProofDecoding.mem_truthCode _ ∅).mpr ⟨rfl, rfl⟩
  exact ⟨(equal env).symm ▸ rightMember, rightMember⟩

/-- Two genuinely different accepted source certificates yield checked
dependent telescopes with the same nonempty environment space. The witness
uses the identity proof in the computed function's dependent fibre. -/
theorem independent_source_contexts_inhabited
    (h : CofinalInaccessibles.{u}) (seed ground : ZFSet.{u}) (valuation : Nat → Nat)
    (groundTyped : ground ∈ universeSet h seed 0) (constants : DeclName → ZFSet.{u}) :
    let leftFormation := Code.instantiate noConversionRename noConversionSubstitute
      identityFamily (.head functionLevel) independentFunction lowerFamily lowerIndependentCode
    let rightFormation := Code.instantiate noConversionRename noConversionSubstitute
      identityFamily (.head u2) independentFunction upperFamily upperIndependentCode
    checkContext Tower.rules noConversionCheck (.snoc .nil (inst0 independentFunction identityFamily))
      (.snoc .nil functionLevel leftFormation) = true ∧
    checkContext Tower.rules noConversionCheck (.snoc .nil (inst0 independentFunction identityFamily))
      (.snoc .nil u2 rightFormation) = true ∧
    ∃ leftValid rightValid : Environment.{u} 1 → Prop,
      assembleContext (interpretHead h seed ground valuation) constants
        (.snoc .nil functionLevel leftFormation)
        (.snoc .nil (inst0 independentFunction identityFamily)) = some leftValid ∧
      assembleContext (interpretHead h seed ground valuation) constants
        (.snoc .nil u2 rightFormation)
        (.snoc .nil (inst0 independentFunction identityFamily)) = some rightValid ∧
      leftValid = rightValid ∧
      ∃ env : Environment.{u} 1, leftValid env ∧ rightValid env := by
  obtain ⟨left, atLeft, _⟩ := accepted_assembles
    (interpretHead h seed ground valuation) constants Tower.rules noConversionCheck
    lowerIndependentCode independent_functions_checked_and_qualified.1
  obtain ⟨right, atRight, _⟩ := accepted_assembles
    (interpretHead h seed ground valuation) constants Tower.rules noConversionCheck
    upperIndependentCode independent_functions_checked_and_qualified.2.1
  obtain ⟨normal, atNormal, _⟩ := accepted_assembles
    (interpretHead h seed ground valuation) constants Tower.rules noConversionCheck
    identityCode functions_checked.1
  obtain ⟨leftChecked, rightChecked, leftValid, rightValid,
      atLeftContext, atRightContext, sameValid⟩ := by
    simpa only [independentFunction] using
      (qualified_rootBeta_family_contexts (interpretHead h seed ground valuation) constants
        Tower.rules TowerDecisions.headTarget FormationSensitive.towerUniverseRegularity
        successor_qualified
        (ZFSetReplayUniverseModel.universeModel h seed ground valuation groundTyped)
        (empty_constants_model _ constants) .nil lowerIndependentCode upperIndependentCode
        identityCode left right normal (valid := fun _ => True) rfl
        independent_functions_checked_and_qualified.1
        independent_functions_checked_and_qualified.2.1
        independent_functions_checked_and_qualified.2.2.1
        independent_functions_checked_and_qualified.2.2.2
        rfl atLeft atRight functions_checked.1 (by decide +kernel) atNormal
        identityFamily functionLevel u2 (by decide +kernel) (by decide +kernel)
        lowerFamily upperFamily family_checked.1 family_checked.2.1 family_checked.2.2)
  obtain ⟨leftType, _, atLeftType, _, inhabited⟩ :=
    computed_family_inhabited h seed ground valuation groundTyped constants
  refine ⟨leftChecked, rightChecked, leftValid, rightValid,
    atLeftContext, atRightContext, sameValid, ?_⟩
  let emptyEnv : Environment.{u} 0 := fun index => Fin.elim0 index
  refine ⟨ZFSetTypeExpressionInterpretation.extend emptyEnv (∅ : ZFSet.{u}), ?_, ?_⟩
  · exact (context_extension_valid_iff (interpretHead h seed ground valuation) constants
      .nil (inst0 independentFunction identityFamily) .nil functionLevel _
      (fun _ => True) leftValid leftType rfl atLeftType atLeftContext emptyEnv ∅).mpr
        ⟨True.intro, (inhabited emptyEnv).1⟩
  · rw [← sameValid]
    exact (context_extension_valid_iff (interpretHead h seed ground valuation) constants
      .nil (inst0 independentFunction identityFamily) .nil functionLevel _
      (fun _ => True) leftValid leftType rfl atLeftType atLeftContext emptyEnv ∅).mpr
        ⟨True.intro, (inhabited emptyEnv).1⟩

#print axioms computed_equals_normal
#print axioms family_instances_differ
#print axioms computed_family_values
#print axioms independent_source_family_values
#print axioms computed_family_contexts
#print axioms computed_family_inhabited
#print axioms independent_source_contexts_inhabited

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetReplayComputedFamilyControls
