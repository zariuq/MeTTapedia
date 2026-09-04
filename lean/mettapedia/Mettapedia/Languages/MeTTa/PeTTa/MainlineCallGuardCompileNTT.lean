import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
import Mettapedia.OSLF.Framework.SelectedNativeTypeCalculusCompiler
import Mettapedia.GSLT.LanguageDef.WellSortedChecker

/-!
# Generated native-type calculus for the PeTTa call-guard compiler

The cold call-guard compiler is already an ordinary authored `LanguageDef`.
This module supplies the independent typing evidence required by the shared
selected-native-type compiler and applies that compiler to every authored
rewrite root.

Every root has an empty fixed context, hence exactly one local modal slot.  We
select both vertices of that one-dimensional fibre, in authored rewrite order:
`star` followed by `box`.  The resulting calculus is therefore mechanically
generated from the cold source language and its explicit finite native-type
demand.  It is not a handwritten PeTTa typing calculus and it is not the
semantic `gsltOSLF` interpretation.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileNTT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.OSLF.Framework
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational

set_option autoImplicit false

/-- The validated cold source consumed by the shared OSLF construction. -/
def coldSource : ValidatedLanguageDef :=
  ⟨language, language_validate⟩

/-- Exact sorting evidence for one authored root transition.  All fifteen
rewrites transform `CGCompileControl` states; the executable checker is used
only to reconstruct derivations in the independently defined `HasType`
relation. -/
def rootTyping (index : Fin coldSource.language.rewrites.length) :
    DisplayedRewriteTyping coldSource where
  site := DisplayedRewriteSite.root coldSource.language index
  rewriteType := .base "CGCompileControl"
  focusBoundPrefix := []
  focusType := .base "CGCompileControl"
  rewriteLeftTyped := by
    apply checkHasType_sound
    fin_cases index <;> decide +kernel
  rewriteRightTyped := by
    apply checkHasType_sound
    fin_cases index <;> decide +kernel
  sourceIsObject := by
    fin_cases index <;> decide +kernel
  focusTyped := by
    apply checkHasType_sound
    fin_cases index <;> decide +kernel

/-- Root typing requests mention only the authored `CGCompileControl`
carrier.  No foreign carrier can enter the generated foundation. -/
theorem rootTyping_grounded
    (index : Fin coldSource.language.rewrites.length) :
    SelectedNativeTypeFoundation.CarrierGrounded (rootTyping index) := by
  intro object objectMembership name nameMembership
  simp [SelectedNativeTypeFoundation.requiredCarrierRoots,
    rootTyping, DisplayedContextProfile.carrierTypes,
    DisplayedContextProfile.bindings, DisplayedContextProfile.variableNames,
    DisplayedContextProfile.externalFreeFvarNames,
    DisplayedRewriteSite.root] at objectMembership
  rcases objectMembership with rfl | rfl
  all_goals
    simp [TypeExpr.baseNames] at nameMembership
    subst name
    decide

/-- One explicitly profiled root occurrence. -/
def profiledRoot (index : Fin coldSource.language.rewrites.length)
    (code : CarrierUniverseSignature.Code) :
    ProfiledRewriteOccurrence coldSource :=
  ProfiledRewriteOccurrence.constant
    (rootTyping index) (rootTyping_grounded index) code

/-- Complete authored-order selection: both vertices for every root. -/
def selectedOccurrences :
    List (ProfiledRewriteOccurrence coldSource) :=
  (List.finRange coldSource.language.rewrites.length).flatMap fun index =>
    [profiledRoot index .star, profiledRoot index .box]

/-- Full finite native-type demand for the cold compiler. -/
def demand : SelectedNativeTypeDemand coldSource :=
  ⟨selectedOccurrences⟩

/-- A deliberately partial endpoint selection used only as a negative
control. -/
def allStarOccurrences :
    List (ProfiledRewriteOccurrence coldSource) :=
  (List.finRange coldSource.language.rewrites.length).map fun index =>
    profiledRoot index .star

/-- The deliberately partial all-star demand. -/
def allStarDemand : SelectedNativeTypeDemand coldSource :=
  ⟨allStarOccurrences⟩

/-- Generated control artifact for the deliberately partial profile. -/
def allStarGeneratedCalculus : CalculusLanguageDef :=
  SelectedNativeTypeCalculusCompiler.definition allStarDemand

/-- The complete selection retains two profile occurrences for every one of
the fifteen authored transition occurrences. -/
theorem selectedOccurrences_count : selectedOccurrences.length = 30 := by
  decide

/-- The partial endpoint control retains only one profile occurrence per
authored transition. -/
theorem allStarOccurrences_count : allStarOccurrences.length = 15 := by
  decide

/-- Selecting only one endpoint cannot masquerade as the complete local
hypercube demand. -/
theorem demand_ne_allStarDemand : demand ≠ allStarDemand := by
  intro equality
  have lengths := congrArg
    (fun selected => selected.occurrences.length) equality
  change 30 = 15 at lengths
  omega

/-- The shared profile-sensitive compiler's concrete output for the complete
cold call-guard demand. -/
def generatedCalculus : CalculusLanguageDef :=
  SelectedNativeTypeCalculusCompiler.definition demand

/-- Small validation batches keep the executable admission check aligned with
the generator's ordinary rule list without asking the kernel to normalize all
ninety-two rows in one expression. -/
private def ruleBatch (offset : Nat) : List RuleSchema :=
  (generatedCalculus.rules.drop offset).take 8

private theorem ruleBatch0_valid :
    (ruleBatch 0).all (RuleSchema.isValidIn generatedCalculus) = true := by
  decide +kernel

private theorem ruleBatch1_valid :
    (ruleBatch 8).all (RuleSchema.isValidIn generatedCalculus) = true := by
  decide +kernel

private theorem ruleBatch2_valid :
    (ruleBatch 16).all (RuleSchema.isValidIn generatedCalculus) = true := by
  decide +kernel

private theorem ruleBatch3_valid :
    (ruleBatch 24).all (RuleSchema.isValidIn generatedCalculus) = true := by
  decide +kernel

private theorem ruleBatch4_valid :
    (ruleBatch 32).all (RuleSchema.isValidIn generatedCalculus) = true := by
  decide +kernel

private theorem ruleBatch5_valid :
    (ruleBatch 40).all (RuleSchema.isValidIn generatedCalculus) = true := by
  decide +kernel

private theorem ruleBatch6_valid :
    (ruleBatch 48).all (RuleSchema.isValidIn generatedCalculus) = true := by
  decide +kernel

private theorem ruleBatch7_valid :
    (ruleBatch 56).all (RuleSchema.isValidIn generatedCalculus) = true := by
  decide +kernel

private theorem ruleBatch8_valid :
    (ruleBatch 64).all (RuleSchema.isValidIn generatedCalculus) = true := by
  decide +kernel

private theorem ruleBatch9_valid :
    (ruleBatch 72).all (RuleSchema.isValidIn generatedCalculus) = true := by
  decide +kernel

private theorem ruleBatch10_valid :
    (ruleBatch 80).all (RuleSchema.isValidIn generatedCalculus) = true := by
  decide +kernel

private theorem ruleBatch11_valid :
    (ruleBatch 88).all (RuleSchema.isValidIn generatedCalculus) = true := by
  decide +kernel

private theorem generatedRules_eq_batches :
    generatedCalculus.rules =
      ruleBatch 0 ++ ruleBatch 8 ++ ruleBatch 16 ++ ruleBatch 24 ++
      ruleBatch 32 ++ ruleBatch 40 ++ ruleBatch 48 ++ ruleBatch 56 ++
      ruleBatch 64 ++ ruleBatch 72 ++ ruleBatch 80 ++ ruleBatch 88 := by
  decide +kernel

/-- Every emitted inference row is admitted against the complete generated
constructor and judgment signature. -/
theorem generatedRules_validIn :
    generatedCalculus.rules.all
      (RuleSchema.isValidIn generatedCalculus) = true := by
  rw [generatedRules_eq_batches]
  simp only [List.all_append, ruleBatch0_valid, ruleBatch1_valid,
    ruleBatch2_valid, ruleBatch3_valid, ruleBatch4_valid, ruleBatch5_valid,
    ruleBatch6_valid, ruleBatch7_valid, ruleBatch8_valid, ruleBatch9_valid,
    ruleBatch10_valid, ruleBatch11_valid, Bool.and_self]

/-- V2 admission implies the local V1 schema boundary for every generated
rule; this is derived rather than rechecking the same rows. -/
theorem generatedRules_locallyValid :
    generatedCalculus.rules.all RuleSchema.isLocallyValid = true := by
  apply List.all_eq_true.mpr
  intro rule membership
  have valid := List.all_eq_true.mp generatedRules_validIn rule membership
  simp only [RuleSchema.isValidIn, Bool.and_eq_true] at valid
  exact valid.1

/-- The generated constructor-only language passes the structural validator. -/
theorem generatedLanguage_validate :
    generatedCalculus.toLanguageDef.validate = [] := by
  decide +kernel

/-- Generated rule identifiers remain occurrence-indexed and duplicate-free. -/
theorem generatedRuleIds_unique :
    ((generatedCalculus.ruleIds.eraseDups.length ==
      generatedCalculus.ruleIds.length) = true) := by
  rfl

/-- The generated judgment signature is finite, unambiguous, and disjoint
from its ordinary constructor namespace. -/
theorem generatedJudgmentSignature_valid :
    generatedCalculus.judgmentSignatureValid = true := by
  rfl

/-- The concrete generated calculus passes the complete ordinary admission
gate. -/
theorem generatedCalculus_valid : generatedCalculus.isValid = true := by
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [generatedLanguage_validate, generatedRules_locallyValid,
    generatedRuleIds_unique, generatedJudgmentSignature_valid,
    generatedRules_validIn]
  rfl

/-- The admitted generated artifact is an ordinary proof-carrying flat
calculus language. -/
def validatedGeneratedCalculus : ValidatedCalculusLanguageDef :=
  ⟨generatedCalculus, generatedCalculus_valid⟩

/-- Concrete generated inventory.  The thirty selected profile occurrences
produce ninety profile rules; the remaining four rules are the shared carrier
and canonical-context infrastructure. -/
theorem generatedCalculus_inventory :
    generatedCalculus.types.length = 3 ∧
      generatedCalculus.terms.length = 128 ∧
      generatedCalculus.judgments.length = 2 ∧
      generatedCalculus.rules.length = 94 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- All generated constructor labels inhabit the private generated-calculus
namespace.  This is the right-summand half of the capture-freedom proof used
when the generated calculus is attached to an authored source language. -/
theorem generatedConstructorLabels_private :
    ∀ name ∈
      Mettapedia.GSLT.LanguageDef.RewriteValidationCertificate.constructorLabels
        generatedCalculus.toLanguageDef,
      name.toList.head? = some '$' := by
  decide +kernel

/-- Empty selection produces no occurrence-local rules, whereas the complete
call-guard demand generates a nonempty proof calculus. -/
theorem generatedCalculus_nontrivial : generatedCalculus.rules ≠ [] := by
  intro empty
  have count := congrArg List.length empty
  change 94 = 0 at count
  omega

/-- Profile selection is operationally visible to syntax generation: the
partial control emits only forty-nine inference rows. -/
theorem allStarGeneratedCalculus_rule_count :
    allStarGeneratedCalculus.rules.length = 49 := by
  rfl

/-- Omitting every box endpoint cannot generate the complete calculus. -/
theorem allStarGeneratedCalculus_ne_generatedCalculus :
    allStarGeneratedCalculus ≠ generatedCalculus := by
  intro equality
  have counts := congrArg (fun calculus : CalculusLanguageDef =>
    calculus.rules.length) equality
  change 49 = 94 at counts
  omega

#print axioms rootTyping_grounded
#print axioms demand_ne_allStarDemand
#print axioms generatedCalculus_inventory
#print axioms generatedCalculus_nontrivial
#print axioms allStarGeneratedCalculus_ne_generatedCalculus
#print axioms generatedRules_validIn
#print axioms generatedCalculus_valid
#print axioms generatedConstructorLabels_private

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileNTT
