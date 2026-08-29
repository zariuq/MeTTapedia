import Mettapedia.GSLT.LanguageDef.ExtensionComposition
import Mettapedia.GSLT.LanguageDef.InferenceChecker

/-!
# Admission boundary for composed inference layers

Authored coGSLT layers compose independently of any checker.  This module
interprets that generic composition through `CalculusLanguageDef.isValid` and
proves that admission is not closed under unconstrained payload composition.
The separation keeps the algebraic operation foundational while making its
validation boundary explicit.
-/

namespace Mettapedia.GSLT.LanguageDef.ExtensionCompositionAdmission

open Mettapedia.GSLT.LanguageDef.ExtensionComposition
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceExtension
open Mettapedia.OSLF.MeTTaIL.Syntax

private theorem emptyLanguage_validate (name : String) :
    (LanguageDef.empty name).validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly <;>
    simp [LanguageDef.empty, LanguageDef.typeNames]

private def canaryLanguage : LanguageDef :=
  LanguageDef.empty "extension-composition-admission-canary"

private def canaryJudgment : JudgmentDecl := ⟨"Canary", 1⟩

private def canaryCalculus : ProofCalculus := { judgments := [canaryJudgment] }

private def mergedCalculus : ProofCalculus :=
  { judgments := [canaryJudgment, canaryJudgment] }

private def canaryDefinition (calculus : ProofCalculus) : CalculusLanguageDef :=
  CalculusLanguageDef.extend canaryLanguage calculus

private theorem canaryLanguage_validate : canaryLanguage.validate = [] :=
  emptyLanguage_validate "extension-composition-admission-canary"

private theorem canaryCalculus_valid :
    (canaryDefinition canaryCalculus).isValid = true := by
  have localRules :
      (canaryDefinition canaryCalculus).hasValidLocalRules = true := by
    simp [CalculusLanguageDef.hasValidLocalRules,
      CalculusLanguageDef.ruleIds, CalculusLanguageDef.extend,
      canaryDefinition, canaryCalculus,
      canaryLanguage_validate]
  unfold CalculusLanguageDef.isValid
  rw [localRules]
  decide

private theorem canaryCalculus_merge :
    proofCalculusMonoid.op canaryCalculus canaryCalculus = some mergedCalculus :=
  rfl

private theorem mergedCalculus_invalid :
    (canaryDefinition mergedCalculus).isValid = false := by
  have signature :
      (canaryDefinition mergedCalculus).judgmentSignatureValid = false := by
    decide
  simp [CalculusLanguageDef.isValid, signature]

/-- Two individually admitted inference layers can merge successfully as
authored data while their flat composite fails admission. -/
theorem admission_not_closed_under_composition :
    ∃ (language : LanguageDef) (first second merged : ProofCalculus),
      (CalculusLanguageDef.extend language first).isValid = true ∧
        (CalculusLanguageDef.extend language second).isValid = true ∧
        proofCalculusMonoid.op first second = some merged ∧
        (CalculusLanguageDef.extend language merged).isValid = false :=
  ⟨canaryLanguage, canaryCalculus, canaryCalculus, mergedCalculus,
    canaryCalculus_valid, canaryCalculus_valid, canaryCalculus_merge,
    mergedCalculus_invalid⟩

end Mettapedia.GSLT.LanguageDef.ExtensionCompositionAdmission
