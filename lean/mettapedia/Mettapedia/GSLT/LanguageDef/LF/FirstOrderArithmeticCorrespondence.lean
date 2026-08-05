import Mettapedia.GSLT.LanguageDef.LF.FirstOrderContextualCorrespondence

/-!
# Proof-producing arithmetic correspondence for first-order LF

The first-order LF presentation represents de Bruijn comparisons and index
shifts with explicit Peano proof trees.  This module compiles executable
natural-number order and addition into those raw trees and proves that the
actual source-neutral checker accepts them.

The compiler is source-independent data production: its output is checked
against the validated presentation rather than trusted by construction.
-/

namespace Mettapedia.GSLT.LanguageDef.LFFirstOrderArithmeticCorrespondence

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualConversion
open Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualCorrespondence
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CheckedSource
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Compile a natural-number comparison. Inputs not satisfying `<` produce a
deliberately invalid rule identifier; the acceptance theorem requires the
semantic inequality. -/
def ltRawProof : Nat → Nat → RawProof
  | 0, right + 1 =>
      rawProof "lf-fo-lt-zero-succ" [encodeNat right] []
  | left + 1, right + 1 =>
      rawProof "lf-fo-lt-succ-succ" [encodeNat left, encodeNat right]
        [ltRawProof left right]
  | _, _ => rawProof "lf-fo-invalid-lt" [] []

/-- Compile the unique Peano derivation of `left + right`. -/
def addRawProof : Nat → Nat → RawProof
  | 0, right =>
      rawProof "lf-fo-add-zero" [encodeNat right] []
  | left + 1, right =>
      rawProof "lf-fo-add-succ"
        [encodeNat left, encodeNat right, encodeNat (left + right)]
        [addRawProof left right]

/-- Every true runtime inequality compiles to an accepted generic-checker
certificate. -/
theorem ltRawProof_accepts {left right : Nat} (hlt : left < right) :
    checked.checkRaw (lt (encodeNat left) (encodeNat right))
      (ltRawProof left right) = true := by
  induction left generalizing right with
  | zero =>
      cases right with
      | zero => omega
      | succ right =>
          simp (config := { maxSteps := 1000000, decide := true })
            [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
             InferenceChecker.checkRawChildren, CheckedGSLT.presentation,
             checked, source, presentation, language, allRules, ltRawProof,
             rawProof, ltZeroSuccRule, rule, formal, m, instantiateRule?,
             Presentation.lookupRule?, instantiateSchema?,
             instantiateSchemaAt?, instantiateSchemas?,
             instantiateSchemasAt?, lookupArgumentAt?, argumentsValidAt,
             encodeNat_argumentValid, lt, encodeNat, zero, succ, ruleId]
  | succ left leftIH =>
      cases right with
      | zero => omega
      | succ right =>
          have hprevious : left < right := by omega
          have hchild := leftIH hprevious
          simp (config := { maxSteps := 1000000, decide := true })
            [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
             InferenceChecker.checkRawChildren, CheckedGSLT.presentation,
             checked, source, presentation, language, allRules, ltRawProof,
             rawProof, ltSuccSuccRule, rule, formal, m, instantiateRule?,
             Presentation.lookupRule?, instantiateSchema?,
             instantiateSchemaAt?, instantiateSchemas?,
             instantiateSchemasAt?, lookupArgumentAt?, argumentsValidAt,
             encodeNat_argumentValid, lt, encodeNat, succ, ruleId]
          simpa [CheckedGSLT.checkRaw, CheckedGSLT.presentation, checked,
            source, presentation, language, allRules, ltSuccSuccRule, rule,
            formal, m, lt, succ, ruleId] using hchild

/-- Every runtime sum compiles to an accepted generic-checker certificate for
its exact result. -/
theorem addRawProof_accepts (left right : Nat) :
    checked.checkRaw
      (add (encodeNat left) (encodeNat right) (encodeNat (left + right)))
      (addRawProof left right) = true := by
  induction left with
  | zero =>
      simp (config := { maxSteps := 1000000, decide := true })
        [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
         InferenceChecker.checkRawChildren, CheckedGSLT.presentation, checked,
         source, presentation, language, allRules, addRawProof, rawProof,
         addZeroRule, rule, formal, m, instantiateRule?,
         Presentation.lookupRule?, instantiateSchema?, instantiateSchemaAt?,
         instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?,
         argumentsValidAt, encodeNat_argumentValid, add, encodeNat, zero,
         ruleId]
  | succ left leftIH =>
      have hresult :
          succ (encodeNat (left + right)) =
            encodeNat (left + 1 + right) := by
        have hsum : left + 1 + right = (left + right) + 1 := by omega
        rw [hsum]
        rfl
      simp (config := { maxSteps := 1000000, decide := true })
        [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
         InferenceChecker.checkRawChildren, CheckedGSLT.presentation, checked,
         source, presentation, language, allRules, addRawProof, rawProof,
         addSuccRule, rule, formal, m, instantiateRule?,
         Presentation.lookupRule?, instantiateSchema?, instantiateSchemaAt?,
         instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?,
         argumentsValidAt, encodeNat_argumentValid, add, encodeNat,
         succ, ruleId]
      exact ⟨hresult, leftIH⟩

/-! ## Positive and negative executable boundaries -/

theorem three_lt_five_accepts :
    checked.checkRaw (lt (encodeNat 3) (encodeNat 5))
      (ltRawProof 3 5) = true := by
  exact ltRawProof_accepts (by decide)

/-- The total compiler's invalid branch cannot turn a false strict comparison
into evidence. -/
theorem one_lt_one_rejects :
    checked.checkRaw (lt (encodeNat 1) (encodeNat 1))
      (ltRawProof 1 1) = false := by
  simp (config := { maxSteps := 1000000, decide := true })
    [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
     InferenceChecker.checkRawChildren, CheckedGSLT.presentation, checked,
     source, presentation, language, allRules, ltRawProof, rawProof,
     ltSuccSuccRule, rule, formal, m, instantiateRule?,
     Presentation.lookupRule?, instantiateSchema?, instantiateSchemaAt?,
     instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?,
     lt, encodeNat, zero, succ, ruleId]

theorem three_add_five_accepts :
    checked.checkRaw (add (encodeNat 3) (encodeNat 5) (encodeNat 8))
      (addRawProof 3 5) = true := by
  simpa using addRawProof_accepts 3 5

#print axioms ltRawProof_accepts
#print axioms addRawProof_accepts
#print axioms three_lt_five_accepts
#print axioms one_lt_one_rejects
#print axioms three_add_five_accepts

end Mettapedia.GSLT.LanguageDef.LFFirstOrderArithmeticCorrespondence
