import Mettapedia.GSLT.LanguageDef.LF.FirstOrderArithmeticCorrespondence

/-!
# Proof-producing operational correspondence for first-order LF

This module compiles the executable de Bruijn operations used by the LF
runtime into first-order proof trees.  The trees are checked by the same
source-neutral inference checker used for imported presentations.

The first tranche covers general lifting.  Its variable cases deliberately
carry separate order and addition certificates, so the checker validates the
side conditions rather than trusting the runtime branch decision.
-/

namespace Mettapedia.GSLT.LanguageDef.LFFirstOrderOperationalCorrespondence

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping
open Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualConversion
open Mettapedia.GSLT.LanguageDef.LFFirstOrderContextualCorrespondence
open Mettapedia.GSLT.LanguageDef.LFFirstOrderArithmeticCorrespondence
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CheckedSource
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## General de Bruijn lifting -/

/-- Compile the runtime lift of one LF term to a first-order proof tree. -/
def liftRawProof (distance cutoff : Nat) : Term → RawProof
  | .var index =>
      if index < cutoff then
        rawProof "lf-fo-lift-var-below"
          [encodeNat distance, encodeNat cutoff, encodeNat index]
          [ltRawProof index cutoff]
      else if index = cutoff then
        rawProof "lf-fo-lift-var-equal"
          [encodeNat distance, encodeNat cutoff, encodeNat (cutoff + distance)]
          [addRawProof cutoff distance]
      else
        rawProof "lf-fo-lift-var-above"
          [encodeNat distance, encodeNat cutoff, encodeNat index,
            encodeNat (index + distance)]
          [ltRawProof cutoff index, addRawProof index distance]
  | .srt .type =>
      rawProof "lf-fo-lift-srt"
        [encodeNat distance, encodeNat cutoff, typeSort] []
  | .srt .kind =>
      rawProof "lf-fo-lift-srt"
        [encodeNat distance, encodeNat cutoff, kindSort] []
  | .con name =>
      rawProof "lf-fo-lift-con"
        [encodeNat distance, encodeNat cutoff, encodeName name] []
  | .pi domain body =>
      rawProof "lf-fo-lift-pi"
        [encodeNat distance, encodeNat cutoff, encodeTerm domain,
          encodeTerm body, encodeTerm (LFTyping.lift distance cutoff domain),
          encodeTerm (LFTyping.lift distance (cutoff + 1) body)]
        [liftRawProof distance cutoff domain,
          liftRawProof distance (cutoff + 1) body]
  | .lam domain body =>
      rawProof "lf-fo-lift-lam"
        [encodeNat distance, encodeNat cutoff, encodeTerm domain,
          encodeTerm body, encodeTerm (LFTyping.lift distance cutoff domain),
          encodeTerm (LFTyping.lift distance (cutoff + 1) body)]
        [liftRawProof distance cutoff domain,
          liftRawProof distance (cutoff + 1) body]
  | .app function argument =>
      rawProof "lf-fo-lift-app"
        [encodeNat distance, encodeNat cutoff, encodeTerm function,
          encodeTerm argument,
          encodeTerm (LFTyping.lift distance cutoff function),
          encodeTerm (LFTyping.lift distance cutoff argument)]
        [liftRawProof distance cutoff function,
          liftRawProof distance cutoff argument]

/-- Every runtime LF lift compiles to a certificate accepted by the actual
generic checker. -/
theorem liftRawProof_accepts (distance cutoff : Nat) (term : Term) :
    checked.checkRaw
      (lifts (encodeNat distance) (encodeNat cutoff) (encodeTerm term)
        (encodeTerm (LFTyping.lift distance cutoff term)))
      (liftRawProof distance cutoff term) = true := by
  induction term generalizing cutoff with
  | var index =>
      by_cases hbelow : index < cutoff
      · have hlt := ltRawProof_accepts hbelow
        simp (config := { maxSteps := 1000000, decide := true })
          [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
           InferenceChecker.checkRawChildren, CheckedGSLT.definition, checked,
           source, allRules, liftRawProof, rawProof,
           liftVarBelowRule, rule, formal, m, instantiateRule?,
           CalculusLanguageDef.lookupRule?, instantiateSchema?, instantiateSchemaAt?,
           instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?,
           argumentsValidAt, encodeNat_argumentValid, lifts, lt, encodeTerm,
           LFTyping.lift, hbelow, var, ruleId]
        simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition, checked, source,
          allRules, ltZeroSuccRule, ltSuccSuccRule,
          liftVarBelowRule, rule, formal, m, lt, encodeNat, zero, succ,
          lifts, var, ruleId] using hlt
      · by_cases hequal : index = cutoff
        · subst index
          have hadd := addRawProof_accepts cutoff distance
          simp (config := { maxSteps := 1000000, decide := true })
            [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
             InferenceChecker.checkRawChildren, CheckedGSLT.definition,
             checked, source, allRules, liftRawProof,
             rawProof, liftVarEqualRule, rule, formal, m, instantiateRule?,
             CalculusLanguageDef.lookupRule?, instantiateSchema?,
             instantiateSchemaAt?, instantiateSchemas?,
             instantiateSchemasAt?, lookupArgumentAt?, argumentsValidAt,
             encodeNat_argumentValid, lifts, add, encodeTerm, LFTyping.lift,
             var, ruleId]
          simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition, checked,
            source, allRules, addZeroRule, addSuccRule,
            liftVarEqualRule, rule, formal, m, add, encodeNat, zero, succ,
            lifts, var, ruleId] using hadd
        · have habove : cutoff < index := by omega
          have hlt := ltRawProof_accepts habove
          have hadd := addRawProof_accepts index distance
          simp (config := { maxSteps := 1000000, decide := true })
            [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
             InferenceChecker.checkRawChildren, CheckedGSLT.definition,
             checked, source, allRules, liftRawProof,
             rawProof, liftVarAboveRule, rule, formal, m, instantiateRule?,
             CalculusLanguageDef.lookupRule?, instantiateSchema?,
             instantiateSchemaAt?, instantiateSchemas?,
             instantiateSchemasAt?, lookupArgumentAt?, argumentsValidAt,
             encodeNat_argumentValid, lifts, lt, add, encodeTerm,
             LFTyping.lift, hbelow, hequal, var, ruleId]
          constructor
          · simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition, checked,
              source, allRules, ltZeroSuccRule,
              ltSuccSuccRule, liftVarAboveRule, rule, formal, m, lt, encodeNat,
              add, zero, succ, lifts, var, ruleId] using hlt
          · simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition, checked,
              source, allRules, addZeroRule,
              addSuccRule, liftVarAboveRule, rule, formal, m, add, encodeNat,
              lt, zero, succ, lifts, var, ruleId] using hadd
  | srt sort =>
      cases sort <;>
        simp (config := { maxSteps := 1000000, decide := true })
          [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
           InferenceChecker.checkRawChildren, CheckedGSLT.definition, checked,
           source, allRules, liftRawProof, rawProof,
           liftSrtRule, rule, formal, m, instantiateRule?,
           CalculusLanguageDef.lookupRule?, instantiateSchema?, instantiateSchemaAt?,
           instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?,
           argumentsValidAt, encodeNat_argumentValid, lifts, encodeTerm,
           LFTyping.lift, typeSort, kindSort, srt, ruleId]
  | con name =>
      simp (config := { maxSteps := 1000000, decide := true })
        [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
         InferenceChecker.checkRawChildren, CheckedGSLT.definition, checked,
         source, allRules, liftRawProof, rawProof,
         liftConRule, rule, formal, m, instantiateRule?,
         CalculusLanguageDef.lookupRule?, instantiateSchema?, instantiateSchemaAt?,
         instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?,
         argumentsValidAt, encodeNat_argumentValid, encodeName_argumentValid,
         lifts, encodeTerm, LFTyping.lift, con, ruleId]
  | pi domain body domainIH bodyIH =>
      simp (config := { maxSteps := 1000000, decide := true })
        [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
         InferenceChecker.checkRawChildren, CheckedGSLT.definition, checked,
         source, allRules, liftRawProof, rawProof,
         liftPiRule, rule, formal, m, instantiateRule?,
         CalculusLanguageDef.lookupRule?, instantiateSchema?, instantiateSchemaAt?,
         instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?,
         argumentsValidAt, encodeNat_argumentValid, encodeTerm_argumentValid,
         lifts, succ, encodeTerm, LFTyping.lift, pi, ruleId]
      constructor
      · simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition, checked, source,
          allRules, liftPiRule, rule, formal, m, lifts,
          encodeNat, succ, pi, ruleId] using domainIH cutoff
      · simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition, checked, source,
          allRules, liftPiRule, rule, formal, m, lifts,
          encodeNat, succ, pi, ruleId] using bodyIH (cutoff + 1)
  | lam domain body domainIH bodyIH =>
      simp (config := { maxSteps := 1000000, decide := true })
        [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
         InferenceChecker.checkRawChildren, CheckedGSLT.definition, checked,
         source, allRules, liftRawProof, rawProof,
         liftLamRule, rule, formal, m, instantiateRule?,
         CalculusLanguageDef.lookupRule?, instantiateSchema?, instantiateSchemaAt?,
         instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?,
         argumentsValidAt, encodeNat_argumentValid, encodeTerm_argumentValid,
         lifts, succ, encodeTerm, LFTyping.lift, lam, ruleId]
      constructor
      · simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition, checked, source,
          allRules, liftLamRule, rule, formal, m, lifts,
          encodeNat, succ, lam, ruleId] using domainIH cutoff
      · simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition, checked, source,
          allRules, liftLamRule, rule, formal, m, lifts,
          encodeNat, succ, lam, ruleId] using bodyIH (cutoff + 1)
  | app function argument functionIH argumentIH =>
      simp (config := { maxSteps := 1000000, decide := true })
        [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
         InferenceChecker.checkRawChildren, CheckedGSLT.definition, checked,
         source, allRules, liftRawProof, rawProof,
         liftAppRule, rule, formal, m, instantiateRule?,
         CalculusLanguageDef.lookupRule?, instantiateSchema?, instantiateSchemaAt?,
         instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?,
         argumentsValidAt, encodeNat_argumentValid, encodeTerm_argumentValid,
         lifts, encodeTerm, LFTyping.lift, app, ruleId]
      constructor
      · simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition, checked, source,
          allRules, liftAppRule, rule, formal, m, lifts,
          app, ruleId] using functionIH cutoff
      · simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition, checked, source,
          allRules, liftAppRule, rule, formal, m, lifts,
          app, ruleId] using argumentIH cutoff

/-! ## Capture-avoiding substitution -/

/-- Compile runtime substitution to a first-order proof tree. -/
def substRawProof (index : Nat) (replacement : Term) : Term → RawProof
  | .var variableIndex =>
      if variableIndex = index then
        rawProof "lf-fo-subst-var-equal"
          [encodeNat index, encodeTerm replacement] []
      else if variableIndex < index then
        rawProof "lf-fo-subst-var-below"
          [encodeNat index, encodeTerm replacement, encodeNat variableIndex]
          [ltRawProof variableIndex index]
      else
        rawProof "lf-fo-subst-var-above"
          [encodeNat index, encodeTerm replacement,
            encodeNat (variableIndex - 1)]
          [ltRawProof index variableIndex]
  | .srt .type =>
      rawProof "lf-fo-subst-srt"
        [encodeNat index, encodeTerm replacement, typeSort] []
  | .srt .kind =>
      rawProof "lf-fo-subst-srt"
        [encodeNat index, encodeTerm replacement, kindSort] []
  | .con name =>
      rawProof "lf-fo-subst-con"
        [encodeNat index, encodeTerm replacement, encodeName name] []
  | .pi domain body =>
      let liftedReplacement := LFTyping.lift 1 0 replacement
      rawProof "lf-fo-subst-pi"
        [encodeNat index, encodeTerm replacement, encodeTerm domain,
          encodeTerm body, encodeTerm (LFTyping.subst index replacement domain),
          encodeTerm liftedReplacement,
          encodeTerm
            (LFTyping.subst (index + 1) liftedReplacement body)]
        [substRawProof index replacement domain,
          liftRawProof 1 0 replacement,
          substRawProof (index + 1) liftedReplacement body]
  | .lam domain body =>
      let liftedReplacement := LFTyping.lift 1 0 replacement
      rawProof "lf-fo-subst-lam"
        [encodeNat index, encodeTerm replacement, encodeTerm domain,
          encodeTerm body, encodeTerm (LFTyping.subst index replacement domain),
          encodeTerm liftedReplacement,
          encodeTerm
            (LFTyping.subst (index + 1) liftedReplacement body)]
        [substRawProof index replacement domain,
          liftRawProof 1 0 replacement,
          substRawProof (index + 1) liftedReplacement body]
  | .app function argument =>
      rawProof "lf-fo-subst-app"
        [encodeNat index, encodeTerm replacement, encodeTerm function,
          encodeTerm argument,
          encodeTerm (LFTyping.subst index replacement function),
          encodeTerm (LFTyping.subst index replacement argument)]
        [substRawProof index replacement function,
          substRawProof index replacement argument]

private theorem encodeNat_pred_succ {value : Nat} (hpositive : 0 < value) :
    succ (encodeNat (value - 1)) = encodeNat value := by
  have hvalue : value = (value - 1) + 1 := by omega
  rw [hvalue]
  rfl

/-- Every runtime LF substitution compiles to a certificate accepted by the
actual generic checker. -/
theorem substRawProof_accepts (index : Nat) (replacement term : Term) :
    checked.checkRaw
      (substitutes (encodeNat index) (encodeTerm replacement)
        (encodeTerm term)
        (encodeTerm (LFTyping.subst index replacement term)))
      (substRawProof index replacement term) = true := by
  induction term generalizing index replacement with
  | var variableIndex =>
      by_cases hequal : variableIndex = index
      · subst variableIndex
        simp (config := { maxSteps := 1000000, decide := true })
          [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
           InferenceChecker.checkRawChildren, CheckedGSLT.definition, checked,
           source, allRules, substRawProof, rawProof,
           substVarEqualRule, rule, formal, m, instantiateRule?,
           CalculusLanguageDef.lookupRule?, instantiateSchema?, instantiateSchemaAt?,
           instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?,
           argumentsValidAt, encodeNat_argumentValid, encodeTerm_argumentValid,
           substitutes, encodeTerm, LFTyping.subst, var, ruleId]
      · by_cases hbelow : variableIndex < index
        · have hnotAbove : ¬index < variableIndex := by omega
          have hlt := ltRawProof_accepts hbelow
          simp (config := { maxSteps := 1000000, decide := true })
            [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
             InferenceChecker.checkRawChildren, CheckedGSLT.definition,
             checked, source, allRules, substRawProof,
             rawProof, substVarBelowRule, rule, formal, m, instantiateRule?,
             CalculusLanguageDef.lookupRule?, instantiateSchema?,
             instantiateSchemaAt?, instantiateSchemas?,
             instantiateSchemasAt?, lookupArgumentAt?, argumentsValidAt,
             encodeNat_argumentValid, encodeTerm_argumentValid, substitutes,
             lt, encodeTerm, LFTyping.subst, hequal, hbelow, hnotAbove, var,
             ruleId]
          simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition, checked,
            source, allRules, ltZeroSuccRule,
            ltSuccSuccRule, substVarBelowRule, rule, formal, m, lt, substitutes,
            var, ruleId] using hlt
        · have habove : index < variableIndex := by omega
          have hpositive : 0 < variableIndex := by omega
          have hencoded := encodeNat_pred_succ hpositive
          have hlt := ltRawProof_accepts habove
          have hltPredecessor :
              checked.checkRaw
                (lt (encodeNat index) (succ (encodeNat (variableIndex - 1))))
                (ltRawProof index variableIndex) = true := by
            rw [hencoded]
            exact hlt
          simp (config := { maxSteps := 1000000, decide := true })
            [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
             InferenceChecker.checkRawChildren, CheckedGSLT.definition,
             checked, source, allRules, substRawProof,
             rawProof, substVarAboveRule, rule, formal, m, instantiateRule?,
             CalculusLanguageDef.lookupRule?, instantiateSchema?,
             instantiateSchemaAt?, instantiateSchemas?,
             instantiateSchemasAt?, lookupArgumentAt?, argumentsValidAt,
             encodeNat_argumentValid, encodeTerm_argumentValid, substitutes,
             lt, succ, encodeTerm, LFTyping.subst, hequal, hbelow, habove,
             var, ruleId]
          constructor
          · exact hencoded
          · simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition, checked,
              source, allRules, ltZeroSuccRule,
              ltSuccSuccRule, substVarAboveRule, rule, formal, m, lt,
              substitutes, succ, var, ruleId] using hltPredecessor
  | srt sort =>
      cases sort <;>
        simp (config := { maxSteps := 1000000, decide := true })
          [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
           InferenceChecker.checkRawChildren, CheckedGSLT.definition, checked,
           source, allRules, substRawProof, rawProof,
           substSrtRule, rule, formal, m, instantiateRule?,
           CalculusLanguageDef.lookupRule?, instantiateSchema?, instantiateSchemaAt?,
           instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?,
           argumentsValidAt, encodeNat_argumentValid, encodeTerm_argumentValid,
           substitutes, encodeTerm, LFTyping.subst, typeSort, kindSort, srt,
           ruleId]
  | con name =>
      simp (config := { maxSteps := 1000000, decide := true })
        [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
         InferenceChecker.checkRawChildren, CheckedGSLT.definition, checked,
         source, allRules, substRawProof, rawProof,
         substConRule, rule, formal, m, instantiateRule?,
         CalculusLanguageDef.lookupRule?, instantiateSchema?, instantiateSchemaAt?,
         instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?,
         argumentsValidAt, encodeNat_argumentValid, encodeTerm_argumentValid,
         encodeName_argumentValid, substitutes, encodeTerm, LFTyping.subst, con,
         ruleId]
  | pi domain body domainIH bodyIH =>
      simp (config := { maxSteps := 1000000, decide := true })
        [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
         InferenceChecker.checkRawChildren, CheckedGSLT.definition, checked,
         source, allRules, substRawProof, rawProof,
         substPiRule, rule, formal, m, instantiateRule?,
         CalculusLanguageDef.lookupRule?, instantiateSchema?, instantiateSchemaAt?,
         instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?,
         argumentsValidAt, encodeNat_argumentValid, encodeTerm_argumentValid,
         substitutes, lifts, one, zero, succ, encodeTerm, LFTyping.subst, pi,
         ruleId]
      constructor
      · simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition, checked, source,
          allRules, substPiRule, rule, formal, m,
          substitutes, lifts, one, zero, succ, pi, ruleId] using
            domainIH index replacement
      constructor
      · simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition, checked, source,
          allRules, substPiRule, rule, formal, m,
          substitutes, lifts, one, zero, encodeNat, succ, pi, ruleId] using
            liftRawProof_accepts 1 0 replacement
      · simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition, checked, source,
          allRules, substPiRule, rule, formal, m,
          substitutes, lifts, one, zero, encodeNat, succ, pi, ruleId] using
            bodyIH (index + 1) (LFTyping.lift 1 0 replacement)
  | lam domain body domainIH bodyIH =>
      simp (config := { maxSteps := 1000000, decide := true })
        [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
         InferenceChecker.checkRawChildren, CheckedGSLT.definition, checked,
         source, allRules, substRawProof, rawProof,
         substLamRule, rule, formal, m, instantiateRule?,
         CalculusLanguageDef.lookupRule?, instantiateSchema?, instantiateSchemaAt?,
         instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?,
         argumentsValidAt, encodeNat_argumentValid, encodeTerm_argumentValid,
         substitutes, lifts, one, zero, succ, encodeTerm, LFTyping.subst, lam,
         ruleId]
      constructor
      · simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition, checked, source,
          allRules, substLamRule, rule, formal, m,
          substitutes, lifts, one, zero, succ, lam, ruleId] using
            domainIH index replacement
      constructor
      · simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition, checked, source,
          allRules, substLamRule, rule, formal, m,
          substitutes, lifts, one, zero, encodeNat, succ, lam, ruleId] using
            liftRawProof_accepts 1 0 replacement
      · simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition, checked, source,
          allRules, substLamRule, rule, formal, m,
          substitutes, lifts, one, zero, encodeNat, succ, lam, ruleId] using
            bodyIH (index + 1) (LFTyping.lift 1 0 replacement)
  | app function argument functionIH argumentIH =>
      simp (config := { maxSteps := 1000000, decide := true })
        [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
         InferenceChecker.checkRawChildren, CheckedGSLT.definition, checked,
         source, allRules, substRawProof, rawProof,
         substAppRule, rule, formal, m, instantiateRule?,
         CalculusLanguageDef.lookupRule?, instantiateSchema?, instantiateSchemaAt?,
         instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?,
         argumentsValidAt, encodeNat_argumentValid, encodeTerm_argumentValid,
         substitutes, encodeTerm, LFTyping.subst, app, ruleId]
      constructor
      · simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition, checked, source,
          allRules, substAppRule, rule, formal, m,
          substitutes, app, ruleId] using functionIH index replacement
      · simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition, checked, source,
          allRules, substAppRule, rule, formal, m,
          substitutes, app, ruleId] using argumentIH index replacement

/-! ## Unused-binder elimination -/

/-- Compile successful runtime unbinding together with its semantic result.
Failure is retained as `none`, including the exact captured-variable case. -/
def unbindCertified? (cutoff : Nat) : Term → Option (Term × RawProof)
  | .var variableIndex =>
      if variableIndex < cutoff then
        some (.var variableIndex,
          rawProof "lf-fo-unbind-var-below"
            [encodeNat cutoff, encodeNat variableIndex]
            [ltRawProof variableIndex cutoff])
      else if variableIndex = cutoff then
        none
      else
        some (.var (variableIndex - 1),
          rawProof "lf-fo-unbind-var-above"
            [encodeNat cutoff, encodeNat (variableIndex - 1)]
            [ltRawProof cutoff variableIndex])
  | .srt .type =>
      some (.srt .type,
        rawProof "lf-fo-unbind-srt" [encodeNat cutoff, typeSort] [])
  | .srt .kind =>
      some (.srt .kind,
        rawProof "lf-fo-unbind-srt" [encodeNat cutoff, kindSort] [])
  | .con name =>
      some (.con name,
        rawProof "lf-fo-unbind-con"
          [encodeNat cutoff, encodeName name] [])
  | .pi domain body => do
      let domainCertificate ← unbindCertified? cutoff domain
      let bodyCertificate ← unbindCertified? (cutoff + 1) body
      pure (.pi domainCertificate.1 bodyCertificate.1,
        rawProof "lf-fo-unbind-pi"
          [encodeNat cutoff, encodeTerm domain, encodeTerm body,
            encodeTerm domainCertificate.1, encodeTerm bodyCertificate.1]
          [domainCertificate.2, bodyCertificate.2])
  | .lam domain body => do
      let domainCertificate ← unbindCertified? cutoff domain
      let bodyCertificate ← unbindCertified? (cutoff + 1) body
      pure (.lam domainCertificate.1 bodyCertificate.1,
        rawProof "lf-fo-unbind-lam"
          [encodeNat cutoff, encodeTerm domain, encodeTerm body,
            encodeTerm domainCertificate.1, encodeTerm bodyCertificate.1]
          [domainCertificate.2, bodyCertificate.2])
  | .app function argument => do
      let functionCertificate ← unbindCertified? cutoff function
      let argumentCertificate ← unbindCertified? cutoff argument
      pure (.app functionCertificate.1 argumentCertificate.1,
        rawProof "lf-fo-unbind-app"
          [encodeNat cutoff, encodeTerm function, encodeTerm argument,
            encodeTerm functionCertificate.1, encodeTerm argumentCertificate.1]
          [functionCertificate.2, argumentCertificate.2])

/-- A successful compiled unbind has the same result as the runtime operation,
and its proof tree is accepted by the generic checker. -/
theorem unbindCertified?_sound :
    ∀ (cutoff : Nat) (term result : Term) (proof : RawProof),
      unbindCertified? cutoff term = some (result, proof) →
        LFBetaEta.unbind cutoff term = some result ∧
        checked.checkRaw
          (unbinds (encodeNat cutoff) (encodeTerm term) (encodeTerm result))
          proof = true := by
  intro cutoff term
  induction term generalizing cutoff with
  | var variableIndex =>
      intro result proof hcertificate
      by_cases hbelow : variableIndex < cutoff
      · simp [unbindCertified?, hbelow] at hcertificate
        rcases hcertificate with ⟨rfl, rfl⟩
        have hlt := ltRawProof_accepts hbelow
        constructor
        · simp [LFBetaEta.unbind, hbelow]
        · simp (config := { maxSteps := 1000000, decide := true })
            [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
             InferenceChecker.checkRawChildren, CheckedGSLT.definition,
             checked, source, allRules, rawProof,
             unbindVarBelowRule, rule, formal, m, instantiateRule?,
             CalculusLanguageDef.lookupRule?, instantiateSchema?,
             instantiateSchemaAt?, instantiateSchemas?,
             instantiateSchemasAt?, lookupArgumentAt?, argumentsValidAt,
             encodeNat_argumentValid, unbinds, lt, encodeTerm, var, ruleId]
          simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition, checked,
            source, allRules, ltZeroSuccRule,
            ltSuccSuccRule, unbindVarBelowRule, rule, formal, m, lt, unbinds,
            var, ruleId] using hlt
      · by_cases hequal : variableIndex = cutoff
        · simp [unbindCertified?, hequal] at hcertificate
        · have habove : cutoff < variableIndex := by omega
          have hpositive : 0 < variableIndex := by omega
          have hencoded := encodeNat_pred_succ hpositive
          have hlt := ltRawProof_accepts habove
          have hltPredecessor :
              checked.checkRaw
                (lt (encodeNat cutoff)
                  (succ (encodeNat (variableIndex - 1))))
                (ltRawProof cutoff variableIndex) = true := by
            rw [hencoded]
            exact hlt
          simp [unbindCertified?, hbelow, hequal] at hcertificate
          rcases hcertificate with ⟨rfl, rfl⟩
          constructor
          · simp [LFBetaEta.unbind, hbelow, hequal]
          · simp (config := { maxSteps := 1000000, decide := true })
              [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
               InferenceChecker.checkRawChildren, CheckedGSLT.definition,
               checked, source, allRules, rawProof,
               unbindVarAboveRule, rule, formal, m, instantiateRule?,
               CalculusLanguageDef.lookupRule?, instantiateSchema?,
               instantiateSchemaAt?, instantiateSchemas?,
               instantiateSchemasAt?, lookupArgumentAt?, argumentsValidAt,
               encodeNat_argumentValid, unbinds, lt, succ, encodeTerm, var,
               ruleId]
            constructor
            · exact hencoded
            · simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition, checked,
                source, allRules, ltZeroSuccRule,
                ltSuccSuccRule, unbindVarAboveRule, rule, formal, m, lt,
                unbinds, succ, var, ruleId] using hltPredecessor
  | srt sort =>
      intro result proof hcertificate
      cases sort <;>
        simp [unbindCertified?] at hcertificate <;>
        rcases hcertificate with ⟨rfl, rfl⟩ <;>
        constructor
      · simp [LFBetaEta.unbind]
      · simp (config := { maxSteps := 1000000, decide := true })
          [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
           InferenceChecker.checkRawChildren, CheckedGSLT.definition, checked,
           source, allRules, rawProof, unbindSrtRule,
           rule, formal, m, instantiateRule?, CalculusLanguageDef.lookupRule?,
           instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
           instantiateSchemasAt?, lookupArgumentAt?, argumentsValidAt,
           encodeNat_argumentValid, unbinds, encodeTerm, typeSort, srt, ruleId]
      · simp [LFBetaEta.unbind]
      · simp (config := { maxSteps := 1000000, decide := true })
          [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
           InferenceChecker.checkRawChildren, CheckedGSLT.definition, checked,
           source, allRules, rawProof, unbindSrtRule,
           rule, formal, m, instantiateRule?, CalculusLanguageDef.lookupRule?,
           instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
           instantiateSchemasAt?, lookupArgumentAt?, argumentsValidAt,
           encodeNat_argumentValid, unbinds, encodeTerm, kindSort, srt, ruleId]
  | con name =>
      intro result proof hcertificate
      simp [unbindCertified?] at hcertificate
      rcases hcertificate with ⟨rfl, rfl⟩
      constructor
      · simp [LFBetaEta.unbind]
      · simp (config := { maxSteps := 1000000, decide := true })
          [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
           InferenceChecker.checkRawChildren, CheckedGSLT.definition, checked,
           source, allRules, rawProof, unbindConRule,
           rule, formal, m, instantiateRule?, CalculusLanguageDef.lookupRule?,
           instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
           instantiateSchemasAt?, lookupArgumentAt?, argumentsValidAt,
           encodeNat_argumentValid, encodeName_argumentValid, unbinds,
           encodeTerm, con, ruleId]
  | pi domain body domainIH bodyIH =>
      intro result proof hcertificate
      cases hdomain : unbindCertified? cutoff domain with
      | none =>
          simp [unbindCertified?, hdomain] at hcertificate
      | some domainCertificate =>
          cases hbody : unbindCertified? (cutoff + 1) body with
          | none =>
              simp [unbindCertified?, hdomain, hbody] at hcertificate
          | some bodyCertificate =>
              rcases domainCertificate with ⟨domainResult, domainProof⟩
              rcases bodyCertificate with ⟨bodyResult, bodyProof⟩
              have hdomainSound :=
                domainIH cutoff domainResult domainProof hdomain
              have hbodySound :=
                bodyIH (cutoff + 1) bodyResult bodyProof hbody
              rcases hdomainSound with ⟨hdomainRuntime, hdomainCheck⟩
              rcases hbodySound with ⟨hbodyRuntime, hbodyCheck⟩
              simp [unbindCertified?, hdomain, hbody] at hcertificate
              rcases hcertificate with ⟨rfl, rfl⟩
              constructor
              · simp [LFBetaEta.unbind, hdomainRuntime, hbodyRuntime]
              · simp (config := { maxSteps := 1000000, decide := true })
                  [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
                   InferenceChecker.checkRawChildren, CheckedGSLT.definition,
                   checked, source, allRules, rawProof,
                   unbindPiRule, rule, formal, m, instantiateRule?,
                   CalculusLanguageDef.lookupRule?, instantiateSchema?,
                   instantiateSchemaAt?, instantiateSchemas?,
                   instantiateSchemasAt?, lookupArgumentAt?, argumentsValidAt,
                   encodeNat_argumentValid, encodeTerm_argumentValid, unbinds,
                   succ, encodeTerm, pi, ruleId]
                constructor
                · simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition,
                    checked, source, allRules,
                    unbindPiRule, rule, formal, m, unbinds, succ, pi, ruleId]
                    using hdomainCheck
                · simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition,
                    checked, source, allRules,
                    unbindPiRule, rule, formal, m, unbinds, encodeNat, succ, pi,
                    ruleId] using hbodyCheck
  | lam domain body domainIH bodyIH =>
      intro result proof hcertificate
      cases hdomain : unbindCertified? cutoff domain with
      | none =>
          simp [unbindCertified?, hdomain] at hcertificate
      | some domainCertificate =>
          cases hbody : unbindCertified? (cutoff + 1) body with
          | none =>
              simp [unbindCertified?, hdomain, hbody] at hcertificate
          | some bodyCertificate =>
              rcases domainCertificate with ⟨domainResult, domainProof⟩
              rcases bodyCertificate with ⟨bodyResult, bodyProof⟩
              have hdomainSound :=
                domainIH cutoff domainResult domainProof hdomain
              have hbodySound :=
                bodyIH (cutoff + 1) bodyResult bodyProof hbody
              rcases hdomainSound with ⟨hdomainRuntime, hdomainCheck⟩
              rcases hbodySound with ⟨hbodyRuntime, hbodyCheck⟩
              simp [unbindCertified?, hdomain, hbody] at hcertificate
              rcases hcertificate with ⟨rfl, rfl⟩
              constructor
              · simp [LFBetaEta.unbind, hdomainRuntime, hbodyRuntime]
              · simp (config := { maxSteps := 1000000, decide := true })
                  [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
                   InferenceChecker.checkRawChildren, CheckedGSLT.definition,
                   checked, source, allRules, rawProof,
                   unbindLamRule, rule, formal, m, instantiateRule?,
                   CalculusLanguageDef.lookupRule?, instantiateSchema?,
                   instantiateSchemaAt?, instantiateSchemas?,
                   instantiateSchemasAt?, lookupArgumentAt?, argumentsValidAt,
                   encodeNat_argumentValid, encodeTerm_argumentValid, unbinds,
                   succ, encodeTerm, lam, ruleId]
                constructor
                · simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition,
                    checked, source, allRules,
                    unbindLamRule, rule, formal, m, unbinds, succ, lam, ruleId]
                    using hdomainCheck
                · simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition,
                    checked, source, allRules,
                    unbindLamRule, rule, formal, m, unbinds, encodeNat, succ,
                    lam, ruleId] using hbodyCheck
  | app function argument functionIH argumentIH =>
      intro result proof hcertificate
      cases hfunction : unbindCertified? cutoff function with
      | none =>
          simp [unbindCertified?, hfunction] at hcertificate
      | some functionCertificate =>
          cases hargument : unbindCertified? cutoff argument with
          | none =>
              simp [unbindCertified?, hfunction, hargument] at hcertificate
          | some argumentCertificate =>
              rcases functionCertificate with ⟨functionResult, functionProof⟩
              rcases argumentCertificate with ⟨argumentResult, argumentProof⟩
              have hfunctionSound :=
                functionIH cutoff functionResult functionProof hfunction
              have hargumentSound :=
                argumentIH cutoff argumentResult argumentProof hargument
              rcases hfunctionSound with ⟨hfunctionRuntime, hfunctionCheck⟩
              rcases hargumentSound with ⟨hargumentRuntime, hargumentCheck⟩
              simp [unbindCertified?, hfunction, hargument] at hcertificate
              rcases hcertificate with ⟨rfl, rfl⟩
              constructor
              · simp [LFBetaEta.unbind, hfunctionRuntime, hargumentRuntime]
              · simp (config := { maxSteps := 1000000, decide := true })
                  [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
                   InferenceChecker.checkRawChildren, CheckedGSLT.definition,
                   checked, source, allRules, rawProof,
                   unbindAppRule, rule, formal, m, instantiateRule?,
                   CalculusLanguageDef.lookupRule?, instantiateSchema?,
                   instantiateSchemaAt?, instantiateSchemas?,
                   instantiateSchemasAt?, lookupArgumentAt?, argumentsValidAt,
                   encodeNat_argumentValid, encodeTerm_argumentValid, unbinds,
                   encodeTerm, app, ruleId]
                constructor
                · simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition,
                    checked, source, allRules,
                    unbindAppRule, rule, formal, m, unbinds, app, ruleId] using
                    hfunctionCheck
                · simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition,
                    checked, source, allRules,
                    unbindAppRule, rule, formal, m, unbinds, app, ruleId] using
                    hargumentCheck

/-! ## Root and contextual beta-eta certificates -/

/-- Compile a root beta contraction, including its full substitution tree. -/
def betaRootRawProof (domain body argument : Term) : RawProof :=
  rawProof "lf-fo-root-beta"
    [encodeTerm domain, encodeTerm body, encodeTerm argument,
      encodeTerm (LFTyping.subst0 argument body)]
    [substRawProof 0 argument body]

theorem betaRootRawProof_accepts (domain body argument : Term) :
    checked.checkRaw
      (rootStep
        (encodeTerm (.app (.lam domain body) argument))
        (encodeTerm (LFTyping.subst0 argument body)))
      (betaRootRawProof domain body argument) = true := by
  have hsubst := substRawProof_accepts 0 argument body
  simp (config := { maxSteps := 1000000, decide := true })
    [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
     InferenceChecker.checkRawChildren, CheckedGSLT.definition, checked,
     source, allRules, betaRootRawProof, rawProof,
     rootBetaRule, rule, formal, m, instantiateRule?,
     CalculusLanguageDef.lookupRule?, instantiateSchema?, instantiateSchemaAt?,
     instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?,
     argumentsValidAt, encodeTerm_argumentValid, rootStep, substitutes, zero,
     encodeTerm, LFTyping.subst0, app, lam, ruleId]
  simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition, checked, source,
    allRules, rootBetaRule, rule, formal, m, rootStep,
    substitutes, zero, encodeNat, app, lam, ruleId] using hsubst

/-- Compile a root eta contraction when unused-binder elimination succeeds. -/
def etaRootCertified? (domain function : Term) : Option (Term × RawProof) := do
  let unbindCertificate ← unbindCertified? 0 function
  pure (unbindCertificate.1,
    rawProof "lf-fo-root-eta"
      [encodeTerm domain, encodeTerm function,
        encodeTerm unbindCertificate.1]
      [unbindCertificate.2])

theorem etaRootCertified?_sound
    (domain function result : Term) (proof : RawProof)
    (hcertificate :
      etaRootCertified? domain function = some (result, proof)) :
    LFBetaEta.unbind 0 function = some result ∧
    checked.checkRaw
      (rootStep
        (encodeTerm (.lam domain (.app function (.var 0))))
        (encodeTerm result))
      proof = true := by
  cases hunbind : unbindCertified? 0 function with
  | none =>
      simp [etaRootCertified?, hunbind] at hcertificate
  | some unbindCertificate =>
      rcases unbindCertificate with ⟨unbindResult, unbindProof⟩
      have hunbindSound :=
        unbindCertified?_sound 0 function unbindResult unbindProof hunbind
      rcases hunbindSound with ⟨hruntime, hcheck⟩
      simp [etaRootCertified?, hunbind] at hcertificate
      rcases hcertificate with ⟨rfl, rfl⟩
      constructor
      · exact hruntime
      · simp (config := { maxSteps := 1000000, decide := true })
          [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
           InferenceChecker.checkRawChildren, CheckedGSLT.definition, checked,
           source, allRules, rawProof, rootEtaRule,
           rule, formal, m, instantiateRule?, CalculusLanguageDef.lookupRule?,
           instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
           instantiateSchemasAt?, lookupArgumentAt?, argumentsValidAt,
           encodeTerm_argumentValid, rootStep, unbinds, zero, encodeNat,
           encodeTerm, lam, app, var, ruleId]
        simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition, checked, source,
          allRules, rootEtaRule, rule, formal, m,
          rootStep, unbinds, zero, encodeNat, lam, app, var, ruleId] using hcheck

/-- Place any accepted encoded root contraction in any runtime one-hole
context. -/
def contextualRawProof
    (context : LFContextualBetaEta.Context)
    (rootSource rootTarget : Term) (rootProof : RawProof) : RawProof :=
  rawProof "lf-fo-contextual-conversion"
    [encodeContext context, encodeTerm rootSource, encodeTerm rootTarget,
      encodeTerm (context.plug rootSource),
      encodeTerm (context.plug rootTarget)]
    [rootProof, plugRawProof context rootSource,
      plugRawProof context rootTarget]

theorem contextualRawProof_accepts
    (context : LFContextualBetaEta.Context)
    (rootSource rootTarget : Term) (rootProof : RawProof)
    (hroot :
      checked.checkRaw
        (rootStep (encodeTerm rootSource) (encodeTerm rootTarget))
        rootProof = true) :
    checked.checkRaw
      (converts
        (encodeTerm (context.plug rootSource))
        (encodeTerm (context.plug rootTarget)))
      (contextualRawProof context rootSource rootTarget rootProof) = true := by
  have hsourcePlug := plugRawProof_accepts context rootSource
  have htargetPlug := plugRawProof_accepts context rootTarget
  simp (config := { maxSteps := 1000000, decide := true })
    [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
     InferenceChecker.checkRawChildren, CheckedGSLT.definition, checked,
     source, allRules, contextualRawProof, rawProof,
     contextualConversionRule, rule, formal, m, instantiateRule?,
     CalculusLanguageDef.lookupRule?, instantiateSchema?, instantiateSchemaAt?,
     instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?,
     argumentsValidAt, encodeContext_argumentValid, encodeTerm_argumentValid,
     converts, rootStep, plugs, ruleId]
  constructor
  · simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition, checked, source,
      allRules, contextualConversionRule, rule, formal,
      m, converts, rootStep, plugs, ruleId] using hroot
  constructor
  · simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition, checked, source,
      allRules, contextualConversionRule, rule, formal,
      m, converts, rootStep, plugs, ruleId] using hsourcePlug
  · simpa [CheckedGSLT.checkRaw, CheckedGSLT.definition, checked, source,
      allRules, contextualConversionRule, rule, formal,
      m, converts, rootStep, plugs, ruleId] using htargetPlug

/-- Universal proof-producing contextual beta conversion. -/
def contextualBetaRawProof
    (context : LFContextualBetaEta.Context)
    (domain body argument : Term) : RawProof :=
  contextualRawProof context
    (.app (.lam domain body) argument)
    (LFTyping.subst0 argument body)
    (betaRootRawProof domain body argument)

theorem contextualBetaRawProof_accepts
    (context : LFContextualBetaEta.Context)
    (domain body argument : Term) :
    checked.checkRaw
      (converts
        (encodeTerm
          (context.plug (.app (.lam domain body) argument)))
        (encodeTerm
          (context.plug (LFTyping.subst0 argument body))))
      (contextualBetaRawProof context domain body argument) = true := by
  exact contextualRawProof_accepts _ _ _ _
    (betaRootRawProof_accepts domain body argument)

/-- Compile an eta contraction under an arbitrary one-hole context.  The
result returned to the caller is the complete contextual target, not merely
the unbound root term. -/
def contextualEtaCertified?
    (context : LFContextualBetaEta.Context)
    (domain function : Term) : Option (Term × RawProof) := do
  let rootCertificate ← etaRootCertified? domain function
  let rootSource := .lam domain (.app function (.var 0))
  pure (context.plug rootCertificate.1,
    contextualRawProof context rootSource rootCertificate.1
      rootCertificate.2)

theorem contextualEtaCertified?_sound
    (context : LFContextualBetaEta.Context)
    (domain function target : Term) (proof : RawProof)
    (hcertificate :
      contextualEtaCertified? context domain function =
        some (target, proof)) :
    ∃ rootTarget,
      LFBetaEta.unbind 0 function = some rootTarget ∧
      target = context.plug rootTarget ∧
      checked.checkRaw
        (converts
          (encodeTerm
            (context.plug
              (.lam domain (.app function (.var 0)))))
          (encodeTerm target))
        proof = true := by
  cases heta : etaRootCertified? domain function with
  | none =>
      simp [contextualEtaCertified?, heta] at hcertificate
  | some rootCertificate =>
      rcases rootCertificate with ⟨rootTarget, rootProof⟩
      have hetaSound :=
        etaRootCertified?_sound domain function rootTarget rootProof heta
      rcases hetaSound with ⟨hunbind, hrootCheck⟩
      simp [contextualEtaCertified?, heta] at hcertificate
      rcases hcertificate with ⟨rfl, rfl⟩
      exact ⟨rootTarget, hunbind, rfl,
        contextualRawProof_accepts _ _ _ _ hrootCheck⟩

/-! ## Finite conversion-certificate composition -/

/-- Runtime data for one already-generated conversion certificate.  The
checker theorem is deliberately not stored in the structure: serialized
certificates remain ordinary data and are rechecked at the trust boundary. -/
structure ConversionCertificate where
  source : Term
  target : Term
  proof : RawProof

namespace ConversionCertificate

/-- The exact proposition discharged when one runtime certificate is checked. -/
def Accepted (certificate : ConversionCertificate) : Prop :=
  checked.checkRaw
    (converts (encodeTerm certificate.source)
      (encodeTerm certificate.target))
    certificate.proof = true

/-- Explicit reflexive certificate. -/
def refl (term : Term) : ConversionCertificate :=
  { source := term
    target := term
    proof :=
      rawProof "lf-fo-conversion-refl" [encodeTerm term] [] }

theorem refl_accepted (term : Term) : (refl term).Accepted := by
  simp (config := { maxSteps := 1000000, decide := true })
    [Accepted, CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
     InferenceChecker.checkRawChildren, CheckedGSLT.definition, checked,
     LFFirstOrderContextualConversion.source,
     LFFirstOrderContextualConversion.definition,
     LFFirstOrderContextualConversion.allRules, refl, rawProof,
     LFFirstOrderContextualConversion.conversionReflRule,
     LFFirstOrderContextualConversion.rule,
     LFFirstOrderContextualConversion.formal,
     LFFirstOrderContextualConversion.m, instantiateRule?,
     CalculusLanguageDef.lookupRule?, instantiateSchema?, instantiateSchemaAt?,
     instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?,
     argumentsValidAt, encodeTerm_argumentValid, converts,
     LFFirstOrderContextualConversion.ruleId]

/-- Compose two certificates whose runtime endpoints coincide. -/
def trans (first second : ConversionCertificate)
    (_ : first.target = second.source) : ConversionCertificate :=
  { source := first.source
    target := second.target
    proof :=
      rawProof "lf-fo-conversion-trans"
        [encodeTerm first.source, encodeTerm first.target,
          encodeTerm second.target]
        [first.proof, second.proof] }

theorem trans_accepted (first second : ConversionCertificate)
    (hendpoints : first.target = second.source)
    (hfirst : first.Accepted) (hsecond : second.Accepted) :
    (trans first second hendpoints).Accepted := by
  simp (config := { maxSteps := 1000000, decide := true })
    [Accepted, CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
     InferenceChecker.checkRawChildren, CheckedGSLT.definition, checked,
     LFFirstOrderContextualConversion.source,
     LFFirstOrderContextualConversion.definition,
     LFFirstOrderContextualConversion.allRules, trans, rawProof,
     LFFirstOrderContextualConversion.conversionTransRule,
     LFFirstOrderContextualConversion.rule,
     LFFirstOrderContextualConversion.formal,
     LFFirstOrderContextualConversion.m, instantiateRule?,
     CalculusLanguageDef.lookupRule?, instantiateSchema?, instantiateSchemaAt?,
     instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?,
     argumentsValidAt, encodeTerm_argumentValid, converts,
     LFFirstOrderContextualConversion.ruleId]
  constructor
  · exact hfirst
  · simpa [Accepted, CheckedGSLT.checkRaw, CheckedGSLT.definition, checked,
      LFFirstOrderContextualConversion.source,
      LFFirstOrderContextualConversion.definition,
      LFFirstOrderContextualConversion.allRules,
      LFFirstOrderContextualConversion.conversionTransRule,
      LFFirstOrderContextualConversion.rule,
      LFFirstOrderContextualConversion.formal,
      LFFirstOrderContextualConversion.m,
      LFFirstOrderContextualConversion.ruleId,
      LFFirstOrderContextualConversion.converts, hendpoints] using hsecond

/-- Executable composition rejects a broken intermediate endpoint. -/
def trans? (first second : ConversionCertificate) :
    Option ConversionCertificate :=
  if hendpoints : first.target = second.source then
    some (trans first second hendpoints)
  else
    none

theorem trans?_sound (first second result : ConversionCertificate)
    (hfirst : first.Accepted) (hsecond : second.Accepted)
    (hcompose : trans? first second = some result) :
    result.source = first.source ∧
    result.target = second.target ∧ result.Accepted := by
  by_cases hendpoints : first.target = second.source
  · simp [trans?, hendpoints] at hcompose
    subst result
    exact ⟨rfl, rfl, trans_accepted first second hendpoints hfirst hsecond⟩
  · simp [trans?, hendpoints] at hcompose

/-- Left-associated composition of one accepted certificate with a remaining
chronological list. -/
def composeFrom? (accumulator : ConversionCertificate) :
    List ConversionCertificate → Option ConversionCertificate
  | [] => some accumulator
  | next :: rest => do
      let combined ← trans? accumulator next
      composeFrom? combined rest

theorem composeFrom?_sound
    (accumulator result : ConversionCertificate)
    (rest : List ConversionCertificate)
    (haccumulator : accumulator.Accepted)
    (hrest : ∀ certificate ∈ rest, certificate.Accepted)
    (hcompose : composeFrom? accumulator rest = some result) :
    result.Accepted := by
  induction rest generalizing accumulator result with
  | nil =>
      simp [composeFrom?] at hcompose
      subst result
      exact haccumulator
  | cons next tail ih =>
      cases hstep : trans? accumulator next with
      | none =>
          simp [composeFrom?, hstep] at hcompose
      | some combined =>
          have hnext : next.Accepted :=
            hrest next (by simp)
          have hcombined : combined.Accepted :=
            (trans?_sound accumulator next combined haccumulator hnext
              hstep).2.2
          have htail :
              ∀ certificate ∈ tail, certificate.Accepted := by
            intro certificate hmember
            exact hrest certificate (by simp [hmember])
          exact ih combined result hcombined htail
            (by simpa [composeFrom?, hstep] using hcompose)

/-- Compose a nonempty chronological list of runtime certificates. -/
def compose? : List ConversionCertificate → Option ConversionCertificate
  | [] => none
  | first :: rest => composeFrom? first rest

theorem compose?_sound
    (certificates : List ConversionCertificate)
    (result : ConversionCertificate)
    (haccepted :
      ∀ certificate ∈ certificates, certificate.Accepted)
    (hcompose : compose? certificates = some result) :
    result.Accepted := by
  cases certificates with
  | nil =>
      simp [compose?] at hcompose
  | cons first rest =>
      exact composeFrom?_sound first result rest
        (haccepted first (by simp))
        (by
          intro certificate hmember
          exact haccepted certificate (by simp [hmember]))
        (by simpa [compose?] using hcompose)

/-- Package the universal contextual-beta compiler as composable runtime data. -/
def beta
    (context : LFContextualBetaEta.Context)
    (domain body argument : Term) : ConversionCertificate :=
  { source := context.plug (.app (.lam domain body) argument)
    target := context.plug (LFTyping.subst0 argument body)
    proof := contextualBetaRawProof context domain body argument }

theorem beta_accepted
    (context : LFContextualBetaEta.Context)
    (domain body argument : Term) :
    (beta context domain body argument).Accepted := by
  exact contextualBetaRawProof_accepts context domain body argument

/-- Package a successful contextual-eta compiler result as composable data. -/
def eta?
    (context : LFContextualBetaEta.Context)
    (domain function : Term) : Option ConversionCertificate := do
  let certificate ← contextualEtaCertified? context domain function
  pure
    { source :=
        context.plug (.lam domain (.app function (.var 0)))
      target := certificate.1
      proof := certificate.2 }

/-- Successful eta compilation retains the exact unreduced runtime source. -/
theorem eta?_source
    (context : LFContextualBetaEta.Context)
    (domain function : Term) (certificate : ConversionCertificate)
    (hcertificate : eta? context domain function = some certificate) :
    certificate.source =
      context.plug (.lam domain (.app function (.var 0))) := by
  cases hroot :
      contextualEtaCertified? context domain function with
  | none =>
      simp [eta?, hroot] at hcertificate
  | some rootCertificate =>
      rcases rootCertificate with ⟨target, proof⟩
      simp [eta?, hroot] at hcertificate
      subst certificate
      rfl

theorem eta?_sound
    (context : LFContextualBetaEta.Context)
    (domain function : Term) (certificate : ConversionCertificate)
    (hcertificate : eta? context domain function = some certificate) :
    certificate.Accepted := by
  cases hroot :
      contextualEtaCertified? context domain function with
  | none =>
      simp [eta?, hroot] at hcertificate
  | some rootCertificate =>
      rcases rootCertificate with ⟨target, proof⟩
      have hsound :=
        contextualEtaCertified?_sound context domain function target proof
          hroot
      rcases hsound with ⟨rootTarget, hunbind, rfl, hcheck⟩
      simp [eta?, hroot] at hcertificate
      subst certificate
      exact hcheck

end ConversionCertificate

/-! ## Executable boundaries -/

private def nestedBetaContext : LFContextualBetaEta.Context :=
  .piBody (.srt .type)
    (.lamBody (.srt .type)
      (.appFunction .hole (.srt .kind)))

/-- A generated certificate validates beta contraction beneath three distinct
constructor positions. -/
theorem nested_contextual_beta_accepts :
    checked.checkRaw
      (converts
        (encodeTerm
          (nestedBetaContext.plug
            (.app (.lam (.srt .type) (.var 0)) (.srt .kind))))
        (encodeTerm
          (nestedBetaContext.plug (.srt .kind))))
      (contextualBetaRawProof nestedBetaContext
        (.srt .type) (.var 0) (.srt .kind)) = true := by
  exact contextualBetaRawProof_accepts _ _ _ _

/-- A free variable survives eta contraction and is decremented exactly once;
the existential certificate is checked by the generic source-neutral
checker. -/
theorem eta_free_variable_certificate_exists :
    ∃ target proof,
      etaRootCertified? (.srt .type) (.var 1) = some (target, proof) ∧
      LFBetaEta.unbind 0 (.var 1) = some target ∧
      checked.checkRaw
        (rootStep
          (encodeTerm
            (.lam (.srt .type) (.app (.var 1) (.var 0))))
          (encodeTerm target))
        proof = true := by
  cases hcertificate :
      etaRootCertified? (.srt .type) (.var 1) with
  | none =>
      simp [etaRootCertified?, unbindCertified?] at hcertificate
  | some certificate =>
      rcases certificate with ⟨target, proof⟩
      have hsound :=
        etaRootCertified?_sound (.srt .type) (.var 1) target proof
          hcertificate
      exact ⟨target, proof, rfl, hsound⟩

/-- Eta compilation fails at the captured variable rather than manufacturing
an invalid proof. -/
theorem eta_captured_variable_rejects :
    etaRootCertified? (.srt .type) (.var 0) = none := by
  rfl

/-- Root-beta proof objects are tied to the exact computed substitution
target.  Reusing one against a different target is rejected by the generic
checker. -/
theorem changed_beta_target_rejects :
    checked.checkRaw
      (rootStep
        (encodeTerm
          (.app (.lam (.srt .type) (.var 0)) (.srt .kind)))
        (encodeTerm (.srt .type)))
      (betaRootRawProof (.srt .type) (.var 0) (.srt .kind)) = false := by
  simp (config := { maxSteps := 1000000, decide := true })
    [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
     InferenceChecker.checkRawChildren, CheckedGSLT.definition, checked,
     source, allRules, betaRootRawProof, rawProof,
     rootBetaRule, rule, formal, m, instantiateRule?,
     CalculusLanguageDef.lookupRule?, instantiateSchema?, instantiateSchemaAt?,
     instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?,
     rootStep, substitutes, encodeTerm, LFTyping.subst0, zero, typeSort,
     kindSort, srt, app, lam, var, ruleId]

private def innerBetaRedex : Term :=
  .app (.lam (.srt .type) (.var 0)) (.srt .kind)

private def firstBetaCertificate : ConversionCertificate :=
  .beta .hole (.srt .type) (.var 0) innerBetaRedex

private def secondBetaCertificate : ConversionCertificate :=
  .beta .hole (.srt .type) (.var 0) (.srt .kind)

private def twoStepBetaCertificate : ConversionCertificate :=
  ConversionCertificate.trans firstBetaCertificate secondBetaCertificate
    (by rfl)

/-- The executable list compiler connects two successive beta contractions and
returns their checked transitive certificate. -/
theorem two_step_beta_composition_exact :
    ConversionCertificate.compose?
      [firstBetaCertificate, secondBetaCertificate] =
        some twoStepBetaCertificate := by
  rfl

theorem two_step_beta_composition_accepts :
    twoStepBetaCertificate.Accepted := by
  apply ConversionCertificate.compose?_sound
    [firstBetaCertificate, secondBetaCertificate] twoStepBetaCertificate
  · intro certificate hmember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmember
    rcases hmember with rfl | rfl
    · exact ConversionCertificate.beta_accepted _ _ _ _
    · exact ConversionCertificate.beta_accepted _ _ _ _
  · exact two_step_beta_composition_exact

/-- Reversing the same two certificates breaks the intermediate endpoint and
is rejected before a transitivity proof is emitted. -/
theorem reversed_beta_chain_rejects :
    ConversionCertificate.trans?
      secondBetaCertificate firstBetaCertificate = none := by
  rfl

theorem nested_lift_accepts :
    checked.checkRaw
      (lifts (encodeNat 2) (encodeNat 1)
        (encodeTerm (.lam (.srt .type) (.app (.var 1) (.var 0))))
        (encodeTerm
          (LFTyping.lift 2 1
            (.lam (.srt .type) (.app (.var 1) (.var 0))))))
      (liftRawProof 2 1
        (.lam (.srt .type) (.app (.var 1) (.var 0)))) = true := by
  exact liftRawProof_accepts 2 1 _

/-- A lift certificate is tied to its exact target. -/
theorem changed_lift_target_rejects :
    checked.checkRaw
      (lifts (encodeNat 2) (encodeNat 1) (encodeTerm (.var 3))
        (encodeTerm (.var 4)))
      (liftRawProof 2 1 (.var 3)) = false := by
  simp (config := { maxSteps := 1000000, decide := true })
    [CheckedGSLT.checkRaw, InferenceChecker.checkRaw,
     InferenceChecker.checkRawChildren, CheckedGSLT.definition, checked,
     source, allRules, liftRawProof, rawProof,
     liftVarAboveRule, rule, formal, m, instantiateRule?,
     CalculusLanguageDef.lookupRule?, instantiateSchema?, instantiateSchemaAt?,
     instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?,
     lifts, encodeTerm, ltRawProof, addRawProof, lt, add, encodeNat, zero, succ,
     var, ruleId]

#print axioms liftRawProof_accepts
#print axioms substRawProof_accepts
#print axioms unbindCertified?_sound
#print axioms betaRootRawProof_accepts
#print axioms etaRootCertified?_sound
#print axioms contextualRawProof_accepts
#print axioms contextualBetaRawProof_accepts
#print axioms contextualEtaCertified?_sound
#print axioms nested_lift_accepts
#print axioms changed_lift_target_rejects
#print axioms nested_contextual_beta_accepts
#print axioms eta_free_variable_certificate_exists
#print axioms eta_captured_variable_rejects
#print axioms changed_beta_target_rejects
#print axioms ConversionCertificate.refl_accepted
#print axioms ConversionCertificate.trans_accepted
#print axioms ConversionCertificate.trans?_sound
#print axioms ConversionCertificate.compose?_sound
#print axioms ConversionCertificate.beta_accepted
#print axioms ConversionCertificate.eta?_source
#print axioms ConversionCertificate.eta?_sound
#print axioms two_step_beta_composition_exact
#print axioms two_step_beta_composition_accepts
#print axioms reversed_beta_chain_rejects

end Mettapedia.GSLT.LanguageDef.LFFirstOrderOperationalCorrespondence
