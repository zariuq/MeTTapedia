import Mettapedia.GSLT.LanguageDef.HOLKernelProfiles
import Mettapedia.GSLT.LanguageDef.InferenceInstantiationBridge

namespace Mettapedia.GSLT.LanguageDef.HOLInferenceExtraction

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceExtraction
open Mettapedia.GSLT.LanguageDef.InferenceInstantiationBridge
open Mettapedia.GSLT.LanguageDef.HOLKernelProfiles

def holLightEvidenceProfile : EvidenceProfile :=
  { checkHead := "HLCheck"
    okHead := "HLOk"
    proofCategory := "HolProof"
    evidenceCategory := "HolThm"
    derivedHead := "$hol.thm"
    relationHeadPrefix := "$hol.rel." }

def hol4EvidenceProfile : EvidenceProfile :=
  { checkHead := "H4Check"
    okHead := "H4Ok"
    proofCategory := "HolProof"
    evidenceCategory := "HolThm"
    derivedHead := "$hol.thm"
    relationHeadPrefix := "$hol.rel." }

def holLightInferenceDefinition? : Option CalculusLanguageDef :=
  rawDefinition? holLightEvidenceProfile holLightEqKernel holLightLogic.1

def hol4InferenceDefinition? : Option CalculusLanguageDef :=
  rawDefinition? hol4EvidenceProfile hol4LcfKernel hol4Logic.1

def holLightValidatedDefinition? : Option ValidatedCalculusLanguageDef :=
  validatedDefinition? holLightEvidenceProfile holLightEqKernel
    holLightLogic.1

def hol4ValidatedDefinition? : Option ValidatedCalculusLanguageDef :=
  validatedDefinition? hol4EvidenceProfile hol4LcfKernel hol4Logic.1

def extractedEvidenceArity? (profile : EvidenceProfile)
    (language : LanguageDef) : Option (List Nat) := do
  let rules ← language.rewrites.mapM (extractRule? profile language)
  pure <| rules.map (·.evidencePremises.length)

def extractedSideArity? (profile : EvidenceProfile)
    (language : LanguageDef) : Option (List Nat) := do
  let rules ← language.rewrites.mapM (extractRule? profile language)
  pure <| rules.map (·.sidePremises.length)

/-- Check every authored generated rule, including its ordered premises and
conclusion, against the proved source/checker instantiation fragment. -/
def extractedRulesInBindingFragment? (profile : EvidenceProfile)
    (language : LanguageDef) : Option Bool := do
  let rules ← language.rewrites.mapM (extractRule? profile language)
  pure <| rules.all fun extraction =>
    (RuleSchema.patterns extraction.schema).all
      (checkBindingSchemaFragment extraction.schema.metavariables)

#guard holLightValidatedDefinition?.isSome
#guard hol4ValidatedDefinition?.isSome

#guard extractedEvidenceArity? holLightEvidenceProfile holLightEqKernel ==
  some [0, 2, 2, 1, 0, 0, 2, 2, 1, 1, 2, 2, 2, 1, 0]

#guard extractedSideArity? holLightEvidenceProfile holLightEqKernel ==
  some [0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0]

#guard extractedEvidenceArity? hol4EvidenceProfile hol4LcfKernel ==
  some [0, 0, 0, 1, 1, 2, 1, 1]

#guard extractedSideArity? hol4EvidenceProfile hol4LcfKernel ==
  some [1, 0, 1, 1, 1, 0, 0, 0]

#guard (relationFactRules holLightEvidenceProfile holLightEqKernel
  holLightLogic.1).length == 3
#guard (relationFactRules hol4EvidenceProfile hol4LcfKernel
  hol4Logic.1).length == 3

#guard holLightInferenceDefinition?.map (·.rules.length) == some 18
#guard hol4InferenceDefinition?.map (·.rules.length) == some 11

#guard extractedRulesInBindingFragment? holLightEvidenceProfile holLightEqKernel ==
  some true

#guard extractedRulesInBindingFragment? hol4EvidenceProfile hol4LcfKernel ==
  some true

private def app (head : String) (arguments : List Pattern := []) : Pattern :=
  .apply head arguments

private def emptyHyps : Pattern := app "EmptyHyps"
private def hyp (term : Pattern) : Pattern := app "Hyp" [term]
private def removeHyp (term hypotheses : Pattern) : Pattern :=
  app "RemoveHyp" [term, hypotheses]
private def unionHyps (left right : Pattern) : Pattern :=
  app "UnionHyps" [left, right]
private def seq (hypotheses conclusion : Pattern) : Pattern :=
  app "Seq" [hypotheses, conclusion]
private def eqTerm (left right : Pattern) : Pattern := app "Eq" [left, right]
private def impTerm (left right : Pattern) : Pattern := app "Imp" [left, right]

private def ruleInstance (id : String) (arguments : List Pattern := []) : RuleInstance :=
  { ruleId := { value := id }, arguments }

private def node (id : String) (arguments : List Pattern := [])
    (children : List RawProof := []) : RawProof :=
  .node (ruleInstance id arguments) children

private def factProof? (definition : CalculusLanguageDef) (goal : Pattern) : Option RawProof := do
  let rule ← definition.rules.find? fun candidate =>
    candidate.metavariables.isEmpty && candidate.premises.isEmpty &&
      decide (candidate.conclusion = goal)
  pure <| node rule.id.value

private def relationFactProof? (profile : EvidenceProfile)
    (definition : CalculusLanguageDef) (relation : String) (arguments : List Pattern) :
    Option RawProof :=
  factProof? definition (profile.relationJudgment relation arguments)

def hol4ImpIdGoal : Pattern :=
  hol4EvidenceProfile.derived
    (seq (removeHyp A (hyp A)) (impTerm A A))

def hol4ImpIdProof? : Option RawProof := do
  let definition ← hol4InferenceDefinition?
  let boolA ← relationFactProof? hol4EvidenceProfile definition "isBool" [A]
  let assumeA := node "H4_ASSUME" [A] [boolA]
  pure <| node "H4_DISCH" [A, hyp A, A] [assumeA, boolA]

def hol4ImpIdMissingChildProof? : Option RawProof := do
  let definition ← hol4InferenceDefinition?
  let boolA ← relationFactProof? hol4EvidenceProfile definition "isBool" [A]
  let assumeA := node "H4_ASSUME" [A] [boolA]
  pure <| node "H4_DISCH" [A, hyp A, A] [assumeA]

def hol4ImpIdReorderedProof? : Option RawProof := do
  let definition ← hol4InferenceDefinition?
  let boolA ← relationFactProof? hol4EvidenceProfile definition "isBool" [A]
  let assumeA := node "H4_ASSUME" [A] [boolA]
  pure <| node "H4_DISCH" [A, hyp A, A] [boolA, assumeA]

def hol4ImpIdExtraChildProof? : Option RawProof := do
  let definition ← hol4InferenceDefinition?
  let boolA ← relationFactProof? hol4EvidenceProfile definition "isBool" [A]
  let assumeA := node "H4_ASSUME" [A] [boolA]
  pure <| node "H4_DISCH" [A, hyp A, A] [assumeA, boolA, boolA]

def hol4ImpIdWrongRuleProof? : Option RawProof := do
  let definition ← hol4InferenceDefinition?
  let boolA ← relationFactProof? hol4EvidenceProfile definition "isBool" [A]
  pure <| node "H4_ASSUME" [A] [boolA]

def hol4ImpIdChecks : Option (Bool × Bool × Bool × Bool × Bool) := do
  let definition ← hol4ValidatedDefinition?
  let positive ← hol4ImpIdProof?
  let missing ← hol4ImpIdMissingChildProof?
  let reordered ← hol4ImpIdReorderedProof?
  let extra ← hol4ImpIdExtraChildProof?
  let wrongRule ← hol4ImpIdWrongRuleProof?
  pure
    (checkRaw definition hol4ImpIdGoal positive,
      checkRaw definition hol4ImpIdGoal missing,
      checkRaw definition hol4ImpIdGoal reordered,
      checkRaw definition hol4ImpIdGoal extra,
      checkRaw definition hol4ImpIdGoal wrongRule)

#guard hol4ImpIdChecks == some (true, false, false, false, false)

def holLightSelfImpGoal : Pattern :=
  holLightEvidenceProfile.derived (seq emptyHyps (impTerm A A))

def holLightSelfImpProof? : Option RawProof := do
  let definition ← holLightInferenceDefinition?
  let boolA ← relationFactProof? holLightEvidenceProfile definition "isBool" [A]
  let boolAnd ←
    relationFactProof? holLightEvidenceProfile definition "isBool" [AndAA]
  let assumeA := node "HL_ASSUME" [A] [boolA]
  let assumeAnd := node "HL_ASSUME" [AndAA] [boolAnd]
  let conj := node "HL_CONJ_AA_REPLAY" [] [assumeA, assumeA, boolA]
  let conjunct := node "HL_CONJUNCT1_AA_REPLAY" [] [assumeAnd, boolAnd]
  let deduct := node "HL_DEDUCT_ANTISYM_SINGLETON" [A, AndAA] [conj, conjunct]
  let impDef := node "HL_IMP_DEF_AA"
  pure <| node "HL_EQ_MP_EMPTY" [eqTerm AndAA A, impTerm A A] [impDef, deduct]

def holLightSelfImpReorderedProof? : Option RawProof := do
  let definition ← holLightInferenceDefinition?
  let boolA ← relationFactProof? holLightEvidenceProfile definition "isBool" [A]
  let boolAnd ←
    relationFactProof? holLightEvidenceProfile definition "isBool" [AndAA]
  let assumeA := node "HL_ASSUME" [A] [boolA]
  let assumeAnd := node "HL_ASSUME" [AndAA] [boolAnd]
  let conj := node "HL_CONJ_AA_REPLAY" [] [assumeA, assumeA, boolA]
  let conjunct := node "HL_CONJUNCT1_AA_REPLAY" [] [assumeAnd, boolAnd]
  let deduct := node "HL_DEDUCT_ANTISYM_SINGLETON" [A, AndAA] [conj, conjunct]
  let impDef := node "HL_IMP_DEF_AA"
  pure <| node "HL_EQ_MP_EMPTY" [eqTerm AndAA A, impTerm A A] [deduct, impDef]

def holLightSelfImpMissingChildProof? : Option RawProof := do
  let definition ← holLightInferenceDefinition?
  let boolA ← relationFactProof? holLightEvidenceProfile definition "isBool" [A]
  let boolAnd ←
    relationFactProof? holLightEvidenceProfile definition "isBool" [AndAA]
  let assumeA := node "HL_ASSUME" [A] [boolA]
  let assumeAnd := node "HL_ASSUME" [AndAA] [boolAnd]
  let conj := node "HL_CONJ_AA_REPLAY" [] [assumeA, assumeA, boolA]
  let conjunct := node "HL_CONJUNCT1_AA_REPLAY" [] [assumeAnd, boolAnd]
  let deduct := node "HL_DEDUCT_ANTISYM_SINGLETON" [A, AndAA] [conj, conjunct]
  pure <| node "HL_EQ_MP_EMPTY" [eqTerm AndAA A, impTerm A A] [deduct]

def holLightSelfImpExtraChildProof? : Option RawProof := do
  let definition ← holLightInferenceDefinition?
  let boolA ← relationFactProof? holLightEvidenceProfile definition "isBool" [A]
  let boolAnd ←
    relationFactProof? holLightEvidenceProfile definition "isBool" [AndAA]
  let assumeA := node "HL_ASSUME" [A] [boolA]
  let assumeAnd := node "HL_ASSUME" [AndAA] [boolAnd]
  let conj := node "HL_CONJ_AA_REPLAY" [] [assumeA, assumeA, boolA]
  let conjunct := node "HL_CONJUNCT1_AA_REPLAY" [] [assumeAnd, boolAnd]
  let deduct := node "HL_DEDUCT_ANTISYM_SINGLETON" [A, AndAA] [conj, conjunct]
  let impDef := node "HL_IMP_DEF_AA"
  pure <|
    node "HL_EQ_MP_EMPTY" [eqTerm AndAA A, impTerm A A] [impDef, deduct, impDef]

def holLightSelfImpWrongRuleProof? : Option RawProof := do
  let definition ← holLightInferenceDefinition?
  let boolA ← relationFactProof? holLightEvidenceProfile definition "isBool" [A]
  pure <| node "HL_ASSUME" [A] [boolA]

def holLightSelfImpChecks : Option (Bool × Bool × Bool × Bool × Bool) := do
  let definition ← holLightValidatedDefinition?
  let positive ← holLightSelfImpProof?
  let reordered ← holLightSelfImpReorderedProof?
  let missing ← holLightSelfImpMissingChildProof?
  let extra ← holLightSelfImpExtraChildProof?
  let wrongRule ← holLightSelfImpWrongRuleProof?
  pure
    (checkRaw definition holLightSelfImpGoal positive,
      checkRaw definition holLightSelfImpGoal reordered,
      checkRaw definition holLightSelfImpGoal missing,
      checkRaw definition holLightSelfImpGoal extra,
      checkRaw definition holLightSelfImpGoal wrongRule)

#guard holLightSelfImpChecks == some (true, false, false, false, false)


end Mettapedia.GSLT.LanguageDef.HOLInferenceExtraction
