import Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalNamingLanguageDef

/-!
# Exact execution of authored definitional naming

This module connects the authored linear naming LanguageDef to an independent
syntax-directed derivation.  The derivation does not invoke the rewrite
engine.  Its execution theorem proves exact singleton reduction, preserving
order and multiplicity.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalNamingAgreement

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalNamingLanguageDef

local macro "naming_root" : tactic =>
  `(tactic|
    simp [rewriteAt,
      TptpFofDefinitionalNamingLanguageDef.language_rewrites,
      TptpFofDefinitionalNamingLanguageDef.rewrites,
      variablesRewrites, leafNameRewrites, connectiveNameRewrites,
      reverseRewrites, openRewrites,
      applyRuleUsing, matchPatternForRule_eq_syntactic,
      premisesUsing, premiseStepUsing,
      TptpFofDefinitionalNamingLanguageDef.mkRule,
      TptpFofDefinitionalNamingLanguageDef.congruence,
      TptpFofDefinitionalNamingLanguageDef.leafNameRule,
      TptpFofDefinitionalNamingLanguageDef.connectiveNameRule,
      TptpFofDefinitionalNamingLanguageDef.openMatrixRule,
      variablesRequest, variablesResult, nameRequest, nameResult,
      reverseDefinitionsRequest, reverseDefinitionsResult,
      reverseIntroducedRequest, reverseIntroducedResult,
      openRequest, openResult, indexZero, indexSucc,
      TptpFofDefinitionalNamingLanguageDef.a,
      TptpFofDefinitionalNamingLanguageDef.v,
      TptpFofSkolemLanguageDef.termVariable,
      TptpFofSkolemLanguageDef.termsNil,
      TptpFofSkolemLanguageDef.termsCons,
      TptpFofSkolemLanguageDef.verum,
      TptpFofSkolemLanguageDef.falsum,
      TptpFofSkolemLanguageDef.positive,
      TptpFofSkolemLanguageDef.negative,
      TptpFofSkolemLanguageDef.equal,
      TptpFofSkolemLanguageDef.notEqual,
      TptpFofSkolemLanguageDef.and,
      TptpFofSkolemLanguageDef.or,
      TptpFofSkolemLanguageDef.all,
      TptpFofSkolemLanguageDef.a,
      TptpFofDefinitionalCnfLanguageDef.refVerum,
      TptpFofDefinitionalCnfLanguageDef.refFalsum,
      TptpFofDefinitionalCnfLanguageDef.refOriginalPositive,
      TptpFofDefinitionalCnfLanguageDef.refOriginalNegative,
      TptpFofDefinitionalCnfLanguageDef.refEqual,
      TptpFofDefinitionalCnfLanguageDef.refNotEqual,
      TptpFofDefinitionalCnfLanguageDef.refDefinedPositive,
      TptpFofDefinitionalCnfLanguageDef.definitionAnd,
      TptpFofDefinitionalCnfLanguageDef.definitionOr,
      TptpFofDefinitionalCnfLanguageDef.definitionsNil,
      TptpFofDefinitionalCnfLanguageDef.definitionsCons,
      TptpFofDefinitionalCnfLanguageDef.introducedPredicate,
      TptpFofDefinitionalCnfLanguageDef.introducedNil,
      TptpFofDefinitionalCnfLanguageDef.introducedCons,
      TptpFofDefinitionalCnfLanguageDef.namedOutput,
      TptpFofDefinitionalCnfLanguageDef.a,
      matchPattern, matchArgs, mergeBindings,
      applyBindingsForRule, applyBindings])

local macro "naming_root_using_all" : tactic =>
  `(tactic|
    simp only [variablesRequest, variablesResult, nameRequest, nameResult,
      reverseDefinitionsRequest, reverseDefinitionsResult,
      reverseIntroducedRequest, reverseIntroducedResult,
      openRequest, openResult, indexZero, indexSucc,
      TptpFofDefinitionalNamingLanguageDef.a,
      TptpFofSkolemLanguageDef.termVariable,
      TptpFofSkolemLanguageDef.termsNil,
      TptpFofSkolemLanguageDef.termsCons,
      TptpFofSkolemLanguageDef.verum,
      TptpFofSkolemLanguageDef.falsum,
      TptpFofSkolemLanguageDef.positive,
      TptpFofSkolemLanguageDef.negative,
      TptpFofSkolemLanguageDef.equal,
      TptpFofSkolemLanguageDef.notEqual,
      TptpFofSkolemLanguageDef.and,
      TptpFofSkolemLanguageDef.or,
      TptpFofSkolemLanguageDef.all,
      TptpFofSkolemLanguageDef.a,
      TptpFofDefinitionalCnfLanguageDef.refVerum,
      TptpFofDefinitionalCnfLanguageDef.refFalsum,
      TptpFofDefinitionalCnfLanguageDef.refOriginalPositive,
      TptpFofDefinitionalCnfLanguageDef.refOriginalNegative,
      TptpFofDefinitionalCnfLanguageDef.refEqual,
      TptpFofDefinitionalCnfLanguageDef.refNotEqual,
      TptpFofDefinitionalCnfLanguageDef.refDefinedPositive,
      TptpFofDefinitionalCnfLanguageDef.definitionAnd,
      TptpFofDefinitionalCnfLanguageDef.definitionOr,
      TptpFofDefinitionalCnfLanguageDef.definitionsNil,
      TptpFofDefinitionalCnfLanguageDef.definitionsCons,
      TptpFofDefinitionalCnfLanguageDef.introducedPredicate,
      TptpFofDefinitionalCnfLanguageDef.introducedNil,
      TptpFofDefinitionalCnfLanguageDef.introducedCons,
      TptpFofDefinitionalCnfLanguageDef.namedOutput,
      TptpFofDefinitionalCnfLanguageDef.a] at * <;>
    simp (config := { maxSteps := 1000000 }) [*, rewriteAt,
      TptpFofDefinitionalNamingLanguageDef.language_rewrites,
      TptpFofDefinitionalNamingLanguageDef.rewrites,
      variablesRewrites, leafNameRewrites, connectiveNameRewrites,
      reverseRewrites, openRewrites,
      applyRuleUsing, matchPatternForRule_eq_syntactic,
      premisesUsing, premiseStepUsing,
      TptpFofDefinitionalNamingLanguageDef.mkRule,
      TptpFofDefinitionalNamingLanguageDef.congruence,
      TptpFofDefinitionalNamingLanguageDef.leafNameRule,
      TptpFofDefinitionalNamingLanguageDef.connectiveNameRule,
      TptpFofDefinitionalNamingLanguageDef.openMatrixRule,
      variablesRequest, variablesResult, nameRequest, nameResult,
      reverseDefinitionsRequest, reverseDefinitionsResult,
      reverseIntroducedRequest, reverseIntroducedResult,
      openRequest, openResult, indexZero, indexSucc,
      TptpFofDefinitionalNamingLanguageDef.a,
      TptpFofDefinitionalNamingLanguageDef.v,
      TptpFofSkolemLanguageDef.termVariable,
      TptpFofSkolemLanguageDef.termsNil,
      TptpFofSkolemLanguageDef.termsCons,
      TptpFofSkolemLanguageDef.verum,
      TptpFofSkolemLanguageDef.falsum,
      TptpFofSkolemLanguageDef.positive,
      TptpFofSkolemLanguageDef.negative,
      TptpFofSkolemLanguageDef.equal,
      TptpFofSkolemLanguageDef.notEqual,
      TptpFofSkolemLanguageDef.and,
      TptpFofSkolemLanguageDef.or,
      TptpFofSkolemLanguageDef.all,
      TptpFofSkolemLanguageDef.a,
      TptpFofDefinitionalCnfLanguageDef.refVerum,
      TptpFofDefinitionalCnfLanguageDef.refFalsum,
      TptpFofDefinitionalCnfLanguageDef.refOriginalPositive,
      TptpFofDefinitionalCnfLanguageDef.refOriginalNegative,
      TptpFofDefinitionalCnfLanguageDef.refEqual,
      TptpFofDefinitionalCnfLanguageDef.refNotEqual,
      TptpFofDefinitionalCnfLanguageDef.refDefinedPositive,
      TptpFofDefinitionalCnfLanguageDef.definitionAnd,
      TptpFofDefinitionalCnfLanguageDef.definitionOr,
      TptpFofDefinitionalCnfLanguageDef.definitionsNil,
      TptpFofDefinitionalCnfLanguageDef.definitionsCons,
      TptpFofDefinitionalCnfLanguageDef.introducedPredicate,
      TptpFofDefinitionalCnfLanguageDef.introducedNil,
      TptpFofDefinitionalCnfLanguageDef.introducedCons,
      TptpFofDefinitionalCnfLanguageDef.namedOutput,
      TptpFofDefinitionalCnfLanguageDef.a,
      matchPattern, matchArgs, mergeBindings,
      applyBindingsForRule, applyBindings])

/-! ## Independent pattern-level derivation -/

inductive MatrixPattern : Pattern → Type
  | verum : MatrixPattern TptpFofSkolemLanguageDef.verum
  | falsum : MatrixPattern TptpFofSkolemLanguageDef.falsum
  | positive (relation arguments : Pattern) :
      MatrixPattern (TptpFofSkolemLanguageDef.positive relation arguments)
  | negative (relation arguments : Pattern) :
      MatrixPattern (TptpFofSkolemLanguageDef.negative relation arguments)
  | equal (left right : Pattern) :
      MatrixPattern (TptpFofSkolemLanguageDef.equal left right)
  | notEqual (left right : Pattern) :
      MatrixPattern (TptpFofSkolemLanguageDef.notEqual left right)
  | and (left right : Pattern) :
      MatrixPattern (TptpFofSkolemLanguageDef.and left right)
  | or (left right : Pattern) :
      MatrixPattern (TptpFofSkolemLanguageDef.or left right)

inductive Derivation : Pattern → Pattern → Type
  | variablesZero (next : Pattern) :
      Derivation (variablesRequest indexZero next)
        (variablesResult indexZero next TptpFofSkolemLanguageDef.termsNil)
  | variablesSucc {remaining next tail : Pattern}
      (tailDerivation : Derivation
        (variablesRequest remaining (indexSucc next))
        (variablesResult remaining (indexSucc next) tail)) :
      Derivation (variablesRequest (indexSucc remaining) next)
        (variablesResult (indexSucc remaining) next
          (TptpFofSkolemLanguageDef.termsCons
            (TptpFofSkolemLanguageDef.termVariable next) tail))
  | nameVerum (depth frontier definitions introduced : Pattern) :
      Derivation
        (nameRequest depth frontier TptpFofSkolemLanguageDef.verum
          definitions introduced)
        (nameResult depth frontier TptpFofSkolemLanguageDef.verum
          TptpFofDefinitionalCnfLanguageDef.refVerum frontier
          definitions introduced)
  | nameFalsum (depth frontier definitions introduced : Pattern) :
      Derivation
        (nameRequest depth frontier TptpFofSkolemLanguageDef.falsum
          definitions introduced)
        (nameResult depth frontier TptpFofSkolemLanguageDef.falsum
          TptpFofDefinitionalCnfLanguageDef.refFalsum frontier
          definitions introduced)
  | namePositive (depth frontier relation arguments definitions introduced : Pattern) :
      Derivation
        (nameRequest depth frontier
          (TptpFofSkolemLanguageDef.positive relation arguments)
          definitions introduced)
        (nameResult depth frontier
          (TptpFofSkolemLanguageDef.positive relation arguments)
          (TptpFofDefinitionalCnfLanguageDef.refOriginalPositive
            relation arguments)
          frontier definitions introduced)
  | nameNegative (depth frontier relation arguments definitions introduced : Pattern) :
      Derivation
        (nameRequest depth frontier
          (TptpFofSkolemLanguageDef.negative relation arguments)
          definitions introduced)
        (nameResult depth frontier
          (TptpFofSkolemLanguageDef.negative relation arguments)
          (TptpFofDefinitionalCnfLanguageDef.refOriginalNegative
            relation arguments)
          frontier definitions introduced)
  | nameEqual (depth frontier left right definitions introduced : Pattern) :
      Derivation
        (nameRequest depth frontier
          (TptpFofSkolemLanguageDef.equal left right) definitions introduced)
        (nameResult depth frontier
          (TptpFofSkolemLanguageDef.equal left right)
          (TptpFofDefinitionalCnfLanguageDef.refEqual left right)
          frontier definitions introduced)
  | nameNotEqual (depth frontier left right definitions introduced : Pattern) :
      Derivation
        (nameRequest depth frontier
          (TptpFofSkolemLanguageDef.notEqual left right)
          definitions introduced)
        (nameResult depth frontier
          (TptpFofSkolemLanguageDef.notEqual left right)
          (TptpFofDefinitionalCnfLanguageDef.refNotEqual left right)
          frontier definitions introduced)
  | nameAnd {depth frontier left right definitions introduced
      leftRoot leftNext leftDefinitions leftIntroduced
      rightRoot rightNext rightDefinitions rightIntroduced arguments : Pattern}
      (leftDerivation : Derivation
        (nameRequest depth frontier left definitions introduced)
        (nameResult depth frontier left leftRoot leftNext leftDefinitions
          leftIntroduced))
      (rightDerivation : Derivation
        (nameRequest depth leftNext right leftDefinitions leftIntroduced)
        (nameResult depth leftNext right rightRoot rightNext rightDefinitions
          rightIntroduced))
      (variablesDerivation : Derivation
        (variablesRequest depth indexZero)
        (variablesResult depth indexZero arguments)) :
      Derivation
        (nameRequest depth frontier
          (TptpFofSkolemLanguageDef.and left right) definitions introduced)
        (nameResult depth frontier
          (TptpFofSkolemLanguageDef.and left right)
          (TptpFofDefinitionalCnfLanguageDef.refDefinedPositive
            rightNext arguments)
          (indexSucc rightNext)
          (TptpFofDefinitionalCnfLanguageDef.definitionsCons
            (TptpFofDefinitionalCnfLanguageDef.definitionAnd rightNext
              (TptpFofSkolemLanguageDef.and left right) leftRoot rightRoot)
            rightDefinitions)
          (TptpFofDefinitionalCnfLanguageDef.introducedCons
            (TptpFofDefinitionalCnfLanguageDef.introducedPredicate
              rightNext depth)
            rightIntroduced))
  | nameOr {depth frontier left right definitions introduced
      leftRoot leftNext leftDefinitions leftIntroduced
      rightRoot rightNext rightDefinitions rightIntroduced arguments : Pattern}
      (leftDerivation : Derivation
        (nameRequest depth frontier left definitions introduced)
        (nameResult depth frontier left leftRoot leftNext leftDefinitions
          leftIntroduced))
      (rightDerivation : Derivation
        (nameRequest depth leftNext right leftDefinitions leftIntroduced)
        (nameResult depth leftNext right rightRoot rightNext rightDefinitions
          rightIntroduced))
      (variablesDerivation : Derivation
        (variablesRequest depth indexZero)
        (variablesResult depth indexZero arguments)) :
      Derivation
        (nameRequest depth frontier
          (TptpFofSkolemLanguageDef.or left right) definitions introduced)
        (nameResult depth frontier
          (TptpFofSkolemLanguageDef.or left right)
          (TptpFofDefinitionalCnfLanguageDef.refDefinedPositive
            rightNext arguments)
          (indexSucc rightNext)
          (TptpFofDefinitionalCnfLanguageDef.definitionsCons
            (TptpFofDefinitionalCnfLanguageDef.definitionOr rightNext
              (TptpFofSkolemLanguageDef.or left right) leftRoot rightRoot)
            rightDefinitions)
          (TptpFofDefinitionalCnfLanguageDef.introducedCons
            (TptpFofDefinitionalCnfLanguageDef.introducedPredicate
              rightNext depth)
            rightIntroduced))
  | reverseDefinitionsNil (accumulator : Pattern) :
      Derivation
        (reverseDefinitionsRequest
          TptpFofDefinitionalCnfLanguageDef.definitionsNil accumulator)
        (reverseDefinitionsResult
          TptpFofDefinitionalCnfLanguageDef.definitionsNil accumulator
          accumulator)
  | reverseDefinitionsCons {head tail accumulator target : Pattern}
      (tailDerivation : Derivation
        (reverseDefinitionsRequest tail
          (TptpFofDefinitionalCnfLanguageDef.definitionsCons
            head accumulator))
        (reverseDefinitionsResult tail
          (TptpFofDefinitionalCnfLanguageDef.definitionsCons
            head accumulator) target)) :
      Derivation
        (reverseDefinitionsRequest
          (TptpFofDefinitionalCnfLanguageDef.definitionsCons head tail)
          accumulator)
        (reverseDefinitionsResult
          (TptpFofDefinitionalCnfLanguageDef.definitionsCons head tail)
          accumulator target)
  | reverseIntroducedNil (accumulator : Pattern) :
      Derivation
        (reverseIntroducedRequest
          TptpFofDefinitionalCnfLanguageDef.introducedNil accumulator)
        (reverseIntroducedResult
          TptpFofDefinitionalCnfLanguageDef.introducedNil accumulator
          accumulator)
  | reverseIntroducedCons {head tail accumulator target : Pattern}
      (tailDerivation : Derivation
        (reverseIntroducedRequest tail
          (TptpFofDefinitionalCnfLanguageDef.introducedCons head accumulator))
        (reverseIntroducedResult tail
          (TptpFofDefinitionalCnfLanguageDef.introducedCons head accumulator)
          target)) :
      Derivation
        (reverseIntroducedRequest
          (TptpFofDefinitionalCnfLanguageDef.introducedCons head tail)
          accumulator)
        (reverseIntroducedResult
          (TptpFofDefinitionalCnfLanguageDef.introducedCons head tail)
          accumulator target)
  | openAll {depth frontier body target : Pattern}
      (bodyDerivation : Derivation
        (openRequest (indexSucc depth) frontier body)
        (openResult (indexSucc depth) frontier body target)) :
      Derivation
        (openRequest depth frontier (TptpFofSkolemLanguageDef.all body))
        (openResult depth frontier (TptpFofSkolemLanguageDef.all body) target)
  | openMatrix {depth frontier source root next reverseDefinitions
      reverseIntroduced definitions introduced : Pattern}
      (shape : MatrixPattern source)
      (nameDerivation : Derivation
        (nameRequest depth frontier source
          TptpFofDefinitionalCnfLanguageDef.definitionsNil
          TptpFofDefinitionalCnfLanguageDef.introducedNil)
        (nameResult depth frontier source root next reverseDefinitions
          reverseIntroduced))
      (definitionsDerivation : Derivation
        (reverseDefinitionsRequest reverseDefinitions
          TptpFofDefinitionalCnfLanguageDef.definitionsNil)
        (reverseDefinitionsResult reverseDefinitions
          TptpFofDefinitionalCnfLanguageDef.definitionsNil definitions))
      (introducedDerivation : Derivation
        (reverseIntroducedRequest reverseIntroduced
          TptpFofDefinitionalCnfLanguageDef.introducedNil)
        (reverseIntroducedResult reverseIntroduced
          TptpFofDefinitionalCnfLanguageDef.introducedNil introduced)) :
      Derivation (openRequest depth frontier source)
        (openResult depth frontier source
          (TptpFofDefinitionalCnfLanguageDef.namedOutput
            root next definitions introduced))

def Derivation.height : {source target : Pattern} →
    Derivation source target → Nat
  | _, _, .variablesZero _
  | _, _, .nameVerum _ _ _ _
  | _, _, .nameFalsum _ _ _ _
  | _, _, .namePositive _ _ _ _ _ _
  | _, _, .nameNegative _ _ _ _ _ _
  | _, _, .nameEqual _ _ _ _ _ _
  | _, _, .nameNotEqual _ _ _ _ _ _
  | _, _, .reverseDefinitionsNil _
  | _, _, .reverseIntroducedNil _ => 1
  | _, _, .variablesSucc tail
  | _, _, .reverseDefinitionsCons tail
  | _, _, .reverseIntroducedCons tail
  | _, _, .openAll tail => tail.height + 1
  | _, _, .nameAnd left right vector
  | _, _, .nameOr left right vector =>
      max (max left.height right.height) vector.height + 1
  | _, _, .openMatrix _ name definitions introduced =>
      max (max name.height definitions.height) introduced.height + 1

set_option maxHeartbeats 5000000 in
theorem Derivation.rewriteAt_exact {source target : Pattern}
    (derivation : Derivation source target) (fuel : Nat)
    (enough : derivation.height ≤ fuel) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofDefinitionalNamingLanguageDef.language fuel source = [target] := by
  induction derivation generalizing fuel with
  | variablesZero next =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel => naming_root
  | variablesSucc tail tailHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have childEnough : tail.height ≤ fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          have childExact := tailHypothesis fuel childEnough
          naming_root_using_all
  | nameVerum | nameFalsum | namePositive | nameNegative | nameEqual |
      nameNotEqual | reverseDefinitionsNil | reverseIntroducedNil =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel => naming_root
  | nameAnd left right vector leftHypothesis rightHypothesis
      vectorHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have maximumEnough :
              max (max left.height right.height) vector.height ≤ fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          have leftExact := leftHypothesis fuel
            ((Nat.le_max_left _ _).trans
              ((Nat.le_max_left _ _).trans maximumEnough))
          have rightExact := rightHypothesis fuel
            ((Nat.le_max_right _ _).trans
              ((Nat.le_max_left _ _).trans maximumEnough))
          have vectorExact := vectorHypothesis fuel
            ((Nat.le_max_right _ _).trans maximumEnough)
          naming_root_using_all
  | nameOr left right vector leftHypothesis rightHypothesis
      vectorHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have maximumEnough :
              max (max left.height right.height) vector.height ≤ fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          have leftExact := leftHypothesis fuel
            ((Nat.le_max_left _ _).trans
              ((Nat.le_max_left _ _).trans maximumEnough))
          have rightExact := rightHypothesis fuel
            ((Nat.le_max_right _ _).trans
              ((Nat.le_max_left _ _).trans maximumEnough))
          have vectorExact := vectorHypothesis fuel
            ((Nat.le_max_right _ _).trans maximumEnough)
          naming_root_using_all
  | reverseDefinitionsCons tail tailHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have childEnough : tail.height ≤ fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          have childExact := tailHypothesis fuel childEnough
          naming_root_using_all
  | reverseIntroducedCons tail tailHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have childEnough : tail.height ≤ fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          have childExact := tailHypothesis fuel childEnough
          naming_root_using_all
  | openAll tail tailHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have childEnough : tail.height ≤ fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          have childExact := tailHypothesis fuel childEnough
          naming_root_using_all
  | openMatrix shape name definitions introduced nameHypothesis
      definitionsHypothesis introducedHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have maximumEnough :
              max (max name.height definitions.height) introduced.height ≤ fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          have nameExact := nameHypothesis fuel
            ((Nat.le_max_left _ _).trans
              ((Nat.le_max_left _ _).trans maximumEnough))
          have definitionsExact := definitionsHypothesis fuel
            ((Nat.le_max_right _ _).trans
              ((Nat.le_max_left _ _).trans maximumEnough))
          have introducedExact := introducedHypothesis fuel
            ((Nat.le_max_right _ _).trans maximumEnough)
          cases shape <;> naming_root_using_all

theorem Derivation.no_invention {source target invented : Pattern}
    (derivation : Derivation source target) (fuel : Nat)
    (enough : derivation.height ≤ fuel)
    (membership : invented ∈ rewriteAt
      (engineBasePremises RelationEnv.empty)
      TptpFofDefinitionalNamingLanguageDef.language fuel source) :
    invented = target := by
  rw [derivation.rewriteAt_exact fuel enough] at membership
  simpa using membership

theorem variablesZero_rewriteAt_exact (next : Pattern) (fuel : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofDefinitionalNamingLanguageDef.language (fuel + 1)
      (variablesRequest indexZero next) =
    [variablesResult indexZero next TptpFofSkolemLanguageDef.termsNil] := by
  naming_root

theorem universalName_has_no_reduct
    (depth frontier body definitions introduced : Pattern) (fuel : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofDefinitionalNamingLanguageDef.language fuel
      (nameRequest depth frontier (TptpFofSkolemLanguageDef.all body)
        definitions introduced) = [] := by
  cases fuel <;> naming_root

theorem nestedUniversalName_has_no_reduct
    (depth frontier body definitions introduced : Pattern) (fuel : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofDefinitionalNamingLanguageDef.language fuel
      (nameRequest depth frontier
        (TptpFofSkolemLanguageDef.and
          (TptpFofSkolemLanguageDef.all body)
          TptpFofSkolemLanguageDef.verum)
        definitions introduced) = [] := by
  cases fuel with
  | zero => naming_root
  | succ fuel =>
      have childExact := universalName_has_no_reduct depth frontier body
        definitions introduced fuel
      naming_root_using_all

theorem nestedUniversal_open_has_no_reduct
    (depth frontier body : Pattern) (fuel : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofDefinitionalNamingLanguageDef.language fuel
      (openRequest depth frontier
        (TptpFofSkolemLanguageDef.and
          (TptpFofSkolemLanguageDef.all body)
          TptpFofSkolemLanguageDef.verum)) = [] := by
  cases fuel with
  | zero => naming_root
  | succ fuel =>
      have childExact := nestedUniversalName_has_no_reduct depth frontier body
        TptpFofDefinitionalCnfLanguageDef.definitionsNil
        TptpFofDefinitionalCnfLanguageDef.introducedNil fuel
      naming_root_using_all

#print axioms variablesZero_rewriteAt_exact
#print axioms universalName_has_no_reduct
#print axioms nestedUniversalName_has_no_reduct
#print axioms nestedUniversal_open_has_no_reduct
#print axioms Derivation.rewriteAt_exact
#print axioms Derivation.no_invention

end Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalNamingAgreement
