import Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalCnfGenerationLanguageDef

/-!
# Exact execution of authored definitional CNF generation

This module connects the authored CNF-generation LanguageDef to an independent
pattern-level derivation.  The derivation does not invoke the rewrite engine.
Its execution theorem proves exact singleton reduction, preserving clause
order and multiplicity.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalCnfGenerationAgreement

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalCnfGenerationLanguageDef

local macro "generation_root" : tactic =>
  `(tactic|
    simp [rewriteAt,
      TptpFofDefinitionalCnfGenerationLanguageDef.language_rewrites,
      TptpFofDefinitionalCnfGenerationLanguageDef.rewrites,
      variablesRewrites, negateRewrites, clausesRewrites, generateRewrites,
      applyRuleUsing, matchPatternForRule_eq_syntactic,
      premisesUsing, premiseStepUsing,
      TptpFofDefinitionalCnfGenerationLanguageDef.mkRule,
      TptpFofDefinitionalCnfGenerationLanguageDef.congruence,
      TptpFofDefinitionalCnfGenerationLanguageDef.negateRule,
      TptpFofDefinitionalCnfGenerationLanguageDef.definitionRule_left,
      variablesRequest, variablesResult, negateRequest, negateResult,
      clausesRequest, clausesResult, generateRequest, generateResult,
      indexZero, indexSucc, unitClause, binaryClause, ternaryClause,
      prependThree, TptpFofDefinitionalCnfGenerationLanguageDef.a,
      TptpFofDefinitionalCnfGenerationLanguageDef.v,
      TptpFofSkolemLanguageDef.termVariable,
      TptpFofSkolemLanguageDef.termsNil,
      TptpFofSkolemLanguageDef.termsCons,
      TptpFofSkolemLanguageDef.a,
      TptpFofDefinitionalCnfLanguageDef.refVerum,
      TptpFofDefinitionalCnfLanguageDef.refFalsum,
      TptpFofDefinitionalCnfLanguageDef.refOriginalPositive,
      TptpFofDefinitionalCnfLanguageDef.refOriginalNegative,
      TptpFofDefinitionalCnfLanguageDef.refEqual,
      TptpFofDefinitionalCnfLanguageDef.refNotEqual,
      TptpFofDefinitionalCnfLanguageDef.refDefinedPositive,
      TptpFofDefinitionalCnfLanguageDef.refDefinedNegative,
      TptpFofDefinitionalCnfLanguageDef.definitionAnd,
      TptpFofDefinitionalCnfLanguageDef.definitionOr,
      TptpFofDefinitionalCnfLanguageDef.definitionsNil,
      TptpFofDefinitionalCnfLanguageDef.definitionsCons,
      TptpFofDefinitionalCnfLanguageDef.introducedPredicate,
      TptpFofDefinitionalCnfLanguageDef.introducedNil,
      TptpFofDefinitionalCnfLanguageDef.introducedCons,
      TptpFofDefinitionalCnfLanguageDef.namedOutput,
      TptpFofDefinitionalCnfLanguageDef.clauseNil,
      TptpFofDefinitionalCnfLanguageDef.clauseCons,
      TptpFofDefinitionalCnfLanguageDef.clausesNil,
      TptpFofDefinitionalCnfLanguageDef.clausesCons,
      TptpFofDefinitionalCnfLanguageDef.cnfOutput,
      TptpFofDefinitionalCnfLanguageDef.a,
      matchPattern, matchArgs, mergeBindings,
      applyBindingsForRule, applyBindings])

local macro "generation_root_using_all" : tactic =>
  `(tactic|
    simp only [variablesRequest, variablesResult, negateRequest, negateResult,
      clausesRequest, clausesResult, generateRequest, generateResult,
      indexZero, indexSucc, unitClause, binaryClause, ternaryClause,
      prependThree, TptpFofDefinitionalCnfGenerationLanguageDef.a,
      TptpFofSkolemLanguageDef.termVariable,
      TptpFofSkolemLanguageDef.termsNil,
      TptpFofSkolemLanguageDef.termsCons,
      TptpFofSkolemLanguageDef.a,
      TptpFofDefinitionalCnfLanguageDef.refVerum,
      TptpFofDefinitionalCnfLanguageDef.refFalsum,
      TptpFofDefinitionalCnfLanguageDef.refOriginalPositive,
      TptpFofDefinitionalCnfLanguageDef.refOriginalNegative,
      TptpFofDefinitionalCnfLanguageDef.refEqual,
      TptpFofDefinitionalCnfLanguageDef.refNotEqual,
      TptpFofDefinitionalCnfLanguageDef.refDefinedPositive,
      TptpFofDefinitionalCnfLanguageDef.refDefinedNegative,
      TptpFofDefinitionalCnfLanguageDef.definitionAnd,
      TptpFofDefinitionalCnfLanguageDef.definitionOr,
      TptpFofDefinitionalCnfLanguageDef.definitionsNil,
      TptpFofDefinitionalCnfLanguageDef.definitionsCons,
      TptpFofDefinitionalCnfLanguageDef.introducedPredicate,
      TptpFofDefinitionalCnfLanguageDef.introducedNil,
      TptpFofDefinitionalCnfLanguageDef.introducedCons,
      TptpFofDefinitionalCnfLanguageDef.namedOutput,
      TptpFofDefinitionalCnfLanguageDef.clauseNil,
      TptpFofDefinitionalCnfLanguageDef.clauseCons,
      TptpFofDefinitionalCnfLanguageDef.clausesNil,
      TptpFofDefinitionalCnfLanguageDef.clausesCons,
      TptpFofDefinitionalCnfLanguageDef.cnfOutput,
      TptpFofDefinitionalCnfLanguageDef.a] at * <;>
    simp (config := { maxSteps := 1000000 }) [*, rewriteAt,
      TptpFofDefinitionalCnfGenerationLanguageDef.language_rewrites,
      TptpFofDefinitionalCnfGenerationLanguageDef.rewrites,
      variablesRewrites, negateRewrites, clausesRewrites, generateRewrites,
      applyRuleUsing, matchPatternForRule_eq_syntactic,
      premisesUsing, premiseStepUsing,
      TptpFofDefinitionalCnfGenerationLanguageDef.mkRule,
      TptpFofDefinitionalCnfGenerationLanguageDef.congruence,
      TptpFofDefinitionalCnfGenerationLanguageDef.negateRule,
      TptpFofDefinitionalCnfGenerationLanguageDef.definitionRule,
      variablesRequest, variablesResult, negateRequest, negateResult,
      clausesRequest, clausesResult, generateRequest, generateResult,
      indexZero, indexSucc, unitClause, binaryClause, ternaryClause,
      prependThree, TptpFofDefinitionalCnfGenerationLanguageDef.a,
      TptpFofDefinitionalCnfGenerationLanguageDef.v,
      TptpFofSkolemLanguageDef.termVariable,
      TptpFofSkolemLanguageDef.termsNil,
      TptpFofSkolemLanguageDef.termsCons,
      TptpFofSkolemLanguageDef.a,
      TptpFofDefinitionalCnfLanguageDef.refVerum,
      TptpFofDefinitionalCnfLanguageDef.refFalsum,
      TptpFofDefinitionalCnfLanguageDef.refOriginalPositive,
      TptpFofDefinitionalCnfLanguageDef.refOriginalNegative,
      TptpFofDefinitionalCnfLanguageDef.refEqual,
      TptpFofDefinitionalCnfLanguageDef.refNotEqual,
      TptpFofDefinitionalCnfLanguageDef.refDefinedPositive,
      TptpFofDefinitionalCnfLanguageDef.refDefinedNegative,
      TptpFofDefinitionalCnfLanguageDef.definitionAnd,
      TptpFofDefinitionalCnfLanguageDef.definitionOr,
      TptpFofDefinitionalCnfLanguageDef.definitionsNil,
      TptpFofDefinitionalCnfLanguageDef.definitionsCons,
      TptpFofDefinitionalCnfLanguageDef.introducedPredicate,
      TptpFofDefinitionalCnfLanguageDef.introducedNil,
      TptpFofDefinitionalCnfLanguageDef.introducedCons,
      TptpFofDefinitionalCnfLanguageDef.namedOutput,
      TptpFofDefinitionalCnfLanguageDef.clauseNil,
      TptpFofDefinitionalCnfLanguageDef.clauseCons,
      TptpFofDefinitionalCnfLanguageDef.clausesNil,
      TptpFofDefinitionalCnfLanguageDef.clausesCons,
      TptpFofDefinitionalCnfLanguageDef.cnfOutput,
      TptpFofDefinitionalCnfLanguageDef.a,
      matchPattern, matchArgs, mergeBindings,
      applyBindingsForRule, applyBindings])

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
  | negateVerum :
      Derivation (negateRequest TptpFofDefinitionalCnfLanguageDef.refVerum)
        (negateResult TptpFofDefinitionalCnfLanguageDef.refVerum
          TptpFofDefinitionalCnfLanguageDef.refFalsum)
  | negateFalsum :
      Derivation (negateRequest TptpFofDefinitionalCnfLanguageDef.refFalsum)
        (negateResult TptpFofDefinitionalCnfLanguageDef.refFalsum
          TptpFofDefinitionalCnfLanguageDef.refVerum)
  | negateOriginalPositive (relation arguments : Pattern) :
      Derivation
        (negateRequest
          (TptpFofDefinitionalCnfLanguageDef.refOriginalPositive
            relation arguments))
        (negateResult
          (TptpFofDefinitionalCnfLanguageDef.refOriginalPositive
            relation arguments)
          (TptpFofDefinitionalCnfLanguageDef.refOriginalNegative
            relation arguments))
  | negateOriginalNegative (relation arguments : Pattern) :
      Derivation
        (negateRequest
          (TptpFofDefinitionalCnfLanguageDef.refOriginalNegative
            relation arguments))
        (negateResult
          (TptpFofDefinitionalCnfLanguageDef.refOriginalNegative
            relation arguments)
          (TptpFofDefinitionalCnfLanguageDef.refOriginalPositive
            relation arguments))
  | negateEqual (left right : Pattern) :
      Derivation
        (negateRequest
          (TptpFofDefinitionalCnfLanguageDef.refEqual left right))
        (negateResult
          (TptpFofDefinitionalCnfLanguageDef.refEqual left right)
          (TptpFofDefinitionalCnfLanguageDef.refNotEqual left right))
  | negateNotEqual (left right : Pattern) :
      Derivation
        (negateRequest
          (TptpFofDefinitionalCnfLanguageDef.refNotEqual left right))
        (negateResult
          (TptpFofDefinitionalCnfLanguageDef.refNotEqual left right)
          (TptpFofDefinitionalCnfLanguageDef.refEqual left right))
  | negateDefinedPositive (id arguments : Pattern) :
      Derivation
        (negateRequest
          (TptpFofDefinitionalCnfLanguageDef.refDefinedPositive id arguments))
        (negateResult
          (TptpFofDefinitionalCnfLanguageDef.refDefinedPositive id arguments)
          (TptpFofDefinitionalCnfLanguageDef.refDefinedNegative id arguments))
  | negateDefinedNegative (id arguments : Pattern) :
      Derivation
        (negateRequest
          (TptpFofDefinitionalCnfLanguageDef.refDefinedNegative id arguments))
        (negateResult
          (TptpFofDefinitionalCnfLanguageDef.refDefinedNegative id arguments)
          (TptpFofDefinitionalCnfLanguageDef.refDefinedPositive id arguments))
  | clausesNil (root : Pattern) :
      Derivation
        (clausesRequest root TptpFofDefinitionalCnfLanguageDef.definitionsNil
          TptpFofDefinitionalCnfLanguageDef.introducedNil)
        (clausesResult root TptpFofDefinitionalCnfLanguageDef.definitionsNil
          TptpFofDefinitionalCnfLanguageDef.introducedNil
          (TptpFofDefinitionalCnfLanguageDef.clausesCons
            (unitClause root) TptpFofDefinitionalCnfLanguageDef.clausesNil))
  | clausesAnd {root id source left right tail arity introducedTail arguments
      leftNegative rightNegative rest : Pattern}
      (variablesDerivation : Derivation
        (variablesRequest arity indexZero)
        (variablesResult arity indexZero arguments))
      (leftNegation : Derivation (negateRequest left)
        (negateResult left leftNegative))
      (rightNegation : Derivation (negateRequest right)
        (negateResult right rightNegative))
      (tailDerivation : Derivation
        (clausesRequest root tail introducedTail)
        (clausesResult root tail introducedTail rest)) :
      Derivation
        (clausesRequest root
          (TptpFofDefinitionalCnfLanguageDef.definitionsCons
            (TptpFofDefinitionalCnfLanguageDef.definitionAnd
              id source left right) tail)
          (TptpFofDefinitionalCnfLanguageDef.introducedCons
            (TptpFofDefinitionalCnfLanguageDef.introducedPredicate id arity)
            introducedTail))
        (clausesResult root
          (TptpFofDefinitionalCnfLanguageDef.definitionsCons
            (TptpFofDefinitionalCnfLanguageDef.definitionAnd
              id source left right) tail)
          (TptpFofDefinitionalCnfLanguageDef.introducedCons
            (TptpFofDefinitionalCnfLanguageDef.introducedPredicate id arity)
            introducedTail)
          (prependThree
            (binaryClause
              (TptpFofDefinitionalCnfLanguageDef.refDefinedNegative
                id arguments) left)
        (binaryClause
          (TptpFofDefinitionalCnfLanguageDef.refDefinedNegative
            id arguments) right)
            (ternaryClause
              (TptpFofDefinitionalCnfLanguageDef.refDefinedPositive
                id arguments) leftNegative rightNegative)
            rest))
  | clausesOr {root id source left right tail arity introducedTail arguments
      leftNegative rightNegative rest : Pattern}
      (variablesDerivation : Derivation
        (variablesRequest arity indexZero)
        (variablesResult arity indexZero arguments))
      (leftNegation : Derivation (negateRequest left)
        (negateResult left leftNegative))
      (rightNegation : Derivation (negateRequest right)
        (negateResult right rightNegative))
      (tailDerivation : Derivation
        (clausesRequest root tail introducedTail)
        (clausesResult root tail introducedTail rest)) :
      Derivation
        (clausesRequest root
          (TptpFofDefinitionalCnfLanguageDef.definitionsCons
            (TptpFofDefinitionalCnfLanguageDef.definitionOr
              id source left right) tail)
          (TptpFofDefinitionalCnfLanguageDef.introducedCons
            (TptpFofDefinitionalCnfLanguageDef.introducedPredicate id arity)
            introducedTail))
        (clausesResult root
          (TptpFofDefinitionalCnfLanguageDef.definitionsCons
            (TptpFofDefinitionalCnfLanguageDef.definitionOr
              id source left right) tail)
          (TptpFofDefinitionalCnfLanguageDef.introducedCons
            (TptpFofDefinitionalCnfLanguageDef.introducedPredicate id arity)
            introducedTail)
          (prependThree
            (ternaryClause
              (TptpFofDefinitionalCnfLanguageDef.refDefinedNegative
                id arguments) left right)
            (binaryClause
              (TptpFofDefinitionalCnfLanguageDef.refDefinedPositive
                id arguments) leftNegative)
            (binaryClause
              (TptpFofDefinitionalCnfLanguageDef.refDefinedPositive
                id arguments) rightNegative)
            rest))
  | generate {root next definitions introduced clauses : Pattern}
      (clausesDerivation : Derivation
        (clausesRequest root definitions introduced)
        (clausesResult root definitions introduced clauses)) :
      Derivation
        (generateRequest
          (TptpFofDefinitionalCnfLanguageDef.namedOutput
            root next definitions introduced))
        (generateResult
          (TptpFofDefinitionalCnfLanguageDef.namedOutput
            root next definitions introduced)
          (TptpFofDefinitionalCnfLanguageDef.cnfOutput
            (TptpFofDefinitionalCnfLanguageDef.namedOutput
              root next definitions introduced) clauses))

def Derivation.height : {source target : Pattern} →
    Derivation source target → Nat
  | _, _, .variablesZero _
  | _, _, .negateVerum
  | _, _, .negateFalsum
  | _, _, .negateOriginalPositive _ _
  | _, _, .negateOriginalNegative _ _
  | _, _, .negateEqual _ _
  | _, _, .negateNotEqual _ _
  | _, _, .negateDefinedPositive _ _
  | _, _, .negateDefinedNegative _ _
  | _, _, .clausesNil _ => 1
  | _, _, .variablesSucc tail
  | _, _, .generate tail => tail.height + 1
  | _, _, .clausesAnd variableDerivation left right tail
  | _, _, .clausesOr variableDerivation left right tail =>
      max (max variableDerivation.height left.height)
        (max right.height tail.height) + 1

theorem variablesZero_rewriteAt_exact (next : Pattern) (fuel : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofDefinitionalCnfGenerationLanguageDef.language (fuel + 1)
      (variablesRequest indexZero next) =
    [variablesResult indexZero next TptpFofSkolemLanguageDef.termsNil] := by
  generation_root

theorem negateVerum_rewriteAt_exact (fuel : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofDefinitionalCnfGenerationLanguageDef.language (fuel + 1)
      (negateRequest TptpFofDefinitionalCnfLanguageDef.refVerum) =
    [negateResult TptpFofDefinitionalCnfLanguageDef.refVerum
      TptpFofDefinitionalCnfLanguageDef.refFalsum] := by
  generation_root

theorem negateFalsum_rewriteAt_exact (fuel : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofDefinitionalCnfGenerationLanguageDef.language (fuel + 1)
      (negateRequest TptpFofDefinitionalCnfLanguageDef.refFalsum) =
    [negateResult TptpFofDefinitionalCnfLanguageDef.refFalsum
      TptpFofDefinitionalCnfLanguageDef.refVerum] := by
  generation_root

theorem negateOriginalPositive_rewriteAt_exact
    (relation arguments : Pattern) (fuel : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofDefinitionalCnfGenerationLanguageDef.language (fuel + 1)
      (negateRequest
        (TptpFofDefinitionalCnfLanguageDef.refOriginalPositive
          relation arguments)) =
    [negateResult
      (TptpFofDefinitionalCnfLanguageDef.refOriginalPositive
        relation arguments)
      (TptpFofDefinitionalCnfLanguageDef.refOriginalNegative
        relation arguments)] := by
  generation_root

theorem negateOriginalNegative_rewriteAt_exact
    (relation arguments : Pattern) (fuel : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofDefinitionalCnfGenerationLanguageDef.language (fuel + 1)
      (negateRequest
        (TptpFofDefinitionalCnfLanguageDef.refOriginalNegative
          relation arguments)) =
    [negateResult
      (TptpFofDefinitionalCnfLanguageDef.refOriginalNegative
        relation arguments)
      (TptpFofDefinitionalCnfLanguageDef.refOriginalPositive
        relation arguments)] := by
  generation_root

theorem negateEqual_rewriteAt_exact
    (left right : Pattern) (fuel : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofDefinitionalCnfGenerationLanguageDef.language (fuel + 1)
      (negateRequest
        (TptpFofDefinitionalCnfLanguageDef.refEqual left right)) =
    [negateResult
      (TptpFofDefinitionalCnfLanguageDef.refEqual left right)
      (TptpFofDefinitionalCnfLanguageDef.refNotEqual left right)] := by
  generation_root

theorem negateNotEqual_rewriteAt_exact
    (left right : Pattern) (fuel : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofDefinitionalCnfGenerationLanguageDef.language (fuel + 1)
      (negateRequest
        (TptpFofDefinitionalCnfLanguageDef.refNotEqual left right)) =
    [negateResult
      (TptpFofDefinitionalCnfLanguageDef.refNotEqual left right)
      (TptpFofDefinitionalCnfLanguageDef.refEqual left right)] := by
  generation_root

theorem negateDefinedPositive_rewriteAt_exact
    (id arguments : Pattern) (fuel : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofDefinitionalCnfGenerationLanguageDef.language (fuel + 1)
      (negateRequest
        (TptpFofDefinitionalCnfLanguageDef.refDefinedPositive id arguments)) =
    [negateResult
      (TptpFofDefinitionalCnfLanguageDef.refDefinedPositive id arguments)
      (TptpFofDefinitionalCnfLanguageDef.refDefinedNegative id arguments)] := by
  generation_root

theorem negateDefinedNegative_rewriteAt_exact
    (id arguments : Pattern) (fuel : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofDefinitionalCnfGenerationLanguageDef.language (fuel + 1)
      (negateRequest
        (TptpFofDefinitionalCnfLanguageDef.refDefinedNegative id arguments)) =
    [negateResult
      (TptpFofDefinitionalCnfLanguageDef.refDefinedNegative id arguments)
      (TptpFofDefinitionalCnfLanguageDef.refDefinedPositive id arguments)] := by
  generation_root

theorem clausesNil_rewriteAt_exact (root : Pattern) (fuel : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofDefinitionalCnfGenerationLanguageDef.language (fuel + 1)
      (clausesRequest root TptpFofDefinitionalCnfLanguageDef.definitionsNil
        TptpFofDefinitionalCnfLanguageDef.introducedNil) =
    [clausesResult root TptpFofDefinitionalCnfLanguageDef.definitionsNil
      TptpFofDefinitionalCnfLanguageDef.introducedNil
      (TptpFofDefinitionalCnfLanguageDef.clausesCons
        (unitClause root) TptpFofDefinitionalCnfLanguageDef.clausesNil)] := by
  generation_root

theorem clausesAnd_rewriteAt_exact
    (root id source left right tail arity introducedTail arguments
      leftNegative rightNegative rest : Pattern)
    (fuel : Nat)
    (variablesExact :
      rewriteAt (engineBasePremises RelationEnv.empty)
        TptpFofDefinitionalCnfGenerationLanguageDef.language fuel
        (variablesRequest arity indexZero) =
      [variablesResult arity indexZero arguments])
    (leftExact :
      rewriteAt (engineBasePremises RelationEnv.empty)
        TptpFofDefinitionalCnfGenerationLanguageDef.language fuel
        (negateRequest left) = [negateResult left leftNegative])
    (rightExact :
      rewriteAt (engineBasePremises RelationEnv.empty)
        TptpFofDefinitionalCnfGenerationLanguageDef.language fuel
        (negateRequest right) = [negateResult right rightNegative])
    (tailExact :
      rewriteAt (engineBasePremises RelationEnv.empty)
        TptpFofDefinitionalCnfGenerationLanguageDef.language fuel
        (clausesRequest root tail introducedTail) =
      [clausesResult root tail introducedTail rest]) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofDefinitionalCnfGenerationLanguageDef.language (fuel + 1)
      (clausesRequest root
        (TptpFofDefinitionalCnfLanguageDef.definitionsCons
          (TptpFofDefinitionalCnfLanguageDef.definitionAnd
            id source left right) tail)
        (TptpFofDefinitionalCnfLanguageDef.introducedCons
          (TptpFofDefinitionalCnfLanguageDef.introducedPredicate id arity)
          introducedTail)) =
    [clausesResult root
      (TptpFofDefinitionalCnfLanguageDef.definitionsCons
        (TptpFofDefinitionalCnfLanguageDef.definitionAnd
          id source left right) tail)
      (TptpFofDefinitionalCnfLanguageDef.introducedCons
        (TptpFofDefinitionalCnfLanguageDef.introducedPredicate id arity)
        introducedTail)
      (prependThree
        (binaryClause
          (TptpFofDefinitionalCnfLanguageDef.refDefinedNegative id arguments)
          left)
        (binaryClause
          (TptpFofDefinitionalCnfLanguageDef.refDefinedNegative id arguments)
          right)
        (ternaryClause
          (TptpFofDefinitionalCnfLanguageDef.refDefinedPositive id arguments)
          leftNegative rightNegative)
        rest)] := by
  generation_root_using_all

theorem clausesOr_rewriteAt_exact
    (root id source left right tail arity introducedTail arguments
      leftNegative rightNegative rest : Pattern)
    (fuel : Nat)
    (variablesExact :
      rewriteAt (engineBasePremises RelationEnv.empty)
        TptpFofDefinitionalCnfGenerationLanguageDef.language fuel
        (variablesRequest arity indexZero) =
      [variablesResult arity indexZero arguments])
    (leftExact :
      rewriteAt (engineBasePremises RelationEnv.empty)
        TptpFofDefinitionalCnfGenerationLanguageDef.language fuel
        (negateRequest left) = [negateResult left leftNegative])
    (rightExact :
      rewriteAt (engineBasePremises RelationEnv.empty)
        TptpFofDefinitionalCnfGenerationLanguageDef.language fuel
        (negateRequest right) = [negateResult right rightNegative])
    (tailExact :
      rewriteAt (engineBasePremises RelationEnv.empty)
        TptpFofDefinitionalCnfGenerationLanguageDef.language fuel
        (clausesRequest root tail introducedTail) =
      [clausesResult root tail introducedTail rest]) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofDefinitionalCnfGenerationLanguageDef.language (fuel + 1)
      (clausesRequest root
        (TptpFofDefinitionalCnfLanguageDef.definitionsCons
          (TptpFofDefinitionalCnfLanguageDef.definitionOr
            id source left right) tail)
        (TptpFofDefinitionalCnfLanguageDef.introducedCons
          (TptpFofDefinitionalCnfLanguageDef.introducedPredicate id arity)
          introducedTail)) =
    [clausesResult root
      (TptpFofDefinitionalCnfLanguageDef.definitionsCons
        (TptpFofDefinitionalCnfLanguageDef.definitionOr
          id source left right) tail)
      (TptpFofDefinitionalCnfLanguageDef.introducedCons
        (TptpFofDefinitionalCnfLanguageDef.introducedPredicate id arity)
        introducedTail)
      (prependThree
        (ternaryClause
          (TptpFofDefinitionalCnfLanguageDef.refDefinedNegative id arguments)
          left right)
        (binaryClause
          (TptpFofDefinitionalCnfLanguageDef.refDefinedPositive id arguments)
          leftNegative)
        (binaryClause
          (TptpFofDefinitionalCnfLanguageDef.refDefinedPositive id arguments)
          rightNegative)
        rest)] := by
  generation_root_using_all

theorem generate_rewriteAt_exact
    (root next definitions introduced clauses : Pattern) (fuel : Nat)
    (clausesExact :
      rewriteAt (engineBasePremises RelationEnv.empty)
        TptpFofDefinitionalCnfGenerationLanguageDef.language fuel
        (clausesRequest root definitions introduced) =
      [clausesResult root definitions introduced clauses]) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofDefinitionalCnfGenerationLanguageDef.language (fuel + 1)
      (generateRequest
        (TptpFofDefinitionalCnfLanguageDef.namedOutput
          root next definitions introduced)) =
    [generateResult
      (TptpFofDefinitionalCnfLanguageDef.namedOutput
        root next definitions introduced)
      (TptpFofDefinitionalCnfLanguageDef.cnfOutput
        (TptpFofDefinitionalCnfLanguageDef.namedOutput
          root next definitions introduced) clauses)] := by
  generation_root_using_all

theorem Derivation.rewriteAt_exact {source target : Pattern}
    (derivation : Derivation source target) (fuel : Nat)
    (enough : derivation.height ≤ fuel) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofDefinitionalCnfGenerationLanguageDef.language fuel source =
        [target] := by
  induction derivation generalizing fuel with
  | variablesZero =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          simpa [Nat.succ_eq_add_one] using
            variablesZero_rewriteAt_exact _ fuel
  | variablesSucc tail tailHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have childEnough : tail.height ≤ fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          have childExact := tailHypothesis fuel childEnough
          generation_root_using_all
  | negateVerum =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          simpa [Nat.succ_eq_add_one] using negateVerum_rewriteAt_exact fuel
  | negateFalsum =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          simpa [Nat.succ_eq_add_one] using negateFalsum_rewriteAt_exact fuel
  | negateOriginalPositive =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          simpa [Nat.succ_eq_add_one] using
            negateOriginalPositive_rewriteAt_exact _ _ fuel
  | negateOriginalNegative =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          simpa [Nat.succ_eq_add_one] using
            negateOriginalNegative_rewriteAt_exact _ _ fuel
  | negateEqual =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          simpa [Nat.succ_eq_add_one] using
            negateEqual_rewriteAt_exact _ _ fuel
  | negateNotEqual =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          simpa [Nat.succ_eq_add_one] using
            negateNotEqual_rewriteAt_exact _ _ fuel
  | negateDefinedPositive =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          simpa [Nat.succ_eq_add_one] using
            negateDefinedPositive_rewriteAt_exact _ _ fuel
  | negateDefinedNegative =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          simpa [Nat.succ_eq_add_one] using
            negateDefinedNegative_rewriteAt_exact _ _ fuel
  | clausesNil =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          simpa [Nat.succ_eq_add_one] using
            clausesNil_rewriteAt_exact _ fuel
  | clausesAnd variableDerivation left right tail variablesHypothesis leftHypothesis
      rightHypothesis tailHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have maximumEnough :
              max (max variableDerivation.height left.height)
                  (max right.height tail.height) ≤ fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          have variablesExact := variablesHypothesis fuel
            ((Nat.le_max_left _ _).trans
              ((Nat.le_max_left _ _).trans maximumEnough))
          have leftExact := leftHypothesis fuel
            ((Nat.le_max_right _ _).trans
              ((Nat.le_max_left _ _).trans maximumEnough))
          have rightExact := rightHypothesis fuel
            ((Nat.le_max_left _ _).trans
              ((Nat.le_max_right _ _).trans maximumEnough))
          have tailExact := tailHypothesis fuel
            ((Nat.le_max_right _ _).trans
              ((Nat.le_max_right _ _).trans maximumEnough))
          simpa [Nat.succ_eq_add_one] using
            clausesAnd_rewriteAt_exact _ _ _ _ _ _ _ _ _ _ _ _ fuel
              variablesExact leftExact rightExact tailExact
  | clausesOr variableDerivation left right tail variablesHypothesis leftHypothesis
      rightHypothesis tailHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have maximumEnough :
              max (max variableDerivation.height left.height)
                  (max right.height tail.height) ≤ fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          have variablesExact := variablesHypothesis fuel
            ((Nat.le_max_left _ _).trans
              ((Nat.le_max_left _ _).trans maximumEnough))
          have leftExact := leftHypothesis fuel
            ((Nat.le_max_right _ _).trans
              ((Nat.le_max_left _ _).trans maximumEnough))
          have rightExact := rightHypothesis fuel
            ((Nat.le_max_left _ _).trans
              ((Nat.le_max_right _ _).trans maximumEnough))
          have tailExact := tailHypothesis fuel
            ((Nat.le_max_right _ _).trans
              ((Nat.le_max_right _ _).trans maximumEnough))
          simpa [Nat.succ_eq_add_one] using
            clausesOr_rewriteAt_exact _ _ _ _ _ _ _ _ _ _ _ _ fuel
              variablesExact leftExact rightExact tailExact
  | generate tail tailHypothesis =>
      cases fuel with
      | zero => simp [Derivation.height] at enough
      | succ fuel =>
          have childEnough : tail.height ≤ fuel := by
            simpa [Derivation.height, Nat.succ_eq_add_one] using enough
          have childExact := tailHypothesis fuel childEnough
          simpa [Nat.succ_eq_add_one] using
            generate_rewriteAt_exact _ _ _ _ _ fuel childExact

theorem Derivation.no_invention {source expected target : Pattern}
    (derivation : Derivation source expected) (fuel : Nat)
    (enough : derivation.height ≤ fuel)
    (membership : target ∈ rewriteAt
      (engineBasePremises RelationEnv.empty)
      TptpFofDefinitionalCnfGenerationLanguageDef.language fuel source) :
    target = expected := by
  rw [derivation.rewriteAt_exact fuel enough] at membership
  simpa using membership

theorem mismatched_empty_ledgers_have_no_reduct
    (root id arity : Pattern) (fuel : Nat) :
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofDefinitionalCnfGenerationLanguageDef.language fuel
      (clausesRequest root TptpFofDefinitionalCnfLanguageDef.definitionsNil
        (TptpFofDefinitionalCnfLanguageDef.introducedCons
          (TptpFofDefinitionalCnfLanguageDef.introducedPredicate id arity)
          TptpFofDefinitionalCnfLanguageDef.introducedNil)) = [] := by
  cases fuel <;> generation_root

theorem mismatched_definition_identity_has_no_reduct
    (root definitionId introducedId source left right arity : Pattern)
    (fuel : Nat) :
    definitionId ≠ introducedId →
    rewriteAt (engineBasePremises RelationEnv.empty)
      TptpFofDefinitionalCnfGenerationLanguageDef.language fuel
      (clausesRequest root
        (TptpFofDefinitionalCnfLanguageDef.definitionsCons
          (TptpFofDefinitionalCnfLanguageDef.definitionAnd
            definitionId source left right)
          TptpFofDefinitionalCnfLanguageDef.definitionsNil)
        (TptpFofDefinitionalCnfLanguageDef.introducedCons
          (TptpFofDefinitionalCnfLanguageDef.introducedPredicate
            introducedId arity)
          TptpFofDefinitionalCnfLanguageDef.introducedNil)) = [] := by
  intro distinct
  cases fuel with
  | zero => generation_root
  | succ fuel =>
      generation_root
      intro equal
      exact (distinct equal).elim

#print axioms mismatched_empty_ledgers_have_no_reduct
#print axioms mismatched_definition_identity_has_no_reduct
#print axioms variablesZero_rewriteAt_exact
#print axioms negateDefinedNegative_rewriteAt_exact
#print axioms clausesNil_rewriteAt_exact
#print axioms Derivation.rewriteAt_exact
#print axioms Derivation.no_invention

end Mettapedia.GSLT.LanguageDef.TptpFofDefinitionalCnfGenerationAgreement
