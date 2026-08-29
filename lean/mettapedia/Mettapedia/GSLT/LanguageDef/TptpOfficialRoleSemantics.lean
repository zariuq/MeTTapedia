import Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationSyntax

/-!
# Semantic formula roles from the official TPTP vocabulary

The TPTP grammar admits formula roles as syntax, but the role is also semantic
data.  In particular, assumptions require discharge, conjectures require a
goal discipline, negated conjectures require a counter-theorem step, and the
literal role `unknown` is an error state rather than an axiom.

This module decodes the complete named role vocabulary from the official AST
without assigning an inference calculus.  Calculus services consume these
roles together with source and useful-information data.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialRoleSemantics

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationSyntax

inductive FormulaRole where
  | axiom
  | hypothesis
  | definition
  | assumption
  | lemma
  | theorem
  | corollary
  | conjecture
  | negatedConjecture
  | plain
  | type
  | interpretation
  | finiteInterpretationDomain
  | finiteInterpretationFunctors
  | finiteInterpretationPredicates
  | unknown
  deriving DecidableEq, Repr

def FormulaRole.code : FormulaRole -> String
  | .axiom => "axiom"
  | .hypothesis => "hypothesis"
  | .definition => "definition"
  | .assumption => "assumption"
  | .lemma => "lemma"
  | .theorem => "theorem"
  | .corollary => "corollary"
  | .conjecture => "conjecture"
  | .negatedConjecture => "negated_conjecture"
  | .plain => "plain"
  | .type => "type"
  | .interpretation => "interpretation"
  | .finiteInterpretationDomain => "fi_domain"
  | .finiteInterpretationFunctors => "fi_functors"
  | .finiteInterpretationPredicates => "fi_predicates"
  | .unknown => "unknown"

def FormulaRole.parse? : String -> Option FormulaRole
  | "axiom" => some .axiom
  | "hypothesis" => some .hypothesis
  | "definition" => some .definition
  | "assumption" => some .assumption
  | "lemma" => some .lemma
  | "theorem" => some .theorem
  | "corollary" => some .corollary
  | "conjecture" => some .conjecture
  | "negated_conjecture" => some .negatedConjecture
  | "plain" => some .plain
  | "type" => some .type
  | "interpretation" => some .interpretation
  | "fi_domain" => some .finiteInterpretationDomain
  | "fi_functors" => some .finiteInterpretationFunctors
  | "fi_predicates" => some .finiteInterpretationPredicates
  | "unknown" => some .unknown
  | _ => none

def decodeFormulaRole? (role : Pattern) : Option FormulaRole := do
  FormulaRole.parse? (← decodeRoleLexeme? role)

@[simp] theorem FormulaRole.parse_code (role : FormulaRole) :
    FormulaRole.parse? role.code = some role := by
  cases role <;> rfl

/-- Axiom-like roles may be accepted as problem premises.  Their external
source and problem membership still have to be checked separately. -/
def FormulaRole.isAxiomLike : FormulaRole -> Bool
  | .axiom | .hypothesis | .definition | .lemma | .theorem | .corollary => true
  | _ => false

def FormulaRole.requiresDischarge : FormulaRole -> Bool
  | .assumption => true
  | _ => false

def FormulaRole.isConjecture : FormulaRole -> Bool
  | .conjecture => true
  | _ => false

def FormulaRole.isNegatedConjecture : FormulaRole -> Bool
  | .negatedConjecture => true
  | _ => false

def FormulaRole.isTypeDeclaration : FormulaRole -> Bool
  | .type => true
  | _ => false

def FormulaRole.isInterpretationData : FormulaRole -> Bool
  | .interpretation
  | .finiteInterpretationDomain
  | .finiteInterpretationFunctors
  | .finiteInterpretationPredicates => true
  | _ => false

/-- The literal `unknown` role is syntactically recognized but cannot be
silently assigned semantic authority. -/
def FormulaRole.semanticSupported : FormulaRole -> Bool
  | .unknown => false
  | _ => true

namespace Canary

private def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

def role (value : String) : Pattern :=
  a "tptp92-ast:formula-role:alt-1"
    [a "tptp92-ast:token:lower-word" [a value]]

def refinedRole (value refinement : String) : Pattern :=
  a "tptp92-ast:formula-role:alt-2" [
    a "tptp92-ast:token:lower-word" [a value],
    a "tptp92-ast:general-term:alt-1" [
      a "tptp92-ast:general-data:alt-1" [
        a "tptp92-ast:atomic-word:alt-1" [
          a "tptp92-ast:token:lower-word" [a refinement]]]]]

theorem every_official_named_role_round_trips (role : FormulaRole) :
    decodeFormulaRole? (Canary.role role.code) = some role := by
  cases role <;> rfl

theorem role_refinement_preserves_base_semantics :
    decodeFormulaRole? (refinedRole "axiom" "derived") = some .axiom := by
  rfl

theorem custom_role_is_unsupported :
    decodeFormulaRole? (role "private_role") = none := by
  rfl

theorem assumption_requires_discharge :
    FormulaRole.assumption.requiresDischarge = true := by
  rfl

theorem unknown_role_is_not_semantically_supported :
    FormulaRole.unknown.semanticSupported = false := by
  rfl

theorem conjecture_and_negated_conjecture_are_distinct :
    FormulaRole.conjecture != FormulaRole.negatedConjecture := by
  decide

end Canary

#print axioms FormulaRole.parse_code
#print axioms Canary.every_official_named_role_round_trips
#print axioms Canary.role_refinement_preserves_base_semantics
#print axioms Canary.custom_role_is_unsupported
#print axioms Canary.assumption_requires_discharge
#print axioms Canary.unknown_role_is_not_semantically_supported
#print axioms Canary.conjecture_and_negated_conjecture_are_distinct

end Mettapedia.GSLT.LanguageDef.TptpOfficialRoleSemantics
