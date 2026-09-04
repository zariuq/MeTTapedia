import Mettapedia.GSLT.LanguageDef.TptpFofCnfOfficialSerializationPlan

/-!
# Reference semantics for allocated CNF to official TPTP AST

This is the independent, partial reference function for the authored
serialization GSLT.  It consumes an explicit finite lexical plan and emits
only official TPTP 9.2 AST subtrees.  Unsupported or malformed semantic
patterns, absent allocation rows, and invalid plans fail closed.

The result retains each internal clause identity beside its external name and
annotated CNF formula.  That identity map is the later reconstruction seam for
TSTP parent references; it is not hidden in source text or recomputed from
spellings.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofCnfOfficialSerializationSemantics

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.TptpFofCnfOfficialSerializationPlan

def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

def atomicWordPlain (lexeme : Pattern) : Pattern :=
  a "tptp92-ast:atomic-word:alt-2" [
    a "tptp92-ast:token:single-quoted" [lexeme]]

def functorPlain (lexeme : Pattern) : Pattern :=
  a "tptp92-ast:functor:alt-1" [atomicWordPlain lexeme]

def definedFunctor (lexeme : Pattern) : Pattern :=
  a "tptp92-ast:defined-functor:alt-1" [
    a "tptp92-ast:atomic-defined-word:alt-1" [
      a "tptp92-ast:token:dollar-word" [lexeme]]]

def systemFunctor (lexeme : Pattern) : Pattern :=
  a "tptp92-ast:system-functor:alt-1" [
    a "tptp92-ast:atomic-system-word:alt-1" [
      a "tptp92-ast:token:dollar-dollar-word" [lexeme]]]

def arguments : List Pattern -> Option Pattern
  | [] => none
  | [head] => some <| a "tptp92-ast:fof-arguments:alt-1" [head]
  | head :: tail => do
      let renderedTail ← arguments tail
      some <| a "tptp92-ast:fof-arguments:alt-2" [head, renderedTail]

def plainTerm (functor : Pattern) (terms : List Pattern) : Pattern :=
  let body := match arguments terms with
    | none => a "tptp92-ast:fof-plain-term:alt-1" [
        a "tptp92-ast:constant:alt-1" [functor]]
    | some rendered =>
        a "tptp92-ast:fof-plain-term:alt-2" [functor, rendered]
  a "tptp92-ast:fof-term:alt-1" [
    a "tptp92-ast:fof-function-term:alt-1" [body]]

def definedTerm (functor : Pattern) (terms : List Pattern) : Pattern :=
  let body := match arguments terms with
    | none => a "tptp92-ast:fof-defined-plain-term:alt-1" [
        a "tptp92-ast:defined-constant:alt-1" [functor]]
    | some rendered =>
        a "tptp92-ast:fof-defined-plain-term:alt-2" [functor, rendered]
  a "tptp92-ast:fof-term:alt-1" [
    a "tptp92-ast:fof-function-term:alt-2" [
      a "tptp92-ast:fof-defined-term:alt-2" [
        a "tptp92-ast:fof-defined-atomic-term:alt-1" [body]]]]

def systemTerm (functor : Pattern) (terms : List Pattern) : Pattern :=
  let body := match arguments terms with
    | none => a "tptp92-ast:fof-system-term:alt-1" [
        a "tptp92-ast:system-constant:alt-1" [functor]]
    | some rendered =>
        a "tptp92-ast:fof-system-term:alt-2" [functor, rendered]
  a "tptp92-ast:fof-term:alt-1" [
    a "tptp92-ast:fof-function-term:alt-3" [body]]

def numericTerm (alternative tokenLabel : String) (lexeme : Pattern) :
    Pattern :=
  a "tptp92-ast:fof-term:alt-1" [
    a "tptp92-ast:fof-function-term:alt-2" [
      a "tptp92-ast:fof-defined-term:alt-1" [
        a "tptp92-ast:defined-term:alt-1" [
          a alternative [a tokenLabel [lexeme]]]]]]

def distinctObjectTerm (lexeme : Pattern) : Pattern :=
  a "tptp92-ast:fof-term:alt-1" [
    a "tptp92-ast:fof-function-term:alt-2" [
      a "tptp92-ast:fof-defined-term:alt-1" [
        a "tptp92-ast:defined-term:alt-2" [
          a "tptp92-ast:token:distinct-object" [lexeme]]]]]

mutual
  def serializeTerm? (plan : Plan) : Pattern -> Option Pattern
    | .apply "tptp-fof-skolem:term-variable" [index] =>
        return a "tptp92-ast:fof-term:alt-2" [
          ← plan.variableNames.lookup? index]
    | .apply "tptp-fof-skolem:term-original" [function, sourceTerms] => do
        let terms ← serializeTerms? plan sourceTerms
        match function with
        | .apply "tptp-fof-symbol:function-plain" [lexeme] =>
            some (plainTerm (functorPlain lexeme) terms)
        | .apply "tptp-fof-symbol:function-defined" [lexeme] =>
            some (definedTerm (definedFunctor lexeme) terms)
        | .apply "tptp-fof-symbol:function-system" [lexeme] =>
            some (systemTerm (systemFunctor lexeme) terms)
        | .apply "tptp-fof-symbol:function-integer" [lexeme] =>
            if terms.isEmpty then some (
              numericTerm "tptp92-ast:number:alt-1"
                "tptp92-ast:token:integer" lexeme)
            else none
        | .apply "tptp-fof-symbol:function-rational" [lexeme] =>
            if terms.isEmpty then some (
              numericTerm "tptp92-ast:number:alt-2"
                "tptp92-ast:token:rational" lexeme)
            else none
        | .apply "tptp-fof-symbol:function-real" [lexeme] =>
            if terms.isEmpty then some (
              numericTerm "tptp92-ast:number:alt-3"
                "tptp92-ast:token:real" lexeme)
            else none
        | .apply "tptp-fof-symbol:function-distinct-object" [lexeme] =>
            if terms.isEmpty then some (distinctObjectTerm lexeme) else none
        | _ => none
    | .apply "tptp-fof-skolem:term-generated" [identity, sourceTerms] => do
        let functor ← plan.skolemFunctors.lookup? identity
        let terms ← serializeTerms? plan sourceTerms
        some (plainTerm functor terms)
    | _ => none

  def serializeTerms? (plan : Plan) : Pattern -> Option (List Pattern)
    | .apply "tptp-fof-skolem:terms-nil" [] => some []
    | .apply "tptp-fof-skolem:terms-cons" [head, tail] =>
        return (← serializeTerm? plan head) :: (← serializeTerms? plan tail)
    | _ => none
end

def plainAtomicFormula (functor : Pattern) (terms : List Pattern) : Pattern :=
  let term := match arguments terms with
    | none => a "tptp92-ast:fof-plain-term:alt-1" [
        a "tptp92-ast:constant:alt-1" [functor]]
    | some rendered =>
        a "tptp92-ast:fof-plain-term:alt-2" [functor, rendered]
  a "tptp92-ast:fof-atomic-formula:alt-1" [
    a "tptp92-ast:fof-plain-atomic-formula:alt-1" [term]]

def definedAtomicFormula? (functor : Pattern) (terms : List Pattern) :
    Option Pattern := do
  let rendered ← arguments terms
  some <| a "tptp92-ast:fof-atomic-formula:alt-2" [
    a "tptp92-ast:fof-defined-atomic-formula:alt-1" [
      a "tptp92-ast:fof-defined-plain-formula:alt-1" [
        a "tptp92-ast:fof-defined-plain-term:alt-2"
          [functor, rendered]]]]

def systemAtomicFormula (functor : Pattern) (terms : List Pattern) : Pattern :=
  let term := match arguments terms with
    | none => a "tptp92-ast:fof-system-term:alt-1" [
        a "tptp92-ast:system-constant:alt-1" [functor]]
    | some rendered =>
        a "tptp92-ast:fof-system-term:alt-2" [functor, rendered]
  a "tptp92-ast:fof-atomic-formula:alt-3" [
    a "tptp92-ast:fof-system-atomic-formula:alt-1" [term]]

def truthAtomicFormula (lexeme : String) : Pattern :=
  a "tptp92-ast:fof-atomic-formula:alt-2" [
    a "tptp92-ast:fof-defined-atomic-formula:alt-1" [
      a "tptp92-ast:fof-defined-plain-formula:alt-1" [
        a "tptp92-ast:fof-defined-plain-term:alt-1" [
          a "tptp92-ast:defined-constant:alt-1" [
            definedFunctor (a lexeme)]]]]]

def equalityAtomicFormula (left right : Pattern) : Pattern :=
  a "tptp92-ast:fof-atomic-formula:alt-2" [
    a "tptp92-ast:fof-defined-atomic-formula:alt-2" [
      a "tptp92-ast:fof-defined-infix-formula:alt-1" [
        left,
        a "tptp92-ast:defined-infix-pred:alt-1" [
          a "tptp92-ast:infix-equality:alt-1"],
        right]]]

def positiveLiteral (formula : Pattern) : Pattern :=
  a "tptp92-ast:cnf-literal:alt-1" [formula]

def negativeLiteral (formula : Pattern) : Pattern :=
  a "tptp92-ast:cnf-literal:alt-2" [formula]

def inequalityLiteral (left right : Pattern) : Pattern :=
  a "tptp92-ast:cnf-literal:alt-4" [
    a "tptp92-ast:fof-infix-unary:alt-1" [
      left, a "tptp92-ast:infix-inequality:alt-1", right]]

def serializeOriginalAtomic? (function : Pattern) (terms : List Pattern) :
    Option Pattern :=
  match function with
  | .apply "tptp-fof-symbol:predicate-plain" [lexeme] =>
      some (plainAtomicFormula (functorPlain lexeme) terms)
  | .apply "tptp-fof-symbol:predicate-defined" [lexeme] =>
      definedAtomicFormula? (definedFunctor lexeme) terms
  | .apply "tptp-fof-symbol:predicate-system" [lexeme] =>
      some (systemAtomicFormula (systemFunctor lexeme) terms)
  | _ => none

def serializeReference? (plan : Plan) : Pattern -> Option Pattern
  | .apply "tptp-fof-named:ref-verum" [] =>
      some (positiveLiteral (truthAtomicFormula "$true"))
  | .apply "tptp-fof-named:ref-falsum" [] =>
      some (positiveLiteral (truthAtomicFormula "$false"))
  | .apply "tptp-fof-named:ref-original-positive"
      [relation, sourceTerms] => do
        let terms ← serializeTerms? plan sourceTerms
        positiveLiteral <$> serializeOriginalAtomic? relation terms
  | .apply "tptp-fof-named:ref-original-negative"
      [relation, sourceTerms] => do
        let terms ← serializeTerms? plan sourceTerms
        negativeLiteral <$> serializeOriginalAtomic? relation terms
  | .apply "tptp-fof-named:ref-equal" [left, right] =>
      return positiveLiteral <| equalityAtomicFormula
        (← serializeTerm? plan left) (← serializeTerm? plan right)
  | .apply "tptp-fof-named:ref-not-equal" [left, right] =>
      return inequalityLiteral
        (← serializeTerm? plan left) (← serializeTerm? plan right)
  | .apply "tptp-fof-named:ref-defined-positive"
      [identity, sourceTerms] => do
        let functor ← plan.definitionFunctors.lookup? identity
        let terms ← serializeTerms? plan sourceTerms
        some (positiveLiteral (plainAtomicFormula functor terms))
  | .apply "tptp-fof-named:ref-defined-negative"
      [identity, sourceTerms] => do
        let functor ← plan.definitionFunctors.lookup? identity
        let terms ← serializeTerms? plan sourceTerms
        some (negativeLiteral (plainAtomicFormula functor terms))
  | _ => none

def serializeClauseLiterals? (plan : Plan) : Pattern -> Option (List Pattern)
  | .apply "tptp-fof-cnf:clause-nil" [] => some []
  | .apply "tptp-fof-cnf:clause-cons" [head, tail] =>
      return (← serializeReference? plan head) ::
        (← serializeClauseLiterals? plan tail)
  | _ => none

def disjunction (literals : List Pattern) : Pattern :=
  match literals with
  | [] => a "tptp92-ast:cnf-disjunction:alt-1" [
      positiveLiteral (truthAtomicFormula "$false")]
  | head :: tail => tail.foldl
      (fun left right =>
        a "tptp92-ast:cnf-disjunction:alt-2" [left, right])
      (a "tptp92-ast:cnf-disjunction:alt-1" [head])

def serializeClause? (plan : Plan) (source : Pattern) : Option Pattern := do
  let literals ← serializeClauseLiterals? plan source
  some <| a "tptp92-ast:cnf-formula:alt-1" [disjunction literals]

def role? : Pattern -> Option Pattern
  | .apply "tptp-fof-batch:positive" [] =>
      some <| a "tptp92-ast:formula-role:alt-1" [
        a "tptp92-ast:token:lower-word" [a "axiom"]]
  | .apply "tptp-fof-batch:negative" [] =>
      some <| a "tptp92-ast:formula-role:alt-1" [
        a "tptp92-ast:token:lower-word" [a "negated_conjecture"]]
  | _ => none

def annotatedCnf (name role formula : Pattern) : Pattern :=
  a "tptp92-ast:annotated-formula:alt-5" [
    a "tptp92-ast:cnf-annotated:alt-1" [
      name, role, formula, a "tptp92-ast:annotations:alt-2"]]

structure SerializedClauseEntry where
  identity : Pattern
  name : Pattern
  clause : Pattern
  annotated : Pattern
  deriving DecidableEq, Repr

structure Result where
  source : Pattern
  polarity : Pattern
  entries : List SerializedClauseEntry
  deriving DecidableEq, Repr

def serializeEntries? (plan : Plan) (polarity : Pattern) :
    Pattern -> Option (List SerializedClauseEntry)
  | .apply "tptp-fof-cnf-allocated:entries-nil" [] => some []
  | .apply "tptp-fof-cnf-allocated:entries-cons" [
      .apply "tptp-fof-cnf-allocated:clause-entry" [
        identity,
        .apply "tptp-fof-cnf-allocated:name" [nameIndex],
        clause], rest] => do
      let name ← plan.clauseNames.lookup? nameIndex
      let role ← role? polarity
      let formula ← serializeClause? plan clause
      let tail ← serializeEntries? plan polarity rest
      some (⟨identity, name, clause, annotatedCnf name role formula⟩ :: tail)
  | _ => none

def serialize? (plan : Plan) (source : Pattern) : Option Result := do
  if !plan.valid then none else
    match source with
    | .apply "tptp-fof-cnf-allocated:output" [
        batch, _, _, entries] =>
        match batch with
        | .apply "tptp-fof-batch:output" [_, polarity, _, _, _] =>
            return ⟨source, polarity, ← serializeEntries? plan polarity entries⟩
        | _ => none
    | _ => none

/-! ## Positive and negative controls -/

namespace Canary

def index := TptpFofCnfOfficialSerializationPlan.index
def plan := TptpFofCnfOfficialSerializationPlan.Canary.plan

def variableTerm : Pattern :=
  a "tptp-fof-skolem:term-variable" [index 0]

def skolemTerm : Pattern :=
  a "tptp-fof-skolem:term-generated" [index 2,
    a "tptp-fof-skolem:terms-cons" [variableTerm,
      a "tptp-fof-skolem:terms-nil"]]

def plainPredicateReference : Pattern :=
  a "tptp-fof-named:ref-original-positive" [
    a "tptp-fof-symbol:predicate-plain" [a "p"],
    a "tptp-fof-skolem:terms-cons" [skolemTerm,
      a "tptp-fof-skolem:terms-nil"]]

def generatedNegativeReference : Pattern :=
  a "tptp-fof-named:ref-defined-negative" [index 2,
    a "tptp-fof-skolem:terms-cons" [variableTerm,
      a "tptp-fof-skolem:terms-nil"]]

def clause : Pattern :=
  a "tptp-fof-cnf:clause-cons" [plainPredicateReference,
    a "tptp-fof-cnf:clause-cons" [generatedNegativeReference,
      a "tptp-fof-cnf:clause-nil"]]

theorem two_literal_clause_serializes :
    (serializeClause? plan clause).isSome = true := by
  decide +kernel

theorem empty_clause_becomes_explicit_false :
    serializeClause? plan (a "tptp-fof-cnf:clause-nil") = some (
      a "tptp92-ast:cnf-formula:alt-1" [
        a "tptp92-ast:cnf-disjunction:alt-1" [
          positiveLiteral (truthAtomicFormula "$false")]]) := by
  rfl

theorem missing_variable_allocation_fails_closed :
    serializeTerm? plan
      (a "tptp-fof-skolem:term-variable" [index 99]) = none := by
  rfl

theorem malformed_clause_fails_closed :
    serializeClause? plan (a "not-a-clause") = none := by
  rfl

def plainTwo : Pattern :=
  a "tptp-fof-skolem:term-original" [
    a "tptp-fof-symbol:function-plain" [a "2"],
    a "tptp-fof-skolem:terms-nil"]

def integerTwo : Pattern :=
  a "tptp-fof-skolem:term-original" [
    a "tptp-fof-symbol:function-integer" [a "2"],
    a "tptp-fof-skolem:terms-nil"]

theorem equal_lexemes_in_distinct_symbol_classes_stay_distinct :
    serializeTerm? plan plainTwo != serializeTerm? plan integerTwo := by
  decide +kernel

end Canary

#print axioms Canary.two_literal_clause_serializes
#print axioms Canary.empty_clause_becomes_explicit_false
#print axioms Canary.missing_variable_allocation_fails_closed
#print axioms Canary.malformed_clause_fails_closed
#print axioms Canary.equal_lexemes_in_distinct_symbol_classes_stay_distinct

end Mettapedia.GSLT.LanguageDef.TptpFofCnfOfficialSerializationSemantics
