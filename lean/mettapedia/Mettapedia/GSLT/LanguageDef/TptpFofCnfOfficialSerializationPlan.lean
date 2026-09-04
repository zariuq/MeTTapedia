import Mettapedia.GSLT.LanguageDef.TptpFofCnfAllocatedBatchLanguageDef
import Mettapedia.GSLT.LanguageDef.TptpOfficialAbstractSyntax
import Mettapedia.GSLT.LanguageDef.CarrierWellSorted

/-!
# Finite lexical plans for official TPTP CNF serialization

Clausification allocates structural natural-number identities.  The official
TPTP AST instead carries lexical tokens.  This module makes that boundary an
explicit finite object: every admitted source identity is paired with the
official AST subtree that will represent it.

The plan is data, not a second serializer.  Its rows feed ordinary
`relationQuery` premises in the authored serialization language.  Validation
checks the source and target sorts, duplicate keys, duplicate targets, and the
disjointness of generated Skolem and definition-symbol namespaces.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpFofCnfOfficialSerializationPlan

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.GSLT.LanguageDef.CarrierWellSorted

def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

structure Row where
  source : Pattern
  target : Pattern
  deriving DecidableEq, Repr

abbrev Table := List Row

structure Plan where
  clauseNames : Table
  variableNames : Table
  skolemFunctors : Table
  definitionFunctors : Table
  deriving DecidableEq, Repr

def Table.sourceKeys (table : Table) : List Pattern :=
  table.map (·.source)

def Table.targets (table : Table) : List Pattern :=
  table.map (·.target)

def Table.lookup? (table : Table) (source : Pattern) : Option Pattern :=
  (table.find? fun row => row.source == source).map (·.target)

def inhabits (language : LanguageDef) (sort : String)
    (pattern : Pattern) : Bool :=
  checkHasType language WellSorted.FreeTypeContext.empty [] pattern
    (.base sort)

def Table.validFor (table : Table) (targetSort : String) : Bool :=
  decide table.sourceKeys.Nodup &&
    decide table.targets.Nodup &&
    table.all fun row =>
      inhabits TptpResolvedFofLanguageDef.language
          "TptpResolvedFof:Index" row.source &&
        inhabits TptpOfficialAbstractSyntax.language targetSort row.target

def targetsDisjoint (left right : Table) : Bool :=
  left.targets.all fun target => !(right.targets.contains target)

def Plan.valid (plan : Plan) : Bool :=
  plan.clauseNames.validFor "Tptp92Ast:name" &&
    plan.variableNames.validFor "Tptp92Ast:variable" &&
    plan.skolemFunctors.validFor "Tptp92Ast:functor" &&
    plan.definitionFunctors.validFor "Tptp92Ast:functor" &&
    targetsDisjoint plan.skolemFunctors plan.definitionFunctors

def clauseNameRelation : String :=
  "tptp-cnf-official-serialization:clause-name"

def variableRelation : String :=
  "tptp-cnf-official-serialization:variable"

def skolemFunctorRelation : String :=
  "tptp-cnf-official-serialization:skolem-functor"

def definitionFunctorRelation : String :=
  "tptp-cnf-official-serialization:definition-functor"

private def rowsForQuery (table : Table) (arguments : List Pattern) :
    List (List Pattern) :=
  match arguments with
  | source :: _ =>
      match table.lookup? source with
      | some target => [[source, target]]
      | none => []
  | [] => []

/-- The exact finite relation environment consumed by serialization rules. -/
def Plan.relationEnv (plan : Plan) : RelationEnv where
  tuples relation arguments :=
    if relation = clauseNameRelation then
      rowsForQuery plan.clauseNames arguments
    else if relation = variableRelation then
      rowsForQuery plan.variableNames arguments
    else if relation = skolemFunctorRelation then
      rowsForQuery plan.skolemFunctors arguments
    else if relation = definitionFunctorRelation then
      rowsForQuery plan.definitionFunctors arguments
    else []

theorem Plan.clauseNameTuples_of_lookup (plan : Plan)
    (source requested target : Pattern)
    (lookup : plan.clauseNames.lookup? source = some target) :
    plan.relationEnv.tuples clauseNameRelation [source, requested] =
      [[source, target]] := by
  simp [Plan.relationEnv, rowsForQuery, lookup, clauseNameRelation,
    variableRelation, skolemFunctorRelation, definitionFunctorRelation]

theorem Plan.variableTuples_of_lookup (plan : Plan)
    (source requested target : Pattern)
    (lookup : plan.variableNames.lookup? source = some target) :
    plan.relationEnv.tuples variableRelation [source, requested] =
      [[source, target]] := by
  simp [Plan.relationEnv, rowsForQuery, lookup, clauseNameRelation,
    variableRelation, skolemFunctorRelation, definitionFunctorRelation]

theorem Plan.variableTuples_of_missing (plan : Plan)
    (source requested : Pattern)
    (lookup : plan.variableNames.lookup? source = none) :
    plan.relationEnv.tuples variableRelation [source, requested] = [] := by
  simp [Plan.relationEnv, rowsForQuery, lookup, clauseNameRelation,
    variableRelation, skolemFunctorRelation, definitionFunctorRelation]

theorem Plan.skolemFunctorTuples_of_lookup (plan : Plan)
    (source requested target : Pattern)
    (lookup : plan.skolemFunctors.lookup? source = some target) :
    plan.relationEnv.tuples skolemFunctorRelation [source, requested] =
      [[source, target]] := by
  simp [Plan.relationEnv, rowsForQuery, lookup, clauseNameRelation,
    variableRelation, skolemFunctorRelation, definitionFunctorRelation]

theorem Plan.definitionFunctorTuples_of_lookup (plan : Plan)
    (source requested target : Pattern)
    (lookup : plan.definitionFunctors.lookup? source = some target) :
    plan.relationEnv.tuples definitionFunctorRelation [source, requested] =
      [[source, target]] := by
  simp [Plan.relationEnv, rowsForQuery, lookup, clauseNameRelation,
    variableRelation, skolemFunctorRelation, definitionFunctorRelation]

def quotedAtomicWord (lexeme : String) : Pattern :=
  a "tptp92-ast:atomic-word:alt-2" [
    a "tptp92-ast:token:single-quoted" [a lexeme]]

def quotedName (lexeme : String) : Pattern :=
  a "tptp92-ast:name:alt-1" [quotedAtomicWord lexeme]

def quotedFunctor (lexeme : String) : Pattern :=
  a "tptp92-ast:functor:alt-1" [quotedAtomicWord lexeme]

def variableAst (lexeme : String) : Pattern :=
  a "tptp92-ast:variable:alt-1" [
    a "tptp92-ast:token:upper-word" [a lexeme]]

def index (value : Nat) : Pattern :=
  TptpResolvedFofLanguageDef.encodeNatIndex value

private def indexZeroRule : GrammarRule :=
  TptpResolvedFofLanguageDef.ownTerms[0]

private def indexSuccRule : GrammarRule :=
  TptpResolvedFofLanguageDef.ownTerms[1]

private theorem indexZeroRule_shape : indexZeroRule = {
    label := "tptp-fof-resolved:index-zero"
    category := "TptpResolvedFof:Index"
    params := []
    syntaxPattern := [.terminal "tptp-fof-resolved:index-zero"]
    evalPolicy? := none } := by
  rfl

private theorem indexSuccRule_shape : indexSuccRule = {
    label := "tptp-fof-resolved:index-succ"
    category := "TptpResolvedFof:Index"
    params := [.simple "predecessor" (.base "TptpResolvedFof:Index")]
    syntaxPattern := [.terminal "tptp-fof-resolved:index-succ"]
    evalPolicy? := none } := by
  rfl

private theorem indexZeroRule_mem :
    indexZeroRule ∈ TptpResolvedFofLanguageDef.language.terms := by
  change indexZeroRule ∈
    TptpFofSymbolLanguageDef.terms ++ TptpResolvedFofLanguageDef.ownTerms
  simp [indexZeroRule]

private theorem indexSuccRule_mem :
    indexSuccRule ∈ TptpResolvedFofLanguageDef.language.terms := by
  change indexSuccRule ∈
    TptpFofSymbolLanguageDef.terms ++ TptpResolvedFofLanguageDef.ownTerms
  simp [indexSuccRule]

private theorem index_typed (value : Nat) :
    HasType TptpResolvedFofLanguageDef.language
      WellSorted.FreeTypeContext.empty []
      (index value) (.base "TptpResolvedFof:Index") := by
  induction value with
  | zero =>
      change HasType TptpResolvedFofLanguageDef.language
        WellSorted.FreeTypeContext.empty []
        (.apply "tptp-fof-resolved:index-zero" [])
        (.base "TptpResolvedFof:Index")
      exact HasType.constructor indexZeroRule_mem
        (by rw [indexZeroRule_shape]; simp [WellSorted.UsesBareCollection])
        ArgumentsHaveTypes.nil
  | succ value inductionHypothesis =>
      have arguments : ArgumentsHaveTypes
          TptpResolvedFofLanguageDef.language
          WellSorted.FreeTypeContext.empty []
          [index value] indexSuccRule.params := by
        rw [indexSuccRule_shape]
        exact .cons (by trivial) rfl inductionHypothesis .nil
      change HasType TptpResolvedFofLanguageDef.language
        WellSorted.FreeTypeContext.empty []
        (.apply "tptp-fof-resolved:index-succ" [index value])
        (.base "TptpResolvedFof:Index")
      exact HasType.constructor indexSuccRule_mem
        (by rw [indexSuccRule_shape]; simp [WellSorted.UsesBareCollection])
        arguments

theorem index_inhabits (value : Nat) :
    inhabits TptpResolvedFofLanguageDef.language
      "TptpResolvedFof:Index" (index value) = true := by
  apply checkHasType_complete_of_object (index_typed value)
  induction value with
  | zero => rfl
  | succ value inductionHypothesis =>
      change WellSorted.isObjectPatternList [index value] = true
      simpa only [WellSorted.isObjectPatternList,
        WellSorted.isObjectPattern, Bool.and_true] using inductionHypothesis

theorem index_injective : Function.Injective index := by
  intro left right equality
  exact TptpFofClausificationBatchLanguageDef.encodeNatIndex_injective equality

private def atomicWordQuotedRule : GrammarRule :=
  TptpOfficialAbstractSyntax.atomicWordQuotedRule

private def functorRule : GrammarRule :=
  TptpOfficialAbstractSyntax.functorRule

private def nameRule : GrammarRule :=
  TptpOfficialAbstractSyntax.nameRule

private def singleQuotedRule : GrammarRule :=
  TptpOfficialAbstractSyntax.singleQuotedRule

private def upperWordRule : GrammarRule :=
  TptpOfficialAbstractSyntax.upperWordRule

private def variableRule : GrammarRule :=
  TptpOfficialAbstractSyntax.variableRule

private theorem atomicWordQuotedRule_shape : atomicWordQuotedRule = {
    label := "tptp92-ast:atomic-word:alt-2"
    category := "Tptp92Ast:atomic-word"
    params := [.simple "single-quoted"
      (.base "Tptp92AstToken:single-quoted")]
    syntaxPattern := []
    evalPolicy? := none } := by rfl

private theorem functorRule_shape : functorRule = {
    label := "tptp92-ast:functor:alt-1"
    category := "Tptp92Ast:functor"
    params := [.simple "atomic-word" (.base "Tptp92Ast:atomic-word")]
    syntaxPattern := []
    evalPolicy? := none } := by rfl

private theorem nameRule_shape : nameRule = {
    label := "tptp92-ast:name:alt-1"
    category := "Tptp92Ast:name"
    params := [.simple "atomic-word" (.base "Tptp92Ast:atomic-word")]
    syntaxPattern := []
    evalPolicy? := none } := by rfl

private theorem singleQuotedRule_shape : singleQuotedRule = {
    label := "tptp92-ast:token:single-quoted"
    category := "Tptp92AstToken:single-quoted"
    params := [.simple "lexeme" (.base "String")]
    syntaxPattern := []
    evalPolicy? := none } := by rfl

private theorem upperWordRule_shape : upperWordRule = {
    label := "tptp92-ast:token:upper-word"
    category := "Tptp92AstToken:upper-word"
    params := [.simple "lexeme" (.base "String")]
    syntaxPattern := []
    evalPolicy? := none } := by rfl

private theorem variableRule_shape : variableRule = {
    label := "tptp92-ast:variable:alt-1"
    category := "Tptp92Ast:variable"
    params := [.simple "upper-word" (.base "Tptp92AstToken:upper-word")]
    syntaxPattern := []
    evalPolicy? := none } := by rfl

private theorem stringAtom_typed (lexeme : String) :
    HasType TptpOfficialAbstractSyntax.language
      WellSorted.FreeTypeContext.empty []
      (a lexeme) (.base "String") := by
  apply HasType.builtinAtom
  refine ⟨TptpOfficialAbstractSyntax.stringTypeDeclaration,
    TptpOfficialAbstractSyntax.stringTypeDeclaration_mem_language, ?_, ?_⟩
  · rw [TptpOfficialAbstractSyntax.stringTypeDeclaration_shape]
  · rw [TptpOfficialAbstractSyntax.stringTypeDeclaration_shape]
    rfl

private theorem singleQuoted_typed (lexeme : String) :
    HasType TptpOfficialAbstractSyntax.language
      WellSorted.FreeTypeContext.empty []
      (a "tptp92-ast:token:single-quoted" [a lexeme])
      (.base "Tptp92AstToken:single-quoted") := by
  have arguments : ArgumentsHaveTypes TptpOfficialAbstractSyntax.language
      WellSorted.FreeTypeContext.empty [] [a lexeme]
      singleQuotedRule.params := by
    rw [singleQuotedRule_shape]
    exact .cons (by trivial) rfl (stringAtom_typed lexeme) .nil
  simpa [a, singleQuotedRule_shape,
      TptpOfficialAbstractSyntax.singleQuotedRule_shape] using
    (HasType.constructor
      TptpOfficialAbstractSyntax.singleQuotedRule_mem_language
      (by
        rw [TptpOfficialAbstractSyntax.singleQuotedRule_shape]
        simp [WellSorted.UsesBareCollection])
      arguments)

private theorem quotedAtomicWord_typed (lexeme : String) :
    HasType TptpOfficialAbstractSyntax.language
      WellSorted.FreeTypeContext.empty []
      (quotedAtomicWord lexeme) (.base "Tptp92Ast:atomic-word") := by
  have arguments : ArgumentsHaveTypes TptpOfficialAbstractSyntax.language
      WellSorted.FreeTypeContext.empty []
      [a "tptp92-ast:token:single-quoted" [a lexeme]]
      atomicWordQuotedRule.params := by
    rw [atomicWordQuotedRule_shape]
    exact .cons (by trivial) rfl (singleQuoted_typed lexeme) .nil
  simpa [a, quotedAtomicWord, atomicWordQuotedRule_shape,
      TptpOfficialAbstractSyntax.atomicWordQuotedRule_shape] using
    (HasType.constructor
      TptpOfficialAbstractSyntax.atomicWordQuotedRule_mem_language
      (by
        rw [TptpOfficialAbstractSyntax.atomicWordQuotedRule_shape]
        simp [WellSorted.UsesBareCollection]) arguments)

private theorem quotedName_typed (lexeme : String) :
    HasType TptpOfficialAbstractSyntax.language
      WellSorted.FreeTypeContext.empty []
      (quotedName lexeme) (.base "Tptp92Ast:name") := by
  have arguments : ArgumentsHaveTypes TptpOfficialAbstractSyntax.language
      WellSorted.FreeTypeContext.empty [] [quotedAtomicWord lexeme]
      nameRule.params := by
    rw [nameRule_shape]
    exact .cons (by trivial) rfl (quotedAtomicWord_typed lexeme) .nil
  simpa [a, quotedName, nameRule_shape,
      TptpOfficialAbstractSyntax.nameRule_shape] using
    (HasType.constructor TptpOfficialAbstractSyntax.nameRule_mem_language
      (by
        rw [TptpOfficialAbstractSyntax.nameRule_shape]
        simp [WellSorted.UsesBareCollection]) arguments)

private theorem quotedFunctor_typed (lexeme : String) :
    HasType TptpOfficialAbstractSyntax.language
      WellSorted.FreeTypeContext.empty []
      (quotedFunctor lexeme) (.base "Tptp92Ast:functor") := by
  have arguments : ArgumentsHaveTypes TptpOfficialAbstractSyntax.language
      WellSorted.FreeTypeContext.empty [] [quotedAtomicWord lexeme]
      functorRule.params := by
    rw [functorRule_shape]
    exact .cons (by trivial) rfl (quotedAtomicWord_typed lexeme) .nil
  simpa [a, quotedFunctor, functorRule_shape,
      TptpOfficialAbstractSyntax.functorRule_shape] using
    (HasType.constructor TptpOfficialAbstractSyntax.functorRule_mem_language
      (by
        rw [TptpOfficialAbstractSyntax.functorRule_shape]
        simp [WellSorted.UsesBareCollection])
      arguments)

private theorem upperWord_typed (lexeme : String) :
    HasType TptpOfficialAbstractSyntax.language
      WellSorted.FreeTypeContext.empty []
      (a "tptp92-ast:token:upper-word" [a lexeme])
      (.base "Tptp92AstToken:upper-word") := by
  have arguments : ArgumentsHaveTypes TptpOfficialAbstractSyntax.language
      WellSorted.FreeTypeContext.empty [] [a lexeme] upperWordRule.params := by
    rw [upperWordRule_shape]
    exact .cons (by trivial) rfl (stringAtom_typed lexeme) .nil
  simpa [a, upperWordRule_shape,
      TptpOfficialAbstractSyntax.upperWordRule_shape] using
    (HasType.constructor TptpOfficialAbstractSyntax.upperWordRule_mem_language
      (by
        rw [TptpOfficialAbstractSyntax.upperWordRule_shape]
        simp [WellSorted.UsesBareCollection])
      arguments)

private theorem variableAst_typed (lexeme : String) :
    HasType TptpOfficialAbstractSyntax.language
      WellSorted.FreeTypeContext.empty []
      (variableAst lexeme) (.base "Tptp92Ast:variable") := by
  have arguments : ArgumentsHaveTypes TptpOfficialAbstractSyntax.language
      WellSorted.FreeTypeContext.empty []
      [a "tptp92-ast:token:upper-word" [a lexeme]] variableRule.params := by
    rw [variableRule_shape]
    exact .cons (by trivial) rfl (upperWord_typed lexeme) .nil
  simpa [a, variableAst, variableRule_shape,
      TptpOfficialAbstractSyntax.variableRule_shape] using
    (HasType.constructor TptpOfficialAbstractSyntax.variableRule_mem_language
      (by
        rw [TptpOfficialAbstractSyntax.variableRule_shape]
        simp [WellSorted.UsesBareCollection])
      arguments)

theorem quotedName_inhabits (lexeme : String) :
    inhabits TptpOfficialAbstractSyntax.language "Tptp92Ast:name"
      (quotedName lexeme) = true := by
  exact checkHasType_complete_of_object (quotedName_typed lexeme) (by rfl)

theorem quotedFunctor_inhabits (lexeme : String) :
    inhabits TptpOfficialAbstractSyntax.language "Tptp92Ast:functor"
      (quotedFunctor lexeme) = true := by
  exact checkHasType_complete_of_object (quotedFunctor_typed lexeme) (by rfl)

theorem variableAst_inhabits (lexeme : String) :
    inhabits TptpOfficialAbstractSyntax.language "Tptp92Ast:variable"
      (variableAst lexeme) = true := by
  exact checkHasType_complete_of_object (variableAst_typed lexeme) (by rfl)

theorem quotedName_injective : Function.Injective quotedName := by
  intro left right equality
  simpa [quotedName, quotedAtomicWord, a] using equality

theorem quotedFunctor_injective : Function.Injective quotedFunctor := by
  intro left right equality
  simpa [quotedFunctor, quotedAtomicWord, a] using equality

theorem variableAst_injective : Function.Injective variableAst := by
  intro left right equality
  simpa [variableAst, a] using equality

/-! ## Executable positive and negative controls -/

namespace Canary

def plan : Plan where
  clauseNames := [
    ⟨index 7, quotedName "cetta_cnf_7"⟩,
    ⟨index 8, quotedName "cetta_cnf_8"⟩]
  variableNames := [
    ⟨index 0, variableAst "X0"⟩,
    ⟨index 1, variableAst "X1"⟩]
  skolemFunctors := [
    ⟨index 2, quotedFunctor "cetta_skolem_2"⟩]
  definitionFunctors := [
    ⟨index 2, quotedFunctor "cetta_definition_2"⟩]

theorem plan_is_valid : plan.valid = true := by
  decide +kernel

theorem clause_lookup_is_exact :
    plan.clauseNames.lookup? (index 8) =
      some (quotedName "cetta_cnf_8") := by
  rfl

theorem relation_environment_exposes_exact_row :
    plan.relationEnv.tuples clauseNameRelation
        [index 7, .fvar "target"] =
      [[index 7, quotedName "cetta_cnf_7"]] := by
  rfl

def duplicateKeyPlan : Plan := {
  plan with
    clauseNames := [
      ⟨index 7, quotedName "first"⟩,
      ⟨index 7, quotedName "second"⟩] }

theorem duplicate_key_is_rejected : duplicateKeyPlan.valid = false := by
  decide +kernel

def duplicateGeneratedTargetPlan : Plan := {
  plan with
    definitionFunctors := [
      ⟨index 3, quotedFunctor "cetta_skolem_2"⟩] }

theorem generated_namespace_collision_is_rejected :
    duplicateGeneratedTargetPlan.valid = false := by
  decide +kernel

def malformedTargetPlan : Plan := {
  plan with
    variableNames := [⟨index 0, a "not-an-official-variable"⟩] }

theorem malformed_target_is_rejected : malformedTargetPlan.valid = false := by
  decide +kernel

end Canary

#print axioms Canary.plan_is_valid
#print axioms Canary.clause_lookup_is_exact
#print axioms Canary.relation_environment_exposes_exact_row
#print axioms Canary.duplicate_key_is_rejected
#print axioms Canary.generated_namespace_collision_is_rejected
#print axioms Canary.malformed_target_is_rejected

end Mettapedia.GSLT.LanguageDef.TptpFofCnfOfficialSerializationPlan
