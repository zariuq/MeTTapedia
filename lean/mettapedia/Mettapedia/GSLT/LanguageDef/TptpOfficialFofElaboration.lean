import Mettapedia.GSLT.LanguageDef.TptpFofBinderResolution
import Mettapedia.GSLT.LanguageDef.TptpNamedFofLanguageDef
import Mettapedia.GSLT.LanguageDef.TptpOfficialAbstractSyntax
import Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationSyntax

/-!
# Official FOF AST elaboration

This module elaborates the grammar-shaped official TPTP 9.2 FOF abstract
syntax into the named semantic FOF consumed by binder resolution.  The raw
annotated formula, name, role, and annotations remain attached to every
successful result.

The elaborator is deliberately partial.  A malformed or non-FOF pattern is
rejected rather than guessed.  It performs no normalization, clausification,
proof search, or inference verification.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialFofElaboration

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationSyntax
open Mettapedia.GSLT.LanguageDef.TptpFofBinderResolution
open Mettapedia.GSLT.LanguageDef.TptpFofSymbolIdentity
open Mettapedia.GSLT.LanguageDef.TptpNamedFofLanguageDef

def decodeVariableName? : Pattern -> Option String
  | .apply "tptp92-ast:variable:alt-1" [
      .apply "tptp92-ast:token:upper-word" [.apply lexeme []]] =>
        some lexeme
  | _ => none

def decodeFunctorName? : Pattern -> Option String
  | .apply "tptp92-ast:functor:alt-1" [
      .apply "tptp92-ast:atomic-word:alt-1" [
        .apply "tptp92-ast:token:lower-word" [.apply lexeme []]]]
  | .apply "tptp92-ast:functor:alt-1" [
      .apply "tptp92-ast:atomic-word:alt-2" [
        .apply "tptp92-ast:token:single-quoted" [.apply lexeme []]]]
  | .apply "tptp92-ast:functor:alt-1" [
      .apply "tptp92-ast:atomic-word:alt-3" [
        .apply "tptp92-ast:token:back-quoted" [.apply lexeme []]]] =>
        some lexeme
  | _ => none

def decodeDefinedFunctorName? : Pattern -> Option String
  | .apply "tptp92-ast:defined-functor:alt-1" [
      .apply "tptp92-ast:atomic-defined-word:alt-1" [
        .apply "tptp92-ast:token:dollar-word" [.apply lexeme []]]] =>
      some lexeme
  | _ => none

def decodeSystemFunctorName? : Pattern -> Option String
  | .apply "tptp92-ast:system-functor:alt-1" [
      .apply "tptp92-ast:atomic-system-word:alt-1" [
        .apply "tptp92-ast:token:dollar-dollar-word" [.apply lexeme []]]] =>
      some lexeme
  | _ => none

def decodeNumberName? : Pattern -> Option String
  | .apply "tptp92-ast:number:alt-1" [
      .apply "tptp92-ast:token:integer" [.apply lexeme []]]
  | .apply "tptp92-ast:number:alt-2" [
      .apply "tptp92-ast:token:rational" [.apply lexeme []]]
  | .apply "tptp92-ast:number:alt-3" [
      .apply "tptp92-ast:token:real" [.apply lexeme []]] => some lexeme
  | _ => none

def decodeNumberHead? : Pattern -> Option FunctionHead
  | .apply "tptp92-ast:number:alt-1" [
      .apply "tptp92-ast:token:integer" [.apply lexeme []]] =>
      some ⟨.integer, lexeme⟩
  | .apply "tptp92-ast:number:alt-2" [
      .apply "tptp92-ast:token:rational" [.apply lexeme []]] =>
      some ⟨.rational, lexeme⟩
  | .apply "tptp92-ast:number:alt-3" [
      .apply "tptp92-ast:token:real" [.apply lexeme []]] =>
      some ⟨.real, lexeme⟩
  | _ => none

private def conjunction : List NamedFormula -> NamedFormula
  | [] => .verum
  | formula :: formulas => formulas.foldl NamedFormula.and formula

private def disjunction : List NamedFormula -> NamedFormula
  | [] => .falsum
  | formula :: formulas => formulas.foldl NamedFormula.or formula

private def bindAll (binders : List String) (body : NamedFormula) : NamedFormula :=
  binders.foldr NamedFormula.all body

private def bindEx (binders : List String) (body : NamedFormula) : NamedFormula :=
  binders.foldr NamedFormula.ex body

mutual
  def decodeTerm? : Pattern -> Option NamedTerm
    | .apply "tptp92-ast:fof-term:alt-1" [term] => decodeFunctionTerm? term
    | .apply "tptp92-ast:fof-term:alt-2" [variablePattern] =>
        NamedTerm.variable <$> decodeVariableName? variablePattern
    | _ => none

  def decodeArguments? : Pattern -> Option (List NamedTerm)
    | .apply "tptp92-ast:fof-arguments:alt-1" [term] =>
        return [← decodeTerm? term]
    | .apply "tptp92-ast:fof-arguments:alt-2" [term, arguments] =>
        return (← decodeTerm? term) :: (← decodeArguments? arguments)
    | _ => none

  def decodeFunctionTerm? : Pattern -> Option NamedTerm
    | .apply "tptp92-ast:fof-function-term:alt-1" [term] =>
        decodePlainTerm? term
    | .apply "tptp92-ast:fof-function-term:alt-2" [term] =>
        decodeDefinedTerm? term
    | .apply "tptp92-ast:fof-function-term:alt-3" [term] =>
        decodeSystemTerm? term
    | _ => none

  def decodePlainTerm? : Pattern -> Option NamedTerm
    | .apply "tptp92-ast:fof-plain-term:alt-1" [
        .apply "tptp92-ast:constant:alt-1" [functor]] =>
        return .function ⟨.plain, ← decodeFunctorName? functor⟩ []
    | .apply "tptp92-ast:fof-plain-term:alt-2" [functor, arguments] =>
        return .function ⟨.plain, ← decodeFunctorName? functor⟩
          (← decodeArguments? arguments)
    | _ => none

  def decodeDefinedTerm? : Pattern -> Option NamedTerm
    | .apply "tptp92-ast:fof-defined-term:alt-1" [
        .apply "tptp92-ast:defined-term:alt-1" [number]] =>
        return .function (← decodeNumberHead? number) []
    | .apply "tptp92-ast:fof-defined-term:alt-1" [
        .apply "tptp92-ast:defined-term:alt-2" [
          .apply "tptp92-ast:token:distinct-object" [.apply lexeme []]]] =>
        some (.function ⟨.distinctObject, lexeme⟩ [])
    | .apply "tptp92-ast:fof-defined-term:alt-2" [
        .apply "tptp92-ast:fof-defined-atomic-term:alt-1" [term]] =>
        decodeDefinedPlainTerm? term
    | _ => none

  def decodeDefinedPlainTerm? : Pattern -> Option NamedTerm
    | .apply "tptp92-ast:fof-defined-plain-term:alt-1" [
        .apply "tptp92-ast:defined-constant:alt-1" [functor]] =>
        return .function ⟨.defined, ← decodeDefinedFunctorName? functor⟩ []
    | .apply "tptp92-ast:fof-defined-plain-term:alt-2" [functor, arguments] =>
        return .function ⟨.defined, ← decodeDefinedFunctorName? functor⟩
          (← decodeArguments? arguments)
    | _ => none

  def decodeSystemTerm? : Pattern -> Option NamedTerm
    | .apply "tptp92-ast:fof-system-term:alt-1" [
        .apply "tptp92-ast:system-constant:alt-1" [functor]] =>
        return .function ⟨.system, ← decodeSystemFunctorName? functor⟩ []
    | .apply "tptp92-ast:fof-system-term:alt-2" [functor, arguments] =>
        return .function ⟨.system, ← decodeSystemFunctorName? functor⟩
          (← decodeArguments? arguments)
    | _ => none

  def decodeFormula? : Pattern -> Option NamedFormula
    | .apply "tptp92-ast:fof-formula:alt-1" [formula] =>
        decodeLogicFormula? formula
    | .apply "tptp92-ast:fof-formula:alt-2" [formula] =>
        decodeSequent? formula
    | _ => none

  def decodeLogicFormula? : Pattern -> Option NamedFormula
    | .apply "tptp92-ast:fof-logic-formula:alt-1" [formula] =>
        decodeBinaryFormula? formula
    | .apply "tptp92-ast:fof-logic-formula:alt-2" [formula] =>
        decodeUnaryFormula? formula
    | .apply "tptp92-ast:fof-logic-formula:alt-3" [formula] =>
        decodeUnitaryFormula? formula
    | _ => none

  def decodeBinaryFormula? : Pattern -> Option NamedFormula
    | .apply "tptp92-ast:fof-binary-formula:alt-1" [formula] =>
        decodeBinaryNonassoc? formula
    | .apply "tptp92-ast:fof-binary-formula:alt-2" [formula] =>
        decodeBinaryAssoc? formula
    | _ => none

  def decodeBinaryNonassoc? : Pattern -> Option NamedFormula
    | .apply "tptp92-ast:fof-binary-nonassoc:alt-1"
        [left, connective, right] => do
        let left <- decodeUnitFormula? left
        let right <- decodeUnitFormula? right
        match connective with
        | .apply "tptp92-ast:nonassoc-connective:alt-1" [] =>
            some (.iff left right)
        | .apply "tptp92-ast:nonassoc-connective:alt-2" [] =>
            some (.implies left right)
        | .apply "tptp92-ast:nonassoc-connective:alt-3" [] =>
            some (.reverseImplies left right)
        | .apply "tptp92-ast:nonassoc-connective:alt-4" [] =>
            some (.xor left right)
        | .apply "tptp92-ast:nonassoc-connective:alt-5" [] =>
            some (.nor left right)
        | .apply "tptp92-ast:nonassoc-connective:alt-6" [] =>
            some (.nand left right)
        | _ => none
    | _ => none

  def decodeBinaryAssoc? : Pattern -> Option NamedFormula
    | .apply "tptp92-ast:fof-binary-assoc:alt-1" [formula] =>
        decodeOrFormula? formula
    | .apply "tptp92-ast:fof-binary-assoc:alt-2" [formula] =>
        decodeAndFormula? formula
    | _ => none

  def decodeOrFormula? : Pattern -> Option NamedFormula
    | .apply "tptp92-ast:fof-or-formula:alt-1" [left, right] =>
        return .or (← decodeUnitFormula? left) (← decodeUnitFormula? right)
    | .apply "tptp92-ast:fof-or-formula:alt-2" [left, right] =>
        return .or (← decodeOrFormula? left) (← decodeUnitFormula? right)
    | _ => none

  def decodeAndFormula? : Pattern -> Option NamedFormula
    | .apply "tptp92-ast:fof-and-formula:alt-1" [left, right] =>
        return .and (← decodeUnitFormula? left) (← decodeUnitFormula? right)
    | .apply "tptp92-ast:fof-and-formula:alt-2" [left, right] =>
        return .and (← decodeAndFormula? left) (← decodeUnitFormula? right)
    | _ => none

  def decodeUnaryFormula? : Pattern -> Option NamedFormula
    | .apply "tptp92-ast:fof-unary-formula:alt-1"
        [.apply "tptp92-ast:unary-connective:alt-1" [], body] =>
        NamedFormula.not <$> decodeUnitFormula? body
    | .apply "tptp92-ast:fof-unary-formula:alt-2" [formula] =>
        decodeInfixUnary? formula
    | _ => none

  def decodeUnitFormula? : Pattern -> Option NamedFormula
    | .apply "tptp92-ast:fof-unit-formula:alt-1" [formula] =>
        decodeUnitaryFormula? formula
    | .apply "tptp92-ast:fof-unit-formula:alt-2" [formula] =>
        decodeUnaryFormula? formula
    | _ => none

  def decodeUnitaryFormula? : Pattern -> Option NamedFormula
    | .apply "tptp92-ast:fof-unitary-formula:alt-1" [formula] =>
        decodeQuantifiedFormula? formula
    | .apply "tptp92-ast:fof-unitary-formula:alt-2" [formula] =>
        decodeAtomicFormula? formula
    | .apply "tptp92-ast:fof-unitary-formula:alt-3" [formula] =>
        decodeLogicFormula? formula
    | _ => none

  def decodeQuantifiedFormula? : Pattern -> Option NamedFormula
    | .apply "tptp92-ast:fof-quantified-formula:alt-1"
        [quantifier, variablePatterns, body] => do
        let binderNames <- decodeVariableList? variablePatterns
        let body <- decodeUnitFormula? body
        match quantifier with
        | .apply "tptp92-ast:fof-quantifier:alt-1" [] =>
            some (bindAll binderNames body)
        | .apply "tptp92-ast:fof-quantifier:alt-2" [] =>
            some (bindEx binderNames body)
        | _ => none
    | _ => none

  def decodeVariableList? : Pattern -> Option (List String)
    | .apply "tptp92-ast:fof-variable-list:alt-1" [variablePattern] =>
        return [← decodeVariableName? variablePattern]
    | .apply "tptp92-ast:fof-variable-list:alt-2"
        [variablePattern, variablePatterns] =>
        return (← decodeVariableName? variablePattern) ::
          (← decodeVariableList? variablePatterns)
    | _ => none

  def decodeAtomicFormula? : Pattern -> Option NamedFormula
    | .apply "tptp92-ast:fof-atomic-formula:alt-1" [formula] =>
        decodePlainAtomicFormula? formula
    | .apply "tptp92-ast:fof-atomic-formula:alt-2" [formula] =>
        decodeDefinedAtomicFormula? formula
    | .apply "tptp92-ast:fof-atomic-formula:alt-3" [formula] =>
        decodeSystemAtomicFormula? formula
    | _ => none

  def decodePlainAtomicFormula? : Pattern -> Option NamedFormula
    | .apply "tptp92-ast:fof-plain-atomic-formula:alt-1" [
        .apply "tptp92-ast:fof-plain-term:alt-1" [
          .apply "tptp92-ast:constant:alt-1" [functor]]] =>
        return .predicate ⟨.plain, ← decodeFunctorName? functor⟩ []
    | .apply "tptp92-ast:fof-plain-atomic-formula:alt-1" [
        .apply "tptp92-ast:fof-plain-term:alt-2" [functor, arguments]] =>
        return .predicate ⟨.plain, ← decodeFunctorName? functor⟩
          (← decodeArguments? arguments)
    | _ => none

  def decodeDefinedAtomicFormula? : Pattern -> Option NamedFormula
    | .apply "tptp92-ast:fof-defined-atomic-formula:alt-1" [formula] =>
        decodeDefinedPlainFormula? formula
    | .apply "tptp92-ast:fof-defined-atomic-formula:alt-2" [formula] =>
        decodeDefinedInfixFormula? formula
    | _ => none

  def decodeDefinedPlainFormula? : Pattern -> Option NamedFormula
    | .apply "tptp92-ast:fof-defined-plain-formula:alt-1" [term] => do
        let term <- decodeDefinedPlainTerm? term
        match term with
        | .function ⟨.defined, "$true"⟩ [] => some .verum
        | .function ⟨.defined, "$false"⟩ [] => some .falsum
        | .function ⟨.defined, name⟩ (argument :: arguments) =>
            some (.predicate ⟨.defined, name⟩ (argument :: arguments))
        | _ => none
    | _ => none

  def decodeDefinedInfixFormula? : Pattern -> Option NamedFormula
    | .apply "tptp92-ast:fof-defined-infix-formula:alt-1"
        [left, .apply "tptp92-ast:defined-infix-pred:alt-1"
          [.apply "tptp92-ast:infix-equality:alt-1" []], right] =>
        return .equal (← decodeTerm? left) (← decodeTerm? right)
    | _ => none

  def decodeSystemAtomicFormula? : Pattern -> Option NamedFormula
    | .apply "tptp92-ast:fof-system-atomic-formula:alt-1" [
        .apply "tptp92-ast:fof-system-term:alt-1" [
          .apply "tptp92-ast:system-constant:alt-1" [functor]]] =>
        return .predicate ⟨.system, ← decodeSystemFunctorName? functor⟩ []
    | .apply "tptp92-ast:fof-system-atomic-formula:alt-1" [
        .apply "tptp92-ast:fof-system-term:alt-2" [functor, arguments]] =>
        return .predicate ⟨.system, ← decodeSystemFunctorName? functor⟩
          (← decodeArguments? arguments)
    | _ => none

  def decodeInfixUnary? : Pattern -> Option NamedFormula
    | .apply "tptp92-ast:fof-infix-unary:alt-1"
        [left, .apply "tptp92-ast:infix-inequality:alt-1" [], right] =>
        return .not (.equal (← decodeTerm? left) (← decodeTerm? right))
    | _ => none

  def decodeSequent? : Pattern -> Option NamedFormula
    | .apply "tptp92-ast:fof-sequent:alt-1"
        [left, .apply "tptp92-ast:gentzen-arrow:alt-1" [], right] =>
        return .implies (conjunction (← decodeFormulaTuple? left))
          (disjunction (← decodeFormulaTuple? right))
    | .apply "tptp92-ast:fof-sequent:alt-2" [sequent] =>
        decodeSequent? sequent
    | _ => none

  def decodeFormulaTuple? : Pattern -> Option (List NamedFormula)
    | .apply "tptp92-ast:fof-formula-tuple:alt-1" [] => some []
    | .apply "tptp92-ast:fof-formula-tuple:alt-2" [formulas] =>
        decodeFormulaTupleList? formulas
    | _ => none

  def decodeFormulaTupleList? : Pattern -> Option (List NamedFormula)
    | .apply "tptp92-ast:fof-formula-tuple-list:alt-1" [formula, rest] =>
        return (← decodeLogicFormula? formula) ::
          (← decodeCommaFormulaList? rest)
    | _ => none

  def decodeCommaFormulaList? : Pattern -> Option (List NamedFormula)
    | .apply "tptp92-ast:list:tptp92ast-comma-fof-logic-formula:nil" [] =>
        some []
    | .apply "tptp92-ast:list:tptp92ast-comma-fof-logic-formula:cons"
        [.apply "tptp92-ast:comma-fof-logic-formula:alt-1" [formula], rest] =>
        return (← decodeLogicFormula? formula) ::
          (← decodeCommaFormulaList? rest)
    | _ => none
end

structure ElaboratedFof where
  raw : Pattern
  name : String
  role : String
  sourceFormula : Pattern
  annotations : Pattern
  formula : NamedFormula

def elaborateAnnotatedFof? (raw : Pattern) : Option ElaboratedFof := do
  match raw with
  | .apply "tptp92-ast:fof-annotated:alt-1"
      [name, role, sourceFormula, annotations] =>
      some {
        raw
        name := ← decodeName? name
        role := ← decodeRoleLexeme? role
        sourceFormula
        annotations
        formula := ← decodeFormula? sourceFormula
      }
  | _ => none

/-- The semantic elaborator's target-owned representation.  This function is
the reference action that the authored AST-to-named-FOF rewrite system must
implement exactly. -/
def lowerFormulaToNamedPattern? (sourceFormula : Pattern) : Option Pattern :=
  (decodeFormula? sourceFormula).map encodeFormula

theorem elaborate_preserves_source {raw : Pattern} {result : ElaboratedFof}
    (success : elaborateAnnotatedFof? raw = some result) :
    result.raw = raw := by
  simp only [elaborateAnnotatedFof?] at success
  split at success
  · rcases Option.bind_eq_some_iff.mp success with
      ⟨decodedName, _, remaining⟩
    rcases Option.bind_eq_some_iff.mp remaining with
      ⟨decodedRole, _, remaining⟩
    rcases Option.bind_eq_some_iff.mp remaining with
      ⟨decodedFormula, _, resultEquality⟩
    cases resultEquality
    rfl
  · contradiction

namespace Canary

private def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

def token (kind lexeme : String) : Pattern := a kind [a lexeme]
def variablePattern (name : String) : Pattern :=
  a "tptp92-ast:variable:alt-1" [token "tptp92-ast:token:upper-word" name]
def variableTerm (name : String) : Pattern :=
  a "tptp92-ast:fof-term:alt-2" [variablePattern name]
def lowerAtomicWord (lexeme : String) : Pattern :=
  a "tptp92-ast:atomic-word:alt-1" [
    token "tptp92-ast:token:lower-word" lexeme]
def quotedAtomicWord (lexeme : String) : Pattern :=
  a "tptp92-ast:atomic-word:alt-2" [
    token "tptp92-ast:token:single-quoted" lexeme]
def functorPattern (atomicWord : Pattern) : Pattern :=
  a "tptp92-ast:functor:alt-1" [atomicWord]
def equality (left right : Pattern) : Pattern :=
  a "tptp92-ast:fof-atomic-formula:alt-2" [
    a "tptp92-ast:fof-defined-atomic-formula:alt-2" [
      a "tptp92-ast:fof-defined-infix-formula:alt-1" [
        left,
        a "tptp92-ast:defined-infix-pred:alt-1" [
          a "tptp92-ast:infix-equality:alt-1"],
        right]]]
def atomicUnit (formula : Pattern) : Pattern :=
  a "tptp92-ast:fof-unit-formula:alt-1" [
    a "tptp92-ast:fof-unitary-formula:alt-2" [formula]]
def unitaryUnit (formula : Pattern) : Pattern :=
  a "tptp92-ast:fof-unit-formula:alt-1" [formula]
def quantified (quantifier variablePatterns body : Pattern) : Pattern :=
  a "tptp92-ast:fof-unitary-formula:alt-1" [
    a "tptp92-ast:fof-quantified-formula:alt-1"
      [quantifier, variablePatterns, body]]
def logicUnit (formula : Pattern) : Pattern :=
  a "tptp92-ast:fof-logic-formula:alt-3" [formula]

def shadowingFormula : Pattern :=
  a "tptp92-ast:fof-formula:alt-1" [logicUnit <|
    quantified
      (a "tptp92-ast:fof-quantifier:alt-1")
      (a "tptp92-ast:fof-variable-list:alt-1" [variablePattern "X"])
      (unitaryUnit <| quantified
        (a "tptp92-ast:fof-quantifier:alt-2")
        (a "tptp92-ast:fof-variable-list:alt-1" [variablePattern "X"])
        (atomicUnit (equality (variableTerm "X") (variableTerm "X"))))]

def shadowingNamed : NamedFormula :=
  .all "X" (.ex "X" (.equal (.variable "X") (.variable "X")))

def annotatedShadowing : Pattern :=
  a "tptp92-ast:fof-annotated:alt-1" [
    a "tptp92-ast:name:alt-1" [
      a "tptp92-ast:atomic-word:alt-1" [
        token "tptp92-ast:token:lower-word" "shadowing"]],
    a "tptp92-ast:formula-role:alt-1" [
      token "tptp92-ast:token:lower-word" "axiom"],
    shadowingFormula,
    a "tptp92-ast:annotations:alt-2"]

theorem official_shadowing_elaborates_exactly :
    decodeFormula? shadowingFormula = some shadowingNamed := by
  simp [shadowingFormula, shadowingNamed, logicUnit, quantified, unitaryUnit,
    atomicUnit, equality, variableTerm, variablePattern, token, a,
    decodeFormula?, decodeLogicFormula?, decodeUnitaryFormula?,
    decodeQuantifiedFormula?, decodeVariableList?, decodeUnitFormula?,
    decodeAtomicFormula?, decodeDefinedAtomicFormula?,
    decodeDefinedInfixFormula?, decodeTerm?, decodeVariableName?,
    bindAll, bindEx]

theorem official_shadowing_lowers_to_target_language :
    lowerFormulaToNamedPattern? shadowingFormula =
      some (encodeFormula shadowingNamed) := by
  simp [lowerFormulaToNamedPattern?, official_shadowing_elaborates_exactly]

theorem official_shadowing_resolves_exactly :
    (decodeFormula? shadowingFormula).bind resolveClosedFormula? =
      some (.all (.ex (.equal (.bvar 0) (.bvar 0)))) := by
  simp [official_shadowing_elaborates_exactly, resolveClosedFormula?,
    shadowingNamed, resolveFormula?, resolveTerm?, lookupBinder?]

theorem annotated_elaboration_retains_source_metadata :
    elaborateAnnotatedFof? annotatedShadowing = some {
      raw := annotatedShadowing
      name := "shadowing"
      role := "axiom"
      sourceFormula := shadowingFormula
      annotations := a "tptp92-ast:annotations:alt-2"
      formula := shadowingNamed
    } := by
  simp [elaborateAnnotatedFof?, annotatedShadowing, decodeName?,
    decodeAtomicWord?, decodeRoleLexeme?, decodeLexeme?,
    official_shadowing_elaborates_exactly, token, a]

def emptySequent : Pattern :=
  a "tptp92-ast:fof-formula:alt-2" [
    a "tptp92-ast:fof-sequent:alt-1" [
      a "tptp92-ast:fof-formula-tuple:alt-1",
      a "tptp92-ast:gentzen-arrow:alt-1",
      a "tptp92-ast:fof-formula-tuple:alt-1"]]

theorem empty_sequent_has_truth_to_falsity_semantics :
    decodeFormula? emptySequent = some (.implies .verum .falsum) := by
  rfl

def definedNullaryFormula (lexeme : String) : Pattern :=
  a "tptp92-ast:fof-formula:alt-1" [logicUnit <|
    a "tptp92-ast:fof-unitary-formula:alt-2" [
      a "tptp92-ast:fof-atomic-formula:alt-2" [
        a "tptp92-ast:fof-defined-atomic-formula:alt-1" [
          a "tptp92-ast:fof-defined-plain-formula:alt-1" [
            a "tptp92-ast:fof-defined-plain-term:alt-1" [
              a "tptp92-ast:defined-constant:alt-1" [
                a "tptp92-ast:defined-functor:alt-1" [
                  a "tptp92-ast:atomic-defined-word:alt-1" [
                    token "tptp92-ast:token:dollar-word" lexeme]]]]]]]]]

theorem defined_true_is_verum :
    decodeFormula? (definedNullaryFormula "$true") = some .verum := by
  rfl

theorem defined_false_is_falsum :
    decodeFormula? (definedNullaryFormula "$false") = some .falsum := by
  rfl

/-- The structural grammar has a deliberately broad term carrier, but the
TPTP semantic production admits only `$true` and `$false` as nullary defined
propositions. -/
theorem other_nullary_defined_word_is_not_a_formula :
    decodeFormula? (definedNullaryFormula "$other") = none := by
  rfl

theorem malformed_formula_fails_closed :
    decodeFormula? (a "tptp92-ast:fof-formula:alt-1" [a "invented"]) = none := by
  rfl

theorem wrong_variable_token_category_is_rejected :
    decodeTerm? (a "tptp92-ast:fof-term:alt-2" [
      a "tptp92-ast:variable:alt-1" [
        token "tptp92-ast:token:lower-word" "x"]]) = none := by
  rfl

theorem wrong_number_token_category_is_rejected :
    decodeTerm? (a "tptp92-ast:fof-term:alt-1" [
      a "tptp92-ast:fof-function-term:alt-2" [
        a "tptp92-ast:fof-defined-term:alt-1" [
          a "tptp92-ast:defined-term:alt-1" [
            a "tptp92-ast:number:alt-1" [
              token "tptp92-ast:token:rational" "1/2"]]]]]) = none := by
  rfl

/-- The official scanner removes the outer quote delimiters.  Consequently
the lower-word and single-quoted presentations of one atomic word elaborate
to the same semantic symbol identity. -/
theorem lower_and_single_quoted_atomic_words_share_identity
    (lexeme : String) :
    decodeFunctorName? (functorPattern (lowerAtomicWord lexeme)) =
      decodeFunctorName? (functorPattern (quotedAtomicWord lexeme)) := by
  rfl

end Canary

#print axioms elaborate_preserves_source
#print axioms Canary.official_shadowing_elaborates_exactly
#print axioms Canary.official_shadowing_lowers_to_target_language
#print axioms Canary.official_shadowing_resolves_exactly
#print axioms Canary.annotated_elaboration_retains_source_metadata
#print axioms Canary.empty_sequent_has_truth_to_falsity_semantics
#print axioms Canary.defined_true_is_verum
#print axioms Canary.defined_false_is_falsum
#print axioms Canary.other_nullary_defined_word_is_not_a_formula
#print axioms Canary.malformed_formula_fails_closed
#print axioms Canary.wrong_variable_token_category_is_rejected
#print axioms Canary.wrong_number_token_category_is_rejected
#print axioms Canary.lower_and_single_quoted_atomic_words_share_identity

end Mettapedia.GSLT.LanguageDef.TptpOfficialFofElaboration
