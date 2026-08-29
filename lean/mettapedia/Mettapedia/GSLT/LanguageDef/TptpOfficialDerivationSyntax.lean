import Mettapedia.GSLT.LanguageDef.TptpOfficialSemanticCarrierNTT

/-!
# Calculus-neutral TSTP derivation syntax

The official TPTP abstract syntax represents every proof annotation as a
recursive `source`.  This module gives that syntax a typed, lossless view for
all annotated formula families.  It deliberately does not assign logical
meaning to inference-rule names: calculus semantics belongs to separately
validated services.

The view preserves parent order, parent details, useful information, optional
information, source alternatives, occurrence identity, and source spans.  Its
encoders return the exact official-AST and semantic-carrier patterns, so later
chronological admission and verification can be proved against the actual
TPTP authority rather than a resolution-specific lookalike.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationSyntax

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.TptpOfficialSemanticCarrier

private def a (label : String) (arguments : List Pattern := []) : Pattern :=
  .apply label arguments

/-! ## Shared lexical projections -/

def decodeLexeme? : Pattern -> Option String
  | .apply _ [.apply lexeme []] => some lexeme
  | _ => none

def decodeAtomicWord? : Pattern -> Option String
  | .apply "tptp92-ast:atomic-word:alt-1" [token]
  | .apply "tptp92-ast:atomic-word:alt-2" [token]
  | .apply "tptp92-ast:atomic-word:alt-3" [token] => decodeLexeme? token
  | _ => none

def decodeName? : Pattern -> Option String
  | .apply "tptp92-ast:name:alt-1" [word] => decodeAtomicWord? word
  | .apply "tptp92-ast:name:alt-2" [token] => decodeLexeme? token
  | _ => none

def decodeRoleLexeme? : Pattern -> Option String
  | .apply "tptp92-ast:formula-role:alt-1" [token] => decodeLexeme? token
  | .apply "tptp92-ast:formula-role:alt-2" [token, _refinement] =>
      decodeLexeme? token
  | _ => none

def decodeInferenceRule? : Pattern -> Option String
  | .apply "tptp92-ast:inference-rule:alt-1" [word] => decodeAtomicWord? word
  | _ => none

def decodeIntroType? : Pattern -> Option String
  | .apply "tptp92-ast:intro-type:alt-1" [word] => decodeAtomicWord? word
  | _ => none

/-! ## Recursive source validation and dependency extraction

The official source term remains the serialization authority.  `SourceHead`
is a one-layer view used by calculus services, while `sourceReferences?`
validates the entire recursive source and returns every named dependency in
official left-to-right order.  This avoids replacing the official recursive
grammar with a second private proof language.
-/

inductive SourceHead where
  | named (name : Pattern)
  | inference (rule usefulInfo parents : Pattern)
  | introduced (introType usefulInfo parents : Pattern)
  | external (source : Pattern)
  | unknown
  | alternatives (sources : Pattern)
  deriving DecidableEq, Repr

def decodeSourceHead? : Pattern -> Option SourceHead
  | .apply "tptp92-ast:source:alt-1" [
      .apply "tptp92-ast:dag-source:alt-1" [name]] =>
      some (.named name)
  | .apply "tptp92-ast:source:alt-1" [
      .apply "tptp92-ast:dag-source:alt-2" [
        .apply "tptp92-ast:inference-record:alt-1"
          [rule, usefulInfo, parents]]] =>
      some (.inference rule usefulInfo parents)
  | .apply "tptp92-ast:source:alt-2" [
      .apply "tptp92-ast:internal-source:alt-1"
        [introType, usefulInfo, parents]] =>
      some (.introduced introType usefulInfo parents)
  | .apply "tptp92-ast:source:alt-3" [source] =>
      some (.external source)
  | .apply "tptp92-ast:source:alt-4" [] => some .unknown
  | .apply "tptp92-ast:source:alt-5" [sources] =>
      some (.alternatives sources)
  | _ => none

mutual
  def sourceReferences? : Pattern -> Option (List Pattern)
    | .apply "tptp92-ast:source:alt-1" [
        .apply "tptp92-ast:dag-source:alt-1" [name]] =>
        some [name]
    | .apply "tptp92-ast:source:alt-1" [
        .apply "tptp92-ast:dag-source:alt-2" [
          .apply "tptp92-ast:inference-record:alt-1"
            [_rule, _usefulInfo, parents]]] =>
        parentReferences? parents
    | .apply "tptp92-ast:source:alt-2" [
        .apply "tptp92-ast:internal-source:alt-1"
          [_introType, _usefulInfo, parents]] =>
        parentReferences? parents
    | .apply "tptp92-ast:source:alt-3" [_external] => some []
    | .apply "tptp92-ast:source:alt-4" [] => some []
    | .apply "tptp92-ast:source:alt-5" [sources] =>
        alternativeReferences? sources
    | _ => none

  def parentInfoReferences? : Pattern -> Option (List Pattern)
    | .apply "tptp92-ast:parent-info:alt-1" [source, _details] =>
        sourceReferences? source
    | _ => none

  def commaParentReferences? : Pattern -> Option (List Pattern)
    | .apply "tptp92-ast:list:tptp92ast-comma-parent-info:nil" [] => some []
    | .apply "tptp92-ast:list:tptp92ast-comma-parent-info:cons" [
        .apply "tptp92-ast:comma-parent-info:alt-1" [parent], rest] => do
        let first <- parentInfoReferences? parent
        let tail <- commaParentReferences? rest
        some (first ++ tail)
    | _ => none

  def parentReferences? : Pattern -> Option (List Pattern)
    | .apply "tptp92-ast:parents:alt-1" [] => some []
    | .apply "tptp92-ast:parents:alt-2" [
        .apply "tptp92-ast:parent-list:alt-1" [parent, rest]] => do
        let first <- parentInfoReferences? parent
        let tail <- commaParentReferences? rest
        some (first ++ tail)
    | _ => none

  def alternativeReferences? : Pattern -> Option (List Pattern)
    | .apply "tptp92-ast:sources:alt-1" [source] =>
        sourceReferences? source
    | .apply "tptp92-ast:sources:alt-2" [source, rest] => do
        let first <- sourceReferences? source
        let tail <- alternativeReferences? rest
        some (first ++ tail)
    | _ => none
end

/-! ## All-family annotated formulae -/

inductive FormulaDialect where
  | thf
  | tff
  | tcf
  | fof
  | cnf
  | tpi
  deriving DecidableEq, Repr

structure AnnotatedFormulaView where
  dialect : FormulaDialect
  name : Pattern
  role : Pattern
  formula : Pattern
  annotations : Pattern
  deriving DecidableEq, Repr

def encodeAnnotatedFormula (view : AnnotatedFormulaView) : FormulaPayload :=
  let arguments := [view.name, view.role, view.formula, view.annotations]
  match view.dialect with
  | .thf => .thf (a "tptp92-ast:thf-annotated:alt-1" arguments)
  | .tff => .tff (a "tptp92-ast:tff-annotated:alt-1" arguments)
  | .tcf => .tcf (a "tptp92-ast:tcf-annotated:alt-1" arguments)
  | .fof => .fof (a "tptp92-ast:fof-annotated:alt-1" arguments)
  | .cnf => .cnf (a "tptp92-ast:cnf-annotated:alt-1" arguments)
  | .tpi => .tpi (a "tptp92-ast:tpi-annotated:alt-1" arguments)

def decodeAnnotatedFormula? : FormulaPayload -> Option AnnotatedFormulaView
  | .thf (.apply "tptp92-ast:thf-annotated:alt-1"
      [name, role, formula, annotations]) =>
      some ⟨.thf, name, role, formula, annotations⟩
  | .tff (.apply "tptp92-ast:tff-annotated:alt-1"
      [name, role, formula, annotations]) =>
      some ⟨.tff, name, role, formula, annotations⟩
  | .tcf (.apply "tptp92-ast:tcf-annotated:alt-1"
      [name, role, formula, annotations]) =>
      some ⟨.tcf, name, role, formula, annotations⟩
  | .fof (.apply "tptp92-ast:fof-annotated:alt-1"
      [name, role, formula, annotations]) =>
      some ⟨.fof, name, role, formula, annotations⟩
  | .cnf (.apply "tptp92-ast:cnf-annotated:alt-1"
      [name, role, formula, annotations]) =>
      some ⟨.cnf, name, role, formula, annotations⟩
  | .tpi (.apply "tptp92-ast:tpi-annotated:alt-1"
      [name, role, formula, annotations]) =>
      some ⟨.tpi, name, role, formula, annotations⟩
  | _ => none

inductive AnnotationView where
  | absent
  | sourced (source optionalInfo : Pattern)
  deriving DecidableEq, Repr

def encodeAnnotations : AnnotationView -> Pattern
  | .absent => a "tptp92-ast:annotations:alt-2"
  | .sourced source optionalInfo =>
      a "tptp92-ast:annotations:alt-1"
        [source, optionalInfo]

def decodeAnnotations? : Pattern -> Option AnnotationView
  | .apply "tptp92-ast:annotations:alt-2" [] => some .absent
  | .apply "tptp92-ast:annotations:alt-1" [source, optionalInfo] => do
      let _references <- sourceReferences? source
      some (.sourced source optionalInfo)
  | _ => none

structure DerivationNodeView where
  occurrence : Pattern
  dialect : FormulaDialect
  name : Pattern
  role : Pattern
  formula : Pattern
  annotation : AnnotationView
  span : Pattern
  deriving DecidableEq, Repr

def encodeDerivationNode (view : DerivationNodeView) : AnnotatedInputView := {
  occurrence := view.occurrence
  payload := encodeAnnotatedFormula {
    dialect := view.dialect
    name := view.name
    role := view.role
    formula := view.formula
    annotations := encodeAnnotations view.annotation
  }
  span := view.span
}

def decodeDerivationNode? (input : AnnotatedInputView) :
    Option DerivationNodeView := do
  let formula <- decodeAnnotatedFormula? input.payload
  let annotation <- decodeAnnotations? formula.annotations
  some {
    occurrence := input.occurrence
    dialect := formula.dialect
    name := formula.name
    role := formula.role
    formula := formula.formula
    annotation := annotation
    span := input.span
  }

/-! ## Exactness -/

theorem decode_encode_annotated_formula (view : AnnotatedFormulaView) :
    decodeAnnotatedFormula? (encodeAnnotatedFormula view) = some view := by
  cases view with
  | mk dialect name role formula annotations =>
      cases dialect <;> rfl

theorem encodeAnnotatedFormula_injective :
    Function.Injective encodeAnnotatedFormula := by
  intro left right equality
  have decoded := congrArg decodeAnnotatedFormula? equality
  simpa only [decode_encode_annotated_formula, Option.some.injEq] using decoded

def AnnotationView.WellFormed : AnnotationView -> Prop
  | .absent => True
  | .sourced source _ => (sourceReferences? source).isSome

theorem decode_encode_annotations
    (annotation : AnnotationView) (wellFormed : annotation.WellFormed) :
    decodeAnnotations? (encodeAnnotations annotation) = some annotation := by
  cases annotation with
  | absent => rfl
  | sourced source optionalInfo =>
      simp only [AnnotationView.WellFormed] at wellFormed
      cases referencesEq : sourceReferences? source with
      | none => simp [referencesEq] at wellFormed
      | some references =>
          simp [encodeAnnotations, decodeAnnotations?, a, referencesEq]

theorem decode_encode_derivation_node
    (view : DerivationNodeView) (wellFormed : view.annotation.WellFormed) :
    decodeDerivationNode? (encodeDerivationNode view) = some view := by
  unfold encodeDerivationNode decodeDerivationNode?
  rw [decode_encode_annotated_formula]
  simp [decode_encode_annotations view.annotation wellFormed]

/-! ## Positive and negative controls -/

namespace Canary

def token (label value : String) : Pattern :=
  a label [a value]

def word (value : String) : Pattern :=
  a "tptp92-ast:atomic-word:alt-1" [token "tptp92-ast:token:lower-word" value]

def name (value : String) : Pattern :=
  a "tptp92-ast:name:alt-1" [word value]

def namedSource (value : String) : Pattern :=
  a "tptp92-ast:source:alt-1" [
    a "tptp92-ast:dag-source:alt-1" [name value]]

def parent (source : Pattern) : Pattern :=
  a "tptp92-ast:parent-info:alt-1" [
    source, a "tptp92-ast:parent-details:alt-2"]

def twoParents (left right : Pattern) : Pattern :=
  a "tptp92-ast:parents:alt-2" [
    a "tptp92-ast:parent-list:alt-1" [
      parent left,
      a "tptp92-ast:list:tptp92ast-comma-parent-info:cons" [
        a "tptp92-ast:comma-parent-info:alt-1" [parent right],
        a "tptp92-ast:list:tptp92ast-comma-parent-info:nil"]]]

def nestedInference : Pattern :=
  a "tptp92-ast:source:alt-1" [
    a "tptp92-ast:dag-source:alt-2" [
      a "tptp92-ast:inference-record:alt-1" [
        a "tptp92-ast:inference-rule:alt-1" [word "resolution"],
        a "tptp92-ast:useful-info:alt-2",
        twoParents (namedSource "left") (namedSource "right")]]]

theorem nested_dependencies_are_exact_and_ordered :
    sourceReferences? nestedInference = some [name "left", name "right"] := by
  rfl

theorem malformed_parent_list_is_rejected :
    sourceReferences?
      (a "tptp92-ast:source:alt-1" [
        a "tptp92-ast:dag-source:alt-2" [
          a "tptp92-ast:inference-record:alt-1" [
            a "tptp92-ast:inference-rule:alt-1" [word "resolution"],
            a "tptp92-ast:useful-info:alt-2",
            a "tptp92-ast:parents:alt-2" []]]]) = none := by
  rfl

theorem malformed_nested_alternative_is_rejected :
    sourceReferences?
      (a "tptp92-ast:source:alt-5" [
        a "tptp92-ast:sources:alt-2" [namedSource "left", a "bad"]]) =
      none := by
  rfl

def exampleNode (dialect : FormulaDialect) : DerivationNodeView := {
  occurrence := a "occurrence"
  dialect := dialect
  name := name "n"
  role := a "role"
  formula := a "formula"
  annotation := .sourced nestedInference (a "tptp92-ast:optional-info:alt-2")
  span := a "span"
}

theorem exampleNode_wellFormed (dialect : FormulaDialect) :
    (exampleNode dialect).annotation.WellFormed := by
  simp [exampleNode, AnnotationView.WellFormed, nested_dependencies_are_exact_and_ordered]

theorem every_dialect_round_trips (dialect : FormulaDialect) :
    decodeDerivationNode? (encodeDerivationNode (exampleNode dialect)) =
      some (exampleNode dialect) :=
  decode_encode_derivation_node _ (exampleNode_wellFormed dialect)

theorem mismatched_dialect_constructor_is_rejected :
    decodeAnnotatedFormula?
      (.cnf (a "tptp92-ast:fof-annotated:alt-1"
        [name "n", a "role", a "formula",
          a "tptp92-ast:annotations:alt-2"])) = none := by
  rfl

end Canary

#print axioms decode_encode_annotated_formula
#print axioms encodeAnnotatedFormula_injective
#print axioms decode_encode_annotations
#print axioms decode_encode_derivation_node
#print axioms Canary.nested_dependencies_are_exact_and_ordered
#print axioms Canary.malformed_parent_list_is_rejected
#print axioms Canary.malformed_nested_alternative_is_rejected
#print axioms Canary.every_dialect_round_trips
#print axioms Canary.mismatched_dialect_constructor_is_rejected

end Mettapedia.GSLT.LanguageDef.TptpOfficialDerivationSyntax
