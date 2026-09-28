import Mettapedia.GSLT.Parsing.ClassAwareGrammarConstruction
import Mettapedia.GSLT.Parsing.GrammarConstructorActions

/-!
# Typed interpretation actions over exact lexical construction routes

The source constructor is the existing exact-span `Operation`, including its
terminal layout and occurrence index. Each structural constructor uses its
already declared grammar-indexed template. Lexical interpretation is a total
function supplied by the language interpretation; it is not recovered from
rule names or guessed from the scalar evidence.

The route translation retains every source constructor, lexical source, and
layout witness. Only the value interpretation changes. OSLF of its actual
evaluation computation characterizes exactly the direct fold result. This
connects exact source routes to typed target actions, not yet a particular
language's representation laws or any native implementation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareGrammarActions

open Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler
open Mettapedia.GSLT.Parsing.ParserProfileSemantics
open Mettapedia.GSLT.Parsing.PresentationExprSemantics
open Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence
open Mettapedia.GSLT.Parsing.ClassAwareGrammarConstruction
open Mettapedia.GSLT.Parsing.LanguageDefGrammarAlgebra (childSorts)
open Mettapedia.GSLT.Parsing.GrammarConstructorActions (Templates)
open Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted
open Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySortedEvaluation
open Mettapedia.OSLF.Framework.PathTypeSynthesis

variable {literalScalars? : String → Option (List Nat)}
  {profile : ParserProfileLayer} {rules : List CompiledRule} {input : List Nat}
  {target : ManySortedConstructionAlgebra.{0, 0, 0, 0}}

/-- Interpretations retain each exact-span index, while using existing target
values at the grammar category's declared image sort. -/
abbrev Value (templates : Templates rules target) (index : Index) :=
  target.Object (templates.sortMap index.sort)

/-- The complete lexical branch is part of the interpretation's input. The
caller must supply a result for every admitted lexical occurrence. -/
abbrev LexicalInterpretation (templates : Templates rules target)
    (profile : ParserProfileLayer) (input : List Nat) :=
  ∀ {index : Index}, LexicalSource profile input index → Value templates index

/-- Reindex children using the exact terminal/nonterminal layout. Terminals
have no semantic child slot; their recognition remains in the layout witness
and their representation meaning belongs to the declared row template. -/
def targetChildren (sortMap : String → target.Kind) :
    {atoms : List StructuralAtom} → {start stop : Nat} → {indices : List Index} →
    Layout literalScalars? input atoms start stop indices →
    FamilyList (fun index => target.Object (sortMap index.sort)) indices →
    FamilyList target.Object ((childSorts atoms).map sortMap)
  | [], _, _, _, .nil, .nil => .nil
  | .terminal _ _ :: atoms, _, _, _, .terminal _ _ rest, values =>
      targetChildren sortMap (atoms := atoms) rest values
  | .nonterminal _ _ _ :: atoms, _, _, _, .nonterminal rest, .cons head tail =>
      .cons head (targetChildren sortMap (atoms := atoms) rest tail)

/-- A source occurrence selects its exact typed action, with no string lookup. -/
def executeOperation (templates : Templates rules target)
    {children : List Index} {output : Index}
    (operation : Operation literalScalars? rules input children output)
    (values : FamilyList (Value templates) children) : Value templates output := by
  cases operation with
  | «at» row layout =>
      exact OpenConstructionRoute.evaluate target
        (targetChildren templates.sortMap layout values) (templates.action row)

/-- The same source route signature, interpreted by the declared target actions. -/
abbrev interpretationAlgebra (templates : Templates rules target)
    (lexical : LexicalInterpretation templates profile input) :
    ManySortedConstructionAlgebra where
  Kind := Index
  Object := Value templates
  Source := LexicalSource profile input
  Operation := Operation literalScalars? rules input
  interpretSource := lexical
  interpretOperation := executeOperation templates

mutual
  /-- Retain the exact source constructor and lexical evidence at every node. -/
  def interpretationRoute (templates : Templates rules target)
      (lexical : LexicalInterpretation templates profile input) {index : Index} :
      ConstructionTree (algebra literalScalars? profile rules input) index →
      ConstructionTree (interpretationAlgebra (literalScalars? := literalScalars?)
        templates lexical) index
    | .source leaf => .source leaf
    | .apply operation arguments =>
        .apply operation (interpretationArguments templates lexical arguments)

  def interpretationArguments (templates : Templates rules target)
      (lexical : LexicalInterpretation templates profile input) {indices : List Index} :
      ConstructionArguments (algebra literalScalars? profile rules input) indices →
      ConstructionArguments (interpretationAlgebra (literalScalars? := literalScalars?)
        templates lexical) indices
    | .nil => .nil
    | .cons head tail =>
        .cons (interpretationRoute templates lexical head)
          (interpretationArguments templates lexical tail)
end

mutual
  /-- Direct source fold, which need not allocate translated machine trees. -/
  def fold (templates : Templates rules target)
      (lexical : LexicalInterpretation templates profile input) {index : Index} :
      ConstructionTree (algebra literalScalars? profile rules input) index → Value templates index
    | .source leaf => lexical leaf
    | .apply operation arguments =>
        executeOperation templates operation (foldArguments templates lexical arguments)

  def foldArguments (templates : Templates rules target)
      (lexical : LexicalInterpretation templates profile input) {indices : List Index} :
      ConstructionArguments (algebra literalScalars? profile rules input) indices →
      FamilyList (Value templates) indices
    | .nil => .nil
    | .cons head tail =>
        .cons (fold templates lexical head) (foldArguments templates lexical tail)
end

mutual
  /-- Translation to the operational carrier computes the same direct fold. -/
  theorem interpretationRoute_evaluates (templates : Templates rules target)
      (lexical : LexicalInterpretation templates profile input) {index : Index}
      (route : ConstructionTree (algebra literalScalars? profile rules input) index) :
      (interpretationAlgebra templates lexical).evaluate
        (interpretationRoute templates lexical route) = fold templates lexical route := by
    match route with
    | .source leaf => rfl
    | .apply operation arguments =>
        change executeOperation templates operation
          ((interpretationAlgebra templates lexical).evaluateArguments
            (interpretationArguments templates lexical arguments)) = _
        rw [interpretationArguments_evaluate]
        rfl
    termination_by structural route

  theorem interpretationArguments_evaluate (templates : Templates rules target)
      (lexical : LexicalInterpretation templates profile input) {indices : List Index}
      (arguments : ConstructionArguments (algebra literalScalars? profile rules input) indices) :
      (interpretationAlgebra templates lexical).evaluateArguments
        (interpretationArguments templates lexical arguments) =
          foldArguments templates lexical arguments := by
    match arguments with
    | .nil => rfl
    | .cons head tail =>
        change FamilyList.cons
          ((interpretationAlgebra templates lexical).evaluate
            (interpretationRoute templates lexical head))
          ((interpretationAlgebra templates lexical).evaluateArguments
            (interpretationArguments templates lexical tail)) = _
        rw [interpretationRoute_evaluates, interpretationArguments_evaluate]
        rfl
    termination_by structural arguments
end

/-- The operational native type describes exactly this declared fold, including
its concrete lexical interpretation and exact source constructor occurrences. -/
theorem result_native_iff (templates : Templates rules target)
    (lexical : LexicalInterpretation templates profile input) {index : Index}
    (route : ConstructionTree (algebra literalScalars? profile rules input) index)
    (value : Value templates index) :
    (pathOSLF (evaluationGSLT (interpretationAlgebra templates lexical) index)).satisfies
      (enterState (interpretationAlgebra templates lexical)
        (interpretationRoute templates lexical route))
      (resultNativeType (interpretationAlgebra templates lexical) value).pred ↔
        fold templates lexical route = value := by
  rw [entered_result_iff, interpretationRoute_evaluates]

/-- Every exact source derivation yields a source-connected interpretation
inhabiting its result native type. The original CST observation remains paired
with that very route; this does not assert representation preservation. -/
theorem source_has_interpretation (templates : Templates rules target)
    (lexical : LexicalInterpretation templates profile input)
    {sort : String} {start stop : Nat} {tree : CST}
    (derivation : SourcePlanDerivesAt literalScalars? profile rules input
      sort start stop tree) :
    ∃ route : ConstructionTree (algebra literalScalars? profile rules input) ⟨sort, start, stop⟩,
      (algebra literalScalars? profile rules input).evaluate route = tree ∧
      (pathOSLF (evaluationGSLT (interpretationAlgebra templates lexical)
        ⟨sort, start, stop⟩)).satisfies
        (enterState (interpretationAlgebra templates lexical)
          (interpretationRoute templates lexical route))
        (resultNativeType (interpretationAlgebra templates lexical)
          (fold templates lexical route)).pred := by
  let route := sourceRoute derivation
  exact ⟨route.val, route.property,
    (result_native_iff templates lexical route.val _).mpr rfl⟩

/-- A different observation cannot borrow the original fold's native evidence. -/
theorem rejects_different_result (templates : Templates rules target)
    (lexical : LexicalInterpretation templates profile input) {index : Index}
    (route : ConstructionTree (algebra literalScalars? profile rules input) index)
    (value : Value templates index) (different : fold templates lexical route ≠ value) :
    ¬ (pathOSLF (evaluationGSLT (interpretationAlgebra templates lexical) index)).satisfies
      (enterState (interpretationAlgebra templates lexical)
        (interpretationRoute templates lexical route))
      (resultNativeType (interpretationAlgebra templates lexical) value).pred := by
  rw [result_native_iff]
  exact different

#print axioms interpretationRoute_evaluates
#print axioms result_native_iff
#print axioms source_has_interpretation

end Mettapedia.GSLT.Parsing.ClassAwareGrammarActions
