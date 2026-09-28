import Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence
import Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted

/-!
# Exact-span construction routes for lexical and structural grammars

The source-plan relation already supplies exact scalar matching, source-row
occurrences, and ordered CST children. This module transports that relation
to the generic many-sorted construction algebra. Lexical sources carry the
existing class-recognition evidence; structural constructors carry an exact
terminal layout. The child indices enforce both category and contiguous
source positions. No language-specific recognition or name dispatch is added.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareGrammarConstruction

open Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler
open Mettapedia.GSLT.Parsing.ParserProfileSemantics
open Mettapedia.GSLT.Parsing.PresentationExprSemantics
open Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence
open Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted

/-- A child is identified by its category and exact source span. -/
structure Index where
  sort : String
  start : Nat
  stop : Nat
  deriving DecidableEq, Repr

/-- Lexical leaves use the existing exact class/CST judgment, including the
scalar payload. They are not arbitrary strings satisfying a pointwise test. -/
abbrev LexicalSource (profile : ParserProfileLayer) (input : List Nat)
    (index : Index) :=
  Σ tree : CST, SourceLexicalDerivesAt profile input
    index.sort index.start index.stop [tree]

set_option autoImplicit true in
/-- A production's exact scalar layout with typed holes for nonterminals.
Terminal evidence and child spans come from the same source input. -/
inductive Layout (literalScalars? : String → Option (List Nat))
    (input : List Nat) : List StructuralAtom → Nat → Nat → List Index → Type where
  | nil : Layout literalScalars? input [] cursor cursor []
  | terminal
      (decoded : literalScalars? token = some codepoints)
      (matched : ScalarSequenceMatchesAt input codepoints start middle)
      (rest : Layout literalScalars? input atoms middle stop children) :
      Layout literalScalars? input (.terminal token parserRef :: atoms)
        start stop children
  | nonterminal
      (rest : Layout literalScalars? input atoms middle stop children) :
      Layout literalScalars? input (.nonterminal parameter sort parserRef :: atoms)
        start stop (⟨sort, start, middle⟩ :: children)

set_option autoImplicit true in
/-- Constructors are source-rule occurrences, never a separate name table. -/
inductive Operation (literalScalars? : String → Option (List Nat))
    (rules : List CompiledRule) (input : List Nat) : List Index → Index → Type where
  | at (row : Fin rules.length)
      (layout : Layout literalScalars? input (rules.get row).atoms start stop children) :
      Operation literalScalars? rules input children
        ⟨(rules.get row).source.category, start, stop⟩

/-- Forget only heterogeneous indices, retaining every child in order. -/
def childTrees : {indices : List Index} →
    FamilyList (fun _ : Index => CST) indices → List CST
  | [], .nil => []
  | _ :: _, .cons head tail => head :: childTrees tail

def observeOperation (literalScalars? : String → Option (List Nat))
    (rules : List CompiledRule) (input : List Nat) :
    {children : List Index} → {output : Index} →
    Operation literalScalars? rules input children output →
    FamilyList (fun _ : Index => CST) children → CST
  | _, ⟨_, start, stop⟩, .at row _, values =>
      .node (rules.get row).source.label start stop (childTrees values)

abbrev algebra (literalScalars? : String → Option (List Nat))
    (profile : ParserProfileLayer) (rules : List CompiledRule) (input : List Nat) :
    ManySortedConstructionAlgebra where
  Kind := Index
  Object := fun _ => CST
  Source := LexicalSource profile input
  Operation := Operation literalScalars? rules input
  interpretSource := Sigma.fst
  interpretOperation := observeOperation literalScalars? rules input

variable {literalScalars? : String → Option (List Nat)}
  {profile : ParserProfileLayer} {rules : List CompiledRule} {input : List Nat}

/-- Evidence for each child is retained at its exact indexed observation. -/
def ValidChildren (literalScalars? : String → Option (List Nat))
    (profile : ParserProfileLayer) (rules : List CompiledRule) (input : List Nat) :
    {indices : List Index} →
    FamilyList (fun _ : Index => CST) indices → Type
  | [], .nil => Unit
  | index :: _, .cons head tail =>
      SourcePlanDerivesAt literalScalars? profile rules input
        index.sort index.start index.stop head ×
      @ValidChildren literalScalars? profile rules input _ tail

def Layout.realize : {atoms : List StructuralAtom} → {start stop : Nat} →
    {indices : List Index} → Layout literalScalars? input atoms start stop indices →
    (values : FamilyList (fun _ : Index => CST) indices) →
    @ValidChildren literalScalars? profile rules input _ values →
    SourcePlanItemsDeriveAt literalScalars? profile rules input
      atoms start stop (childTrees values)
  | _, _, _, _, .nil, .nil, _ => .nil
  | _, _, _, _, .terminal decoded matched rest, values, valid =>
      .terminal decoded matched (rest.realize values valid)
  | _, _, _, _, .nonterminal rest, .cons _ tail, valid =>
      .nonterminal valid.1 (rest.realize tail valid.2)

def LexicalSource.derives {index : Index}
    (source : LexicalSource profile input index) :
    SourcePlanDerivesAt literalScalars? profile rules input
      index.sort index.start index.stop source.1 := by
  rcases index with ⟨sort, start, stop⟩
  rcases source with ⟨tree, evidence⟩
  cases evidence with
  | apply occurrence body =>
      exact .lexical occurrence.val occurrence.isLt rfl rfl body

/-- Scalar-class sources consume exactly one scalar, ruling out both an
empty lexeme and a multi-scalar run at this boundary. -/
theorem LexicalSource.width {index : Index}
    (source : LexicalSource profile input index) : index.stop = index.start + 1 := by
  rcases index with ⟨sort, start, stop⟩
  rcases source with ⟨tree, evidence⟩
  cases evidence with
  | apply occurrence body =>
      rcases body with ⟨recognized, _⟩
      change RecognizesAtUsing _ _ input (.class _) start stop at recognized
      cases recognized
      rfl

mutual
  /-- Evaluating any route gives the exact source-plan CST it derives. -/
  def routeDerives {index : Index}
      (route : ConstructionTree (algebra literalScalars? profile rules input) index) :
      SourcePlanDerivesAt literalScalars? profile rules input
        index.sort index.start index.stop
        ((algebra literalScalars? profile rules input).evaluate route) := by
    match route with
    | .source leaf => exact leaf.derives
    | .apply (.at row layout) arguments =>
        exact .structural row.val row.isLt rfl rfl
          (layout.realize _ (argumentsDerive arguments))
    termination_by structural route

  /-- All children of a route retain their individual derivations. -/
  def argumentsDerive {indices : List Index}
      (arguments : ConstructionArguments (algebra literalScalars? profile rules input) indices) :
      @ValidChildren literalScalars? profile rules input _
        ((algebra literalScalars? profile rules input).evaluateArguments arguments) := by
    match arguments with
    | .nil => exact ()
    | .cons head tail => exact ⟨routeDerives head, argumentsDerive tail⟩
    termination_by structural arguments
end

mutual
  /-- Reify every source derivation into a typed route, without searching for
  a production or replacing its lexical evidence. -/
  def sourceRoute {sort : String} {start stop : Nat} {tree : CST}
      (derivation : SourcePlanDerivesAt literalScalars? profile rules input
        sort start stop tree) :
      { route : ConstructionTree (algebra literalScalars? profile rules input)
          ⟨sort, start, stop⟩ //
        (algebra literalScalars? profile rules input).evaluate route = tree } := by
    match derivation with
    | .lexical position valid resultSort_exact ruleLabel_exact matched =>
        subst_vars
        exact ⟨.source ⟨_, .apply ⟨position, valid⟩ matched⟩, rfl⟩
    | .structural position valid resultSort_exact ruleLabel_exact body =>
        subst_vars
        obtain ⟨indices, layout, arguments, equality⟩ := sourceArguments body
        refine ⟨.apply (.at ⟨position, valid⟩ layout) arguments, ?_⟩
        change CST.node _ _ _
          (childTrees ((algebra literalScalars? profile rules input).evaluateArguments arguments)) = _
        rw [equality]
    termination_by structural derivation

  /-- Reification retains each literal check and every ordered child hole. -/
  def sourceArguments {atoms : List StructuralAtom} {start stop : Nat} {children : List CST}
      (derivation : SourcePlanItemsDeriveAt literalScalars? profile rules input
        atoms start stop children) :
      Σ indices : List Index,
        Σ _layout : Layout literalScalars? input atoms start stop indices,
          { arguments : ConstructionArguments (algebra literalScalars? profile rules input) indices //
            childTrees ((algebra literalScalars? profile rules input).evaluateArguments arguments) =
              children } := by
    match derivation with
    | .nil => exact ⟨[], .nil, .nil, rfl⟩
    | .terminal decoded matched rest =>
        obtain ⟨indices, layout, arguments, equality⟩ := sourceArguments rest
        exact ⟨indices, .terminal decoded matched layout, arguments, equality⟩
    | .nonterminal head rest =>
        obtain ⟨route, route_eq⟩ := sourceRoute head
        obtain ⟨indices, layout, arguments, equality⟩ := sourceArguments rest
        refine ⟨_ :: indices, .nonterminal layout, .cons route arguments, ?_⟩
        simp only [ManySortedConstructionAlgebra.evaluateArguments_cons, childTrees,
          route_eq, equality]
    termination_by structural derivation
end

/-- Exact source derivability and typed construction agree for every input,
category, span and CST, including lexical leaves. This does not assert that
an arbitrary native parser implements either side. -/
theorem source_iff_route {sort : String} {start stop : Nat} {tree : CST} :
    Nonempty (SourcePlanDerivesAt literalScalars? profile rules input sort start stop tree) ↔
      ∃ route : ConstructionTree (algebra literalScalars? profile rules input) ⟨sort, start, stop⟩,
        (algebra literalScalars? profile rules input).evaluate route = tree := by
  constructor
  · rintro ⟨derivation⟩
    exact ⟨(sourceRoute derivation).val, (sourceRoute derivation).property⟩
  · rintro ⟨route, equality⟩
    rw [← equality]
    exact ⟨routeDerives route⟩

/-- Compose the existing independent source/ParserPack correspondence with
route construction. The agreement concerns the formal plan; a native table
snapshot still needs its own connection to that plan. -/
theorem parserPack_iff_route {plan : CompiledParserPackPlan}
    (agreement : ParserPackPlanAgreement literalScalars? profile rules plan)
    {sort : String} {start stop : Nat} {tree : CST} :
    Nonempty (ParserPackDerivesAt profile plan input sort start stop tree) ↔
      ∃ route : ConstructionTree (algebra literalScalars? profile rules input) ⟨sort, start, stop⟩,
        (algebra literalScalars? profile rules input).evaluate route = tree :=
  (sourcePlan_nonempty_iff_parserPack_nonempty agreement sort start stop tree).symm.trans
    source_iff_route

#print axioms source_iff_route
#print axioms LexicalSource.width
#print axioms parserPack_iff_route

end Mettapedia.GSLT.Parsing.ClassAwareGrammarConstruction
