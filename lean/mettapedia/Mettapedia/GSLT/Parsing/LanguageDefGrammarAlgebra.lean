import Mettapedia.GSLT.Parsing.LanguageDefSyntaxCorrespondence
import Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted

/-!
# Construction algebras derived from a LanguageDef grammar

Constructor identities are positions in the existing structural compiler's
output, not a second list of language-specific names. Their ordered input
sorts come from the compiled source items. The existing many-sorted tree
carrier therefore supplies a total structural fold without untyped child
lookup. This module relates that carrier to `GrammarDerives` in both
directions. It covers the structural compiler's terminal/nonterminal domain;
it does not establish raw-byte lexing or a particular compact interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.LanguageDefGrammarAlgebra

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.GrammarDerives
open Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler
open Mettapedia.GSLT.Parsing.LanguageDefSyntaxCorrespondence
open Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted

/-- Nonterminal children, in source occurrence order. Terminals are already
fixed by the production and are restored by the syntax interpretation. -/
def childSorts : List StructuralAtom → List String
  | [] => []
  | .terminal _ _ :: rest => childSorts rest
  | .nonterminal _ sort _ :: rest => sort :: childSorts rest

/-- Every production occurrence gives precisely one typed constructor.
Distinct positions remain distinct even when their source rows are equal. -/
inductive Operation (rules : List CompiledRule) : List String → String → Type where
  | at (index : Fin rules.length) :
      Operation rules (childSorts rules[index].atoms) rules[index].source.category

/-- The syntax observation used by the existing grammar relation. This is
not the public compact-value language. -/
structure Observation where
  tokens : List String
  tree : Pattern
  deriving DecidableEq, Repr

/-- Restore the exact terminal/nonterminal interleaving of a production. -/
def assemble : (atoms : List StructuralAtom) →
    FamilyList (fun _ : String => Observation) (childSorts atoms) →
    List String × List Pattern
  | [], .nil => ([], [])
  | .terminal token _ :: rest, values =>
      let suffix := assemble rest values
      (token :: suffix.1, suffix.2)
  | .nonterminal _ _ _ :: rest, .cons head tail =>
      let suffix := assemble rest tail
      (head.tokens ++ suffix.1, head.tree :: suffix.2)

def observeOperation (rules : List CompiledRule) :
    {inputs : List String} → {output : String} → Operation rules inputs output →
    FamilyList (fun _ : String => Observation) inputs → Observation
  | _, _, .at index, values =>
      let parts := assemble rules[index].atoms values
      ⟨parts.1, .apply rules[index].source.label parts.2⟩

/-- There are no arbitrary syntax leaves: leaves are nullary productions.
Every constructor and every permitted child sort comes from `rules`. -/
def syntaxAlgebra (rules : List CompiledRule) : ManySortedConstructionAlgebra where
  Kind := String
  Object := fun _ => Observation
  Source := fun _ => Empty
  Operation := Operation rules
  interpretSource := Empty.elim
  interpretOperation := observeOperation rules

/-- Supplying a total interpretation requires an operation at every source
constructor's exact type. No default or runtime missing-case branch exists. -/
structure Interpretation (rules : List CompiledRule) where
  Carrier : String → Type
  operation : {inputs : List String} → {output : String} →
    Operation rules inputs output → FamilyList Carrier inputs → Carrier output

/-- One derived language may have different interpretations, without changing
its syntax constructor domain. Representation correctness is a further law. -/
def Interpretation.algebra {rules : List CompiledRule}
    (interpretation : Interpretation rules) : ManySortedConstructionAlgebra where
  Kind := String
  Object := interpretation.Carrier
  Source := fun _ => Empty
  Operation := Operation rules
  interpretSource := Empty.elim
  interpretOperation := interpretation.operation

def ValidArguments (rules : List CompiledRule) : {sorts : List String} →
    FamilyList (fun _ : String => Observation) sorts → Prop
  | [], .nil => True
  | sort :: _, .cons head tail =>
      CompiledDerives rules sort head.tokens head.tree ∧ ValidArguments rules tail

theorem assemble_derives
    {binding : Binding} {rules : List CompiledRule} {source : GrammarRule}
    {items : List SyntaxItem} {atoms : List StructuralAtom}
    (layout : ItemsCompile binding source items atoms)
    (values : FamilyList (fun _ : String => Observation) (childSorts atoms))
    (valid : ValidArguments rules values) :
    CompiledItemsDerives rules source items atoms
      (assemble atoms values).1 (assemble atoms values).2 := by
  induction layout with
  | nil => cases values; exact .nil source
  | @cons item atom items atoms compiled _ ih =>
      cases item with
      | terminal token =>
          simp only [compileItem?] at compiled
          cases ref : binding.literalRef token with
          | none => simp [ref] at compiled
          | some parserRef =>
              simp [ref] at compiled
              subst atom
              exact .terminal source token parserRef items atoms _ _ (ih values valid)
      | nonTerminal name =>
          simp only [compileItem?] at compiled
          cases lookup : paramSort? source name with
          | none => simp [lookup] at compiled
          | some sort =>
              simp [lookup] at compiled
              subst atom
              cases values with
              | cons head tail =>
                  exact .nonterminal source name sort _ lookup _ _ valid.1
                    items atoms _ _ (ih tail valid.2)
      | separator _ | delimiter _ _ | op _ => simp [compileItem?] at compiled

mutual
  /-- A construction route cannot invent a derivation of the compiled grammar. -/
  theorem evaluate_derives
      {binding : Binding} {language : LanguageDef} {rules : List CompiledRule}
      (compiled : compileRules? binding language = some rules)
      {sort : String} (route : ConstructionTree (syntaxAlgebra rules) sort) :
      CompiledDerives rules sort
        ((syntaxAlgebra rules).evaluate route).tokens
        ((syntaxAlgebra rules).evaluate route).tree := by
    match route with
    | .source value => exact Empty.elim value
    | .apply (.at index) arguments =>
        exact .rule rules[index] (List.getElem_mem _) _ rfl _ _
          (assemble_derives (compileRules_member_items compiled (List.getElem_mem _))
            _ (evaluateArguments_valid compiled arguments))
    termination_by structural route

  theorem evaluateArguments_valid
      {binding : Binding} {language : LanguageDef} {rules : List CompiledRule}
      (compiled : compileRules? binding language = some rules)
      {sorts : List String}
      (arguments : ConstructionArguments (syntaxAlgebra rules) sorts) :
      ValidArguments rules ((syntaxAlgebra rules).evaluateArguments arguments) := by
    match arguments with
    | .nil => trivial
    | .cons head tail =>
        exact ⟨evaluate_derives compiled head, evaluateArguments_valid compiled tail⟩
    termination_by structural arguments
end

/-- Syntax observation of a constructed route is authorized by the original
LanguageDef, not merely by a separately authored signature. -/
theorem evaluate_source_derives
    {binding : Binding} {language : LanguageDef} {rules : List CompiledRule}
    (compiled : compileRules? binding language = some rules)
    {sort : String} (route : ConstructionTree (syntaxAlgebra rules) sort) :
    Derives language sort
      ((syntaxAlgebra rules).evaluate route).tokens
      ((syntaxAlgebra rules).evaluate route).tree :=
  compileRules_reflects_derivation compiled (evaluate_derives compiled route)

mutual
  /-- Every derivation of the compiled grammar has a typed construction route.
  This is the no-omission direction, including arbitrary recursive depth. -/
  theorem derivation_has_route
      {rules : List CompiledRule} {sort : String}
      {tokens : List String} {tree : Pattern}
      (derivation : CompiledDerives rules sort tokens tree) :
      ∃ route : ConstructionTree (syntaxAlgebra rules) sort,
        (syntaxAlgebra rules).evaluate route = ⟨tokens, tree⟩ := by
    match derivation with
    | .rule rule member _ sortEq _ _ items =>
        have argumentsExist := items_have_arguments items
        subst sortEq
        obtain ⟨index, selected⟩ := List.mem_iff_get.mp member
        subst rule
        obtain ⟨arguments, observed⟩ := argumentsExist
        refine ⟨.apply (.at index) arguments, ?_⟩
        change Observation.mk
          (assemble _ ((syntaxAlgebra rules).evaluateArguments arguments)).1
          (.apply _ (assemble _ ((syntaxAlgebra rules).evaluateArguments arguments)).2) = _
        rw [observed]
        rfl
    termination_by structural derivation

  theorem items_have_arguments
      {rules : List CompiledRule} {source : GrammarRule}
      {items : List SyntaxItem} {atoms : List StructuralAtom}
      {tokens : List String} {children : List Pattern}
      (derivation : CompiledItemsDerives rules source items atoms tokens children) :
      ∃ arguments : ConstructionArguments (syntaxAlgebra rules) (childSorts atoms),
        assemble atoms ((syntaxAlgebra rules).evaluateArguments arguments) =
          (tokens, children) := by
    match derivation with
    | .nil _ => exact ⟨.nil, rfl⟩
    | .terminal _ token _ _ restAtoms _ _ rest =>
        obtain ⟨arguments, observed⟩ := items_have_arguments rest
        refine ⟨arguments, ?_⟩
        change (token :: (assemble restAtoms
          ((syntaxAlgebra rules).evaluateArguments arguments)).1,
          (assemble restAtoms ((syntaxAlgebra rules).evaluateArguments arguments)).2) = _
        rw [observed]
    | .nonterminal _ _ _ _ _ _ _ head _ restAtoms _ _ rest =>
        obtain ⟨route, observedHead⟩ := derivation_has_route head
        obtain ⟨arguments, observedTail⟩ := items_have_arguments rest
        refine ⟨.cons route arguments, ?_⟩
        change (((syntaxAlgebra rules).evaluate route).tokens ++
          (assemble restAtoms ((syntaxAlgebra rules).evaluateArguments arguments)).1,
          ((syntaxAlgebra rules).evaluate route).tree ::
          (assemble restAtoms ((syntaxAlgebra rules).evaluateArguments arguments)).2) = _
        rw [observedHead, observedTail]
    termination_by structural derivation
end

/-- The constructor algebra has exactly the source grammar's observations.
Neither a finite witness inventory nor an independent syntax definition is
used in either direction. -/
theorem source_derives_iff_route
    {binding : Binding} {language : LanguageDef} {rules : List CompiledRule}
    (compiled : compileRules? binding language = some rules)
    (sort : String) (tokens : List String) (tree : Pattern) :
    Derives language sort tokens tree ↔
      ∃ route : ConstructionTree (syntaxAlgebra rules) sort,
        (syntaxAlgebra rules).evaluate route = ⟨tokens, tree⟩ := by
  constructor
  · intro derivation
    exact derivation_has_route (compileRules_preserves_derivation compiled derivation)
  · rintro ⟨route, observed⟩
    have authorized := evaluate_source_derives compiled route
    simpa only [observed] using authorized

mutual
  /-- A total interpretation folds the grammar's own typed constructor tree.
  The result family is part of the function's type. -/
  def interpret {rules : List CompiledRule} (interpretation : Interpretation rules)
      {sort : String} : ConstructionTree (syntaxAlgebra rules) sort →
      interpretation.Carrier sort
    | .source impossible => Empty.elim impossible
    | .apply operation arguments =>
        interpretation.operation operation (interpretArguments interpretation arguments)

  def interpretArguments {rules : List CompiledRule}
      (interpretation : Interpretation rules) {sorts : List String} :
      ConstructionArguments (syntaxAlgebra rules) sorts →
      FamilyList interpretation.Carrier sorts
    | .nil => .nil
    | .cons head tail =>
        .cons (interpret interpretation head) (interpretArguments interpretation tail)
end

#print axioms assemble_derives
#print axioms evaluate_source_derives
#print axioms source_derives_iff_route

end Mettapedia.GSLT.Parsing.LanguageDefGrammarAlgebra
