import Mettapedia.GSLT.Parsing.PlainBnfSemanticAdmission
import Mettapedia.GSLT.Parsing.LanguageDefSyntaxCorrespondence
import Mettapedia.GSLT.Parsing.ParserPackSemanticGSLT
import Mathlib.Tactic

/-!
# Plain-BNF denotation to semantic ParserPack compilation

This module connects the structured plain-BNF denotation to the existing
language-neutral parser compiler.  It introduces no semantic intermediate
language.  The public result contains the denoted source `LanguageDef`, the
compiled source rows with their exactness witness, and the target
proof-relevant GSLT with its exact compiler arrow.  Concrete parser tables are
hidden inside `SemanticCompilation`.

Compilation is deliberately fail-closed.  A later admission theorem will show
that every admitted plain-BNF document succeeds; until then, failure remains an
explicit `none` rather than a fallback grammar.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.PlainBnfDenotationCompilation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.GrammarDerives
open Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler
open Mettapedia.GSLT.Parsing.LanguageDefSyntaxCorrespondence
open Mettapedia.GSLT.Parsing.ClassAwareParserPackCorrespondence
open Mettapedia.GSLT.Parsing.ParserPackSemanticGSLT
open Mettapedia.GSLT.Parsing.PlainBnfStructuredDenotation
open Mettapedia.GSLT.Parsing.PlainBnfSemanticAdmission

/-- Namespace a parser reference while retaining the complete authored name. -/
def parserReference (kind value : String) : String :=
  "__plain_bnf." ++ kind ++ "." ++ value

theorem parserReference_injective (kind : String) :
    Function.Injective (parserReference kind) := by
  intro left right equal
  apply String.ext
  have listEqual :
      ("__plain_bnf." ++ kind ++ ".").toList ++ left.toList =
        ("__plain_bnf." ++ kind ++ ".").toList ++ right.toList := by
    simpa [parserReference, String.toList_append, List.append_assoc] using
      congrArg String.toList equal
  exact List.append_right_injective
    ("__plain_bnf." ++ kind ++ ".").toList listEqual

/-- Structural parser binding derived only from the denoted profile. -/
def syntaxBinding (profile : ParserProfileSemantics.ParserProfileLayer) :
    Binding where
  literalRef := fun token => some (parserReference "literal" token)
  lexicalSortRef := fun sort =>
    (profile.lexicalRule? sort).map (parserReference "lexical")
  categoryRef := parserReference "category"
  ruleRef := parserReference "rule"

/-- Exact Unicode-scalar spelling of a structural terminal. -/
def literalScalars? (token : String) : Option (List Nat) :=
  some (token.toList.map Char.toNat)

/-! ## Totality of structural compilation on denoted BNF rows -/

private theorem parameterSort_of_binding
    (bindings : List (String × String))
    (namesNodup : (bindings.map Prod.fst).Nodup)
    {parameter sort : String} (member : (parameter, sort) ∈ bindings) :
    (bindings.map fun binding =>
        TermParam.simple binding.1 (.base binding.2)).findSome?
      (fun candidate =>
        match candidate with
        | .simple name (.base resultSort) =>
            if name == parameter then some resultSort else none
        | _ => none) = some sort := by
  induction bindings with
  | nil => simp at member
  | cons head tail ih =>
      have separated := List.nodup_cons.mp namesNodup
      by_cases isHead : head = (parameter, sort)
      · subst head
        simp
      · have inTail : (parameter, sort) ∈ tail := by
          rw [List.mem_cons] at member
          rcases member with equal | inTail
          · exact False.elim (isHead equal.symm)
          · exact inTail
        have differentKey : head.1 ≠ parameter := by
          intro sameKey
          apply separated.1
          exact List.mem_map.mpr ⟨(parameter, sort), inTail, by
            simp [sameKey]⟩
        rw [List.map_cons, List.findSome?_cons]
        rw [ih separated.2 inTail]
        simp [differentKey]

private theorem paramSort_denoted_binding
    (rule : GrammarRule) (bindings : List (String × String))
    (paramsExact : rule.params = bindings.map fun binding =>
      TermParam.simple binding.1 (.base binding.2))
    (namesNodup : (bindings.map Prod.fst).Nodup)
    {parameter sort : String} (member : (parameter, sort) ∈ bindings) :
    paramSort? rule parameter = some sort := by
  rw [paramSort?, paramsExact]
  exact parameterSort_of_binding bindings namesNodup member

private theorem compile_denoted_syntax_isSome
    (profile : ParserProfileSemantics.ParserProfileLayer)
    (rule : GrammarRule) (allBindings : List (String × String))
    (paramsExact : rule.params = allBindings.map fun binding =>
      TermParam.simple binding.1 (.base binding.2))
    (namesNodup : (allBindings.map Prod.fst).Nodup)
    (elements : List Element) (index : Nat)
    (contained : ∀ binding,
      binding ∈ denoteReferenceBindings elements index ->
        binding ∈ allBindings) :
    (compileSyntaxItems? (syntaxBinding profile) rule
      (denoteSyntax elements index)).isSome = true := by
  induction elements generalizing index with
  | nil => rfl
  | cons element rest ih =>
      cases element with
      | literal text span =>
          have tailContained : ∀ binding,
              binding ∈ denoteReferenceBindings rest index ->
                binding ∈ allBindings := by
            intro binding member
            exact contained binding (by
              simpa [denoteReferenceBindings] using member)
          by_cases empty : text.isEmpty = true
          · simpa [denoteSyntax, empty] using
              ih index tailContained
          · have nonempty : text.isEmpty = false :=
              Bool.eq_false_of_not_eq_true empty
            have tail := ih index tailContained
            cases tailResult : compileSyntaxItems?
                (syntaxBinding profile) rule (denoteSyntax rest index) with
            | none => simp [tailResult] at tail
            | some atoms =>
                have head : (compileItem? (syntaxBinding profile) rule
                    (.terminal text)).isSome = true := by
                  rfl
                cases headResult : compileItem? (syntaxBinding profile) rule
                    (.terminal text) with
                | none => simp [headResult] at head
                | some atom =>
                    unfold compileSyntaxItems? at tailResult ⊢
                    simp [denoteSyntax, nonempty, headResult, tailResult]
      | reference sort span =>
          let parameter := generatedParameterName index
          have bindingMember : (parameter, sort) ∈ allBindings :=
            contained (parameter, sort) (by
              simp [parameter, denoteReferenceBindings])
          have lookup : paramSort? rule parameter = some sort :=
            paramSort_denoted_binding rule allBindings paramsExact
              namesNodup bindingMember
          have tailContained : ∀ binding,
              binding ∈ denoteReferenceBindings rest (index + 1) ->
                binding ∈ allBindings := by
            intro binding member
            exact contained binding (by
              simp [denoteReferenceBindings, member])
          have tail := ih (index + 1) tailContained
          cases tailResult : compileSyntaxItems? (syntaxBinding profile) rule
              (denoteSyntax rest (index + 1)) with
          | none => simp [tailResult] at tail
          | some atoms =>
              have head : (compileItem? (syntaxBinding profile) rule
                  (.nonTerminal parameter)).isSome = true := by
                simp [compileItem?, lookup]
              cases headResult : compileItem? (syntaxBinding profile) rule
                  (.nonTerminal parameter) with
              | none => simp [headResult] at head
              | some atom =>
                  unfold compileSyntaxItems? at tailResult ⊢
                  simp [denoteSyntax, parameter, headResult, tailResult]

private theorem compile_denoted_alternative_isSome
    (profile : ParserProfileSemantics.ParserProfileLayer)
    (category : String) (alternativeIndex : Nat)
    (alternative : Alternative) :
    (compileRule? (syntaxBinding profile)
      (denoteAlternative category alternativeIndex alternative)).isSome = true := by
  unfold compileRule?
  have compiledItems :
      (compileItems? (syntaxBinding profile)
        (denoteAlternative category alternativeIndex alternative)).isSome = true := by
    apply compile_denoted_syntax_isSome profile
      (denoteAlternative category alternativeIndex alternative)
      (denoteReferenceBindings alternative.elements 0)
    · rfl
    · exact denoteReferenceBinding_names_nodup alternative.elements 0
    · intro binding member
      exact member
  cases itemResult : compileItems? (syntaxBinding profile)
      (denoteAlternative category alternativeIndex alternative) with
  | none => simp [itemResult] at compiledItems
  | some atoms => rfl

private theorem compile_denoted_alternatives_isSome
    (profile : ParserProfileSemantics.ParserProfileLayer)
    (category : String) (alternatives : List Alternative) (index : Nat) :
    ((denoteAlternatives category alternatives index).mapM
      (compileRule? (syntaxBinding profile))).isSome = true := by
  induction alternatives generalizing index with
  | nil => rfl
  | cons alternative rest ih =>
      simp only [denoteAlternatives, List.mapM_cons]
      have head := compile_denoted_alternative_isSome
        profile category index alternative
      cases headResult : compileRule? (syntaxBinding profile)
          (denoteAlternative category index alternative) with
      | none => simp [headResult] at head
      | some compiledHead =>
          have tail := ih (index + 1)
          cases tailResult :
              (denoteAlternatives category rest (index + 1)).mapM
                (compileRule? (syntaxBinding profile)) with
          | none => simp [tailResult] at tail
          | some compiledTail =>
              rfl

private theorem compile_denoted_rules_isSome
    (profile : ParserProfileSemantics.ParserProfileLayer)
    (entries : List Entry) :
    ((denoteRules entries).mapM
      (compileRule? (syntaxBinding profile))).isSome = true := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      cases entry with
      | comment text span =>
          simpa [denoteRules] using ih
      | blank span =>
          simpa [denoteRules] using ih
      | rule category expression span =>
          rw [denoteRules, List.mapM_append]
          have current := compile_denoted_alternatives_isSome profile category
            expression.alternatives 0
          cases currentResult :
              (denoteAlternatives category expression.alternatives 0).mapM
                (compileRule? (syntaxBinding profile)) with
          | none => simp [currentResult] at current
          | some compiledCurrent =>
              cases tailResult : (denoteRules rest).mapM
                  (compileRule? (syntaxBinding profile)) with
              | none => simp [tailResult] at ih
              | some compiledTail =>
                  rfl

/-- Every structurally denoted plain-BNF grammar reaches the generic compiled
row layer.  This theorem says nothing about semantic admission; it says that
the denotation never emits unsupported syntax constructors. -/
theorem denoted_source_rows_compile
    (document : Document) (authority : GrammarAuthority) :
    (compileRules?
      (syntaxBinding (denote document authority).profile)
      (denote document authority).language).isSome = true := by
  simpa [compileRules?, denote] using
    compile_denoted_rules_isSome (denote document authority).profile
      document.entries

/-! ## Totality of the scalar and ParserPack compilation stages -/

private theorem scalar_atom_compiles (atom : StructuralAtom) :
    (compileStructuralAtomItems? literalScalars? atom).isSome = true := by
  cases atom <;> rfl

private theorem scalar_atoms_mapM_compiles (atoms : List StructuralAtom) :
    (atoms.mapM (compileStructuralAtomItems? literalScalars?)).isSome = true := by
  induction atoms with
  | nil => rfl
  | cons atom rest ih =>
      have head := scalar_atom_compiles atom
      cases headResult : compileStructuralAtomItems? literalScalars? atom with
      | none => simp [headResult] at head
      | some headItems =>
          cases tailResult :
              rest.mapM (compileStructuralAtomItems? literalScalars?) with
          | none => simp [tailResult] at ih
          | some tailItems =>
              simp [List.mapM_cons, headResult, tailResult]

private theorem scalar_structural_items_compile
    (atoms : List StructuralAtom) :
    (compileStructuralItems? literalScalars? atoms).isSome = true := by
  unfold compileStructuralItems?
  have rows := scalar_atoms_mapM_compiles atoms
  cases rowsResult :
      atoms.mapM (compileStructuralAtomItems? literalScalars?) with
  | none => simp [rowsResult] at rows
  | some compiledRows => rfl

private theorem scalar_structural_rule_compiles
    (startSort : String) (rule : CompiledRule) :
    (compileStructuralRule? literalScalars? startSort rule).isSome = true := by
  unfold compileStructuralRule?
  have items := scalar_structural_items_compile rule.atoms
  cases itemResult : compileStructuralItems? literalScalars? rule.atoms with
  | none => simp [itemResult] at items
  | some bodyItems => rfl

private theorem scalar_structural_rules_mapM_compile
    (startSort : String) (rules : List CompiledRule) :
    (rules.mapM
      (compileStructuralRule? literalScalars? startSort)).isSome = true := by
  induction rules with
  | nil => rfl
  | cons rule rest ih =>
      have head := scalar_structural_rule_compiles startSort rule
      cases headResult : compileStructuralRule? literalScalars? startSort rule with
      | none => simp [headResult] at head
      | some compiledHead =>
          cases tailResult :
              rest.mapM (compileStructuralRule? literalScalars? startSort) with
          | none => simp [tailResult] at ih
          | some compiledTail =>
              simp [List.mapM_cons, headResult, tailResult]

/-- Exact scalar decoding makes the ParserPack plan compiler total on every
structurally compiled rule vector. -/
theorem scalar_parserPack_plan_compiles
    (profile : ParserProfileSemantics.ParserProfileLayer)
    (rules : List CompiledRule) :
    (compileParserPackPlan? literalScalars? profile rules).isSome = true := by
  unfold compileParserPackPlan? compileStructuralProductions?
  have structural :=
    scalar_structural_rules_mapM_compile profile.startSort rules
  cases structuralResult :
      rules.mapM (compileStructuralRule? literalScalars? profile.startSort) with
  | none => simp [structuralResult] at structural
  | some compiledRules => rfl

/-- Consequently the public proof-relevant semantic compiler is total after
the structural rule compiler has succeeded. -/
theorem scalar_semantic_compilation_succeeds
    (profile : ParserProfileSemantics.ParserProfileLayer)
    (rules : List CompiledRule) :
    (compileSemantic? literalScalars? profile rules).isSome = true := by
  have plan := scalar_parserPack_plan_compiles profile rules
  unfold compileSemantic?
  split
  · simp_all
  · rfl

/-- A successful compilation package.  The source-row equation is retained
because it is the hypothesis consumed by the structural preservation and
reflection theorems.  `semantic` hides the concrete ParserPack plan. -/
structure Compilation (document : Document) (authority : GrammarAuthority) where
  rules : List CompiledRule
  sourceRowsExact :
    compileRules?
      (syntaxBinding (denote document authority).profile)
      (denote document authority).language = some rules
  semantic :
    SemanticCompilation literalScalars?
      (denote document authority).profile rules

/-- Execute both existing generic compiler stages.  No default rules, empty
fallback plan, or first-match recovery is introduced on failure. -/
def compile? (document : Document) (authority : GrammarAuthority) :
    Option (Compilation document authority) :=
  match sourceRows : compileRules?
      (syntaxBinding (denote document authority).profile)
      (denote document authority).language with
  | none => none
  | some rules =>
      match compileSemantic? literalScalars?
          (denote document authority).profile rules with
      | none => none
      | some semantic =>
          some { rules, sourceRowsExact := sourceRows, semantic }

/-- The complete denotation-to-semantic-GSLT compiler is total on structured
plain-BNF documents.  Grammar admission remains an independent judgment. -/
theorem compilation_succeeds
    (document : Document) (authority : GrammarAuthority) :
    (compile? document authority).isSome = true := by
  have sourceRows := denoted_source_rows_compile document authority
  unfold compile?
  split
  · simp_all
  · rename_i rules sourceRowsExact
    have semantic := scalar_semantic_compilation_succeeds
      (denote document authority).profile rules
    split
    · simp_all
    · rfl

/-- An admitted grammar and its compiled parser remain one indexed object.
The source language is available as `input.validatedLanguage`; the parser
component is generated from that exact language and authority. -/
structure AdmittedCompilation (input : AdmittedInput) where
  parser : Compilation input.document input.authority

/-- Execute the generic ParserPack compiler only after carrying the admission
proof into this public boundary. -/
def compileAdmitted? (input : AdmittedInput) :
    Option (AdmittedCompilation input) :=
  (compile? input.document input.authority).map fun parser => { parser }

theorem admitted_compilation_succeeds (input : AdmittedInput) :
    (compileAdmitted? input).isSome = true := by
  simpa [compileAdmitted?] using
    compilation_succeeds input.document input.authority

namespace Compilation

/-- Successful structural compilation preserves every source production and
its source order. -/
theorem source_rules_exact {document : Document} {authority : GrammarAuthority}
    (compilation : Compilation document authority) :
    compilation.rules.map (fun rule => rule.source) =
      (denote document authority).language.terms :=
  compileRules_sourceRules
    (syntaxBinding (denote document authority).profile)
    (denote document authority).language compilation.rules
    compilation.sourceRowsExact

/-- Successful structural compilation preserves each syntax row item-for-item,
including literal and reference multiplicity. -/
theorem source_syntax_exact
    {document : Document} {authority : GrammarAuthority}
    (compilation : Compilation document authority) :
    compilation.rules.map (fun rule =>
        rule.atoms.map StructuralAtom.sourceSyntax) =
      (denote document authority).language.terms.map
        (fun rule => rule.syntaxPattern) :=
  compileRules_sourceSyntax
    (syntaxBinding (denote document authority).profile)
    (denote document authority).language compilation.rules
    compilation.sourceRowsExact

/-- Token-level derivations of the compiled structural rows are exactly the
derivations of the denoted `LanguageDef`. -/
theorem structural_derivation_iff
    {document : Document} {authority : GrammarAuthority}
    (compilation : Compilation document authority)
    (sort : String) (tokens : List String) (tree : Pattern) :
    CompiledDerives compilation.rules sort tokens tree <->
      Derives (denote document authority).language sort tokens tree :=
  compileRules_derivation_iff compilation.sourceRowsExact sort tokens tree

/-- The exact proof-relevant semantic arrow from scannerless source parsing to
the compiled ParserPack GSLT. -/
def exactParserCompiler
    {document : Document} {authority : GrammarAuthority}
    (compilation : Compilation document authority) :=
  compilation.semantic.compiler

/-- The equation-class semantic compiler consumed by ordinary GSLT/OSLF
constructions. -/
def semanticParserCompiler
    {document : Document} {authority : GrammarAuthority}
    (compilation : Compilation document authority) :=
  compilation.semantic.semanticCompiler

end Compilation

namespace AdmittedCompilation

/-- Parsing by the compiled structural rows is exactly parsing by the
validated language denoted from the admitted source document. -/
theorem structural_derivation_iff
    {input : AdmittedInput} (compilation : AdmittedCompilation input)
    (sort : String) (tokens : List String) (tree : Pattern) :
    CompiledDerives compilation.parser.rules sort tokens tree <->
      Derives input.validatedLanguage.language sort tokens tree := by
  exact Compilation.structural_derivation_iff compilation.parser sort tokens tree

end AdmittedCompilation

/-! ## Executable positive and negative controls -/

private def zeroSpan : SourceSpan := { start := 0, stop := 0 }

private def oneRuleDocument : Document :=
  { entries := [
      .rule "s"
        { alternatives := [
            { elements := [.literal "a" zeroSpan]
              span := zeroSpan }]
          span := zeroSpan }
        zeroSpan]
    span := zeroSpan }

private def oneRuleAuthority : GrammarAuthority :=
  { startName := "s", lexicalDeclarations := [] }

/-- Positive control: a real denoted grammar passes both generic compiler
stages and yields the sealed semantic GSLT compilation package. -/
theorem one_rule_compilation_succeeds :
    (compile? oneRuleDocument oneRuleAuthority).isSome = true := by
  decide +kernel

private def unsupportedLanguage : LanguageDef :=
  { name := "UnsupportedPlainBnfMutation"
    types := [{ name := "s" }]
    terms := [{
      label := "s#"
      category := "s"
      params := []
      syntaxPattern := [.separator ","] }]
    equations := []
    rewrites := [] }

/-- Negative control at the generic seam: unsupported structural syntax fails
instead of disappearing from the generated parser.  Plain-BNF denotation never
emits this constructor, but the compiler boundary remains fail-closed. -/
theorem unsupported_syntax_is_rejected :
    compileRules? (syntaxBinding {
      name := "UnsupportedProfile"
      startSort := "s"
      classes := []
      states := [] }) unsupportedLanguage = none := by
  decide +kernel

#print axioms parserReference_injective
#print axioms denoted_source_rows_compile
#print axioms scalar_parserPack_plan_compiles
#print axioms scalar_semantic_compilation_succeeds
#print axioms compilation_succeeds
#print axioms admitted_compilation_succeeds
#print axioms Compilation.source_rules_exact
#print axioms Compilation.source_syntax_exact
#print axioms Compilation.structural_derivation_iff
#print axioms AdmittedCompilation.structural_derivation_iff
#print axioms one_rule_compilation_succeeds
#print axioms unsupported_syntax_is_rejected

end Mettapedia.GSLT.Parsing.PlainBnfDenotationCompilation
