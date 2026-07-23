import Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler

/-!
# `LanguageDef` structural syntax compiler correspondence

This module gives the generated structural-rule IR its own derivation
judgment and proves bidirectional correspondence with
`OSLF.Framework.GrammarDerives`.  The two judgments are deliberately
distinct: the theorem is a compiler preservation/reflection result, not a
renaming of the source relation.

The proof covers the terminal/nonterminal fragment admitted by
`compileRules?`.  Raw-byte lexical recognition remains a separate relation;
after lexical admission has produced an ordered token ledger, this theorem
states exactly what the structural compiler preserves.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.LanguageDefSyntaxCorrespondence

open Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler
open Mettapedia.OSLF.Framework.GrammarDerives
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Successful compilation as an indexed relation -/

/-- Pointwise evidence corresponding to successful `List.mapM` compilation
of one source syntax row. -/
inductive ItemsCompile (binding : Binding) (rule : GrammarRule) :
    List SyntaxItem → List StructuralAtom → Prop where
  | nil : ItemsCompile binding rule [] []
  | cons {item : SyntaxItem} {atom : StructuralAtom}
      {items : List SyntaxItem} {atoms : List StructuralAtom}
      (compiled : compileItem? binding rule item = some atom)
      (rest : ItemsCompile binding rule items atoms) :
      ItemsCompile binding rule (item :: items) (atom :: atoms)

/-- Pointwise evidence corresponding to successful `compileRules?`. -/
inductive RulesCompile (binding : Binding) :
    List GrammarRule → List CompiledRule → Prop where
  | nil : RulesCompile binding [] []
  | cons {source : GrammarRule} {rule : CompiledRule}
      {sources : List GrammarRule} {rules : List CompiledRule}
      (compiled : compileRule? binding source = some rule)
      (rest : RulesCompile binding sources rules) :
      RulesCompile binding (source :: sources) (rule :: rules)

private theorem itemsCompile_of_mapM
    (binding : Binding) (rule : GrammarRule) :
    ∀ (items : List SyntaxItem) (atoms : List StructuralAtom),
      compileSyntaxItems? binding rule items = some atoms →
        ItemsCompile binding rule items atoms := by
  intro items
  induction items with
  | nil =>
      intro atoms compiled
      simp [compileSyntaxItems?] at compiled
      subst atoms
      exact .nil
  | cons item items inductionHypothesis =>
      intro atoms compiled
      simp only [compileSyntaxItems?, List.mapM_cons,
        Option.bind_eq_bind] at compiled
      cases headResult : compileItem? binding rule item with
      | none => simp [headResult] at compiled
      | some atom =>
          simp only [headResult] at compiled
          cases tailResult : List.mapM (compileItem? binding rule) items with
          | none => simp [tailResult] at compiled
          | some tail =>
              simp [tailResult] at compiled
              subst atoms
              exact .cons headResult <|
                inductionHypothesis tail (by
                  simpa [compileSyntaxItems?] using tailResult)

private theorem rulesCompile_of_mapM (binding : Binding) :
    ∀ (sources : List GrammarRule) (rules : List CompiledRule),
      sources.mapM (compileRule? binding) = some rules →
        RulesCompile binding sources rules := by
  intro sources
  induction sources with
  | nil =>
      intro rules compiled
      simp at compiled
      subst rules
      exact .nil
  | cons source sources inductionHypothesis =>
      intro rules compiled
      simp only [List.mapM_cons, Option.bind_eq_bind] at compiled
      cases headResult : compileRule? binding source with
      | none => simp [headResult] at compiled
      | some rule =>
          simp only [headResult] at compiled
          cases tailResult : sources.mapM (compileRule? binding) with
          | none => simp [tailResult] at compiled
          | some tail =>
              simp [tailResult] at compiled
              subst rules
              exact .cons headResult (inductionHypothesis tail tailResult)

private theorem rulesCompile_of_compileRules
    (binding : Binding) (language : LanguageDef)
    (rules : List CompiledRule)
    (compiled : compileRules? binding language = some rules) :
    RulesCompile binding language.terms rules := by
  exact rulesCompile_of_mapM binding language.terms rules <| by
    simpa [compileRules?] using compiled

private theorem RulesCompile.source_member
    {binding : Binding} :
    ∀ {sources : List GrammarRule} {rules : List CompiledRule},
      RulesCompile binding sources rules →
      ∀ {source : GrammarRule}, source ∈ sources →
        ∃ rule, rule ∈ rules ∧
          compileRule? binding source = some rule := by
  intro sources rules compiled source member
  induction compiled with
  | nil => simp at member
  | cons headCompiled tailCompiled inductionHypothesis =>
      simp only [List.mem_cons] at member
      rcases member with equality | member
      · subst source
        exact ⟨_, by simp, headCompiled⟩
      · obtain ⟨rule, ruleMember, ruleCompiled⟩ :=
          inductionHypothesis member
        exact ⟨rule, by simp [ruleMember], ruleCompiled⟩

private theorem RulesCompile.rule_member
    {binding : Binding} :
    ∀ {sources : List GrammarRule} {rules : List CompiledRule},
      RulesCompile binding sources rules →
      ∀ {rule : CompiledRule}, rule ∈ rules →
        ∃ source, source ∈ sources ∧
          compileRule? binding source = some rule := by
  intro sources rules compiled rule member
  induction compiled with
  | nil => simp at member
  | cons headCompiled tailCompiled inductionHypothesis =>
      simp only [List.mem_cons] at member
      rcases member with equality | member
      · subst rule
        exact ⟨_, by simp, headCompiled⟩
      · obtain ⟨source, sourceMember, ruleCompiled⟩ :=
          inductionHypothesis member
        exact ⟨source, by simp [sourceMember], ruleCompiled⟩

/-! ## A distinct generated-IR derivation judgment -/

mutual
  /-- Token-level derivation of the generated structural-rule IR. -/
  inductive CompiledDerives (rules : List CompiledRule) :
      String → List String → Pattern → Prop where
    | rule (rule : CompiledRule) (member : rule ∈ rules)
        (sort : String) (sortEq : rule.source.category = sort)
        (tokens : List String) (children : List Pattern)
        (items : CompiledItemsDerives rules rule.source
          rule.source.syntaxPattern rule.atoms tokens children) :
        CompiledDerives rules sort tokens
          (.apply rule.source.label children)

  /-- Left-to-right evaluation of one compiled atom vector.  Source items and
  atoms are separate indices; each constructor enforces their exact local
  correspondence. -/
  inductive CompiledItemsDerives (rules : List CompiledRule) :
      GrammarRule → List SyntaxItem → List StructuralAtom →
        List String → List Pattern → Prop where
    | nil (rule : GrammarRule) :
        CompiledItemsDerives rules rule [] [] [] []
    | terminal (rule : GrammarRule) (token parserRef : String)
        (restItems : List SyntaxItem) (restAtoms : List StructuralAtom)
        (tokens : List String) (children : List Pattern)
        (rest : CompiledItemsDerives rules rule restItems restAtoms
          tokens children) :
        CompiledItemsDerives rules rule
          (.terminal token :: restItems)
          (.terminal token parserRef :: restAtoms)
          (token :: tokens) children
    | nonterminal (rule : GrammarRule) (name sort parserRef : String)
        (sortLookup : paramSort? rule name = some sort)
        (subtokens : List String) (tree : Pattern)
        (subtree : CompiledDerives rules sort subtokens tree)
        (restItems : List SyntaxItem) (restAtoms : List StructuralAtom)
        (tokens : List String) (children : List Pattern)
        (rest : CompiledItemsDerives rules rule restItems restAtoms
          tokens children) :
        CompiledItemsDerives rules rule
          (.nonTerminal name :: restItems)
          (.nonterminal name sort parserRef :: restAtoms)
          (subtokens ++ tokens) (tree :: children)
end

mutual
  private theorem preserveDerivation
      {binding : Binding} {language : LanguageDef}
      {rules : List CompiledRule}
      (compilation : RulesCompile binding language.terms rules)
      {sort : String} {tokens : List String} {tree : Pattern}
      (derivation : Derives language sort tokens tree) :
      CompiledDerives rules sort tokens tree := by
    cases derivation with
    | rule source sourceMember sort sortEq tokens children items =>
        obtain ⟨rule, ruleMember, ruleCompiled⟩ :=
          compilation.source_member sourceMember
        have atomCompilation :
            ItemsCompile binding source source.syntaxPattern rule.atoms :=
          itemsCompile_of_mapM binding source source.syntaxPattern rule.atoms <| by
            simpa [compileItems?] using
              compileRule_atoms binding source rule ruleCompiled
        have sourceEq : rule.source = source :=
          compileRule_source binding source rule ruleCompiled
        subst source
        exact .rule rule ruleMember sort sortEq tokens children
          (preserveItems compilation atomCompilation items)

  private theorem preserveItems
      {binding : Binding} {language : LanguageDef}
      {rules : List CompiledRule}
      (compilation : RulesCompile binding language.terms rules)
      {rule : GrammarRule} {items : List SyntaxItem}
      {atoms : List StructuralAtom} {tokens : List String}
      {children : List Pattern}
      (atomCompilation : ItemsCompile binding rule items atoms)
      (derivation : DerivesItems language rule items tokens children) :
      CompiledItemsDerives rules rule items atoms tokens children := by
    cases derivation with
    | nil =>
        cases atomCompilation
        exact .nil rule
    | terminal rule token restItems tokens children restDerivation =>
        cases atomCompilation with
        | cons compiled restCompilation =>
            cases parser : binding.literalRef token with
            | none => simp [compileItem?, parser] at compiled
            | some parserRef =>
                simp [compileItem?, parser] at compiled
                subst_vars
                exact .terminal rule token parserRef restItems _ tokens
                  children <|
                    preserveItems compilation restCompilation restDerivation
    | nonTerminal rule name sort sortLookup subtokens tree subtree
        restItems tokens children restDerivation =>
        cases atomCompilation with
        | cons compiled restCompilation =>
            simp [compileItem?, sortLookup] at compiled
            subst_vars
            exact .nonterminal rule name sort
              ((binding.lexicalSortRef sort).getD (binding.categoryRef sort))
              sortLookup subtokens tree
              (preserveDerivation compilation subtree)
              restItems _ tokens children
              (preserveItems compilation restCompilation restDerivation)
end

mutual
  private def reflectDerivation
      {language : LanguageDef} {rules : List CompiledRule}
      (sourceRules : rules.map (fun rule => rule.source) = language.terms)
      {sort : String} {tokens : List String} {tree : Pattern}
      (derivation : CompiledDerives rules sort tokens tree) :
      Derives language sort tokens tree :=
    match derivation with
    | .rule rule member sort sortEq tokens children items =>
        .rule rule.source
          (by
            rw [← sourceRules]
            exact List.mem_map.mpr ⟨rule, member, rfl⟩)
          sort sortEq tokens children (reflectItems sourceRules items)

  private def reflectItems
      {language : LanguageDef} {rules : List CompiledRule}
      (sourceRules : rules.map (fun rule => rule.source) = language.terms)
      {rule : GrammarRule} {items : List SyntaxItem}
      {atoms : List StructuralAtom} {tokens : List String}
      {children : List Pattern}
      (derivation :
        CompiledItemsDerives rules rule items atoms tokens children) :
      DerivesItems language rule items tokens children :=
    match derivation with
    | .nil rule => .nil rule
    | .terminal rule token _parserRef restItems _restAtoms tokens children rest =>
        .terminal rule token restItems tokens children
          (reflectItems sourceRules rest)
    | .nonterminal rule name sort _parserRef sortLookup subtokens tree subtree
        restItems _restAtoms tokens children rest =>
        .nonTerminal rule name sort sortLookup subtokens tree
          (reflectDerivation sourceRules subtree) restItems tokens children
          (reflectItems sourceRules rest)
end

/-! ## Preservation, reflection, and action-shape closure -/

/-- Every source derivation is retained by the generated structural-rule IR. -/
theorem compileRules_preserves_derivation
    {binding : Binding} {language : LanguageDef}
    {rules : List CompiledRule}
    (compiled : compileRules? binding language = some rules)
    {sort : String} {tokens : List String} {tree : Pattern}
    (derivation : Derives language sort tokens tree) :
    CompiledDerives rules sort tokens tree :=
  preserveDerivation
    (rulesCompile_of_compileRules binding language rules compiled) derivation

/-- Every generated structural-rule derivation reflects to the authored
`LanguageDef` relation. -/
theorem compileRules_reflects_derivation
    {binding : Binding} {language : LanguageDef}
    {rules : List CompiledRule}
    (compiled : compileRules? binding language = some rules)
    {sort : String} {tokens : List String} {tree : Pattern}
    (derivation : CompiledDerives rules sort tokens tree) :
    Derives language sort tokens tree :=
  reflectDerivation
    (compileRules_sourceRules binding language rules compiled) derivation

/-- Bidirectional token-level correctness of the structural compiler. -/
theorem compileRules_derivation_iff
    {binding : Binding} {language : LanguageDef}
    {rules : List CompiledRule}
    (compiled : compileRules? binding language = some rules)
    (sort : String) (tokens : List String) (tree : Pattern) :
    CompiledDerives rules sort tokens tree ↔
      Derives language sort tokens tree :=
  ⟨compileRules_reflects_derivation compiled,
    compileRules_preserves_derivation compiled⟩

/-- Every stored rule body has the independently decodable action skeleton
required by its compiled atoms.  This closes the semantic-action side of the
structural correspondence: rule membership alone cannot hide a terminal
value retention, child drop, child reordering, or malformed pair shape. -/
theorem compileRules_action_shape
    {binding : Binding} {language : LanguageDef}
    {rules : List CompiledRule}
    (compiled : compileRules? binding language = some rules)
    (rule : CompiledRule) (member : rule ∈ rules) :
    rule.body = .node rule.source.label (compileSequence rule.atoms) ∧
      decodeSequenceActions? (compileSequence rule.atoms) =
        some (rule.atoms.map StructuralAtom.referenceAction) := by
  let compilation := rulesCompile_of_compileRules binding language rules compiled
  obtain ⟨source, _sourceMember, ruleCompiled⟩ :=
    compilation.rule_member member
  have sourceEq : rule.source = source :=
    compileRule_source binding source rule ruleCompiled
  constructor
  · rw [compileRule_body binding source rule ruleCompiled, sourceEq]
  · exact decodeSequenceActions_compileSequence rule.atoms

end Mettapedia.GSLT.Parsing.LanguageDefSyntaxCorrespondence
