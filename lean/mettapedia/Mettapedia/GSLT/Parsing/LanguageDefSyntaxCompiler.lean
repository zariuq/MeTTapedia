import Mettapedia.GSLT.LanguageDef.GrammarInferenceExtraction

/-!
# Structural `LanguageDef` to scannerless syntax compilation

This module provides the language-neutral part of a source-grammar compiler.
It retains the exact authored terminal/nonterminal origin of every structural
atom while producing the scannerless expression language consumed by
GSLT2Parse.  Concrete lexical classes and token spellings remain parameters.

The principal integrity property is `compileItems_sourceSyntax`: successful
compilation neither invents, drops, nor reorders an authored syntax item.
-/

namespace Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Scannerless grammar expressions represented by `syntax_core_v1`. -/
inductive Expr where
  | epsilon
  | char (codepoint : Nat)
  | class (name : String)
  | literal (codepoints : List Nat)
  | alt (left right : Expr)
  | seq (first second : Expr)
  | left (first second : Expr)
  | right (first second : Expr)
  | node (label : String) (body : Expr)
  | ref (name : String)
  | star (body : Expr)
  | plus (body : Expr)
  | eof
  deriving DecidableEq, Repr

/-- One named scannerless definition. -/
structure Definition where
  name : String
  body : Expr
  deriving DecidableEq, Repr

/-- One finite scalar-class membership fact. -/
structure ClassMember where
  className : String
  codepoint : Nat
  deriving DecidableEq, Repr

/-- A complete language contribution to the shared syntax GSLT. -/
structure Presentation where
  name : String
  definitions : List Definition
  members : List ClassMember
  deriving DecidableEq, Repr

/-- Decode precisely the terminal-expression fragment accepted by a
structural ParserPack item.  More general scannerless expressions are not
silently approximated as terminals. -/
def Expr.literalCodepoints? : Expr → Option (List Nat)
  | .char codepoint => some [codepoint]
  | .literal codepoints => some codepoints
  | _ => none

/-- Find a uniquely named definition.  Missing and duplicate names both fail
closed because neither supplies an unambiguous authored meaning. -/
def Presentation.uniqueDefinition?
    (presentation : Presentation) (name : String) : Option Definition :=
  match presentation.definitions.filter (fun definition =>
      definition.name == name) with
  | [definition] => some definition
  | _ => none

/-- Resolve a named terminal definition through the supplied presentation. -/
def Presentation.literalCodepoints?
    (presentation : Presentation) (name : String) : Option (List Nat) := do
  let definition ← presentation.uniqueDefinition? name
  definition.body.literalCodepoints?

private def literalLookupCanary : Presentation := {
  name := "LiteralLookupCanary"
  definitions := [{ name := "letter-a", body := .char 97 }]
  members := []
}

theorem literal_definition_lookup_positive :
    literalLookupCanary.literalCodepoints? "letter-a" = some [97] := by
  decide

private def duplicateLiteralLookupCanary : Presentation := {
  name := "DuplicateLiteralLookupCanary"
  definitions := [
    { name := "letter-a", body := .char 97 },
    { name := "letter-a", body := .char 65 }]
  members := []
}

/-- Negative control: a duplicate name cannot choose one terminal meaning by
list order. -/
theorem duplicate_literal_definition_is_rejected :
    duplicateLiteralLookupCanary.literalCodepoints? "letter-a" = none := by
  decide

/-- A compiled terminal remembers both its authored spelling and the parser
definition used to recognize it.  A compiled nonterminal likewise retains the
authored parameter name and sort. -/
inductive StructuralAtom where
  | terminal (token parserRef : String)
  | nonterminal (parameter sort parserRef : String)
  deriving DecidableEq, Repr

def StructuralAtom.sourceSyntax : StructuralAtom → SyntaxItem
  | .terminal token _ => .terminal token
  | .nonterminal parameter _ _ => .nonTerminal parameter

/-- Lexical and naming policy supplied by a language instantiation. -/
structure Binding where
  literalRef : String → Option String
  lexicalSortRef : String → Option String
  categoryRef : String → String
  ruleRef : String → String

def compileItem? (binding : Binding) (rule : GrammarRule) :
    SyntaxItem → Option StructuralAtom
  | .terminal token => do
      let parserRef ← binding.literalRef token
      pure (.terminal token parserRef)
  | .nonTerminal parameter => do
      let sort ←
        Mettapedia.OSLF.Framework.GrammarDerives.paramSort? rule parameter
      let parserRef :=
        (binding.lexicalSortRef sort).getD (binding.categoryRef sort)
      pure (.nonterminal parameter sort parserRef)
  | .separator _ | .delimiter _ _ | .op _ => none

/-- Compile an arbitrary structural suffix under one source rule.  This
worker is public because the correspondence proof follows source and compiled
item derivations in lockstep. -/
def compileSyntaxItems? (binding : Binding) (rule : GrammarRule)
    (items : List SyntaxItem) : Option (List StructuralAtom) :=
  items.mapM (compileItem? binding rule)

def compileItems? (binding : Binding) (rule : GrammarRule) :
    Option (List StructuralAtom) :=
  compileSyntaxItems? binding rule rule.syntaxPattern

@[simp] theorem compileItem_sourceSyntax
    (binding : Binding) (rule : GrammarRule)
    (item : SyntaxItem) (atom : StructuralAtom)
    (compiled : compileItem? binding rule item = some atom) :
    atom.sourceSyntax = item := by
  cases item with
  | terminal token =>
      unfold compileItem? at compiled
      cases parser : binding.literalRef token with
      | none => simp [parser] at compiled
      | some parserRef =>
          simp [parser] at compiled
          cases compiled
          rfl
  | nonTerminal parameter =>
      unfold compileItem? at compiled
      cases parameterSort :
          Mettapedia.OSLF.Framework.GrammarDerives.paramSort? rule parameter with
      | none => simp [parameterSort] at compiled
      | some sort =>
          simp [parameterSort] at compiled
          cases compiled
          rfl
  | separator separator =>
      simp [compileItem?] at compiled
  | delimiter opening closing =>
      simp [compileItem?] at compiled
  | op operator =>
      simp [compileItem?] at compiled

/-- Successful structural compilation preserves the authored syntax list
exactly, including order and multiplicity. -/
theorem compileItems_sourceSyntax
    (binding : Binding) (rule : GrammarRule)
    (atoms : List StructuralAtom)
    (compiled : compileItems? binding rule = some atoms) :
    atoms.map StructuralAtom.sourceSyntax = rule.syntaxPattern := by
  unfold compileItems? at compiled
  unfold compileSyntaxItems? at compiled
  have mapM_preserves : ∀ (items : List SyntaxItem) (result : List StructuralAtom),
      items.mapM (compileItem? binding rule) = some result →
        result.map StructuralAtom.sourceSyntax = items := by
    intro items
    induction items with
    | nil =>
        intro result h
        simp at h
        subst result
        rfl
    | cons item items ih =>
        intro result h
        simp only [List.mapM_cons, Option.bind_eq_bind] at h
        cases itemResult : compileItem? binding rule item with
        | none => simp [itemResult] at h
        | some atom =>
            simp [itemResult] at h
            cases restResult : List.mapM (compileItem? binding rule) items with
            | none => simp [restResult] at h
            | some rest =>
                simp [restResult] at h
                subst result
                simp [compileItem_sourceSyntax binding rule item atom itemResult,
                  ih rest restResult]
  exact mapM_preserves rule.syntaxPattern atoms compiled

private def containsNonterminal : List StructuralAtom → Bool
  | [] => false
  | .terminal _ _ :: rest => containsNonterminal rest
  | .nonterminal _ _ _ :: _ => true

/-- Emit semantic actions that discard concrete terminal values but retain
all authored nonterminal children in source order. -/
def compileSequence : List StructuralAtom → Expr
  | [] => .epsilon
  | .terminal _ parserRef :: rest =>
      .right (.ref parserRef) (compileSequence rest)
  | .nonterminal _ _ parserRef :: rest =>
      if containsNonterminal rest then
        .seq (.ref parserRef) (compileSequence rest)
      else
        .left (.ref parserRef) (compileSequence rest)

/-! ## Independently decoded action plan

The generated expression must do more than mention the same references.  A
terminal reference is consumed and discarded; a nonterminal reference is
retained.  `seq` is required exactly when a retained value follows, while
`left` is required for the final retained value so the semantic result is not
wrapped in a spurious pair.  The decoder below is intentionally separate from
`compileSequence`: it rejects expressions with the right references but the
wrong semantic action shape.
-/

/-- One left-to-right reference action recovered from a generated expression. -/
structure ReferenceAction where
  parserRef : String
  retain : Bool
  deriving DecidableEq, Repr

def StructuralAtom.referenceAction : StructuralAtom → ReferenceAction
  | .terminal _ parserRef => { parserRef, retain := false }
  | .nonterminal _ _ parserRef => { parserRef, retain := true }

private def hasRetainedAction (actions : List ReferenceAction) : Bool :=
  actions.any (fun action => action.retain)

/-- Decode exactly the linear fragment emitted by `compileSequence`.
The Boolean side conditions distinguish the value-pairing `seq` case from
the final-value `left` case. -/
def decodeSequenceActions? : Expr → Option (List ReferenceAction)
  | .epsilon => some []
  | .right (.ref parserRef) rest => do
      let actions ← decodeSequenceActions? rest
      pure ({ parserRef, retain := false } :: actions)
  | .seq (.ref parserRef) rest => do
      let actions ← decodeSequenceActions? rest
      if hasRetainedAction actions then
        pure ({ parserRef, retain := true } :: actions)
      else
        none
  | .left (.ref parserRef) rest => do
      let actions ← decodeSequenceActions? rest
      if hasRetainedAction actions then
        none
      else
        pure ({ parserRef, retain := true } :: actions)
  | _ => none

@[simp] private theorem hasRetainedAction_map_referenceAction
    (atoms : List StructuralAtom) :
    hasRetainedAction (atoms.map StructuralAtom.referenceAction) =
      containsNonterminal atoms := by
  induction atoms with
  | nil => rfl
  | cons atom atoms inductionHypothesis =>
      cases atom with
      | terminal token parserRef =>
          simpa [hasRetainedAction, containsNonterminal,
            StructuralAtom.referenceAction] using inductionHypothesis
      | nonterminal parameter sort parserRef =>
          simp [hasRetainedAction, containsNonterminal,
            StructuralAtom.referenceAction]

/-- The semantic action skeleton of every generated structural sequence is
exactly the authored atom sequence: all references occur once, in order;
terminal values are discarded; nonterminal values are retained; and the
pairing shape is canonical. -/
theorem decodeSequenceActions_compileSequence
    (atoms : List StructuralAtom) :
    decodeSequenceActions? (compileSequence atoms) =
      some (atoms.map StructuralAtom.referenceAction) := by
  induction atoms with
  | nil => rfl
  | cons atom atoms inductionHypothesis =>
      cases atom with
      | terminal token parserRef =>
          simp [compileSequence, decodeSequenceActions?, inductionHypothesis,
            StructuralAtom.referenceAction]
      | nonterminal parameter sort parserRef =>
          simp only [compileSequence]
          by_cases retained : containsNonterminal atoms = true
          · simp [retained, decodeSequenceActions?, inductionHypothesis,
              hasRetainedAction_map_referenceAction,
              StructuralAtom.referenceAction]
          · have noRetained : containsNonterminal atoms = false := by
              exact Bool.eq_false_of_not_eq_true retained
            simp [noRetained, decodeSequenceActions?, inductionHypothesis,
              hasRetainedAction_map_referenceAction,
              StructuralAtom.referenceAction]

structure CompiledRule where
  source : GrammarRule
  atoms : List StructuralAtom
  body : Expr
  deriving DecidableEq, Repr

def compileRule? (binding : Binding) (rule : GrammarRule) :
    Option CompiledRule :=
  match compileItems? binding rule with
  | none => none
  | some atoms =>
      some
        { source := rule
          atoms := atoms
          body := .node rule.label (compileSequence atoms) }

theorem compileRule_source
    (binding : Binding) (rule : GrammarRule)
    (compiledRule : CompiledRule)
    (compiled : compileRule? binding rule = some compiledRule) :
    compiledRule.source = rule := by
  unfold compileRule? at compiled
  cases atomsResult : compileItems? binding rule with
  | none => simp [atomsResult] at compiled
  | some atoms =>
      simp [atomsResult] at compiled
      cases compiled
      rfl

/-- The atom vector stored in a compiled rule is exactly the successful
result of compiling that rule's authored syntax row. -/
theorem compileRule_atoms
    (binding : Binding) (source : GrammarRule)
    (rule : CompiledRule)
    (compiled : compileRule? binding source = some rule) :
    compileItems? binding source = some rule.atoms := by
  unfold compileRule? at compiled
  cases atomsResult : compileItems? binding source with
  | none => simp [atomsResult] at compiled
  | some atoms =>
      simp [atomsResult] at compiled
      cases compiled
      simp

/-- The expression stored in a compiled rule is precisely the node/action
lowering of its atom vector. -/
theorem compileRule_body
    (binding : Binding) (source : GrammarRule)
    (rule : CompiledRule)
    (compiled : compileRule? binding source = some rule) :
    rule.body = .node source.label (compileSequence rule.atoms) := by
  unfold compileRule? at compiled
  cases atomsResult : compileItems? binding source with
  | none => simp [atomsResult] at compiled
  | some atoms =>
      simp [atomsResult] at compiled
      cases compiled
      rfl

theorem compileRule_sourceSyntax
    (binding : Binding) (source : GrammarRule) (rule : CompiledRule)
    (compiled : compileRule? binding source = some rule) :
    rule.atoms.map StructuralAtom.sourceSyntax = source.syntaxPattern := by
  have sourceEq : rule.source = source :=
    compileRule_source binding source rule compiled
  unfold compileRule? at compiled
  cases atomsResult : compileItems? binding source with
  | none => simp [atomsResult] at compiled
  | some atoms =>
      simp [atomsResult] at compiled
      cases compiled
      exact compileItems_sourceSyntax binding source atoms atomsResult

def compileRules? (binding : Binding) (language : LanguageDef) :
    Option (List CompiledRule) :=
  language.terms.mapM (compileRule? binding)

/-- Structural parser compilation is insensitive to every non-syntactic
field of a `LanguageDef`.  In particular, adding equations or rewrites cannot
silently alter the generated parser: only the authored grammar rows are read. -/
theorem compileRules_eq_of_terms_eq
    (binding : Binding) (left right : LanguageDef)
    (sameTerms : left.terms = right.terms) :
    compileRules? binding left = compileRules? binding right := by
  simp only [compileRules?, sameTerms]

theorem compileRules_sourceRules
    (binding : Binding) (language : LanguageDef)
    (rules : List CompiledRule)
    (compiled : compileRules? binding language = some rules) :
    rules.map (fun rule => rule.source) = language.terms := by
  unfold compileRules? at compiled
  have mapM_preserves : ∀ (source : List GrammarRule)
      (result : List CompiledRule),
      source.mapM (compileRule? binding) = some result →
        result.map (fun rule => rule.source) = source := by
    intro source
    induction source with
    | nil =>
        intro result h
        simp at h
        subst result
        rfl
    | cons rule source ih =>
        intro result h
        simp only [List.mapM_cons, Option.bind_eq_bind] at h
        cases ruleResult : compileRule? binding rule with
        | none => simp [ruleResult] at h
        | some compiledRule =>
            have sourceEq : compiledRule.source = rule :=
              compileRule_source binding rule compiledRule ruleResult
            cases restResult : List.mapM (compileRule? binding) source with
            | none => simp [ruleResult, restResult] at h
            | some rest =>
                simp [ruleResult, restResult] at h
                subst result
                simp [sourceEq, ih rest restResult]
  exact mapM_preserves language.terms rules compiled

/-- Successful whole-language compilation preserves every authored syntax
row, in rule order and with each row's item order and multiplicity intact. -/
theorem compileRules_sourceSyntax
    (binding : Binding) (language : LanguageDef)
    (rules : List CompiledRule)
    (compiled : compileRules? binding language = some rules) :
    rules.map (fun rule =>
        rule.atoms.map StructuralAtom.sourceSyntax) =
      language.terms.map (fun rule => rule.syntaxPattern) := by
  unfold compileRules? at compiled
  have mapM_preserves : ∀ (source : List GrammarRule)
      (result : List CompiledRule),
      source.mapM (compileRule? binding) = some result →
        result.map (fun rule =>
            rule.atoms.map StructuralAtom.sourceSyntax) =
          source.map (fun rule => rule.syntaxPattern) := by
    intro source
    induction source with
    | nil =>
        intro result h
        simp at h
        subst result
        rfl
    | cons rule source ih =>
        intro result h
        simp only [List.mapM_cons, Option.bind_eq_bind] at h
        cases ruleResult : compileRule? binding rule with
        | none => simp [ruleResult] at h
        | some compiledRule =>
            have syntaxEq :
                compiledRule.atoms.map StructuralAtom.sourceSyntax =
                  rule.syntaxPattern :=
              compileRule_sourceSyntax binding rule compiledRule ruleResult
            cases restResult : List.mapM (compileRule? binding) source with
            | none => simp [ruleResult, restResult] at h
            | some rest =>
                simp [ruleResult, restResult] at h
                subst result
                simp [syntaxEq, ih rest restResult]
  exact mapM_preserves language.terms rules compiled

/-- The source categories, in first-occurrence order.  Lexical sorts without
productions are intentionally absent. -/
def grammarCategories (language : LanguageDef) : List String :=
  (language.terms.map (fun rule => rule.category)).eraseDups

private def alternatives? : List Expr → Option Expr
  | [] => none
  | [expression] => some expression
  | expression :: expressions => do
      let rest ← alternatives? expressions
      pure (.alt expression rest)

/-- Compile the alternatives for one authored result category.  The
definition refers to the separately compiled source rules; it does not
reconstruct their bodies or introduce a language-specific production. -/
def compileCategory? (binding : Binding) (rules : List CompiledRule)
    (category : String) : Option Definition := do
  let alternatives ← alternatives? <|
    (rules.filter (fun rule => rule.source.category == category)).map
      (fun rule => Expr.ref (binding.ruleRef rule.source.label))
  pure
    { name := binding.categoryRef category
      body := alternatives }

/-- Compile every source category after all source rules have compiled. -/
def compileCategoryDefinitions? (binding : Binding) (language : LanguageDef)
    (rules : List CompiledRule) : Option (List Definition) :=
  (grammarCategories language).mapM (compileCategory? binding rules)

/-- Rendered definition corresponding to one compiled authored production. -/
def CompiledRule.definition (binding : Binding)
    (rule : CompiledRule) : Definition :=
  { name := binding.ruleRef rule.source.label
    body := rule.body }

private def renderCodepoints : List Nat → String
  | [] => "nil"
  | codepoint :: rest =>
      s!"(cons (cp {codepoint}) {renderCodepoints rest})"

def Expr.render : Expr → String
  | .epsilon => "(eps nil)"
  | .char codepoint => s!"(char (cp {codepoint}))"
  | .class name => s!"(class {name})"
  | .literal codepoints => s!"(lit {renderCodepoints codepoints})"
  | .alt first second => s!"(alt {first.render} {second.render})"
  | .seq first second => s!"(seq {first.render} {second.render})"
  | .left first second => s!"(left {first.render} {second.render})"
  | .right first second => s!"(right {first.render} {second.render})"
  | .node label body => s!"(node {label} {body.render})"
  | .ref name => s!"(ref {name})"
  | .star body => s!"(star {body.render})"
  | .plus body => s!"(plus {body.render})"
  | .eof => "eof"

def Definition.render (definition : Definition) : String :=
  s!"    (rule def-{definition.name} " ++
    s!"(head (definition {definition.name} {definition.body.render})) (body))"

def ClassMember.render (member : ClassMember) : String :=
  s!"    (rule member-{member.className}-{member.codepoint} " ++
    s!"(head (member {member.className} (cp {member.codepoint}))) (body))"

def Presentation.render (presentation : Presentation) : String :=
  let rules :=
    (presentation.definitions.map Definition.render) ++
      (presentation.members.map ClassMember.render)
  s!"(gslt-presentation-v1 {presentation.name}\n" ++
    "  (signature\n  )\n  (equations)\n  (rewrites\n" ++
    String.intercalate "\n" rules ++ "\n  ))\n"

end Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler
