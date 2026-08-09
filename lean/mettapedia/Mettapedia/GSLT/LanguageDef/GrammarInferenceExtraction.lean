import Mettapedia.GSLT.LanguageDef.InferenceChecker
import Mettapedia.GSLT.LanguageDef.InferenceCheckerDAG
import Mettapedia.OSLF.Framework.GrammarDerives
import Provenance.Util.ValueTypeString

/-!
# Grammar derivations as generic inference presentations

This module generates a source-indexed inference presentation from the
terminal/nonterminal fragment of a `LanguageDef` grammar.  Parsing algorithms
remain untrusted proof producers.  Their successful branches must lower to
ordinary `RawProof` values accepted by the generic inference checker.

The generated judgments use half-open token spans:

* `Boundary source i` records a valid token boundary in the admitted source;
* `TokenSpan source i j token` records one exact token occurrence;
* `GrammarDerives source sort i j tree` records a grammar derivation.

Adjacent grammar items share the same boundary metavariable.  A terminal item
therefore cannot be skipped or reordered, and nonterminal child spans compose
structurally.  Empty productions require an explicit boundary fact.  The
source ledger is finite and contributes only ground fact rules; grammar rows
contribute the recursive rules.

The current domain is deliberately the same v0 fragment as
`OSLF.Framework.GrammarDerives`: terminals and first-order nonterminals, with
each constructor parameter used exactly once and in order.  Unsupported rows
reject generation rather than silently disappearing.
-/

namespace Mettapedia.GSLT.LanguageDef.GrammarInferenceExtraction

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.GrammarDerives
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceCheckerDAG

/-- The source identity and its already-tokenized contents.  Binding the
identity to source bytes belongs to source admission, not this grammar layer. -/
structure SourceLedger where
  identity : String
  tokens : List String
deriving Repr, DecidableEq

/-- Empty source identities and empty lexer tokens are rejected at this seam. -/
def SourceLedger.isValid (ledger : SourceLedger) : Bool :=
  ledger.identity != "" && ledger.tokens.all (· != "")

private def reservedPrefix : String := "__lib_parse."
private def dataTypeName : String := reservedPrefix ++ "Data"

private def boundaryJudgmentHead : String := reservedPrefix ++ "Boundary"
private def tokenSpanJudgmentHead : String := reservedPrefix ++ "TokenSpan"
private def derivesJudgmentHead : String := reservedPrefix ++ "GrammarDerives"

/-- Length-tagged labels make source, token, sort, and boundary payloads
distinct ground constructors.  Any collision with an authored constructor is
rejected by ordinary `LanguageDef`/presentation validation. -/
private def literalLabel (kind value : String) : String :=
  reservedPrefix ++ "literal." ++ kind ++ "." ++ value

private def literalPattern (kind value : String) : Pattern :=
  .apply (literalLabel kind value) []

private theorem literalLabel_injective (kind : String) :
    Function.Injective (literalLabel kind) := by
  intro first second equality
  apply String.ext
  have listEquality :
      (reservedPrefix ++ "literal." ++ kind ++ ".").toList ++ first.toList =
        (reservedPrefix ++ "literal." ++ kind ++ ".").toList ++ second.toList := by
    simpa [literalLabel, String.toList_append, List.append_assoc] using
      congrArg String.toList equality
  exact List.append_right_injective
    (reservedPrefix ++ "literal." ++ kind ++ ".").toList listEquality

private theorem literalPattern_injective (kind : String) :
    Function.Injective (literalPattern kind) := by
  intro first second equality
  have labelEquality : literalLabel kind first = literalLabel kind second := by
    injection equality
  exact literalLabel_injective kind labelEquality

private def sourcePattern (ledger : SourceLedger) : Pattern :=
  literalPattern "source" ledger.identity

private def tokenPattern (token : String) : Pattern :=
  literalPattern "token" token

private def sortPattern (sort : String) : Pattern :=
  literalPattern "sort" sort

/-! Boundaries are ground decimal literals rather than unary successor trees.
This preserves injectivity while keeping each source position constant-sized. -/
private def boundaryPattern (index : Nat) : Pattern :=
  literalPattern "boundary" (toString index)

private theorem natRepr_injective : Function.Injective Nat.repr := by
  intro first second equality
  have firstRoundTrip := natStringValue_repr first
  have secondRoundTrip := natStringValue_repr second
  rw [equality] at firstRoundTrip
  exact firstRoundTrip.symm.trans secondRoundTrip

private theorem boundaryPattern_injective :
    Function.Injective boundaryPattern := by
  intro first second equality
  apply natRepr_injective
  simpa [boundaryPattern] using
    literalPattern_injective "boundary" equality

private def sourceVariable : Pattern := .fvar "source"
private def boundaryVariable (index : Nat) : Pattern :=
  .fvar ("boundary" ++ toString index)
private def treeVariable (index : Nat) : Pattern :=
  .fvar ("tree" ++ toString index)

private def boundaryJudgment (source boundary : Pattern) : Pattern :=
  .apply boundaryJudgmentHead [source, boundary]

private def tokenSpanJudgment
    (source left right token : Pattern) : Pattern :=
  .apply tokenSpanJudgmentHead [source, left, right, token]

private def derivesJudgment
    (source sort left right tree : Pattern) : Pattern :=
  .apply derivesJudgmentHead [source, sort, left, right, tree]

/-- Public construction of the exact root judgment for a whole source. -/
def rootJudgment (ledger : SourceLedger) (sort : String) (tree : Pattern) : Pattern :=
  derivesJudgment (sourcePattern ledger) (sortPattern sort)
    (boundaryPattern 0) (boundaryPattern ledger.tokens.length) tree

private def namespacedId (kind payload : String) : RuleId :=
  ⟨reservedPrefix ++ "rule." ++ kind ++ "." ++
    toString payload.length ++ "." ++ payload⟩

private def dataTerm (label : String) : GrammarRule :=
  { label
    category := dataTypeName
    params := []
    syntaxPattern := [] }

private def simpleParameter? : TermParam → Bool
  | .simple _ (.base _) => true
  | _ => false

private def syntaxItemSupported : SyntaxItem → Bool
  | .terminal _ | .nonTerminal _ => true
  | .separator _ | .delimiter _ _ | .op _ => false

private def nonTerminalNames : List SyntaxItem → List String
  | [] => []
  | .nonTerminal name :: rest => name :: nonTerminalNames rest
  | _ :: rest => nonTerminalNames rest

/-- Domain gate shared by generation and the correspondence theorem.  Besides
the v0 item restriction, constructor arity must agree with the derivation-tree
children generated by the concrete syntax row. -/
def ruleSupportedForInference (rule : GrammarRule) : Bool :=
  rule.params.all simpleParameter? &&
    rule.syntaxPattern.all syntaxItemSupported &&
    rule.params.map TermParam.bodyName == nonTerminalNames rule.syntaxPattern &&
    (rule.params.map TermParam.bodyName).eraseDups.length == rule.params.length

def grammarSupportedForInference (language : LanguageDef) : Bool :=
  language.terms.all ruleSupportedForInference

private def parameterSortNames (rule : GrammarRule) : List String :=
  rule.params.filterMap fun parameter =>
    match parameter with
    | .simple _ (.base sort) => some sort
    | _ => none

private def terminalNames (rule : GrammarRule) : List String :=
  rule.syntaxPattern.filterMap fun item =>
    match item with
    | .terminal token => some token
    | _ => none

private def literalLabels (language : LanguageDef) (ledger : SourceLedger) : List String :=
  let source := [literalLabel "source" ledger.identity]
  let boundaries :=
    (List.range (ledger.tokens.length + 1)).map fun index =>
      literalLabel "boundary" (toString index)
  let tokens :=
    (ledger.tokens ++ language.terms.flatMap terminalNames).map
      (literalLabel "token")
  let sorts :=
    (language.terms.map (·.category) ++
      language.terms.flatMap parameterSortNames).map (literalLabel "sort")
  (source ++ boundaries ++ tokens ++ sorts).eraseDups

/-- Project an authored grammar rule to the constructor signature consumed by
the generic checker.  Parsing syntax remains in the source grammar and is
represented by generated inference rules, not duplicated in the signature. -/
private def checkerConstructorDecl (rule : GrammarRule) : GrammarRule :=
  { rule with syntaxPattern := [] }

/-- Extend only the constructor and data vocabulary used by generated
judgments.  Grammar labels, categories, and parameters continue to determine
the exact parse-tree constructors and arities. -/
private def encodedLanguage (language : LanguageDef) (ledger : SourceLedger) : LanguageDef :=
  { language with
    types := language.types ++ [TypeDecl.plain dataTypeName]
    terms := language.terms.map checkerConstructorDecl ++
      (literalLabels language ledger).map dataTerm }

private def boundaryFactRule (ledger : SourceLedger) (index : Nat) : RuleSchema :=
  { id := namespacedId "boundary" (ledger.identity ++ ":" ++ toString index)
    metavariables := []
    premises := []
    conclusion := boundaryJudgment (sourcePattern ledger) (boundaryPattern index) }

private def tokenFactRule (ledger : SourceLedger) (index : Nat) (token : String) : RuleSchema :=
  { id := namespacedId "token" (ledger.identity ++ ":" ++ toString index)
    metavariables := []
    premises := []
    conclusion := tokenSpanJudgment (sourcePattern ledger)
      (boundaryPattern index) (boundaryPattern (index + 1)) (tokenPattern token) }

private def boundaryFactRules (ledger : SourceLedger) : List RuleSchema :=
  (List.range (ledger.tokens.length + 1)).map (boundaryFactRule ledger)

private def tokenFactRulesFrom (ledger : SourceLedger) :
    Nat → List String → List RuleSchema
  | _, [] => []
  | index, token :: tokens =>
      tokenFactRule ledger index token ::
        tokenFactRulesFrom ledger (index + 1) tokens

private def tokenFactRules (ledger : SourceLedger) : List RuleSchema :=
  tokenFactRulesFrom ledger 0 ledger.tokens

private structure SchemaBuild where
  premises : List Pattern
  children : List Pattern
  nextBoundary : Nat
  nextTree : Nat

private def buildSyntaxItems (rule : GrammarRule) :
    List SyntaxItem → Nat → Nat → Option SchemaBuild
  | [], boundaryIndex, treeIndex =>
      some
        { premises := []
          children := []
          nextBoundary := boundaryIndex
          nextTree := treeIndex }
  | .terminal token :: rest, boundaryIndex, treeIndex => do
      let tail ← buildSyntaxItems rule rest (boundaryIndex + 1) treeIndex
      pure { tail with
        premises := tokenSpanJudgment sourceVariable
          (boundaryVariable boundaryIndex)
          (boundaryVariable (boundaryIndex + 1))
          (tokenPattern token) :: tail.premises }
  | .nonTerminal name :: rest, boundaryIndex, treeIndex => do
      let sort ← paramSort? rule name
      let tail ← buildSyntaxItems rule rest (boundaryIndex + 1) (treeIndex + 1)
      let child := treeVariable treeIndex
      pure { tail with
        premises := derivesJudgment sourceVariable (sortPattern sort)
          (boundaryVariable boundaryIndex)
          (boundaryVariable (boundaryIndex + 1)) child :: tail.premises
        children := child :: tail.children }
  | .separator _ :: _, _, _ => none
  | .delimiter _ _ :: _, _, _ => none
  | .op _ :: _, _, _ => none

private def productionMetavariables (built : SchemaBuild) :
    List (String × Nat) :=
  let sourceFormal := [("source", 0)]
  let boundaryFormals :=
    (List.range (built.nextBoundary + 1)).map fun index =>
      ("boundary" ++ toString index, 0)
  let treeFormals :=
    (List.range built.nextTree).map fun index =>
      ("tree" ++ toString index, 0)
  sourceFormal ++ boundaryFormals ++ treeFormals

private def productionPremises (rule : GrammarRule) (built : SchemaBuild) :
    List Pattern :=
  if rule.syntaxPattern.isEmpty then
    [boundaryJudgment sourceVariable (boundaryVariable 0)]
  else
    built.premises

private def productionConclusion (rule : GrammarRule) (built : SchemaBuild) :
    Pattern :=
  derivesJudgment sourceVariable (sortPattern rule.category)
    (boundaryVariable 0) (boundaryVariable built.nextBoundary)
    (.apply rule.label built.children)

private def productionSchema (rule : GrammarRule) (built : SchemaBuild) :
    RuleSchema :=
  { id := namespacedId "production" rule.label
    metavariables := productionMetavariables built
    premises := productionPremises rule built
    conclusion := productionConclusion rule built }

private def productionRule? (rule : GrammarRule) : Option RuleSchema := do
  if !ruleSupportedForInference rule then none else
    let built ← buildSyntaxItems rule rule.syntaxPattern 0 0
    pure (productionSchema rule built)

private def grammarRules (language : LanguageDef) : List RuleSchema :=
  language.terms.filterMap productionRule?

private def rawPresentation (language : LanguageDef) (ledger : SourceLedger) : Presentation :=
  { language := encodedLanguage language ledger
    calculus :=
      { judgments :=
          [{ head := boundaryJudgmentHead, arity := 2 },
           { head := tokenSpanJudgmentHead, arity := 4 },
           { head := derivesJudgmentHead, arity := 5 }]
        rules :=
          boundaryFactRules ledger ++ tokenFactRules ledger ++ grammarRules language } }

/-- Generate the raw source-indexed presentation only for the exact supported
grammar fragment and a syntactically valid source ledger. -/
def generate? (language : LanguageDef) (ledger : SourceLedger) : Option Presentation :=
  if grammarSupportedForInference language && ledger.isValid then
    some (rawPresentation language ledger)
  else
    none

/-- Generate and pass the result through the generic V2 admission boundary. -/
def admit? (language : LanguageDef) (ledger : SourceLedger) :
    Option ValidatedPresentation := do
  let presentation ← generate? language ledger
  presentation.validateV2?

/-! ## Declarative source-span meaning -/

/-- `DerivesSpan` relates the numeric boundaries used by the generated
presentation to the token-list relation in `GrammarDerives`.  The parsed
segment is contiguous by construction. -/
def DerivesSpan (language : LanguageDef) (ledger : SourceLedger)
    (sort : String) (left right : Nat) (tree : Pattern) : Prop :=
  ∃ before parsed after,
    ledger.tokens = before ++ parsed ++ after ∧
      left = before.length ∧
      right = (before ++ parsed).length ∧
      Derives language sort parsed tree

/-- A valid boundary is the length of some prefix of the admitted token list. -/
def BoundaryAt (ledger : SourceLedger) (index : Nat) : Prop :=
  ∃ before after,
    ledger.tokens = before ++ after ∧ before.length = index

/-- Source-span interpretation of an ordered grammar-item derivation. -/
def DerivesItemsSpan (language : LanguageDef) (ledger : SourceLedger)
    (rule : GrammarRule) (items : List SyntaxItem)
    (left right : Nat) (children : List Pattern) : Prop :=
  ∃ before parsed after,
    ledger.tokens = before ++ parsed ++ after ∧
      left = before.length ∧
      right = (before ++ parsed).length ∧
      DerivesItems language rule items parsed children

private theorem prefix_unique
    {values first second firstRest secondRest : List String}
    (firstDecomposition : values = first ++ firstRest)
    (secondDecomposition : values = second ++ secondRest)
    (sameLength : first.length = second.length) :
    first = second := by
  have appendEquality : first ++ firstRest = second ++ secondRest :=
    firstDecomposition.symm.trans secondDecomposition
  clear firstDecomposition secondDecomposition values
  induction first generalizing second with
  | nil =>
      have : second.length = 0 := by simpa using sameLength.symm
      exact (List.eq_nil_of_length_eq_zero this).symm
  | cons firstHead firstTail inductionHypothesis =>
      cases second with
      | nil => simp at sameLength
      | cons secondHead secondTail =>
          simp only [List.cons_append, List.cons.injEq] at appendEquality
          simp only [List.length_cons, Nat.succ.injEq] at sameLength
          rw [← appendEquality.1]
          exact congrArg (List.cons firstHead)
            (inductionHypothesis sameLength appendEquality.2)

private theorem derivesSpan_start_boundary
    {language : LanguageDef} {ledger : SourceLedger}
    {sort : String} {left right : Nat} {tree : Pattern}
    (span : DerivesSpan language ledger sort left right tree) :
    BoundaryAt ledger left := by
  rcases span with ⟨before, parsed, after, source, rfl, right, derivation⟩
  exact ⟨before, parsed ++ after, by simpa [List.append_assoc] using source, rfl⟩

private theorem derivesSpan_end_boundary
    {language : LanguageDef} {ledger : SourceLedger}
    {sort : String} {left right : Nat} {tree : Pattern}
    (span : DerivesSpan language ledger sort left right tree) :
    BoundaryAt ledger right := by
  rcases span with ⟨before, parsed, after, source, left, rfl, derivation⟩
  exact ⟨before ++ parsed, after, by simpa [List.append_assoc] using source, rfl⟩

private theorem token_start_boundary
    {ledger : SourceLedger} {before after : List String} {token : String}
    (source : ledger.tokens = before ++ token :: after) :
    BoundaryAt ledger before.length :=
  ⟨before, token :: after, source, rfl⟩

private theorem token_end_boundary
    {ledger : SourceLedger} {before after : List String} {token : String}
    (source : ledger.tokens = before ++ token :: after) :
    BoundaryAt ledger (before.length + 1) := by
  refine ⟨before ++ [token], after, ?_, by simp⟩
  simpa [List.append_assoc] using source

private theorem boundaryAt_of_le (ledger : SourceLedger) (index : Nat)
    (within : index ≤ ledger.tokens.length) :
    BoundaryAt ledger index := by
  cases ledger with
  | mk identity tokens =>
      change index ≤ tokens.length at within
      change ∃ before after,
        tokens = before ++ after ∧ before.length = index
      induction tokens generalizing index with
      | nil =>
          simp only [List.length_nil] at within
          have : index = 0 := by omega
          subst index
          exact ⟨[], [], rfl, rfl⟩
      | cons token tokens inductionHypothesis =>
          cases index with
          | zero => exact ⟨[], token :: tokens, by simp, rfl⟩
          | succ index =>
              have tailWithin : index ≤ tokens.length := by simpa using within
              rcases inductionHypothesis index tailWithin with
                ⟨before, after, source, beforeLength⟩
              exact ⟨token :: before, after, by simp [source], by simp [beforeLength]⟩

/-- On the canonical whole-source boundaries, span derivability is exactly
the existing grammar relation over the ledger's complete token list. -/
theorem derivesSpan_whole_iff
    (language : LanguageDef) (ledger : SourceLedger)
    (sort : String) (tree : Pattern) :
    DerivesSpan language ledger sort 0 ledger.tokens.length tree ↔
      Derives language sort ledger.tokens tree := by
  constructor
  · rintro ⟨before, parsed, after, htokens, hleft, hright, hderives⟩
    have hbeforeLength : before.length = 0 := hleft.symm
    have hbefore : before = [] := List.eq_nil_of_length_eq_zero hbeforeLength
    subst before
    simp only [List.nil_append] at htokens hright
    have hafterLength : after.length = 0 := by
      have hlength := congrArg List.length htokens
      simp only [List.length_append] at hlength
      omega
    have hafter : after = [] := List.eq_nil_of_length_eq_zero hafterLength
    subst after
    simp only [List.append_nil] at htokens
    rw [htokens]
    exact hderives
  · intro hderives
    exact ⟨[], ledger.tokens, [], by simp, rfl, by simp, hderives⟩

/-- Semantic interpretation of the three generated judgment forms.  This is
the target of the generic-checker soundness proof; it is independent of any
particular parsing algorithm or forest representation. -/
inductive JudgmentMeaning (language : LanguageDef) (ledger : SourceLedger) :
    Pattern → Prop where
  | boundary (index : Nat) (within : index ≤ ledger.tokens.length) :
      JudgmentMeaning language ledger
        (boundaryJudgment (sourcePattern ledger) (boundaryPattern index))
  | token (before after : List String) (value : String)
      (source : ledger.tokens = before ++ value :: after) :
      JudgmentMeaning language ledger
        (tokenSpanJudgment (sourcePattern ledger)
          (boundaryPattern before.length) (boundaryPattern (before.length + 1))
          (tokenPattern value))
  | derives (sort : String) (left right : Nat) (tree : Pattern)
      (derivation : DerivesSpan language ledger sort left right tree) :
      JudgmentMeaning language ledger
        (derivesJudgment (sourcePattern ledger) (sortPattern sort)
          (boundaryPattern left) (boundaryPattern right) tree)

/-- The semantic interpretation of a whole-source generated goal reduces to
ordinary grammar derivability. -/
theorem rootJudgment_has_meaning_iff
    (language : LanguageDef) (ledger : SourceLedger)
    (sort : String) (tree : Pattern) :
    JudgmentMeaning language ledger (rootJudgment ledger sort tree) ↔
      Derives language sort ledger.tokens tree := by
  constructor
  · intro meaning
    generalize hgoal : rootJudgment ledger sort tree = goal at meaning
    cases meaning with
    | boundary index within =>
        simp [rootJudgment, derivesJudgment, boundaryJudgment,
          derivesJudgmentHead, boundaryJudgmentHead, reservedPrefix] at hgoal
    | token before after value source =>
        simp [rootJudgment, derivesJudgment, tokenSpanJudgment,
          derivesJudgmentHead, tokenSpanJudgmentHead, reservedPrefix] at hgoal
    | derives otherSort left right otherTree span =>
        have argumentEquality :
            [sourcePattern ledger, sortPattern sort, boundaryPattern 0,
              boundaryPattern ledger.tokens.length, tree] =
            [sourcePattern ledger, sortPattern otherSort, boundaryPattern left,
              boundaryPattern right, otherTree] := by
          injection hgoal
        simp only [List.cons.injEq, and_true] at argumentEquality
        have sortEquality : sort = otherSort :=
          literalPattern_injective "sort" argumentEquality.2.1
        have leftEquality : 0 = left :=
          boundaryPattern_injective argumentEquality.2.2.1
        have rightEquality : ledger.tokens.length = right :=
          boundaryPattern_injective argumentEquality.2.2.2.1
        have treeEquality : tree = otherTree := argumentEquality.2.2.2.2
        subst otherSort
        subst left
        subst right
        subst otherTree
        exact (derivesSpan_whole_iff language ledger sort tree).mp span
  · intro derivation
    exact .derives sort 0 ledger.tokens.length tree
      ((derivesSpan_whole_iff language ledger sort tree).mpr derivation)

/-! ## Generated-rule membership -/

private theorem boundaryFactRule_mem
    (ledger : SourceLedger) (index : Nat)
    (within : index ≤ ledger.tokens.length) :
    boundaryFactRule ledger index ∈ boundaryFactRules ledger := by
  apply List.mem_map.mpr
  exact ⟨index, List.mem_range.mpr (by omega), rfl⟩

private theorem boundaryFactRules_mem_iff
    (ledger : SourceLedger) (rule : RuleSchema) :
    rule ∈ boundaryFactRules ledger ↔
      ∃ index, index ≤ ledger.tokens.length ∧
        rule = boundaryFactRule ledger index := by
  constructor
  · intro membership
    rcases List.mem_map.mp membership with ⟨index, inRange, rfl⟩
    exact ⟨index, by have := List.mem_range.mp inRange; omega, rfl⟩
  · rintro ⟨index, within, rfl⟩
    exact boundaryFactRule_mem ledger index within

private theorem tokenFactRulesFrom_mem
    (ledger : SourceLedger) :
    ∀ (tokens : List String) (start : Nat) (rule : RuleSchema),
      rule ∈ tokenFactRulesFrom ledger start tokens →
        ∃ before value after,
          tokens = before ++ value :: after ∧
            rule = tokenFactRule ledger (start + before.length) value
  | [], _, _, membership => by simp [tokenFactRulesFrom] at membership
  | token :: tokens, start, rule, membership => by
      simp only [tokenFactRulesFrom, List.mem_cons] at membership
      rcases membership with equality | membership
      · subst rule
        exact ⟨[], token, tokens, by simp, by simp⟩
      · rcases tokenFactRulesFrom_mem ledger tokens (start + 1) rule membership with
          ⟨before, value, after, decomposition, ruleEquality⟩
        refine ⟨token :: before, value, after, ?_, ?_⟩
        · simp [decomposition]
        · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ruleEquality

private theorem tokenFactRule_mem_from
    (ledger : SourceLedger) (start : Nat) (before : List String)
    (value : String) (after : List String) :
    tokenFactRule ledger (start + before.length) value ∈
      tokenFactRulesFrom ledger start (before ++ value :: after) := by
  induction before generalizing start with
  | nil => simp [tokenFactRulesFrom]
  | cons token before inductionHypothesis =>
      simp only [List.cons_append, tokenFactRulesFrom, List.mem_cons]
      apply Or.inr
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        inductionHypothesis (start + 1)

private theorem tokenFactRules_mem_iff
    (ledger : SourceLedger) (rule : RuleSchema) :
    rule ∈ tokenFactRules ledger ↔
      ∃ before value after,
        ledger.tokens = before ++ value :: after ∧
          rule = tokenFactRule ledger before.length value := by
  constructor
  · intro membership
    rcases tokenFactRulesFrom_mem ledger ledger.tokens 0 rule
        (by simpa [tokenFactRules] using membership) with
      ⟨before, value, after, decomposition, ruleEquality⟩
    exact ⟨before, value, after, decomposition, by simpa using ruleEquality⟩
  · rintro ⟨before, value, after, decomposition, rfl⟩
    unfold tokenFactRules
    rw [decomposition]
    simpa using tokenFactRule_mem_from ledger 0 before value after

private theorem grammarRules_mem_iff
    (language : LanguageDef) (schema : RuleSchema) :
    schema ∈ grammarRules language ↔
      ∃ rule, rule ∈ language.terms ∧ productionRule? rule = some schema := by
  simp [grammarRules]

/-! ## Ground source facts -/

private def validatedRawPresentation
    (language : LanguageDef) (ledger : SourceLedger)
    (valid : (rawPresentation language ledger).isValidV2 = true) :
    ValidatedPresentation :=
  ⟨rawPresentation language ledger, valid⟩

private theorem instantiate_boundaryPattern (depth index : Nat) :
    instantiateSchemaAt? [] [] depth (boundaryPattern index) =
      some (boundaryPattern index) := by
  simp [boundaryPattern, literalPattern, instantiateSchemaAt?,
    instantiateSchemasAt?]

private theorem instantiate_boundaryJudgment
    (ledger : SourceLedger) (index : Nat) :
    instantiateSchemaAt? [] [] 0
        (boundaryJudgment (sourcePattern ledger) (boundaryPattern index)) =
      some (boundaryJudgment (sourcePattern ledger) (boundaryPattern index)) := by
  simp [boundaryJudgment, sourcePattern, literalPattern,
    instantiateSchemaAt?, instantiateSchemasAt?, instantiate_boundaryPattern]

private theorem instantiate_tokenSpanJudgment
    (ledger : SourceLedger) (index : Nat) (token : String) :
    instantiateSchemaAt? [] [] 0
        (tokenSpanJudgment (sourcePattern ledger)
          (boundaryPattern index) (boundaryPattern (index + 1))
          (tokenPattern token)) =
      some
        (tokenSpanJudgment (sourcePattern ledger)
          (boundaryPattern index) (boundaryPattern (index + 1))
          (tokenPattern token)) := by
  simp [tokenSpanJudgment, sourcePattern, tokenPattern, literalPattern,
    instantiateSchemaAt?, instantiateSchemasAt?,
    instantiate_boundaryPattern]

private theorem instantiate_literalPattern_any
    (formals : List (String × Nat)) (arguments : List Pattern)
    (depth : Nat) (kind value : String) :
    instantiateSchemaAt? formals arguments depth (literalPattern kind value) =
      some (literalPattern kind value) := by
  simp [literalPattern, instantiateSchemaAt?, instantiateSchemasAt?]

private theorem instantiates_literalPattern_result
    {formals : List (String × Nat)} {arguments : List Pattern}
    {depth : Nat} {kind value : String} {result : Pattern}
    (instantiation :
      InstantiatesAt formals arguments depth (literalPattern kind value) result) :
    result = literalPattern kind value := by
  have executable := instantiateSchemaAt?_complete instantiation
  rw [instantiate_literalPattern_any] at executable
  exact (Option.some.inj executable).symm

private theorem tokenInstantiation_shape
    {formals : List (String × Nat)} {arguments : List Pattern}
    {leftSchema rightSchema result : Pattern} {token : String}
    (instantiation :
      Instantiates formals arguments
        (tokenSpanJudgment sourceVariable leftSchema rightSchema
          (tokenPattern token)) result) :
    ∃ sourceValue leftValue rightValue,
      Instantiates formals arguments sourceVariable sourceValue ∧
        Instantiates formals arguments leftSchema leftValue ∧
        Instantiates formals arguments rightSchema rightValue ∧
        result = tokenSpanJudgment sourceValue leftValue rightValue
          (tokenPattern token) := by
  cases instantiation with
  | apply items =>
      cases items with
      | cons sourceInstantiation remaining =>
          cases remaining with
          | cons leftInstantiation remaining =>
              cases remaining with
              | cons rightInstantiation remaining =>
                  cases remaining with
                  | cons tokenInstantiation remaining =>
                      cases remaining with
                      | nil =>
                          have tokenEquality :=
                            instantiates_literalPattern_result tokenInstantiation
                          subst tokenEquality
                          exact ⟨_, _, _, sourceInstantiation, leftInstantiation,
                            rightInstantiation, rfl⟩

private theorem boundaryInstantiation_shape
    {formals : List (String × Nat)} {arguments : List Pattern}
    {boundarySchema result : Pattern}
    (instantiation :
      Instantiates formals arguments
        (boundaryJudgment sourceVariable boundarySchema) result) :
    ∃ sourceValue boundaryValue,
      Instantiates formals arguments sourceVariable sourceValue ∧
        Instantiates formals arguments boundarySchema boundaryValue ∧
        result = boundaryJudgment sourceValue boundaryValue := by
  cases instantiation with
  | apply items =>
      cases items with
      | cons sourceInstantiation remaining =>
          cases remaining with
          | cons boundaryInstantiation remaining =>
              cases remaining with
              | nil =>
                  exact ⟨_, _, sourceInstantiation, boundaryInstantiation, rfl⟩

private theorem derivesInstantiation_shape
    {formals : List (String × Nat)} {arguments : List Pattern}
    {leftSchema rightSchema treeSchema result : Pattern} {sort : String}
    (instantiation :
      Instantiates formals arguments
        (derivesJudgment sourceVariable (sortPattern sort)
          leftSchema rightSchema treeSchema) result) :
    ∃ sourceValue leftValue rightValue treeValue,
      Instantiates formals arguments sourceVariable sourceValue ∧
        Instantiates formals arguments leftSchema leftValue ∧
        Instantiates formals arguments rightSchema rightValue ∧
        Instantiates formals arguments treeSchema treeValue ∧
        result = derivesJudgment sourceValue (sortPattern sort)
          leftValue rightValue treeValue := by
  cases instantiation with
  | apply items =>
      cases items with
      | cons sourceInstantiation remaining =>
          cases remaining with
          | cons sortInstantiation remaining =>
              cases remaining with
              | cons leftInstantiation remaining =>
                  cases remaining with
                  | cons rightInstantiation remaining =>
                      cases remaining with
                      | cons treeInstantiation remaining =>
                          cases remaining with
                          | nil =>
                              have sortEquality :=
                                instantiates_literalPattern_result sortInstantiation
                              subst sortEquality
                              exact ⟨_, _, _, _, sourceInstantiation,
                                leftInstantiation, rightInstantiation,
                                treeInstantiation, rfl⟩

private theorem boundaryMeaning_inversion
    {language : LanguageDef} {ledger : SourceLedger}
    {sourceValue boundaryValue : Pattern}
    (meaning : JudgmentMeaning language ledger
      (boundaryJudgment sourceValue boundaryValue)) :
    ∃ index, index ≤ ledger.tokens.length ∧
      sourceValue = sourcePattern ledger ∧
      boundaryValue = boundaryPattern index := by
  generalize hgoal : boundaryJudgment sourceValue boundaryValue = goal at meaning
  cases meaning with
  | boundary index within =>
      have argumentEquality :
          [sourceValue, boundaryValue] =
            [sourcePattern ledger, boundaryPattern index] := by
        injection hgoal
      simp only [List.cons.injEq, and_true] at argumentEquality
      exact ⟨index, within, argumentEquality.1, argumentEquality.2⟩
  | token before after value source =>
      simp [boundaryJudgment, tokenSpanJudgment, boundaryJudgmentHead,
        tokenSpanJudgmentHead, reservedPrefix] at hgoal
  | derives sort left right tree derivation =>
      simp [boundaryJudgment, derivesJudgment, boundaryJudgmentHead,
        derivesJudgmentHead, reservedPrefix] at hgoal

private theorem tokenMeaning_inversion
    {language : LanguageDef} {ledger : SourceLedger}
    {sourceValue leftValue rightValue : Pattern} {token : String}
    (meaning : JudgmentMeaning language ledger
      (tokenSpanJudgment sourceValue leftValue rightValue
        (tokenPattern token))) :
    ∃ before after,
      ledger.tokens = before ++ token :: after ∧
        sourceValue = sourcePattern ledger ∧
        leftValue = boundaryPattern before.length ∧
        rightValue = boundaryPattern (before.length + 1) := by
  generalize hgoal :
    tokenSpanJudgment sourceValue leftValue rightValue (tokenPattern token) =
      goal at meaning
  cases meaning with
  | boundary index within =>
      simp [tokenSpanJudgment, boundaryJudgment, tokenSpanJudgmentHead,
        boundaryJudgmentHead, reservedPrefix] at hgoal
  | token before after value source =>
      have argumentEquality :
          [sourceValue, leftValue, rightValue, tokenPattern token] =
            [sourcePattern ledger, boundaryPattern before.length,
              boundaryPattern (before.length + 1), tokenPattern value] := by
        injection hgoal
      simp only [List.cons.injEq, and_true] at argumentEquality
      have tokenEquality : token = value :=
        literalPattern_injective "token" argumentEquality.2.2.2
      subst value
      exact ⟨before, after, source, argumentEquality.1,
        argumentEquality.2.1, argumentEquality.2.2.1⟩
  | derives sort left right tree derivation =>
      simp [tokenSpanJudgment, derivesJudgment, tokenSpanJudgmentHead,
        derivesJudgmentHead, reservedPrefix] at hgoal

private theorem derivesMeaning_inversion
    {language : LanguageDef} {ledger : SourceLedger}
    {sourceValue leftValue rightValue tree : Pattern} {sort : String}
    (meaning : JudgmentMeaning language ledger
      (derivesJudgment sourceValue (sortPattern sort)
        leftValue rightValue tree)) :
    ∃ left right,
      sourceValue = sourcePattern ledger ∧
        leftValue = boundaryPattern left ∧
        rightValue = boundaryPattern right ∧
        DerivesSpan language ledger sort left right tree := by
  generalize hgoal :
    derivesJudgment sourceValue (sortPattern sort) leftValue rightValue tree =
      goal at meaning
  cases meaning with
  | boundary index within =>
      simp [derivesJudgment, boundaryJudgment, derivesJudgmentHead,
        boundaryJudgmentHead, reservedPrefix] at hgoal
  | token before after value source =>
      simp [derivesJudgment, tokenSpanJudgment, derivesJudgmentHead,
        tokenSpanJudgmentHead, reservedPrefix] at hgoal
  | derives otherSort left right otherTree derivation =>
      have argumentEquality :
          [sourceValue, sortPattern sort, leftValue, rightValue, tree] =
            [sourcePattern ledger, sortPattern otherSort,
              boundaryPattern left, boundaryPattern right, otherTree] := by
        injection hgoal
      simp only [List.cons.injEq, and_true] at argumentEquality
      have sortEquality : sort = otherSort :=
        literalPattern_injective "sort" argumentEquality.2.1
      subst otherSort
      have treeEquality : tree = otherTree := argumentEquality.2.2.2.2
      subst otherTree
      exact ⟨left, right, argumentEquality.1, argumentEquality.2.2.1,
        argumentEquality.2.2.2.1, derivation⟩

private theorem terminal_span_cons
    {language : LanguageDef} {ledger : SourceLedger}
    {rule : GrammarRule} {token : String} {rest : List SyntaxItem}
    {before after : List String} {right : Nat} {children : List Pattern}
    (source : ledger.tokens = before ++ token :: after)
    (tailSpan : DerivesItemsSpan language ledger rule rest
      (before.length + 1) right children) :
    DerivesItemsSpan language ledger rule (.terminal token :: rest)
      before.length right children := by
  rcases tailSpan with
    ⟨tailBefore, parsed, tailAfter, tailSource, tailLeft, tailRight, tailItems⟩
  have beforeEquality : before ++ [token] = tailBefore := by
    apply prefix_unique
      (values := ledger.tokens)
      (firstRest := after)
      (secondRest := parsed ++ tailAfter)
    · simpa [List.append_assoc] using source
    · simpa [List.append_assoc] using tailSource
    · simpa using tailLeft
  subst tailBefore
  exact
    ⟨before, token :: parsed, tailAfter,
      by simpa [List.append_assoc] using tailSource,
      rfl,
      by simpa [List.append_assoc] using tailRight,
      DerivesItems.terminal rule token rest parsed children tailItems⟩

private theorem nonTerminal_span_cons
    {language : LanguageDef} {ledger : SourceLedger}
    {rule : GrammarRule} {name sort : String} {rest : List SyntaxItem}
    {left middle right : Nat} {tree : Pattern} {children : List Pattern}
    (sortLookup : paramSort? rule name = some sort)
    (headSpan : DerivesSpan language ledger sort left middle tree)
    (tailSpan : DerivesItemsSpan language ledger rule rest
      middle right children) :
    DerivesItemsSpan language ledger rule (.nonTerminal name :: rest)
      left right (tree :: children) := by
  rcases headSpan with
    ⟨before, parsedHead, afterHead, headSource, headLeft, headRight, headDerives⟩
  rcases tailSpan with
    ⟨tailBefore, parsedTail, afterTail, tailSource, tailLeft, tailRight, tailItems⟩
  have beforeEquality : before ++ parsedHead = tailBefore := by
    apply prefix_unique
      (values := ledger.tokens)
      (firstRest := afterHead)
      (secondRest := parsedTail ++ afterTail)
    · simpa [List.append_assoc] using headSource
    · simpa [List.append_assoc] using tailSource
    · omega
  subst tailBefore
  exact
    ⟨before, parsedHead ++ parsedTail, afterTail,
      by simpa [List.append_assoc] using tailSource,
      headLeft,
      by simpa [List.append_assoc] using tailRight,
      DerivesItems.nonTerminal rule name sort sortLookup parsedHead tree
        headDerives rest parsedTail children tailItems⟩

private theorem buildSyntaxItems_semantic
    (language : LanguageDef) (ledger : SourceLedger) (rule : GrammarRule)
    (formals : List (String × Nat)) (arguments : List Pattern) :
    ∀ (items : List SyntaxItem) (boundaryIndex treeIndex : Nat)
      (built : SchemaBuild) (instantiated : List Pattern) (left : Nat),
      buildSyntaxItems rule items boundaryIndex treeIndex = some built →
      InstantiatesList formals arguments built.premises instantiated →
      (∀ premise ∈ instantiated, JudgmentMeaning language ledger premise) →
      Instantiates formals arguments sourceVariable (sourcePattern ledger) →
      Instantiates formals arguments (boundaryVariable boundaryIndex)
        (boundaryPattern left) →
      BoundaryAt ledger left →
      ∃ right children,
        DerivesItemsSpan language ledger rule items left right children ∧
          Instantiates formals arguments
            (boundaryVariable built.nextBoundary) (boundaryPattern right) ∧
          InstantiatesList formals arguments built.children children
  | [], boundaryIndex, treeIndex, built, instantiated, left,
      buildEquality, premiseInstantiation, meanings,
      sourceInstantiation, boundaryInstantiation, boundaryValid => by
      simp only [buildSyntaxItems, Option.some.injEq] at buildEquality
      subst built
      cases premiseInstantiation with
      | nil =>
          rcases boundaryValid with ⟨before, after, source, beforeLength⟩
          refine ⟨left, [], ?_, boundaryInstantiation,
            InstantiatesListAt.nil 0⟩
          exact ⟨before, [], after, by simpa using source,
            beforeLength.symm, by simp [beforeLength], DerivesItems.nil rule⟩
  | .terminal token :: rest, boundaryIndex, treeIndex,
      built, instantiated, left, buildEquality, premiseInstantiation,
      meanings, sourceInstantiation, boundaryInstantiation, boundaryValid => by
      simp only [buildSyntaxItems] at buildEquality
      cases tailEquality :
          buildSyntaxItems rule rest (boundaryIndex + 1) treeIndex with
      | none => simp [tailEquality] at buildEquality
      | some tail =>
          let expected : SchemaBuild :=
            { tail with
              premises := tokenSpanJudgment sourceVariable
                (boundaryVariable boundaryIndex)
                (boundaryVariable (boundaryIndex + 1))
                (tokenPattern token) :: tail.premises }
          have expectedEquality : built = expected := by
            simpa [expected, tailEquality] using buildEquality.symm
          subst built
          simp only [expected] at premiseInstantiation ⊢
          change InstantiatesList formals arguments
            (tokenSpanJudgment sourceVariable (boundaryVariable boundaryIndex)
              (boundaryVariable (boundaryIndex + 1)) (tokenPattern token) ::
              tail.premises) instantiated at premiseInstantiation
          cases premiseInstantiation with
          | cons headInstantiation tailInstantiation =>
              rename_i headResult tailResults
              rcases tokenInstantiation_shape headInstantiation with
                ⟨sourceValue, leftValue, rightValue, headSourceInstantiation,
                  headLeftInstantiation, headRightInstantiation, headEquality⟩
              have headMeaning : JudgmentMeaning language ledger
                  (tokenSpanJudgment sourceValue leftValue rightValue
                    (tokenPattern token)) := by
                rw [← headEquality]
                exact meanings _ (by simp)
              rcases tokenMeaning_inversion headMeaning with
                ⟨before, after, tokenSource, sourceValueEquality,
                  leftValueEquality, rightValueEquality⟩
              have sourceAgreement : sourceValue = sourcePattern ledger :=
                InstantiatesAt.functional headSourceInstantiation sourceInstantiation
              have leftAgreement : leftValue = boundaryPattern left :=
                InstantiatesAt.functional headLeftInstantiation boundaryInstantiation
              have leftEquality : left = before.length :=
                boundaryPattern_injective
                  (leftAgreement.symm.trans leftValueEquality)
              rw [sourceValueEquality] at headSourceInstantiation
              rw [rightValueEquality] at headRightInstantiation
              have tailMeanings : ∀ premise ∈ tailResults,
                  JudgmentMeaning language ledger premise := by
                intro premise membership
                exact meanings premise (by simp [membership])
              rcases buildSyntaxItems_semantic language ledger rule formals arguments
                  rest (boundaryIndex + 1) treeIndex tail tailResults
                  (before.length + 1)
                  tailEquality tailInstantiation tailMeanings
                  headSourceInstantiation headRightInstantiation
                  (token_end_boundary tokenSource) with
                ⟨right, children, tailSpan, endInstantiation,
                  childrenInstantiation⟩
              subst left
              exact ⟨right, children,
                terminal_span_cons tokenSource tailSpan,
                endInstantiation, childrenInstantiation⟩
  | .nonTerminal name :: rest, boundaryIndex, treeIndex,
      built, instantiated, left, buildEquality, premiseInstantiation,
      meanings, sourceInstantiation, boundaryInstantiation, boundaryValid => by
      simp only [buildSyntaxItems] at buildEquality
      cases sortEquality : paramSort? rule name with
      | none => simp [sortEquality] at buildEquality
      | some sort =>
          simp only [sortEquality] at buildEquality
          cases tailEquality :
              buildSyntaxItems rule rest (boundaryIndex + 1) (treeIndex + 1) with
          | none => simp [tailEquality] at buildEquality
          | some tail =>
              let expected : SchemaBuild :=
                { tail with
                  premises := derivesJudgment sourceVariable (sortPattern sort)
                    (boundaryVariable boundaryIndex)
                    (boundaryVariable (boundaryIndex + 1))
                    (treeVariable treeIndex) :: tail.premises
                  children := treeVariable treeIndex :: tail.children }
              have expectedEquality : built = expected := by
                simpa [expected, sortEquality, tailEquality] using buildEquality.symm
              subst built
              simp only [expected] at premiseInstantiation ⊢
              change InstantiatesList formals arguments
                (derivesJudgment sourceVariable (sortPattern sort)
                  (boundaryVariable boundaryIndex)
                  (boundaryVariable (boundaryIndex + 1))
                  (treeVariable treeIndex) :: tail.premises)
                instantiated at premiseInstantiation
              cases premiseInstantiation with
              | cons headInstantiation tailInstantiation =>
                  rename_i headResult tailResults
                  rcases derivesInstantiation_shape headInstantiation with
                    ⟨sourceValue, leftValue, rightValue, treeValue,
                      headSourceInstantiation, headLeftInstantiation,
                      headRightInstantiation, headTreeInstantiation, headEquality⟩
                  have headMeaning : JudgmentMeaning language ledger
                      (derivesJudgment sourceValue (sortPattern sort)
                        leftValue rightValue treeValue) := by
                    rw [← headEquality]
                    exact meanings _ (by simp)
                  rcases derivesMeaning_inversion headMeaning with
                    ⟨headLeft, headRight, sourceValueEquality,
                      leftValueEquality, rightValueEquality, headSpan⟩
                  have leftAgreement : leftValue = boundaryPattern left :=
                    InstantiatesAt.functional headLeftInstantiation
                      boundaryInstantiation
                  have leftEquality : left = headLeft :=
                    boundaryPattern_injective
                      (leftAgreement.symm.trans leftValueEquality)
                  rw [sourceValueEquality] at headSourceInstantiation
                  rw [rightValueEquality] at headRightInstantiation
                  have tailMeanings : ∀ premise ∈ tailResults,
                      JudgmentMeaning language ledger premise := by
                    intro premise membership
                    exact meanings premise (by simp [membership])
                  rcases buildSyntaxItems_semantic language ledger rule
                      formals arguments rest (boundaryIndex + 1) (treeIndex + 1)
                      tail tailResults headRight tailEquality tailInstantiation tailMeanings
                      headSourceInstantiation headRightInstantiation
                      (derivesSpan_end_boundary headSpan) with
                    ⟨right, children, tailSpan, endInstantiation,
                      childrenInstantiation⟩
                  rw [leftEquality]
                  exact ⟨right, treeValue :: children,
                    nonTerminal_span_cons sortEquality headSpan tailSpan,
                    endInstantiation,
                    .cons headTreeInstantiation childrenInstantiation⟩
  | .separator separator :: rest, boundaryIndex, treeIndex,
      built, instantiated, left, buildEquality, premiseInstantiation,
      meanings, sourceInstantiation, boundaryInstantiation, boundaryValid => by
      simp [buildSyntaxItems] at buildEquality
  | .delimiter openToken closeToken :: rest, boundaryIndex, treeIndex,
      built, instantiated, left, buildEquality, premiseInstantiation,
      meanings, sourceInstantiation, boundaryInstantiation, boundaryValid => by
      simp [buildSyntaxItems] at buildEquality
  | .op operation :: rest, boundaryIndex, treeIndex,
      built, instantiated, left, buildEquality, premiseInstantiation,
      meanings, sourceInstantiation, boundaryInstantiation, boundaryValid => by
      simp [buildSyntaxItems] at buildEquality
termination_by items => sizeOf items

private theorem buildSyntaxItems_start
    (language : LanguageDef) (ledger : SourceLedger) (rule : GrammarRule)
    (formals : List (String × Nat)) (arguments : List Pattern)
    {items : List SyntaxItem} {boundaryIndex treeIndex : Nat}
    {built : SchemaBuild} {instantiated : List Pattern}
    (nonempty : items ≠ [])
    (buildEquality :
      buildSyntaxItems rule items boundaryIndex treeIndex = some built)
    (premiseInstantiation :
      InstantiatesList formals arguments built.premises instantiated)
    (meanings : ∀ premise ∈ instantiated,
      JudgmentMeaning language ledger premise) :
    ∃ left,
      Instantiates formals arguments sourceVariable (sourcePattern ledger) ∧
        Instantiates formals arguments (boundaryVariable boundaryIndex)
          (boundaryPattern left) ∧
        BoundaryAt ledger left := by
  cases items with
  | nil => exact False.elim (nonempty rfl)
  | cons item rest =>
      cases item with
      | terminal token =>
          simp only [buildSyntaxItems] at buildEquality
          cases tailEquality :
              buildSyntaxItems rule rest (boundaryIndex + 1) treeIndex with
          | none => simp [tailEquality] at buildEquality
          | some tail =>
              let expected : SchemaBuild :=
                { tail with
                  premises := tokenSpanJudgment sourceVariable
                    (boundaryVariable boundaryIndex)
                    (boundaryVariable (boundaryIndex + 1))
                    (tokenPattern token) :: tail.premises }
              have expectedEquality : built = expected := by
                simpa [expected, tailEquality] using buildEquality.symm
              subst built
              simp only [expected] at premiseInstantiation
              change InstantiatesList formals arguments
                (tokenSpanJudgment sourceVariable (boundaryVariable boundaryIndex)
                  (boundaryVariable (boundaryIndex + 1)) (tokenPattern token) ::
                  tail.premises) instantiated at premiseInstantiation
              cases premiseInstantiation with
              | cons headInstantiation tailInstantiation =>
                  rename_i headResult tailResults
                  rcases tokenInstantiation_shape headInstantiation with
                    ⟨sourceValue, leftValue, rightValue,
                      sourceInstantiation, leftInstantiation,
                      rightInstantiation, headEquality⟩
                  have headMeaning : JudgmentMeaning language ledger
                      (tokenSpanJudgment sourceValue leftValue rightValue
                        (tokenPattern token)) := by
                    rw [← headEquality]
                    exact meanings _ (by simp)
                  rcases tokenMeaning_inversion headMeaning with
                    ⟨before, after, tokenSource, sourceValueEquality,
                      leftValueEquality, rightValueEquality⟩
                  rw [sourceValueEquality] at sourceInstantiation
                  rw [leftValueEquality] at leftInstantiation
                  exact ⟨before.length, sourceInstantiation, leftInstantiation,
                    token_start_boundary tokenSource⟩
      | nonTerminal name =>
          simp only [buildSyntaxItems] at buildEquality
          cases sortEquality : paramSort? rule name with
          | none => simp [sortEquality] at buildEquality
          | some sort =>
              simp only [sortEquality] at buildEquality
              cases tailEquality :
                  buildSyntaxItems rule rest (boundaryIndex + 1) (treeIndex + 1) with
              | none => simp [tailEquality] at buildEquality
              | some tail =>
                  let expected : SchemaBuild :=
                    { tail with
                      premises := derivesJudgment sourceVariable (sortPattern sort)
                        (boundaryVariable boundaryIndex)
                        (boundaryVariable (boundaryIndex + 1))
                        (treeVariable treeIndex) :: tail.premises
                      children := treeVariable treeIndex :: tail.children }
                  have expectedEquality : built = expected := by
                    simpa [expected, sortEquality, tailEquality] using
                      buildEquality.symm
                  subst built
                  simp only [expected] at premiseInstantiation
                  change InstantiatesList formals arguments
                    (derivesJudgment sourceVariable (sortPattern sort)
                      (boundaryVariable boundaryIndex)
                      (boundaryVariable (boundaryIndex + 1))
                      (treeVariable treeIndex) :: tail.premises)
                    instantiated at premiseInstantiation
                  cases premiseInstantiation with
                  | cons headInstantiation tailInstantiation =>
                      rename_i headResult tailResults
                      rcases derivesInstantiation_shape headInstantiation with
                        ⟨sourceValue, leftValue, rightValue, treeValue,
                          sourceInstantiation, leftInstantiation,
                          rightInstantiation, treeInstantiation, headEquality⟩
                      have headMeaning : JudgmentMeaning language ledger
                          (derivesJudgment sourceValue (sortPattern sort)
                            leftValue rightValue treeValue) := by
                        rw [← headEquality]
                        exact meanings _ (by simp)
                      rcases derivesMeaning_inversion headMeaning with
                        ⟨left, right, sourceValueEquality,
                          leftValueEquality, rightValueEquality, span⟩
                      rw [sourceValueEquality] at sourceInstantiation
                      rw [leftValueEquality] at leftInstantiation
                      exact ⟨left, sourceInstantiation, leftInstantiation,
                        derivesSpan_start_boundary span⟩
      | separator separator => simp [buildSyntaxItems] at buildEquality
      | delimiter openToken closeToken => simp [buildSyntaxItems] at buildEquality
      | op operation => simp [buildSyntaxItems] at buildEquality

private theorem treeInstantiation_result
    {formals : List (String × Nat)} {arguments : List Pattern}
    {label : String} {schemas results : List Pattern} {tree : Pattern}
    (treeInstantiation :
      Instantiates formals arguments (.apply label schemas) tree)
    (childrenInstantiation :
      InstantiatesList formals arguments schemas results) :
    tree = .apply label results := by
  cases treeInstantiation with
  | apply actualInstantiation =>
      have resultEquality :=
        InstantiatesListAt.functional actualInstantiation childrenInstantiation
      rw [resultEquality]

private theorem productionRule?_some_components
    {rule : GrammarRule} {schema : RuleSchema}
    (generated : productionRule? rule = some schema) :
    ruleSupportedForInference rule = true ∧
      ∃ built,
        buildSyntaxItems rule rule.syntaxPattern 0 0 = some built ∧
          schema = productionSchema rule built := by
  by_cases supported : ruleSupportedForInference rule = true
  · refine ⟨supported, ?_⟩
    simp only [productionRule?, supported, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte] at generated
    cases buildEquality : buildSyntaxItems rule rule.syntaxPattern 0 0 with
    | none => simp [buildEquality] at generated
    | some built =>
        simp [buildEquality] at generated
        exact ⟨built, rfl, generated.symm⟩
  · have unsupported : ruleSupportedForInference rule = false :=
      Bool.eq_false_of_not_eq_true supported
    simp [productionRule?, unsupported] at generated

private theorem production_application_meaning
    (language : LanguageDef) (ledger : SourceLedger)
    (valid : (rawPresentation language ledger).isValidV2 = true)
    (rule : GrammarRule) (ruleMember : rule ∈ language.terms)
    (built : SchemaBuild)
    (buildEquality :
      buildSyntaxItems rule rule.syntaxPattern 0 0 = some built)
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern}
    (application : RuleApplication
      (validatedRawPresentation language ledger valid)
      ruleInstance premises conclusion)
    (selected :
      (validatedRawPresentation language ledger valid).1.lookupRule?
        ruleInstance.ruleId = some (productionSchema rule built))
    (meanings : ∀ premise ∈ premises,
      JudgmentMeaning language ledger premise) :
    JudgmentMeaning language ledger conclusion := by
  cases application with
  | intro stored lookup argumentsValid sideConditionsValid premisesInstantiate conclusionInstantiates =>
      have storedEquality : stored = productionSchema rule built := by
        rw [selected] at lookup
        exact (Option.some.inj lookup).symm
      subst stored
      change InstantiatesList (productionMetavariables built)
        ruleInstance.arguments (productionPremises rule built) premises
        at premisesInstantiate
      change Instantiates (productionMetavariables built)
        ruleInstance.arguments (productionConclusion rule built) conclusion
        at conclusionInstantiates
      unfold productionConclusion at conclusionInstantiates
      rcases derivesInstantiation_shape conclusionInstantiates with
        ⟨conclusionSource, conclusionLeft, conclusionRight, conclusionTree,
          conclusionSourceInstantiation, conclusionLeftInstantiation,
          conclusionRightInstantiation, conclusionTreeInstantiation,
          conclusionEquality⟩
      by_cases empty : rule.syntaxPattern = []
      · rw [empty] at buildEquality
        simp only [buildSyntaxItems, Option.some.injEq] at buildEquality
        subst built
        simp [productionPremises, empty] at premisesInstantiate
        change InstantiatesList
          (productionMetavariables
            { premises := [], children := [], nextBoundary := 0, nextTree := 0 })
          ruleInstance.arguments
          [boundaryJudgment sourceVariable (boundaryVariable 0)] premises
          at premisesInstantiate
        cases premisesInstantiate with
        | cons boundaryInstantiation remainingInstantiation =>
            rename_i boundaryResult remainingResults
            cases remainingInstantiation with
            | nil =>
                rcases boundaryInstantiation_shape boundaryInstantiation with
                  ⟨boundarySource, boundaryValue,
                    boundarySourceInstantiation, boundaryValueInstantiation,
                    boundaryEquality⟩
                have boundaryMeaning : JudgmentMeaning language ledger
                    (boundaryJudgment boundarySource boundaryValue) := by
                  rw [← boundaryEquality]
                  exact meanings _ (by simp)
                rcases boundaryMeaning_inversion boundaryMeaning with
                  ⟨index, within, boundarySourceEquality,
                    boundaryValueEquality⟩
                have sourceAgreement :
                    conclusionSource = boundarySource :=
                  InstantiatesAt.functional conclusionSourceInstantiation
                    boundarySourceInstantiation
                have leftAgreement : conclusionLeft = boundaryValue :=
                  InstantiatesAt.functional conclusionLeftInstantiation
                    boundaryValueInstantiation
                have rightAgreement : conclusionRight = boundaryValue :=
                  InstantiatesAt.functional conclusionRightInstantiation
                    boundaryValueInstantiation
                have treeEquality : conclusionTree = .apply rule.label [] :=
                  treeInstantiation_result conclusionTreeInstantiation
                    (InstantiatesListAt.nil 0)
                have sourceEquality : conclusionSource = sourcePattern ledger :=
                  sourceAgreement.trans boundarySourceEquality
                have leftEquality : conclusionLeft = boundaryPattern index :=
                  leftAgreement.trans boundaryValueEquality
                have rightEquality : conclusionRight = boundaryPattern index :=
                  rightAgreement.trans boundaryValueEquality
                rw [sourceEquality, leftEquality, rightEquality, treeEquality]
                  at conclusionEquality
                rw [conclusionEquality]
                rcases boundaryAt_of_le ledger index within with
                  ⟨before, after, source, beforeLength⟩
                apply JudgmentMeaning.derives rule.category index index
                  (.apply rule.label [])
                have emptyItems :
                    DerivesItems language rule rule.syntaxPattern [] [] := by
                  rw [empty]
                  exact DerivesItems.nil rule
                exact
                  ⟨before, [], after, by simpa using source,
                    beforeLength.symm, by simp [beforeLength],
                    Derives.rule rule ruleMember rule.category rfl [] []
                      emptyItems⟩
      · have nonemptyPremisesInstantiation :
            InstantiatesList (productionMetavariables built)
              ruleInstance.arguments built.premises premises := by
          simpa [productionPremises, empty] using premisesInstantiate
        rcases buildSyntaxItems_start language ledger rule
            (productionMetavariables built) ruleInstance.arguments empty
            buildEquality nonemptyPremisesInstantiation meanings with
          ⟨left, sourceInstantiation, leftInstantiation, leftBoundary⟩
        rcases buildSyntaxItems_semantic language ledger rule
            (productionMetavariables built) ruleInstance.arguments
            rule.syntaxPattern 0 0 built premises left buildEquality
            nonemptyPremisesInstantiation meanings sourceInstantiation leftInstantiation
            leftBoundary with
          ⟨right, children, itemsSpan, rightInstantiation,
            childrenInstantiation⟩
        have sourceEquality : conclusionSource = sourcePattern ledger :=
          InstantiatesAt.functional conclusionSourceInstantiation sourceInstantiation
        have leftEquality : conclusionLeft = boundaryPattern left :=
          InstantiatesAt.functional conclusionLeftInstantiation leftInstantiation
        have rightEquality : conclusionRight = boundaryPattern right :=
          InstantiatesAt.functional conclusionRightInstantiation rightInstantiation
        have treeEquality : conclusionTree = .apply rule.label children :=
          treeInstantiation_result conclusionTreeInstantiation
            childrenInstantiation
        rw [sourceEquality, leftEquality, rightEquality, treeEquality]
          at conclusionEquality
        rw [conclusionEquality]
        rcases itemsSpan with
          ⟨before, parsed, after, source, leftIndex, rightIndex, itemsDerivation⟩
        apply JudgmentMeaning.derives rule.category left right
          (.apply rule.label children)
        exact
          ⟨before, parsed, after, source, leftIndex, rightIndex,
            Derives.rule rule ruleMember rule.category rfl parsed children
              itemsDerivation⟩

private theorem groundConclusion_of_application
    {presentation : ValidatedPresentation}
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern} {schema : RuleSchema}
    (application :
      RuleApplication presentation ruleInstance premises conclusion)
    (selected : presentation.1.lookupRule? ruleInstance.ruleId = some schema)
    (noFormals : schema.metavariables = [])
    (groundConclusion :
      instantiateSchemaAt? [] [] 0 schema.conclusion = some schema.conclusion) :
    conclusion = schema.conclusion := by
  cases application with
  | intro stored lookup argumentsValid sideConditionsValid premisesInstantiate conclusionInstantiates =>
      have storedEquality : stored = schema := by
        rw [selected] at lookup
        exact (Option.some.inj lookup).symm
      subst stored
      rw [noFormals] at argumentsValid conclusionInstantiates
      cases argumentsEquality : ruleInstance.arguments with
      | nil =>
          have executable := instantiateSchemaAt?_complete conclusionInstantiates
          rw [argumentsEquality, groundConclusion] at executable
          exact (Option.some.inj executable).symm
      | cons argument arguments =>
          rw [argumentsEquality] at argumentsValid
          simp [argumentsValidAt] at argumentsValid

private theorem boundaryFact_application_meaning
    (language : LanguageDef) (ledger : SourceLedger)
    (valid : (rawPresentation language ledger).isValidV2 = true)
    (index : Nat) (within : index ≤ ledger.tokens.length)
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern}
    (application : RuleApplication
      (validatedRawPresentation language ledger valid)
      ruleInstance premises conclusion)
    (selected :
      (validatedRawPresentation language ledger valid).1.lookupRule?
        ruleInstance.ruleId = some (boundaryFactRule ledger index)) :
    JudgmentMeaning language ledger conclusion := by
  have conclusionEquality := groundConclusion_of_application application selected
    (by rfl) (instantiate_boundaryJudgment ledger index)
  rw [conclusionEquality]
  exact .boundary index within

private theorem tokenFact_application_meaning
    (language : LanguageDef) (ledger : SourceLedger)
    (valid : (rawPresentation language ledger).isValidV2 = true)
    (before after : List String) (token : String)
    (source : ledger.tokens = before ++ token :: after)
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern}
    (application : RuleApplication
      (validatedRawPresentation language ledger valid)
      ruleInstance premises conclusion)
    (selected :
      (validatedRawPresentation language ledger valid).1.lookupRule?
        ruleInstance.ruleId =
          some (tokenFactRule ledger before.length token)) :
    JudgmentMeaning language ledger conclusion := by
  have conclusionEquality := groundConclusion_of_application application selected
    (by rfl) (instantiate_tokenSpanJudgment ledger before.length token)
  rw [conclusionEquality]
  exact .token before after token source

/-- Every application admitted from the generated source presentation
preserves the declarative grammar meaning. -/
theorem generated_rule_application_meaning
    (language : LanguageDef) (ledger : SourceLedger)
    (valid : (rawPresentation language ledger).isValidV2 = true)
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication
      (validatedRawPresentation language ledger valid)
      ruleInstance premises conclusion)
    (premiseMeanings : ∀ premise ∈ premises,
      JudgmentMeaning language ledger premise) :
    JudgmentMeaning language ledger conclusion := by
  cases application with
  | intro stored lookup argumentsValid sideConditionsValid premisesInstantiate conclusionInstantiates =>
      have storedMember :
          stored ∈ boundaryFactRules ledger ++ tokenFactRules ledger ++
            grammarRules language := by
        change stored ∈
          (validatedRawPresentation language ledger valid).1.rules
        exact List.mem_of_find?_eq_some lookup
      rcases List.mem_append.mp storedMember with
        sourceFactMember | grammarMember
      · rcases List.mem_append.mp sourceFactMember with
          boundaryMember | tokenMember
        · rcases (boundaryFactRules_mem_iff ledger stored).mp boundaryMember with
            ⟨index, within, storedEquality⟩
          subst stored
          exact boundaryFact_application_meaning language ledger valid index within
            (.intro _ lookup argumentsValid sideConditionsValid premisesInstantiate
              conclusionInstantiates)
            lookup
        · rcases (tokenFactRules_mem_iff ledger stored).mp tokenMember with
            ⟨before, token, after, source, storedEquality⟩
          subst stored
          exact tokenFact_application_meaning language ledger valid
            before after token source
            (.intro _ lookup argumentsValid sideConditionsValid premisesInstantiate
              conclusionInstantiates)
            lookup
      · rcases (grammarRules_mem_iff language stored).mp grammarMember with
          ⟨rule, ruleMember, generated⟩
        rcases productionRule?_some_components generated with
          ⟨supported, built, buildEquality, storedEquality⟩
        subst stored
        exact production_application_meaning language ledger valid
          rule ruleMember built buildEquality
          (.intro _ lookup argumentsValid sideConditionsValid premisesInstantiate
            conclusionInstantiates)
          lookup premiseMeanings

/-- The generic checker's Type-valued derivations over a generated grammar
presentation are semantically sound for the source-indexed grammar relation. -/
theorem generated_derivation_sound
    (language : LanguageDef) (ledger : SourceLedger)
    (valid : (rawPresentation language ledger).isValidV2 = true)
    {goal : Pattern}
    (derivation : Derivation
      (validatedRawPresentation language ledger valid) goal) :
    JudgmentMeaning language ledger goal :=
  derivation.sound_of_ruleApplications (JudgmentMeaning language ledger)
    (generated_rule_application_meaning language ledger valid)

/-- Any raw proof accepted for a whole-source parse goal denotes an ordinary
`GrammarDerives.Derives` witness for the exact admitted token list. -/
theorem checkedProof_root_sound
    (language : LanguageDef) (ledger : SourceLedger)
    (valid : (rawPresentation language ledger).isValidV2 = true)
    (sort : String) (tree : Pattern)
    (proof : CheckedProof (validatedRawPresentation language ledger valid)
      (rootJudgment ledger sort tree)) :
    Derives language sort ledger.tokens tree := by
  rcases checkRaw_soundness proof.2 with ⟨derivation⟩
  exact (rootJudgment_has_meaning_iff language ledger sort tree).mp
    (generated_derivation_sound language ledger valid derivation)

/-! ## Shared proof-DAG presentation

The ordinary presentation above exposes the complete derivation tree in every
`GrammarDerives` judgment.  That is a useful direct specification, but a
right-recursive grammar repeats increasingly large child trees in rule
arguments.  The presentation below keeps the same source, spans, rule
identities, and ordered premises while storing the tree only in the proof
structure.  Its semantic interpretation reconstructs an ordinary
`GrammarDerives.Derives` witness.
-/

private def derivesNodeJudgmentHead : String :=
  reservedPrefix ++ "GrammarDerivesNode"

private def derivesNodeJudgment
    (source sort left right : Pattern) : Pattern :=
  .apply derivesNodeJudgmentHead [source, sort, left, right]

/-- Root judgment for a shared proof-DAG parse of a complete source. -/
def dagRootJudgment (ledger : SourceLedger) (sort : String) : Pattern :=
  derivesNodeJudgment (sourcePattern ledger) (sortPattern sort)
    (boundaryPattern 0) (boundaryPattern ledger.tokens.length)

private structure DAGSchemaBuild where
  premises : List Pattern
  nextBoundary : Nat

private def buildDAGSyntaxItems (rule : GrammarRule) :
    List SyntaxItem → Nat → Option DAGSchemaBuild
  | [], boundaryIndex =>
      some { premises := [], nextBoundary := boundaryIndex }
  | .terminal token :: rest, boundaryIndex => do
      let tail ← buildDAGSyntaxItems rule rest (boundaryIndex + 1)
      pure { tail with
        premises := tokenSpanJudgment sourceVariable
          (boundaryVariable boundaryIndex)
          (boundaryVariable (boundaryIndex + 1))
          (tokenPattern token) :: tail.premises }
  | .nonTerminal name :: rest, boundaryIndex => do
      let sort ← paramSort? rule name
      let tail ← buildDAGSyntaxItems rule rest (boundaryIndex + 1)
      pure { tail with
        premises := derivesNodeJudgment sourceVariable (sortPattern sort)
          (boundaryVariable boundaryIndex)
          (boundaryVariable (boundaryIndex + 1)) :: tail.premises }
  | .separator _ :: _, _ => none
  | .delimiter _ _ :: _, _ => none
  | .op _ :: _, _ => none

private def dagProductionMetavariables (built : DAGSchemaBuild) :
    List (String × Nat) :=
  let sourceFormal := [("source", 0)]
  let boundaryFormals :=
    (List.range (built.nextBoundary + 1)).map fun index =>
      ("boundary" ++ toString index, 0)
  sourceFormal ++ boundaryFormals

private def dagProductionPremises
    (rule : GrammarRule) (built : DAGSchemaBuild) : List Pattern :=
  if rule.syntaxPattern.isEmpty then
    [boundaryJudgment sourceVariable (boundaryVariable 0)]
  else
    built.premises

private def dagProductionConclusion
    (rule : GrammarRule) (built : DAGSchemaBuild) : Pattern :=
  derivesNodeJudgment sourceVariable (sortPattern rule.category)
    (boundaryVariable 0) (boundaryVariable built.nextBoundary)

private def dagProductionSchema
    (rule : GrammarRule) (built : DAGSchemaBuild) : RuleSchema :=
  { id := namespacedId "production" rule.label
    metavariables := dagProductionMetavariables built
    premises := dagProductionPremises rule built
    conclusion := dagProductionConclusion rule built }

private def dagProductionRule (rule : GrammarRule) : Option RuleSchema := do
  if !ruleSupportedForInference rule then none else
    let built ← buildDAGSyntaxItems rule rule.syntaxPattern 0
    pure (dagProductionSchema rule built)

private def dagGrammarRules (language : LanguageDef) : List RuleSchema :=
  language.terms.filterMap dagProductionRule

private theorem dagGrammarRules_mem_iff
    (language : LanguageDef) (schema : RuleSchema) :
    schema ∈ dagGrammarRules language ↔
      ∃ rule, rule ∈ language.terms ∧ dagProductionRule rule = some schema := by
  simp [dagGrammarRules]

private def rawDAGPresentation
    (language : LanguageDef) (ledger : SourceLedger) : Presentation :=
  { language := encodedLanguage language ledger
    calculus :=
      { judgments :=
          [{ head := boundaryJudgmentHead, arity := 2 },
           { head := tokenSpanJudgmentHead, arity := 4 },
           { head := derivesNodeJudgmentHead, arity := 4 }]
        rules := boundaryFactRules ledger ++ tokenFactRules ledger ++
          dagGrammarRules language } }

/-- Generate the shared proof-DAG presentation from the same grammar and
source ledger as the direct tree presentation. -/
def generateDAGPresentation
    (language : LanguageDef) (ledger : SourceLedger) : Option Presentation :=
  if grammarSupportedForInference language && ledger.isValid then
    some (rawDAGPresentation language ledger)
  else
    none

/-- Generate and validate the shared proof-DAG presentation. -/
def admitDAGPresentation
    (language : LanguageDef) (ledger : SourceLedger) :
    Option ValidatedPresentation := do
  let presentation ← generateDAGPresentation language ledger
  presentation.validateV2?

private inductive DAGJudgmentMeaning
    (language : LanguageDef) (ledger : SourceLedger) : Pattern → Prop where
  | boundary (index : Nat) (within : index ≤ ledger.tokens.length) :
      DAGJudgmentMeaning language ledger
        (boundaryJudgment (sourcePattern ledger) (boundaryPattern index))
  | token (before after : List String) (value : String)
      (source : ledger.tokens = before ++ value :: after) :
      DAGJudgmentMeaning language ledger
        (tokenSpanJudgment (sourcePattern ledger)
          (boundaryPattern before.length) (boundaryPattern (before.length + 1))
          (tokenPattern value))
  | derives (sort : String) (left right : Nat) (tree : Pattern)
      (derivation : DerivesSpan language ledger sort left right tree) :
      DAGJudgmentMeaning language ledger
        (derivesNodeJudgment (sourcePattern ledger) (sortPattern sort)
          (boundaryPattern left) (boundaryPattern right))

private theorem dagRootJudgment_has_meaning_iff
    (language : LanguageDef) (ledger : SourceLedger) (sort : String) :
    DAGJudgmentMeaning language ledger (dagRootJudgment ledger sort) ↔
      ∃ tree, Derives language sort ledger.tokens tree := by
  constructor
  · intro meaning
    generalize hgoal : dagRootJudgment ledger sort = goal at meaning
    cases meaning with
    | boundary index within =>
        simp [dagRootJudgment, derivesNodeJudgment, boundaryJudgment,
          derivesNodeJudgmentHead, boundaryJudgmentHead, reservedPrefix] at hgoal
    | token before after value source =>
        simp [dagRootJudgment, derivesNodeJudgment, tokenSpanJudgment,
          derivesNodeJudgmentHead, tokenSpanJudgmentHead, reservedPrefix] at hgoal
    | derives otherSort left right tree span =>
        have argumentEquality :
            [sourcePattern ledger, sortPattern sort, boundaryPattern 0,
              boundaryPattern ledger.tokens.length] =
            [sourcePattern ledger, sortPattern otherSort,
              boundaryPattern left, boundaryPattern right] := by
          injection hgoal
        simp only [List.cons.injEq, and_true] at argumentEquality
        have sortEquality : sort = otherSort :=
          literalPattern_injective "sort" argumentEquality.2.1
        have leftEquality : 0 = left :=
          boundaryPattern_injective argumentEquality.2.2.1
        have rightEquality : ledger.tokens.length = right :=
          boundaryPattern_injective argumentEquality.2.2.2
        subst otherSort
        subst left
        subst right
        exact ⟨tree, (derivesSpan_whole_iff language ledger sort tree).mp span⟩
  · rintro ⟨tree, derivation⟩
    exact .derives sort 0 ledger.tokens.length tree
      ((derivesSpan_whole_iff language ledger sort tree).mpr derivation)

private def validatedRawDAGPresentation
    (language : LanguageDef) (ledger : SourceLedger)
    (valid : (rawDAGPresentation language ledger).isValidV2 = true) :
    ValidatedPresentation :=
  ⟨rawDAGPresentation language ledger, valid⟩

private theorem derivesNodeInstantiation_shape
    {formals : List (String × Nat)} {arguments : List Pattern}
    {leftSchema rightSchema result : Pattern} {sort : String}
    (instantiation :
      Instantiates formals arguments
        (derivesNodeJudgment sourceVariable (sortPattern sort)
          leftSchema rightSchema) result) :
    ∃ sourceValue leftValue rightValue,
      Instantiates formals arguments sourceVariable sourceValue ∧
        Instantiates formals arguments leftSchema leftValue ∧
        Instantiates formals arguments rightSchema rightValue ∧
        result = derivesNodeJudgment sourceValue (sortPattern sort)
          leftValue rightValue := by
  cases instantiation with
  | apply items =>
      cases items with
      | cons sourceInstantiation remaining =>
          cases remaining with
          | cons sortInstantiation remaining =>
              cases remaining with
              | cons leftInstantiation remaining =>
                  cases remaining with
                  | cons rightInstantiation remaining =>
                      cases remaining with
                      | nil =>
                          have sortEquality :=
                            instantiates_literalPattern_result sortInstantiation
                          subst sortEquality
                          exact ⟨_, _, _, sourceInstantiation,
                            leftInstantiation, rightInstantiation, rfl⟩

private theorem dagBoundaryMeaning_inversion
    {language : LanguageDef} {ledger : SourceLedger}
    {sourceValue boundaryValue : Pattern}
    (meaning : DAGJudgmentMeaning language ledger
      (boundaryJudgment sourceValue boundaryValue)) :
    ∃ index, index ≤ ledger.tokens.length ∧
      sourceValue = sourcePattern ledger ∧
      boundaryValue = boundaryPattern index := by
  generalize hgoal : boundaryJudgment sourceValue boundaryValue = goal at meaning
  cases meaning with
  | boundary index within =>
      have argumentEquality :
          [sourceValue, boundaryValue] =
            [sourcePattern ledger, boundaryPattern index] := by
        injection hgoal
      simp only [List.cons.injEq, and_true] at argumentEquality
      exact ⟨index, within, argumentEquality.1, argumentEquality.2⟩
  | token before after value source =>
      simp [boundaryJudgment, tokenSpanJudgment, boundaryJudgmentHead,
        tokenSpanJudgmentHead, reservedPrefix] at hgoal
  | derives sort left right tree derivation =>
      simp [boundaryJudgment, derivesNodeJudgment, boundaryJudgmentHead,
        derivesNodeJudgmentHead, reservedPrefix] at hgoal

private theorem dagTokenMeaning_inversion
    {language : LanguageDef} {ledger : SourceLedger}
    {sourceValue leftValue rightValue : Pattern} {token : String}
    (meaning : DAGJudgmentMeaning language ledger
      (tokenSpanJudgment sourceValue leftValue rightValue
        (tokenPattern token))) :
    ∃ before after,
      ledger.tokens = before ++ token :: after ∧
        sourceValue = sourcePattern ledger ∧
        leftValue = boundaryPattern before.length ∧
        rightValue = boundaryPattern (before.length + 1) := by
  generalize hgoal :
    tokenSpanJudgment sourceValue leftValue rightValue (tokenPattern token) =
      goal at meaning
  cases meaning with
  | boundary index within =>
      simp [tokenSpanJudgment, boundaryJudgment, tokenSpanJudgmentHead,
        boundaryJudgmentHead, reservedPrefix] at hgoal
  | token before after value source =>
      have argumentEquality :
          [sourceValue, leftValue, rightValue, tokenPattern token] =
            [sourcePattern ledger, boundaryPattern before.length,
              boundaryPattern (before.length + 1), tokenPattern value] := by
        injection hgoal
      simp only [List.cons.injEq, and_true] at argumentEquality
      have tokenEquality : token = value :=
        literalPattern_injective "token" argumentEquality.2.2.2
      subst value
      exact ⟨before, after, source, argumentEquality.1,
        argumentEquality.2.1, argumentEquality.2.2.1⟩
  | derives sort left right tree derivation =>
      simp [tokenSpanJudgment, derivesNodeJudgment, tokenSpanJudgmentHead,
        derivesNodeJudgmentHead, reservedPrefix] at hgoal

private theorem dagDerivesMeaning_inversion
    {language : LanguageDef} {ledger : SourceLedger}
    {sourceValue leftValue rightValue : Pattern} {sort : String}
    (meaning : DAGJudgmentMeaning language ledger
      (derivesNodeJudgment sourceValue (sortPattern sort)
        leftValue rightValue)) :
    ∃ left right tree,
      sourceValue = sourcePattern ledger ∧
        leftValue = boundaryPattern left ∧
        rightValue = boundaryPattern right ∧
        DerivesSpan language ledger sort left right tree := by
  generalize hgoal :
    derivesNodeJudgment sourceValue (sortPattern sort) leftValue rightValue =
      goal at meaning
  cases meaning with
  | boundary index within =>
      simp [derivesNodeJudgment, boundaryJudgment, derivesNodeJudgmentHead,
        boundaryJudgmentHead, reservedPrefix] at hgoal
  | token before after value source =>
      simp [derivesNodeJudgment, tokenSpanJudgment, derivesNodeJudgmentHead,
        tokenSpanJudgmentHead, reservedPrefix] at hgoal
  | derives otherSort left right tree derivation =>
      have argumentEquality :
          [sourceValue, sortPattern sort, leftValue, rightValue] =
            [sourcePattern ledger, sortPattern otherSort,
              boundaryPattern left, boundaryPattern right] := by
        injection hgoal
      simp only [List.cons.injEq, and_true] at argumentEquality
      have sortEquality : sort = otherSort :=
        literalPattern_injective "sort" argumentEquality.2.1
      subst otherSort
      exact ⟨left, right, tree, argumentEquality.1,
        argumentEquality.2.2.1, argumentEquality.2.2.2, derivation⟩

private theorem buildDAGSyntaxItems_semantic
    (language : LanguageDef) (ledger : SourceLedger) (rule : GrammarRule)
    (formals : List (String × Nat)) (arguments : List Pattern) :
    ∀ (items : List SyntaxItem) (boundaryIndex : Nat)
      (built : DAGSchemaBuild) (instantiated : List Pattern) (left : Nat),
      buildDAGSyntaxItems rule items boundaryIndex = some built →
      InstantiatesList formals arguments built.premises instantiated →
      (∀ premise ∈ instantiated, DAGJudgmentMeaning language ledger premise) →
      Instantiates formals arguments sourceVariable (sourcePattern ledger) →
      Instantiates formals arguments (boundaryVariable boundaryIndex)
        (boundaryPattern left) →
      BoundaryAt ledger left →
      ∃ right children,
        DerivesItemsSpan language ledger rule items left right children ∧
          Instantiates formals arguments
            (boundaryVariable built.nextBoundary) (boundaryPattern right)
  | [], boundaryIndex, built, instantiated, left,
      buildEquality, premiseInstantiation, meanings,
      sourceInstantiation, boundaryInstantiation, boundaryValid => by
      simp only [buildDAGSyntaxItems, Option.some.injEq] at buildEquality
      subst built
      cases premiseInstantiation with
      | nil =>
          rcases boundaryValid with ⟨before, after, source, beforeLength⟩
          refine ⟨left, [], ?_, boundaryInstantiation⟩
          exact ⟨before, [], after, by simpa using source,
            beforeLength.symm, by simp [beforeLength], DerivesItems.nil rule⟩
  | .terminal token :: rest, boundaryIndex, built, instantiated, left,
      buildEquality, premiseInstantiation, meanings,
      sourceInstantiation, boundaryInstantiation, boundaryValid => by
      simp only [buildDAGSyntaxItems] at buildEquality
      cases tailEquality :
          buildDAGSyntaxItems rule rest (boundaryIndex + 1) with
      | none => simp [tailEquality] at buildEquality
      | some tail =>
          let expected : DAGSchemaBuild :=
            { tail with
              premises := tokenSpanJudgment sourceVariable
                (boundaryVariable boundaryIndex)
                (boundaryVariable (boundaryIndex + 1))
                (tokenPattern token) :: tail.premises }
          have expectedEquality : built = expected := by
            simpa [expected, tailEquality] using buildEquality.symm
          subst built
          simp only [expected] at premiseInstantiation ⊢
          change InstantiatesList formals arguments
            (tokenSpanJudgment sourceVariable (boundaryVariable boundaryIndex)
              (boundaryVariable (boundaryIndex + 1)) (tokenPattern token) ::
              tail.premises) instantiated at premiseInstantiation
          cases premiseInstantiation with
          | cons headInstantiation tailInstantiation =>
              rename_i headResult tailResults
              rcases tokenInstantiation_shape headInstantiation with
                ⟨sourceValue, leftValue, rightValue, headSourceInstantiation,
                  headLeftInstantiation, headRightInstantiation, headEquality⟩
              have headMeaning : DAGJudgmentMeaning language ledger
                  (tokenSpanJudgment sourceValue leftValue rightValue
                    (tokenPattern token)) := by
                rw [← headEquality]
                exact meanings _ (by simp)
              rcases dagTokenMeaning_inversion headMeaning with
                ⟨before, after, tokenSource, sourceValueEquality,
                  leftValueEquality, rightValueEquality⟩
              have leftAgreement : leftValue = boundaryPattern left :=
                InstantiatesAt.functional headLeftInstantiation
                  boundaryInstantiation
              have leftEquality : left = before.length :=
                boundaryPattern_injective
                  (leftAgreement.symm.trans leftValueEquality)
              rw [sourceValueEquality] at headSourceInstantiation
              rw [rightValueEquality] at headRightInstantiation
              have tailMeanings : ∀ premise ∈ tailResults,
                  DAGJudgmentMeaning language ledger premise := by
                intro premise membership
                exact meanings premise (by simp [membership])
              rcases buildDAGSyntaxItems_semantic language ledger rule
                  formals arguments rest (boundaryIndex + 1) tail tailResults
                  (before.length + 1) tailEquality tailInstantiation tailMeanings
                  headSourceInstantiation headRightInstantiation
                  (token_end_boundary tokenSource) with
                ⟨right, children, tailSpan, endInstantiation⟩
              subst left
              exact ⟨right, children,
                terminal_span_cons tokenSource tailSpan, endInstantiation⟩
  | .nonTerminal name :: rest, boundaryIndex, built, instantiated, left,
      buildEquality, premiseInstantiation, meanings,
      sourceInstantiation, boundaryInstantiation, boundaryValid => by
      simp only [buildDAGSyntaxItems] at buildEquality
      cases sortEquality : paramSort? rule name with
      | none => simp [sortEquality] at buildEquality
      | some sort =>
          simp only [sortEquality] at buildEquality
          cases tailEquality :
              buildDAGSyntaxItems rule rest (boundaryIndex + 1) with
          | none => simp [tailEquality] at buildEquality
          | some tail =>
              let expected : DAGSchemaBuild :=
                { tail with
                  premises := derivesNodeJudgment sourceVariable
                    (sortPattern sort) (boundaryVariable boundaryIndex)
                    (boundaryVariable (boundaryIndex + 1)) :: tail.premises }
              have expectedEquality : built = expected := by
                simpa [expected, sortEquality, tailEquality] using
                  buildEquality.symm
              subst built
              simp only [expected] at premiseInstantiation ⊢
              change InstantiatesList formals arguments
                (derivesNodeJudgment sourceVariable (sortPattern sort)
                  (boundaryVariable boundaryIndex)
                  (boundaryVariable (boundaryIndex + 1)) :: tail.premises)
                instantiated at premiseInstantiation
              cases premiseInstantiation with
              | cons headInstantiation tailInstantiation =>
                  rename_i headResult tailResults
                  rcases derivesNodeInstantiation_shape headInstantiation with
                    ⟨sourceValue, leftValue, rightValue,
                      headSourceInstantiation, headLeftInstantiation,
                      headRightInstantiation, headEquality⟩
                  have headMeaning : DAGJudgmentMeaning language ledger
                      (derivesNodeJudgment sourceValue (sortPattern sort)
                        leftValue rightValue) := by
                    rw [← headEquality]
                    exact meanings _ (by simp)
                  rcases dagDerivesMeaning_inversion headMeaning with
                    ⟨headLeft, headRight, tree, sourceValueEquality,
                      leftValueEquality, rightValueEquality, headSpan⟩
                  have leftAgreement : leftValue = boundaryPattern left :=
                    InstantiatesAt.functional headLeftInstantiation
                      boundaryInstantiation
                  have leftEquality : left = headLeft :=
                    boundaryPattern_injective
                      (leftAgreement.symm.trans leftValueEquality)
                  rw [sourceValueEquality] at headSourceInstantiation
                  rw [rightValueEquality] at headRightInstantiation
                  have tailMeanings : ∀ premise ∈ tailResults,
                      DAGJudgmentMeaning language ledger premise := by
                    intro premise membership
                    exact meanings premise (by simp [membership])
                  rcases buildDAGSyntaxItems_semantic language ledger rule
                      formals arguments rest (boundaryIndex + 1) tail tailResults
                      headRight tailEquality tailInstantiation tailMeanings
                      headSourceInstantiation headRightInstantiation
                      (derivesSpan_end_boundary headSpan) with
                    ⟨right, children, tailSpan, endInstantiation⟩
                  rw [leftEquality]
                  exact ⟨right, tree :: children,
                    nonTerminal_span_cons sortEquality headSpan tailSpan,
                    endInstantiation⟩
  | .separator separator :: rest, boundaryIndex, built, instantiated, left,
      buildEquality, premiseInstantiation, meanings,
      sourceInstantiation, boundaryInstantiation, boundaryValid => by
      simp [buildDAGSyntaxItems] at buildEquality
  | .delimiter openToken closeToken :: rest, boundaryIndex, built,
      instantiated, left, buildEquality, premiseInstantiation, meanings,
      sourceInstantiation, boundaryInstantiation, boundaryValid => by
      simp [buildDAGSyntaxItems] at buildEquality
  | .op operation :: rest, boundaryIndex, built, instantiated, left,
      buildEquality, premiseInstantiation, meanings,
      sourceInstantiation, boundaryInstantiation, boundaryValid => by
      simp [buildDAGSyntaxItems] at buildEquality
termination_by items => sizeOf items

private theorem buildDAGSyntaxItems_start
    (language : LanguageDef) (ledger : SourceLedger) (rule : GrammarRule)
    (formals : List (String × Nat)) (arguments : List Pattern)
    {items : List SyntaxItem} {boundaryIndex : Nat}
    {built : DAGSchemaBuild} {instantiated : List Pattern}
    (nonempty : items ≠ [])
    (buildEquality :
      buildDAGSyntaxItems rule items boundaryIndex = some built)
    (premiseInstantiation :
      InstantiatesList formals arguments built.premises instantiated)
    (meanings : ∀ premise ∈ instantiated,
      DAGJudgmentMeaning language ledger premise) :
    ∃ left,
      Instantiates formals arguments sourceVariable (sourcePattern ledger) ∧
        Instantiates formals arguments (boundaryVariable boundaryIndex)
          (boundaryPattern left) ∧
        BoundaryAt ledger left := by
  cases items with
  | nil => exact False.elim (nonempty rfl)
  | cons item rest =>
      cases item with
      | terminal token =>
          simp only [buildDAGSyntaxItems] at buildEquality
          cases tailEquality :
              buildDAGSyntaxItems rule rest (boundaryIndex + 1) with
          | none => simp [tailEquality] at buildEquality
          | some tail =>
              let expected : DAGSchemaBuild :=
                { tail with
                  premises := tokenSpanJudgment sourceVariable
                    (boundaryVariable boundaryIndex)
                    (boundaryVariable (boundaryIndex + 1))
                    (tokenPattern token) :: tail.premises }
              have expectedEquality : built = expected := by
                simpa [expected, tailEquality] using buildEquality.symm
              subst built
              simp only [expected] at premiseInstantiation
              change InstantiatesList formals arguments
                (tokenSpanJudgment sourceVariable
                  (boundaryVariable boundaryIndex)
                  (boundaryVariable (boundaryIndex + 1))
                  (tokenPattern token) :: tail.premises)
                instantiated at premiseInstantiation
              cases premiseInstantiation with
              | cons headInstantiation tailInstantiation =>
                  rename_i headResult tailResults
                  rcases tokenInstantiation_shape headInstantiation with
                    ⟨sourceValue, leftValue, rightValue,
                      sourceInstantiation, leftInstantiation,
                      rightInstantiation, headEquality⟩
                  have headMeaning : DAGJudgmentMeaning language ledger
                      (tokenSpanJudgment sourceValue leftValue rightValue
                        (tokenPattern token)) := by
                    rw [← headEquality]
                    exact meanings _ (by simp)
                  rcases dagTokenMeaning_inversion headMeaning with
                    ⟨before, after, tokenSource, sourceValueEquality,
                      leftValueEquality, rightValueEquality⟩
                  rw [sourceValueEquality] at sourceInstantiation
                  rw [leftValueEquality] at leftInstantiation
                  exact ⟨before.length, sourceInstantiation, leftInstantiation,
                    token_start_boundary tokenSource⟩
      | nonTerminal name =>
          simp only [buildDAGSyntaxItems] at buildEquality
          cases sortEquality : paramSort? rule name with
          | none => simp [sortEquality] at buildEquality
          | some sort =>
              simp only [sortEquality] at buildEquality
              cases tailEquality :
                  buildDAGSyntaxItems rule rest (boundaryIndex + 1) with
              | none => simp [tailEquality] at buildEquality
              | some tail =>
                  let expected : DAGSchemaBuild :=
                    { tail with
                      premises := derivesNodeJudgment sourceVariable
                        (sortPattern sort) (boundaryVariable boundaryIndex)
                        (boundaryVariable (boundaryIndex + 1)) :: tail.premises }
                  have expectedEquality : built = expected := by
                    simpa [expected, sortEquality, tailEquality] using
                      buildEquality.symm
                  subst built
                  simp only [expected] at premiseInstantiation
                  change InstantiatesList formals arguments
                    (derivesNodeJudgment sourceVariable (sortPattern sort)
                      (boundaryVariable boundaryIndex)
                      (boundaryVariable (boundaryIndex + 1)) :: tail.premises)
                    instantiated at premiseInstantiation
                  cases premiseInstantiation with
                  | cons headInstantiation tailInstantiation =>
                      rename_i headResult tailResults
                      rcases derivesNodeInstantiation_shape headInstantiation with
                        ⟨sourceValue, leftValue, rightValue,
                          sourceInstantiation, leftInstantiation,
                          rightInstantiation, headEquality⟩
                      have headMeaning : DAGJudgmentMeaning language ledger
                          (derivesNodeJudgment sourceValue (sortPattern sort)
                            leftValue rightValue) := by
                        rw [← headEquality]
                        exact meanings _ (by simp)
                      rcases dagDerivesMeaning_inversion headMeaning with
                        ⟨left, right, tree, sourceValueEquality,
                          leftValueEquality, rightValueEquality, span⟩
                      rw [sourceValueEquality] at sourceInstantiation
                      rw [leftValueEquality] at leftInstantiation
                      exact ⟨left, sourceInstantiation, leftInstantiation,
                        derivesSpan_start_boundary span⟩
      | separator separator => simp [buildDAGSyntaxItems] at buildEquality
      | delimiter openToken closeToken =>
          simp [buildDAGSyntaxItems] at buildEquality
      | op operation => simp [buildDAGSyntaxItems] at buildEquality

private theorem dagProductionRule_some_components
    {rule : GrammarRule} {schema : RuleSchema}
    (generated : dagProductionRule rule = some schema) :
    ruleSupportedForInference rule = true ∧
      ∃ built,
        buildDAGSyntaxItems rule rule.syntaxPattern 0 = some built ∧
          schema = dagProductionSchema rule built := by
  by_cases supported : ruleSupportedForInference rule = true
  · refine ⟨supported, ?_⟩
    simp only [dagProductionRule, supported, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte] at generated
    cases buildEquality : buildDAGSyntaxItems rule rule.syntaxPattern 0 with
    | none => simp [buildEquality] at generated
    | some built =>
        simp [buildEquality] at generated
        exact ⟨built, rfl, generated.symm⟩
  · have unsupported : ruleSupportedForInference rule = false :=
      Bool.eq_false_of_not_eq_true supported
    simp [dagProductionRule, unsupported] at generated

private theorem dagProduction_application_meaning
    (language : LanguageDef) (ledger : SourceLedger)
    (rule : GrammarRule) (ruleMember : rule ∈ language.terms)
    (built : DAGSchemaBuild)
    (buildEquality :
      buildDAGSyntaxItems rule rule.syntaxPattern 0 = some built)
    {presentation : ValidatedPresentation}
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern}
    (application : RuleApplication presentation ruleInstance premises conclusion)
    (selected :
      presentation.1.lookupRule? ruleInstance.ruleId =
        some (dagProductionSchema rule built))
    (meanings : ∀ premise ∈ premises,
      DAGJudgmentMeaning language ledger premise) :
    DAGJudgmentMeaning language ledger conclusion := by
  cases application with
  | intro stored lookup argumentsValid sideConditionsValid premisesInstantiate conclusionInstantiates =>
      have storedEquality : stored = dagProductionSchema rule built := by
        rw [selected] at lookup
        exact (Option.some.inj lookup).symm
      subst stored
      change InstantiatesList (dagProductionMetavariables built)
        ruleInstance.arguments (dagProductionPremises rule built) premises
        at premisesInstantiate
      change Instantiates (dagProductionMetavariables built)
        ruleInstance.arguments (dagProductionConclusion rule built) conclusion
        at conclusionInstantiates
      unfold dagProductionConclusion at conclusionInstantiates
      rcases derivesNodeInstantiation_shape conclusionInstantiates with
        ⟨conclusionSource, conclusionLeft, conclusionRight,
          conclusionSourceInstantiation, conclusionLeftInstantiation,
          conclusionRightInstantiation, conclusionEquality⟩
      by_cases empty : rule.syntaxPattern = []
      · rw [empty] at buildEquality
        simp only [buildDAGSyntaxItems, Option.some.injEq] at buildEquality
        subst built
        simp [dagProductionPremises, empty] at premisesInstantiate
        change InstantiatesList
          (dagProductionMetavariables
            { premises := [], nextBoundary := 0 })
          ruleInstance.arguments
          [boundaryJudgment sourceVariable (boundaryVariable 0)] premises
          at premisesInstantiate
        cases premisesInstantiate with
        | cons boundaryInstantiation remainingInstantiation =>
            rename_i boundaryResult remainingResults
            cases remainingInstantiation with
            | nil =>
                rcases boundaryInstantiation_shape boundaryInstantiation with
                  ⟨boundarySource, boundaryValue,
                    boundarySourceInstantiation, boundaryValueInstantiation,
                    boundaryEquality⟩
                have boundaryMeaning : DAGJudgmentMeaning language ledger
                    (boundaryJudgment boundarySource boundaryValue) := by
                  rw [← boundaryEquality]
                  exact meanings _ (by simp)
                rcases dagBoundaryMeaning_inversion boundaryMeaning with
                  ⟨index, within, boundarySourceEquality,
                    boundaryValueEquality⟩
                have sourceAgreement : conclusionSource = boundarySource :=
                  InstantiatesAt.functional conclusionSourceInstantiation
                    boundarySourceInstantiation
                have leftAgreement : conclusionLeft = boundaryValue :=
                  InstantiatesAt.functional conclusionLeftInstantiation
                    boundaryValueInstantiation
                have rightAgreement : conclusionRight = boundaryValue :=
                  InstantiatesAt.functional conclusionRightInstantiation
                    boundaryValueInstantiation
                have sourceEquality : conclusionSource = sourcePattern ledger :=
                  sourceAgreement.trans boundarySourceEquality
                have leftEquality : conclusionLeft = boundaryPattern index :=
                  leftAgreement.trans boundaryValueEquality
                have rightEquality : conclusionRight = boundaryPattern index :=
                  rightAgreement.trans boundaryValueEquality
                rw [sourceEquality, leftEquality, rightEquality]
                  at conclusionEquality
                rw [conclusionEquality]
                rcases boundaryAt_of_le ledger index within with
                  ⟨before, after, source, beforeLength⟩
                apply DAGJudgmentMeaning.derives rule.category index index
                  (.apply rule.label [])
                have emptyItems :
                    DerivesItems language rule rule.syntaxPattern [] [] := by
                  rw [empty]
                  exact DerivesItems.nil rule
                exact
                  ⟨before, [], after, by simpa using source,
                    beforeLength.symm, by simp [beforeLength],
                    Derives.rule rule ruleMember rule.category rfl [] []
                      emptyItems⟩
      · have nonemptyPremisesInstantiation :
            InstantiatesList (dagProductionMetavariables built)
              ruleInstance.arguments built.premises premises := by
          simpa [dagProductionPremises, empty] using premisesInstantiate
        rcases buildDAGSyntaxItems_start language ledger rule
            (dagProductionMetavariables built) ruleInstance.arguments empty
            buildEquality nonemptyPremisesInstantiation meanings with
          ⟨left, sourceInstantiation, leftInstantiation, leftBoundary⟩
        rcases buildDAGSyntaxItems_semantic language ledger rule
            (dagProductionMetavariables built) ruleInstance.arguments
            rule.syntaxPattern 0 built premises left buildEquality
            nonemptyPremisesInstantiation meanings sourceInstantiation
            leftInstantiation leftBoundary with
          ⟨right, children, itemsSpan, rightInstantiation⟩
        have sourceEquality : conclusionSource = sourcePattern ledger :=
          InstantiatesAt.functional conclusionSourceInstantiation
            sourceInstantiation
        have leftEquality : conclusionLeft = boundaryPattern left :=
          InstantiatesAt.functional conclusionLeftInstantiation leftInstantiation
        have rightEquality : conclusionRight = boundaryPattern right :=
          InstantiatesAt.functional conclusionRightInstantiation rightInstantiation
        rw [sourceEquality, leftEquality, rightEquality] at conclusionEquality
        rw [conclusionEquality]
        rcases itemsSpan with
          ⟨before, parsed, after, source, leftIndex, rightIndex,
            itemsDerivation⟩
        apply DAGJudgmentMeaning.derives rule.category left right
          (.apply rule.label children)
        exact
          ⟨before, parsed, after, source, leftIndex, rightIndex,
            Derives.rule rule ruleMember rule.category rfl parsed children
              itemsDerivation⟩

private theorem dagBoundaryFact_application_meaning
    (language : LanguageDef) (ledger : SourceLedger)
    (index : Nat) (within : index ≤ ledger.tokens.length)
    {presentation : ValidatedPresentation}
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern}
    (application : RuleApplication presentation ruleInstance premises conclusion)
    (selected :
      presentation.1.lookupRule? ruleInstance.ruleId =
        some (boundaryFactRule ledger index)) :
    DAGJudgmentMeaning language ledger conclusion := by
  have conclusionEquality := groundConclusion_of_application application selected
    (by rfl) (instantiate_boundaryJudgment ledger index)
  rw [conclusionEquality]
  exact .boundary index within

private theorem dagTokenFact_application_meaning
    (language : LanguageDef) (ledger : SourceLedger)
    (before after : List String) (token : String)
    (source : ledger.tokens = before ++ token :: after)
    {presentation : ValidatedPresentation}
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern}
    (application : RuleApplication presentation ruleInstance premises conclusion)
    (selected :
      presentation.1.lookupRule? ruleInstance.ruleId =
        some (tokenFactRule ledger before.length token)) :
    DAGJudgmentMeaning language ledger conclusion := by
  have conclusionEquality := groundConclusion_of_application application selected
    (by rfl) (instantiate_tokenSpanJudgment ledger before.length token)
  rw [conclusionEquality]
  exact .token before after token source

/-- Every application admitted from the generated shared proof-DAG
presentation preserves the declarative grammar meaning. -/
theorem generated_dag_rule_application_meaning
    (language : LanguageDef) (ledger : SourceLedger)
    (valid : (rawDAGPresentation language ledger).isValidV2 = true)
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication
      (validatedRawDAGPresentation language ledger valid)
      ruleInstance premises conclusion)
    (premiseMeanings : ∀ premise ∈ premises,
      DAGJudgmentMeaning language ledger premise) :
    DAGJudgmentMeaning language ledger conclusion := by
  cases application with
  | intro stored lookup argumentsValid sideConditionsValid premisesInstantiate conclusionInstantiates =>
      have storedMember :
          stored ∈ boundaryFactRules ledger ++ tokenFactRules ledger ++
            dagGrammarRules language := by
        change stored ∈
          (validatedRawDAGPresentation language ledger valid).1.rules
        exact List.mem_of_find?_eq_some lookup
      rcases List.mem_append.mp storedMember with
        sourceFactMember | grammarMember
      · rcases List.mem_append.mp sourceFactMember with
          boundaryMember | tokenMember
        · rcases (boundaryFactRules_mem_iff ledger stored).mp boundaryMember with
            ⟨index, within, storedEquality⟩
          subst stored
          exact dagBoundaryFact_application_meaning language ledger index within
            (.intro _ lookup argumentsValid sideConditionsValid premisesInstantiate
              conclusionInstantiates)
            lookup
        · rcases (tokenFactRules_mem_iff ledger stored).mp tokenMember with
            ⟨before, token, after, source, storedEquality⟩
          subst stored
          exact dagTokenFact_application_meaning language ledger
            before after token source
            (.intro _ lookup argumentsValid sideConditionsValid premisesInstantiate
              conclusionInstantiates)
            lookup
      · rcases (dagGrammarRules_mem_iff language stored).mp grammarMember with
          ⟨rule, ruleMember, generated⟩
        rcases dagProductionRule_some_components generated with
          ⟨supported, built, buildEquality, storedEquality⟩
        subst stored
        exact dagProduction_application_meaning language ledger
          rule ruleMember built buildEquality
          (.intro _ lookup argumentsValid sideConditionsValid premisesInstantiate
            conclusionInstantiates)
          lookup premiseMeanings

/-- Type-valued derivations over the generated shared proof-DAG presentation
are semantically sound for the source-indexed grammar relation. -/
theorem generated_dag_derivation_sound
    (language : LanguageDef) (ledger : SourceLedger)
    (valid : (rawDAGPresentation language ledger).isValidV2 = true)
    {goal : Pattern}
    (derivation : Derivation
      (validatedRawDAGPresentation language ledger valid) goal) :
    DAGJudgmentMeaning language ledger goal :=
  derivation.sound_of_ruleApplications (DAGJudgmentMeaning language ledger)
    (generated_dag_rule_application_meaning language ledger valid)

/-- Any raw proof accepted for a shared proof-DAG whole-source goal
reconstructs an ordinary grammar derivation for the exact admitted tokens. -/
theorem checkedDAGProof_root_sound
    (language : LanguageDef) (ledger : SourceLedger)
    (valid : (rawDAGPresentation language ledger).isValidV2 = true)
    (sort : String)
    (proof : CheckedProof (validatedRawDAGPresentation language ledger valid)
      (dagRootJudgment ledger sort)) :
    ∃ tree, Derives language sort ledger.tokens tree := by
  rcases checkRaw_soundness proof.2 with ⟨derivation⟩
  exact (dagRootJudgment_has_meaning_iff language ledger sort).mp
    (generated_dag_derivation_sound language ledger valid derivation)

/-- Successful chronological block checking reconstructs a grammar derivation
for the exact admitted source.  Block boundaries are semantically inert. -/
theorem checkedDAGBlocks_root_sound
    (language : LanguageDef) (ledger : SourceLedger)
    (valid : (rawDAGPresentation language ledger).isValidV2 = true)
    (sort : String) (rootId : Nat) (blocks : List (List DAGNode))
    (checked : checkDAGBlocks
      (validatedRawDAGPresentation language ledger valid)
      (dagRootJudgment ledger sort) rootId blocks = true) :
    ∃ tree, Derives language sort ledger.tokens tree := by
  rcases checkDAGBlocks_sound checked with ⟨proof, proofAccepted⟩
  exact checkedDAGProof_root_sound language ledger valid sort
    ⟨proof, proofAccepted⟩

/-! ## Classified lexical leaves

The native grammar format admits literal-token declarations (`VarD`) and
lexical-class declarations (`LexD`) in addition to productions.  The first
matching declaration determines a one-token leaf sort.  Classified tokens
retain their exact serialized source atom together with the two observations
used by that deterministic lookup.
-/

inductive LexicalDeclaration where
  | literal (atomName sort : String)
  | lexicalClass (className sort : String)
deriving Repr, DecidableEq

structure ClassifiedToken where
  serialized : String
  literalName : Option String
  className : String
deriving Repr, DecidableEq

def lexicalDeclarationSort?
    (declaration : LexicalDeclaration) (token : ClassifiedToken) :
    Option String :=
  match declaration with
  | .literal atomName sort =>
      if token.literalName = some atomName then some sort else none
  | .lexicalClass className sort =>
      if token.className = className then some sort else none

/-- First-match lexical classification, in admitted grammar-entry order. -/
def lexicalSort? : List LexicalDeclaration → ClassifiedToken → Option String
  | [], _ => none
  | declaration :: declarations, token =>
      match lexicalDeclarationSort? declaration token with
      | some sort => some sort
      | none => lexicalSort? declarations token

structure ClassifiedSource where
  identity : String
  tokens : List ClassifiedToken
deriving Repr, DecidableEq

def ClassifiedSource.ledger (source : ClassifiedSource) : SourceLedger :=
  { identity := source.identity
    tokens := source.tokens.map ClassifiedToken.serialized }

def ClassifiedSource.isValid (source : ClassifiedSource) : Bool :=
  source.ledger.isValid &&
    source.tokens.all fun token => token.serialized != ""

def lexicalRuleLabel
    (source : ClassifiedSource) (index : Nat) : String :=
  reservedPrefix ++ "lexical-leaf." ++ source.identity ++ "." ++ index.repr

def lexicalGrammarRule
    (source : ClassifiedSource) (index : Nat)
    (token : ClassifiedToken) (sort : String) : GrammarRule :=
  { label := lexicalRuleLabel source index
    category := sort
    params := []
    syntaxPattern := [.terminal token.serialized] }

def lexicalGrammarRulesFrom
    (declarations : List LexicalDeclaration) (source : ClassifiedSource) :
    List ClassifiedToken → Nat → List GrammarRule
  | [], _ => []
  | token :: tokens, index =>
      match lexicalSort? declarations token with
      | none => lexicalGrammarRulesFrom declarations source tokens (index + 1)
      | some sort =>
          lexicalGrammarRule source index token sort ::
            lexicalGrammarRulesFrom declarations source tokens (index + 1)

def lexicalGrammarRules
    (declarations : List LexicalDeclaration) (source : ClassifiedSource) :
    List GrammarRule :=
  lexicalGrammarRulesFrom declarations source source.tokens 0

/-- Add exactly the derived lexical leaf rules to the production grammar. -/
def lexicalizedLanguage (language : LanguageDef)
    (declarations : List LexicalDeclaration)
    (source : ClassifiedSource) : LanguageDef :=
  { language with
    terms := lexicalGrammarRules declarations source ++ language.terms }

private theorem baseRule_mem_lexicalizedLanguage
    {language : LanguageDef} {declarations : List LexicalDeclaration}
    {source : ClassifiedSource} {rule : GrammarRule}
    (membership : rule ∈ language.terms) :
    rule ∈ (lexicalizedLanguage language declarations source).terms := by
  simp [lexicalizedLanguage, membership]

private def lexicalFactRule (source : ClassifiedSource)
    (index : Nat) (sort : String) : RuleSchema :=
  { id := namespacedId "leaf" (source.identity ++ ":" ++ index.repr)
    metavariables := []
    premises := []
    conclusion :=
      derivesNodeJudgment (sourcePattern source.ledger) (sortPattern sort)
        (boundaryPattern index) (boundaryPattern (index + 1)) }

private def lexicalFactRulesFrom
    (declarations : List LexicalDeclaration) (source : ClassifiedSource) :
    List ClassifiedToken → Nat → List RuleSchema
  | [], _ => []
  | token :: tokens, index =>
      match lexicalSort? declarations token with
      | none => lexicalFactRulesFrom declarations source tokens (index + 1)
      | some sort =>
          lexicalFactRule source index sort ::
            lexicalFactRulesFrom declarations source tokens (index + 1)

private def lexicalFactRules
    (declarations : List LexicalDeclaration) (source : ClassifiedSource) :
    List RuleSchema :=
  lexicalFactRulesFrom declarations source source.tokens 0

private def rawLexicalDAGPresentation (language : LanguageDef)
    (declarations : List LexicalDeclaration)
    (source : ClassifiedSource) : Presentation :=
  { language := encodedLanguage language source.ledger
    calculus :=
      { judgments :=
          [{ head := boundaryJudgmentHead, arity := 2 },
           { head := tokenSpanJudgmentHead, arity := 4 },
           { head := derivesNodeJudgmentHead, arity := 4 }]
        rules :=
          boundaryFactRules source.ledger ++ tokenFactRules source.ledger ++
            lexicalFactRules declarations source ++ dagGrammarRules language } }

/-- Generate the compact presentation including deterministic `VarD`/`LexD`
leaf rules. -/
def generateLexicalDAGPresentation (language : LanguageDef)
    (declarations : List LexicalDeclaration)
    (source : ClassifiedSource) : Option Presentation :=
  if grammarSupportedForInference language && source.isValid then
    some (rawLexicalDAGPresentation language declarations source)
  else
    none

/-- Generate and validate the compact presentation whose leaf rules are
determined by the ordered lexical declarations. -/
def admitLexicalDAGPresentation (language : LanguageDef)
    (declarations : List LexicalDeclaration)
    (source : ClassifiedSource) : Option ValidatedPresentation := do
  let presentation ← generateLexicalDAGPresentation language declarations source
  presentation.validateV2?

private def validatedRawLexicalDAGPresentation
    (language : LanguageDef) (declarations : List LexicalDeclaration)
    (source : ClassifiedSource)
    (valid :
      (rawLexicalDAGPresentation language declarations source).isValidV2 = true) :
    ValidatedPresentation :=
  ⟨rawLexicalDAGPresentation language declarations source, valid⟩

private theorem admittedLexicalDAGPresentation_is_generated
    (language : LanguageDef) (declarations : List LexicalDeclaration)
    (source : ClassifiedSource) (presentation : ValidatedPresentation)
    (admitted :
      admitLexicalDAGPresentation language declarations source =
        some presentation) :
    ∃ valid :
        (rawLexicalDAGPresentation language declarations source).isValidV2 =
          true,
      presentation =
        validatedRawLexicalDAGPresentation language declarations source valid := by
  cases generated : generateLexicalDAGPresentation language declarations source with
  | none =>
      simp [admitLexicalDAGPresentation, generated] at admitted
  | some raw =>
      by_cases valid : raw.isValidV2 = true
      · have admittedValue :
            (⟨raw, valid⟩ : ValidatedPresentation) = presentation := by
          apply Option.some.inj
          simpa [admitLexicalDAGPresentation, generated,
            Presentation.validateV2?, valid] using admitted
        have rawEquality :
            raw = rawLexicalDAGPresentation language declarations source := by
          unfold generateLexicalDAGPresentation at generated
          split at generated
          next supported => exact (Option.some.inj generated).symm
          next unsupported => simp at generated
        subst raw
        exact ⟨valid, admittedValue.symm⟩
      · simp [admitLexicalDAGPresentation, generated,
          Presentation.validateV2?, valid] at admitted

private theorem lexicalFactRulesFrom_mem
    (declarations : List LexicalDeclaration) (source : ClassifiedSource) :
    ∀ (tokens : List ClassifiedToken) (start : Nat) (schema : RuleSchema),
      schema ∈ lexicalFactRulesFrom declarations source tokens start →
        ∃ before token after sort,
          tokens = before ++ token :: after ∧
            lexicalSort? declarations token = some sort ∧
            schema = lexicalFactRule source (start + before.length) sort
  | [], _, _, membership => by
      simp [lexicalFactRulesFrom] at membership
  | token :: tokens, start, schema, membership => by
      cases classified : lexicalSort? declarations token with
      | none =>
          simp only [lexicalFactRulesFrom, classified] at membership
          rcases lexicalFactRulesFrom_mem declarations source tokens
              (start + 1) schema membership with
            ⟨before, value, after, sort, decomposition,
              valueClassified, schemaEquality⟩
          refine ⟨token :: before, value, after, sort, ?_,
            valueClassified, ?_⟩
          · simp [decomposition]
          · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
              schemaEquality
      | some headSort =>
          simp only [lexicalFactRulesFrom, classified, List.mem_cons]
            at membership
          rcases membership with equality | membership
          · subst schema
            exact ⟨[], token, tokens, headSort, by simp, classified, by simp⟩
          · rcases lexicalFactRulesFrom_mem declarations source tokens
                (start + 1) schema membership with
              ⟨before, value, after, sort, decomposition,
                valueClassified, schemaEquality⟩
            refine ⟨token :: before, value, after, sort, ?_,
              valueClassified, ?_⟩
            · simp [decomposition]
            · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                schemaEquality

private theorem lexicalFactRules_mem
    (declarations : List LexicalDeclaration) (source : ClassifiedSource)
    (schema : RuleSchema)
    (membership : schema ∈ lexicalFactRules declarations source) :
    ∃ before token after sort,
      source.tokens = before ++ token :: after ∧
        lexicalSort? declarations token = some sort ∧
        schema = lexicalFactRule source before.length sort := by
  rcases lexicalFactRulesFrom_mem declarations source source.tokens 0 schema
      (by simpa [lexicalFactRules] using membership) with
    ⟨before, token, after, sort, decomposition,
      classified, schemaEquality⟩
  exact ⟨before, token, after, sort, decomposition, classified,
    by simpa using schemaEquality⟩

private theorem lexicalGrammarRule_mem_from
    (declarations : List LexicalDeclaration) (source : ClassifiedSource) :
    ∀ (before : List ClassifiedToken) (token : ClassifiedToken)
      (after : List ClassifiedToken) (start : Nat) (sort : String),
      lexicalSort? declarations token = some sort →
        lexicalGrammarRule source (start + before.length) token sort ∈
          lexicalGrammarRulesFrom declarations source
            (before ++ token :: after) start
  | [], token, after, start, sort, classified => by
      simp [lexicalGrammarRulesFrom, classified]
  | head :: before, token, after, start, sort, classified => by
      cases headClassified : lexicalSort? declarations head with
      | none =>
          simp only [List.cons_append, lexicalGrammarRulesFrom,
            headClassified]
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            lexicalGrammarRule_mem_from declarations source before token after
              (start + 1) sort classified
      | some headSort =>
          simp only [List.cons_append, lexicalGrammarRulesFrom,
            headClassified, List.mem_cons]
          apply Or.inr
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            lexicalGrammarRule_mem_from declarations source before token after
              (start + 1) sort classified

private theorem lexicalGrammarRule_mem
    (declarations : List LexicalDeclaration) (source : ClassifiedSource)
    (before : List ClassifiedToken) (token : ClassifiedToken)
    (after : List ClassifiedToken) (sort : String)
    (decomposition : source.tokens = before ++ token :: after)
    (classified : lexicalSort? declarations token = some sort) :
    lexicalGrammarRule source before.length token sort ∈
      lexicalGrammarRules declarations source := by
  unfold lexicalGrammarRules
  rw [decomposition]
  simpa using lexicalGrammarRule_mem_from declarations source
    before token after 0 sort classified

private theorem instantiate_lexicalFactConclusion
    (source : ClassifiedSource) (index : Nat) (sort : String) :
    instantiateSchemaAt? [] [] 0 (lexicalFactRule source index sort).conclusion =
      some (lexicalFactRule source index sort).conclusion := by
  simp [lexicalFactRule, derivesNodeJudgment, sourcePattern, sortPattern,
    boundaryPattern, literalPattern, instantiateSchemaAt?,
    instantiateSchemasAt?]

private theorem lexicalFact_application_meaning
    (language : LanguageDef) (declarations : List LexicalDeclaration)
    (source : ClassifiedSource)
    (before : List ClassifiedToken) (token : ClassifiedToken)
    (after : List ClassifiedToken) (sort : String)
    (decomposition : source.tokens = before ++ token :: after)
    (classified : lexicalSort? declarations token = some sort)
    {presentation : ValidatedPresentation}
    {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern}
    (application : RuleApplication presentation ruleInstance premises conclusion)
    (selected :
      presentation.1.lookupRule? ruleInstance.ruleId =
        some (lexicalFactRule source before.length sort)) :
    DAGJudgmentMeaning (lexicalizedLanguage language declarations source)
      source.ledger conclusion := by
  have conclusionEquality := groundConclusion_of_application application selected
    (by rfl) (instantiate_lexicalFactConclusion source before.length sort)
  rw [conclusionEquality]
  let rule := lexicalGrammarRule source before.length token sort
  have lexicalMember :
      rule ∈ lexicalGrammarRules declarations source := by
    exact lexicalGrammarRule_mem declarations source before token after sort
      decomposition classified
  have ruleMember :
      rule ∈ (lexicalizedLanguage language declarations source).terms := by
    simp [lexicalizedLanguage, lexicalMember]
  have ledgerDecomposition :
      source.ledger.tokens =
        before.map ClassifiedToken.serialized ++ [token.serialized] ++
          after.map ClassifiedToken.serialized := by
    simp [ClassifiedSource.ledger, decomposition]
  apply DAGJudgmentMeaning.derives sort before.length (before.length + 1)
    (.apply rule.label [])
  refine ⟨before.map ClassifiedToken.serialized, [token.serialized],
    after.map ClassifiedToken.serialized, ledgerDecomposition, ?_, ?_, ?_⟩
  · simp
  · simp
  · apply Derives.rule rule ruleMember sort rfl [token.serialized] []
    exact DerivesItems.terminal rule token.serialized [] [] []
      (DerivesItems.nil rule)

/-- Every rule application in the classified lexical presentation preserves
the ordinary grammar meaning of the lexicalized language. -/
theorem generated_lexical_dag_rule_application_meaning
    (language : LanguageDef) (declarations : List LexicalDeclaration)
    (source : ClassifiedSource)
    (valid :
      (rawLexicalDAGPresentation language declarations source).isValidV2 = true)
    (ruleInstance : RuleInstance) (premises : List Pattern)
    (conclusion : Pattern)
    (application : RuleApplication
      (validatedRawLexicalDAGPresentation language declarations source valid)
      ruleInstance premises conclusion)
    (premiseMeanings : ∀ premise ∈ premises,
      DAGJudgmentMeaning (lexicalizedLanguage language declarations source)
        source.ledger premise) :
    DAGJudgmentMeaning (lexicalizedLanguage language declarations source)
      source.ledger conclusion := by
  cases application with
  | intro stored lookup argumentsValid sideConditionsValid premisesInstantiate conclusionInstantiates =>
      have storedMember :
          stored ∈
            ((boundaryFactRules source.ledger ++ tokenFactRules source.ledger) ++
              lexicalFactRules declarations source) ++
                dagGrammarRules language := by
        change stored ∈
          (validatedRawLexicalDAGPresentation
            language declarations source valid).1.rules
        exact List.mem_of_find?_eq_some lookup
      rcases List.mem_append.mp storedMember with
        admittedFactMember | grammarMember
      · rcases List.mem_append.mp admittedFactMember with
          sourceFactMember | lexicalMember
        · rcases List.mem_append.mp sourceFactMember with
            boundaryMember | tokenMember
          · rcases (boundaryFactRules_mem_iff source.ledger stored).mp
                boundaryMember with
              ⟨index, within, storedEquality⟩
            subst stored
            exact dagBoundaryFact_application_meaning
              (lexicalizedLanguage language declarations source) source.ledger
              index within
              (.intro _ lookup argumentsValid sideConditionsValid premisesInstantiate
                conclusionInstantiates)
              lookup
          · rcases (tokenFactRules_mem_iff source.ledger stored).mp
                tokenMember with
              ⟨before, token, after, tokenSource, storedEquality⟩
            subst stored
            exact dagTokenFact_application_meaning
              (lexicalizedLanguage language declarations source) source.ledger
              before after token tokenSource
              (.intro _ lookup argumentsValid sideConditionsValid premisesInstantiate
                conclusionInstantiates)
              lookup
        · rcases lexicalFactRules_mem declarations source stored lexicalMember with
            ⟨before, token, after, sort, decomposition,
              classified, storedEquality⟩
          subst stored
          exact lexicalFact_application_meaning language declarations source
            before token after sort decomposition classified
            (.intro _ lookup argumentsValid sideConditionsValid premisesInstantiate
              conclusionInstantiates)
            lookup
      · rcases (dagGrammarRules_mem_iff language stored).mp grammarMember with
          ⟨rule, baseRuleMember, generated⟩
        rcases dagProductionRule_some_components generated with
          ⟨supported, built, buildEquality, storedEquality⟩
        subst stored
        exact dagProduction_application_meaning
          (lexicalizedLanguage language declarations source) source.ledger
          rule (baseRule_mem_lexicalizedLanguage baseRuleMember)
          built buildEquality
          (.intro _ lookup argumentsValid sideConditionsValid premisesInstantiate
            conclusionInstantiates)
          lookup premiseMeanings

theorem generated_lexical_dag_derivation_sound
    (language : LanguageDef) (declarations : List LexicalDeclaration)
    (source : ClassifiedSource)
    (valid :
      (rawLexicalDAGPresentation language declarations source).isValidV2 = true)
    {goal : Pattern}
    (derivation : Derivation
      (validatedRawLexicalDAGPresentation language declarations source valid)
      goal) :
    DAGJudgmentMeaning (lexicalizedLanguage language declarations source)
      source.ledger goal :=
  derivation.sound_of_ruleApplications
    (DAGJudgmentMeaning
      (lexicalizedLanguage language declarations source) source.ledger)
    (generated_lexical_dag_rule_application_meaning
      language declarations source valid)

/-- Accepted classified proof-DAG blocks reconstruct an ordinary grammar
derivation in the language extended only by the derived lexical leaf rules. -/
theorem checkedLexicalDAGBlocks_root_sound
    (language : LanguageDef) (declarations : List LexicalDeclaration)
    (source : ClassifiedSource)
    (valid :
      (rawLexicalDAGPresentation language declarations source).isValidV2 = true)
    (sort : String) (rootId : Nat) (blocks : List (List DAGNode))
    (checked : checkDAGBlocks
      (validatedRawLexicalDAGPresentation language declarations source valid)
      (dagRootJudgment source.ledger sort) rootId blocks = true) :
    ∃ tree,
      Derives (lexicalizedLanguage language declarations source)
        sort source.ledger.tokens tree := by
  rcases checkDAGBlocks_sound checked with ⟨proof, proofAccepted⟩
  rcases checkRaw_soundness proofAccepted with ⟨derivation⟩
  exact (dagRootJudgment_has_meaning_iff
    (lexicalizedLanguage language declarations source)
    source.ledger sort).mp
      (generated_lexical_dag_derivation_sound
        language declarations source valid derivation)

/-- Compact checking retains the exact reconstructed raw proof as well as its
typed derivation and grammar meaning. -/
theorem checkedLexicalDAGBlocks_root_exact
    (language : LanguageDef) (declarations : List LexicalDeclaration)
    (source : ClassifiedSource)
    (valid :
      (rawLexicalDAGPresentation language declarations source).isValidV2 = true)
    (sort : String) (rootId : Nat) (blocks : List (List DAGNode))
    (checked : checkDAGBlocks
      (validatedRawLexicalDAGPresentation language declarations source valid)
      (dagRootJudgment source.ledger sort) rootId blocks = true) :
    ∃ (proof : RawProof)
        (derivation : Derivation
          (validatedRawLexicalDAGPresentation language declarations source valid)
          (dagRootJudgment source.ledger sort))
        (tree : Pattern),
      expandDAGBlocks?
          (validatedRawLexicalDAGPresentation language declarations source valid)
          (dagRootJudgment source.ledger sort) rootId blocks = some proof ∧
        derivation.erase = proof ∧
        Derives (lexicalizedLanguage language declarations source)
          sort source.ledger.tokens tree := by
  rcases checkDAGBlocks_exact_derivation checked with
    ⟨proof, derivation, expanded, erased⟩
  rcases (dagRootJudgment_has_meaning_iff
      (lexicalizedLanguage language declarations source)
      source.ledger sort).mp
      (generated_lexical_dag_derivation_sound
        language declarations source valid derivation) with
    ⟨tree, treeDerivation⟩
  exact ⟨proof, derivation, tree, expanded, erased, treeDerivation⟩

/-- The public classified-source admission boundary preserves the same
whole-source guarantee: accepted chronological DAG blocks reconstruct an
ordinary grammar derivation for the exact admitted token sequence. -/
theorem admittedLexicalDAGBlocks_root_sound
    (language : LanguageDef) (declarations : List LexicalDeclaration)
    (source : ClassifiedSource)
    (presentation : ValidatedPresentation)
    (admitted :
      admitLexicalDAGPresentation language declarations source =
        some presentation)
    (sort : String) (rootId : Nat) (blocks : List (List DAGNode))
    (checked : checkDAGBlocks presentation
      (dagRootJudgment source.ledger sort) rootId blocks = true) :
    ∃ tree,
      Derives (lexicalizedLanguage language declarations source)
        sort source.ledger.tokens tree := by
  rcases admittedLexicalDAGPresentation_is_generated
      language declarations source presentation admitted with
    ⟨valid, presentationEquality⟩
  subst presentation
  exact checkedLexicalDAGBlocks_root_sound
    language declarations source valid sort rootId blocks checked

/-- Public exact-erasure form of classified source admission. -/
theorem admittedLexicalDAGBlocks_root_exact
    (language : LanguageDef) (declarations : List LexicalDeclaration)
    (source : ClassifiedSource)
    (presentation : ValidatedPresentation)
    (admitted :
      admitLexicalDAGPresentation language declarations source =
        some presentation)
    (sort : String) (rootId : Nat) (blocks : List (List DAGNode))
    (checked : checkDAGBlocks presentation
      (dagRootJudgment source.ledger sort) rootId blocks = true) :
    ∃ (proof : RawProof)
        (derivation : Derivation presentation
          (dagRootJudgment source.ledger sort))
        (tree : Pattern),
      expandDAGBlocks? presentation (dagRootJudgment source.ledger sort)
          rootId blocks = some proof ∧
        derivation.erase = proof ∧
        Derives (lexicalizedLanguage language declarations source)
          sort source.ledger.tokens tree := by
  rcases admittedLexicalDAGPresentation_is_generated
      language declarations source presentation admitted with
    ⟨valid, presentationEquality⟩
  subst presentation
  exact checkedLexicalDAGBlocks_root_exact
    language declarations source valid sort rootId blocks checked

/-! ## Executable boundary fixtures -/

private def exprType : TypeDecl := TypeDecl.plain "Expr"

private def zeroRule : GrammarRule :=
  { label := "Zero"
    category := "Expr"
    params := []
    syntaxPattern := [.terminal "0"] }

private def parenRule : GrammarRule :=
  { label := "Paren"
    category := "Expr"
    params := [.simple "body" (.base "Expr")]
    syntaxPattern := [.terminal "(", .nonTerminal "body", .terminal ")"] }

private def exprLanguage : LanguageDef :=
  { name := "grammar-inference-fixture"
    types := [exprType]
    terms := [zeroRule, parenRule]
    equations := []
    rewrites := [] }

/-! ### Classified lexical boundary fixtures -/

private def lexicalPrecedenceToken : ClassifiedToken :=
  { serialized := "alpha"
    literalName := some "alpha"
    className := "identifier" }

private def literalFirstDeclarations : List LexicalDeclaration :=
  [.literal "alpha" "LiteralExpr",
   .lexicalClass "identifier" "ClassExpr"]

private def classFirstDeclarations : List LexicalDeclaration :=
  [.lexicalClass "identifier" "ClassExpr",
   .literal "alpha" "LiteralExpr"]

theorem lexical_literal_first_precedence :
    lexicalSort? literalFirstDeclarations lexicalPrecedenceToken =
      some "LiteralExpr" := by
  decide

theorem lexical_class_first_precedence :
    lexicalSort? classFirstDeclarations lexicalPrecedenceToken =
      some "ClassExpr" := by
  decide

theorem lexical_unmatched_token_rejects :
    lexicalSort? [.literal "beta" "Expr",
      .lexicalClass "number" "Expr"] lexicalPrecedenceToken = none := by
  decide

private def lexicalFixtureDeclarations : List LexicalDeclaration :=
  [.lexicalClass "identifier" "Expr"]

private def lexicalFixtureLanguage : LanguageDef :=
  { name := "grammar-inference-lexical-fixture"
    types := [exprType]
    terms := [zeroRule]
    equations := []
    rewrites := [] }

private def lexicalFixtureSource : ClassifiedSource :=
  { identity := "fixture-lexical"
    tokens :=
      [{ serialized := "alpha"
         literalName := some "alpha"
         className := "identifier" }] }

theorem lexical_fixture_generates :
    generateLexicalDAGPresentation lexicalFixtureLanguage
      lexicalFixtureDeclarations lexicalFixtureSource =
        some (rawLexicalDAGPresentation lexicalFixtureLanguage
          lexicalFixtureDeclarations lexicalFixtureSource) := by
  rfl

private def invalidLexicalFixtureSource : ClassifiedSource :=
  { identity := "fixture-invalid-lexical"
    tokens :=
      [{ serialized := ""
         literalName := none
         className := "identifier" }] }

theorem lexical_empty_serialization_rejects :
    generateLexicalDAGPresentation lexicalFixtureLanguage
      lexicalFixtureDeclarations invalidLexicalFixtureSource = none := by
  decide

private def zeroLedger : SourceLedger :=
  { identity := "fixture-zero", tokens := ["0"] }

private theorem string_eraseDups_nodup :
    (values : List String) → values.eraseDups.Nodup
  | [] => by simp
  | value :: values => by
      rw [List.eraseDups_cons]
      constructor
      · intro candidate membership equality
        subst candidate
        have filteredMembership :
            value ∈ List.filter (fun candidate => !candidate == value) values :=
          List.mem_eraseDups.mp membership
        simp at filteredMembership
      · exact string_eraseDups_nodup _
termination_by values => values.length
decreasing_by
  simpa using Nat.lt_succ_of_le
    (List.length_filter_le (fun candidate => !candidate == value) values)

private theorem literalLabels_nodup
    (language : LanguageDef) (ledger : SourceLedger) :
    (literalLabels language ledger).Nodup := by
  unfold literalLabels
  exact string_eraseDups_nodup _

private theorem zeroLiteralLabels_eq :
    literalLabels exprLanguage zeroLedger =
      [literalLabel "source" "fixture-zero",
       literalLabel "boundary" "0", literalLabel "boundary" "1",
       literalLabel "token" "0",
       literalLabel "token" "(", literalLabel "token" ")",
       literalLabel "sort" "Expr"] := by
  simp [literalLabels, terminalNames, parameterSortNames, exprLanguage,
    zeroRule, parenRule, zeroLedger, literalLabel, reservedPrefix]
  decide

private theorem zeroEncodedLanguage_validate :
    (encodedLanguage exprLanguage zeroLedger).validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly
  · rfl
  · rfl
  · simp [encodedLanguage, exprLanguage, exprType, dataTypeName,
      reservedPrefix, LanguageDef.typeNames, TypeDecl.plain]
  · simp only [encodedLanguage, List.map_append, List.map_map]
    rw [zeroLiteralLabels_eq]
    simp [exprLanguage, zeroRule, parenRule, checkerConstructorDecl,
      dataTerm, literalLabel, reservedPrefix]
  · simp [encodedLanguage, checkerConstructorDecl, dataTerm,
      exprLanguage, exprType, zeroRule, parenRule, dataTypeName,
      LanguageDef.typeNames, TypeDecl.plain]
  · simp [encodedLanguage, checkerConstructorDecl, dataTerm,
      exprLanguage, exprType, zeroRule, parenRule, dataTypeName,
      LanguageDef.typeNames, TypeDecl.plain, TermParam.typeExpr,
      TypeExpr.baseNames]
  · simp [encodedLanguage, checkerConstructorDecl, dataTerm,
      exprLanguage, zeroRule, parenRule]

example : grammarSupportedForInference exprLanguage = true := by decide
example : zeroLedger.isValid = true := by decide
example : (generate? exprLanguage zeroLedger).isSome = true := by decide

private theorem index_lt_two (index : Nat) (hindex : index < 2) :
    index = 0 ∨ index = 1 := by omega

private theorem index_lt_four (index : Nat) (hindex : index < 4) :
    index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 := by omega

private theorem repr_zero : Nat.repr 0 = "0" := by decide
private theorem repr_one : Nat.repr 1 = "1" := by decide

private theorem zeroBoundaryRuleValidV1 (index : Nat) (hindex : index < 2) :
    RuleSchema.isValidV1 (boundaryFactRule zeroLedger index) = true := by
  rcases index_lt_two index hindex with rfl | rfl <;>
    simp [boundaryFactRule, RuleSchema.isValidV1,
      RuleSchema.metavariableNames, RuleSchema.occurrences,
      RuleSchema.patterns, patternMetavariableOccurrencesAt,
      patternsMetavariableOccurrencesAt, Pattern.isWellScoped,
      Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
      patternHasNoCollectionRest, patternsHaveNoCollectionRest,
      Pattern.hasCanonicalBinderMetadata,
      Pattern.hasCanonicalBinderMetadataList, boundaryJudgment,
      sourcePattern, zeroLedger, boundaryPattern, literalPattern,
      literalLabel, namespacedId, reservedPrefix]

private theorem zeroTokenRuleValidV1 :
    RuleSchema.isValidV1 (tokenFactRule zeroLedger 0 "0") = true := by
  simp [tokenFactRule, RuleSchema.isValidV1,
    RuleSchema.metavariableNames, RuleSchema.occurrences,
    RuleSchema.patterns, patternMetavariableOccurrencesAt,
    patternsMetavariableOccurrencesAt, Pattern.isWellScoped,
    Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, tokenSpanJudgment,
    sourcePattern, zeroLedger, boundaryPattern, tokenPattern,
    literalPattern, literalLabel, namespacedId, reservedPrefix]

private theorem zeroRulesValidV1 :
    (rawPresentation exprLanguage zeroLedger).rules.all
      RuleSchema.isValidV1 = true := by
  simp only [Presentation.rules, rawPresentation, List.all_append,
    Bool.and_eq_true]
  constructor
  · constructor
    · change ([0, 1] : List Nat).all
        (RuleSchema.isValidV1 ∘ boundaryFactRule zeroLedger) = true
      simp [zeroBoundaryRuleValidV1]
    · change [tokenFactRule zeroLedger 0 "0"].all
        RuleSchema.isValidV1 = true
      simp [zeroTokenRuleValidV1]
  · simp [grammarRules,
      productionRule?, productionSchema, productionMetavariables,
      productionPremises, productionConclusion, buildSyntaxItems,
      ruleSupportedForInference, simpleParameter?, syntaxItemSupported,
      nonTerminalNames, paramSort?, TermParam.bodyName,
      RuleSchema.isValidV1,
      RuleSchema.metavariableNames, RuleSchema.occurrences,
      RuleSchema.patterns, patternMetavariableOccurrencesAt,
      patternsMetavariableOccurrencesAt, Pattern.isWellScoped,
      Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
      patternHasNoCollectionRest, patternsHaveNoCollectionRest,
      Pattern.hasCanonicalBinderMetadata,
      Pattern.hasCanonicalBinderMetadataList, boundaryJudgment,
      tokenSpanJudgment, derivesJudgment, sourceVariable,
      sortPattern, tokenPattern, literalPattern,
      boundaryVariable, treeVariable, literalLabel, namespacedId,
      exprLanguage, zeroRule, parenRule, reservedPrefix]
    constructor
    · constructor
      · decide
      · intro index hindex
        rcases index_lt_two index (by omega) with rfl | rfl <;> simp
    · have hbody : ["body"].eraseDups.length = 1 := by decide
      simp [hbody, patternMetavariableOccurrencesAt,
        patternsMetavariableOccurrencesAt, Pattern.isWellScoped,
        Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
        patternHasNoCollectionRest, patternsHaveNoCollectionRest,
        Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
      constructor
      · have hzero : ∃ index, index < 4 ∧ index.repr = Nat.repr 0 :=
          ⟨0, by omega, rfl⟩
        have hone : ∃ index, index < 4 ∧ index.repr = Nat.repr 1 :=
          ⟨1, by omega, rfl⟩
        have htwo : ∃ index, index < 4 ∧ index.repr = Nat.repr 2 :=
          ⟨2, by omega, rfl⟩
        have hthree : ∃ index, index < 4 ∧ index.repr = Nat.repr 3 :=
          ⟨3, by omega, rfl⟩
        simp [hzero, hone, htwo, hthree]
        decide
      · intro index hindex
        rcases index_lt_four index hindex with
          rfl | rfl | rfl | rfl <;> simp

private theorem zeroRuleIdsUnique :
    (rawPresentation exprLanguage zeroLedger).ruleIds.eraseDups.length =
      (rawPresentation exprLanguage zeroLedger).ruleIds.length := by decide

private theorem zeroJudgmentSignatureValid :
    (rawPresentation exprLanguage zeroLedger).judgmentSignatureValid = true := by
  decide

private theorem zeroRulesValidIn :
    (rawPresentation exprLanguage zeroLedger).rules.all
      (RuleSchema.isValidIn (rawPresentation exprLanguage zeroLedger)) = true := by
  apply List.all_eq_true.mpr
  intro rule hrule
  have hv1 : RuleSchema.isValidV1 rule = true :=
    (List.all_eq_true.mp zeroRulesValidV1) rule hrule
  simp [RuleSchema.isValidIn, hv1]
  simp [rawPresentation, boundaryFactRules, tokenFactRules,
    tokenFactRulesFrom, grammarRules, productionRule?, productionSchema,
    productionMetavariables, productionPremises, productionConclusion,
    buildSyntaxItems, ruleSupportedForInference, simpleParameter?,
    syntaxItemSupported, nonTerminalNames, paramSort?, TermParam.bodyName,
    exprLanguage, zeroRule, parenRule, zeroLedger] at hrule
  rcases hrule with ⟨index, hindex, rfl⟩ | rfl | rfl | ⟨hbody, rfl⟩
  · rcases index_lt_two index (by omega) with rfl | rfl <;>
      simp [RuleSchema.patterns, boundaryFactRule, rawPresentation,
        Presentation.judgmentSchemaValid, Presentation.lookupJudgment?,
        fixedConstructorListsValid, fixedConstructorsValid,
        languageHasConstructorArity, encodedLanguage,
        zeroLiteralLabels_eq, dataTerm, literalLabel,
        boundaryJudgment, sourcePattern, boundaryPattern, literalPattern,
        TypeDecl.plain, dataTypeName, reservedPrefix, repr_zero,
        repr_one] <;>
      simp [exprLanguage, exprType, zeroRule, parenRule,
        checkerConstructorDecl, TypeDecl.plain]
  · simp [RuleSchema.patterns, tokenFactRule, rawPresentation,
      Presentation.judgmentSchemaValid, Presentation.lookupJudgment?,
      fixedConstructorListsValid, fixedConstructorsValid,
      languageHasConstructorArity, encodedLanguage,
      zeroLiteralLabels_eq, dataTerm, literalLabel,
      tokenSpanJudgment, sourcePattern, boundaryPattern, tokenPattern,
      literalPattern, TypeDecl.plain, dataTypeName, reservedPrefix,
      repr_zero, repr_one] ;
    simp [exprLanguage, exprType, zeroRule, parenRule,
      checkerConstructorDecl, TypeDecl.plain]
  · simp [RuleSchema.patterns, rawPresentation,
      Presentation.judgmentSchemaValid, Presentation.lookupJudgment?,
      fixedConstructorListsValid, fixedConstructorsValid,
      languageHasConstructorArity, encodedLanguage,
      zeroLiteralLabels_eq, dataTerm, literalLabel,
      tokenSpanJudgment, derivesJudgment, sourceVariable,
      sortPattern, tokenPattern, literalPattern,
      boundaryVariable, TypeDecl.plain, dataTypeName, reservedPrefix] ;
    simp [exprLanguage, exprType, zeroRule, parenRule,
      checkerConstructorDecl, TypeDecl.plain]
  · simp [RuleSchema.patterns, rawPresentation,
      Presentation.judgmentSchemaValid, Presentation.lookupJudgment?,
      fixedConstructorListsValid, fixedConstructorsValid,
      languageHasConstructorArity, encodedLanguage,
      zeroLiteralLabels_eq, dataTerm, literalLabel,
      tokenSpanJudgment, derivesJudgment, sourceVariable,
      sortPattern, tokenPattern, literalPattern,
      boundaryVariable, treeVariable, TypeDecl.plain, dataTypeName,
      reservedPrefix] ;
    simp [exprLanguage, exprType, zeroRule, parenRule,
      checkerConstructorDecl, TypeDecl.plain]

private theorem zeroRawLanguageValidate :
    (rawPresentation exprLanguage zeroLedger).language.validate = [] := by
  change (encodedLanguage exprLanguage zeroLedger).validate = []
  exact zeroEncodedLanguage_validate

private theorem zeroPresentationValid :
    (rawPresentation exprLanguage zeroLedger).isValidV2 = true := by
  unfold Presentation.isValidV2 Presentation.isValidV1
  rw [zeroRawLanguageValidate, zeroRulesValidV1, zeroRuleIdsUnique,
    zeroJudgmentSignatureValid, zeroRulesValidIn]
  simp [Presentation.conversionDeclarationValid, rawPresentation,
    encodedLanguage, exprLanguage]

example : (admit? exprLanguage zeroLedger).isSome = true := by
  have hgenerate : generate? exprLanguage zeroLedger =
      some (rawPresentation exprLanguage zeroLedger) := by
    simp [generate?, grammarSupportedForInference,
      ruleSupportedForInference, simpleParameter?, syntaxItemSupported,
      nonTerminalNames, TermParam.bodyName, exprLanguage, zeroRule,
      parenRule, zeroLedger]
    constructor <;> decide
  simp [admit?, hgenerate, Presentation.validateV2?, zeroPresentationValid]

private def zeroProductionSchema : RuleSchema :=
  { id := namespacedId "production" "Zero"
    metavariables :=
      [("source", 0), ("boundary" ++ toString 0, 0),
       ("boundary" ++ toString 1, 0)]
    premises :=
      [tokenSpanJudgment sourceVariable (boundaryVariable 0)
        (boundaryVariable 1) (tokenPattern "0")]
    conclusion :=
      derivesJudgment sourceVariable (sortPattern "Expr")
        (boundaryVariable 0) (boundaryVariable 1) (.apply "Zero" []) }

private theorem zeroProductionRule_eq :
    productionRule? zeroRule = some zeroProductionSchema := by
  simp [productionRule?, productionSchema, productionMetavariables,
    productionPremises, productionConclusion, buildSyntaxItems,
    ruleSupportedForInference, syntaxItemSupported,
    nonTerminalNames, zeroRule, zeroProductionSchema, boundaryVariable]
  decide

private def zeroPresentation : ValidatedPresentation :=
  validatedRawPresentation exprLanguage zeroLedger zeroPresentationValid

private theorem zeroProductionLookup :
    zeroPresentation.1.lookupRule? (namespacedId "production" "Zero") =
      some zeroProductionSchema := by
  have hrange : List.range (zeroLedger.tokens.length + 1) = [0, 1] := by
    decide
  have htokenRules : tokenFactRulesFrom zeroLedger 0 zeroLedger.tokens =
      [tokenFactRule zeroLedger 0 "0"] := by rfl
  have hboundaryZero :
      (boundaryFactRule zeroLedger 0).id ≠ namespacedId "production" "Zero" := by
    simp [boundaryFactRule, namespacedId, zeroLedger, reservedPrefix]
    decide
  have hboundaryOne :
      (boundaryFactRule zeroLedger 1).id ≠ namespacedId "production" "Zero" := by
    simp [boundaryFactRule, namespacedId, zeroLedger, reservedPrefix]
    decide
  have htoken :
      (tokenFactRule zeroLedger 0 "0").id ≠ namespacedId "production" "Zero" := by
    simp [tokenFactRule, namespacedId, zeroLedger, reservedPrefix]
    decide
  simp [zeroPresentation, validatedRawPresentation, Presentation.lookupRule?,
    rawPresentation, boundaryFactRules, tokenFactRules,
    grammarRules, exprLanguage, zeroProductionRule_eq,
    hboundaryZero, hboundaryOne, htoken, hrange, htokenRules,
    zeroProductionSchema]

private theorem zeroTokenLookup :
    zeroPresentation.1.lookupRule?
        (namespacedId "token" (zeroLedger.identity ++ ":0")) =
      some (tokenFactRule zeroLedger 0 "0") := by
  have hrange : List.range (zeroLedger.tokens.length + 1) = [0, 1] := by
    decide
  have htokenRules : tokenFactRulesFrom zeroLedger 0 zeroLedger.tokens =
      [tokenFactRule zeroLedger 0 "0"] := by rfl
  have hboundaryZero :
      (boundaryFactRule zeroLedger 0).id ≠
        namespacedId "token" (zeroLedger.identity ++ ":0") := by
    simp [boundaryFactRule, namespacedId, zeroLedger, reservedPrefix]
    decide
  have hboundaryOne :
      (boundaryFactRule zeroLedger 1).id ≠
        namespacedId "token" (zeroLedger.identity ++ ":0") := by
    simp [boundaryFactRule, namespacedId, zeroLedger, reservedPrefix]
    decide
  have htokenSelf :
      (tokenFactRule zeroLedger 0 "0").id =
        namespacedId "token" (zeroLedger.identity ++ ":0") := by
    simp [tokenFactRule, namespacedId, zeroLedger, reservedPrefix]
    decide
  simp [zeroPresentation, validatedRawPresentation, Presentation.lookupRule?,
    rawPresentation, boundaryFactRules, tokenFactRules,
    hboundaryZero, hboundaryOne, htokenSelf, hrange, htokenRules]

private def zeroGoal : Pattern :=
  rootJudgment zeroLedger "Expr" (.apply "Zero" [])

private def zeroTokenGoal : Pattern :=
  tokenSpanJudgment (sourcePattern zeroLedger) (boundaryPattern 0)
    (boundaryPattern 1) (tokenPattern "0")

private def zeroTokenRawProof : RawProof :=
  .node
    { ruleId := namespacedId "token" (zeroLedger.identity ++ ":0")
      arguments := [] }
    []

private def zeroProductionInstance : RuleInstance :=
  { ruleId := namespacedId "production" "Zero"
    arguments :=
      [sourcePattern zeroLedger, boundaryPattern 0, boundaryPattern 1] }

private def zeroRawProof : RawProof :=
  .node zeroProductionInstance [zeroTokenRawProof]

private theorem zeroTokenProofAccepts :
    checkRaw zeroPresentation zeroTokenGoal zeroTokenRawProof = true := by
  simp only [zeroTokenRawProof, checkRaw, instantiateRule?, zeroTokenLookup]
  simp [zeroTokenGoal, tokenFactRule, checkRawChildren, argumentsValidAt,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
    instantiateSchemasAt?, tokenSpanJudgment, sourcePattern, boundaryPattern,
    tokenPattern, literalPattern, literalLabel, zeroLedger, reservedPrefix]

private theorem zeroProductionInstantiates :
    instantiateRule? zeroPresentation zeroProductionInstance =
      some ([zeroTokenGoal], zeroGoal) := by
  have hsourceZero : "source" ≠ "boundary" ++ Nat.repr 0 := by decide
  have hsourceOne : "source" ≠ "boundary" ++ Nat.repr 1 := by decide
  have hreps : Nat.repr 0 ≠ Nat.repr 1 := by decide
  simp only [zeroProductionInstance, instantiateRule?, zeroProductionLookup]
  simp [zeroProductionSchema, argumentsValidAt, argumentValidAt,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
    instantiateSchemasAt?, lookupArgumentAt?, zeroTokenGoal, zeroGoal,
    rootJudgment, tokenSpanJudgment, derivesJudgment, sourceVariable,
    sourcePattern, sortPattern, tokenPattern, literalPattern,
    boundaryPattern, boundaryVariable, literalLabel, zeroLedger,
    Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, hsourceZero, hsourceOne, hreps]

private theorem zeroProofAccepts :
    checkRaw zeroPresentation zeroGoal zeroRawProof = true := by
  simp [zeroRawProof, checkRaw, zeroProductionInstantiates,
    checkRawChildren, zeroTokenProofAccepts]

example : checkRaw zeroPresentation zeroGoal zeroRawProof = true :=
  zeroProofAccepts

private def zeroCheckedProof : CheckedProof zeroPresentation zeroGoal :=
  ⟨zeroRawProof, zeroProofAccepts⟩

/-- The runnable fixture lands in the checker-defined Type-valued derivation,
not merely in a parser-specific replay relation. -/
theorem zero_has_typed_derivation :
    Nonempty (Derivation zeroPresentation zeroGoal) :=
  G3_checkedProof_nonempty_iff_derivation.mp ⟨zeroCheckedProof⟩

/-- End-to-end semantic calibration: generic-checker acceptance of the fixture
implies the independently defined grammar relation for the exact source. -/
theorem zero_checked_proof_derives :
    Derives exprLanguage "Expr" zeroLedger.tokens (.apply "Zero" []) :=
  checkedProof_root_sound exprLanguage zeroLedger zeroPresentationValid
    "Expr" (.apply "Zero" []) zeroCheckedProof

/-- Reusing the same raw tree for a different parse tree is rejected. -/
example : checkRaw zeroPresentation
    (rootJudgment zeroLedger "Expr" (.apply "Paren" [.apply "Zero" []]))
    zeroRawProof = false := by
  apply Bool.eq_false_of_not_eq_true
  intro hchanged
  have hgoals := checkRaw_goal_unique zeroProofAccepts hchanged
  simp [zeroGoal, rootJudgment, derivesJudgment] at hgoals

/-- Omitting the terminal occurrence proof is rejected. -/
example : checkRaw zeroPresentation zeroGoal
    (.node zeroProductionInstance []) = false := by
  simp [checkRaw, zeroProductionInstantiates, checkRawChildren]

private def unsupportedRule : GrammarRule :=
  { label := "Separated"
    category := "Expr"
    params := []
    syntaxPattern := [.separator ","] }

private def unsupportedLanguage : LanguageDef :=
  { exprLanguage with terms := [zeroRule, unsupportedRule] }

example : grammarSupportedForInference unsupportedLanguage = false := by decide
example : generate? unsupportedLanguage zeroLedger = none := by decide

private def emptyTokenLedger : SourceLedger :=
  { identity := "fixture-empty-token", tokens := [""] }

example : emptyTokenLedger.isValid = false := by decide
example : generate? exprLanguage emptyTokenLedger = none := by decide

end Mettapedia.GSLT.LanguageDef.GrammarInferenceExtraction
