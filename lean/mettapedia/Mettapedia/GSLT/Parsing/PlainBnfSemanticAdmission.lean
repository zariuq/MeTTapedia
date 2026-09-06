import Mettapedia.GSLT.Parsing.PlainBnfLexicalScalarSemantics
import Mettapedia.GSLT.Parsing.PlainBnfStructuredDenotation
import Mettapedia.GSLT.LanguageDef.StructuralCategory
import Mathlib.Tactic

/-!
# Independent semantic admission for structured plain BNF

The authored admission GSLT and its native realizations need an independent
meaning against which they can be checked.  This module states that meaning
directly over the structured grammar values produced by CST projection.  It
does not interpret an opaque parser record and it does not call the authored
GSLT as its own specification.

Occurrences remain explicit.  In particular, name resolution returns the
complete ordered list of grammar and lexical occurrences with a given name;
admission requires this list to be a singleton rather than selecting its first
member.  This makes duplicate definitions and namespace collisions visible.

The structured scalar carrier is `Nat`.  Negative integers are rejected by the
wire decoder before reaching this layer; Unicode range, surrogate exclusion,
nonemptiness, and strict ordering are checked here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.PlainBnfSemanticAdmission

open Mettapedia.OSLF.MeTTaIL.Syntax
open PlainBnfLexicalScalarSemantics
open PlainBnfStructuredDenotation

/-! ## Occurrence-preserving projections -/

structure RuleOccurrence where
  entryIndex : Nat
  name : String
  expression : Expression
  span : SourceSpan
  deriving DecidableEq, Repr

structure LexicalOccurrence where
  declarationIndex : Nat
  declaration : LexicalDeclaration
  deriving DecidableEq, Repr

/-- A source reference is identified by all three structural positions, not
only by its spelling or span. -/
structure ReferenceOccurrence where
  owner : String
  entryIndex : Nat
  alternativeIndex : Nat
  elementIndex : Nat
  name : String
  span : SourceSpan
  deriving DecidableEq, Repr

inductive ResolutionTarget where
  | grammar (occurrence : RuleOccurrence)
  | lexical (occurrence : LexicalOccurrence)
  deriving DecidableEq, Repr

def ruleOccurrencesFrom : List Entry -> Nat -> List RuleOccurrence
  | [], _ => []
  | .rule name expression span :: rest, index =>
      { entryIndex := index, name, expression, span } ::
        ruleOccurrencesFrom rest (index + 1)
  | .comment _ _ :: rest, index => ruleOccurrencesFrom rest (index + 1)
  | .blank _ :: rest, index => ruleOccurrencesFrom rest (index + 1)

def ruleOccurrences (document : Document) : List RuleOccurrence :=
  ruleOccurrencesFrom document.entries 0

def lexicalOccurrencesFrom :
    List LexicalDeclaration -> Nat -> List LexicalOccurrence
  | [], _ => []
  | declaration :: rest, index =>
      { declarationIndex := index, declaration } ::
        lexicalOccurrencesFrom rest (index + 1)

def lexicalOccurrences (authority : GrammarAuthority) :
    List LexicalOccurrence :=
  lexicalOccurrencesFrom authority.lexicalDeclarations 0

def referenceOccurrencesInElements
    (owner : String) (entryIndex alternativeIndex : Nat) :
    List Element -> Nat -> List ReferenceOccurrence
  | [], _ => []
  | .reference name span :: rest, elementIndex =>
      { owner, entryIndex, alternativeIndex, elementIndex, name, span } ::
        referenceOccurrencesInElements owner entryIndex alternativeIndex
          rest (elementIndex + 1)
  | .literal _ _ :: rest, elementIndex =>
      referenceOccurrencesInElements owner entryIndex alternativeIndex
        rest (elementIndex + 1)

def referenceOccurrencesInAlternatives
    (owner : String) (entryIndex : Nat) :
    List Alternative -> Nat -> List ReferenceOccurrence
  | [], _ => []
  | alternative :: rest, alternativeIndex =>
      referenceOccurrencesInElements owner entryIndex alternativeIndex
          alternative.elements 0 ++
        referenceOccurrencesInAlternatives owner entryIndex rest
          (alternativeIndex + 1)

def referenceOccurrencesFrom :
    List Entry -> Nat -> List ReferenceOccurrence
  | [], _ => []
  | .rule name expression _ :: rest, entryIndex =>
      referenceOccurrencesInAlternatives name entryIndex
          expression.alternatives 0 ++
        referenceOccurrencesFrom rest (entryIndex + 1)
  | .comment _ _ :: rest, entryIndex =>
      referenceOccurrencesFrom rest (entryIndex + 1)
  | .blank _ :: rest, entryIndex =>
      referenceOccurrencesFrom rest (entryIndex + 1)

def referenceOccurrences (document : Document) :
    List ReferenceOccurrence :=
  referenceOccurrencesFrom document.entries 0

/-- Occurrence-rich collection forgets to exactly the source reference-name
projection; indices and spans are retained in the left-hand carrier. -/
theorem referenceOccurrencesInElements_names
    (owner : String) (entryIndex alternativeIndex : Nat)
    (elements : List Element) (elementIndex : Nat) :
    (referenceOccurrencesInElements owner entryIndex alternativeIndex
        elements elementIndex).map (·.name) =
      elements.filterMap Element.referenceName? := by
  induction elements generalizing elementIndex with
  | nil => rfl
  | cons element rest ih =>
      cases element with
      | reference name span =>
          simp [referenceOccurrencesInElements, Element.referenceName?, ih]
      | literal text span =>
          simp [referenceOccurrencesInElements, Element.referenceName?, ih]

theorem referenceOccurrencesInAlternatives_names
    (owner : String) (entryIndex : Nat)
    (alternatives : List Alternative) (alternativeIndex : Nat) :
    (referenceOccurrencesInAlternatives owner entryIndex alternatives
        alternativeIndex).map (·.name) =
      alternatives.flatMap Alternative.referenceNames := by
  induction alternatives generalizing alternativeIndex with
  | nil => rfl
  | cons alternative rest ih =>
      simp [referenceOccurrencesInAlternatives,
        referenceOccurrencesInElements_names, Alternative.referenceNames, ih]

theorem referenceOccurrencesFrom_names
    (entries : List Entry) (entryIndex : Nat) :
    (referenceOccurrencesFrom entries entryIndex).map (·.name) =
      entryReferenceNames entries := by
  induction entries generalizing entryIndex with
  | nil => rfl
  | cons entry rest ih =>
      cases entry with
      | rule name expression span =>
          simp [referenceOccurrencesFrom,
            referenceOccurrencesInAlternatives_names, entryReferenceNames,
            Entry.referenceNames, Expression.referenceNames, ih]
      | comment text span =>
          simp [referenceOccurrencesFrom, entryReferenceNames,
            Entry.referenceNames, ih]
      | blank span =>
          simp [referenceOccurrencesFrom, entryReferenceNames,
            Entry.referenceNames, ih]

def grammarTargets (document : Document) (name : String) :
    List ResolutionTarget :=
  (ruleOccurrences document).filterMap fun occurrence =>
    if occurrence.name = name then some (.grammar occurrence) else none

def lexicalTargets (authority : GrammarAuthority) (name : String) :
    List ResolutionTarget :=
  (lexicalOccurrences authority).filterMap fun occurrence =>
    if occurrence.declaration.referenceName = name then
      some (.lexical occurrence)
    else none

/-- Complete resolution candidates, in grammar-source order followed by
lexical-authority order.  No ambiguity policy is hidden here. -/
def resolutionTargets (document : Document) (authority : GrammarAuthority)
    (name : String) : List ResolutionTarget :=
  grammarTargets document name ++ lexicalTargets authority name

theorem name_mem_ruleOccurrence_names_of_mem_grammarTargets
    (document : Document) (name : String) (target : ResolutionTarget)
    (member : target ∈ grammarTargets document name) :
    name ∈ (ruleOccurrences document).map (·.name) := by
  rw [grammarTargets, List.mem_filterMap] at member
  rcases member with ⟨occurrence, occurrenceMember, selected⟩
  split at selected
  next equal =>
    exact List.mem_map.mpr ⟨occurrence, occurrenceMember, equal⟩
  next unequal => simp at selected

theorem name_mem_lexicalOccurrence_names_of_mem_lexicalTargets
    (authority : GrammarAuthority) (name : String) (target : ResolutionTarget)
    (member : target ∈ lexicalTargets authority name) :
    name ∈ (lexicalOccurrences authority).map
      (·.declaration.referenceName) := by
  rw [lexicalTargets, List.mem_filterMap] at member
  rcases member with ⟨occurrence, occurrenceMember, selected⟩
  split at selected
  next equal =>
    exact List.mem_map.mpr ⟨occurrence, occurrenceMember, equal⟩
  next unequal => simp at selected

/-! ## Independent admission proposition -/

def MatcherWellFormed : LexicalMatcher -> Prop
  | .points scalars =>
      ScalarListWellFormed (scalars.map Int.ofNat)
  | .except scalars =>
      scalars = [] ∨ ScalarListWellFormed (scalars.map Int.ofNat)

def checkLexicalMatcher : LexicalMatcher -> Bool
  | .points scalars =>
      checkScalarList (scalars.map Int.ofNat)
  | .except scalars =>
      scalars.isEmpty || checkScalarList (scalars.map Int.ofNat)

theorem checkLexicalMatcher_eq_true_iff (matcher : LexicalMatcher) :
    checkLexicalMatcher matcher = true <-> MatcherWellFormed matcher := by
  cases matcher with
  | points scalars => exact checkScalarList_eq_true_iff _
  | except scalars =>
      simp only [checkLexicalMatcher, MatcherWellFormed, Bool.or_eq_true,
        List.isEmpty_iff, checkScalarList_eq_true_iff]

/-- An empty exclusion list excludes nothing; it is not an empty point class. -/
theorem empty_exclusion_is_well_formed : MatcherWellFormed (.except []) := by
  exact Or.inl rfl

theorem empty_point_class_is_refused : checkLexicalMatcher (.points []) = false := rfl

theorem empty_exclusion_is_accepted : checkLexicalMatcher (.except []) = true := rfl

instance (matcher : LexicalMatcher) : Decidable (MatcherWellFormed matcher) :=
  if checked : checkLexicalMatcher matcher = true then
    isTrue ((checkLexicalMatcher_eq_true_iff matcher).mp checked)
  else
    isFalse fun wellFormed =>
      checked ((checkLexicalMatcher_eq_true_iff matcher).mpr wellFormed)

def DeclarationWellFormed
    (declaration : LexicalDeclaration) : Prop :=
  declaration.referenceName ≠ "" /\
    declaration.className ≠ "" /\
    declaration.ruleLabel ≠ "" /\
    MatcherWellFormed declaration.matcher

instance (declaration : LexicalDeclaration) :
    Decidable (DeclarationWellFormed declaration) := by
  unfold DeclarationWellFormed
  infer_instance

/-- Finite, decidable formulation of namespace disjointness. -/
def NamesDisjoint (left right : List String) : Prop :=
  left.Forall fun name => name ∉ right

instance (left right : List String) : Decidable (NamesDisjoint left right) := by
  unfold NamesDisjoint
  infer_instance

/-- Acceptance conditions independently stated over structured data.  Graph
properties such as reachability, productivity, and nullability are deliberately
not admission conditions; they are separate analyses of an admitted grammar. -/
def WellFormed (document : Document)
    (authority : GrammarAuthority) : Prop :=
  ruleOccurrences document ≠ [] /\
  ((ruleOccurrences document).map (·.name)).Nodup /\
  ((lexicalOccurrences authority).map
      (·.declaration.referenceName)).Nodup /\
  ((lexicalOccurrences authority).map
      (·.declaration.className)).Nodup /\
  ((lexicalOccurrences authority).map
      (·.declaration.ruleLabel)).Nodup /\
  NamesDisjoint
    ((ruleOccurrences document).map (·.name))
    ((lexicalOccurrences authority).map (·.declaration.referenceName)) /\
  authority.lexicalDeclarations.Forall DeclarationWellFormed /\
  (grammarTargets document authority.startName).length = 1 /\
  (referenceOccurrences document).Forall fun occurrence =>
    (resolutionTargets document authority occurrence.name).length = 1

instance (document : Document) (authority : GrammarAuthority) :
    Decidable (WellFormed document authority) := by
  unfold WellFormed
  infer_instance

/-- Executable admission checker derived from the independent proposition. -/
def check (document : Document) (authority : GrammarAuthority) : Bool :=
  decide (WellFormed document authority)

theorem check_eq_true_iff (document : Document)
    (authority : GrammarAuthority) :
    check document authority = true <-> WellFormed document authority := by
  simp [check]

/-- The proof-carrying input accepted by semantic denotation. -/
structure AdmittedInput where
  document : Document
  authority : GrammarAuthority
  wellFormed : WellFormed document authority

def admit? (document : Document) (authority : GrammarAuthority) :
    Option AdmittedInput :=
  if wellFormed : WellFormed document authority then
    some { document, authority, wellFormed }
  else none

theorem admit_isSome_iff (document : Document)
    (authority : GrammarAuthority) :
    (admit? document authority).isSome = true <->
      WellFormed document authority := by
  simp [admit?]

/-- Denotation is only exposed through the proof-carrying input at this
boundary; the underlying total structural fold remains separately reusable. -/
def AdmittedInput.denote (input : AdmittedInput) : Candidate :=
  PlainBnfStructuredDenotation.denote input.document input.authority

/-! ## Useful consequences for the denoted language -/

theorem ruleOccurrence_names (entries : List Entry) (index : Nat) :
    (ruleOccurrencesFrom entries index).map (·.name) =
      entries.filterMap Entry.ruleName? := by
  induction entries generalizing index with
  | nil => rfl
  | cons entry rest ih =>
      cases entry with
      | rule name expression span =>
          simp [ruleOccurrencesFrom, Entry.ruleName?, ih]
      | comment text span =>
          simp [ruleOccurrencesFrom, Entry.ruleName?, ih]
      | blank span =>
          simp [ruleOccurrencesFrom, Entry.ruleName?, ih]

theorem lexicalOccurrence_referenceNames
    (declarations : List LexicalDeclaration) (index : Nat) :
    (lexicalOccurrencesFrom declarations index).map
        (·.declaration.referenceName) =
      declarations.map (·.referenceName) := by
  induction declarations generalizing index with
  | nil => rfl
  | cons declaration rest ih =>
      simp [lexicalOccurrencesFrom, ih]

/-- A uniquely resolved source reference names a sort emitted by denotation.
The proof inspects the complete target list; it never selects a preferred
namespace or first occurrence. -/
theorem name_mem_denoted_type_names_of_unique_resolution
    (document : Document) (authority : GrammarAuthority) (name : String)
    (unique : (resolutionTargets document authority name).length = 1) :
    name ∈ (PlainBnfStructuredDenotation.denote document authority).language.typeNames := by
  cases targetsEqual : resolutionTargets document authority name with
  | nil => simp [targetsEqual] at unique
  | cons target rest =>
      have targetMember :
          target ∈ resolutionTargets document authority name := by
        rw [targetsEqual]
        exact List.mem_cons_self
      rw [resolutionTargets, List.mem_append] at targetMember
      change name ∈
        (PlainBnfStructuredDenotation.denote document authority).language.types.map
          TypeDecl.name
      rw [PlainBnfStructuredDenotation.denote_type_names]
      rcases targetMember with grammarMember | lexicalMember
      · apply List.mem_append_left
        have occurrenceNameMember :=
          name_mem_ruleOccurrence_names_of_mem_grammarTargets document name
            target grammarMember
        change name ∈ (ruleOccurrencesFrom document.entries 0).map
          (fun occurrence => occurrence.name) at occurrenceNameMember
        simpa [ruleOccurrence_names] using occurrenceNameMember
      ·
        have occurrenceNameMember :=
          name_mem_lexicalOccurrence_names_of_mem_lexicalTargets authority name
            target lexicalMember
        change name ∈
          (lexicalOccurrencesFrom authority.lexicalDeclarations 0).map
            (·.declaration.referenceName) at occurrenceNameMember
        have lexicalNameMember :
            name ∈ authority.lexicalDeclarations.map (·.referenceName) := by
          simpa [lexicalOccurrence_referenceNames] using occurrenceNameMember
        exact List.mem_append_right
          (document.entries.filterMap Entry.ruleName?) lexicalNameMember

/-- Admission makes the generated type namespace duplicate-free. -/
theorem AdmittedInput.denoted_type_names_nodup (input : AdmittedInput) :
    (input.denote.language.types.map (·.name)).Nodup := by
  change
    ((PlainBnfStructuredDenotation.denote
      input.document input.authority).language.types.map (·.name)).Nodup
  rw [PlainBnfStructuredDenotation.denote_type_names]
  rw [← ruleOccurrence_names input.document.entries 0]
  rw [← lexicalOccurrence_referenceNames
    input.authority.lexicalDeclarations 0]
  rcases input.wellFormed with
    ⟨_, ruleNamesNodup, lexicalReferenceNamesNodup, _, _,
      grammarLexicalNamesDisjoint, _⟩
  apply List.nodup_append'.mpr
  refine ⟨ruleNamesNodup, lexicalReferenceNamesNodup, ?_⟩
  rw [List.disjoint_left]
  exact List.forall_iff_forall_mem.mp grammarLexicalNamesDisjoint

/-- Admission's unique source rule names, together with the injective
category/alternative occurrence encoding, make every generated constructor
label distinct. -/
theorem AdmittedInput.denoted_constructor_labels_nodup
    (input : AdmittedInput) :
    (input.denote.language.terms.map (·.label)).Nodup := by
  change ((denoteRules input.document.entries).map (·.label)).Nodup
  apply denoteRules_labels_nodup
  rw [← ruleOccurrence_names input.document.entries 0]
  exact input.wellFormed.2.1

/-- Every generated constructor returns a source-declared grammar sort. -/
theorem AdmittedInput.denoted_categories_declared
    (input : AdmittedInput) (rule : GrammarRule)
    (member : rule ∈ input.denote.language.terms) :
    rule.category ∈ input.denote.language.typeNames := by
  have categoryMember := category_mem_ruleNames_of_mem_denoteRules
    input.document.entries member
  change rule.category ∈
    (PlainBnfStructuredDenotation.denote input.document input.authority).language.types.map
      TypeDecl.name
  rw [PlainBnfStructuredDenotation.denote_type_names]
  exact List.mem_append_left _ categoryMember

/-- Admission proves that every generated parameter sort resolves to exactly
one declared grammar or lexical sort. -/
theorem AdmittedInput.denoted_parameter_types_declared
    (input : AdmittedInput) (rule : GrammarRule)
    (ruleMember : rule ∈ input.denote.language.terms)
    (parameter : TermParam) (parameterMember : parameter ∈ rule.params)
    (typeName : String)
    (typeNameMember :
      typeName ∈ (TermParam.typeExpr parameter).baseNames) :
    typeName ∈ input.denote.language.typeNames := by
  have sourceNameMember :
      typeName ∈ entryReferenceNames input.document.entries :=
    referenceName_mem_of_parameter_type_mem_denoteRules input.document.entries
      rule ruleMember parameter parameterMember typeName typeNameMember
  have occurrenceNameMember :
      typeName ∈
        (referenceOccurrencesFrom input.document.entries 0).map (·.name) := by
    rw [referenceOccurrencesFrom_names]
    exact sourceNameMember
  rcases List.mem_map.mp occurrenceNameMember with
    ⟨occurrence, occurrenceMember, occurrenceNameEqual⟩
  rcases input.wellFormed with
    ⟨_, _, _, _, _, _, _, _, referencesResolve⟩
  have unique := (List.forall_iff_forall_mem.mp referencesResolve)
    occurrence occurrenceMember
  rw [occurrenceNameEqual] at unique
  exact name_mem_denoted_type_names_of_unique_resolution input.document
    input.authority typeName unique

/-- An admitted plain-BNF document denotes an ordinary validated syntax
language.  This is the semantic handoff to generic ParserPack compilation. -/
theorem AdmittedInput.denoted_language_valid (input : AdmittedInput) :
    input.denote.language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxAndRewrites
      input.denote.language
  · rfl
  · exact input.denoted_type_names_nodup
  · exact input.denoted_constructor_labels_nodup
  · simp [AdmittedInput.denote, PlainBnfStructuredDenotation.denote]
  · exact input.denoted_categories_declared
  · exact input.denoted_parameter_types_declared
  · exact PlainBnfStructuredDenotation.denote_concreteSyntaxRowsValid
      input.document input.authority
  · intro rewrite rewriteMember
    simp [AdmittedInput.denote, PlainBnfStructuredDenotation.denote] at rewriteMember

/-- Proof-carrying packaged form of the denoted syntax language. -/
def AdmittedInput.validatedLanguage (input : AdmittedInput) :
    Mettapedia.GSLT.LanguageDef.ValidatedLanguageDef :=
  { language := input.denote.language
    valid := input.denoted_language_valid }

/-! ## Positive and negative controls -/

private def span : SourceSpan := { start := 0, stop := 1 }

private def lexicalA : LexicalDeclaration :=
  { referenceName := "letter"
    className := "letter-class"
    matcher := .points [97]
    ruleLabel := "letter-rule"
    origin := { authority := "example", occurrence := 0 } }

private def validDocument : Document :=
  { entries := [
      .rule "start"
        { alternatives := [
            { elements := [.reference "letter" span]
              span }]
          span }
        span]
    span }

private def validAuthority : GrammarAuthority :=
  { startName := "start", lexicalDeclarations := [lexicalA] }

theorem valid_grammar_is_admitted :
    check validDocument validAuthority = true := by
  decide +kernel

theorem empty_grammar_is_refused :
    check { entries := [], span } validAuthority = false := by
  decide +kernel

theorem unresolved_reference_is_refused :
    let document : Document :=
      { entries := [
          .rule "start"
            { alternatives := [
                { elements := [.reference "missing" span]
                  span }]
              span }
            span]
        span }
    check document { startName := "start", lexicalDeclarations := [] } =
      false := by
  decide +kernel

theorem duplicate_rule_is_refused :
    let expression : Expression :=
      { alternatives := [{ elements := [], span }], span }
    let document : Document :=
      { entries := [
          .rule "start" expression span,
          .rule "start" expression span]
        span }
    check document { startName := "start", lexicalDeclarations := [] } =
      false := by
  decide +kernel

theorem lexical_rule_collision_is_refused :
    let document : Document :=
      { entries := [
          .rule "letter"
            { alternatives := [{ elements := [], span }], span }
            span]
        span }
    check document { startName := "letter", lexicalDeclarations := [lexicalA] } =
      false := by
  decide +kernel

theorem malformed_lexical_matcher_is_refused :
    let malformed := { lexicalA with matcher := .points [97, 97] }
    check validDocument
      { startName := "start", lexicalDeclarations := [malformed] } = false := by
  decide +kernel

#print axioms checkLexicalMatcher_eq_true_iff
#print axioms check_eq_true_iff
#print axioms admit_isSome_iff
#print axioms referenceOccurrencesFrom_names
#print axioms ruleOccurrence_names
#print axioms lexicalOccurrence_referenceNames
#print axioms name_mem_denoted_type_names_of_unique_resolution
#print axioms AdmittedInput.denoted_type_names_nodup
#print axioms AdmittedInput.denoted_constructor_labels_nodup
#print axioms AdmittedInput.denoted_categories_declared
#print axioms AdmittedInput.denoted_parameter_types_declared
#print axioms AdmittedInput.denoted_language_valid
#print axioms valid_grammar_is_admitted
#print axioms empty_grammar_is_refused
#print axioms unresolved_reference_is_refused
#print axioms duplicate_rule_is_refused
#print axioms lexical_rule_collision_is_refused
#print axioms malformed_lexical_matcher_is_refused

end Mettapedia.GSLT.Parsing.PlainBnfSemanticAdmission
