import Mettapedia.GSLT.Parsing.ParserProfileSemantics
import Mettapedia.OSLF.MeTTaIL.Syntax
import Mathlib.Tactic

/-!
# Structured plain-BNF denotation

This module gives the existing `BnfGrammarDocument` data vocabulary a typed,
backend-independent meaning.  It is not another parser representation: the
constructors below are the direct semantic counterparts of the structured
values produced by the plain-BNF CST projection.

Denotation is a total structural fold from an admitted grammar document and
its explicit lexical authority to the project's ordinary `LanguageDef` and
`ParserProfileLayer`.  Rule order, alternative occurrences, literal order,
reference order, source spans, duplicate alternatives, and lexical declaration
order remain observable.  Validation and parsing are separate constructions;
their correspondence with this denotation requires separate theorems.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.PlainBnfStructuredDenotation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.Parsing.ParserProfileSemantics

/-! ## Direct typed meaning of the structured BNF values -/

/-- Half-open scalar offsets retained from the source CST. -/
structure SourceSpan where
  start : Nat
  stop : Nat
  deriving DecidableEq, Repr

/-- A plain-BNF element is either a named grammar/lexical reference or a
literal scalar string.  Both retain their exact source occurrence. -/
inductive Element where
  | reference (name : String) (span : SourceSpan)
  | literal (text : String) (span : SourceSpan)
  deriving DecidableEq, Repr

namespace Element

/-- Forget only the occurrence metadata of a reference.  This projection is
used in preservation theorems; the structured `Element` remains the source
carrier. -/
def referenceName? : Element -> Option String
  | .reference name _ => some name
  | .literal _ _ => none

end Element

structure Alternative where
  elements : List Element
  span : SourceSpan
  deriving DecidableEq, Repr

structure Expression where
  alternatives : List Alternative
  span : SourceSpan
  deriving DecidableEq, Repr

/-- Comments and blank lines remain in the structured document even though
they do not denote grammar constructors. -/
inductive Entry where
  | rule (name : String) (expression : Expression) (span : SourceSpan)
  | comment (text : String) (span : SourceSpan)
  | blank (span : SourceSpan)
  deriving DecidableEq, Repr

structure Document where
  entries : List Entry
  span : SourceSpan
  deriving DecidableEq, Repr

namespace Alternative

/-- Reference spellings projected from one source alternative, retaining
source order and multiplicity. -/
def referenceNames (alternative : Alternative) : List String :=
  alternative.elements.filterMap Element.referenceName?

end Alternative

namespace Expression

def referenceNames (expression : Expression) : List String :=
  expression.alternatives.flatMap Alternative.referenceNames

end Expression

namespace Entry


def referenceNames : Entry -> List String
  | .rule _ expression _ => expression.referenceNames
  | .comment _ _ | .blank _ => []

end Entry

/-- Reference spellings from every rule entry, retaining entry, alternative,
and element order as well as multiplicity. -/
def entryReferenceNames (entries : List Entry) : List String :=
  entries.flatMap Entry.referenceNames

inductive LexicalMatcher where
  | points (scalars : List Nat)
  | except (excluded : List Nat)
  deriving DecidableEq, Repr

/-- Authored provenance for a lexical declaration is distinct from its list
position in the current authority. -/
structure LexicalOrigin where
  authority : String
  occurrence : Nat
  deriving DecidableEq, Repr

structure LexicalDeclaration where
  referenceName : String
  className : String
  matcher : LexicalMatcher
  ruleLabel : String
  origin : LexicalOrigin
  deriving DecidableEq, Repr

structure GrammarAuthority where
  startName : String
  lexicalDeclarations : List LexicalDeclaration
  deriving DecidableEq, Repr

/-! ## Proof-relevant origin output -/

structure GeneratedRuleOrigin where
  label : String
  category : String
  ruleSpan : SourceSpan
  alternativeSpan : SourceSpan
  deriving DecidableEq, Repr

structure GeneratedLexicalOrigin where
  resultSort : String
  className : String
  ruleLabel : String
  matcher : LexicalMatcher
  source : LexicalOrigin
  deriving DecidableEq, Repr

structure DenotationOrigins where
  rules : List GeneratedRuleOrigin
  lexical : List GeneratedLexicalOrigin
  deriving DecidableEq, Repr

/-- The semantic result produced by the plain-BNF denotation GSLT. -/
structure Candidate where
  language : LanguageDef
  profile : ParserProfileLayer
  origins : DenotationOrigins
  deriving Repr

/-! ## Exact structural fold -/

/-- The occurrence suffix used by the executable GSLT: `#`, `#x`, `#xx`, ... -/
def occurrenceSuffix (index : Nat) : String :=
  "#" ++ String.ofList (List.replicate index 'x')

def generatedRuleLabel (category : String) (index : Nat) : String :=
  category ++ occurrenceSuffix index

def generatedParameterName (index : Nat) : String :=
  "p" ++ occurrenceSuffix index

/-- Consume the maximal leading run of `x` characters.  Applied to the
reverse of a generated rule label, this exposes the final `#` delimiter and
recovers the alternative index without imposing restrictions on category
names. -/
def consumeLeadingXs : List Char -> Nat × List Char
  | 'x' :: rest =>
      let consumed := consumeLeadingXs rest
      (consumed.1 + 1, consumed.2)
  | rest => (0, rest)

@[simp] theorem consumeLeadingXs_replicate_delimiter
    (index : Nat) (tail : List Char) :
    consumeLeadingXs (List.replicate index 'x' ++ '#' :: tail) =
      (index, '#' :: tail) := by
  induction index with
  | zero => rfl
  | succ index ih =>
      simp [List.replicate_succ, consumeLeadingXs, ih]

/-- Partial inverse of the generated rule-label encoding.  The rightmost `#`
is the structural delimiter; preceding `#` characters remain part of the
category name. -/
def decodeGeneratedRuleLabel (label : String) : Option (String × Nat) :=
  let consumed := consumeLeadingXs label.toList.reverse
  match consumed.2 with
  | '#' :: reversedCategory =>
      some (String.ofList reversedCategory.reverse, consumed.1)
  | _ => none

@[simp] theorem decodeGeneratedRuleLabel_generated
    (category : String) (index : Nat) :
    decodeGeneratedRuleLabel (generatedRuleLabel category index) =
      some (category, index) := by
  simp [decodeGeneratedRuleLabel, generatedRuleLabel, occurrenceSuffix,
    String.toList_append, List.reverse_append]

/-- Generated labels retain both the complete category name and alternative
occurrence index. -/
theorem generatedRuleLabel_joint_injective :
    Function.Injective (Function.uncurry generatedRuleLabel) := by
  rintro ⟨leftCategory, leftIndex⟩ ⟨rightCategory, rightIndex⟩ equal
  have decoded := congrArg decodeGeneratedRuleLabel equal
  simpa [Function.uncurry] using decoded

/-- Negative control: an arbitrary constructor label without the structural
delimiter is not misidentified as a generated BNF occurrence. -/
theorem decodeGeneratedRuleLabel_rejects_missing_delimiter :
    decodeGeneratedRuleLabel "ordinary-label" = none := by
  decide +kernel

theorem generatedParameterName_injective :
    Function.Injective generatedParameterName := by
  intro left right equal
  have characterLists := congrArg String.toList equal
  have lengths := congrArg List.length characterLists
  simp [generatedParameterName, occurrenceSuffix, String.toList_append] at lengths
  exact lengths

/-- Reference bindings generated while traversing one alternative.  The first
component is the constructor-parameter name; the second is its referenced
grammar or lexical sort. -/
def denoteReferenceBindings : List Element -> Nat -> List (String × String)
  | [], _ => []
  | .reference name _ :: rest, index =>
      (generatedParameterName index, name) ::
        denoteReferenceBindings rest (index + 1)
  | .literal _ _ :: rest, index =>
      denoteReferenceBindings rest index

def denoteParameters (elements : List Element) (index : Nat) :
    List TermParam :=
  (denoteReferenceBindings elements index).map fun binding =>
    .simple binding.1 (.base binding.2)

theorem simpleParameters_baseNames (bindings : List (String × String)) :
    ((bindings.map fun binding =>
        TermParam.simple binding.1 (.base binding.2)).flatMap fun parameter =>
      (TermParam.typeExpr parameter).baseNames) = bindings.map Prod.snd := by
  induction bindings with
  | nil => rfl
  | cons binding rest ih =>
      change [binding.2] ++
          ((rest.map fun restBinding =>
              TermParam.simple restBinding.1 (.base restBinding.2)).flatMap
            fun parameter => (TermParam.typeExpr parameter).baseNames) =
        binding.2 :: rest.map Prod.snd
      rw [ih]
      rfl

theorem simpleParameters_boundNames (bindings : List (String × String)) :
    ((bindings.map fun binding =>
        TermParam.simple binding.1 (.base binding.2)).flatMap fun parameter =>
      TermParam.bodyName parameter :: TermParam.binderNames parameter) =
        bindings.map Prod.fst := by
  induction bindings with
  | nil => rfl
  | cons binding rest ih =>
      change [binding.1] ++
          ((rest.map fun restBinding =>
              TermParam.simple restBinding.1 (.base restBinding.2)).flatMap
            fun parameter =>
              TermParam.bodyName parameter ::
                TermParam.binderNames parameter) =
        binding.1 :: rest.map Prod.fst
      rw [ih]
      rfl

/-- Parameter sorts are exactly the source references, in occurrence order.
No literal contributes a sort and no repeated reference is removed. -/
theorem denoteReferenceBindings_sorts
    (elements : List Element) (index : Nat) :
    (denoteReferenceBindings elements index).map Prod.snd =
      elements.filterMap Element.referenceName? := by
  induction elements generalizing index with
  | nil => rfl
  | cons element rest ih =>
      cases element with
      | reference name span =>
          simp [denoteReferenceBindings, Element.referenceName?, ih]
      | literal text span =>
          simp [denoteReferenceBindings, Element.referenceName?, ih]

/-- Flattening the generated parameter types recovers exactly the ordered
source-reference spellings. -/
theorem denoteParameters_baseNames
    (elements : List Element) (index : Nat) :
    ((denoteParameters elements index).flatMap fun parameter =>
        (TermParam.typeExpr parameter).baseNames) =
      elements.filterMap Element.referenceName? := by
  rw [denoteParameters, simpleParameters_baseNames,
    denoteReferenceBindings_sorts]

/-- The bound syntax names are exactly the generated reference-parameter
names.  Plain BNF introduces no binders at this layer. -/
theorem denoteParameters_boundNames
    (elements : List Element) (index : Nat) :
    ((denoteParameters elements index).flatMap fun parameter =>
        TermParam.bodyName parameter :: TermParam.binderNames parameter) =
      (denoteReferenceBindings elements index).map Prod.fst := by
  rw [denoteParameters, simpleParameters_boundNames]

theorem generatedParameterName_lower_not_mem
    (elements : List Element) {lower index : Nat} (less : lower < index) :
    generatedParameterName lower ∉
      (denoteReferenceBindings elements index).map Prod.fst := by
  induction elements generalizing index with
  | nil => simp [denoteReferenceBindings]
  | cons element rest ih =>
      cases element with
      | reference name span =>
          simp only [denoteReferenceBindings, List.map_cons,
            List.mem_cons, not_or]
          constructor
          · intro equal
            have := generatedParameterName_injective equal
            omega
          · exact ih (by omega)
      | literal text span =>
          simpa [denoteReferenceBindings] using ih less

/-- Generated parameter names are fresh by occurrence index; the denotation
does not rely on a later deduplication pass to make lookup deterministic. -/
theorem denoteReferenceBinding_names_nodup
    (elements : List Element) (index : Nat) :
    ((denoteReferenceBindings elements index).map Prod.fst).Nodup := by
  induction elements generalizing index with
  | nil => simp [denoteReferenceBindings]
  | cons element rest ih =>
      cases element with
      | reference name span =>
          simp only [denoteReferenceBindings, List.map_cons,
            List.nodup_cons]
          exact ⟨generatedParameterName_lower_not_mem rest (by omega),
            ih (index + 1)⟩
      | literal text span =>
          simpa [denoteReferenceBindings] using ih index

/-- Empty literals denote epsilon; nonempty literals remain one terminal item.
References use exactly the generated parameter name at the corresponding
reference occurrence. -/
def denoteSyntax : List Element -> Nat -> List SyntaxItem
  | [], _ => []
  | .reference _ _ :: rest, index =>
      .nonTerminal (generatedParameterName index) ::
        denoteSyntax rest (index + 1)
  | .literal text _ :: rest, index =>
      if text.isEmpty then denoteSyntax rest index
      else .terminal text :: denoteSyntax rest index

/-- Adding another available parameter cannot invalidate one of the plain
syntax items emitted by this fold. -/
theorem concreteSyntaxItemAllowed_cons_of_true
    (head : String) (names : List String) (item : SyntaxItem)
    (allowed : LanguageDef.concreteSyntaxItemAllowed names item = true) :
    LanguageDef.concreteSyntaxItemAllowed (head :: names) item = true := by
  cases item <;> simp_all [LanguageDef.concreteSyntaxItemAllowed]

/-- Every generated nonterminal names the parameter emitted for that exact
reference occurrence; generated terminals require no parameter. -/
theorem denoteSyntax_allowed_by_bindings
    (elements : List Element) (index : Nat) (item : SyntaxItem)
    (member : item ∈ denoteSyntax elements index) :
    LanguageDef.concreteSyntaxItemAllowed
      ((denoteReferenceBindings elements index).map Prod.fst) item = true := by
  induction elements generalizing index item with
  | nil => simp [denoteSyntax] at member
  | cons element rest ih =>
      cases element with
      | reference name span =>
          simp only [denoteSyntax, List.mem_cons] at member
          rcases member with equal | inRest
          · subst item
            simp [denoteReferenceBindings,
              LanguageDef.concreteSyntaxItemAllowed]
          · exact concreteSyntaxItemAllowed_cons_of_true
              (generatedParameterName index)
              ((denoteReferenceBindings rest (index + 1)).map Prod.fst)
              item (ih (index + 1) item inRest)
      | literal text span =>
          by_cases empty : text.isEmpty
          · change item ∈
              (if text.isEmpty then denoteSyntax rest index
                else .terminal text :: denoteSyntax rest index) at member
            rw [if_pos empty] at member
            simpa [denoteReferenceBindings] using ih index item member
          · change item ∈
              (if text.isEmpty then denoteSyntax rest index
                else .terminal text :: denoteSyntax rest index) at member
            rw [if_neg empty] at member
            rcases List.mem_cons.mp member with equal | inRest
            · subst item
              simp [LanguageDef.concreteSyntaxItemAllowed]
            · simpa [denoteReferenceBindings] using ih index item inRest

/-- References contribute one typed parameter and one nonterminal use.
Literals contribute no constructor parameter. -/
def denoteElements (elements : List Element) (index : Nat) :
    List TermParam × List SyntaxItem :=
  (denoteParameters elements index, denoteSyntax elements index)

def denoteAlternative (category : String) (index : Nat)
    (alternative : Alternative) : GrammarRule :=
  let interpreted := denoteElements alternative.elements 0
  { label := generatedRuleLabel category index
    category := category
    params := interpreted.1
    syntaxPattern := interpreted.2 }

def denoteAlternatives (category : String) :
    List Alternative -> Nat -> List GrammarRule
  | [], _ => []
  | alternative :: rest, index =>
      denoteAlternative category index alternative ::
        denoteAlternatives category rest (index + 1)

/-- Every base sort used by a denoted alternative parameter is the spelling
of an actual source reference occurrence in that alternative. -/
theorem referenceName_mem_of_parameter_type_mem_denoteAlternative
    (category : String) (index : Nat) (alternative : Alternative)
    (parameter : TermParam)
    (parameterMember :
      parameter ∈ (denoteAlternative category index alternative).params)
    (typeName : String)
    (typeNameMember :
      typeName ∈ (TermParam.typeExpr parameter).baseNames) :
    typeName ∈ alternative.referenceNames := by
  have flattened : typeName ∈
      ((denoteParameters alternative.elements 0).flatMap fun generated =>
        (TermParam.typeExpr generated).baseNames) :=
    List.mem_flatMap.mpr ⟨parameter,
      by simpa [denoteAlternative, denoteElements] using parameterMember,
      typeNameMember⟩
  simpa [Alternative.referenceNames, denoteParameters_baseNames] using flattened

theorem referenceName_mem_of_parameter_type_mem_denoteAlternatives
    (category : String) (alternatives : List Alternative) (index : Nat)
    (rule : GrammarRule)
    (ruleMember : rule ∈ denoteAlternatives category alternatives index)
    (parameter : TermParam) (parameterMember : parameter ∈ rule.params)
    (typeName : String)
    (typeNameMember :
      typeName ∈ (TermParam.typeExpr parameter).baseNames) :
    typeName ∈ alternatives.flatMap Alternative.referenceNames := by
  induction alternatives generalizing index with
  | nil => simp [denoteAlternatives] at ruleMember
  | cons alternative rest ih =>
      simp only [denoteAlternatives, List.mem_cons] at ruleMember
      rcases ruleMember with equal | inRest
      · subst rule
        apply List.mem_append_left
        exact referenceName_mem_of_parameter_type_mem_denoteAlternative
          category index alternative parameter parameterMember typeName
          typeNameMember
      · apply List.mem_append_right alternative.referenceNames
        exact ih (index + 1) inRest

/-- Every syntax row of one denoted alternative uses only literal terminals
or the parameters generated from that same alternative. -/
theorem denoteAlternative_concreteSyntax_valid
    (category : String) (index : Nat) (alternative : Alternative)
    (item : SyntaxItem)
    (member : item ∈
      (denoteAlternative category index alternative).syntaxPattern) :
    LanguageDef.concreteSyntaxItemAllowed
      ((denoteAlternative category index alternative).params.flatMap
        fun parameter =>
          TermParam.bodyName parameter :: TermParam.binderNames parameter)
      item = true := by
  change item ∈ denoteSyntax alternative.elements 0 at member
  change LanguageDef.concreteSyntaxItemAllowed
    ((denoteParameters alternative.elements 0).flatMap fun parameter =>
      TermParam.bodyName parameter :: TermParam.binderNames parameter)
    item = true
  rw [denoteParameters_boundNames]
  exact denoteSyntax_allowed_by_bindings alternative.elements 0 item member

theorem denoteAlternatives_concreteSyntax_valid
    (category : String) (alternatives : List Alternative) (index : Nat)
    (rule : GrammarRule)
    (ruleMember : rule ∈ denoteAlternatives category alternatives index)
    (item : SyntaxItem) (itemMember : item ∈ rule.syntaxPattern) :
    LanguageDef.concreteSyntaxItemAllowed
      (rule.params.flatMap fun parameter =>
        TermParam.bodyName parameter :: TermParam.binderNames parameter)
      item = true := by
  induction alternatives generalizing index with
  | nil => simp [denoteAlternatives] at ruleMember
  | cons alternative rest ih =>
      simp only [denoteAlternatives, List.mem_cons] at ruleMember
      rcases ruleMember with equal | inRest
      · subst rule
        exact denoteAlternative_concreteSyntax_valid category index alternative
          item itemMember
      · exact ih (index + 1) inRest

theorem generatedRuleLabel_lower_not_mem_denoteAlternatives
    (category : String) (alternatives : List Alternative)
    {lower index : Nat} (less : lower < index) :
    generatedRuleLabel category lower ∉
      (denoteAlternatives category alternatives index).map (·.label) := by
  induction alternatives generalizing index with
  | nil => simp [denoteAlternatives]
  | cons alternative rest ih =>
      simp only [denoteAlternatives, List.map_cons, List.mem_cons, not_or]
      constructor
      · intro equal
        have pairEqual : (category, lower) = (category, index) :=
          generatedRuleLabel_joint_injective equal
        have indexEqual := congrArg Prod.snd pairEqual
        omega
      · exact ih (by omega)

/-- Alternative occurrences within one source rule receive distinct labels. -/
theorem denoteAlternatives_labels_nodup
    (category : String) (alternatives : List Alternative) (index : Nat) :
    ((denoteAlternatives category alternatives index).map
      (·.label)).Nodup := by
  induction alternatives generalizing index with
  | nil => simp [denoteAlternatives]
  | cons alternative rest ih =>
      simp only [denoteAlternatives, List.map_cons, List.nodup_cons]
      exact ⟨generatedRuleLabel_lower_not_mem_denoteAlternatives
        category rest (by omega), ih (index + 1)⟩

/-- Recover the source category and occurrence index from every denoted
alternative label. -/
theorem decodeGeneratedRuleLabel_of_mem_denoteAlternatives
    (category : String) (alternatives : List Alternative) (start : Nat)
    {label : String}
    (member : label ∈
      (denoteAlternatives category alternatives start).map (·.label)) :
    ∃ index, decodeGeneratedRuleLabel label = some (category, index) := by
  induction alternatives generalizing start with
  | nil => simp [denoteAlternatives] at member
  | cons alternative rest ih =>
      simp only [denoteAlternatives, List.map_cons, List.mem_cons] at member
      rcases member with equal | inRest
      · subst label
        exact ⟨start, decodeGeneratedRuleLabel_generated category start⟩
      · exact ih (start + 1) inRest

/-- Flatten rule entries and their alternatives in source order.  Comments and
blank entries are retained by `Document` but have no grammar-rule denotation. -/
def denoteRules : List Entry -> List GrammarRule
  | [] => []
  | .rule category expression _ :: rest =>
      denoteAlternatives category expression.alternatives 0 ++ denoteRules rest
  | .comment _ _ :: rest => denoteRules rest
  | .blank _ :: rest => denoteRules rest

/-- Every generated parameter sort comes from an explicit source reference
in the complete document. -/
theorem referenceName_mem_of_parameter_type_mem_denoteRules
    (entries : List Entry) (rule : GrammarRule)
    (ruleMember : rule ∈ denoteRules entries)
    (parameter : TermParam) (parameterMember : parameter ∈ rule.params)
    (typeName : String)
    (typeNameMember :
      typeName ∈ (TermParam.typeExpr parameter).baseNames) :
    typeName ∈ entryReferenceNames entries := by
  induction entries with
  | nil => simp [denoteRules] at ruleMember
  | cons entry rest ih =>
      cases entry with
      | rule category expression span =>
          simp only [denoteRules, List.mem_append] at ruleMember
          rcases ruleMember with inCurrent | inRest
          · apply List.mem_append_left
            exact referenceName_mem_of_parameter_type_mem_denoteAlternatives
              category expression.alternatives 0 rule inCurrent parameter
              parameterMember typeName typeNameMember
          · apply List.mem_append_right expression.referenceNames
            exact ih inRest
      | comment text span =>
          simpa [entryReferenceNames, Entry.referenceNames, denoteRules] using
            ih ruleMember
      | blank span =>
          simpa [entryReferenceNames, Entry.referenceNames, denoteRules] using
            ih ruleMember

theorem denoteRules_concreteSyntax_valid
    (entries : List Entry) (rule : GrammarRule)
    (ruleMember : rule ∈ denoteRules entries)
    (item : SyntaxItem) (itemMember : item ∈ rule.syntaxPattern) :
    LanguageDef.concreteSyntaxItemAllowed
      (rule.params.flatMap fun parameter =>
        TermParam.bodyName parameter :: TermParam.binderNames parameter)
      item = true := by
  induction entries with
  | nil => simp [denoteRules] at ruleMember
  | cons entry rest ih =>
      cases entry with
      | rule category expression span =>
          simp only [denoteRules, List.mem_append] at ruleMember
          rcases ruleMember with inCurrent | inRest
          · exact denoteAlternatives_concreteSyntax_valid category
              expression.alternatives 0 rule inCurrent item itemMember
          · exact ih inRest
      | comment text span => exact ih (by simpa [denoteRules] using ruleMember)
      | blank span => exact ih (by simpa [denoteRules] using ruleMember)

def denoteRuleTypes : List Entry -> List TypeDecl
  | [] => []
  | .rule category _ _ :: rest =>
      { name := category, carrier := .ast } :: denoteRuleTypes rest
  | .comment _ _ :: rest => denoteRuleTypes rest
  | .blank _ :: rest => denoteRuleTypes rest

def denoteLexicalTypes (declarations : List LexicalDeclaration) :
    List TypeDecl :=
  declarations.map fun declaration =>
    { name := declaration.referenceName, carrier := .ast }

def denoteLexicalClass (declaration : LexicalDeclaration) :
    LexicalClassDecl :=
  { name := declaration.className
    kind := match declaration.matcher with
      | .points scalars => .points scalars
      | .except excluded => .except excluded }

def denoteLexicalState (declaration : LexicalDeclaration) :
    LexicalStateDecl :=
  { resultSort := declaration.referenceName
    className := declaration.className
    ruleLabel := declaration.ruleLabel }

def denoteAlternativeOrigins (category : String) (ruleSpan : SourceSpan) :
    List Alternative -> Nat -> List GeneratedRuleOrigin
  | [], _ => []
  | alternative :: rest, index =>
      { label := generatedRuleLabel category index
        category := category
        ruleSpan := ruleSpan
        alternativeSpan := alternative.span } ::
      denoteAlternativeOrigins category ruleSpan rest (index + 1)

def denoteRuleOrigins : List Entry -> List GeneratedRuleOrigin
  | [] => []
  | .rule category expression ruleSpan :: rest =>
      denoteAlternativeOrigins category ruleSpan expression.alternatives 0 ++
        denoteRuleOrigins rest
  | .comment _ _ :: rest => denoteRuleOrigins rest
  | .blank _ :: rest => denoteRuleOrigins rest

def denoteLexicalOrigin (declaration : LexicalDeclaration) :
    GeneratedLexicalOrigin :=
  { resultSort := declaration.referenceName
    className := declaration.className
    ruleLabel := declaration.ruleLabel
    matcher := declaration.matcher
    source := declaration.origin }

/-- Total denotation of already structured data.  Admission is intentionally
not folded into this function: successful validation supplies the document and
authority, while this function states what their denotation is. -/
def denote (document : Document) (authority : GrammarAuthority) : Candidate :=
  { language := {
      name := "PlainBnfDenotedSyntaxV1"
      types := denoteRuleTypes document.entries ++
        denoteLexicalTypes authority.lexicalDeclarations
      terms := denoteRules document.entries
      equations := []
      rewrites := [] }
    profile := {
      name := "PlainBnfDenotedParserV1"
      startSort := authority.startName
      classes := authority.lexicalDeclarations.map denoteLexicalClass
      states := authority.lexicalDeclarations.map denoteLexicalState }
    origins := {
      rules := denoteRuleOrigins document.entries
      lexical := authority.lexicalDeclarations.map denoteLexicalOrigin } }

/-- The structural denotation never emits dangling concrete-syntax
nonterminals: every such item names a parameter generated for the same source
reference occurrence. -/
theorem denote_concreteSyntaxRowsValid
    (document : Document) (authority : GrammarAuthority) :
    LanguageDef.concreteSyntaxRowsValid
      (denote document authority).language = true := by
  unfold LanguageDef.concreteSyntaxRowsValid
  simp only [List.all_eq_true]
  intro rule ruleMember item itemMember
  exact denoteRules_concreteSyntax_valid document.entries rule ruleMember item
    itemMember

/-! ## Structural preservation laws -/

def Entry.alternativeCount : Entry -> Nat
  | .rule _ expression _ => expression.alternatives.length
  | .comment _ _ | .blank _ => 0

theorem denoteAlternatives_length (category : String)
    (alternatives : List Alternative) (index : Nat) :
    (denoteAlternatives category alternatives index).length =
      alternatives.length := by
  induction alternatives generalizing index with
  | nil => rfl
  | cons alternative rest ih =>
      simp [denoteAlternatives, ih]

theorem denoteAlternativeOrigins_length (category : String)
    (ruleSpan : SourceSpan) (alternatives : List Alternative) (index : Nat) :
    (denoteAlternativeOrigins category ruleSpan alternatives index).length =
      alternatives.length := by
  induction alternatives generalizing index with
  | nil => rfl
  | cons alternative rest ih =>
      simp [denoteAlternativeOrigins, ih]

/-- Every source alternative contributes exactly one target constructor.
Neither identical alternatives nor identical terminal sequences are collapsed. -/
theorem denoteRules_length (entries : List Entry) :
    (denoteRules entries).length =
      (entries.map Entry.alternativeCount).sum := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      cases entry with
      | rule category expression span =>
          simp [denoteRules, Entry.alternativeCount,
            denoteAlternatives_length, ih]
      | comment text span =>
          simp [denoteRules, Entry.alternativeCount, ih]
      | blank span =>
          simp [denoteRules, Entry.alternativeCount, ih]

theorem denoteRuleOrigins_length (entries : List Entry) :
    (denoteRuleOrigins entries).length =
      (entries.map Entry.alternativeCount).sum := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      cases entry with
      | rule category expression span =>
          simp [denoteRuleOrigins, Entry.alternativeCount,
            denoteAlternativeOrigins_length, ih]
      | comment text span =>
          simp [denoteRuleOrigins, Entry.alternativeCount, ih]
      | blank span =>
          simp [denoteRuleOrigins, Entry.alternativeCount, ih]

def GrammarRule.originKey (rule : GrammarRule) : String × String :=
  (rule.label, rule.category)

def GeneratedRuleOrigin.key (origin : GeneratedRuleOrigin) : String × String :=
  (origin.label, origin.category)

/-- Alternative denotation and origin emission use the same occurrence index,
so generated labels and result categories align position by position. -/
theorem denoteAlternatives_originKeys (category : String)
    (ruleSpan : SourceSpan) (alternatives : List Alternative) (index : Nat) :
    (denoteAlternatives category alternatives index).map GrammarRule.originKey =
      (denoteAlternativeOrigins category ruleSpan alternatives index).map
        GeneratedRuleOrigin.key := by
  induction alternatives generalizing index with
  | nil => rfl
  | cons alternative rest ih =>
      simp [denoteAlternatives, denoteAlternativeOrigins,
        denoteAlternative, GrammarRule.originKey,
        GeneratedRuleOrigin.key, ih]

/-- Rule constructors and proof-relevant origins correspond one-for-one in
the complete flattened source order. -/
theorem denoteRules_originKeys (entries : List Entry) :
    (denoteRules entries).map GrammarRule.originKey =
      (denoteRuleOrigins entries).map GeneratedRuleOrigin.key := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      cases entry with
      | rule category expression span =>
          simp only [denoteRules, denoteRuleOrigins, List.map_append]
          rw [denoteAlternatives_originKeys, ih]
      | comment text span =>
          simp [denoteRules, denoteRuleOrigins, ih]
      | blank span =>
          simp [denoteRules, denoteRuleOrigins, ih]

theorem denoteRules_length_eq_origin_length (entries : List Entry) :
    (denoteRules entries).length = (denoteRuleOrigins entries).length := by
  rw [denoteRules_length, denoteRuleOrigins_length]

def Entry.ruleName? : Entry -> Option String
  | .rule name _ _ => some name
  | .comment _ _ | .blank _ => none

theorem category_eq_of_mem_denoteAlternatives
    (category : String) (alternatives : List Alternative) (index : Nat)
    {rule : GrammarRule}
    (member : rule ∈ denoteAlternatives category alternatives index) :
    rule.category = category := by
  induction alternatives generalizing index with
  | nil => simp [denoteAlternatives] at member
  | cons alternative rest ih =>
      simp only [denoteAlternatives, List.mem_cons] at member
      rcases member with equal | inRest
      · subst rule
        rfl
      · exact ih (index + 1) inRest

/-- Every denoted constructor returns the sort declared by its source rule
occurrence. -/
theorem category_mem_ruleNames_of_mem_denoteRules
    (entries : List Entry) {rule : GrammarRule}
    (member : rule ∈ denoteRules entries) :
    rule.category ∈ entries.filterMap Entry.ruleName? := by
  induction entries with
  | nil => simp [denoteRules] at member
  | cons entry rest ih =>
      cases entry with
      | rule category expression span =>
          simp only [denoteRules, List.mem_append] at member
          rcases member with inCurrent | inRest
          · have categoryEqual := category_eq_of_mem_denoteAlternatives
              category expression.alternatives 0 inCurrent
            simp [Entry.ruleName?, categoryEqual]
          · simp only [List.filterMap_cons, Entry.ruleName?, List.mem_cons]
            exact Or.inr (ih inRest)
      | comment text span =>
          simpa [denoteRules, Entry.ruleName?] using ih member
      | blank span =>
          simpa [denoteRules, Entry.ruleName?] using ih member

/-- Every denoted constructor label decodes to a category that occurs as an
authored rule name. -/
theorem decodeGeneratedRuleLabel_of_mem_denoteRules
    (entries : List Entry) {label : String}
    (member : label ∈ (denoteRules entries).map (·.label)) :
    ∃ category index,
      category ∈ entries.filterMap Entry.ruleName? ∧
        decodeGeneratedRuleLabel label = some (category, index) := by
  induction entries with
  | nil => simp [denoteRules] at member
  | cons entry rest ih =>
      cases entry with
      | rule category expression span =>
          simp only [denoteRules, List.map_append, List.mem_append] at member
          rcases member with inCurrent | inRest
          · obtain ⟨index, decoded⟩ :=
              decodeGeneratedRuleLabel_of_mem_denoteAlternatives category
                expression.alternatives 0 inCurrent
            exact ⟨category, index, by simp [Entry.ruleName?], decoded⟩
          · obtain ⟨sourceCategory, index, sourceMember, decoded⟩ := ih inRest
            have extended :
                sourceCategory ∈
                  (Entry.rule category expression span :: rest).filterMap
                    Entry.ruleName? := by
              simp only [List.filterMap_cons, Entry.ruleName?, List.mem_cons]
              exact Or.inr sourceMember
            exact ⟨sourceCategory, index, extended, decoded⟩
      | comment text span =>
          exact ih (by simpa [denoteRules] using member)
      | blank span =>
          exact ih (by simpa [denoteRules] using member)

/-- Duplicate-free source rule names and occurrence indexing jointly imply
duplicate-free generated constructor labels. -/
theorem denoteRules_labels_nodup
    (entries : List Entry)
    (namesNodup : (entries.filterMap Entry.ruleName?).Nodup) :
    ((denoteRules entries).map (·.label)).Nodup := by
  induction entries with
  | nil => simp [denoteRules]
  | cons entry rest ih =>
      cases entry with
      | comment text span =>
          apply ih
          simpa [Entry.ruleName?] using namesNodup
      | blank span =>
          apply ih
          simpa [Entry.ruleName?] using namesNodup
      | rule category expression span =>
          have separated :
              category ∉ rest.filterMap Entry.ruleName? ∧
                (rest.filterMap Entry.ruleName?).Nodup := by
            simpa [Entry.ruleName?] using namesNodup
          rw [denoteRules, List.map_append]
          apply List.nodup_append'.mpr
          refine ⟨denoteAlternatives_labels_nodup category
              expression.alternatives 0,
            ih separated.2, ?_⟩
          rw [List.disjoint_left]
          intro label inCurrent inRest
          obtain ⟨currentIndex, currentDecoded⟩ :=
            decodeGeneratedRuleLabel_of_mem_denoteAlternatives category
              expression.alternatives 0 inCurrent
          obtain ⟨restCategory, restIndex, restCategoryMember,
              restDecoded⟩ :=
            decodeGeneratedRuleLabel_of_mem_denoteRules rest inRest
          rw [currentDecoded] at restDecoded
          have pairEqual : (category, currentIndex) =
              (restCategory, restIndex) := by
            injection restDecoded
          have categoryEqual : category = restCategory :=
            congrArg Prod.fst pairEqual
          exact separated.1 (categoryEqual ▸ restCategoryMember)

/-- The rule-type half of denotation is exactly the source rule-name
projection, including its list order and any repeated names supplied to this
total fold.  Rejection of duplicate definitions belongs to admission. -/
theorem denoteRuleTypes_names (entries : List Entry) :
    (denoteRuleTypes entries).map TypeDecl.name =
      entries.filterMap Entry.ruleName? := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      cases entry with
      | rule category expression span =>
          simp [denoteRuleTypes, Entry.ruleName?, ih]
      | comment text span =>
          simp [denoteRuleTypes, Entry.ruleName?, ih]
      | blank span =>
          simp [denoteRuleTypes, Entry.ruleName?, ih]

/-- Type declaration order is the source rule order followed by the authored
lexical declaration order.  No set conversion occurs. -/
theorem denote_type_names (document : Document)
    (authority : GrammarAuthority) :
    (denote document authority).language.types.map TypeDecl.name =
      document.entries.filterMap Entry.ruleName? ++
        authority.lexicalDeclarations.map (·.referenceName) := by
  simp [denote, denoteLexicalTypes, denoteRuleTypes_names]

/-- Lexical class and state lists have exactly the authored declaration
multiplicity; duplicate-looking declarations are not silently erased here. -/
theorem denote_lexical_lengths (document : Document)
    (authority : GrammarAuthority) :
    (denote document authority).profile.classes.length =
        authority.lexicalDeclarations.length ∧
      (denote document authority).profile.states.length =
        authority.lexicalDeclarations.length ∧
      (denote document authority).origins.lexical.length =
        authority.lexicalDeclarations.length := by
  simp [denote]

/-! ## Positive and negative multiplicity controls -/

private def zeroSpan : SourceSpan := { start := 0, stop := 0 }

private def duplicateAlternative : Alternative :=
  { elements := [.literal "x" zeroSpan]
    span := zeroSpan }

private def ambiguousDocument : Document :=
  { entries := [
      .rule "ambiguous"
        { alternatives := [duplicateAlternative, duplicateAlternative]
          span := zeroSpan }
        zeroSpan]
    span := zeroSpan }

private def emptyAuthority : GrammarAuthority :=
  { startName := "ambiguous", lexicalDeclarations := [] }

/-- Positive control: equal-looking alternatives remain two ordered constructor
occurrences with distinct generated labels and identical source syntax. -/
theorem duplicate_alternatives_preserve_multiplicity :
    let rules := (denote ambiguousDocument emptyAuthority).language.terms
    rules.length = 2 ∧
      rules.map (·.label) = ["ambiguous#", "ambiguous#x"] ∧
      rules.map (·.category) = ["ambiguous", "ambiguous"] ∧
      rules.map (·.syntaxPattern) =
        [[.terminal "x"], [.terminal "x"]] := by
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · rfl
  · rfl

/-- Negative control: the two occurrences are not interchangeable records even
though their categories and recognized terminal strings agree. -/
theorem duplicate_alternatives_are_not_one_rule :
    let rules := (denote ambiguousDocument emptyAuthority).language.terms
    rules[0]? ≠ rules[1]? := by
  decide

#print axioms denoteAlternatives_length
#print axioms decodeGeneratedRuleLabel_generated
#print axioms generatedRuleLabel_joint_injective
#print axioms decodeGeneratedRuleLabel_rejects_missing_delimiter
#print axioms generatedParameterName_injective
#print axioms denoteReferenceBindings_sorts
#print axioms denoteParameters_baseNames
#print axioms denoteParameters_boundNames
#print axioms generatedParameterName_lower_not_mem
#print axioms denoteReferenceBinding_names_nodup
#print axioms denoteSyntax_allowed_by_bindings
#print axioms referenceName_mem_of_parameter_type_mem_denoteRules
#print axioms denoteRules_concreteSyntax_valid
#print axioms denote_concreteSyntaxRowsValid
#print axioms denoteAlternativeOrigins_length
#print axioms denoteRules_length
#print axioms denoteRuleOrigins_length
#print axioms denoteAlternatives_labels_nodup
#print axioms decodeGeneratedRuleLabel_of_mem_denoteRules
#print axioms denoteRules_labels_nodup
#print axioms denoteAlternatives_originKeys
#print axioms denoteRules_originKeys
#print axioms denoteRules_length_eq_origin_length
#print axioms denoteRuleTypes_names
#print axioms denote_type_names
#print axioms denote_lexical_lengths
#print axioms duplicate_alternatives_preserve_multiplicity
#print axioms duplicate_alternatives_are_not_one_rule

end Mettapedia.GSLT.Parsing.PlainBnfStructuredDenotation
