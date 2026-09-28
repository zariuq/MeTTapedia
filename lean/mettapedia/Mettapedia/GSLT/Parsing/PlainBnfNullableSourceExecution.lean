import Mettapedia.GSLT.Parsing.PlainBnfReferenceCollectionSourceExecution
import Mettapedia.GSLT.Parsing.PlainBnfKnownNamesSourceExecution
import Mettapedia.GSLT.Parsing.PlainBnfGraphSemantics
import Mettapedia.GSLT.Parsing.PlainBnfReadinessEnvironment

/-!
# Authored nullable-expression execution

The selected seventeen graph-source rules execute over the existing
source-spanned String expression carrier, known-name trie/history, and lexical
lookup. Known-name lookup has priority over lexical lookup. Boolean totality
uses the explicit known-index validity invariant; arbitrary stored payloads
are not silently repaired into the queried name. This is source-contextual
execution, not generated or native-runtime correspondence.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfNullableSourceExecution

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT (Rewrite decodeList)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open SourceSExprPatternCodec (encode encodeList)
open SourceSExprPatternInstantiation (pattern patternList
  applyRuleBindings_of_binderFree binderFree_pattern)
open PlainBnfStructuredDenotation (SourceSpan Element Alternative Expression LexicalDeclaration)
open PlainBnfGraphNameTrie (Trie)
open PlainBnfTrieSourceExecution (scalarRelations call result observedRule result_injective)
open PlainBnfReferenceCollectionSourceExecution
  (text span element elements alternative alternatives expression declarations firstDeclaration lookupResult)
open PlainBnfKnownNamesSourceExecution (known Valid nameResult)
open PlainBnfIndexedCollectorSourceExecution
  (headedBy premiseClosed closed_extension disjoint_heads_do_not_match)
open PlainBnfReadinessEnvironment
  (knownHeads known_heads known_closed lexicalLookupHeads lexical_lookup_heads lexical_lookup_closed)
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

def mode? (relation : String) : Option (Nat × Nat) :=
  match relation with
  | "BNFExpressionNullableV1" | "BNFAlternativesNullableV1" | "BNFAlternativeNullableV1" |
    "BNFElementsNullableV1" | "BNFElementNullableV1" | "BNFNullableReferenceAfterLookupV1" => some (3, 1)
  | "BNFAlternativesNullableAfterHeadV1" | "BNFElementsNullableAfterHeadV1" => some (4, 1)
  | "BNFNullableReferenceAfterLexicalLookupV1" => some (1, 1)
  | _ => (PlainBnfKnownNamesSourceExecution.mode? relation).or
      (PlainBnfReferenceCollectionSourceExecution.mode? relation)

def splitCall? : SExpr → Option (SExpr × SExpr)
  | .list (.atom relation :: arguments) => do
      let (inputs, outputs) ← mode? relation
      if arguments.length = inputs + outputs then
        some (.list (.atom relation :: arguments.take inputs), .list (arguments.drop inputs))
      else none
  | _ => none

def lowerPremise? : SExpr → Option Premise
  | .list [.atom "different", left, right] =>
      some (.relationQuery "different" [pattern left, pattern right])
  | source => do
      let (input, output) ← splitCall? source
      some (.congruence (pattern input) (pattern output))

def lowerRule? (source : Rewrite) : Option RewriteRule := do
  let (input, output) ← splitCall? source.head
  let premises ← decodeList lowerPremise? source.body
  some {
    name := source.name
    typeContext := []
    premises := premises
    left := pattern input
    right := pattern output }

def nullableRows : List Rewrite := (PlainBnfReferenceSourceAdmission.graphSource.rewrites.drop 64).take 17
def rows : List Rewrite := PlainBnfKnownNamesSourceExecution.rows ++
  PlainBnfReferenceCollectionSourceExecution.lookupRows ++ nullableRows
def rules? : Option (List RewriteRule) := rows.mapM lowerRule?
theorem rules_present : rules?.isSome = true := rfl
def nullableRules : List RewriteRule := (nullableRows.mapM lowerRule?).get (by rfl)
def language : LanguageDef :=
  { name := "PlainBnfAuthoredNullableExpression", types := [], terms := [], equations := [],
    rewrites := rules?.get rules_present }

theorem source_translation_exact : rows.mapM lowerRule? = some language.rewrites := rfl
theorem source_occurrences_exact : nullableRows.zipIdx 64 =
    ((PlainBnfReferenceSourceAdmission.graphSource.rewrites.zipIdx).drop 64).take 17 := rfl
theorem language_partition : language.rewrites = PlainBnfKnownNamesSourceExecution.language.rewrites ++
    PlainBnfReferenceCollectionSourceExecution.lookupLanguage.rewrites ++ nullableRules := rfl
theorem exactly_forty_one_rules : language.rewrites.length = 41 := rfl

/-- Displayed proof observations; the executable rules come from actual rows. -/
private def observed (name : String) (input output : SExpr) (body : List SExpr := []) : RewriteRule :=
  { name, typeContext := [], premises := (body.mapM lowerPremise?).getD [],
    left := pattern input, right := pattern output }

private def observedRules : List RewriteRule := [
  observed "bnf-expression-nullable-v1"
    (metta_sexpr% petta "(BNFExpressionNullableV1 (bnf-v1:expression ?alternatives ?span) ?nullable ?lexicals)")
    (metta_sexpr% petta "(?result)")
    [metta_sexpr% petta "(BNFAlternativesNullableV1 ?alternatives ?nullable ?lexicals ?result)"],
  observed "bnf-alternatives-nullable-nil-v1"
    (metta_sexpr% petta "(BNFAlternativesNullableV1 (metta-nullary bnf-v1:alternatives-nil) ?nullable ?lexicals)")
    (metta_sexpr% petta "(BNFNoV1)"),
  observed "bnf-alternatives-nullable-cons-v1"
    (metta_sexpr% petta "(BNFAlternativesNullableV1 (bnf-v1:alternatives-cons ?alternative ?tail) ?nullable ?lexicals)")
    (metta_sexpr% petta "(?result)")
    [metta_sexpr% petta "(BNFAlternativeNullableV1 ?alternative ?nullable ?lexicals ?headResult)",
     metta_sexpr% petta "(BNFAlternativesNullableAfterHeadV1 ?headResult ?tail ?nullable ?lexicals ?result)"],
  observed "bnf-alternatives-nullable-head-yes-v1"
    (metta_sexpr% petta "(BNFAlternativesNullableAfterHeadV1 BNFYesV1 ?tail ?nullable ?lexicals)")
    (metta_sexpr% petta "(BNFYesV1)"),
  observed "bnf-alternatives-nullable-head-no-v1"
    (metta_sexpr% petta "(BNFAlternativesNullableAfterHeadV1 BNFNoV1 ?tail ?nullable ?lexicals)")
    (metta_sexpr% petta "(?result)")
    [metta_sexpr% petta "(BNFAlternativesNullableV1 ?tail ?nullable ?lexicals ?result)"],
  observed "bnf-alternative-nullable-v1"
    (metta_sexpr% petta "(BNFAlternativeNullableV1 (bnf-v1:alternative ?elements ?span) ?nullable ?lexicals)")
    (metta_sexpr% petta "(?result)")
    [metta_sexpr% petta "(BNFElementsNullableV1 ?elements ?nullable ?lexicals ?result)"],
  observed "bnf-elements-nullable-nil-v1"
    (metta_sexpr% petta "(BNFElementsNullableV1 (metta-nullary bnf-v1:elements-nil) ?nullable ?lexicals)")
    (metta_sexpr% petta "(BNFYesV1)"),
  observed "bnf-elements-nullable-cons-v1"
    (metta_sexpr% petta "(BNFElementsNullableV1 (bnf-v1:elements-cons ?element ?tail) ?nullable ?lexicals)")
    (metta_sexpr% petta "(?result)")
    [metta_sexpr% petta "(BNFElementNullableV1 ?element ?nullable ?lexicals ?headResult)",
     metta_sexpr% petta "(BNFElementsNullableAfterHeadV1 ?headResult ?tail ?nullable ?lexicals ?result)"],
  observed "bnf-elements-nullable-head-no-v1"
    (metta_sexpr% petta "(BNFElementsNullableAfterHeadV1 BNFNoV1 ?tail ?nullable ?lexicals)")
    (metta_sexpr% petta "(BNFNoV1)"),
  observed "bnf-elements-nullable-head-yes-v1"
    (metta_sexpr% petta "(BNFElementsNullableAfterHeadV1 BNFYesV1 ?tail ?nullable ?lexicals)")
    (metta_sexpr% petta "(?result)")
    [metta_sexpr% petta "(BNFElementsNullableV1 ?tail ?nullable ?lexicals ?result)"],
  observed "bnf-empty-literal-nullable-v1"
    (metta_sexpr% petta "(BNFElementNullableV1 (bnf-v1:literal (metta-nullary bnf-v1:text-nil) ?span) ?nullable ?lexicals)")
    (metta_sexpr% petta "(BNFYesV1)"),
  observed "bnf-nonempty-literal-not-nullable-v1"
    (metta_sexpr% petta "(BNFElementNullableV1 (bnf-v1:literal (bnf-v1:text-cons ?head ?tail) ?span) ?nullable ?lexicals)")
    (metta_sexpr% petta "(BNFNoV1)"),
  observed "bnf-reference-nullable-v1"
    (metta_sexpr% petta "(BNFElementNullableV1 (bnf-v1:reference ?name ?span) ?nullable ?lexicals)")
    (metta_sexpr% petta "(?result)")
    [metta_sexpr% petta "(BNFNameLookupV1 ?name ?nullable ?lookup)",
     metta_sexpr% petta "(BNFNullableReferenceAfterLookupV1 ?name ?lookup ?lexicals ?result)"],
  observed "bnf-nullable-reference-found-v1"
    (metta_sexpr% petta "(BNFNullableReferenceAfterLookupV1 ?name (BNFNameFoundV1 ?name) ?lexicals)")
    (metta_sexpr% petta "(BNFYesV1)"),
  observed "bnf-nullable-reference-missing-v1"
    (metta_sexpr% petta "(BNFNullableReferenceAfterLookupV1 ?name BNFNameMissingV1 ?lexicals)")
    (metta_sexpr% petta "(?result)")
    [metta_sexpr% petta "(BNFLexicalReferenceLookupV1 ?name ?lexicals ?lexicalLookup)",
     metta_sexpr% petta "(BNFNullableReferenceAfterLexicalLookupV1 ?lexicalLookup ?result)"],
  observed "bnf-lexical-reference-not-nullable-v1"
    (metta_sexpr% petta "(BNFNullableReferenceAfterLexicalLookupV1 (BNFLexicalFoundV1 ?declaration))")
    (metta_sexpr% petta "(BNFNoV1)"),
  observed "bnf-unknown-reference-not-nullable-v1"
    (metta_sexpr% petta "(BNFNullableReferenceAfterLexicalLookupV1 BNFLexicalMissingV1)")
    (metta_sexpr% petta "(BNFNoV1)")]

private theorem rules_exact : nullableRules = observedRules := rfl

def nullableHeads := ["BNFExpressionNullableV1", "BNFAlternativesNullableV1", "BNFAlternativeNullableV1",
  "BNFElementsNullableV1", "BNFElementNullableV1", "BNFAlternativesNullableAfterHeadV1",
  "BNFElementsNullableAfterHeadV1", "BNFNullableReferenceAfterLookupV1",
  "BNFNullableReferenceAfterLexicalLookupV1"]

theorem nullable_heads : nullableRules.all (fun rule => headedBy nullableHeads rule.left) = true := by
  simp [rules_exact, observedRules, observed, headedBy, nullableHeads, pattern, patternList,
    encode, SourceIntegerProvider.sourceVariableToken]

def relationHeads := knownHeads ++ lexicalLookupHeads ++ nullableHeads

theorem family_heads : language.rewrites.all (fun rule => headedBy relationHeads rule.left) = true := by
  apply List.all_eq_true.mpr
  intro rule member
  simp only [language_partition, List.mem_append] at member
  rcases member with (member | member) | member
  · exact PlainBnfReadinessEnvironment.headedBy_mono knownHeads relationHeads
      (by intro name present; simp [relationHeads, present]) _
      (List.all_eq_true.mp known_heads rule member)
  · exact PlainBnfReadinessEnvironment.headedBy_mono lexicalLookupHeads relationHeads
      (by intro name present; simp [relationHeads, present]) _
      (List.all_eq_true.mp lexical_lookup_heads rule member)
  · exact PlainBnfReadinessEnvironment.headedBy_mono nullableHeads relationHeads
      (by intro name present; simp [relationHeads, present]) _
      (List.all_eq_true.mp nullable_heads rule member)

private theorem premiseClosed_mono (small large : List String) (included : small ⊆ large)
    (premise : Premise) (closed : premiseClosed small premise = true) :
    premiseClosed large premise = true := by
  cases premise with
  | congruence source _ =>
    exact PlainBnfReadinessEnvironment.headedBy_mono small large included source closed
  | scopedStep step =>
    simp only [premiseClosed, Bool.or_eq_true] at closed ⊢
    exact closed.imp id
      (PlainBnfReadinessEnvironment.headedBy_mono small large included step.source)
  | _ => rfl

theorem family_closed : language.rewrites.all
    (fun rule => rule.premises.all (premiseClosed relationHeads)) = true := by
  have localClosed : nullableRules.all
      (fun rule => rule.premises.all (premiseClosed relationHeads)) = true := by
    simp [rules_exact, observedRules, observed, lowerPremise?, splitCall?, mode?,
      PlainBnfKnownNamesSourceExecution.mode?, PlainBnfCollectorSourceExecution.mode?,
      PlainBnfReferenceCollectionSourceExecution.mode?, premiseClosed, headedBy,
      relationHeads, knownHeads, lexicalLookupHeads, nullableHeads,
      PlainBnfKnownNamesSourceExecution.knownNames, PlainBnfIndexedCollectorSourceExecution.trieNames,
      pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode]
  apply List.all_eq_true.mpr
  intro rule member
  apply List.all_eq_true.mpr
  intro premise present
  simp only [language_partition, List.mem_append] at member
  rcases member with (member | member) | member
  · exact premiseClosed_mono knownHeads relationHeads
      (by intro name found; simp [relationHeads, found]) _
      (List.all_eq_true.mp (List.all_eq_true.mp known_closed rule member) premise present)
  · exact premiseClosed_mono lexicalLookupHeads relationHeads
      (by intro name found; simp [relationHeads, found]) _
      (List.all_eq_true.mp (List.all_eq_true.mp lexical_lookup_closed rule member) premise present)
  · exact List.all_eq_true.mp (List.all_eq_true.mp localClosed rule member) premise present

theorem family_queries : language.rewrites.all
    (fun rule => rule.premises.all (PlainBnfReadinessEnvironment.queriesOnly ["different"])) = true := rfl

private theorem known_names_disjoint : List.Disjoint (lexicalLookupHeads ++ nullableHeads) knownHeads := by
  simp [lexicalLookupHeads, nullableHeads, knownHeads, PlainBnfKnownNamesSourceExecution.knownNames,
    PlainBnfIndexedCollectorSourceExecution.trieNames]

private theorem lexical_names_disjoint : List.Disjoint (knownHeads ++ nullableHeads) lexicalLookupHeads := by
  simp [lexicalLookupHeads, nullableHeads, knownHeads, PlainBnfKnownNamesSourceExecution.knownNames,
    PlainBnfIndexedCollectorSourceExecution.trieNames]

theorem known_conservative_extension (fuel : Nat) (source : Pattern)
    (headed : headedBy knownHeads source = true) :
    rewriteAt (engineBasePremises scalarRelations) language fuel source =
      rewriteAt (engineBasePremises scalarRelations) PlainBnfKnownNamesSourceExecution.language fuel source := by
  apply closed_extension knownHeads scalarRelations _ _ []
    (PlainBnfReferenceCollectionSourceExecution.lookupLanguage.rewrites ++ nullableRules)
  · simpa [List.append_assoc] using language_partition
  · intro rule member premise present
    exact List.all_eq_true.mp (List.all_eq_true.mp known_closed rule member) premise present
  · intro rule member input inputHead
    simp only [List.nil_append, List.mem_append] at member
    rcases member with member | member
    · exact disjoint_heads_do_not_match lexicalLookupHeads knownHeads
        (List.disjoint_append_left.mp known_names_disjoint).1 _ _
        (List.all_eq_true.mp lexical_lookup_heads rule member) inputHead
    · exact disjoint_heads_do_not_match nullableHeads knownHeads
        (List.disjoint_append_left.mp known_names_disjoint).2 _ _
        (List.all_eq_true.mp nullable_heads rule member) inputHead
  · exact headed

theorem lexical_conservative_extension (fuel : Nat) (source : Pattern)
    (headed : headedBy lexicalLookupHeads source = true) :
    rewriteAt (engineBasePremises scalarRelations) language fuel source =
      rewriteAt (engineBasePremises scalarRelations) PlainBnfReferenceCollectionSourceExecution.lookupLanguage fuel source := by
  apply closed_extension lexicalLookupHeads scalarRelations _ _
    PlainBnfKnownNamesSourceExecution.language.rewrites nullableRules
  · exact language_partition
  · intro rule member premise present
    exact List.all_eq_true.mp (List.all_eq_true.mp lexical_lookup_closed rule member) premise present
  · intro rule member input inputHead
    rcases List.mem_append.mp member with member | member
    · exact disjoint_heads_do_not_match knownHeads lexicalLookupHeads
        (List.disjoint_append_left.mp lexical_names_disjoint).1 _ _
        (List.all_eq_true.mp known_heads rule member) inputHead
    · exact disjoint_heads_do_not_match nullableHeads lexicalLookupHeads
        (List.disjoint_append_left.mp lexical_names_disjoint).2 _ _
        (List.all_eq_true.mp nullable_heads rule member) inputHead
  · exact headed

private theorem nullable_rewriteAt (fuel : Nat) (source : Pattern)
    (headed : headedBy nullableHeads source = true) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1) source =
      nullableRules.flatMap (fun rule => applyRuleUsing (engineBasePremises scalarRelations) language
        (rewriteAt (engineBasePremises scalarRelations) language fuel) rule source) := by
  apply PlainBnfHeapSourceExecution.skip_unmatched_prefix _ language
    (PlainBnfKnownNamesSourceExecution.language.rewrites ++
      PlainBnfReferenceCollectionSourceExecution.lookupLanguage.rewrites) nullableRules language_partition fuel source
  intro rule member
  rcases List.mem_append.mp member with member | member
  · exact disjoint_heads_do_not_match knownHeads nullableHeads
      (List.disjoint_append_left.mp known_names_disjoint).2.symm _ _
      (List.all_eq_true.mp known_heads rule member) headed
  · exact disjoint_heads_do_not_match lexicalLookupHeads nullableHeads
      (List.disjoint_append_left.mp lexical_names_disjoint).2.symm _ _
      (List.all_eq_true.mp lexical_lookup_heads rule member) headed

def answer (value : Bool) : SExpr := .atom (if value then "BNFYesV1" else "BNFNoV1")
def keyScalars (key : String) : List Nat := key.toList.map Char.toNat
def isKnown (history : List SExpr) (key : String) : Bool := decide (text key ∈ history)

def elementMeaning (history : List SExpr) : Element → Bool
  | .literal value _ => value == ""
  | .reference key _ => isKnown history key
def elementsMeaning (history : List SExpr) (input : List Element) : Bool := input.all (elementMeaning history)
def alternativeMeaning (history : List SExpr) (input : Alternative) : Bool := elementsMeaning history input.elements
def alternativesMeaning (history : List SExpr) (input : List Alternative) : Bool := input.any (alternativeMeaning history)
def expressionMeaning (history : List SExpr) (input : Expression) : Bool := alternativesMeaning history input.alternatives

def expressionCall (input : Expression) (index : Trie SExpr Nat) (history : List SExpr)
    (lexicals : List LexicalDeclaration) : Pattern :=
  call "BNFExpressionNullableV1" [expression input, known index history, declarations lexicals]
def alternativesCall (input : List Alternative) (index : Trie SExpr Nat) (history : List SExpr)
    (lexicals : List LexicalDeclaration) : Pattern :=
  call "BNFAlternativesNullableV1" [alternatives input, known index history, declarations lexicals]
def afterAlternativesCall (head : Bool) (input : List Alternative) (index : Trie SExpr Nat)
    (history : List SExpr) (lexicals : List LexicalDeclaration) : Pattern :=
  call "BNFAlternativesNullableAfterHeadV1" [answer head, alternatives input, known index history, declarations lexicals]
def alternativeCall (input : Alternative) (index : Trie SExpr Nat) (history : List SExpr)
    (lexicals : List LexicalDeclaration) : Pattern :=
  call "BNFAlternativeNullableV1" [alternative input, known index history, declarations lexicals]
def elementsCall (input : List Element) (index : Trie SExpr Nat) (history : List SExpr)
    (lexicals : List LexicalDeclaration) : Pattern :=
  call "BNFElementsNullableV1" [elements input, known index history, declarations lexicals]
def afterElementsCall (head : Bool) (input : List Element) (index : Trie SExpr Nat)
    (history : List SExpr) (lexicals : List LexicalDeclaration) : Pattern :=
  call "BNFElementsNullableAfterHeadV1" [answer head, elements input, known index history, declarations lexicals]
def elementCall (input : Element) (index : Trie SExpr Nat) (history : List SExpr)
    (lexicals : List LexicalDeclaration) : Pattern :=
  call "BNFElementNullableV1" [element input, known index history, declarations lexicals]
def afterLookupCall (key : String) (found : Option SExpr) (lexicals : List LexicalDeclaration) : Pattern :=
  call "BNFNullableReferenceAfterLookupV1" [text key, nameResult found, declarations lexicals]
def afterLexicalCall (found : Option LexicalDeclaration) : Pattern :=
  call "BNFNullableReferenceAfterLexicalLookupV1" [lookupResult found]

theorem answer_injective : Function.Injective answer := by
  intro left right same
  cases left <;> cases right <;> simp_all [answer]

theorem result_answer_injective : Function.Injective (fun value => result (answer value)) := by
  intro left right same
  exact answer_injective (result_injective same)

theorem element_meaning_iff (history : List SExpr) (input : Element) :
    elementMeaning history input = true ↔
      PlainBnfGraphSemantics.ElementNullable {key | text key ∈ history} input := by
  cases input <;> simp [elementMeaning, isKnown, PlainBnfGraphSemantics.ElementNullable]

theorem alternative_meaning_iff (history : List SExpr) (input : Alternative) :
    alternativeMeaning history input = true ↔
      PlainBnfGraphSemantics.AlternativeNullable {key | text key ∈ history} input := by
  simp [alternativeMeaning, elementsMeaning, PlainBnfGraphSemantics.AlternativeNullable,
    element_meaning_iff]

theorem expression_meaning_iff (history : List SExpr) (input : Expression) :
    expressionMeaning history input = true ↔
      PlainBnfGraphSemantics.ExpressionNullable {key | text key ∈ history} input := by
  simp [expressionMeaning, alternativesMeaning, PlainBnfGraphSemantics.ExpressionNullable,
    alternative_meaning_iff]

/-- Contextual depth follows the actual ordered, short-circuit calls. Lexical
lookup is still executed on a missing known name, even though both lexical
outcomes are nonnullable. These bounds do not supply execution answers. -/
def afterLookupHeight (key : String) (present : Bool) (lexicals : List LexicalDeclaration) : Nat :=
  if present then 0 else PlainBnfReferenceCollectionSourceExecution.lookupHeight key lexicals + 1

def elementHeight (input : Element) (index : Trie SExpr Nat) (history : List SExpr)
    (lexicals : List LexicalDeclaration) : Nat :=
  match input with
  | .literal _ _ => 0
  | .reference key _ => max (PlainBnfTrieSourceExecution.lookupHeight (keyScalars key) index + 1)
      (afterLookupHeight key (isKnown history key) lexicals) + 1

def elementsHeight : List Element → Trie SExpr Nat → List SExpr → List LexicalDeclaration → Nat
  | [], _, _, _ => 0
  | head :: tail, index, history, lexicals =>
      max (elementHeight head index history lexicals)
        (if elementMeaning history head then elementsHeight tail index history lexicals + 1 else 0) + 1

def alternativeHeight (input : Alternative) (index : Trie SExpr Nat) (history : List SExpr)
    (lexicals : List LexicalDeclaration) : Nat := elementsHeight input.elements index history lexicals + 1

def alternativesHeight : List Alternative → Trie SExpr Nat → List SExpr → List LexicalDeclaration → Nat
  | [], _, _, _ => 0
  | head :: tail, index, history, lexicals =>
      max (alternativeHeight head index history lexicals)
        (if alternativeMeaning history head then 0 else alternativesHeight tail index history lexicals + 1) + 1

def expressionHeight (input : Expression) (index : Trie SExpr Nat) (history : List SExpr)
    (lexicals : List LexicalDeclaration) : Nat := alternativesHeight input.alternatives index history lexicals + 1

theorem known_lookup_valid_answers (fuel : Nat) (key : String) (index : Trie SExpr Nat)
    (history : List SExpr) (valid : Valid index history) :
    rewriteAt (engineBasePremises scalarRelations) language fuel
      (call "BNFNameLookupV1" [text key, known index history]) =
      if PlainBnfTrieSourceExecution.lookupHeight (keyScalars key) index + 1 < fuel then
        [result (nameResult (if isKnown history key then some (text key) else none))] else [] := by
  rw [known_conservative_extension fuel _ (by
    simp [call, encode, encodeList, headedBy, knownHeads,
      PlainBnfKnownNamesSourceExecution.knownNames, PlainBnfIndexedCollectorSourceExecution.trieNames])]
  change rewriteAt _ _ _ (PlainBnfKnownNamesSourceExecution.knownLookupCall (keyScalars key) index history) = _
  rw [PlainBnfKnownNamesSourceExecution.known_lookup_answers, valid]
  change (if PlainBnfTrieSourceExecution.lookupHeight (keyScalars key) index + 1 < fuel then
    [result (nameResult (if text key ∈ history then some (text key) else none))] else []) = _
  by_cases present : text key ∈ history <;> simp [isKnown, present]

theorem lexical_lookup_answers (fuel : Nat) (key : String) (lexicals : List LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) language fuel
      (PlainBnfReferenceCollectionSourceExecution.lookupCall key lexicals) =
      if PlainBnfReferenceCollectionSourceExecution.lookupHeight key lexicals < fuel then
        [result (lookupResult (firstDeclaration key lexicals))] else [] := by
  rw [lexical_conservative_extension fuel _ (by
    simp [PlainBnfReferenceCollectionSourceExecution.lookupCall, call, encode, encodeList,
      headedBy, lexicalLookupHeads])]
  exact PlainBnfReferenceCollectionSourceExecution.lookup_answers fuel key lexicals

theorem after_lexical_answers (fuel : Nat) (found : Option LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (afterLexicalCall found) =
      if 0 < fuel then [result (answer false)] else [] := by
  cases fuel with
  | zero => simp [rewriteAt]
  | succ fuel =>
    rw [nullable_rewriteAt fuel _ (by
      simp [afterLexicalCall, call, encode, encodeList, headedBy, nullableHeads])]
    cases found <;>
      simp [rules_exact, observedRules, observed, lowerPremise?, splitCall?, mode?,
        applyRuleUsing, afterLexicalCall, lookupResult, call, answer, result,
        applyRuleBindings_of_binderFree, binderFree, binderFreeList,
        pattern, patternList, SourceIntegerProvider.sourceVariableToken,
        encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
        premisesUsing, premiseStepUsing, applyBindings]

private theorem after_lookup_present (fuel : Nat) (key : String) (lexicals : List LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (afterLookupCall key (some (text key)) lexicals) = [result (answer true)] := by
  rw [nullable_rewriteAt fuel _ (by
    simp [afterLookupCall, call, encode, encodeList, headedBy, nullableHeads])]
  simp [rules_exact, observedRules, observed, lowerPremise?, splitCall?, mode?,
    applyRuleUsing, afterLookupCall, nameResult, call, answer, result,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, premiseStepUsing, applyBindings]

private theorem after_lookup_missing (fuel : Nat) (key : String) (lexicals : List LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (afterLookupCall key none lexicals) =
      if PlainBnfReferenceCollectionSourceExecution.lookupHeight key lexicals < fuel then
        [result (answer false)] else [] := by
  rw [nullable_rewriteAt fuel _ (by
    simp [afterLookupCall, call, encode, encodeList, headedBy, nullableHeads])]
  have queried := lexical_lookup_answers fuel key lexicals
  have finished := after_lexical_answers fuel (firstDeclaration key lexicals)
  simp [rules_exact, observedRules, observed, lowerPremise?, splitCall?, mode?,
    PlainBnfKnownNamesSourceExecution.mode?, PlainBnfCollectorSourceExecution.mode?,
    PlainBnfReferenceCollectionSourceExecution.mode?,
    applyRuleUsing, afterLookupCall, nameResult, call,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, premiseStepUsing, applyBindings]
  simp only [PlainBnfReferenceCollectionSourceExecution.lookupCall, call, encode, encodeList] at queried
  rw [queried]
  split
  · rename_i enough
    simp [result, encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]
    simp only [afterLexicalCall, call, encode, encodeList] at finished
    rw [finished]
    have positive : 0 < fuel := Nat.lt_of_le_of_lt (Nat.zero_le _) enough
    simp [positive, result, encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]
  · simp

theorem after_lookup_answers (fuel : Nat) (key : String) (present : Bool)
    (lexicals : List LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) language fuel
      (afterLookupCall key (if present then some (text key) else none) lexicals) =
      if afterLookupHeight key present lexicals < fuel then [result (answer present)] else [] := by
  cases fuel with
  | zero => simp [rewriteAt]
  | succ fuel =>
    cases present with
    | false => simpa [afterLookupHeight] using after_lookup_missing fuel key lexicals
    | true => simpa [afterLookupHeight] using after_lookup_present fuel key lexicals

private theorem literal_answers (fuel : Nat) (value : String) (location : SourceSpan)
    (index : Trie SExpr Nat) (history : List SExpr) (lexicals : List LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (elementCall (.literal value location) index history lexicals) =
      [result (answer (value == ""))] := by
  rw [nullable_rewriteAt fuel _ (by
    simp [elementCall, call, encode, encodeList, headedBy, nullableHeads])]
  cases chars : value.toList with
  | nil =>
    have empty : value = "" := String.toList_injective (by simpa using chars)
    subst value
    simp [rules_exact, observedRules, observed, lowerPremise?, splitCall?, mode?,
      applyRuleUsing, elementCall, element, text, PlainBnfCollectorSourceExecution.name,
      applyRuleBindings_of_binderFree, binderFree, binderFreeList,
      call, answer, result, pattern, patternList, SourceIntegerProvider.sourceVariableToken,
      encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
      premisesUsing, premiseStepUsing, applyBindings]
  | cons head tail =>
    have nonempty : value ≠ "" := by
      intro empty
      subst value
      simp at chars
    simp [rules_exact, observedRules, observed, lowerPremise?, splitCall?, mode?,
      applyRuleUsing, elementCall, element, text, chars, PlainBnfCollectorSourceExecution.name,
      applyRuleBindings_of_binderFree, binderFree, binderFreeList,
      call, answer, result, nonempty, pattern, patternList, SourceIntegerProvider.sourceVariableToken,
      encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
      premisesUsing, premiseStepUsing, applyBindings]

private theorem reference_answers (fuel : Nat) (key : String) (location : SourceSpan)
    (index : Trie SExpr Nat) (history : List SExpr) (lexicals : List LexicalDeclaration)
    (valid : Valid index history) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (elementCall (.reference key location) index history lexicals) =
      if PlainBnfTrieSourceExecution.lookupHeight (keyScalars key) index + 1 < fuel ∧
          afterLookupHeight key (isKnown history key) lexicals < fuel then
        [result (answer (isKnown history key))] else [] := by
  rw [nullable_rewriteAt fuel _ (by
    simp [elementCall, call, encode, encodeList, headedBy, nullableHeads])]
  have queried := known_lookup_valid_answers fuel key index history valid
  have finished := after_lookup_answers fuel key (isKnown history key) lexicals
  simp [rules_exact, observedRules, observed, lowerPremise?, splitCall?, mode?,
    PlainBnfKnownNamesSourceExecution.mode?,
    applyRuleUsing, elementCall, element, call, pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, premiseStepUsing, applyBindings]
  simp only [call, encode, encodeList] at queried
  rw [queried]
  split
  · rename_i queryEnough
    simp [result, encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]
    simp only [afterLookupCall, call, encode, encodeList] at finished
    rw [finished]
    by_cases afterEnough : afterLookupHeight key (isKnown history key) lexicals < fuel
    all_goals simp [afterEnough, queryEnough, result, encode, encodeList,
      matchPattern, matchArgs, mergeBindings, List.foldlM]
  · rename_i queryShort
    simp [queryShort]

theorem element_answers (fuel : Nat) (input : Element) (index : Trie SExpr Nat)
    (history : List SExpr) (lexicals : List LexicalDeclaration) (valid : Valid index history) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (elementCall input index history lexicals) =
      if elementHeight input index history lexicals < fuel then [result (answer (elementMeaning history input))] else [] := by
  cases fuel with
  | zero => simp [rewriteAt]
  | succ fuel =>
    cases input with
    | literal value location =>
      simpa [elementHeight, elementMeaning] using literal_answers fuel value location index history lexicals
    | reference key location =>
      simpa [elementHeight, elementMeaning] using reference_answers fuel key location index history lexicals valid

def afterElementsHeight (head : Bool) (input : List Element) (index : Trie SExpr Nat)
    (history : List SExpr) (lexicals : List LexicalDeclaration) : Nat :=
  if head then elementsHeight input index history lexicals + 1 else 0

theorem elements_pair_answers (fuel : Nat) (index : Trie SExpr Nat) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (valid : Valid index history) :
    (∀ input, rewriteAt (engineBasePremises scalarRelations) language fuel (elementsCall input index history lexicals) =
      if elementsHeight input index history lexicals < fuel then
        [result (answer (elementsMeaning history input))] else []) ∧
    (∀ head input, rewriteAt (engineBasePremises scalarRelations) language fuel
        (afterElementsCall head input index history lexicals) =
      if afterElementsHeight head input index history lexicals < fuel then
        [result (answer (head && elementsMeaning history input))] else []) := by
  induction fuel with
  | zero => constructor <;> intros <;> simp [rewriteAt]
  | succ fuel ih =>
    constructor
    · intro input
      rw [nullable_rewriteAt fuel _ (by
        simp [elementsCall, call, encode, encodeList, headedBy, nullableHeads])]
      cases input with
      | nil =>
        simp [rules_exact, observedRules, observed, lowerPremise?, splitCall?, mode?,
          applyRuleUsing, elementsCall, elements, elementsHeight, elementsMeaning, call, answer, result,
          applyRuleBindings_of_binderFree, binderFree, binderFreeList,
          pattern, patternList, SourceIntegerProvider.sourceVariableToken,
          encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
          premisesUsing, premiseStepUsing, applyBindings]
      | cons head tail =>
        have first := element_answers fuel head index history lexicals valid
        have following := ih.2 (elementMeaning history head) tail
        simp [rules_exact, observedRules, observed, lowerPremise?, splitCall?, mode?,
          applyRuleUsing, elementsCall, elements, call,
          applyRuleBindings_of_binderFree, binderFree, binderFreeList,
          pattern, patternList, SourceIntegerProvider.sourceVariableToken,
          encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
          premisesUsing, premiseStepUsing, applyBindings]
        simp only [elementCall, call, encode, encodeList] at first
        rw [first]
        split
        · rename_i firstEnough
          simp [result, encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]
          simp only [afterElementsCall, call, encode, encodeList] at following
          rw [following]
          split <;> simp_all [elementsHeight, afterElementsHeight, elementsMeaning, result,
            encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]
        · rename_i firstShort
          simp [elementsHeight, firstShort]
    · intro head input
      rw [nullable_rewriteAt fuel _ (by
        simp [afterElementsCall, call, encode, encodeList, headedBy, nullableHeads])]
      cases head with
      | false =>
        simp [rules_exact, observedRules, observed, lowerPremise?, splitCall?, mode?,
          applyRuleUsing, afterElementsCall, afterElementsHeight, call, answer, result,
          applyRuleBindings_of_binderFree, binderFree, binderFreeList,
          pattern, patternList, SourceIntegerProvider.sourceVariableToken,
          encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
          premisesUsing, premiseStepUsing, applyBindings]
      | true =>
        have recursive := ih.1 input
        simp [rules_exact, observedRules, observed, lowerPremise?, splitCall?, mode?,
          applyRuleUsing, afterElementsCall, call, answer,
          applyRuleBindings_of_binderFree, binderFree, binderFreeList,
          pattern, patternList, SourceIntegerProvider.sourceVariableToken,
          encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
          premisesUsing, premiseStepUsing, applyBindings]
        simp only [elementsCall, call, encode, encodeList] at recursive
        rw [recursive]
        split <;> simp_all [afterElementsHeight, answer, result, encode, encodeList,
          matchPattern, matchArgs, mergeBindings, List.foldlM]

theorem elements_answers (fuel : Nat) (input : List Element) (index : Trie SExpr Nat)
    (history : List SExpr) (lexicals : List LexicalDeclaration) (valid : Valid index history) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (elementsCall input index history lexicals) =
      if elementsHeight input index history lexicals < fuel then
        [result (answer (elementsMeaning history input))] else [] :=
  (elements_pair_answers fuel index history lexicals valid).1 input

theorem alternative_answers (fuel : Nat) (input : Alternative) (index : Trie SExpr Nat)
    (history : List SExpr) (lexicals : List LexicalDeclaration) (valid : Valid index history) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (alternativeCall input index history lexicals) =
      if alternativeHeight input index history lexicals < fuel then
        [result (answer (alternativeMeaning history input))] else [] := by
  cases fuel with
  | zero => simp [rewriteAt]
  | succ fuel =>
    rw [nullable_rewriteAt fuel _ (by
      simp [alternativeCall, call, encode, encodeList, headedBy, nullableHeads])]
    have recursive := elements_answers fuel input.elements index history lexicals valid
    simp [rules_exact, observedRules, observed, lowerPremise?, splitCall?, mode?,
      applyRuleUsing, alternativeCall, alternative, call,
      applyRuleBindings_of_binderFree, binderFree, binderFreeList,
      pattern, patternList, SourceIntegerProvider.sourceVariableToken,
      encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
      premisesUsing, premiseStepUsing, applyBindings]
    simp only [elementsCall, call, encode, encodeList] at recursive
    rw [recursive]
    split <;> simp_all [alternativeHeight, alternativeMeaning, result, encode, encodeList,
      matchPattern, matchArgs, mergeBindings, List.foldlM]

def afterAlternativesHeight (head : Bool) (input : List Alternative) (index : Trie SExpr Nat)
    (history : List SExpr) (lexicals : List LexicalDeclaration) : Nat :=
  if head then 0 else alternativesHeight input index history lexicals + 1

theorem alternatives_pair_answers (fuel : Nat) (index : Trie SExpr Nat) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (valid : Valid index history) :
    (∀ input, rewriteAt (engineBasePremises scalarRelations) language fuel (alternativesCall input index history lexicals) =
      if alternativesHeight input index history lexicals < fuel then
        [result (answer (alternativesMeaning history input))] else []) ∧
    (∀ head input, rewriteAt (engineBasePremises scalarRelations) language fuel
        (afterAlternativesCall head input index history lexicals) =
      if afterAlternativesHeight head input index history lexicals < fuel then
        [result (answer (head || alternativesMeaning history input))] else []) := by
  induction fuel with
  | zero => constructor <;> intros <;> simp [rewriteAt]
  | succ fuel ih =>
    constructor
    · intro input
      rw [nullable_rewriteAt fuel _ (by
        simp [alternativesCall, call, encode, encodeList, headedBy, nullableHeads])]
      cases input with
      | nil =>
        simp [rules_exact, observedRules, observed, lowerPremise?, splitCall?, mode?,
          applyRuleUsing, alternativesCall, alternatives, alternativesHeight, alternativesMeaning, call, answer, result,
          applyRuleBindings_of_binderFree, binderFree, binderFreeList,
          pattern, patternList, SourceIntegerProvider.sourceVariableToken,
          encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
          premisesUsing, premiseStepUsing, applyBindings]
      | cons head tail =>
        have first := alternative_answers fuel head index history lexicals valid
        have following := ih.2 (alternativeMeaning history head) tail
        simp [rules_exact, observedRules, observed, lowerPremise?, splitCall?, mode?,
          applyRuleUsing, alternativesCall, alternatives, call,
          applyRuleBindings_of_binderFree, binderFree, binderFreeList,
          pattern, patternList, SourceIntegerProvider.sourceVariableToken,
          encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
          premisesUsing, premiseStepUsing, applyBindings]
        simp only [alternativeCall, call, encode, encodeList] at first
        rw [first]
        split
        · rename_i firstEnough
          simp [result, encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]
          simp only [afterAlternativesCall, call, encode, encodeList] at following
          rw [following]
          split <;> simp_all [alternativesHeight, afterAlternativesHeight, alternativesMeaning, result,
            encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]
        · rename_i firstShort
          simp [alternativesHeight, firstShort]
    · intro head input
      rw [nullable_rewriteAt fuel _ (by
        simp [afterAlternativesCall, call, encode, encodeList, headedBy, nullableHeads])]
      cases head with
      | false =>
        have recursive := ih.1 input
        simp [rules_exact, observedRules, observed, lowerPremise?, splitCall?, mode?,
          applyRuleUsing, afterAlternativesCall, call, answer,
          applyRuleBindings_of_binderFree, binderFree, binderFreeList,
          pattern, patternList, SourceIntegerProvider.sourceVariableToken,
          encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
          premisesUsing, premiseStepUsing, applyBindings]
        simp only [alternativesCall, call, encode, encodeList] at recursive
        rw [recursive]
        split <;> simp_all [afterAlternativesHeight, answer, result, encode, encodeList,
          matchPattern, matchArgs, mergeBindings, List.foldlM]
      | true =>
        simp [rules_exact, observedRules, observed, lowerPremise?, splitCall?, mode?,
          applyRuleUsing, afterAlternativesCall, afterAlternativesHeight, call, answer, result,
          applyRuleBindings_of_binderFree, binderFree, binderFreeList,
          pattern, patternList, SourceIntegerProvider.sourceVariableToken,
          encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
          premisesUsing, premiseStepUsing, applyBindings]

theorem alternatives_answers (fuel : Nat) (input : List Alternative) (index : Trie SExpr Nat)
    (history : List SExpr) (lexicals : List LexicalDeclaration) (valid : Valid index history) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (alternativesCall input index history lexicals) =
      if alternativesHeight input index history lexicals < fuel then
        [result (answer (alternativesMeaning history input))] else [] :=
  (alternatives_pair_answers fuel index history lexicals valid).1 input

theorem expression_answers (fuel : Nat) (input : Expression) (index : Trie SExpr Nat)
    (history : List SExpr) (lexicals : List LexicalDeclaration) (valid : Valid index history) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (expressionCall input index history lexicals) =
      if expressionHeight input index history lexicals < fuel then
        [result (answer (expressionMeaning history input))] else [] := by
  cases fuel with
  | zero => simp [rewriteAt]
  | succ fuel =>
    rw [nullable_rewriteAt fuel _ (by
      simp [expressionCall, call, encode, encodeList, headedBy, nullableHeads])]
    have recursive := alternatives_answers fuel input.alternatives index history lexicals valid
    simp [rules_exact, observedRules, observed, lowerPremise?, splitCall?, mode?,
      applyRuleUsing, expressionCall, expression, call,
      applyRuleBindings_of_binderFree, binderFree, binderFreeList,
      pattern, patternList, SourceIntegerProvider.sourceVariableToken,
      encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
      premisesUsing, premiseStepUsing, applyBindings]
    simp only [alternativesCall, call, encode, encodeList] at recursive
    rw [recursive]
    split <;> simp_all [expressionHeight, expressionMeaning, result, encode, encodeList,
      matchPattern, matchArgs, mergeBindings, List.foldlM]

private theorem step_of_exact_answers (source : Pattern) (value : Bool) (height : Nat)
    (answers : ∀ fuel, rewriteAt (engineBasePremises scalarRelations) language fuel source =
      if height < fuel then [result (answer value)] else []) (target : Pattern) :
    Step (engineBasePremises scalarRelations) language source target ↔
      target = result (answer value) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [answers] at member
    split at member
    · simpa using member
    · cases member
  · rintro rfl
    exact ⟨height + 1, by simp [answers]⟩

theorem element_step_iff (input : Element) (index : Trie SExpr Nat) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (valid : Valid index history) (target : Pattern) :
    Step (engineBasePremises scalarRelations) language (elementCall input index history lexicals) target ↔
      target = result (answer (elementMeaning history input)) :=
  step_of_exact_answers _ _ _ (fun fuel => element_answers fuel input index history lexicals valid) target

theorem elements_step_iff (input : List Element) (index : Trie SExpr Nat) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (valid : Valid index history) (target : Pattern) :
    Step (engineBasePremises scalarRelations) language (elementsCall input index history lexicals) target ↔
      target = result (answer (elementsMeaning history input)) :=
  step_of_exact_answers _ _ _ (fun fuel => elements_answers fuel input index history lexicals valid) target

theorem alternative_step_iff (input : Alternative) (index : Trie SExpr Nat) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (valid : Valid index history) (target : Pattern) :
    Step (engineBasePremises scalarRelations) language (alternativeCall input index history lexicals) target ↔
      target = result (answer (alternativeMeaning history input)) :=
  step_of_exact_answers _ _ _ (fun fuel => alternative_answers fuel input index history lexicals valid) target

theorem alternatives_step_iff (input : List Alternative) (index : Trie SExpr Nat) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (valid : Valid index history) (target : Pattern) :
    Step (engineBasePremises scalarRelations) language (alternativesCall input index history lexicals) target ↔
      target = result (answer (alternativesMeaning history input)) :=
  step_of_exact_answers _ _ _ (fun fuel => alternatives_answers fuel input index history lexicals valid) target

theorem expression_step_iff (input : Expression) (index : Trie SExpr Nat) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (valid : Valid index history) (target : Pattern) :
    Step (engineBasePremises scalarRelations) language (expressionCall input index history lexicals) target ↔
      target = result (answer (expressionMeaning history input)) :=
  step_of_exact_answers _ _ _ (fun fuel => expression_answers fuel input index history lexicals valid) target

theorem expression_decoded_step_iff (input : Expression) (index : Trie SExpr Nat) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (valid : Valid index history) (output : Bool) :
    Step (engineBasePremises scalarRelations) language (expressionCall input index history lexicals)
      (result (answer output)) ↔ output = expressionMeaning history input := by
  rw [expression_step_iff input index history lexicals valid, result_answer_injective.eq_iff]

theorem expression_nullable_iff (input : Expression) (index : Trie SExpr Nat) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (valid : Valid index history) :
    Step (engineBasePremises scalarRelations) language (expressionCall input index history lexicals)
      (result (answer true)) ↔
        PlainBnfGraphSemantics.ExpressionNullable {key | text key ∈ history} input := by
  rw [expression_decoded_step_iff input index history lexicals valid, eq_comm, expression_meaning_iff]

theorem expression_nonnullable_iff (input : Expression) (index : Trie SExpr Nat) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (valid : Valid index history) :
    Step (engineBasePremises scalarRelations) language (expressionCall input index history lexicals)
      (result (answer false)) ↔
        ¬ PlainBnfGraphSemantics.ExpressionNullable {key | text key ∈ history} input := by
  rw [expression_decoded_step_iff input index history lexicals valid, ← expression_meaning_iff]
  cases expressionMeaning history input <;> simp

/-- Literal decisions do not query either supplied index. -/
theorem empty_literal_answers (fuel : Nat) (location : SourceSpan) (index : Trie SExpr Nat)
    (history : List SExpr) (lexicals : List LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (elementCall (.literal "" location) index history lexicals) = [result (answer true)] := by
  simpa using literal_answers fuel "" location index history lexicals

theorem nonempty_literal_answers (fuel : Nat) (value : String) (nonempty : value ≠ "")
    (location : SourceSpan) (index : Trie SExpr Nat) (history : List SExpr)
    (lexicals : List LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (elementCall (.literal value location) index history lexicals) = [result (answer false)] := by
  have different : (value == "") = false := by simpa using nonempty
  simpa [different] using literal_answers fuel value location index history lexicals

/-- Known-name priority is independent of whether a lexical declaration shares
the same name. No disjointness condition is hidden in this theorem. -/
theorem known_reference_nullable (key : String) (location : SourceSpan) (index : Trie SExpr Nat)
    (history : List SExpr) (lexicals : List LexicalDeclaration) (valid : Valid index history)
    (present : text key ∈ history) :
    Step (engineBasePremises scalarRelations) language
      (elementCall (.reference key location) index history lexicals) (result (answer true)) := by
  rw [element_step_iff _ _ _ _ valid]
  simp [elementMeaning, isKnown, present]

/-- Both lexical references and unknown names are nonnullable only when they
are absent from the valid known-name index. -/
theorem absent_reference_nonnullable (key : String) (location : SourceSpan) (index : Trie SExpr Nat)
    (history : List SExpr) (lexicals : List LexicalDeclaration) (valid : Valid index history)
    (absent : text key ∉ history) :
    Step (engineBasePremises scalarRelations) language
      (elementCall (.reference key location) index history lexicals) (result (answer false)) := by
  rw [element_step_iff _ _ _ _ valid]
  simp [elementMeaning, isKnown, absent]

theorem lexical_overlap_keeps_known_priority (declaration : LexicalDeclaration) (location : SourceSpan)
    (tail : List LexicalDeclaration) :
    Step (engineBasePremises scalarRelations) language
      (elementCall (.reference declaration.referenceName location)
        (PlainBnfKnownNamesSourceExecution.historyIndex [keyScalars declaration.referenceName])
        [text declaration.referenceName] (declaration :: tail)) (result (answer true)) := by
  apply known_reference_nullable
  · exact PlainBnfKnownNamesSourceExecution.historyIndex_valid [keyScalars declaration.referenceName]
  · simp

/-- A successful alternative suppresses all remaining alternatives. The tail
and both context packets may be opaque; no validity assumption is necessary. -/
theorem alternatives_short_circuit (fuel : Nat) (tail nullable lexicals : SExpr) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (call "BNFAlternativesNullableAfterHeadV1" [answer true, tail, nullable, lexicals]) =
      [result (answer true)] := by
  rw [nullable_rewriteAt fuel _ (by simp [call, encode, encodeList, headedBy, nullableHeads])]
  simp [rules_exact, observedRules, observed, lowerPremise?, splitCall?, mode?,
    applyRuleUsing, call, answer, result, pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, premiseStepUsing, applyBindings]

theorem elements_short_circuit (fuel : Nat) (tail nullable lexicals : SExpr) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (call "BNFElementsNullableAfterHeadV1" [answer false, tail, nullable, lexicals]) =
      [result (answer false)] := by
  rw [nullable_rewriteAt fuel _ (by simp [call, encode, encodeList, headedBy, nullableHeads])]
  simp [rules_exact, observedRules, observed, lowerPremise?, splitCall?, mode?,
    applyRuleUsing, call, answer, result, pattern, patternList, SourceIntegerProvider.sourceVariableToken,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM,
    premisesUsing, premiseStepUsing, applyBindings]

/-- The found rule repeats the queried name in the returned payload. A
different payload matches neither found nor missing: it is not a negative
answer, and it is not repaired into the query. -/
theorem wrong_found_payload_answers (fuel : Nat) (key : String) (payload : SExpr)
    (wrong : payload ≠ text key) (lexicals : List LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) language fuel
      (afterLookupCall key (some payload) lexicals) = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    have encodedWrong : encode payload ≠ encode (text key) :=
      fun same => wrong (SourceSExprPatternCodec.encode_injective same)
    rw [nullable_rewriteAt fuel _ (by
      simp [afterLookupCall, call, encode, encodeList, headedBy, nullableHeads])]
    simp [rules_exact, observedRules, observed, lowerPremise?, splitCall?, mode?,
      applyRuleUsing, afterLookupCall, nameResult, call, pattern, patternList,
      SourceIntegerProvider.sourceVariableToken, encode, encodeList,
      matchPattern, matchArgs, mergeBindings, List.foldlM, Ne.symm encodedWrong]

theorem wrong_found_payload_has_no_step (key : String) (payload : SExpr)
    (wrong : payload ≠ text key) (lexicals : List LexicalDeclaration) (target : Pattern) :
    ¬ Step (engineBasePremises scalarRelations) language
      (afterLookupCall key (some payload) lexicals) target := by
  rw [← exists_mem_rewriteAt_iff_step]
  simp [wrong_found_payload_answers, wrong]

end Mettapedia.GSLT.Parsing.PlainBnfNullableSourceExecution
