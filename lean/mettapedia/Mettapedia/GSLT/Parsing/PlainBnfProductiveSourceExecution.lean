import Mettapedia.GSLT.Parsing.PlainBnfReadinessEnvironment
import Mettapedia.GSLT.Parsing.PlainBnfGraphSemantics

/-!
# Authored productive-expression execution

The sixteen actual graph-source clauses retain ordered, short-circuit
evaluation. Known names use the existing sparse trie and its history invariant;
otherwise the first lexical declaration supplies the actual matcher call.
Inputs are the existing String/Unicode-Nat structured expression carrier.
This does not assert physical admission or generated/native execution.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfProductiveSourceExecution

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT (Rewrite decodeList)
open SourceSExprPatternCodec (encode encodeList)
open SourceSExprPatternInstantiation (pattern patternList)
open PlainBnfStructuredDenotation (SourceSpan Element Alternative Expression LexicalMatcher LexicalDeclaration)
open PlainBnfTrieSourceExecution (call result)
open PlainBnfReferenceSourceAdmission (graphSource)
open PlainBnfReferenceCollectionSourceExecution
  (text span element elements alternative alternatives expression declarations declaration
   lookupCall lookupResult firstDeclaration lookupHeight matcher)
open PlainBnfKnownNamesSourceExecution (known Valid)
open PlainBnfLexicalMatcherSourceExecution (answer relations matcherMeaning matcherHeight matcherCall)
open PlainBnfIndexedCollectorSourceExecution
  (headedBy premiseClosed closed_extension disjoint_heads_do_not_match)
open PlainBnfReadinessEnvironment
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

abbrev NameIndex := PlainBnfGraphNameTrie.Trie SExpr Nat

def mode? : String → Option (Nat × Nat)
  | "BNFExpressionProductiveV1" | "BNFAlternativesProductiveV1" |
    "BNFAlternativeProductiveV1" | "BNFElementsProductiveV1" |
    "BNFElementProductiveV1" | "BNFProductiveReferenceAfterLookupV1" => some (3, 1)
  | "BNFAlternativesProductiveAfterHeadV1" | "BNFElementsProductiveAfterHeadV1" => some (4, 1)
  | "BNFProductiveReferenceAfterLexicalLookupV1" | "BNFLexicalMatcherInhabitedV1" => some (1, 1)
  | "BNFNameLookupV1" | "BNFLexicalReferenceLookupV1" => some (2, 1)
  | _ => none

def splitCall? : SExpr → Option (SExpr × SExpr)
  | .list (.atom relation :: arguments) => do
      let (inputs, outputs) ← mode? relation
      if arguments.length = inputs + outputs then
        some (.list (.atom relation :: arguments.take inputs), .list (arguments.drop inputs))
      else none
  | _ => none

def lowerPremise? (source : SExpr) : Option Premise := do
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

def rows : List Rewrite := (graphSource.rewrites.drop 24).take 16
def rules : List RewriteRule := (rows.mapM lowerRule?).get (by rfl)
def dependencies : List RewriteRule :=
  PlainBnfKnownNamesSourceExecution.language.rewrites ++
  PlainBnfReferenceCollectionSourceExecution.lookupLanguage.rewrites ++
  PlainBnfLexicalMatcherSourceExecution.language.rewrites
def language : LanguageDef :=
  { name := "PlainBnfAuthoredProductiveExpressions", types := [], terms := [], equations := [],
    rewrites := dependencies ++ rules }

theorem source_translation_exact : rows.mapM lowerRule? = some rules := rfl
theorem source_occurrences_exact : rows.zipIdx 24 = ((graphSource.rewrites.zipIdx).drop 24).take 16 := rfl

def relationHeads : List String :=
  ["BNFExpressionProductiveV1", "BNFAlternativesProductiveV1",
   "BNFAlternativesProductiveAfterHeadV1", "BNFAlternativeProductiveV1",
   "BNFElementsProductiveV1", "BNFElementsProductiveAfterHeadV1",
   "BNFElementProductiveV1", "BNFProductiveReferenceAfterLookupV1",
   "BNFProductiveReferenceAfterLexicalLookupV1"]

theorem source_family_exhaustive :
    graphSource.rewrites.filter (fun row => match row.head with
      | .list (.atom head :: _) => relationHeads.contains head
      | _ => false) = rows := rfl

/- Checked finite observations, not the authority constructing `language`. -/
private def observed (name : String) (input output : SExpr) (body : List SExpr := []) : RewriteRule :=
  { name, typeContext := [], premises := (body.mapM lowerPremise?).getD [],
    left := pattern input, right := pattern output }

private def observedRules : List RewriteRule :=
  [observed "bnf-expression-productive-v1"
    (metta_sexpr% petta "(BNFExpressionProductiveV1 (bnf-v1:expression ?alternatives ?span) ?productive ?lexicals)")
    (metta_sexpr% petta "(?result)")
    [metta_sexpr% petta "(BNFAlternativesProductiveV1 ?alternatives ?productive ?lexicals ?result)"],
   observed "bnf-alternatives-productive-nil-v1"
    (metta_sexpr% petta "(BNFAlternativesProductiveV1 (metta-nullary bnf-v1:alternatives-nil) ?productive ?lexicals)")
    (metta_sexpr% petta "(BNFNoV1)"),
   observed "bnf-alternatives-productive-cons-v1"
    (metta_sexpr% petta "(BNFAlternativesProductiveV1 (bnf-v1:alternatives-cons ?alternative ?tail) ?productive ?lexicals)")
    (metta_sexpr% petta "(?result)")
    [metta_sexpr% petta "(BNFAlternativeProductiveV1 ?alternative ?productive ?lexicals ?headResult)",
     metta_sexpr% petta "(BNFAlternativesProductiveAfterHeadV1 ?headResult ?tail ?productive ?lexicals ?result)"],
   observed "bnf-alternatives-productive-head-yes-v1"
    (metta_sexpr% petta "(BNFAlternativesProductiveAfterHeadV1 BNFYesV1 ?tail ?productive ?lexicals)")
    (metta_sexpr% petta "(BNFYesV1)"),
   observed "bnf-alternatives-productive-head-no-v1"
    (metta_sexpr% petta "(BNFAlternativesProductiveAfterHeadV1 BNFNoV1 ?tail ?productive ?lexicals)")
    (metta_sexpr% petta "(?result)")
    [metta_sexpr% petta "(BNFAlternativesProductiveV1 ?tail ?productive ?lexicals ?result)"],
   observed "bnf-alternative-productive-v1"
    (metta_sexpr% petta "(BNFAlternativeProductiveV1 (bnf-v1:alternative ?elements ?span) ?productive ?lexicals)")
    (metta_sexpr% petta "(?result)")
    [metta_sexpr% petta "(BNFElementsProductiveV1 ?elements ?productive ?lexicals ?result)"],
   observed "bnf-elements-productive-nil-v1"
    (metta_sexpr% petta "(BNFElementsProductiveV1 (metta-nullary bnf-v1:elements-nil) ?productive ?lexicals)")
    (metta_sexpr% petta "(BNFYesV1)"),
   observed "bnf-elements-productive-cons-v1"
    (metta_sexpr% petta "(BNFElementsProductiveV1 (bnf-v1:elements-cons ?element ?tail) ?productive ?lexicals)")
    (metta_sexpr% petta "(?result)")
    [metta_sexpr% petta "(BNFElementProductiveV1 ?element ?productive ?lexicals ?headResult)",
     metta_sexpr% petta "(BNFElementsProductiveAfterHeadV1 ?headResult ?tail ?productive ?lexicals ?result)"],
   observed "bnf-elements-productive-head-no-v1"
    (metta_sexpr% petta "(BNFElementsProductiveAfterHeadV1 BNFNoV1 ?tail ?productive ?lexicals)")
    (metta_sexpr% petta "(BNFNoV1)"),
   observed "bnf-elements-productive-head-yes-v1"
    (metta_sexpr% petta "(BNFElementsProductiveAfterHeadV1 BNFYesV1 ?tail ?productive ?lexicals)")
    (metta_sexpr% petta "(?result)")
    [metta_sexpr% petta "(BNFElementsProductiveV1 ?tail ?productive ?lexicals ?result)"],
   observed "bnf-literal-productive-v1"
    (metta_sexpr% petta "(BNFElementProductiveV1 (bnf-v1:literal ?text ?span) ?productive ?lexicals)")
    (metta_sexpr% petta "(BNFYesV1)"),
   observed "bnf-reference-productive-v1"
    (metta_sexpr% petta "(BNFElementProductiveV1 (bnf-v1:reference ?name ?span) ?productive ?lexicals)")
    (metta_sexpr% petta "(?result)")
    [metta_sexpr% petta "(BNFNameLookupV1 ?name ?productive ?lookup)",
     metta_sexpr% petta "(BNFProductiveReferenceAfterLookupV1 ?name ?lookup ?lexicals ?result)"],
   observed "bnf-productive-reference-found-v1"
    (metta_sexpr% petta "(BNFProductiveReferenceAfterLookupV1 ?name (BNFNameFoundV1 ?name) ?lexicals)")
    (metta_sexpr% petta "(BNFYesV1)"),
   observed "bnf-productive-reference-missing-v1"
    (metta_sexpr% petta "(BNFProductiveReferenceAfterLookupV1 ?name BNFNameMissingV1 ?lexicals)")
    (metta_sexpr% petta "(?result)")
    [metta_sexpr% petta "(BNFLexicalReferenceLookupV1 ?name ?lexicals ?lexicalLookup)",
     metta_sexpr% petta "(BNFProductiveReferenceAfterLexicalLookupV1 ?lexicalLookup ?result)"],
   observed "bnf-productive-lexical-reference-v1"
    (metta_sexpr% petta "(BNFProductiveReferenceAfterLexicalLookupV1 (BNFLexicalFoundV1 (bnf-v1:lexical-declaration ?name ?class ?matcher ?label ?origin)))")
    (metta_sexpr% petta "(?result)")
    [metta_sexpr% petta "(BNFLexicalMatcherInhabitedV1 ?matcher ?result)"],
   observed "bnf-unproductive-unknown-reference-v1"
    (metta_sexpr% petta "(BNFProductiveReferenceAfterLexicalLookupV1 BNFLexicalMissingV1)")
    (metta_sexpr% petta "(BNFNoV1)")]

private theorem rules_exact : rules = observedRules := rfl
theorem family_heads : rules.all (fun rule => headedBy relationHeads rule.left) = true := by
  simp [rules_exact, observedRules, observed, headedBy, relationHeads,
    pattern, patternList, encode, SourceIntegerProvider.sourceVariableToken]

private theorem productive_rewriteAt (fuel : Nat) (source : Pattern)
    (headed : headedBy relationHeads source = true) :
    rewriteAt (engineBasePremises relations) language (fuel + 1) source =
      rules.flatMap (fun rule => applyRuleUsing (engineBasePremises relations) language
        (rewriteAt (engineBasePremises relations) language fuel) rule source) := by
  apply PlainBnfHeapSourceExecution.skip_unmatched_prefix _ language dependencies rules rfl
  intro rule member
  simp only [dependencies, List.mem_append] at member
  rcases member with (member | member) | member
  · exact disjoint_heads_do_not_match knownHeads relationHeads (by
      simp [knownHeads, PlainBnfIndexedCollectorSourceExecution.trieNames,
        PlainBnfKnownNamesSourceExecution.knownNames, relationHeads]) _ _
      (List.all_eq_true.mp known_heads rule member) headed
  · exact disjoint_heads_do_not_match lexicalLookupHeads relationHeads (by
      simp [lexicalLookupHeads, relationHeads]) _ _
      (List.all_eq_true.mp lexical_lookup_heads rule member) headed
  · exact disjoint_heads_do_not_match lexicalMatcherHeads relationHeads (by
      simp [lexicalMatcherHeads, relationHeads]) _ _
      (List.all_eq_true.mp lexical_matcher_heads rule member) headed

def member (history : List SExpr) (key : String) : Bool := decide (text key ∈ history)
theorem member_iff (history : List SExpr) (key : String) :
    member history key = true ↔ text key ∈ history := by
  exact decide_eq_true_iff
def lexicalMeaning (found : Option LexicalDeclaration) : Bool :=
  found.any (fun declaration => matcherMeaning declaration.matcher)
def referenceMeaning (history : List SExpr) (lexicals : List LexicalDeclaration) (key : String) : Bool :=
  member history key || lexicalMeaning (firstDeclaration key lexicals)
def elementMeaning (history : List SExpr) (lexicals : List LexicalDeclaration) : Element → Bool
  | .literal _ _ => true
  | .reference key _ => referenceMeaning history lexicals key
def alternativeMeaning (history : List SExpr) (lexicals : List LexicalDeclaration) (value : Alternative) : Bool :=
  value.elements.all (elementMeaning history lexicals)
def expressionMeaning (history : List SExpr) (lexicals : List LexicalDeclaration) (value : Expression) : Bool :=
  value.alternatives.any (alternativeMeaning history lexicals)

def afterLexicalCall (found : Option LexicalDeclaration) : Pattern :=
  call "BNFProductiveReferenceAfterLexicalLookupV1" [lookupResult found]
def afterLookupCall (key : String) (present : Bool) (lexicals : List LexicalDeclaration) : Pattern :=
  call "BNFProductiveReferenceAfterLookupV1"
    [text key, PlainBnfKnownNamesSourceExecution.nameResult (if present then some (text key) else none),
     declarations lexicals]
def elementCall (value : Element) (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) : Pattern :=
  call "BNFElementProductiveV1" [element value, known index history, declarations lexicals]
def elementsCall (value : List Element) (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) : Pattern :=
  call "BNFElementsProductiveV1" [elements value, known index history, declarations lexicals]
def elementsAfterCall (head : Bool) (tail : List Element) (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) : Pattern :=
  call "BNFElementsProductiveAfterHeadV1" [answer head, elements tail, known index history, declarations lexicals]
def alternativeCall (value : Alternative) (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) : Pattern :=
  call "BNFAlternativeProductiveV1" [alternative value, known index history, declarations lexicals]
def alternativesCall (value : List Alternative) (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) : Pattern :=
  call "BNFAlternativesProductiveV1" [alternatives value, known index history, declarations lexicals]
def alternativesAfterCall (head : Bool) (tail : List Alternative) (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) : Pattern :=
  call "BNFAlternativesProductiveAfterHeadV1" [answer head, alternatives tail, known index history, declarations lexicals]
def expressionCall (value : Expression) (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) : Pattern :=
  call "BNFExpressionProductiveV1" [expression value, known index history, declarations lexicals]


theorem known_extension (fuel : Nat) (source : Pattern)
    (headed : headedBy knownHeads source = true) :
    rewriteAt (engineBasePremises relations) language fuel source =
      rewriteAt (engineBasePremises relations) PlainBnfKnownNamesSourceExecution.language fuel source := by
  apply closed_extension knownHeads relations PlainBnfKnownNamesSourceExecution.language language ([]) (PlainBnfReferenceCollectionSourceExecution.lookupLanguage.rewrites ++ PlainBnfLexicalMatcherSourceExecution.language.rewrites ++ rules)
  · simp [language, dependencies, List.append_assoc]
  · intro rule member premise present
    exact List.all_eq_true.mp (List.all_eq_true.mp known_closed rule member) premise present
  · intro rule member value itsHead
    simp only [List.nil_append, List.mem_append] at member
    rcases member with (member | member) | member
    · exact disjoint_heads_do_not_match lexicalLookupHeads knownHeads (by
        simp [lexicalLookupHeads, knownHeads, PlainBnfIndexedCollectorSourceExecution.trieNames,
          PlainBnfKnownNamesSourceExecution.knownNames]) _ _
        (List.all_eq_true.mp lexical_lookup_heads rule member) itsHead
    · exact disjoint_heads_do_not_match lexicalMatcherHeads knownHeads (by
        simp [lexicalMatcherHeads, knownHeads, PlainBnfIndexedCollectorSourceExecution.trieNames,
          PlainBnfKnownNamesSourceExecution.knownNames]) _ _
        (List.all_eq_true.mp lexical_matcher_heads rule member) itsHead
    · exact disjoint_heads_do_not_match relationHeads knownHeads (by
        simp [relationHeads, knownHeads, PlainBnfIndexedCollectorSourceExecution.trieNames,
          PlainBnfKnownNamesSourceExecution.knownNames]) _ _
        (List.all_eq_true.mp family_heads rule member) itsHead
  · exact headed

private theorem lookup_extension (fuel : Nat) (source : Pattern)
    (headed : headedBy lexicalLookupHeads source = true) :
    rewriteAt (engineBasePremises relations) language fuel source =
      rewriteAt (engineBasePremises relations) PlainBnfReferenceCollectionSourceExecution.lookupLanguage fuel source := by
  apply closed_extension lexicalLookupHeads relations PlainBnfReferenceCollectionSourceExecution.lookupLanguage language (PlainBnfKnownNamesSourceExecution.language.rewrites) (PlainBnfLexicalMatcherSourceExecution.language.rewrites ++ rules)
  · simp [language, dependencies, List.append_assoc]
  · intro rule member premise present
    exact List.all_eq_true.mp (List.all_eq_true.mp lexical_lookup_closed rule member) premise present
  · intro rule member value itsHead
    simp only [List.mem_append] at member
    rcases member with member | member | member
    · exact disjoint_heads_do_not_match knownHeads lexicalLookupHeads (by
        simp [lexicalLookupHeads, knownHeads, PlainBnfIndexedCollectorSourceExecution.trieNames,
          PlainBnfKnownNamesSourceExecution.knownNames]) _ _
        (List.all_eq_true.mp known_heads rule member) itsHead
    · exact disjoint_heads_do_not_match lexicalMatcherHeads lexicalLookupHeads (by
        simp [lexicalMatcherHeads, lexicalLookupHeads]) _ _
        (List.all_eq_true.mp lexical_matcher_heads rule member) itsHead
    · exact disjoint_heads_do_not_match relationHeads lexicalLookupHeads (by
        simp [relationHeads, lexicalLookupHeads]) _ _
        (List.all_eq_true.mp family_heads rule member) itsHead
  · exact headed

private theorem matcher_extension (fuel : Nat) (source : Pattern)
    (headed : headedBy lexicalMatcherHeads source = true) :
    rewriteAt (engineBasePremises relations) language fuel source =
      rewriteAt (engineBasePremises relations) PlainBnfLexicalMatcherSourceExecution.language fuel source := by
  apply closed_extension lexicalMatcherHeads relations PlainBnfLexicalMatcherSourceExecution.language language (PlainBnfKnownNamesSourceExecution.language.rewrites ++ PlainBnfReferenceCollectionSourceExecution.lookupLanguage.rewrites) (rules)
  · simp [language, dependencies, List.append_assoc]
  · intro rule member premise present
    exact List.all_eq_true.mp (List.all_eq_true.mp lexical_matcher_closed rule member) premise present
  · intro rule member value itsHead
    simp only [List.mem_append] at member
    rcases member with (member | member) | member
    · exact disjoint_heads_do_not_match knownHeads lexicalMatcherHeads (by
        simp [lexicalMatcherHeads, knownHeads, PlainBnfIndexedCollectorSourceExecution.trieNames,
          PlainBnfKnownNamesSourceExecution.knownNames]) _ _
        (List.all_eq_true.mp known_heads rule member) itsHead
    · exact disjoint_heads_do_not_match lexicalLookupHeads lexicalMatcherHeads (by
        simp [lexicalMatcherHeads, lexicalLookupHeads]) _ _
        (List.all_eq_true.mp lexical_lookup_heads rule member) itsHead
    · exact disjoint_heads_do_not_match relationHeads lexicalMatcherHeads (by
        simp [relationHeads, lexicalMatcherHeads]) _ _
        (List.all_eq_true.mp family_heads rule member) itsHead
  · exact headed

theorem known_lookup_answers (fuel : Nat) (key : String) (index : NameIndex)
    (history : List SExpr) (valid : Valid index history) :
    rewriteAt (engineBasePremises relations) language fuel
      (PlainBnfKnownNamesSourceExecution.knownLookupCall (key.toList.map Char.toNat) index history) =
      if PlainBnfTrieSourceExecution.lookupHeight (key.toList.map Char.toNat) index + 1 < fuel then
        [result (PlainBnfKnownNamesSourceExecution.nameResult
          (if member history key then some (text key) else none))] else [] := by
  rw [known_extension fuel _ (by
    simp [headedBy, knownHeads, PlainBnfKnownNamesSourceExecution.knownNames,
      PlainBnfKnownNamesSourceExecution.knownLookupCall, call, encode, encodeList])]
  rw [known_environment, PlainBnfKnownNamesSourceExecution.known_lookup_answers, valid]
  simp_rw [member_iff]
  rfl

theorem lexical_lookup_answers (fuel : Nat) (key : String) (lexicals : List LexicalDeclaration) :
    rewriteAt (engineBasePremises relations) language fuel (lookupCall key lexicals) =
      if lookupHeight key lexicals < fuel then
        [result (lookupResult (firstDeclaration key lexicals))] else [] := by
  rw [lookup_extension fuel _ (by
    simp [headedBy, lexicalLookupHeads, lookupCall, call, encode, encodeList])]
  rw [lexical_lookup_environment]
  exact PlainBnfReferenceCollectionSourceExecution.lookup_answers _ _ _

theorem lexical_matcher_answers (fuel : Nat) (value : LexicalMatcher) :
    rewriteAt (engineBasePremises relations) language fuel (matcherCall value) =
      if matcherHeight value < fuel then [result (answer (matcherMeaning value))] else [] := by
  rw [matcher_extension fuel _ (by
    simp [headedBy, lexicalMatcherHeads, matcherCall, call, encode, encodeList])]
  exact PlainBnfLexicalMatcherSourceExecution.matcher_answers _ _


abbrev outputs (values : List Bool) : List Pattern := values.map (result ∘ answer)

local macro "productive_reduce" : tactic =>
  `(tactic| (
    rw [productive_rewriteAt _ _ (by
      simp [headedBy, relationHeads, afterLexicalCall, afterLookupCall, elementCall,
        elementsCall, elementsAfterCall, alternativeCall, alternativesCall,
        alternativesAfterCall, expressionCall, call, encode, encodeList])]
    simp [rules_exact, observedRules, observed, lowerPremise?, splitCall?, mode?,
      applyRuleUsing, afterLexicalCall, afterLookupCall, elementCall, elementsCall,
      elementsAfterCall, alternativeCall, alternativesCall, alternativesAfterCall, expressionCall,
      call, lookupResult, PlainBnfKnownNamesSourceExecution.nameResult,
      element, elements, alternative, alternatives, expression, declaration, text,
      answer, pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
      matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, premiseStepUsing,
      applyBindings]))

local macro "productive_finish" : tactic =>
  `(tactic| simp [outputs, List.flatMap_map, result, answer, encode, encodeList,
    matchPattern, matchArgs, List.foldlM, mergeBindings, ← List.map_eq_flatMap])

private theorem afterLexical_none (fuel : Nat) :
    rewriteAt (engineBasePremises relations) language (fuel + 1) (afterLexicalCall none) =
      outputs [false] := by
  productive_reduce
  productive_finish

private theorem afterLexical_some (fuel : Nat) (found : LexicalDeclaration) (values : List Bool)
    (recursive : rewriteAt (engineBasePremises relations) language fuel
      (matcherCall found.matcher) = outputs values) :
    rewriteAt (engineBasePremises relations) language (fuel + 1) (afterLexicalCall (some found)) =
      outputs values := by
  productive_reduce
  simp only [matcherCall, call, encode, encodeList] at recursive
  rw [recursive]
  productive_finish

private theorem afterLookup_true (fuel : Nat) (key : String) (lexicals : List LexicalDeclaration) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
      (afterLookupCall key true lexicals) = outputs [true] := by
  productive_reduce
  productive_finish

private theorem afterLookup_false_none (fuel : Nat) (key : String) (lexicals : List LexicalDeclaration)
    (missing : rewriteAt (engineBasePremises relations) language fuel (lookupCall key lexicals) = []) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
      (afterLookupCall key false lexicals) = [] := by
  productive_reduce
  simp only [lookupCall, call, encode, encodeList, text] at missing
  rw [missing]
  simp

private theorem afterLookup_false_some (fuel : Nat) (key : String) (lexicals : List LexicalDeclaration)
    (found : Option LexicalDeclaration) (values : List Bool)
    (looked : rewriteAt (engineBasePremises relations) language fuel (lookupCall key lexicals) =
      [result (lookupResult found)])
    (recursive : rewriteAt (engineBasePremises relations) language fuel (afterLexicalCall found) =
      outputs values) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
      (afterLookupCall key false lexicals) = outputs values := by
  productive_reduce
  simp only [lookupCall, call, encode, encodeList, text] at looked
  rw [looked]
  simp [result, encode, encodeList, matchPattern, matchArgs, mergeBindings,
    List.foldlM]
  simp only [afterLexicalCall, call, encode, encodeList] at recursive
  rw [recursive]
  productive_finish

private theorem literal_answers (fuel : Nat) (value : String) (location : SourceSpan)
    (index : NameIndex) (history : List SExpr) (lexicals : List LexicalDeclaration) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
      (elementCall (.literal value location) index history lexicals) = outputs [true] := by
  productive_reduce
  productive_finish

private theorem reference_none (fuel : Nat) (key : String) (location : SourceSpan)
    (index : NameIndex) (history : List SExpr) (lexicals : List LexicalDeclaration)
    (missing : rewriteAt (engineBasePremises relations) language fuel
      (PlainBnfKnownNamesSourceExecution.knownLookupCall (key.toList.map Char.toNat) index history) = []) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
      (elementCall (.reference key location) index history lexicals) = [] := by
  productive_reduce
  simp only [PlainBnfKnownNamesSourceExecution.knownLookupCall, call, encode, encodeList] at missing
  rw [missing]
  simp

private theorem reference_some (fuel : Nat) (key : String) (location : SourceSpan)
    (index : NameIndex) (history : List SExpr) (lexicals : List LexicalDeclaration)
    (present : Bool) (values : List Bool)
    (looked : rewriteAt (engineBasePremises relations) language fuel
      (PlainBnfKnownNamesSourceExecution.knownLookupCall (key.toList.map Char.toNat) index history) =
        [result (PlainBnfKnownNamesSourceExecution.nameResult
          (if present then some (text key) else none))])
    (recursive : rewriteAt (engineBasePremises relations) language fuel
      (afterLookupCall key present lexicals) = outputs values) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
      (elementCall (.reference key location) index history lexicals) = outputs values := by
  productive_reduce
  simp only [PlainBnfKnownNamesSourceExecution.knownLookupCall, call, encode, encodeList, text] at looked
  rw [looked]
  simp [result, encode, encodeList, matchPattern, matchArgs, mergeBindings,
    List.foldlM]
  simp only [afterLookupCall, call, encode, encodeList, text] at recursive
  rw [recursive]
  productive_finish

private theorem elements_nil (fuel : Nat) (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
      (elementsCall [] index history lexicals) = outputs [true] := by
  productive_reduce
  productive_finish

private theorem elements_cons_none (fuel : Nat) (head : Element) (tail : List Element)
    (index : NameIndex) (history : List SExpr) (lexicals : List LexicalDeclaration)
    (missing : rewriteAt (engineBasePremises relations) language fuel
      (elementCall head index history lexicals) = []) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
      (elementsCall (head :: tail) index history lexicals) = [] := by
  productive_reduce
  simp only [elementCall, element, call, encode, encodeList, text] at missing
  rw [missing]
  simp

private theorem elements_cons_some (fuel : Nat) (head : Element) (tail : List Element)
    (index : NameIndex) (history : List SExpr) (lexicals : List LexicalDeclaration)
    (headValue : Bool) (values : List Bool)
    (looked : rewriteAt (engineBasePremises relations) language fuel
      (elementCall head index history lexicals) = outputs [headValue])
    (recursive : rewriteAt (engineBasePremises relations) language fuel
      (elementsAfterCall headValue tail index history lexicals) = outputs values) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
      (elementsCall (head :: tail) index history lexicals) = outputs values := by
  productive_reduce
  simp only [elementCall, element, call, encode, encodeList, text] at looked
  rw [looked]
  simp [outputs, result, encode, encodeList, matchPattern, matchArgs, mergeBindings,
    List.foldlM]
  simp only [elementsAfterCall, call, encode, encodeList] at recursive
  rw [recursive]
  productive_finish

private theorem elements_after_stop (fuel : Nat) (tail : List Element) (index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
      (elementsAfterCall false tail index history lexicals) = outputs [false] := by
  productive_reduce
  productive_finish

private theorem elements_after_continue (fuel : Nat) (tail : List Element) (index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration) (values : List Bool)
    (recursive : rewriteAt (engineBasePremises relations) language fuel
      (elementsCall tail index history lexicals) = outputs values) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
      (elementsAfterCall true tail index history lexicals) = outputs values := by
  productive_reduce
  simp only [elementsCall, call, encode, encodeList] at recursive
  rw [recursive]
  productive_finish

private theorem alternatives_nil (fuel : Nat) (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
      (alternativesCall [] index history lexicals) = outputs [false] := by
  productive_reduce
  productive_finish

private theorem alternatives_cons_none (fuel : Nat) (head : Alternative) (tail : List Alternative)
    (index : NameIndex) (history : List SExpr) (lexicals : List LexicalDeclaration)
    (missing : rewriteAt (engineBasePremises relations) language fuel
      (alternativeCall head index history lexicals) = []) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
      (alternativesCall (head :: tail) index history lexicals) = [] := by
  productive_reduce
  simp only [alternativeCall, alternative, call, encode, encodeList] at missing
  rw [missing]
  simp

private theorem alternatives_cons_some (fuel : Nat) (head : Alternative) (tail : List Alternative)
    (index : NameIndex) (history : List SExpr) (lexicals : List LexicalDeclaration)
    (headValue : Bool) (values : List Bool)
    (looked : rewriteAt (engineBasePremises relations) language fuel
      (alternativeCall head index history lexicals) = outputs [headValue])
    (recursive : rewriteAt (engineBasePremises relations) language fuel
      (alternativesAfterCall headValue tail index history lexicals) = outputs values) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
      (alternativesCall (head :: tail) index history lexicals) = outputs values := by
  productive_reduce
  simp only [alternativeCall, alternative, call, encode, encodeList] at looked
  rw [looked]
  simp [outputs, result, encode, encodeList, matchPattern, matchArgs, mergeBindings,
    List.foldlM]
  simp only [alternativesAfterCall, call, encode, encodeList] at recursive
  rw [recursive]
  productive_finish

private theorem alternatives_after_stop (fuel : Nat) (tail : List Alternative) (index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
      (alternativesAfterCall true tail index history lexicals) = outputs [true] := by
  productive_reduce
  productive_finish

private theorem alternatives_after_continue (fuel : Nat) (tail : List Alternative) (index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration) (values : List Bool)
    (recursive : rewriteAt (engineBasePremises relations) language fuel
      (alternativesCall tail index history lexicals) = outputs values) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
      (alternativesAfterCall false tail index history lexicals) = outputs values := by
  productive_reduce
  simp only [alternativesCall, call, encode, encodeList] at recursive
  rw [recursive]
  productive_finish

private theorem alternative_step (fuel : Nat) (value : Alternative) (index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration) (values : List Bool)
    (recursive : rewriteAt (engineBasePremises relations) language fuel
      (elementsCall value.elements index history lexicals) = outputs values) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
      (alternativeCall value index history lexicals) = outputs values := by
  productive_reduce
  simp only [elementsCall, call, encode, encodeList] at recursive
  rw [recursive]
  productive_finish

private theorem expression_step (fuel : Nat) (value : Expression) (index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration) (values : List Bool)
    (recursive : rewriteAt (engineBasePremises relations) language fuel
      (alternativesCall value.alternatives index history lexicals) = outputs values) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
      (expressionCall value index history lexicals) = outputs values := by
  productive_reduce
  simp only [alternativesCall, call, encode, encodeList] at recursive
  rw [recursive]
  productive_finish


/-- Exact contextual height; short-circuited tails do not contribute. -/
def afterLexicalHeight : Option LexicalDeclaration → Nat
  | none => 0
  | some declaration => 1 + matcherHeight declaration.matcher
def afterLookupHeight (key : String) (present : Bool) (lexicals : List LexicalDeclaration) : Nat :=
  if present then 0 else 1 + max (lookupHeight key lexicals)
    (afterLexicalHeight (firstDeclaration key lexicals))
def elementHeight (index : NameIndex) (history : List SExpr) (lexicals : List LexicalDeclaration) : Element → Nat
  | .literal _ _ => 0
  | .reference key _ => 1 + max
      (PlainBnfTrieSourceExecution.lookupHeight (key.toList.map Char.toNat) index + 1)
      (afterLookupHeight key (member history key) lexicals)
def elementsHeight (index : NameIndex) (history : List SExpr) (lexicals : List LexicalDeclaration) : List Element → Nat
  | [] => 0
  | head :: tail => 1 + max (elementHeight index history lexicals head)
      (if elementMeaning history lexicals head then 1 + elementsHeight index history lexicals tail else 0)
def elementsAfterHeight (head : Bool) (tail : List Element) (index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration) : Nat :=
  if head then 1 + elementsHeight index history lexicals tail else 0
def alternativeHeight (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (value : Alternative) : Nat :=
  1 + elementsHeight index history lexicals value.elements
def alternativesHeight (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) : List Alternative → Nat
  | [] => 0
  | head :: tail => 1 + max (alternativeHeight index history lexicals head)
      (if alternativeMeaning history lexicals head then 0 else 1 + alternativesHeight index history lexicals tail)
def alternativesAfterHeight (head : Bool) (tail : List Alternative) (index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration) : Nat :=
  if head then 0 else 1 + alternativesHeight index history lexicals tail
def expressionHeight (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (value : Expression) : Nat :=
  1 + alternativesHeight index history lexicals value.alternatives

def bounded (height fuel : Nat) (value : Bool) : List Bool :=
  if height < fuel then [value] else []

private theorem afterLexical_answers (fuel : Nat) (found : Option LexicalDeclaration) :
    rewriteAt (engineBasePremises relations) language fuel (afterLexicalCall found) =
      outputs (bounded (afterLexicalHeight found) fuel (lexicalMeaning found)) := by
  cases fuel with
  | zero => simp [rewriteAt, bounded, outputs]
  | succ fuel =>
    cases found with
    | none => simpa [bounded, afterLexicalHeight, lexicalMeaning] using afterLexical_none fuel
    | some found =>
      have recursive := lexical_matcher_answers fuel found.matcher
      have step := afterLexical_some fuel found (bounded (matcherHeight found.matcher) fuel
        (matcherMeaning found.matcher)) (by
          by_cases enough : matcherHeight found.matcher < fuel <;>
            simpa [outputs, bounded, enough] using recursive)
      have bound : 1 + matcherHeight found.matcher < fuel + 1 ↔ matcherHeight found.matcher < fuel := by omega
      simpa only [bounded, afterLexicalHeight, lexicalMeaning, Option.any_some, bound] using step

private theorem afterLookup_answers (fuel : Nat) (key : String) (present : Bool)
    (lexicals : List LexicalDeclaration) :
    rewriteAt (engineBasePremises relations) language fuel (afterLookupCall key present lexicals) =
      outputs (bounded (afterLookupHeight key present lexicals) fuel
        (present || lexicalMeaning (firstDeclaration key lexicals))) := by
  cases fuel with
  | zero => simp [rewriteAt, bounded, outputs]
  | succ fuel =>
    cases present with
    | true => simpa [bounded, afterLookupHeight] using afterLookup_true fuel key lexicals
    | false =>
      by_cases enough : lookupHeight key lexicals < fuel
      · have step := afterLookup_false_some fuel key lexicals (firstDeclaration key lexicals)
          (bounded (afterLexicalHeight (firstDeclaration key lexicals)) fuel
            (lexicalMeaning (firstDeclaration key lexicals)))
          (by simpa [enough] using lexical_lookup_answers fuel key lexicals)
          (afterLexical_answers fuel _)
        have bound : 1 + max (lookupHeight key lexicals)
            (afterLexicalHeight (firstDeclaration key lexicals)) < fuel + 1 ↔
            afterLexicalHeight (firstDeclaration key lexicals) < fuel := by omega
        simpa [afterLookupHeight, bounded, bound] using step
      · have step := afterLookup_false_none fuel key lexicals
          (by simpa [enough] using lexical_lookup_answers fuel key lexicals)
        have bound : ¬ 1 + max (lookupHeight key lexicals)
            (afterLexicalHeight (firstDeclaration key lexicals)) < fuel + 1 := by omega
        simpa [afterLookupHeight, bounded, bound, outputs] using step

theorem element_answers (fuel : Nat) (value : Element) (index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration) (valid : Valid index history) :
    rewriteAt (engineBasePremises relations) language fuel (elementCall value index history lexicals) =
      outputs (bounded (elementHeight index history lexicals value) fuel
        (elementMeaning history lexicals value)) := by
  cases fuel with
  | zero => simp [rewriteAt, bounded, outputs]
  | succ fuel =>
    cases value with
    | literal value location =>
      simpa [bounded, elementHeight, elementMeaning] using literal_answers fuel value location index history lexicals
    | reference key location =>
      by_cases enough : PlainBnfTrieSourceExecution.lookupHeight (key.toList.map Char.toNat) index + 1 < fuel
      · have step := reference_some fuel key location index history lexicals (member history key)
          (bounded (afterLookupHeight key (member history key) lexicals) fuel
            (referenceMeaning history lexicals key))
          (by simpa [enough] using known_lookup_answers fuel key index history valid)
          (afterLookup_answers fuel key (member history key) lexicals)
        have bound : 1 + max
            (PlainBnfTrieSourceExecution.lookupHeight (key.toList.map Char.toNat) index + 1)
            (afterLookupHeight key (member history key) lexicals) < fuel + 1 ↔
            afterLookupHeight key (member history key) lexicals < fuel := by omega
        simpa [elementHeight, elementMeaning, bounded, bound] using step
      · have step := reference_none fuel key location index history lexicals
          (by simpa [enough] using known_lookup_answers fuel key index history valid)
        have bound : ¬ 1 + max
            (PlainBnfTrieSourceExecution.lookupHeight (key.toList.map Char.toNat) index + 1)
            (afterLookupHeight key (member history key) lexicals) < fuel + 1 := by omega
        simpa [elementHeight, bounded, bound, outputs] using step


private theorem elements_all_answers (fuel : Nat) (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (valid : Valid index history) :
    (∀ value, rewriteAt (engineBasePremises relations) language fuel
      (elementsCall value index history lexicals) =
      outputs (bounded (elementsHeight index history lexicals value) fuel
        (value.all (elementMeaning history lexicals)))) ∧
    (∀ head tail, rewriteAt (engineBasePremises relations) language fuel
      (elementsAfterCall head tail index history lexicals) =
      outputs (bounded (elementsAfterHeight head tail index history lexicals) fuel
        (head && tail.all (elementMeaning history lexicals)))) := by
  induction fuel with
  | zero => simp [rewriteAt, bounded, outputs]
  | succ fuel ih =>
    constructor
    · intro value
      cases value with
      | nil => simpa [elementsHeight, bounded] using elements_nil fuel index history lexicals
      | cons head tail =>
        by_cases enough : elementHeight index history lexicals head < fuel
        · have step := elements_cons_some fuel head tail index history lexicals
            (elementMeaning history lexicals head)
            (bounded (elementsAfterHeight (elementMeaning history lexicals head) tail index history lexicals)
              fuel (elementMeaning history lexicals head && tail.all (elementMeaning history lexicals)))
            (by simpa [bounded, enough] using element_answers fuel head index history lexicals valid)
            (ih.2 _ _)
          have bound : 1 + max (elementHeight index history lexicals head)
              (elementsAfterHeight (elementMeaning history lexicals head) tail index history lexicals) < fuel + 1 ↔
              elementsAfterHeight (elementMeaning history lexicals head) tail index history lexicals < fuel := by omega
          simp only [elementsAfterHeight] at bound step
          simpa only [elementsHeight, List.all_cons, bounded, bound] using step
        · have step := elements_cons_none fuel head tail index history lexicals
            (by simpa [bounded, enough, outputs] using element_answers fuel head index history lexicals valid)
          have bound : ¬ 1 + max (elementHeight index history lexicals head)
              (elementsAfterHeight (elementMeaning history lexicals head) tail index history lexicals) < fuel + 1 := by omega
          change ¬ elementsHeight index history lexicals (head :: tail) < fuel + 1 at bound
          simpa only [bounded, if_neg bound, outputs, List.map_nil] using step
    · intro head tail
      cases head with
      | false => simpa [elementsAfterHeight, bounded] using elements_after_stop fuel tail index history lexicals
      | true =>
        have step := elements_after_continue fuel tail index history lexicals
          (bounded (elementsHeight index history lexicals tail) fuel
            (tail.all (elementMeaning history lexicals))) (ih.1 tail)
        have bound : 1 + elementsHeight index history lexicals tail < fuel + 1 ↔
            elementsHeight index history lexicals tail < fuel := by omega
        simpa only [elementsAfterHeight, Bool.true_eq, ↓reduceIte, bounded, bound, Bool.true_and] using step

theorem elements_answers (fuel : Nat) (value : List Element) (index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration) (valid : Valid index history) :
    rewriteAt (engineBasePremises relations) language fuel (elementsCall value index history lexicals) =
      outputs (bounded (elementsHeight index history lexicals value) fuel
        (value.all (elementMeaning history lexicals))) :=
  (elements_all_answers fuel index history lexicals valid).1 value

theorem alternative_answers (fuel : Nat) (value : Alternative) (index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration) (valid : Valid index history) :
    rewriteAt (engineBasePremises relations) language fuel (alternativeCall value index history lexicals) =
      outputs (bounded (alternativeHeight index history lexicals value) fuel
        (alternativeMeaning history lexicals value)) := by
  cases fuel with
  | zero => simp [rewriteAt, bounded, outputs]
  | succ fuel =>
    have step := alternative_step fuel value index history lexicals
      (bounded (elementsHeight index history lexicals value.elements) fuel
        (alternativeMeaning history lexicals value))
      (elements_answers fuel value.elements index history lexicals valid)
    have bound : 1 + elementsHeight index history lexicals value.elements < fuel + 1 ↔
        elementsHeight index history lexicals value.elements < fuel := by omega
    simpa only [alternativeHeight, bounded, bound] using step

private theorem alternatives_all_answers (fuel : Nat) (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (valid : Valid index history) :
    (∀ value, rewriteAt (engineBasePremises relations) language fuel
      (alternativesCall value index history lexicals) =
      outputs (bounded (alternativesHeight index history lexicals value) fuel
        (value.any (alternativeMeaning history lexicals)))) ∧
    (∀ head tail, rewriteAt (engineBasePremises relations) language fuel
      (alternativesAfterCall head tail index history lexicals) =
      outputs (bounded (alternativesAfterHeight head tail index history lexicals) fuel
        (head || tail.any (alternativeMeaning history lexicals)))) := by
  induction fuel with
  | zero => simp [rewriteAt, bounded, outputs]
  | succ fuel ih =>
    constructor
    · intro value
      cases value with
      | nil => simpa [alternativesHeight, bounded] using alternatives_nil fuel index history lexicals
      | cons head tail =>
        by_cases enough : alternativeHeight index history lexicals head < fuel
        · have step := alternatives_cons_some fuel head tail index history lexicals
            (alternativeMeaning history lexicals head)
            (bounded (alternativesAfterHeight (alternativeMeaning history lexicals head) tail index history lexicals)
              fuel (alternativeMeaning history lexicals head || tail.any (alternativeMeaning history lexicals)))
            (by simpa [bounded, enough] using alternative_answers fuel head index history lexicals valid)
            (ih.2 _ _)
          have bound : 1 + max (alternativeHeight index history lexicals head)
              (alternativesAfterHeight (alternativeMeaning history lexicals head) tail index history lexicals) < fuel + 1 ↔
              alternativesAfterHeight (alternativeMeaning history lexicals head) tail index history lexicals < fuel := by omega
          simp only [alternativesAfterHeight] at bound step
          simpa only [alternativesHeight, List.any_cons, bounded, bound] using step
        · have step := alternatives_cons_none fuel head tail index history lexicals
            (by simpa [bounded, enough, outputs] using alternative_answers fuel head index history lexicals valid)
          have bound : ¬ 1 + max (alternativeHeight index history lexicals head)
              (alternativesAfterHeight (alternativeMeaning history lexicals head) tail index history lexicals) < fuel + 1 := by omega
          change ¬ alternativesHeight index history lexicals (head :: tail) < fuel + 1 at bound
          simpa only [bounded, if_neg bound, outputs, List.map_nil] using step
    · intro head tail
      cases head with
      | true => simpa [alternativesAfterHeight, bounded] using alternatives_after_stop fuel tail index history lexicals
      | false =>
        have step := alternatives_after_continue fuel tail index history lexicals
          (bounded (alternativesHeight index history lexicals tail) fuel
            (tail.any (alternativeMeaning history lexicals))) (ih.1 tail)
        have bound : 1 + alternativesHeight index history lexicals tail < fuel + 1 ↔
            alternativesHeight index history lexicals tail < fuel := by omega
        simpa only [alternativesAfterHeight, Bool.false_eq_true, ↓reduceIte, bounded, bound, Bool.false_or] using step

theorem alternatives_answers (fuel : Nat) (value : List Alternative) (index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration) (valid : Valid index history) :
    rewriteAt (engineBasePremises relations) language fuel (alternativesCall value index history lexicals) =
      outputs (bounded (alternativesHeight index history lexicals value) fuel
        (value.any (alternativeMeaning history lexicals))) :=
  (alternatives_all_answers fuel index history lexicals valid).1 value

theorem expression_answers (fuel : Nat) (value : Expression) (index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration) (valid : Valid index history) :
    rewriteAt (engineBasePremises relations) language fuel (expressionCall value index history lexicals) =
      if expressionHeight index history lexicals value < fuel then
        [result (answer (expressionMeaning history lexicals value))] else [] := by
  cases fuel with
  | zero => simp [rewriteAt]
  | succ fuel =>
    have step := expression_step fuel value index history lexicals
      (bounded (alternativesHeight index history lexicals value.alternatives) fuel
        (expressionMeaning history lexicals value))
      (alternatives_answers fuel value.alternatives index history lexicals valid)
    have bound : 1 + alternativesHeight index history lexicals value.alternatives < fuel + 1 ↔
        alternativesHeight index history lexicals value.alternatives < fuel := by omega
    by_cases enough : alternativesHeight index history lexicals value.alternatives < fuel <;>
      simpa only [expressionHeight, bound, bounded, enough, ↓reduceIte, outputs, List.map_cons,
        List.map_nil, Function.comp_apply] using step

theorem expression_step_iff (value : Expression) (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (valid : Valid index history) (target : Pattern) :
    Step (engineBasePremises relations) language (expressionCall value index history lexicals) target ↔
      target = result (answer (expressionMeaning history lexicals value)) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [expression_answers fuel value index history lexicals valid] at member
    split_ifs at member
    · simpa using member
    · cases member
  · rintro rfl
    exact ⟨expressionHeight index history lexicals value + 1, by
      simp [expression_answers, valid]⟩

theorem expression_decoded_step_iff (value : Expression) (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (valid : Valid index history) (output : Bool) :
    Step (engineBasePremises relations) language (expressionCall value index history lexicals)
      (result (answer output)) ↔ output = expressionMeaning history lexicals value := by
  rw [expression_step_iff _ _ _ _ valid]
  exact PlainBnfLexicalMatcherSourceExecution.result_answer_injective.eq_iff


def wholeHeads : List String := knownHeads ++ lexicalLookupHeads ++ lexicalMatcherHeads ++ relationHeads

theorem whole_heads : language.rewrites.all (fun rule => headedBy wholeHeads rule.left) = true := by
  apply List.all_eq_true.mpr
  intro rule member
  simp only [language, dependencies, List.mem_append] at member
  rcases member with ((member | member) | member) | member
  · exact headedBy_mono knownHeads wholeHeads (by
      intro name present
      simp [wholeHeads, present]) _ (List.all_eq_true.mp known_heads rule member)
  · exact headedBy_mono lexicalLookupHeads wholeHeads (by
      intro name present
      simp [wholeHeads, present]) _ (List.all_eq_true.mp lexical_lookup_heads rule member)
  · exact headedBy_mono lexicalMatcherHeads wholeHeads (by
      intro name present
      simp [wholeHeads, present]) _ (List.all_eq_true.mp lexical_matcher_heads rule member)
  · exact headedBy_mono relationHeads wholeHeads (by
      intro name present
      simp [wholeHeads, present]) _ (List.all_eq_true.mp family_heads rule member)

private theorem premise_mono (small large : List String) (included : small ⊆ large)
    (premise : Premise) (closed : premiseClosed small premise = true) :
    premiseClosed large premise = true := by
  cases premise with
  | congruence source target => exact headedBy_mono small large included source closed
  | _ => rfl

theorem productive_closed : rules.all (fun rule => rule.premises.all (premiseClosed wholeHeads)) = true := by
  simp [rules_exact, observedRules, observed, lowerPremise?, splitCall?, mode?, premiseClosed,
    headedBy, wholeHeads, relationHeads, knownHeads, lexicalLookupHeads, lexicalMatcherHeads,
    PlainBnfIndexedCollectorSourceExecution.trieNames, PlainBnfKnownNamesSourceExecution.knownNames,
    pattern, patternList, encode, SourceIntegerProvider.sourceVariableToken]

theorem whole_closed : language.rewrites.all (fun rule => rule.premises.all (premiseClosed wholeHeads)) = true := by
  apply List.all_eq_true.mpr
  intro rule member
  apply List.all_eq_true.mpr
  intro premise present
  simp only [language, dependencies, List.mem_append] at member
  rcases member with ((member | member) | member) | member
  · exact premise_mono knownHeads wholeHeads (by
      intro name included
      simp [wholeHeads, included]) premise
      (List.all_eq_true.mp (List.all_eq_true.mp known_closed rule member) premise present)
  · exact premise_mono lexicalLookupHeads wholeHeads (by
      intro name included
      simp [wholeHeads, included]) premise
      (List.all_eq_true.mp (List.all_eq_true.mp lexical_lookup_closed rule member) premise present)
  · exact premise_mono lexicalMatcherHeads wholeHeads (by
      intro name included
      simp [wholeHeads, included]) premise
      (List.all_eq_true.mp (List.all_eq_true.mp lexical_matcher_closed rule member) premise present)
  · exact List.all_eq_true.mp (List.all_eq_true.mp productive_closed rule member) premise present


/-- The Boolean observation agrees with the independent lexical semantics only
on the admitted ordered scalar domain. -/
theorem matcherMeaning_iff (declaration : LexicalDeclaration)
    (valid : PlainBnfSemanticAdmission.MatcherWellFormed declaration.matcher) :
    matcherMeaning declaration.matcher = true ↔
      PlainBnfLexicalInhabitation.InhabitedClass
        (PlainBnfStructuredDenotation.denoteLexicalClass declaration).kind := by
  have exactCheck := PlainBnfGraphSemantics.lexical_inhabitation_check_exact declaration valid
  cases declaration with
  | mk name className value label origin =>
    cases value <;> exact exactCheck

theorem firstDeclaration_predicate (key : String) (lexicals : List LexicalDeclaration)
    (unique : (lexicals.map (·.referenceName)).Nodup) (predicate : LexicalDeclaration → Prop) :
    (∃ found, firstDeclaration key lexicals = some found ∧ predicate found) ↔
      ∃ found ∈ lexicals, found.referenceName = key ∧ predicate found := by
  induction lexicals with
  | nil => simp [firstDeclaration]
  | cons head tail ih =>
    have apart : head.referenceName ∉ tail.map (·.referenceName) :=
      (List.nodup_cons.mp unique).1
    have restUnique : (tail.map (·.referenceName)).Nodup := (List.nodup_cons.mp unique).2
    by_cases same : head.referenceName = key
    · have noTail : ¬ ∃ found ∈ tail, found.referenceName = key ∧ predicate found := by
        rintro ⟨found, present, equal, _⟩
        exact apart (List.mem_map.mpr ⟨found, present, equal.trans same.symm⟩)
      simp [firstDeclaration, same, noTail]
    · have next := ih restUnique
      simpa [firstDeclaration, same] using next

theorem lexicalMeaning_iff (key : String) (authority : PlainBnfStructuredDenotation.GrammarAuthority)
    (unique : (authority.lexicalDeclarations.map (·.referenceName)).Nodup)
    (valid : ∀ declaration ∈ authority.lexicalDeclarations,
      PlainBnfSemanticAdmission.MatcherWellFormed declaration.matcher) :
    lexicalMeaning (firstDeclaration key authority.lexicalDeclarations) = true ↔
      PlainBnfGraphSemantics.LexicalProductive authority key := by
  have selected := firstDeclaration_predicate key authority.lexicalDeclarations unique
    (fun declaration => matcherMeaning declaration.matcher = true)
  have observation : lexicalMeaning (firstDeclaration key authority.lexicalDeclarations) = true ↔
      ∃ found, firstDeclaration key authority.lexicalDeclarations = some found ∧
        matcherMeaning found.matcher = true := by
    cases found : firstDeclaration key authority.lexicalDeclarations <;> simp [lexicalMeaning]
  rw [observation, selected]
  constructor
  · rintro ⟨found, present, same, inhabited⟩
    exact ⟨found, present, same, (matcherMeaning_iff found (valid found present)).mp inhabited⟩
  · rintro ⟨found, present, same, inhabited⟩
    exact ⟨found, present, same, (matcherMeaning_iff found (valid found present)).mpr inhabited⟩

theorem elementMeaning_iff (history : List SExpr)
    (authority : PlainBnfStructuredDenotation.GrammarAuthority)
    (unique : (authority.lexicalDeclarations.map (·.referenceName)).Nodup)
    (valid : ∀ declaration ∈ authority.lexicalDeclarations,
      PlainBnfSemanticAdmission.MatcherWellFormed declaration.matcher) (value : Element) :
    elementMeaning history authority.lexicalDeclarations value = true ↔
      PlainBnfGraphSemantics.ElementProductive {key | text key ∈ history} authority value := by
  cases value with
  | literal value location => simp [elementMeaning, PlainBnfGraphSemantics.ElementProductive]
  | reference key location =>
    simp only [elementMeaning, referenceMeaning, Bool.or_eq_true, member_iff,
      lexicalMeaning_iff key authority unique valid, PlainBnfGraphSemantics.ElementProductive,
      Set.mem_ofPred_eq]

theorem expressionMeaning_iff (history : List SExpr)
    (authority : PlainBnfStructuredDenotation.GrammarAuthority)
    (unique : (authority.lexicalDeclarations.map (·.referenceName)).Nodup)
    (valid : ∀ declaration ∈ authority.lexicalDeclarations,
      PlainBnfSemanticAdmission.MatcherWellFormed declaration.matcher) (value : Expression) :
    expressionMeaning history authority.lexicalDeclarations value = true ↔
      PlainBnfGraphSemantics.ExpressionProductive {key | text key ∈ history} authority value := by
  simp only [expressionMeaning, List.any_eq_true, alternativeMeaning, List.all_eq_true,
    elementMeaning_iff history authority unique valid, PlainBnfGraphSemantics.ExpressionProductive,
    PlainBnfGraphSemantics.AlternativeProductive]

theorem expression_yes_iff_productive (value : Expression) (index : NameIndex) (history : List SExpr)
    (knownValid : Valid index history) (authority : PlainBnfStructuredDenotation.GrammarAuthority)
    (unique : (authority.lexicalDeclarations.map (·.referenceName)).Nodup)
    (valid : ∀ declaration ∈ authority.lexicalDeclarations,
      PlainBnfSemanticAdmission.MatcherWellFormed declaration.matcher) :
    Step (engineBasePremises relations) language
      (expressionCall value index history authority.lexicalDeclarations) (result (answer true)) ↔
      PlainBnfGraphSemantics.ExpressionProductive {key | text key ∈ history} authority value := by
  rw [expression_decoded_step_iff _ _ _ _ knownValid, eq_comm]
  exact expressionMeaning_iff history authority unique valid value

theorem expression_no_iff_unproductive (value : Expression) (index : NameIndex) (history : List SExpr)
    (knownValid : Valid index history) (authority : PlainBnfStructuredDenotation.GrammarAuthority)
    (unique : (authority.lexicalDeclarations.map (·.referenceName)).Nodup)
    (valid : ∀ declaration ∈ authority.lexicalDeclarations,
      PlainBnfSemanticAdmission.MatcherWellFormed declaration.matcher) :
    Step (engineBasePremises relations) language
      (expressionCall value index history authority.lexicalDeclarations) (result (answer false)) ↔
      ¬ PlainBnfGraphSemantics.ExpressionProductive {key | text key ∈ history} authority value := by
  rw [expression_decoded_step_iff _ _ _ _ knownValid, eq_comm,
    ← expressionMeaning_iff history authority unique valid value]
  cases expressionMeaning history authority.lexicalDeclarations value <;> decide


private def controlSpan : SourceSpan := { start := 3, stop := 11 }
private def singleElement (value : Element) : Expression :=
  { alternatives := [{ elements := [value], span := controlSpan }], span := controlSpan }
private def controlDeclaration (value : LexicalMatcher) : LexicalDeclaration :=
  { referenceName := "x", className := "class-x", matcher := value,
    ruleLabel := "x-rule", origin := { authority := "control", occurrence := 0 } }

theorem epsilon_and_empty_alternatives (index : NameIndex) (history : List SExpr)
    (lexicals : List LexicalDeclaration) (valid : Valid index history) :
    Step (engineBasePremises relations) language
      (expressionCall { alternatives := [{ elements := [], span := controlSpan }], span := controlSpan }
        index history lexicals) (result (answer true)) ∧
    Step (engineBasePremises relations) language
      (expressionCall { alternatives := [], span := controlSpan } index history lexicals)
      (result (answer false)) := by
  constructor <;> rw [expression_decoded_step_iff _ _ _ _ valid] <;>
    rfl

theorem literal_text_is_productive_data (value : String) :
    Step (engineBasePremises relations) language
      (expressionCall (singleElement (.literal value controlSpan)) .empty [] [])
      (result (answer true)) := by
  rw [expression_decoded_step_iff _ _ _ _ PlainBnfKnownNamesSourceExecution.valid_empty]
  rfl

theorem unknown_reference_is_unproductive :
    Step (engineBasePremises relations) language
      (expressionCall (singleElement (.reference "missing" controlSpan)) .empty [] [])
      (result (answer false)) := by
  rw [expression_decoded_step_iff _ _ _ _ PlainBnfKnownNamesSourceExecution.valid_empty]
  rfl

theorem short_circuit_keeps_its_branch (fuel : Nat) (index : NameIndex)
    (history : List SExpr) (lexicals : List LexicalDeclaration)
    (elementTail : List Element) (alternativeTail : List Alternative) :
    rewriteAt (engineBasePremises relations) language (fuel + 1)
      (elementsAfterCall false elementTail index history lexicals) = [result (answer false)] ∧
    rewriteAt (engineBasePremises relations) language (fuel + 1)
      (alternativesAfterCall true alternativeTail index history lexicals) = [result (answer true)] :=
  ⟨elements_after_stop fuel elementTail index history lexicals,
   alternatives_after_stop fuel alternativeTail index history lexicals⟩

theorem repeated_alternative_still_returns_one_occurrence (value : Alternative)
    (index : NameIndex) (history : List SExpr) (lexicals : List LexicalDeclaration)
    (valid : Valid index history) :
    let repeated : Expression := { alternatives := [value, value], span := controlSpan }
    rewriteAt (engineBasePremises relations) language
      (expressionHeight index history lexicals repeated + 1)
      (expressionCall repeated index history lexicals) =
      [result (answer (alternativeMeaning history lexicals value))] := by
  dsimp only
  rw [expression_answers _ _ _ _ _ valid]
  simp [expressionMeaning]

theorem insufficient_depth_returns_no_partial_answer (value : Expression)
    (index : NameIndex) (history : List SExpr) (lexicals : List LexicalDeclaration)
    (valid : Valid index history) :
    rewriteAt (engineBasePremises relations) language (expressionHeight index history lexicals value)
      (expressionCall value index history lexicals) = [] := by
  rw [expression_answers _ _ _ _ _ valid]
  simp

theorem wrong_found_payload_has_no_answer (fuel : Nat) (query stored : String)
    (different : query ≠ stored) (lexicals : List LexicalDeclaration) :
    rewriteAt (engineBasePremises relations) language fuel
      (call "BNFProductiveReferenceAfterLookupV1"
        [text query, PlainBnfKnownNamesSourceExecution.nameResult (some (text stored)),
          declarations lexicals]) = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    rw [productive_rewriteAt fuel _ (by
      simp [headedBy, relationHeads, call, encode, encodeList])]
    simp [rules_exact, observedRules, observed, lowerPremise?, splitCall?, mode?,
      applyRuleUsing, call, PlainBnfKnownNamesSourceExecution.nameResult,
      pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
      matchPattern, matchArgs, mergeBindings, List.foldlM,
      PlainBnfReferenceCollectionSourceExecution.encoded_text_eq_iff, different]

/-- Even individually well-formed lexical declarations may disagree when their
names collide. First lookup and existential semantics are then different. -/
theorem duplicate_lexical_names_can_change_the_semantic_answer :
    ∃ excluded : List Nat,
      PlainBnfSemanticAdmission.MatcherWellFormed (.except excluded) ∧
      PlainBnfSemanticAdmission.MatcherWellFormed (.except []) ∧
      Step (engineBasePremises relations) language
        (expressionCall (singleElement (.reference "x" controlSpan)) .empty []
          [controlDeclaration (.except excluded), controlDeclaration (.except [])])
        (result (answer false)) ∧
      PlainBnfGraphSemantics.ExpressionProductive ∅
        { startName := "s", lexicalDeclarations :=
            [controlDeclaration (.except excluded), controlDeclaration (.except [])] }
        (singleElement (.reference "x" controlSpan)) := by
  obtain ⟨excluded, valid, uninhabited⟩ :=
    PlainBnfLexicalInhabitation.well_formed_exclusion_can_be_uninhabited
  have domain : PlainBnfSemanticAdmission.MatcherWellFormed (.except excluded) := Or.inr valid
  have rejects : matcherMeaning (.except excluded) = false := by
    have exactMeaning := matcherMeaning_iff (controlDeclaration (.except excluded)) domain
    have notYes : matcherMeaning (.except excluded) ≠ true := fun yes =>
      uninhabited (exactMeaning.mp yes)
    exact Bool.eq_false_iff.mpr notYes
  refine ⟨excluded, domain, Or.inl rfl, ?_, ?_⟩
  · rw [expression_decoded_step_iff _ _ _ _ PlainBnfKnownNamesSourceExecution.valid_empty]
    simp [singleElement, expressionMeaning, alternativeMeaning, elementMeaning, referenceMeaning,
      member, firstDeclaration, controlDeclaration, lexicalMeaning, rejects]
  · refine ⟨{ elements := [.reference "x" controlSpan], span := controlSpan }, by
      simp [singleElement], ?_⟩
    intro element present
    simp only [List.mem_singleton] at present
    subst element
    exact Or.inr ⟨controlDeclaration (.except []), by simp,
      rfl, PlainBnfLexicalInhabitation.empty_exclusion_is_inhabited⟩

#print axioms source_translation_exact
#print axioms whole_closed
#print axioms expression_answers
#print axioms expression_step_iff
#print axioms expression_yes_iff_productive
#print axioms expression_no_iff_unproductive
#print axioms duplicate_lexical_names_can_change_the_semantic_answer

end Mettapedia.GSLT.Parsing.PlainBnfProductiveSourceExecution
