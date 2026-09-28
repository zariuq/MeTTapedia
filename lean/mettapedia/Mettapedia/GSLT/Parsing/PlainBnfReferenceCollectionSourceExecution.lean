import Mettapedia.GSLT.Parsing.PlainBnfHeapSourceExecution
import Mettapedia.GSLT.Parsing.PlainBnfReferenceSourceAdmission
import Mettapedia.GSLT.Parsing.PlainBnfStructuredDenotation

/-!
# Authored ordered grammar-reference collection

Actual append, lexical lookup, and reference-collection rules execute in
the existing contextual relation. The input carrier is the existing
source-spanned plain-BNF structure. The result intentionally projects names,
retaining their order and multiplicity while excluding lexical declarations.
The domain is decoded `StructuredDenotation` expressions and declarations:
names are Strings encoded as canonical Unicode scalar lists. Arbitrary edited
Integer text carriers, physical admission, and normalization are not asserted.
This is not physical parsing, generated PeTTa, or whole-scheduler adequacy.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfReferenceCollectionSourceExecution

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT
  (Rewrite Source Operator decodeList decodeOperator decodeRewrite atomToken?)
open SourceSExprPatternCodec (encode encodeList)
open SourceSExprPatternInstantiation (pattern patternList
  applyRuleBindings_of_binderFree binderFree_pattern)
open PlainBnfStructuredDenotation (SourceSpan Element Alternative Expression LexicalMatcher LexicalDeclaration)
open PlainBnfTrieSourceExecution (call result scalarRelations)
open PlainBnfIndexedCollectorSourceExecution
  (headedBy premiseClosed closed_extension disjoint_heads_do_not_match)
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

open PlainBnfReferenceSourceAdmission (graphSource admissionSource)

def mode? : String → Option (Nat × Nat)
  | "BNFAppendNamesV1" | "BNFLexicalReferenceLookupV1" |
    "BNFCollectExpressionReferencesV1" | "BNFCollectAlternativesReferencesV1" |
    "BNFCollectElementsReferencesV1" | "BNFCollectElementReferencesV1" |
    "BNFCollectReferenceAfterLexicalLookupV1" => some (2, 1)
  | _ => none

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

def appendRows : List Rewrite := (graphSource.rewrites.drop 5).take 2
def lookupRows : List Rewrite := (admissionSource.rewrites.drop 13).take 3
def collectionRows : List Rewrite := (graphSource.rewrites.drop 7).take 9

def appendRules : List RewriteRule := (appendRows.mapM lowerRule?).get (by rfl)
def lookupRules : List RewriteRule := (lookupRows.mapM lowerRule?).get (by rfl)
def collectionRules : List RewriteRule := (collectionRows.mapM lowerRule?).get (by rfl)

def appendLanguage : LanguageDef :=
  { name := "PlainBnfAuthoredNameAppend", types := [], terms := [], equations := [], rewrites := appendRules }
def lookupLanguage : LanguageDef :=
  { name := "PlainBnfAuthoredLexicalReferenceLookup", types := [], terms := [], equations := [], rewrites := lookupRules }
def language : LanguageDef :=
  { name := "PlainBnfAuthoredReferenceCollection", types := [], terms := [], equations := [],
    rewrites := appendRules ++ lookupRules ++ collectionRules }

theorem source_translation_exact :
    (appendRows ++ lookupRows ++ collectionRows).mapM lowerRule? = some language.rewrites := rfl

theorem append_occurrences_exact : appendRows.zipIdx 5 =
    ((graphSource.rewrites.zipIdx).drop 5).take 2 := rfl
theorem lookup_occurrences_exact : lookupRows.zipIdx 13 =
    ((admissionSource.rewrites.zipIdx).drop 13).take 3 := rfl
theorem collection_occurrences_exact : collectionRows.zipIdx 7 =
    ((graphSource.rewrites.zipIdx).drop 7).take 9 := rfl

def text (value : String) : SExpr :=
  PlainBnfCollectorSourceExecution.name (value.toList.map Char.toNat)

theorem text_existing_name_codec (value : String) :
    text value = PlainBnfCollectorSourceExecution.name (value.toList.map Char.toNat) := rfl

theorem text_injective : Function.Injective text := by
  intro left right same
  apply String.toList_injective
  exact (List.map_inj_right (fun _ _ equal => Char.toNat_inj.mp equal)).mp
    (PlainBnfCollectorSourceExecution.name_injective same)

theorem encoded_text_eq_iff (left right : String) :
    encode (text left) = encode (text right) ↔ left = right :=
  ⟨fun same => text_injective (SourceSExprPatternCodec.encode_injective same),
    fun same => congrArg (fun value => encode (text value)) same⟩

def span (value : SourceSpan) : SExpr :=
  .list [.atom "bnf-v1:source-span", .atom (toString value.start), .atom (toString value.stop)]

def element : Element → SExpr
  | .literal value location => .list [.atom "bnf-v1:literal", text value, span location]
  | .reference value location => .list [.atom "bnf-v1:reference", text value, span location]

def elements : List Element → SExpr
  | [] => .list [.atom "metta-nullary", .atom "bnf-v1:elements-nil"]
  | first :: rest => .list [.atom "bnf-v1:elements-cons", element first, elements rest]

def alternative (value : Alternative) : SExpr :=
  .list [.atom "bnf-v1:alternative", elements value.elements, span value.span]

def alternatives : List Alternative → SExpr
  | [] => .list [.atom "metta-nullary", .atom "bnf-v1:alternatives-nil"]
  | first :: rest => .list [.atom "bnf-v1:alternatives-cons", alternative first, alternatives rest]

def expression (value : Expression) : SExpr :=
  .list [.atom "bnf-v1:expression", alternatives value.alternatives, span value.span]

def scalars : List Nat → SExpr
  | [] => .list [.atom "metta-nullary", .atom "bnf-v1:scalars-nil"]
  | first :: rest => .list [.atom "bnf-v1:scalars-cons", .atom (toString first), scalars rest]

def matcher : LexicalMatcher → SExpr
  | .points values => .list [.atom "bnf-v1:lexical-points", scalars values]
  | .except values => .list [.atom "bnf-v1:lexical-except", scalars values]

def declaration (value : LexicalDeclaration) : SExpr :=
  .list [.atom "bnf-v1:lexical-declaration", text value.referenceName,
    .atom (reprStr value.className), matcher value.matcher, .atom (reprStr value.ruleLabel),
    .list [.atom "bnf-v1:lexical-origin", .atom (reprStr value.origin.authority),
      .atom (toString value.origin.occurrence)]]

def declarations : List LexicalDeclaration → SExpr
  | [] => .list [.atom "metta-nullary", .atom "bnf-v1:lexical-declarations-nil"]
  | first :: rest => .list [.atom "bnf-v1:lexical-declarations-cons", declaration first, declarations rest]

def names : List String → SExpr
  | [] => .atom "BNFNamesNilV1"
  | first :: rest => .list [.atom "BNFNamesConsV1", text first, names rest]

theorem names_injective : Function.Injective names := by
  intro left
  induction left with
  | nil => intro right same; cases right <;> simp_all [names]
  | cons first rest ih =>
      intro right same
      cases right with
      | nil => simp [names] at same
      | cons other following =>
          simp only [names, SExpr.list.injEq, List.cons.injEq, and_true, true_and] at same
          rw [text_injective same.1, ih same.2]

def appendCall (left right : List String) : Pattern := call "BNFAppendNamesV1" [names left, names right]
def lookupCall (key : String) (lexicals : List LexicalDeclaration) : Pattern :=
  call "BNFLexicalReferenceLookupV1" [text key, declarations lexicals]

def lookupResult : Option LexicalDeclaration → SExpr
  | none => .atom "BNFLexicalMissingV1"
  | some found => .list [.atom "BNFLexicalFoundV1", declaration found]

def firstDeclaration (key : String) (lexicals : List LexicalDeclaration) : Option LexicalDeclaration :=
  lexicals.find? (·.referenceName == key)

def grammarReferences (value : Expression) (lexicals : List LexicalDeclaration) : List String :=
  value.referenceNames.filter (fun key => !(lexicals.any (·.referenceName == key)))

/- These finite observations are checked against actual decoded rows. They do
not define the executable languages. -/
private def observed (name : String) (input output : SExpr)
    (body : List SExpr := []) : RewriteRule :=
  { name, typeContext := [], premises := (body.mapM lowerPremise?).getD [],
    left := pattern input, right := pattern output }

private def appendObserved : List RewriteRule :=
  [observed "bnf-append-names-nil-v1"
    (metta_sexpr% petta "(BNFAppendNamesV1 BNFNamesNilV1 ?right)")
    (metta_sexpr% petta "(?right)"),
   observed "bnf-append-names-cons-v1"
    (metta_sexpr% petta "(BNFAppendNamesV1 (BNFNamesConsV1 ?head ?tail) ?right)")
    (metta_sexpr% petta "((BNFNamesConsV1 ?head ?after))")
    [metta_sexpr% petta "(BNFAppendNamesV1 ?tail ?right ?after)"]]

private def lookupObserved : List RewriteRule :=
  [observed "bnf-lexical-reference-lookup-missing-v1"
    (metta_sexpr% petta "(BNFLexicalReferenceLookupV1 ?name (metta-nullary bnf-v1:lexical-declarations-nil))")
    (metta_sexpr% petta "(BNFLexicalMissingV1)"),
   observed "bnf-lexical-reference-lookup-found-v1"
    (metta_sexpr% petta "(BNFLexicalReferenceLookupV1 ?name (bnf-v1:lexical-declarations-cons (bnf-v1:lexical-declaration ?name ?class ?matcher ?label ?origin) ?tail))")
    (metta_sexpr% petta "((BNFLexicalFoundV1 (bnf-v1:lexical-declaration ?name ?class ?matcher ?label ?origin)))"),
   observed "bnf-lexical-reference-lookup-tail-v1"
    (metta_sexpr% petta "(BNFLexicalReferenceLookupV1 ?name (bnf-v1:lexical-declarations-cons (bnf-v1:lexical-declaration ?other ?class ?matcher ?label ?origin) ?tail))")
    (metta_sexpr% petta "(?result)")
    [metta_sexpr% petta "(different ?name ?other)",
     metta_sexpr% petta "(BNFLexicalReferenceLookupV1 ?name ?tail ?result)"]]

private theorem append_rules_exact : appendRules = appendObserved := rfl
private theorem lookup_rules_exact : lookupRules = lookupObserved := rfl

private theorem append_language_rules : appendLanguage.rewrites = appendObserved := append_rules_exact
private theorem lookup_language_rules : lookupLanguage.rewrites = lookupObserved := lookup_rules_exact

private def collectionObserved : List RewriteRule :=
  [observed "bnf-collect-expression-references-v1"
    (metta_sexpr% petta "(BNFCollectExpressionReferencesV1 (bnf-v1:expression ?alternatives ?span) ?lexicals)")
    (metta_sexpr% petta "(?references)")
    [metta_sexpr% petta "(BNFCollectAlternativesReferencesV1 ?alternatives ?lexicals ?references)"],
   observed "bnf-collect-alternatives-references-nil-v1"
    (metta_sexpr% petta "(BNFCollectAlternativesReferencesV1 (metta-nullary bnf-v1:alternatives-nil) ?lexicals)")
    (metta_sexpr% petta "(BNFNamesNilV1)"),
   observed "bnf-collect-alternatives-references-cons-v1"
    (metta_sexpr% petta "(BNFCollectAlternativesReferencesV1 (bnf-v1:alternatives-cons (bnf-v1:alternative ?elements ?span) ?tail) ?lexicals)")
    (metta_sexpr% petta "(?references)")
    [metta_sexpr% petta "(BNFCollectElementsReferencesV1 ?elements ?lexicals ?current)",
     metta_sexpr% petta "(BNFCollectAlternativesReferencesV1 ?tail ?lexicals ?following)",
     metta_sexpr% petta "(BNFAppendNamesV1 ?current ?following ?references)"],
   observed "bnf-collect-elements-references-nil-v1"
    (metta_sexpr% petta "(BNFCollectElementsReferencesV1 (metta-nullary bnf-v1:elements-nil) ?lexicals)")
    (metta_sexpr% petta "(BNFNamesNilV1)"),
   observed "bnf-collect-elements-references-cons-v1"
    (metta_sexpr% petta "(BNFCollectElementsReferencesV1 (bnf-v1:elements-cons ?element ?tail) ?lexicals)")
    (metta_sexpr% petta "(?references)")
    [metta_sexpr% petta "(BNFCollectElementReferencesV1 ?element ?lexicals ?current)",
     metta_sexpr% petta "(BNFCollectElementsReferencesV1 ?tail ?lexicals ?following)",
     metta_sexpr% petta "(BNFAppendNamesV1 ?current ?following ?references)"],
   observed "bnf-collect-literal-reference-v1"
    (metta_sexpr% petta "(BNFCollectElementReferencesV1 (bnf-v1:literal ?text ?span) ?lexicals)")
    (metta_sexpr% petta "(BNFNamesNilV1)"),
   observed "bnf-collect-nonterminal-reference-v1"
    (metta_sexpr% petta "(BNFCollectElementReferencesV1 (bnf-v1:reference ?name ?span) ?lexicals)")
    (metta_sexpr% petta "(?references)")
    [metta_sexpr% petta "(BNFLexicalReferenceLookupV1 ?name ?lexicals ?lookup)",
     metta_sexpr% petta "(BNFCollectReferenceAfterLexicalLookupV1 ?name ?lookup ?references)"],
   observed "bnf-collect-grammar-reference-v1"
    (metta_sexpr% petta "(BNFCollectReferenceAfterLexicalLookupV1 ?name BNFLexicalMissingV1)")
    (metta_sexpr% petta "((BNFNamesConsV1 ?name BNFNamesNilV1))"),
   observed "bnf-collect-lexical-reference-v1"
    (metta_sexpr% petta "(BNFCollectReferenceAfterLexicalLookupV1 ?name (BNFLexicalFoundV1 ?declaration))")
    (metta_sexpr% petta "(BNFNamesNilV1)")]

private theorem collection_rules_exact : collectionRules = collectionObserved := rfl

private def appendHeads := ["BNFAppendNamesV1"]
def lookupHeads := ["BNFLexicalReferenceLookupV1"]
private def collectionHeads := ["BNFCollectExpressionReferencesV1", "BNFCollectAlternativesReferencesV1",
  "BNFCollectElementsReferencesV1", "BNFCollectElementReferencesV1",
  "BNFCollectReferenceAfterLexicalLookupV1"]

private theorem append_closed : appendLanguage.rewrites.all
    (fun rule => rule.premises.all (premiseClosed appendHeads)) = true := by
  simp [append_language_rules, appendObserved, observed, premiseClosed, headedBy, appendHeads,
    lowerPremise?, splitCall?, mode?, pattern, patternList, encode,
    SourceIntegerProvider.sourceVariableToken]

theorem lookup_closed : lookupLanguage.rewrites.all
    (fun rule => rule.premises.all (premiseClosed lookupHeads)) = true := by
  simp [lookup_language_rules, lookupObserved, observed, premiseClosed, headedBy, lookupHeads,
    lowerPremise?, splitCall?, mode?, pattern, patternList, encode,
    SourceIntegerProvider.sourceVariableToken]

private theorem append_heads : appendRules.all (fun rule => headedBy appendHeads rule.left) = true := by
  simp [append_rules_exact, appendObserved, observed, headedBy, appendHeads,
    pattern, patternList, encode, SourceIntegerProvider.sourceVariableToken]
theorem lookup_heads : lookupRules.all (fun rule => headedBy lookupHeads rule.left) = true := by
  simp [lookup_rules_exact, lookupObserved, observed, headedBy, lookupHeads,
    pattern, patternList, encode, SourceIntegerProvider.sourceVariableToken]
private theorem collection_heads : collectionRules.all
    (fun rule => headedBy collectionHeads rule.left) = true := by
  simp [collection_rules_exact, collectionObserved, observed, headedBy, collectionHeads,
    pattern, patternList, encode, SourceIntegerProvider.sourceVariableToken]

/-- Observed call-family boundary for conservative source-language extension. -/
def relationHeads := ["BNFAppendNamesV1", "BNFLexicalReferenceLookupV1",
  "BNFCollectExpressionReferencesV1", "BNFCollectAlternativesReferencesV1",
  "BNFCollectElementsReferencesV1", "BNFCollectElementReferencesV1",
  "BNFCollectReferenceAfterLexicalLookupV1"]

theorem family_heads : language.rewrites.all
    (fun rule => headedBy relationHeads rule.left) = true := by
  simp [language, append_rules_exact, lookup_rules_exact, collection_rules_exact,
    appendObserved, lookupObserved, collectionObserved, observed, headedBy, relationHeads,
    pattern, patternList, encode, SourceIntegerProvider.sourceVariableToken]

theorem family_closed : language.rewrites.all
    (fun rule => rule.premises.all (premiseClosed relationHeads)) = true := by
  simp [language, append_rules_exact, lookup_rules_exact, collection_rules_exact,
    appendObserved, lookupObserved, collectionObserved, observed, premiseClosed, headedBy,
    relationHeads, lowerPremise?, splitCall?, mode?, pattern, patternList, encode,
    SourceIntegerProvider.sourceVariableToken]

private theorem append_extension (fuel : Nat) (source : Pattern)
    (headed : headedBy appendHeads source = true) :
    rewriteAt (engineBasePremises scalarRelations) language fuel source =
      rewriteAt (engineBasePremises scalarRelations) appendLanguage fuel source := by
  apply closed_extension appendHeads scalarRelations _ _ [] (lookupRules ++ collectionRules)
  · simp [language, appendLanguage]
  · intro rule member premise present
    exact List.all_eq_true.mp (List.all_eq_true.mp append_closed rule member) premise present
  · intro rule member value itsHead
    simp only [List.nil_append, List.mem_append] at member
    rcases member with member | member
    · exact disjoint_heads_do_not_match lookupHeads appendHeads (by
        simp [lookupHeads, appendHeads]) _ _
        (List.all_eq_true.mp lookup_heads rule member) itsHead
    · exact disjoint_heads_do_not_match collectionHeads appendHeads (by
        simp [collectionHeads, appendHeads]) _ _
        (List.all_eq_true.mp collection_heads rule member) itsHead
  · exact headed

private theorem lookup_extension (fuel : Nat) (source : Pattern)
    (headed : headedBy lookupHeads source = true) :
    rewriteAt (engineBasePremises scalarRelations) language fuel source =
      rewriteAt (engineBasePremises scalarRelations) lookupLanguage fuel source := by
  apply closed_extension lookupHeads scalarRelations _ _ appendRules collectionRules
  · rfl
  · intro rule member premise present
    exact List.all_eq_true.mp (List.all_eq_true.mp lookup_closed rule member) premise present
  · intro rule member value itsHead
    simp only [List.mem_append] at member
    rcases member with member | member
    · exact disjoint_heads_do_not_match appendHeads lookupHeads (by
        simp [lookupHeads, appendHeads]) _ _
        (List.all_eq_true.mp append_heads rule member) itsHead
    · exact disjoint_heads_do_not_match collectionHeads lookupHeads (by
        simp [collectionHeads, lookupHeads]) _ _
        (List.all_eq_true.mp collection_heads rule member) itsHead
  · exact headed

private theorem collection_rewriteAt (fuel : Nat) (source : Pattern)
    (headed : headedBy collectionHeads source = true) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1) source =
      collectionRules.flatMap (fun rule => applyRuleUsing (engineBasePremises scalarRelations)
        language (rewriteAt (engineBasePremises scalarRelations) language fuel) rule source) := by
  apply PlainBnfHeapSourceExecution.skip_unmatched_prefix _ language
    (appendRules ++ lookupRules) collectionRules rfl
  intro rule member
  simp only [List.mem_append] at member
  rcases member with member | member
  · exact disjoint_heads_do_not_match appendHeads collectionHeads (by
      simp [appendHeads, collectionHeads]) _ _
      (List.all_eq_true.mp append_heads rule member) headed
  · exact disjoint_heads_do_not_match lookupHeads collectionHeads (by
      simp [lookupHeads, collectionHeads]) _ _
      (List.all_eq_true.mp lookup_heads rule member) headed

private theorem append_nil (base : BasePremiseEvaluator) (fuel : Nat) (right : List String) :
    rewriteAt base appendLanguage (fuel + 1) (appendCall [] right) = [result (names right)] := by
  simp [rewriteAt, append_language_rules, appendObserved, observed,
    lowerPremise?, splitCall?, mode?, applyRuleUsing, appendCall, call, result, names,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, applyBindings]

private theorem append_cons (base : BasePremiseEvaluator) (fuel : Nat)
    (head : String) (tail right : List String) (answers : List (List String))
    (recursive : rewriteAt base appendLanguage fuel (appendCall tail right) =
      answers.map (result ∘ names)) :
    rewriteAt base appendLanguage (fuel + 1) (appendCall (head :: tail) right) =
      answers.map (fun answer => result (names (head :: answer))) := by
  rw [rewriteAt]
  simp [append_language_rules, appendObserved, observed,
    lowerPremise?, splitCall?, mode?, applyRuleUsing, appendCall, call, names,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, premiseStepUsing,
    applyBindings]
  simp only [appendCall, call, encode, encodeList] at recursive
  rw [recursive]
  simp [List.flatMap_map, result, encode, encodeList, matchPattern, matchArgs,
    List.foldlM, mergeBindings, ← List.map_eq_flatMap]

theorem append_answers (base : BasePremiseEvaluator) (fuel : Nat) (left right : List String) :
    rewriteAt base appendLanguage fuel (appendCall left right) =
      if left.length < fuel then [result (names (left ++ right))] else [] := by
  induction fuel generalizing left with
  | zero => simp [rewriteAt]
  | succ fuel ih =>
      cases left with
      | nil => simpa using append_nil base fuel right
      | cons head tail =>
          by_cases enough : tail.length < fuel
          · have step := append_cons base fuel head tail right [tail ++ right]
              (by simpa [enough] using ih tail)
            simpa [enough] using step
          · have step := append_cons base fuel head tail right []
              (by simpa [enough] using ih tail)
            simpa [enough] using step

def lookupHeight (key : String) : List LexicalDeclaration → Nat
  | [] => 0
  | head :: tail => if head.referenceName == key then 0 else 1 + lookupHeight key tail

private theorem lookup_nil (fuel : Nat) (key : String) :
    rewriteAt (engineBasePremises scalarRelations) lookupLanguage (fuel + 1) (lookupCall key []) =
      [result (lookupResult none)] := by
  simp [rewriteAt, lookup_language_rules, lookupObserved, observed,
    lowerPremise?, splitCall?, mode?, applyRuleUsing, lookupCall, call, result,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    declarations, lookupResult,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, applyBindings]

private theorem lookup_found (fuel : Nat) (head : LexicalDeclaration) (tail : List LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) lookupLanguage (fuel + 1)
      (lookupCall head.referenceName (head :: tail)) = [result (lookupResult (some head))] := by
  simp [rewriteAt, lookup_language_rules, lookupObserved, observed,
    lowerPremise?, splitCall?, mode?, applyRuleUsing, lookupCall, call, result,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    declarations, declaration, lookupResult,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, premiseStepUsing,
    applyBindings, engineBasePremises, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, scalarRelations]

private theorem lookup_other (fuel : Nat) (key : String) (head : LexicalDeclaration)
    (tail : List LexicalDeclaration) (different : key ≠ head.referenceName)
    (answers : List SExpr)
    (recursive : rewriteAt (engineBasePremises scalarRelations) lookupLanguage fuel
      (lookupCall key tail) = answers.map result) :
    rewriteAt (engineBasePremises scalarRelations) lookupLanguage (fuel + 1)
      (lookupCall key (head :: tail)) = answers.map result := by
  rw [rewriteAt]
  simp [lookup_language_rules, lookupObserved, observed,
    lowerPremise?, splitCall?, mode?, applyRuleUsing, lookupCall, call,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    declarations, declaration,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, premiseStepUsing,
    applyBindings, engineBasePremises, premiseStepWithEnv, relationQueryStep,
    builtinRelationTuples, scalarRelations, encoded_text_eq_iff, different,
    matchRelationArgs, matchRelationArgument, Bindings.lookup]
  simp only [lookupCall, call, encode, encodeList, scalarRelations] at recursive
  rw [recursive]
  simp [List.flatMap_map, result, encode, encodeList, matchPattern, matchArgs,
    List.foldlM, mergeBindings, ← List.map_eq_flatMap]

theorem lookup_answers (fuel : Nat) (key : String) (lexicals : List LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) lookupLanguage fuel (lookupCall key lexicals) =
      if lookupHeight key lexicals < fuel then
        [result (lookupResult (firstDeclaration key lexicals))] else [] := by
  induction fuel generalizing lexicals with
  | zero => simp [rewriteAt]
  | succ fuel ih =>
      cases lexicals with
      | nil => simpa [lookupHeight, firstDeclaration] using lookup_nil fuel key
      | cons head tail =>
          by_cases same : key = head.referenceName
          · subst key
            simpa [lookupHeight, firstDeclaration] using lookup_found fuel head tail
          · have other : head.referenceName ≠ key := Ne.symm same
            by_cases enough : lookupHeight key tail < fuel
            · have step := lookup_other fuel key head tail same
                [lookupResult (firstDeclaration key tail)] (by simpa [enough] using ih tail)
              have bound : 1 + lookupHeight key tail ≤ fuel := by omega
              simpa [lookupHeight, firstDeclaration, other, bound] using step
            · have step := lookup_other fuel key head tail same [] (by simpa [enough] using ih tail)
              have bound : ¬ 1 + lookupHeight key tail ≤ fuel := by omega
              simpa [lookupHeight, firstDeclaration, other, bound] using step

theorem append_in_collection (fuel : Nat) (left right : List String) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (appendCall left right) =
      if left.length < fuel then [result (names (left ++ right))] else [] := by
  rw [append_extension fuel _ (by simp [headedBy, appendHeads, appendCall, call, encode, encodeList])]
  exact append_answers _ _ _ _

theorem lookup_in_collection (fuel : Nat) (key : String) (lexicals : List LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (lookupCall key lexicals) =
      if lookupHeight key lexicals < fuel then
        [result (lookupResult (firstDeclaration key lexicals))] else [] := by
  rw [lookup_extension fuel _ (by simp [headedBy, lookupHeads, lookupCall, call, encode, encodeList])]
  exact lookup_answers _ _ _

def afterCall (key : String) (found : Option LexicalDeclaration) : Pattern :=
  call "BNFCollectReferenceAfterLexicalLookupV1" [text key, lookupResult found]
def elementCall (value : Element) (lexicals : List LexicalDeclaration) : Pattern :=
  call "BNFCollectElementReferencesV1" [element value, declarations lexicals]
def elementsCall (value : List Element) (lexicals : List LexicalDeclaration) : Pattern :=
  call "BNFCollectElementsReferencesV1" [elements value, declarations lexicals]
def alternativesCall (value : List Alternative) (lexicals : List LexicalDeclaration) : Pattern :=
  call "BNFCollectAlternativesReferencesV1" [alternatives value, declarations lexicals]
def expressionCall (value : Expression) (lexicals : List LexicalDeclaration) : Pattern :=
  call "BNFCollectExpressionReferencesV1" [expression value, declarations lexicals]

def afterNames (key : String) : Option LexicalDeclaration → List String
  | none => [key]
  | some _ => []

theorem after_names_exact (key : String) (lexicals : List LexicalDeclaration) :
    afterNames key (firstDeclaration key lexicals) =
      if lexicals.any (·.referenceName == key) then [] else [key] := by
  induction lexicals with
  | nil => rfl
  | cons head tail ih =>
    by_cases same : head.referenceName = key <;>
      simp [firstDeclaration, same, afterNames] at ih ⊢
    exact ih

private theorem after_answers (fuel : Nat) (key : String) (found : Option LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1) (afterCall key found) =
      [result (names (afterNames key found))] := by
  rw [collection_rewriteAt fuel _ (by
    simp [afterCall, call, encode, encodeList, headedBy, collectionHeads])]
  cases found <;>
    simp [collection_rules_exact, collectionObserved, observed, lowerPremise?, splitCall?, mode?,
      applyRuleUsing, afterCall, call, result, lookupResult, afterNames, names,
      applyRuleBindings_of_binderFree, binderFree, binderFreeList,
      pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
      matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, applyBindings]

private theorem literal_answers (fuel : Nat) (value : String) (location : SourceSpan)
    (lexicals : List LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (elementCall (.literal value location) lexicals) = [result (names [])] := by
  rw [collection_rewriteAt fuel _ (by
    simp [elementCall, call, encode, encodeList, headedBy, collectionHeads])]
  simp [collection_rules_exact, collectionObserved, observed, lowerPremise?, splitCall?, mode?,
    applyRuleUsing, elementCall, call, result, element, names,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, applyBindings]

private theorem reference_none (fuel : Nat) (key : String) (location : SourceSpan)
    (lexicals : List LexicalDeclaration)
    (missing : rewriteAt (engineBasePremises scalarRelations) language fuel (lookupCall key lexicals) = []) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (elementCall (.reference key location) lexicals) = [] := by
  rw [collection_rewriteAt fuel _ (by
    simp [elementCall, call, encode, encodeList, headedBy, collectionHeads])]
  simp [collection_rules_exact, collectionObserved, observed, lowerPremise?, splitCall?, mode?,
    applyRuleUsing, elementCall, call, element,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, premiseStepUsing, applyBindings]
  simp only [lookupCall, call, encode, encodeList] at missing
  rw [missing]
  simp

private theorem reference_some (fuel : Nat) (key : String) (location : SourceSpan)
    (lexicals : List LexicalDeclaration) (found : Option LexicalDeclaration)
    (looked : rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (lookupCall key lexicals) = [result (lookupResult found)]) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 2)
      (elementCall (.reference key location) lexicals) = [result (names (afterNames key found))] := by
  rw [collection_rewriteAt (fuel + 1) _ (by
    simp [elementCall, call, encode, encodeList, headedBy, collectionHeads])]
  simp [collection_rules_exact, collectionObserved, observed, lowerPremise?, splitCall?, mode?,
    applyRuleUsing, elementCall, call, element,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, premiseStepUsing, applyBindings]
  simp only [lookupCall, call, result, encode, encodeList] at looked
  rw [looked]
  simp [matchPattern, matchArgs, mergeBindings, List.foldlM]
  have after := after_answers fuel key found
  simp only [afterCall, call, encode, encodeList] at after
  rw [after]
  simp [result, encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]

def elementNames (value : Element) (lexicals : List LexicalDeclaration) : List String :=
  value.referenceName?.toList.filter (fun key => !(lexicals.any (·.referenceName == key)))

def elementHeight (value : Element) (lexicals : List LexicalDeclaration) : Nat :=
  match value with
  | .literal _ _ => 0
  | .reference key _ => 1 + lookupHeight key lexicals

theorem element_answers (fuel : Nat) (value : Element) (lexicals : List LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (elementCall value lexicals) =
      if elementHeight value lexicals < fuel then [result (names (elementNames value lexicals))] else [] := by
  cases fuel with
  | zero => simp [rewriteAt]
  | succ fuel =>
    cases value with
    | literal value location =>
      simpa [elementHeight, elementNames, Element.referenceName?] using literal_answers fuel value location lexicals
    | reference key location =>
      by_cases enough : lookupHeight key lexicals < fuel
      · cases fuel with
        | zero => omega
        | succ smaller =>
          have step := reference_some smaller key location lexicals (firstDeclaration key lexicals)
            (by simpa [enough] using lookup_in_collection (smaller + 1) key lexicals)
          have bound : 1 + lookupHeight key lexicals < smaller + 1 + 1 := by omega
          cases contains : lexicals.any (·.referenceName == key) <;>
            simpa [elementHeight, bound, after_names_exact, elementNames, Element.referenceName?,
              contains] using step
      · have step := reference_none fuel key location lexicals
          (by simpa [enough] using lookup_in_collection fuel key lexicals)
        have bound : ¬ 1 + lookupHeight key lexicals < fuel + 1 := by omega
        simpa [elementHeight, bound] using step
def elementsNames (values : List Element) (lexicals : List LexicalDeclaration) : List String :=
  values.flatMap (elementNames · lexicals)

def elementsHeight : List Element → List LexicalDeclaration → Nat
  | [], _ => 0
  | head :: tail, lexicals =>
      1 + max (elementHeight head lexicals)
        (max (elementsHeight tail lexicals) (elementNames head lexicals).length)

private theorem elements_nil (fuel : Nat) (lexicals : List LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (elementsCall [] lexicals) = [result (names [])] := by
  rw [collection_rewriteAt fuel _ (by
    simp [elementsCall, call, encode, encodeList, headedBy, collectionHeads])]
  simp [collection_rules_exact, collectionObserved, observed, lowerPremise?, splitCall?, mode?,
    applyRuleUsing, elementsCall, call, result, elements, names,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, applyBindings]

private theorem elements_cons (fuel : Nat) (head : Element) (tail : List Element)
    (lexicals : List LexicalDeclaration) (current following : Option (List String))
    (first : rewriteAt (engineBasePremises scalarRelations) language fuel
      (elementCall head lexicals) = current.toList.map (result ∘ names))
    (rest : rewriteAt (engineBasePremises scalarRelations) language fuel
      (elementsCall tail lexicals) = following.toList.map (result ∘ names)) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (elementsCall (head :: tail) lexicals) =
      current.toList.flatMap (fun left => following.toList.flatMap (fun right =>
        if left.length < fuel then [result (names (left ++ right))] else [])) := by
  rw [collection_rewriteAt fuel _ (by
    simp [elementsCall, call, encode, encodeList, headedBy, collectionHeads])]
  simp [collection_rules_exact, collectionObserved, observed, lowerPremise?, splitCall?, mode?,
    applyRuleUsing, elementsCall, call, elements,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, premiseStepUsing, applyBindings]
  simp only [elementCall, call, encode, encodeList] at first
  rw [first]
  cases current with
  | none => simp
  | some left =>
    simp [result, encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]
    simp only [elementsCall, call, encode, encodeList] at rest
    rw [rest]
    cases following with
    | none => simp
    | some right =>
      simp [result, encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]
      have appended := append_in_collection fuel left right
      simp only [appendCall, call, encode, encodeList] at appended
      rw [appended]
      split_ifs <;>
        simp [result, encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]

theorem elements_answers (fuel : Nat) (values : List Element) (lexicals : List LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (elementsCall values lexicals) =
      if elementsHeight values lexicals < fuel then [result (names (elementsNames values lexicals))] else [] := by
  induction fuel generalizing values with
  | zero => simp [rewriteAt]
  | succ fuel ih =>
    cases values with
    | nil => simpa [elementsHeight, elementsNames] using elements_nil fuel lexicals
    | cons head tail =>
      have step := elements_cons fuel head tail lexicals
        (if elementHeight head lexicals < fuel then some (elementNames head lexicals) else none)
        (if elementsHeight tail lexicals < fuel then some (elementsNames tail lexicals) else none)
        (by split_ifs <;> simp_all [element_answers])
        (by split_ifs <;> simp_all)
      by_cases first : elementHeight head lexicals < fuel <;>
        by_cases rest : elementsHeight tail lexicals < fuel <;>
        by_cases appends : (elementNames head lexicals).length < fuel
      all_goals
        have height : (elementsHeight (head :: tail) lexicals < fuel + 1) ↔
            (elementHeight head lexicals < fuel ∧ elementsHeight tail lexicals < fuel ∧
              (elementNames head lexicals).length < fuel) := by
          simp only [elementsHeight]
          omega
        simpa [first, rest, appends, height, elementsNames] using step

def alternativesNames (values : List Alternative) (lexicals : List LexicalDeclaration) : List String :=
  values.flatMap (fun value => elementsNames value.elements lexicals)

def alternativesHeight : List Alternative → List LexicalDeclaration → Nat
  | [], _ => 0
  | head :: tail, lexicals =>
      1 + max (elementsHeight head.elements lexicals)
        (max (alternativesHeight tail lexicals) (elementsNames head.elements lexicals).length)

private theorem alternatives_nil (fuel : Nat) (lexicals : List LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (alternativesCall [] lexicals) = [result (names [])] := by
  rw [collection_rewriteAt fuel _ (by
    simp [alternativesCall, call, encode, encodeList, headedBy, collectionHeads])]
  simp [collection_rules_exact, collectionObserved, observed, lowerPremise?, splitCall?, mode?,
    applyRuleUsing, alternativesCall, call, result, alternatives, names,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, applyBindings]

private theorem alternatives_cons (fuel : Nat) (head : Alternative) (tail : List Alternative)
    (lexicals : List LexicalDeclaration) (current following : Option (List String))
    (first : rewriteAt (engineBasePremises scalarRelations) language fuel
      (elementsCall head.elements lexicals) = current.toList.map (result ∘ names))
    (rest : rewriteAt (engineBasePremises scalarRelations) language fuel
      (alternativesCall tail lexicals) = following.toList.map (result ∘ names)) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (alternativesCall (head :: tail) lexicals) =
      current.toList.flatMap (fun left => following.toList.flatMap (fun right =>
        if left.length < fuel then [result (names (left ++ right))] else [])) := by
  rw [collection_rewriteAt fuel _ (by
    simp [alternativesCall, call, encode, encodeList, headedBy, collectionHeads])]
  simp [collection_rules_exact, collectionObserved, observed, lowerPremise?, splitCall?, mode?,
    applyRuleUsing, alternativesCall, call, alternatives, alternative,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, premiseStepUsing, applyBindings]
  simp only [elementsCall, call, encode, encodeList] at first
  rw [first]
  cases current with
  | none => simp
  | some left =>
    simp [result, encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]
    simp only [alternativesCall, call, encode, encodeList] at rest
    rw [rest]
    cases following with
    | none => simp
    | some right =>
      simp [result, encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]
      have appended := append_in_collection fuel left right
      simp only [appendCall, call, encode, encodeList] at appended
      rw [appended]
      split_ifs <;>
        simp [result, encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]

theorem alternatives_answers (fuel : Nat) (values : List Alternative) (lexicals : List LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (alternativesCall values lexicals) =
      if alternativesHeight values lexicals < fuel then
        [result (names (alternativesNames values lexicals))] else [] := by
  induction fuel generalizing values with
  | zero => simp [rewriteAt]
  | succ fuel ih =>
    cases values with
    | nil => simpa [alternativesHeight, alternativesNames] using alternatives_nil fuel lexicals
    | cons head tail =>
      have step := alternatives_cons fuel head tail lexicals
        (if elementsHeight head.elements lexicals < fuel then some (elementsNames head.elements lexicals) else none)
        (if alternativesHeight tail lexicals < fuel then some (alternativesNames tail lexicals) else none)
        (by split_ifs <;> simp_all [elements_answers])
        (by split_ifs <;> simp_all)
      by_cases first : elementsHeight head.elements lexicals < fuel <;>
        by_cases rest : alternativesHeight tail lexicals < fuel <;>
        by_cases appends : (elementsNames head.elements lexicals).length < fuel
      all_goals
        have height : (alternativesHeight (head :: tail) lexicals < fuel + 1) ↔
            (elementsHeight head.elements lexicals < fuel ∧ alternativesHeight tail lexicals < fuel ∧
              (elementsNames head.elements lexicals).length < fuel) := by
          simp only [alternativesHeight]
          omega
        simpa [first, rest, appends, height, alternativesNames] using step

private theorem expression_step (fuel : Nat) (value : Expression) (lexicals : List LexicalDeclaration)
    (answers : List (List String))
    (recursive : rewriteAt (engineBasePremises scalarRelations) language fuel
      (alternativesCall value.alternatives lexicals) = answers.map (result ∘ names)) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (expressionCall value lexicals) = answers.map (result ∘ names) := by
  rw [collection_rewriteAt fuel _ (by
    simp [expressionCall, call, encode, encodeList, headedBy, collectionHeads])]
  simp [collection_rules_exact, collectionObserved, observed, lowerPremise?, splitCall?, mode?,
    applyRuleUsing, expressionCall, call, expression,
    applyRuleBindings_of_binderFree, binderFree, binderFreeList,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, premiseStepUsing, applyBindings]
  simp only [alternativesCall, call, encode, encodeList] at recursive
  rw [recursive]
  simp [List.flatMap_map, result, encode, encodeList, matchPattern, matchArgs,
    List.foldlM, mergeBindings, ← List.map_eq_flatMap]

theorem elements_names_exact (values : List Element) (lexicals : List LexicalDeclaration) :
    elementsNames values lexicals =
      (values.filterMap Element.referenceName?).filter (fun key => !(lexicals.any (·.referenceName == key))) := by
  rw [List.filterMap_eq_flatMap_toList, List.filter_flatMap]
  rfl

theorem alternatives_names_exact (values : List Alternative) (lexicals : List LexicalDeclaration) :
    alternativesNames values lexicals =
      (values.flatMap Alternative.referenceNames).filter (fun key => !(lexicals.any (·.referenceName == key))) := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    simpa [alternativesNames, Alternative.referenceNames, List.filter_append, elements_names_exact]
      using congrArg (fun rest => elementsNames head.elements lexicals ++ rest) ih

/-- Depth of the actual selected source dependency calls, not an answer-producing evaluator. -/
def expressionHeight (value : Expression) (lexicals : List LexicalDeclaration) : Nat :=
  1 + alternativesHeight value.alternatives lexicals

/-- Exact ordered answer list of the actual source family. The stated meaning
uses the existing structured expression's reference sequence, filtered only
by lexical membership; equal names at different positions remain repeated. -/
theorem expression_answers (fuel : Nat) (value : Expression) (lexicals : List LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (expressionCall value lexicals) =
      if expressionHeight value lexicals < fuel then [result (names (grammarReferences value lexicals))] else [] := by
  cases fuel with
  | zero => simp [rewriteAt]
  | succ fuel =>
    by_cases enough : alternativesHeight value.alternatives lexicals < fuel
    · have step := expression_step fuel value lexicals [alternativesNames value.alternatives lexicals]
        (by simpa [enough] using alternatives_answers fuel value.alternatives lexicals)
      have bound : expressionHeight value lexicals < fuel + 1 := by unfold expressionHeight; omega
      simpa [bound, alternatives_names_exact, grammarReferences, Expression.referenceNames] using step
    · have step := expression_step fuel value lexicals []
        (by simpa [enough] using alternatives_answers fuel value.alternatives lexicals)
      have bound : ¬ expressionHeight value lexicals < fuel + 1 := by unfold expressionHeight; omega
      simpa [bound] using step

theorem expression_step_iff (value : Expression) (lexicals : List LexicalDeclaration) (target : Pattern) :
    Step (engineBasePremises scalarRelations) language (expressionCall value lexicals) target ↔
      target = result (names (grammarReferences value lexicals)) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [expression_answers] at member
    split at member
    · simpa using member
    · cases member
  · rintro rfl
    exact ⟨expressionHeight value lexicals + 1, by simp [expression_answers]⟩

theorem result_names_injective : Function.Injective (result ∘ names) := by
  intro left right same
  apply names_injective
  have decoded := SourceSExprPatternCodec.encode_injective same
  simpa only [SExpr.list.injEq, List.cons.injEq, and_true] using decoded

theorem expression_decoded_step_iff (value : Expression) (lexicals : List LexicalDeclaration)
    (output : List String) :
    Step (engineBasePremises scalarRelations) language (expressionCall value lexicals) (result (names output)) ↔
      output = grammarReferences value lexicals := by
  rw [expression_step_iff]
  exact result_names_injective.eq_iff

theorem lexical_names_absent (value : Expression) (lexicals : List LexicalDeclaration)
    (output : List String)
    (returned : Step (engineBasePremises scalarRelations) language
      (expressionCall value lexicals) (result (names output)))
    (key : String) (present : key ∈ output) :
    ¬ lexicals.any (·.referenceName == key) := by
  rw [(expression_decoded_step_iff _ _ _).mp returned, grammarReferences] at present
  simpa using (List.mem_filter.mp present).2

theorem output_is_source_subsequence (value : Expression) (lexicals : List LexicalDeclaration)
    (output : List String)
    (returned : Step (engineBasePremises scalarRelations) language
      (expressionCall value lexicals) (result (names output))) :
    output.Sublist value.referenceNames := by
  rw [(expression_decoded_step_iff _ _ _).mp returned]
  exact List.filter_sublist

/-- Source rules are selected by their actual relation heads, retaining order;
the rest of both decoded sources has no selected call head. -/
theorem graph_selected_family : graphSource.rewrites.filter
    (fun row => (splitCall? row.head).isSome) = appendRows ++ collectionRows := by rfl

theorem admission_selected_family : admissionSource.rewrites.filter
    (fun row => (splitCall? row.head).isSome) = lookupRows := by rfl

private def location : SourceSpan := ⟨1, 2⟩
private def digitFirst : LexicalDeclaration :=
  ⟨"digit", "Digit", .points [48, 49], "digit-first", ⟨"control", 4⟩⟩
private def digitSecond : LexicalDeclaration :=
  ⟨"digit", "OtherDigit", .points [50], "digit-second", ⟨"control", 9⟩⟩
private def specimen : Expression :=
  ⟨[⟨[.literal "ignored" location, .reference "β" location, .reference "digit" location,
      .reference "β" location], location⟩,
    ⟨[], location⟩, ⟨[.reference "α" location], location⟩], location⟩

theorem first_lexical_occurrence_preserved :
    rewriteAt (engineBasePremises scalarRelations) lookupLanguage 1
      (lookupCall "digit" [digitFirst, digitSecond]) = [result (lookupResult (some digitFirst))] := by
  simpa only [digitFirst] using lookup_found 0 digitFirst [digitSecond]

theorem specimen_names : grammarReferences specimen [digitFirst, digitSecond] = ["β", "β", "α"] := by
  decide

/-- Two occurrences of β occur inside one returned name sequence; they are
not two answer occurrences. Literal and lexical leaves contribute no name. -/
theorem duplicate_reference_occurrences_preserved :
    rewriteAt (engineBasePremises scalarRelations) language
      (expressionHeight specimen [digitFirst, digitSecond] + 1)
      (expressionCall specimen [digitFirst, digitSecond]) = [result (names ["β", "β", "α"])] := by
  simp [expression_answers, specimen_names]

theorem deduplicated_reference_output_refused :
    ¬ Step (engineBasePremises scalarRelations) language
      (expressionCall specimen [digitFirst, digitSecond]) (result (names ["β", "α"])) := by
  rw [expression_decoded_step_iff, specimen_names]
  decide

theorem reordered_reference_output_refused :
    ¬ Step (engineBasePremises scalarRelations) language
      (expressionCall specimen [digitFirst, digitSecond]) (result (names ["α", "β", "β"])) := by
  rw [expression_decoded_step_iff, specimen_names]
  decide

theorem insufficient_depth_has_no_result (value : Expression) (lexicals : List LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) language (expressionHeight value lexicals)
      (expressionCall value lexicals) = [] := by simp [expression_answers]

theorem empty_expression_has_one_empty_sequence :
    rewriteAt (engineBasePremises scalarRelations) language 2
      (expressionCall ⟨[], location⟩ []) = [result (names [])] := by
  simp [expression_answers, expressionHeight, alternativesHeight,
    grammarReferences, Expression.referenceNames]

theorem expression_mode_rejects_extra_field (value : Expression) (lexicals : List LexicalDeclaration) :
    splitCall? (.list [.atom "BNFCollectExpressionReferencesV1", expression value,
      declarations lexicals, .atom "?references", .atom "extra"]) = none := by
  simp [splitCall?, mode?]

theorem scheduler_call_not_selected (input : SExpr) :
    splitCall? (.list [.atom "BNFDiscoveryRunV1", input]) = none := by simp [splitCall?, mode?]

#print axioms expression_answers
#print axioms expression_step_iff
#print axioms expression_decoded_step_iff
#print axioms graph_selected_family
#print axioms admission_selected_family
#print axioms duplicate_reference_occurrences_preserved

end Mettapedia.GSLT.Parsing.PlainBnfReferenceCollectionSourceExecution
