import Mettapedia.GSLT.Parsing.PlainBnfDefinitionIndexSourceExecution
import Mettapedia.GSLT.Parsing.PlainBnfReferenceCollectionSourceExecution
import Mettapedia.GSLT.Parsing.PlainBnfDeclarationAdmission

/-!
# Authored reference-resolution diagnostics

The literal/reference and after-lookup clauses are extracted from admission
occurrences 55–60. Their definition and lexical queries execute the existing
authored source families. An empty-origin constructed definition index supplies
well-shaped first-definition payloads, rather than treating every arbitrary
stored atom as a valid definition. The actual indexed collector's output is
also supported through its proved first-definition representation invariant,
retaining that returned index and its original lookup depth without rebuilding.

This selected leaf boundary checks existence of a resolution, not uniqueness.
Duplicate declarations and grammar/lexical collisions need the independent
admission checks. Outer entry/expression traversal and diagnostic concatenation
are separate source families; no full validation or native theorem is implied.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfReferenceValidationSourceExecution

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT (Rewrite decodeList)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open SourceSExprPatternCodec (encode encodeList)
open SourceSExprPatternInstantiation (pattern patternList)
open PlainBnfStructuredDenotation (SourceSpan Element LexicalDeclaration)
open PlainBnfReferenceCollectionSourceExecution
  (text span element declarations lookupCall lookupResult firstDeclaration lookupHeads)
open PlainBnfGraphNameTrie (Trie lookup)
open PlainBnfTrieSourceExecution (scalarRelations call result trie)
open PlainBnfDefinitionIndexSourceExecution
  (buildIndex declarationResult definitionLookupCall definitionResult)
open PlainBnfIndexedCollectorSourceExecution
  (headedBy premiseClosed closed_extension disjoint_heads_do_not_match)
open PlainBnfReferenceSourceAdmission (admissionSource)
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

abbrev NameIndex := Trie SExpr Nat
abbrev RankedDefinitions := List (PlainBnfSourceRank.Rank × PlainBnfDefinitionIndexSourceExecution.Definition Nat)
abbrev DefinitionResult := PlainBnfDeclarationSemantics.LookupResult SExpr SExpr

def mode? : String → Option (Nat × Nat)
  | "BNFScanElementReferencesV1" | "BNFReferenceAfterLexicalLookupV1" => some (4, 1)
  | "BNFReferenceAfterDefinitionLookupV1" => some (5, 1)
  | "BNFDefinitionLookupV1" | "BNFLexicalReferenceLookupV1" => some (2, 1)
  | _ => none

def splitCall? : SExpr → Option (SExpr × SExpr)
  | .list (.atom head :: arguments) => do
      let (inputs, outputs) ← mode? head
      if arguments.length = inputs + outputs then
        some (.list (.atom head :: arguments.take inputs), .list (arguments.drop inputs))
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

def rows : List Rewrite := (admissionSource.rewrites.drop 55).take 6
def rules : List RewriteRule := (rows.mapM lowerRule?).get (by rfl)
def dependencies : List RewriteRule :=
  PlainBnfDefinitionIndexSourceExecution.language.rewrites ++
    PlainBnfReferenceCollectionSourceExecution.lookupLanguage.rewrites
def language : LanguageDef :=
  { name := "PlainBnfAuthoredReferenceResolution", types := [], terms := [], equations := [],
    rewrites := dependencies ++ rules }

theorem source_translation_exact : rows.mapM lowerRule? = some rules := rfl
theorem source_occurrences_exact : rows.zipIdx 55 = ((admissionSource.rewrites.zipIdx).drop 55).take 6 := rfl

def relationHeads :=
  ["BNFScanElementReferencesV1", "BNFReferenceAfterDefinitionLookupV1", "BNFReferenceAfterLexicalLookupV1"]

theorem source_family_exhaustive : admissionSource.rewrites.filter (fun row => match row.head with
    | .list (.atom head :: _) => relationHeads.contains head
    | _ => false) = rows := rfl

/- These finite observations are checked against, and do not construct, the
actual source-derived rules above. -/
private def observed (name : String) (input output : SExpr) (body : List SExpr := []) : RewriteRule :=
  { name, typeContext := [], premises := (body.mapM lowerPremise?).getD [],
    left := pattern input, right := pattern output }

private def observedRules : List RewriteRule := [
  observed "bnf-scan-element-literal-v1"
    (metta_sexpr% petta "(BNFScanElementReferencesV1 ?owner (bnf-v1:literal ?text ?span) ?definitions ?lexicals)")
    (metta_sexpr% petta "(BNFDiagnosticsNilV1)"),
  observed "bnf-scan-element-reference-v1"
    (metta_sexpr% petta "(BNFScanElementReferencesV1 ?owner (bnf-v1:reference ?name ?span) ?definitions ?lexicals)")
    (metta_sexpr% petta "(?diagnostics)")
    [metta_sexpr% petta "(BNFDefinitionLookupV1 ?name ?definitions ?lookup)",
     metta_sexpr% petta "(BNFReferenceAfterDefinitionLookupV1 ?owner ?name ?span ?lookup ?lexicals ?diagnostics)"],
  observed "bnf-reference-found-v1"
    (metta_sexpr% petta "(BNFReferenceAfterDefinitionLookupV1 ?owner ?name ?span (BNFDefinitionFoundV1 ?expression ?firstSpan) ?lexicals)")
    (metta_sexpr% petta "(BNFDiagnosticsNilV1)"),
  observed "bnf-reference-definition-missing-v1"
    (metta_sexpr% petta "(BNFReferenceAfterDefinitionLookupV1 ?owner ?name ?span BNFDefinitionMissingV1 ?lexicals)")
    (metta_sexpr% petta "(?diagnostics)")
    [metta_sexpr% petta "(BNFLexicalReferenceLookupV1 ?name ?lexicals ?lookup)",
     metta_sexpr% petta "(BNFReferenceAfterLexicalLookupV1 ?owner ?name ?span ?lookup ?diagnostics)"],
  observed "bnf-reference-lexical-found-v1"
    (metta_sexpr% petta "(BNFReferenceAfterLexicalLookupV1 ?owner ?name ?span (BNFLexicalFoundV1 ?declaration))")
    (metta_sexpr% petta "(BNFDiagnosticsNilV1)"),
  observed "bnf-reference-unresolved-v1"
    (metta_sexpr% petta "(BNFReferenceAfterLexicalLookupV1 ?owner ?name ?span BNFLexicalMissingV1)")
    (metta_sexpr% petta "((BNFDiagnosticsConsV1 (BNFUnresolvedReferenceV1 ?owner ?name ?span) BNFDiagnosticsNilV1))")]

private theorem rules_exact : rules = observedRules := rfl

theorem family_heads : rules.all (fun rule => headedBy relationHeads rule.left) = true := by
  simp [rules_exact, observedRules, observed, headedBy, relationHeads,
    pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode]

private theorem definition_extension (fuel : Nat) (source : Pattern)
    (headed : headedBy PlainBnfDefinitionIndexSourceExecution.relationHeads source = true) :
    rewriteAt (engineBasePremises scalarRelations) language fuel source =
      rewriteAt (engineBasePremises scalarRelations) PlainBnfDefinitionIndexSourceExecution.language fuel source := by
  apply closed_extension PlainBnfDefinitionIndexSourceExecution.relationHeads scalarRelations _ _ []
    (PlainBnfReferenceCollectionSourceExecution.lookupLanguage.rewrites ++ rules)
  · simp [language, dependencies, List.append_assoc]
  · intro rule member premise present
    exact List.all_eq_true.mp
      (List.all_eq_true.mp PlainBnfDefinitionIndexSourceExecution.family_closed rule member) premise present
  · intro rule member value itsHead
    simp only [List.nil_append, List.mem_append] at member
    rcases member with member | member
    · exact disjoint_heads_do_not_match lookupHeads PlainBnfDefinitionIndexSourceExecution.relationHeads
        (by simp [lookupHeads, PlainBnfDefinitionIndexSourceExecution.relationHeads,
          PlainBnfDefinitionIndexSourceExecution.indexNames, PlainBnfIndexedCollectorSourceExecution.trieNames]) _ _
        (List.all_eq_true.mp PlainBnfReferenceCollectionSourceExecution.lookup_heads rule member) itsHead
    · exact disjoint_heads_do_not_match relationHeads PlainBnfDefinitionIndexSourceExecution.relationHeads
        (by simp [relationHeads, PlainBnfDefinitionIndexSourceExecution.relationHeads,
          PlainBnfDefinitionIndexSourceExecution.indexNames, PlainBnfIndexedCollectorSourceExecution.trieNames]) _ _
        (List.all_eq_true.mp family_heads rule member) itsHead
  · exact headed

private theorem lexical_extension (fuel : Nat) (source : Pattern)
    (headed : headedBy lookupHeads source = true) :
    rewriteAt (engineBasePremises scalarRelations) language fuel source =
      rewriteAt (engineBasePremises scalarRelations) PlainBnfReferenceCollectionSourceExecution.lookupLanguage fuel source := by
  apply closed_extension lookupHeads scalarRelations _ _
    PlainBnfDefinitionIndexSourceExecution.language.rewrites rules
  · rfl
  · intro rule member premise present
    exact List.all_eq_true.mp
      (List.all_eq_true.mp PlainBnfReferenceCollectionSourceExecution.lookup_closed rule member) premise present
  · intro rule member value itsHead
    simp only [List.mem_append] at member
    rcases member with member | member
    · exact disjoint_heads_do_not_match PlainBnfDefinitionIndexSourceExecution.relationHeads lookupHeads
        (by simp [lookupHeads, PlainBnfDefinitionIndexSourceExecution.relationHeads,
          PlainBnfDefinitionIndexSourceExecution.indexNames, PlainBnfIndexedCollectorSourceExecution.trieNames]) _ _
        (List.all_eq_true.mp PlainBnfDefinitionIndexSourceExecution.family_heads rule member) itsHead
    · exact disjoint_heads_do_not_match relationHeads lookupHeads (by simp [relationHeads, lookupHeads]) _ _
        (List.all_eq_true.mp family_heads rule member) itsHead
  · exact headed

private theorem resolution_rewriteAt (fuel : Nat) (source : Pattern)
    (headed : headedBy relationHeads source = true) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1) source =
      rules.flatMap (fun rule => applyRuleUsing (engineBasePremises scalarRelations) language
        (rewriteAt (engineBasePremises scalarRelations) language fuel) rule source) := by
  apply PlainBnfHeapSourceExecution.skip_unmatched_prefix _ language dependencies rules rfl fuel source
  intro rule member
  simp only [dependencies, List.mem_append] at member
  rcases member with member | member
  · exact disjoint_heads_do_not_match PlainBnfDefinitionIndexSourceExecution.relationHeads relationHeads
      (by simp [relationHeads, PlainBnfDefinitionIndexSourceExecution.relationHeads,
        PlainBnfDefinitionIndexSourceExecution.indexNames, PlainBnfIndexedCollectorSourceExecution.trieNames]) _ _
      (List.all_eq_true.mp PlainBnfDefinitionIndexSourceExecution.family_heads rule member) headed
  · exact disjoint_heads_do_not_match lookupHeads relationHeads (by simp [relationHeads, lookupHeads]) _ _
      (List.all_eq_true.mp PlainBnfReferenceCollectionSourceExecution.lookup_heads rule member) headed

def diagnostics : List SExpr → SExpr
  | [] => .atom "BNFDiagnosticsNilV1"
  | head :: tail => .list [.atom "BNFDiagnosticsConsV1", head, diagnostics tail]
def unresolved (owner key : String) (location : SourceSpan) : SExpr :=
  .list [.atom "BNFUnresolvedReferenceV1", text owner, text key, span location]
def indexWire (index : NameIndex) : SExpr := .list [.atom "BNFIndexedDefinitionsV1", trie index]
def elementCall (owner : String) (value : Element) (index : NameIndex)
    (lexicals : List LexicalDeclaration) : Pattern :=
  call "BNFScanElementReferencesV1" [text owner, element value, indexWire index, declarations lexicals]
def afterDefinitionCall (owner key : String) (location : SourceSpan) (found : DefinitionResult)
    (lexicals : List LexicalDeclaration) : Pattern :=
  call "BNFReferenceAfterDefinitionLookupV1" [text owner, text key, span location,
    declarationResult found, declarations lexicals]
def afterLexicalCall (owner key : String) (location : SourceSpan) (found : Option LexicalDeclaration) : Pattern :=
  call "BNFReferenceAfterLexicalLookupV1" [text owner, text key, span location, lookupResult found]

theorem definition_lookup_answers (fuel : Nat) (key : String) (index : NameIndex) :
    rewriteAt (engineBasePremises scalarRelations) language fuel
      (definitionLookupCall (key.toList.map Char.toNat) index) =
      if PlainBnfTrieSourceExecution.lookupHeight (key.toList.map Char.toNat) index + 1 < fuel then
        [result (definitionResult (lookup (key.toList.map Char.toNat) index))] else [] := by
  rw [definition_extension fuel _ (by
    simp [headedBy, PlainBnfDefinitionIndexSourceExecution.relationHeads,
      PlainBnfDefinitionIndexSourceExecution.indexNames, definitionLookupCall, call, encode, encodeList])]
  exact PlainBnfDefinitionIndexSourceExecution.definition_lookup_answers _ _ _

theorem constructed_lookup_answers (fuel : Nat) (input : RankedDefinitions) (key : String) :
    rewriteAt (engineBasePremises scalarRelations) language fuel
      (definitionLookupCall (key.toList.map Char.toNat) (buildIndex input .empty)) =
      if PlainBnfTrieSourceExecution.lookupHeight (key.toList.map Char.toNat) (buildIndex input .empty) + 1 < fuel then
        [result (declarationResult (PlainBnfDeclarationSemantics.lookup
          (key.toList.map Char.toNat) (input.map Prod.snd)))] else [] := by
  rw [definition_lookup_answers, PlainBnfDefinitionIndexSourceExecution.lookup_buildIndex]
  simp only [PlainBnfGraphNameTrie.lookup_empty, Option.none_or]
  rw [PlainBnfDefinitionIndexSourceExecution.first_occurrence_matches_declaration_lookup]

theorem lexical_lookup_answers (fuel : Nat) (key : String) (lexicals : List LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (lookupCall key lexicals) =
      if PlainBnfReferenceCollectionSourceExecution.lookupHeight key lexicals < fuel then
        [result (lookupResult (firstDeclaration key lexicals))] else [] := by
  rw [lexical_extension fuel _ (by simp [headedBy, lookupHeads, lookupCall, call, encode, encodeList])]
  exact PlainBnfReferenceCollectionSourceExecution.lookup_answers _ _ _

def afterLexicalMeaning (owner key : String) (location : SourceSpan) (found : Option LexicalDeclaration) : List SExpr :=
  if found.isSome then [] else [unresolved owner key location]
def afterDefinitionMeaning (owner key : String) (location : SourceSpan) (found : DefinitionResult)
    (lexicals : List LexicalDeclaration) : List SExpr :=
  match found with
  | .found _ _ => []
  | .missing => afterLexicalMeaning owner key location (firstDeclaration key lexicals)
def elementMeaning (owner : String) (value : Element) (input : RankedDefinitions)
    (lexicals : List LexicalDeclaration) : List SExpr :=
  match value with
  | .literal _ _ => []
  | .reference key location => afterDefinitionMeaning owner key location
      (PlainBnfDeclarationSemantics.lookup (key.toList.map Char.toNat) (input.map Prod.snd)) lexicals

def afterDefinitionHeight (key : String) (found : DefinitionResult) (lexicals : List LexicalDeclaration) : Nat :=
  match found with
  | .found _ _ => 0
  | .missing => PlainBnfReferenceCollectionSourceExecution.lookupHeight key lexicals + 1
def elementHeight (value : Element) (input : RankedDefinitions) (lexicals : List LexicalDeclaration) : Nat :=
  match value with
  | .literal _ _ => 0
  | .reference key _ =>
      max (PlainBnfTrieSourceExecution.lookupHeight (key.toList.map Char.toNat) (buildIndex input .empty) + 1)
        (afterDefinitionHeight key
          (PlainBnfDeclarationSemantics.lookup (key.toList.map Char.toNat) (input.map Prod.snd)) lexicals) + 1

local macro "resolution_reduce" : tactic =>
  `(tactic| (
    rw [resolution_rewriteAt _ _ (by
      simp [headedBy, relationHeads, elementCall, afterDefinitionCall, afterLexicalCall, call, encode, encodeList])]
    simp [rules_exact, observedRules, observed, lowerPremise?, splitCall?, mode?,
      applyRuleUsing, elementCall, afterDefinitionCall, afterLexicalCall, indexWire,
      call, element, declarationResult, lookupResult,
      pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
      matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing,
      premiseStepUsing, applyBindings]))

local macro "resolution_finish" : tactic =>
  `(tactic| simp [result, List.flatMap_map, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, ← List.map_eq_flatMap])

theorem after_lexical_answers (fuel : Nat) (owner key : String) (location : SourceSpan)
    (found : Option LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) language fuel (afterLexicalCall owner key location found) =
      if 0 < fuel then [result (diagnostics (afterLexicalMeaning owner key location found))] else [] := by
  cases fuel with
  | zero => simp [rewriteAt]
  | succ fuel =>
      cases found <;> resolution_reduce <;>
        simp [diagnostics, afterLexicalMeaning, unresolved] <;> resolution_finish

private theorem definition_found_answers (fuel : Nat) (owner key : String) (location : SourceSpan)
    (body firstSpan : SExpr) (lexicals : List LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (afterDefinitionCall owner key location (.found body firstSpan) lexicals) =
      [result (diagnostics [])] := by
  resolution_reduce
  simp [diagnostics]
  resolution_finish

private theorem definition_missing_no_lookup (fuel : Nat) (owner key : String) (location : SourceSpan)
    (lexicals : List LexicalDeclaration)
    (absent : rewriteAt (engineBasePremises scalarRelations) language fuel (lookupCall key lexicals) = []) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (afterDefinitionCall owner key location .missing lexicals) = [] := by
  resolution_reduce
  simp only [lookupCall, call, encode, encodeList] at absent
  rw [absent]
  simp

private theorem definition_missing_some_lookup (fuel : Nat) (owner key : String) (location : SourceSpan)
    (lexicals : List LexicalDeclaration) (found : Option LexicalDeclaration) (answers : List SExpr)
    (looked : rewriteAt (engineBasePremises scalarRelations) language fuel (lookupCall key lexicals) =
      [result (lookupResult found)])
    (continued : rewriteAt (engineBasePremises scalarRelations) language fuel
      (afterLexicalCall owner key location found) = answers.map result) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (afterDefinitionCall owner key location .missing lexicals) = answers.map result := by
  resolution_reduce
  simp only [lookupCall, call, encode, encodeList] at looked
  rw [looked]
  simp [result, encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]
  simp only [afterLexicalCall, call, encode, encodeList] at continued
  rw [continued]
  resolution_finish

theorem after_definition_answers (fuel : Nat) (owner key : String) (location : SourceSpan)
    (found : DefinitionResult) (lexicals : List LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) language fuel
      (afterDefinitionCall owner key location found lexicals) =
      if afterDefinitionHeight key found lexicals < fuel then
        [result (diagnostics (afterDefinitionMeaning owner key location found lexicals))] else [] := by
  cases fuel with
  | zero => simp [rewriteAt]
  | succ fuel =>
      cases found with
      | found body firstSpan =>
          simpa [afterDefinitionHeight, afterDefinitionMeaning] using
            definition_found_answers fuel owner key location body firstSpan lexicals
      | missing =>
          have queried := lexical_lookup_answers fuel key lexicals
          by_cases enough : PlainBnfReferenceCollectionSourceExecution.lookupHeight key lexicals < fuel
          · rw [if_pos enough] at queried
            have positive : 0 < fuel := by omega
            have continued : rewriteAt (engineBasePremises scalarRelations) language fuel
                (afterLexicalCall owner key location (firstDeclaration key lexicals)) =
                [diagnostics (afterLexicalMeaning owner key location (firstDeclaration key lexicals))].map result := by
              simp [after_lexical_answers, positive]
            have step := definition_missing_some_lookup fuel owner key location lexicals _ _ queried continued
            simpa [afterDefinitionHeight, afterDefinitionMeaning, enough] using step
          · rw [if_neg enough] at queried
            have step := definition_missing_no_lookup fuel owner key location lexicals queried
            simpa [afterDefinitionHeight, enough] using step

private theorem literal_answers (fuel : Nat) (owner value : String) (location : SourceSpan)
    (index : NameIndex) (lexicals : List LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (elementCall owner (.literal value location) index lexicals) = [result (diagnostics [])] := by
  resolution_reduce
  simp [diagnostics]
  resolution_finish

private theorem reference_no_lookup (fuel : Nat) (owner key : String) (location : SourceSpan)
    (index : NameIndex) (lexicals : List LexicalDeclaration)
    (absent : rewriteAt (engineBasePremises scalarRelations) language fuel
      (definitionLookupCall (key.toList.map Char.toNat) index) = []) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (elementCall owner (.reference key location) index lexicals) = [] := by
  resolution_reduce
  simp only [definitionLookupCall, call, encode, encodeList] at absent
  simp only [text]
  rw [absent]
  simp

private theorem reference_some_lookup (fuel : Nat) (owner key : String) (location : SourceSpan)
    (index : NameIndex) (lexicals : List LexicalDeclaration) (found : DefinitionResult) (answers : List SExpr)
    (looked : rewriteAt (engineBasePremises scalarRelations) language fuel
      (definitionLookupCall (key.toList.map Char.toNat) index) = [result (declarationResult found)])
    (continued : rewriteAt (engineBasePremises scalarRelations) language fuel
      (afterDefinitionCall owner key location found lexicals) = answers.map result) :
    rewriteAt (engineBasePremises scalarRelations) language (fuel + 1)
      (elementCall owner (.reference key location) index lexicals) = answers.map result := by
  resolution_reduce
  simp only [definitionLookupCall, call, encode, encodeList] at looked
  simp only [text]
  rw [looked]
  simp [result, encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]
  simp only [afterDefinitionCall, call, text, encode, encodeList] at continued
  rw [continued]
  resolution_finish

/-- Independent leaf observation over the returned declaration list. -/
def declarationElementMeaning (owner : String) (value : Element)
    (definitions : List (PlainBnfDefinitionIndexSourceExecution.Definition Nat))
    (lexicals : List LexicalDeclaration) : List SExpr :=
  match value with
  | .literal _ _ => []
  | .reference key location => afterDefinitionMeaning owner key location
      (PlainBnfDeclarationSemantics.lookup (key.toList.map Char.toNat) definitions) lexicals

/-- The bound measures lookup in the actual supplied trie, not a reconstructed
trie with merely equivalent lookup values. -/
def indexElementHeight (value : Element) (index : NameIndex)
    (definitions : List (PlainBnfDefinitionIndexSourceExecution.Definition Nat))
    (lexicals : List LexicalDeclaration) : Nat :=
  match value with
  | .literal _ _ => 0
  | .reference key _ =>
      max (PlainBnfTrieSourceExecution.lookupHeight (key.toList.map Char.toNat) index + 1)
        (afterDefinitionHeight key
          (PlainBnfDeclarationSemantics.lookup (key.toList.map Char.toNat) definitions) lexicals) + 1

private theorem element_answers_of_lookup_result (fuel : Nat) (owner : String) (value : Element)
    (index : NameIndex) (definitions : List (PlainBnfDefinitionIndexSourceExecution.Definition Nat))
    (lexicals : List LexicalDeclaration)
    (represented : ∀ key : String,
      definitionResult (lookup (key.toList.map Char.toNat) index) =
        declarationResult (PlainBnfDeclarationSemantics.lookup (key.toList.map Char.toNat) definitions)) :
    rewriteAt (engineBasePremises scalarRelations) language fuel
      (elementCall owner value index lexicals) =
      if indexElementHeight value index definitions lexicals < fuel then
        [result (diagnostics (declarationElementMeaning owner value definitions lexicals))] else [] := by
  cases fuel with
  | zero => simp [rewriteAt]
  | succ fuel =>
      cases value with
      | literal value location =>
          simpa [indexElementHeight, declarationElementMeaning] using
            literal_answers fuel owner value location index lexicals
      | reference key location =>
          have queried := definition_lookup_answers fuel key index
          rw [represented key] at queried
          have continued := after_definition_answers fuel owner key location
            (PlainBnfDeclarationSemantics.lookup (key.toList.map Char.toNat) definitions) lexicals
          by_cases lookupEnough : PlainBnfTrieSourceExecution.lookupHeight
              (key.toList.map Char.toNat) index + 1 < fuel
          · rw [if_pos lookupEnough] at queried
            let found := PlainBnfDeclarationSemantics.lookup (key.toList.map Char.toNat) definitions
            let output := diagnostics (afterDefinitionMeaning owner key location found lexicals)
            have recursiveAnswers : rewriteAt (engineBasePremises scalarRelations) language fuel
                (afterDefinitionCall owner key location found lexicals) =
                (if afterDefinitionHeight key found lexicals < fuel then [output] else []).map result := by
              rw [continued]
              split <;> rfl
            rw [reference_some_lookup fuel owner key location _ lexicals _ _ queried recursiveAnswers]
            by_cases tailEnough : afterDefinitionHeight key found lexicals < fuel
            · have enough : indexElementHeight (.reference key location) index definitions lexicals < fuel + 1 := by
                simp only [indexElementHeight]
                dsimp only [found] at tailEnough
                omega
              simp [tailEnough, enough, output, declarationElementMeaning, found]
            · have short : ¬ indexElementHeight (.reference key location) index definitions lexicals < fuel + 1 := by
                simp only [indexElementHeight]
                dsimp only [found] at tailEnough
                omega
              simp [tailEnough, short]
          · rw [if_neg lookupEnough] at queried
            rw [reference_no_lookup fuel owner key location _ lexicals queried]
            have short : ¬ indexElementHeight (.reference key location) index definitions lexicals < fuel + 1 := by
              simp only [indexElementHeight]
              omega
            simp [short]

/-- Exact source answers with the real independently constructed index. The
original definition bodies and spans are obtained from actual trie lookup. -/
theorem element_answers (fuel : Nat) (owner : String) (value : Element) (input : RankedDefinitions)
    (lexicals : List LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) language fuel
      (elementCall owner value (buildIndex input .empty) lexicals) =
      if elementHeight value input lexicals < fuel then
        [result (diagnostics (elementMeaning owner value input lexicals))] else [] := by
  have represented : ∀ key : String,
      definitionResult (lookup (key.toList.map Char.toNat) (buildIndex input .empty)) =
        declarationResult (PlainBnfDeclarationSemantics.lookup (key.toList.map Char.toNat) (input.map Prod.snd)) := by
    intro key
    rw [PlainBnfDefinitionIndexSourceExecution.lookup_buildIndex]
    simp only [PlainBnfGraphNameTrie.lookup_empty, Option.none_or]
    exact PlainBnfDefinitionIndexSourceExecution.first_occurrence_matches_declaration_lookup input _
  have general := element_answers_of_lookup_result fuel owner value
    (buildIndex input .empty) (input.map Prod.snd) lexicals represented
  cases value <;> exact general

abbrev CollectorInput := List (PlainBnfIndexedCollectorSourceExecution.Entry Nat)
abbrev CollectorOutput :=
  (List (PlainBnfIndexedCollectorSourceExecution.Definition Nat) ×
    List (PlainBnfIndexedCollectorSourceExecution.Diagnostic Nat)) ×
    PlainBnfIndexedCollectorSourceExecution.Index Nat

/-- The real collector-produced index executes the leaf query with its own
lookup bound. The first-definition payload equation is derived from the actual
collector Step, not supplied as a callback or an assumed rebuilding identity. -/
theorem collector_element_answers (fuel : Nat) (owner : String) (value : Element)
    (input : CollectorInput) (output : CollectorOutput)
    (executed : Step (engineBasePremises scalarRelations) PlainBnfIndexedCollectorSourceExecution.language
      (PlainBnfIndexedCollectorSourceExecution.collectCall input)
      (PlainBnfIndexedCollectorSourceExecution.encodeResult output))
    (lexicals : List LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) language fuel
      (elementCall owner value (PlainBnfIndexedCollectorSourceExecution.indexTrie output.2) lexicals) =
      if indexElementHeight value (PlainBnfIndexedCollectorSourceExecution.indexTrie output.2) output.1.1 lexicals < fuel then
        [result (diagnostics (declarationElementMeaning owner value output.1.1 lexicals))] else [] := by
  exact element_answers_of_lookup_result fuel owner value _ output.1.1 lexicals
    (fun key => PlainBnfDeclarationAdmission.source_index_result input output executed (key.toList.map Char.toNat))

theorem collector_element_step_iff (owner : String) (value : Element)
    (input : CollectorInput) (output : CollectorOutput)
    (executed : Step (engineBasePremises scalarRelations) PlainBnfIndexedCollectorSourceExecution.language
      (PlainBnfIndexedCollectorSourceExecution.collectCall input)
      (PlainBnfIndexedCollectorSourceExecution.encodeResult output))
    (lexicals : List LexicalDeclaration) (target : Pattern) :
    Step (engineBasePremises scalarRelations) language
      (elementCall owner value (PlainBnfIndexedCollectorSourceExecution.indexTrie output.2) lexicals) target ↔
      target = result (diagnostics (declarationElementMeaning owner value output.1.1 lexicals)) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [collector_element_answers fuel owner value input output executed] at member
    split at member
    · simpa using member
    · cases member
  · rintro rfl
    exact ⟨indexElementHeight value (PlainBnfIndexedCollectorSourceExecution.indexTrie output.2) output.1.1 lexicals + 1,
      by simp [collector_element_answers _ _ _ input output executed]⟩

/-- Insufficient depth remains an empty answer stream, even for a reference
whose eventual result is successful empty diagnostics. -/
theorem collector_element_short (fuel : Nat) (owner : String) (value : Element)
    (input : CollectorInput) (output : CollectorOutput)
    (executed : Step (engineBasePremises scalarRelations) PlainBnfIndexedCollectorSourceExecution.language
      (PlainBnfIndexedCollectorSourceExecution.collectCall input)
      (PlainBnfIndexedCollectorSourceExecution.encodeResult output))
    (lexicals : List LexicalDeclaration)
    (short : fuel ≤ indexElementHeight value
      (PlainBnfIndexedCollectorSourceExecution.indexTrie output.2) output.1.1 lexicals) :
    rewriteAt (engineBasePremises scalarRelations) language fuel
      (elementCall owner value (PlainBnfIndexedCollectorSourceExecution.indexTrie output.2) lexicals) = [] := by
  rw [collector_element_answers fuel owner value input output executed]
  exact if_neg (by omega)

theorem collector_element_answer_occurrences_le_one (fuel : Nat) (owner : String) (value : Element)
    (input : CollectorInput) (output : CollectorOutput)
    (executed : Step (engineBasePremises scalarRelations) PlainBnfIndexedCollectorSourceExecution.language
      (PlainBnfIndexedCollectorSourceExecution.collectCall input)
      (PlainBnfIndexedCollectorSourceExecution.encodeResult output))
    (lexicals : List LexicalDeclaration) :
    (rewriteAt (engineBasePremises scalarRelations) language fuel
      (elementCall owner value (PlainBnfIndexedCollectorSourceExecution.indexTrie output.2) lexicals)).length ≤ 1 := by
  rw [collector_element_answers fuel owner value input output executed]
  split <;> simp

theorem element_step_iff (owner : String) (value : Element) (input : RankedDefinitions)
    (lexicals : List LexicalDeclaration) (target : Pattern) :
    Step (engineBasePremises scalarRelations) language
      (elementCall owner value (buildIndex input .empty) lexicals) target ↔
      target = result (diagnostics (elementMeaning owner value input lexicals)) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [element_answers] at member
    split at member
    · simpa using member
    · cases member
  · rintro rfl
    exact ⟨elementHeight value input lexicals + 1, by simp [element_answers]⟩

/-- Actual source index construction discharges the index premise; no
caller-supplied lookup truth table is part of this interface. -/
theorem indexed_element_step_iff (owner : String) (value : Element) (input : RankedDefinitions)
    (index : NameIndex) (lexicals : List LexicalDeclaration) (target : Pattern)
    (constructed : Step (engineBasePremises scalarRelations) PlainBnfDefinitionIndexSourceExecution.language
      (PlainBnfDefinitionIndexSourceExecution.indexCall input .empty) (result (trie index))) :
    Step (engineBasePremises scalarRelations) language (elementCall owner value index lexicals) target ↔
      target = result (diagnostics (elementMeaning owner value input lexicals)) := by
  have exactIndex := (PlainBnfDefinitionIndexSourceExecution.index_decoded_step_iff input .empty index).mp constructed
  rw [exactIndex, element_step_iff]

theorem diagnostics_injective : Function.Injective diagnostics := by
  intro left
  induction left with
  | nil => intro right same; cases right <;> simp_all [diagnostics]
  | cons head tail ih =>
      intro right same
      cases right with
      | nil => simp [diagnostics] at same
      | cons other rest =>
          have parts : head = other ∧ diagnostics tail = diagnostics rest := by
            simpa only [diagnostics, SExpr.list.injEq, List.cons.injEq, true_and, and_true] using same
          exact congrArg₂ List.cons parts.1 (ih parts.2)

theorem element_decoded_step_iff (owner : String) (value : Element) (input : RankedDefinitions)
    (lexicals : List LexicalDeclaration) (output : List SExpr) :
    Step (engineBasePremises scalarRelations) language
      (elementCall owner value (buildIndex input .empty) lexicals) (result (diagnostics output)) ↔
      output = elementMeaning owner value input lexicals := by
  rw [element_step_iff, PlainBnfTrieSourceExecution.result_injective.eq_iff, diagnostics_injective.eq_iff]

theorem lexical_missing_iff (key : String) (lexicals : List LexicalDeclaration) :
    firstDeclaration key lexicals = none ↔ key ∉ lexicals.map (·.referenceName) := by
  simp [firstDeclaration, List.mem_map]

/-- Absence of a diagnostic is existence of a grammar or lexical target.
This deliberately does not assert that such a target is unique. -/
theorem reference_meaning_empty_iff (owner key : String) (location : SourceSpan)
    (input : RankedDefinitions) (lexicals : List LexicalDeclaration) :
    elementMeaning owner (.reference key location) input lexicals = [] ↔
      (key.toList.map Char.toNat) ∈ (input.map Prod.snd).map (·.name) ∨
        key ∈ lexicals.map (·.referenceName) := by
  rw [← not_iff_not]
  have meaning : elementMeaning owner (.reference key location) input lexicals ≠ [] ↔
      PlainBnfDeclarationSemantics.lookup (key.toList.map Char.toNat) (input.map Prod.snd) = .missing ∧
        firstDeclaration key lexicals = none := by
    cases definitionFound : PlainBnfDeclarationSemantics.lookup (key.toList.map Char.toNat) (input.map Prod.snd) <;>
      cases lexicalFound : firstDeclaration key lexicals <;>
        simp [elementMeaning, afterDefinitionMeaning, afterLexicalMeaning, definitionFound, lexicalFound]
  exact meaning.trans (by
    rw [PlainBnfDeclarationSemantics.lookup_missing_iff, lexical_missing_iff]
    exact not_or.symm)

theorem reference_resolution_step_iff (owner key : String) (location : SourceSpan)
    (input : RankedDefinitions) (lexicals : List LexicalDeclaration) :
    Step (engineBasePremises scalarRelations) language
      (elementCall owner (.reference key location) (buildIndex input .empty) lexicals)
      (result (diagnostics [])) ↔
      (key.toList.map Char.toNat) ∈ (input.map Prod.snd).map (·.name) ∨
        key ∈ lexicals.map (·.referenceName) := by
  rw [element_decoded_step_iff, eq_comm, reference_meaning_empty_iff]

theorem element_answer_occurrences_le_one (fuel : Nat) (owner : String) (value : Element)
    (input : RankedDefinitions) (lexicals : List LexicalDeclaration) :
    (rewriteAt (engineBasePremises scalarRelations) language fuel
      (elementCall owner value (buildIndex input .empty) lexicals)).length ≤ 1 := by
  rw [element_answers]
  split <;> simp

theorem unresolved_reference_exact (owner key : String) (location : SourceSpan) :
    Step (engineBasePremises scalarRelations) language
      (elementCall owner (.reference key location) (buildIndex [] .empty) [])
      (result (diagnostics [unresolved owner key location])) := by
  rw [element_decoded_step_iff]
  rfl

theorem unresolved_reference_not_success (owner key : String) (location : SourceSpan) :
    ¬ Step (engineBasePremises scalarRelations) language
      (elementCall owner (.reference key location) (buildIndex [] .empty) [])
      (result (diagnostics [])) := by
  rw [reference_resolution_step_iff]
  simp

theorem grammar_reference_resolves (owner key : String) (location : SourceSpan)
    (rank : PlainBnfSourceRank.Rank) (body declarationSpan : SExpr) (lexicals : List LexicalDeclaration) :
    let input : RankedDefinitions := [(rank, ⟨key.toList.map Char.toNat, body, declarationSpan⟩)]
    Step (engineBasePremises scalarRelations) language
      (elementCall owner (.reference key location) (buildIndex input .empty) lexicals)
      (result (diagnostics [])) := by
  dsimp only
  rw [reference_resolution_step_iff]
  simp

/-- Even repeated lexical declarations are a successful existence lookup.
Their uniqueness remains a separate admission obligation. -/
theorem duplicate_lexical_targets_still_resolve (owner : String) (location : SourceSpan)
    (declaration : LexicalDeclaration) :
    Step (engineBasePremises scalarRelations) language
      (elementCall owner (.reference declaration.referenceName location) (buildIndex [] .empty)
        [declaration, declaration]) (result (diagnostics [])) := by
  rw [reference_resolution_step_iff]
  simp

theorem changed_unresolved_owner_refused (owner changed key : String) (location : SourceSpan)
    (different : changed ≠ owner) :
    ¬ Step (engineBasePremises scalarRelations) language
      (elementCall owner (.reference key location) (buildIndex [] .empty) [])
      (result (diagnostics [unresolved changed key location])) := by
  rw [element_decoded_step_iff]
  change ¬ [unresolved changed key location] = [unresolved owner key location]
  intro same
  have fields : text changed = text owner := by
    simpa only [unresolved, List.cons.injEq, SExpr.list.injEq, true_and, and_true] using same
  exact different (PlainBnfReferenceCollectionSourceExecution.text_injective fields)

/-- A bare marker is not a well-shaped definition payload. The missing
answer here differs from a successful empty diagnostic list. -/
theorem malformed_definition_payload_no_answers (fuel : Nat) (owner key : String) (location : SourceSpan)
    (lexicals : List LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) language fuel
      (call "BNFReferenceAfterDefinitionLookupV1"
        [text owner, text key, span location, .atom "BNFDefinitionFoundV1", declarations lexicals]) = [] := by
  cases fuel with
  | zero => rfl
  | succ fuel => resolution_reduce

#print axioms source_translation_exact
#print axioms constructed_lookup_answers
#print axioms element_answers
#print axioms indexed_element_step_iff
#print axioms collector_element_answers
#print axioms collector_element_step_iff
#print axioms collector_element_short
#print axioms collector_element_answer_occurrences_le_one
#print axioms reference_resolution_step_iff
#print axioms unresolved_reference_not_success
#print axioms duplicate_lexical_targets_still_resolve
#print axioms changed_unresolved_owner_refused
#print axioms malformed_definition_payload_no_answers

end Mettapedia.GSLT.Parsing.PlainBnfReferenceValidationSourceExecution
