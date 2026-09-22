import Mettapedia.GSLT.Parsing.PlainBnfKnownNamesSourceExecution
import Mettapedia.GSLT.Parsing.PlainBnfReferenceSourceAdmission
import Mettapedia.GSLT.Parsing.PlainBnfStructuredEnumeration

/-!
# Ordered graph diagnostics from the authored source clauses

Graph occurrences 20–23 and 60–63 traverse original definition occurrences.
The existing known-name trie supplies lookup: a missing key produces exactly
one name/span diagnostic; any found payload suppresses it. No diagnostic hook
or semantic membership oracle is added. Identifying lookup with membership in
the recorded history requires the existing known-index validity invariant.

The Boolean selects unreachable (`false`) or unproductive (`true`) diagnostics;
it is not the productive/nullable selector used by the discovery controller.
These are selected contextual source-execution results over structured String
definitions, not a full Analyze caller, generated PeTTa, or native theorem.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfGraphDiagnosticsSourceExecution

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT (Rewrite decodeList)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open SourceSExprPatternCodec (encode encodeList)
open SourceSExprPatternInstantiation (pattern patternList)
open PlainBnfStructuredDiscoveryGraph (Definition Definitions)
open PlainBnfStructuredDenotation (SourceSpan)
open PlainBnfStructuredEnumeration (wireDefinition)
open PlainBnfReferenceCollectionSourceExecution (text span)
open PlainBnfGraphNameTrie (Trie lookup)
open PlainBnfTrieSourceExecution (scalarRelations call result lookupHeight)
open PlainBnfKnownNamesSourceExecution (known nameResult knownLookupCall Valid)
open PlainBnfIndexedCollectorSourceExecution
  (headedBy premiseClosed closed_extension disjoint_heads_do_not_match)
open PlainBnfReferenceSourceAdmission (graphSource)
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

abbrev NameIndex := Trie SExpr Nat

def relation (productive : Bool) : String :=
  if productive then "BNFUnproductiveDiagnosticsV1" else "BNFUnreachableDiagnosticsV1"
def afterRelation (productive : Bool) : String :=
  if productive then "BNFUnproductiveAfterLookupV1" else "BNFUnreachableAfterLookupV1"
def tag (productive : Bool) : String :=
  if productive then "BNFUnproductiveDefinitionV1" else "BNFUnreachableDefinitionV1"

def mode? : String → Option (Nat × Nat)
  | "BNFUnreachableDiagnosticsV1" | "BNFUnproductiveDiagnosticsV1" | "BNFNameLookupV1" => some (2, 1)
  | "BNFUnreachableAfterLookupV1" | "BNFUnproductiveAfterLookupV1" => some (4, 1)
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

def rows (productive : Bool) : List Rewrite :=
  (graphSource.rewrites.drop (if productive then 60 else 20)).take 4
def rules (productive : Bool) : List RewriteRule :=
  ((rows productive).mapM lowerRule?).get (by cases productive <;> rfl)
def language (productive : Bool) : LanguageDef :=
  { name := "PlainBnfAuthoredGraphDiagnostics", types := [], terms := [], equations := [],
    rewrites := PlainBnfKnownNamesSourceExecution.language.rewrites ++ rules productive }

theorem source_translation_exact (productive : Bool) :
    (rows productive).mapM lowerRule? = some (rules productive) := by
  cases productive <;> rfl

theorem source_occurrences_exact (productive : Bool) :
    (rows productive).zipIdx (if productive then 60 else 20) =
      ((graphSource.rewrites.zipIdx).drop (if productive then 60 else 20)).take 4 := by
  cases productive <;> rfl

def relationHeads (productive : Bool) := [relation productive, afterRelation productive]

theorem source_family_exhaustive (productive : Bool) :
    graphSource.rewrites.filter (fun row => match row.head with
      | .list (.atom head :: _) => (relationHeads productive).contains head
      | _ => false) = rows productive := by
  cases productive <;> rfl

/- Checked observations only; executable rules above come from actual source. -/
private def observed (name : String) (input output : SExpr) (body : List SExpr := []) : RewriteRule :=
  { name, typeContext := [], premises := (body.mapM lowerPremise?).getD [],
    left := pattern input, right := pattern output }

private def observedRules (productive : Bool) : List RewriteRule :=
  let state := SExpr.atom (if productive then "?productive" else "?reachable")
  let definition := metta_sexpr% petta "(BNFDefinitionV1 ?name ?expression ?span)"
  [observed (if productive then "bnf-unproductive-diagnostics-nil-v1" else "bnf-unreachable-diagnostics-nil-v1")
    (.list [.atom (relation productive), .atom "BNFDefinitionsNilV1", state])
    (metta_sexpr% petta "(BNFDiagnosticsNilV1)"),
   observed (if productive then "bnf-unproductive-diagnostics-cons-v1" else "bnf-unreachable-diagnostics-cons-v1")
    (.list [.atom (relation productive), .list [.atom "BNFDefinitionsConsV1", definition, .atom "?tail"], state])
    (metta_sexpr% petta "(?diagnostics)")
    [.list [.atom "BNFNameLookupV1", .atom "?name", state, .atom "?lookup"],
     .list [.atom (afterRelation productive), .atom "?lookup", definition, .atom "?tail", state, .atom "?diagnostics"]],
   observed (if productive then "bnf-productive-definition-v1" else "bnf-reachable-definition-v1")
    (.list [.atom (afterRelation productive), metta_sexpr% petta "(BNFNameFoundV1 ?name)",
      .atom "?definition", .atom "?tail", state])
    (metta_sexpr% petta "(?diagnostics)")
    [.list [.atom (relation productive), .atom "?tail", state, .atom "?diagnostics"]],
   observed (if productive then "bnf-unproductive-definition-v1" else "bnf-unreachable-definition-v1")
    (.list [.atom (afterRelation productive), .atom "BNFNameMissingV1", definition, .atom "?tail", state])
    (.list [.list [.atom "BNFDiagnosticsConsV1", .list [.atom (tag productive), .atom "?name", .atom "?span"],
      .atom "?diagnostics"]])
    [.list [.atom (relation productive), .atom "?tail", state, .atom "?diagnostics"]]]

private theorem rules_exact (productive : Bool) : rules productive = observedRules productive := by
  cases productive <;> rfl

theorem family_heads (productive : Bool) : (rules productive).all
    (fun rule => headedBy (relationHeads productive) rule.left) = true := by
  cases productive <;>
    simp [rules_exact, observedRules, observed, headedBy, relationHeads, relation, afterRelation,
      pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode]

theorem known_extension (productive : Bool) (fuel : Nat) (source : Pattern)
    (headed : headedBy PlainBnfKnownNamesSourceExecution.relationHeads source = true) :
    rewriteAt (engineBasePremises scalarRelations) (language productive) fuel source =
      rewriteAt (engineBasePremises scalarRelations) PlainBnfKnownNamesSourceExecution.language fuel source := by
  apply closed_extension PlainBnfKnownNamesSourceExecution.relationHeads scalarRelations _ _ [] (rules productive)
  · rfl
  · intro rule member premise present
    exact List.all_eq_true.mp
      (List.all_eq_true.mp PlainBnfKnownNamesSourceExecution.family_closed rule member) premise present
  · intro rule member value itsHead
    exact disjoint_heads_do_not_match (relationHeads productive) PlainBnfKnownNamesSourceExecution.relationHeads
      (by cases productive <;> simp [relationHeads, relation, afterRelation,
        PlainBnfKnownNamesSourceExecution.relationHeads, PlainBnfKnownNamesSourceExecution.knownNames,
        PlainBnfIndexedCollectorSourceExecution.trieNames]) _ _
      (List.all_eq_true.mp (family_heads productive) rule member) itsHead
  · exact headed

private theorem diagnostics_rewriteAt (productive : Bool) (fuel : Nat) (source : Pattern)
    (headed : headedBy (relationHeads productive) source = true) :
    rewriteAt (engineBasePremises scalarRelations) (language productive) (fuel + 1) source =
      (rules productive).flatMap (fun rule => applyRuleUsing (engineBasePremises scalarRelations)
        (language productive) (rewriteAt (engineBasePremises scalarRelations) (language productive) fuel) rule source) := by
  rw [rewriteAt, language, List.flatMap_append]
  have absent : PlainBnfKnownNamesSourceExecution.language.rewrites.flatMap
      (fun rule => applyRuleUsing (engineBasePremises scalarRelations) (language productive)
        (rewriteAt (engineBasePremises scalarRelations) (language productive) fuel) rule source) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro rule member
    have noMatch := disjoint_heads_do_not_match PlainBnfKnownNamesSourceExecution.relationHeads
      (relationHeads productive) (by cases productive <;> simp [relationHeads, relation, afterRelation,
        PlainBnfKnownNamesSourceExecution.relationHeads, PlainBnfKnownNamesSourceExecution.knownNames,
        PlainBnfIndexedCollectorSourceExecution.trieNames]) _ _
      (List.all_eq_true.mp PlainBnfKnownNamesSourceExecution.family_heads rule member) headed
    simp [applyRuleUsing, noMatch]
  simp only [language] at absent
  rw [absent, List.nil_append]

def definition (value : Definition) : SExpr :=
  PlainBnfEnumerationSourceExecution.definition (wireDefinition value)
def definitions (values : Definitions) : SExpr :=
  PlainBnfEnumerationSourceExecution.definitions (values.map wireDefinition)
def diagnostic (productive : Bool) (value : String × SourceSpan) : SExpr :=
  .list [.atom (tag productive), text value.1, span value.2]
def diagnostics (productive : Bool) : List (String × SourceSpan) → SExpr
  | [] => .atom "BNFDiagnosticsNilV1"
  | head :: tail => .list [.atom "BNFDiagnosticsConsV1", diagnostic productive head, diagnostics productive tail]

def missing (values : Definitions) (index : NameIndex) : List (String × SourceSpan) :=
  (values.filter fun value => (lookup (value.name.toList.map Char.toNat) index).isNone).map
    (fun value => (value.name, value.span))

def diagnosticsCall (productive : Bool) (values : Definitions) (index : NameIndex) (history : List SExpr) : Pattern :=
  call (relation productive) [definitions values, known index history]
def afterCall (productive : Bool) (found : Option SExpr) (head : Definition) (tail : Definitions)
    (index : NameIndex) (history : List SExpr) : Pattern :=
  call (afterRelation productive) [nameResult found, definition head, definitions tail, known index history]

theorem lookup_answers (productive : Bool) (fuel : Nat) (key : String)
    (index : NameIndex) (history : List SExpr) :
    rewriteAt (engineBasePremises scalarRelations) (language productive) fuel
      (knownLookupCall (key.toList.map Char.toNat) index history) =
      if lookupHeight (key.toList.map Char.toNat) index + 1 < fuel then
        [result (nameResult (lookup (key.toList.map Char.toNat) index))] else [] := by
  rw [known_extension productive fuel _ (by
    simp [headedBy, PlainBnfKnownNamesSourceExecution.relationHeads,
      PlainBnfKnownNamesSourceExecution.knownNames, knownLookupCall, call, encode, encodeList])]
  exact PlainBnfKnownNamesSourceExecution.known_lookup_answers _ _ _ _

local macro "diagnostics_reduce" : tactic =>
  `(tactic| (
    rw [diagnostics_rewriteAt _ _ _ (by
      simp [headedBy, relationHeads, diagnosticsCall, afterCall, call, encode, encodeList])]
    simp [rules_exact, observedRules, observed, lowerPremise?, splitCall?, mode?,
      applyRuleUsing, diagnosticsCall, afterCall, relation, afterRelation, tag,
      definition, definitions, PlainBnfEnumerationSourceExecution.definition,
      PlainBnfEnumerationSourceExecution.definitions, PlainBnfCollectorSourceExecution.definitions,
      wireDefinition, nameResult, call, pattern, patternList,
      SourceIntegerProvider.sourceVariableToken, encode, encodeList,
      matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing,
      premiseStepUsing, applyBindings]))

local macro "diagnostics_finish" : tactic =>
  `(tactic| simp [result, List.flatMap_map, encode, encodeList,
    matchPattern, matchArgs, mergeBindings, List.foldlM, ← List.map_eq_flatMap])

private theorem nil_answers (productive : Bool) (fuel : Nat) (index : NameIndex) (history : List SExpr) :
    rewriteAt (engineBasePremises scalarRelations) (language productive) (fuel + 1)
      (diagnosticsCall productive [] index history) = [result (.atom "BNFDiagnosticsNilV1")] := by
  cases productive <;> diagnostics_reduce <;> diagnostics_finish

private theorem after_missing_step (productive : Bool) (fuel : Nat)
    (head : Definition) (tail : Definitions) (index : NameIndex) (history : List SExpr)
    (answers : List SExpr)
    (recursive : rewriteAt (engineBasePremises scalarRelations) (language productive) fuel
      (diagnosticsCall productive tail index history) = answers.map result) :
    rewriteAt (engineBasePremises scalarRelations) (language productive) (fuel + 1)
      (afterCall productive none head tail index history) =
      answers.map (fun answer => result
        (.list [.atom "BNFDiagnosticsConsV1", diagnostic productive (head.name, head.span), answer])) := by
  cases productive <;> diagnostics_reduce
  all_goals
    simp [diagnosticsCall, call, relation, definitions,
      PlainBnfEnumerationSourceExecution.definitions, List.map_map, Function.comp_def,
      encode, encodeList] at recursive
    simp only [Function.comp_def]
    rw [recursive]
    simp [diagnostic, tag, wireDefinition, PlainBnfEnumerationSourceExecution.definition]
    diagnostics_finish

private theorem after_found_step (productive : Bool) (fuel : Nat) (payload : SExpr)
    (head : Definition) (tail : Definitions) (index : NameIndex) (history : List SExpr)
    (answers : List SExpr)
    (recursive : rewriteAt (engineBasePremises scalarRelations) (language productive) fuel
      (diagnosticsCall productive tail index history) = answers.map result) :
    rewriteAt (engineBasePremises scalarRelations) (language productive) (fuel + 1)
      (afterCall productive (some payload) head tail index history) = answers.map result := by
  cases productive <;> diagnostics_reduce
  all_goals
    simp [diagnosticsCall, call, relation, definitions,
      PlainBnfEnumerationSourceExecution.definitions, List.map_map, Function.comp_def,
      encode, encodeList] at recursive
    simp only [Function.comp_def]
    rw [recursive]
    diagnostics_finish

private theorem cons_no_lookup (productive : Bool) (fuel : Nat)
    (head : Definition) (tail : Definitions) (index : NameIndex) (history : List SExpr)
    (absent : rewriteAt (engineBasePremises scalarRelations) (language productive) fuel
      (knownLookupCall (head.name.toList.map Char.toNat) index history) = []) :
    rewriteAt (engineBasePremises scalarRelations) (language productive) (fuel + 1)
      (diagnosticsCall productive (head :: tail) index history) = [] := by
  cases productive <;> diagnostics_reduce
  all_goals
    simp only [knownLookupCall, call, encode, encodeList] at absent
    simp only [text]
    rw [absent]
    simp

private theorem cons_some_lookup (productive : Bool) (fuel : Nat)
    (head : Definition) (tail : Definitions) (index : NameIndex) (history : List SExpr)
    (found : Option SExpr) (answers : List SExpr)
    (looked : rewriteAt (engineBasePremises scalarRelations) (language productive) fuel
      (knownLookupCall (head.name.toList.map Char.toNat) index history) = [result (nameResult found)])
    (recursive : rewriteAt (engineBasePremises scalarRelations) (language productive) fuel
      (afterCall productive found head tail index history) = answers.map result) :
    rewriteAt (engineBasePremises scalarRelations) (language productive) (fuel + 1)
      (diagnosticsCall productive (head :: tail) index history) = answers.map result := by
  cases productive <;> diagnostics_reduce
  all_goals
    simp only [knownLookupCall, call, encode, encodeList] at looked
    simp only [text]
    rw [looked]
    simp [result, encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM]
    simp [afterCall, call, afterRelation, definition, definitions,
      PlainBnfEnumerationSourceExecution.definition, PlainBnfEnumerationSourceExecution.definitions,
      wireDefinition, List.map_map, Function.comp_def, text, encode, encodeList] at recursive
    simp only [Function.comp_def, PlainBnfEnumerationSourceExecution.definition, wireDefinition, text]
    rw [recursive]
    diagnostics_finish

def diagnosticsHeight : Definitions → NameIndex → Nat
  | [], _ => 0
  | head :: tail, index =>
      max (lookupHeight (head.name.toList.map Char.toNat) index + 1)
        (diagnosticsHeight tail index + 1) + 1

private def afterData (productive : Bool) (found : Option SExpr) (head : Definition) (tail : SExpr) : SExpr :=
  if found.isNone then
    .list [.atom "BNFDiagnosticsConsV1", diagnostic productive (head.name, head.span), tail]
  else tail

private theorem after_answers_step (productive : Bool) (fuel : Nat) (found : Option SExpr)
    (head : Definition) (tail : Definitions) (index : NameIndex) (history : List SExpr)
    (answers : List SExpr)
    (recursive : rewriteAt (engineBasePremises scalarRelations) (language productive) fuel
      (diagnosticsCall productive tail index history) = answers.map result) :
    rewriteAt (engineBasePremises scalarRelations) (language productive) (fuel + 1)
      (afterCall productive found head tail index history) =
      (answers.map (afterData productive found head)).map result := by
  cases found with
  | none => simpa [afterData, List.map_map, Function.comp_def] using
      after_missing_step productive fuel head tail index history answers recursive
  | some payload => simpa [afterData, List.map_map, Function.comp_def] using
      after_found_step productive fuel payload head tail index history answers recursive

private theorem after_answers_from_tail (productive : Bool) (found : Option SExpr)
    (head : Definition) (tail : Definitions) (index : NameIndex) (history : List SExpr)
    (height : Nat) (value : SExpr)
    (recursive : ∀ fuel, rewriteAt (engineBasePremises scalarRelations) (language productive) fuel
      (diagnosticsCall productive tail index history) = if height < fuel then [result value] else [])
    (fuel : Nat) :
    rewriteAt (engineBasePremises scalarRelations) (language productive) fuel
      (afterCall productive found head tail index history) =
      if height + 1 < fuel then [result (afterData productive found head value)] else [] := by
  cases fuel with
  | zero => simp [rewriteAt]
  | succ fuel =>
      have recursiveAnswers : rewriteAt (engineBasePremises scalarRelations) (language productive) fuel
          (diagnosticsCall productive tail index history) =
          (if height < fuel then [value] else []).map result := by
        rw [recursive]
        split <;> rfl
      rw [after_answers_step productive fuel found head tail index history _ recursiveAnswers]
      by_cases enough : height < fuel <;> simp [enough]

theorem missing_cons (head : Definition) (tail : Definitions) (index : NameIndex) :
    missing (head :: tail) index =
      if (lookup (head.name.toList.map Char.toNat) index).isNone then
        (head.name, head.span) :: missing tail index else missing tail index := by
  simp only [missing, List.filter_cons]
  split <;> simp

private theorem afterData_missing (productive : Bool) (head : Definition) (tail : Definitions)
    (index : NameIndex) :
    afterData productive (lookup (head.name.toList.map Char.toNat) index) head
      (diagnostics productive (missing tail index)) = diagnostics productive (missing (head :: tail) index) := by
  rw [missing_cons]
  unfold afterData
  split <;> rfl

/-- Exact finite-depth ordered answers. Neither valid history nor a guessed
membership premise is needed: the actual sparse trie is executed. -/
theorem diagnostics_answers (productive : Bool) (values : Definitions) (index : NameIndex)
    (history : List SExpr) (fuel : Nat) :
    rewriteAt (engineBasePremises scalarRelations) (language productive) fuel
      (diagnosticsCall productive values index history) =
      if diagnosticsHeight values index < fuel then
        [result (diagnostics productive (missing values index))] else [] := by
  induction values generalizing fuel with
  | nil =>
      cases fuel with
      | zero => simp [rewriteAt]
      | succ fuel => simpa [diagnosticsHeight, missing, diagnostics] using nil_answers productive fuel index history
  | cons head tail ih =>
      cases fuel with
      | zero => simp [rewriteAt]
      | succ fuel =>
          have queried := lookup_answers productive fuel head.name index history
          have continued := after_answers_from_tail productive
            (lookup (head.name.toList.map Char.toNat) index) head tail index history
            (diagnosticsHeight tail index) (diagnostics productive (missing tail index)) ih fuel
          rw [afterData_missing] at continued
          by_cases lookupEnough : lookupHeight (head.name.toList.map Char.toNat) index + 1 < fuel
          · rw [if_pos lookupEnough] at queried
            have recursiveAnswers : rewriteAt (engineBasePremises scalarRelations) (language productive) fuel
                (afterCall productive (lookup (head.name.toList.map Char.toNat) index) head tail index history) =
                (if diagnosticsHeight tail index + 1 < fuel then
                  [diagnostics productive (missing (head :: tail) index)] else []).map result := by
              rw [continued]
              split <;> rfl
            rw [cons_some_lookup productive fuel head tail index history _ _ queried recursiveAnswers]
            by_cases tailEnough : diagnosticsHeight tail index + 1 < fuel
            · have enough : diagnosticsHeight (head :: tail) index < fuel + 1 := by
                simp only [diagnosticsHeight]
                omega
              simp [tailEnough, enough]
            · have short : ¬ diagnosticsHeight (head :: tail) index < fuel + 1 := by
                simp only [diagnosticsHeight]
                omega
              simp [tailEnough, short]
          · rw [if_neg lookupEnough] at queried
            rw [cons_no_lookup productive fuel head tail index history queried]
            have short : ¬ diagnosticsHeight (head :: tail) index < fuel + 1 := by
              simp only [diagnosticsHeight]
              omega
            simp [short]

/-- Successful arbitrary targets are exactly the original ordered diagnostics,
and sufficient source depth always returns that complete packet. -/
theorem diagnostics_step_iff (productive : Bool) (values : Definitions) (index : NameIndex)
    (history : List SExpr) (target : Pattern) :
    Step (engineBasePremises scalarRelations) (language productive)
      (diagnosticsCall productive values index history) target ↔
      target = result (diagnostics productive (missing values index)) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [diagnostics_answers] at member
    split at member
    · simpa using member
    · cases member
  · rintro rfl
    exact ⟨diagnosticsHeight values index + 1, by simp [diagnostics_answers]⟩

theorem diagnostic_injective (productive : Bool) : Function.Injective (diagnostic productive) := by
  rintro ⟨leftName, leftSpan⟩ ⟨rightName, rightSpan⟩ same
  have parts : text leftName = text rightName ∧ span leftSpan = span rightSpan := by
    simpa only [diagnostic, SExpr.list.injEq, List.cons.injEq, true_and, and_true] using same
  exact Prod.ext (PlainBnfReferenceCollectionSourceExecution.text_injective parts.1)
    (PlainBnfStructuredEnumeration.span_injective parts.2)

theorem diagnostics_injective (productive : Bool) : Function.Injective (diagnostics productive) := by
  intro left
  induction left with
  | nil => intro right same; cases right <;> simp_all [diagnostics]
  | cons head tail ih =>
      intro right same
      cases right with
      | nil => simp [diagnostics] at same
      | cons other rest =>
          have parts : diagnostic productive head = diagnostic productive other ∧
              diagnostics productive tail = diagnostics productive rest := by
            simpa only [diagnostics, SExpr.list.injEq, List.cons.injEq, true_and, and_true] using same
          exact congrArg₂ List.cons (diagnostic_injective productive parts.1) (ih parts.2)

theorem diagnostics_decoded_step_iff (productive : Bool) (values : Definitions) (index : NameIndex)
    (history : List SExpr) (output : List (String × SourceSpan)) :
    Step (engineBasePremises scalarRelations) (language productive)
      (diagnosticsCall productive values index history) (result (diagnostics productive output)) ↔
      output = missing values index := by
  rw [diagnostics_step_iff, PlainBnfTrieSourceExecution.result_injective.eq_iff,
    (diagnostics_injective productive).eq_iff]

/-- The history interpretation requires the real index invariant. Its proof
does not replace execution of the existing name lookup clauses. -/
theorem missing_eq_history_filter (values : Definitions) (index : NameIndex) (history : List SExpr)
    (valid : Valid index history) :
    missing values index = (values.filter fun value => decide (text value.name ∉ history)).map
      (fun value => (value.name, value.span)) := by
  have predicates : (fun value : Definition => (lookup (value.name.toList.map Char.toNat) index).isNone) =
      (fun value => decide (text value.name ∉ history)) := by
    funext value
    rw [valid]
    by_cases present : text value.name ∈ history
    all_goals
      simp only [text] at present
      simp [present, text]
  simp only [missing, predicates]

theorem valid_diagnostics_step_iff (productive : Bool) (values : Definitions) (index : NameIndex)
    (history : List SExpr) (valid : Valid index history) (target : Pattern) :
    Step (engineBasePremises scalarRelations) (language productive)
      (diagnosticsCall productive values index history) target ↔
      target = result (diagnostics productive
        ((values.filter fun value => decide (text value.name ∉ history)).map
          (fun value => (value.name, value.span)))) := by
  rw [diagnostics_step_iff, missing_eq_history_filter values index history valid]

theorem missing_sublist (values : Definitions) (index : NameIndex) :
    (missing values index).Sublist (values.map fun value => (value.name, value.span)) :=
  List.filter_sublist.map _

theorem missing_append (left right : Definitions) (index : NameIndex) :
    missing (left ++ right) index = missing left index ++ missing right index := by
  simp [missing]

theorem answer_occurrences_le_one (productive : Bool) (values : Definitions) (index : NameIndex)
    (history : List SExpr) (fuel : Nat) :
    (rewriteAt (engineBasePremises scalarRelations) (language productive) fuel
      (diagnosticsCall productive values index history)).length ≤ 1 := by
  rw [diagnostics_answers]
  split <;> simp

/-- Equal missing declarations produce equal diagnostic occurrences twice,
in one returned list; they are not deduplicated into one diagnostic. -/
theorem repeated_missing_definition (productive : Bool) (value : Definition) :
    Step (engineBasePremises scalarRelations) (language productive)
      (diagnosticsCall productive [value, value] .empty [])
      (result (diagnostics productive [(value.name, value.span), (value.name, value.span)])) := by
  rw [diagnostics_decoded_step_iff]
  simp [missing]

theorem repeated_diagnostic_cannot_be_deleted (productive : Bool) (value : Definition) :
    ¬ Step (engineBasePremises scalarRelations) (language productive)
      (diagnosticsCall productive [value, value] .empty [])
      (result (diagnostics productive [(value.name, value.span)])) := by
  rw [diagnostics_decoded_step_iff]
  simp [missing]

/-- Changing only an emitted location is observable even though the name
and every input body are unchanged. -/
theorem changed_span_refused (productive : Bool) (value : Definition) (changed : SourceSpan)
    (different : changed ≠ value.span) :
    ¬ Step (engineBasePremises scalarRelations) (language productive)
      (diagnosticsCall productive [value] .empty [])
      (result (diagnostics productive [(value.name, changed)])) := by
  rw [diagnostics_decoded_step_iff]
  simp [missing, different]

theorem reordered_diagnostics_refused (productive : Bool) (first second : Definition)
    (different : (first.name, first.span) ≠ (second.name, second.span)) :
    ¬ Step (engineBasePremises scalarRelations) (language productive)
      (diagnosticsCall productive [first, second] .empty [])
      (result (diagnostics productive [(second.name, second.span), (first.name, first.span)])) := by
  rw [diagnostics_decoded_step_iff]
  simp only [missing, PlainBnfGraphNameTrie.lookup_empty, Option.isNone_none, List.filter_cons,
    List.filter_nil, if_true, List.map_cons, List.map_nil, List.cons.injEq,
    and_true]
  exact fun equal => different equal.2

/-- A stale empty history is not a substitute for inspecting the actual
trie: even a non-name stored payload is Found and suppresses this diagnostic. -/
theorem found_payload_suppresses_diagnostic (productive : Bool) (value : Definition) (payload : SExpr) :
    let index : NameIndex := PlainBnfGraphNameTrie.insertFirst
      (value.name.toList.map Char.toNat) payload .empty
    Step (engineBasePremises scalarRelations) (language productive)
      (diagnosticsCall productive [value] index []) (result (diagnostics productive [])) ∧
      ¬ Valid index [] := by
  dsimp only
  constructor
  · rw [diagnostics_decoded_step_iff]
    simp [missing, PlainBnfGraphNameTrie.lookup_insertFirst]
  · intro valid
    have contradiction := valid (value.name.toList.map Char.toNat)
    simp [PlainBnfGraphNameTrie.lookup_insertFirst] at contradiction

#print axioms source_translation_exact
#print axioms diagnostics_answers
#print axioms diagnostics_step_iff
#print axioms diagnostics_decoded_step_iff
#print axioms valid_diagnostics_step_iff
#print axioms repeated_diagnostic_cannot_be_deleted
#print axioms changed_span_refused
#print axioms reordered_diagnostics_refused
#print axioms found_payload_suppresses_diagnostic

end Mettapedia.GSLT.Parsing.PlainBnfGraphDiagnosticsSourceExecution
