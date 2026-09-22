import Mettapedia.GSLT.Parsing.PlainBnfReferenceCollectionSourceExecution

/-!
# Actual lexical key lookups and duplicate diagnostics

The reference lookup reuses its existing source family. Class and label lookup
and the three diagnostic pairs are decoded from their actual authored rows.
The independent observation retains the entire first matching declaration and
the current and first-tail origins. Keys are compared in the existing exact
S-expression encoding; no string-renderer injectivity is assumed.

These are selected source-execution laws, not the recursive lexical validator,
generated PeTTa, or a native admission theorem. The field selector below is
proof metadata only and introduces no source or runtime representation.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfLexicalKeyValidationSourceExecution

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.GSLT.LanguageDef.CanonicalSourceGSLT (Rewrite decodeList)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open SourceSExprPatternCodec (encode encodeList)
open SourceSExprPatternInstantiation (pattern patternList)
open PlainBnfStructuredDenotation (LexicalDeclaration LexicalOrigin)
open PlainBnfReferenceCollectionSourceExecution (text declarations declaration lookupResult)
open PlainBnfReferenceSourceAdmission (admissionSource)
open PlainBnfTrieSourceExecution (call result scalarRelations)

inductive Key where
  | reference | className | label
  deriving DecidableEq, Repr

def keyName : Key → LexicalDeclaration → String
  | .reference, value => value.referenceName
  | .className, value => value.className
  | .label, value => value.ruleLabel

def keyWire : Key → String → SExpr
  | .reference, value => text value
  | .className, value => .atom (reprStr value)
  | .label, value => .atom (reprStr value)

def wireKey (field : Key) (value : LexicalDeclaration) : SExpr := keyWire field (keyName field value)

def lookupRelation : Key → String
  | .reference => "BNFLexicalReferenceLookupV1"
  | .className => "BNFLexicalClassLookupV1"
  | .label => "BNFLexicalLabelLookupV1"

def diagnosticRelation : Key → String
  | .reference => "BNFLexicalReferenceDiagnosticV1"
  | .className => "BNFLexicalClassDiagnosticV1"
  | .label => "BNFLexicalLabelDiagnosticV1"

def diagnosticTag : Key → String
  | .reference => "BNFDuplicateLexicalReferenceV1"
  | .className => "BNFDuplicateLexicalClassV1"
  | .label => "BNFDuplicateLexicalLabelV1"

def lookupOffset : Key → Nat | .reference => 13 | .className => 16 | .label => 19
def diagnosticOffset : Key → Nat | .reference => 36 | .className => 38 | .label => 40

def mode? : String → Option (Nat × Nat)
  | "BNFLexicalReferenceLookupV1" | "BNFLexicalClassLookupV1" | "BNFLexicalLabelLookupV1" => some (2, 1)
  | "BNFLexicalReferenceDiagnosticV1" | "BNFLexicalClassDiagnosticV1" | "BNFLexicalLabelDiagnosticV1" => some (3, 1)
  | _ => none

def splitCall? : SExpr → Option (SExpr × SExpr)
  | .list (.atom head :: arguments) => do
      let (inputs, outputs) ← mode? head
      if arguments.length = inputs + outputs then
        some (.list (.atom head :: arguments.take inputs), .list (arguments.drop inputs))
      else none
  | _ => none

def lowerPremise? : SExpr → Option Premise
  | .list [.atom "different", left, right] => some (.relationQuery "different" [pattern left, pattern right])
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

def lookupRows (field : Key) : List Rewrite :=
  (admissionSource.rewrites.drop (lookupOffset field)).take 3
def diagnosticRows (field : Key) : List Rewrite :=
  (admissionSource.rewrites.drop (diagnosticOffset field)).take 2

def lookupRules : Key → List RewriteRule
  | .reference => PlainBnfReferenceCollectionSourceExecution.lookupRules
  | .className => ((lookupRows .className).mapM lowerRule?).get (by rfl)
  | .label => ((lookupRows .label).mapM lowerRule?).get (by rfl)

def diagnosticRules (field : Key) : List RewriteRule :=
  ((diagnosticRows field).mapM lowerRule?).get (by cases field <;> rfl)

def lookupLanguage : Key → LanguageDef
  | .reference => PlainBnfReferenceCollectionSourceExecution.lookupLanguage
  | field =>
      { name := "PlainBnfAuthoredLexicalKeyLookup", types := [], terms := [], equations := [],
        rewrites := lookupRules field }

def diagnosticLanguage (field : Key) : LanguageDef :=
  { name := "PlainBnfAuthoredLexicalKeyDiagnostic", types := [], terms := [], equations := [],
    rewrites := diagnosticRules field }

theorem lookup_translation_exact (field : Key) :
    (lookupRows field).mapM lowerRule? = some (lookupLanguage field).rewrites := by
  cases field <;> rfl

theorem diagnostic_translation_exact (field : Key) :
    (diagnosticRows field).mapM lowerRule? = some (diagnosticLanguage field).rewrites := by
  cases field <;> rfl

theorem lookup_occurrences_exact (field : Key) :
    (lookupRows field).zipIdx (lookupOffset field) =
      ((admissionSource.rewrites.zipIdx).drop (lookupOffset field)).take 3 := by
  cases field <;> rfl

theorem diagnostic_occurrences_exact (field : Key) :
    (diagnosticRows field).zipIdx (diagnosticOffset field) =
      ((admissionSource.rewrites.zipIdx).drop (diagnosticOffset field)).take 2 := by
  cases field <;> rfl

theorem reference_family_reused : lookupLanguage .reference =
    PlainBnfReferenceCollectionSourceExecution.lookupLanguage := rfl

private def variableName : Key → String | .reference => "?name" | .className => "?class" | .label => "?label"
private def sourcePrefix : Key → String
  | .reference => "bnf-lexical-reference" | .className => "bnf-lexical-class" | .label => "bnf-lexical-label"

private def declarationPattern (field : Key) (other : Bool) : SExpr :=
  .list [.atom "bnf-v1:lexical-declaration",
    .atom (if field = .reference ∧ other then "?other" else "?name"),
    .atom (if field = .className ∧ other then "?other" else "?class"), .atom "?matcher",
    .atom (if field = .label ∧ other then "?other" else "?label"), .atom "?origin"]

private def observed (name : String) (input output : SExpr) (body : List SExpr := []) : RewriteRule :=
  { name, typeContext := [], premises := (body.mapM lowerPremise?).getD [],
    left := pattern input, right := pattern output }

private def lookupObserved (field : Key) : List RewriteRule :=
  let relation := SExpr.atom (lookupRelation field)
  let query := SExpr.atom (variableName field)
  [observed (sourcePrefix field ++ "-lookup-missing-v1")
    (.list [relation, query, .list [.atom "metta-nullary", .atom "bnf-v1:lexical-declarations-nil"]])
    (.list [.atom "BNFLexicalMissingV1"]),
   observed (sourcePrefix field ++ "-lookup-found-v1")
    (.list [relation, query, .list [.atom "bnf-v1:lexical-declarations-cons", declarationPattern field false, .atom "?tail"]])
    (.list [.list [.atom "BNFLexicalFoundV1", declarationPattern field false]]),
   observed (sourcePrefix field ++ "-lookup-tail-v1")
    (.list [relation, query, .list [.atom "bnf-v1:lexical-declarations-cons", declarationPattern field true, .atom "?tail"]])
    (.list [.atom "?result"])
    [.list [.atom "different", query, .atom "?other"],
     .list [relation, query, .atom "?tail", .atom "?result"]]]

private theorem lookup_rules_exact (field : Key) : (lookupLanguage field).rewrites = lookupObserved field := by
  cases field <;> rfl

def lookupCall (field : Key) (query : SExpr) (values : List LexicalDeclaration) : Pattern :=
  call (lookupRelation field) [query, declarations values]

def firstDeclaration (field : Key) (query : SExpr) (values : List LexicalDeclaration) : Option LexicalDeclaration :=
  values.find? (fun value => wireKey field value == query)

def lookupHeight (field : Key) (query : SExpr) : List LexicalDeclaration → Nat
  | [] => 0
  | head :: tail => if wireKey field head == query then 0 else 1 + lookupHeight field query tail

private theorem lookup_nil (field : Key) (fuel : Nat) (query : SExpr) :
    rewriteAt (engineBasePremises scalarRelations) (lookupLanguage field) (fuel + 1)
      (lookupCall field query []) = [result (lookupResult none)] := by
  cases field <;>
    simp [rewriteAt, lookup_rules_exact, lookupObserved, observed, sourcePrefix, variableName, lookupRelation,
      lowerPremise?, splitCall?, mode?, applyRuleUsing, lookupCall, call, result,
      declarations, lookupResult, pattern, patternList, SourceIntegerProvider.sourceVariableToken,
      encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, applyBindings]

local macro "lookup_found_reduce" : tactic => `(tactic|
    simp [rewriteAt, lookup_rules_exact, lookupObserved, observed, sourcePrefix, variableName, lookupRelation,
      declarationPattern, wireKey, keyWire, keyName, lowerPremise?, splitCall?, mode?, applyRuleUsing,
      lookupCall, call, result, declarations, declaration, lookupResult,
      pattern, patternList, SourceIntegerProvider.sourceVariableToken, encode, encodeList,
      matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, premiseStepUsing,
      applyBindings, engineBasePremises, premiseStepWithEnv, relationQueryStep, builtinRelationTuples, scalarRelations])

private theorem lookup_found_reference (fuel : Nat) (head : LexicalDeclaration) (tail : List LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) (lookupLanguage .reference) (fuel + 1)
      (lookupCall .reference (wireKey .reference head) (head :: tail)) = [result (lookupResult (some head))] := by
  lookup_found_reduce

private theorem lookup_found_class (fuel : Nat) (head : LexicalDeclaration) (tail : List LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) (lookupLanguage .className) (fuel + 1)
      (lookupCall .className (wireKey .className head) (head :: tail)) = [result (lookupResult (some head))] := by
  lookup_found_reduce

private theorem lookup_found_label (fuel : Nat) (head : LexicalDeclaration) (tail : List LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) (lookupLanguage .label) (fuel + 1)
      (lookupCall .label (wireKey .label head) (head :: tail)) = [result (lookupResult (some head))] := by
  lookup_found_reduce

private theorem lookup_found (field : Key) (fuel : Nat) (head : LexicalDeclaration) (tail : List LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) (lookupLanguage field) (fuel + 1)
      (lookupCall field (wireKey field head) (head :: tail)) = [result (lookupResult (some head))] := by
  cases field
  · exact lookup_found_reference fuel head tail
  · exact lookup_found_class fuel head tail
  · exact lookup_found_label fuel head tail

private theorem encode_ne (left right : SExpr) (different : left ≠ right) : encode left ≠ encode right :=
  fun same => different (SourceSExprPatternCodec.encode_injective same)

local macro "lookup_other_reduce" different:ident recursive:ident : tactic => `(tactic| (
  rw [rewriteAt]
  have encodedDifferent := encode_ne _ _ ($different:term)
  simp only [wireKey, keyWire, keyName, encode, encodeList] at encodedDifferent
  simp [lookup_rules_exact, lookupObserved, observed, sourcePrefix, variableName, lookupRelation,
      declarationPattern, lowerPremise?, splitCall?, mode?, applyRuleUsing, lookupCall, call,
      declarations, declaration, pattern, patternList, SourceIntegerProvider.sourceVariableToken,
      encode, encodeList, matchPattern, matchArgs, mergeBindings, List.foldlM, premisesUsing, premiseStepUsing,
      applyBindings, engineBasePremises, premiseStepWithEnv, relationQueryStep,
      builtinRelationTuples, scalarRelations, encodedDifferent,
      matchRelationArgs, matchRelationArgument, Bindings.lookup]
  simp only [lookupCall, call, encode, encodeList, scalarRelations, lookupRelation] at $recursive:ident
  rw [$recursive:term]
  simp [List.flatMap_map, result, encode, encodeList, matchPattern, matchArgs,
      List.foldlM, mergeBindings, ← List.map_eq_flatMap]))

private theorem lookup_other_reference (fuel : Nat) (query : SExpr) (head : LexicalDeclaration)
    (tail : List LexicalDeclaration) (different : query ≠ wireKey .reference head)
    (answers : List SExpr)
    (recursive : rewriteAt (engineBasePremises scalarRelations) (lookupLanguage .reference) fuel
      (lookupCall .reference query tail) = answers.map result) :
    rewriteAt (engineBasePremises scalarRelations) (lookupLanguage .reference) (fuel + 1)
      (lookupCall .reference query (head :: tail)) = answers.map result := by
  lookup_other_reduce different recursive

private theorem lookup_other_class (fuel : Nat) (query : SExpr) (head : LexicalDeclaration)
    (tail : List LexicalDeclaration) (different : query ≠ wireKey .className head)
    (answers : List SExpr)
    (recursive : rewriteAt (engineBasePremises scalarRelations) (lookupLanguage .className) fuel
      (lookupCall .className query tail) = answers.map result) :
    rewriteAt (engineBasePremises scalarRelations) (lookupLanguage .className) (fuel + 1)
      (lookupCall .className query (head :: tail)) = answers.map result := by
  lookup_other_reduce different recursive

private theorem lookup_other_label (fuel : Nat) (query : SExpr) (head : LexicalDeclaration)
    (tail : List LexicalDeclaration) (different : query ≠ wireKey .label head)
    (answers : List SExpr)
    (recursive : rewriteAt (engineBasePremises scalarRelations) (lookupLanguage .label) fuel
      (lookupCall .label query tail) = answers.map result) :
    rewriteAt (engineBasePremises scalarRelations) (lookupLanguage .label) (fuel + 1)
      (lookupCall .label query (head :: tail)) = answers.map result := by
  lookup_other_reduce different recursive

private theorem lookup_other (field : Key) (fuel : Nat) (query : SExpr) (head : LexicalDeclaration)
    (tail : List LexicalDeclaration) (different : query ≠ wireKey field head)
    (answers : List SExpr)
    (recursive : rewriteAt (engineBasePremises scalarRelations) (lookupLanguage field) fuel
      (lookupCall field query tail) = answers.map result) :
    rewriteAt (engineBasePremises scalarRelations) (lookupLanguage field) (fuel + 1)
      (lookupCall field query (head :: tail)) = answers.map result := by
  cases field
  · exact lookup_other_reference fuel query head tail different answers recursive
  · exact lookup_other_class fuel query head tail different answers recursive
  · exact lookup_other_label fuel query head tail different answers recursive

theorem lookup_answers (field : Key) (fuel : Nat) (query : SExpr) (values : List LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) (lookupLanguage field) fuel (lookupCall field query values) =
      if lookupHeight field query values < fuel then [result (lookupResult (firstDeclaration field query values))] else [] := by
  induction fuel generalizing values with
  | zero => simp [rewriteAt]
  | succ fuel ih =>
      cases values with
      | nil => simpa [lookupHeight, firstDeclaration] using lookup_nil field fuel query
      | cons head tail =>
          by_cases same : query = wireKey field head
          · subst query
            simpa [lookupHeight, firstDeclaration] using lookup_found field fuel head tail
          · have other := Ne.symm same
            by_cases enough : lookupHeight field query tail < fuel
            · have step := lookup_other field fuel query head tail same [lookupResult (firstDeclaration field query tail)]
                (by simpa [enough] using ih tail)
              have bound : 1 + lookupHeight field query tail ≤ fuel := by omega
              simpa [lookupHeight, firstDeclaration, other, bound] using step
            · have step := lookup_other field fuel query head tail same [] (by simpa [enough] using ih tail)
              have bound : ¬ 1 + lookupHeight field query tail ≤ fuel := by omega
              simpa [lookupHeight, firstDeclaration, other, bound] using step

theorem lookup_step_iff (field : Key) (query : SExpr) (values : List LexicalDeclaration) (target : Pattern) :
    Step (engineBasePremises scalarRelations) (lookupLanguage field) (lookupCall field query values) target ↔
      target = result (lookupResult (firstDeclaration field query values)) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [lookup_answers] at member
    split at member
    · simpa using member
    · cases member
  · rintro rfl
    exact ⟨lookupHeight field query values + 1, by simp [lookup_answers]⟩

theorem firstDeclaration_none_iff (field : Key) (query : SExpr) (values : List LexicalDeclaration) :
    firstDeclaration field query values = none ↔ query ∉ values.map (wireKey field) := by
  rw [firstDeclaration, List.find?_eq_none]
  constructor
  · intro missing present
    obtain ⟨value, member, same⟩ := List.mem_map.mp present
    apply missing value member
    simp only [same, beq_self_eq_true]
  · intro absent value member matching
    exact absent (List.mem_map.mpr ⟨value, member, beq_iff_eq.mp matching⟩)

theorem lookup_missing_iff (field : Key) (query : SExpr) (values : List LexicalDeclaration) :
    Step (engineBasePremises scalarRelations) (lookupLanguage field)
      (lookupCall field query values) (result (lookupResult none)) ↔
      query ∉ values.map (wireKey field) := by
  rw [lookup_step_iff, PlainBnfTrieSourceExecution.result_injective.eq_iff]
  rw [← firstDeclaration_none_iff]
  cases firstDeclaration field query values <;> simp [lookupResult]

def origin (value : LexicalOrigin) : SExpr :=
  .list [.atom "bnf-v1:lexical-origin", .atom (reprStr value.authority), .atom (toString value.occurrence)]

def diagnostics (field : Key) (query currentOrigin : SExpr) : Option LexicalDeclaration → SExpr
  | none => .atom "BNFDiagnosticsNilV1"
  | some found => .list [.atom "BNFDiagnosticsConsV1",
      .list [.atom (diagnosticTag field), query, currentOrigin, origin found.origin],
      .atom "BNFDiagnosticsNilV1"]

def diagnosticCall (field : Key) (query currentOrigin : SExpr) (found : Option LexicalDeclaration) : Pattern :=
  call (diagnosticRelation field) [query, currentOrigin, lookupResult found]

private def diagnosticObserved (field : Key) : List RewriteRule :=
  let relation := SExpr.atom (diagnosticRelation field)
  let query := SExpr.atom (variableName field)
  [observed (sourcePrefix field ++ "-unique-v1")
    (.list [relation, query, .atom "?origin", .atom "BNFLexicalMissingV1"])
    (.list [.atom "BNFDiagnosticsNilV1"]),
   observed (sourcePrefix field ++ "-duplicate-v1")
    (.list [relation, query, .atom "?origin", .list [.atom "BNFLexicalFoundV1",
      .list [.atom "bnf-v1:lexical-declaration", .atom "?otherName", .atom "?otherClass",
        .atom "?otherMatcher", .atom "?otherLabel", .atom "?firstOrigin"]]])
    (.list [.list [.atom "BNFDiagnosticsConsV1",
      .list [.atom (diagnosticTag field), query, .atom "?origin", .atom "?firstOrigin"],
      .atom "BNFDiagnosticsNilV1"]])]

private theorem diagnostic_rules_exact (field : Key) :
    (diagnosticLanguage field).rewrites = diagnosticObserved field := by
  cases field <;> rfl

private theorem diagnostic_missing (field : Key) (fuel : Nat) (query currentOrigin : SExpr) :
    rewriteAt (engineBasePremises scalarRelations) (diagnosticLanguage field) (fuel + 1)
      (diagnosticCall field query currentOrigin none) =
        [result (diagnostics field query currentOrigin none)] := by
  cases field <;>
    simp [rewriteAt, diagnostic_rules_exact, diagnosticObserved, observed, sourcePrefix, variableName,
      diagnosticRelation, diagnosticTag, applyRuleUsing,
      diagnosticCall, call, result, lookupResult, diagnostics, pattern, patternList,
      SourceIntegerProvider.sourceVariableToken, encode, encodeList, matchPattern, matchArgs,
      mergeBindings, List.foldlM, premisesUsing, applyBindings]

local macro "diagnostic_found_reduce" : tactic => `(tactic|
    simp [rewriteAt, diagnostic_rules_exact, diagnosticObserved, observed, sourcePrefix, variableName,
      diagnosticRelation, diagnosticTag, lowerPremise?, splitCall?, mode?, applyRuleUsing,
      diagnosticCall, call, result, lookupResult, diagnostics, declaration, origin, pattern, patternList,
      SourceIntegerProvider.sourceVariableToken, encode, encodeList, matchPattern, matchArgs,
      mergeBindings, List.foldlM, premisesUsing, applyBindings])

private theorem diagnostic_found_reference (fuel : Nat) (query currentOrigin : SExpr) (found : LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) (diagnosticLanguage .reference) (fuel + 1)
      (diagnosticCall .reference query currentOrigin (some found)) =
        [result (diagnostics .reference query currentOrigin (some found))] := by
  diagnostic_found_reduce

private theorem diagnostic_found_class (fuel : Nat) (query currentOrigin : SExpr) (found : LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) (diagnosticLanguage .className) (fuel + 1)
      (diagnosticCall .className query currentOrigin (some found)) =
        [result (diagnostics .className query currentOrigin (some found))] := by
  diagnostic_found_reduce

private theorem diagnostic_found_label (fuel : Nat) (query currentOrigin : SExpr) (found : LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) (diagnosticLanguage .label) (fuel + 1)
      (diagnosticCall .label query currentOrigin (some found)) =
        [result (diagnostics .label query currentOrigin (some found))] := by
  diagnostic_found_reduce

theorem diagnostic_answers (field : Key) (fuel : Nat) (query currentOrigin : SExpr)
    (found : Option LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) (diagnosticLanguage field) fuel
      (diagnosticCall field query currentOrigin found) =
        if 0 < fuel then [result (diagnostics field query currentOrigin found)] else [] := by
  cases fuel with
  | zero => simp [rewriteAt]
  | succ fuel =>
      simp only [Nat.zero_lt_succ, ↓reduceIte]
      cases found with
      | none => exact diagnostic_missing field fuel query currentOrigin
      | some found =>
          cases field
          · exact diagnostic_found_reference fuel query currentOrigin found
          · exact diagnostic_found_class fuel query currentOrigin found
          · exact diagnostic_found_label fuel query currentOrigin found

theorem diagnostic_step_iff (field : Key) (query currentOrigin : SExpr)
    (found : Option LexicalDeclaration) (target : Pattern) :
    Step (engineBasePremises scalarRelations) (diagnosticLanguage field)
      (diagnosticCall field query currentOrigin found) target ↔
        target = result (diagnostics field query currentOrigin found) := by
  rw [← exists_mem_rewriteAt_iff_step]
  constructor
  · rintro ⟨fuel, member⟩
    rw [diagnostic_answers] at member
    split at member
    · simpa using member
    · cases member
  · rintro rfl
    exact ⟨1, by simp [diagnostic_answers]⟩

theorem diagnostic_empty_iff (field : Key) (query currentOrigin : SExpr) (found : Option LexicalDeclaration) :
    diagnostics field query currentOrigin found = .atom "BNFDiagnosticsNilV1" ↔ found = none := by
  cases found <;> simp [diagnostics]

theorem diagnostics_of_lookupResult_eq (field : Key) (query currentOrigin : SExpr)
    (left right : Option LexicalDeclaration) (same : lookupResult left = lookupResult right) :
    diagnostics field query currentOrigin left = diagnostics field query currentOrigin right := by
  cases left with
  | none => cases right <;> simp_all [lookupResult]
  | some left =>
      cases right with
      | none => simp [lookupResult] at same
      | some right =>
          have originEq : origin left.origin = origin right.origin := by
            simp only [lookupResult, SExpr.list.injEq, List.cons.injEq, and_true, true_and] at same
            have component := congrArg (fun value : SExpr => match value with
              | .list [_, _, _, _, _, component] => component
              | _ => .atom "") same
            simpa only [declaration, origin] using component
          simp [diagnostics, originEq]

/-- The actual lookup establishes the matching-key premise; the diagnostic pair
itself reacts only to missing versus found and does not recheck the key. -/
theorem lookup_then_diagnostic_iff (field : Key) (query currentOrigin : SExpr)
    (values : List LexicalDeclaration) (target : Pattern) :
    (∃ found : Option LexicalDeclaration,
      Step (engineBasePremises scalarRelations) (lookupLanguage field)
        (lookupCall field query values) (result (lookupResult found)) ∧
      Step (engineBasePremises scalarRelations) (diagnosticLanguage field)
        (diagnosticCall field query currentOrigin found) target) ↔
      target = result (diagnostics field query currentOrigin (firstDeclaration field query values)) := by
  constructor
  · rintro ⟨found, lookup, diagnostic⟩
    rw [lookup_step_iff, PlainBnfTrieSourceExecution.result_injective.eq_iff] at lookup
    exact ((diagnostic_step_iff _ _ _ _ _).mp diagnostic).trans
      (congrArg result (diagnostics_of_lookupResult_eq field query currentOrigin _ _ lookup))
  · intro targetEq
    exact ⟨firstDeclaration field query values, (lookup_step_iff _ _ _ _).mpr rfl,
      (diagnostic_step_iff _ _ _ _ _).mpr targetEq⟩

theorem lookup_then_empty_diagnostic_iff (field : Key) (query currentOrigin : SExpr)
    (values : List LexicalDeclaration) :
    (∃ found : Option LexicalDeclaration,
      Step (engineBasePremises scalarRelations) (lookupLanguage field)
        (lookupCall field query values) (result (lookupResult found)) ∧
      Step (engineBasePremises scalarRelations) (diagnosticLanguage field)
        (diagnosticCall field query currentOrigin found) (result (.atom "BNFDiagnosticsNilV1"))) ↔
      query ∉ values.map (wireKey field) := by
  rw [lookup_then_diagnostic_iff, PlainBnfTrieSourceExecution.result_injective.eq_iff, eq_comm,
    diagnostic_empty_iff, firstDeclaration_none_iff]

theorem wire_keys_unique_iff (field : Key) (values : List LexicalDeclaration) :
    (values.map (wireKey field)).Nodup ↔
      ∀ before current tail, values = before ++ current :: tail →
        firstDeclaration field (wireKey field current) tail = none := by
  induction values with
  | nil =>
      constructor
      · intro _ before current tail impossible
        have lengths := congrArg List.length impossible
        simp at lengths
      · intro _
        simp
  | cons head tail ih =>
      constructor
      · intro distinct before current rest equation
        cases before with
        | nil =>
            simp only [List.nil_append, List.cons.injEq] at equation
            rcases equation with ⟨rfl, rfl⟩
            exact (firstDeclaration_none_iff _ _ _).mpr (List.nodup_cons.mp distinct).1
        | cons first before =>
            simp only [List.cons_append, List.cons.injEq] at equation
            exact ih.mp (List.nodup_cons.mp distinct).2 before current rest equation.2
      · intro missing
        apply List.nodup_cons.mpr
        constructor
        · exact (firstDeclaration_none_iff _ _ _).mp (missing [] head tail rfl)
        · apply ih.mpr
          intro before current rest equation
          exact missing (head :: before) current rest (by simp [equation])

/-- Empty actual lookup/diagnostic outputs at every source tail characterize
wire-key uniqueness, retaining the ordered declaration list itself unchanged. -/
theorem source_tail_checks_iff_wire_unique (field : Key) (values : List LexicalDeclaration) :
    (∀ before current tail, values = before ++ current :: tail →
      ∃ found : Option LexicalDeclaration,
        Step (engineBasePremises scalarRelations) (lookupLanguage field)
          (lookupCall field (wireKey field current) tail) (result (lookupResult found)) ∧
        Step (engineBasePremises scalarRelations) (diagnosticLanguage field)
          (diagnosticCall field (wireKey field current) (origin current.origin) found)
          (result (.atom "BNFDiagnosticsNilV1"))) ↔
      (values.map (wireKey field)).Nodup := by
  simp_rw [lookup_then_empty_diagnostic_iff, ← firstDeclaration_none_iff]
  exact (wire_keys_unique_iff field values).symm

/-- The admission direction needs no injectivity assumption about the string
renderer: equal original keys necessarily have equal encoded keys. -/
theorem names_unique_of_wire_unique (field : Key) (values : List LexicalDeclaration)
    (distinct : (values.map (wireKey field)).Nodup) :
    (values.map (keyName field)).Nodup := by
  apply List.Nodup.of_map (keyWire field)
  rw [List.map_map]
  exact distinct

theorem source_tail_checks_imply_key_unique (field : Key) (values : List LexicalDeclaration)
    (checks : ∀ before current tail, values = before ++ current :: tail →
      ∃ found : Option LexicalDeclaration,
        Step (engineBasePremises scalarRelations) (lookupLanguage field)
          (lookupCall field (wireKey field current) tail) (result (lookupResult found)) ∧
        Step (engineBasePremises scalarRelations) (diagnosticLanguage field)
          (diagnosticCall field (wireKey field current) (origin current.origin) found)
          (result (.atom "BNFDiagnosticsNilV1"))) :
    (values.map (keyName field)).Nodup :=
  names_unique_of_wire_unique field values ((source_tail_checks_iff_wire_unique _ _).mp checks)

theorem lookup_heads (field : Key) : (lookupLanguage field).rewrites.all
    (fun rule => PlainBnfIndexedCollectorSourceExecution.headedBy [lookupRelation field] rule.left) = true := by
  cases field <;> simp [lookup_rules_exact, lookupObserved, observed, lookupRelation,
    PlainBnfIndexedCollectorSourceExecution.headedBy, sourcePrefix, variableName,
    pattern, patternList, encode, SourceIntegerProvider.sourceVariableToken]

theorem lookup_closed (field : Key) : (lookupLanguage field).rewrites.all
    (fun rule => rule.premises.all
      (PlainBnfIndexedCollectorSourceExecution.premiseClosed [lookupRelation field])) = true := by
  cases field <;> simp [lookup_rules_exact, lookupObserved, observed, lookupRelation,
    PlainBnfIndexedCollectorSourceExecution.premiseClosed, PlainBnfIndexedCollectorSourceExecution.headedBy,
    sourcePrefix, variableName, lowerPremise?, splitCall?, mode?, pattern, patternList, encode,
    SourceIntegerProvider.sourceVariableToken]

theorem lookup_queries (field : Key) : (lookupLanguage field).rewrites.all
    (fun rule => rule.premises.all fun premise => match premise with
      | .relationQuery relation _ => relation == "different"
      | _ => true) = true := by
  cases field <;> simp [lookup_rules_exact, lookupObserved, observed, lookupRelation,
    sourcePrefix, variableName, lowerPremise?, splitCall?, mode?]

theorem diagnostic_heads (field : Key) : (diagnosticLanguage field).rewrites.all
    (fun rule => PlainBnfIndexedCollectorSourceExecution.headedBy [diagnosticRelation field] rule.left) = true := by
  cases field <;> simp [diagnostic_rules_exact, diagnosticObserved, observed, diagnosticRelation,
    PlainBnfIndexedCollectorSourceExecution.headedBy, sourcePrefix, variableName,
    pattern, patternList, encode, SourceIntegerProvider.sourceVariableToken]

theorem diagnostic_premises_empty (field : Key) : (diagnosticLanguage field).rewrites.all
    (fun rule => rule.premises.isEmpty) = true := by
  cases field <;> simp [diagnostic_rules_exact, diagnosticObserved, observed]

private def specimen (occurrence : Nat) : LexicalDeclaration :=
  { referenceName := "digit", className := "Digit", matcher := .points [48], ruleLabel := "digit-token",
    origin := { authority := "lexical-specimen", occurrence } }

theorem first_tail_declaration_preserved (field : Key) :
    Step (engineBasePremises scalarRelations) (lookupLanguage field)
      (lookupCall field (wireKey field (specimen 0)) [specimen 1, specimen 2])
      (result (lookupResult (some (specimen 1)))) := by
  rw [lookup_step_iff]
  cases field <;> simp [firstDeclaration, wireKey, keyWire, keyName, specimen]

theorem second_tail_declaration_preserved (field : Key) :
    Step (engineBasePremises scalarRelations) (lookupLanguage field)
      (lookupCall field (wireKey field (specimen 1)) [specimen 2])
      (result (lookupResult (some (specimen 2)))) := by
  rw [lookup_step_iff]
  cases field <;> simp [firstDeclaration, wireKey, keyWire, keyName, specimen]

theorem duplicate_self_is_not_removed (field : Key) :
    Step (engineBasePremises scalarRelations) (lookupLanguage field)
      (lookupCall field (wireKey field (specimen 0)) [specimen 0, specimen 0])
      (result (lookupResult (some (specimen 0)))) := by
  rw [lookup_step_iff]
  cases field <;> simp [firstDeclaration, wireKey, keyWire, keyName, specimen]

theorem both_current_and_first_tail_origins :
    Step (engineBasePremises scalarRelations) (diagnosticLanguage .reference)
      (diagnosticCall .reference (text "digit") (origin (specimen 1).origin) (some (specimen 2)))
      (result (.list [.atom "BNFDiagnosticsConsV1",
        .list [.atom "BNFDuplicateLexicalReferenceV1", text "digit",
          origin ⟨"lexical-specimen", 1⟩,
          origin ⟨"lexical-specimen", 2⟩],
        .atom "BNFDiagnosticsNilV1"])) := by
  rw [diagnostic_step_iff]
  rfl

theorem not_a_global_first_origin :
    ¬ Step (engineBasePremises scalarRelations) (diagnosticLanguage .reference)
      (diagnosticCall .reference (text "digit") (origin (specimen 1).origin) (some (specimen 2)))
      (result (diagnostics .reference (text "digit") (origin (specimen 0).origin) (some (specimen 2)))) := by
  rw [diagnostic_step_iff, PlainBnfTrieSourceExecution.result_injective.eq_iff]
  simp [diagnostics, origin, specimen, diagnosticTag]

theorem duplicated_keys_cannot_pass (field : Key) :
    ¬ (∃ found : Option LexicalDeclaration,
      Step (engineBasePremises scalarRelations) (lookupLanguage field)
        (lookupCall field (wireKey field (specimen 0)) [specimen 1]) (result (lookupResult found)) ∧
      Step (engineBasePremises scalarRelations) (diagnosticLanguage field)
        (diagnosticCall field (wireKey field (specimen 0)) (origin (specimen 0).origin) found)
        (result (.atom "BNFDiagnosticsNilV1"))) := by
  rw [lookup_then_empty_diagnostic_iff]
  cases field <;> simp [wireKey, keyWire, keyName, specimen]

/-- A diagnostic alone is not a key-validation check: the lookup must supply
the matching declaration before this actual found branch is used. -/
theorem diagnostic_alone_does_not_recheck_key :
    Step (engineBasePremises scalarRelations) (diagnosticLanguage .reference)
      (diagnosticCall .reference (text "not-digit") (.atom "opaque-origin") (some (specimen 0)))
      (result (diagnostics .reference (text "not-digit") (.atom "opaque-origin") (some (specimen 0)))) :=
  (diagnostic_step_iff _ _ _ _ _).mpr rfl

theorem zero_depth_is_not_missing (field : Key) (query : SExpr) (values : List LexicalDeclaration) :
    rewriteAt (engineBasePremises scalarRelations) (lookupLanguage field) 0 (lookupCall field query values) = [] ∧
      rewriteAt (engineBasePremises scalarRelations) (lookupLanguage field)
        (lookupHeight field query values + 1) (lookupCall field query values) =
        [result (lookupResult (firstDeclaration field query values))] := by
  simp [lookup_answers]

#print axioms lookup_answers
#print axioms lookup_step_iff
#print axioms diagnostic_answers
#print axioms lookup_then_diagnostic_iff
#print axioms source_tail_checks_iff_wire_unique
#print axioms source_tail_checks_imply_key_unique
#print axioms both_current_and_first_tail_origins
#print axioms not_a_global_first_origin

end Mettapedia.GSLT.Parsing.PlainBnfLexicalKeyValidationSourceExecution
