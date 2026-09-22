import Mettapedia.GSLT.LanguageDef.AuthoredRuleSorting
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.OSLF.Framework.WMCalculusContextClosure
import Mettapedia.OSLF.Framework.WMCalculusEncoding
import Mettapedia.OSLF.Framework.RedexPosition

/-!
# Authored WM sorting and its representation boundaries

The core and minimal contextual presentations declare the four WM constructors.
Their validation and sorted rewrite judgments are checked here. Removing that
grammar is a negative control. Two independent boundaries remain: raw atom names
can collide across sorts, and the unary constructor-path category does not
represent the binary WM operations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusSortedBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.AuthoredRuleSorting
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusContextClosure
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusEncoding
open Mettapedia.OSLF.Framework.RedexPosition

/-- No constructor application can receive an authored type if the
presentation declares no constructor grammar at all. -/
theorem no_constructor_typing_of_empty_grammar
    (lang : LanguageDef) (empty : lang.terms = [])
    (free : FreeTypeContext) (bound : List TypeExpr)
    (ctor : String) (args : List Pattern) (expected : TypeExpr) :
    ¬ HasType lang free bound (.apply ctor args) expected := by
  intro typed
  cases typed with
  | constructor member _ _ =>
      rw [empty] at member
      cases member

theorem core_grammar_declared : wmCoreLanguageDef.terms = coreTerms := rfl

theorem contextual_grammar_declared :
    (wmExtVertexLanguageDefWithCong wmExtVertexMinimal).terms = coreTerms := rfl

/-- The presheaf base extracted from an empty grammar has no generating
unary sort-crossing arrows. This is stronger than merely lacking a sorted
proof for one rewrite rule. -/
theorem no_unary_crossings_of_empty_grammar
    (lang : LanguageDef) (empty : lang.terms = []) :
    unaryCrossings lang = [] := by
  simp [unaryCrossings, empty]

theorem core_unary_crossings_empty :
    unaryCrossings wmCoreLanguageDef = [] := by
  decide +kernel

theorem contextual_unary_crossings_empty :
    unaryCrossings (wmExtVertexLanguageDefWithCong wmExtVertexMinimal) = [] := by
  decide +kernel

/-- Without generators, a constructor-category path cannot change sort.
The actual WM base category therefore has no cross-sort morphism supplied
by its authored grammar. -/
theorem no_cross_sort_path_of_empty_crossings
    {lang : LanguageDef} (empty : unaryCrossings lang = [])
    {source target : LangSort lang} (path : SortPath lang source target) :
    source = target := by
  induction path with
  | nil => rfl
  | cons _ arrow _ =>
      have valid := arrow.valid
      rw [empty] at valid
      cases valid

theorem core_sort_path_preserves_sort
    {source target : LangSort wmCoreLanguageDef}
    (path : SortPath wmCoreLanguageDef source target) : source = target :=
  no_cross_sort_path_of_empty_crossings core_unary_crossings_empty path

/-- No nonidentity endomorphism is hidden among the paths either: each hom
fibre of the actual WM constructor category is a subsingleton. The base
category used by the current presheaf lift is therefore discrete. -/
theorem sort_paths_subsingleton_of_empty_crossings
    {lang : LanguageDef} (empty : unaryCrossings lang = [])
    {source target : LangSort lang} :
    Subsingleton (SortPath lang source target) := by
  constructor
  intro left right
  cases left with
  | nil =>
      cases right with
      | nil => rfl
      | cons _ arrow =>
          have valid := arrow.valid
          rw [empty] at valid
          cases valid
  | cons _ arrow =>
      have valid := arrow.valid
      rw [empty] at valid
      cases valid

theorem core_sort_paths_subsingleton
    {source target : LangSort wmCoreLanguageDef} :
    Subsingleton (SortPath wmCoreLanguageDef source target) :=
  sort_paths_subsingleton_of_empty_crossings core_unary_crossings_empty

/-- This is the exact contextual presentation used as the WM presheaf base
by the native observation and answer modules. Its homs are also discrete. -/
theorem contextual_sort_paths_subsingleton
    {source target :
      LangSort (wmExtVertexLanguageDefWithCong wmExtVertexMinimal)} :
    Subsingleton
      (SortPath (wmExtVertexLanguageDefWithCong wmExtVertexMinimal)
        source target) :=
  sort_paths_subsingleton_of_empty_crossings
    contextual_unary_crossings_empty

set_option maxHeartbeats 2000000 in
/-- All core constructor and rewrite declarations pass the language gate. -/
theorem core_validation : wmCoreLanguageDef.validate = [] := by
  simp only [LanguageDef.validate, wmCoreLanguageDef, coreRules,
    List.flatMap_cons, List.flatMap_nil]
  simp only [LanguageDef.validateRewrite, LanguageDef.validateRulePatterns,
    ruleEvidenceAdd, ruleRevisionComm, ruleRevisionAssoc,
    ruleCombineComm, ruleCombineZero, LanguageDef.patternFvarNames,
    ← fvarNames_eq, ← binderNames_eq, ← binderNamesList_eq]
  decide +kernel

/-- Explicitly removing the grammar reproduces the formation obstruction. -/
def missingGrammar : LanguageDef :=
  LanguageDef.ofCore wmCoreLanguageDef.name wmCoreLanguageDef.types []
    wmCoreLanguageDef.equations wmCoreLanguageDef.rewrites

theorem missingGrammar_validation_first_diagnostics :
    missingGrammar.validate.take 3 =
      [ { context := "rewrite WM_EvidenceAdd lhs",
          message := "unknown constructor `Extract/2`" },
        { context := "rewrite WM_EvidenceAdd lhs",
          message := "unknown constructor `Revise/2`" },
        { context := "rewrite WM_EvidenceAdd rhs",
          message := "unknown constructor `Combine/2`" } ] := by
  decide +kernel

def congruencePatternChecks (ctx : String) (constructors : List String)
    (typeCtx : List (String × TypeExpr)) (left right first second : Pattern) :
    List ValidationError :=
  (if [left, right, first, second].all Pattern.isWellScoped then [] else
    [{ context := ctx, message := "rule contains an out-of-scope de Bruijn index" }]) ++
  ((fvarNames left ++ fvarNames right ++ (fvarNames first ++ fvarNames second)).eraseDups.flatMap
    fun n => if constructors.contains n then
      [{ context := ctx, message := s!"pattern variable `{n}` collides with declared constructor label `{n}` (silent wildcard)" }]
    else []) ++
  ((binderNames left ++ binderNames right ++ (binderNames first ++ binderNames second)).eraseDups.flatMap
    fun n => if constructors.contains n then
      [{ context := ctx, message := s!"binder `{n}` shadows declared constructor label `{n}`" }]
    else []) ++
  (typeCtx.filterMap fun (n, _) => if constructors.contains n then
    some { context := ctx, message := s!"typeContext declares `{n}` which is also a constructor label" }
    else none) ++
  ((fvarNames right).eraseDups.flatMap fun n =>
    if (fvarNames left ++ fvarNames second).contains n || constructors.contains n then []
    else [{ context := ctx, message := s!"right-hand side variable `{n}` is bound neither on the left nor by a premise" }])

/-- Replace only the validator's well-founded traversals, before supplying
concrete terms; its tests and diagnostics remain unchanged. -/
theorem congruencePatternChecks_eq (ctx : String) (constructors : List String)
    (typeCtx : List (String × TypeExpr)) (left right first second : Pattern) :
    LanguageDef.validateRulePatterns ctx constructors typeCtx
      [.congruence first second] left right =
        congruencePatternChecks ctx constructors typeCtx left right first second := by
  simp [LanguageDef.validateRulePatterns, congruencePatternChecks,
    LanguageDef.premisePatterns, LanguageDef.premiseFvarNames,
    LanguageDef.premiseProducedFvarNames, LanguageDef.premiseForAllParams,
    patternFvarNames_nil, ← binderNames_eq]
  rfl

private theorem congruence_validation (rule : RewriteRule)
    (member : rule ∈ coreCongruenceRules) :
    LanguageDef.validateRewrite wmCoreLanguageDef rule = [] := by
  simp only [coreCongruenceRules, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [LanguageDef.validateRewrite,
      ruleReviseCongLeft, ruleReviseCongRight, ruleExtractCongLeft,
      ruleExtractCongRight, ruleCombineCongLeft, ruleCombineCongRight,
      congruencePatternChecks_eq] <;>
    decide +kernel

theorem contextual_validation :
    (wmExtVertexLanguageDefWithCong wmExtVertexMinimal).validate = [] := by
  have rules : (wmExtVertexLanguageDefWithCong wmExtVertexMinimal).rewrites =
      coreRules ++ coreCongruenceRules := rfl
  have eqs : (wmExtVertexLanguageDefWithCong wmExtVertexMinimal).equations =
      [] := rfl
  have coreRows : coreRules.flatMap
      (LanguageDef.validateRewrite (wmExtVertexLanguageDefWithCong wmExtVertexMinimal)) =
        [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro rule member
    exact LanguageDef.validateRewrite_eq_nil_of_validate_eq_nil
      wmCoreLanguageDef core_validation rule member
  have congrRows : coreCongruenceRules.flatMap
      (LanguageDef.validateRewrite (wmExtVertexLanguageDefWithCong wmExtVertexMinimal)) =
        [] := by
    apply List.flatMap_eq_nil_iff.mpr
    exact congruence_validation
  rw [LanguageDef.validate]
  simp only [rules, eqs, List.flatMap_append, coreRows, congrRows]
  decide +kernel

/-- Both sides of every core rewrite have their declared common sort. -/
theorem core_rules_checked :
    wmCoreLanguageDef.rewrites.all (checkRewriteWellSorted wmCoreLanguageDef) =
      true := by
  decide +kernel

theorem core_rules_sorted {rule : RewriteRule}
    (member : rule ∈ wmCoreLanguageDef.rewrites) :
    RewriteWellSorted wmCoreLanguageDef rule :=
  checkRewriteWellSorted_sound ((List.all_eq_true.mp core_rules_checked) rule member)

/-- The same sorting check covers all six authored congruence rules. -/
theorem contextual_rules_checked :
    (wmExtVertexLanguageDefWithCong wmExtVertexMinimal).rewrites.all
      (checkRewriteWellSorted (wmExtVertexLanguageDefWithCong wmExtVertexMinimal)) =
        true := by
  decide +kernel

theorem contextual_rules_sorted {rule : RewriteRule}
    (member : rule ∈ (wmExtVertexLanguageDefWithCong wmExtVertexMinimal).rewrites) :
    RewriteWellSorted (wmExtVertexLanguageDefWithCong wmExtVertexMinimal) rule :=
  checkRewriteWellSorted_sound
    ((List.all_eq_true.mp contextual_rules_checked) rule member)

theorem evidenceAdd_sorted : RewriteWellSorted wmCoreLanguageDef ruleEvidenceAdd :=
  core_rules_sorted (by simp [wmCoreLanguageDef, coreRules])

theorem evidenceAdd_sorted_contextually :
    RewriteWellSorted
      (wmExtVertexLanguageDefWithCong wmExtVertexMinimal) ruleEvidenceAdd :=
  contextual_rules_sorted
    (coreRules_subset_congRules_ext wmExtVertexMinimal ruleEvidenceAdd
      (by simp [coreRules]))

theorem missingGrammar_evidenceAdd_not_sorted :
    ¬ RewriteWellSorted missingGrammar ruleEvidenceAdd := by
  rintro ⟨expected, left, _⟩
  exact no_constructor_typing_of_empty_grammar missingGrammar rfl _ _ _ _ expected left

/-! ## An independent encoding boundary -/

/-- The current encoder erases the sort distinction between a named state
and a named query when their raw names coincide. Its injectivity theorem is
only within each sort, so it does not contradict this equation. -/
theorem same_name_state_query_encoding (atomName : String) :
    encodeWM (WMTerm.state atomName) = encodeWM (WMTerm.query atomName) := rfl

/-- One ordinary free-variable context cannot assign two different base
sorts to the same raw pattern variable, in any authored language. -/
theorem same_name_not_both_sorted (lang : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr) (atomName : String) :
    ¬ (HasType lang free bound (encodeWM (WMTerm.state atomName)) (.base "State") ∧
       HasType lang free bound (encodeWM (WMTerm.query atomName)) (.base "Query")) := by
  rintro ⟨stateTyped, queryTyped⟩
  have stateLookup : free atomName = some (.base "State") := by
    cases stateTyped with
    | fvar lookup => exact lookup
  have queryLookup : free atomName = some (.base "Query") := by
    cases queryTyped with
    | fvar lookup => exact lookup
  have unequal : (TypeExpr.base "State") ≠ (.base "Query") := by decide
  exact unequal (Option.some.inj (stateLookup.symm.trans queryLookup))

/-! ## Why adding only binary grammar does not repair this presheaf base -/

/-- An independent probe with an actual declared binary constructor.
It is not a replacement or extension of the authored WM language. -/
private def binaryConstructorRule : GrammarRule :=
  { label := "Pair"
    category := "B"
    params := [.simple "left" (.base "A"), .simple "right" (.base "A")]
    syntaxPattern := [] }

private def binaryConstructorProbe : LanguageDef :=
  LanguageDef.ofCore "BinaryProbe"
    [TypeDecl.plain "A", TypeDecl.plain "B"]
    [binaryConstructorRule] [] []

/-- The probe has a genuine two-argument constructor from A-arguments to
a B-result; the grammar is not empty. -/
theorem binary_probe_has_constructor :
    ∃ rule ∈ binaryConstructorProbe.terms,
      rule.params.length = 2 ∧ rule.category = "B" := by
  exact ⟨binaryConstructorRule, by decide, by decide, rfl⟩

private def probeFree : FreeTypeContext :=
  fun variableName =>
    if variableName = "x" then some (.base "A")
    else if variableName = "y" then some (.base "A") else none

/-- The binary declaration is not merely a label in a list: its application
really receives the authored B sort from two independently typed A inputs. -/
theorem binary_probe_application_sorted :
    HasType binaryConstructorProbe probeFree []
      (.apply "Pair" [.fvar "x", .fvar "y"]) (.base "B") := by
  apply HasType.constructor (rule := binaryConstructorRule)
  · decide
  · rintro ⟨_, _, _, shape⟩
    simp [binaryConstructorRule] at shape
  · apply ArgumentsHaveTypes.cons
    · trivial
    · rfl
    · exact HasType.fvar (by simp [probeFree])
    · apply ArgumentsHaveTypes.cons
      · trivial
      · rfl
      · exact HasType.fvar (by simp [probeFree])
      · exact ArgumentsHaveTypes.nil

/-- The existing constructor category extracts unary crossings only, so
the declared binary constructor contributes no generating arrow. -/
theorem binary_probe_unary_crossings_empty :
    unaryCrossings binaryConstructorProbe = [] := by
  decide +kernel

private def probeA : LangSort binaryConstructorProbe := ⟨"A", by decide⟩
private def probeB : LangSort binaryConstructorProbe := ⟨"B", by decide⟩

/-- Even a repaired WM grammar containing its binary Extract/Revise/Combine
formers would not, by itself, make the present unary-crossing constructor
category express those multi-argument operations. This concrete probe
exhibits that separate categorical limitation without changing WM. -/
theorem binary_probe_has_no_cross_sort_path :
    ¬ Nonempty (SortPath binaryConstructorProbe probeA probeB) := by
  rintro ⟨path⟩
  have same := no_cross_sort_path_of_empty_crossings
    binary_probe_unary_crossings_empty path
  have different : probeA ≠ probeB := by decide
  exact different same

#print axioms core_validation
#print axioms contextual_validation
#print axioms core_rules_sorted
#print axioms contextual_rules_sorted

end Mettapedia.OSLF.Framework.WMCalculusSortedBoundary
