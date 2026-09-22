import Mettapedia.GSLT.Parsing.PlainBnfIndexedCollectorSourceExecution
import Mettapedia.GSLT.Parsing.PlainBnfDefinitionIndexSourceExecution
import Mettapedia.GSLT.Parsing.PlainBnfStructuredEnumeration

/-!
# Declaration admission from the executed indexed collector

The empty-diagnostic condition of the actual authored collector is equivalent
to uniqueness of the declared names. On that domain the collector retains
every complete declaration in source order, including its expression and span.
Comments and blank entries are traversed but are not declarations.

The generic result admits arbitrary name, expression, and span payloads. Its
structured-document specialization uses the existing canonical String/Nat
codecs; it does not assert that arbitrary edited wire data has such an image.
Only the declaration-uniqueness conjunct of semantic admission is established
here, not whole validation, generated PeTTa, or native execution.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfDeclarationAdmission

open PlainBnfDeclarationSemantics

universe uN uE uS uT
variable {Name : Type uN} {Expression : Type uE} {Span : Type uS} {Text : Type uT}

/-- Ordered observation of the rule entries, without deduplication. -/
def declarations : List (Entry Name Expression Span Text) → List (Definition Name Expression Span)
  | [] => []
  | .rule name expression span :: tail => ⟨name, expression, span⟩ :: declarations tail
  | .comment _ _ :: tail | .blank _ :: tail => declarations tail

variable [DecidableEq Name]

/-- Empty diagnostics are exactly fresh, pairwise distinct input names;
the already collected prefix itself need not be duplicate-free. -/
theorem collect_clean_iff (input : List (Entry Name Expression Span Text))
    (before : List (Definition Name Expression Span)) :
    (collect input before).2 = [] ↔
      ((declarations input).map Definition.name).Nodup ∧
      (before.map Definition.name).Disjoint ((declarations input).map Definition.name) := by
  induction input generalizing before with
  | nil => simp [collect, declarations]
  | cons head tail ih =>
      cases head with
      | comment => simpa [collect, declarations] using ih before
      | blank => simpa [collect, declarations] using ih before
      | rule name expression span =>
          cases found : lookup name before with
          | missing =>
              have fresh := (lookup_missing_iff name before).mp found
              simp only [collect, found, definitionStep, List.nil_append, declarations, List.map_cons]
              rw [ih]
              simp only [List.map_append, List.map_cons, List.map_nil,
                List.disjoint_append_left, List.disjoint_cons_left, List.disjoint_nil_left,
                and_true, List.nodup_cons, List.disjoint_cons_right]
              simp only [fresh]
              tauto
          | found old firstSpan =>
              have present : name ∈ before.map Definition.name := by
                by_contra absent
                have missing := (lookup_missing_iff name before).mpr absent
                rw [found] at missing
                cases missing
              simp [collect, found, definitionStep, declarations, List.disjoint_cons_right, present]

/-- No input occurrence is dropped when declaration validation succeeds. -/
theorem collect_clean_payloads (input : List (Entry Name Expression Span Text))
    (before : List (Definition Name Expression Span))
    (clean : (collect input before).2 = []) :
    (collect input before).1 = before ++ declarations input := by
  induction input generalizing before with
  | nil => simp [collect, declarations]
  | cons head tail ih =>
      cases head with
      | comment => simpa [collect, declarations] using ih before clean
      | blank => simpa [collect, declarations] using ih before clean
      | rule name expression span =>
          cases found : lookup name before with
          | missing =>
              simp only [collect, found, definitionStep, List.nil_append] at clean ⊢
              rw [ih _ clean]
              simp [declarations, List.append_assoc]
          | found old firstSpan =>
              simp [collect, found, definitionStep] at clean

theorem collect_empty_clean_iff (input : List (Entry Name Expression Span Text)) :
    (collect input []).2 = [] ↔ ((declarations input).map Definition.name).Nodup := by
  simp [collect_clean_iff]

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (Step engineBasePremises rewriteAt)
open PlainBnfTrieSourceExecution (scalarRelations)

variable {Scalar : Type} [DecidableEq Scalar]
  [PlainBnfCollectorSourceExecution.NameScalarCodec Scalar]

/-- The condition is attached to the actual source execution, not a checker
that calls the specification as its own reference. -/
theorem source_clean_iff (input : List (PlainBnfIndexedCollectorSourceExecution.Entry Scalar))
    (output : (List (PlainBnfIndexedCollectorSourceExecution.Definition Scalar) ×
      List (PlainBnfIndexedCollectorSourceExecution.Diagnostic Scalar)) ×
      PlainBnfIndexedCollectorSourceExecution.Index Scalar)
    (executed : Step (engineBasePremises scalarRelations)
      PlainBnfIndexedCollectorSourceExecution.language
      (PlainBnfIndexedCollectorSourceExecution.collectCall input)
      (PlainBnfIndexedCollectorSourceExecution.encodeResult output)) :
    output.1.2 = [] ↔ ((declarations input).map Definition.name).Nodup := by
  rw [(PlainBnfIndexedCollectorSourceExecution.collect_observations input output executed).1]
  exact collect_empty_clean_iff input

theorem source_clean_payloads (input : List (PlainBnfIndexedCollectorSourceExecution.Entry Scalar))
    (output : (List (PlainBnfIndexedCollectorSourceExecution.Definition Scalar) ×
      List (PlainBnfIndexedCollectorSourceExecution.Diagnostic Scalar)) ×
      PlainBnfIndexedCollectorSourceExecution.Index Scalar)
    (executed : Step (engineBasePremises scalarRelations)
      PlainBnfIndexedCollectorSourceExecution.language
      (PlainBnfIndexedCollectorSourceExecution.collectCall input)
      (PlainBnfIndexedCollectorSourceExecution.encodeResult output))
    (clean : output.1.2 = []) : output.1.1 = declarations input := by
  have observed := (PlainBnfIndexedCollectorSourceExecution.collect_observations input output executed).1
  rw [observed] at clean ⊢
  simpa using collect_clean_payloads input [] clean

/-- The actual returned index supplies the first complete definition payload.
It need not be replaced with an index rebuilt from ranked definitions. -/
theorem source_index_result (input : List (PlainBnfIndexedCollectorSourceExecution.Entry Scalar))
    (output : (List (PlainBnfIndexedCollectorSourceExecution.Definition Scalar) ×
      List (PlainBnfIndexedCollectorSourceExecution.Diagnostic Scalar)) ×
      PlainBnfIndexedCollectorSourceExecution.Index Scalar)
    (executed : Step (engineBasePremises scalarRelations)
      PlainBnfIndexedCollectorSourceExecution.language
      (PlainBnfIndexedCollectorSourceExecution.collectCall input)
      (PlainBnfIndexedCollectorSourceExecution.encodeResult output))
    (query : List Scalar) :
    PlainBnfDefinitionIndexSourceExecution.definitionResult
      (PlainBnfGraphNameTrie.lookup query (PlainBnfIndexedCollectorSourceExecution.indexTrie output.2)) =
      PlainBnfDefinitionIndexSourceExecution.declarationResult (lookup query output.1.1) := by
  rw [PlainBnfIndexedCollectorSourceExecution.index_lookup,
    (PlainBnfIndexedCollectorSourceExecution.collect_observations input output executed).2 query]
  cases lookup query output.1.1 <;>
    rfl

/-- Exact finite-depth lookup through the collector-produced index. This is
the index passed by the enclosing validation source, not a supplied truth table. -/
theorem source_index_lookup_answers (input : List (PlainBnfIndexedCollectorSourceExecution.Entry Scalar))
    (output : (List (PlainBnfIndexedCollectorSourceExecution.Definition Scalar) ×
      List (PlainBnfIndexedCollectorSourceExecution.Diagnostic Scalar)) ×
      PlainBnfIndexedCollectorSourceExecution.Index Scalar)
    (executed : Step (engineBasePremises scalarRelations)
      PlainBnfIndexedCollectorSourceExecution.language
      (PlainBnfIndexedCollectorSourceExecution.collectCall input)
      (PlainBnfIndexedCollectorSourceExecution.encodeResult output))
    (query : List Scalar) (fuel : Nat) :
    rewriteAt (engineBasePremises scalarRelations) PlainBnfDefinitionIndexSourceExecution.language fuel
      (PlainBnfDefinitionIndexSourceExecution.definitionLookupCall query
        (PlainBnfIndexedCollectorSourceExecution.indexTrie output.2)) =
      if PlainBnfTrieSourceExecution.lookupHeight query
          (PlainBnfIndexedCollectorSourceExecution.indexTrie output.2) + 1 < fuel then
        [PlainBnfTrieSourceExecution.result
          (PlainBnfDefinitionIndexSourceExecution.declarationResult (lookup query output.1.1))]
      else [] := by
  rw [PlainBnfDefinitionIndexSourceExecution.definition_lookup_answers,
    source_index_result input output executed query]

theorem source_index_lookup_step_iff (input : List (PlainBnfIndexedCollectorSourceExecution.Entry Scalar))
    (output : (List (PlainBnfIndexedCollectorSourceExecution.Definition Scalar) ×
      List (PlainBnfIndexedCollectorSourceExecution.Diagnostic Scalar)) ×
      PlainBnfIndexedCollectorSourceExecution.Index Scalar)
    (executed : Step (engineBasePremises scalarRelations)
      PlainBnfIndexedCollectorSourceExecution.language
      (PlainBnfIndexedCollectorSourceExecution.collectCall input)
      (PlainBnfIndexedCollectorSourceExecution.encodeResult output))
    (query : List Scalar) (target : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    Step (engineBasePremises scalarRelations) PlainBnfDefinitionIndexSourceExecution.language
      (PlainBnfDefinitionIndexSourceExecution.definitionLookupCall query
        (PlainBnfIndexedCollectorSourceExecution.indexTrie output.2)) target ↔
      target = PlainBnfTrieSourceExecution.result
        (PlainBnfDefinitionIndexSourceExecution.declarationResult (lookup query output.1.1)) := by
  rw [PlainBnfDefinitionIndexSourceExecution.definition_lookup_step_iff,
    source_index_result input output executed query]

/-! ## The existing structured-document image -/

open PlainBnfReferenceCollectionSourceExecution (text expression span)
open PlainBnfStructuredDiscoveryGraph (definitionsFromDocument)

def canonicalName (value : String) : List Nat := value.toList.map Char.toNat

theorem canonicalName_injective : Function.Injective canonicalName := by
  intro left right same
  apply PlainBnfReferenceCollectionSourceExecution.text_injective
  exact congrArg PlainBnfCollectorSourceExecution.name same

def wireDefinition (value : PlainBnfStructuredDiscoveryGraph.Definition) :
    PlainBnfIndexedCollectorSourceExecution.Definition Nat :=
  ⟨canonicalName value.name, expression value.expression, span value.span⟩

def wireEntry : PlainBnfStructuredDenotation.Entry → PlainBnfIndexedCollectorSourceExecution.Entry Nat
  | .rule name value location => .rule (canonicalName name) (expression value) (span location)
  | .comment value location => .comment (text value) (span location)
  | .blank location => .blank (span location)

/-- The collector's returned definition has exactly the encoding consumed by
the already proved source enumeration; there is no render-and-reparse step. -/
theorem wireDefinition_enumeration (value : PlainBnfStructuredDiscoveryGraph.Definition) :
    PlainBnfCollectorSourceExecution.definition (wireDefinition value) =
      PlainBnfEnumerationSourceExecution.definition
        (PlainBnfStructuredEnumeration.wireDefinition value) := rfl

private theorem declarations_occurrences (input : List PlainBnfStructuredDenotation.Entry)
    (index : Nat) :
    declarations (input.map wireEntry) =
      (PlainBnfSemanticAdmission.ruleOccurrencesFrom input index).map
        (fun occurrence => wireDefinition ⟨occurrence.name, occurrence.expression, occurrence.span⟩) := by
  induction input generalizing index with
  | nil => rfl
  | cons head tail ih =>
      cases head <;>
        simpa [declarations, wireEntry, PlainBnfSemanticAdmission.ruleOccurrencesFrom,
          wireDefinition] using ih (index + 1)

theorem structured_declarations (document : PlainBnfStructuredDenotation.Document) :
    declarations (document.entries.map wireEntry) =
      (definitionsFromDocument document).map wireDefinition := by
  simpa [definitionsFromDocument, PlainBnfSemanticAdmission.ruleOccurrences, List.map_map, Function.comp_def]
    using declarations_occurrences document.entries 0

private theorem canonical_names_nodup (names : List String) :
    (names.map canonicalName).Nodup ↔ names.Nodup := by
  induction names with
  | nil => simp
  | cons head tail ih =>
      simp only [List.map_cons, List.nodup_cons, List.mem_map, ih]
      constructor
      · rintro ⟨absent, unique⟩
        exact ⟨fun member => absent ⟨head, member, rfl⟩, unique⟩
      · rintro ⟨absent, unique⟩
        refine ⟨?_, unique⟩
        rintro ⟨other, member, same⟩
        exact absent ((canonicalName_injective same) ▸ member)

theorem structured_names_nodup_iff (document : PlainBnfStructuredDenotation.Document) :
    ((declarations (document.entries.map wireEntry)).map Definition.name).Nodup ↔
      ((PlainBnfSemanticAdmission.ruleOccurrences document).map (·.name)).Nodup := by
  rw [structured_declarations]
  simpa [definitionsFromDocument, wireDefinition, List.map_map, Function.comp_def]
    using canonical_names_nodup ((PlainBnfSemanticAdmission.ruleOccurrences document).map (·.name))

/-- Exactly the name-uniqueness conjunct needed by `WellFormed`, now linked to
the authored indexed collector on canonically encoded structured documents. -/
theorem structured_source_clean_iff (document : PlainBnfStructuredDenotation.Document)
    (output : (List (PlainBnfIndexedCollectorSourceExecution.Definition Nat) ×
      List (PlainBnfIndexedCollectorSourceExecution.Diagnostic Nat)) ×
      PlainBnfIndexedCollectorSourceExecution.Index Nat)
    (executed : Step (engineBasePremises scalarRelations)
      PlainBnfIndexedCollectorSourceExecution.language
      (PlainBnfIndexedCollectorSourceExecution.collectCall (document.entries.map wireEntry))
      (PlainBnfIndexedCollectorSourceExecution.encodeResult output)) :
    output.1.2 = [] ↔
      ((PlainBnfSemanticAdmission.ruleOccurrences document).map (·.name)).Nodup :=
  (source_clean_iff _ output executed).trans (structured_names_nodup_iff document)

theorem structured_source_payloads (document : PlainBnfStructuredDenotation.Document)
    (output : (List (PlainBnfIndexedCollectorSourceExecution.Definition Nat) ×
      List (PlainBnfIndexedCollectorSourceExecution.Diagnostic Nat)) ×
      PlainBnfIndexedCollectorSourceExecution.Index Nat)
    (executed : Step (engineBasePremises scalarRelations)
      PlainBnfIndexedCollectorSourceExecution.language
      (PlainBnfIndexedCollectorSourceExecution.collectCall (document.entries.map wireEntry))
      (PlainBnfIndexedCollectorSourceExecution.encodeResult output))
    (clean : output.1.2 = []) :
    output.1.1 = (definitionsFromDocument document).map wireDefinition :=
  (source_clean_payloads _ output executed clean).trans (structured_declarations document)

/-- Duplicate spellings cannot pass even when every complete payload agrees. -/
theorem duplicate_not_clean (name : Name) (value : Expression) (location : Span)
    (comment : Text) :
    (collect [.rule name value location, .comment comment location,
      .blank location, .rule name value location] []).2 ≠ [] := by
  rw [ne_eq, collect_empty_clean_iff]
  simp [declarations]

/-- Rule-looking text in a comment is not a declaration. -/
theorem comment_and_blank_are_not_duplicates (name : Name) (value : Expression)
    (location : Span) (comment : Text) :
    (collect [.comment comment location, .rule name value location, .blank location] []).2 = [] := by
  rw [collect_empty_clean_iff]
  simp [declarations]

end Mettapedia.GSLT.Parsing.PlainBnfDeclarationAdmission
