import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NumberedSourceResolve
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NumberedSourceRegistryControls

/-!
# Reference queries, actual cached syntax and registry changes

The captured truth prefix is queried independently of the cache folds.
Transport consumes the checked registry extension. Missing cache data and
signature-invalid annotations are distinguished from source-node decoding.
The shadow control concerns metadata, not a new kernel derivation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberedSourceResolveControls

open Lean Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ProofExecution DefinitionAdapters SignatureFormation NumberedSourceSyntax NumberedSourceResolve

theorem captured_truth_resolves :
    term? NumberedSourceSyntaxControls.symbols NumberedSourceSyntaxControls.typeRows
      NumberedSourceSyntaxControls.termRows 4 = some StandardTheoryInterpretation.Source.truthBody := by
  rw [← NumberedSourceSyntaxControls.decodedTruth_eq]
  exact term_complete _ _ _ _ _ NumberedSourceSyntaxControls.decodedTruth_at

theorem captured_truth_query_computes :
    (term? NumberedSourceSyntaxControls.symbols NumberedSourceSyntaxControls.typeRows
      NumberedSourceSyntaxControls.termRows 4).isSome = true := by decide +kernel

/-- Annotation indices belong to the type table, not the term-index order. -/
theorem independent_annotation_space :
    (term? NumberedSourceSyntaxControls.symbols NumberedSourceSyntaxControls.typeRows
      NumberedSourceSyntaxControls.termRows 2).isSome = true := by decide +kernel

theorem actual_truth_registration_preserves_query :
    term? NumberedSourceRegistryControls.truthSymbols NumberedSourceSyntaxControls.typeRows
      NumberedSourceSyntaxControls.termRows 4 = some StandardTheoryInterpretation.Source.truthBody :=
  term_preserved ((NumberedSourceRegistry.preserves?_eq_true_iff _ _).mp
    NumberedSourceRegistryControls.truth_preserves_literal_prefix) _ _ _ _ captured_truth_resolves

theorem actual_cached_query_survives_registration :
    term? NumberedSourceRegistryControls.truthSymbols NumberedSourceSyntaxControls.typeRows
      NumberedSourceSyntaxControls.termRows 4 = some NumberedSourceSyntaxControls.decodedTruth :=
  checked_cached_term_preserved NumberedSourceRegistryControls.truth_preserves_literal_prefix _ _
    NumberedSourceSyntaxControls.termCache NumberedSourceSyntaxControls.term_cache_correct 4 _
      (Option.some_get NumberedSourceSyntaxControls.term_four_available).symm

theorem cache_miss_is_not_syntax_refusal :
    appendTerm? NumberedSourceSyntaxControls.symbols NumberedSourceSyntaxControls.termRows
      NumberedSourceSyntaxControls.typeCache (fun _ => none) 4 = none ∧
      (term? NumberedSourceSyntaxControls.symbols NumberedSourceSyntaxControls.typeRows
        NumberedSourceSyntaxControls.termRows 4).isSome = true :=
  ⟨rfl,captured_truth_query_computes⟩

def wrongAnnotation (index : Nat) : Option Json :=
  if index = 5 then some (.arr #[.str "const",.str "=",.num 0])
  else NumberedSourceSyntaxControls.termRows index

theorem wrong_annotation_decodes :
    term? NumberedSourceSyntaxControls.symbols NumberedSourceSyntaxControls.typeRows wrongAnnotation 5 =
      some (.const Const.equality Ty.bool) := by
  apply term_complete
  refine TermAt.constant rfl rfl rfl ?_
  exact NumberedSourceSyntaxControls.type_cache_correct 0 _ rfl

theorem decoded_annotation_still_fails_signature :
    (checkSource SourceProfile.primitiveContext.signature
      (ExportReplay.instanceCertificates SourceProfile.primitiveContext.signature)
      (.const Const.equality Ty.bool)).isNone = true :=
  NumberedSourceSyntaxControls.equality_annotation_signature_refused

def selfApplication (index : Nat) : Option Json :=
  if index = 0 then some (.arr #[.str "app",.num 0,.num 0]) else none

theorem self_reference_refused :
    term? NumberedSourceSyntaxControls.symbols NumberedSourceSyntaxControls.typeRows selfApplication 0 = none := by
  rw [term_unfold]
  rfl

theorem old_shadow_query :
    term? NumberedSourceRegistryControls.shadowBefore NumberedSourceSyntaxControls.typeRows
      NumberedSourceRegistryControls.shadowRows 0 = some NumberedSourceRegistryControls.oldTerm :=
  term_complete _ _ _ _ _ NumberedSourceRegistryControls.old_shadow_read

theorem new_shadow_query :
    term? NumberedSourceRegistryControls.shadowAfter NumberedSourceSyntaxControls.typeRows
      NumberedSourceRegistryControls.shadowRows 0 = some NumberedSourceRegistryControls.newTerm :=
  term_complete _ _ _ _ _ NumberedSourceRegistryControls.new_shadow_read

theorem shadow_cannot_return_old_node :
    term? NumberedSourceRegistryControls.shadowAfter NumberedSourceSyntaxControls.typeRows
      NumberedSourceRegistryControls.shadowRows 0 ≠ some NumberedSourceRegistryControls.oldTerm := by
  intro found
  exact NumberedSourceRegistryControls.old_shadow_read_not_retained (term_sound _ _ _ _ _ found)

/-- A whole-registry check can fail while a query's smaller support survives. -/
theorem unrelated_query_survives_shadow :
    NumberedSourceRegistry.preserves? NumberedSourceRegistryControls.shadowBefore
      NumberedSourceRegistryControls.shadowAfter = false ∧
      term? NumberedSourceRegistryControls.shadowBefore NumberedSourceSyntaxControls.typeRows
        NumberedSourceSyntaxControls.termRows 4 = some NumberedSourceSyntaxControls.decodedTruth ∧
      term? NumberedSourceRegistryControls.shadowAfter NumberedSourceSyntaxControls.typeRows
        NumberedSourceSyntaxControls.termRows 4 = some NumberedSourceSyntaxControls.decodedTruth := by
  obtain ⟨rejected,before,after⟩ := NumberedSourceRegistryControls.unrelated_truth_cache_survives_shadow
  exact ⟨rejected,
    term_cache_read_agrees _ _ _ _ before 4 _ (Option.some_get NumberedSourceSyntaxControls.term_four_available).symm,
    term_cache_read_agrees _ _ _ _ after 4 _ (Option.some_get NumberedSourceSyntaxControls.term_four_available).symm⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberedSourceResolveControls
