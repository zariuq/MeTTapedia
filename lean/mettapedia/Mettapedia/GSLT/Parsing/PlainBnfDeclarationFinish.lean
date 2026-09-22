import Mettapedia.GSLT.Parsing.PlainBnfDeclarationAdmission
import Mettapedia.GSLT.Parsing.PlainBnfValidationFinishSourceExecution

/-!
# Ordered declaration collection, diagnostic append, and finish

This composes the actual indexed collector with the actual diagnostic append
and validation finish clauses. Acceptance at this boundary requires a nonempty
unique declaration list and no remaining diagnostics. A `StartSome` value is
an explicit input here: its resolution and the production of the remaining
lexical/reference/start diagnostics are not assumed to have been validated.

The component Steps are related at their exact encoded values. This is not yet
execution of the enclosing validation rule or its generated PeTTa body.
-/

namespace Mettapedia.GSLT.Parsing.PlainBnfDeclarationFinish

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (Step BasePremiseEvaluator engineBasePremises)
open PlainBnfTrieSourceExecution (result scalarRelations result_injective)
open PlainBnfDeclarationAdmission (declarations source_clean_iff source_clean_payloads)
open PlainBnfValidationFinishSourceExecution
  (language diagnostics nil definitionsCons finishCall accepted refused startSome appendCall
   finish_empty_step_iff finish_accepted_step_iff finish_refused_step_iff append_decoded_step_iff)

variable {Scalar : Type} [DecidableEq Scalar]
  [PlainBnfCollectorSourceExecution.NameScalarCodec Scalar]

def encodedDefinitions (values : List (PlainBnfIndexedCollectorSourceExecution.Definition Scalar)) : SExpr :=
  PlainBnfCollectorSourceExecution.definitions (values.map PlainBnfCollectorSourceExecution.definition)

omit [DecidableEq Scalar] in
/-- An empty list of declarations never admits, even with a fabricated
`StartSome` and an empty diagnostic list. Nonempty diagnostics prohibit acceptance. -/
theorem finish_acceptance_iff (base : BasePremiseEvaluator)
    (documentSpan startName startSpan lexicals : SExpr)
    (values : List (PlainBnfIndexedCollectorSourceExecution.Definition Scalar))
    (ds : List SExpr) :
    Step base language
      (finishCall documentSpan (startSome startName startSpan) (encodedDefinitions values) lexicals (diagnostics ds))
      (result (accepted (startSome startName startSpan) (encodedDefinitions values) lexicals)) ↔
      values ≠ [] ∧ ds = [] := by
  cases values with
  | nil =>
      simp only [encodedDefinitions, List.map_nil, PlainBnfCollectorSourceExecution.definitions]
      rw [finish_empty_step_iff]
      simp [result_injective.eq_iff, accepted, refused]
  | cons head tail =>
      have unfold : encodedDefinitions (head :: tail) =
          definitionsCons (PlainBnfCollectorSourceExecution.definition head) (encodedDefinitions tail) := rfl
      rw [unfold]
      cases ds with
      | nil =>
          rw [show diagnostics [] = nil from rfl]
          rw [finish_accepted_step_iff]
          simp
      | cons first rest =>
          rw [show diagnostics (first :: rest) =
            PlainBnfValidationFinishSourceExecution.cons first (diagnostics rest) from rfl]
          rw [finish_refused_step_iff]
          simp [result_injective.eq_iff, accepted, refused]

omit [DecidableEq Scalar] in
/-- The declaration diagnostic codec agrees with the finish/append codec at
every list, not merely at the empty successful case. -/
theorem diagnostic_codecs (values : List (PlainBnfIndexedCollectorSourceExecution.Diagnostic Scalar)) :
    PlainBnfCollectorSourceExecution.diagnostics values =
      diagnostics (values.map PlainBnfCollectorSourceExecution.diagnostic) := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      simp [PlainBnfCollectorSourceExecution.diagnostics, diagnostics,
        PlainBnfValidationFinishSourceExecution.cons, ih]

/-- Exact declaration-side acceptance contract after an executed source
collector. Other checks contribute ordinary ordered diagnostic occurrences;
none can cancel a duplicate-definition diagnostic. -/
theorem collector_append_finish_iff
    (input : List (PlainBnfIndexedCollectorSourceExecution.Entry Scalar))
    (output : (List (PlainBnfIndexedCollectorSourceExecution.Definition Scalar) ×
      List (PlainBnfIndexedCollectorSourceExecution.Diagnostic Scalar)) ×
      PlainBnfIndexedCollectorSourceExecution.Index Scalar)
    (executed : Step (engineBasePremises scalarRelations)
      PlainBnfIndexedCollectorSourceExecution.language
      (PlainBnfIndexedCollectorSourceExecution.collectCall input)
      (PlainBnfIndexedCollectorSourceExecution.encodeResult output))
    (documentSpan startName startSpan lexicals : SExpr) (remaining : List SExpr) :
    (∃ combined : List SExpr,
      Step (engineBasePremises scalarRelations) language
        (appendCall (PlainBnfCollectorSourceExecution.diagnostics output.1.2) (diagnostics remaining))
        (result (diagnostics combined)) ∧
      Step (engineBasePremises scalarRelations) language
        (finishCall documentSpan (startSome startName startSpan)
          (encodedDefinitions output.1.1) lexicals (diagnostics combined))
        (result (accepted (startSome startName startSpan) (encodedDefinitions output.1.1) lexicals))) ↔
      declarations input ≠ [] ∧
      ((declarations input).map PlainBnfDeclarationSemantics.Definition.name).Nodup ∧
      remaining = [] := by
  rw [diagnostic_codecs]
  simp only [append_decoded_step_iff, finish_acceptance_iff, exists_eq_left,
    List.append_eq_nil_iff, List.map_eq_nil_iff]
  constructor
  · rintro ⟨nonempty, clean, rest⟩
    exact ⟨(source_clean_payloads input output executed clean) ▸ nonempty,
      (source_clean_iff input output executed).mp clean, rest⟩
  · rintro ⟨nonempty, unique, rest⟩
    have clean := (source_clean_iff input output executed).mpr unique
    exact ⟨(source_clean_payloads input output executed clean).symm ▸ nonempty, clean, rest⟩

end Mettapedia.GSLT.Parsing.PlainBnfDeclarationFinish
