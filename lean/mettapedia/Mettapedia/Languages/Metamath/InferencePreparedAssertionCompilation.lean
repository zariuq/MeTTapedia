import Mettapedia.GSLT.LanguageDef.MonotoneUniqueIndexCompilation
import Mettapedia.Languages.Metamath.InferenceAssertionFusedCompilation

/-!
# Prepared assertion-record compilation for Metamath inference

A successful Metamath prefix projection already proves that stored assertion
labels are unique.  This file turns precisely that invariant into an indexed
assertion-record artifact and composes record selection with the independently
proved fused assertion-application semantics.

The source semantics remains the authored ordered scan.  A malformed snapshot
with duplicate assertion labels can still be scanned, but it is not admitted
to the indexed path; the negative example records the observable ambiguity.
-/

namespace Mettapedia.Languages.Metamath.InferencePreparedAssertionCompilation

open Mettapedia.GSLT.LanguageDef.MonotoneUniqueIndexCompilation
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
open Mettapedia.Languages.Metamath.InferenceAssertionFusedCompilation

/-! ## The source-derived record table -/

/-- The admitted effect trace builds one fresh immutable table and then reads
it.  Mutation after publication is deliberately outside this artifact. -/
def assertionIndexShape : TableShape :=
  ⟨32, [.insertFresh, .lookup]⟩

def assertionIndexPlan : Plan :=
  ⟨32, [.insertFresh, .lookup]⟩

theorem assertionIndexShape_recognized :
    recognize assertionIndexShape = some assertionIndexPlan := by
  rfl

/-- Each indexed value is the complete stored assertion record: label,
formula, frame, and ordered mandatory hypotheses. -/
def assertionRecordEntries (projection : PrefixProjection) :
    List (String × AssertionView) :=
  projection.assertions.map fun assertion => (assertion.label, assertion)

/-- Source scan plus the requested label occurrences. -/
def assertionRecordSource (projection : PrefixProjection)
    (queries : List String) : SourceProgram String AssertionView where
  shape := assertionIndexShape
  entries := assertionRecordEntries projection
  queries := queries

/-- Exact lookup observation exported by the prepared immutable index. -/
def compiledAssertionRecord? (projection : PrefixProjection)
    (label : String) : Option AssertionView :=
  (compileIndex (assertionRecordEntries projection))[label]?

/-! ## Projection validity supplies exact cardinality -/

/-- The assertion-label suffix of every revalidated prefix projection is
duplicate-free.  No second uniqueness certificate is introduced. -/
theorem assertionLabels_nodup_of_prefixProjectionValid
    (projection : PrefixProjection)
    (valid : prefixProjectionValid projection = true) :
    (projection.assertions.map AssertionView.label).Nodup := by
  have valid' := valid
  simp only [prefixProjectionValid, Bool.and_eq_true] at valid'
  have labelsValid := valid'.2
  simp only [sourceRuleLabelsValid, Bool.and_eq_true, beq_iff_eq] at labelsValid
  have allLabels : (sourceRuleLabels projection).Nodup :=
    nodup_of_eraseDups_length_eq _ labelsValid.2
  simpa [sourceRuleLabels] using (List.nodup_append.mp allLabels).2.1

/-- Successful live projection exposes the same assertion-label invariant. -/
theorem projected_assertionLabels_nodup
    (db : RuntimeDB) (projection : PrefixProjection)
    (projected : projectPrefix? db = some projection) :
    (projection.assertions.map AssertionView.label).Nodup :=
  assertionLabels_nodup_of_prefixProjectionValid projection
    (prefixProjectionValid_of_projectPrefix?_eq_some db projection projected)

/-- Proposition-level uniqueness is exactly the executable admission bit
consumed by the generic unique-index compiler. -/
theorem assertionRecordKeys_allDistinct
    (projection : PrefixProjection)
    (valid : prefixProjectionValid projection = true) :
    Mettapedia.Util.LinearHash.allDistinct
        ((assertionRecordEntries projection).map Prod.fst) = true := by
  rw [show (assertionRecordEntries projection).map Prod.fst =
      projection.assertions.map AssertionView.label by
    simp [assertionRecordEntries]]
  exact (Mettapedia.Util.LinearHash.allDistinct_eq_true_iff _).2
    (assertionLabels_nodup_of_prefixProjectionValid projection valid)

/-- A valid prefix projection is admitted directly to the generic immutable
unique-index compiler. -/
def admittedAssertionRecords (projection : PrefixProjection)
    (queries : List String)
    (valid : prefixProjectionValid projection = true) :
    AdmittedProgram String AssertionView where
  source := assertionRecordSource projection queries
  plan := assertionIndexPlan
  shapeAccepted := assertionIndexShape_recognized
  keysDistinct := by
    simpa [assertionRecordSource] using
      assertionRecordKeys_allDistinct projection valid

/-! ## Exact record lookup -/

/-- Unique authored labels make the source scan select the exact stored
record occurrence, not merely another record with the same key. -/
theorem sourceLookup_assertionRecord_of_mem
    (assertions : List AssertionView) (target : AssertionView)
    (unique : (assertions.map AssertionView.label).Nodup)
    (member : target ∈ assertions) :
    sourceLookup target.label
        (assertions.map fun assertion => (assertion.label, assertion)) =
      some target := by
  induction assertions with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, List.nodup_cons] at unique
      rcases List.mem_cons.mp member with targetEq | targetMember
      · subst target
        simp [sourceLookup]
      · have labelsNe : head.label ≠ target.label := by
          intro labelsEq
          apply unique.1
          rw [labelsEq]
          exact List.mem_map_of_mem targetMember
        simp [sourceLookup, labelsNe,
          inductionHypothesis unique.2 targetMember]

/-- The compiled map returns the exact source assertion selected by the
duplicate-free ordered scan. -/
theorem compiledAssertionRecord_lookup_of_mem
    (projection : PrefixProjection) (assertion : AssertionView)
    (valid : prefixProjectionValid projection = true)
    (member : assertion ∈ projection.assertions) :
    compiledAssertionRecord? projection assertion.label = some assertion := by
  unfold compiledAssertionRecord?
  rw [lookup_compileIndex]
  exact sourceLookup_assertionRecord_of_mem projection.assertions assertion
    (assertionLabels_nodup_of_prefixProjectionValid projection valid) member

/-- The complete artifact observes exactly the authored ordered scan for any
query list, including absent labels. -/
theorem compiledAssertionRecords_observe_source
    (projection : PrefixProjection) (queries : List String)
    (valid : prefixProjectionValid projection = true) :
    runArtifact
        (compile (admittedAssertionRecords projection queries valid).plan
          (admittedAssertionRecords projection queries valid).source) =
      runSource (assertionRecordSource projection queries) := by
  exact runArtifact_compile
    (admittedAssertionRecords projection queries valid).plan
    (admittedAssertionRecords projection queries valid).source

/-! ## Selection followed by fused application -/

/-- One successful live projection simultaneously licenses exact stored-record
selection and allocation-free assertion application.  Selection preserves the
whole `AssertionView`; fusion preserves the proof-relevant substitution,
essential-hypothesis, disjoint-variable, and result obligations. -/
theorem projected_preparedAssertionApplication
    (db : RuntimeDB) (projection : PrefixProjection)
    (assertion : AssertionView)
    (projected : projectPrefix? db = some projection)
    (member : assertion ∈ projection.assertions)
    (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula) :
    compiledAssertionRecord? projection assertion.label = some assertion ∧
      (AssertionApplicationSemantics projection.callerFrame assertion actuals
          result ↔
        FusedAssertionApplicationSemantics projection.callerFrame assertion
          actuals result) := by
  have valid :=
    prefixProjectionValid_of_projectPrefix?_eq_some db projection projected
  exact ⟨compiledAssertionRecord_lookup_of_mem projection assertion valid
      member,
    projected_assertionApplicationSemantics_iff_fused db projection assertion
      projected member actuals result⟩

/-! ## Refusing duplicate-label control -/

namespace Examples

private def emptyFrame : RuntimeFrame := ⟨#[], #[]⟩

private def firstAssertion : AssertionView where
  label := "dup"
  formula := ⟨"|-", [.const "A"]⟩
  frame := emptyFrame
  hypotheses := []

private def secondAssertion : AssertionView where
  label := "dup"
  formula := ⟨"|-", [.const "B"]⟩
  frame := emptyFrame
  hypotheses := []

def duplicateProjection : PrefixProjection where
  declaredConstants := ["|-", "A", "B"]
  declaredVariables := []
  callerFrame := emptyFrame
  activeHypotheses := []
  assertions := [firstAssertion, secondAssertion]

/-- Both duplicate records remain visible to the source semantics. -/
theorem duplicate_second_is_visible :
    secondAssertion ∈ duplicateProjection.assertions := by
  simp [duplicateProjection]

/-- The ordered source scan selects the first duplicate and therefore cannot
serve as an exact selector for the second occurrence. -/
theorem duplicate_source_selects_first :
    sourceLookup "dup" (assertionRecordEntries duplicateProjection) =
      some firstAssertion := by
  rfl

theorem duplicate_source_does_not_select_second :
    sourceLookup "dup" (assertionRecordEntries duplicateProjection) ≠
      some secondAssertion := by
  change some firstAssertion ≠ some secondAssertion
  intro same
  have formulas := congrArg AssertionView.formula (Option.some.inj same)
  simp [firstAssertion, secondAssertion] at formulas

/-- Projection validation rejects the ambiguous stored assertion table. -/
theorem duplicate_projection_refused :
    prefixProjectionValid duplicateProjection = false := by
  rw [Bool.eq_false_iff]
  intro accepted
  simp only [prefixProjectionValid, Bool.and_eq_true] at accepted
  have labelsAccepted := accepted.2
  simp [sourceRuleLabelsValid, sourceRuleLabels, duplicateProjection,
    firstAssertion, secondAssertion] at labelsAccepted
  have impossible : ¬ (["dup", "dup"].eraseDups.length = 2) := by
    decide
  exact impossible labelsAccepted.2

/-- The executable unique-index admission bit refuses the same ambiguity. -/
theorem duplicate_index_refused :
    Mettapedia.Util.LinearHash.allDistinct
        ((assertionRecordEntries duplicateProjection).map Prod.fst) = false := by
  rw [Mettapedia.Util.LinearHash.allDistinct_eq_eraseDupsLength]
  decide

end Examples

#print axioms assertionLabels_nodup_of_prefixProjectionValid
#print axioms compiledAssertionRecord_lookup_of_mem
#print axioms projected_preparedAssertionApplication
#print axioms Examples.duplicate_projection_refused

end Mettapedia.Languages.Metamath.InferencePreparedAssertionCompilation
