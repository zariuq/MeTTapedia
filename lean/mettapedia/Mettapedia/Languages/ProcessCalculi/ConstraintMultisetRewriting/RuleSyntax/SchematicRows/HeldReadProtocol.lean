import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadMaterializer

/-!
# An actual materialize-and-consume execution denotes a schematic read

The equivalence concerns a two-firing run with a private temporary occurrence.
It compares all final models over a fixed source interpretation, not merely
the existence of an unconstrained solution. The persistent source, original
occurrences and their shared terms are retained. The temporary is not present at
the end. A chronological observer still sees two events; no equivalence for
arbitrary observations of the intermediate state is asserted.

Freshness does not itself hide a row from other ambient firings. Contextual
replacement additionally requires a private access scope or a protocol-phase
restriction; the isolated run equivalence does not supply that restriction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadProtocol

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig)
open RuleOccurrences HeldCopyConsumer HeldReadMaterializer

universe uOcc uR uC uZ
variable {O : Type uOcc} [DecidableEq O] {R : Type uR} [DecidableEq R]
  {C : Type uC} {Z : Type uZ}
  (codes : Codes RowTerms C Z) (ambient : Set C) (s : RState RowTerms O R C Z)
  (held : R) (temporary output : O) (reader : C)

abbrev machine := (rstep X O R E codes ambient).toStep

noncomputable def execution
    (materialized : (materializer codes s held temporary).Admits X ambient)
    (consumed : (consumer codes ((materializer codes s held temporary).result X)
      reader temporary output).Admits X ambient) : (machine codes ambient).Run s :=
  .cons (materializer codes s held temporary) materialized
    (.cons (consumer codes ((materializer codes s held temporary).result X) reader temporary output)
      consumed (.nil _))

theorem execution_last
    (materialized : (materializer codes s held temporary).Admits X ambient)
    (consumed : (consumer codes ((materializer codes s held temporary).result X)
      reader temporary output).Admits X ambient) :
    (execution codes ambient s held temporary output reader materialized consumed).last =
      (consumer codes ((materializer codes s held temporary).result X) reader temporary output).result X := rfl

theorem execution_length
    (materialized : (materializer codes s held temporary).Admits X ambient)
    (consumed : (consumer codes ((materializer codes s held temporary).result X)
      reader temporary output).Admits X ambient) :
    (execution codes ambient s held temporary output reader materialized consumed).word.length = 2 := rfl

theorem reading_iff_execution (schema : Schema RowTerms)
    (declared : codes.unfold (s.held held).code = schema.toSpec)
    (readerDeclared : codes.unfold reader = readerSpec) (readerAvailable : reader ∈ ambient)
    (heldPresent : held ∈ s.rules) (persistent : (s.held held).mode = .persistent)
    (lengths : schema.params.length = (s.held held).args.length)
    (temporaryFresh : temporary ∉ s.present) (outputFresh : output ∉ s.present)
    (different : output ≠ temporary) (caller : Subst rowSig)
    (known : X.Models (a := s.frame) (b := PUnit.unit) caller s.knowledge) (value : Tm) :
    (⟨schema, (s.held held).args⟩ : Closure RowTerms s.frame).ReadsAt X (b := PUnit.unit) caller value ↔
      ∃ (materialized : (materializer codes s held temporary).Admits X ambient)
        (consumed : (consumer codes ((materializer codes s held temporary).result X)
          reader temporary output).Admits X ambient) (point : Subst rowSig),
        X.Models (a := s.frame) (b := PUnit.unit) point
          (execution codes ambient s held temporary output reader materialized consumed).last.knowledge ∧
        (∀ term, s.Mentions term → point.applyTerm term = caller.applyTerm term) ∧
        point.applyTerm
          ((execution codes ambient s held temporary output reader materialized consumed).last.label output) = value := by
  have temporaryPresent : temporary ∈ ((materializer codes s held temporary).result X).present := by
    rw [HeldReadMaterializer.result_present]
    exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  have outputNotPresent : output ∉ ((materializer codes s held temporary).result X).present := by
    rw [HeldReadMaterializer.result_present]
    simp only [Finset.mem_union, Finset.mem_singleton, not_or]
    exact ⟨outputFresh, different⟩
  constructor
  · intro reading
    have materialized := HeldReadMaterializer.admitted codes s held temporary schema ambient
      declared heldPresent temporaryFresh caller known value reading
    obtain ⟨middle, middleKnown, sourceAgrees, middleValue⟩ :=
      (reading_iff_models codes s held temporary schema ambient declared heldPresent lengths caller known value).mp reading
    have consumed := HeldReadConsumer.admitted codes ((materializer codes s held temporary).result X)
      reader temporary output ambient readerDeclared readerAvailable temporaryPresent outputNotPresent middle middleKnown
    obtain ⟨point, finalKnown, kept, outputValue⟩ := HeldReadConsumer.extends_model codes
      ((materializer codes s held temporary).result X) reader temporary output readerDeclared
      temporaryPresent middle middleKnown
    refine ⟨materialized, consumed, point, finalKnown, ?_, ?_⟩
    · intro term mentioned
      exact (kept term (source_mentions_retained codes s held temporary schema ambient
        declared persistent temporaryFresh term mentioned)).trans (sourceAgrees term mentioned)
    · change point.applyTerm (((consumer codes ((materializer codes s held temporary).result X)
        reader temporary output).result X).label output) = value
      rw [consumer_result_label codes ((materializer codes s held temporary).result X)
        reader temporary output readerDeclared]
      exact outputValue.trans middleValue
  · rintro ⟨materialized, consumed, point, finalKnown, kept, valueEq⟩
    have model := (HeldReadConsumer.result_models_iff codes
      ((materializer codes s held temporary).result X) reader temporary output readerDeclared point).mp finalKnown
    apply (reading_iff_models codes s held temporary schema ambient declared heldPresent lengths caller known value).mpr
    exact ⟨point, model.1, kept, model.2.symm.trans valueEq⟩

theorem temporary_not_present
    (materialized : (materializer codes s held temporary).Admits X ambient)
    (consumed : (consumer codes ((materializer codes s held temporary).result X)
      reader temporary output).Admits X ambient) (different : output ≠ temporary) :
    temporary ∉ (execution codes ambient s held temporary output reader materialized consumed).last.present :=
  temporary_is_consumed codes ((materializer codes s held temporary).result X)
    reader temporary output (Ne.symm different)

theorem final_present
    (materialized : (materializer codes s held temporary).Admits X ambient)
    (consumed : (consumer codes ((materializer codes s held temporary).result X)
      reader temporary output).Admits X ambient) (temporaryFresh : temporary ∉ s.present) :
    (execution codes ambient s held temporary output reader materialized consumed).last.present =
      s.present ∪ {output} := by
  rw [execution_last, HeldReadConsumer.result_present, HeldReadMaterializer.result_present]
  ext occurrence
  by_cases same : occurrence = temporary
  · subst occurrence
    simp [temporaryFresh]
  · simp [same]

theorem final_rules
    (materialized : (materializer codes s held temporary).Admits X ambient)
    (consumed : (consumer codes ((materializer codes s held temporary).result X)
      reader temporary output).Admits X ambient) (persistent : (s.held held).mode = .persistent) :
    (execution codes ambient s held temporary output reader materialized consumed).last.rules = s.rules := by
  rw [execution_last, consumer_keeps_held_rules, HeldReadMaterializer.result_rules codes s held temporary persistent]

#print axioms execution_length
#print axioms reading_iff_execution
#print axioms temporary_not_present
#print axioms final_present
#print axioms final_rules

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadProtocol
