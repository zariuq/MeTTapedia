import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadProtocol

/-! # Executed and separating controls for private materialization -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadControls

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig)
open RuleOccurrences HeldCopyConsumer HeldReadMaterializer HeldReadProtocol
open ApplicationSyntax (symbol)

def codeBook (schema : Schema RowTerms) : Codes RowTerms Bool Unit where
  unfold code := if code then readerSpec else schema.toSpec
  denotes _ _ _ := False
  close _ _ _ := none

def source (arguments : List Tm) : RState RowTerms Nat Nat Bool Unit :=
  ⟨⟨PUnit.unit, [], ∅, fun _ => symbol 99⟩, {0}, fun _ => ⟨false, arguments, .persistent, ()⟩⟩

def freeSchema : Schema RowTerms := ⟨PUnit.unit, [], [], .var 0⟩
def capturedSchema : Schema RowTerms := ⟨PUnit.unit, [], [.var 0], .var 0⟩

def publicSource : RState RowTerms Nat Nat Bool Unit :=
  { source [] with present := {7} }

theorem free_reading (value : Tm) :
    (⟨freeSchema, []⟩ : Closure RowTerms PUnit.unit).ReadsAt X (b := PUnit.unit)
      (Subst.id rowSig) value := by
  refine ⟨(fun _ => value), Interface.Frames.models_nil
    (X := X) (a := PUnit.unit) (b := PUnit.unit) _, List.Forall₂.nil, rfl⟩

theorem free_execution (value : Tm) :
    ∃ run : (machine (codeBook freeSchema) ({true} : Set Bool)).Run (source []),
      run.word.length = 2 ∧ 0 ∉ run.last.present ∧ 0 ∈ run.last.rules ∧
      ∃ point : Subst rowSig,
        X.Models (a := PUnit.unit) (b := PUnit.unit) point run.last.knowledge ∧
        point.applyTerm (run.last.label 1) = value := by
  obtain ⟨materialized, consumed, point, model, _, output⟩ :=
    (reading_iff_execution (codeBook freeSchema) {true} (source []) 0 0 1 true freeSchema
      rfl rfl (by simp) (by decide) rfl rfl (by decide) (by decide) (by decide)
      (Subst.id rowSig) (Interface.Frames.models_nil
        (X := X) (a := PUnit.unit) (b := PUnit.unit) _) value).mp (free_reading value)
  refine ⟨execution (codeBook freeSchema) {true} (source []) 0 0 1 true materialized consumed,
    execution_length _ _ _ _ _ _ _ _ _, temporary_not_present _ _ _ _ _ _ _ _ _ (by decide),
    ?_, point, model, output⟩
  rw [final_rules _ _ _ _ _ _ _ _ _ rfl]
  decide

theorem captured_materializer_admitted :
    (materializer (codeBook capturedSchema) (source [.var 0]) 0 0).Admits X ({true} : Set Bool) := by
  apply HeldReadMaterializer.admitted (codeBook capturedSchema) (source [.var 0]) 0 0
    capturedSchema {true} rfl (by decide) (by decide) (Subst.id rowSig)
    (Interface.Frames.models_nil (X := X) (a := PUnit.unit) (b := PUnit.unit) _) (.var 0)
  exact (Closure.readsAt_captured_iff (a := PUnit.unit) (b := PUnit.unit)
    X (.var 0 : Tm) (Subst.id rowSig) (.var 0)).mpr rfl

theorem captured_output_cannot_change
    (materialized : (materializer (codeBook capturedSchema) (source [.var 0]) 0 0).Admits X ({true} : Set Bool))
    (consumed : (consumer (codeBook capturedSchema)
      ((materializer (codeBook capturedSchema) (source [.var 0]) 0 0).result X)
      true 0 1).Admits X ({true} : Set Bool)) (point : Subst rowSig)
    (model : X.Models (a := PUnit.unit) (b := PUnit.unit) point
      (execution (codeBook capturedSchema) {true} (source [.var 0]) 0 0 1 true materialized consumed).last.knowledge)
    (kept : ∀ term, (source [.var 0]).Mentions term → point.applyTerm term = term) :
    point.applyTerm
      ((execution (codeBook capturedSchema) {true} (source [.var 0]) 0 0 1 true materialized consumed).last.label 1) ≠
      symbol 5 := by
  intro changed
  have reading := (reading_iff_execution (codeBook capturedSchema) {true} (source [.var 0]) 0 0 1 true
    capturedSchema rfl rfl (by simp) (by decide) rfl rfl (by decide) (by decide) (by decide)
    (Subst.id rowSig) (Interface.Frames.models_nil
      (X := X) (a := PUnit.unit) (b := PUnit.unit) _) (symbol 5)).mpr
      ⟨materialized, consumed, point, model, fun term mentioned =>
        (kept term mentioned).trans (Subst.applyTerm_id term).symm, changed⟩
  have impossible := (Closure.readsAt_captured_iff (a := PUnit.unit) (b := PUnit.unit)
    X (.var 0 : Tm) (Subst.id rowSig) (symbol 5)).mp reading
  cases impossible

theorem chronological_observer_separates
    (materialized : (materializer (codeBook freeSchema) (source []) 0 0).Admits X ({true} : Set Bool))
    (consumed : (consumer (codeBook freeSchema)
      ((materializer (codeBook freeSchema) (source []) 0 0).result X) true 0 1).Admits X ({true} : Set Bool)) :
    (execution (codeBook freeSchema) {true} (source []) 0 0 1 true materialized consumed).word.length ≠ 1 := by
  rw [execution_length]
  decide

/-- An unrestricted ambient helper can consume an old public row. Merely
choosing fresh names for the intended protocol does not restrict this firing. -/
theorem fresh_name_is_not_a_privacy_contract :
    ∃ firing : RFiring Nat Nat E (codeBook freeSchema) publicSource,
      firing.Admits X ({true} : Set Bool) ∧ 7 ∈ publicSource.present ∧
        7 ∉ (firing.result X).present := by
  refine ⟨consumer (codeBook freeSchema) publicSource true 7 8, ?_, by decide, ?_⟩
  · exact HeldReadConsumer.admitted (codeBook freeSchema) publicSource true 7 8 {true}
      rfl (by simp) (by decide) (by decide) (Subst.id rowSig)
      (Interface.Frames.models_nil (X := X) (a := PUnit.unit) (b := PUnit.unit) _)
  · exact temporary_is_consumed (codeBook freeSchema) publicSource true 7 8 (by decide)

#print axioms free_execution
#print axioms captured_materializer_admitted
#print axioms captured_output_cannot_change
#print axioms chronological_observer_separates
#print axioms fresh_name_is_not_a_privacy_contract

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadControls
