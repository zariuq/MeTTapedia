import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadDirectBridge
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadControls

/-! # Concrete mixed-store controls for the independent direct/held bridge -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadDirectControls

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig)
open ApplicationMachine (RowTerms Store X sourceBound)
open ApplicationSyntax (symbol)

def mixed (datum : Row RowTerms PUnit.unit) : Store Nat :=
  ⟨PUnit.unit, [], {0, 1, 2}, fun o => if o = 0 then datum else .shared (.var 0)⟩

def freeDatum : Closure RowTerms PUnit.unit := ⟨HeldReadControls.freeSchema, []⟩
def freeSource : Store Nat := mixed (.schematic freeDatum)
def capturedSource : Store Nat := mixed (.schematic (Closure.captured (.var 0)))

theorem free_reading (value : Tm) :
    (freeSource.label 0).ReadsAt X (b := PUnit.unit) (Subst.id rowSig) value :=
  HeldReadControls.free_reading value

theorem shared_coordinate_mentioned : freeSource.scope.Mentions (.var 0 : Tm) := by
  apply (State.scope_mentions_iff freeSource (.var 0 : Tm)).mpr
  refine Or.inr (Or.inr ⟨1, by decide, ?_⟩)
  change (.var 0 : Tm) ∈ [(.var 0 : Tm)]
  exact List.mem_singleton_self (.var 0 : Tm)

theorem direct_execution_keeps_shared_coordinate (value : Tm) :
    ∃ _admitted : (HeldReadDirect.candidate (sourceBound freeSource) freeSource 0 4).Admits X,
      ∃ point : Subst rowSig,
        X.Models (a := PUnit.unit) (b := PUnit.unit) point
          ((HeldReadDirect.candidate (sourceBound freeSource) freeSource 0 4).result X).knowledge ∧
        point.applyTerm (.var 0) = .var 0 ∧
        (((HeldReadDirect.candidate (sourceBound freeSource) freeSource 0 4).result X).label 4).ReadsAt X
          (b := PUnit.unit) point value := by
  obtain ⟨admitted, point, known, agrees, output⟩ :=
    (HeldReadDirect.reading_iff_actual_result freeSource (Subst.id rowSig)
      (Interface.Frames.models_nil (X := X) (a := PUnit.unit) (b := PUnit.unit) _)
      0 4 (by decide) (by decide) value).mp (free_reading value)
  exact ⟨admitted, point, known, agrees (.var 0) shared_coordinate_mentioned, output⟩

theorem free_direct_held_agree :
    HeldReadDirectBridge.directResults freeSource (Subst.id rowSig) 0 4 =
      HeldReadDirectBridge.heldResults freeSource (symbol 99) (Subst.id rowSig) 0 3 4 :=
  HeldReadDirectBridge.results_equal freeSource (symbol 99) (Subst.id rowSig)
    (Interface.Frames.models_nil (X := X) (a := PUnit.unit) (b := PUnit.unit) _)
    0 3 4 freeDatum rfl rfl (by decide) (by decide) (by decide) (by decide)

theorem equal_payloads_keep_distinct_occurrences :
    (HeldReadEncoding.encode freeSource (symbol 99)).present = {1, 2} ∧
      (HeldReadEncoding.encode freeSource (symbol 99)).rules = {0} := by
  decide

theorem captured_valid :
    (.var 0 : Tm) ∈ HeldReadDirectBridge.directResults capturedSource (Subst.id rowSig) 0 4 := by
  apply (HeldReadDirectBridge.direct_iff_reading capturedSource (Subst.id rowSig)
    (Interface.Frames.models_nil (X := X) (a := PUnit.unit) (b := PUnit.unit) _)
    0 4 (by decide) (by decide) (.var 0)).mpr
  exact (Closure.readsAt_captured_iff (a := PUnit.unit) (b := PUnit.unit)
    X (.var 0 : Tm) (Subst.id rowSig) (.var 0)).mpr rfl

theorem captured_rejects_change :
    symbol 7 ∉ HeldReadDirectBridge.directResults capturedSource (Subst.id rowSig) 0 4 := by
  intro member
  have reading := (HeldReadDirectBridge.direct_iff_reading capturedSource (Subst.id rowSig)
    (Interface.Frames.models_nil (X := X) (a := PUnit.unit) (b := PUnit.unit) _)
    0 4 (by decide) (by decide) (symbol 7)).mp member
  have impossible := (Closure.readsAt_captured_iff (a := PUnit.unit) (b := PUnit.unit)
    X (.var 0 : Tm) (Subst.id rowSig) (symbol 7)).mp reading
  cases impossible

theorem captured_held_rejects_change :
    symbol 7 ∉ HeldReadDirectBridge.heldResults capturedSource (symbol 99) (Subst.id rowSig) 0 3 4 := by
  rw [← HeldReadDirectBridge.results_equal capturedSource (symbol 99) (Subst.id rowSig)
    (Interface.Frames.models_nil (X := X) (a := PUnit.unit) (b := PUnit.unit) _)
    0 3 4 (Closure.captured (.var 0)) rfl rfl (by decide) (by decide) (by decide) (by decide)]
  exact captured_rejects_change

#print axioms direct_execution_keeps_shared_coordinate
#print axioms free_direct_held_agree
#print axioms equal_payloads_keep_distinct_occurrences
#print axioms captured_valid
#print axioms captured_rejects_change
#print axioms captured_held_rejects_change

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadDirectControls
