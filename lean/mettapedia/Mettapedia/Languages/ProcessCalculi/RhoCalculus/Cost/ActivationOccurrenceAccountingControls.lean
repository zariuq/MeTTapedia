import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationOccurrencePathAccounting
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationOccurrencePathControls

/-!
# Whole, split and non-admitted occurrence accounting controls

The positive witnesses use actual generated parser images at a nonempty
quoted channel and the existing one-firing runtime path. A compound whole
signature in the broader raw runtime supplies the negative control: it can
consume two cells without being a split-shaped firing. Thus the generated
admission premise, not firing shape alone, licenses the exact cell formula.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationOccurrenceAccountingControls

open ActivationGenerated ActivationLocatedControls ActivationOccurrencePathControls

theorem whole_counts :
    ∃ step, ∃ path : CostPath 0 (initialTraceComponents (literalEncodeTerm wholeTerm)) 1
        (applyTracedStep (initialTraceComponents (literalEncodeTerm wholeTerm)) step 0),
      path.depth = 1 ∧ path.consumedPurseCells = 1 ∧ path.splitFiringCount = 0 ∧
      path.receipt.totalRawMeasure.card = 1 := by
  obtain ⟨step, enabled, _location, spent, _oldPath⟩ := actual_closed_location_entry
  let path := UnitPolicyControls.fireOnce (literalEncodeTerm wholeTerm)
    (whole_image.literal_wellFormed channel_image.literal_wellFormed) step enabled
  have cells : step.selectedPurses.length = 1 := by
    rw [whole_image.canonical_candidate_cells_eq_atoms channel_image enabled,
      spent, Multiset.card_singleton]
  have consumed : path.consumedPurseCells = 1 := by
    change step.selectedPurses.length + 0 = 1
    rw [cells, Nat.add_zero]
  have count := path.admitted_consumed_cells whole_image.initial_serialized_admission
  have depth : path.depth = 1 := rfl
  have noSplit : path.splitFiringCount = 0 := by omega
  have atomic := (whole_image.finite_path_atomic_balance channel_image path).1
  refine ⟨step, path, depth, consumed, noSplit, ?_⟩
  rw [path.receipt_rawMeasure_eq_emitted_spend, ← atomic, consumed]

theorem split_counts :
    ∃ step, ∃ path : CostPath 0
        (initialTraceComponents (literalEncodeTerm ActivationSplitControls.source)) 1
        (applyTracedStep (initialTraceComponents (literalEncodeTerm ActivationSplitControls.source)) step 0),
      path.depth = 1 ∧ path.consumedPurseCells = 2 ∧ path.splitFiringCount = 1 ∧
      path.receipt.totalRawMeasure.card = 2 ∧
      path.consumedPurseCells ≠ path.depth := by
  obtain ⟨step, enabled, _spent, cells, _oldPath, _balance⟩ :=
    ActivationSplitControls.actual_two_generated_purse_execution
  let path := UnitPolicyControls.fireOnce (literalEncodeTerm ActivationSplitControls.source)
    (split_image.literal_wellFormed channel_image.literal_wellFormed) step enabled
  have consumed : path.consumedPurseCells = 2 := by
    change step.selectedPurses.length + 0 = 2
    rw [cells, Nat.add_zero]
  have count := path.admitted_consumed_cells split_image.initial_serialized_admission
  have depth : path.depth = 1 := rfl
  have oneSplit : path.splitFiringCount = 1 := by omega
  have atomic := (split_image.finite_path_atomic_balance channel_image path).1
  refine ⟨step, path, depth, consumed, oneSplit, ?_, by omega⟩
  rw [path.receipt_rawMeasure_eq_emitted_spend, ← atomic, consumed]

/-- The raw whole rule may cover a compound signature with two separate
heads. It is a real enabled path, but is outside generated signature admission. -/
theorem raw_compound_whole_breaks_shape_only_accounting :
    UnitPolicyControls.splitHeadsPath.depth = 1 ∧
      UnitPolicyControls.splitHeadsPath.splitFiringCount = 0 ∧
      UnitPolicyControls.splitHeadsPath.consumedPurseCells = 2 ∧
      UnitPolicyControls.splitHeadsPath.consumedPurseCells ≠
        UnitPolicyControls.splitHeadsPath.depth + UnitPolicyControls.splitHeadsPath.splitFiringCount := by
  decide +kernel

/-- The general theorem itself detects the missing source admission, without
postulating a parser failure for this wider runtime configuration. -/
theorem raw_compound_whole_not_admitted (location : RawCostName) :
    ¬ (((initialTraceComponents UnitPolicyControls.splitHeads).map RawTraceComponent.term).Forall
      (SerializationAdmission.ConfigAdmitted location)) := by
  intro admitted
  have count := UnitPolicyControls.splitHeadsPath.admitted_consumed_cells admitted
  exact raw_compound_whole_breaks_shape_only_accounting.2.2.2 count

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationOccurrenceAccountingControls
