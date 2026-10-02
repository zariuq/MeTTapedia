import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationOccurrencePathAccounting

/-!
# When firing counts agree with physical and receipt counts

For admitted execution, split funding is exactly the obstruction to counting
one cell per firing. The receipt counts the same consumed signing atoms when
the initial configuration is an actual generated parser image. These laws
classify complete paths, including later firings created by substitution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

open ActivationGenerated.SerializationAdmission

theorem RawStepShape.splitIndicator_eq_zero_iff (shape : RawStepShape) :
    shape.splitIndicator = 0 ↔ shape ≠ .split := by
  cases shape <;> simp [RawStepShape.splitIndicator]

private theorem split_sum_zero_iff (steps : List RawRuntimeStep) :
    (steps.map fun step => step.shape.splitIndicator).sum = 0 ↔
      ∀ step ∈ steps, step.shape ≠ .split := by
  induction steps with
  | nil => simp
  | cons step rest ih =>
      simp only [List.map_cons, List.sum_cons, Nat.add_eq_zero_iff,
        RawStepShape.splitIndicator_eq_zero_iff, ih, List.mem_cons,
        forall_eq_or_imp]

namespace CostPath

theorem splitFiringCount_eq_zero_iff {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) :
    path.splitFiringCount = 0 ↔ ∀ step ∈ path.steps, step.shape ≠ .split :=
  split_sum_zero_iff path.steps

/-- A whole-only regime is characterized on the actual retained candidates,
rather than inferred from an endpoint or from its numerical price. -/
theorem admitted_cells_eq_depth_iff {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) {location : RawCostName}
    (images : (components.map RawTraceComponent.term).Forall (ConfigAdmitted location)) :
    path.consumedPurseCells = path.depth ↔
      ∀ step ∈ path.steps, step.shape ≠ .split := by
  rw [path.admitted_consumed_cells images, ← path.splitFiringCount_eq_zero_iff]
  omega

end CostPath

namespace ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Exact receipt multiplicity agrees with physical cell depletion for every
actual finite path from this parser image. No prices occur in the statement. -/
theorem ConfigImage.finite_path_receipt_card
    {channelSource source : Pattern} {location : CostName LiteralAuthority}
    {term : CostTerm LiteralAuthority} (channelImage : NameImage 0 channelSource location)
    (image : ConfigImage location source term) {finalId finalComponents}
    (path : CostPath 0 (initialTraceComponents (literalEncodeTerm term)) finalId finalComponents) :
    path.receipt.totalRawMeasure.card = path.depth + path.splitFiringCount := by
  rw [path.receipt_rawMeasure_eq_emitted_spend]
  obtain ⟨cells, _balance, _atomic⟩ := image.finite_path_atomic_balance channelImage path
  rw [← cells]
  exact path.admitted_consumed_cells image.initial_serialized_admission

/-- Receipt cardinality counts firings exactly when none of their retained
candidates uses split funding. Equal endpoints remain separate occurrences. -/
theorem ConfigImage.finite_path_receipt_card_eq_depth_iff
    {channelSource source : Pattern} {location : CostName LiteralAuthority}
    {term : CostTerm LiteralAuthority} (channelImage : NameImage 0 channelSource location)
    (image : ConfigImage location source term) {finalId finalComponents}
    (path : CostPath 0 (initialTraceComponents (literalEncodeTerm term)) finalId finalComponents) :
    path.receipt.totalRawMeasure.card = path.depth ↔
      ∀ step ∈ path.steps, step.shape ≠ .split := by
  rw [image.finite_path_receipt_card channelImage path,
    ← path.splitFiringCount_eq_zero_iff]
  omega

end ActivationGenerated

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
