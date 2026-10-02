import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationRuntime
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Conservation

/-!
# Physical resource conservation through executable Cost paths

The source admission is invariant under the actual occurrence-bearing runtime.
Physical cells and stored signing atoms therefore account for concrete paths,
including every intermediate normalization. The receipt remains a readout of
the same exact spend; its numerical interpretation never supplies authority.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe u

/-- The runtime's initial normalization preserves an admitted decoded source. -/
theorem initialTraceComponents_resourceSeparated (term : RawCostTerm)
    (separated : (decodeCostTerm term).components.ResourceSeparated) :
    (decodeRawConfig ((initialTraceComponents term).map RawTraceComponent.term)).ResourceSeparated := by
  simpa [initialTraceComponents, Function.comp_def] using
    term.normalizeConfig_resourceSeparated separated

/-- Initial producer annotation changes no physical inventory observation. -/
theorem initialTraceComponents_physical_measure
    {Measure : Type u} [AddCommMonoid Measure] (weight : CostStack String → Measure)
    (term : RawCostTerm) :
    (decodeRawConfig ((initialTraceComponents term).map RawTraceComponent.term)).physicalPurseMeasure weight = (decodeCostTerm term).components.physicalPurseMeasure weight := by
  simpa [initialTraceComponents, Function.comp_def] using
    term.normalizeConfig_physicalPurseMeasure weight

namespace CostPath

/-- Resource separation holds at the end of every actual executable path from
an admitted canonical source. -/
theorem executable_preserves_resourceSeparated :
    ∀ {nextId components finalId finalComponents}
      (_path : CostPath nextId components finalId finalComponents),
      TraceComponentsCanonical components →
      (decodeRawConfig (components.map RawTraceComponent.term)).ResourceSeparated →
      (decodeRawConfig (finalComponents.map RawTraceComponent.term)).ResourceSeparated := by
  intro nextId components finalId finalComponents path
  induction path with
  | done supported bounded =>
      intro _canonical separated
      exact separated
  | @fire nextId components finalId finalComponents supported bounded step enabled rest induction =>
      intro canonical separated
      exact induction (applyTracedStep_canonical canonical enabled nextId)
        (applyTracedStep_resourceSeparated canonical separated enabled nextId)

/-- The existing path's selected-head count is exactly the depletion of cells
physically present in its normalized configurations. -/
theorem executable_physical_cells_balance :
    ∀ {nextId components finalId finalComponents}
      (path : CostPath nextId components finalId finalComponents),
      TraceComponentsCanonical components →
      (decodeRawConfig (components.map RawTraceComponent.term)).ResourceSeparated →
      (decodeRawConfig (components.map RawTraceComponent.term)).physicalPurseCells =
        (decodeRawConfig (finalComponents.map RawTraceComponent.term)).physicalPurseCells +
          path.consumedPurseCells := by
  intro nextId components finalId finalComponents path
  induction path with
  | done supported bounded =>
      intro _canonical _separated
      simp [consumedPurseCells, steps]
  | @fire nextId components finalId finalComponents supported bounded step enabled rest induction =>
      intro canonical separated
      have first := applyTracedStep_physical_cells_balance canonical separated enabled nextId
      have tail := induction (applyTracedStep_canonical canonical enabled nextId)
        (applyTracedStep_resourceSeparated canonical separated enabled nextId)
      simp only [consumedPurseCells, steps, List.map_cons, List.sum_cons]
      change _ = _ + (step.selectedPurses.length + rest.consumedPurseCells)
      omega

/-- Actual runtime paths preserve purse occurrences, including exhausted
purses. Neither signatures nor code copies create new purse occurrences. -/
theorem executable_physical_purse_occurrences :
    ∀ {nextId components finalId finalComponents}
      (_path : CostPath nextId components finalId finalComponents),
      TraceComponentsCanonical components →
      (decodeRawConfig (components.map RawTraceComponent.term)).ResourceSeparated →
      (decodeRawConfig (components.map RawTraceComponent.term)).physicalPurseOccurrences =
        (decodeRawConfig (finalComponents.map RawTraceComponent.term)).physicalPurseOccurrences := by
  intro nextId components finalId finalComponents path
  induction path with
  | done supported bounded =>
      intro _canonical _separated
      rfl
  | @fire nextId components finalId finalComponents supported bounded step enabled rest induction =>
      intro canonical separated
      exact (applyTracedStep_physical_purse_occurrences canonical separated enabled nextId).trans
        (induction (applyTracedStep_canonical canonical enabled nextId)
          (applyTracedStep_resourceSeparated canonical separated enabled nextId))

/-- Physical signing atoms deplete by the path's existing exact spend list. -/
theorem executable_stored_signatures_balance :
    ∀ {nextId components finalId finalComponents}
      (path : CostPath nextId components finalId finalComponents),
      TraceComponentsCanonical components →
      (decodeRawConfig (components.map RawTraceComponent.term)).ResourceSeparated →
      (decodeRawConfig (components.map RawTraceComponent.term)).storedSignatures =
        (decodeRawConfig (finalComponents.map RawTraceComponent.term)).storedSignatures +
          path.spends.sum := by
  intro nextId components finalId finalComponents path
  induction path with
  | done supported bounded =>
      intro _canonical _separated
      simp [spends, steps]
  | @fire nextId components finalId finalComponents supported bounded step enabled rest induction =>
      intro canonical separated
      have first := applyTracedStep_stored_signatures_balance canonical separated enabled nextId
      have tail := induction (applyTracedStep_canonical canonical enabled nextId)
        (applyTracedStep_resourceSeparated canonical separated enabled nextId)
      simp only [spends, steps, List.map_cons, List.sum_cons]
      rw [first, tail]
      change _ + _ + step.spend.toMultiset = _ + (step.spend.toMultiset + _)
      ac_rfl

/-- The number of executable firings plus remaining cells cannot exceed the
cells physically present initially; multi-purse funding may consume more. -/
theorem executable_depth_add_remaining_cells_le
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents)
    (canonical : TraceComponentsCanonical components)
    (separated : (decodeRawConfig (components.map RawTraceComponent.term)).ResourceSeparated) :
    path.depth + (decodeRawConfig (finalComponents.map RawTraceComponent.term)).physicalPurseCells ≤
      (decodeRawConfig (components.map RawTraceComponent.term)).physicalPurseCells := by
  have balance := path.executable_physical_cells_balance canonical separated
  have bound := path.depth_le_consumedPurseCells
  omega

/-- An admitted canonical source with no cells supports no nonempty execution. -/
theorem executable_depth_eq_zero_of_no_cells
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents)
    (canonical : TraceComponentsCanonical components)
    (separated : (decodeRawConfig (components.map RawTraceComponent.term)).ResourceSeparated)
    (noCells : (decodeRawConfig (components.map RawTraceComponent.term)).physicalPurseCells = 0) :
    path.depth = 0 := by
  have bound := path.executable_depth_add_remaining_cells_le canonical separated
  omega

/-- For executions starting at event zero, actual physical depletion equals
the total signing measure of the already constructed causal receipt. -/
theorem executable_stored_signatures_receipt_balance
    {components finalId finalComponents}
    (path : CostPath 0 components finalId finalComponents)
    (canonical : TraceComponentsCanonical components)
    (separated : (decodeRawConfig (components.map RawTraceComponent.term)).ResourceSeparated) :
    (decodeRawConfig (components.map RawTraceComponent.term)).storedSignatures =
      (decodeRawConfig (finalComponents.map RawTraceComponent.term)).storedSignatures +
        path.receipt.totalRawMeasure := by
  rw [path.receipt_rawMeasure_eq_emitted_spend]
  exact path.executable_stored_signatures_balance canonical separated

/-- Every additive interpretation preserves the physical signing balance;
the interpretation is an observer applied after exact authorization. -/
theorem executable_additive_inventory_balance
    {Measure : Type u} [AddCommMonoid Measure] (weight : String → Measure)
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents)
    (canonical : TraceComponentsCanonical components)
    (separated : (decodeRawConfig (components.map RawTraceComponent.term)).ResourceSeparated) :
    CostSig.additiveFold weight
        (decodeRawConfig (components.map RawTraceComponent.term)).storedSignatures =
      CostSig.additiveFold weight
          (decodeRawConfig (finalComponents.map RawTraceComponent.term)).storedSignatures +
        CostSig.additiveFold weight path.spends.sum := by
  rw [path.executable_stored_signatures_balance canonical separated,
    CostSig.additiveFold_add]

end CostPath
end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
