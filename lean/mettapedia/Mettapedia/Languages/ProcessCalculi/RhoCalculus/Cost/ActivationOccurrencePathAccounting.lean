import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationOccurrencePathReadout
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationSplitOccurrenceReadout
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ExecutableBudgetAcceptance

/-!
# Exact occurrence accounting for admitted finite execution

The actual source parser admits one signing atom in each stored purse head.
Whole firings consume one such cell; split firings consume two. Consequently
consumed cells equal firing count plus split-firing count throughout an
admitted path. This uses the selected physical occurrence cover at every
source, including sources produced by earlier substitution.

The chronological entry readout agrees with the existing spends and receipt.
Pricing remains an observation applied after exact authorization, with a
nonnegativity premise where prefix acceptance requires it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

open ActivationGenerated ActivationGenerated.SerializationAdmission

universe u

/-- A numerical observation of the existing firing shape. -/
def RawStepShape.splitIndicator : RawStepShape → Nat
  | .wholeRecvSend => 0
  | .wholeSendRecv => 0
  | .split => 1

theorem RawWholeOccurrenceCover.splitIndicator_zero {config : RawCostConfig}
    (cover : RawWholeOccurrenceCover config) : cover.runtimeStep.shape.splitIndicator = 0 := by
  unfold RawWholeOccurrenceCover.runtimeStep
  split <;> rfl

/-- This law requires actual parser admission of both code and purse heads.
A generic runtime whole signature may contain more than one signing atom. -/
theorem runtime_candidate_admitted_selected_cells {location : RawCostName}
    {config : RawCostConfig} (images : config.Forall (ConfigAdmitted location))
    {step : RawRuntimeStep} (enabled : step ∈ runtimeCostCandidatesFromConfig config) :
    step.selectedPurses.length = 1 + step.shape.splitIndicator := by
  rcases runtime_candidate_exact_occurrence_cover enabled with ⟨cover, same⟩ | ⟨cover, same⟩
  · obtain ⟨purse, singleton, _location, _head, _tail⟩ := cover.admitted_selected_singleton images
    rw [← same, cover.splitIndicator_zero]
    change cover.selected.length = 1 + 0
    rw [singleton]
    rfl
  · rw [← same]
    exact cover.admitted_selected_length_two images

namespace CostPath

/-- Count split occurrences without deduplicating equal participants or keys. -/
def splitFiringCount {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) : Nat :=
  (path.steps.map fun step => step.shape.splitIndicator).sum

/-- Chronological entries retain the actual candidate spends, in order. -/
theorem firingEntries_spends {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) :
    path.firingEntries.map (fun entry => entry.2.2.spend.toMultiset) = path.spends := by
  rw [spends, ← path.firingEntries_steps]
  simp only [List.map_map, Function.comp_def]

theorem firingEntries_consumed_cells {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) :
    (path.firingEntries.map fun entry => entry.2.2.selectedPurses.length).sum =
      path.consumedPurseCells := by
  rw [consumedPurseCells, ← path.firingEntries_steps]
  simp only [List.map_map, Function.comp_def]

theorem firingEntries_split_count {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) :
    (path.firingEntries.map fun entry => entry.2.2.shape.splitIndicator).sum =
      path.splitFiringCount := by
  rw [splitFiringCount, ← path.firingEntries_steps]
  simp only [List.map_map, Function.comp_def]

/-- Admission is preserved at each actual successor, so this is a law about
the full execution rather than only the initial catalogue. -/
theorem admitted_consumed_cells {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) {location : RawCostName}
    (images : (components.map RawTraceComponent.term).Forall (ConfigAdmitted location)) :
    path.consumedPurseCells = path.depth + path.splitFiringCount := by
  induction path with
  | done supported bounded => rfl
  | @fire nextId components finalId finalComponents supported bounded step enabled rest ih =>
      have head := runtime_candidate_admitted_selected_cells images enabled
      have tail := ih (applyTracedStep_admitted images enabled nextId)
      change step.selectedPurses.length + rest.consumedPurseCells =
        (rest.depth + 1) + (step.shape.splitIndicator + rest.splitFiringCount)
      rw [head, tail]
      omega

/-- Equal endpoint firings remain separate charges in the same causal receipt. -/
theorem receipt_measure_eq_firingEntries {components finalId finalComponents}
    (path : CostPath 0 components finalId finalComponents) :
    path.receipt.totalRawMeasure =
      (path.firingEntries.map fun entry => entry.2.2.spend.toMultiset).sum := by
  rw [path.firingEntries_spends, path.receipt_rawMeasure_eq_emitted_spend]

/-- The account is the chronological price of these same source-bearing
entries; no lookup keyed only by endpoint replaces the occurrence sequence. -/
theorem additiveAccount_eq_firingEntries {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents)
    {Measure : Type u} [AddCommMonoid Measure] (weight : String → Measure) :
    path.additiveAccount weight =
      path.firingEntries.map (fun entry => CostSig.additiveFold weight entry.2.2.spend.toMultiset) := by
  rw [additiveAccount, ← path.firingEntries_spends]
  simp only [List.map_map, Function.comp_def]

end CostPath

namespace ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The final physical inventory, whole charges and split charges account
for every initial purse cell of an actual generated parser image. -/
theorem ConfigImage.finite_path_occurrence_cell_balance
    {channelSource source : Pattern} {location : CostName LiteralAuthority}
    {term : CostTerm LiteralAuthority} (channelImage : NameImage 0 channelSource location)
    (image : ConfigImage location source term) {finalId finalComponents}
    (path : CostPath 0 (initialTraceComponents (literalEncodeTerm term)) finalId finalComponents) :
    path.consumedPurseCells = path.depth + path.splitFiringCount ∧
      (decodeRawConfig ((initialTraceComponents (literalEncodeTerm term)).map
          RawTraceComponent.term)).physicalPurseCells =
        (decodeRawConfig (finalComponents.map RawTraceComponent.term)).physicalPurseCells +
          path.depth + path.splitFiringCount := by
  have count := path.admitted_consumed_cells image.initial_serialized_admission
  obtain ⟨atomic, balance, _finalAtomic⟩ := image.finite_path_atomic_balance channelImage path
  exact ⟨count, by rw [← atomic, count] at balance; simpa only [Nat.add_assoc] using balance⟩

/-- All-prefix budget acceptance prices the exact same retained entries.
The price hypothesis is independent of the parser's literal funding keys. -/
theorem ConfigImage.finite_path_occurrence_prefixAccepted
    {channelSource source : Pattern} {location : CostName LiteralAuthority}
    {term : CostTerm LiteralAuthority} (channelImage : NameImage 0 channelSource location)
    (image : ConfigImage location source term) {finalId finalComponents}
    (path : CostPath 0 (initialTraceComponents (literalEncodeTerm term)) finalId finalComponents)
    {Measure : Type u} [AddCommMonoid Measure] [Preorder Measure]
    [AddLeftMono Measure] [AddRightMono Measure]
    (weight : String → Measure) (nonnegative : ∀ atom, 0 ≤ weight atom) :
    CostPath.OrderedAccount.PrefixAccepted
      (path.firingEntries.map fun entry => CostSig.additiveFold weight entry.2.2.spend.toMultiset)
      (CostSig.additiveFold weight
        (decodeRawConfig ((initialTraceComponents (literalEncodeTerm term)).map
          RawTraceComponent.term)).storedSignatures) := by
  rw [← path.additiveAccount_eq_firingEntries weight]
  exact image.finite_path_prefixAccepted channelImage path weight nonnegative

end ActivationGenerated

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
