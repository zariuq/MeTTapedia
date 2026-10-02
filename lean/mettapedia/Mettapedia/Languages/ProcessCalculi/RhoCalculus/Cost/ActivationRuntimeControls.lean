import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationExecutablePath
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationSeparationControls

/-!
# Inhabited executable physical-resource controls

An authored compiler-image receiver copies a nonempty compiler-image payload.
One real purse cell containing two signing atoms funds that communication.
The existing unrestricted purse-payload execution supplies the contrasting
failure of physical conservation outside resource separation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationRuntimeControls

open ActivationSeparationControls

/-- The actual raw runtime representation of the compiler-image source, with
the external funding purse kept outside communicated code. -/
def compiledSource : RawCostTerm :=
  .par (.signed (.recv (.quote .nil)
    (.par (.drop (.bvar 0)) (.par (.drop (.bvar 0)) .nil))) ["a"])
    (.par (.signed (.send (.quote .nil)
      (.signed (.send (.quote .nil) .nil) ["a"])) ["a"])
      (.purse (.quote .nil) [["a", "a"]]))

theorem compiled_source_decodes : (decodeCostTerm compiledSource).components = source := by
  simp [compiledSource, source, sender, channel,
    ActivationCodeImage.wrappedCopyReceiver, ActivationCodeImage.wrappedNonemptyPayload,
    decodeCostTerm, decodeCostProc, decodeCostName, decodeCostStack, decodeCostSig,
    CostTerm.components, Multiset.cons_swap]
  rfl

theorem compiled_source_wellFormed : compiledSource.wellFormed = true := by
  decide +kernel

def compiledRun := ActivationControls.initialRun 3 compiledSource compiled_source_wellFormed

theorem compiled_runtime_source_separated :
    (decodeRawConfig ((initialTraceComponents compiledSource).map RawTraceComponent.term)).ResourceSeparated := by
  apply initialTraceComponents_resourceSeparated
  rw [compiled_source_decodes]
  exact compiler_funded_source_separated

/-- A nonempty actual communication uses one cell containing two signing
atoms, copies the authored nonempty payload, and exhausts no unrelated code. -/
theorem compiled_runtime_counts :
    compiledRun.2.2.depth = 1 ∧ compiledRun.2.2.consumedPurseCells = 1 ∧
      compiledRun.2.2.rawEmission.map RawEmittedEvent.rawSpend = [["a", "a"]] ∧
      (compiledRun.2.1.map RawTraceComponent.term).count
        (.signed (.send (.quote .nil) .nil) ["a"]) = 2 ∧
      (decodeRawConfig ((initialTraceComponents compiledSource).map RawTraceComponent.term)).physicalPurseCells = 1 ∧
      (decodeRawConfig ((initialTraceComponents compiledSource).map RawTraceComponent.term)).storedSignatures.card = 2 ∧
      (decodeRawConfig (compiledRun.2.1.map RawTraceComponent.term)).physicalPurseCells = 0 ∧
      (decodeRawConfig (compiledRun.2.1.map RawTraceComponent.term)).storedSignatures = 0 ∧
      (decodeRawConfig (compiledRun.2.1.map RawTraceComponent.term)).physicalPurseOccurrences = 1 ∧
      runtimeCostCandidatesFromConfig (compiledRun.2.1.map RawTraceComponent.term) = [] := by
  decide +kernel

/-- The compiler-image execution inhabits the general physical cell theorem;
the result follows from its domain admission, rather than a separate counter. -/
theorem compiled_runtime_cell_balance :
    (decodeRawConfig ((initialTraceComponents compiledSource).map RawTraceComponent.term)).physicalPurseCells =
    (decodeRawConfig (compiledRun.2.1.map RawTraceComponent.term)).physicalPurseCells +
      compiledRun.2.2.consumedPurseCells :=
  compiledRun.2.2.executable_physical_cells_balance
    (initialTraceComponents_canonical compiledSource) compiled_runtime_source_separated

/-- The same inhabited execution connects actual stored atoms to its causal
receipt, without using that receipt to enable the firing. -/
theorem compiled_runtime_receipt_balance :
    (decodeRawConfig ((initialTraceComponents compiledSource).map RawTraceComponent.term)).storedSignatures =
    (decodeRawConfig (compiledRun.2.1.map RawTraceComponent.term)).storedSignatures +
      compiledRun.2.2.receipt.totalRawMeasure :=
  compiledRun.2.2.executable_stored_signatures_receipt_balance
    (initialTraceComponents_canonical compiledSource) compiled_runtime_source_separated

/-- The actual accepted purse-payload path creates cells and signing atoms in
newly active purses. Runtime support alone does not imply physical balance. -/
theorem authority_payload_breaks_runtime_inventory :
    (decodeRawConfig ((initialTraceComponents ActivationControls.authorityDuplication).map RawTraceComponent.term)).physicalPurseCells ≠
      (decodeRawConfig (ActivationControls.authorityDuplicationRun.2.1.map RawTraceComponent.term)).physicalPurseCells +
      ActivationControls.authorityDuplicationRun.2.2.consumedPurseCells ∧
    (decodeRawConfig ((initialTraceComponents ActivationControls.authorityDuplication).map RawTraceComponent.term)).storedSignatures ≠
      (decodeRawConfig (ActivationControls.authorityDuplicationRun.2.1.map RawTraceComponent.term)).storedSignatures +
      ActivationControls.authorityDuplicationRun.2.2.spends.sum := by
  decide +kernel

/-- The physical counterexample is excluded by the named source admission;
the unrestricted original runtime relation is left intact. -/
theorem authority_payload_source_not_separated :
    ¬ (decodeRawConfig ((initialTraceComponents ActivationControls.authorityDuplication).map RawTraceComponent.term)).ResourceSeparated := by
  intro separated
  exact authority_payload_breaks_runtime_inventory.1
    (ActivationControls.authorityDuplicationRun.2.2.executable_physical_cells_balance
      (initialTraceComponents_canonical ActivationControls.authorityDuplication) separated)

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationRuntimeControls
