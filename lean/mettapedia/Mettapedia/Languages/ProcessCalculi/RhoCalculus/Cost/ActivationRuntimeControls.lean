import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationExecutablePath
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationSeparationControls

/-!
# Inhabited executable physical-resource controls

An authored compiler-image receiver copies a nonempty compiler-image payload.
One real purse cell containing two signing atoms funds that communication.
The existing unrestricted purse-payload execution supplies the contrasting
failure of physical conservation outside resource separation.

A receiver that sends on the name it receives meets a sender of a dequoted
name. The executable step and the funded firing of its event leave the same
purses, but not the same configuration: the step adds its contractum
normalized, the event its contractum as substituted. A meeting under no seal
fires with no purse; no funded event spends nothing.
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

/-! ## The funded event of an executable step -/

/-- A receiver that sends on the name it receives, meeting a sender of the name
`*@0`, under the seal `a`. -/
def renamingMeeting : RawCostTerm :=
  .signed (.par (.recv (.quote .nil) (.signed (.send (.bvar 0) .nil) ["a"]))
    (.send (.quote .nil) (.drop (.quote .nil)))) ["a"]

/-- One purse on the channel, holding one cell `a`. -/
def renamingPurse : RawCostTerm := .purse (.quote .nil) [["a"]]

/-- The runtime presentation of the meeting with its purse: the purse first. -/
def renamingComponents : List RawTraceComponent :=
  initialTraceComponents (.par renamingMeeting renamingPurse)

/-- The contractum of the meeting, normalized: `@*@0` becomes `@0`. -/
def renamingContractum : RawCostTerm :=
  (RawCostTerm.commSubst (.signed (.send (.bvar 0) .nil) ["a"]) (.drop (.quote .nil))).normalize

/-- The one executable step: the meeting at index 1, paid by the purse at
index 0. -/
def renamingStep : RawRuntimeStep where
  shape := .wholeRecvSend
  location := .quote .nil
  spend := ["a"]
  participantIndices := [1]
  selectedPurses := [⟨0, .quote .nil, ["a"], []⟩]
  contractum := renamingContractum
  residual := residualFor (renamingComponents.map RawTraceComponent.term) [1]
    [⟨0, .quote .nil, ["a"], []⟩] renamingContractum

/-- The meeting as a funded event, paid by the one cell of the purse. -/
def renamingEvent : CostedEvent String :=
  .wholeRecvSend (.quote .nil) (.signed (.send (.bvar 0) .nil) {"a"}) (.drop (.quote .nil)) {"a"}
    (Multiset.singleton_ne_zero _) ⟨{⟨{"a"}, .empty, Multiset.singleton_ne_zero _⟩}, by decide⟩

/-- The step embeds as that funded event. -/
def renamingEmbedding : RuntimeEventEmbedding (renamingComponents.map RawTraceComponent.term) where
  step := renamingStep
  enabled := by decide +kernel
  event := renamingEvent
  picked := [(renamingMeeting, 1), (renamingPurse, 0)]
  indices_eq := rfl
  picked_source := by decide +kernel
  consumed_eq := by decide +kernel

theorem renaming_separated :
    (decodeRawConfig (renamingComponents.map RawTraceComponent.term)).ResourceSeparated := by
  apply initialTraceComponents_resourceSeparated
  intro term member
  simp only [renamingMeeting, renamingPurse, decodeCostTerm, CostTerm.components,
    Multiset.mem_add, Multiset.mem_cons, Multiset.notMem_zero, or_false] at member
  rcases member with rfl | rfl <;> rfl

/-- **The step and the funded firing leave the same purses**: the purse,
emptied. -/
theorem renaming_purses_agree :
    CostConfig.purses (decodeRawConfig
        ((applyTracedStep renamingComponents renamingStep 0).map RawTraceComponent.term)) =
      CostConfig.purses ((costResourceSystem String).fire
        (decodeRawConfig (renamingComponents.map RawTraceComponent.term))
        (site := renamingEvent.location) ⟨renamingEvent, rfl⟩) ∧
    CostConfig.purses (decodeRawConfig
        ((applyTracedStep renamingComponents renamingStep 0).map RawTraceComponent.term)) =
      {(.quote .nil, [])} :=
  ⟨(renamingEmbedding.fire_purses (initialTraceComponents_canonical _) renaming_separated 0).2.1,
    by decide +kernel⟩

/-- **The step and the funded firing leave different configurations.** After
the step the sender's channel is `@0`, normalized; after the funded firing it is
`@*@0`, as substituted. The two contracta differ in exactly this way. -/
theorem renaming_configurations_differ :
    decodeRawConfig ((applyTracedStep renamingComponents renamingStep 0).map RawTraceComponent.term) ≠
      (costResourceSystem String).fire
        (decodeRawConfig (renamingComponents.map RawTraceComponent.term))
        (site := renamingEvent.location) ⟨renamingEvent, rfl⟩ ∧
    (decodeCostTerm renamingContractum).components =
      {.signed (.send (.quote .nil) .nil) {"a"}} ∧
    renamingEvent.contractum = {.signed (.send (.quote (.drop (.quote .nil))) .nil) {"a"}} := by
  decide +kernel

/-! ## A step with no purse -/

/-- A meeting under no seal. -/
def unsealedComponents : List RawTraceComponent :=
  initialTraceComponents (.signed (.par (.recv (.quote .nil) .nil) (.send (.quote .nil) .nil)) [])

/-- **A step with no purse.** The unsealed meeting is not well formed, yet the
configuration is canonical and separated and a step is enabled; it selects no
purse and spends nothing, and no funded event spends nothing. -/
theorem unsealed_step_unpaid :
    (decodeRawConfig (unsealedComponents.map RawTraceComponent.term)).ResourceSeparated ∧
      ¬ TraceComponentsWellFormed unsealedComponents ∧
      (∃ step ∈ runtimeCostCandidatesFromConfig (unsealedComponents.map RawTraceComponent.term),
        step.selectedPurses = [] ∧ step.spend = []) ∧
      ∀ event : CostedEvent String, event.spend ≠ decodeCostSig [] := by
  refine ⟨?_, ?_, by decide +kernel, fun event => event.spend_valid⟩
  · apply initialTraceComponents_resourceSeparated
    intro term member
    simp only [decodeCostTerm, CostTerm.components, Multiset.mem_cons, Multiset.notMem_zero,
      or_false] at member
    subst member
    rfl
  · unfold TraceComponentsWellFormed
    decide +kernel

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationRuntimeControls
