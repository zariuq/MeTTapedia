import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Activation
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Path

/-!
# Actual activation, copying and discard controls

These examples use nonempty communicated code containing an inner COMM.
The outer COMM substitutes that code into a Drop, into two Drops, or into
no Drop.  The occurrence-bearing runtime paths then measure only firings
that actually occur.  A separate accepted-syntax counterexample transmits
a purse instead of code, exposing why the code-only admission is necessary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationControls

/-- Follow a bounded number of actual enabled occurrences, retaining the
runtime's participant and funding evidence at every firing. -/
def firstEnabledPath (fuel nextId : Nat) (components : List RawTraceComponent)
    (supported : TraceComponentsWellFormed components)
    (bounded : TraceComponentsBefore nextId components) :
    Σ finalId, Σ finalComponents, CostPath nextId components finalId finalComponents :=
  match fuel with
  | 0 => ⟨nextId, components, .done supported bounded⟩
  | fuel + 1 =>
      match equality : runtimeCostCandidatesFromConfig
          (components.map RawTraceComponent.term) with
      | [] => ⟨nextId, components, .done supported bounded⟩
      | step :: _ =>
          let enabled : step ∈ runtimeCostCandidatesFromConfig
              (components.map RawTraceComponent.term) := by
            rw [equality]
            exact List.mem_cons_self
          let rest := firstEnabledPath fuel (nextId + 1)
            (applyTracedStep components step nextId)
            (applyTracedStep_wellFormed supported enabled nextId)
            (applyTracedStep_before bounded step)
          ⟨rest.1, rest.2.1, .fire supported bounded step enabled rest.2.2⟩

/-- Start a certified occurrence path without exposing concrete normalization
during dependent type inference. -/
def initialRun (fuel : Nat) (term : RawCostTerm) (supported : term.wellFormed = true) :
    Σ finalId, Σ finalComponents,
      CostPath 0 (initialTraceComponents term) finalId finalComponents :=
  firstEnabledPath fuel 0 (initialTraceComponents term)
    (initialTraceComponents_wellFormed supported) (initialTraceComponents_before term)

def outerChannel : RawCostName := .signature ["o"]

def innerChannel : RawCostName := .signature ["i"]

def innerCode : RawCostTerm :=
  .signed (.par (.recv innerChannel .nil) (.send innerChannel .nil)) ["b"]

def outerCode (body payload : RawCostTerm) : RawCostTerm :=
  .signed (.par (.recv outerChannel body) (.send outerChannel payload)) ["a"]

def openBody : RawCostTerm := .drop (.bvar 0)

def duplicateBody : RawCostTerm := .par openBody openBody

def outerFunding : RawCostTerm := .purse outerChannel [["a"]]

def innerFunding (cells : Nat) : RawCostTerm :=
  .purse innerChannel (List.replicate cells ["b"])

def activationUnfunded : RawCostTerm :=
  .par (outerCode openBody innerCode) outerFunding

def activationFunded : RawCostTerm :=
  .par activationUnfunded (innerFunding 1)

def duplicationFunded (cells : Nat) : RawCostTerm :=
  .par (.par (outerCode duplicateBody innerCode) outerFunding) (innerFunding cells)

def discardFunded : RawCostTerm :=
  .par (.par (outerCode .nil innerCode) outerFunding) (innerFunding 1)

def transmittedPurse : RawCostTerm := .purse innerChannel [["b"]]

def authorityDuplication : RawCostTerm :=
  .par (outerCode duplicateBody transmittedPurse) outerFunding

private theorem activation_terms_wellFormed :
    activationUnfunded.wellFormed = true ∧ activationFunded.wellFormed = true ∧
      (duplicationFunded 1).wellFormed = true ∧
      (duplicationFunded 2).wellFormed = true ∧ discardFunded.wellFormed = true ∧
      authorityDuplication.wellFormed = true := by
  simp [activationUnfunded, activationFunded, duplicationFunded, discardFunded,
    authorityDuplication, outerCode, innerCode, openBody, duplicateBody,
    outerFunding, innerFunding, transmittedPurse, outerChannel, innerChannel,
    RawCostTerm.wellFormed, RawCostProc.wellFormed, RawCostName.wellFormed,
    RawCostSig.valid]

def activationUnfundedRun :=
  initialRun 3 activationUnfunded activation_terms_wellFormed.1

def activationFundedRun :=
  initialRun 3 activationFunded activation_terms_wellFormed.2.1

def duplicationOneCellRun :=
  initialRun 4 (duplicationFunded 1) activation_terms_wellFormed.2.2.1

def duplicationTwoCellRun :=
  initialRun 4 (duplicationFunded 2) activation_terms_wellFormed.2.2.2.1

def discardRun :=
  initialRun 3 discardFunded activation_terms_wellFormed.2.2.2.2.1

def authorityDuplicationRun :=
  initialRun 2 authorityDuplication activation_terms_wellFormed.2.2.2.2.2

/-- Outer substitution exposes a sealed COMM, but supplies no inner head. -/
theorem activation_without_inner_funding :
    activationUnfunded.supported = true ∧
      activationUnfundedRun.2.2.depth = 1 ∧
      activationUnfundedRun.2.2.rawEmission.map RawEmittedEvent.rawSpend = [["a"]] ∧
      innerCode.normalize ∈ activationUnfundedRun.2.1.map RawTraceComponent.term ∧
      runtimeCostCandidatesFromConfig
        (activationUnfundedRun.2.1.map RawTraceComponent.term) = [] := by
  decide +kernel

/-- The same newly exposed COMM fires when its own located head is supplied. -/
theorem activation_with_inner_funding :
    activationFunded.supported = true ∧
      activationFundedRun.2.2.depth = 2 ∧
      activationFundedRun.2.2.consumedPurseCells = 2 ∧
      activationFundedRun.2.2.rawEmission.map RawEmittedEvent.rawSpend =
        [["a"], ["b"]] := by
  decide +kernel

/-- Copying sealed code twice does not replenish its one external fuel cell. -/
theorem duplication_one_cell_leaves_blocked_copy :
    (duplicationFunded 1).supported = true ∧
      duplicationOneCellRun.2.2.depth = 2 ∧
      duplicationOneCellRun.2.2.consumedPurseCells = 2 ∧
      innerCode.normalize ∈ duplicationOneCellRun.2.1.map RawTraceComponent.term ∧
      runtimeCostCandidatesFromConfig
        (duplicationOneCellRun.2.1.map RawTraceComponent.term) = [] := by
  decide +kernel

/-- Two copies keep the same seal and consume two separate inner cells. -/
theorem duplication_two_cells_fires_both_copies :
    (duplicationFunded 2).supported = true ∧
      duplicationTwoCellRun.2.2.depth = 3 ∧
      duplicationTwoCellRun.2.2.consumedPurseCells = 3 ∧
      duplicationTwoCellRun.2.2.rawEmission.map RawEmittedEvent.rawSpend =
        [["a"], ["b"], ["b"]] := by
  decide +kernel

/-- Discarding a nonempty communicated continuation performs no inner firing
and retains the exact still-funded inner purse. -/
theorem discarded_continuation_does_not_charge :
    discardFunded.supported = true ∧
      discardRun.2.2.depth = 1 ∧
      discardRun.2.2.consumedPurseCells = 1 ∧
      discardRun.2.2.rawEmission.map RawEmittedEvent.rawSpend = [["a"]] ∧
      (innerFunding 1).normalize ∈ discardRun.2.1.map RawTraceComponent.term ∧
      innerCode.normalize ∉ discardRun.2.1.map RawTraceComponent.term ∧
      runtimeCostCandidatesFromConfig
        (discardRun.2.1.map RawTraceComponent.term) = [] := by
  decide +kernel

/-- The unrestricted accepted runtime permits authority-bearing payloads.
One transmitted purse becomes two active matching purses after substitution. -/
theorem accepted_authority_payload_is_duplicated :
    authorityDuplication.supported = true ∧
      authorityDuplicationRun.2.2.depth = 1 ∧
      authorityDuplicationRun.2.2.rawEmission.map RawEmittedEvent.rawSpend = [["a"]] ∧
      (authorityDuplicationRun.2.1.map RawTraceComponent.term).count
        transmittedPurse.normalize = 2 := by
  decide +kernel

/-- The same authority duplication is a step of the declarative Cost relation,
not merely an artifact of executable enumeration. -/
theorem declarative_authority_payload_is_duplicated :
    let outer : CostName String := .signature {"o"}
    let inner : CostName String := .signature {"i"}
    let purse : CostTerm String := .purse inner (.cons {"b"} .empty)
    let body : CostTerm String := .par (.drop (.bvar 0)) (.drop (.bvar 0))
    CostStep
      ({CostTerm.signed (.par (.recv outer body) (.send outer purse)) {"a"}} +
        {CostTerm.purse outer (.cons {"a"} .empty)})
      outer {"a"}
      ({purse} + {purse} + {CostTerm.purse outer .empty}) := by
  dsimp
  simpa [CostTerm.commSubst, CostTerm.substitute, CostTerm.components] using
    CostStep.wholeRecvSend_single_head (0 : CostConfig String)
      (.signature {"o"})
      (.par (.drop (.bvar 0)) (.drop (.bvar 0)))
      (.purse (.signature {"i"}) (.cons {"b"} .empty))
      {"a"} (by simp [CostSig.RuntimeValid]) .empty

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationControls
