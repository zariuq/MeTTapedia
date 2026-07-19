import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Path

/-!
# Independent replay of emitted cost-rho receipts

This module checks an externally emitted receipt by searching the declarative
occurrence-sensitive Lean frontier.  Acceptance means that the complete event
record and claimed residual are reproduced by an actual `CostPath`; the
checker does not trust an external successor state or reconstruct provenance
from equal syntax.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

/-- Replay an ordered receipt against the independent occurrence-sensitive
frontier.  Branches are retained: a receipt is accepted when at least one
actual firing path reproduces it exactly. -/
def replayReceipt : Nat → List RawTraceComponent → RawReceipt → RawCostTerm → Bool
  | _, components, [], residual => decide (tracedResidual components = residual)
  | nextId, components, event :: rest, residual =>
      (runtimeCostCandidatesFromConfig
        (components.map RawTraceComponent.term)).any fun step =>
          decide (eventFor components step nextId = event) &&
            replayReceipt (nextId + 1)
              (applyTracedStep components step nextId) rest residual

/-- Successful replay produces a genuine occurrence-sensitive `CostPath`
whose raw emission and final residual are exactly the external claims. -/
theorem replayReceipt_sound
    {nextId : Nat} {components : List RawTraceComponent}
    {receipt : RawReceipt} {residual : RawCostTerm}
    (supported : TraceComponentsWellFormed components)
    (bounded : TraceComponentsBefore nextId components)
    (accepted : replayReceipt nextId components receipt residual = true) :
    ∃ finalId finalComponents,
      ∃ path : CostPath nextId components finalId finalComponents,
        finalId = nextId + receipt.length ∧
        path.rawEmission = receipt ∧
        tracedResidual finalComponents = residual := by
  induction receipt generalizing nextId components with
  | nil =>
      simp only [replayReceipt, decide_eq_true_eq] at accepted
      exact ⟨nextId, components, .done supported bounded, by simp,
        rfl, accepted⟩
  | cons event rest ih =>
      simp only [replayReceipt] at accepted
      obtain ⟨step, enabled, stepAccepted⟩ := List.any_eq_true.mp accepted
      have acceptedParts :
          decide (eventFor components step nextId = event) = true ∧
            replayReceipt (nextId + 1)
              (applyTracedStep components step nextId) rest residual = true := by
        simpa only [Bool.and_eq_true] using stepAccepted
      have eventEq : eventFor components step nextId = event :=
        of_decide_eq_true acceptedParts.1
      have nextSupported :=
        applyTracedStep_wellFormed supported enabled nextId
      have nextBounded := applyTracedStep_before bounded step
      obtain ⟨finalId, finalComponents, tailPath, finalIdEq,
          tailEmissionEq, residualEq⟩ :=
        ih nextSupported nextBounded acceptedParts.2
      refine ⟨finalId, finalComponents,
        .fire supported bounded step enabled tailPath, ?_, ?_, residualEq⟩
      · simp only [List.length_cons]
        omega
      · simp [CostPath.rawEmission, eventEq, tailEmissionEq]

/-- The replay checker is complete for the declarative finite path relation. -/
theorem replayReceipt_complete
    {nextId finalId : Nat}
    {components finalComponents : List RawTraceComponent}
    (path : CostPath nextId components finalId finalComponents) :
    replayReceipt nextId components path.rawEmission
      (tracedResidual finalComponents) = true := by
  induction path with
  | done => simp [CostPath.rawEmission, replayReceipt]
  | fire supported bounded step enabled rest ih =>
      simp only [CostPath.rawEmission, replayReceipt]
      apply List.any_eq_true.mpr
      exact ⟨step, enabled, by simp [ih]⟩

/-- Public certificate checker for a raw initial term, emitted receipt, and
claimed final residual.  Malformed source syntax fails closed. -/
def validateReceipt (term : RawCostTerm) (receipt : RawReceipt)
    (residual : RawCostTerm) : Bool :=
  if term.wellFormed then
    replayReceipt 0 (initialTraceComponents term) receipt residual
  else false

/-- A public certificate accepted from a well-formed source has a declarative
path witness with exactly the claimed emission and residual. -/
theorem validateReceipt_sound
    {term : RawCostTerm} {receipt : RawReceipt} {residual : RawCostTerm}
    (accepted : validateReceipt term receipt residual = true) :
    ∃ finalComponents,
      ∃ path : CostPath 0 (initialTraceComponents term)
          receipt.length finalComponents,
        path.rawEmission = receipt ∧
        tracedResidual finalComponents = residual := by
  unfold validateReceipt at accepted
  split at accepted
  next supported =>
    obtain ⟨finalId, finalComponents, path, finalIdEq,
        emissionEq, residualEq⟩ :=
      replayReceipt_sound (initialTraceComponents_wellFormed supported)
        (initialTraceComponents_before term) accepted
    simp only [Nat.zero_add] at finalIdEq
    subst finalId
    exact ⟨finalComponents, path, emissionEq, residualEq⟩
  next unsupported =>
    simp at accepted

/-- Every concrete path from a supported source is accepted as an external
receipt certificate. -/
theorem validateReceipt_complete
    {term : RawCostTerm} (supported : term.wellFormed = true)
    {finalId : Nat} {finalComponents : List RawTraceComponent}
    (path : CostPath 0 (initialTraceComponents term) finalId finalComponents) :
    validateReceipt term path.rawEmission
      (tracedResidual finalComponents) = true := by
  simp [validateReceipt, supported, replayReceipt_complete path]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
