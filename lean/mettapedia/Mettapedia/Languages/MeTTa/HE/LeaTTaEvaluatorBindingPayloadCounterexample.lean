import Mettapedia.Languages.MeTTa.HE.LeaTTaEvaluatorConfigurationConformance

/-!
# Evaluator binding-payload carrier counterexample

The general evaluator can expose a collapsed binding set as an abstract
service payload and the runtime's opaque `Ground.bindings` value.  These atoms
are related by the service-aware evaluator boundary, but they cannot be
related by the structural type-presentation binding carrier.  Consequently
that type-specific carrier is not a valid global invariant for full evaluator
conformance.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaEvaluatorBindingPayloadCounterexample

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open LeaTTaBridge
open LeaTTaMinimalInstructionConformance
open LeaTTaTypePresentationFoldConformance
open Spec.Eval.Minimal

/-- Native binding theory containing one abstract collapsed-binding payload. -/
def payloadSpecBindings (services : Services) : Bindings :=
  ⟨[("x", .grounded (services.bindingPayload Bindings.empty))], []⟩

/-- Runtime binding theory containing the corresponding opaque carrier. -/
def payloadRuntimeBindings : Metta.Bindings :=
  [.val "x" (.gnd (.bindings []))]

/-- Positive boundary: the payload values themselves are related exactly by
the service-aware atom relation. -/
theorem payload_atoms_related (services : Services) :
    AtomRuntimeRel services
      (.grounded (services.bindingPayload Bindings.empty))
      (.gnd (.bindings [])) :=
  .bindingPayload Bindings.empty [] LeaBindingRelEquiv.empty

/-- The type-presentation carrier cannot relate the corresponding evaluator
bindings.  Its structural translation maps every native grounded value into
an ordinary runtime grounded constructor, never `Ground.bindings`. -/
theorem no_type_presentation_simulation (services : Services) :
    ¬∃ presentation,
      TypePresentationSimulationState presentation
        (payloadSpecBindings services) payloadRuntimeBindings := by
  rintro ⟨presentation, state⟩
  let valuation : String → Metta.Atom := fun name =>
    if name = "x" then
      .gnd (toLeaTTaGround (services.bindingPayload Bindings.empty))
    else .var name
  have specSatisfied : HEBindingSatisfied valuation
      (payloadSpecBindings services) := by
    constructor
    · intro name value member
      simp [payloadSpecBindings] at member
      rcases member with ⟨rfl, rfl⟩
      simp [valuation]
    · simp [payloadSpecBindings]
  have runtimeSatisfied : LeaBindingSatisfied valuation
      payloadRuntimeBindings :=
    (state.semantic.theory valuation).mp specSatisfied
  have payloadEquation := runtimeSatisfied.1 "x"
    (.gnd (.bindings [])) (by simp [payloadRuntimeBindings])
  cases payloadValue : services.bindingPayload Bindings.empty <;>
    simp [valuation, payloadValue, toLeaTTaGround,
      applyClassSolution] at payloadEquation

/-- The runtime matcher can place the opaque payload into a live evaluator
binding, so the negative theorem is not about an unreachable binding shape. -/
theorem payload_binding_is_matcher_reachable :
    payloadRuntimeBindings ∈
      Metta.matchAtoms (.var "x") (.gnd (.bindings [])) := by
  have loopFree : payloadRuntimeBindings.hasLoop = false :=
    Metta.Bindings.hasLoop_singleton_val_of_not_mem _ _ (by simp [Metta.Atom.vars])
  simp [payloadRuntimeBindings, Metta.matchAtoms, Metta.matchAtomsWith]
  simpa [payloadRuntimeBindings] using loopFree

end Mettapedia.Languages.MeTTa.HE.LeaTTaEvaluatorBindingPayloadCounterexample
