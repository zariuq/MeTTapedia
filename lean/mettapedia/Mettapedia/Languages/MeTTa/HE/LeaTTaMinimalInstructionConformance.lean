import Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal
import Mettapedia.Languages.MeTTa.HE.LeaTTaBindingTransport

/-!
# LeaTTa minimal-instruction carrier conformance

The executable-independent minimal semantics represents a collapsed binding
set by an abstract grounded value.  LeaTTa represents the same object by the
typed `Ground.bindings` carrier.  This module relates those two representations
without choosing the runtime's private spelling in the specification.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaMinimalInstructionConformance

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
open Spec.Eval.Minimal

/-- Atom correspondence extended by one opaque binding-payload case.  Ordinary
grounded values use the established structural translation; a service payload
is related to the typed runtime carrier through binding-set equivalence. -/
inductive AtomRuntimeRel (services : Services) : Atom → Metta.Atom → Prop where
  | symbol (name : String) :
      AtomRuntimeRel services (.symbol name) (.sym name)
  | variable (name : String) :
      AtomRuntimeRel services (.var name) (.var name)
  | grounded (value : GroundedValue)
      (notPayload : ∀ bindings, value ≠ services.bindingPayload bindings) :
      AtomRuntimeRel services (.grounded value)
        (.gnd (toLeaTTaGround value))
  | bindingPayload (bindings : Bindings) (runtimeBindings : Metta.Bindings) :
      LeaBindingRelEquiv bindings runtimeBindings →
      AtomRuntimeRel services
        (.grounded (services.bindingPayload bindings))
        (.gnd (.bindings (Metta.Bindings.store runtimeBindings)))
  | expression (atoms : List Atom) (runtimeAtoms : List Metta.Atom) :
      List.Forall₂ (AtomRuntimeRel services) atoms runtimeAtoms →
      AtomRuntimeRel services (.expression atoms) (.expr runtimeAtoms)

/-- A semantic result and a runtime result agree on both the result atom and
the complete binding set. -/
structure ResultRuntimeRel (services : Services)
    (result : ResultPair) (runtimeResult : Metta.Atom × Metta.Bindings) : Prop where
  atom : AtomRuntimeRel services result.1 runtimeResult.1
  bindings : LeaBindingRelEquiv result.2 runtimeResult.2

/-- Runtime encoding used by repaired `collapse-bind`. -/
def encodeRuntimeResult
    (result : Metta.Atom × Metta.Bindings) : Metta.Atom :=
  .expr [result.1, .gnd (.bindings (Metta.Bindings.store result.2))]

/-- One related result pair has related opaque encodings. -/
theorem encodeResult_runtime {services : Services}
    {result : ResultPair} {runtimeResult : Metta.Atom × Metta.Bindings}
    (related : ResultRuntimeRel services result runtimeResult) :
    AtomRuntimeRel services (encodeResult services result)
      (encodeRuntimeResult runtimeResult) := by
  apply AtomRuntimeRel.expression
  exact .cons related.atom
    (.cons (.bindingPayload result.2 runtimeResult.2 related.bindings) .nil)

/-- Ordered pointwise result correspondence lifts through the exact
collapse encoding without losing order or multiplicity. -/
theorem encodeResults_runtime {services : Services}
    {results : ResultSet}
    {runtimeResults : List (Metta.Atom × Metta.Bindings)}
    (related : List.Forall₂ (ResultRuntimeRel services) results runtimeResults) :
    AtomRuntimeRel services (encodeResults services results)
      (.expr (runtimeResults.map encodeRuntimeResult)) := by
  apply AtomRuntimeRel.expression
  induction related with
  | nil => exact .nil
  | cons head tail inductionHypothesis =>
      exact .cons (encodeResult_runtime head) inductionHypothesis

/-- The concrete runtime payload restores the exact runtime binding list
before `superpose-bind` performs its continuation merge. -/
theorem runtime_binding_payload_roundtrip (bindings : Metta.Bindings) :
    Metta.Bindings.restore (Metta.Bindings.store bindings) = bindings :=
  Metta.Bindings.restore_store bindings

/-- A lawful abstract context handle uses the ordinary grounded-value lane:
unlike a collapsed binding set, it requires no runtime-specific constructor. -/
theorem contextPayload_runtime {services : Services}
    (laws : ServiceLaws services) (space : Space) :
    AtomRuntimeRel services
      (.grounded (services.contextPayload space))
      (.gnd (toLeaTTaGround (services.contextPayload space))) :=
  .grounded _ (laws.contextPayload_ne_bindingPayload space)

/-! ## Positive and negative boundary canaries -/

/-- Positive: empty binding sets are related and therefore have related opaque
payloads. -/
example (services : Services) :
    AtomRuntimeRel services
      (.grounded (services.bindingPayload Bindings.empty))
      (.gnd (.bindings (Metta.Bindings.store []))) :=
  .bindingPayload Bindings.empty [] LeaBindingRelEquiv.empty

/-- Negative: a binding payload cannot satisfy the separation premise of the
ordinary-grounded constructor. -/
theorem binding_payload_is_not_ordinary {services : Services}
    (bindings : Bindings) :
    ¬(∀ candidate,
      services.bindingPayload bindings ≠ services.bindingPayload candidate) := by
  intro separated
  exact separated bindings rfl

end Mettapedia.Languages.MeTTa.HE.LeaTTaMinimalInstructionConformance
