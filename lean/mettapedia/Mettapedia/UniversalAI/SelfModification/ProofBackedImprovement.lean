import Mathlib.Logic.IsEmpty.Basic
import Mathlib.Order.Defs.PartialOrder

/-!
# Proof-backed improvement as a reusable interface

This file separates the mathematical core of proof-backed self-improvement
from any particular agent, formal system, search procedure, or programming
language.  Evidence is `Type`-valued so a realization may retain distinct proof
objects.  Historical Gödel-machine machinery and other reflective systems can
map into this interface by an explicit representation theorem.
-/

namespace Mettapedia.UniversalAI.SelfModification

universe uState uValue uEvidence

/-- A proof-relevant transition system whose certified transitions strictly
improve a value. -/
structure ProofBackedImprovement
    (State : Type uState) (Value : Type uValue) [Preorder Value] where
  value : State → Value
  Evidence : State → State → Type uEvidence
  improves : ∀ {before after}, Evidence before after → value before < value after

namespace ProofBackedImprovement

/-- Certified evidence cannot justify a self-loop in a preorder. -/
theorem no_self_evidence
    {State : Type uState} {Value : Type uValue} [Preorder Value]
    (system : ProofBackedImprovement State Value) (state : State) :
    IsEmpty (system.Evidence state state) :=
  ⟨fun evidence => (lt_irrefl (system.value state)) (system.improves evidence)⟩

/-- Forget proof identity and retain only the support relation. -/
def Support
    {State : Type uState} {Value : Type uValue} [Preorder Value]
    (system : ProofBackedImprovement State Value) (before after : State) : Prop :=
  Nonempty (system.Evidence before after)

/-- Support still implies strict improvement, but cannot reconstruct proof
identity or multiplicity. -/
theorem support_improves
    {State : Type uState} {Value : Type uValue} [Preorder Value]
    (system : ProofBackedImprovement State Value) {before after : State}
    (support : system.Support before after) :
    system.value before < system.value after := by
  rcases support with ⟨evidence⟩
  exact system.improves evidence

end ProofBackedImprovement

end Mettapedia.UniversalAI.SelfModification
