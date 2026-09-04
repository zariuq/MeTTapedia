import Mettapedia.Languages.OpenTheory.AxiomPolicy
import Mettapedia.Logic.Derivation

/-!
# Least theory closure of the pinned OpenTheory primitive kernel

An axiom policy constrains provenance, but an isolated primitive request may
still mention theorem inputs that were never derived.  This module exposes the
embedded theorem inputs as an ordered premise list and takes the least
finitary closure of policy-qualified primitive steps.

The resulting `PolicyPrimitiveRule` plus `Derives` is the proof-theoretic
object-theory boundary for the currently formalized primitive kernel.  It does
not yet include constant/type definitions, article-state execution, a reader,
or any selected standard HOL axiom policy.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory

open Mettapedia.Logic

namespace PrimitiveRequest

/-- Ordered theorem inputs consumed by a primitive request.  Nullary kernel
rules have no theorem premises. -/
def premises : PrimitiveRequest → List Theorem
  | .core (.axiom _sequent) => []
  | .core (.assume _term) => []
  | .core (.refl _term) => []
  | .core (.app left right) => [left, right]
  | .core (.deductAntisym left right) => [left, right]
  | .core (.eqMp equality premise) => [equality, premise]
  | .binding (.abs _sourceVar input) => [input]
  | .binding (.betaConv _redex) => []
  | .subst _substitution input => [input]

end PrimitiveRequest

/-- A primitive OpenTheory rule instance with its exact ordered theorem
premises and independently selected axiom policy. -/
def PolicyPrimitiveRule (policy : AxiomPolicy) :
    List Theorem → Theorem → Prop :=
  fun premises out =>
    ∃ request : PrimitiveRequest,
      request.premises = premises ∧
      request.InputAxiomsAllowed policy ∧
      PrimitiveStep request out

namespace PolicyPrimitiveRule

theorem outputAxiomsAllowed (policy : AxiomPolicy)
    {premises : List Theorem} {out : Theorem}
    (rule : PolicyPrimitiveRule policy premises out) :
    policy.AllowsTheorem out := by
  obtain ⟨request, _premises, inputsAllowed, step⟩ := rule
  obtain ⟨evidence⟩ := step
  exact evidence.outputAxiomsAllowed policy inputsAllowed

end PolicyPrimitiveRule

/-- Every theorem in the least policy-qualified closure has fully authorized
axiom provenance. -/
theorem derives_only_authorized_axioms (policy : AxiomPolicy)
    {out : Theorem} (derivation : Derives (PolicyPrimitiveRule policy) out) :
    policy.AllowsTheorem out := by
  apply Derives.least (policy.AllowsTheorem) _ derivation
  intro premises conclusion rule _premisesAllowed
  exact rule.outputAxiomsAllowed policy

/-- Any theorem carrying a disallowed axiom tag is outside the least closure. -/
theorem underivable_of_disallowed_axioms (policy : AxiomPolicy)
    (out : Theorem) (disallowed : ¬ policy.AllowsTheorem out) :
    ¬ Derives (PolicyPrimitiveRule policy) out := by
  intro derivation
  exact disallowed (derives_only_authorized_axioms policy derivation)

/-- A checked request with the exact premise list and policy obligation forms
one primitive rule instance. -/
theorem rule_of_checkPrimitive (policy : AxiomPolicy)
    (request : PrimitiveRequest) (out : Theorem)
    (inputsAllowed : request.InputAxiomsAllowed policy)
    (accepted : checkPrimitive request = some out) :
    PolicyPrimitiveRule policy request.premises out := by
  exact ⟨request, rfl, inputsAllowed,
    (checkPrimitive_eq_some_iff request out).mp accepted⟩

/-- A policy-qualified nullary request yields a one-node derivation. -/
theorem derives_of_nullary_check (policy : AxiomPolicy)
    (request : PrimitiveRequest) (out : Theorem)
    (nullary : request.premises = [])
    (inputsAllowed : request.InputAxiomsAllowed policy)
    (accepted : checkPrimitive request = some out) :
    Derives (PolicyPrimitiveRule policy) out := by
  refine Derives.node [] out ?_ ?_
  · rw [← nullary]
    exact rule_of_checkPrimitive policy request out inputsAllowed accepted
  · intro premise member
    simp at member

end Mettapedia.Languages.OpenTheory
