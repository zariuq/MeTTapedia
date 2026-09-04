import Mettapedia.Languages.OpenTheory.PrimitiveRules

/-!
# Axiom policies for the pinned OpenTheory primitive kernel

The primitive OpenTheory kernel is an inference framework, not by itself an
object theory.  Its `axiom` rule may introduce any Boolean sequent and records
that sequent in the theorem's provenance.  An object theory must therefore
supply an independent policy identifying which axiom sequents are admitted.

This module makes that boundary explicit.  Each primitive request carries an
input-provenance obligation, and every primitive evidence constructor is
proved to preserve the selected policy.  No particular HOL axiom set,
definition package, article machine, or semantic model is selected here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory

/-- A selected family of admissible OpenTheory axiom sequents. -/
abbrev AxiomPolicy := Sequent → Prop

namespace AxiomPolicy

/-- Every axiom-provenance tag of a theorem is authorized by the policy. -/
def AllowsTheorem (policy : AxiomPolicy) (result : Theorem) : Prop :=
  ∀ sequent ∈ result.axioms, policy sequent

theorem allows_of_axioms_eq_empty (policy : AxiomPolicy) (result : Theorem)
    (axiomsEmpty : result.axioms = ∅) : policy.AllowsTheorem result := by
  intro sequent member
  rw [axiomsEmpty] at member
  simp at member

theorem allows_of_axioms_eq_singleton (policy : AxiomPolicy)
    (result : Theorem) (sequent : Sequent)
    (axiomsSingleton : result.axioms = {sequent})
    (allowed : policy sequent) : policy.AllowsTheorem result := by
  intro tagged member
  rw [axiomsSingleton, Finset.mem_singleton] at member
  subst tagged
  exact allowed

theorem allows_of_axioms_eq_union (policy : AxiomPolicy)
    (result left right : Theorem)
    (axiomsUnion : result.axioms = left.axioms ∪ right.axioms)
    (leftAllowed : policy.AllowsTheorem left)
    (rightAllowed : policy.AllowsTheorem right) :
    policy.AllowsTheorem result := by
  intro sequent member
  rw [axiomsUnion, Finset.mem_union] at member
  cases member with
  | inl leftMember => exact leftAllowed sequent leftMember
  | inr rightMember => exact rightAllowed sequent rightMember

theorem allows_of_axioms_eq (policy : AxiomPolicy)
    (result source : Theorem) (axiomsEqual : result.axioms = source.axioms)
    (sourceAllowed : policy.AllowsTheorem source) :
    policy.AllowsTheorem result := by
  intro sequent member
  rw [axiomsEqual] at member
  exact sourceAllowed sequent member

end AxiomPolicy

namespace CoreRequest

/-- The exact policy obligation contributed by the inputs of a core request. -/
def InputAxiomsAllowed (policy : AxiomPolicy) : CoreRequest → Prop
  | .axiom sequent => policy sequent
  | .assume _term => True
  | .refl _term => True
  | .app left right =>
      policy.AllowsTheorem left ∧ policy.AllowsTheorem right
  | .deductAntisym left right =>
      policy.AllowsTheorem left ∧ policy.AllowsTheorem right
  | .eqMp equality premise =>
      policy.AllowsTheorem equality ∧ policy.AllowsTheorem premise

end CoreRequest

namespace BindingRequest

/-- The exact policy obligation contributed by the inputs of a binding
request. -/
def InputAxiomsAllowed (policy : AxiomPolicy) : BindingRequest → Prop
  | .abs _sourceVar input => policy.AllowsTheorem input
  | .betaConv _redex => True

end BindingRequest

namespace PrimitiveRequest

/-- The exact axiom-policy obligation for a combined primitive request. -/
def InputAxiomsAllowed (policy : AxiomPolicy) : PrimitiveRequest → Prop
  | .core request => request.InputAxiomsAllowed policy
  | .binding request => request.InputAxiomsAllowed policy
  | .subst _substitution input => policy.AllowsTheorem input

end PrimitiveRequest

namespace CoreEvidence

/-- Every pinned core inference preserves authorized axiom provenance. -/
theorem outputAxiomsAllowed (policy : AxiomPolicy)
    {request : CoreRequest} {out : Theorem}
    (inputsAllowed : request.InputAxiomsAllowed policy)
    (evidence : CoreEvidence request out) :
    policy.AllowsTheorem out := by
  cases evidence with
  | «axiom» hbool parts =>
      exact policy.allows_of_axioms_eq_singleton out _ parts.1 inputsAllowed
  | assume hbool parts =>
      exact policy.allows_of_axioms_eq_empty out parts.1
  | refl equality construction parts =>
      exact policy.allows_of_axioms_eq_empty out parts.1
  | app functionLeft functionRight argumentLeft argumentRight applicationLeft
      applicationRight equality functionView argumentView leftApplication
      rightApplication construction parts =>
      exact policy.allows_of_axioms_eq_union out _ _ parts.1
        inputsAllowed.1 inputsAllowed.2
  | deductAntisym equality construction parts =>
      exact policy.allows_of_axioms_eq_union out _ _ parts.1
        inputsAllowed.1 inputsAllowed.2
  | eqMp left right view hmatch parts =>
      exact policy.allows_of_axioms_eq_union out _ _ parts.1
        inputsAllowed.1 inputsAllowed.2

end CoreEvidence

namespace BindingEvidence

/-- Every pinned binding inference preserves authorized axiom provenance. -/
theorem outputAxiomsAllowed (policy : AxiomPolicy)
    {request : BindingRequest} {out : Theorem}
    (inputsAllowed : request.InputAxiomsAllowed policy)
    (evidence : BindingEvidence request out) :
    policy.AllowsTheorem out := by
  cases evidence with
  | abs fresh left right leftAbs rightAbs equality view leftAbstraction
      rightAbstraction construction parts =>
      exact policy.allows_of_axioms_eq out _ parts.1 inputsAllowed
  | betaConv reduced equality reduction construction parts =>
      exact policy.allows_of_axioms_eq_empty out parts.1

end BindingEvidence

namespace PrimitiveEvidence

/-- Every one of the nine pinned primitive rules preserves an independently
selected axiom policy. -/
theorem outputAxiomsAllowed (policy : AxiomPolicy)
    {request : PrimitiveRequest} {out : Theorem}
    (inputsAllowed : request.InputAxiomsAllowed policy)
    (evidence : PrimitiveEvidence request out) :
    policy.AllowsTheorem out := by
  cases evidence with
  | core coreEvidence =>
      exact coreEvidence.outputAxiomsAllowed policy inputsAllowed
  | binding bindingEvidence =>
      exact bindingEvidence.outputAxiomsAllowed policy inputsAllowed
  | subst substitutionEvidence =>
      exact policy.allows_of_axioms_eq out _ substitutionEvidence.1
        inputsAllowed

end PrimitiveEvidence

/-- A primitive step qualified by an independently selected axiom policy. -/
def PolicyQualifiedPrimitiveStep (policy : AxiomPolicy)
    (request : PrimitiveRequest) (out : Theorem) : Prop :=
  request.InputAxiomsAllowed policy ∧ PrimitiveStep request out

/-- Every policy-qualified primitive step produces a theorem whose complete
axiom provenance satisfies that policy. -/
theorem PolicyQualifiedPrimitiveStep.outputAxiomsAllowed
    (policy : AxiomPolicy) {request : PrimitiveRequest} {out : Theorem}
    (step : PolicyQualifiedPrimitiveStep policy request out) :
    policy.AllowsTheorem out := by
  obtain ⟨inputsAllowed, ⟨evidence⟩⟩ := step
  exact evidence.outputAxiomsAllowed policy inputsAllowed

/-- Executable primitive acceptance plus the policy obligation yields an
authorized theorem. -/
theorem checkPrimitive_outputAxiomsAllowed (policy : AxiomPolicy)
    (request : PrimitiveRequest) (out : Theorem)
    (inputsAllowed : request.InputAxiomsAllowed policy)
    (accepted : checkPrimitive request = some out) :
    policy.AllowsTheorem out := by
  obtain ⟨evidence⟩ := (checkPrimitive_eq_some_iff request out).mp accepted
  exact evidence.outputAxiomsAllowed policy inputsAllowed

/-! ## Boundary canaries -/

/-- The unrestricted policy admits every possible axiom provenance. -/
def unrestrictedAxiomPolicy : AxiomPolicy := fun _sequent => True

/-- The empty policy admits no primitive axiom provenance. -/
def emptyAxiomPolicy : AxiomPolicy := fun _sequent => False

theorem unrestricted_allows_every_request (request : PrimitiveRequest) :
    request.InputAxiomsAllowed unrestrictedAxiomPolicy := by
  cases request with
  | core request =>
      cases request <;> simp [PrimitiveRequest.InputAxiomsAllowed,
        CoreRequest.InputAxiomsAllowed, unrestrictedAxiomPolicy,
        AxiomPolicy.AllowsTheorem]
  | binding request =>
      cases request <;> simp [PrimitiveRequest.InputAxiomsAllowed,
        BindingRequest.InputAxiomsAllowed, unrestrictedAxiomPolicy,
        AxiomPolicy.AllowsTheorem]
  | subst substitution input =>
      simp [PrimitiveRequest.InputAxiomsAllowed, unrestrictedAxiomPolicy,
        AxiomPolicy.AllowsTheorem]

/-- Negative control: the empty object theory rejects every axiom request,
even though the unqualified primitive kernel can execute a Boolean one. -/
theorem empty_rejects_axiom_request (sequent : Sequent) :
    ¬ (PrimitiveRequest.core (.axiom sequent)).InputAxiomsAllowed
      emptyAxiomPolicy := by
  simp [PrimitiveRequest.InputAxiomsAllowed,
    CoreRequest.InputAxiomsAllowed, emptyAxiomPolicy]

/-- Non-axiomatic reflexivity has no axiom-policy precondition. -/
theorem empty_allows_refl_request (term : CanonicalTerm) :
    (PrimitiveRequest.core (.refl term)).InputAxiomsAllowed
      emptyAxiomPolicy := by
  simp [PrimitiveRequest.InputAxiomsAllowed,
    CoreRequest.InputAxiomsAllowed]

end Mettapedia.Languages.OpenTheory
