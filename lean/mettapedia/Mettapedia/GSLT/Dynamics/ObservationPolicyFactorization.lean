import Mettapedia.GSLT.Dynamics.ObservationDiscipline
import Mettapedia.GSLT.Core.NonFactorization

/-!
# General policy factorization through observation readouts

An observation discipline retains a witness container `S` and exposes a
readout `S -> V`.  A downstream policy is safe to run from `V` exactly when
it is constant on the fibres of that readout.  This module states that
criterion for arbitrary inhabited policy result types.

The result type is required to be inhabited only so that a total policy on
`V` can return something at values outside the image of the readout.  Those
values are never produced by the discipline and impose no semantic
constraint.
-/

namespace Mettapedia.GSLT.Dynamics

open Mettapedia.Algebra

universe uEvent uContainer uValue uDecision

namespace ObservationDiscipline

/-- A policy is supported by an observation discipline when it factors
through the discipline's value readout. -/
def SupportsPolicy {Event : Type uEvent}
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event)
    (policy : discipline.collection.Container -> Decision) : Prop :=
  Mettapedia.GSLT.Core.NonFactorization.Factors
    discipline.readout policy

/-- The policy is constant on readout fibres when equal observations always
induce equal decisions. -/
def PolicyConstantOnReadoutFibers {Event : Type uEvent}
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event)
    (policy : discipline.collection.Container -> Decision) : Prop :=
  Mettapedia.GSLT.Core.NonFactorization.ConstantOnFibers
    discipline.readout policy

/-- **Exact policy-support criterion.**  For an inhabited decision type, a
policy factors through the observation readout exactly when it is constant
on readout fibres.  Values outside the readout image receive an arbitrary
default and cannot affect an observed execution. -/
theorem supportsPolicy_iff_constantOnReadoutFibers
    {Event : Type uEvent} [Nonempty Decision]
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event)
    (policy : discipline.collection.Container -> Decision) :
    discipline.SupportsPolicy policy ↔
      discipline.PolicyConstantOnReadoutFibers policy := by
  constructor
  · exact Mettapedia.GSLT.Core.NonFactorization.Factors.constantOnFibers
  · intro constant
    classical
    let fallback : Decision := Classical.choice inferInstance
    let recover : discipline.Value -> Decision := fun value =>
      if h : ∃ container, discipline.readout container = value then
        policy (Classical.choose h)
      else
        fallback
    refine ⟨recover, fun container => ?_⟩
    simp only [recover]
    split
    · rename_i reachable
      exact constant _ _ (Classical.choose_spec reachable)
    · rename_i unreachable
      exact False.elim (unreachable ⟨container, rfl⟩)

/-- Any policy explicitly computed from the readout is supported. -/
theorem supportsPolicy_of_readoutPolicy {Event : Type uEvent}
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event)
    (observedPolicy : discipline.Value -> Decision) :
    discipline.SupportsPolicy
      (observedPolicy ∘ discipline.readout) := by
  exact ⟨observedPolicy, fun _ => rfl⟩

/-- One readout collision with distinct policy results refutes support. -/
theorem not_supportsPolicy_of_collision {Event : Type uEvent}
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event)
    (policy : discipline.collection.Container -> Decision)
    {first second : discipline.collection.Container}
    (sameReadout : discipline.readout first = discipline.readout second)
    (differentDecision : policy first ≠ policy second) :
    ¬ discipline.SupportsPolicy policy :=
  Mettapedia.GSLT.Core.NonFactorization.NonTrivialFiber.not_factors
    { left := first
      right := second
      sameShadow := sameReadout
      differentValue := differentDecision }

/-- Supported policies are closed under postcomposition of their decisions. -/
theorem supportsPolicy_postcompose {Event : Type uEvent}
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event)
    (policy : discipline.collection.Container -> Decision)
    (supported : discipline.SupportsPolicy policy)
    (translate : Decision -> OtherDecision) :
    discipline.SupportsPolicy (translate ∘ policy) := by
  obtain ⟨observedPolicy, recovers⟩ := supported
  refine ⟨translate ∘ observedPolicy, fun container => ?_⟩
  simp only [Function.comp_apply, recovers]

/-- Two independently supported policies on one retained container pair into
one supported product decision without merging their result algebras. -/
theorem supportsPolicy_pair {Event : Type uEvent}
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event)
    (leftPolicy : discipline.collection.Container -> LeftDecision)
    (rightPolicy : discipline.collection.Container -> RightDecision)
    (leftSupported : discipline.SupportsPolicy leftPolicy)
    (rightSupported : discipline.SupportsPolicy rightPolicy) :
    discipline.SupportsPolicy
      (fun container => (leftPolicy container, rightPolicy container)) := by
  obtain ⟨leftObserved, leftRecovers⟩ := leftSupported
  obtain ⟨rightObserved, rightRecovers⟩ := rightSupported
  refine ⟨fun value => (leftObserved value, rightObserved value),
    fun container => ?_⟩
  exact Prod.ext (leftRecovers container) (rightRecovers container)

/-! ## Proof-relevant decision specifications

A decision problem may admit several decisions at one retained history, and
the reason a decision is admissible can itself carry evidence.  The following
interface therefore uses a type-valued specification rather than prematurely
selecting one distinguished decision or quotienting admissibility to a
Boolean.  A collision is operationally significant precisely when no one
decision has admissibility evidence at both ends of an observation fibre.
-/

universe uEvidence

/-- Evidence that a container-indexed policy realizes a proof-relevant
decision specification at every retained container. -/
abbrev PolicyRealization {Event : Type uEvent}
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event)
    (Admissible : discipline.collection.Container → Decision → Type uEvidence)
    (policy : discipline.collection.Container → Decision) :
    Type (max uContainer uEvidence) :=
  ∀ container, Admissible container (policy container)

/-- Evidence that a policy computed only from the observation readout realizes
the specification at every retained container. -/
abbrev ReadoutPolicyRealization {Event : Type uEvent}
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event)
    (Admissible : discipline.collection.Container → Decision → Type uEvidence)
    (policy : discipline.Value → Decision) : Type (max uContainer uEvidence) :=
  ∀ container, Admissible container (policy (discipline.readout container))

/-- Two retained containers in one observation fibre whose admissible
decision types have empty intersection.  This is stronger and more general
than requiring a preselected decision function to differ at the two points. -/
structure IncompatibleDecisionFiber {Event : Type uEvent}
    (discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event)
    (Admissible : discipline.collection.Container → Decision → Type uEvidence) where
  left : discipline.collection.Container
  right : discipline.collection.Container
  sameReadout : discipline.readout left = discipline.readout right
  incompatible : ∀ decision,
    IsEmpty (Admissible left decision × Admissible right decision)

/-- An incompatible observation fibre rules out every policy that sees only
the readout.  The conclusion is type-valued: it excludes a complete family of
admissibility witnesses, not merely a Boolean success flag. -/
theorem IncompatibleDecisionFiber.no_readoutPolicyRealization
    {Event : Type uEvent}
    {discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event}
    {Admissible : discipline.collection.Container → Decision → Type uEvidence}
    (fiber : IncompatibleDecisionFiber discipline Admissible)
    (policy : discipline.Value → Decision) :
    IsEmpty (ReadoutPolicyRealization discipline Admissible policy) := by
  constructor
  intro realizes
  letI := fiber.incompatible (policy (discipline.readout fiber.left))
  exact isEmptyElim
    (⟨realizes fiber.left,
        by simpa only [fiber.sameReadout] using realizes fiber.right⟩ :
      Admissible fiber.left (policy (discipline.readout fiber.left)) ×
        Admissible fiber.right (policy (discipline.readout fiber.left)))

/-- A policy realizing an incompatible specification cannot itself factor
through the observation readout. -/
theorem IncompatibleDecisionFiber.realizingPolicy_not_supported
    {Event : Type uEvent}
    {discipline : ObservationDiscipline.{uEvent, uContainer, uValue} Event}
    {Admissible : discipline.collection.Container → Decision → Type uEvidence}
    (fiber : IncompatibleDecisionFiber discipline Admissible)
    (policy : discipline.collection.Container → Decision)
    (realizes : PolicyRealization discipline Admissible policy) :
    ¬ discipline.SupportsPolicy policy := by
  apply not_supportsPolicy_of_collision discipline policy fiber.sameReadout
  intro sameDecision
  letI := fiber.incompatible (policy fiber.left)
  exact isEmptyElim
    (⟨realizes fiber.left,
        by simpa only [sameDecision] using realizes fiber.right⟩ :
      Admissible fiber.left (policy fiber.left) ×
        Admissible fiber.right (policy fiber.left))

end ObservationDiscipline

/-! ## Work/span policy controls -/

namespace WorkSpanPolicyCanary

def unitCost : Unit -> WorkSpan :=
  fun _ => ⟨1, 1⟩

def full : ObservationDiscipline Unit :=
  WorkSpanObservation.discipline unitCost

def workOnly : ObservationDiscipline Unit :=
  WorkSpanObservation.workOnly unitCost

def workAtLeastTwo (value : WorkSpan) : Bool :=
  decide (2 ≤ value.work)

def spanAtLeastTwo (value : WorkSpan) : Bool :=
  decide (2 ≤ value.span)

/-- The identity WorkSpan readout supports every policy on WorkSpan. -/
theorem full_supports_every_policy (policy : WorkSpan -> Decision) :
    full.SupportsPolicy policy := by
  exact ⟨policy, fun _ => rfl⟩

/-- Work-only observation supports a work-threshold policy. -/
theorem workOnly_supports_workAtLeastTwo :
    workOnly.SupportsPolicy workAtLeastTwo := by
  refine ⟨fun work : Nat => decide (2 ≤ work), fun _ => ?_⟩
  rfl

/-- The same work-only observation cannot support a span-threshold policy. -/
theorem workOnly_not_supports_spanAtLeastTwo :
    ¬ workOnly.SupportsPolicy spanAtLeastTwo := by
  apply ObservationDiscipline.not_supportsPolicy_of_collision workOnly
      spanAtLeastTwo (first := (⟨2, 1⟩ : WorkSpan)) (second := ⟨2, 2⟩)
  · rfl
  · decide

/-- A lossy observation may still support a declared policy. -/
theorem workOnly_lossy_but_supports_workAtLeastTwo :
    workOnly.Lossy ∧ workOnly.SupportsPolicy workAtLeastTwo :=
  ⟨by
      apply ObservationDiscipline.lossy_of_collision workOnly
          (first := (⟨2, 1⟩ : WorkSpan)) (second := ⟨2, 2⟩)
      · intro same
        have sameSpan := congrArg WorkSpan.span same
        norm_num at sameSpan
      · rfl,
    workOnly_supports_workAtLeastTwo⟩

end WorkSpanPolicyCanary

#print axioms ObservationDiscipline.supportsPolicy_iff_constantOnReadoutFibers
#print axioms ObservationDiscipline.supportsPolicy_of_readoutPolicy
#print axioms ObservationDiscipline.not_supportsPolicy_of_collision
#print axioms ObservationDiscipline.supportsPolicy_postcompose
#print axioms ObservationDiscipline.supportsPolicy_pair
#print axioms ObservationDiscipline.IncompatibleDecisionFiber.no_readoutPolicyRealization
#print axioms ObservationDiscipline.IncompatibleDecisionFiber.realizingPolicy_not_supported
#print axioms WorkSpanPolicyCanary.full_supports_every_policy
#print axioms WorkSpanPolicyCanary.workOnly_lossy_but_supports_workAtLeastTwo
#print axioms WorkSpanPolicyCanary.workOnly_not_supports_spanAtLeastTwo

end Mettapedia.GSLT.Dynamics
