import Mettapedia.GSLT.Core.PolicyFamilySufficiency
import Mettapedia.GSLT.Dynamics.CapabilityIndexedObservationArchitecture

/-!
# Universal policy-family readouts for observation architectures

This module applies the generic least-sufficient-readout theorem to the exact
operational candidates of a capability-indexed observation architecture.  A
scheduler view supports a whole family precisely when its composite readout
`S -> V -> Q` retains the canonical vector of policy answers.

The theorem does not identify semantic values with scheduler scores and does
not require the scheduler readout to be faithful.  Loss is permitted exactly
when every declared policy is constant on the forgotten fibres.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics

open Mettapedia.GSLT.Core

universe uState uExecution uScore uPolicy uResult

namespace CapabilityIndexedObservationArchitecture.SchedulerReadout

variable {State : Type uState}
variable {Execution : State -> State -> Type uExecution}
variable {architecture :
  CapabilityIndexedObservationArchitecture State Execution}
variable {Score : Type uScore}

/-- The actual scheduler input on the architecture's declared operational
domain. -/
def candidateReadout (view : architecture.SchedulerReadout Score) :
    architecture.domain.Candidate -> Score :=
  fun candidate =>
    view.readout (architecture.discipline.readout candidate.1)

/-- A scheduler view supports a policy family when it retains executable
functions for every policy on every admitted operational candidate. -/
def SupportsFamily (view : architecture.SchedulerReadout Score)
    (family : PolicyFamily.{_, uPolicy, uResult}
      architecture.domain.Candidate) : Prop :=
  family.SupportsReadout view.candidateReadout

/-- **Exact scheduler-family criterion.**  Supporting every declared policy
is equivalent to refining the canonical policy vector. -/
theorem supportsFamily_iff_vectorFactors
    (view : architecture.SchedulerReadout Score)
    (family : PolicyFamily.{_, uPolicy, uResult}
      architecture.domain.Candidate) :
    view.SupportsFamily family <->
      NonFactorization.Factors view.candidateReadout family.vector :=
  family.supportsReadout_iff_vectorFactors view.candidateReadout

/-- Any supported scheduler view has a fixed forgetting map onto the least
sufficient policy vector. -/
theorem supportedFamily_refines_vector
    (view : architecture.SchedulerReadout Score)
    (family : PolicyFamily.{_, uPolicy, uResult}
      architecture.domain.Candidate)
    (supported : view.SupportsFamily family) :
    NonFactorization.Factors view.candidateReadout family.vector :=
  (view.supportsFamily_iff_vectorFactors family).1 supported

/-- A scheduler admitted for a larger family remains admitted for every
reindexed subrequest. -/
theorem supportsFamily_reindex
    (view : architecture.SchedulerReadout Score)
    (family : PolicyFamily.{_, uPolicy, uResult}
      architecture.domain.Candidate)
    {RequestedPolicy : Type*} (select : RequestedPolicy -> family.Policy)
    (supported : view.SupportsFamily family) :
    view.SupportsFamily (family.reindex select) :=
  family.supportsReadout_reindex select supported

/-- A collision separated by one declared policy refuses the whole family. -/
theorem not_supportsFamily_of_policy_collision
    (view : architecture.SchedulerReadout Score)
    (family : PolicyFamily.{_, uPolicy, uResult}
      architecture.domain.Candidate)
    {first second : architecture.domain.Candidate}
    (sameReadout : view.candidateReadout first = view.candidateReadout second)
    (policy : family.Policy)
    (differentDecision :
      family.decide policy first ≠ family.decide policy second) :
    Not (view.SupportsFamily family) :=
  family.not_supportsReadout_of_policy_collision view.candidateReadout
    sameReadout policy differentDecision

end CapabilityIndexedObservationArchitecture.SchedulerReadout

/-! ## A scheduler-family canary -/

namespace ObservationPolicyFamilyCanary

open CapabilityIndexedObservationArchitecture
open CapabilityIndexedObservationCanary

inductive HistoryPolicy where
  | length
  | beginsLeft
deriving DecidableEq

/-- A heterogeneous family: one policy returns a length, the other an
order-sensitive Boolean. -/
def historyFamily :
    PolicyFamily provenanceArchitecture.domain.Candidate where
  Policy := HistoryPolicy
  Result := fun
    | .length => Nat
    | .beginsLeft => Bool
  decide := fun
    | .length => fun candidate => candidate.1.length
    | .beginsLeft => fun candidate => beginsLeft candidate.1

inductive LengthPolicy where
  | length
deriving DecidableEq

/-- The smaller family requests only the statistic exposed by the scheduler. -/
def lengthFamily :
    PolicyFamily provenanceArchitecture.domain.Candidate :=
  historyFamily.reindex (fun _ : LengthPolicy => HistoryPolicy.length)

/-- The length scheduler realizes the length-only family despite being lossy. -/
theorem lengthScheduler_supports_lengthFamily :
    lengthScheduler.SupportsFamily lengthFamily := by
  refine ⟨{
    run := fun _ observed => observed
    agrees := ?_ }⟩
  intro policy candidate
  cases policy
  rfl

private def leftCandidate : provenanceArchitecture.domain.Candidate :=
  ⟨[Canary.Event.left, Canary.Event.right],
    ⟨[Canary.Event.left, Canary.Event.right], rfl⟩⟩

private def rightCandidate : provenanceArchitecture.domain.Candidate :=
  ⟨[Canary.Event.right, Canary.Event.left],
    ⟨[Canary.Event.right, Canary.Event.left], rfl⟩⟩

/-- Adding the order-sensitive policy makes the same lossy readout
insufficient.  The retained semantic state is unchanged; only the declared
consumer family has grown. -/
theorem lengthScheduler_refuses_historyFamily :
    Not (lengthScheduler.SupportsFamily historyFamily) := by
  apply lengthScheduler.not_supportsFamily_of_policy_collision historyFamily
      (first := leftCandidate) (second := rightCandidate) rfl
      .beginsLeft
  change true ≠ false
  decide

/-- The positive and negative controls coexist: lossiness alone neither
licenses nor refuses a scheduler view; exact policy-family sufficiency does. -/
theorem lossy_readout_is_family_relative :
    lengthScheduler.Lossy /\
      lengthScheduler.SupportsFamily lengthFamily /\
      Not (lengthScheduler.SupportsFamily historyFamily) :=
  ⟨lengthScheduler_isLossy,
    lengthScheduler_supports_lengthFamily,
    lengthScheduler_refuses_historyFamily⟩

end ObservationPolicyFamilyCanary

#print axioms CapabilityIndexedObservationArchitecture.SchedulerReadout.supportsFamily_iff_vectorFactors
#print axioms CapabilityIndexedObservationArchitecture.SchedulerReadout.supportedFamily_refines_vector
#print axioms CapabilityIndexedObservationArchitecture.SchedulerReadout.supportsFamily_reindex
#print axioms CapabilityIndexedObservationArchitecture.SchedulerReadout.not_supportsFamily_of_policy_collision
#print axioms ObservationPolicyFamilyCanary.lengthScheduler_supports_lengthFamily
#print axioms ObservationPolicyFamilyCanary.lengthScheduler_refuses_historyFamily
#print axioms ObservationPolicyFamilyCanary.lossy_readout_is_family_relative

end Mettapedia.GSLT.Dynamics
