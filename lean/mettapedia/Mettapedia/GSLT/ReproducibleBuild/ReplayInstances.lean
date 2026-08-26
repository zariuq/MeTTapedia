import Mettapedia.GSLT.ReproducibleBuild.HattaProfile
import Mettapedia.Languages.MeTTa.Prime.PeTTaChainerDAGReplayV1
import Mettapedia.Languages.MeTTa.Prime.SourceScopedAdaptiveRealization
import Mettapedia.Languages.MeTTa.HE.StateFreeExecution

/-!
# Prime and HE trajectory instances

Prime's PeTTaChainer DAG replay and HE's derivation-local state-free execution
are different evidence disciplines.  This file connects each to the generic
trajectory boundary without identifying them.

The Prime instance reuses the actual DAG-node replay machine.  The HE instance
turns one actual interpreter step into a replay event and transports an
existing `StateFreeExecution.Certificate` to a world-preservation theorem.
The existing Prime occurrence-erasure obstruction is reused as the collapsed
receipt control rather than re-proved.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ReproducibleBuild.ReplayInstances

open Mettapedia.GSLT.ReproducibleBuild.TrajectoryReplay

/-! ## Prime PeTTaChainer DAG replay -/

namespace Prime

open Mettapedia.Languages.MeTTa.Prime.PeTTaChainerDAGReplayV1

/-- The generic event system whose states and events are exactly those of the
existing Prime DAG replay engine. -/
def dagEventSystem : EventSystem (List CheckedNode) DAGNode where
  Step := fun initial node final => PLift (replayNode initial node = some final)
  step? := replayNode

theorem dagEventSystem_transitionAdequate :
    TransitionAdequate dagEventSystem := by
  intro initial node final
  constructor
  · exact fun replayed => ⟨⟨replayed⟩⟩
  · rintro ⟨⟨replayed⟩⟩
    exact replayed

/-- Generic trajectory replay is definitionally the existing Prime DAG-node
replay loop.  This is an interface theorem, not a replacement implementation. -/
theorem replay_eq_replayNodes (environment : List CheckedNode)
    (nodes : List DAGNode) :
    TrajectoryReplay.replay dagEventSystem environment nodes =
      replayNodes environment nodes := by
  induction nodes generalizing environment with
  | nil => rfl
  | cons node nodes ih =>
      simp only [TrajectoryReplay.replay, replayNodes, dagEventSystem]
      cases replayed : replayNode environment node with
      | none => rfl
      | some next =>
          simpa [dagEventSystem] using ih next

/-- Successful Prime node replay yields an authoritative proof-relevant
trajectory through the generic transition boundary. -/
theorem replayNodes_eq_some_iff_trajectory
    (environment : List CheckedNode) (nodes : List DAGNode)
    (final : List CheckedNode) :
    replayNodes environment nodes = some final <->
      Nonempty (Trajectory dagEventSystem.Step environment nodes final) := by
  rw [<- replay_eq_replayNodes]
  exact replay_eq_some_iff_trajectory dagEventSystem
    dagEventSystem_transitionAdequate environment nodes final

end Prime

/-! ## HE derivation-local state-free replay -/

namespace HE

open Metta
open Metta.Minimal
open Mettapedia.Languages.MeTTa.HE.StateFreeExecution

/-- One HE replay event supplies the fuel and work item for an actual
`interpretStack1` transition. -/
abbrev Event := Nat × Item

/-- The HE event system exposes the real interpreter state transition.  It
does not use Prime DAG nodes or Prime certificate checking. -/
def eventSystem (env : MinEnv) : EventSystem St Event where
  Step := fun initial event final =>
    PLift (final = (interpretStack1 env event.1 initial event.2).2)
  step? := fun initial event =>
    some (interpretStack1 env event.1 initial event.2).2

theorem eventSystem_transitionAdequate (env : MinEnv) :
    TransitionAdequate (eventSystem env) := by
  intro initial event final
  simp [eventSystem, eq_comm]

/-- An existing HE state-free certificate makes a replayed interpreter step
world-preserving.  The transition remains an HE step, not a generic proof-DAG
step. -/
theorem replay_singleton_preservesWorld_of_certificate
    {env : MinEnv} {Inv : World -> Item -> Prop}
    (certificate : Certificate env Inv)
    (fuel : Nat) (initial : St) (item : Item)
    (reached : Inv initial.world item) :
    let final := (interpretStack1 env fuel initial item).2
    TrajectoryReplay.replay (eventSystem env) initial [(fuel, item)] =
        some final /\
      final.world = initial.world := by
  dsimp
  constructor
  · simp [TrajectoryReplay.replay, eventSystem]
  · exact certificate.preserves fuel initial item reached

/-- The genuine full-prelude finished-frame certificate instantiates the HE
side of the replay boundary. -/
theorem fullPrelude_finished_replay_preservesWorld (fuel : Nat) :
    let item : Item :=
      { stack := [{ atom := Atom.sym "a", fin := true }], bnd := [] }
    let final := (interpretStack1 fullPreludeEnv fuel St.init item).2
    TrajectoryReplay.replay (eventSystem fullPreludeEnv) St.init
        [(fuel, item)] = some final /\
      final.world = St.init.world := by
  dsimp
  apply replay_singleton_preservesWorld_of_certificate
    (finished_stateFreeExecution fullPreludeEnv)
  exact pureFinished_inv _

/-- The existing concrete mutation witness prevents the HE instance from
accepting every event as state-free. -/
theorem mutation_has_no_covering_certificate
    (Inv : World -> Item -> Prop)
    (certificate : Certificate fullPreludeEnv Inv) :
    Not (Inv St.init.world mutatingItem) :=
  no_certificate_covers_mutation Inv certificate

end HE

/-! ## Receipt-collapse control -/

/-- Reuse the existing source-scoped Prime obstruction: replacing an
occurrence multiset by its support cannot preserve exact receipt distinctions. -/
theorem occurrenceSupportErasure_not_exactReceiptReplay :
    Not (Mettapedia.Cybernetics.Distinction.Conserves
      (Mettapedia.Cybernetics.Distinction.inequality (Multiset Unit))
      (Mettapedia.Cybernetics.Distinction.inequality (Finset Unit))
      (@Mettapedia.GSLT.Dynamics.AnswerEffects.bagToSupport.{0}.map Unit)) :=
  Mettapedia.Languages.MeTTa.Prime.SourceScopedAdaptiveRealization.occurrenceSupportErasure_not_exactDistinctionConserving

end Mettapedia.GSLT.ReproducibleBuild.ReplayInstances

#print axioms Mettapedia.GSLT.ReproducibleBuild.ReplayInstances.Prime.replayNodes_eq_some_iff_trajectory
#print axioms Mettapedia.GSLT.ReproducibleBuild.ReplayInstances.HE.fullPrelude_finished_replay_preservesWorld
#print axioms Mettapedia.GSLT.ReproducibleBuild.ReplayInstances.occurrenceSupportErasure_not_exactReceiptReplay
