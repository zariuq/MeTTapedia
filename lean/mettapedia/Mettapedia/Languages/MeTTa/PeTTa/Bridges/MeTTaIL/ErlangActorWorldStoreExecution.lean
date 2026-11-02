import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorProcessStoreCorrespondence
import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangActorWorldWire

/-! The loaded actor commit updates exactly the selected source process.
In-flight messages, the fresh-pid counter and prior administrative history
are retained. Choosing the next machine state remains the operation's
separate sequential/mailbox correspondence obligation. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorWorldStoreExecution

open Mettapedia.GSLT.LanguageDef CettaWire ModuleFormat.ErlangActorProcessWire ModuleFormat.ErlangActorWorldWire
open Mettapedia.Languages.Erlang
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval DeclarativeSpec BridgeKit WireKit ErlangControllerSource

theorem returns (box : Mailbox Value → Term) (machine : MachineState → Term) (payload : Value → Term)
    (state : State) {system : ActorSystem} (valid : system.CanonicalPids)
    {index : Nat} {selected : LocalProcess} (found : system.processes[index]? = some selected)
    (replacement : LocalProcess) (identity : replacement.identity = index) (effect history : Term) :
    PureReturns runtime [] state (apply "gslt:er-actor:store"
      [number index, encoded (box replacement.mailbox), encoded (machine replacement.machine), encoded effect,
        encoded (world box machine payload system history)]) state
      (encoded (world box machine payload (system.replace index replacement) (record effect history))) := by
  have updated := ErlangActorProcessStoreCorrespondence.source_update_realized box machine state valid found replacement
  apply ErlangActorStoreCall.store_returns
  metta_literal
  metta_eval [updated] with actor_checked unfolding [world, record, process, ActorSystem.replace, identity]

theorem completed_commit_readback (box : Mailbox Value → Term) (machine : MachineState → Term)
    (payload : Value → Term) (state after : State) {system : ActorSystem} (valid : system.CanonicalPids)
    {index : Nat} {selected : LocalProcess} (found : system.processes[index]? = some selected)
    (replacement : LocalProcess) (identity : replacement.identity = index) (effect history observed : Term)
    (read : Runs runtime {state := state, control := .evaluate [] (apply "gslt:er-actor:store"
      [number index, encoded (box replacement.mailbox), encoded (machine replacement.machine), encoded effect,
        encoded (world box machine payload system history)])}
      (.complete after [encoded observed] [] [])) :
    observed = world box machine payload (system.replace index replacement) (record effect history) := by
  have actual := returns box machine payload state valid found replacement identity effect history
  have values := (pure_returns_derivation_iff runtime [] state state _ _ actual after _ [] []).mp read |>.2.1
  exact CettaWireAtom.encode_injective _ _ (List.cons.inj values).1

theorem portable_returns (box : Mailbox Value → Term) (machine : MachineState → Term) (payload : Value → Term)
    (state : State) {system : ActorSystem} (valid : system.CanonicalPids)
    {index : Nat} {selected : LocalProcess} (found : system.processes[index]? = some selected)
    (replacement : LocalProcess) (identity : replacement.identity = index) (effect history : Term) :
    PureReturns portableRuntime [] state (apply "gslt:er-actor:store"
      [number index, encoded (box replacement.mailbox), encoded (machine replacement.machine), encoded effect,
        encoded (world box machine payload system history)]) state
      (encoded (world box machine payload (system.replace index replacement) (record effect history))) := by
  have original := returns box machine payload state valid found replacement identity effect history
  apply captured_call_in_extension (Library.closed portable_checked) (Library.agreement portable_checked)
    [] (Library.bind ["pid", "mailbox", "machine", "effect", "system"]
      [number index, encoded (box replacement.mailbox), encoded (machine replacement.machine), encoded effect,
        encoded (world box machine payload system history)]) state state "gslt:er-actor:store"
    [number index, encoded (box replacement.mailbox), encoded (machine replacement.machine), encoded effect,
        encoded (world box machine payload system history)] ["pid", "mailbox", "machine", "effect", "system"] _
    (by decide +kernel) (by decide) (by decide +kernel) (by decide)
  · intro offset argument found
    obtain ⟨bounded, _⟩ := List.getElem?_eq_some_iff.mp found
    simp only [List.length_cons, List.length_nil] at bounded
    interval_cases offset
    all_goals
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at found
      subst argument
      first | exact Or.inr rfl | exact Or.inl (by decide +kernel)
  · simp [Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
      Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup, Library.bind,
      CettaWireAtom.applySubst_encode, encoded, number, CettaWireAtom.encode]
  · exact original

theorem commit_canonical {system : ActorSystem} (valid : system.CanonicalPids)
    {index : Nat} {selected : LocalProcess} (found : system.processes[index]? = some selected)
    (replacement : LocalProcess) (identity : replacement.identity = index) :
    (system.replace index replacement).CanonicalPids :=
  valid.replace found (identity.trans (valid.at found).symm)

theorem portable_completed_commit_readback (box : Mailbox Value → Term) (machine : MachineState → Term)
    (payload : Value → Term) (state after : State) {system : ActorSystem} (valid : system.CanonicalPids)
    {index : Nat} {selected : LocalProcess} (found : system.processes[index]? = some selected)
    (replacement : LocalProcess) (identity : replacement.identity = index) (effect history observed : Term)
    (read : Runs portableRuntime {state := state, control := .evaluate [] (apply "gslt:er-actor:store"
      [number index, encoded (box replacement.mailbox), encoded (machine replacement.machine), encoded effect,
        encoded (world box machine payload system history)])}
      (.complete after [encoded observed] [] [])) :
    observed = world box machine payload (system.replace index replacement) (record effect history) := by
  have actual := portable_returns box machine payload state valid found replacement identity effect history
  have values := (pure_returns_derivation_iff portableRuntime [] state state _ _ actual after _ [] []).mp read |>.2.1
  exact CettaWireAtom.encode_injective _ _ (List.cons.inj values).1

#print axioms returns
#print axioms completed_commit_readback
#print axioms portable_returns
#print axioms commit_canonical
#print axioms portable_completed_commit_readback

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorWorldStoreExecution
