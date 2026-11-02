import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailboxEmissionAgreement
import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailboxResumptionAgreement

/-! Full-machine begin and advance calls used by the emitted Erlang actor
adapter. Pending searches, state history and receipts are returned intact.
Completed packet readback does not assume that its target decodes to a
source queue. The actor callback and native-rho transfer are separate joins. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangMailboxMachineExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox
open Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox.Execution
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Machines.ResumableSearchRunner (Machine Reached)
open Eval DeclarativeSpec BridgeKit WireKit
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open SpaceSemantics (Program)

abbrev spec := Emission.spec

def advanceCall (machine : Complete.Classes.Machine plan) (ticks quantum : Nat) : OSLFCore.Atom :=
  apply "gslt:runner:advance"
    [CompleteExecution.classSearchBackend, CompleteExecution.planValue plan plan.snapshot.freeTypes [] (.base "ErMailboxConfig"),
      encoded (StandardWire.commitTerm plan .canonical (CompleteEmission.table spec)),
      number ticks, number quantum, encoded (CompleteExecution.classMachineTerm plan machine)]

theorem begin_returns {name : String} {emitted : Program}
    (ok : CompleteEmission.emit? spec name .classes = .ok emitted)
    (state : State) (source : Pattern) (typed : Model.Sorted source) :
    PureReturns (CompleteEmission.runtime.append emitted) [] state
      (apply (CompleteEmission.beginHead name) [CompleteExecution.patternValue source]) state
      (encoded (CompleteExecution.classMachineTerm plan (CompleteEmission.begun spec source))) := by
  obtain ⟨rfl, admitted⟩ := CompleteEmission.emit?_ok ok
  have footprinted : CompleteEmission.Footprinted spec := CompleteEmission.footprinted_of_compiled admitted
  have checked : Complete.Classes.Checked plan [] (.base "ErMailboxConfig") source :=
    (Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted_eq_true_iff _ _ _ _ _).mpr typed
  have inside := Complete.Footprint.sorted_within footprinted.scope.declared checked
  have ready := CompleteExecution.commitReady_of_checked plan (mode := .canonical) (CompleteEmission.table_for spec) checked
  exact CompleteEmission.begin_entry_returns admitted.fresh footprinted state source inside ready

theorem begin_ready {name : String} {emitted : Program}
    (ok : CompleteEmission.emit? spec name .classes = .ok emitted)
    (source : Pattern) (typed : Model.Sorted source) :
    CompleteExecution.RunnerReady [] (.base "ErMailboxConfig") (Complete.Footprint.declaredFootprint plan)
      (CompleteEmission.begun spec source) := by
  have footprinted : CompleteEmission.Footprinted spec := CompleteEmission.footprinted_of_compiled (CompleteEmission.emit?_ok ok).2
  have checked : Complete.Classes.Checked plan [] (.base "ErMailboxConfig") source :=
    (Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted_eq_true_iff _ _ _ _ _).mpr typed
  exact CompleteExecution.searchReady_begin footprinted.scope
    (Complete.Normalized.commit_within plan .canonical source _
      (Complete.Footprint.sorted_within footprinted.scope.declared checked))

private theorem advance_supported {name : String} (fresh : CompleteEmission.namesFresh spec name .classes = true) :
    CompleteEmission.allowed name "gslt:runner:advance" = true := by
  have present : CompleteEmission.runtime.equations.any (·.head == "gslt:runner:advance") = true := by decide +kernel
  obtain ⟨row, member, head⟩ := List.any_eq_true.mp present
  have rowAllowed := List.all_eq_true.mp (CompleteEmission.fresh_parts fresh).2.2.2.1 row member
  have same : row.head = "gslt:runner:advance" := by simpa only [beq_iff_eq] using head
  exact same ▸ (Bool.and_eq_true_iff.mp rowAllowed).1

theorem advance_returns {name : String} {emitted : Program}
    (ok : CompleteEmission.emit? spec name .classes = .ok emitted)
    (state : State) (machine : Complete.Classes.Machine plan)
    (ready : CompleteExecution.RunnerReady [] (.base "ErMailboxConfig") (Complete.Footprint.declaredFootprint plan) machine)
    (ticks quantum : Nat) :
    PureReturns (CompleteEmission.runtime.append emitted) [] state (advanceCall machine ticks quantum) state
      (encoded (CompleteExecution.classMachineTerm plan (Machine.advance Runner.search ticks quantum machine))) := by
  obtain ⟨rfl, admitted⟩ := CompleteEmission.emit?_ok ok
  have footprinted : CompleteEmission.Footprinted spec := CompleteEmission.footprinted_of_compiled admitted
  have original := CompleteExecution.runner_advance_returns plan state .canonical (CompleteEmission.table spec)
    (CompleteEmission.table_for spec) plan.snapshot.freeTypes [] (.base "ErMailboxConfig")
    (Complete.Footprint.declaredFootprint plan) footprinted.tabled footprinted.scope quantum ticks machine ready
  let args := [CompleteExecution.classSearchBackend,
    CompleteExecution.planValue plan plan.snapshot.freeTypes [] (.base "ErMailboxConfig"),
    encoded (StandardWire.commitTerm plan .canonical (CompleteEmission.table spec)), number ticks, number quantum,
    encoded (CompleteExecution.classMachineTerm plan machine)]
  let names := ["backend", "plan", "standard", "ticks", "quantum", "machine"]
  apply captured_call_in_extension (CompleteEmission.runtime_closed admitted.fresh) CompleteEmission.runtime_agreement
    [] (names.zip args) state state "gslt:runner:advance" args names _
    (advance_supported admitted.fresh) (by decide) (by decide +kernel) (by decide)
  · intro offset argument found
    have bound : offset < 6 := by
      have length := (List.getElem?_eq_some_iff.mp found).1
      simpa only [args, List.length_cons, List.length_nil] using length
    exact Or.inl (CompleteEmission.runtime_raw "gslt:runner:advance" 6 (by decide +kernel) offset bound)
  · simp [args, names, Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
      Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup,
      CettaWireAtom.applySubst_encode, encoded, number, CettaWireAtom.encode]
  · exact original

theorem advance_ready {name : String} {emitted : Program}
    (ok : CompleteEmission.emit? spec name .classes = .ok emitted)
    (machine : Complete.Classes.Machine plan)
    (ready : CompleteExecution.RunnerReady [] (.base "ErMailboxConfig") (Complete.Footprint.declaredFootprint plan) machine)
    (ticks quantum : Nat) :
    CompleteExecution.RunnerReady [] (.base "ErMailboxConfig") (Complete.Footprint.declaredFootprint plan)
      (Machine.advance Runner.search ticks quantum machine) := by
  have footprinted : CompleteEmission.Footprinted spec := CompleteEmission.footprinted_of_compiled (CompleteEmission.emit?_ok ok).2
  induction ticks generalizing machine with
  | zero => exact ready
  | succ ticks ih =>
      exact ih _ (CompleteExecution.runner_ready_tick footprinted.scope .canonical ready quantum)

theorem completed_advance_readback {name : String} {emitted : Program}
    (ok : CompleteEmission.emit? spec name .classes = .ok emitted)
    (state after : State) (machine : Complete.Classes.Machine plan)
    (ready : CompleteExecution.RunnerReady [] (.base "ErMailboxConfig") (Complete.Footprint.declaredFootprint plan) machine)
    (ticks quantum : Nat) (observed : Term)
    (read : Runs (CompleteEmission.runtime.append emitted)
      {state := state, control := .evaluate [] (advanceCall machine ticks quantum)}
      (.complete after [encoded observed] [] [])) :
    observed = CompleteExecution.classMachineTerm plan (Machine.advance Runner.search ticks quantum machine) := by
  have actual := advance_returns ok state machine ready ticks quantum
  have values := (pure_returns_derivation_iff (CompleteEmission.runtime.append emitted)
    [] state state _ _ actual after _ [] []).mp read |>.2.1
  exact CettaWireAtom.encode_injective _ _ (List.cons.inj values).1

theorem completed_answer_readback {name : String} {emitted : Program}
    (ok : CompleteEmission.emit? spec name .classes = .ok emitted)
    (state after : State) {source answer : Pattern} (settles : Settles Runner.base source answer)
    (machine : Complete.Classes.Machine plan) (reached : Reached Runner.search machine)
    (origin : Path Runner.base source machine.state)
    (canonical : CanonicalBags.canon machine.state = machine.state) (typed : Model.Sorted machine.state)
    (ready : CompleteExecution.RunnerReady [] (.base "ErMailboxConfig") (Complete.Footprint.declaredFootprint plan) machine)
    (ticks quantum : Nat) (target query states receipts : Term)
    (read : Runs (CompleteEmission.runtime.append emitted)
      {state := state, control := .evaluate [] (advanceCall machine ticks quantum)}
      (.complete after [encoded (.application "ClassMachine" [.symbol "ClassDone", target, query, states, receipts])] [] [])) :
    target = InferenceCettaWire.encodePattern answer := by
  have observed := completed_advance_readback ok state after machine ready ticks quantum _ read
  have fields := (Term.application.inj observed).2
  obtain ⟨phase, rest⟩ := List.cons.inj fields
  obtain ⟨value, _⟩ := List.cons.inj rest
  have done : (Machine.advance Runner.search ticks quantum machine).phase = .done := by
    cases actual : (Machine.advance Runner.search ticks quantum machine).phase <;>
      simp_all [CompleteExecution.classPhaseSymbol]
  have correct := Runner.advance_done_value settles reached origin canonical typed ticks quantum done
  exact value.trans (congrArg InferenceCettaWire.encodePattern correct)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangMailboxMachineExecution
