import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorLinkedTransport
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangMailboxKernelAdmission
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.BridgeEval
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.BridgeDemandEval

/-! The actual generated mailbox begin/resume/kernel entries run the shared
canonical class machine. Input conditions come from the source-value
admission owner; incomplete work remains a complete pending machine. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangMailboxKernelExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox
open Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox.Execution
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Machines.ResumableSearchRunner (Machine)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit
open ErlangMailboxKernelSource (spec name emitted)

abbrev baseRuntime := ErlangActorLinkedSource.emittedLibrary.runtime
abbrev kernelRuntime := ErlangActorLinkedSource.kernelLibrary.runtime

theorem emitted_begin_returns (state : State) (source : Pattern) (typed : Model.Sorted source) :
    PureReturns baseRuntime [] state
      (apply (CompleteEmission.beginHead name) [CompleteExecution.patternValue source]) state
      (encoded (CompleteExecution.classMachineTerm plan (CompleteEmission.begun spec source))) := by
  have actual := ErlangMailboxMachineExecution.begin_returns ErlangMailboxKernelAdmission.emitted_ok state source typed
  apply captured_call_in_extension ErlangActorLinkedTransport.closed ErlangActorLinkedTransport.agreement
    [] (Library.bind ["source"] [CompleteExecution.patternValue source]) state state (CompleteEmission.beginHead name)
    [CompleteExecution.patternValue source] ["source"] _
    (by decide +kernel) (by decide) (by decide +kernel) (by decide)
  · intro offset argument found
    have bound : offset < 1 := (List.getElem?_eq_some_iff.mp found).1
    have zero : offset = 0 := by omega
    subst offset
    exact Or.inl (by decide +kernel)
  · simp [Library.bind, CompleteExecution.patternValue, encoded, CettaWireAtom.applySubst_encode,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
      Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup]
  · exact actual

theorem advance_returns (state : State) (machine : Complete.Classes.Machine plan)
    (ready : CompleteExecution.RunnerReady [] (.base "ErMailboxConfig") (Complete.Footprint.declaredFootprint plan) machine)
    (ticks quantum : Nat) :
    PureReturns baseRuntime [] state (ErlangMailboxMachineExecution.advanceCall machine ticks quantum) state
      (encoded (CompleteExecution.classMachineTerm plan (Machine.advance Runner.search ticks quantum machine))) := by
  have actual := ErlangMailboxMachineExecution.advance_returns ErlangMailboxKernelAdmission.emitted_ok state machine ready ticks quantum
  let args := [CompleteExecution.classSearchBackend,
    CompleteExecution.planValue plan plan.snapshot.freeTypes [] (.base "ErMailboxConfig"),
    encoded (StandardWire.commitTerm plan .canonical (CompleteEmission.table spec)), number ticks, number quantum,
    encoded (CompleteExecution.classMachineTerm plan machine)]
  let names := ["backend", "plan", "standard", "ticks", "quantum", "machine"]
  apply captured_call_in_extension ErlangActorLinkedTransport.closed ErlangActorLinkedTransport.agreement
    [] (Library.bind names args) state state "gslt:runner:advance" args names _
    (by decide +kernel) (by decide) (by decide +kernel) (by decide)
  · intro offset argument found
    have bound : offset < 6 := (List.getElem?_eq_some_iff.mp found).1
    apply Or.inl
    have agreement : ProgramAgreementOn (CompleteEmission.allowed name) CompleteEmission.runtime
        ErlangActorLinkedTransport.minimal := CompleteEmission.runtime_agreement (spec := spec) (profile := .classes)
    rw [← agreement.demand "gslt:runner:advance" offset (by decide +kernel)]
    exact CompleteEmission.runtime_raw "gslt:runner:advance" 6 (by decide +kernel) offset bound
  · simp [args, names, Library.bind, CettaWireAtom.applySubst_encode, encoded, number, CettaWireAtom.encode,
      Mettapedia.Languages.ProcessCalculi.MORK.applySubst,
      Mettapedia.Languages.ProcessCalculi.MORK.Subst.lookup]
  · exact actual

theorem begin_returns (state : State) (source : Pattern) (typed : Model.Sorted source) :
    PureReturns kernelRuntime [] state (apply "gslt:er-rho:mailbox-begin" [CompleteExecution.patternValue source]) state
      (encoded (.application "ErRhoKernelPending"
        [CompleteExecution.classMachineTerm plan (CompleteEmission.begun spec source)])) := by
  have started : PureReturns kernelRuntime [] state
      (apply (CompleteEmission.beginHead name) [CompleteExecution.patternValue source]) state
      (encoded (CompleteExecution.classMachineTerm plan (CompleteEmission.begun spec source))) := by
    metta_lift ErlangActorLinkedSource.kernel_checked ["source"] (emitted_begin_returns state source typed)
  metta_call ErlangActorLinkedSource.kernel_checked
  metta_eval [started] with ErlangActorLinkedSource.kernel_checked

private theorem resume_call_returns (state : State) (ticks quantum : Nat) (result answer : Term)
    (body : PureReturns kernelRuntime (Library.bind ["ticks", "quantum", "result"]
      [number ticks, number quantum, encoded result]) state
      (ErlangActorLinkedSource.kernelLibrary.body "gslt:er-rho:mailbox-resume") state (encoded answer)) :
    PureReturns kernelRuntime [] state (apply "gslt:er-rho:mailbox-resume"
      [number ticks, number quantum, encoded result]) state (encoded answer) := by
  have present : (ErlangActorLinkedSource.kernelLibrary.equationOf "gslt:er-rho:mailbox-resume").isSome = true := by decide +kernel
  obtain ⟨row, found⟩ := Option.isSome_iff_exists.mp present
  have ready : Library.demandReady ErlangActorLinkedSource.kernelLibrary row = true := by
    have checked : ((ErlangActorLinkedSource.kernelLibrary.equationOf "gslt:er-rho:mailbox-resume").map
      (Library.demandReady ErlangActorLinkedSource.kernelLibrary)).getD false = true := by decide +kernel
    simpa only [found, Option.map_some, Option.getD_some] using checked
  apply Library.demand_call ErlangActorLinkedSource.kernel_checked found ready [] state state state
    [number ticks, number quantum, encoded result] [number ticks, number quantum, encoded result] _ (by metta_literal; rfl)
  · have args := ArgumentsReturn.evaluated (program := kernelRuntime) (caller := [])
      (head := "gslt:er-rho:mailbox-resume") (index := 0) (by decide +kernel)
      (number_returns kernelRuntime [] state ticks)
      (ArgumentsReturn.evaluated (index := 1) (by decide +kernel) (number_returns kernelRuntime [] state quantum)
        (ArgumentsReturn.raw (argument := encoded result) (by decide +kernel) (.nil _ _)))
    simpa only [Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil] using args
  · exact body

def resultTerm (machine : Complete.Classes.Machine plan) : Term :=
  if machine.phase = .done then .application "ErRhoKernelDone"
    [InferenceCettaWire.encodePattern machine.state, CompleteExecution.classMachineTerm plan machine]
  else .application "ErRhoKernelPending" [CompleteExecution.classMachineTerm plan machine]

theorem resume_returns (state : State) (machine : Complete.Classes.Machine plan)
    (ready : CompleteExecution.RunnerReady [] (.base "ErMailboxConfig") (Complete.Footprint.declaredFootprint plan) machine)
    (ticks quantum : Nat) :
    PureReturns kernelRuntime [] state (apply "gslt:er-rho:mailbox-resume"
      [number ticks, number quantum, encoded (.application "ErRhoKernelPending" [CompleteExecution.classMachineTerm plan machine])]) state
      (encoded (resultTerm (Machine.advance Runner.search ticks quantum machine))) := by
  have advanced : PureReturns kernelRuntime [] state (ErlangMailboxMachineExecution.advanceCall machine ticks quantum) state
      (encoded (CompleteExecution.classMachineTerm plan (Machine.advance Runner.search ticks quantum machine))) := by
    metta_lift ErlangActorLinkedSource.kernel_checked ["backend", "plan", "standard", "ticks", "quantum", "machine"]
      (advance_returns state machine ready ticks quantum)
  cases phase : (Machine.advance Runner.search ticks quantum machine).phase
  all_goals
    apply resume_call_returns
    change PureReturns kernelRuntime _ state ErlangMailboxKernelSource.resumeBody state _
    unfold ErlangMailboxKernelSource.resumeBody
    metta_eval [advanced] with ErlangActorLinkedSource.kernel_checked
      unfolding [ErlangMailboxKernelSource.a, ErlangMailboxKernelSource.v, resultTerm,
        CompleteExecution.classMachineTerm, CompleteExecution.classPhaseSymbol, phase]
  all_goals
    apply pure_let_returns _ _ _ _ _ _ _ _ rfl
    · exact Eval.quote_returns _ _ _ _
    · apply pure_let_returns _ _ _ _ _ _ _ _ rfl
      · exact Eval.quote_returns _ _ _ _
      · simp only [CompleteEmission.planAtom, CompleteEmission.standardAtom,
          CettaWireAtom.applySubst_encode]
        apply pure_let_returns _ _ _ _ _ _ _ _ rfl
        · metta_capture_any advanced unfolding [ErlangMailboxMachineExecution.advanceCall,
            ErlangMailboxKernelSource.spec, ErlangMailboxMachineExecution.spec, Emission.spec,
            CompleteExecution.classMachineTerm, CompleteExecution.classPhaseSymbol]
        · metta_eval with ErlangActorLinkedSource.kernel_checked
          unfolding [ErlangMailboxKernelSource.a, ErlangMailboxKernelSource.v,
              resultTerm, CompleteExecution.classMachineTerm, CompleteExecution.classPhaseSymbol, phase]


theorem kernel_returns (state : State) (source : Pattern) (typed : Model.Sorted source) :
    PureReturns kernelRuntime [] state (apply "gslt:er-rho:mailbox-kernel" [CompleteExecution.patternValue source]) state
      (encoded (resultTerm (Machine.advance Runner.search 2000 2 (CompleteEmission.begun spec source)))) := by
  have begun := begin_returns state source typed
  have ready := ErlangMailboxMachineExecution.begin_ready ErlangMailboxKernelAdmission.emitted_ok source typed
  have resumed := resume_returns state (CompleteEmission.begun spec source) ready 2000 2
  metta_call ErlangActorLinkedSource.kernel_checked
  metta_eval [begun, resumed] with ErlangActorLinkedSource.kernel_checked

theorem completed_kernel_readback (state after : State) (source : Pattern) (typed : Model.Sorted source)
    (observed : Term)
    (read : DeclarativeSpec.Runs kernelRuntime
      {state := state, control := .evaluate [] (apply "gslt:er-rho:mailbox-kernel" [CompleteExecution.patternValue source])}
      (.complete after [encoded observed] [] [])) :
    observed = resultTerm (Machine.advance Runner.search 2000 2 (CompleteEmission.begun spec source)) := by
  have actual := kernel_returns state source typed
  have values := (pure_returns_derivation_iff kernelRuntime [] state state _ _ actual after _ [] []).mp read |>.2.1
  exact CettaWireAtom.encode_injective _ _ (List.cons.inj values).1


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangMailboxKernelExecution
