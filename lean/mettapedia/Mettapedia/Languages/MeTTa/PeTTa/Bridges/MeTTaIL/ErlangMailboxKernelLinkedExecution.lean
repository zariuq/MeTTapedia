import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangMailboxKernelExecution

/-! The generated mailbox kernel executes unchanged after the rho, actor
and portable libraries are loaded in their checked order. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangMailboxKernelLinkedExecution

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox
open Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox.Execution
open Mettapedia.Machines.ResumableSearchRunner (Machine)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit
open ErlangMailboxKernelSource (spec)

def result (source : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) : Term :=
  ErlangMailboxKernelExecution.resultTerm
    (Machine.advance Runner.search 2000 2 (CompleteEmission.begun spec source))

theorem rho_returns (state : State) (source : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (typed : Model.Sorted source) :
    PureReturns ErlangActorLinkedSource.rhoLibrary.runtime [] state
      (apply "gslt:er-rho:mailbox-kernel" [CompleteExecution.patternValue source]) state
      (encoded (result source)) := by
  metta_lift ErlangActorLinkedSource.rho_checked ["source"]
    (ErlangMailboxKernelExecution.kernel_returns state source typed)

theorem actor_returns (state : State) (source : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (typed : Model.Sorted source) :
    PureReturns ErlangActorLinkedSource.runtime [] state
      (apply "gslt:er-rho:mailbox-kernel" [CompleteExecution.patternValue source]) state
      (encoded (result source)) := by
  metta_lift ErlangActorLinkedSource.actor_checked ["source"]
    (rho_returns state source typed)

theorem portable_returns (state : State) (source : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (typed : Model.Sorted source) :
    PureReturns ErlangActorLinkedSource.portableRuntime [] state
      (apply "gslt:er-rho:mailbox-kernel" [CompleteExecution.patternValue source]) state
      (encoded (result source)) := by
  metta_lift ErlangActorLinkedSource.portable_checked ["source"]
    (actor_returns state source typed)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangMailboxKernelLinkedExecution
