import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangMailboxMachineExecution

/-! Generated mailbox entry bodies as a shared program. The native generator
renders these same bodies, and the execution proofs consume them directly.
A resumed kernel retains the entire class machine, including pending work. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 2000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangMailboxKernelSource

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics (Program)
open Eval BridgeKit

abbrev spec := ErlangMailboxMachineExecution.spec
def name : String := "er-mailbox-rho"

def emitted : Program := CompleteEmission.program spec name .classes

def a (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
def v (name : String) : Atom := .var name

def beginBody : Atom :=
  a "let" [v "initial", a (CompleteEmission.beginHead name) [v "source"],
    a "ErRhoKernelPending" [v "initial"]]

def resumeBody : Atom :=
  a "case" [v "result", .expression [
    .expression [a "ErRhoKernelPending" [v "machine"],
      a "let*" [.expression [
        .expression [v "plan", a "quote" [CompleteEmission.planAtom spec]],
        .expression [v "standard", a "quote" [CompleteEmission.standardAtom spec]],
        .expression [v "finished", a "gslt:runner:advance"
          [CompleteExecution.classSearchBackend, v "plan", v "standard", v "ticks", v "quantum", v "machine"]]],
        a "case" [v "finished", .expression [
          .expression [a "ClassMachine" [.symbol "ClassDone", v "target", v "query", v "states", v "receipts"],
            a "ErRhoKernelDone" [v "target", v "finished"]],
          .expression [v "pending", a "ErRhoKernelPending" [v "pending"]]]]]],
    .expression [v "stopped", v "stopped"]]]

def kernelBody : Atom :=
  a "let" [v "initial", a "gslt:er-rho:mailbox-begin" [v "source"],
    a "gslt:er-rho:mailbox-resume" [.grounded (.int 2000), .grounded (.int 2), v "initial"]]

def beginEquation : SpaceSemantics.Equation := ⟨"gslt:er-rho:mailbox-begin", [v "source"], beginBody⟩
def resumeEquation : SpaceSemantics.Equation := ⟨"gslt:er-rho:mailbox-resume", [v "ticks", v "quantum", v "result"], resumeBody⟩
def kernelEquation : SpaceSemantics.Equation := ⟨"gslt:er-rho:mailbox-kernel", [v "source"], kernelBody⟩

def program : Program where
  equations := [beginEquation, resumeEquation, kernelEquation]
  declarations := [CompleteEmission.declaration "gslt:er-rho:mailbox-begin" 1,
    .expression [.symbol ":", .symbol "gslt:er-rho:mailbox-resume",
      .expression [.symbol "->", .symbol "Number", .symbol "Number", .symbol "Atom", .symbol "%Undefined%"]],
    CompleteEmission.declaration "gslt:er-rho:mailbox-kernel" 1]
  layout := [.declaration, .equation, .declaration, .equation, .declaration, .equation]


end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangMailboxKernelSource
