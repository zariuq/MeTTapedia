import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangMailboxKernelSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmissionCodeSupport

/-! The mailbox entry program separates a fixed call vocabulary from its
parametric plan data. Later library checks need no repeated plan expansion. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangMailboxKernelCodeSupport

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Eval ErlangMailboxKernelSource

def heads : List String := ["let", "let*", "quote", "case", "ErRhoKernelPending", "ErRhoKernelDone",
  "ClassMachine", "gslt:runner:advance", CompleteEmission.beginHead name,
  "gslt:er-rho:mailbox-begin", "gslt:er-rho:mailbox-resume"]

theorem bodies_supported (allowed : String → Bool) (wire : WirePlanSupport.Supported allowed)
    (checked : heads.all allowed = true) :
    program.equations.all (fun equation => codeWithin allowed equation.body) = true := by
  have plan := CompleteEmissionCodeSupport.plan_supported spec allowed wire
  have normal := CompleteEmissionCodeSupport.canonical_supported spec allowed wire rfl
  simp only [heads, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at checked
  obtain ⟨letAllowed, letStarAllowed, quoteAllowed, caseAllowed, pendingAllowed, doneAllowed, machineAllowed,
    advanceAllowed, beginAllowed, kernelBeginAllowed, kernelResumeAllowed⟩ := checked
  simp only [program, List.all_cons, List.all_nil, Bool.and_true, beginEquation, resumeEquation, kernelEquation,
    beginBody, resumeBody, kernelBody, a, v, codeWithin, expressionHeadWithin, atomsWithin,
    CompleteExecution.classSearchBackend, plan, normal, letAllowed, letStarAllowed, quoteAllowed, caseAllowed,
    pendingAllowed, doneAllowed, machineAllowed, advanceAllowed, beginAllowed, kernelBeginAllowed, kernelResumeAllowed,
    Bool.true_and, Bool.and_true]
  decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangMailboxKernelCodeSupport
