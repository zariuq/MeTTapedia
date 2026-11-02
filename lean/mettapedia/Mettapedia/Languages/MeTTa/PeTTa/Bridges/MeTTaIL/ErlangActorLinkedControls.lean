import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorLinkedSource

/-! The actual linked extensions satisfy the namespace contract. Moving the
kernel after its callers or assigning the whole rho namespace to a later
layer fails that contract; these are concrete nonempty program controls. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorLinkedControls

open BridgeKit Eval SpaceSemantics
open ErlangActorLinkedSource

private theorem rejected_base_row (library : Library) (row : Equation)
    (member : row ∈ library.base.equations)
    (rejected : (library.inherited row.head && codeWithin library.inherited row.body) = false) :
    library.check = false := by
  apply Bool.eq_false_iff.mpr
  intro checked
  simp only [Library.check, Bool.and_eq_true] at checked
  have accepted := List.all_eq_true.mp checked.1.1.2 row member
  rw [rejected] at accepted
  cases accepted

def lateKernel : Library := ⟨ErlangControllerSource.runtime, ErlangMailboxKernelSource.program, kernelPrefixes⟩
def wideRho : Library := ⟨kernelLibrary.runtime, ErlangControllerSource.rhoSource.program, ["gslt:er-rho:"]⟩

theorem late_kernel_rejected : lateKernel.check = false := by
  let row := ErlangControllerSource.rhoSource.program.equations[0]'(by decide +kernel)
  apply rejected_base_row lateKernel row
  · exact List.mem_append_left _ (List.mem_append_right _ (List.getElem_mem _))
  · decide +kernel

theorem wide_rho_rejected : wideRho.check = false := by
  apply rejected_base_row wideRho ErlangMailboxKernelSource.beginEquation
  · exact List.mem_append_right _ (List.mem_cons_self ..)
  · decide +kernel

theorem extensions_checked : emittedLibrary.check = true ∧ kernelLibrary.check = true ∧ rhoLibrary.check = true ∧
    actorLibrary.check = true ∧ portableLibrary.check = true :=
  ⟨emitted_checked, kernel_checked, rho_checked, actor_checked, portable_checked⟩

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorLinkedControls
