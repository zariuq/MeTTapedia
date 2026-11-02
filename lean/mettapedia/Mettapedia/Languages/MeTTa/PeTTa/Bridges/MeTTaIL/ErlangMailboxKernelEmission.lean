import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangMailboxKernelSource

/-! Source rendering of the actual mailbox entry program. Every successful
render reads back as exactly the program used by its execution proofs. -/

set_option autoImplicit false
set_option maxRecDepth 32768

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangMailboxKernelEmission

open ErlangMailboxKernelSource

def render? : Option String := ReadAfterRender.renderProgram? program

theorem loaded_exact : SpaceSemantics.loadedAtoms program =
    [CompleteEmission.declaration "gslt:er-rho:mailbox-begin" 1, beginEquation.toAtom,
      .expression [.symbol ":", .symbol "gslt:er-rho:mailbox-resume",
        .expression [.symbol "->", .symbol "Number", .symbol "Number", .symbol "Atom", .symbol "%Undefined%"]],
      resumeEquation.toAtom, CompleteEmission.declaration "gslt:er-rho:mailbox-kernel" 1, kernelEquation.toAtom] := rfl

theorem rendered_reads_back {text : String} (rendered : render? = some text) :
    SpaceSemantics.readProgram text = .ok program := by
  have expressions : ReadAfterRender.AllExpressions (SpaceSemantics.loadedAtoms program) := by
    rw [loaded_exact]
    intro atom member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
  rw [ReadAfterRender.read_render rendered expressions, loaded_exact]
  rfl

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangMailboxKernelEmission
