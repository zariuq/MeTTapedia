import Mettapedia.Languages.OCaml.ExpressionDecoding
import Mettapedia.Languages.OCaml.AssemblyEvaluationExtension

/-! Assembly preserves operand/clause order and existing closures. An
operand swap cannot describe the allocated code, and replacing an old
instruction is refused by the append-only contract. -/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml.ExpressionAssemblyControls

open ExpressionTree Assembly

private def ordered : ExpressionTree := .primitive .subtract [.integer 1, .integer 2]
private def swapped : ExpressionTree := .primitive .subtract [.integer 2, .integer 1]
private def oldArena : Array Instruction := #[.literal (.integer 7), .lambda .bind 0]

theorem ordered_reads : Reads (ordered.assemble []).code ordered (ordered.assemble []).entry :=
  assembled_reads ordered []

theorem swapped_operands_refused : ¬ Reads (ordered.assemble []).code swapped (ordered.assemble []).entry := by
  intro changed
  have same := Reads.unique ordered_reads changed
  have fields := (ExpressionTree.primitive.inj same).2
  have head := (List.cons.inj fields).1
  simp [ExpressionTree.integer] at head

theorem compiled_code_reads_back (tree : ExpressionTree) (constructors : List Constructor) :
    readFuel (tree.assemble constructors).code (sizeOf tree + 1) (tree.assemble constructors).entry = some tree :=
  assembled_readback tree constructors

theorem old_closure_applies : Applies ⟨[], oldArena, 1⟩ (.closure (.lambda 1) []) (.literal (.integer 0))
    (.ok (.literal (.integer 7))) :=
  .lambda rfl rfl (.literal rfl)

theorem allocation_preserves_closure (tree : ExpressionTree) :
    Applies ⟨[], (tree.compile.run oldArena).2, 1⟩ (.closure (.lambda 1) []) (.literal (.integer 0))
      (.ok (.literal (.integer 7))) :=
  (compile_correct tree oldArena).1.applies [] 1 old_closure_applies

theorem overwriting_old_code_refused :
    ¬ Extension oldArena #[.literal (.integer 99), .lambda .bind 0] := by
  intro changed
  have same := changed.kept 0 (by decide)
  simp [oldArena] at same

#print axioms ordered_reads
#print axioms swapped_operands_refused
#print axioms compiled_code_reads_back
#print axioms old_closure_applies
#print axioms allocation_preserves_closure
#print axioms overwriting_old_code_refused

end Mettapedia.Languages.OCaml.ExpressionAssemblyControls
