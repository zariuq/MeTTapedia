import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceLowering
import Mettapedia.Languages.OCaml.ExpressionDecoding

/-! The actual source frontend exposes its tree before assembly. Successful
program lowering preserves that tree's declaration list and instruction
graph, and the independent decoder recovers exactly that tree. Source-to-tree
binding and operational adequacy remain separate proof obligations. -/

set_option autoImplicit false
set_option maxRecDepth 32768

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceLowering

open Mettapedia.Languages

theorem lower_tree_readback {input : String} {source : SourcePacket.Packet} {program : OCaml.Program}
    (built : lower input source = .ok program) :
    ∃ tree : OCaml.TreeProgram, lowerTree input source = .ok tree ∧ program = OCaml.TreeProgram.assemble tree ∧ program.checkScope = true := by
  exact Except.checkedMap_ok built

theorem lower_graph_readback {input : String} {source : SourcePacket.Packet} {program : OCaml.Program}
    (built : lower input source = .ok program) :
    ∃ tree, lowerTree input source = .ok tree ∧ program.constructors = tree.constructors ∧
      OCaml.ExpressionTree.Reads program.code tree.expression program.entry ∧
      OCaml.ExpressionTree.readFuel program.code (sizeOf tree.expression + 1) program.entry = some tree.expression := by
  obtain ⟨tree, parsed, rfl, _⟩ := lower_tree_readback built
  refine ⟨tree, parsed, ?_, ?_, ?_⟩
  · simpa only [OCaml.TreeProgram.assemble] using
      OCaml.ExpressionTree.assemble_preserves_declarations tree.expression tree.constructors
  · simpa only [OCaml.TreeProgram.assemble] using OCaml.ExpressionTree.assembled_reads tree.expression tree.constructors
  · simpa only [OCaml.TreeProgram.assemble] using OCaml.ExpressionTree.assembled_readback tree.expression tree.constructors

#print axioms lower_tree_readback
#print axioms lower_graph_readback

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceLowering
