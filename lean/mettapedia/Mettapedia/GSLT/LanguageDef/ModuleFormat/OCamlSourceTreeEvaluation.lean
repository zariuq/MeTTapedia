import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceTreeAssembly
import Mettapedia.Languages.OCaml.ExpressionOperationalCorrespondence

/-! Successful ordinary-source lowering retains the produced expression tree
and its two-sided finite operational meaning. Raw syntax-to-tree binding
adequacy is a separate boundary. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceLowering

open Mettapedia.Languages

theorem lower_tree_graph {input : String} {source : SourcePacket.Packet} {program : OCaml.Program} {tree : OCaml.TreeProgram}
    (built : lower input source = .ok program) (parsed : lowerTree input source = .ok tree) :
    program.constructors = tree.constructors ∧ OCaml.ExpressionTree.Reads program.code tree.expression program.entry := by
  obtain ⟨actual, lowered, constructors, read, _⟩ := lower_graph_readback built
  have same := Except.ok.inj (parsed.symm.trans lowered)
  subst actual
  exact ⟨constructors, read⟩

theorem lower_evaluation_iff {input : String} {source : SourcePacket.Packet} {program : OCaml.Program} {tree : OCaml.TreeProgram}
    (built : lower input source = .ok program) (parsed : lowerTree input source = .ok tree) (result : OCaml.TreeResult) :
    OCaml.TreeEvaluates tree.constructors [] tree.expression result ↔
      ∃ actual, OCaml.Evaluates program [] program.entry actual ∧ OCaml.TreeResultRelated program.code result actual := by
  obtain ⟨constructors, read⟩ := lower_tree_graph built parsed
  simpa only [constructors] using OCaml.tree_evaluation_iff program read .nil result

theorem lower_operational_readback {input : String} {source : SourcePacket.Packet} {program : OCaml.Program}
    (built : lower input source = .ok program) :
    ∃ tree : OCaml.TreeProgram, lowerTree input source = .ok tree ∧ program.constructors = tree.constructors ∧
      (∀ result, OCaml.TreeEvaluates tree.constructors [] tree.expression result →
        ∃ actual, OCaml.Evaluates program [] program.entry actual ∧ OCaml.TreeResultRelated program.code result actual) ∧
      (∀ actual, OCaml.Evaluates program [] program.entry actual →
        ∃ result, OCaml.TreeEvaluates tree.constructors [] tree.expression result ∧ OCaml.TreeResultRelated program.code result actual) := by
  obtain ⟨tree, parsed, constructors, read, _⟩ := lower_graph_readback built
  refine ⟨tree, parsed, constructors, ?_, ?_⟩
  · intro result evaluated
    exact (constructors ▸ evaluated).toIndexed program read .nil
  · intro actual evaluated
    simpa only [constructors] using evaluated.toTree program read .nil

#print axioms lower_operational_readback
#print axioms lower_tree_graph
#print axioms lower_evaluation_iff

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceLowering
