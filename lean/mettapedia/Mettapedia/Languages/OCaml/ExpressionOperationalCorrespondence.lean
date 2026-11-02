import Mettapedia.Languages.OCaml.TreeEvaluationEquivalence
import Mettapedia.Languages.OCaml.ExpressionAssemblyCorrectness

/-! Two-sided finite operational correspondence for the actual assembler.
Closure results are related by body readings and captures. Literal and fault
observations agree exactly, independent of internal code addresses. -/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml.ExpressionTree

theorem assembled_evaluation_iff (tree : ExpressionTree) (constructors : List Constructor) (result : TreeResult) :
    TreeEvaluates constructors [] tree result ↔
      ∃ actual, Evaluates (tree.assemble constructors) [] (tree.assemble constructors).entry actual ∧
        TreeResultRelated (tree.assemble constructors).code result actual :=
  tree_evaluation_iff (tree.assemble constructors) (assembled_reads tree constructors) .nil result

theorem assembled_evaluation {tree : ExpressionTree} {constructors : List Constructor} {result : TreeResult}
    (evaluated : TreeEvaluates constructors [] tree result) :
    ∃ actual, Evaluates (tree.assemble constructors) [] (tree.assemble constructors).entry actual ∧
      TreeResultRelated (tree.assemble constructors).code result actual := by
  apply evaluated.toIndexed (tree.assemble constructors) (assembled_reads tree constructors) .nil

theorem assembled_reflection {tree : ExpressionTree} {constructors : List Constructor} {actual : Result}
    (evaluated : Evaluates (tree.assemble constructors) [] (tree.assemble constructors).entry actual) :
    ∃ result, TreeEvaluates constructors [] tree result ∧ TreeResultRelated (tree.assemble constructors).code result actual :=
  evaluated.toTree (tree.assemble constructors) (assembled_reads tree constructors) .nil

theorem assembled_literal_iff (tree : ExpressionTree) (constructors : List Constructor) (literal : Literal) :
    Evaluates (tree.assemble constructors) [] (tree.assemble constructors).entry (.ok (.literal literal)) ↔
      TreeEvaluates constructors [] tree (.ok (.literal literal)) := by
  constructor
  · intro evaluated
    exact TreeResultRelated.literalWitness_back (assembled_reflection evaluated)
  · intro evaluated
    exact TreeResultRelated.literalWitness (assembled_evaluation evaluated)

theorem assembled_fault_iff (tree : ExpressionTree) (constructors : List Constructor) (error : Fault) :
    Evaluates (tree.assemble constructors) [] (tree.assemble constructors).entry (.error error) ↔
      TreeEvaluates constructors [] tree (.error error) := by
  constructor
  · intro evaluated
    exact TreeResultRelated.faultWitness_back (assembled_reflection evaluated)
  · intro evaluated
    exact TreeResultRelated.faultWitness (assembled_evaluation evaluated)

#print axioms assembled_evaluation
#print axioms assembled_evaluation_iff
#print axioms assembled_reflection
#print axioms assembled_literal_iff
#print axioms assembled_fault_iff

end Mettapedia.Languages.OCaml.ExpressionTree
