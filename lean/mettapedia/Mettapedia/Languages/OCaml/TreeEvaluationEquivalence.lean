import Mettapedia.Languages.OCaml.TreeEvaluationReflection
import Mettapedia.Languages.OCaml.TreeValueReadback

/-! Evaluation equivalence for each exact tree result, including compound
values and closures. Uniqueness of indexed-value readback closes the reverse
direction without treating physical function addresses as source values. -/

set_option autoImplicit false

namespace Mettapedia.Languages.OCaml

theorem tree_evaluation_iff (program : Program) {environment : TreeEnvironment} {values : Environment}
    {tree : ExpressionTree} {code : Code} (read : ExpressionTree.Reads program.code tree code)
    (captures : TreeValuesRelated program.code environment values) (result : TreeResult) :
    TreeEvaluates program.constructors environment tree result ↔
      ∃ actual, Evaluates program values code actual ∧ TreeResultRelated program.code result actual := by
  constructor
  · intro evaluated
    exact evaluated.toIndexed program read captures
  · rintro ⟨actual, evaluated, related⟩
    obtain ⟨source, recovered, aligned⟩ := evaluated.toTree program read captures
    have same := related.left_unique aligned
    exact same.symm ▸ recovered

#print axioms tree_evaluation_iff

end Mettapedia.Languages.OCaml
