import Mettapedia.GSLT.GraphTheory.BohmTree

/-! Controls separating actual reduction, bounded head search, and unsolvability. -/

namespace Mettapedia.GSLT.GraphTheory

/-- A reduced identity is recognized and has actual solvability evidence. -/
theorem identity_redex_head_search :
    toHNF 2 (.app LambdaTerm.I LambdaTerm.I) = some LambdaTerm.I ∧
      (LambdaTerm.app LambdaTerm.I LambdaTerm.I).Solvable := by
  refine ⟨rfl, ?_⟩
  exact solvable_of_toHNF (fuel := 2) (hnf := LambdaTerm.I) rfl

/-- Exhausting the current budget cannot establish unsolvability. -/
theorem exhausted_identity_is_solvable :
    toHNF 1 (.app LambdaTerm.I LambdaTerm.I) = none ∧
      (LambdaTerm.app LambdaTerm.I LambdaTerm.I).Solvable :=
  ⟨rfl, identity_redex_head_search.2⟩

/-- Actual Omega unsolvability forbids success at any finite budget. -/
theorem Omega_head_search_fails (fuel : Nat) :
    toHNF fuel LambdaTerm.Omega = none :=
  unsolvable_toHNF_none Omega_unsolvable fuel

/-- Real β reduction can change a fixed-budget tree observation. -/
theorem reduction_changes_bounded_tree :
    let reduct := LambdaTerm.app LambdaTerm.I (.app LambdaTerm.I LambdaTerm.I)
    ((.app LambdaTerm.I reduct) ⇛ reduct) ∧
      bohmTree 1 (.app LambdaTerm.I reduct) ≠ bohmTree 1 reduct := by
  dsimp only
  constructor
  · exact ParRed.beta (ParRed.refl (.var 0))
      (ParRed.refl (.app LambdaTerm.I (.app LambdaTerm.I LambdaTerm.I)))
  · change (BohmTree.bot : BohmTree) ≠ .node 1 0 []
    intro h
    cases h

/-- Exact counterexample to the existing admitted bounded beta-invariance law. -/
theorem bounded_beta_equality_fails :
    let argument := LambdaTerm.app LambdaTerm.I (.app LambdaTerm.I LambdaTerm.I)
    bohmTree 1 (.app (.lam (.var 0)) argument) ≠
      bohmTree 1 (argument.subst 0 (.var 0)) :=
  reduction_changes_bounded_tree.2

end Mettapedia.GSLT.GraphTheory
