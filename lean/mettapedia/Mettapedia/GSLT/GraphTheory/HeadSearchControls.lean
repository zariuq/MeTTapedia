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

/-- Exact counterexample to unqualified fixed-budget beta invariance. -/
theorem bounded_beta_equality_fails :
    let argument := LambdaTerm.app LambdaTerm.I (.app LambdaTerm.I LambdaTerm.I)
    bohmTree 1 (.app (.lam (.var 0)) argument) ≠
      bohmTree 1 (argument.subst 0 (.var 0)) :=
  reduction_changes_bounded_tree.2

/-! ### Fixed-budget equality is not a congruence

`λx. I x` needs one head step more than `I`. Alone, both are observed
identically at every depth. In a context that leaves exactly enough fuel for
`I`, the extra step exhausts the budget. So equality of the fixed-budget
observations is closed neither under application nor under substitution.
-/

private theorem bohmTree_succ_eq {d fuel : Nat} {t hnf : LambdaTerm} {numLams head : Nat}
    {arguments : List LambdaTerm} (search : toHNF fuel t = some hnf)
    (enough : fuel ≤ (d + 1) * (d + 1 + 1) + 1)
    (headForm : extractHNF hnf = some (numLams, head, arguments)) :
    bohmTree (d + 1) t = .node numLams head (arguments.map (bohmTree d)) := by
  simp only [bohmTree, toHNF_result_stable search enough, headForm]

/-- `I` and `λx. I x` have the same fixed-budget observation at every depth. -/
theorem searchTreeEqual_identity_expansion :
    SearchTreeEqual LambdaTerm.I (.lam (.app LambdaTerm.I (.var 0))) := by
  intro n
  cases n with
  | zero => rfl
  | succ d =>
      have positive : 0 < (d + 1) * (d + 1 + 1) := Nat.mul_pos (Nat.succ_pos d) (Nat.succ_pos _)
      rw [bohmTree_succ_eq (show toHNF 1 LambdaTerm.I = some LambdaTerm.I from rfl) (by omega)
          (show extractHNF LambdaTerm.I = some (1, 0, []) from rfl),
        bohmTree_succ_eq
          (show toHNF 2 (.lam (.app LambdaTerm.I (.var 0))) = some LambdaTerm.I from rfl)
          (by omega) (show extractHNF LambdaTerm.I = some (1, 0, []) from rfl)]

/-- Fixed-budget equality is not closed under application to an argument. -/
theorem searchTreeEqual_not_app_left_congruence :
    ¬∀ function function' argument : LambdaTerm, SearchTreeEqual function function' →
      SearchTreeEqual (.app function argument) (.app function' argument) := by
  intro congruence
  have observed := congruence _ _ (.app LambdaTerm.I LambdaTerm.I)
    searchTreeEqual_identity_expansion 1
  change (BohmTree.node 1 0 [] : BohmTree) = .bot at observed
  cases observed

/-- Fixed-budget equality is not closed under application of a function. -/
theorem searchTreeEqual_not_app_right_congruence :
    ¬∀ function argument argument' : LambdaTerm, SearchTreeEqual argument argument' →
      SearchTreeEqual (.app function argument) (.app function argument') := by
  intro congruence
  have observed := congruence (.lam (.app LambdaTerm.I (.var 0))) _ _
    searchTreeEqual_identity_expansion 1
  change (BohmTree.node 1 0 [] : BohmTree) = .bot at observed
  cases observed

/-- Fixed-budget equality is not closed under substitution. -/
theorem searchTreeEqual_not_subst_congruence :
    ¬∀ body argument argument' : LambdaTerm, SearchTreeEqual argument argument' →
      SearchTreeEqual (argument.subst 0 body) (argument'.subst 0 body) := by
  intro congruence
  have observed := congruence (.app LambdaTerm.I (.app LambdaTerm.I (.var 0))) _ _
    searchTreeEqual_identity_expansion 1
  change (BohmTree.node 1 0 [] : BohmTree) = .bot at observed
  cases observed

end Mettapedia.GSLT.GraphTheory
