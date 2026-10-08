import Mettapedia.CategoryTheory.FiniteActionTreeCoiteration
import Mettapedia.CategoryTheory.FinitePowersetWeakPullback

/-!
# Complete one-step observations determine a finite action tree

The quotient observes the root colour and the entire successor set of
subtree classes at each action. Equal observations generate an independently
admitted coloured relation on raw trees. This proves extensionality and
exhibits the precise absence of branch-order or occurrence recovery.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.FiniteActionTree.Tree

universe a u

variable {Actions : Type a} {Colours : Type u}

theorem ext {first second : Tree Actions Colours}
    (roots : root first = root second)
    (successors : ∀ action, step first action = step second action) : first = second := by
  let relation : Raw Actions Colours → Raw Actions Colours → Prop := fun left right =>
    root (project left) = root (project right) ∧
      ∀ action, step (project left) action = step (project right) action
  have admitted : Admitted relation := by
    intro left right held
    refine ⟨held.1, fun action => ?_⟩
    have matching := (FinitePowersetWeakPullback.related_iff_matching project project
      (FiniteActionTree.step left action) (FiniteActionTree.step right action)).2
        (held.2 action)
    constructor
    · intro value member
      obtain ⟨other, otherMember, same⟩ := matching.1 value member
      exact ⟨other, otherMember, congrArg root same,
        fun label => congrArg (fun tree => step tree label) same⟩
    · intro other member
      obtain ⟨value, valueMember, same⟩ := matching.2 other member
      exact ⟨value, valueMember, congrArg root same,
        fun label => congrArg (fun tree => step tree label) same⟩
  obtain ⟨left, leftRep⟩ := Quotient.exists_rep first
  obtain ⟨right, rightRep⟩ := Quotient.exists_rep second
  change project left = first at leftRep
  change project right = second at rightRep
  have paired : relation left right := by
    change root (project left) = root (project right) ∧ _
    rw [leftRep, rightRep]
    exact ⟨roots, successors⟩
  exact leftRep.symm.trans ((project_eq_of_bisimilar
    (bisimilar_of_admitted admitted paired)).trans rightRep)

theorem equal_iff_observations (first second : Tree Actions Colours) :
    first = second ↔ root first = root second ∧
      ∀ action, step first action = step second action := by
  constructor
  · rintro rfl
    exact ⟨rfl, fun _ => rfl⟩
  · rintro ⟨roots, successors⟩
    exact ext roots successors

end Mettapedia.CategoryTheory.FiniteActionTree.Tree
