import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveRuleSubstitution

/-!
# Faithfulness of the retained component-tree action

Actual variable leaves distinguish supplied component families. Equality of
substitution actions on all retained trees therefore determines the complete
component family, including its evidence. This does not concern erased typing
proofs or the proof-irrelevant histories of conversion side conditions.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveRuleSubstitutionControls

open FormationSensitiveRuleSignature

variable {Head : Type} {R : Rules Head} {n m : Nat}
  {Γ : Ctx Head n} {Δ : Ctx Head m} {σ : Sub Head n m}

/-- Variable leaves expose exactly the supplied component tree at each index. -/
theorem components_eq_iff_variable_actions
    (first second : TreeSubstitution (R := R) Γ Δ σ) :
    first = second ↔ ∀ index : Fin n,
      (Tree.variableLeaf (R := R) Γ index).substitute first =
        (Tree.variableLeaf (R := R) Γ index).substitute second := by
  constructor
  · intro same index
    cases same
    rfl
  · intro actions
    funext index
    exact actions index

/-- Equality of component families is equivalent to equality of their action
on every retained tree in the source telescope. -/
theorem components_eq_iff_all_actions
    (first second : TreeSubstitution (R := R) Γ Δ σ) :
    first = second ↔ ∀ (term type : Tm Head n) (tree : Tree R (judgment Γ term type)),
      tree.substitute first = tree.substitute second := by
  constructor
  · intro same term type tree
    cases same
    rfl
  · intro actions
    apply (components_eq_iff_variable_actions first second).mpr
    intro index
    exact actions (.var index) (Ctx.lookup Γ index) (Tree.variableLeaf Γ index)

/-- Distinct component evidence can already be distinguished by an actual
variable tree; no observer of erased typing witnesses can replace this test. -/
theorem distinct_components_have_distinguishing_variable
    (first second : TreeSubstitution (R := R) Γ Δ σ) (different : first ≠ second) :
    ∃ index : Fin n,
      (Tree.variableLeaf (R := R) Γ index).substitute first ≠
        (Tree.variableLeaf (R := R) Γ index).substitute second := by
  classical
  by_contra none
  apply different
  apply (components_eq_iff_variable_actions first second).mpr
  intro index
  apply not_ne_iff.mp
  exact fun distinguishes => none ⟨index, distinguishes⟩

end FormationSensitiveRuleSubstitutionControls
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
