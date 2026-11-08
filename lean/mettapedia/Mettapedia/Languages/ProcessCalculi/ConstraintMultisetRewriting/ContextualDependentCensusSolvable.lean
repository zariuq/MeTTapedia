import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentIdEndpointsArgumentsControls

/-!
# The census rows still unread are solvable

Each of the three census rows that the last family leaves suspended at budget 16 is a **solvable** store of the
dynamic pattern fragment: over `A X : U0`, the instantiation `X := A` makes both sides the same term. So none of
them is a refutation the solver misses; each is a solution the solver does not reach, and a rule that decomposes
the shape exactly would commit.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentCensus.Controls

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist
open ContextualDependentGeneralPattern.Controls ContextualDependentPatternSolver.Controls
open ContextualDependentFragment.Controls ContextualDependentOccursCheck.Controls ContextualDependentDynamicFragment

/-- `A : U0` as a term over `A : U0`. -/
def typeVariable : Term ContextualDependentInversion.Controls.typeContext ContextualDependentInversion.Controls.extraType :=
  ⟨.var 0, .var 0⟩

/-- **The instantiation `X := A`**, from `A : U0` to `A X : U0`. -/
def sameAsA : ContextualDependentInversion.Controls.typeContext ⟶ twoTypes :=
  Elimination.instantiate ContextualDependentInversion.Controls.typeContext typeVariable

/-- A one-equation store whose two sides become one term under `X := A` is solvable. -/
theorem solvable_of_same (first second : TotalTerm twoTypes)
    (same : first.reindex sameAsA = second.reindex sameAsA) :
    (frames setting.levels).Solvable [(first, second)] := by
  refine ⟨_, sameAsA, fun equation member => ?_⟩
  rw [List.mem_singleton.mp member]
  change (frames setting.levels).E (first.reindex sameAsA) (second.reindex sameAsA)
  rw [same]
  exact ((frames setting.levels).equivalence _).refl _

/-- **A spine at a flexible base type**: `λ g. g X ≐ λ g. g A` is solvable. -/
theorem flexibleBase_solvable : (frames setting.levels).Solvable flexibleBaseStore :=
  solvable_of_same _ _ (totalTerm_ext rfl (by decide +kernel))

/-- **Nested projections**: `λ g. fst (fst (g X)) ≐ λ g. fst (fst (g A))` is solvable. -/
theorem nested_solvable : (frames setting.levels).Solvable nestedStore :=
  solvable_of_same _ _ (totalTerm_ext rfl (by decide +kernel))

/-- **A projection applied to arguments**: `λ g. fst (g X) A ≐ λ g. fst (g A) A` is solvable. -/
theorem applied_solvable : (frames setting.levels).Solvable appliedStore :=
  solvable_of_same _ _ (totalTerm_ext rfl (by decide +kernel))

/-- **Each row is in the fragment, solvable, and suspended by the last family at budget 16.** -/
theorem rows_unread :
    (InFragmentStore flexibleBaseStore ∧ (frames setting.levels).Solvable flexibleBaseStore ∧
        (run ContextualDependentIdEndpointsArguments.Controls.argumentsOnly flexibleBaseStore 8).readout = .suspended) ∧
      (InFragmentStore nestedStore ∧ (frames setting.levels).Solvable nestedStore ∧
        (run ContextualDependentIdEndpointsArguments.Controls.argumentsOnly nestedStore 8).readout = .suspended) ∧
      (InFragmentStore appliedStore ∧ (frames setting.levels).Solvable appliedStore ∧
        (run ContextualDependentIdEndpointsArguments.Controls.argumentsOnly appliedStore 8).readout = .suspended) :=
  ⟨⟨flexibleBase_in_fragment, flexibleBase_solvable,
      ContextualDependentIdEndpointsArguments.Controls.flexibleBase_arguments_suspended⟩,
    ⟨nested_in_fragment, nested_solvable, ContextualDependentIdEndpointsArguments.Controls.nested_arguments_suspended⟩,
    ⟨applied_in_fragment, applied_solvable,
      ContextualDependentIdEndpointsArguments.Controls.applied_arguments_suspended⟩⟩

end ContextualDependentCensus.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
