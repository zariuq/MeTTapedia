import Mettapedia.GSLT.Topos.ConstructivePresheafDependentPredicates
import Mettapedia.GSLT.Topos.ConstructivePresheafFunctionControls

/-!
# Argument/result correlation is retained

Equality of a Boolean argument and its result is a natural dependent
predicate. The identity function satisfies it; Boolean negation does not.
Both projections of the result relation admit every Boolean, so forgetting
the correlation would lose this distinction.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.ConstructivePresheaf.DependentControls

open CategoryTheory
open scoped ConstructivePresheaf
open PresheafEventModalities.Controls (vertices)

def matchingResults : Subfunctor (FunctorToTypes.prod vertices vertices) where
  obj _ := {pair | pair.1 = pair.2}
  map _ _ same := same

theorem identity_passes (stage : Nat) :
    FunctionControls.identityAt stage ∈
      (dependentFunctionPredicate (⊤ : Subfunctor vertices) matchingResults).obj stage := by
  intro later restriction argument member
  rfl

theorem negation_fails :
    (curryFunction FunctionControls.xorOperation).app 0 true ∉
      (dependentFunctionPredicate (⊤ : Subfunctor vertices) matchingResults).obj 0 := by
  intro held
  have impossible : false = true := held 0 (𝟙 0) false trivial
  cases impossible

theorem each_argument_has_a_result (stage : Nat) (argument : Bool) :
    ∃ result, (argument, result) ∈ matchingResults.obj stage := ⟨argument, rfl⟩

theorem each_result_has_an_argument (stage : Nat) (result : Bool) :
    ∃ argument, (argument, result) ∈ matchingResults.obj stage := ⟨result, rfl⟩

theorem projections_do_not_recover_correlation :
    (∃ result, (false, result) ∈ matchingResults.obj 0) ∧
    (∃ argument, (argument, true) ∈ matchingResults.obj 0) ∧
    (false, true) ∉ matchingResults.obj 0 := by
  refine ⟨⟨false, rfl⟩, ⟨true, rfl⟩, ?_⟩
  intro impossible
  cases impossible

end Mettapedia.GSLT.Topos.ConstructivePresheaf.DependentControls
