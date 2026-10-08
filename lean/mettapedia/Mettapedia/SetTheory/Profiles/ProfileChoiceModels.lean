import Mettapedia.SetTheory.Profiles.ProfileChoice
import Mettapedia.SetTheory.Profiles.CommonCoreClassical

/-!
# Choice and universal-set comparisons on actual material carriers

The selector comparison is instantiated in the existing ZFSet and HSet
operations. Its theorem arguments retain the exact extensional Choice law.
The Russell control uses a literal authored bounded formula in the common
language, so universal-set theories cannot be merged with that Separation
instance over an unchanged membership relation.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.ProfileChoiceModels

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualMaterialSetTheory
open GraphBoundedFormulaRealization
open Mettapedia.SetTheory.CarveOuts.Sites (Tarski)
open CommonCoreClassical
open ProfileChoice

universe u
variable {S : Type u} {member : Mem S}

theorem operations_pair_choice_implies_excluded_middle
    (operations : Operations S member) (selector : ExtensionalPairSelector member) :
    ∀ p : Prop, p ∨ ¬ p :=
  extensional_pair_choice_implies_excluded_middle operations.extensionality
    (fun parent predicate => ⟨operations.separate predicate parent,
      operations.separate_spec predicate parent⟩)
    ⟨operations.empty, operations.empty_spec⟩
    (fun first second => ⟨operations.pair first second,
      fun child => operations.pair_spec first second child⟩) selector

theorem wellFounded_pair_choice_implies_excluded_middle
    (selector : ExtensionalPairSelector (S := ZFSet.{u}) (· ∈ ·)) :
    ∀ p : Prop, p ∨ ¬ p :=
  operations_pair_choice_implies_excluded_middle wellFoundedOperations selector

theorem hyperset_pair_choice_implies_excluded_middle
    (selector : ExtensionalPairSelector (S := HSet.{u}) (· ∈ ·)) :
    ∀ p : Prop, p ∨ ¬ p :=
  operations_pair_choice_implies_excluded_middle hypersetOperations selector

def russellPredicate : BoundedFormula 1 := .imply (.member 0 0) .bottom

theorem russellPredicate_is_bounded :
    toFormula russellPredicate = ContextualMaterialLogic.Formula.imply (.member 0 0) .bottom := rfl

/-- Only one explicitly bounded Separation instance is needed. -/
theorem universal_set_refutes_common_bounded_instance (universal : S)
    (containsEverything : ∀ child, member child universal) :
    ¬ Tarski member (separationAxiom (toFormula russellPredicate)) Fin.elim0 := by
  intro separated
  change ∀ parent, ∃ selected, ∀ child,
    (member child selected → member child parent ∧ ¬ member child child) ∧
    (member child parent ∧ ¬ member child child → member child selected) at separated
  obtain ⟨selected, specification⟩ := separated universal
  exact universal_set_refutes_russell_separation universal containsEverything
    ⟨selected, fun child => ⟨(specification child).1, (specification child).2⟩⟩

theorem common_bounded_instance_has_adoption :
    Nonempty (CommonCore.Axiom (separationAxiom (toFormula russellPredicate))) :=
  ⟨.boundedSeparation russellPredicate⟩

theorem operations_have_no_universal_set (operations : Operations S member) :
    ¬ ∃ universal, ∀ child, member child universal := by
  rintro ⟨universal, containsEverything⟩
  exact universal_set_refutes_common_bounded_instance universal containsEverything
    (validate operations (.boundedSeparation russellPredicate) Fin.elim0)

theorem wellFounded_has_no_universal_set :
    ¬ ∃ universal : ZFSet.{u}, ∀ child, child ∈ universal :=
  operations_have_no_universal_set wellFoundedOperations

theorem hyperset_has_no_universal_set :
    ¬ ∃ universal : HSet.{u}, ∀ child, child ∈ universal :=
  operations_have_no_universal_set hypersetOperations

end Mettapedia.SetTheory.Profiles.ProfileChoiceModels
