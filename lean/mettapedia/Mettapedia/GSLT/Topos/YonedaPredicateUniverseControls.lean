import Mettapedia.GSLT.Topos.YonedaPredicateUniverseBridge
import Mettapedia.GSLT.Core.LambdaTheoryClosedControls

/-!
# Mixed-universe Yoneda predicate controls

Two-index set diagrams have object universe one and morphism universe zero.
Their actual raised representables retain independently supplied natural
transformations and the exact values of their restriction. A future-sensitive
positive-output predicate admits the supplied shift, while excluding the
identity map. Both the predicate constraint and the complete base arrow
survive the total-category equivalence and its projection.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Topos.YonedaPredicateUniverseControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open Mettapedia.CategoryTheory.AsSmallYoneda
open Mettapedia.GSLT.Core.LambdaTheoryClosedControls
open YonedaPredicateUniverseBridge

def positiveOutput : Subfunctor (yoneda.obj numbers) where
  obj world := { arrow | ∀ value : world.unop.obj ⟨false⟩,
    (0 : Nat) < (arrow.app ⟨false⟩ value : Nat) }
  map change _ held value := held (change.unop.app ⟨false⟩ value)

abbrev unrestricted : Original Diagrams := ⟨numbers, ⊤⟩

abbrev positive : Original Diagrams := ⟨numbers, positiveOutput⟩

def admittedShift : unrestricted ⟶ positive where
  base := shift
  entails := by
    intro world arrow _ value
    exact Nat.zero_lt_succ _

theorem positive_contains_shift : shift ∈ positiveOutput.obj (op numbers) := by
  intro value
  exact Nat.zero_lt_succ _

theorem identity_not_positive : (𝟙 numbers) ∉ positiveOutput.obj (op numbers) := by
  intro held
  exact Nat.lt_irrefl 0 (held (0 : Nat))

theorem no_identity_admission :
    ¬ ∃ arrow : unrestricted ⟶ positive, arrow.base = 𝟙 numbers := by
  rintro ⟨arrow, same⟩
  have held := arrow.entails (op numbers)
    (show (𝟙 numbers) ∈ (⊤ : Subfunctor (yoneda.obj numbers)).obj (op numbers)
      from Set.mem_univ _)
  have output : (𝟙 numbers) ∈ positiveOutput.obj (op numbers) := by
    simpa only [same, yoneda.map_id, Subfunctor.preimage_id] using held
  exact identity_not_positive output

theorem normalized_positive_shift :
    (up Diagrams).map shift ∈
      (YonedaPredicate.predicate ((raiseTotal Diagrams).obj positive)).obj
        (op ((up Diagrams).obj numbers)) :=
  (raised_predicate_readout positive numbers shift).mpr positive_contains_shift

theorem normalized_identity_still_rejected :
    (up Diagrams).map (𝟙 numbers) ∉
      (YonedaPredicate.predicate ((raiseTotal Diagrams).obj positive)).obj
        (op ((up Diagrams).obj numbers)) := by
  intro held
  exact identity_not_positive
    ((raised_predicate_readout positive numbers (𝟙 numbers)).mp held)

/-- Exact downward reading of an independently authored generalized element. -/
theorem raised_generalized_element_value :
    ((down Diagrams).map
      ((yoneda.obj ((up Diagrams).obj numbers)).map ((up Diagrams).map shift).op
        ((up Diagrams).map (𝟙 numbers)))).app ⟨false⟩ (10 : Nat) = (11 : Nat) := rfl

theorem raised_exchange_value :
    ((down Diagrams).map
      ((yoneda.obj ((up Diagrams).obj numbers)).map
        ((up Diagrams).map (swapMap.functor.map shift)).op
        ((up Diagrams).map (𝟙 numbers)))).app ⟨false⟩ (10 : Nat) = (12 : Nat) := rfl

theorem actual_values_still_differ :
    ((down Diagrams).map
      ((yoneda.obj ((up Diagrams).obj numbers)).map ((up Diagrams).map shift).op
        ((up Diagrams).map (𝟙 numbers)))).app ⟨false⟩ (10 : Nat) ≠
    ((down Diagrams).map
      ((yoneda.obj ((up Diagrams).obj numbers)).map
        ((up Diagrams).map (swapMap.functor.map shift)).op
        ((up Diagrams).map (𝟙 numbers)))).app ⟨false⟩ (10 : Nat) := by
  rw [raised_generalized_element_value, raised_exchange_value]
  change (11 : Nat) ≠ 12
  omega

theorem raised_admitted_arrow_value :
    ((down Diagrams).map ((raiseTotal Diagrams).map admittedShift).base).app
      ⟨false⟩ (10 : Nat) = (11 : Nat) := rfl

theorem omitted_admitted_arrow_changes_value :
    ((down Diagrams).map ((raiseTotal Diagrams).map admittedShift).base).app
        ⟨false⟩ (10 : Nat) ≠ (𝟙 numbers : numbers ⟶ numbers).app ⟨false⟩ (10 : Nat) := by
  rw [raised_admitted_arrow_value]
  change (11 : Nat) ≠ 10
  omega

theorem complete_arrow_roundtrip :
    (lowerTotal Diagrams).map ((raiseTotal Diagrams).map admittedShift) = admittedShift :=
  Original.Hom.ext _ _ rfl

theorem original_projection_retains_arrow :
    (Original.projection Diagrams).map admittedShift = shift := rfl

theorem original_has_finite_limits : HasFiniteLimits (Original Diagrams) := inferInstance

@[instance_reducible]
def originalClosedStructure : MonoidalClosed (Original Diagrams) := inferInstance

theorem original_projection_is_lex :
    PreservesFiniteLimits (Original.projection Diagrams) := inferInstance

/-- The actual closed canonical projection is formed at the earned common
category universe, with no equality between the original two universes. -/
theorem canonical_projection_closed :
    MonoidalClosedFunctor (YonedaPredicate.projection (Small Diagrams)) := inferInstance

abbrev projectionMap := canonicalProjection diagramsTheory

theorem canonical_map_recovers_complete_base_arrow :
    (down Diagrams).map (projectionMap.functor.map
      ((raiseTotal Diagrams).map admittedShift)) = shift :=
  canonical_projection_recovers_original_arrow diagramsTheory admittedShift

end Mettapedia.GSLT.Topos.YonedaPredicateUniverseControls
