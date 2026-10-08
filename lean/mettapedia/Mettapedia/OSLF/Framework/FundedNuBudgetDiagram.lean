import Mettapedia.OSLF.Framework.FundedNuObservationClasses
import Mettapedia.GSLT.LanguageDef.Cost.Elaboration.ReplayKey
import Mathlib.CategoryTheory.Category.Preorder

/-!
# Resource refinement of the actual unfolding observation classes

Larger purses reveal more finite chains. Restriction retains precisely the
information available at a smaller purse, and earns a nonconstant presheaf on
the resource order. Its state sections classify the actual instruction
profiles. Every old class-dependent family pulls back coherently along these
maps; the construction does not transport an arbitrary hidden-state family.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.FundedNuBudgetDiagram

open _root_.CategoryTheory _root_.Opposite
open FundedNuObservationClasses FundedNuBudgetSeparation
open Mettapedia.GSLT.LanguageDef.Cost.Elaboration

theorem classify_lower_representative (smaller larger : Nat) (within : smaller ≤ larger)
    (state : Option Nat) :
    classify smaller (representative larger (classify larger state)) = classify smaller state := by
  cases state with
  | none => rfl
  | some length =>
      by_cases visible : length < larger
      · simp only [classify, dif_pos visible, representative, Option.map_some]
      · have invisible : ¬ length < smaller := by omega
        simp only [classify, dif_neg visible, dif_neg invisible, representative, Option.map_none]

def restriction (smaller larger : Nat) (_within : smaller ≤ larger) : Class larger → Class smaller :=
  fun code => classify smaller (representative larger code)

theorem restriction_state (smaller larger : Nat) (within : smaller ≤ larger) (state : Option Nat) :
    restriction smaller larger within (classify larger state) = classify smaller state :=
  classify_lower_representative smaller larger within state

theorem restriction_identity (budget : Nat) (code : Class budget) :
    restriction budget budget le_rfl code = code := classify_representative budget code

theorem restriction_composition (first middle last : Nat)
    (before : first ≤ middle) (after : middle ≤ last) (code : Class last) :
    restriction first middle before (restriction middle last after code) =
      restriction first last (le_trans before after) code :=
  classify_lower_representative first middle before (representative last code)

def observationClasses : Natᵒᵖ ⥤ Type where
  obj budget := Class budget.unop
  map change := TypeCat.ofHom (restriction _ _ (leOfHom change.unop))
  map_id budget := by
    apply ConcreteCategory.hom_ext
    intro code
    exact restriction_identity budget.unop code
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro code
    exact (restriction_composition _ _ _ (leOfHom second.unop) (leOfHom first.unop) code).symm

/-- The same independently supplied state gives a coherent class at every
resource stage. Its equation is derived from actual profile classification. -/
def classifications :
    (Functor.const Natᵒᵖ).obj (Option Nat) ⟶ observationClasses where
  app budget := TypeCat.ofHom (classify budget.unop)
  naturality first second change := by
    apply ConcreteCategory.hom_ext
    intro state
    exact (restriction_state second.unop first.unop (leOfHom change.unop) state).symm

theorem larger_profile_refines (smaller larger : Nat) (within : smaller ≤ larger) :
    ReplayKey.Refines (view larger) (view smaller) := by
  intro first second same
  apply (profile_equality_classifies smaller first second).mpr
  have codes := (profile_equality_classifies larger first second).mp same
  have restricted := congrArg (restriction smaller larger within) codes
  simpa only [restriction_state] using restricted

theorem one_more_cell_strictly_refines (budget : Nat) :
    ReplayKey.StrictlyRefines (view (budget + 1)) (view budget) := by
  refine ⟨larger_profile_refines budget (budget + 1) (by omega), ?_⟩
  intro reverse
  have oldSame := bounded_views_agree budget budget le_rfl
  have newSame := reverse oldSame
  have read := congrArg (fun profile => (profile (budget + 1)).1) newSame
  change (observation (budget + 1) (budget + 1) (some budget)).1 =
    (observation (budget + 1) (budget + 1) none).1 at read
  rw [one_more_cell_earns_refutation, persistent_loop_still_waits] at read
  change (some false : Option Bool) = none at read
  cases read

universe u

def pullFamily {smaller larger : Nat} (within : smaller ≤ larger)
    (family : Class smaller → Type u) : Class larger → Type u :=
  fun code => family (restriction smaller larger within code)

theorem pullFamily_identity (budget : Nat) (family : Class budget → Type u) :
    pullFamily le_rfl family = family := by
  funext code
  exact congrArg family (restriction_identity budget code)

theorem pullFamily_composition {first middle last : Nat}
    (before : first ≤ middle) (after : middle ≤ last) (family : Class first → Type u) :
    pullFamily after (pullFamily before family) = pullFamily (le_trans before after) family := by
  funext code
  exact congrArg family (restriction_composition first middle last before after code)

/-- Arbitrary families depending on an old observable class retain every
supplied witness when viewed at a larger resource stage. -/
def familyStateComparison {smaller larger : Nat} (within : smaller ≤ larger)
    (family : Class smaller → Type u) (state : Option Nat) :
    pullFamily within family (classify larger state) ≃ family (classify smaller state) :=
  Equiv.cast (congrArg family (restriction_state smaller larger within state))

end Mettapedia.OSLF.Framework.FundedNuBudgetDiagram
