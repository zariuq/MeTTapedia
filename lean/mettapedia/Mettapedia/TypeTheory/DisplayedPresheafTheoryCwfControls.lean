import Mettapedia.TypeTheory.DisplayedPresheafTheoryCwf
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Nonidentity controls for the structured theory CwF action

A theory functor exchanges two authored routes whose actual actions are
successor and reset. Its action changes a presheaf context's arrow map.
Two further theory restrictions select different objects of a nonconstant
natural section. Comprehension still retains each supplied witness, and
the generic variable reads that witness without replacing it.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafTheoryCwfControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.GSLT.Core.ContextualLadder
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafCwf DisplayedPresheafTheoryRestriction DisplayedPresheafTheoryCwf

abbrev Worlds := WalkingParallelPair
abbrev Callers := Discrete Unit

def exchange : Worlds ⥤ Worlds where
  obj := id
  map arrow := by
    cases arrow
    · exact WalkingParallelPairHom.right
    · exact WalkingParallelPairHom.left
    · exact WalkingParallelPairHom.id _
  map_id world := by cases world <;> rfl
  map_comp first second := by cases first <;> cases second <;> rfl

/-- The presheaf has equal carriers but unequal, computationally relevant
maps on its two parallel arrows. -/
def changingContext : Worldsᵒᵖ ⥤ Type :=
  walkingParallelPairOpEquiv.inverse ⋙
    parallelPair (TypeCat.ofHom Nat.succ) (TypeCat.ofHom (fun (_ : Nat) => 1))

def backwardsRoute : Opposite.op (WalkingParallelPair.one : Worlds) ⟶
    Opposite.op (WalkingParallelPair.zero : Worlds) :=
  Quiver.Hom.op (show (WalkingParallelPair.zero : Worlds) ⟶ WalkingParallelPair.one from
    WalkingParallelPairHom.left)

theorem original_route_computes (number : Nat) :
    changingContext.map backwardsRoute number = Nat.succ number := rfl

theorem restricted_route_computes (number : Nat) :
    ((contextFunctor exchange).obj ⟨changingContext⟩).val.map
      backwardsRoute number = (1 : Nat) := rfl

/-- A nonidentity theory functor yields a genuinely changed CwF context;
it is not represented by the identity action on native contexts. -/
theorem actual_context_action_is_not_identity :
    (contextFunctor exchange).obj ⟨changingContext⟩ ≠
      (⟨changingContext⟩ : (presheafCwf Worlds).base.Context) := by
  intro same
  have diagrams := congrArg ContextualBase.Context.val same
  have routes : HEq
      (((contextFunctor exchange).obj ⟨changingContext⟩).val.map backwardsRoute)
      (changingContext.map backwardsRoute) := by rw [diagrams]
  have values := ConcreteCategory.congr_hom (eq_of_heq routes) (1 : Nat)
  change (1 : Nat) = Nat.succ 1 at values
  exact Nat.succ_ne_self 1 values.symm

def base : Worldsᵒᵖ ⥤ Type := (Functor.const _).obj PUnit

def witnesses : DisplayedFamily base := CategoryOfElements.π base ⋙ changingContext

/-- The section assigns zero at the source of both routes and one at
their target; successor and reset both send that zero to one. -/
def contextualTerm : witnesses.sections where
  val point := by
    rcases point with ⟨⟨world⟩, value⟩
    cases world
    · exact (1 : Nat)
    · exact (0 : Nat)
  property := by
    rintro ⟨⟨first⟩, x⟩ ⟨⟨second⟩, y⟩ ⟨⟨route⟩, follows⟩
    change PUnit at x y
    cases x
    cases y
    cases first <;> cases second <;> cases route <;> rfl

def selectZero : Callers ⥤ Worlds := (Functor.const Callers).obj .zero
def selectOne : Callers ⥤ Worlds := (Functor.const Callers).obj .one

def point (selection : Callers ⥤ Worlds) : (selection.op ⋙ base).Elements :=
  ⟨Opposite.op (Discrete.mk ()), PUnit.unit⟩

theorem selection_zero_term :
    ((familyMorphism selectZero).mapTerm contextualTerm).val (point selectZero) = (1 : Nat) := rfl

theorem selection_one_term :
    ((familyMorphism selectOne).mapTerm contextualTerm).val (point selectOne) = (0 : Nat) := rfl

theorem different_theory_objects_give_different_terms :
    ((familyMorphism selectZero).mapTerm contextualTerm).val (point selectZero) ≠
      ((familyMorphism selectOne).mapTerm contextualTerm).val (point selectOne) := by
  rw [selection_zero_term, selection_one_term]
  exact Nat.one_ne_zero

def receipt (number : Nat) : (selectZero.op ⋙ totalSpace witnesses).Elements :=
  ⟨Opposite.op (Discrete.mk ()), ⟨PUnit.unit, number⟩⟩

/-- The supplied receipt remains intact after theory change and native
context comprehension. -/
theorem restricted_generic_variable_reads_witness (number : Nat) :
    ((familyMorphism selectZero).mapTerm (presheafVariable witnesses)).val
      (receipt number) = number := rfl

theorem restricted_projection_reads_base (number : Nat) :
    ((familyMorphism selectZero).base.map
      (show (⟨totalSpace witnesses⟩ : (presheafCwf Worlds).base.Context) ⟶ ⟨base⟩ from
        totalProjection witnesses)).app (Opposite.op (Discrete.mk ()))
          (receipt number).2 = PUnit.unit := rfl

/-- The preserved projection deliberately forgets evidence, whereas the
preserved generic variable can still distinguish supplied witnesses. -/
theorem projection_does_not_identify_witnesses :
    ((familyMorphism selectZero).mapTerm (presheafVariable witnesses)).val (receipt 3) ≠
      ((familyMorphism selectZero).mapTerm (presheafVariable witnesses)).val (receipt 4) := by
  rw [restricted_generic_variable_reads_witness, restricted_generic_variable_reads_witness]
  change (3 : Nat) ≠ 4
  decide

end Mettapedia.TypeTheory.DisplayedPresheafTheoryCwfControls
