import Mettapedia.CategoryTheory.StrictTwoArrow
import Mathlib.CategoryTheory.Category.Cat

/-!
# Fixed-source and square compatibility controls

These controls exercise the generic construction in Cat. The constant
Boolean functor has both identity and negation natural endomorphisms.
Negation is an actual two-cell but does not fix the supplied Boolean
structure. A pair of endpoint transformations can likewise fail the
two-dimensional square condition. No finite-limit or closed-functor claim
is made about this separate generic consumer.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.StrictTwoCategoryControls

open _root_.CategoryTheory _root_.CategoryTheory.Bicategory

def constantBool : Type ⥤ Type := (Functor.const (Type 0)).obj Bool

def negate : constantBool ⟶ constantBool where
  app _ := TypeCat.ofHom Bool.not
  naturality := by intros; rfl

def booleanReadout (arrow : Bool ⟶ Bool) : Bool := arrow false

def providedBool : StrictTwoCoslice Cat.{0,1} (Cat.of (Type 0)) :=
  ⟨Cat.of (Type 0), constantBool.toCatHom⟩

def constantLeg : providedBool ⟶ providedBool where
  hom := constantBool.toCatHom
  comm := by apply Cat.ext; rfl

def identityCell : constantLeg ⟶ constantLeg := 𝟙 constantLeg

theorem supplied_identity_fixes_bool :
    booleanReadout (identityCell.hom.toNatTrans.app Bool) = false := rfl

/-- The fixed-source condition rejects a genuine natural endomorphism. -/
theorem negation_does_not_fix_structure :
    ¬ ∃ admitted : constantLeg ⟶ constantLeg, admitted.hom = negate.toCatHom₂ := by
  rintro ⟨admitted, chosen⟩
  have fixed := admitted.fixed
  rw [chosen] at fixed
  have same := eq_of_heq fixed
  have read := congrArg (fun cell => booleanReadout (cell.toNatTrans.app Bool)) same
  exact Bool.noConfusion read

def boolArrow : StrictTwoArrow Cat.{0,1} :=
  ⟨Cat.of (Type 0), Cat.of (Type 0), constantBool.toCatHom⟩

def constantSquare : boolArrow ⟶ boolArrow where
  left := constantBool.toCatHom
  right := constantBool.toCatHom
  comm := rfl

def compatibleIdentity : constantSquare ⟶ constantSquare := 𝟙 constantSquare

theorem complete_identity_components :
    booleanReadout (compatibleIdentity.left.toNatTrans.app Bool) = false ∧
    booleanReadout (compatibleIdentity.right.toNatTrans.app Bool) = false := ⟨rfl, rfl⟩

/-- Valid endpoint transformations need not form a two-cell of the arrow category. -/
theorem incompatible_pair : ¬ ∃ admitted : constantSquare ⟶ constantSquare,
    admitted.left = 𝟙 constantBool.toCatHom ∧ admitted.right = negate.toCatHom₂ := by
  rintro ⟨admitted, left, right⟩
  have compatible := admitted.compatible
  rw [left, right] at compatible
  have same := eq_of_heq compatible
  have read := congrArg (fun cell => booleanReadout (cell.toNatTrans.app Bool)) same
  exact Bool.noConfusion read

theorem negation_is_nonidentity : negate ≠ 𝟙 constantBool := by
  intro same
  exact Bool.noConfusion (congrArg (fun cell => booleanReadout (cell.app Bool)) same)

end Mettapedia.CategoryTheory.StrictTwoCategoryControls
