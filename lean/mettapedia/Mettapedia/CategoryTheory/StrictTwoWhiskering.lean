import Mathlib.CategoryTheory.Bicategory.Strict.Basic
import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor

/-!
# Equality transport for strict two-categories

The equalities below expose strict unit and associativity laws on actual
two-cells. Heterogeneous equality records only the transport of their
one-cell endpoints; no two-cell is identified by its endpoints alone.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.StrictTwoWhiskering

open _root_.CategoryTheory _root_.CategoryTheory.Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B] [Bicategory.Strict B]

omit [Bicategory.Strict B] in
theorem left_heq {a b c : B} {f f' : a ⟶ b} (same : f = f')
    {g g' h h' : b ⟶ c} (source : g = g') (target : h = h')
    {change : g ⟶ h} {change' : g' ⟶ h'} (cells : HEq change change') :
    HEq (f ◁ change) (f' ◁ change') := by
  cases same
  cases source
  cases target
  cases eq_of_heq cells
  rfl

omit [Bicategory.Strict B] in
theorem right_heq {a b c : B} {f f' g g' : a ⟶ b}
    (source : f = f') (target : g = g')
    {change : f ⟶ g} {change' : f' ⟶ g'} (cells : HEq change change')
    {h h' : b ⟶ c} (same : h = h') : HEq (change ▷ h) (change' ▷ h') := by
  cases source
  cases target
  cases same
  cases eq_of_heq cells
  rfl

theorem left_unit {a b : B} {f g : a ⟶ b} (change : f ⟶ g) :
    HEq ((𝟙 a) ◁ change) change := by
  rw [id_whiskerLeft, Bicategory.Strict.leftUnitor_eqToIso,
    Bicategory.Strict.leftUnitor_eqToIso]
  simp

theorem right_unit {a b : B} {f g : a ⟶ b} (change : f ⟶ g) :
    HEq (change ▷ (𝟙 b)) change := by
  rw [whiskerRight_id, Bicategory.Strict.rightUnitor_eqToIso,
    Bicategory.Strict.rightUnitor_eqToIso]
  simp

theorem left_assoc {a b c d : B} (f : a ⟶ b) (g : b ⟶ c)
    {h h' : c ⟶ d} (change : h ⟶ h') :
    HEq ((f ≫ g) ◁ change) (f ◁ (g ◁ change)) := by
  rw [comp_whiskerLeft, Bicategory.Strict.associator_eqToIso,
    Bicategory.Strict.associator_eqToIso]
  simp

theorem right_assoc {a b c d : B} {f f' : a ⟶ b}
    (change : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d) :
    HEq (change ▷ (g ≫ h)) ((change ▷ g) ▷ h) := by
  rw [whiskerRight_comp, Bicategory.Strict.associator_eqToIso,
    Bicategory.Strict.associator_eqToIso]
  simp

theorem mixed_assoc {a b c d : B} (f : a ⟶ b) {g g' : b ⟶ c}
    (change : g ⟶ g') (h : c ⟶ d) :
    HEq ((f ◁ change) ▷ h) (f ◁ (change ▷ h)) := by
  rw [whisker_assoc, Bicategory.Strict.associator_eqToIso,
    Bicategory.Strict.associator_eqToIso]
  simp

/-- A transported equality of complete natural transformations fixes each
component after the same endpoint transport. -/
theorem natTrans_app_heq {C D : Type*} [Category* C] [Category* D]
    {F F' G G' : C ⥤ D} (source : F = F') (target : G = G')
    {earlier : F ⟶ G} {later : F' ⟶ G'} (same : HEq earlier later) (object : C) :
    HEq (earlier.app object) (later.app object) := by
  cases source
  cases target
  cases eq_of_heq same
  rfl

end Mettapedia.CategoryTheory.StrictTwoWhiskering
