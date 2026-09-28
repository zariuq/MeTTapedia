import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# Constructive operations on standard presheaf predicates

These operations use Mathlib's `Functor`, `NatTrans`, and `Subfunctor`
carriers directly. Naming `NatTrans` avoids the functor category instance,
whose identity-naturality proof currently uses classical contradiction.
Images retain existential witnesses, and universal quantification ranges
over all restrictions. No representative or witness is selected.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.ConstructivePresheaf

open CategoryTheory

universe u v w
variable {C : Type u} [Category.{v} C] {P Q : C ⥤ Type w}

/-- The ordinary inclusion order, stated without selecting a Boolean algebra
instance for sets. No excluded middle is needed for a presheaf's predicate order. -/
scoped instance predicateOrder (F : C ⥤ Type w) : PartialOrder (Subfunctor F) where
  le a b := ∀ X, ∀ ⦃x : F.obj X⦄, x ∈ a.obj X → x ∈ b.obj X
  lt a b := (∀ X, ∀ ⦃x : F.obj X⦄, x ∈ a.obj X → x ∈ b.obj X) ∧
    ¬ (∀ X, ∀ ⦃x : F.obj X⦄, x ∈ b.obj X → x ∈ a.obj X)
  le_refl _ := fun _ _ holds => holds
  le_trans _ _ _ first second := fun X _ holds => second X (first X holds)
  lt_iff_le_not_ge _ _ := Iff.rfl
  le_antisymm a b forward backward := by
    apply Subfunctor.ext
    funext X
    funext x
    exact propext ⟨forward X (x := x), backward X (x := x)⟩

scoped instance predicateTop (F : C ⥤ Type w) : Top (Subfunctor F) where
  top := { obj := fun _ => Set.univ, map := fun _ _ _ => trivial }

scoped instance predicateBot (F : C ⥤ Type w) : Bot (Subfunctor F) where
  bot := { obj := fun _ => ∅, map := fun _ _ holds => holds.elim }

open scoped ConstructivePresheaf

/-- Precomposition uses the existing functors and their declared laws. -/
def restrict {B : Type*} [Category B] (H : B ⥤ C) (F : C ⥤ Type w) :
    B ⥤ Type w where
  obj X := F.obj (H.obj X)
  map f := F.map (H.map f)
  map_id X := (congrArg F.map (H.map_id X)).trans (F.map_id (H.obj X))
  map_comp f g := (congrArg F.map (H.map_comp f g)).trans (F.map_comp (H.map f) (H.map g))

def preimage (f : NatTrans P Q) (predicate : Subfunctor Q) : Subfunctor P where
  obj X := {x | f.app X x ∈ predicate.obj X}
  map {X Y} restriction := by
    intro x holds
    have naturally := congrArg (fun h : P.obj X ⟶ Q.obj Y => h x)
      (f.naturality restriction)
    change f.app Y (P.map restriction x) ∈ predicate.obj Y
    change f.app Y (P.map restriction x) = Q.map restriction (f.app X x) at naturally
    rw [naturally]
    exact predicate.map restriction holds

def image (f : NatTrans P Q) (predicate : Subfunctor P) : Subfunctor Q where
  obj X := {y | ∃ x : P.obj X, x ∈ predicate.obj X ∧ f.app X x = y}
  map {X Y} restriction := by
    rintro y ⟨x, holds, rfl⟩
    refine ⟨P.map restriction x, predicate.map restriction holds, ?_⟩
    exact congrArg (fun h : P.obj X ⟶ Q.obj Y => h x) (f.naturality restriction)

def forallAlong (f : NatTrans P Q) (predicate : Subfunctor P) : Subfunctor Q where
  obj X := {y | ∀ (Y : C) (restriction : X ⟶ Y) (x : P.obj Y),
    f.app Y x = Q.map restriction y → x ∈ predicate.obj Y}
  map {X Y} first := by
    intro y holds Z second x over
    apply holds Z (first ≫ second) x
    exact over.trans (Q.map_comp_apply first second y).symm

theorem image_le_iff (f : NatTrans P Q) (a : Subfunctor P) (b : Subfunctor Q) :
    image f a ≤ b ↔ a ≤ preimage f b := by
  constructor
  · intro included X x holds
    exact included X ⟨x, holds, rfl⟩
  · intro included X y member
    obtain ⟨x, holds, rfl⟩ := member
    exact included X holds

theorem preimage_le_iff (f : NatTrans P Q) (a : Subfunctor Q) (b : Subfunctor P) :
    preimage f a ≤ b ↔ a ≤ forallAlong f b := by
  constructor
  · intro included X y holds Y restriction x over
    apply included Y
    show f.app Y x ∈ a.obj Y
    rw [over]
    exact a.map restriction holds
  · intro included X x holds
    apply included X holds X (𝟙 X) x
    exact (Q.map_id_apply X (f.app X x)).symm

/-- A graph in the same standard presheaf carriers, with explicit natural maps. -/
structure EventGraph (C : Type u) [Category.{v} C] where
  vertex : C ⥤ Type w
  edge : C ⥤ Type w
  source : NatTrans edge vertex
  target : NatTrans edge vertex

end Mettapedia.GSLT.Topos.ConstructivePresheaf
