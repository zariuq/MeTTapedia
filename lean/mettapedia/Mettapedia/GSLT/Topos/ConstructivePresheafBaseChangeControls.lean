import Mettapedia.GSLT.Topos.ConstructivePresheafBaseChange
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Nontrivial pullback and missing-lift controls

The rectangle of Boolean pairs is the pullback of the two maps to a singleton.
The commuting diagonal square omits off-diagonal pairs and fails existential
base change. Commutation by itself cannot justify the base-change equation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.ConstructivePresheaf.BaseChangeControls

open CategoryTheory
open scoped ConstructivePresheaf

abbrev Base := Discrete PUnit

def constant (T : Type) : Base ⥤ Type where
  obj _ := T
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def terminalMap : NatTrans (constant Bool) (constant PUnit) where
  app _ := TypeCat.ofHom (fun _ => PUnit.unit)
  naturality _ _ _ := rfl

def first : NatTrans (constant (Bool × Bool)) (constant Bool) where
  app _ := TypeCat.ofHom Prod.fst
  naturality _ _ _ := rfl

def second : NatTrans (constant (Bool × Bool)) (constant Bool) where
  app _ := TypeCat.ofHom Prod.snd
  naturality _ _ _ := rfl

def rectangle : PullbackSquare second first terminalMap terminalMap where
  commutes _ _ := rfl
  lift _ r q _ := ⟨(r, q), rfl, rfl⟩
  unique _ _ _ := Prod.ext

def trueOnly : Subfunctor (constant Bool) where
  obj _ := {x | x = true}
  map _ _ holds := holds

def spot : Base := ⟨PUnit.unit⟩

theorem rectangle_includes_off_diagonal :
    false ∈ (image first (preimage second trueOnly)).obj spot :=
  ⟨(false, true), rfl, rfl⟩

theorem rectangle_existential_base_change :
    preimage terminalMap (image terminalMap trueOnly) =
      image first (preimage second trueOnly) := image_baseChange rectangle trueOnly

theorem rectangle_universal_base_change :
    preimage terminalMap (forallAlong terminalMap trueOnly) =
      forallAlong first (preimage second trueOnly) := forall_baseChange rectangle trueOnly

def identityMap : NatTrans (constant Bool) (constant Bool) where
  app _ := TypeCat.ofHom id
  naturality _ _ _ := rfl

theorem diagonal_commutes (X : Base) (x : Bool) :
    terminalMap.app X (identityMap.app X x) =
      terminalMap.app X (identityMap.app X x) := rfl

theorem diagonal_has_no_pullback_lift :
    ¬ Nonempty (PullbackSquare identityMap identityMap terminalMap terminalMap) := by
  rintro ⟨square⟩
  let lifted := square.lift spot false true rfl
  have impossible : false = true := lifted.property.1.symm.trans lifted.property.2
  cases impossible

theorem commuting_square_does_not_suffice :
    preimage terminalMap (image terminalMap trueOnly) ≠
      image identityMap (preimage identityMap trueOnly) := by
  intro same
  have member : false ∈ (preimage terminalMap (image terminalMap trueOnly)).obj spot :=
    ⟨true, rfl, rfl⟩
  rw [same] at member
  obtain ⟨x, held, equal⟩ := member
  have impossible : false = true := equal.symm.trans held
  cases impossible

end Mettapedia.GSLT.Topos.ConstructivePresheaf.BaseChangeControls
