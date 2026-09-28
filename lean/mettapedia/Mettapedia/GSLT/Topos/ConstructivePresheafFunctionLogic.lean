import Mettapedia.GSLT.Topos.ConstructivePresheafFunctionPredicates
import Mettapedia.GSLT.Topos.PresheafPredicateHeyting

/-!
# Internal logical description of the function predicate

The function predicate is the universal quantification, along the parameter
projection, of the implication from argument membership to result membership
under evaluation. Both implication and quantification inspect all future
restrictions. This identifies the direct predicate with the internal logical
formula used by the presheaf predicate construction.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.ConstructivePresheaf

open CategoryTheory
open scoped ConstructivePresheaf

universe u
variable {C : Type u} [Category.{u} C]
variable {F G : C ⥤ Type u}

def firstProjection (F G : C ⥤ Type u) : NatTrans (FunctorToTypes.prod F G) F where
  app _ := TypeCat.ofHom Prod.fst
  naturality _ _ _ := rfl

def secondProjection (F G : C ⥤ Type u) : NatTrans (FunctorToTypes.prod F G) G where
  app _ := TypeCat.ofHom Prod.snd
  naturality _ _ _ := rfl

def conjunction (first second : Subfunctor F) : Subfunctor F where
  obj X := {x | x ∈ first.obj X ∧ x ∈ second.obj X}
  map restriction _ member := ⟨first.map restriction member.1, second.map restriction member.2⟩

/-- The existing future-restriction implication has the defining adjunction
under the constructive predicate order. -/
theorem implication_adjunction (premise antecedent consequent : Subfunctor F) :
    premise ≤ himpPointwise antecedent consequent ↔
      conjunction premise antecedent ≤ consequent := by
  constructor
  · intro held X x member
    have result := held X member.1 X (𝟙 X)
    rw [F.map_id_apply] at result
    exact result member.2
  · intro held X x member Y restriction argument
    exact held Y ⟨premise.map restriction member, argument⟩

theorem functionPredicate_internal_formula (source : Subfunctor F) (target : Subfunctor G) :
    functionPredicate source target =
      forallAlong (secondProjection F (functions F G))
        (himpPointwise (preimage (firstProjection F (functions F G)) source)
          (preimage (evaluate F G) target)) := by
  apply Subfunctor.ext
  funext X
  funext value
  apply propext
  constructor
  · intro held Y restriction pair over Z further member
    change pair.2 = FunctionSection.restrict F G restriction value at over
    change F.map further pair.1 ∈ source.obj Z at member
    change (FunctionSection.restrict F G further pair.2).app Z (𝟙 Z)
      (F.map further pair.1) ∈ target.obj Z
    rw [over]
    change value.app Z (restriction ≫ further ≫ 𝟙 Z) (F.map further pair.1) ∈ target.obj Z
    rw [Category.comp_id]
    exact held Z (restriction ≫ further) (F.map further pair.1) member
  · intro held Y restriction argument member
    have result := held Y restriction
      (argument, FunctionSection.restrict F G restriction value) rfl Y (𝟙 Y)
    change F.map (𝟙 Y) argument ∈ source.obj Y →
      value.app Y (restriction ≫ 𝟙 Y ≫ 𝟙 Y) (F.map (𝟙 Y) argument) ∈ target.obj Y at result
    rw [F.map_id_apply, Category.comp_id, Category.comp_id] at result
    exact result member

end Mettapedia.GSLT.Topos.ConstructivePresheaf
