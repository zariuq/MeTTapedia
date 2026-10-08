import Mathlib.CategoryTheory.Quotient
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualCategory

/-!
# The mixed generated refinement substitution quotient

Arrow equations are exactly the authored typed substitution equations. Their
compatibility with composition follows from ordered component congruence and
the earned substitution-equality reconstruction theorem.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual

open _root_.CategoryTheory

universe u
variable {S : Symbols.{u}} {D : Signature S}

def homEquality (D : Signature S) : HomRel (Context D) :=
  fun {source target} first second =>
    Holds D (.substitutionEq source.raw target.raw first.substitution second.substitution)

theorem homEquality_refl {source target : Context D} (morphism : source ⟶ target) :
    homEquality D morphism morphism := substitutionEquality_refl morphism.admitted

theorem homEquality_symm {source target : Context D} {first second : source ⟶ target}
    (same : homEquality D first second) : homEquality D second first := substitutionEquality_symm same

theorem homEquality_trans {source target : Context D} {first middle last : source ⟶ target}
    (earlier : homEquality D first middle) (later : homEquality D middle last) :
    homEquality D first last := substitutionEquality_trans earlier later

theorem homEquality_precompose {source middle target : Context D} (earlier : source ⟶ middle)
    {first second : middle ⟶ target} (same : homEquality D first second) :
    homEquality D (earlier ≫ first) (earlier ≫ second) :=
  substitutionEquality_precompose source.formed target.formed earlier.admitted
    first.admitted second.admitted same

theorem homEquality_postcompose {source middle target : Context D} {first second : source ⟶ middle}
    (same : homEquality D first second) (later : middle ⟶ target) :
    homEquality D (first ≫ later) (second ≫ later) :=
  substitutionEquality_postcompose source.formed target.formed first.admitted
    second.admitted later.admitted same

instance homEquality_congruence (D : Signature S) : Congruence (homEquality D) where
  comp_left := homEquality_precompose
  comp_right := fun later same => homEquality_postcompose same later
  equivalence := ⟨homEquality_refl, homEquality_symm, homEquality_trans⟩

theorem homEquality_pair {source target : Context D} {type : TypeOver target}
    {first second : source ⟶ target} (base : homEquality D first second)
    {left : Term source (type.reindex first)} {right : Term source (type.reindex second)}
    (values : Holds D (.termEq source.raw left.code right.code (type.reindex first).code)) :
    homEquality D (pair first left) (pair second right) :=
  conclude (.substitutionExtendEquality source.raw target.raw type.code first.substitution
    second.substitution left.code right.code) ⟨base, type.formed, values, right.typed, trivial⟩

abbrev quotientContext (D : Signature S) := _root_.CategoryTheory.Quotient (homEquality D)

def quotientProjection (D : Signature S) : Context D ⥤ quotientContext D :=
  _root_.CategoryTheory.Quotient.functor (homEquality D)

@[simp] theorem quotientProjection_obj_as (context : Context D) :
    ((quotientProjection D).obj context).as = context := rfl

theorem quotientProjection_map_eq_iff {source target : Context D} (first second : source ⟶ target) :
    (quotientProjection D).map first = (quotientProjection D).map second ↔ homEquality D first second :=
  _root_.CategoryTheory.Quotient.functor_map_eq_iff (homEquality D) first second

theorem quotientProjection_map_surjective (source target : Context D) :
    Function.Surjective (@(quotientProjection D).map source target) :=
  (_root_.CategoryTheory.Quotient.full_functor (homEquality D)).map_surjective

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual
