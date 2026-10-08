import Mathlib.CategoryTheory.Quotient
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedContextualCategory
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.ContextualSubstitutionEquality

/-!
# The typed equation quotient of admitted substitutions

Each endpoint is a typed-formed telescope and each arrow carries an actual
component typing. The congruence uses dependent typed substitution equality,
including its retyping between component annotations. Composition closure
introduces no additional arrow equations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedContextual

open _root_.CategoryTheory TypedEquality TypedEquality.Normalization

variable {Head : Type} {rules : Rules Head}

def homTypedEquality (rules : Rules Head) : HomRel (Context rules) :=
  fun {source target} first second =>
    SubstEq rules target.raw source.raw first.substitution second.substitution

theorem homTypedEquality_refl {source target : Context rules} (morphism : source ⟶ target) :
    homTypedEquality rules morphism morphism := SubstEq.reflexive morphism.typed

theorem homTypedEquality_symm {source target : Context rules} {first second : source ⟶ target}
    (same : homTypedEquality rules first second) : homTypedEquality rules second first :=
  same.symmetric target.formed second.typed

theorem homTypedEquality_trans {source target : Context rules} {first middle last : source ⟶ target}
    (earlier : homTypedEquality rules first middle) (later : homTypedEquality rules middle last) :
    homTypedEquality rules first last := earlier.transitive target.formed later

theorem homTypedEquality_precompose {source middle target : Context rules}
    (earlier : source ⟶ middle) {first second : middle ⟶ target}
    (same : homTypedEquality rules first second) :
    homTypedEquality rules (earlier ≫ first) (earlier ≫ second) := same.precompose earlier.typed

theorem homTypedEquality_postcompose {source middle target : Context rules}
    {first second : source ⟶ middle} (same : homTypedEquality rules first second)
    (later : middle ⟶ target) : homTypedEquality rules (first ≫ later) (second ≫ later) :=
  same.postcompose later.typed

theorem homTypedEquality_comp {source middle target : Context rules}
    {first first' : source ⟶ middle} {second second' : middle ⟶ target}
    (earlier : homTypedEquality rules first first') (later : homTypedEquality rules second second') :
    homTypedEquality rules (first ≫ second) (first' ≫ second') :=
  earlier.compose target.formed later first'.typed

theorem homTypedEquality_pair {source target : Context rules} {type : TypeOver target}
    {first second : source ⟶ target} (base : homTypedEquality rules first second)
    {left : Term source (type.reindex first)} {right : Term source (type.reindex second)}
    (values : Equal rules source.raw left.code right.code (type.reindex first).code) :
    homTypedEquality rules (pair first left) (pair second right) :=
  base.cons type.code left.typed values

instance homTypedEquality_congruence (rules : Rules Head) : Congruence (homTypedEquality rules) where
  comp_left := homTypedEquality_precompose
  comp_right := fun later same => homTypedEquality_postcompose same later
  equivalence := ⟨homTypedEquality_refl, homTypedEquality_symm, homTypedEquality_trans⟩

abbrev quotientContext (rules : Rules Head) := _root_.CategoryTheory.Quotient (homTypedEquality rules)

def quotientProjection (rules : Rules Head) : Context rules ⥤ quotientContext rules :=
  _root_.CategoryTheory.Quotient.functor (homTypedEquality rules)

@[simp] theorem quotientProjection_obj_as (context : Context rules) :
    ((quotientProjection rules).obj context).as = context := rfl

theorem quotientProjection_map_eq_iff {source target : Context rules} (first second : source ⟶ target) :
    (quotientProjection rules).map first = (quotientProjection rules).map second ↔
      homTypedEquality rules first second :=
  _root_.CategoryTheory.Quotient.functor_map_eq_iff (homTypedEquality rules) first second

theorem quotientProjection_map_surjective (source target : Context rules) :
    Function.Surjective (@(quotientProjection rules).map source target) :=
  (_root_.CategoryTheory.Quotient.full_functor (homTypedEquality rules)).map_surjective

theorem quotientProjection_pair_eq {source target : Context rules} {type : TypeOver target}
    {first second : source ⟶ target} (base : homTypedEquality rules first second)
    {left : Term source (type.reindex first)} {right : Term source (type.reindex second)}
    (values : Equal rules source.raw left.code right.code (type.reindex first).code) :
    (quotientProjection rules).map (pair first left) = (quotientProjection rules).map (pair second right) :=
  (quotientProjection_map_eq_iff _ _).mpr (homTypedEquality_pair base values)

end TypedContextual
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
