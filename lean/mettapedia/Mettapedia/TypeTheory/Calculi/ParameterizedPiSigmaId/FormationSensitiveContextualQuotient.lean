import Mathlib.CategoryTheory.Quotient
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveContextualCategory

/-! # Conversion quotient of formed substitutions

The construction is parameterized by the declared rules and uses the existing
formation, substitution and conversion judgments. Concrete language controls
are separate consumers, not premises of these laws.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveContextual

open _root_.CategoryTheory

variable {Head : Type} {rules : Rules Head}

/-- Each arrow already carries its actual refined typing. Its components
are compared by the unchanged native conversion relation. -/
def homConversion (rules : Rules Head) : HomRel (Context rules) :=
  fun {_source target} first second => ∀ index : Fin target.arity,
    Conv rules.headEq (first.substitution index) (second.substitution index) rules.computation

theorem homConversion_refl {source target : Context rules} (morphism : source ⟶ target) :
    homConversion rules morphism morphism := fun _ => .refl _

theorem homConversion_symm {source target : Context rules} {first second : source ⟶ target}
    (converted : homConversion rules first second) : homConversion rules second first :=
  fun index => .symm _ _ (converted index)

theorem homConversion_trans {source target : Context rules} {first middle last : source ⟶ target}
    (earlier : homConversion rules first middle) (later : homConversion rules middle last) :
    homConversion rules first last := fun index => .trans _ _ _ (earlier index) (later index)

/-- Precomposition applies one checked substitution to a conversion of
each later component. -/
theorem homConversion_precompose {source middle target : Context rules}
    (earlier : source ⟶ middle) {first second : middle ⟶ target}
    (converted : homConversion rules first second) :
    homConversion rules (earlier ≫ first) (earlier ≫ second) :=
  fun index => (converted index).substitute earlier.substitution

/-- Postcomposition varies the substitution inside each fixed later
component. This is the pointwise substitution-congruence theorem. -/
theorem homConversion_postcompose {source middle target : Context rules}
    {first second : source ⟶ middle} (converted : homConversion rules first second)
    (later : middle ⟶ target) : homConversion rules (first ≫ later) (second ≫ later) :=
  fun index => Conv.substitutePointwise converted (later.substitution index)

theorem homConversion_comp {source middle target : Context rules}
    {first first' : source ⟶ middle} {second second' : middle ⟶ target}
    (earlier : homConversion rules first first') (later : homConversion rules second second') :
    homConversion rules (first ≫ second) (first' ≫ second') :=
  homConversion_trans (homConversion_postcompose earlier second)
    (homConversion_precompose first' later)

/-- Pairing retains the actual types of both terms, even when reindexing
the family along the two base substitutions gives different annotations. -/
theorem homConversion_pair {source target : Context rules} {type : TypeOver target}
    {first second : source ⟶ target}
    (base : homConversion rules first second)
    {left : Term source (type.reindex first)} {right : Term source (type.reindex second)}
    (values : Conv rules.headEq left.code right.code rules.computation) :
    homConversion rules (pair first left) (pair second right) := by
  intro index
  refine Fin.cases ?_ ?_ index
  · exact values
  · intro prior
    exact base prior

instance homConversion_congruence (rules : Rules Head) : Congruence (homConversion rules) where
  comp_left := homConversion_precompose
  comp_right := fun later converted => homConversion_postcompose converted later
  equivalence :=
    ⟨homConversion_refl, homConversion_symm, homConversion_trans⟩

/-- Mathlib retains the actual formed context in each object's `as` field;
this is not an object quotient or a second definition of substitution. -/
abbrev quotientContext (rules : Rules Head) := _root_.CategoryTheory.Quotient (homConversion rules)

def quotientProjection (rules : Rules Head) : Context rules ⥤ quotientContext rules :=
  _root_.CategoryTheory.Quotient.functor (homConversion rules)

@[simp] theorem quotientProjection_obj_as (context : Context rules) :
    ((quotientProjection rules).obj context).as = context := rfl

/-- Congruence proves that no additional arrow identifications were made
by Mathlib's composition-closed quotient construction. -/
theorem quotientProjection_map_eq_iff {source target : Context rules}
    (first second : source ⟶ target) :
    (quotientProjection rules).map first = (quotientProjection rules).map second ↔
      homConversion rules first second :=
  _root_.CategoryTheory.Quotient.functor_map_eq_iff (homConversion rules) first second

theorem quotientProjection_map_surjective (source target : Context rules) :
    Function.Surjective (@(quotientProjection rules).map source target) :=
  (_root_.CategoryTheory.Quotient.full_functor (homConversion rules)).map_surjective

theorem quotientProjection_pair_eq {source target : Context rules} {type : TypeOver target}
    {first second : source ⟶ target}
    (base : homConversion rules first second)
    {left : Term source (type.reindex first)} {right : Term source (type.reindex second)}
    (values : Conv rules.headEq left.code right.code rules.computation) :
    (quotientProjection rules).map (pair first left) =
      (quotientProjection rules).map (pair second right) :=
  (quotientProjection_map_eq_iff _ _).mpr (homConversion_pair base values)


end FormationSensitiveContextual
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
