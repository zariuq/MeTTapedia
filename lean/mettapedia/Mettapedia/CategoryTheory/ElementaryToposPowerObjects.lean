import Mettapedia.CategoryTheory.ElementaryToposImages
import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Power objects from cartesian closure and a classifier

The power object is the exponential into the supplied classifier. Its
membership relation, the classification of every parameterized subobject,
and the uniqueness and substitution of the classifying parameter are
derived from the exponential adjunction and the classifier pullbacks.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.ElementaryToposPowerObjects

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open ElementaryToposImages

universe u v
variable {C : Type u} [Category.{v} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasPullbacks C]
variable (classifier : Subobject.Classifier C)

abbrev power (object : C) : C := (ihom object).obj classifier.Ω

abbrev membershipObject (object : C) : C :=
  pullback ((ihom.ev object).app classifier.Ω) classifier.truth

abbrev membership (object : C) :
    membershipObject classifier object ⟶ object ⊗ power classifier object :=
  pullback.fst _ _

def name {object parameter selected : C}
    (inclusion : selected ⟶ object ⊗ parameter) [Mono inclusion] :
    parameter ⟶ power classifier object :=
  curry (classifier.χ inclusion)

omit [HasPullbacks C] in
@[reassoc (attr := simp)] theorem name_evaluation {object parameter selected : C}
    (inclusion : selected ⟶ object ⊗ parameter) [Mono inclusion] :
    object ◁ name classifier inclusion ≫ (ihom.ev object).app classifier.Ω =
      classifier.χ inclusion :=
  whiskerLeft_curry_ihom_ev_app object classifier.Ω (classifier.χ inclusion)

def membershipWitness {object parameter selected : C}
    (inclusion : selected ⟶ object ⊗ parameter) [Mono inclusion] :
    selected ⟶ membershipObject classifier object :=
  pullback.lift (inclusion ≫ object ◁ name classifier inclusion)
    (classifier.χ₀ selected) (by
      rw [Category.assoc, name_evaluation]
      exact (classifier.isPullback inclusion).w)

@[reassoc (attr := simp)] theorem membershipWitness_membership
    {object parameter selected : C}
    (inclusion : selected ⟶ object ⊗ parameter) [Mono inclusion] :
    membershipWitness classifier inclusion ≫ membership classifier object =
      inclusion ≫ object ◁ name classifier inclusion :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem membershipWitness_truth
    {object parameter selected : C}
    (inclusion : selected ⟶ object ⊗ parameter) [Mono inclusion] :
    membershipWitness classifier inclusion ≫ pullback.snd _ _ = classifier.χ₀ selected :=
  pullback.lift_snd _ _ _

theorem classifies {object parameter selected : C}
    (inclusion : selected ⟶ object ⊗ parameter) [Mono inclusion] :
    IsPullback inclusion (membershipWitness classifier inclusion)
      (object ◁ name classifier inclusion) (membership classifier object) := by
  have entire : IsPullback inclusion (classifier.χ₀ selected)
      (object ◁ name classifier inclusion ≫ (ihom.ev object).app classifier.Ω)
      classifier.truth := by
    simpa only [name_evaluation] using classifier.isPullback inclusion
  have entire' : IsPullback inclusion
      (membershipWitness classifier inclusion ≫ pullback.snd _ _)
      (object ◁ name classifier inclusion ≫ (ihom.ev object).app classifier.Ω)
      classifier.truth := by
    simpa only [membershipWitness_truth] using entire
  exact entire'.of_bot (membershipWitness_membership classifier inclusion).symm
    (IsPullback.of_hasPullback ((ihom.ev object).app classifier.Ω) classifier.truth)

theorem name_unique {object parameter selected : C}
    (inclusion : selected ⟶ object ⊗ parameter) [Mono inclusion]
    (other : parameter ⟶ power classifier object)
    (witness : selected ⟶ membershipObject classifier object)
    (square : IsPullback inclusion witness (object ◁ other) (membership classifier object)) :
    other = name classifier inclusion := by
  apply uncurry_injective
  rw [name, uncurry_curry, uncurry_eq]
  exact classifier.uniq inclusion
    (square.paste_vert
      (IsPullback.of_hasPullback ((ihom.ev object).app classifier.Ω) classifier.truth))

omit [HasPullbacks C] in
theorem name_substitution {object first second oldSelected newSelected : C}
    (inclusion : oldSelected ⟶ object ⊗ second) [Mono inclusion]
    (substituted : newSelected ⟶ object ⊗ first) [Mono substituted]
    (arrow : first ⟶ second) (selectedMap : newSelected ⟶ oldSelected)
    (square : IsPullback substituted selectedMap (object ◁ arrow) inclusion) :
    name classifier substituted = arrow ≫ name classifier inclusion := by
  change curry (classifier.χ substituted) = arrow ≫ curry (classifier.χ inclusion)
  rw [← curry_natural_left]
  apply congrArg curry
  exact (classifier.uniq substituted (square.paste_vert (classifier.isPullback inclusion))).symm

/-- Every parameterized subobject has one characteristic function section. -/
def predicateEquiv (object parameter : C) :
    (parameter ⟶ power classifier object) ≃ Subobject (object ⊗ parameter) :=
  ((ihom.adjunction object).homEquiv parameter classifier.Ω).symm.trans
    (classifier.representableBy.homEquiv (X := object ⊗ parameter))

theorem predicateEquiv_substitution {object first second : C}
    (arrow : first ⟶ second) (predicate : second ⟶ power classifier object) :
    predicateEquiv classifier object first (arrow ≫ predicate) =
      (Subobject.pullback (object ◁ arrow)).obj
        (predicateEquiv classifier object second predicate) := by
  change classifier.representableBy.homEquiv (uncurry (arrow ≫ predicate)) = _
  rw [uncurry_natural_left]
  exact classifier.representableBy.homEquiv_comp _ _

def singleton (object : C) : object ⟶ power classifier object :=
  name classifier (lift (𝟙 object) (𝟙 object))

omit [HasPullbacks C] in
theorem singleton_holds {object parameter : C} (value : parameter ⟶ object) :
    evaluate classifier value (value ≫ singleton classifier object) =
      truthAt classifier parameter := by
  rw [singleton, name, evaluate_curry]
  have diagonal : lift value value = value ≫ lift (𝟙 object) (𝟙 object) := by simp
  rw [diagonal, Category.assoc, (classifier.isPullback (lift (𝟙 object) (𝟙 object))).w]
  exact truthAt_naturality classifier value

omit [HasPullbacks C] in
theorem singleton_detects_equality {object parameter : C} (first second : parameter ⟶ object)
    (held : evaluate classifier first (second ≫ singleton classifier object) =
      truthAt classifier parameter) : first = second := by
  have truthCondition : lift first second ≫ classifier.χ (lift (𝟙 object) (𝟙 object)) =
      classifier.χ₀ parameter ≫ classifier.truth := by
    simpa only [singleton, name, evaluate_curry, truthAt] using held
  let witness := (classifier.isPullback (lift (𝟙 object) (𝟙 object))).lift
    (lift first second) (classifier.χ₀ parameter) truthCondition
  have coordinate := (classifier.isPullback (lift (𝟙 object) (𝟙 object))).lift_fst
    (lift first second) (classifier.χ₀ parameter) truthCondition
  have left := congrArg (fun arrow => arrow ≫ fst object object) coordinate
  have right := congrArg (fun arrow => arrow ≫ snd object object) coordinate
  exact (by simpa using left : witness = first).symm.trans (by simpa using right)

instance singleton_mono (object : C) : Mono (singleton classifier object) where
  right_cancellation first second same := by
    apply singleton_detects_equality classifier first second
    rw [← same]
    exact singleton_holds classifier first

end Mettapedia.CategoryTheory.ElementaryToposPowerObjects
