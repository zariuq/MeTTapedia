import Mathlib.CategoryTheory.Subobject.Classifier.Defs
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Classifiers in slice categories

The classifier over a base object is the product of the base classifier
with that object. Classification is proved by cancelling the bottom
product pullback. Uniqueness pastes that same square back to the original
classifier, so both the characteristic coordinate and the base coordinate
are retained.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.SliceClassifier

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]

variable (classifier : Subobject.Classifier C) (base : C)

def truthDomain : Over base := Over.mk (prod.snd : classifier.Ω₀ ⨯ base ⟶ base)

def truthCodomain : Over base := Over.mk (prod.snd : classifier.Ω ⨯ base ⟶ base)

def truth : truthDomain classifier base ⟶ truthCodomain classifier base :=
  Over.homMk (prod.map classifier.truth (𝟙 base)) (by simp [truthDomain, truthCodomain])

def terminalMap (object : Over base) : object ⟶ truthDomain classifier base :=
  Over.homMk (prod.lift (classifier.χ₀ object.left) object.hom) (by simp [truthDomain])

def characteristic {selected object : Over base}
    (inclusion : selected ⟶ object) [Mono inclusion] :
    object ⟶ truthCodomain classifier base :=
  Over.homMk (prod.lift (classifier.χ inclusion.left) object.hom) (by simp [truthCodomain])

theorem characteristic_square {selected object : Over base}
    (inclusion : selected ⟶ object) [Mono inclusion] :
    inclusion ≫ characteristic classifier base inclusion =
      terminalMap classifier base selected ≫ truth classifier base := by
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · simp only [Over.comp_left, characteristic, terminalMap, truth, Over.homMk_left,
      Category.assoc, prod.lift_fst, prod.map_fst]
    simpa only [Category.assoc, prod.lift_fst_assoc] using
      (classifier.isPullback inclusion.left).w
  · simp [characteristic, terminalMap, truth]

theorem characteristic_isPullback {selected object : Over base}
    (inclusion : selected ⟶ object) [Mono inclusion] :
    IsPullback inclusion (terminalMap classifier base selected)
      (characteristic classifier base inclusion) (truth classifier base) := by
  have rectangle := (IsPullback.of_prod_fst_with_id classifier.truth base).flip
  have entire : IsPullback inclusion.left
      ((terminalMap classifier base selected).left ≫ prod.fst)
      ((characteristic classifier base inclusion).left ≫ prod.fst)
      classifier.truth := by
    simpa only [terminalMap, characteristic, Over.homMk_left, prod.lift_fst] using
      classifier.isPullback inclusion.left
  have square := entire.of_bot
    (congrArg Over.Hom.left (characteristic_square classifier base inclusion)) rectangle
  apply IsPullback.of_map_of_faithful (Over.forget base)
  exact square

theorem characteristic_unique {selected object : Over base}
    (inclusion : selected ⟶ object) [Mono inclusion]
    (otherDomain : selected ⟶ truthDomain classifier base)
    (other : object ⟶ truthCodomain classifier base)
    (square : IsPullback inclusion otherDomain other (truth classifier base)) :
    other = characteristic classifier base inclusion := by
  have rectangle := (IsPullback.of_prod_fst_with_id classifier.truth base).flip
  have entire := (square.map (Over.forget base)).paste_vert rectangle
  have classified : other.left ≫ prod.fst = classifier.χ inclusion.left :=
    classifier.uniq inclusion.left entire
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · simpa only [characteristic, Over.homMk_left, prod.lift_fst] using classified
  · exact (Over.w other).trans (by simp [characteristic, truthCodomain])

/-- The actual product classifier in the slice, with its complete universal
property for arbitrary monomorphisms of the slice. -/
def overClassifier : Subobject.Classifier (Over base) where
  Ω₀ := truthDomain classifier base
  Ω := truthCodomain classifier base
  truth := truth classifier base
  mono_truth := by
    have : Mono (truth classifier base).left := by
      change Mono (prod.map classifier.truth (𝟙 base))
      infer_instance
    exact Over.mono_of_mono_left (truth classifier base)
  χ₀ := terminalMap classifier base
  χ := characteristic classifier base
  isPullback := characteristic_isPullback classifier base
  uniq inclusion _ otherDomain other square :=
    characteristic_unique classifier base inclusion otherDomain other square

instance slice_hasClassifier [HasSubobjectClassifier C] (base : C) :
    HasSubobjectClassifier (Over base) where
  exists_classifier := ⟨overClassifier HasSubobjectClassifier.exists_classifier.some base⟩

@[simp] theorem characteristic_readout {selected object : Over base}
    (inclusion : selected ⟶ object) [Mono inclusion] :
    (characteristic classifier base inclusion).left ≫ prod.fst =
      classifier.χ inclusion.left := by
  simp [characteristic]

@[simp] theorem characteristic_base {selected object : Over base}
    (inclusion : selected ⟶ object) [Mono inclusion] :
    (characteristic classifier base inclusion).left ≫ prod.snd = object.hom := by
  simp [characteristic]

end Mettapedia.CategoryTheory.SliceClassifier
