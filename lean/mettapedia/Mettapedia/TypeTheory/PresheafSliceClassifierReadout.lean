import Mettapedia.TypeTheory.PresheafSliceLogicalAction

/-!
# Complete sieve readouts of the chosen slice classifier

The classifier obtained from representability agrees with the directly
constructed characteristic sieve on every actual subfunctor. The slice
classifier therefore retains both the full future sieve and the base
coordinate. These are readouts of the chosen categorical classifier, not
an independently supplied classification function.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.TypeTheory.PresheafSliceClassifierReadout

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.GSLT.Topos

universe u
variable {C : Type u} [Category.{u} C]

theorem base_characteristic (object : Face.{u, u, u} C) (predicate : Subfunctor object) :
    PresheafSliceLogicalAction.baseClassifier.χ predicate.ι =
      chiOfSubfunctor object predicate := by
  change chiOfSubfunctor object (Subfunctor.range (Subobject.mk predicate.ι).arrow) = _
  rw [Subfunctor.range_subobjectMk_ι]

variable {base : Face.{u, u, u} C}

def selected (object : Over base) (predicate : Subfunctor object.left) : Over base :=
  Over.mk (predicate.ι ≫ object.hom)

def inclusion (object : Over base) (predicate : Subfunctor object.left) :
    selected object predicate ⟶ object :=
  Over.homMk predicate.ι rfl

instance inclusion_mono (object : Over base) (predicate : Subfunctor object.left) :
    Mono (inclusion object predicate) := by
  let : Mono (inclusion object predicate).left := inferInstanceAs (Mono predicate.ι)
  exact Over.mono_of_mono_left _

def characteristic (object : Over base) (predicate : Subfunctor object.left) :
    object ⟶ (PresheafSliceLogicalAction.sliceTopos base).classifier.Ω := by
  let : Mono (inclusion object predicate) := inclusion_mono object predicate
  exact (PresheafSliceLogicalAction.sliceTopos base).classifier.χ (inclusion object predicate)

@[reassoc] theorem characteristic_sieve (object : Over base)
    (predicate : Subfunctor object.left) :
    (characteristic object predicate).left ≫ prod.fst =
      chiOfSubfunctor object.left predicate := by
  change (SliceClassifier.characteristic PresheafSliceLogicalAction.baseClassifier
      base (inclusion object predicate)).left ≫ prod.fst = _
  rw [SliceClassifier.characteristic_readout]
  exact base_characteristic object.left predicate

@[reassoc] theorem characteristic_base (object : Over base)
    (predicate : Subfunctor object.left) :
    (characteristic object predicate).left ≫ prod.snd = object.hom :=
  SliceClassifier.characteristic_base _ _ _

@[reassoc] theorem substitution_sieve {source : Face.{u, u, u} C}
    (route : source ⟶ base) (object : Over base) (predicate : Subfunctor object.left) :
    ((Over.pullback route).map (characteristic object predicate)).left ≫
        (PresheafSliceLogicalAction.classifierComparison route).hom.left ≫ prod.fst =
      pullback.fst object.hom route ≫ chiOfSubfunctor object.left predicate := by
  change ((Over.pullback route).map (characteristic object predicate)).left ≫
      (SliceClassifierPullback.constantComparison route
        PresheafSliceLogicalAction.baseClassifier.Ω).hom.left ≫ prod.fst = _
  rw [SliceClassifierPullback.constantComparison_value]
  rw [← Category.assoc]
  trans (pullback.fst object.hom route ≫ (characteristic object predicate).left) ≫ prod.fst
  · exact congrArg (fun arrow => arrow ≫ prod.fst) (pullback.lift_fst _ _ _)
  · rw [Category.assoc, characteristic_sieve]

@[reassoc] theorem substitution_base {source : Face.{u, u, u} C}
    (route : source ⟶ base) (object : Over base) (predicate : Subfunctor object.left) :
    ((Over.pullback route).map (characteristic object predicate)).left ≫
        (PresheafSliceLogicalAction.classifierComparison route).hom.left ≫ prod.snd =
      pullback.snd object.hom route := by
  change ((Over.pullback route).map (characteristic object predicate)).left ≫
      (SliceClassifierPullback.constantComparison route
        PresheafSliceLogicalAction.baseClassifier.Ω).hom.left ≫ prod.snd = _
  rw [SliceClassifierPullback.constantComparison_base]
  exact pullback.lift_snd _ _ _

end Mettapedia.TypeTheory.PresheafSliceClassifierReadout
