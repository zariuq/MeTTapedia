import Mettapedia.CategoryTheory.SliceClassifier
import Mettapedia.CategoryTheory.LogicalClassifierComparison
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Logical preservation of slice classifiers

Pulling back the product classifier over a base retains its truth value
and replaces only the base coordinate. The comparison is an actual
isomorphism of slice objects, commutes with truth, and is the canonical
characteristic comparison of the mapped truth arrow.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.SliceClassifierPullback

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open SliceClassifier

set_option backward.isDefEq.respectTransparency false

universe u v
variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
variable {first last : C} (route : first ⟶ last)

def constantObject (base value : C) : Over base :=
  Over.mk (prod.snd : value ⨯ base ⟶ base)

theorem product_isPullback (value : C) :
    IsPullback (prod.map (𝟙 value) route) prod.snd prod.snd route := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (by simp)
    (fun cone => prod.lift (cone.fst ≫ prod.fst) cone.snd) ?_ ?_ ?_)
  · intro cone
    apply prod.hom_ext
    · simp
    · simpa using cone.condition.symm
  · intro cone
    simp
  · intro cone candidate firstProjection secondProjection
    apply prod.hom_ext
    · have readout := congrArg (fun arrow => arrow ≫ prod.fst) firstProjection
      simpa using readout
    · simpa using secondProjection

def constantComparison (value : C) :
    (Over.pullback route).obj (constantObject last value) ≅ constantObject first value :=
  Over.isoMk (product_isPullback route value).isoPullback.symm (by
    exact (product_isPullback route value).isoPullback_inv_snd)

@[reassoc (attr := simp)] theorem constantComparison_value (value : C) :
    (constantComparison route value).hom.left ≫ prod.fst =
      pullback.fst (prod.snd : value ⨯ last ⟶ last) route ≫ prod.fst := by
  have readout := congrArg (fun arrow => arrow ≫ prod.fst)
    (product_isPullback route value).isoPullback_inv_fst
  change (product_isPullback route value).isoPullback.inv ≫ prod.fst = _
  simpa only [Category.assoc, prod.map_fst, Category.id_comp, Category.comp_id] using readout

@[reassoc (attr := simp)] theorem constantComparison_base (value : C) :
    (constantComparison route value).hom.left ≫ prod.snd =
      pullback.snd (prod.snd : value ⨯ last ⟶ last) route := by
  exact (product_isPullback route value).isoPullback_inv_snd

variable (classifier : Subobject.Classifier C)

def classifierComparison :
    (Over.pullback route).obj (overClassifier classifier last).Ω ≅
      (overClassifier classifier first).Ω :=
  constantComparison route classifier.Ω

def truthDomainComparison :
    (Over.pullback route).obj (overClassifier classifier last).Ω₀ ≅
      (overClassifier classifier first).Ω₀ :=
  constantComparison route classifier.Ω₀

theorem truth_commutes :
    (Over.pullback route).map (overClassifier classifier last).truth ≫
        (classifierComparison route classifier).hom =
      (truthDomainComparison route classifier).hom ≫ (overClassifier classifier first).truth := by
  apply Over.OverMorphism.ext
  apply prod.hom_ext
  · change
      (((Over.pullback route).map (truth classifier last)).left ≫
        (constantComparison route classifier.Ω).hom.left) ≫ prod.fst =
      ((constantComparison route classifier.Ω₀).hom.left ≫
        (prod.map classifier.truth (𝟙 first))) ≫ prod.fst
    simp [truth, truthDomain, truthCodomain]
  · change
      (((Over.pullback route).map (truth classifier last)).left ≫
        (constantComparison route classifier.Ω).hom.left) ≫ prod.snd =
      ((constantComparison route classifier.Ω₀).hom.left ≫
        prod.map classifier.truth (𝟙 first)) ≫ prod.snd
    simp [truth, truthDomain, truthCodomain]

theorem truth_isPullback :
    IsPullback ((Over.pullback route).map (overClassifier classifier last).truth)
      (truthDomainComparison route classifier).hom
      (classifierComparison route classifier).hom (overClassifier classifier first).truth :=
  IsPullback.of_vert_isIso_mono ⟨truth_commutes route classifier⟩

theorem canonical_comparison :
    LogicalClassifierComparison.comparison
        (overClassifier classifier last) (overClassifier classifier first) (Over.pullback route) =
      (classifierComparison route classifier).hom := by
  symm
  exact (overClassifier classifier first).uniq
    ((Over.pullback route).map (overClassifier classifier last).truth)
    (truth_isPullback route classifier)

instance canonical_comparison_invertible :
    IsIso (LogicalClassifierComparison.comparison
      (overClassifier classifier last) (overClassifier classifier first) (Over.pullback route)) := by
  rw [canonical_comparison]
  infer_instance

theorem characteristic_substitution {selected object : Over last}
    (inclusion : selected ⟶ object) [Mono inclusion] :
    (Over.pullback route).map ((overClassifier classifier last).χ inclusion) ≫
        (classifierComparison route classifier).hom =
      (overClassifier classifier first).χ ((Over.pullback route).map inclusion) := by
  rw [← canonical_comparison]
  exact LogicalClassifierComparison.characteristic_preservation
    (overClassifier classifier last) (overClassifier classifier first) (Over.pullback route) inclusion

end Mettapedia.CategoryTheory.SliceClassifierPullback
