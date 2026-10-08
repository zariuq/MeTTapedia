import Mathlib.CategoryTheory.Subobject.Classifier.Defs
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Shapes.Images

/-!
# Images constructed from elementary topos structure

For an arrow `f : X ⟶ Y`, the first equalizer selects predicates on `Y`
that hold on `f`. The second equalizer selects the elements of `Y` on which
every selected predicate holds. Exponentials express these intersections
without requiring limits of arbitrary diagrams. Classifier pullbacks supply
the factor into every competing monomorphism.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.ElementaryToposImages

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed

universe u v
variable {C : Type u} [Category.{v} C]
variable (classifier : Subobject.Classifier C)

def truthAt (object : C) : object ⟶ classifier.Ω :=
  classifier.χ₀ object ≫ classifier.truth

@[reassoc (attr := simp)] theorem truthAt_naturality {first second : C}
    (arrow : first ⟶ second) : arrow ≫ truthAt classifier second = truthAt classifier first := by
  dsimp [truthAt]
  rw [← Category.assoc]
  congr 1
  exact classifier.isTerminalΩ₀.hom_ext _ _

variable [CartesianMonoidalCategory C] [MonoidalClosed C]

def evaluate {object context : C} (value : context ⟶ object)
    (predicate : context ⟶ (ihom object).obj classifier.Ω) : context ⟶ classifier.Ω :=
  lift value predicate ≫ (ihom.ev object).app classifier.Ω

theorem evaluate_substitution {object first second : C} (arrow : first ⟶ second)
    (value : second ⟶ object) (predicate : second ⟶ (ihom object).obj classifier.Ω) :
    arrow ≫ evaluate classifier value predicate =
      evaluate classifier (arrow ≫ value) (arrow ≫ predicate) := by
  simp only [evaluate, ← Category.assoc, comp_lift]

theorem evaluate_pre {first second context : C} (arrow : first ⟶ second)
    (value : context ⟶ first) (predicate : context ⟶ (ihom second).obj classifier.Ω) :
    evaluate classifier value (predicate ≫ (pre arrow).app classifier.Ω) =
      evaluate classifier (value ≫ arrow) predicate := by
  dsimp [evaluate]
  rw [← lift_whiskerLeft, Category.assoc, id_tensor_pre_app_comp_ev,
    ← Category.assoc, lift_whiskerRight]

theorem evaluate_curry {object parameter context : C} (value : context ⟶ object)
    (argument : context ⟶ parameter) (body : object ⊗ parameter ⟶ classifier.Ω) :
    evaluate classifier value (argument ≫ curry body) = lift value argument ≫ body := by
  dsimp [evaluate]
  rw [← lift_whiskerLeft, Category.assoc, whiskerLeft_curry_ihom_ev_app]

theorem evaluate_internalize {object context : C} (value : context ⟶ object)
    (predicate : object ⟶ classifier.Ω) :
    evaluate classifier value (toUnit context ≫ internalizeHom predicate) =
      value ≫ predicate := by
  rw [internalizeHom, evaluate_curry]
  simp only [← Category.assoc, lift_fst]

variable [HasEqualizers C] {X Y : C} (f : X ⟶ Y)

abbrev predicateObject (Y : C) : C := (ihom Y).obj classifier.Ω

def restrictPredicate : predicateObject classifier Y ⟶ (ihom X).obj classifier.Ω :=
  (pre f).app classifier.Ω

def trueRestriction (_f : X ⟶ Y) : predicateObject classifier Y ⟶ (ihom X).obj classifier.Ω :=
  curry (truthAt classifier (X ⊗ predicateObject classifier Y))

abbrev candidates : C := equalizer (restrictPredicate classifier f) (trueRestriction classifier f)

abbrev candidateInclusion : candidates classifier f ⟶ predicateObject classifier Y :=
  equalizer.ι (restrictPredicate classifier f) (trueRestriction classifier f)

theorem candidate_holds {context : C} (candidate : context ⟶ candidates classifier f)
    (value : context ⟶ X) :
    evaluate classifier (value ≫ f) (candidate ≫ candidateInclusion classifier f) =
      truthAt classifier context := by
  rw [← evaluate_pre]
  rw [Category.assoc]
  change evaluate classifier value
    (candidate ≫ equalizer.ι (restrictPredicate classifier f) (trueRestriction classifier f) ≫
      restrictPredicate classifier f) = _
  rw [equalizer.condition]
  change evaluate classifier value
    (candidate ≫ candidateInclusion classifier f ≫
      curry (truthAt classifier (X ⊗ predicateObject classifier Y))) = _
  rw [← Category.assoc, evaluate_curry, truthAt_naturality]

def testAll : Y ⟶ (ihom (candidates classifier f)).obj classifier.Ω :=
  curry (evaluate classifier (snd _ _) (fst _ _ ≫ candidateInclusion classifier f))

def trueOnCandidates : Y ⟶ (ihom (candidates classifier f)).obj classifier.Ω :=
  curry (truthAt classifier (candidates classifier f ⊗ Y))

abbrev imageObject : C := equalizer (testAll classifier f) (trueOnCandidates classifier f)

abbrev inclusion : imageObject classifier f ⟶ Y :=
  equalizer.ι (testAll classifier f) (trueOnCandidates classifier f)

theorem factor_condition : f ≫ testAll classifier f = f ≫ trueOnCandidates classifier f := by
  dsimp [testAll, trueOnCandidates]
  rw [← curry_natural_left, ← curry_natural_left]
  apply congrArg curry
  rw [evaluate_substitution]
  simp only [whiskerLeft_snd, whiskerLeft_fst_assoc]
  rw [candidate_holds, truthAt_naturality]

def factor : X ⟶ imageObject classifier f :=
  equalizer.lift f (factor_condition classifier f)

@[reassoc (attr := simp)] theorem factor_inclusion :
    factor classifier f ≫ inclusion classifier f = f := equalizer.lift_ι _ _

theorem image_candidate_holds {context : C} (point : context ⟶ imageObject classifier f)
    (candidate : context ⟶ candidates classifier f) :
    evaluate classifier (point ≫ inclusion classifier f)
      (candidate ≫ candidateInclusion classifier f) = truthAt classifier context := by
  have equal := congrArg uncurry
    (equalizer.condition (testAll classifier f) (trueOnCandidates classifier f))
  simp only [uncurry_natural_left, testAll, trueOnCandidates, uncurry_curry] at equal
  rw [evaluate_substitution] at equal
  simp only [whiskerLeft_snd, whiskerLeft_fst_assoc, truthAt_naturality] at equal
  have evaluated := congrArg (fun arrow => lift candidate point ≫ arrow) equal
  change lift candidate point ≫ evaluate classifier
    (snd _ _ ≫ inclusion classifier f) (fst _ _ ≫ candidateInclusion classifier f) =
      lift candidate point ≫ truthAt classifier _ at evaluated
  rw [evaluate_substitution, truthAt_naturality] at evaluated
  simpa only [lift_snd_assoc, lift_fst_assoc] using evaluated

omit [CartesianMonoidalCategory C] [MonoidalClosed C] [HasEqualizers C] in
theorem factor_characteristic (alternative : MonoFactorisation f) :
    f ≫ classifier.χ alternative.m = truthAt classifier X := by
  calc
    f ≫ classifier.χ alternative.m =
        (alternative.e ≫ alternative.m) ≫ classifier.χ alternative.m :=
      congrArg (fun arrow => arrow ≫ classifier.χ alternative.m) alternative.fac.symm
    _ = alternative.e ≫ truthAt classifier alternative.I := by
      rw [Category.assoc, (classifier.isPullback alternative.m).w]
      rfl
    _ = truthAt classifier X := truthAt_naturality classifier alternative.e

def candidatePoint (alternative : MonoFactorisation f) :
    𝟙_ C ⟶ candidates classifier f :=
  equalizer.lift (internalizeHom (classifier.χ alternative.m)) (by
    change internalizeHom (classifier.χ alternative.m) ≫ (pre f).app classifier.Ω =
      internalizeHom (classifier.χ alternative.m) ≫
        curry (truthAt classifier (X ⊗ predicateObject classifier Y))
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_natural_left, internalizeHom, uncurry_curry,
      uncurry_curry]
    simp only [whiskerRight_fst_assoc, factor_characteristic, truthAt_naturality])

@[reassoc (attr := simp)] theorem candidatePoint_inclusion
    (alternative : MonoFactorisation f) :
    candidatePoint classifier f alternative ≫ candidateInclusion classifier f =
      internalizeHom (classifier.χ alternative.m) := equalizer.lift_ι _ _

theorem image_contained_in_factorization (alternative : MonoFactorisation f) :
    inclusion classifier f ≫ classifier.χ alternative.m =
      truthAt classifier (imageObject classifier f) := by
  have held := image_candidate_holds classifier f (𝟙 _)
    (toUnit _ ≫ candidatePoint classifier f alternative)
  simpa only [Category.id_comp, Category.assoc, candidatePoint_inclusion,
    evaluate_internalize] using held

def imageFactorisation : MonoFactorisation f where
  I := imageObject classifier f
  m := inclusion classifier f
  e := factor classifier f
  fac := factor_inclusion classifier f

def isImage : IsImage (imageFactorisation classifier f) where
  lift alternative := (classifier.isPullback alternative.m).lift
    (inclusion classifier f) (classifier.χ₀ _) (image_contained_in_factorization classifier f alternative)
  lift_fac alternative := (classifier.isPullback alternative.m).lift_fst _ _ _

include classifier in
theorem hasImages : HasImages C where
  has_image f := HasImage.mk
    { F := imageFactorisation classifier f
      isImage := isImage classifier f }

omit [CartesianMonoidalCategory C] [MonoidalClosed C] [HasEqualizers C] in
include classifier in
/-- Classifier pullbacks make every monomorphism regular and hence strong.
The resulting right lifting properties make every epimorphism strong. -/
theorem strongEpiCategory : StrongEpiCategory C := by
  have : HasSubobjectClassifier C := ⟨⟨classifier⟩⟩
  refine ⟨?_⟩
  intro first second arrow _
  refine ⟨inferInstance, ?_⟩
  intro selected target inclusion _
  have : StrongMono inclusion := StrongMonoCategory.strongMono_of_mono inclusion
  exact StrongMono.rlp arrow

end Mettapedia.CategoryTheory.ElementaryToposImages
