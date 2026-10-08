import Mettapedia.CategoryTheory.ElementaryToposImages
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Epimorphisms are stable under pullback in an elementary topos

Graphs turn a pullback into a pullback along a product of the original
epimorphism. Cartesian closure preserves that epimorphism. Classifying two
graph subobjects then shows that a monomorphism containing the pulled-back
arrow must have a section. Equalizers give epimorphic cancellation.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.ElementaryToposStableEpimorphisms

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory

universe u v
variable {C : Type u} [Category.{v} C]

theorem characteristic_pullback (classifier : Subobject.Classifier C)
    {P X Y Z : C} {left : P ⟶ X} {right : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    [Mono f] [Mono right] (square : IsPullback left right f g) :
    g ≫ classifier.χ f = classifier.χ right :=
  classifier.uniq right (square.flip.paste_vert (classifier.isPullback f))

variable [CartesianMonoidalCategory C]

def graph {X Y : C} (f : X ⟶ Y) : X ⟶ X ⊗ Y := lift (𝟙 X) f

instance graph_mono {X Y : C} (f : X ⟶ Y) : Mono (graph f) := by
  dsimp [graph]
  infer_instance

theorem graph_pullback {P X Y Z : C}
    {left : P ⟶ X} {right : P ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y}
    (square : IsPullback left right f g) :
    IsPullback right (lift right left) (graph g) (Z ◁ f) := by
  have commutes : right ≫ graph g = lift right left ≫ (Z ◁ f) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [graph]
    · simpa [graph] using square.w.symm
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk commutes
    (fun cone => square.lift (cone.snd ≫ snd _ _) cone.fst (by
      have second := congrArg (fun arrow => arrow ≫ snd _ _) cone.condition
      simpa [graph] using second.symm)) ?_ ?_ ?_)
  · intro cone
    exact square.lift_snd _ _ _
  · intro cone
    apply CartesianMonoidalCategory.hom_ext
    · have first := congrArg (fun arrow => arrow ≫ fst _ _) cone.condition
      simpa [graph] using first
    · simp
  · intro cone candidate first second
    apply square.hom_ext
    · have projection := congrArg (fun arrow => arrow ≫ snd _ _) second
      simpa using projection
    · exact first.trans (square.lift_snd _ _ _).symm

omit [CartesianMonoidalCategory C] in
theorem mono_factor_pullback {P X Y Z Q : C}
    {left : P ⟶ X} {right : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (square : IsPullback left right f g) (inclusion : Q ⟶ X) [Mono inclusion]
    (factor : P ⟶ Q) (recovers : factor ≫ inclusion = left) :
    IsPullback factor right (inclusion ≫ f) g := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (by
    rw [← Category.assoc, recovers, square.w])
    (fun cone => square.lift (cone.fst ≫ inclusion) cone.snd (by
      simpa only [Category.assoc] using cone.condition)) ?_ ?_ ?_)
  · intro cone
    apply (cancel_mono inclusion).mp
    rw [Category.assoc, recovers, square.lift_fst]
  · intro cone
    exact square.lift_snd _ _ _
  · intro cone candidate first second
    apply square.hom_ext
    · calc
        candidate ≫ left = (candidate ≫ factor) ≫ inclusion := by
          rw [Category.assoc, recovers]
        _ = cone.fst ≫ inclusion := congrArg (fun arrow => arrow ≫ inclusion) first
        _ = square.lift (cone.fst ≫ inclusion) cone.snd _ ≫ left :=
          (square.lift_fst _ _ _).symm
    · exact second.trans (square.lift_snd _ _ _).symm

variable [MonoidalClosed C]

theorem pullback_factor_has_section (classifier : Subobject.Classifier C)
    {P X Y Z Q : C} {left : P ⟶ X} {right : P ⟶ Z}
    {f : X ⟶ Y} {g : Z ⟶ Y} [Epi f]
    (square : IsPullback left right f g) (inclusion : Q ⟶ Z) [Mono inclusion]
    (factor : P ⟶ Q) (recovers : factor ≫ inclusion = right) :
    ∃ section_ : Z ⟶ Q, section_ ≫ inclusion = 𝟙 Z := by
  have graphSquare := graph_pullback square
  have : Mono (lift right left) := graphSquare.mono_snd_of_mono
  have restricted := mono_factor_pullback graphSquare inclusion factor recovers
  have : Epi (Z ◁ f) := by
    change Epi ((MonoidalCategory.tensorLeft Z).map f)
    infer_instance
  have same : classifier.χ (graph g) = classifier.χ (inclusion ≫ graph g) := by
    apply (cancel_epi (Z ◁ f)).mp
    exact (characteristic_pullback classifier graphSquare).trans
      (characteristic_pullback classifier restricted).symm
  have held : graph g ≫ classifier.χ (inclusion ≫ graph g) =
      classifier.χ₀ Z ≫ classifier.truth := by
    rw [← same]
    exact (classifier.isPullback (graph g)).w
  let section_ := (classifier.isPullback (inclusion ≫ graph g)).lift
    (graph g) (classifier.χ₀ Z) held
  refine ⟨section_, ?_⟩
  apply (cancel_mono (graph g)).mp
  rw [Category.assoc, Category.id_comp]
  exact (classifier.isPullback (inclusion ≫ graph g)).lift_fst _ _ _

variable [HasEqualizers C]

theorem epi_of_pullback (classifier : Subobject.Classifier C)
    {P X Y Z : C} {left : P ⟶ X} {right : P ⟶ Z}
    {f : X ⟶ Y} {g : Z ⟶ Y} [Epi f]
    (square : IsPullback left right f g) : Epi right where
  left_cancellation first second same := by
    obtain ⟨section_, section_fac⟩ := pullback_factor_has_section classifier square
      (equalizer.ι first second) (equalizer.lift right same) (equalizer.lift_ι _ _)
    calc
      first = (section_ ≫ equalizer.ι first second) ≫ first := by
        rw [section_fac, Category.id_comp]
      _ = (section_ ≫ equalizer.ι first second) ≫ second := by
        rw [Category.assoc, equalizer.condition, ← Category.assoc]
      _ = second := by rw [section_fac, Category.id_comp]

end Mettapedia.CategoryTheory.ElementaryToposStableEpimorphisms
