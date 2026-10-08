import Mettapedia.CategoryTheory.RelativeClosedSyntaxPresentedPullbacks
import Mettapedia.CategoryTheory.RelativeClosedSyntaxInterpretation
import Mettapedia.CategoryTheory.CartesianEqualizerPullback

/-!
# Complete interpretation of presented matching pairs

The raw product equalizer and its independently formed semantic matching
object have complete object, projection and lift readouts. A lift requires
the actual matching diagram, including substitutions that identify endpoints.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.PullbackInterpretation

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open GeneratedCategory Interpretation

universe u v a w z

variable {C : Type u} [Category.{v} C] {symbols : Symbols.{a}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {D : Type w} [Category.{z} D] [CartesianMonoidalCategory D]
variable [MonoidalClosed D] [HasFiniteLimits D]
variable (meaning : Assignment C symbols D)
variable {left right target : Object signature}
variable (before : RawHom left target) (after : RawHom right target)
variable {L R T : D} (f : L ⟶ T) (g : R ⟶ T)
variable (leftRead : meaning.evaluateObject left.code = some L)
variable (rightRead : meaning.evaluateObject right.code = some R)
variable (targetRead : meaning.evaluateObject target.code = some T)
variable (beforeRead : meaning.evaluateArrow before.code = some ⟨L,T,f⟩)
variable (afterRead : meaning.evaluateArrow after.code = some ⟨R,T,g⟩)

include leftRead rightRead beforeRead in
theorem before_read : meaning.evaluateArrow (PresentedPullback.before before after).code =
    some ⟨L ⊗ R,T,CartesianEqualizerPullback.firstMap f g⟩ :=
  meaning.evaluate_compose _ _ (meaning.evaluate_first leftRead rightRead) beforeRead

include leftRead rightRead afterRead in
theorem after_read : meaning.evaluateArrow (PresentedPullback.after before after).code =
    some ⟨L ⊗ R,T,CartesianEqualizerPullback.secondMap f g⟩ :=
  meaning.evaluate_compose _ _ (meaning.evaluate_second leftRead rightRead) afterRead

include leftRead rightRead targetRead beforeRead afterRead

theorem object_read : meaning.evaluateObject (PresentedPullback.object before after).code =
    some (CartesianEqualizerPullback.object f g) :=
  meaning.evaluate_equalizer _ _ (meaning.evaluate_product leftRead rightRead) targetRead
    (before_read meaning before after f g leftRead rightRead beforeRead)
    (after_read meaning before after f g leftRead rightRead afterRead)

theorem inclusion_read : meaning.evaluateArrow (PresentedPullback.inclusion before after).code =
    some ⟨CartesianEqualizerPullback.object f g,L ⊗ R,
      equalizer.ι (CartesianEqualizerPullback.firstMap f g) (CartesianEqualizerPullback.secondMap f g)⟩ :=
  meaning.evaluate_equalizer_arrow _ _ (meaning.evaluate_product leftRead rightRead) targetRead
    (before_read meaning before after f g leftRead rightRead beforeRead)
    (after_read meaning before after f g leftRead rightRead afterRead)

theorem first_read : meaning.evaluateArrow (PresentedPullback.first before after).code =
    some ⟨CartesianEqualizerPullback.object f g,L,CartesianEqualizerPullback.first f g⟩ :=
  meaning.evaluate_compose _ _
    (inclusion_read meaning before after f g leftRead rightRead targetRead beforeRead afterRead)
    (meaning.evaluate_first leftRead rightRead)

theorem second_read : meaning.evaluateArrow (PresentedPullback.second before after).code =
    some ⟨CartesianEqualizerPullback.object f g,R,CartesianEqualizerPullback.second f g⟩ :=
  meaning.evaluate_compose _ _
    (inclusion_read meaning before after f g leftRead rightRead targetRead beforeRead afterRead)
    (meaning.evaluate_second leftRead rightRead)

theorem lift_read {context : Object signature}
    (first : RawHom context left) (second : RawHom context right)
    (matching : classOf (first.compose before) = classOf (second.compose after))
    {stage : D} (contextRead : meaning.evaluateObject context.code = some stage)
    (p : stage ⟶ L) (q : stage ⟶ R) (commutes : p ≫ f = q ≫ g)
    (firstRead : meaning.evaluateArrow first.code = some ⟨stage,L,p⟩)
    (secondRead : meaning.evaluateArrow second.code = some ⟨stage,R,q⟩) :
    meaning.evaluateArrow (PresentedPullback.lift before after first second matching).code =
      some ⟨stage,CartesianEqualizerPullback.object f g,CartesianEqualizerPullback.lift f g p q commutes⟩ := by
  exact meaning.evaluate_equalizer_lift _ _ _ (by
    simpa only [CartesianEqualizerPullback.firstMap, CartesianEqualizerPullback.secondMap,
      ← Category.assoc, CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_snd]
      using commutes)
    (meaning.evaluate_product leftRead rightRead) targetRead contextRead
    (before_read meaning before after f g leftRead rightRead beforeRead)
    (after_read meaning before after f g leftRead rightRead afterRead)
    (meaning.evaluate_pair p q firstRead secondRead)

end Mettapedia.CategoryTheory.RelativeClosedSyntax.PullbackInterpretation
