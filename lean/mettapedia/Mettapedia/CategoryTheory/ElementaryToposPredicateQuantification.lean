import Mettapedia.CategoryTheory.ElementaryToposPowerObjects
import Mettapedia.CategoryTheory.ElementaryToposStableEpimorphisms

/-!
# Universal subobjects from graph classification

The selected subobject of the codomain of `f` consists of those parameters
whose complete fibre factors through a supplied monomorphism. It is an
equalizer of the names of the full graph and the restricted graph. The
universal factorization is earned from their characteristic pullbacks.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.ElementaryToposPredicateQuantification

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed
open ElementaryToposPowerObjects ElementaryToposStableEpimorphisms

universe u v
variable {C : Type u} [Category.{v} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C]
variable [HasPullbacks C] [HasEqualizers C]
variable (classifier : Subobject.Classifier C)
variable {X Y selected : C} (f : X ⟶ Y) (inclusion : selected ⟶ X) [Mono inclusion]

abbrev universalObject : C :=
  equalizer (name classifier (graph f)) (name classifier (inclusion ≫ graph f))

abbrev universalInclusion : universalObject classifier f inclusion ⟶ Y :=
  equalizer.ι _ _

omit [HasEqualizers C] [HasPullbacks C] in
theorem fibre_factor_iff {parameter fibre : C} (base : parameter ⟶ Y)
    (left : fibre ⟶ X) (right : fibre ⟶ parameter)
    (square : IsPullback left right f base) :
    base ≫ name classifier (graph f) = base ≫ name classifier (inclusion ≫ graph f) ↔
      ∃ factor : fibre ⟶ selected, factor ≫ inclusion = left := by
  have graphSquare : IsPullback left (lift left right) (graph f) (X ◁ base) :=
    graph_pullback square.flip
  have : Mono (lift left right) := graphSquare.mono_snd_of_mono
  constructor
  · intro same
    have evaluations := congrArg uncurry same
    simp only [uncurry_natural_left, name, uncurry_curry] at evaluations
    have held : (left ≫ graph f) ≫ classifier.χ (inclusion ≫ graph f) =
        classifier.χ₀ fibre ≫ classifier.truth := by
      calc
        _ = (lift left right ≫ X ◁ base) ≫ classifier.χ (inclusion ≫ graph f) := by
          rw [graphSquare.w]
        _ = lift left right ≫ (X ◁ base ≫ classifier.χ (graph f)) := by
          rw [Category.assoc, ← evaluations]
        _ = left ≫ (graph f ≫ classifier.χ (graph f)) := by
          rw [← Category.assoc, ← graphSquare.w, Category.assoc]
        _ = classifier.χ₀ fibre ≫ classifier.truth := by
          rw [(classifier.isPullback (graph f)).w, ← Category.assoc]
          congr 1
          exact classifier.isTerminalΩ₀.hom_ext _ _
    let factor := (classifier.isPullback (inclusion ≫ graph f)).lift
      (left ≫ graph f) (classifier.χ₀ fibre) held
    refine ⟨factor, ?_⟩
    apply (cancel_mono (graph f)).mp
    rw [Category.assoc]
    exact (classifier.isPullback (inclusion ≫ graph f)).lift_fst _ _ _
  · rintro ⟨factor, recovers⟩
    have restricted := mono_factor_pullback graphSquare inclusion factor recovers
    have first := classifier.uniq (lift left right)
      (graphSquare.flip.paste_vert (classifier.isPullback (graph f)))
    have second := classifier.uniq (lift left right)
      (restricted.flip.paste_vert (classifier.isPullback (inclusion ≫ graph f)))
    apply uncurry_injective
    simp only [uncurry_natural_left, name, uncurry_curry]
    exact first.trans second.symm

def universalFactor :
    pullback f (universalInclusion classifier f inclusion) ⟶ selected :=
  (fibre_factor_iff classifier f inclusion (universalInclusion classifier f inclusion)
    (pullback.fst _ _) (pullback.snd _ _)
    (IsPullback.of_hasPullback f (universalInclusion classifier f inclusion))).mp
      (equalizer.condition _ _) |>.choose

@[reassoc (attr := simp)] theorem universalFactor_inclusion :
    universalFactor classifier f inclusion ≫ inclusion =
      pullback.fst f (universalInclusion classifier f inclusion) :=
  ((fibre_factor_iff classifier f inclusion (universalInclusion classifier f inclusion)
    (pullback.fst _ _) (pullback.snd _ _)
    (IsPullback.of_hasPullback f (universalInclusion classifier f inclusion))).mp
      (equalizer.condition _ _)).choose_spec

def universalLift {parameter fibre : C} (base : parameter ⟶ Y)
    (left : fibre ⟶ X) (right : fibre ⟶ parameter)
    (square : IsPullback left right f base)
    (factor : fibre ⟶ selected) (recovers : factor ≫ inclusion = left) :
    parameter ⟶ universalObject classifier f inclusion :=
  equalizer.lift base ((fibre_factor_iff classifier f inclusion base left right square).mpr
    ⟨factor, recovers⟩)

omit [HasPullbacks C] in
@[reassoc (attr := simp)] theorem universalLift_inclusion {parameter fibre : C}
    (base : parameter ⟶ Y) (left : fibre ⟶ X) (right : fibre ⟶ parameter)
    (square : IsPullback left right f base)
    (factor : fibre ⟶ selected) (recovers : factor ≫ inclusion = left) :
    universalLift classifier f inclusion base left right square factor recovers ≫
      universalInclusion classifier f inclusion = base :=
  equalizer.lift_ι _ _

omit [HasPullbacks C] in
theorem universalLift_unique {parameter fibre : C} (base : parameter ⟶ Y)
    (left : fibre ⟶ X) (right : fibre ⟶ parameter)
    (square : IsPullback left right f base)
    (factor : fibre ⟶ selected) (recovers : factor ≫ inclusion = left)
    (candidate : parameter ⟶ universalObject classifier f inclusion)
    (candidate_readout : candidate ≫ universalInclusion classifier f inclusion = base) :
    candidate = universalLift classifier f inclusion base left right square factor recovers := by
  apply (cancel_mono (universalInclusion classifier f inclusion)).mp
  rw [candidate_readout, universalLift_inclusion]

omit [HasPullbacks C] in
theorem selected_fibre_factors {parameter fibre : C}
    (candidate : parameter ⟶ universalObject classifier f inclusion)
    (left : fibre ⟶ X) (right : fibre ⟶ parameter)
    (square : IsPullback left right f (candidate ≫ universalInclusion classifier f inclusion)) :
    ∃ factor : fibre ⟶ selected, factor ≫ inclusion = left := by
  apply (fibre_factor_iff classifier f inclusion _ left right square).mp
  rw [Category.assoc, Category.assoc, equalizer.condition]

def universalElement {parameter : C} (point : parameter ⟶ X)
    (candidate : parameter ⟶ universalObject classifier f inclusion)
    (liesOver : point ≫ f = candidate ≫ universalInclusion classifier f inclusion) :
    parameter ⟶ selected :=
  pullback.lift point candidate liesOver ≫ universalFactor classifier f inclusion

@[reassoc (attr := simp)] theorem universalElement_inclusion {parameter : C}
    (point : parameter ⟶ X)
    (candidate : parameter ⟶ universalObject classifier f inclusion)
    (liesOver : point ≫ f = candidate ≫ universalInclusion classifier f inclusion) :
    universalElement classifier f inclusion point candidate liesOver ≫ inclusion = point := by
  simp only [universalElement, Category.assoc, universalFactor_inclusion]
  exact pullback.lift_fst _ _ _

end Mettapedia.CategoryTheory.ElementaryToposPredicateQuantification
