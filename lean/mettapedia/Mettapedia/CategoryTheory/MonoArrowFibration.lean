import Mettapedia.CategoryTheory.MonoArrowImageAdjunction
import Mettapedia.CategoryTheory.CodomainComprehensionFibration
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono

/-!
# The monomorphism fibration and full comprehension

Pullback of a monomorphism supplies an actual Cartesian lift. Conversely,
testing a Cartesian square against identity predicates recovers its full
pullback universal property. Comprehension consequently preserves and
reflects Cartesian arrows, not only the selected lifts.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.MonoArrowImageAdjunction

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable {C : Type u} [Category.{v} C]

def truth (base : C) : Predicate C :=
  ⟨Arrow.mk (𝟙 base), by change Mono (𝟙 base); infer_instance⟩

theorem stronglyCartesian_of_pullback {first second : Predicate C}
    (square : first ⟶ second)
    (cartesian : IsPullback square.hom.left first.obj.hom second.obj.hom square.hom.right) :
    (projection C).IsStronglyCartesian square.hom.right square where
  toIsHomLift := by
    change (projection C).IsHomLift ((projection C).map square) square
    infer_instance
  universal_property' := by
    intro object baseArrow supplied suppliedLift
    have := suppliedLift
    have base : baseArrow ≫ square.hom.right = supplied.hom.right :=
      IsHomLift.eq_of_isHomLift (projection C)
        (baseArrow ≫ square.hom.right) supplied
    let factor : object ⟶ first := ObjectProperty.homMk
      (Arrow.homMk
        (cartesian.lift supplied.hom.left (object.obj.hom ≫ baseArrow) (by
          rw [Category.assoc, base, Arrow.w]))
        baseArrow (by simp))
    refine ⟨factor, ⟨?_, ?_⟩, ?_⟩
    · change (projection C).IsHomLift ((projection C).map factor) factor
      infer_instance
    · apply ObjectProperty.hom_ext
      apply Arrow.hom_ext
      · exact cartesian.lift_fst _ _ _
      · exact base
    · intro candidate properties
      have := properties.1
      apply predicate_hom_ext
      exact (IsHomLift.eq_of_isHomLift (projection C) baseArrow candidate).symm

section ChosenPullbacks

variable [HasPullbacks C]

def pullbackPredicate {base : C} (predicate : Predicate C)
    (route : base ⟶ predicate.obj.right) : Predicate C :=
  ⟨Arrow.mk (pullback.snd predicate.obj.hom route), by
    change Mono (pullback.snd predicate.obj.hom route)
    infer_instance⟩

def pullbackSquare {base : C} (predicate : Predicate C)
    (route : base ⟶ predicate.obj.right) : pullbackPredicate predicate route ⟶ predicate :=
  ObjectProperty.homMk
    (Arrow.homMk (pullback.fst predicate.obj.hom route) route pullback.condition)

instance pullbackSquare_stronglyCartesian {base : C} (predicate : Predicate C)
    (route : base ⟶ predicate.obj.right) :
    (projection C).IsStronglyCartesian route (pullbackSquare predicate route) :=
  stronglyCartesian_of_pullback (pullbackSquare predicate route)
    (IsPullback.of_hasPullback predicate.obj.hom route)

instance projection_fibered : (projection C).IsFibered :=
  Functor.IsFibered.of_exists_isStronglyCartesian
    (fun (predicate : Predicate C) (base : C) (route : base ⟶ predicate.obj.right) =>
      ⟨pullbackPredicate predicate route, pullbackSquare predicate route, inferInstance⟩)

end ChosenPullbacks

def conePredicateSquare {first second : Predicate C} (square : first ⟶ second)
    (cone : PullbackCone second.obj.hom square.hom.right) : truth cone.pt ⟶ second :=
  ObjectProperty.homMk (Arrow.homMk cone.fst (cone.snd ≫ square.hom.right)
    (by
      change cone.fst ≫ second.obj.hom = 𝟙 cone.pt ≫ (cone.snd ≫ square.hom.right)
      rw [Category.id_comp]
      exact cone.condition))

instance conePredicateSquare_lift {first second : Predicate C} (square : first ⟶ second)
    (cone : PullbackCone second.obj.hom square.hom.right) :
    (projection C).IsHomLift (cone.snd ≫ square.hom.right) (conePredicateSquare square cone) := by
  change (projection C).IsHomLift ((projection C).map (conePredicateSquare square cone)) _
  infer_instance

def conePredicateFactor {first second : Predicate C} (square : first ⟶ second)
    [(projection C).IsStronglyCartesian square.hom.right square]
    (cone : PullbackCone second.obj.hom square.hom.right) : truth cone.pt ⟶ first :=
  Functor.IsStronglyCartesian.map (projection C) square.hom.right square
    (g := cone.snd) rfl (conePredicateSquare square cone)

instance conePredicateFactor_lift {first second : Predicate C} (square : first ⟶ second)
    [(projection C).IsStronglyCartesian square.hom.right square]
    (cone : PullbackCone second.obj.hom square.hom.right) :
    (projection C).IsHomLift cone.snd (conePredicateFactor square cone) := by
  unfold conePredicateFactor
  infer_instance

theorem conePredicateFactor_comp {first second : Predicate C} (square : first ⟶ second)
    [(projection C).IsStronglyCartesian square.hom.right square]
    (cone : PullbackCone second.obj.hom square.hom.right) :
    conePredicateFactor square cone ≫ square = conePredicateSquare square cone :=
  Functor.IsStronglyCartesian.fac (projection C) square.hom.right square
    rfl (conePredicateSquare square cone)

theorem conePredicateFactor_base {first second : Predicate C} (square : first ⟶ second)
    [(projection C).IsStronglyCartesian square.hom.right square]
    (cone : PullbackCone second.obj.hom square.hom.right) :
    (conePredicateFactor square cone).hom.right = cone.snd :=
  (IsHomLift.eq_of_isHomLift (projection C)
    (a := truth cone.pt) (b := first) cone.snd (conePredicateFactor square cone)).symm

theorem pullback_of_stronglyCartesian {first second : Predicate C} (square : first ⟶ second)
    [(projection C).IsStronglyCartesian square.hom.right square] :
    IsPullback square.hom.left first.obj.hom second.obj.hom square.hom.right := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (Arrow.w square.hom)
    (fun cone => (conePredicateFactor square cone).hom.left) ?_ ?_ ?_)
  · intro cone
    exact congrArg (fun arrow => arrow.hom.left) (conePredicateFactor_comp square cone)
  · intro cone
    have readout := Arrow.w (conePredicateFactor square cone).hom
    rw [conePredicateFactor_base] at readout
    change (conePredicateFactor square cone).hom.left ≫ first.obj.hom =
      𝟙 cone.pt ≫ cone.snd at readout
    exact readout.trans (Category.id_comp cone.snd)
  · intro cone candidate _firstProjection secondProjection
    apply (cancel_mono first.obj.hom).mp
    have readout := Arrow.w (conePredicateFactor square cone).hom
    rw [conePredicateFactor_base] at readout
    change (conePredicateFactor square cone).hom.left ≫ first.obj.hom =
      𝟙 cone.pt ≫ cone.snd at readout
    exact secondProjection.trans (readout.trans (Category.id_comp cone.snd)).symm

variable [HasPullbacks C]

theorem cartesian_iff_pullback {first second : Predicate C} (square : first ⟶ second) :
    (projection C).IsCartesian square.hom.right square ↔
      IsPullback square.hom.left first.obj.hom second.obj.hom square.hom.right := by
  constructor
  · intro cartesian
    have := cartesian
    exact pullback_of_stronglyCartesian square
  · intro cartesian
    have := stronglyCartesian_of_pullback square cartesian
    infer_instance

theorem comprehension_cartesian_iff {first second : Predicate C} (square : first ⟶ second) :
    (projection C).IsCartesian square.hom.right square ↔
      Arrow.rightFunc.IsCartesian square.hom.right ((comprehension C).map square) := by
  change (projection C).IsCartesian square.hom.right square ↔
    Arrow.rightFunc.IsCartesian square.hom.right square.hom
  rw [cartesian_iff_pullback, CodomainComprehension.cartesian_iff_pullback]

end Mettapedia.CategoryTheory.MonoArrowImageAdjunction
