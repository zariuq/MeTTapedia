import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Full codomain comprehension and its unit

Identity arrows give the comprehension unit. Codomain is its left adjoint
and domain is its right adjoint. The universal property of a Cartesian
arrow is exactly the universal property of its commuting pullback square.
These facts concern arbitrary arrows and maps, rather than only a chosen
cleavage.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.CodomainComprehension

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v
variable (C : Type u) [Category.{v} C]

def unit : C ⥤ Arrow C where
  obj object := Arrow.mk (𝟙 object)
  map arrow := Arrow.homMk arrow arrow (by simp)

def codomainAdjunction : Arrow.rightFunc ⊣ unit C :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun object target =>
        { toFun := fun arrow => Arrow.homMk (object.hom ≫ arrow) arrow (by simp [unit])
          invFun := fun square => square.right
          left_inv := fun _ => rfl
          right_inv := fun square => by
            apply Arrow.hom_ext
            · simpa [unit] using (Arrow.w square).symm
            · rfl }
      homEquiv_naturality_left_symm := by
        intro first second target square arrow
        rfl
      homEquiv_naturality_right := by
        intro object first second arrow next
        apply Arrow.hom_ext
        · change object.hom ≫ (arrow ≫ next) = (object.hom ≫ arrow) ≫ next
          exact (Category.assoc _ _ _).symm
        · rfl }

def domainAdjunction : unit C ⊣ Arrow.leftFunc :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun source object =>
        { toFun := fun square => square.left
          invFun := fun arrow => Arrow.homMk arrow (arrow ≫ object.hom) (by simp [unit])
          left_inv := fun square => by
            apply Arrow.hom_ext
            · rfl
            · simp [unit]
          right_inv := fun _ => rfl }
      homEquiv_naturality_left_symm := by
        intro first second object arrow square
        apply Arrow.hom_ext
        · rfl
        · change (arrow ≫ square) ≫ object.hom = arrow ≫ (square ≫ object.hom)
          exact Category.assoc _ _ _
      homEquiv_naturality_right := by
        intro source first second square arrow
        rfl }

instance unit_faithful : (unit C).Faithful where
  map_injective same := congrArg Arrow.Hom.left same

instance unit_full : (unit C).Full where
  map_surjective square := by
    refine ⟨square.left, ?_⟩
    apply Arrow.hom_ext
    · rfl
    · simpa [unit] using (Arrow.w square)

/-- Full comprehension sends a dependent type to its very display arrow;
the source total category is already the actual arrow category. -/
def comprehension : Arrow C ⥤ Arrow C := 𝟭 _

instance comprehension_full : (comprehension C).Full := show (𝟭 (Arrow C)).Full from inferInstance
instance comprehension_faithful : (comprehension C).Faithful := show (𝟭 (Arrow C)).Faithful from inferInstance

variable {C}

theorem pullback_stronglyCartesian {first second : Arrow C}
    (square : first ⟶ second)
    (cartesian : IsPullback square.left first.hom second.hom square.right) :
    Arrow.rightFunc.IsStronglyCartesian square.right square where
  toIsHomLift := by
    change Arrow.rightFunc.IsHomLift (Arrow.rightFunc.map square) square
    infer_instance
  universal_property' := by
    intro object baseArrow supplied suppliedLift
    have := suppliedLift
    have base : baseArrow ≫ square.right = supplied.right :=
      IsHomLift.eq_of_isHomLift Arrow.rightFunc (baseArrow ≫ square.right) supplied
    let factor : object ⟶ first :=
      Arrow.homMk (cartesian.lift supplied.left (object.hom ≫ baseArrow) (by
        rw [Category.assoc, base, Arrow.w])) baseArrow (by simp)
    refine ⟨factor, ⟨?_, ?_⟩, ?_⟩
    · change Arrow.rightFunc.IsHomLift (Arrow.rightFunc.map factor) factor
      infer_instance
    · apply Arrow.hom_ext
      · exact cartesian.lift_fst _ _ _
      · exact base
    · intro candidate properties
      have := properties.1
      have candidateBase : candidate.right = baseArrow :=
        (IsHomLift.eq_of_isHomLift Arrow.rightFunc baseArrow candidate).symm
      apply Arrow.hom_ext
      · apply cartesian.hom_ext
        · simpa [factor] using congrArg Arrow.Hom.left properties.2
        · simp [factor, candidateBase]
      · exact candidateBase

def coneSquare {first second : Arrow C} (square : first ⟶ second)
    (cone : PullbackCone second.hom square.right) : Arrow.mk cone.snd ⟶ second :=
  Arrow.homMk cone.fst square.right cone.condition

instance coneSquare_lift {first second : Arrow C} (square : first ⟶ second)
    (cone : PullbackCone second.hom square.right) :
    Arrow.rightFunc.IsHomLift square.right (coneSquare square cone) := by
  change Arrow.rightFunc.IsHomLift (Arrow.rightFunc.map (coneSquare square cone)) _
  infer_instance

noncomputable def coneFactor {first second : Arrow C} (square : first ⟶ second)
    [Arrow.rightFunc.IsStronglyCartesian square.right square]
    (cone : PullbackCone second.hom square.right) : Arrow.mk cone.snd ⟶ first :=
  Functor.IsStronglyCartesian.map Arrow.rightFunc square.right square
    (g := 𝟙 first.right) (f' := square.right) (Category.id_comp _).symm
    (coneSquare square cone)

instance coneFactor_lift {first second : Arrow C} (square : first ⟶ second)
    [Arrow.rightFunc.IsStronglyCartesian square.right square]
    (cone : PullbackCone second.hom square.right) :
    Arrow.rightFunc.IsHomLift (𝟙 first.right) (coneFactor square cone) := by
  unfold coneFactor
  infer_instance

theorem coneFactor_comp {first second : Arrow C} (square : first ⟶ second)
    [Arrow.rightFunc.IsStronglyCartesian square.right square]
    (cone : PullbackCone second.hom square.right) :
    coneFactor square cone ≫ square = coneSquare square cone :=
  Functor.IsStronglyCartesian.fac Arrow.rightFunc square.right square
    (Category.id_comp _).symm (coneSquare square cone)

theorem coneFactor_base {first second : Arrow C} (square : first ⟶ second)
    [Arrow.rightFunc.IsStronglyCartesian square.right square]
    (cone : PullbackCone second.hom square.right) :
    (coneFactor square cone).right = 𝟙 first.right :=
  (IsHomLift.eq_of_isHomLift Arrow.rightFunc
    (a := Arrow.mk cone.snd) (𝟙 first.right) (coneFactor square cone)).symm

theorem stronglyCartesian_pullback {first second : Arrow C}
    (square : first ⟶ second)
    [Arrow.rightFunc.IsStronglyCartesian square.right square] :
    IsPullback square.left first.hom second.hom square.right := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (Arrow.w square)
    (fun cone => (coneFactor square cone).left) ?_ ?_ ?_)
  · intro cone
    exact congrArg Arrow.Hom.left (coneFactor_comp square cone)
  · intro cone
    have readout := Arrow.w (coneFactor square cone)
    rw [coneFactor_base] at readout
    change (coneFactor square cone).left ≫ first.hom = cone.snd ≫ 𝟙 first.right at readout
    rw [Category.comp_id] at readout
    exact readout
  · intro cone candidate firstProjection secondProjection
    let factor : Arrow.mk cone.snd ⟶ first :=
      Arrow.homMk candidate (𝟙 first.right) (by simpa using secondProjection)
    have : Arrow.rightFunc.IsHomLift (𝟙 first.right) factor := by
      change Arrow.rightFunc.IsHomLift (Arrow.rightFunc.map factor) factor
      infer_instance
    have same := Functor.IsStronglyCartesian.map_uniq Arrow.rightFunc
      square.right square (Category.id_comp _).symm (coneSquare square cone) factor (by
        apply Arrow.hom_ext
        · exact firstProjection
        · exact Category.id_comp _)
    simpa [factor, coneFactor] using congrArg Arrow.Hom.left same

theorem stronglyCartesian_iff_pullback {first second : Arrow C}
    (square : first ⟶ second) :
    Arrow.rightFunc.IsStronglyCartesian square.right square ↔
      IsPullback square.left first.hom second.hom square.right :=
  ⟨fun _ => stronglyCartesian_pullback square, pullback_stronglyCartesian square⟩

end Mettapedia.CategoryTheory.CodomainComprehension
