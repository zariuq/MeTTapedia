import Mettapedia.Computability.SplitReadoutComparison
import Mettapedia.TypeTheory.JointObservationDependentDescent

/-!
# Contextual joint observations and their compatible image

An indexed family of natural observations of one presheaf has a joint target
presheaf.  The compatible joint image consists, at every context, of joint
views which arise from one source element.  Compatibility is stable under
substitution because every observation is natural.

Pointwise joint separation has two equivalent consequences:

* every pointwise dependent family descends to the compatible view; and
* the source presheaf is naturally isomorphic to its compatible joint image.

The natural isomorphism is not obtained by assuming an arbitrary choice of
representatives is coherent.  Its forward direction is the authored joint
observation, and naturality is inherited from the observation family;
uniqueness supplied by joint separation determines the inverse.

This is a contextual comparison theorem.  It does not yet construct a CwF
morphism, transport comprehension, or claim that all tuples in the
unrestricted product of target presheaves are compatible.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.ContextualJointObservation

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.TypeTheory.JointObservationDependentDescent
open Mettapedia.TypeTheory.UniversalDependentFamilyDescent

universe uContext vContext uFace uFibre

variable {Context : Type uContext} [Category.{vContext} Context]
variable {source : Face.{uContext, vContext, uFace} Context}

/-- A family of contextual observations with a common source presheaf. -/
structure ContextualObservationFamily
    (source : Face.{uContext, vContext, uFace} Context) where
  Index : Type uFace
  target : Index -> Face.{uContext, vContext, uFace} Context
  observe : (index : Index) -> source ⟶ target index

namespace ContextualObservationFamily

variable (family : ContextualObservationFamily source)

/-- The pointwise dependent product of all target faces. -/
def jointFace : Face.{uContext, vContext, uFace} Context where
  obj context := (index : family.Index) -> (family.target index).obj context
  map substitution := TypeCat.ofHom fun views index =>
    (family.target index).map substitution (views index)
  map_id context := by
    apply ConcreteCategory.hom_ext
    intro views
    funext index
    exact congrArg (fun map => map (views index))
      ((family.target index).map_id context)
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro views
    funext index
    exact congrArg (fun map => map (views index))
      ((family.target index).map_comp first second)

/-- All contextual observations assembled into one natural transformation. -/
def jointObservation : source ⟶ jointFace family where
  app context := TypeCat.ofHom fun sourceElement index =>
    (family.observe index).app context sourceElement
  naturality := by
    intro first second substitution
    apply ConcreteCategory.hom_ext
    intro sourceElement
    funext index
    exact congrArg
      (fun map => map sourceElement)
      ((family.observe index).naturality substitution)

/-- The ordinary observation family seen at one context. -/
def atContext (context : Contextᵒᵖ) :
    ObservationFamily (source.obj context) where
  Index := family.Index
  Target index := (family.target index).obj context
  observe index := (family.observe index).app context

@[simp] theorem atContext_joint
    (context : Contextᵒᵖ) (sourceElement : source.obj context) :
    (atContext family context).joint sourceElement =
      (jointObservation family).app context sourceElement :=
  by
    funext index
    rfl

/-- The observations jointly separate source values at every context. -/
def PointwiseJointlySeparating : Prop :=
  forall context, (atContext family context).JointlySeparating

/-- The compatible joint-image presheaf.  A view includes evidence that it is
the joint observation of a source element at the same context. -/
def compatibleFace : Face.{uContext, vContext, uFace} Context where
  obj context := CompatibleImage ((jointObservation family).app context)
  map substitution := TypeCat.ofHom fun view => by
    refine ⟨(jointFace family).map substitution view.1, ?_⟩
    obtain ⟨sourceElement, realizes⟩ := view.2
    refine ⟨source.map substitution sourceElement, ?_⟩
    calc
      (jointObservation family).app _
          (source.map substitution sourceElement) =
          (jointFace family).map substitution
            ((jointObservation family).app _ sourceElement) := by
        exact congrArg (fun map => map sourceElement)
          ((jointObservation family).naturality substitution)
      _ = (jointFace family).map substitution view.1 := by
        exact congrArg ((jointFace family).map substitution) realizes
  map_id context := by
    apply ConcreteCategory.hom_ext
    intro view
    apply Subtype.ext
    exact congrArg (fun map => map view.1) ((jointFace family).map_id context)
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro view
    apply Subtype.ext
    exact congrArg (fun map => map view.1)
      ((jointFace family).map_comp first second)

/-- The source maps naturally to its compatible joint image. -/
def toCompatible : source ⟶ compatibleFace family where
  app context := TypeCat.ofHom fun sourceElement =>
    ⟨(jointObservation family).app context sourceElement,
      ⟨sourceElement, rfl⟩⟩
  naturality := by
    intro first second substitution
    apply ConcreteCategory.hom_ext
    intro sourceElement
    apply Subtype.ext
    exact congrArg (fun map => map sourceElement)
      ((jointObservation family).naturality substitution)

/-- Pointwise injectivity of the natural compatible-image map is exactly
joint separation. -/
theorem toCompatible_injective_iff_jointlySeparating
    (context : Contextᵒᵖ) :
    Function.Injective ((toCompatible family).app context) <->
      (atContext family context).JointlySeparating := by
  constructor
  · intro injective left right sameJoint
    apply injective
    apply Subtype.ext
    exact sameJoint
  · intro separates left right sameCompatible
    apply separates
    exact congrArg Subtype.val sameCompatible

/-- Every compatible joint view has a source representative, by construction. -/
theorem toCompatible_surjective (context : Contextᵒᵖ) :
    Function.Surjective ((toCompatible family).app context) := by
  intro view
  obtain ⟨sourceElement, realizes⟩ := view.2
  refine ⟨sourceElement, ?_⟩
  apply Subtype.ext
  exact realizes

/-- Under pointwise joint separation, every component of the authored map is
an equivalence. -/
noncomputable def componentEquiv
    (separates : family.PointwiseJointlySeparating)
    (context : Contextᵒᵖ) :
    source.obj context ≃ (compatibleFace family).obj context :=
  Equiv.ofBijective ((toCompatible family).app context)
    ⟨(toCompatible_injective_iff_jointlySeparating family context).2
        (separates context),
      toCompatible_surjective family context⟩

/-- **Contextual joint-conservativity theorem.**  Pointwise joint separation
upgrades the authored compatible-image map to a natural isomorphism. -/
noncomputable def compatibleIso
    (separates : family.PointwiseJointlySeparating) :
    source ≅ compatibleFace family :=
  NatIso.ofComponents
    (fun context => (componentEquiv family separates context).toIso)
    (by
      intro first second substitution
      ext sourceElement
      apply Subtype.ext
      exact congrArg (fun map => map sourceElement)
        ((jointObservation family).naturality substitution))

/-- Every pointwise dependent family descends through the compatible views. -/
def PointwiseAllFamiliesDescend : Prop :=
  forall context,
    AllFamiliesDescend.{uFace, uFace, uFibre}
      (atContext family context).compatibleReadout

/-- Pointwise universal dependent-family descent is exactly pointwise joint
separation. -/
theorem pointwiseAllFamiliesDescend_iff_jointlySeparating :
    family.PointwiseAllFamiliesDescend <->
      family.PointwiseJointlySeparating := by
  constructor
  · intro descends context
    exact
      (ObservationFamily.allFamiliesDescend_iff_jointlySeparating
        (atContext family context)).1 (descends context)
  · intro separates context
    exact
      (ObservationFamily.allFamiliesDescend_iff_jointlySeparating
        (atContext family context)).2 (separates context)

end ContextualObservationFamily

/-! ## Constant contextual controls -/

namespace Canary

open Mettapedia.Computability.SplitReadoutComparison
open Mettapedia.TypeTheory.JointObservationDependentDescent.Canary

def pairSource : Face.{0, 0, 0} SplitReadoutComparison.Context :=
  sourceFace (Bool × Bool)

def boolTarget : Face.{0, 0, 0} SplitReadoutComparison.Context :=
  targetFace Bool

def coordinateMap (coordinate : Coordinate) : pairSource ⟶ boolTarget :=
  (Functor.const SplitReadoutComparison.Contextᵒᵖ).map
    (↾(match coordinate with
      | .left => Prod.fst
      | .right => Prod.snd : Bool × Bool -> Bool))

/-- Two natural coordinate projections of a constant contextual face. -/
def contextualCoordinates : ContextualObservationFamily pairSource where
  Index := Coordinate
  target _ := boolTarget
  observe := coordinateMap

theorem contextualCoordinates_pointwiseSeparating :
    contextualCoordinates.PointwiseJointlySeparating := by
  intro context first second sameViews
  apply Prod.ext
  · exact congrFun sameViews .left
  · exact congrFun sameViews .right

/-- The two individually lossy projections jointly recover the source as a
presheaf, not merely as unrelated carriers at each context. -/
noncomputable def contextualCoordinates_iso :
    pairSource ≅ contextualCoordinates.compatibleFace :=
  contextualCoordinates.compatibleIso
    contextualCoordinates_pointwiseSeparating

theorem contextualCoordinates_allFamiliesDescend :
    contextualCoordinates.PointwiseAllFamiliesDescend :=
  (contextualCoordinates.pointwiseAllFamiliesDescend_iff_jointlySeparating).2
    contextualCoordinates_pointwiseSeparating

def duplicateMap (_coordinate : Coordinate) : pairSource ⟶ boolTarget :=
  (Functor.const SplitReadoutComparison.Contextᵒᵖ).map
    (↾(Prod.fst : Bool × Bool -> Bool))

def contextualDuplicate : ContextualObservationFamily pairSource where
  Index := Coordinate
  target _ := boolTarget
  observe := duplicateMap

theorem contextualDuplicate_not_pointwiseSeparating :
    ¬ contextualDuplicate.PointwiseJointlySeparating := by
  intro separates
  let context : SplitReadoutComparison.Contextᵒᵖ :=
    Opposite.op (Discrete.mk PUnit.unit)
  have injective := separates context
  have sameViews :
      (contextualDuplicate.atContext context).joint (false, false) =
        (contextualDuplicate.atContext context).joint (false, true) := by
    funext coordinate
    cases coordinate <;> rfl
  have same := injective sameViews
  exact Bool.false_ne_true (congrArg Prod.snd same)

theorem contextualDuplicate_not_allFamiliesDescend :
    ¬ contextualDuplicate.PointwiseAllFamiliesDescend := by
  rw [contextualDuplicate.pointwiseAllFamiliesDescend_iff_jointlySeparating]
  exact contextualDuplicate_not_pointwiseSeparating

/-- Paired contextual control: genuine complementary views give a natural
isomorphism and universal pointwise descent; duplicated views do not. -/
theorem contextual_jointObservation_boundary :
    Nonempty (pairSource ≅ contextualCoordinates.compatibleFace) ∧
      contextualCoordinates.PointwiseAllFamiliesDescend ∧
      (¬ contextualDuplicate.PointwiseJointlySeparating) ∧
      (¬ contextualDuplicate.PointwiseAllFamiliesDescend) :=
  ⟨⟨contextualCoordinates_iso⟩,
    contextualCoordinates_allFamiliesDescend,
    contextualDuplicate_not_pointwiseSeparating,
    contextualDuplicate_not_allFamiliesDescend⟩

end Canary

#print axioms ContextualObservationFamily.toCompatible_injective_iff_jointlySeparating
#print axioms ContextualObservationFamily.toCompatible_surjective
#print axioms ContextualObservationFamily.compatibleIso
#print axioms ContextualObservationFamily.pointwiseAllFamiliesDescend_iff_jointlySeparating
#print axioms Canary.contextualCoordinates_iso
#print axioms Canary.contextualDuplicate_not_allFamiliesDescend
#print axioms Canary.contextual_jointObservation_boundary

end Mettapedia.Computability.ContextualJointObservation
