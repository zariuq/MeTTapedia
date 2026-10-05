import Mettapedia.TypeTheory.ContextualCoherentSmallMaps
import Mettapedia.TypeTheory.HostChoiceContextualSmallMaps
import Mettapedia.TypeTheory.ContextualSmallFamilyUniverseCoherence

/-!
# External-choice representation of proof-small contextual maps

The small-fibre predicate supplies surjective receipt enumerations. Their
kernel quotients are actual small types, and quotient elimination gives an
injective, surjective reading into the original fibre. The explicitly named
host-choice inverse turns that reading into a decoder. Transport through the
original map then constructs a coherent displayed family and its classifier.

No inverse is inferred constructively from surjectivity. These factories are
an optional external comparison: they neither install internal choice nor
change the original small universe or the ambient successor category.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.HostChoiceContextualSmallMapRepresentation

open CategoryTheory ContextualWitnessCover ContextualImageFactorization
open ContextualCoherentSmallMaps

universe u v w z
variable {D : Type u} [Category.{u} D]

def receiptKernel {X : Type v} (enumeration : Enumeration.{u, v} X) :
    Setoid enumeration.Carrier where
  r first second := enumeration.value first = enumeration.value second
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

abbrev ReceiptClass {X : Type v} (enumeration : Enumeration.{u, v} X) : Type u :=
  Quotient (receiptKernel enumeration)

def quotientReading {X : Type v} (enumeration : Enumeration.{u, v} X) :
    ReceiptClass enumeration → X :=
  Quotient.lift enumeration.value (fun _ _ same => same)

theorem quotientReading_injective {X : Type v} (enumeration : Enumeration.{u, v} X) :
    Function.Injective (quotientReading enumeration) := by
  intro first second
  refine Quotient.inductionOn₂ first second fun left right same => ?_
  exact Quotient.sound same

theorem quotientReading_surjective {X : Type v} (enumeration : Enumeration.{u, v} X) :
    Function.Surjective (quotientReading enumeration) := by
  intro value
  obtain ⟨code, same⟩ := enumeration.covered value
  exact ⟨Quotient.mk _ code, same⟩

/-- The kernel quotient is constructed; its inverse reading is selected
with external host choice. -/
noncomputable def selectedDecoder {X : Type v} (enumeration : Enumeration.{u, v} X) :
    ReceiptClass enumeration ≃ X :=
  Equiv.ofBijective (quotientReading enumeration)
    ⟨quotientReading_injective enumeration, quotientReading_surjective enumeration⟩

variable {X : D ⥤ Type v} {A : D ⥤ Type w}

noncomputable def selectedModel (operation : NaturalHom X A) (small : SmallFibres operation) :
    Data operation :=
  ofEquivs operation
    (fun point => ReceiptClass
      (HostChoiceContextualSmallMaps.selectedEnumerations operation small point.1 point.2))
    (fun point => selectedDecoder
      (HostChoiceContextualSmallMaps.selectedEnumerations operation small point.1 point.2))

theorem smallFibres_iff_coherent (operation : NaturalHom X A) :
    SmallFibres operation ↔ Nonempty (Data operation) := by
  constructor
  · intro small
    exact ⟨selectedModel operation small⟩
  · rintro ⟨model⟩
    exact model.smallFibres

noncomputable def classifier (operation : NaturalHom X A) (small : SmallFibres operation) :
    NaturalHom A ContextualSmallFamilyUniverse.universeFamily :=
  (selectedModel operation small).classifier

noncomputable abbrev ClassifiedPullback (operation : NaturalHom X A) (small : SmallFibres operation) :=
  pullback ContextualSmallFamilyUniverse.universalProjection (classifier operation small)

noncomputable def classificationForward (operation : NaturalHom X A) (small : SmallFibres operation) :
    NaturalHom X (ClassifiedPullback operation small) :=
  (selectedModel operation small).backward.comp
    (ContextualSmallFamilyUniverse.classificationForward (selectedModel operation small).family)

noncomputable def classificationBackward (operation : NaturalHom X A) (small : SmallFibres operation) :
    NaturalHom (ClassifiedPullback operation small) X :=
  (ContextualSmallFamilyUniverse.classificationBackward (selectedModel operation small).family).comp
    (selectedModel operation small).forward

theorem classification_left (operation : NaturalHom X A) (small : SmallFibres operation)
    (point : D) (argument : X.obj point) :
    (classificationBackward operation small).app point
      ((classificationForward operation small).app point argument) = argument := by
  exact (congrArg ((selectedModel operation small).forward.app point)
    (ContextualSmallFamilyUniverse.classification_left
      (selectedModel operation small).family point
      ((selectedModel operation small).backward.app point argument))).trans
        ((selectedModel operation small).backward_forward_value point argument)

theorem classification_right (operation : NaturalHom X A) (small : SmallFibres operation)
    (point : D) (argument : (ClassifiedPullback operation small).obj point) :
    (classificationForward operation small).app point
      ((classificationBackward operation small).app point argument) = argument := by
  exact (congrArg ((ContextualSmallFamilyUniverse.classificationForward
      (selectedModel operation small).family).app point)
    ((selectedModel operation small).forward_backward_value point
      ((ContextualSmallFamilyUniverse.classificationBackward
        (selectedModel operation small).family).app point argument))).trans
          (ContextualSmallFamilyUniverse.classification_right
            (selectedModel operation small).family point argument)

theorem classification_parameter (operation : NaturalHom X A) (small : SmallFibres operation) :
    (classificationForward operation small).comp
      (pullbackSecond ContextualSmallFamilyUniverse.universalProjection (classifier operation small)) =
        operation := by
  apply NaturalHom.ext
  intro point argument
  rfl

noncomputable def classificationEquiv (operation : NaturalHom X A) (small : SmallFibres operation)
    (point : D) : X.obj point ≃ (ClassifiedPullback operation small).obj point where
  toFun := (classificationForward operation small).app point
  invFun := (classificationBackward operation small).app point
  left_inv := classification_left operation small point
  right_inv := classification_right operation small point

noncomputable def classificationSectionEquiv (operation : NaturalHom X A) (small : SmallFibres operation) :
    X.sections ≃ (ClassifiedPullback operation small).sections where
  toFun := (classificationForward operation small).mapSection
  invFun := (classificationBackward operation small).mapSection
  left_inv term := by
    apply Subtype.ext
    funext point
    exact classification_left operation small point (term.val point)
  right_inv term := by
    apply Subtype.ext
    funext point
    exact classification_right operation small point (term.val point)

noncomputable def classified (operation : NaturalHom X A) (small : SmallFibres operation) :
    NaturalHom X ContextualSmallFamilyUniverse.universalTotal :=
  (classificationForward operation small).comp
    (pullbackFirst ContextualSmallFamilyUniverse.universalProjection (classifier operation small))

theorem classification_square (operation : NaturalHom X A) (small : SmallFibres operation) :
    (classified operation small).comp ContextualSmallFamilyUniverse.universalProjection =
      operation.comp (classifier operation small) := by
  apply NaturalHom.ext
  intro point argument
  exact (congrArg (fun map : NaturalHom (ClassifiedPullback operation small)
      ContextualSmallFamilyUniverse.universeFamily =>
        map.app point ((classificationForward operation small).app point argument))
    (pullback_square ContextualSmallFamilyUniverse.universalProjection (classifier operation small))).trans
      (congrArg ((classifier operation small).app point)
        (congrArg (fun map : NaturalHom X A => map.app point argument)
          (classification_parameter operation small)))

/-- The classifier square has its actual inverse universal map even for
test objects in an independently larger universe. -/
theorem classification_universal (operation : NaturalHom X A) (small : SmallFibres operation)
    {R : D ⥤ Type z} (top : NaturalHom R ContextualSmallFamilyUniverse.universalTotal)
    (parameter : NaturalHom R A)
    (square : top.comp ContextualSmallFamilyUniverse.universalProjection =
      parameter.comp (classifier operation small)) :
    ∃! lift : NaturalHom R X,
      lift.comp (classified operation small) = top ∧ lift.comp operation = parameter := by
  let pair := pullbackPair ContextualSmallFamilyUniverse.universalProjection
    (classifier operation small) top parameter square
  let lift := pair.comp (classificationBackward operation small)
  have inverse : lift.comp (classificationForward operation small) = pair := by
    apply NaturalHom.ext
    intro point argument
    exact classification_right operation small point (pair.app point argument)
  refine ⟨lift, ⟨?_, ?_⟩, ?_⟩
  · apply NaturalHom.ext
    intro point argument
    exact (congrArg ((pullbackFirst ContextualSmallFamilyUniverse.universalProjection
      (classifier operation small)).app point)
      (congrArg (fun map : NaturalHom R (ClassifiedPullback operation small) =>
        map.app point argument) inverse)).trans
          (congrArg (fun map : NaturalHom R ContextualSmallFamilyUniverse.universalTotal =>
            map.app point argument)
              (pullbackPair_first ContextualSmallFamilyUniverse.universalProjection
                (classifier operation small) top parameter square))
  · apply NaturalHom.ext
    intro point argument
    exact (congrArg (fun map : NaturalHom X A => map.app point (lift.app point argument))
      (classification_parameter operation small)).symm.trans
        ((congrArg ((pullbackSecond ContextualSmallFamilyUniverse.universalProjection
          (classifier operation small)).app point)
            (congrArg (fun map : NaturalHom R (ClassifiedPullback operation small) =>
              map.app point argument) inverse)).trans
                (congrArg (fun map : NaturalHom R A => map.app point argument)
                  (pullbackPair_second ContextualSmallFamilyUniverse.universalProjection
                    (classifier operation small) top parameter square)))
  · intro other laws
    apply NaturalHom.ext
    intro point argument
    have pairs : (classificationForward operation small).app point (other.app point argument) =
        pair.app point argument := by
      apply Subtype.ext
      refine Prod.ext ?_ ?_
      · exact congrArg (fun map : NaturalHom R ContextualSmallFamilyUniverse.universalTotal =>
          map.app point argument) laws.1
      · exact (congrArg (fun map : NaturalHom X A => map.app point (other.app point argument))
          (classification_parameter operation small)).trans
            (congrArg (fun map : NaturalHom R A => map.app point argument) laws.2)
    exact (classification_left operation small point (other.app point argument)).symm.trans
      (congrArg ((classificationBackward operation small).app point) pairs)

end Mettapedia.TypeTheory.HostChoiceContextualSmallMapRepresentation
