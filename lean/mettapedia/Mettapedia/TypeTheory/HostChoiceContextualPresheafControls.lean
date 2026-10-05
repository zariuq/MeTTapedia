import Mettapedia.TypeTheory.HostChoiceContextualPresheafAmbient
import Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerControls
import Mathlib.CategoryTheory.SingleObj

/-!
# Infinite and nonclassical controls for the optional presheaf model

A genuinely growing successor-bound presheaf is proof-small and has the
constructed universal classification. Its compatible section roundtrips
through both classification maps. The ambient Heyting implication fails
double-negation elimination, and an advancing natural-number cover is an epi
with a Collection square but has no natural splitting.

Receipt quotienting erases duplicated authored tags. The finite iterator
control computes the actual indexed natural-number recursion.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.HostChoiceContextualPresheafControls

open _root_.CategoryTheory ContextualWitnessCover ContextualImageFactorization ContextualCoherentSmallMaps
open ContextualPresheafExactness HostChoiceContextualSmallMapModel
open HostChoiceContextualPresheafAmbient
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open PowerClassPresheafDescent.Controls
open CoveredFuturePowerControls
open CoveredFuturePowerClassifier

namespace Growing

def collapse : NaturalHom raised (HostChoiceContextualSmallMapModel.terminal (D := Stagesᵒᵖ)) where
  app _ _ := PUnit.unit
  naturality _ _ := rfl

def enumeration (point : Stagesᵒᵖ) (value : (HostChoiceContextualSmallMapModel.terminal (D := Stagesᵒᵖ)).obj point) :
    Enumeration.{0, 1} (Fibre collapse point value) where
  Carrier := growingSource.obj point
  value code := ⟨ULift.up code, Subsingleton.elim (α := PUnit.{2}) _ _⟩
  covered receipt := ⟨receipt.val.down, Subtype.ext rfl⟩

theorem small : SmallFibres collapse := fun point value => ⟨enumeration point value⟩

def originSection : raised.sections :=
  ⟨fun point => ULift.up (⟨0, Nat.zero_lt_succ (stageIndex point)⟩, false), by
    intro first second step
    apply congrArg ULift.up
    exact Prod.ext (Fin.ext rfl) rfl⟩

/-- This is a whole compatible section comparison, not present support. -/
theorem classified_section_roundtrip :
    (HostChoiceContextualSmallMapRepresentation.classificationSectionEquiv collapse small).symm
      ((HostChoiceContextualSmallMapRepresentation.classificationSectionEquiv collapse small) originSection) =
        originSection :=
  (HostChoiceContextualSmallMapRepresentation.classificationSectionEquiv collapse small).symm_apply_apply originSection

def growthArrow : world 0 ⟶ world 1 := (homOfLE (Nat.zero_le 1)).op.op

def newArgument : raised.obj (world 1) := ULift.up (stageValue 1 1 (Nat.lt_succ_self 1) false)

theorem new_argument_has_no_old_preimage :
    ¬ ∃ argument : raised.obj (world 0), raised.map growthArrow argument = newArgument := by
  rintro ⟨argument, same⟩
  have index : argument.down.1.val = 1 := congrArg (fun value => value.down.1.val) same
  have bound := argument.down.1.isLt
  change argument.down.1.val < 1 at bound
  omega

theorem classified_new_argument_recovered :
    (HostChoiceContextualSmallMapRepresentation.classificationBackward collapse small).app (world 1)
      ((HostChoiceContextualSmallMapRepresentation.classificationForward collapse small).app (world 1) newArgument) =
        newArgument := HostChoiceContextualSmallMapRepresentation.classification_left collapse small (world 1) newArgument

end Growing

namespace Logic

abbrev ambient := HostChoiceContextualSmallMapModel.terminal (D := Stagesᵒᵖ)

def laterTruth : StablePredicate ambient where
  holds point := 1 ≤ stageIndex point.1
  closed step available := available.trans (growthLe step.1)

def falsity : StablePredicate ambient where
  holds _ := False
  closed _ := False.elim

def negative (predicate : StablePredicate ambient) : StablePredicate ambient := implication predicate falsity

def initial : ambient.Elements := ⟨world 0, PUnit.unit⟩

theorem laterTruth_absent_now : ¬ laterTruth.holds initial := Nat.not_succ_le_zero 0

theorem negative_empty (point : ambient.Elements) : ¬ (negative laterTruth).holds point := by
  intro negativeWitness
  let next := world (stageIndex point.1 + 1)
  let arrival : point.1 ⟶ next := (homOfLE (Nat.le_succ (stageIndex point.1))).op.op
  exact negativeWitness next arrival (Nat.succ_le_succ (Nat.zero_le _))

theorem doubleNegative_now : (negative (negative laterTruth)).holds initial :=
  fun _ _ negativeWitness => negative_empty _ negativeWitness

/-- External choice in the checking model does not make its internal
all-future subobject logic Boolean. -/
theorem internal_doubleNegation_fails : ¬ Included (negative (negative laterTruth)) laterTruth :=
  fun eliminate => laterTruth_absent_now (eliminate initial doubleNegative_now)

end Logic

namespace Receipts

def duplicate : Enumeration.{0, 1} PUnit.{2} where
  Carrier := Bool
  value _ := PUnit.unit
  covered _ := ⟨false, Subsingleton.elim _ _⟩

def retainedFalse : HostChoiceContextualSmallMapRepresentation.ReceiptClass duplicate := Quotient.mk _ false
def retainedTrue : HostChoiceContextualSmallMapRepresentation.ReceiptClass duplicate := Quotient.mk _ true

theorem duplicate_classes_equal : retainedFalse = retainedTrue := Quotient.sound rfl

theorem no_tag_recovery : ¬ ∃ recover : HostChoiceContextualSmallMapRepresentation.ReceiptClass duplicate → Bool,
    recover retainedFalse = false ∧ recover retainedTrue = true := by
  rintro ⟨recover, falseLaw, trueLaw⟩
  have impossible : false = true := falseLaw.symm.trans
    ((congrArg recover duplicate_classes_equal).trans trueLaw)
  exact Bool.false_ne_true impossible

end Receipts

namespace Advancing

abbrev Worlds := SingleObj (Multiplicative Nat)
def point : Worlds := SingleObj.star (Multiplicative Nat)
def loop (number : Nat) : point ⟶ point := Multiplicative.ofAdd number

def wide : Worlds ⥤ Type 1 where
  obj _ := ULift.{1} Nat
  map step := TypeCat.ofHom fun value => ULift.up (step.toAdd + value.down)
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro value
    apply congrArg ULift.up
    exact Nat.zero_add value.down
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro value
    apply congrArg ULift.up
    change second.toAdd + first.toAdd + value.down = second.toAdd + (first.toAdd + value.down)
    exact Nat.add_assoc _ _ _

def zeroWitness (_ : Worlds) : wide.obj point := ULift.up 0

theorem no_wide_section : ¬ Nonempty wide.sections := by
  rintro ⟨term⟩
  have fixed := congrArg ULift.down (term.property (loop 1))
  change 1 + (term.val point).down = (term.val point).down at fixed
  omega

abbrev parameters := HostChoiceContextualSmallMapModel.terminal (D := Worlds)

def cover : NaturalHom wide parameters where
  app _ _ := PUnit.unit
  naturality _ _ := rfl

theorem cover_onto : Cover cover := fun point _ => ⟨zeroWitness point, Subsingleton.elim (α := PUnit.{2}) _ _⟩

def parameterSection : parameters.sections := ⟨fun _ => PUnit.unit, fun _ => rfl⟩

theorem epi_has_no_natural_splitting :
    @Epi (Worlds ⥤ Type 1) _ wide parameters cover.toNatTrans ∧
      ¬ ∃ selected : NaturalHom parameters wide,
        selected.comp cover = ContextualSmallMapConstructions.identity parameters := by
  refine ⟨(natTrans_epi_iff_cover cover).mpr cover_onto, ?_⟩
  rintro ⟨selected, _⟩
  exact no_wide_section ⟨selected.mapSection parameterSection⟩

theorem full_collection_despite_no_split :
    Cover (ContextualCollectionGenerators.parameterMap (ContextualSmallMapConstructions.identity parameters) cover) ∧
      Cover (ContextualCollectionGenerators.comparison (ContextualSmallMapConstructions.identity parameters) cover) ∧
      SmallFibres (ContextualCollectionGenerators.collectedMap (ContextualSmallMapConstructions.identity parameters) cover) := by
  have diagram := HostChoiceContextualCollection.collection_in_successor_category
    (ContextualSmallMapConstructions.identity parameters) cover (small_identity parameters) cover_onto
  exact ⟨diagram.1, diagram.2.1, diagram.2.2.1⟩

end Advancing

namespace Iteration

abbrev parameters := HostChoiceContextualSmallMapModel.terminal (D := Stagesᵒᵖ)
abbrev numbers := HostChoiceContextualSmallMapModel.naturalNumbers (D := Stagesᵒᵖ)

def initial : NaturalHom parameters numbers where
  app _ _ := ULift.up 0
  naturality _ _ := rfl

def successorStep : NaturalHom (product parameters numbers) numbers where
  app _ value := ULift.up (value.2.down + 1)
  naturality _ _ := rfl

theorem actual_iteration (point : Stagesᵒᵖ) (parameter : parameters.obj point) (number : Nat) :
    iterateValue initial successorStep point parameter number = ULift.up number := by
  induction number with
  | zero => rfl
  | succ number hypothesis =>
      change ULift.up ((iterateValue initial successorStep point parameter number).down + 1) = _
      rw [hypothesis]

theorem thirtyTwo : (iterate initial successorStep).app (world 0) (PUnit.unit, ULift.up 32) = ULift.up 32 :=
  actual_iteration (world 0) PUnit.unit 32

end Iteration

end Mettapedia.TypeTheory.HostChoiceContextualPresheafControls
