import Mettapedia.TypeTheory.ContextualQuotientPullback
import Mathlib.CategoryTheory.Category.Preorder

/-!
# Infinite varying image and provenance controls

At world n, n+1 positions are available. Authored receipts additionally
retain a Boolean provenance tag; their declared reading erases that tag.
The carriers live at different raised host universes, while an actual small
receipt functor covers them. A new position appears at every extension.

The quotient has a constructed position decoder and transports whole
natural sections. Provenance is a natural operation of the source, but it
cannot descend through the declared reading, including after pullback.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualImageFactorizationControls

open CategoryTheory ContextualWitnessCover ContextualKernelQuotients ContextualImageFactorization

def receipts : Nat ⥤ Type where
  obj stage := Fin (stage + 1) × Bool
  map step := TypeCat.ofHom fun receipt =>
    (receipt.1.castLE (Nat.succ_le_succ (leOfHom step)), receipt.2)
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro receipt
    exact Prod.ext (Fin.ext rfl) rfl
  map_comp _ _ := by
    apply ConcreteCategory.hom_ext
    intro receipt
    exact Prod.ext (Fin.ext rfl) rfl

def authored : Nat ⥤ Type 1 where
  obj stage := ULift.{1, 0} (receipts.obj stage)
  map step := TypeCat.ofHom fun receipt => ULift.up (receipts.map step receipt.down)
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro receipt
    exact ULift.ext _ _ (Prod.ext (Fin.ext rfl) rfl)
  map_comp _ _ := by
    apply ConcreteCategory.hom_ext
    intro receipt
    exact ULift.ext _ _ (Prod.ext (Fin.ext rfl) rfl)

def observed : Nat ⥤ Type 2 where
  obj stage := ULift.{2, 0} (Fin (stage + 1))
  map step := TypeCat.ofHom fun value => ULift.up (value.down.castLE (Nat.succ_le_succ (leOfHom step)))
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro value
    exact ULift.ext _ _ (Fin.ext rfl)
  map_comp _ _ := by
    apply ConcreteCategory.hom_ext
    intro value
    exact ULift.ext _ _ (Fin.ext rfl)

def reading : NaturalHom authored observed where
  app _ receipt := ULift.up receipt.down.1
  naturality _ _ := rfl

def positions : Nat ⥤ Type 1 where
  obj stage := ULift.{1, 0} (Fin (stage + 1))
  map step := TypeCat.ofHom fun value => ULift.up (value.down.castLE (Nat.succ_le_succ (leOfHom step)))
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro value
    exact ULift.ext _ _ (Fin.ext rfl)
  map_comp _ _ := by
    apply ConcreteCategory.hom_ext
    intro value
    exact ULift.ext _ _ (Fin.ext rfl)

def positionOperation : NaturalHom authored positions where
  app _ receipt := ULift.up receipt.down.1
  naturality _ _ := rfl

theorem positionCompatible : Respects reading positionOperation := by
  intro stage first second same
  exact congrArg (fun value : observed.obj stage => (ULift.up value.down : positions.obj stage)) same

def quotientPosition : NaturalHom (quotient reading) positions := descend reading positionOperation positionCompatible

/-- This is explicit authored constructor data, not a representative
selected from a surjectivity proposition. -/
def positionReceipt : NaturalHom positions authored where
  app _ position := ULift.up (position.down, false)
  naturality _ _ := rfl

def positionClass : NaturalHom positions (quotient reading) := positionReceipt.comp (projection reading)

def quotientPositionEquiv (stage : Nat) : (quotient reading).obj stage ≃ positions.obj stage where
  toFun := quotientPosition.app stage
  invFun := positionClass.app stage
  left_inv value := by
    refine Quotient.inductionOn value fun receipt => ?_
    exact Quotient.sound (s := kernel reading stage) rfl
  right_inv _ := rfl

def tags : Nat ⥤ Type 1 where
  obj _ := ULift.{1, 0} Bool
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def provenance : NaturalHom authored tags where
  app _ receipt := ULift.up receipt.down.2
  naturality _ _ := rfl

def firstReceipt (tag : Bool) : authored.obj 0 := ULift.up (⟨0, Nat.zero_lt_one⟩, tag)

theorem receipts_differ : firstReceipt true ≠ firstReceipt false := by
  intro same
  have tag := congrArg (fun receipt : authored.obj 0 => receipt.down.2) same
  cases tag

theorem reading_identifies_receipts : reading.app 0 (firstReceipt true) = reading.app 0 (firstReceipt false) := rfl

theorem quotient_identifies_receipts :
    (projection reading).app 0 (firstReceipt true) = (projection reading).app 0 (firstReceipt false) :=
  (projection_eq_iff reading 0 _ _).mpr reading_identifies_receipts

theorem provenance_not_compatible : ¬ Respects reading provenance := by
  intro compatible
  have impossible := congrArg ULift.down (compatible 0 reading_identifies_receipts)
  cases impossible

theorem provenance_has_no_quotient_factor :
    ¬ ∃ factor : NaturalHom (quotient reading) tags, (projection reading).comp factor = provenance :=
  fun factor => provenance_not_compatible ((descends_iff reading provenance).mp factor)

def rawSection (tag : Bool) : authored.sections :=
  ⟨fun stage => ULift.up (⟨0, Nat.zero_lt_succ stage⟩, tag), by
    intro first second step
    exact ULift.ext _ _ (Prod.ext (Fin.ext rfl) rfl)⟩

theorem raw_sections_differ : rawSection true ≠ rawSection false := by
  intro same
  have impossible := congrArg (fun term : authored.sections => (term.val 0).down.2) same
  cases impossible

theorem whole_quotient_sections_agree :
    (projection reading).mapSection (rawSection true) = (projection reading).mapSection (rawSection false) := by
  apply (section_kernel_iff reading _ _).mpr
  apply Subtype.ext
  funext stage
  rfl

def smallCover : SmallCover.{0, 1} authored where
  carrier := receipts
  map := {
    app _ := ULift.up
    naturality _ _ := rfl }
  covered _ value := ⟨value.down, rfl⟩

def actualQuotientCover : SmallCover.{0, 1} (quotient reading) := quotientSmallCover reading smallCover

def actualImageCover : SmallCover.{0, 2} (image reading) := imageSmallCover reading smallCover

def fibreEnumeration (stage : Nat) (value : observed.obj stage) :
    Enumeration.{0, 1} (Fibre reading stage value) where
  Carrier := Bool
  value tag := ⟨ULift.up (value.down, tag), rfl⟩
  covered receipt := by
    refine ⟨receipt.val.down.2, Subtype.ext ?_⟩
    have position := congrArg ULift.down receipt.property
    exact ULift.ext _ _ (Prod.ext position.symm rfl)

theorem reading_smallFibres : SmallFibres reading := fun stage value => ⟨fibreEnumeration stage value⟩

def actualQuotientFibreEnumeration (stage : Nat) (value : observed.obj stage) :
    Enumeration.{0, 1} (Fibre (embedding reading) stage value) :=
  coveredFibreEnumeration reading (projection reading) (embedding reading)
    (factorization reading) (projection_surjective reading) stage value (fibreEnumeration stage value)

theorem actual_quotient_embedding_smallFibres : SmallFibres (embedding reading) :=
  smallFibres_quotient_embedding reading reading_smallFibres

theorem actual_image_inclusion_smallFibres : SmallFibres (imageInclusion reading) :=
  smallFibres_imageInclusion reading reading_smallFibres

/-- Cover codes retain authored provenance even when both codes enumerate
the same quotient receipt. A surjective enumeration is not a decoder. -/
theorem quotient_fibre_codes_duplicate (stage : Nat) (value : observed.obj stage) :
    (actualQuotientFibreEnumeration stage value).value true =
      (actualQuotientFibreEnumeration stage value).value false := by
  apply Subtype.ext
  exact Quotient.sound (s := kernel reading stage) rfl

theorem positionReceipt_not_surjective : ¬ Function.Surjective (positionReceipt.app 0) := by
  intro surjective
  obtain ⟨position, same⟩ := surjective (firstReceipt true)
  have impossible := congrArg (fun receipt : authored.obj 0 => receipt.down.2) same
  cases impossible

def omittedFibreReceipt : Fibre provenance 0 (ULift.up true) := ⟨firstReceipt true, rfl⟩

theorem omitted_fibre_not_cover_image :
    ¬ ∃ position : positions.obj 0, positionReceipt.app 0 position = omittedFibreReceipt.val := by
  rintro ⟨position, same⟩
  have impossible := congrArg (fun receipt : authored.obj 0 => receipt.down.2) same
  cases impossible

def toObserved : NaturalHom positions observed where
  app _ position := ULift.up position.down
  naturality _ _ := rfl

def actualPullbackFibreEnumeration (stage : Nat) (position : positions.obj stage) :
    Enumeration.{0, 1} (Fibre (pullbackSecond reading toObserved) stage position) :=
  pullbackFibreEnumeration reading toObserved stage position (fibreEnumeration stage (toObserved.app stage position))

theorem actual_pullback_smallFibres : SmallFibres (pullbackSecond reading toObserved) :=
  smallFibres_pullback reading toObserved reading_smallFibres

def extension (stage : Nat) : stage ⟶ stage + 1 := homOfLE (Nat.le_succ stage)

def newReceipt (stage : Nat) : authored.obj (stage + 1) :=
  ULift.up (⟨stage + 1, Nat.lt_succ_self (stage + 1)⟩, true)

theorem new_receipt_not_old_image (stage : Nat) :
    ¬ ∃ old : authored.obj stage, authored.map (extension stage) old = newReceipt stage := by
  rintro ⟨old, same⟩
  have index := congrArg (fun receipt : authored.obj (stage + 1) => receipt.down.1.val) same
  change old.down.1.val = stage + 1 at index
  have bound : old.down.1.val < stage + 1 := old.down.1.isLt
  rw [index] at bound
  exact Nat.lt_irrefl (stage + 1) bound

theorem quotient_new_position (stage : Nat) :
    (quotientPosition.app (stage + 1) ((projection reading).app (stage + 1) (newReceipt stage))).down.val =
      stage + 1 := rfl

def quotientPullback := ContextualQuotientPullback.source reading positionClass

def pulledPosition : NaturalHom quotientPullback positions :=
  (pullbackFirst (projection reading) positionClass).comp positionOperation

theorem pulledPositionCompatible :
    Respects (ContextualQuotientPullback.onto reading positionClass) pulledPosition := by
  intro stage first second same
  have firstClass := (projection_eq_iff reading stage first.val.1
    (positionReceipt.app stage first.val.2)).mp first.property
  have secondClass := (projection_eq_iff reading stage second.val.1
    (positionReceipt.app stage second.val.2)).mp second.property
  have positionsSame := firstClass.trans
    ((congrArg (toObserved.app stage) same).trans secondClass.symm)
  exact congrArg (fun value : observed.obj stage => (ULift.up value.down : positions.obj stage)) positionsSame

def pulledPositionFactor : NaturalHom positions positions :=
  ContextualQuotientPullback.descend reading positionClass pulledPosition pulledPositionCompatible

theorem pulledPositionFactor_value (stage : Nat) (position : positions.obj stage) :
    pulledPositionFactor.app stage position = position := by
  let receipt : quotientPullback.obj stage := ⟨(positionReceipt.app stage position, position), rfl⟩
  exact ContextualQuotientPullback.descend_beta reading positionClass pulledPosition pulledPositionCompatible
    stage receipt

def pulledProvenance : NaturalHom quotientPullback tags :=
  (pullbackFirst (projection reading) positionClass).comp provenance

theorem pulledProvenance_not_compatible :
    ¬ Respects (ContextualQuotientPullback.onto reading positionClass) pulledProvenance := by
  intro compatible
  let position : positions.obj 0 := ULift.up ⟨0, Nat.zero_lt_one⟩
  let first : quotientPullback.obj 0 := ⟨(firstReceipt true, position), quotient_identifies_receipts⟩
  let second : quotientPullback.obj 0 := ⟨(firstReceipt false, position), rfl⟩
  have impossible := congrArg ULift.down (compatible 0 (first := first) (second := second) rfl)
  cases impossible

end Mettapedia.TypeTheory.ContextualImageFactorizationControls
