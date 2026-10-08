import Mettapedia.CategoryTheory.MonoArrowImageComparison
import Mathlib.CategoryTheory.Limits.Types.Images
import Mathlib.CategoryTheory.Types.Basic

/-!
# Complete image elimination and its evidence boundary

An independently authored inclusion of even values receives a unique image
eliminator. The displayed inputs include dependent positions in `Fin (n+1)`.
The eliminator reads the value, while distinct positions have the same image;
no decoder from that image can reconstruct every original receipt.

A nonidentity square advances the value and its retained dependent position.
The induced image map has the same value readout. These are categorical
controls, with no assertion of a compiled runtime implementation.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.MonoArrowImageControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoArrowImageAdjunction

abbrev Receipt := (n : Nat) × Fin (n + 1)

def readout : Receipt ⟶ Nat := TypeCat.ofHom fun receipt => 2 * receipt.1

def evenInclusion : Nat ⟶ Nat := TypeCat.ofHom fun value => 2 * value

instance evenInclusion_mono : Mono evenInclusion := by
  apply (mono_iff_injective evenInclusion).mpr
  intro first second same
  change 2 * first = 2 * second at same
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) same

def evenPredicate : Predicate (Type) :=
  ⟨Arrow.mk evenInclusion, by change Mono evenInclusion; infer_instance⟩

def authoredEvidence : Arrow.mk readout ⟶ evenPredicate.obj :=
  Arrow.homMk (TypeCat.ofHom fun receipt => receipt.1) (𝟙 Nat) (by ext receipt; rfl)

theorem image_eliminator_retains_value (receipt : Receipt) :
    (descend authoredEvidence).hom.left
      ((unitSquare (Arrow.mk readout)).left receipt) = receipt.1 := by
  have factor := congrArg (fun square => square.left receipt) (descend_factor authoredEvidence)
  exact factor

theorem image_eliminator_unique
    (candidate : image.obj (Arrow.mk readout) ⟶ evenPredicate)
    (onReceipts : unitSquare (Arrow.mk readout) ≫ (comprehension (Type)).map candidate =
      authoredEvidence) : candidate = descend authoredEvidence :=
  descend_unique authoredEvidence candidate onReceipts

def firstReceipt : Receipt := ⟨1, ⟨0, by decide⟩⟩
def secondReceipt : Receipt := ⟨1, ⟨1, by decide⟩⟩

theorem receipt_positions_differ : firstReceipt ≠ secondReceipt := by
  intro same
  have position := congrArg (fun receipt : Receipt => receipt.2.val) same
  change (0 : Nat) = 1 at position
  omega

theorem distinct_positions_have_same_image :
    factorThruImage readout firstReceipt = factorThruImage readout secondReceipt := by
  apply (mono_iff_injective (Limits.image.ι readout)).mp inferInstance
  have first := congrArg (fun operation : Receipt ⟶ Nat => operation firstReceipt)
    (Limits.image.fac readout)
  have second := congrArg (fun operation : Receipt ⟶ Nat => operation secondReceipt)
    (Limits.image.fac readout)
  exact first.trans second.symm

theorem no_full_receipt_decoder :
    ¬ ∃ decode : Limits.image readout → Receipt,
      ∀ receipt, decode (factorThruImage readout receipt) = receipt := by
  rintro ⟨decode, recovers⟩
  apply receipt_positions_differ
  exact (recovers firstReceipt).symm.trans
    ((congrArg decode distinct_positions_have_same_image).trans (recovers secondReceipt))

def advance (receipt : Receipt) : Receipt :=
  ⟨receipt.1 + 1, receipt.2.castSucc⟩

def advanceSquare : Arrow.mk readout ⟶ Arrow.mk readout :=
  Arrow.homMk (TypeCat.ofHom advance) (TypeCat.ofHom fun value : Nat => value + 2) (by
    ext receipt
    change 2 * (receipt.1 + 1) = 2 * receipt.1 + 2
    omega)

theorem image_advance_readout (receipt : Receipt) :
    Limits.image.map advanceSquare (factorThruImage readout receipt) =
      factorThruImage readout (advance receipt) := by
  exact congrArg (fun operation => operation receipt) (Limits.image.factor_map advanceSquare)

theorem advance_preserves_position (receipt : Receipt) :
    (advance receipt).2.val = receipt.2.val := rfl

theorem advance_is_nonidentity : advance firstReceipt ≠ firstReceipt := by
  intro same
  have value := congrArg (fun receipt : Receipt => receipt.1) same
  change (1 : Nat) + 1 = 1 at value
  omega

theorem elimination_after_advance (receipt : Receipt) :
    (descend authoredEvidence).hom.left
      (Limits.image.map advanceSquare (factorThruImage readout receipt)) = receipt.1 + 1 := by
  rw [image_advance_readout]
  exact image_eliminator_retains_value (advance receipt)

end Mettapedia.CategoryTheory.MonoArrowImageControls
