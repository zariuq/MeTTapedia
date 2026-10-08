import Mettapedia.CategoryTheory.ElementaryToposImages
import Mettapedia.CategoryTheory.TypeSubobjectClassifier
import Mettapedia.CategoryTheory.MonoArrowImageControls
import Mathlib.CategoryTheory.Monoidal.Closed.Types

/-!
# Independent controls for the elementary topos image construction

The two-equalizer image is compared with an independently proved image whose
domain consists of the even output values. The comparison reads the actual
input value and excludes odd outputs. Distinct dependent input positions
have the same constructed image, so that image cannot decode every receipt.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.ElementaryToposImageControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoArrowImageControls

abbrev classifier := TypeSubobjectClassifier.classifier

def evenFactorisation : MonoFactorisation readout where
  I := Nat
  m := evenInclusion
  e := TypeCat.ofHom fun receipt => receipt.1
  fac := rfl

def independentEvenImage : IsImage evenFactorisation where
  lift alternative := TypeCat.ofHom fun value =>
    alternative.e ⟨value, ⟨0, Nat.zero_lt_succ _⟩⟩
  lift_fac alternative := by
    ext value
    exact congrArg (fun arrow : Receipt ⟶ Nat => arrow ⟨value, ⟨0, Nat.zero_lt_succ _⟩⟩)
      alternative.fac

def constructedEvenIso : ElementaryToposImages.imageObject classifier readout ≅ Nat :=
  IsImage.isoExt (ElementaryToposImages.isImage classifier readout) independentEvenImage

theorem constructed_image_reads_value (receipt : Receipt) :
    constructedEvenIso.hom (ElementaryToposImages.factor classifier readout receipt) =
      receipt.1 := by
  exact congrArg (fun arrow : Receipt ⟶ Nat => arrow receipt)
    ((ElementaryToposImages.isImage classifier readout).fac_lift evenFactorisation)

theorem constructed_image_contains_even (value : Nat) :
    ∃ point, ElementaryToposImages.inclusion classifier readout point = 2 * value := by
  refine ⟨ElementaryToposImages.factor classifier readout ⟨value, ⟨0, Nat.zero_lt_succ _⟩⟩, ?_⟩
  exact congrArg (fun arrow : Receipt ⟶ Nat => arrow ⟨value, ⟨0, Nat.zero_lt_succ _⟩⟩)
    (ElementaryToposImages.factor_inclusion classifier readout)

theorem constructed_image_excludes_odd (value : Nat) :
    ¬ ∃ point, ElementaryToposImages.inclusion classifier readout point = 2 * value + 1 := by
  rintro ⟨point, odd⟩
  have valueReading := congrArg
    (fun arrow : ElementaryToposImages.imageObject classifier readout ⟶ Nat => arrow point)
    ((ElementaryToposImages.isImage classifier readout).lift_fac evenFactorisation)
  change 2 * constructedEvenIso.hom point =
    ElementaryToposImages.inclusion classifier readout point at valueReading
  rw [odd] at valueReading
  have impossible : 2 * (constructedEvenIso.hom point : Nat) = 2 * value + 1 := valueReading
  have residues := congrArg (fun number : Nat => number % 2) impossible
  simp [Nat.add_mod] at residues

theorem constructed_image_identifies_positions :
    ElementaryToposImages.factor classifier readout firstReceipt =
      ElementaryToposImages.factor classifier readout secondReceipt := by
  apply (mono_iff_injective (ElementaryToposImages.inclusion classifier readout)).mp inferInstance
  have first := congrArg (fun arrow : Receipt ⟶ Nat => arrow firstReceipt)
    (ElementaryToposImages.factor_inclusion classifier readout)
  have second := congrArg (fun arrow : Receipt ⟶ Nat => arrow secondReceipt)
    (ElementaryToposImages.factor_inclusion classifier readout)
  exact first.trans second.symm

theorem constructed_image_has_no_full_receipt_decoder :
    ¬ ∃ decode : ElementaryToposImages.imageObject classifier readout → Receipt,
      ∀ receipt, decode (ElementaryToposImages.factor classifier readout receipt) = receipt := by
  rintro ⟨decode, recovers⟩
  apply receipt_positions_differ
  exact (recovers firstReceipt).symm.trans
    ((congrArg decode constructed_image_identifies_positions).trans (recovers secondReceipt))

end Mettapedia.CategoryTheory.ElementaryToposImageControls
