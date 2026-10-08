import Mettapedia.CategoryTheory.MonoArrowImageCartesian
import Mettapedia.CategoryTheory.ElementaryToposImageControls

/-!
# Nonidentity pullbacks and dependent image receipts

Even and odd base maps pull back the same display. The even map retains
inhabitants at every base value, while the odd map has no inhabitants.
The image square is a genuine pullback in both cases. Different positions
remain distinct in the even display and are identified by its image.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.ElementaryToposPullbackControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoArrowImageControls MonoArrowImageAdjunction

def evenShift : Nat ⟶ Nat := TypeCat.ofHom fun value => 2 * (value + 1)
def oddShift : Nat ⟶ Nat := TypeCat.ofHom fun value => 2 * value + 1

def Fibre (route : Nat ⟶ Nat) :=
  { pair : Receipt × Nat // readout pair.1 = route pair.2 }

def payload (route : Nat ⟶ Nat) : Fibre route ⟶ Receipt :=
  TypeCat.ofHom fun point => point.1.1

def baseValue (route : Nat ⟶ Nat) : Fibre route ⟶ Nat :=
  TypeCat.ofHom fun point => point.1.2

def square (route : Nat ⟶ Nat) : Arrow.mk (baseValue route) ⟶ Arrow.mk readout :=
  Arrow.homMk (payload route) route (by ext point; exact point.2)

theorem original_pullback (route : Nat ⟶ Nat) :
    IsPullback (payload route) (baseValue route) readout route := by
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · ext point
    exact point.2
  · intro first second projections
    apply Subtype.ext
    exact Prod.ext projections.1 projections.2
  · intro receipt value held
    exact ⟨⟨(receipt, value), held⟩, rfl, rfl⟩

theorem reindexed_image_pullback (route : Nat ⟶ Nat) :
    IsPullback (Limits.image.map (square route)) (Limits.image.ι (baseValue route))
      (Limits.image.ι readout) route :=
  image_square_pullback TypeSubobjectClassifier.classifier (square route)
    (original_pullback route)

theorem evenShift_not_identity : evenShift ≠ 𝟙 Nat := by
  intro same
  have zero := congrArg (fun arrow : Nat ⟶ Nat => arrow 0) same
  change 2 * (0 + 1) = 0 at zero
  contradiction

def positive (value : Nat) : Fibre evenShift :=
  ⟨(⟨value + 1, ⟨0, Nat.zero_lt_succ _⟩⟩, value), rfl⟩

theorem even_image_has_every_base_value (value : Nat) :
    ∃ point : Limits.image (baseValue evenShift),
      Limits.image.ι (baseValue evenShift) point = value := by
  refine ⟨factorThruImage (baseValue evenShift) (positive value), ?_⟩
  exact congrArg (fun arrow : Fibre evenShift ⟶ Nat => arrow (positive value))
    (Limits.image.fac (baseValue evenShift))

theorem odd_fibre_empty : IsEmpty (Fibre oddShift) := by
  refine ⟨fun point => ?_⟩
  have impossible : 2 * point.1.1.1 = 2 * point.1.2 + 1 := point.2
  have residues := congrArg (fun number : Nat => number % 2) impossible
  simp [Nat.add_mod] at residues

theorem odd_image_empty : IsEmpty (Limits.image (baseValue oddShift)) := by
  refine ⟨fun point => ?_⟩
  obtain ⟨input, _⟩ := (epi_iff_surjective (factorThruImage (baseValue oddShift))).mp
    inferInstance point
  exact odd_fibre_empty.false input

def firstPosition : Fibre evenShift := ⟨(firstReceipt, 0), rfl⟩
def secondPosition : Fibre evenShift := ⟨(secondReceipt, 0), rfl⟩

theorem positions_differ : firstPosition ≠ secondPosition := by
  intro same
  apply receipt_positions_differ
  exact congrArg (fun point : Fibre evenShift => point.1.1) same

theorem image_identifies_positions :
    factorThruImage (baseValue evenShift) firstPosition =
      factorThruImage (baseValue evenShift) secondPosition := by
  apply (mono_iff_injective (Limits.image.ι (baseValue evenShift))).mp inferInstance
  have first := congrArg (fun arrow : Fibre evenShift ⟶ Nat => arrow firstPosition)
    (Limits.image.fac (baseValue evenShift))
  have second := congrArg (fun arrow : Fibre evenShift ⟶ Nat => arrow secondPosition)
    (Limits.image.fac (baseValue evenShift))
  exact first.trans second.symm

theorem image_has_no_position_decoder :
    ¬ ∃ decode : Limits.image (baseValue evenShift) → Fibre evenShift,
      ∀ input, decode (factorThruImage (baseValue evenShift) input) = input := by
  rintro ⟨decode, recovers⟩
  apply positions_differ
  exact (recovers firstPosition).symm.trans
    ((congrArg decode image_identifies_positions).trans (recovers secondPosition))

end Mettapedia.CategoryTheory.ElementaryToposPullbackControls
