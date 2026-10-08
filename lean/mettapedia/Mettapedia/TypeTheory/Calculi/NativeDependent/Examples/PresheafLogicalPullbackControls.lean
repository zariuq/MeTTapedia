import Mettapedia.TypeTheory.DisplayedPresheafLogicalPullback
import Mettapedia.TypeTheory.NativeLocalParameterControls

/-!
# Origin and dependent witness controls for logical pullback

A noninjective program map sends every natural input to one public index.
The actual Frobenius comparison regroups a Boolean target witness with a
source receipt carrying `Fin (n + 1)`. It preserves the exact origin and
witness in both directions. Erasing the origin identifies receipts that
remain distinct in this logical construction.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.PresheafLogicalPullbackControls

open _root_.CategoryTheory MonoidalCategory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafSliceSubstitution DisplayedPresheafEvidenceTransport
open DisplayedPresheafLogicalPullback NativeLocalParameterControls

def publicPrograms : Worldᵒᵖ ⥤ Type := constant PUnit

def erase : naturals ⟶ publicPrograms where
  app _ := TypeCat.ofHom fun _ => PUnit.unit
  naturality := by intros; rfl

def publicWitnesses : DisplayedFamily publicPrograms :=
  (Functor.const _).obj Bool

def publicPoint : publicPrograms.Elements := ⟨world, PUnit.unit⟩
def sourcePoint (input : Nat) : naturals.Elements := ⟨world, input⟩

def supplied (input : Nat) : finiteFibre.obj (sourcePoint input) :=
  ⟨input, Nat.lt_succ_self _⟩

def pairReceipt (input : Nat) (external : Bool) :
    (transport erase (reindexDisplayed erase publicWitnesses ⊗ finiteFibre)).obj
      publicPoint :=
  (unit erase (reindexDisplayed erase publicWitnesses ⊗ finiteFibre)).app
    (sourcePoint input) ⟨external, supplied input⟩

noncomputable def splitReceipt (input : Nat) (external : Bool) :=
  (((frobenius erase publicWitnesses).natTrans.app finiteFibre).app publicPoint)
    (pairReceipt input external)

theorem comparison_keeps_origin_and_witness (input : Nat) (external : Bool) :
    splitReceipt input external =
      ⟨external, (unit erase finiteFibre).app (sourcePoint input) (supplied input)⟩ :=
  supplied_readout erase publicWitnesses finiteFibre (sourcePoint input)
    external (supplied input)

theorem inverse_recovers_entire_pair (input : Nat) (external : Bool) :
    regroup erase publicWitnesses finiteFibre publicPoint
      (splitReceipt input external) = pairReceipt input external :=
  regroup_after_comparison erase publicWitnesses finiteFibre publicPoint _

theorem first_input_readout : (splitReceipt 0 true).2.val.1 = 0 := by
  rw [comparison_keeps_origin_and_witness]
  rfl

theorem second_input_readout : (splitReceipt 1 true).2.val.1 = 1 := by
  rw [comparison_keeps_origin_and_witness]
  rfl

theorem supplied_value_readout (input : Nat) (external : Bool) :
    (splitReceipt input external).2.val.2.val = input := by
  rw [comparison_keeps_origin_and_witness]
  rfl

theorem noninjective_program_map : erase.app world (0 : Nat) = erase.app world 1 := rfl

theorem distinct_origin_receipts : pairReceipt 0 true ≠ pairReceipt 1 true := by
  intro same
  have origins := congrArg (fun receipt => receipt.val.1) same
  change (0 : Nat) = 1 at origins
  exact Nat.zero_ne_one origins

theorem retained_origins_prevent_erasure :
    (splitReceipt 0 true).1 = (splitReceipt 1 true).1 ∧
      splitReceipt 0 true ≠ splitReceipt 1 true := by
  constructor
  · rw [comparison_keeps_origin_and_witness, comparison_keeps_origin_and_witness]
  · intro same
    apply distinct_origin_receipts
    have inverse := congrArg (regroup erase publicWitnesses finiteFibre publicPoint) same
    simpa only [inverse_recovers_entire_pair] using inverse

end Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.PresheafLogicalPullbackControls
