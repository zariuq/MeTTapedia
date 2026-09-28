import Mettapedia.OSLF.Syntax.FiniteRuleLabelledProofWire

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists

namespace Controls
open RepeatedPremiseControl

abbrev Label := Nat × Bool

def encodeShape : PackedShape presentation → Label
  | ⟨_, .left⟩ => (0, false)
  | ⟨_, .right⟩ => (0, true)
  | ⟨_, .pair⟩ => (1, false)

def decodeShape : Label → Option (PackedShape presentation)
  | (0, false) => some ⟨false, .left⟩
  | (0, true) => some ⟨false, .right⟩
  | (1, false) => some ⟨true, .pair⟩
  | _ => none

def shapeCodec : ShapeCodec presentation Label where
  encode := encodeShape
  decode := decodeShape
  roundtrip := by rintro ⟨_, shape⟩; cases shape <;> rfl
  canonical := by
    rintro ⟨n, bit⟩ shape accepted
    cases n with
    | zero => cases bit <;> cases accepted <;> rfl
    | succ n =>
        cases n with
        | zero => cases bit <;> cases accepted; rfl
        | succ n => cases bit <;> cases accepted

def leftWire : Wire Label := .node (0, false) []
def rightWire : Wire Label := .node (0, true) []
def pairWire : Wire Label := .node (1, false) [leftWire, rightWire]
def swappedWire : Wire Label := .node (1, false) [rightWire, leftWire]

theorem left_encoding : encode presentation shapeCodec leftTree = leftWire := rfl
theorem right_encoding : encode presentation shapeCodec rightTree = rightWire := rfl
theorem pair_encoding : encode presentation shapeCodec pairLeftRight = pairWire := rfl
theorem swapped_encoding : encode presentation shapeCodec pairRightLeft = swappedWire := rfl

theorem pair_accepted : check presentation shapeCodec true pairWire = true :=
  (check_iff ..).mpr ⟨pairLeftRight, pair_encoding⟩
theorem swapped_accepted : check presentation shapeCodec true swappedWire = true :=
  (check_iff ..).mpr ⟨pairRightLeft, swapped_encoding⟩

theorem swapped_history_distinct :
    encodePacked presentation shapeCodec ⟨true,pairLeftRight⟩ ≠
      encodePacked presentation shapeCodec ⟨true,pairRightLeft⟩ := by
  intro equal
  have packed := encodePacked_injective presentation shapeCodec equal
  have trees := Sigma.mk.inj_iff.mp packed
  exact pair_order_matters (eq_of_heq trees.2)

theorem missing_child_rejected :
    check presentation shapeCodec true (.node (1, false) [leftWire]) = false := by
  simp [check, decodeAt, decode, shapeCodec, decodeShape, assemble, atIndex,
    leftWire, presentation]
theorem extra_child_rejected :
    check presentation shapeCodec true (.node (1, false) [leftWire,rightWire,leftWire]) = false := by
  simp [check, decodeAt, decode, shapeCodec, decodeShape, assemble, atIndex,
    leftWire, rightWire, presentation]
theorem wrong_child_judgment_rejected :
    check presentation shapeCodec true (.node (1, false) [pairWire,rightWire]) = false := by
  simp [check, decodeAt, decode, shapeCodec, decodeShape, assemble, atIndex,
    pairWire, leftWire, rightWire, presentation]
theorem unknown_rule_rejected :
    check presentation shapeCodec false (.node (1, true) []) = false := by
  simp [check, decodeAt, decode, shapeCodec, decodeShape]
theorem wrong_conclusion_rejected :
    check presentation shapeCodec false pairWire = false := by
  rw [← pair_encoding]
  simp [check, decodeAt, decode_encode, atIndex]
theorem rejecting_a_wire_is_not_refuting_the_goal :
    check presentation shapeCodec false (.node (1, true) []) = false ∧
      Nonempty (presentation.Derivation () false) := ⟨unknown_rule_rejected, ⟨leftTree⟩⟩

#eval check presentation shapeCodec true pairWire
#eval check presentation shapeCodec true swappedWire
#eval check presentation shapeCodec true (.node (1, false) [pairWire,rightWire])
#eval check presentation shapeCodec false (.node (1, true) [])

end Controls

end Mettapedia.OSLF.Binding.FiniteRuleLabelledProofWire
