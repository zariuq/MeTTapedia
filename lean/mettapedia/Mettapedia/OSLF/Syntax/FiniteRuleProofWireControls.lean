import Mettapedia.OSLF.Syntax.FiniteRuleProofWire

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.FiniteRuleProofWire
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists

namespace Controls
open RepeatedPremiseControl

def encodeShape : PackedShape presentation → Nat
  | ⟨_, .left⟩ => 0
  | ⟨_, .right⟩ => 1
  | ⟨_, .pair⟩ => 2

def decodeShape : Nat → Option (PackedShape presentation)
  | 0 => some ⟨false, .left⟩
  | 1 => some ⟨false, .right⟩
  | 2 => some ⟨true, .pair⟩
  | _ => none

def shapeCodec : ShapeCodec presentation where
  encode := encodeShape
  decode := decodeShape
  roundtrip := by rintro ⟨_, shape⟩; cases shape <;> rfl
  canonical := by
    intro label shape accepted
    cases label with
    | zero => cases accepted; rfl
    | succ label =>
        cases label with
        | zero => cases accepted; rfl
        | succ label =>
            cases label with
            | zero => cases accepted; rfl
            | succ label => cases accepted

def leftWire : Wire := .node 0 []
def rightWire : Wire := .node 1 []
def pairWire : Wire := .node 2 [leftWire, rightWire]
def swappedWire : Wire := .node 2 [rightWire, leftWire]

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
    check presentation shapeCodec true (.node 2 [leftWire]) = false := by
  simp [check, FiniteRuleLabelledProofWire.check, FiniteRuleLabelledProofWire.decodeAt,
    FiniteRuleLabelledProofWire.decode, shapeCodec, decodeShape,
    FiniteRuleLabelledProofWire.assemble, FiniteRuleLabelledProofWire.atIndex,
    leftWire, presentation]
theorem extra_child_rejected :
    check presentation shapeCodec true (.node 2 [leftWire,rightWire,leftWire]) = false := by
  simp [check, FiniteRuleLabelledProofWire.check, FiniteRuleLabelledProofWire.decodeAt,
    FiniteRuleLabelledProofWire.decode, shapeCodec, decodeShape,
    FiniteRuleLabelledProofWire.assemble, FiniteRuleLabelledProofWire.atIndex,
    leftWire, rightWire, presentation]
theorem wrong_child_judgment_rejected :
    check presentation shapeCodec true (.node 2 [pairWire,rightWire]) = false := by
  simp [check, FiniteRuleLabelledProofWire.check, FiniteRuleLabelledProofWire.decodeAt,
    FiniteRuleLabelledProofWire.decode, shapeCodec, decodeShape,
    FiniteRuleLabelledProofWire.assemble, FiniteRuleLabelledProofWire.atIndex,
    pairWire, leftWire, rightWire, presentation]
theorem unknown_rule_rejected :
    check presentation shapeCodec false (.node 3 []) = false := by
  simp [check, FiniteRuleLabelledProofWire.check, FiniteRuleLabelledProofWire.decodeAt,
    FiniteRuleLabelledProofWire.decode, shapeCodec, decodeShape]
theorem wrong_conclusion_rejected :
    check presentation shapeCodec false pairWire = false := by
  rw [← pair_encoding]
  simp [check, FiniteRuleLabelledProofWire.check, FiniteRuleLabelledProofWire.decodeAt,
    encode, FiniteRuleLabelledProofWire.decode_encode, FiniteRuleLabelledProofWire.atIndex]
theorem rejecting_a_wire_is_not_refuting_the_goal :
    check presentation shapeCodec false (.node 3 []) = false ∧
      Nonempty (presentation.Derivation () false) := ⟨unknown_rule_rejected, ⟨leftTree⟩⟩

#eval check presentation shapeCodec true pairWire
#eval check presentation shapeCodec true swappedWire
#eval check presentation shapeCodec true (.node 2 [pairWire,rightWire])
#eval check presentation shapeCodec false (.node 3 [])

end Controls

end Mettapedia.OSLF.Binding.FiniteRuleProofWire
