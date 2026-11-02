import Mettapedia.Logic.HOL.VectorChildArrayBoundary
import Mettapedia.Logic.HOL.VectorChildArrayControls

/-!
# Uniform boundary proofs in the independent Nat/list model

Source membership and numeral sums are constructed independently. The general
open-vector theorems then produce the trailing and padding equations for every
concrete list and suffix offset. Wrong values and treating zero suffix offset
as padding are ruled out by the independently realized model.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.VectorChildArrays.BoundaryControls
open Controls

def full : ClosedTerm Const (E ⇒ .prop) := .lam .top

def fullMember (element : ClosedTerm Const E) : ProofSyntax Const assumptions (.app full element) :=
  .impE (.eqPropER (.beta element .top)) .topI

theorem fullMember_free (element : ClosedTerm Const E) : (fullMember element).FunctionExtensionalityFree := by
  trivial

def member : (values : List Nat) → ProofSyntax Const assumptions
    (ops.toSignature.member full (numeral values.length) (vector values))
  | [] => ops.toSignature.nil_member full
  | head :: tail => ops.toSignature.cons_member full (numeral tail.length) (.const (.element head)) (vector tail)
      (fullMember _) (member tail)

theorem member_free (values : List Nat) : (member values).FunctionExtensionalityFree := by
  induction values with
  | nil => exact ops.toSignature.nil_member_free full
  | cons head tail previous => exact ops.toSignature.cons_member_free _ _ _ _ _ _ (fullMember_free _) previous

def sumNumerals (first : Nat) : (count : Nat) → ProofSyntax Const assumptions
    (ops.sumAt (numeral first) (numeral count) (numeral (first + count)))
  | 0 => SuccessorOrder.sumZero ops.successor ops.zero (numeral first)
  | count + 1 => SuccessorOrder.sumStep ops.successor ops.zero (numeral first) (numeral count)
      (numeral (first + count)) (sumNumerals first count)

theorem sumNumerals_free (first count : Nat) : (sumNumerals first count).FunctionExtensionalityFree := by
  induction count with
  | zero => exact SuccessorOrder.sumZero_free _ _ _
  | succ count previous => exact SuccessorOrder.sumStep_free _ _ _ _ _ _ previous

def trailing (values : List Nat) : ProofSyntax Const assumptions
    (.eq (.app (children values) (numeral (values.length + 1))) (.const (.element 11))) :=
  ops.mixedTrailing full (numeral values.length) (.const (.element 5)) (vector values)
    (.const (.element 11)) (.const (.element 0)) premises (member values)

theorem trailing_free (values : List Nat) : (trailing values).FunctionExtensionalityFree :=
  ops.mixedTrailing_free _ _ _ _ _ _ premises (member values) premises_free (member_free values)

def padding (values : List Nat) (offset : Nat) : ProofSyntax Const assumptions
    (.eq (.app (children values) (numeral (values.length + (offset + 1) + 1))) (.const (.element 0))) :=
  ops.mixedPadding full (numeral values.length) (.const (.element 5)) (vector values)
    (.const (.element 11)) (.const (.element 0)) (numeral offset) (numeral (values.length + (offset + 1)))
    premises (member values) (sumNumerals values.length (offset + 1))

theorem padding_free (values : List Nat) (offset : Nat) : (padding values offset).FunctionExtensionalityFree :=
  ops.mixedPadding_free _ _ _ _ _ _ _ _ premises (member values) (sumNumerals values.length (offset + 1))
    premises_free (member_free values) (sumNumerals_free values.length (offset + 1))

theorem numeral_denote (value : Nat) : model.denote (numeral value) emptyValues = ULift.up value := by
  induction value with
  | zero => rfl
  | succ value previous =>
      change ULift.up ((model.denote (numeral value) emptyValues).down + 1) = ULift.up (value + 1)
      rw [previous]

theorem trailing_value (values : List Nat) :
    (model.denote (children values) emptyValues (ULift.up (values.length + 1))).down = 11 := by
  have equation := sound (trailing values)
  change model.denote (children values) emptyValues (model.denote (numeral (values.length + 1)) emptyValues) = ULift.up 11 at equation
  rw [numeral_denote] at equation
  exact congrArg ULift.down equation

theorem padding_value (values : List Nat) (offset : Nat) :
    (model.denote (children values) emptyValues (ULift.up (values.length + (offset + 1) + 1))).down = 0 := by
  have equation := sound (padding values offset)
  change model.denote (children values) emptyValues
    (model.denote (numeral (values.length + (offset + 1) + 1)) emptyValues) = ULift.up 0 at equation
  rw [numeral_denote] at equation
  exact congrArg ULift.down equation

theorem zero_offset_is_not_padding : ¬ Nonempty (ProofSyntax Const assumptions
    (.imp (ops.sumAt (numeral 0) (numeral 0) (numeral 0))
      (.eq (.app (children []) (numeral 1)) (.const (.element 0))))) := by
  rintro ⟨claimed⟩
  have wrongProof := ProofSyntax.impE claimed (sumNumerals 0 0)
  have wrong : (model.denote (children []) emptyValues (ULift.up 1)).down = 0 :=
    congrArg ULift.down (sound wrongProof)
  have actual := trailing_value []
  exact (by decide : (11:Nat) ≠ 0) (actual.symm.trans wrong)

theorem unguarded_padding_refused : ¬ Nonempty (ProofSyntax Const assumptions
    (.eq (.app (children [7,9]) (numeral 1)) (.const (.element 0)))) := by
  rintro ⟨claimed⟩
  have wrong : (model.denote (children [7,9]) emptyValues (ULift.up 1)).down = 0 :=
    congrArg ULift.down (sound claimed)
  exact (by decide : (7:Nat) ≠ 0) (twoDifferentChildren.1.symm.trans wrong)

theorem wrong_trailing_child_refused : ¬ Nonempty (ProofSyntax Const assumptions
    (.eq (.app (children [7,9]) (numeral 3)) (.const (.element 9)))) := by
  rintro ⟨claimed⟩
  have wrong : (model.denote (children [7,9]) emptyValues (ULift.up 3)).down = 9 :=
    congrArg ULift.down (sound claimed)
  exact (by decide : (11:Nat) ≠ 9) ((trailing_value [7,9]).symm.trans wrong)

#print axioms trailing_free
#print axioms padding_free
#print axioms padding_value
#print axioms zero_offset_is_not_padding
end Mettapedia.Logic.HOL.VectorChildArrays.BoundaryControls
