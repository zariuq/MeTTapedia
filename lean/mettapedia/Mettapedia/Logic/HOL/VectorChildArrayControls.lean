import Mettapedia.Logic.HOL.VectorChildArrayLookup
import Mettapedia.Logic.HOL.HOLLightStandardTheory
import Mettapedia.Logic.HOL.Soundness

/-!
# Independent natural/list interpretation of constructed child arrays

The index and element carriers are natural numbers and vectors are lists.
The six primitive premises are jointly realized. Retained proofs distinguish
two different children and the leading field. A recursive proof producer also
checks the trailing boundary for every concrete list, including the empty list.
Independent logical soundness rejects swapped child values and wrong positions.
The general open-vector trailing/padding correspondence is a separate obligation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.VectorChildArrays.Controls

inductive Base where | number | element | vector
  deriving DecidableEq
abbrev N : Ty Base := .base .number
abbrev E : Ty Base := .base .element
abbrev V : Ty Base := .base .vector

inductive Const : Ty Base → Type where
  | zero : Const N
  | successor : Const (N ⇒ N)
  | nil : Const V
  | cons : Const (N ⇒ E ⇒ V ⇒ V)
  | head : Const (V ⇒ E)
  | tail : Const (V ⇒ V)
  | element (value : Nat) : Const E
  | selection (type : Ty Base) : Const (SelectionProofs.Selection type)

def ops : Operations Const where
  number := N
  element := E
  vector := V
  zero := .const .zero
  successor := .const .successor
  nil := .const .nil
  cons := .const .cons
  head := .const .head
  tail := .const .tail
  elementSelection := .const (.selection (N ⇒ E))
  arraySelection := .const (.selection (N ⇒ V ⇒ N ⇒ E))

def carrier : Base → Type 1
  | .number => ULift.{1} Nat
  | .element => ULift.{1} Nat
  | .vector => ULift.{1} (List Nat)
def inhabitant : (type : Base) → carrier type
  | .number => ULift.up 0
  | .element => ULift.up 0
  | .vector => ULift.up []

noncomputable def meaning : {type : Ty Base} → Const type → Ty.denote.{0,0} carrier type
  | _, .zero => ULift.up 0
  | _, .successor => fun n => ULift.up (n.down + 1)
  | _, .nil => ULift.up []
  | _, .cons => fun _ first rest => ULift.up (first.down :: rest.down)
  | _, .head => fun values => ULift.up (values.down.headD 0)
  | _, .tail => fun values => ULift.up values.down.tail
  | _, .element value => ULift.up value
  | _, .selection type => HOLLightStandardTheory.selectionOperation carrier inhabitant type

noncomputable def model : HenkinModel.{0,0,0} Base Const := .standard carrier meaning
def emptyValues : model.Valuation [] := fun index => nomatch index
def assumptions : List (ClosedFormula Const) := ops.assumptions []
def premises : ops.ComputationPremises assumptions := ops.assumptionPremises
theorem premises_free : premises.FunctionExtensionalityFree := ops.assumptionPremises_free

theorem choice_holds (type : Ty Base) : model.models (SelectionProofs.principle (.const (.selection type))) := by
  intro predicate _ witness _ member
  exact HOLLightStandardTheory.selectionOperation_specified carrier inhabitant type predicate ⟨witness,member⟩

theorem elementRecursion_holds : model.models (ops.recursionLaw E) := by
  intro initial _ step _
  let values : ULift.{1} Nat → ULift.{1} Nat :=
    fun n => Nat.rec initial (fun k previous => step previous (ULift.up k)) n.down
  refine ⟨values,trivial,?_,?_⟩
  · rfl
  · intro n _; rfl

theorem arrayRecursion_holds : model.models (ops.recursionLaw (V ⇒ N ⇒ E)) := by
  intro initial _ step _
  let values : ULift.{1} Nat → (ULift.{1} (List Nat) → ULift.{1} Nat → ULift.{1} Nat) :=
    fun n => Nat.rec initial (fun k previous => step previous (ULift.up k)) n.down
  refine ⟨values,trivial,?_,?_⟩
  · intro vector _ position _; rfl
  · intro n _ vector _ position _; rfl

theorem head_holds : model.models ops.headLaw := by
  intro n _ head _ tail _
  rfl

theorem tail_holds : model.models ops.tailLaw := by
  intro n _ head _ tail _
  rfl

theorem assumptions_realizable : Soundness.SatisfiesHyps model emptyValues assumptions := by
  intro formula member
  simp only [assumptions, Operations.assumptions, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact choice_holds (N ⇒ E)
  · exact elementRecursion_holds
  · exact choice_holds (N ⇒ V ⇒ N ⇒ E)
  · exact arrayRecursion_holds
  · exact head_holds
  · exact tail_holds

theorem sound {formula : ClosedFormula Const} (proof : ProofSyntax Const assumptions formula) :
    (model.denote formula emptyValues).down :=
  Soundness.extDerivation_sound proof.erase
    (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
    (fun _ => trivial) assumptions_realizable

def numeral : Nat → ClosedTerm Const N
  | 0 => ops.zero
  | n+1 => .app ops.successor (numeral n)

def vector : List Nat → ClosedTerm Const V
  | [] => ops.nil
  | head :: rest => ops.toSignature.consValue (numeral rest.length) (.const (.element head)) (vector rest)

def children (values : List Nat) : ClosedTerm Const (N ⇒ E) :=
  ops.mixed (numeral values.length) (.const (.element 5)) (vector values) (.const (.element 11)) (.const (.element 0))

def firstLookup : ProofSyntax Const assumptions
    (IndexedVectorPositions.lookup ops.toSignature (numeral 2) (vector [7,9]) (numeral 0) (.const (.element 7))) :=
  IndexedVectorPositions.here ops.toSignature (numeral 1) (.const (.element 7)) (vector [9])

def secondLookup : ProofSyntax Const assumptions
    (IndexedVectorPositions.lookup ops.toSignature (numeral 2) (vector [7,9]) (numeral 1) (.const (.element 9))) :=
  IndexedVectorPositions.there ops.toSignature (numeral 1) (.const (.element 7)) (vector [9]) (numeral 0) (.const (.element 9))
    (IndexedVectorPositions.here ops.toSignature (numeral 0) (.const (.element 9)) (vector []))

theorem firstLookup_free : firstLookup.FunctionExtensionalityFree := IndexedVectorPositions.here_free _ _ _ _
theorem secondLookup_free : secondLookup.FunctionExtensionalityFree :=
  IndexedVectorPositions.there_free _ _ _ _ _ _ _ (IndexedVectorPositions.here_free _ _ _ _)

def leadingValue : ProofSyntax Const assumptions (.eq (.app (children [7,9]) (numeral 0)) (.const (.element 5))) :=
  ops.prepend_zero _ _ premises.elementChoice premises.elementRecursion

def firstValue : ProofSyntax Const assumptions (.eq (.app (children [7,9]) (numeral 1)) (.const (.element 7))) :=
  ops.mixedAtLookup _ _ _ _ _ _ _ premises firstLookup

def secondValue : ProofSyntax Const assumptions (.eq (.app (children [7,9]) (numeral 2)) (.const (.element 9))) :=
  ops.mixedAtLookup _ _ _ _ _ _ _ premises secondLookup

theorem firstValue_free : firstValue.FunctionExtensionalityFree :=
  ops.mixedAtLookup_free _ _ _ _ _ _ _ premises firstLookup premises_free firstLookup_free
theorem secondValue_free : secondValue.FunctionExtensionalityFree :=
  ops.mixedAtLookup_free _ _ _ _ _ _ _ premises secondLookup premises_free secondLookup_free

def suffixEnd : (values : List Nat) → (rest : ClosedTerm Const (N ⇒ E)) →
    ProofSyntax Const assumptions (.eq (.app (ops.suffix (numeral values.length) (vector values) rest)
      (numeral values.length)) (.app rest (numeral 0)))
  | [], rest => .eqApp (numeral 0) (ops.suffix_zero _ rest premises.arrayChoice premises.arrayRecursion)
  | head :: tail, rest =>
      .eqTrans (.eqApp (numeral (tail.length + 1))
        (ops.suffix_cons (numeral tail.length) (.const (.element head)) (vector tail) rest
          premises.arrayChoice premises.arrayRecursion
          (ops.headAt _ _ _ premises.head) (ops.tailAt _ _ _ premises.tail)))
        (.eqTrans (ops.prepend_successor (.const (.element head)) (ops.suffix (numeral tail.length) (vector tail) rest)
          (numeral tail.length) premises.elementChoice premises.elementRecursion) (suffixEnd tail rest))

theorem suffixEnd_free (values : List Nat) (rest : ClosedTerm Const (N ⇒ E)) :
    (suffixEnd values rest).FunctionExtensionalityFree := by
  induction values with
  | nil => exact ops.suffix_zero_free _ _ _ _ premises_free.2.2.1 premises_free.2.2.2.1
  | cons head tail previous =>
      exact ⟨ops.suffix_cons_free _ _ _ _ _ _ _ _ premises_free.2.2.1 premises_free.2.2.2.1
        (ops.headAt_free _ _ _ _ premises_free.2.2.2.2.1) (ops.tailAt_free _ _ _ _ premises_free.2.2.2.2.2),
        ⟨ops.prepend_successor_free _ _ _ _ _ premises_free.1 premises_free.2.1,previous⟩⟩

def trailingValue (values : List Nat) : ProofSyntax Const assumptions
    (.eq (.app (children values) (numeral (values.length + 1))) (.const (.element 11))) :=
  .eqTrans (ops.prepend_successor _ _ (numeral values.length) premises.elementChoice premises.elementRecursion)
    (.eqTrans (suffixEnd values _) (ops.prepend_zero _ _ premises.elementChoice premises.elementRecursion))

theorem trailingValue_free (values : List Nat) : (trailingValue values).FunctionExtensionalityFree :=
  ⟨ops.prepend_successor_free _ _ _ _ _ premises_free.1 premises_free.2.1,
    ⟨suffixEnd_free values _,ops.prepend_zero_free _ _ _ _ premises_free.1 premises_free.2.1⟩⟩

theorem twoDifferentChildren :
    (model.denote (children [7,9]) emptyValues (ULift.up 1)).down = 7 ∧
      (model.denote (children [7,9]) emptyValues (ULift.up 2)).down = 9 := by
  exact ⟨congrArg ULift.down (sound firstValue),congrArg ULift.down (sound secondValue)⟩

theorem emptyTrailingChild : (model.denote (children []) emptyValues (ULift.up 1)).down = 11 :=
  congrArg ULift.down (sound (trailingValue []))

theorem swapping_children_refused : ¬ Nonempty (ProofSyntax Const assumptions
    (.eq (.app (children [7,9]) (numeral 1)) (.const (.element 9)))) := by
  rintro ⟨claimed⟩
  have wrong : (model.denote (children [7,9]) emptyValues (ULift.up 1)).down = 9 :=
    congrArg ULift.down (sound claimed)
  have impossible : (7:Nat) = 9 := twoDifferentChildren.1.symm.trans wrong
  exact (by decide : (7:Nat) ≠ 9) impossible

theorem using_leading_slot_for_vector_refused : ¬ Nonempty (ProofSyntax Const assumptions
    (.eq (.app (children [7,9]) (numeral 0)) (.const (.element 7)))) := by
  rintro ⟨claimed⟩
  have actual : (model.denote (children [7,9]) emptyValues (ULift.up 0)).down = 5 :=
    congrArg ULift.down (sound leadingValue)
  have wrong : (model.denote (children [7,9]) emptyValues (ULift.up 0)).down = 7 :=
    congrArg ULift.down (sound claimed)
  exact (by decide : (5:Nat) ≠ 7) (actual.symm.trans wrong)

#print axioms assumptions_realizable
#print axioms secondValue_free
#print axioms trailingValue_free
#print axioms swapping_children_refused
end Mettapedia.Logic.HOL.VectorChildArrays.Controls
