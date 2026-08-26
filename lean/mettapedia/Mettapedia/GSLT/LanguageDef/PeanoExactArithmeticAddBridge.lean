import Mettapedia.GSLT.LanguageDef.PeanoAddSpecialization
import Mettapedia.GSLT.LanguageDef.ArithmeticExtension

/-!
# Peano addition and exact-integer addition agree on naturals

The two-clause Peano relation defines addition internally:

```text
add(zero,    n, n)
add(succ m, n, succ k) :- add(m, n, k)
```

Exact arithmetic instead imports integer addition as a primitive operation.
This module proves that the two presentations define exactly the same graph
after embedding Peano numerals into nonnegative integers.  The result is a
small semantic calibration for the primitive-call compiler rung; it does not
turn that rung into a generic compiler generator.
-/

namespace Mettapedia.GSLT.LanguageDef.PeanoExactArithmeticAddBridge

open Mettapedia.GSLT.LanguageDef.PeanoAddSpecialization
open Mettapedia.GSLT.LanguageDef.ArithmeticExtension.ExactInteger

inductive Symbol where
  | zero
  | successor
  | add
deriving DecidableEq, Repr

/-- Canonical unary numeral in the closed Peano presentation. -/
def numeral (value : Nat) : Term Symbol :=
  wrap .successor value (.symbol .zero)

/-- The recognized two-rule addition plan. -/
def additionPlan : Plan Symbol := {
  relation := .add
  zero := .zero
  successor := .successor
  zeroStep := 0
  successorStep := 1
}

private theorem wrap_add (count tail : Nat) (term : Term Symbol) :
    wrap .successor (count + tail) term =
      wrap .successor count (wrap .successor tail term) := by
  induction count with
  | zero => simp [wrap]
  | succ count inductionHypothesis =>
      simpa [wrap, Nat.succ_add] using
        congrArg (Term.unary Symbol.successor) inductionHypothesis

theorem wrap_numeral (count value : Nat) :
    wrap .successor count (numeral value) = numeral (count + value) := by
  exact (wrap_add count value (.symbol .zero)).symm

theorem numeralSize_numeral (value : Nat) :
    numeralSize? Symbol.zero Symbol.successor (numeral value) = some value := by
  exact (numeralSize?_eq_some_iff
    Symbol.zero Symbol.successor (numeral value) value).2 rfl

theorem numeral_injective : Function.Injective numeral := by
  intro first second equal
  apply Option.some.inj
  calc
    some first = numeralSize? Symbol.zero Symbol.successor (numeral first) :=
      (numeralSize_numeral first).symm
    _ = numeralSize? Symbol.zero Symbol.successor (numeral second) :=
      congrArg (numeralSize? Symbol.zero Symbol.successor) equal
    _ = some second := numeralSize_numeral second

/-- The closed Peano relation is precisely ordinary natural-number addition. -/
theorem peanoAdd_iff (first second result : Nat) :
    AddRel Symbol.zero Symbol.successor
      (numeral first) (numeral second) (numeral result) ↔
      result = first + second := by
  constructor
  · intro derivation
    obtain ⟨count, leftShape, resultShape⟩ :=
      (addRel_iff_wrap Symbol.zero Symbol.successor
        (numeral first) (numeral second) (numeral result)).1 derivation
    have countEq : first = count :=
      numeral_injective (by simpa [numeral] using leftShape)
    subst count
    apply numeral_injective
    exact resultShape.trans (wrap_numeral first second)
  · intro resultEq
    subst result
    apply (addRel_iff_wrap Symbol.zero Symbol.successor
      (numeral first) (numeral second) (numeral (first + second))).2
    exact ⟨first, rfl, (wrap_numeral first second).symm⟩

/-- Exact-integer addition restricted to embedded naturals. -/
def NativeNatAdd (first second result : Nat) : Prop :=
  coreSem .add (Int.ofNat first) (Int.ofNat second) =
    .val (Int.ofNat result)

theorem nativeNatAdd_iff (first second result : Nat) :
    NativeNatAdd first second result ↔ result = first + second := by
  simp only [NativeNatAdd, coreSem, undefinedAt, CoreOp.fn,
    CoreOp.isPartial, Bool.false_eq_true, false_and, if_false,
    Outcome.val.injEq]
  constructor
  · intro equal
    have castEqual : Int.ofNat (first + second) = Int.ofNat result := by
      simpa only [Int.ofNat_eq_natCast, Int.natCast_add] using equal
    exact (Int.ofNat_inj.mp castEqual).symm
  · intro equal
    subst result
    simp only [Int.ofNat_eq_natCast, Int.natCast_add]

/-- The Peano rewrite graph and the imported exact-integer primitive graph
coincide on natural-number inputs and outputs. -/
theorem peanoAdd_iff_nativeNatAdd (first second result : Nat) :
    AddRel Symbol.zero Symbol.successor
      (numeral first) (numeral second) (numeral result) ↔
      NativeNatAdd first second result := by
  rw [peanoAdd_iff, nativeNatAdd_iff]

/-- The specialized evaluator preserves the same graph, not merely selected
examples of it. -/
theorem specializedPeanoAdd_iff_nativeNatAdd (first second result : Nat) :
    evaluate? additionPlan (numeral first) (numeral second) =
        some (numeral result) ↔
      NativeNatAdd first second result := by
  rw [evaluate?_eq_some_iff]
  exact peanoAdd_iff_nativeNatAdd first second result

example :
    evaluate? additionPlan (numeral 2) (numeral 3) = some (numeral 5) := by
  apply (specializedPeanoAdd_iff_nativeNatAdd 2 3 5).2
  exact (nativeNatAdd_iff 2 3 5).2 rfl

example :
    evaluate? additionPlan (numeral 2) (numeral 3) ≠ some (numeral 6) := by
  intro invented
  have native :=
    (specializedPeanoAdd_iff_nativeNatAdd 2 3 6).1 invented
  have impossible : 6 = 2 + 3 := (nativeNatAdd_iff 2 3 6).1 native
  omega

#print axioms peanoAdd_iff_nativeNatAdd
#print axioms specializedPeanoAdd_iff_nativeNatAdd

end Mettapedia.GSLT.LanguageDef.PeanoExactArithmeticAddBridge
