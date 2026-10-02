import Mettapedia.Languages.Calculator.Interaction
import Mettapedia.GSLT.LanguageDef.CanonicalSection
import Mettapedia.GSLT.LanguageDef.ClosedEquivalence
import Mettapedia.GSLT.LanguageDef.ClosedTermForms
import Mettapedia.GSLT.LanguageDef.EquationInvariant

/-!
# The calculator has a normal form, and nothing else

The equational calculator authors the laws of arithmetic as equations and no
rewrite.  Its closed terms of sort `Num` are the expressions built from zero,
successor, sum and product, and its static equivalence identifies two of them
exactly when they have the same value.

The value of a pattern is computed by structural recursion.  Every law has
sides of equal value under every substitution, so equivalent expressions have
equal values.  Conversely every closed expression is equivalent, through
closed expressions only, to the unary numeral of its value: the four laws
suffice to add and to multiply numerals, and equivalence is a congruence for
the three operations.

Evaluation to a numeral is therefore a computable section of the static
equivalence, the numerals are its normal forms, and the equivalence is
decidable.  The calculator is a theory with a normal form and no interaction:
it admits no interactive presentation, because it has no rule.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Calculator

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-! ## The value of a pattern -/

/-- What a constructor computes from the values of its arguments. -/
def operation (label : String) : List Nat → Nat
  | [] => 0
  | [argument] => if label = "Succ" then argument + 1 else 0
  | [left, right] =>
      if label = "Add" then left + right else if label = "Mul" then left * right else 0
  | _ => 0

mutual
  /-- The value of a pattern: arithmetic on constructor applications, zero on
  everything else. -/
  def value : Pattern → Nat
    | .bvar _ => 0
    | .fvar _ => 0
    | .apply label arguments => operation label (valueList arguments)
    | .lambda _ _ => 0
    | .multiLambda _ _ _ => 0
    | .subst _ _ => 0
    | .collection _ _ _ => 0

  /-- The values of a list of patterns. -/
  def valueList : List Pattern → List Nat
    | [] => []
    | pattern :: patterns => value pattern :: valueList patterns
end

@[simp] theorem valueList_append (first second : List Pattern) :
    valueList (first ++ second) = valueList first ++ valueList second := by
  induction first with
  | nil => simp [valueList]
  | cons head tail recurse => simp [valueList, recurse]

@[simp] theorem value_zero : value (.apply "Zero" []) = 0 := by
  simp [value, valueList, operation]

@[simp] theorem value_succ (argument : Pattern) :
    value (.apply "Succ" [argument]) = value argument + 1 := by
  simp [value, valueList, operation]

@[simp] theorem value_add (left right : Pattern) :
    value (.apply "Add" [left, right]) = value left + value right := by
  simp [value, valueList, operation]

@[simp] theorem value_mul (left right : Pattern) :
    value (.apply "Mul" [left, right]) = value left * value right := by
  simp [value, valueList, operation]

/-- The value of a numeral is the number it writes. -/
@[simp] theorem value_numeral (count : Nat) : value (numeral count) = count := by
  induction count with
  | zero => exact value_zero
  | succ count recurse =>
      show value (.apply "Succ" [numeral count]) = count + 1
      rw [value_succ, recurse]

/-- A context sees only the value of what fills its hole. -/
theorem value_fill_congr :
    ∀ (context : OneHoleContext) {first second : Pattern},
      value first = value second →
        value (context.fill first) = value (context.fill second)
  | .hole, _, _, same => same
  | .apply label before inner after, _, _, same => by
      simp [OneHoleContext.fill, value, valueList, value_fill_congr inner same]
  | .lambda _ _, _, _, _ => rfl
  | .multiLambda _ _ _, _, _, _ => rfl
  | .substBody _ _, _, _, _ => rfl
  | .substReplacement _ _, _, _, _ => rfl
  | .collection _ _ _ _ _, _, _, _ => rfl

/-! ## Equivalent expressions have equal values -/

/-- The four laws carry no premise and are matched exactly. -/
theorem calculator_plainEquations : PlainEquations calculator := by
  intro equation membership
  have listed : equation ∈ [addZero, addSucc, mulZero, mulSucc] := membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl <;> exact ⟨rfl, by decide, by decide⟩

/-- Each law has sides of equal value under every substitution. -/
theorem laws_preserve_value :
    ∀ equation : Equation, List.Mem equation calculator.equations →
      ∀ bindings : Bindings,
        value (applyBindings bindings equation.left) =
          value (applyBindings bindings equation.right) := by
  intro equation membership bindings
  have listed : equation ∈ [addZero, addSucc, mulZero, mulSucc] := membership
  simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl
  · simp [addZero, applyBindings]
  · simp only [addSucc, applyBindings, List.map_cons, List.map_nil, value_add, value_succ]
    omega
  · simp [mulZero, applyBindings]
  · simp only [mulSucc, applyBindings, List.map_cons, List.map_nil, value_add, value_mul,
      value_succ]
    exact (Nat.succ_mul _ _).trans (Nat.add_comm _ _)

/-- **Soundness of evaluation.**  Equivalent patterns have equal values. -/
theorem value_eq_of_equationEquiv {left right : Pattern}
    (equivalent : EquationEquiv base calculator left right) :
    value left = value right := by
  apply equationEquiv_invariant value
    (fun context _ _ same => value_fill_congr context same) _ equivalent
  rintro source target (authored | derived)
  · obtain ⟨equation, membership, bindings, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ :=
      equationInstance_sides calculator_plainEquations authored
    · exact laws_preserve_value equation membership bindings
    · exact (laws_preserve_value equation membership bindings).symm
  · exact absurd derived
      (no_derivedInstance_of_no_derived_laws (by decide) (by decide) (by decide) source target)

/-! ## The four laws as steps -/

/-- `0 + n = n`, as a step from any pattern of that form. -/
theorem addZero_step (right : Pattern) :
    EquationContextStep base calculator (.apply "Add" [.apply "Zero" [], right]) right := by
  refine equationContextStep_of_forward (equation := addZero) (List.Mem.head _) rfl
    (bindings := [("n", right)]) ?_ (by simp [addZero, applyBindings])
  apply matchRel_complete
  exact MatchRel.apply
    (MatchArgsRel.cons (hb := []) (tb := [("n", right)])
      (MatchRel.apply MatchArgsRel.nil rfl)
      (MatchArgsRel.cons (hb := [("n", right)]) (tb := []) MatchRel.fvar MatchArgsRel.nil rfl)
      rfl) rfl

/-- `S m + n = S (m + n)`. -/
theorem addSucc_step (left right : Pattern) :
    EquationContextStep base calculator
      (.apply "Add" [.apply "Succ" [left], right])
      (.apply "Succ" [.apply "Add" [left, right]]) := by
  refine equationContextStep_of_forward (equation := addSucc)
    (List.Mem.tail _ (List.Mem.head _)) rfl
    (bindings := [("n", right), ("m", left)]) ?_ (by simp [addSucc, applyBindings])
  apply matchRel_complete
  exact MatchRel.apply
    (MatchArgsRel.cons (hb := [("m", left)]) (tb := [("n", right)])
      (MatchRel.apply
        (MatchArgsRel.cons (hb := [("m", left)]) (tb := []) MatchRel.fvar MatchArgsRel.nil rfl)
        rfl)
      (MatchArgsRel.cons (hb := [("n", right)]) (tb := []) MatchRel.fvar MatchArgsRel.nil rfl)
      rfl) rfl

/-- `0 · n = 0`. -/
theorem mulZero_step (right : Pattern) :
    EquationContextStep base calculator (.apply "Mul" [.apply "Zero" [], right])
      (.apply "Zero" []) := by
  refine equationContextStep_of_forward (equation := mulZero)
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))) rfl
    (bindings := [("n", right)]) ?_ (by simp [mulZero, applyBindings])
  apply matchRel_complete
  exact MatchRel.apply
    (MatchArgsRel.cons (hb := []) (tb := [("n", right)])
      (MatchRel.apply MatchArgsRel.nil rfl)
      (MatchArgsRel.cons (hb := [("n", right)]) (tb := []) MatchRel.fvar MatchArgsRel.nil rfl)
      rfl) rfl

/-- `S m · n = n + m · n`. -/
theorem mulSucc_step (left right : Pattern) :
    EquationContextStep base calculator
      (.apply "Mul" [.apply "Succ" [left], right])
      (.apply "Add" [right, .apply "Mul" [left, right]]) := by
  refine equationContextStep_of_forward (equation := mulSucc)
    (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))) rfl
    (bindings := [("n", right), ("m", left)]) ?_ (by simp [mulSucc, applyBindings])
  apply matchRel_complete
  exact MatchRel.apply
    (MatchArgsRel.cons (hb := [("m", left)]) (tb := [("n", right)])
      (MatchRel.apply
        (MatchArgsRel.cons (hb := [("m", left)]) (tb := []) MatchRel.fvar MatchArgsRel.nil rfl)
        rfl)
      (MatchArgsRel.cons (hb := [("n", right)]) (tb := []) MatchRel.fvar MatchArgsRel.nil rfl)
      rfl) rfl

/-! ## Closed expressions -/

/-- The sort of numbers. -/
def numSort : LangSort calculator :=
  ⟨"Num", by
    show "Num" ∈ (["Num"] : List String)
    exact List.Mem.head _⟩

/-- A closed expression: a closed term of sort `Num`. -/
abbrev Expression : Type := ClosedTerm calculator numSort

/-- The static equivalence of the calculator on closed expressions. -/
abbrev expressionSetoid : Setoid Expression := closedEquationSetoid base calculator numSort

/-- No constructor of the calculator is a bare collection. -/
theorem terms_notBare : ∀ rule ∈ terms, ¬ UsesBareCollection rule := by
  intro rule membership
  simp only [terms, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl <;>
  · rintro ⟨parameterName, collectionType, elementType, shape⟩
    cases shape

/-- **The closed expressions, by their head.**  A closed term of sort `Num`
is zero, the successor of one, or the sum or product of two. -/
theorem closed_iff {pattern : Pattern} :
    ClosedTermWellSorted calculator numSort pattern ↔
      pattern = .apply "Zero" [] ∨
        (∃ argument, pattern = .apply "Succ" [argument] ∧
          ClosedTermWellSorted calculator numSort argument) ∨
        (∃ left right, pattern = .apply "Add" [left, right] ∧
          ClosedTermWellSorted calculator numSort left ∧
            ClosedTermWellSorted calculator numSort right) ∨
        (∃ left right, pattern = .apply "Mul" [left, right] ∧
          ClosedTermWellSorted calculator numSort left ∧
            ClosedTermWellSorted calculator numSort right) := by
  constructor
  · intro closed
    rcases closed.head_cases with
      ⟨rule, arguments, membership, -, -, rfl, typed⟩ |
      ⟨rule, collectionType, elements, membership, -, bare, -⟩
    · have shapes := closedShape_apply.mp (closedTermWellSorted_iff.mp closed).2
      have operand : ∀ argument ∈ arguments,
          HasType calculator FreeTypeContext.empty [] argument (.base "Num") →
            ClosedTermWellSorted calculator numSort argument :=
        fun argument argumentMember argumentTyped =>
          closedTermWellSorted_iff.mpr ⟨argumentTyped, shapes argument argumentMember⟩
      change rule ∈ terms at membership
      simp only [terms, List.mem_cons, List.not_mem_nil, or_false] at membership
      rcases membership with rfl | rfl | rfl | rfl
      · have forms := (argumentsHaveTypes_simple_iff arguments []).mp typed
        cases forms
        exact Or.inl rfl
      · have forms := (argumentsHaveTypes_simple_iff arguments [("n", .base "Num")]).mp typed
        cases forms with
        | cons headTyped tail =>
            cases tail
            exact Or.inr (Or.inl ⟨_, rfl, operand _ (by simp) headTyped⟩)
      · have forms := (argumentsHaveTypes_simple_iff arguments
          [("m", .base "Num"), ("n", .base "Num")]).mp typed
        cases forms with
        | cons leftTyped tail =>
            cases tail with
            | cons rightTyped rest =>
                cases rest
                exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl, operand _ (by simp) leftTyped,
                  operand _ (by simp) rightTyped⟩))
      · have forms := (argumentsHaveTypes_simple_iff arguments
          [("m", .base "Num"), ("n", .base "Num")]).mp typed
        cases forms with
        | cons leftTyped tail =>
            cases tail with
            | cons rightTyped rest =>
                cases rest
                exact Or.inr (Or.inr (Or.inr ⟨_, _, rfl, operand _ (by simp) leftTyped,
                  operand _ (by simp) rightTyped⟩))
    · exact absurd bare (terms_notBare rule membership)
  · rintro (rfl | ⟨argument, rfl, closed⟩ | ⟨left, right, rfl, leftClosed, rightClosed⟩ |
      ⟨left, right, rfl, leftClosed, rightClosed⟩)
    · refine closedTermWellSorted_iff.mpr ⟨?_, closedShape_apply.mpr (by simp)⟩
      exact HasType.constructor (rule := terms[0]) (List.getElem_mem (by decide))
        (terms_notBare _ (List.getElem_mem (by decide))) .nil
    · refine closedTermWellSorted_iff.mpr ⟨?_, closedShape_apply.mpr ?_⟩
      · exact HasType.constructor (rule := terms[1]) (List.getElem_mem (by decide))
          (terms_notBare _ (List.getElem_mem (by decide)))
          (.cons trivial rfl closed.1 .nil)
      · intro operand membership
        obtain rfl := List.mem_singleton.mp membership
        exact (closedTermWellSorted_iff.mp closed).2
    · refine closedTermWellSorted_iff.mpr ⟨?_, closedShape_apply.mpr ?_⟩
      · exact HasType.constructor (rule := terms[2]) (List.getElem_mem (by decide))
          (terms_notBare _ (List.getElem_mem (by decide)))
          (.cons trivial rfl leftClosed.1 (.cons trivial rfl rightClosed.1 .nil))
      · intro operand membership
        simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
        rcases membership with rfl | rfl
        · exact (closedTermWellSorted_iff.mp leftClosed).2
        · exact (closedTermWellSorted_iff.mp rightClosed).2
    · refine closedTermWellSorted_iff.mpr ⟨?_, closedShape_apply.mpr ?_⟩
      · exact HasType.constructor (rule := terms[3]) (List.getElem_mem (by decide))
          (terms_notBare _ (List.getElem_mem (by decide)))
          (.cons trivial rfl leftClosed.1 (.cons trivial rfl rightClosed.1 .nil))
      · intro operand membership
        simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
        rcases membership with rfl | rfl
        · exact (closedTermWellSorted_iff.mp leftClosed).2
        · exact (closedTermWellSorted_iff.mp rightClosed).2

/-- Zero, as a closed expression. -/
def zeroTerm : Expression := ⟨.apply "Zero" [], closed_iff.mpr (Or.inl rfl)⟩

/-- The successor of a closed expression. -/
def succTerm (argument : Expression) : Expression :=
  ⟨.apply "Succ" [argument.1], closed_iff.mpr (Or.inr (Or.inl ⟨_, rfl, argument.2⟩))⟩

/-- The sum of two closed expressions. -/
def addTerm (left right : Expression) : Expression :=
  ⟨.apply "Add" [left.1, right.1],
    closed_iff.mpr (Or.inr (Or.inr (Or.inl ⟨_, _, rfl, left.2, right.2⟩)))⟩

/-- The product of two closed expressions. -/
def mulTerm (left right : Expression) : Expression :=
  ⟨.apply "Mul" [left.1, right.1],
    closed_iff.mpr (Or.inr (Or.inr (Or.inr ⟨_, _, rfl, left.2, right.2⟩)))⟩

/-- The numeral of a number, as a closed expression. -/
def numeralTerm : Nat → Expression
  | 0 => zeroTerm
  | count + 1 => succTerm (numeralTerm count)

/-- Its underlying pattern is the unary numeral. -/
@[simp] theorem numeralTerm_val (count : Nat) : (numeralTerm count).1 = numeral count := by
  induction count with
  | zero => rfl
  | succ count recurse =>
      show Pattern.apply "Succ" [(numeralTerm count).1] = numeral (count + 1)
      rw [recurse]
      rfl

/-- Distinct numbers have distinct numerals. -/
theorem numeralTerm_injective : Function.Injective numeralTerm := by
  intro first second same
  have patterns : numeral first = numeral second := by
    rw [← numeralTerm_val, ← numeralTerm_val, same]
  exact Pattern.unary_injective (by decide) patterns

/-! ## Equivalence is a congruence for the operations -/

/-- Successor respects the equivalence. -/
theorem succ_congr {first second : Expression} (equivalent : expressionSetoid.r first second) :
    expressionSetoid.r (succTerm first) (succTerm second) :=
  closedEquationSetoid_fill (.apply "Succ" [] .hole [])
    (fun term => (succTerm term).2) equivalent

/-- Sum respects the equivalence in its left operand. -/
theorem add_congr_left (right : Expression) {first second : Expression}
    (equivalent : expressionSetoid.r first second) :
    expressionSetoid.r (addTerm first right) (addTerm second right) :=
  closedEquationSetoid_fill (.apply "Add" [] .hole [right.1])
    (fun term => (addTerm term right).2) equivalent

/-- Sum respects the equivalence in its right operand. -/
theorem add_congr_right (left : Expression) {first second : Expression}
    (equivalent : expressionSetoid.r first second) :
    expressionSetoid.r (addTerm left first) (addTerm left second) :=
  closedEquationSetoid_fill (.apply "Add" [left.1] .hole [])
    (fun term => (addTerm left term).2) equivalent

/-- Product respects the equivalence in its left operand. -/
theorem mul_congr_left (right : Expression) {first second : Expression}
    (equivalent : expressionSetoid.r first second) :
    expressionSetoid.r (mulTerm first right) (mulTerm second right) :=
  closedEquationSetoid_fill (.apply "Mul" [] .hole [right.1])
    (fun term => (mulTerm term right).2) equivalent

/-- Product respects the equivalence in its right operand. -/
theorem mul_congr_right (left : Expression) {first second : Expression}
    (equivalent : expressionSetoid.r first second) :
    expressionSetoid.r (mulTerm left first) (mulTerm left second) :=
  closedEquationSetoid_fill (.apply "Mul" [left.1] .hole [])
    (fun term => (mulTerm left term).2) equivalent

/-! ## The laws compute on numerals -/

/-- The sum of two numerals is equivalent to the numeral of the sum. -/
theorem add_numerals (first second : Nat) :
    expressionSetoid.r (addTerm (numeralTerm first) (numeralTerm second))
      (numeralTerm (first + second)) := by
  induction first with
  | zero =>
      rw [Nat.zero_add]
      exact closedEquationSetoid_of_step (addZero_step (numeralTerm second).1)
  | succ first recurse =>
      have unfolded : expressionSetoid.r
          (addTerm (numeralTerm (first + 1)) (numeralTerm second))
          (succTerm (addTerm (numeralTerm first) (numeralTerm second))) :=
        closedEquationSetoid_of_step
          (addSucc_step (numeralTerm first).1 (numeralTerm second).1)
      have total : first + 1 + second = first + second + 1 := by omega
      rw [total]
      exact expressionSetoid.iseqv.trans unfolded (succ_congr recurse)

/-- The product of two numerals is equivalent to the numeral of the
product. -/
theorem mul_numerals (first second : Nat) :
    expressionSetoid.r (mulTerm (numeralTerm first) (numeralTerm second))
      (numeralTerm (first * second)) := by
  induction first with
  | zero =>
      rw [Nat.zero_mul]
      exact closedEquationSetoid_of_step (mulZero_step (numeralTerm second).1)
  | succ first recurse =>
      have unfolded : expressionSetoid.r
          (mulTerm (numeralTerm (first + 1)) (numeralTerm second))
          (addTerm (numeralTerm second) (mulTerm (numeralTerm first) (numeralTerm second))) :=
        closedEquationSetoid_of_step
          (mulSucc_step (numeralTerm first).1 (numeralTerm second).1)
      have total : (first + 1) * second = second + first * second :=
        (Nat.succ_mul _ _).trans (Nat.add_comm _ _)
      rw [total]
      exact expressionSetoid.iseqv.trans unfolded
        (expressionSetoid.iseqv.trans (add_congr_right _ recurse) (add_numerals _ _))

/-! ## Every closed expression is equivalent to the numeral of its value -/

/-- **Completeness of evaluation.**  A closed expression is equivalent, through
closed expressions only, to the numeral of its value. -/
theorem equivalent_numeral (pattern : Pattern) :
    ∀ closed : ClosedTermWellSorted calculator numSort pattern,
      expressionSetoid.r ⟨pattern, closed⟩ (numeralTerm (value pattern)) := by
  induction pattern using Pattern.inductionOn with
  | happly label arguments recurse =>
      intro closed
      rcases closed_iff.mp closed with shape | ⟨argument, shape, argumentClosed⟩ |
        ⟨left, right, shape, leftClosed, rightClosed⟩ |
        ⟨left, right, shape, leftClosed, rightClosed⟩
      · simp only [Pattern.apply.injEq] at shape
        obtain ⟨rfl, rfl⟩ := shape
        rw [value_zero]
        exact expressionSetoid.iseqv.refl _
      · simp only [Pattern.apply.injEq] at shape
        obtain ⟨rfl, rfl⟩ := shape
        rw [value_succ]
        exact succ_congr (recurse argument (by simp) argumentClosed)
      · simp only [Pattern.apply.injEq] at shape
        obtain ⟨rfl, rfl⟩ := shape
        rw [value_add]
        have leftStep := add_congr_left ⟨right, rightClosed⟩
          (recurse left (by simp) leftClosed)
        have rightStep := add_congr_right (numeralTerm (value left))
          (recurse right (by simp) rightClosed)
        exact expressionSetoid.iseqv.trans leftStep
          (expressionSetoid.iseqv.trans rightStep (add_numerals _ _))
      · simp only [Pattern.apply.injEq] at shape
        obtain ⟨rfl, rfl⟩ := shape
        rw [value_mul]
        have leftStep := mul_congr_left ⟨right, rightClosed⟩
          (recurse left (by simp) leftClosed)
        have rightStep := mul_congr_right (numeralTerm (value left))
          (recurse right (by simp) rightClosed)
        exact expressionSetoid.iseqv.trans leftStep
          (expressionSetoid.iseqv.trans rightStep (mul_numerals _ _))
  | hbvar index =>
      intro closed
      rcases closed_iff.mp closed with shape | ⟨_, shape, _⟩ | ⟨_, _, shape, _, _⟩ |
        ⟨_, _, shape, _, _⟩ <;> cases shape
  | hfvar name =>
      intro closed
      rcases closed_iff.mp closed with shape | ⟨_, shape, _⟩ | ⟨_, _, shape, _, _⟩ |
        ⟨_, _, shape, _, _⟩ <;> cases shape
  | hlambda binder body _ =>
      intro closed
      rcases closed_iff.mp closed with shape | ⟨_, shape, _⟩ | ⟨_, _, shape, _, _⟩ |
        ⟨_, _, shape, _, _⟩ <;> cases shape
  | hmultiLambda arity binders body _ =>
      intro closed
      rcases closed_iff.mp closed with shape | ⟨_, shape, _⟩ | ⟨_, _, shape, _, _⟩ |
        ⟨_, _, shape, _, _⟩ <;> cases shape
  | hsubst body replacement _ _ =>
      intro closed
      rcases closed_iff.mp closed with shape | ⟨_, shape, _⟩ | ⟨_, _, shape, _, _⟩ |
        ⟨_, _, shape, _, _⟩ <;> cases shape
  | hcollection collectionType elements rest _ =>
      intro closed
      rcases closed_iff.mp closed with shape | ⟨_, shape, _⟩ | ⟨_, _, shape, _, _⟩ |
        ⟨_, _, shape, _, _⟩ <;> cases shape

/-! ## The section -/

/-- **The normal-form section of the calculator.**  Evaluation to a numeral
chooses one representative of each class of the static equivalence. -/
def calculatorSection :
    ComputableSetoidSection (ClosedTerm calculator numSort)
      (closedEquationSetoid base calculator numSort) where
  normalize := fun term => numeralTerm (value term.1)
  equivalent := fun term =>
    expressionSetoid.iseqv.symm (equivalent_numeral term.1 term.2)
  complete := by
    intro left right equivalent
    exact congrArg numeralTerm
      (value_eq_of_equationEquiv (equationEquiv_of_closedEquationSetoid equivalent))

/-- The normal form of a closed expression is the numeral of its value. -/
theorem calculatorSection_normalize (term : Expression) :
    calculatorSection.normalize term = numeralTerm (value term.1) :=
  rfl

/-- Numerals are normal forms. -/
theorem calculatorSection_normalize_numeral (count : Nat) :
    calculatorSection.normalize (numeralTerm count) = numeralTerm count := by
  rw [calculatorSection_normalize, numeralTerm_val, value_numeral]

/-- **Value decides the static equivalence.**  Two closed expressions are
equivalent exactly when they have the same value. -/
theorem equivalent_iff_value_eq {left right : Expression} :
    expressionSetoid.r left right ↔ value left.1 = value right.1 := by
  constructor
  · intro equivalent
    exact value_eq_of_equationEquiv (equationEquiv_of_closedEquationSetoid equivalent)
  · intro same
    exact (calculatorSection.equivalent_iff_normalize_eq left right).mpr
      (congrArg numeralTerm same)

/-- The static equivalence of the calculator is decidable. -/
instance : DecidableRel expressionSetoid.r := fun _ _ =>
  decidable_of_iff _ equivalent_iff_value_eq.symm

/-! ## Examples -/

/-- `1 + 1`, as a closed expression. -/
def onePlusOneTerm : Expression := addTerm (numeralTerm 1) (numeralTerm 1)

/-- Its underlying pattern is the expression of the calculator file. -/
theorem onePlusOneTerm_val : onePlusOneTerm.1 = onePlusOne := rfl

/-- `1 + 1` and `2` have the same normal form, and are equivalent. -/
theorem onePlusOne_normal_form :
    calculatorSection.normalize onePlusOneTerm = calculatorSection.normalize (numeralTerm 2) ∧
      expressionSetoid.r onePlusOneTerm (numeralTerm 2) := by
  have same : calculatorSection.normalize onePlusOneTerm =
      calculatorSection.normalize (numeralTerm 2) := by
    rw [calculatorSection_normalize_numeral, calculatorSection_normalize]
    exact congrArg numeralTerm (by decide +kernel)
  exact ⟨same, (calculatorSection.equivalent_iff_normalize_eq _ _).mpr same⟩

/-- `1` and `2` have different normal forms, and are not equivalent. -/
theorem one_not_equivalent_two :
    calculatorSection.normalize (numeralTerm 1) ≠ calculatorSection.normalize (numeralTerm 2) ∧
      ¬ expressionSetoid.r (numeralTerm 1) (numeralTerm 2) := by
  have different : calculatorSection.normalize (numeralTerm 1) ≠
      calculatorSection.normalize (numeralTerm 2) := by
    rw [calculatorSection_normalize_numeral, calculatorSection_normalize_numeral]
    intro same
    exact absurd (numeralTerm_injective same) (by decide)
  exact ⟨different, fun equivalent =>
    different ((calculatorSection.equivalent_iff_normalize_eq _ _).mp equivalent)⟩

/-- The decision procedure, evaluated: `1 + 1` is `2`, and `1` is not. -/
theorem decision_examples :
    decide (expressionSetoid.r onePlusOneTerm (numeralTerm 2)) = true ∧
      decide (expressionSetoid.r (numeralTerm 1) (numeralTerm 2)) = false := by
  constructor <;> decide +kernel

/-! ## The verdict -/

/-- **The calculator is a theory with a normal form and no interaction.**  Its
static equivalence on closed expressions is equality of evaluated numerals,
and it admits no interactive presentation. -/
theorem calculator_normal_form_only :
    (∀ left right : Expression,
        expressionSetoid.r left right ↔
          calculatorSection.normalize left = calculatorSection.normalize right) ∧
      (∀ term : Expression, ∃ count, calculatorSection.normalize term = numeralTerm count) ∧
        ¬ AdmitsInteractivePresentation calculator :=
  ⟨calculatorSection.equivalent_iff_normalize_eq, fun term => ⟨value term.1, rfl⟩,
    calculator_not_interactive⟩

end Mettapedia.Languages.Calculator
