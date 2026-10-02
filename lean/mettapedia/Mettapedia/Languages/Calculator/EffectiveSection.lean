import Mettapedia.Languages.Calculator.Section
import Mettapedia.GSLT.LanguageDef.EffectiveSection
import Mettapedia.OSLF.MeTTaIL.UnaryNumeralCode

/-!
# The calculator's normal form is effective

Evaluation to a numeral rewrites an expression from the leaves up: once the
arguments of an operation are numerals, the operation is carried out on the
numbers they write.  Reading a number off the code of its numeral, computing
with it, and writing the numeral of the result are primitive recursive on
codes.  So evaluation is tracked by a primitive recursive function on codes,
and the normal-form section of the calculator is effective.

The calculator has no interaction, so this is effectiveness of a section on
the closed terms of a sort, not of the section of an iGSLT.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Calculator

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PatternCode

/-! ## Evaluation as a bottom-up rewriting -/

theorem valueList_eq_map (patterns : List Pattern) : valueList patterns = patterns.map value := by
  induction patterns with
  | nil => rfl
  | cons pattern patterns recurse => simp [valueList, recurse]

/-- The number a pattern writes as a numeral, and zero when it writes none. -/
def writtenNumber (pattern : Pattern) : ℕ :=
  unaryCount "Zero" "Succ" (patternCode pattern)

@[simp] theorem writtenNumber_numeral (count : ℕ) : writtenNumber (numeral count) = count :=
  unaryCount_unaryCode (by decide) count

/-- Evaluate a node whose arguments are numerals.  A node that is not an
application evaluates to zero. -/
def evaluateRoot : Pattern → Pattern
  | .apply label arguments => numeral (operation label (arguments.map writtenNumber))
  | _ => numeral 0

/-- **Evaluation rewrites from the leaves up**: the arguments first, then the
operation on the numbers they have become. -/
theorem numeral_value_eq_bottomUp (pattern : Pattern) :
    numeral (value pattern) = pattern.bottomUp evaluateRoot := by
  induction pattern using Pattern.inductionOn with
  | happly label arguments recurse =>
      simp only [Pattern.bottomUp, Pattern.bottomUpList_eq_map, evaluateRoot, value,
        valueList_eq_map, List.map_map]
      congr 2
      apply List.map_congr_left
      intro argument member
      simp only [Function.comp_apply, ← recurse argument member, writtenNumber_numeral]
  | hbvar index => rfl
  | hfvar name => rfl
  | hlambda binder body _ => rfl
  | hmultiLambda arity binders body _ => rfl
  | hsubst body replacement _ _ => rfl
  | hcollection kind elements rest _ => rfl

/-! ## The operation at a node, on codes -/

/-- What a constructor computes from the values of its arguments, the
constructor being given by the code of its label. -/
def operationCode (labelCode : ℕ) (values : List ℕ) : ℕ :=
  if values.length = 1 then
    if labelCode = stringCode "Succ" then values.headI + 1 else 0
  else if values.length = 2 then
    if labelCode = stringCode "Add" then values.getD 0 0 + values.getD 1 0
    else if labelCode = stringCode "Mul" then values.getD 0 0 * values.getD 1 0
    else 0
  else 0

theorem operationCode_stringCode (label : String) (values : List ℕ) :
    operationCode (stringCode label) values = operation label values := by
  match values with
  | [] => rfl
  | [argument] => simp [operationCode, operation, stringCode_injective.eq_iff]
  | [left, right] => simp [operationCode, operation, stringCode_injective.eq_iff]
  | _ :: _ :: _ :: _ => simp [operationCode, operation]

/-- The operation at a node, on codes. -/
def evaluateRootCode (code : ℕ) : ℕ :=
  if code.unpair.1 = 2 then
    unaryCode "Zero" "Succ"
      (operationCode code.unpair.2.unpair.1
        ((Denumerable.ofNat (List ℕ) code.unpair.2.unpair.2).map (unaryCount "Zero" "Succ")))
  else unaryCode "Zero" "Succ" 0

/-- **The operation at a node is tracked on codes.** -/
theorem evaluateRootCode_patternCode (pattern : Pattern) :
    evaluateRootCode (patternCode pattern) = patternCode (evaluateRoot pattern) := by
  cases pattern with
  | apply label arguments =>
      simp only [evaluateRootCode, patternCode, Nat.unpair_pair, ofNat_patternListCode,
        List.map_map, operationCode_stringCode]
      rfl
  | _ => simp [evaluateRootCode, patternCode, evaluateRoot, unaryCode, numeral]

theorem operationCode_primrec : Primrec₂ operationCode := by
  have values : Primrec fun input : ℕ × List ℕ => input.2 := Primrec.snd
  have length : Primrec fun input : ℕ × List ℕ => input.2.length :=
    Primrec.list_length.comp values
  have entry : ∀ position : ℕ, Primrec fun input : ℕ × List ℕ => input.2.getD position 0 :=
    fun position => (Primrec.list_getD 0).comp values (Primrec.const position)
  have labelled : ∀ label : String,
      PrimrecPred fun input : ℕ × List ℕ => input.1 = stringCode label :=
    fun label => Primrec.eq.comp Primrec.fst (Primrec.const (stringCode label))
  exact Primrec.ite (Primrec.eq.comp length (Primrec.const 1))
    (Primrec.ite (labelled "Succ")
      (Primrec.succ.comp (Primrec.list_headI.comp values)) (Primrec.const 0))
    (Primrec.ite (Primrec.eq.comp length (Primrec.const 2))
      (Primrec.ite (labelled "Add") (Primrec.nat_add.comp (entry 0) (entry 1))
        (Primrec.ite (labelled "Mul") (Primrec.nat_mul.comp (entry 0) (entry 1))
          (Primrec.const 0)))
      (Primrec.const 0))

theorem evaluateRootCode_primrec : Primrec evaluateRootCode := by
  have payload : Primrec fun code : ℕ => code.unpair.2 := Primrec.snd.comp Primrec.unpair
  have label : Primrec fun code : ℕ => code.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp payload)
  have arguments : Primrec fun code : ℕ =>
      (Denumerable.ofNat (List ℕ) code.unpair.2.unpair.2).map (unaryCount "Zero" "Succ") :=
    Primrec.list_map
      ((Primrec.ofNat (List ℕ)).comp (Primrec.snd.comp (Primrec.unpair.comp payload)))
      ((unaryCount_primrec "Zero" "Succ").comp₂ Primrec₂.right)
  exact Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 2))
    ((unaryCode_primrec "Zero" "Succ").comp (operationCode_primrec.comp label arguments))
    (Primrec.const _)

/-! ## Evaluation on codes -/

/-- The function on codes that tracks evaluation to a numeral. -/
def evaluateCode : ℕ → ℕ := bottomUpCode evaluateRootCode

/-- **Evaluation is primitive recursive on codes.** -/
theorem evaluateCode_primrec : Primrec evaluateCode :=
  bottomUpCode_primrec evaluateRootCode_primrec

/-- **The function on codes tracks evaluation.** -/
theorem evaluateCode_patternCode (pattern : Pattern) :
    evaluateCode (patternCode pattern) = patternCode (numeral (value pattern)) := by
  rw [numeral_value_eq_bottomUp]
  exact bottomUpCode_patternCode evaluateRootCode_patternCode pattern

/-- **The normal-form section of the calculator is effective.** -/
theorem calculatorSection_effective : calculatorSection.Effective :=
  ⟨evaluateCode, evaluateCode_primrec.to_comp, fun term => by
    rw [calculatorSection_normalize, numeralTerm_val]
    exact (evaluateCode_patternCode term.1).symm⟩

/-- The tracking function sends the code of `1 + 1` to the code of `2`, and
the code of `1` to another code. -/
theorem evaluateCode_examples :
    evaluateCode (patternCode onePlusOne) = patternCode (numeral 2) ∧
      evaluateCode (patternCode (numeral 1)) ≠ patternCode (numeral 2) := by
  constructor
  · rw [evaluateCode_patternCode]
    exact congrArg (fun count => patternCode (numeral count)) (by decide +kernel)
  · rw [evaluateCode_patternCode, value_numeral]
    intro same
    exact absurd (Pattern.unary_injective (by decide) (patternCode_injective same)) (by decide)

end Mettapedia.Languages.Calculator
