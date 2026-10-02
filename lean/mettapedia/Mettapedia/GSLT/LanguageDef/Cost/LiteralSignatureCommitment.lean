import Mettapedia.GSLT.LanguageDef.Cost.FiniteInteraction
import Mettapedia.GSLT.LanguageDef.Cost.KeyObservation
import Mettapedia.OSLF.MeTTaIL.PatternCode
import Mathlib.Data.Num.Lemmas

/-!
# Exact canonical commitments in the generated signature grammar

The existing unit/product grammar can carry exact structural keys. Binary
serialization has a checked inverse; no digest or collision assumption is
needed. Equality here is literal syntax, separate from any monoid valuation
of that syntax. The serialization does not add funding or enable a firing.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Cost.LiteralSignatureCommitment

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PatternCode
open WellSorted

def unit : Pattern := .apply costSignatureUnitConstructorName []

def product (left right : Pattern) : Pattern :=
  .apply costSignatureProductConstructorName [left, right]

/-- A positive number is encoded by its binary digits, with separate
terminal, zero-bit and one-bit shapes. -/
def encodePositive : PosNum → Pattern
  | .one => product unit unit
  | .bit0 number => product unit (encodePositive number)
  | .bit1 number => product (product unit unit) (encodePositive number)

def decodePositive? : Pattern → Option PosNum
  | .apply constructor [left, right] =>
      if constructor = costSignatureProductConstructorName then
        if left = unit then
          if right = unit then some .one else PosNum.bit0 <$> decodePositive? right
        else if left = product unit unit then PosNum.bit1 <$> decodePositive? right
        else none
      else none
  | _ => none
termination_by source => sizeOf source
decreasing_by
  all_goals
    simp only [Pattern.apply.sizeOf_spec, List.cons.sizeOf_spec, List.nil.sizeOf_spec]
    omega

@[simp] theorem encodePositive_ne_unit (number : PosNum) :
    encodePositive number ≠ unit := by
  cases number <;> simp [encodePositive, product, unit]

@[simp] theorem decodePositive_encodePositive (number : PosNum) :
    decodePositive? (encodePositive number) = some number := by
  induction number with
  | one => simp [encodePositive, product, decodePositive?, unit]
  | bit0 number ih =>
    simp only [encodePositive, product, decodePositive?, ↓reduceIte,
      encodePositive_ne_unit, ih]
    rfl
  | bit1 number ih =>
    simp [encodePositive, product, decodePositive?, unit, ih]

def encodeNumber : Num → Pattern
  | .zero => unit
  | .pos number => encodePositive number

def decodeNumber? (source : Pattern) : Option Num :=
  if source = unit then some .zero else Num.pos <$> decodePositive? source

@[simp] theorem decodeNumber_encodeNumber (number : Num) :
    decodeNumber? (encodeNumber number) = some number := by
  cases number <;> simp [encodeNumber, decodeNumber?]

def encodeNat (number : Nat) : Pattern := encodeNumber (number : Num)

def decodeNat? (source : Pattern) : Option Nat :=
  (decodeNumber? source).map (fun number => (number : Nat))

@[simp] theorem decodeNat_encodeNat (number : Nat) :
    decodeNat? (encodeNat number) = some number := by
  simp [decodeNat?, encodeNat]

theorem encodeNat_injective : Function.Injective encodeNat := by
  intro left right equal
  have decoded := congrArg decodeNat? equal
  simpa only [decodeNat_encodeNat, Option.some.injEq] using decoded

/-- A literal commitment to a structural Pattern value. Binder spellings,
indices, collection order and multiplicities remain part of this value. -/
def literal (source : Pattern) : Pattern := encodeNat (patternCode source)

theorem literal_injective : Function.Injective literal :=
  encodeNat_injective.comp patternCode_injective

theorem encodePositive_object (number : PosNum) :
    isObjectPattern (encodePositive number) = true := by
  induction number <;> simp [encodePositive, product, unit, isObjectPattern, isObjectPatternList, *]

theorem encodeNat_object (number : Nat) :
    isObjectPattern (encodeNat number) = true := by
  unfold encodeNat
  cases (number : Num) with
  | zero => rfl
  | pos value => exact encodePositive_object value

theorem literal_object (source : Pattern) : isObjectPattern (literal source) = true :=
  encodeNat_object (patternCode source)

variable {language : LanguageDef} {free : FreeTypeContext} {bound : List TypeExpr}

theorem unit_typed (declared : costSignatureUnitConstructor ∈ language.terms) :
    HasSort language free bound unit costSignatureSortName := by
  apply HasType.constructor declared
  · simp [UsesBareCollection, costSignatureUnitConstructor]
  · exact .nil

theorem product_typed (declared : costSignatureProductConstructor ∈ language.terms)
    {left right : Pattern}
    (leftTyped : HasSort language free bound left costSignatureSortName)
    (rightTyped : HasSort language free bound right costSignatureSortName) :
    HasSort language free bound (product left right) costSignatureSortName := by
  apply HasType.constructor declared
  · simp [UsesBareCollection, costSignatureProductConstructor]
  · exact .cons trivial rfl leftTyped (.cons trivial rfl rightTyped .nil)

theorem encodePositive_typed
    (unitDeclared : costSignatureUnitConstructor ∈ language.terms)
    (productDeclared : costSignatureProductConstructor ∈ language.terms)
    (number : PosNum) :
    HasSort language free bound (encodePositive number) costSignatureSortName := by
  have unitTyped := unit_typed (free := free) (bound := bound) unitDeclared
  induction number with
  | one => exact product_typed productDeclared unitTyped unitTyped
  | bit0 number ih => exact product_typed productDeclared unitTyped ih
  | bit1 number ih =>
    exact product_typed productDeclared (product_typed productDeclared unitTyped unitTyped) ih

theorem encodeNat_typed
    (unitDeclared : costSignatureUnitConstructor ∈ language.terms)
    (productDeclared : costSignatureProductConstructor ∈ language.terms)
    (number : Nat) :
    HasSort language free bound (encodeNat number) costSignatureSortName := by
  unfold encodeNat
  cases (number : Num) with
  | zero => exact unit_typed unitDeclared
  | pos value => exact encodePositive_typed unitDeclared productDeclared value

theorem literal_typed
    (unitDeclared : costSignatureUnitConstructor ∈ language.terms)
    (productDeclared : costSignatureProductConstructor ∈ language.terms)
    (source : Pattern) :
    HasSort language free bound (literal source) costSignatureSortName :=
  encodeNat_typed unitDeclared productDeclared (patternCode source)

/-- The normalized representative comes from the theory's actual admitted
canonical section, rather than from a second normalization algorithm. -/
def canonical (theory : CIGSLT) (source : theory.CanonicalCarrier) : Pattern :=
  literal (theory.canonicalKey source).val.val

theorem canonical_eq_iff (theory : CIGSLT) (left right : theory.CanonicalCarrier) :
    canonical theory left = canonical theory right ↔ theory.canonicalEquationSetoid.r left right := by
  rw [canonical, canonical, literal_injective.eq_iff]
  rw [← Subtype.ext_iff, ← Subtype.ext_iff]
  exact theory.canonicalKey_eq_iff left right

/-- A malformed positive serialization is rejected, even though it remains
a syntactically legal product of signatures. -/
theorem malformed_positive_rejected :
    decodePositive? (product (product unit (product unit unit)) unit) = none := by
  decide +kernel

theorem zero_one_two_distinct :
    encodeNat 0 ≠ encodeNat 1 ∧ encodeNat 1 ≠ encodeNat 2 := by
  constructor <;> intro equal <;> have contradiction := encodeNat_injective equal <;> omega

end Mettapedia.GSLT.LanguageDef.Cost.LiteralSignatureCommitment
