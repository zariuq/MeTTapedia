import Mettapedia.Languages.C11.UsualIntegerConversions
import Mettapedia.Languages.C11.IntegerProfiles

/-!
# C11 usual arithmetic conversions with floating and complex operands

N1570 6.3.1.8 extends the integer common type of `UsualIntegerConversions`:
when either operand has floating type, the common real type is the floating
type of greater rank, and a complex operand makes the common type complex
with that real type. ISO/IEC TS 18661-3 adds interchange types (`_Float16`,
`_Float32`, `_Float64`, `_Float128`) and extended types (`_Float32x`,
`_Float64x`); GCC and Clang add `__bf16`, the bfloat16 format, as an
extended type. Floating ranks follow significand precision; at an equal
precision an interchange type ranks above the standard type, which ranks
above an extended type, and among standard types `float` < `double` <
`long double` even when formats coincide (6.3.1.8). Precision orders the
value sets of every pair except `_Float16` and `__bf16`, whose value sets
are incomparable (bfloat16 has `float`'s exponent range); both compilers
convert that pair to `_Float16`, which the precision order also gives.

`sysvFloating` holds the i386 and x86-64 System V formats: IEEE binary16,
bfloat16, IEEE binary32 and binary64, the x87 64-bit-significand extended format for `long double` and
`_Float64x`, and IEEE binary128. `windowsFloating` gives `long double` the
format of `double`. `aapcs64Floating` gives AArch64 `long double` the IEEE
binary128 format. With the ILP32, LP64 and LLP64 integer profiles they are
the targets of Cesta's elaborated arithmetic, whose tables are kernel-checked
against these definitions.

Bit-field operands promote by their width; that adapter belongs to the source
types and is outside these canonical types.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11

universe u

inductive RealFloatingType where
  | float
  | double
  | longDouble
  | float32
  | float64
  | float128
  | float32x
  | float64x
  | float16
  | bfloat16
  deriving DecidableEq, Repr

/-- TS 18661-3 tiers at an equal value set: interchange, standard, extended. -/
def RealFloatingType.tier : RealFloatingType → Nat
  | .float16 | .float32 | .float64 | .float128 => 2
  | .float | .double | .longDouble => 1
  | .float32x | .float64x | .bfloat16 => 0

/-- 6.3.1.8: the standard order, which decides between standard types that
    share a format. -/
def RealFloatingType.standardOrder : RealFloatingType → Nat
  | .longDouble => 2
  | .double => 1
  | _ => 0

def RealFloatingType.rankKey (precision : RealFloatingType → Nat) (type : RealFloatingType) : Nat :=
  precision type * 16 + type.tier * 4 + type.standardOrder

structure FloatingProfile where
  name : String
  precision : RealFloatingType → Nat
  /-- N1570 6.2.5p10: the values of `float` are values of `double`, and those of
      `long double`. -/
  standardNested : precision .float ≤ precision .double ∧ precision .double ≤ precision .longDouble
  /-- Distinct types have distinct ranks. -/
  rankInjective : ∀ first second : RealFloatingType,
    first.rankKey precision = second.rankKey precision → first = second

def FloatingProfile.rank (profile : FloatingProfile) (type : RealFloatingType) : Nat :=
  type.rankKey profile.precision

def sysvFloatingPrecision : RealFloatingType → Nat
  | .bfloat16 => 8
  | .float16 => 11
  | .float | .float32 => 24
  | .double | .float64 | .float32x => 53
  | .longDouble | .float64x => 64
  | .float128 => 113

def sysvFloating : FloatingProfile where
  name := "x86 System V floating formats"
  precision := sysvFloatingPrecision
  standardNested := by decide
  rankInjective := by
    intro first second
    cases first <;> cases second <;> decide

def windowsFloatingPrecision : RealFloatingType → Nat
  | .bfloat16 => 8
  | .float16 => 11
  | .float | .float32 => 24
  | .double | .longDouble | .float64 | .float32x => 53
  | .float64x => 64
  | .float128 => 113

def windowsFloating : FloatingProfile where
  name := "x86-64 Windows floating formats"
  precision := windowsFloatingPrecision
  standardNested := by decide
  rankInjective := by
    intro first second
    cases first <;> cases second <;> decide

def aapcs64FloatingPrecision : RealFloatingType → Nat
  | .bfloat16 => 8
  | .float16 => 11
  | .float | .float32 => 24
  | .double | .float64 | .float32x => 53
  | .longDouble | .float128 | .float64x => 113

def aapcs64Floating : FloatingProfile where
  name := "AArch64 AAPCS64 floating formats"
  precision := aapcs64FloatingPrecision
  standardNested := by decide
  rankInjective := by
    intro first second
    cases first <;> cases second <;> decide

/-- The floating type of greater rank. -/
def commonRealFloating (profile : FloatingProfile) (left right : RealFloatingType) : RealFloatingType :=
  if profile.rank right ≤ profile.rank left then left else right

theorem commonRealFloating_commutative (profile : FloatingProfile) (left right : RealFloatingType) :
    commonRealFloating profile left right = commonRealFloating profile right left := by
  unfold commonRealFloating
  by_cases first : profile.rank right ≤ profile.rank left <;>
    by_cases second : profile.rank left ≤ profile.rank right
  · have equal := profile.rankInjective left right (by unfold FloatingProfile.rank at first second; omega)
    subst equal
    simp
  · simp [first, second]
  · simp [first, second]
  · omega

theorem commonRealFloating_idempotent (profile : FloatingProfile) (type : RealFloatingType) :
    commonRealFloating profile type type = type := by
  simp [commonRealFloating]

theorem commonRealFloating_rank (profile : FloatingProfile) (left right : RealFloatingType) :
    profile.rank left ≤ profile.rank (commonRealFloating profile left right) ∧
      profile.rank right ≤ profile.rank (commonRealFloating profile left right) := by
  unfold commonRealFloating
  split <;> omega

inductive ArithmeticType (Extension : Type u) where
  | integer (type : IntegerType Extension)
  | real (type : RealFloatingType)
  | complex (type : RealFloatingType)
  deriving DecidableEq, Repr

def ArithmeticType.isInteger {Extension : Type u} : ArithmeticType Extension → Bool
  | .integer _ => true
  | .real _ | .complex _ => false

def ArithmeticType.isComplex {Extension : Type u} : ArithmeticType Extension → Bool
  | .complex _ => true
  | .integer _ | .real _ => false

/-- N1570 6.3.1.8p1: the common type of the usual arithmetic conversions. -/
def usualArithmeticType {Extension : Type u} [DecidableEq Extension]
    (integers : IntegerTypeParameters Extension) (floating : FloatingProfile) :
    ArithmeticType Extension → ArithmeticType Extension → ArithmeticType Extension
  | .integer left, .integer right => .integer (usualIntegerType integers left right)
  | .integer _, .real right => .real right
  | .real left, .integer _ => .real left
  | .integer _, .complex right => .complex right
  | .complex left, .integer _ => .complex left
  | .real left, .real right => .real (commonRealFloating floating left right)
  | .real left, .complex right => .complex (commonRealFloating floating left right)
  | .complex left, .real right => .complex (commonRealFloating floating left right)
  | .complex left, .complex right => .complex (commonRealFloating floating left right)

theorem usualArithmeticType_commutative {Extension : Type u} [DecidableEq Extension]
    (integers : IntegerTypeParameters Extension) (floating : FloatingProfile)
    (left right : ArithmeticType Extension) :
    usualArithmeticType integers floating left right = usualArithmeticType integers floating right left := by
  cases left <;> cases right <;>
    simp [usualArithmeticType, usualIntegerType_commutative, commonRealFloating_commutative]

/-- A floating operand makes the common type floating. -/
theorem usualArithmeticType_floating {Extension : Type u} [DecidableEq Extension]
    (integers : IntegerTypeParameters Extension) (floating : FloatingProfile)
    (left right : ArithmeticType Extension)
    (operand : left.isInteger = false ∨ right.isInteger = false) :
    (usualArithmeticType integers floating left right).isInteger = false := by
  cases left <;> cases right <;> simp_all [usualArithmeticType, ArithmeticType.isInteger]

/-- The common type is complex exactly when an operand is complex. -/
theorem usualArithmeticType_complex {Extension : Type u} [DecidableEq Extension]
    (integers : IntegerTypeParameters Extension) (floating : FloatingProfile)
    (left right : ArithmeticType Extension) :
    (usualArithmeticType integers floating left right).isComplex = (left.isComplex || right.isComplex) := by
  cases left <;> cases right <;> simp [usualArithmeticType, ArithmeticType.isComplex]

theorem usualArithmeticType_real_idempotent {Extension : Type u} [DecidableEq Extension]
    (integers : IntegerTypeParameters Extension) (floating : FloatingProfile) (type : RealFloatingType) :
    usualArithmeticType integers floating (.real type) (.real type) = .real type ∧
      usualArithmeticType integers floating (.complex type) (.complex type) = .complex type := by
  simp [usualArithmeticType, commonRealFloating_idempotent]

/-! ## The LP64 x86-64 profile -/

abbrev LP64Arithmetic := ArithmeticType IntegerExtension

def lp64UsualArithmetic : LP64Arithmetic → LP64Arithmetic → LP64Arithmetic :=
  usualArithmeticType (integerValueProfile .lp64) sysvFloating

def lp64Promote : IntegerType IntegerExtension → IntegerType IntegerExtension :=
  promoteIntegerType (integerValueProfile .lp64)

/-- Every integer type, for exhaustive checks over a profile. -/
def allIntegerTypes : List (IntegerType IntegerExtension) :=
  [.boolean] ++
    ([.standard .char, .standard .short, .standard .int, .standard .long, .standard .longLong,
      .extended .int128].flatMap fun family => [.signed family, .unsigned family])

def allRealFloatingTypes : List RealFloatingType :=
  [.float, .double, .longDouble, .float32, .float64, .float128, .float32x, .float64x, .float16, .bfloat16]

/-- The arithmetic types of C on this profile; GCC and Clang have no complex `__bf16`. -/
def allLP64Arithmetic : List LP64Arithmetic :=
  allIntegerTypes.map .integer ++ allRealFloatingTypes.map .real ++
    (allRealFloatingTypes.filter (· != .bfloat16)).map .complex

/-- The integer common type is already promoted, in every pair of this profile. -/
theorem lp64_usual_integer_promoted :
    allIntegerTypes.all (fun left => allIntegerTypes.all fun right =>
      lp64Promote (usualIntegerType (integerValueProfile .lp64) left right) ==
        usualIntegerType (integerValueProfile .lp64) left right) = true := by
  decide

/-- Promotion is idempotent in this profile. -/
theorem lp64_promote_idempotent :
    allIntegerTypes.all (fun type => lp64Promote (lp64Promote type) == lp64Promote type) = true := by
  decide

/-! ## Positive and negative examples -/

/-- `unsigned int` with `int` is `unsigned int`, not the larger-looking `int`. -/
example : lp64UsualArithmetic (.integer .int) (.integer .unsignedInt) = .integer .unsignedInt := by decide

/-- LP64: `long` covers `unsigned int`, so `long` is the common type. -/
example : lp64UsualArithmetic (.integer (.signed (.standard .long))) (.integer .unsignedInt) =
    .integer (.signed (.standard .long)) := by decide

/-- ILP32: `long` has `unsigned int`'s width, so the common type is `unsigned long`. -/
example : usualArithmeticType (integerValueProfile .ilp32) sysvFloating
    (.integer (.signed (.standard .long))) (.integer .unsignedInt) =
    .integer (.unsigned (.standard .long)) := by decide

/-- `char` and `short` promote to `int` before the common type is chosen. -/
example : lp64UsualArithmetic (.integer (.signed (.standard .char))) (.integer (.unsigned (.standard .short))) =
    .integer .int := by decide

/-- TS 18661-3: at equal value sets the interchange type wins over the standard type... -/
example : lp64UsualArithmetic (.real .float) (.real .float32) = .real .float32 := by decide

/-- ...and the standard type wins over the extended type. -/
example : lp64UsualArithmetic (.real .double) (.real .float32x) = .real .double := by decide

/-- `long double` and `_Float64x` share a value set; `long double` is standard. -/
example : lp64UsualArithmetic (.real .longDouble) (.real .float64x) = .real .longDouble := by decide

/-- A larger value set wins regardless of tier. -/
example : lp64UsualArithmetic (.real .longDouble) (.real .float128) = .real .float128 := by decide

/-- `_Float16` takes `float`'s rank only from `float`'s larger precision... -/
example : lp64UsualArithmetic (.real .float16) (.real .float) = .real .float := by decide

/-- ...and an integer operand converts to `_Float16` rather than widening it. -/
example : lp64UsualArithmetic (.integer .int) (.real .float16) = .real .float16 := by decide

/-- `_Float16` and `__bf16` have incomparable value sets; the common type is `_Float16`,
    not `__bf16`, as GCC and Clang convert. -/
example : lp64UsualArithmetic (.real .bfloat16) (.real .float16) = .real .float16 := by decide
example : lp64UsualArithmetic (.real .bfloat16) (.real .float16) ≠ .real .bfloat16 := by decide

/-- A complex operand keeps the result complex with the common real type. -/
example : lp64UsualArithmetic (.complex .float) (.real .double) = .complex .double := by decide

/-- Where `long double` has `double`'s format it still outranks `double`. -/
example : usualArithmeticType (integerValueProfile .llp64) windowsFloating (.real .double) (.real .longDouble) =
    .real .longDouble := by decide

/-- AAPCS64 `long double` has the IEEE binary128 value set. -/
example : aapcs64Floating.precision .longDouble = 113 := by decide

/-- AAPCS64 `long double` outranks `double`. -/
example : usualArithmeticType (integerValueProfile .lp64) aapcs64Floating
    (.real .double) (.real .longDouble) = .real .longDouble := by decide

/-- An integer never decides a floating common type. -/
example : lp64UsualArithmetic (.integer (.unsigned (.extended .int128))) (.real .float) = .real .float := by decide

end Mettapedia.Languages.C11
