import Mettapedia.Languages.C11.ArithmeticConversions

/-!
# The C11 type language: compatibility and composite types

The types of N1570 6.2.5: `void`, arithmetic types, plain `char` (a type
distinct from both `signed char` and `unsigned char`), enumerations, pointers,
arrays, functions, structures and unions. Qualifiers sit where C places them:
on a pointer's referenced type, on an array's elements and on each parameter.

Compatibility (6.2.7p1) follows 6.7.2.2p4 (an enumeration is compatible with
its integer type), 6.7.3p10 (identically qualified compatible types),
6.7.6.1p2 (pointers to compatible types), 6.7.6.2p6 (arrays of compatible
elements whose sizes agree when both are known) and 6.7.6.3p15 (functions with
compatible results whose prototypes agree in length, ellipsis and the
unqualified parameter types, or an unprototyped type against a prototype whose
parameters the default argument promotions leave unchanged). Structures and
unions of one translation unit are compatible exactly when they are the same
tag.

Compatibility is reflexive and symmetric but not transitive. The composite
type (6.2.7p3) of compatible types is compatible with both.

The default argument promotions use the LP64 integer profile and promote
`float` to `double`; another data model is another instance of these rules.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11

structure TypeQualifiers where
  const : Bool := false
  volatile : Bool := false
  restrict : Bool := false
  atomic : Bool := false
  deriving DecidableEq, Repr

mutual
inductive CType where
  | void
  | arithmetic (type : ArithmeticType IntegerExtension)
  | character
  | enumeration (tag : Nat) (compatible : IntegerType IntegerExtension)
  | pointer (referencedQualifiers : TypeQualifiers) (referenced : CType)
  | array (elementQualifiers : TypeQualifiers) (element : CType) (length : Option Nat)
  | function (result : CType) (parameters : CParameters)
  | record (isUnion : Bool) (tag : Nat)

inductive CParameters where
  | unprototyped
  | prototype (types : CTypeList) (variadic : Bool)

inductive CTypeList where
  | nil
  | cons (qualifiers : TypeQualifiers) (head : CType) (tail : CTypeList)
end

deriving instance DecidableEq for CType, CParameters, CTypeList

/-- 6.5.2.2p6: a parameter type that the default argument promotions leave
    unchanged (LP64 integers; `float` becomes `double`, while `_Float16` and
    `__bf16` keep their types, as GCC and Clang pass them). -/
def CType.promotionStable : CType → Bool
  | .arithmetic (.integer type) => lp64Promote type == type
  | .arithmetic (.real .float) => false
  | .character => false
  | .enumeration _ compatible => lp64Promote compatible == compatible
  | _ => true

def CTypeList.promotionStable : CTypeList → Bool
  | .nil => true
  | .cons _ head tail => head.promotionStable && tail.promotionStable

mutual
def CType.compatible : CType → CType → Bool
  | .void, .void => true
  | .arithmetic left, .arithmetic right => left == right
  | .character, .character => true
  | .enumeration left _, .enumeration right _ => left == right
  | .enumeration _ compatible, .arithmetic (.integer type) => compatible == type
  | .arithmetic (.integer type), .enumeration _ compatible => compatible == type
  | .pointer leftQualifiers left, .pointer rightQualifiers right =>
      leftQualifiers == rightQualifiers && left.compatible right
  | .array leftQualifiers left leftLength, .array rightQualifiers right rightLength =>
      leftQualifiers == rightQualifiers && left.compatible right &&
        (leftLength.isNone || rightLength.isNone || leftLength == rightLength)
  | .function leftResult leftParameters, .function rightResult rightParameters =>
      leftResult.compatible rightResult && leftParameters.compatible rightParameters
  | .record leftUnion leftTag, .record rightUnion rightTag => leftUnion == rightUnion && leftTag == rightTag
  | _, _ => false

def CParameters.compatible : CParameters → CParameters → Bool
  | .unprototyped, .unprototyped => true
  | .prototype left leftVariadic, .prototype right rightVariadic =>
      leftVariadic == rightVariadic && left.compatible right
  | .unprototyped, .prototype types variadic => !variadic && types.promotionStable
  | .prototype types variadic, .unprototyped => !variadic && types.promotionStable

/-- Parameter qualifiers do not take part (6.7.6.3p15: unqualified versions). -/
def CTypeList.compatible : CTypeList → CTypeList → Bool
  | .nil, .nil => true
  | .cons _ left leftTail, .cons _ right rightTail => left.compatible right && leftTail.compatible rightTail
  | _, _ => false
end

mutual
theorem CType.compatible_refl : (type : CType) → type.compatible type = true
  | .void => rfl
  | .arithmetic _ => by simp [CType.compatible]
  | .character => rfl
  | .enumeration _ _ => by simp [CType.compatible]
  | .pointer _ referenced => by simp [CType.compatible, referenced.compatible_refl]
  | .array _ element _ => by simp [CType.compatible, element.compatible_refl]
  | .function result parameters => by
      simp [CType.compatible, result.compatible_refl, parameters.compatible_refl]
  | .record _ _ => by simp [CType.compatible]

theorem CParameters.compatible_refl : (parameters : CParameters) → parameters.compatible parameters = true
  | .unprototyped => rfl
  | .prototype types _ => by simp [CParameters.compatible, types.compatible_refl]

theorem CTypeList.compatible_refl : (types : CTypeList) → types.compatible types = true
  | .nil => rfl
  | .cons _ head tail => by simp [CTypeList.compatible, head.compatible_refl, tail.compatible_refl]
end

theorem lawfulBEq_symm {α : Type} [BEq α] [LawfulBEq α] (a b : α) : (a == b) = (b == a) :=
  Bool.eq_iff_iff.mpr (by rw [beq_iff_eq, beq_iff_eq]; exact eq_comm)

mutual
theorem CType.compatible_symm : (left right : CType) → left.compatible right = right.compatible left
  | .void, right => by cases right <;> rfl
  | .arithmetic left, right => by
      cases right with
      | arithmetic right => simp only [CType.compatible, lawfulBEq_symm left right]
      | enumeration _ compatible => cases left <;> rfl
      | _ => cases left <;> rfl
  | .character, right => by cases right <;> rfl
  | .enumeration leftTag leftCompatible, right => by
      cases right with
      | enumeration rightTag _ => simp only [CType.compatible, lawfulBEq_symm leftTag rightTag]
      | arithmetic type => cases type <;> rfl
      | _ => rfl
  | .pointer leftQualifiers left, right => by
      cases right with
      | pointer rightQualifiers right =>
          simp only [CType.compatible, CType.compatible_symm left right, lawfulBEq_symm leftQualifiers rightQualifiers]
      | _ => rfl
  | .array leftQualifiers left leftLength, right => by
      cases right with
      | array rightQualifiers right rightLength =>
          simp only [CType.compatible, CType.compatible_symm left right, lawfulBEq_symm leftQualifiers rightQualifiers,
            lawfulBEq_symm leftLength rightLength, Bool.or_comm (Option.isNone leftLength)]
      | _ => rfl
  | .function leftResult leftParameters, right => by
      cases right with
      | function rightResult rightParameters =>
          simp [CType.compatible, CType.compatible_symm leftResult rightResult,
            CParameters.compatible_symm leftParameters rightParameters]
      | _ => rfl
  | .record leftUnion leftTag, right => by
      cases right with
      | record rightUnion rightTag =>
          simp only [CType.compatible, lawfulBEq_symm leftUnion rightUnion, lawfulBEq_symm leftTag rightTag]
      | _ => rfl

theorem CParameters.compatible_symm : (left right : CParameters) → left.compatible right = right.compatible left
  | .unprototyped, .unprototyped => rfl
  | .unprototyped, .prototype _ _ => rfl
  | .prototype _ _, .unprototyped => rfl
  | .prototype left leftVariadic, .prototype right rightVariadic => by
      simp only [CParameters.compatible, CTypeList.compatible_symm left right, lawfulBEq_symm leftVariadic rightVariadic]

theorem CTypeList.compatible_symm : (left right : CTypeList) → left.compatible right = right.compatible left
  | .nil, .nil => rfl
  | .nil, .cons _ _ _ => rfl
  | .cons _ _ _, .nil => rfl
  | .cons _ left leftTail, .cons _ right rightTail => by
      simp [CTypeList.compatible, CType.compatible_symm left right, CTypeList.compatible_symm leftTail rightTail]
end

/-! ## Composite types (6.2.7p3) -/

mutual
def CType.composite : CType → CType → CType
  | .pointer qualifiers left, .pointer _ right => .pointer qualifiers (left.composite right)
  | .array qualifiers left leftLength, .array _ right rightLength =>
      .array qualifiers (left.composite right) (leftLength.or rightLength)
  | .function leftResult leftParameters, .function rightResult rightParameters =>
      .function (leftResult.composite rightResult) (leftParameters.composite rightParameters)
  | left, _ => left

/-- A prototype wins over an unprototyped declaration; prototypes compose
    parameter by parameter. -/
def CParameters.composite : CParameters → CParameters → CParameters
  | .prototype left variadic, .prototype right _ => .prototype (left.composite right) variadic
  | .prototype types variadic, .unprototyped => .prototype types variadic
  | .unprototyped, right => right

def CTypeList.composite : CTypeList → CTypeList → CTypeList
  | .cons qualifiers left leftTail, .cons _ right rightTail =>
      .cons qualifiers (left.composite right) (leftTail.composite rightTail)
  | left, _ => left
end

mutual
theorem CType.composite_compatible : (left right : CType) → left.compatible right = true →
    (left.composite right).compatible left = true ∧ (left.composite right).compatible right = true
  | .pointer leftQualifiers left, .pointer rightQualifiers right, compatible => by
      simp only [CType.compatible, Bool.and_eq_true, beq_iff_eq] at compatible
      obtain ⟨equal, inner⟩ := compatible
      subst equal
      have := CType.composite_compatible left right inner
      simp [CType.composite, CType.compatible, this.1, this.2]
  | .array leftQualifiers left leftLength, .array rightQualifiers right rightLength, compatible => by
      simp only [CType.compatible, Bool.and_eq_true, Bool.or_eq_true,
        Option.isNone_iff_eq_none, beq_iff_eq] at compatible
      obtain ⟨⟨equal, inner⟩, lengths⟩ := compatible
      subst equal
      have := CType.composite_compatible left right inner
      cases leftLength <;> cases rightLength <;> simp_all [CType.composite, CType.compatible, Option.or]
  | .function leftResult leftParameters, .function rightResult rightParameters, compatible => by
      simp only [CType.compatible, Bool.and_eq_true] at compatible
      have results := CType.composite_compatible leftResult rightResult compatible.1
      have parameters := CParameters.composite_compatible leftParameters rightParameters compatible.2
      simp [CType.composite, CType.compatible, results.1, results.2, parameters.1, parameters.2]
  | .void, right, compatible => by cases right <;> simp_all [CType.composite, CType.compatible]
  | .arithmetic type, right, compatible => by
      cases right <;> simp_all [CType.composite, CType.compatible_refl]
  | .character, right, compatible => by cases right <;> simp_all [CType.composite, CType.compatible]
  | .enumeration tag compatibleType, right, compatible => by
      cases right <;> simp_all [CType.composite, CType.compatible_refl]
  | .record isUnion tag, right, compatible => by
      cases right <;> simp_all [CType.composite, CType.compatible_refl]
  | .pointer _ _, .void, compatible | .pointer _ _, .arithmetic _, compatible
  | .pointer _ _, .character, compatible | .pointer _ _, .enumeration _ _, compatible
  | .pointer _ _, .array _ _ _, compatible | .pointer _ _, .function _ _, compatible
  | .pointer _ _, .record _ _, compatible => by simp [CType.compatible] at compatible
  | .array _ _ _, .void, compatible | .array _ _ _, .arithmetic _, compatible
  | .array _ _ _, .character, compatible | .array _ _ _, .enumeration _ _, compatible
  | .array _ _ _, .pointer _ _, compatible | .array _ _ _, .function _ _, compatible
  | .array _ _ _, .record _ _, compatible => by simp [CType.compatible] at compatible
  | .function _ _, .void, compatible | .function _ _, .arithmetic _, compatible
  | .function _ _, .character, compatible | .function _ _, .enumeration _ _, compatible
  | .function _ _, .pointer _ _, compatible | .function _ _, .array _ _ _, compatible
  | .function _ _, .record _ _, compatible => by simp [CType.compatible] at compatible

theorem CParameters.composite_compatible : (left right : CParameters) → left.compatible right = true →
    (left.composite right).compatible left = true ∧ (left.composite right).compatible right = true
  | .unprototyped, right, compatible => by
      simp [CParameters.composite, CParameters.compatible_refl, CParameters.compatible_symm right,
        compatible]
  | .prototype types variadic, .unprototyped, compatible => by
      simp [CParameters.composite, CParameters.compatible_refl, compatible]
  | .prototype left leftVariadic, .prototype right rightVariadic, compatible => by
      simp only [CParameters.compatible, Bool.and_eq_true, beq_iff_eq] at compatible
      obtain ⟨variadic, lists⟩ := compatible
      have := CTypeList.composite_compatible left right lists
      simp [CParameters.composite, CParameters.compatible, variadic, this.1, this.2]

theorem CTypeList.composite_compatible : (left right : CTypeList) → left.compatible right = true →
    (left.composite right).compatible left = true ∧ (left.composite right).compatible right = true
  | .nil, right, compatible => by
      cases right <;> simp_all [CTypeList.composite, CTypeList.compatible]
  | .cons _ left leftTail, .cons _ right rightTail, compatible => by
      simp only [CTypeList.compatible, Bool.and_eq_true] at compatible
      have heads := CType.composite_compatible left right compatible.1
      have tails := CTypeList.composite_compatible leftTail rightTail compatible.2
      simp [CTypeList.composite, CTypeList.compatible, heads.1, heads.2, tails.1, tails.2]
  | .cons _ _ _, .nil, compatible => by simp [CTypeList.compatible] at compatible
end

/-! ## Positive and negative examples -/

private def int : CType := .arithmetic (.integer .int)
private def long : CType := .arithmetic (.integer (.signed (.standard .long)))
private def char : CType := .arithmetic (.integer (.signed (.standard .char)))
private def unqualified : TypeQualifiers := {}
private def constant : TypeQualifiers := { const := true }

/-- The default argument promotions change `float`, but leave `_Float16` and `__bf16`. -/
example : (CType.arithmetic (.real .float)).promotionStable = false := by decide
example : (CType.arithmetic (.real .float16)).promotionStable = true ∧
    (CType.arithmetic (.real .bfloat16)).promotionStable = true := by decide

/-- Plain `char` is a type of its own, even where it is signed (6.2.5p15). -/
example : CType.character.compatible char = false := by decide

/-- An enumeration is compatible with its integer type, but not with another
    enumeration of that type. -/
example : (CType.enumeration 1 .unsignedInt).compatible (.arithmetic (.integer .unsignedInt)) = true := by decide
example : (CType.enumeration 1 .unsignedInt).compatible (.enumeration 2 .unsignedInt) = false := by decide

/-- Qualifiers on a referenced type must agree: `const int *` and `int *` differ. -/
example : (CType.pointer constant int).compatible (.pointer unqualified int) = false := by decide

/-- Compatibility is not transitive: `int[]` is compatible with `int[2]` and
    `int[3]`, which are incompatible. -/
example : (CType.array unqualified int none).compatible (.array unqualified int (some 2)) = true ∧
    (CType.array unqualified int none).compatible (.array unqualified int (some 3)) = true ∧
    (CType.array unqualified int (some 2)).compatible (.array unqualified int (some 3)) = false := by decide

/-- Nor through unprototyped functions: `int ()` is compatible with `int (int)`
    and `int (long)`, which are incompatible. -/
example :
    (CType.function int .unprototyped).compatible (.function int (.prototype (.cons unqualified int .nil) false)) = true ∧
    (CType.function int .unprototyped).compatible (.function int (.prototype (.cons unqualified long .nil) false)) = true ∧
    (CType.function int (.prototype (.cons unqualified int .nil) false)).compatible
      (.function int (.prototype (.cons unqualified long .nil) false)) = false := by decide

/-- A parameter changed by the default promotions cannot meet an unprototyped
    declaration: `int ()` and `int (char)` are incompatible. -/
example : (CType.function int .unprototyped).compatible
    (.function int (.prototype (.cons unqualified char .nil) false)) = false := by decide

/-- Parameter qualifiers do not take part: `int (const int)` and `int (int)` agree. -/
example : (CType.function int (.prototype (.cons constant int .nil) false)).compatible
    (.function int (.prototype (.cons unqualified int .nil) false)) = true := by decide

/-- The composite of `int[]` and `int[3]` is `int[3]`, and of `int ()` and
    `int (int)` the prototype. -/
example : (CType.array unqualified int none).composite (.array unqualified int (some 3)) =
    .array unqualified int (some 3) := by decide
example : (CType.function int .unprototyped).composite (.function int (.prototype (.cons unqualified int .nil) false)) =
    .function int (.prototype (.cons unqualified int .nil) false) := by decide

end Mettapedia.Languages.C11

namespace Mettapedia.Languages.C11.CharacterPointerViews

abbrev unsignedCharacter : CType := .arithmetic (.integer (.unsigned (.standard .char)))
abbrev signedCharacter : CType := .arithmetic (.integer (.signed (.standard .char)))
abbrev destination : CType := .pointer { const := true } unsignedCharacter

inductive Character : CType → Prop where
  | plain : Character .character
  | signed : Character signedCharacter
  | unsigned : Character unsignedCharacter

def character (type : CType) : Bool :=
  type == .character || type == signedCharacter || type == unsignedCharacter

theorem character_iff (type : CType) : character type = true ↔ Character type := by
  simp only [character, Bool.or_eq_true, beq_iff_eq]
  constructor
  · rintro ((rfl | rfl) | rfl)
    · exact .plain
    · exact .signed
    · exact .unsigned
  · intro value
    cases value with
    | plain => exact Or.inl (Or.inl rfl)
    | signed => exact Or.inl (Or.inr rfl)
    | unsigned => exact Or.inr rfl

/-- The source qualifier is retained; the destination adds readonly access.
This is an admitted source profile, not a claim that other casts are C UB. -/
inductive ReadOnly : CType → CType → Prop where
  | character (constant : Bool) (pointee : CType) (kind : Character pointee) :
      ReadOnly (.pointer { const := constant } pointee) destination

def accepted (source target : CType) : Bool := match source with
  | .pointer qualifiers pointee =>
      !qualifiers.volatile && !qualifiers.restrict && !qualifiers.atomic &&
        character pointee && target == destination
  | _ => false

theorem accepted_iff (source target : CType) :
    accepted source target = true ↔ ReadOnly source target := by
  cases source with
  | pointer qualifiers pointee =>
      cases qualifiers with
      | mk constant volatile restricted atomic =>
          simp only [accepted, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq,
            character_iff]
          constructor
          · rintro ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, kind⟩, rfl⟩
            exact .character constant pointee kind
          · intro readOnly
            cases readOnly
            simp_all
  | _ =>
      constructor
      · intro impossible
        cases impossible
      · intro impossible
        cases impossible


end Mettapedia.Languages.C11.CharacterPointerViews

namespace Mettapedia.Languages.C11.CharacterPointerViews.Controls

theorem plain_to_const_unsigned :
    ReadOnly (.pointer {} .character) destination := .character false _ .plain

theorem const_source_is_not_stripped :
    ReadOnly (.pointer { const := true } .character) destination :=
  .character true _ .plain

theorem character_types_need_not_be_compatible :
    CType.character.compatible unsignedCharacter = false ∧
      accepted (.pointer {} .character) destination = true := by decide

theorem unsupported_qualifier_and_depth_are_refused :
    accepted (.pointer { volatile := true } .character) destination = false ∧
    accepted (.pointer { atomic := true } .character) destination = false ∧
    accepted (.pointer { restrict := true } .character) destination = false ∧
    accepted (.pointer {} (.pointer {} .character)) destination = false := by decide

theorem nonpointer_and_nonreadonly_destinations_are_refused :
    accepted .character destination = false ∧
    accepted (.pointer {} .character) (.pointer {} unsignedCharacter) = false ∧
    accepted (.pointer {} .character) (.pointer { const := true } .character) = false := by decide

end Mettapedia.Languages.C11.CharacterPointerViews.Controls
