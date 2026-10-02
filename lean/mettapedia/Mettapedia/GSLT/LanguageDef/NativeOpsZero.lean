import Mettapedia.GSLT.LanguageDef.NativeOpsMemory

/-!
# Typed zero initialization

Source zero values are constructed from the declared record fields and bounded
natural scalars. Target zeros independently describe C scalar and compound
initializers with bit vectors. References and arrays do not traverse their
pointees. By-value recursive records have no finite zero derivation; source
admission separately excludes such layouts. These relations impose no depth
limit on guest terms or on execution.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

mutual
  inductive SourceZero (interface : Interface) : NativeType → SourceValue → Prop where
    | unit : SourceZero interface .unit .unit
    | word : SourceZero interface .word (.word 0)
    | byte : SourceZero interface .byte (.byte 0)
    | bool : SourceZero interface .bool (.bool false)
    | reference (element : NativeType) : SourceZero interface (.ref element) (.reference none)
    | array (element : NativeType) : SourceZero interface (.array element) (.array element none 0)
    | record {name : String} {declaration : Record} {values : List SourceValue}
        (found : lookupRecord interface name = some declaration)
        (fields : SourceZeroFields interface declaration.fields values) :
        SourceZero interface (.named name) (.record name values)

  inductive SourceZeroFields (interface : Interface) :
      List Parameter → List SourceValue → Prop where
    | nil : SourceZeroFields interface [] []
    | cons {field : Parameter} {rest : List Parameter} {value : SourceValue}
        {values : List SourceValue}
        (head : SourceZero interface field.type value)
        (tail : SourceZeroFields interface rest values) :
        SourceZeroFields interface (field :: rest) (value :: values)
end

mutual
  inductive TargetZero (interface : Interface) : NativeType → TargetValue → Prop where
    | scalarUnit : TargetZero interface .unit .unit
    | unsignedWord : TargetZero interface .word (.word (BitVec.ofNat 64 0))
    | unsignedByte : TargetZero interface .byte (.byte (BitVec.ofNat 8 0))
    | boolean : TargetZero interface .bool (.bool false)
    | nullPointer (element : NativeType) :
        TargetZero interface (.ref element) (.reference none)
    | emptyView (element : NativeType) :
        TargetZero interface (.array element) (.array element none (BitVec.ofNat 64 0))
    | compound {name : String} {declaration : Record} {values : List TargetValue}
        (layout : lookupRecord interface name = some declaration)
        (initializers : TargetZeroFields interface declaration.fields values) :
        TargetZero interface (.named name) (.record name values)

  inductive TargetZeroFields (interface : Interface) :
      List Parameter → List TargetValue → Prop where
    | endFields : TargetZeroFields interface [] []
    | nextField {field : Parameter} {rest : List Parameter} {value : TargetValue}
        {values : List TargetValue}
        (initializer : TargetZero interface field.type value)
        (remaining : TargetZeroFields interface rest values) :
        TargetZeroFields interface (field :: rest) (value :: values)
end

mutual
  theorem zero_preservation {interface : Interface} {type : NativeType} {value : SourceValue}
      (zero : SourceZero interface type value) : TargetZero interface type (encodeValue value) := by
    cases zero with
    | unit => exact .scalarUnit
    | word => exact .unsignedWord
    | byte => exact .unsignedByte
    | bool => exact .boolean
    | reference element => exact .nullPointer element
    | array element => exact .emptyView element
    | record found fields => exact .compound found (zero_fields_preservation fields)
  termination_by sizeOf value
  decreasing_by simp_wf; omega

  theorem zero_fields_preservation {interface : Interface} {fields : List Parameter}
      {values : List SourceValue} (zeros : SourceZeroFields interface fields values) :
      TargetZeroFields interface fields (encodeValues values) := by
    cases zeros with
    | nil => exact .endFields
    | cons head tail => exact .nextField (zero_preservation head) (zero_fields_preservation tail)
  termination_by sizeOf values
  decreasing_by all_goals simp_wf; all_goals omega
end

mutual
  theorem zero_reflection {interface : Interface} {type : NativeType} {value : TargetValue}
      (zero : TargetZero interface type value) : SourceZero interface type (decodeValue value) := by
    cases zero with
    | scalarUnit => exact .unit
    | unsignedWord => exact .word
    | unsignedByte => exact .byte
    | boolean => exact .bool
    | nullPointer element => exact .reference element
    | emptyView element => exact .array element
    | compound layout initializers => exact .record layout (zero_fields_reflection initializers)
  termination_by sizeOf value
  decreasing_by simp_wf; omega

  theorem zero_fields_reflection {interface : Interface} {fields : List Parameter}
      {values : List TargetValue} (zeros : TargetZeroFields interface fields values) :
      SourceZeroFields interface fields (decodeValues values) := by
    cases zeros with
    | endFields => exact .nil
    | nextField initializer remaining =>
        exact .cons (zero_reflection initializer) (zero_fields_reflection remaining)
  termination_by sizeOf values
  decreasing_by all_goals simp_wf; all_goals omega
end

theorem zero_correspondence (interface : Interface) (type : NativeType) (value : SourceValue) :
    TargetZero interface type (encodeValue value) ↔ SourceZero interface type value := by
  constructor
  · intro zero
    simpa only [decode_encode_value] using zero_reflection zero
  · exact zero_preservation

theorem zero_no_extra_result {interface : Interface} {type : NativeType} {value : TargetValue}
    (zero : TargetZero interface type value) :
    ∃ source, SourceZero interface type source ∧ value = encodeValue source :=
  ⟨decodeValue value, zero_reflection zero, (encode_decode_value value).symm⟩

theorem reference_zero_does_not_need_pointee_layout (interface : Interface) :
    SourceZero interface (.ref (.named "Unallocated")) (.reference none) := .reference _

theorem byte_zero_cannot_initialize_word (interface : Interface) :
    ¬ TargetZero interface .word (.byte 0) := by
  intro zero
  cases zero

theorem missing_by_value_record_has_no_zero {interface : Interface} {name : String}
    (missing : lookupRecord interface name = none) (value : SourceValue) :
    ¬ SourceZero interface (.named name) value := by
  intro zero
  cases zero with
  | record found _ => simp [missing] at found

end Mettapedia.GSLT.LanguageDef.NativeOps
