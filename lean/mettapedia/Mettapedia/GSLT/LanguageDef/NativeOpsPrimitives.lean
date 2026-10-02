import Mettapedia.GSLT.LanguageDef.NativeOpsMemory

/-!
# Scalar operations within native record and storage values

Ill-typed operands have no transition in this calculus; source admission is
responsible for excluding them.  This layer does not manufacture runtime
type faults that the emitted C does not check.  Numeric refusals are the
actual division and shift guards. Boolean short-circuit evaluation belongs
to expression/control lowering, rather than to an eager primitive call.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps

open NativeWord64 (Fault encode)

def sourceUnaryOp : Unary → SourceValue → Option SourceValue
  | .not, .bool value => some (.bool (!value))
  | .complement, .word value => some (.word (NativeWord64.sourceComplement value))
  | .toWord, .byte value => some (.word (NativeWord64.sourceToWord value))
  | .toByte, .word value => some (.byte (NativeWord64.sourceToByte value))
  | _, _ => none

def targetUnaryOp : Unary → TargetValue → Option TargetValue
  | .not, .bool value => some (.bool (!value))
  | .complement, .word value => some (.word (NativeWord64.targetComplement value))
  | .toWord, .byte value => some (.word (NativeWord64.targetToWord value))
  | .toByte, .word value => some (.byte (NativeWord64.targetToByte value))
  | _, _ => none

theorem unary_value_correspondence (operation : Unary) (value : SourceValue) :
    targetUnaryOp operation (encodeValue value) = (sourceUnaryOp operation value).map encodeValue := by
  cases operation <;> cases value <;> try rfl

def sourceBinaryOp : Binary → SourceValue → SourceValue → Option (Except Fault SourceValue)
  | .word operation, .word left, .word right =>
      some ((NativeWord64.sourceBinary operation left right).map SourceValue.word)
  | .compare operation, .word left, .word right =>
      some (.ok (.bool (NativeWord64.sourceComparison operation left right)))
  | .compare operation, .byte left, .byte right =>
      some (.ok (.bool (NativeWord64.sourceComparison operation left right)))
  | .compare .eq, .bool left, .bool right => some (.ok (.bool (decide (left = right))))
  | .compare .ne, .bool left, .bool right => some (.ok (.bool (decide (left ≠ right))))
  | .compare .eq, .reference left, .reference right => some (.ok (.bool (decide (left = right))))
  | .compare .ne, .reference left, .reference right => some (.ok (.bool (decide (left ≠ right))))
  | .and, .bool left, .bool right => some (.ok (.bool (left && right)))
  | .or, .bool left, .bool right => some (.ok (.bool (left || right)))
  | _, _, _ => none

def targetBinaryOp : Binary → TargetValue → TargetValue → Option (Except Fault TargetValue)
  | .word operation, .word left, .word right =>
      some ((NativeWord64.targetBinary operation left right).map TargetValue.word)
  | .compare operation, .word left, .word right =>
      some (.ok (.bool (NativeWord64.targetComparison operation left right)))
  | .compare operation, .byte left, .byte right =>
      some (.ok (.bool (NativeWord64.targetComparison operation
        (NativeWord64.targetToWord left) (NativeWord64.targetToWord right))))
  | .compare .eq, .bool left, .bool right => some (.ok (.bool (left == right)))
  | .compare .ne, .bool left, .bool right => some (.ok (.bool (!(left == right))))
  | .compare .eq, .reference left, .reference right => some (.ok (.bool (left == right)))
  | .compare .ne, .reference left, .reference right => some (.ok (.bool (!(left == right))))
  | .and, .bool left, .bool right => some (.ok (.bool (left && right)))
  | .or, .bool left, .bool right => some (.ok (.bool (left || right)))
  | _, _, _ => none

private theorem bitvector_word_result (operation : NativeWord64.WordOp)
    (left right : NativeWord64.Word) :
    (NativeWord64.targetBinary operation (encode left) (encode right)).map TargetValue.word =
      ((NativeWord64.sourceBinary operation left right).map SourceValue.word).map encodeValue := by
  have agreement := NativeWord64.binary_correspondence operation left right
  cases native : NativeWord64.targetBinary operation (encode left) (encode right) with
  | error fault =>
      simp only [native, NativeWord64.observe, Except.map] at agreement
      rw [← agreement]
      rfl
  | ok value =>
      simp only [native, NativeWord64.observe, Except.map] at agreement
      rw [← agreement]
      simp [Except.map, encodeValue, encode, BitVec.ofFin_toFin]

private theorem beq_decide {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
    (left right : α) : (left == right) = decide (left = right) := by
  apply Bool.eq_iff_iff.mpr
  simp

theorem binary_value_correspondence (operation : Binary) (left right : SourceValue) :
    targetBinaryOp operation (encodeValue left) (encodeValue right) =
      (sourceBinaryOp operation left right).map (Except.map encodeValue) := by
  cases operation with
  | word operation =>
      cases left <;> cases right <;> try rfl
      simp only [targetBinaryOp, sourceBinaryOp, encodeValue, Option.map_some,
        bitvector_word_result]
  | compare operation =>
      cases left <;> cases right <;> try rfl
      all_goals cases operation <;>
        simp [targetBinaryOp, sourceBinaryOp, encodeValue, Except.map,
          NativeWord64.comparison_correspondence, NativeWord64.byte_promotion_comparison,
          beq_decide]
  | and => cases left <;> cases right <;> rfl
  | or => cases left <;> cases right <;> rfl

theorem unary_value_result_iff (operation : Unary) (value result : SourceValue) :
    targetUnaryOp operation (encodeValue value) = some (encodeValue result) ↔
      sourceUnaryOp operation value = some result := by
  rw [unary_value_correspondence]
  cases sourceUnaryOp operation value <;> simp [encodeValue_injective.eq_iff]

theorem unary_value_missing_iff (operation : Unary) (value : SourceValue) :
    targetUnaryOp operation (encodeValue value) = none ↔ sourceUnaryOp operation value = none := by
  rw [unary_value_correspondence]
  cases sourceUnaryOp operation value <;> simp

end Mettapedia.GSLT.LanguageDef.NativeOps
