import Mettapedia.GSLT.LanguageDef.NativeOpsCDeclarator
import Mettapedia.GSLT.LanguageDef.NativeOpsCNormalization

/-!
# Source-retaining reservation syntax controls

Nonzero aggregate initializers, compound assignments, expression sizeof and
unbraced loops retain their own syntax. Recognition does not supply a record
layout, operand evaluation schedule, integer promotion or allocator contract.
The emitted-operation lowering remains deliberately narrower.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

private def types : TypeNames := ["void".toList, "bool".toList, "Pair".toList,
  "uint32_t".toList]

theorem ordered_aggregate_initializers_retained : expressionText? types
    "(Pair){pointer, count}".toList = some
      (.aggregate ⟨"Pair".toList, 0⟩
        [.identifier "pointer".toList, .identifier "count".toList]) := by
  unfold expressionText?
  rw [show lex "(Pair){pointer, count}".toList = .ok [.punctuation "(".toList, .identifier "Pair".toList, .punctuation ")".toList, .punctuation "{".toList, .identifier "pointer".toList, .punctuation ",".toList, .identifier "count".toList, .punctuation "}".toList] by decide +kernel]
  rfl

theorem trailing_aggregate_comma_is_legal : expressionText? types
    "(Pair){pointer, count,}".toList = some
      (.aggregate ⟨"Pair".toList, 0⟩
        [.identifier "pointer".toList, .identifier "count".toList]) := by
  unfold expressionText?
  rw [show lex "(Pair){pointer, count,}".toList = .ok [.punctuation "(".toList, .identifier "Pair".toList, .punctuation ")".toList, .punctuation "{".toList, .identifier "pointer".toList, .punctuation ",".toList, .identifier "count".toList, .punctuation ",".toList, .punctuation "}".toList] by decide +kernel]
  rfl

theorem empty_c11_aggregate_refused : expressionText? types "(Pair){}".toList = none := by
  unfold expressionText?
  rw [show lex "(Pair){}".toList = .ok [.punctuation "(".toList, .identifier "Pair".toList, .punctuation ")".toList, .punctuation "{".toList, .punctuation "}".toList] by decide +kernel]
  rfl

theorem missing_aggregate_value_refused : expressionText? types "(Pair){x,,y}".toList = none := by
  unfold expressionText?
  rw [show lex "(Pair){x,,y}".toList = .ok [.punctuation "(".toList, .identifier "Pair".toList, .punctuation ")".toList, .punctuation "{".toList, .identifier "x".toList, .punctuation ",".toList, .punctuation ",".toList, .identifier "y".toList, .punctuation "}".toList] by decide +kernel]
  rfl

theorem initializer_order_not_commuted : expressionText? types
    "(Pair){count, pointer}".toList = some
      (.aggregate ⟨"Pair".toList, 0⟩
        [.identifier "count".toList, .identifier "pointer".toList]) := by
  unfold expressionText?
  rw [show lex "(Pair){count, pointer}".toList = .ok [.punctuation "(".toList, .identifier "Pair".toList, .punctuation ")".toList, .punctuation "{".toList, .identifier "count".toList, .punctuation ",".toList, .identifier "pointer".toList, .punctuation "}".toList] by decide +kernel]
  rfl

theorem sizeof_expression_is_not_a_call : expressionText? types
    "sizeof(**items)".toList = some
      (.sizeOfExpr (.unary .dereference
        (.unary .dereference (.identifier "items".toList)))) := by
  unfold expressionText?
  rw [show lex "sizeof(**items)".toList = .ok [.identifier "sizeof".toList, .punctuation "(".toList, .punctuation "*".toList, .punctuation "*".toList, .identifier "items".toList, .punctuation ")".toList] by decide +kernel]
  rfl

theorem sizeof_operand_increment_retained : expressionText? types
    "sizeof i++".toList = some (.sizeOfExpr (.postIncrement (.identifier ['i']))) := by
  unfold expressionText?
  rw [show lex "sizeof i++".toList = .ok [.identifier "sizeof".toList, .identifier "i".toList, .punctuation "++".toList] by decide +kernel]
  rfl

theorem sizeof_type_retained : expressionText? types "sizeof(Pair *)".toList =
    some (.sizeOf ⟨"Pair".toList, 1⟩) := by
  unfold expressionText?
  rw [show lex "sizeof(Pair *)".toList = .ok [.identifier "sizeof".toList, .punctuation "(".toList, .identifier "Pair".toList, .punctuation "*".toList, .punctuation ")".toList] by decide +kernel]
  rfl

theorem bool_compound_assignment_retained : blockText? types
    "{ found |= !present; }".toList = some
      [.compoundAssign .bitOr (.identifier "found".toList)
        (.unary .not (.identifier "present".toList))] := by
  unfold blockText?
  rw [show lex "{ found |= !present; }".toList = .ok [.punctuation "{".toList, .identifier "found".toList, .punctuation "|=".toList, .punctuation "!".toList, .identifier "present".toList, .punctuation ";".toList, .punctuation "}".toList] by decide +kernel]
  rfl

theorem arithmetic_compound_assignment_retained : blockText? types
    "{ next *= 2u; }".toList = some
      [.compoundAssign .mul (.identifier "next".toList) (.unsignedInteger 2)] := by
  unfold blockText?
  rw [show lex "{ next *= 2u; }".toList = .ok [.punctuation "{".toList, .identifier "next".toList, .punctuation "*=".toList, .number "2u".toList, .punctuation ";".toList, .punctuation "}".toList] by decide +kernel]
  rfl

theorem compound_lvalue_is_not_duplicated : blockText? types
    "{ data[i++] += x; }".toList = some
      [.compoundAssign .add
        (.index (.identifier "data".toList) (.postIncrement (.identifier ['i'])))
        (.identifier ['x'])] := by
  unfold blockText?
  rw [show lex "{ data[i++] += x; }".toList = .ok [.punctuation "{".toList, .identifier "data".toList, .punctuation "[".toList, .identifier "i".toList, .punctuation "++".toList, .punctuation "]".toList, .punctuation "+=".toList, .identifier "x".toList, .punctuation ";".toList, .punctuation "}".toList] by decide +kernel]
  rfl

theorem compound_assignment_missing_rhs_refused : blockText? types
    "{ next *= ; }".toList = none := by
  unfold blockText?
  rw [show lex "{ next *= ; }".toList = .ok [.punctuation "{".toList, .identifier "next".toList, .punctuation "*=".toList, .punctuation ";".toList, .punctuation "}".toList] by decide +kernel]
  rfl

theorem unsupported_three_character_assignment_refused : blockText? types
    "{ next <<= 2u; }".toList = none := by
  unfold blockText?
  rw [show lex "{ next <<= 2u; }".toList = .ok [.punctuation "{".toList, .identifier "next".toList, .punctuation "<<".toList, .punctuation "=".toList, .number "2u".toList, .punctuation ";".toList, .punctuation "}".toList] by decide +kernel]
  rfl

theorem unbraced_loop_body_retained : blockText? types
    "{ for (uint32_t i = 0u; i < count; i++) present = rows[i] == x; }".toList = some
      [.forLoop ⟨"uint32_t".toList, 0⟩ ['i'] (.unsignedInteger 0)
        (.binary .lt (.identifier ['i']) (.identifier "count".toList))
        (.postIncrement (.identifier ['i']))
        [.assign (.identifier "present".toList)
          (.binary .eq (.index (.identifier "rows".toList) (.identifier ['i']))
            (.identifier ['x']))]] := by
  unfold blockText?
  rw [show lex "{ for (uint32_t i = 0u; i < count; i++) present = rows[i] == x; }".toList = .ok [.punctuation "{".toList, .identifier "for".toList, .punctuation "(".toList, .identifier "uint32_t".toList, .identifier "i".toList, .punctuation "=".toList, .number "0u".toList, .punctuation ";".toList, .identifier "i".toList, .punctuation "<".toList, .identifier "count".toList, .punctuation ";".toList, .identifier "i".toList, .punctuation "++".toList, .punctuation ")".toList, .identifier "present".toList, .punctuation "=".toList, .identifier "rows".toList, .punctuation "[".toList, .identifier "i".toList, .punctuation "]".toList, .punctuation "==".toList, .identifier "x".toList, .punctuation ";".toList, .punctuation "}".toList] by decide +kernel]
  rfl

theorem while_condition_and_break_retained : blockText? types
    "{ while (next < required) { next *= 2u; if (stop) break; } }".toList = some
      [.whileLoop (.binary .lt (.identifier "next".toList) (.identifier "required".toList))
        [.compoundAssign .mul (.identifier "next".toList) (.unsignedInteger 2),
         .branch (.identifier "stop".toList) [.break] []]] := by
  unfold blockText?
  rw [show lex "{ while (next < required) { next *= 2u; if (stop) break; } }".toList = .ok [.punctuation "{".toList, .identifier "while".toList, .punctuation "(".toList, .identifier "next".toList, .punctuation "<".toList, .identifier "required".toList, .punctuation ")".toList, .punctuation "{".toList, .identifier "next".toList, .punctuation "*=".toList, .number "2u".toList, .punctuation ";".toList, .identifier "if".toList, .punctuation "(".toList, .identifier "stop".toList, .punctuation ")".toList, .identifier "break".toList, .punctuation ";".toList, .punctuation "}".toList, .punctuation "}".toList] by decide +kernel]
  rfl

theorem aggregate_syntax_does_not_grant_readonly_authority
    (catalogue : List External) (fuel : Nat) (type : CType) (values : List CExpr) :
    readOnlyExpression catalogue fuel (.aggregate type values) = false := by
  cases fuel <;> rfl

theorem expression_sizeof_requires_typed_authority
    (catalogue : List External) (fuel : Nat) (operand : CExpr) :
    readOnlyExpression catalogue fuel (.sizeOfExpr operand) = false := by
  cases fuel <;> rfl

theorem compound_syntax_does_not_grant_readonly_authority
    (catalogue : List External) (fuel : Nat) (operator : BinaryOperator)
    (location value : CExpr) :
    readOnlyStatement catalogue fuel (.compoundAssign operator location value) = false := by
  cases fuel <;> rfl

#print axioms ordered_aggregate_initializers_retained
#print axioms trailing_aggregate_comma_is_legal
#print axioms empty_c11_aggregate_refused
#print axioms missing_aggregate_value_refused
#print axioms initializer_order_not_commuted
#print axioms sizeof_expression_is_not_a_call
#print axioms sizeof_operand_increment_retained
#print axioms sizeof_type_retained
#print axioms bool_compound_assignment_retained
#print axioms arithmetic_compound_assignment_retained
#print axioms compound_lvalue_is_not_duplicated
#print axioms compound_assignment_missing_rhs_refused
#print axioms unsupported_three_character_assignment_refused
#print axioms unbraced_loop_body_retained
#print axioms while_condition_and_break_retained
#print axioms aggregate_syntax_does_not_grant_readonly_authority
#print axioms expression_sizeof_requires_typed_authority
#print axioms compound_syntax_does_not_grant_readonly_authority

end Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
