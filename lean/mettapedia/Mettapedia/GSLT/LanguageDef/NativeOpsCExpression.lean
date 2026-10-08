import Mettapedia.GSLT.LanguageDef.NativeOpsCSyntax

/-!
# Complete expression recognition for emitted C

The recognizer uses C precedence, typed cast names and ordinary postfix
selectors. Its structural budget is derived from the supplied finite token
list; it is not an execution or guest recursion limit. A complete expression
must consume every token. Calls remain syntax pending typed catalogue checks.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

mutual
  def expression? (fuel : Nat) (names : TypeNames) (minimum : Nat)
      (tokens : List Token) : Option (CExpr × List Token) :=
    match fuel with
    | 0 => none
    | fuel + 1 => do
        let (first, rest) ← prefix? fuel names tokens
        expressionTail? fuel names minimum first rest

  def expressionTail? (fuel : Nat) (names : TypeNames) (minimum : Nat)
      (left : CExpr) (tokens : List Token) : Option (CExpr × List Token) :=
    match tokens with
    | .punctuation ['?'] :: rest =>
        if minimum != 0 then some (left, tokens)
        else match fuel with
          | 0 => none
          | fuel + 1 => do
              let (whenTrue, afterTrue) ← expression? fuel names 0 rest
              match afterTrue with
              | .punctuation [':'] :: afterColon => do
                  let (whenFalse, afterFalse) ← expression? fuel names 0 afterColon
                  some (.conditional left whenTrue whenFalse, afterFalse)
              | _ => none
    | .punctuation symbol :: rest =>
        match binaryOperator? symbol with
        | none => some (left, tokens)
        | some (operator, precedence) =>
            if precedence < minimum then some (left, tokens)
            else match fuel with
              | 0 => none
              | fuel + 1 => do
                  let (right, afterRight) ← expression? fuel names (precedence + 1) rest
                  expressionTail? fuel names minimum (.binary operator left right) afterRight
    | _ => some (left, tokens)

  def prefix? (fuel : Nat) (names : TypeNames)
      (tokens : List Token) : Option (CExpr × List Token) :=
    match fuel with
    | 0 => none
    | fuel + 1 =>
        match tokens with
        | .punctuation ['!'] :: rest => do
            let (operand, afterOperand) ← prefix? fuel names rest
            some (.unary .not operand, afterOperand)
        | .punctuation ['~'] :: rest => do
            let (operand, afterOperand) ← prefix? fuel names rest
            some (.unary .complement operand, afterOperand)
        | .punctuation ['*'] :: rest => do
            let (operand, afterOperand) ← prefix? fuel names rest
            some (.unary .dereference operand, afterOperand)
        | .punctuation ['&'] :: rest => do
            let (operand, afterOperand) ← prefix? fuel names rest
            some (.unary .address operand, afterOperand)
        | .punctuation ['+', '+'] :: rest => do
            let (operand, afterOperand) ← prefix? fuel names rest
            some (.unary .increment operand, afterOperand)
        | .punctuation ['-', '-'] :: rest => do
            let (operand, afterOperand) ← prefix? fuel names rest
            some (.unary .decrement operand, afterOperand)
        | .punctuation ['-'] :: rest => do
            let (operand, afterOperand) ← prefix? fuel names rest
            some (.unary .negate operand, afterOperand)
        | .punctuation ['('] :: rest =>
            match cType? names rest with
            | some (type, .punctuation [')'] :: afterType) =>
                match afterType with
                | .punctuation ['{'] :: .number ['0'] :: .punctuation ['}'] :: afterZero =>
                    postfix? fuel names (.zero type) afterZero
                | .punctuation ['{'] :: afterOpen => do
                    let (values, afterValues) ← initializers? fuel names afterOpen
                    postfix? fuel names (.aggregate type values) afterValues
                | _ => do
                    let (operand, afterOperand) ← prefix? fuel names afterType
                    some (.cast type operand, afterOperand)
            | _ => do
                let (inside, afterInside) ← expression? fuel names 0 rest
                match afterInside with
                | .punctuation [')'] :: afterParen => postfix? fuel names inside afterParen
                | _ => none
        | .identifier name :: .punctuation ['('] :: rest =>
            if name == "UINT64_C".toList then
              match rest with
              | .number characters :: .punctuation [')'] :: after => do
                  let value ← wordChars? characters
                  postfix? fuel names (.word value) after
              | _ => none
            else if name == "UINT8_C".toList then
              match rest with
              | .number characters :: .punctuation [')'] :: after => do
                  let value ← byteChars? characters
                  postfix? fuel names (.byte value) after
              | _ => none
            else if name == "sizeof".toList then
              match cType? names rest with
              | some (type, .punctuation [')'] :: after) =>
                  postfix? fuel names (.sizeOf type) after
              | _ => do
                  let (operand, afterOperand) ← expression? fuel names 0 rest
                  match afterOperand with
                  | .punctuation [')'] :: after =>
                      postfix? fuel names (.sizeOfExpr operand) after
                  | _ => none
            else do
              let (arguments, after) ← arguments? fuel names rest
              postfix? fuel names (.call name arguments) after
        | .identifier name :: rest =>
            if name == "sizeof".toList then do
              let (operand, afterOperand) ← prefix? fuel names rest
              postfix? fuel names (.sizeOfExpr operand) afterOperand
            else
              let value := if name == "true".toList then CExpr.bool true
                else if name == "false".toList then .bool false
                else if name == "NULL".toList then .null else .identifier name
              postfix? fuel names value rest
        | .number characters :: rest =>
            match unsignedChars? characters with
            | some value => postfix? fuel names (.unsignedInteger value) rest
            | none => do
                let value ← decimalChars? characters
                postfix? fuel names (.decimal value) rest
        | _ => none

  def postfix? (fuel : Nat) (names : TypeNames) (base : CExpr)
      (tokens : List Token) : Option (CExpr × List Token) :=
    match tokens with
    | .punctuation ['+', '+'] :: rest =>
        match fuel with
        | 0 => none
        | fuel + 1 => postfix? fuel names (.postIncrement base) rest
    | .punctuation ['-', '-'] :: rest =>
        match fuel with
        | 0 => none
        | fuel + 1 => postfix? fuel names (.postDecrement base) rest
    | .punctuation ['.'] :: .identifier field :: rest =>
        match fuel with
        | 0 => none
        | fuel + 1 => postfix? fuel names (.field base field false) rest
    | .punctuation ['-', '>'] :: .identifier field :: rest =>
        match fuel with
        | 0 => none
        | fuel + 1 => postfix? fuel names (.field base field true) rest
    | .punctuation ['['] :: rest =>
        match fuel with
        | 0 => none
        | fuel + 1 => do
            let (index, afterIndex) ← expression? fuel names 0 rest
            match afterIndex with
            | .punctuation [']'] :: after => postfix? fuel names (.index base index) after
            | _ => none
    | _ => some (base, tokens)

  def arguments? (fuel : Nat) (names : TypeNames)
      (tokens : List Token) : Option (List CExpr × List Token) :=
    match tokens with
    | .punctuation [')'] :: rest => some ([], rest)
    | _ => match fuel with
      | 0 => none
      | fuel + 1 => do
          let (first, afterFirst) ← expression? fuel names 0 tokens
          match afterFirst with
          | .punctuation [')'] :: rest => some ([first], rest)
          | .punctuation [','] :: rest => do
              match rest with
              | .punctuation [')'] :: _ => none
              | _ => pure ()
              let (others, afterOthers) ← arguments? fuel names rest
              some (first :: others, afterOthers)
          | _ => none

  /-- Positional initializers are retained in source order. An empty list is
  outside C11; a final comma is legal. Layout, conversion and zero-filling
  obligations belong to typed execution rather than syntax recognition. -/
  def initializers? (fuel : Nat) (names : TypeNames)
      (tokens : List Token) : Option (List CExpr × List Token) :=
    match fuel with
    | 0 => none
    | fuel + 1 => do
        let (first, afterFirst) ← expression? fuel names 0 tokens
        match afterFirst with
        | .punctuation ['}'] :: after => some ([first], after)
        | .punctuation [','] :: .punctuation ['}'] :: after => some ([first], after)
        | .punctuation [','] :: rest => do
            let (others, afterOthers) ← initializers? fuel names rest
            some (first :: others, afterOthers)
        | _ => none
end

def completeExpression? (names : TypeNames) (tokens : List Token) : Option CExpr := do
  let (expression, rest) ← expression? (2 * tokens.length + 4) names 0 tokens
  if rest.isEmpty then some expression else none

def expressionText? (names : TypeNames) (characters : List Char) : Option CExpr := do
  let tokens ← (lex characters).toOption
  completeExpression? names tokens

private def exampleTypes : TypeNames := ["void".toList, "uint64_t".toList,
  "uint8_t".toList, "bool".toList, "Pair".toList]

theorem c_precedence_preserved : expressionText? exampleTypes "a + b * c".toList =
    some (.binary .add (.identifier ['a'])
      (.binary .mul (.identifier ['b']) (.identifier ['c']))) := by cbv

theorem c_left_associativity_preserved : expressionText? exampleTypes "a - b - c".toList =
    some (.binary .sub (.binary .sub (.identifier ['a']) (.identifier ['b']))
      (.identifier ['c'])) := by cbv

theorem value_record_lvalue_preserved : expressionText? exampleTypes
    "&(&local_result)->symbol".toList = some
      (.unary .address (.field (.unary .address (.identifier "local_result".toList))
        "symbol".toList true)) := by cbv

theorem explicit_byte_cast_preserved : expressionText? exampleTypes "(uint8_t)x".toList =
    some (.cast ⟨"uint8_t".toList, 0⟩ (.identifier ['x'])) := by cbv

theorem physical_array_data_selector_preserved : expressionText? exampleTypes
    "buffer.data[counter]".toList = some
      (.index (.field (.identifier "buffer".toList) "data".toList false)
        (.identifier "counter".toList)) := by cbv

theorem null_count_conditional_preserved : expressionText? exampleTypes
    "(p == NULL ? UINT64_C(0) : UINT64_C(1))".toList = some
      (.conditional (.binary .eq (.identifier ['p']) .null) (.word 0) (.word 1)) := by cbv

theorem extra_expression_tokens_refused : expressionText? exampleTypes "a b".toList = none :=
  by cbv

theorem missing_field_name_refused : expressionText? exampleTypes "a->".toList = none :=
  by cbv

theorem oversized_word_macro_refused : expressionText? exampleTypes
    "UINT64_C(18446744073709551616)".toList = none := by cbv

theorem trailing_call_argument_comma_refused : expressionText? exampleTypes
    "f(x,)".toList = none := by cbv

/-- The unsigned suffix remains explicit syntax. Its C integer type still
requires an ABI and range check; recognition does not widen the operand. -/
theorem unsigned_zero_keeps_integral_type : expressionText? exampleTypes "0u".toList =
    some (.unsignedInteger 0) := by cbv

theorem unsigned_nonzero_magnitude_retained :
    expressionText? exampleTypes "1u".toList = some (.unsignedInteger 1) := by cbv

theorem unsigned_octal_expression_retained :
    expressionText? exampleTypes "077U".toList = some (.unsignedInteger 63) := by cbv

theorem invalid_unsigned_octal_expression_refused :
    expressionText? exampleTypes "09u".toList = none := by cbv

theorem unsuffixed_octal_expression_not_misread :
    expressionText? exampleTypes "077".toList = none := by cbv

theorem word_macro_octal_not_misread :
    expressionText? exampleTypes "UINT64_C(077)".toList = none := by cbv

theorem byte_macro_octal_not_misread :
    expressionText? exampleTypes "UINT8_C(010)".toList = none := by cbv

theorem postfix_increment_is_not_prefix : expressionText? exampleTypes "i++".toList =
    some (.postIncrement (.identifier ['i'])) := by cbv

theorem postfix_increment_precedes_addition : expressionText? exampleTypes "i++ + j".toList =
    some (.binary .add (.postIncrement (.identifier ['i'])) (.identifier ['j'])) := by cbv

theorem prefix_decrement_retains_field_location : expressionText? exampleTypes
    "--store->lease_length".toList =
      some (.unary .decrement
        (.field (.identifier "store".toList) "lease_length".toList true)) := by cbv

theorem indexed_prefix_decrement_is_retained : expressionText? exampleTypes
    "store->leases[--store->lease_length]".toList =
      some (.index (.field (.identifier "store".toList) "leases".toList true)
        (.unary .decrement
          (.field (.identifier "store".toList) "lease_length".toList true))) := by cbv

theorem postfix_decrement_is_distinct : expressionText? exampleTypes "i--".toList =
    some (.postDecrement (.identifier ['i'])) := by cbv

theorem postfix_decrement_precedes_subtraction : expressionText? exampleTypes
    "i-- - j".toList =
      some (.binary .sub (.postDecrement (.identifier ['i'])) (.identifier ['j'])) := by cbv

theorem unary_minus_retains_signed_decimal :
    expressionText? exampleTypes "-1".toList = some (.unary .negate (.decimal 1)) := by cbv

theorem unary_minus_precedes_multiplication :
    expressionText? exampleTypes "-1 * 2u".toList =
      some (.binary .mul (.unary .negate (.decimal 1)) (.unsignedInteger 2)) := by cbv

theorem separated_minus_is_not_decrement :
    expressionText? exampleTypes "- -1".toList =
      some (.unary .negate (.unary .negate (.decimal 1))) := by cbv

theorem incomplete_unary_minus_refused :
    expressionText? exampleTypes "-".toList = none := by cbv

theorem incomplete_prefix_decrement_refused :
    expressionText? exampleTypes "--".toList = none := by cbv

theorem incomplete_index_decrement_refused :
    expressionText? exampleTypes "store->leases[--]".toList = none := by cbv

end Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
