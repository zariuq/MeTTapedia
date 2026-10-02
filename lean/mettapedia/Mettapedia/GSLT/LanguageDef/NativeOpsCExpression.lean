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
        | .punctuation ['('] :: rest =>
            match cType? names rest with
            | some (type, .punctuation [')'] :: afterType) =>
                match afterType with
                | .punctuation ['{'] :: .number ['0'] :: .punctuation ['}'] :: afterZero =>
                    postfix? fuel names (.zero type) afterZero
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
            else if name == "sizeof".toList then do
              let (type, afterType) ← cType? names rest
              match afterType with
              | .punctuation [')'] :: after => postfix? fuel names (.sizeOf type) after
              | _ => none
            else do
              let (arguments, after) ← arguments? fuel names rest
              postfix? fuel names (.call name arguments) after
        | .identifier name :: rest =>
            let value := if name == "true".toList then CExpr.bool true
              else if name == "false".toList then .bool false
              else if name == "NULL".toList then .null else .identifier name
            postfix? fuel names value rest
        | .number ['0', 'u'] :: rest | .number ['0', 'U'] :: rest =>
            postfix? fuel names (.cast ⟨"unsigned".toList, 0⟩ (.decimal 0)) rest
        | .number characters :: rest => do
            let value ← decimalChars? characters
            postfix? fuel names (.decimal value) rest
        | _ => none

  def postfix? (fuel : Nat) (names : TypeNames) (base : CExpr)
      (tokens : List Token) : Option (CExpr × List Token) :=
    match tokens with
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

/-- The unsigned suffix has its own integral type. It is not rewritten to
an arbitrary 64-bit arithmetic operand. The scalar return reader can check
the exact zero conversion against the function's declared result. -/
theorem unsigned_zero_keeps_integral_type : expressionText? exampleTypes "0u".toList =
    some (.cast ⟨"unsigned".toList, 0⟩ (.decimal 0)) := by cbv

theorem unsupported_unsigned_arithmetic_literal_refused :
    expressionText? exampleTypes "1u".toList = none := by cbv

end Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
