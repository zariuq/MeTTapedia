import Mettapedia.GSLT.LanguageDef.NativeOpsCExpression

/-!
# Complete statement and function recognition for emitted C

Labels, scoped blocks, explicit initialization loops and switch breaks remain
target syntax. Recognition does not grant types or external-call authority.
Every successful complete entry consumes the entire supplied token list.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

def parenthesized? (fuel : Nat) (names : TypeNames) :
    List Token → Option (CExpr × List Token)
  | .punctuation ['('] :: rest => do
      let (condition, afterCondition) ← expression? fuel names 0 rest
      match afterCondition with
      | .punctuation [')'] :: after => some (condition, after)
      | _ => none
  | _ => none

def assignmentOrEffect? (fuel : Nat) (names : TypeNames)
    (tokens : List Token) : Option (CStatement × List Token) := do
  let (first, afterFirst) ← expression? fuel names 0 tokens
  match afterFirst with
  | .punctuation ['='] :: rest => do
      let (value, afterValue) ← expression? fuel names 0 rest
      match afterValue with
      | .punctuation [';'] :: after => some (.assign first value, after)
      | _ => none
  | .punctuation [';'] :: after => some (.effect first, after)
  | .punctuation symbol :: rest => do
      let operator ← compoundAssignmentOperator? symbol
      let (value, afterValue) ← expression? fuel names 0 rest
      match afterValue with
      | .punctuation [';'] :: after => some (.compoundAssign operator first value, after)
      | _ => none
  | _ => none

/-- The declaration-initialized loop header keeps each delimiter and the
remaining body tokens. It neither executes nor types the three expressions. -/
def forHeader? (fuel : Nat) (names : TypeNames) (tokens : List Token) :
    Option (CForHeader × List Token) := do
  let (type, afterType) ← cType? names tokens
  match afterType with
  | .identifier counter :: .punctuation ['='] :: afterCounter => do
      let (initial, afterInitial) ← expression? fuel names 0 afterCounter
      match afterInitial with
      | .punctuation [';'] :: afterInitial => do
          let (condition, afterCondition) ← expression? fuel names 0 afterInitial
          match afterCondition with
          | .punctuation [';'] :: afterCondition => do
              let (increment, afterIncrement) ← expression? fuel names 0 afterCondition
              match afterIncrement with
              | .punctuation [')'] :: afterIncrement =>
                  some (⟨type, counter, initial, condition, increment⟩, afterIncrement)
              | _ => none
          | _ => none
      | _ => none
  | _ => none

mutual
  def block? (fuel : Nat) (names : TypeNames) (tokens : List Token) :
      Option (List CStatement × List Token) :=
    match fuel with
    | 0 => none
    | fuel + 1 => match tokens with
      | .punctuation ['{'] :: rest => statements? fuel names rest
      | _ => none

  def statements? (fuel : Nat) (names : TypeNames)
      (tokens : List Token) : Option (List CStatement × List Token) :=
    match tokens with
    | .punctuation ['}'] :: after => some ([], after)
    | _ => match fuel with
      | 0 => none
      | fuel + 1 => do
          let (first, afterFirst) ← statement? fuel names tokens
          let (others, afterOthers) ← statements? fuel names afterFirst
          some (first :: others, afterOthers)

  def statement? (fuel : Nat) (names : TypeNames)
      (tokens : List Token) : Option (CStatement × List Token) :=
    match fuel with
    | 0 => none
    | fuel + 1 => match tokens with
      | .punctuation [';'] :: after => some (.empty, after)
      | .punctuation ['{'] :: _ => do
          let (body, after) ← block? fuel names tokens
          some (.block body, after)
      | .identifier ['i', 'f'] :: rest => do
          let (condition, afterCondition) ← parenthesized? fuel names rest
          let (whenTrue, afterTrue) ← branchBody? fuel names afterCondition
          match afterTrue with
          | .identifier ['e', 'l', 's', 'e'] :: rest => do
              let (whenFalse, afterFalse) ← branchBody? fuel names rest
              some (.branch condition whenTrue whenFalse, afterFalse)
          | _ => some (.branch condition whenTrue [], afterTrue)
      | .identifier ['f', 'o', 'r'] :: .punctuation ['('] :: rest => do
          let (header, afterHeader) ← forHeader? fuel names rest
          let (body, afterBody) ← block? fuel names afterHeader <|> (do
            let (body, after) ← statement? fuel names afterHeader
            some ([body], after))
          some (.forLoop header.type header.counter header.initial header.condition
            header.increment body, afterBody)
      | .identifier ['w', 'h', 'i', 'l', 'e'] :: rest => do
          let (condition, afterCondition) ← parenthesized? fuel names rest
          let (body, afterBody) ← block? fuel names afterCondition <|> (do
            let (body, after) ← statement? fuel names afterCondition
            some ([body], after))
          some (.whileLoop condition body, afterBody)
      | .identifier ['s', 'w', 'i', 't', 'c', 'h'] :: rest => do
          let (selector, afterSelector) ← parenthesized? fuel names rest
          match afterSelector with
          | .punctuation ['{'] :: afterOpen => do
              let ((cases, otherwise), after) ← switchCases? fuel names afterOpen
              some (.switch selector cases otherwise, after)
          | _ => none
      | .identifier ['g', 'o', 't', 'o'] :: .identifier label ::
          .punctuation [';'] :: after => some (.jump label, after)
      | .identifier ['b', 'r', 'e', 'a', 'k'] :: .punctuation [';'] :: after =>
          some (.break, after)
      | .identifier ['r', 'e', 't', 'u', 'r', 'n'] :: .punctuation [';'] :: after =>
          some (.return none, after)
      | .identifier ['r', 'e', 't', 'u', 'r', 'n'] :: rest => do
          let (value, afterValue) ← expression? fuel names 0 rest
          match afterValue with
          | .punctuation [';'] :: after => some (.return (some value), after)
          | _ => none
      | .identifier label :: .punctuation [':'] :: after => some (.label label, after)
      | .identifier ['c', 'o', 'n', 's', 't'] :: rest => do
          let (type, afterType) ← cType? names rest
          if type.pointers != 1 then none else
          match afterType with
          | .identifier name :: .punctuation ['='] :: rest => do
              let (value, afterValue) ← expression? fuel names 0 rest
              match afterValue with
              | .punctuation [';'] :: after => some (.declarePointeeConst type name value, after)
              | _ => none
          | _ => none
      | _ => match cType? names tokens with
        | some (type, .identifier name :: .punctuation ['='] :: rest) => do
            let (value, afterValue) ← expression? fuel names 0 rest
            match afterValue with
            | .punctuation [';'] :: after => some (.declare type name value, after)
            | _ => none
        | some _ => none
        | none => assignmentOrEffect? fuel names tokens

  /-- An ordinary C conditional arm may be a block or one statement.
  Parsing the complete nested statement attaches an else to its nearest if. -/
  def branchBody? (fuel : Nat) (names : TypeNames) (tokens : List Token) :
      Option (List CStatement × List Token) :=
    match fuel with
    | 0 => none
    | fuel + 1 => match tokens with
      | .punctuation ['{'] :: _ => block? fuel names tokens
      | _ => do
          let (body, after) ← statement? fuel names tokens
          some ([body], after)

  def switchCases? (fuel : Nat) (names : TypeNames) (tokens : List Token) :
      Option ((List (CExpr × List CStatement) × List CStatement) × List Token) :=
    match fuel with
    | 0 => none
    | fuel + 1 => match tokens with
      | .identifier ['c', 'a', 's', 'e'] :: rest => do
          let (value, afterValue) ← expression? fuel names 0 rest
          match afterValue with
          | .punctuation [':'] :: afterColon => do
              let (body, afterBody) ← block? fuel names afterColon
              let ((others, otherwise), after) ← switchCases? fuel names afterBody
              some (((value, body) :: others, otherwise), after)
          | _ => none
      | .identifier ['d', 'e', 'f', 'a', 'u', 'l', 't'] :: .punctuation [':'] :: rest => do
          let (body, afterBody) ← block? fuel names rest
          match afterBody with
          | .punctuation ['}'] :: after => some (([], body), after)
          | _ => none
      | _ => none
end

/-- A block consumes exactly the supplied closing-delimiter continuation. -/
theorem block_of_statements (fuel : Nat) (names : TypeNames)
    (tokens after : List Token) (body : List CStatement)
    (parsed : statements? fuel names tokens = some (body, after)) :
    block? (fuel + 1) names (.punctuation ['{'] :: tokens) = some (body, after) := by
  exact parsed

/-- Identifier-led statements can be checked separately from their complete
remaining block. In particular, the leading token is not the block closer. -/
theorem statements_cons_identifier (fuel : Nat) (names : TypeNames) (name : List Char)
    (tokens afterFirst after : List Token) (first : CStatement) (others : List CStatement)
    (firstParsed : statement? fuel names (.identifier name :: tokens) =
      some (first, afterFirst))
    (remainingParsed : statements? fuel names afterFirst = some (others, after)) :
    statements? (fuel + 1) names (.identifier name :: tokens) =
      some (first :: others, after) := by
  change (do
    let (first, afterFirst) ← statement? fuel names (.identifier name :: tokens)
    let (others, afterOthers) ← statements? fuel names afterFirst
    some (first :: others, afterOthers)) = _
  rw [firstParsed]
  dsimp only [bind, Option.bind]
  rw [remainingParsed]

/-- A separately checked header composes with the entire loop block. -/
theorem for_statement_of_parts (fuel : Nat) (names : TypeNames) (header : CForHeader)
    (body : List CStatement) (start bodyTokens after : List Token)
    (headerParsed : forHeader? fuel names start = some (header, bodyTokens))
    (bodyParsed : block? fuel names bodyTokens = some (body, after)) :
    statement? (fuel + 1) names (.identifier ['f', 'o', 'r'] :: .punctuation ['('] :: start) =
      some (.forLoop header.type header.counter header.initial header.condition
        header.increment body, after) := by
  change (do
    let (header, bodyTokens) ← forHeader? fuel names start
    let (body, afterBody) ← block? fuel names bodyTokens <|> (do
      let (body, after) ← statement? fuel names bodyTokens
      some ([body], after))
    some (CStatement.forLoop header.type header.counter header.initial header.condition
      header.increment body, afterBody)) = _
  rw [headerParsed]
  dsimp only [bind, Option.bind]
  rw [bodyParsed]
  rfl

/-- The delimiter protocol is shared by ordinary and qualified prototypes. -/
def parametersUsing? {ParameterSyntax : Type}
    (parameter : List Token → Option (ParameterSyntax × List Token))
    (fuel : Nat) (tokens : List Token) :
    Option (List ParameterSyntax × List Token) :=
  match tokens with
  | .punctuation [')'] :: rest => some ([], rest)
  | .identifier ['v', 'o', 'i', 'd'] :: .punctuation [')'] :: rest => some ([], rest)
  | _ => match fuel with
    | 0 => none
    | fuel + 1 => do
        let (first, afterFirst) ← parameter tokens
        match afterFirst with
        | .punctuation [')'] :: rest => some ([first], rest)
        | .punctuation [','] :: rest => do
            match rest with
            | .punctuation [')'] :: _ => none
            | .identifier ['v', 'o', 'i', 'd'] :: .punctuation [')'] :: _ => none
            | _ => pure ()
            let (others, afterOthers) ← parametersUsing? parameter fuel rest
            some (first :: others, afterOthers)
        | _ => none

def parameter? (names : TypeNames) (tokens : List Token) :
    Option (CParameter × List Token) := do
  let (type, afterType) ← cType? names tokens
  match afterType with
  | .identifier name :: rest => some (⟨type, name⟩, rest)
  | _ => none

def parameters? (fuel : Nat) (names : TypeNames) (tokens : List Token) :
    Option (List CParameter × List Token) :=
  parametersUsing? (parameter? names) fuel tokens

/-- Leading pointee const is recognized without discarding its qualification.
Other placements and qualifiers remain outside this admission profile. -/
def qualifiedParameter? (names : TypeNames) (tokens : List Token) :
    Option (CQualifiedParameter × List Token) := do
  match tokens with
  | .identifier ['c', 'o', 'n', 's', 't'] :: rest =>
      let (parameter, after) ← parameter? names rest
      if parameter.type.pointers == 1 then some (⟨parameter, true⟩, after) else none
  | _ =>
      let (parameter, after) ← parameter? names tokens
      some (⟨parameter, false⟩, after)

def functionUsing? {ParameterSyntax : Type}
    (parameter : List Token → Option (ParameterSyntax × List Token))
    (fuel : Nat) (names : TypeNames) (tokens : List Token) :
    Option (CFunctionSyntax ParameterSyntax × List Token) := do
  let (result, afterType) ← cType? names tokens
  match afterType with
  | .identifier name :: .punctuation ['('] :: rest => do
      let (parameters, afterParameters) ← parametersUsing? parameter fuel rest
      let (body, afterBody) ← block? fuel names afterParameters
      some (⟨result, name, parameters, body⟩, afterBody)
  | _ => none

def function? (fuel : Nat) (names : TypeNames) (tokens : List Token) :
    Option (CFunction × List Token) :=
  functionUsing? (parameter? names) fuel names tokens

def qualifiedFunction? (fuel : Nat) (names : TypeNames) (tokens : List Token) :
    Option (CQualifiedFunction × List Token) :=
  functionUsing? (qualifiedParameter? names) fuel names tokens

/-- Function recognition composes its type, parameter and block parsers without
discarding their returned continuations. -/
theorem function_using_of_parts {ParameterSyntax : Type}
    (parameter : List Token → Option (ParameterSyntax × List Token))
    (fuel : Nat) (names : TypeNames) (type : CType) (name : List Char)
    (start parameterTokens bodyTokens after : List Token)
    (parameters : List ParameterSyntax) (body : List CStatement)
    (typeParsed : cType? names start =
      some (type, .identifier name :: .punctuation ['('] :: parameterTokens))
    (parametersParsed : parametersUsing? parameter fuel parameterTokens =
      some (parameters, bodyTokens))
    (bodyParsed : block? fuel names bodyTokens = some (body, after)) :
    functionUsing? parameter fuel names start = some (⟨type, name, parameters, body⟩, after) := by
  unfold functionUsing?
  rw [typeParsed]
  change (do
    let (parameters, bodyTokens) ← parametersUsing? parameter fuel parameterTokens
    let (body, afterBody) ← block? fuel names bodyTokens
    some ((⟨type, name, parameters, body⟩ : CFunctionSyntax ParameterSyntax), afterBody)) = _
  rw [parametersParsed]
  dsimp only [bind, Option.bind]
  rw [bodyParsed]

/-- These storage/function specifiers do not change the body of one supplied
invocation. This reader does not establish linkage or whole-program identity. -/
def ordinaryFunctionTokens : List Token → List Token
  | .identifier ['s', 't', 'a', 't', 'i', 'c'] ::
      .identifier ['i', 'n', 'l', 'i', 'n', 'e'] :: rest => rest
  | .identifier ['i', 'n', 'l', 'i', 'n', 'e'] ::
      .identifier ['s', 't', 'a', 't', 'i', 'c'] :: rest => rest
  | .identifier ['s', 't', 'a', 't', 'i', 'c'] :: rest => rest
  | .identifier ['i', 'n', 'l', 'i', 'n', 'e'] :: rest => rest
  | tokens => tokens

/-- Complete text recognition is shared by the ordinary and qualified
profiles. No operational or external-call authority is granted here. -/
def functionTextUsing? {ParameterSyntax : Type}
    (parameter : List Token → Option (ParameterSyntax × List Token))
    (names : TypeNames) (characters : List Char) : Option (CFunctionSyntax ParameterSyntax) := do
  let tokens ← (lex characters).toOption
  let (function, after) ← functionUsing? parameter (2 * tokens.length + 4) names
    (ordinaryFunctionTokens tokens)
  if !after.isEmpty then none else some function

def ordinaryFunctionText? (names : TypeNames) (characters : List Char) : Option CFunction :=
  functionTextUsing? (parameter? names) names characters

def qualifiedFunctionText? (names : TypeNames) (characters : List Char) : Option CQualifiedFunction :=
  functionTextUsing? (qualifiedParameter? names) names characters

theorem function_text_using_of_parts {ParameterSyntax : Type}
    (parameter : List Token → Option (ParameterSyntax × List Token))
    (names : TypeNames) (characters : List Char) (tokens : List Token)
    (function : CFunctionSyntax ParameterSyntax)
    (lexed : lex characters = .ok tokens)
    (parsed : functionUsing? parameter (2 * tokens.length + 4) names
      (ordinaryFunctionTokens tokens) = some (function, [])) :
    functionTextUsing? parameter names characters = some function := by
  unfold functionTextUsing?
  rw [lexed]
  dsimp only [Except.toOption, bind, Option.bind]
  rw [parsed]
  rfl

def functions? (fuel : Nat) (names : TypeNames) (tokens : List Token) :
    Option (List CFunction) :=
  match tokens with
  | [] => some []
  | _ => match fuel with
    | 0 => none
    | fuel + 1 => do
        let (first, afterFirst) ← function? fuel names tokens
        let others ← functions? fuel names afterFirst
        some (first :: others)

def completeUnit? (names : TypeNames) (tokens : List Token) : Option CUnit :=
  match tokens with
  | .punctuation ['#'] :: .identifier ['i', 'n', 'c', 'l', 'u', 'd', 'e'] ::
      .quoted header :: rest => do
      let functions ← functions? (2 * tokens.length + 4) names rest
      some ⟨header, functions⟩
  | _ => none

def unitText? (names : TypeNames) (characters : List Char) : Option CUnit := do
  let tokens ← (lex characters).toOption
  completeUnit? names tokens

def blockText? (names : TypeNames) (characters : List Char) : Option (List CStatement) := do
  let tokens ← (lex characters).toOption
  let (body, after) ← block? (2 * tokens.length + 4) names tokens
  if after.isEmpty then some body else none

/-- Whole block admission separates the actual lexer and complete parser. -/
theorem block_text_of_parts (names : TypeNames) (characters : List Char)
    (tokens : List Token) (body : List CStatement)
    (lexed : lex characters = .ok tokens)
    (parsed : block? (2 * tokens.length + 4) names tokens = some (body, [])) :
    blockText? names characters = some body := by
  unfold blockText?
  rw [lexed]
  dsimp only [Except.toOption, bind, Option.bind]
  rw [parsed]
  rfl

theorem unit_text_of_parts (names : TypeNames) (characters : List Char)
    (tokens : List Token) (unit : CUnit)
    (lexed : lex characters = .ok tokens)
    (parsed : completeUnit? names tokens = some unit) :
    unitText? names characters = some unit := by
  unfold unitText?
  rw [lexed]
  exact parsed

private def exampleTypes : TypeNames := ["void".toList, "uint64_t".toList,
  "uint8_t".toList, "bool".toList, "Pair".toList]

private def labelTokens : List Token := [
 .punctuation ['{'],
 .identifier ['b', 'e', 'g', 'i', 'n'],
 .punctuation [':'],
 .punctuation [';'],
 .punctuation ['{'],
 .identifier ['i', 'f'],
 .punctuation ['('],
 .punctuation ['!'],
 .identifier ['k', 'e', 'e', 'p'],
 .punctuation [')'],
 .punctuation ['{'],
 .identifier ['g', 'o', 't', 'o'],
 .identifier ['e', 'n', 'd'],
 .punctuation [';'],
 .punctuation ['}'],
 .identifier ['g', 'o', 't', 'o'],
 .identifier ['b', 'e', 'g', 'i', 'n'],
 .punctuation [';'],
 .punctuation ['}'],
 .identifier ['e', 'n', 'd'],
 .punctuation [':'],
 .punctuation [';'],
 .punctuation ['}']]

private def switchTokens : List Token := [
 .punctuation ['{'],
 .identifier ['s', 'w', 'i', 't', 'c', 'h'],
 .punctuation ['('],
 .identifier ['x'],
 .punctuation [')'],
 .punctuation ['{'],
 .identifier ['c', 'a', 's', 'e'],
 .identifier ['U', 'I', 'N', 'T', '6', '4', '_', 'C'],
 .punctuation ['('],
 .number ['1'],
 .punctuation [')'],
 .punctuation [':'],
 .punctuation ['{'],
 .identifier ['g', 'o', 't', 'o'],
 .identifier ['e', 'n', 'd'],
 .punctuation [';'],
 .identifier ['b', 'r', 'e', 'a', 'k'],
 .punctuation [';'],
 .punctuation ['}'],
 .identifier ['d', 'e', 'f', 'a', 'u', 'l', 't'],
 .punctuation [':'],
 .punctuation ['{'],
 .identifier ['b', 'r', 'e', 'a', 'k'],
 .punctuation [';'],
 .punctuation ['}'],
 .punctuation ['}'],
 .punctuation ['}']]

private def functionTokens : List Token := [
 .punctuation ['#'],
 .identifier ['i', 'n', 'c', 'l', 'u', 'd', 'e'],
 .quoted ['g', 'u', 'e', 's', 't', '.', 'h'],
 .identifier ['u', 'i', 'n', 't', '6', '4', '_', 't'],
 .identifier ['f'],
 .punctuation ['('],
 .identifier ['u', 'i', 'n', 't', '6', '4', '_', 't'],
 .identifier ['l', 'o', 'c', 'a', 'l', '_', 'x'],
 .punctuation [')'],
 .punctuation ['{'],
 .identifier ['r', 'e', 't', 'u', 'r', 'n'],
 .identifier ['l', 'o', 'c', 'a', 'l', '_', 'x'],
 .punctuation [';'],
 .punctuation ['}']]

theorem source_loop_labels_remain_jumps : blockText? exampleTypes
    "{ begin: ; { if (!keep) { goto end; } goto begin; } end: ; }".toList =
    some [.label "begin".toList, .empty,
      .block [.branch (.unary .not (.identifier "keep".toList))
        [.jump "end".toList] [], .jump "begin".toList], .label "end".toList, .empty] := by
  exact block_text_of_parts exampleTypes "{ begin: ; { if (!keep) { goto end; } goto begin; } end: ; }".toList labelTokens _
    (by decide +kernel) (by rfl)

theorem switch_break_remains_distinct : blockText? exampleTypes
    "{ switch (x) { case UINT64_C(1): { goto end; break; } default: { break; } } }".toList =
    some [.switch (.identifier ['x']) [(.word 1, [.jump "end".toList, .break])]
      [.break]] := by
  exact block_text_of_parts exampleTypes "{ switch (x) { case UINT64_C(1): { goto end; break; } default: { break; } } }".toList switchTokens _
    (by decide +kernel) (by rfl)

theorem complete_function_body_retained : unitText? exampleTypes
    "#include \"guest.h\" uint64_t f(uint64_t local_x) { return local_x; }".toList =
    some ⟨"guest.h".toList,
      [⟨⟨"uint64_t".toList, 0⟩, ['f'], [⟨⟨"uint64_t".toList, 0⟩, "local_x".toList⟩],
        [.return (some (.identifier "local_x".toList))]⟩]⟩ := by
  exact unit_text_of_parts exampleTypes "#include \"guest.h\" uint64_t f(uint64_t local_x) { return local_x; }".toList functionTokens _
    (by decide +kernel) (by rfl)

theorem missing_statement_separator_refused :
    blockText? exampleTypes "{ uint64_t x = 0 return x; }".toList = none := by decide +kernel

theorem repeated_default_refused : blockText? exampleTypes
    "{ switch (x) { default: { break; } default: { break; } } }".toList = none := by decide +kernel

theorem extra_artifact_tokens_refused : unitText? exampleTypes
    "#include \"guest.h\" void f(void) { return; } wrong".toList = none := by decide +kernel

theorem unknown_storage_type_refused : unitText? exampleTypes
    "#include \"guest.h\" Unadmitted f(void) { return; }".toList = none := by decide +kernel

theorem trailing_parameter_comma_refused : unitText? exampleTypes
    "#include \"guest.h\" void f(uint64_t x,) { return; }".toList = none := by decide +kernel

private def nestedIfTokens : List Token :=
  [.punctuation ['{'], .identifier "if".toList, .punctuation ['('],
   .identifier ['x'], .punctuation [')'], .identifier "if".toList,
   .punctuation ['('], .identifier ['y'], .punctuation [')'],
   .identifier "return".toList, .identifier "true".toList, .punctuation [';'],
   .identifier "else".toList, .identifier "return".toList,
   .identifier "false".toList, .punctuation [';'], .punctuation ['}']]

/-- The ordinary C selection policy associates an unbraced else with the
nearest unmatched if, retaining both of that inner branch's arms. -/
theorem unbraced_else_belongs_to_nearest_if : blockText? exampleTypes
    "{ if (x) if (y) return true; else return false; }".toList =
    some [.branch (.identifier ['x'])
      [.branch (.identifier ['y']) [.return (some (.bool true))]
        [.return (some (.bool false))]] []] := by
  exact block_text_of_parts exampleTypes
    "{ if (x) if (y) return true; else return false; }".toList nestedIfTokens _
    (by decide +kernel) (by rfl)

theorem unbraced_missing_separator_refused : blockText? exampleTypes
    "{ if (x) return true else return false; }".toList = none := by decide +kernel

theorem qualified_pointee_const_retained : qualifiedParameter? exampleTypes
    [.identifier "const".toList, .identifier "Pair".toList, .punctuation ['*'],
     .identifier "p".toList, .punctuation [')']] =
      some (⟨⟨⟨"Pair".toList, 1⟩, "p".toList⟩, true⟩, [.punctuation [')']]) := by rfl

/-- Pointer const has a different location from pointee const. It is not
silently read as the supported leading qualifier. -/
theorem qualified_pointer_const_not_pointee_const : qualifiedFunction? 20 exampleTypes
    [.identifier "bool".toList, .identifier "f".toList, .punctuation ['('],
     .identifier "Pair".toList, .punctuation ['*'], .identifier "const".toList,
     .identifier "p".toList, .punctuation [')'], .punctuation ['{'],
     .identifier "return".toList, .identifier "true".toList, .punctuation [';'],
     .punctuation ['}']] = none := by rfl

theorem qualified_deeper_const_pointer_refused : qualifiedParameter? exampleTypes
    [.identifier "const".toList, .identifier "Pair".toList,
     .punctuation ['*'], .punctuation ['*'], .identifier "p".toList] = none := by rfl

theorem qualified_volatile_refused : qualifiedParameter? exampleTypes
    [.identifier "volatile".toList, .identifier "Pair".toList,
     .punctuation ['*'], .identifier "p".toList] = none := by rfl

private def localConstTokens : List Token :=
  [.punctuation ['{'], .identifier "const".toList, .identifier "Pair".toList,
   .punctuation ['*'], .identifier ['p'], .punctuation ['='], .punctuation ['&'],
   .identifier "rows".toList, .punctuation ['['], .identifier ['i'],
   .punctuation [']'], .punctuation [';'], .punctuation ['}']]

theorem local_pointee_const_retained : blockText? exampleTypes
    "{ const Pair *p = &rows[i]; }".toList = some
      [.declarePointeeConst ⟨"Pair".toList, 1⟩ ['p']
        (.unary .address (.index (.identifier "rows".toList) (.identifier ['i'])))] := by
  exact block_text_of_parts exampleTypes "{ const Pair *p = &rows[i]; }".toList
    localConstTokens _ (by decide +kernel) (by rfl)

theorem local_pointer_const_not_pointee_const : blockText? exampleTypes
    "{ Pair * const p = &rows[i]; }".toList = none := by decide +kernel

theorem local_deeper_const_pointer_refused : blockText? exampleTypes
    "{ const Pair **p = &rows[i]; }".toList = none := by decide +kernel

end Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
