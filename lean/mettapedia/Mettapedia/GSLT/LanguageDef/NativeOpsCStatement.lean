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
          let (type, afterType) ← cType? names rest
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
                      | .punctuation [')'] :: afterIncrement => do
                          let (body, afterBody) ← block? fuel names afterIncrement
                          some (.forLoop type counter initial condition increment body, afterBody)
                      | _ => none
                  | _ => none
              | _ => none
          | _ => none
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

def parameters? (fuel : Nat) (names : TypeNames) (tokens : List Token) :
    Option (List CParameter × List Token) :=
  match tokens with
  | .punctuation [')'] :: rest => some ([], rest)
  | .identifier ['v', 'o', 'i', 'd'] :: .punctuation [')'] :: rest => some ([], rest)
  | _ => match fuel with
    | 0 => none
    | fuel + 1 => do
        let (type, afterType) ← cType? names tokens
        match afterType with
        | .identifier name :: .punctuation [')'] :: rest =>
            some ([⟨type, name⟩], rest)
        | .identifier name :: .punctuation [','] :: rest => do
            match rest with
            | .punctuation [')'] :: _ => none
            | .identifier ['v', 'o', 'i', 'd'] :: .punctuation [')'] :: _ => none
            | _ => pure ()
            let (others, afterOthers) ← parameters? fuel names rest
            some (⟨type, name⟩ :: others, afterOthers)
        | _ => none

def function? (fuel : Nat) (names : TypeNames) (tokens : List Token) :
    Option (CFunction × List Token) := do
  let (result, afterType) ← cType? names tokens
  match afterType with
  | .identifier name :: .punctuation ['('] :: rest => do
      let (parameters, afterParameters) ← parameters? fuel names rest
      let (body, afterBody) ← block? fuel names afterParameters
      some (⟨result, name, parameters, body⟩, afterBody)
  | _ => none

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

end Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
