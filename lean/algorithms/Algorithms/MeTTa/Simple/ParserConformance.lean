import Algorithms.MeTTa.Simple.Parser

namespace Algorithms.MeTTa.Simple.ParserConformance

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaSyntax
open Algorithms.MeTTa.Simple.Parser

private def sym (s : String) : Pattern := .apply s []
private def app (f : String) (args : List Pattern) : Pattern := .apply f args

private def parseLineOk? (spec : SyntaxSpec) (line : String) (expected : Stmt) : Bool :=
  match parseLineWith spec line with
  | .ok stmt => decide (stmt = expected)
  | .error _ => false

private def parseProgramOk? (spec : SyntaxSpec) (text : String)
    (expected : List (Nat × Stmt)) : Bool :=
  match parseProgramWith spec text with
  | .ok forms => decide (forms = expected)
  | .error _ => false

private def parseLineErr? (spec : SyntaxSpec) (line : String) : Bool :=
  match parseLineWith spec line with
  | .ok _ => false
  | .error _ => true

private def parseProgramErr? (spec : SyntaxSpec) (text : String) : Bool :=
  match parseProgramWith spec text with
  | .ok _ => false
  | .error _ => true

private def parseLineRoundTripOk? (spec : SyntaxSpec) (line : String) : Bool :=
  match parseLineWith spec line with
  | .error _ => false
  | .ok stmt =>
      let pretty := renderCommandWith spec stmt
      match parseLineWith spec pretty with
      | .ok stmt' => decide (stmt' = stmt)
      | .error _ => false

private def heBracketSyntax : SyntaxSpec :=
  { he with
      lexer := { he.lexer with sexprOpen := '[', sexprClose := ']' } }

private def hashCommentSyntax : SyntaxSpec :=
  { he with
      lexer := { he.lexer with lineCommentStart := some "#" } }

private def qPrefixSyntax : SyntaxSpec :=
  { petta with
      evalPrefix := { petta.evalPrefix with evalPrefixToken := "?" } }

private def qPrefixHashCommentSyntax : SyntaxSpec :=
  { qPrefixSyntax with
      lexer := { qPrefixSyntax.lexer with lineCommentStart := some "#" } }

private def customLoweringHeadsSyntax : SyntaxSpec :=
  { he with loweringHeads := { relationFactHead := "rel!", builtinFactHead := "bi!" } }

private def aliasCommandSyntax : SyntaxSpec :=
  { he with
      headAliases :=
        [ { alias := "rewrite!", canonical := "=" }
        , { alias := "typ!", canonical := ":" }
        ] }

private def strictDispatchSyntax : SyntaxSpec :=
  { he with dispatchPolicy :=
      { fallbackUnknownHeadToFact := false
        fallbackArityMismatchToFact := false
        fallbackUnsupportedCommandToFact := false } }

private def strictAliasCommandSyntax : SyntaxSpec :=
  { aliasCommandSyntax with dispatchPolicy := strictDispatchSyntax.dispatchPolicy }

def checkHeBangPrefixedSymbolFact : Bool :=
  parseLineOk? he "!name" (.fact (sym "!name"))

def checkPeTTaBangPrefixedSymbolQuery : Bool :=
  parseLineOk? petta "!name" (.eval (sym "name"))

def checkHeCommentLineEmpty : Bool :=
  parseLineOk? he "; just a comment" .empty

def checkHeEvalPrefixSpaceForm : Bool :=
  parseLineOk? he "! (foo)" (.eval (app "foo" []))

def checkHeEvalPrefixNewlineForm : Bool :=
  parseProgramOk? he "!\n(foo)\n" [(1, .eval (app "foo" []))]

def checkHeEvalPrefixNewlineCommentForm : Bool :=
  parseProgramOk? he "!\n; keep comment as delimiter\n(foo)\n"
    [(1, .eval (app "foo" []))]

def checkHeStatementTrailingComment : Bool :=
  parseLineOk? he "(= (f a) b) ; trailing comment"
    (.defineEq (app "f" [sym "a"]) (sym "b"))

def checkPeTTaSetFuelIsPlainFact : Bool :=
  parseLineOk? petta "(set-fuel 7)" (.fact (app "set-fuel" [sym "7"]))

def checkHeSetFuelFallsBackToFact : Bool :=
  parseLineOk? he "(set-fuel 7)" (.fact (app "set-fuel" [sym "7"]))

def checkHeDefineTypeForm : Bool :=
  parseLineOk? he "(: foo Bar)" (.defineType (sym "foo") (sym "Bar"))

def checkPeTTaDefineTypeForm : Bool :=
  parseLineOk? petta "(: foo Bar)" (.defineType (sym "foo") (sym "Bar"))

def checkProgramMixedHe : Bool :=
  parseProgramOk? he ";\n(= (f a) b)\n!(f a)\n"
    [ (2, .defineEq (app "f" [sym "a"]) (sym "b"))
    , (3, .eval (app "f" [sym "a"]))
    ]

def checkProgramMixedPeTTa : Bool :=
  parseProgramOk? petta "(set-fuel 3)\n!(set-fuel 3)\n"
    [ (1, .fact (app "set-fuel" [sym "3"]))
    , (2, .eval (app "set-fuel" [sym "3"]))
    ]

def checkCustomBracketDelimiters : Bool :=
  parseLineOk? heBracketSyntax "![foo]" (.eval (app "foo" []))

def checkCustomCommentPrefix : Bool :=
  parseLineOk? hashCommentSyntax "# hash comment" .empty

def checkCustomEvalPrefix : Bool :=
  parseLineOk? qPrefixSyntax "?(foo)" (.eval (app "foo" []))

def checkPeTTaEvalPrefixNewlineCommentForm : Bool :=
  parseProgramOk? petta "!\n; inline comment\n(foo)\n"
    [(1, .eval (app "foo" []))]

def checkCustomEvalPrefixNewlineForm : Bool :=
  parseProgramOk? qPrefixSyntax "?\n(foo)\n"
    [(1, .eval (app "foo" []))]

def checkHeEvalPrefixMultilineCommentBlock : Bool :=
  parseProgramOk? he "!\n; c1\n; c2\n(foo)\n"
    [(1, .eval (app "foo" []))]

def checkCustomEvalPrefixNewlineCommentForm : Bool :=
  parseProgramOk? qPrefixHashCommentSyntax "?\n# inline\n(foo)\n"
    [(1, .eval (app "foo" []))]

def checkHeDefineEqMissingArgFallsBackFact : Bool :=
  parseLineOk? he "(= (f a))" (.fact (app "=" [app "f" [sym "a"]]))

def checkHeDefineTypeExtraArgFallsBackFact : Bool :=
  parseLineOk? he "(: foo Bar Baz)" (.fact (app ":" [sym "foo", sym "Bar", sym "Baz"]))

def checkPeTTaDefineEqExtraArgFallsBackFact : Bool :=
  parseLineOk? petta "(= (f a) b c)"
    (.fact (app "=" [app "f" [sym "a"], sym "b", sym "c"]))

def checkPeTTaDefineTypeMissingArgFallsBackFact : Bool :=
  parseLineOk? petta "(: foo)" (.fact (app ":" [sym "foo"]))

def checkPeTTaInSpaceIsPlainFact : Bool :=
  parseLineOk? petta "(in-space &tmp (match foo foo))"
    (.fact (app "in-space" [sym "&tmp", app "match" [sym "foo", sym "foo"]]))

def checkPeTTaDeclareMemoizedIsPlainFact : Bool :=
  parseLineOk? petta "(declare-memoized! fib)"
    (.fact (app "declare-memoized!" [sym "fib"]))

def checkDefaultRelationLowering : Bool :=
  parseLineOk? he "(relation! edge tim tom)"
    (.relationFact "edge" [sym "tim", sym "tom"])

def checkDefaultBuiltinLowering : Bool :=
  parseLineOk? he "(builtin! eq tim tom)"
    (.builtinFact "eq" [sym "tim", sym "tom"])

def checkCustomRelationLoweringHead : Bool :=
  parseLineOk? customLoweringHeadsSyntax "(rel! edge tim tom)"
    (.relationFact "edge" [sym "tim", sym "tom"])

def checkCustomBuiltinLoweringHead : Bool :=
  parseLineOk? customLoweringHeadsSyntax "(bi! eq tim tom)"
    (.builtinFact "eq" [sym "tim", sym "tom"])

def checkAliasDefineEqHead : Bool :=
  parseLineOk? aliasCommandSyntax "(rewrite! (f a) b)"
    (.defineEq (app "f" [sym "a"]) (sym "b"))

def checkAliasDefineTypeHead : Bool :=
  parseLineOk? aliasCommandSyntax "(typ! foo Bar)"
    (.defineType (sym "foo") (sym "Bar"))

def checkAliasRoundTripPretty : Bool :=
  parseLineRoundTripOk? aliasCommandSyntax "(rewrite! (f $x) (g $x))"

def checkAliasPrettyDoesNotRewriteFactSymbols : Bool :=
  parseLineRoundTripOk? aliasCommandSyntax "(foo =)"

def checkAliasMultilineProgram : Bool :=
  parseProgramOk? aliasCommandSyntax "(rewrite! (f a) b)\n!(f a)\n"
    [ (1, .defineEq (app "f" [sym "a"]) (sym "b"))
    , (2, .eval (app "f" [sym "a"]))
    ]

def checkAliasArityMismatchFallsBackFact : Bool :=
  parseLineOk? aliasCommandSyntax "(rewrite! (f a))"
    (.fact (app "rewrite!" [app "f" [sym "a"]]))

def checkStrictAliasArityMismatchError : Bool :=
  parseLineErr? strictAliasCommandSyntax "(rewrite! (f a))"

def checkStrictUnknownHeadError : Bool :=
  parseLineErr? strictDispatchSyntax "(unknown-head foo)"

def checkStrictArityMismatchError : Bool :=
  parseLineErr? strictDispatchSyntax "(= (f a))"

def checkHeImportHeadNowPlainFact : Bool :=
  parseLineOk? he "(import! &self lib)"
    (.fact (app "import!" [sym "&self", sym "lib"]))

def checkPeTTaAddAtomHeadNowPlainFact : Bool :=
  parseLineOk? petta "(add-atom! &self (friend a b))"
    (.fact (app "add-atom!" [sym "&self", app "friend" [sym "a", sym "b"]]))

def checkHeDocFunctionExpression : Bool :=
  parseLineOk? he "(= (if True $then $else) $then)"
    (.defineEq (app "if" [sym "True", .fvar "then", .fvar "else"]) (.fvar "then"))

def checkHeDocTypeAssignment : Bool :=
  parseLineOk? he "(: if (-> Bool Atom Atom $t))"
    (.defineType (sym "if") (app "->" [sym "Bool", sym "Atom", sym "Atom", .fvar "t"]))

def checkPeTTaExampleConjMatch : Bool :=
  parseLineOk? petta
    "!(match &self (, (friend $a $b) (friend $b $c)) (transitive $a $b $c))"
    (.eval (app "match"
      [sym "&self"
      , app "," [app "friend" [.fvar "a", .fvar "b"], app "friend" [.fvar "b", .fvar "c"]]
      , app "transitive" [.fvar "a", .fvar "b", .fvar "c"]]))

def checkBangOnlyLineIsError : Bool :=
  parseLineErr? he "!"

def checkMissingCloseParenProgramError : Bool :=
  parseProgramErr? he "!(foo\n"

def checkUnexpectedCloseParenProgramError : Bool :=
  parseProgramErr? petta ")\n"

def allChecks : List (String × Bool) :=
  [ ("heBangPrefixedSymbolFact", checkHeBangPrefixedSymbolFact)
  , ("pettaBangPrefixedSymbolQuery", checkPeTTaBangPrefixedSymbolQuery)
  , ("heCommentLineEmpty", checkHeCommentLineEmpty)
  , ("heEvalPrefixSpaceForm", checkHeEvalPrefixSpaceForm)
  , ("heEvalPrefixNewlineForm", checkHeEvalPrefixNewlineForm)
  , ("heEvalPrefixNewlineCommentForm", checkHeEvalPrefixNewlineCommentForm)
  , ("heStatementTrailingComment", checkHeStatementTrailingComment)
  , ("pettaSetFuelIsPlainFact", checkPeTTaSetFuelIsPlainFact)
  , ("heSetFuelFallsBackToFact", checkHeSetFuelFallsBackToFact)
  , ("heDefineTypeForm", checkHeDefineTypeForm)
  , ("pettaDefineTypeForm", checkPeTTaDefineTypeForm)
  , ("programMixedHe", checkProgramMixedHe)
  , ("programMixedPeTTa", checkProgramMixedPeTTa)
  , ("customBracketDelimiters", checkCustomBracketDelimiters)
  , ("customCommentPrefix", checkCustomCommentPrefix)
  , ("customEvalPrefix", checkCustomEvalPrefix)
  , ("pettaEvalPrefixNewlineCommentForm", checkPeTTaEvalPrefixNewlineCommentForm)
  , ("customEvalPrefixNewlineForm", checkCustomEvalPrefixNewlineForm)
  , ("heEvalPrefixMultilineCommentBlock", checkHeEvalPrefixMultilineCommentBlock)
  , ("customEvalPrefixNewlineCommentForm", checkCustomEvalPrefixNewlineCommentForm)
  , ("heDefineEqMissingArgFallsBackFact", checkHeDefineEqMissingArgFallsBackFact)
  , ("heDefineTypeExtraArgFallsBackFact", checkHeDefineTypeExtraArgFallsBackFact)
  , ("pettaDefineEqExtraArgFallsBackFact", checkPeTTaDefineEqExtraArgFallsBackFact)
  , ("pettaDefineTypeMissingArgFallsBackFact", checkPeTTaDefineTypeMissingArgFallsBackFact)
  , ("pettaInSpaceIsPlainFact", checkPeTTaInSpaceIsPlainFact)
  , ("pettaDeclareMemoizedIsPlainFact", checkPeTTaDeclareMemoizedIsPlainFact)
  , ("defaultRelationLowering", checkDefaultRelationLowering)
  , ("defaultBuiltinLowering", checkDefaultBuiltinLowering)
  , ("customRelationLoweringHead", checkCustomRelationLoweringHead)
  , ("customBuiltinLoweringHead", checkCustomBuiltinLoweringHead)
  , ("aliasDefineEqHead", checkAliasDefineEqHead)
  , ("aliasDefineTypeHead", checkAliasDefineTypeHead)
  , ("aliasRoundTripPretty", checkAliasRoundTripPretty)
  , ("aliasPrettyDoesNotRewriteFactSymbols", checkAliasPrettyDoesNotRewriteFactSymbols)
  , ("aliasMultilineProgram", checkAliasMultilineProgram)
  , ("aliasArityMismatchFallsBackFact", checkAliasArityMismatchFallsBackFact)
  , ("strictAliasArityMismatchError", checkStrictAliasArityMismatchError)
  , ("strictUnknownHeadError", checkStrictUnknownHeadError)
  , ("strictArityMismatchError", checkStrictArityMismatchError)
  , ("heImportHeadNowPlainFact", checkHeImportHeadNowPlainFact)
  , ("pettaAddAtomHeadNowPlainFact", checkPeTTaAddAtomHeadNowPlainFact)
  , ("heDocFunctionExpression", checkHeDocFunctionExpression)
  , ("heDocTypeAssignment", checkHeDocTypeAssignment)
  , ("pettaExampleConjMatch", checkPeTTaExampleConjMatch)
  , ("bangOnlyLineIsError", checkBangOnlyLineIsError)
  , ("missingCloseParenProgramError", checkMissingCloseParenProgramError)
  , ("unexpectedCloseParenProgramError", checkUnexpectedCloseParenProgramError)
  ]

def allChecksPass : Bool :=
  allChecks.all (fun x => x.2)

/-! ## Theorem-level parser invariants (non-native_decide) -/

theorem grammar_eval_prefix_field_qPrefix :
    qPrefixSyntax.toGrammarSpec.evalPrefixToken = "?" := by
  rfl

theorem grammar_comment_prefix_field_hash :
    hashCommentSyntax.toGrammarSpec.lineCommentStart = some "#" := by
  rfl

theorem grammar_bracket_fields_custom :
    heBracketSyntax.toGrammarSpec.sexprOpen = "[" ∧
    heBracketSyntax.toGrammarSpec.sexprClose = "]" := by
  constructor <;> rfl

private theorem parseLineOk_true
    (spec : SyntaxSpec) (line : String) (expected : Stmt)
    (h : parseLineOk? spec line expected = true) :
    parseLineWith spec line = .ok expected := by
  unfold parseLineOk? at h
  cases hParsed : parseLineWith spec line with
  | error err =>
      simp [hParsed] at h
  | ok stmt =>
      simp [hParsed] at h
      have hEq : stmt = expected := by
        exact h
      simp [hEq]

private theorem parseProgramOk_true
    (spec : SyntaxSpec) (text : String) (expected : List (Nat × Stmt))
    (h : parseProgramOk? spec text expected = true) :
    parseProgramWith spec text = .ok expected := by
  unfold parseProgramOk? at h
  cases hParsed : parseProgramWith spec text with
  | error err =>
      simp [hParsed] at h
  | ok forms =>
      simp [hParsed] at h
      have hEq : forms = expected := by
        exact h
      simp [hEq]

private theorem parseLineErr_true
    (spec : SyntaxSpec) (line : String)
    (h : parseLineErr? spec line = true) :
    ∃ err, parseLineWith spec line = .error err := by
  unfold parseLineErr? at h
  cases hParsed : parseLineWith spec line with
  | ok stmt =>
      simp [hParsed] at h
  | error err =>
      exact ⟨err, rfl⟩

private theorem parseProgramErr_true
    (spec : SyntaxSpec) (text : String)
    (h : parseProgramErr? spec text = true) :
    ∃ err, parseProgramWith spec text = .error err := by
  unfold parseProgramErr? at h
  cases hParsed : parseProgramWith spec text with
  | ok forms =>
      simp [hParsed] at h
  | error err =>
      exact ⟨err, rfl⟩

theorem parser_uses_grammar_eval_prefix_of_check
    (h : parseLineOk? qPrefixSyntax
      (qPrefixSyntax.toGrammarSpec.evalPrefixToken ++ "(foo)")
      (.eval (app "foo" [])) = true) :
    parseLineWith qPrefixSyntax
      (qPrefixSyntax.toGrammarSpec.evalPrefixToken ++ "(foo)") =
      .ok (.eval (app "foo" [])) := by
  exact parseLineOk_true qPrefixSyntax
    (qPrefixSyntax.toGrammarSpec.evalPrefixToken ++ "(foo)")
    (.eval (app "foo" [])) h

theorem parser_uses_grammar_comment_prefix_of_check
    (h : parseLineOk? hashCommentSyntax
      (hashCommentSyntax.toGrammarSpec.lineCommentStart.getD ";" ++ " hash comment")
      .empty = true) :
    parseLineWith hashCommentSyntax
      (hashCommentSyntax.toGrammarSpec.lineCommentStart.getD ";" ++ " hash comment") =
      .ok .empty := by
  exact parseLineOk_true hashCommentSyntax
    (hashCommentSyntax.toGrammarSpec.lineCommentStart.getD ";" ++ " hash comment")
    .empty h

theorem parser_uses_grammar_bracket_delimiters_of_check
    (h : parseLineOk? heBracketSyntax
      ("!" ++ heBracketSyntax.toGrammarSpec.sexprOpen ++ "foo" ++ heBracketSyntax.toGrammarSpec.sexprClose)
      (.eval (app "foo" [])) = true) :
    parseLineWith heBracketSyntax
      ("!" ++ heBracketSyntax.toGrammarSpec.sexprOpen ++ "foo" ++ heBracketSyntax.toGrammarSpec.sexprClose) =
      .ok (.eval (app "foo" [])) := by
  exact parseLineOk_true heBracketSyntax
    ("!" ++ heBracketSyntax.toGrammarSpec.sexprOpen ++ "foo" ++ heBracketSyntax.toGrammarSpec.sexprClose)
    (.eval (app "foo" [])) h

theorem parser_multiline_eval_comment_block_of_check
    (h : parseProgramOk? he "!\n; c1\n; c2\n(foo)\n"
      [(1, .eval (app "foo" []))] = true) :
    parseProgramWith he "!\n; c1\n; c2\n(foo)\n" =
      .ok [(1, .eval (app "foo" []))] := by
  exact parseProgramOk_true he "!\n; c1\n; c2\n(foo)\n" [(1, .eval (app "foo" []))] h

theorem parser_multiline_custom_eval_comment_of_check
    (h : parseProgramOk? qPrefixHashCommentSyntax "?\n# inline\n(foo)\n"
      [(1, .eval (app "foo" []))] = true) :
    parseProgramWith qPrefixHashCommentSyntax "?\n# inline\n(foo)\n" =
      .ok [(1, .eval (app "foo" []))] := by
  exact parseProgramOk_true qPrefixHashCommentSyntax "?\n# inline\n(foo)\n"
    [(1, .eval (app "foo" []))] h

theorem he_defineEq_missing_arity_falls_back_of_check
    (h : parseLineOk? he "(= (f a))" (.fact (app "=" [app "f" [sym "a"]])) = true) :
    parseLineWith he "(= (f a))" = .ok (.fact (app "=" [app "f" [sym "a"]])) := by
  exact parseLineOk_true he "(= (f a))" (.fact (app "=" [app "f" [sym "a"]])) h

theorem he_defineType_extra_arity_falls_back_of_check
    (h : parseLineOk? he "(: foo Bar Baz)" (.fact (app ":" [sym "foo", sym "Bar", sym "Baz"])) = true) :
    parseLineWith he "(: foo Bar Baz)" = .ok (.fact (app ":" [sym "foo", sym "Bar", sym "Baz"])) := by
  exact parseLineOk_true he "(: foo Bar Baz)"
    (.fact (app ":" [sym "foo", sym "Bar", sym "Baz"])) h

theorem petta_in_space_is_plain_fact_of_check
    (h : parseLineOk? petta "(in-space &tmp (match foo foo))"
      (.fact (app "in-space" [sym "&tmp", app "match" [sym "foo", sym "foo"]])) = true) :
    parseLineWith petta "(in-space &tmp (match foo foo))" =
      .ok (.fact (app "in-space" [sym "&tmp", app "match" [sym "foo", sym "foo"]])) := by
  exact parseLineOk_true petta "(in-space &tmp (match foo foo))"
    (.fact (app "in-space" [sym "&tmp", app "match" [sym "foo", sym "foo"]])) h

theorem custom_relation_lowering_head_of_check
    (h : parseLineOk? customLoweringHeadsSyntax "(rel! edge tim tom)"
      (.relationFact "edge" [sym "tim", sym "tom"]) = true) :
    parseLineWith customLoweringHeadsSyntax "(rel! edge tim tom)" =
      .ok (.relationFact "edge" [sym "tim", sym "tom"]) := by
  exact parseLineOk_true customLoweringHeadsSyntax "(rel! edge tim tom)"
    (.relationFact "edge" [sym "tim", sym "tom"]) h

theorem alias_defineEq_head_of_check
    (h : parseLineOk? aliasCommandSyntax "(rewrite! (f a) b)"
      (.defineEq (app "f" [sym "a"]) (sym "b")) = true) :
    parseLineWith aliasCommandSyntax "(rewrite! (f a) b)" =
      .ok (.defineEq (app "f" [sym "a"]) (sym "b")) := by
  exact parseLineOk_true aliasCommandSyntax "(rewrite! (f a) b)"
    (.defineEq (app "f" [sym "a"]) (sym "b")) h

theorem alias_roundtrip_pretty_of_check
    (h : parseLineRoundTripOk? aliasCommandSyntax "(rewrite! (f $x) (g $x))" = true) :
    parseLineRoundTripOk? aliasCommandSyntax "(rewrite! (f $x) (g $x))" = true := by
  exact h

theorem alias_pretty_preserves_fact_symbols_of_check
    (h : parseLineRoundTripOk? aliasCommandSyntax "(foo =)" = true) :
    parseLineRoundTripOk? aliasCommandSyntax "(foo =)" = true := by
  exact h

theorem alias_multiline_program_of_check
    (h : parseProgramOk? aliasCommandSyntax "(rewrite! (f a) b)\n!(f a)\n"
      [ (1, .defineEq (app "f" [sym "a"]) (sym "b"))
      , (2, .eval (app "f" [sym "a"]))
      ] = true) :
    parseProgramWith aliasCommandSyntax "(rewrite! (f a) b)\n!(f a)\n" =
      .ok [ (1, .defineEq (app "f" [sym "a"]) (sym "b"))
          , (2, .eval (app "f" [sym "a"]))
          ] := by
  exact parseProgramOk_true aliasCommandSyntax "(rewrite! (f a) b)\n!(f a)\n"
    [ (1, .defineEq (app "f" [sym "a"]) (sym "b"))
    , (2, .eval (app "f" [sym "a"]))
    ] h

theorem alias_arity_mismatch_falls_back_of_check
    (h : parseLineOk? aliasCommandSyntax "(rewrite! (f a))"
      (.fact (app "rewrite!" [app "f" [sym "a"]])) = true) :
    parseLineWith aliasCommandSyntax "(rewrite! (f a))" =
      .ok (.fact (app "rewrite!" [app "f" [sym "a"]])) := by
  exact parseLineOk_true aliasCommandSyntax "(rewrite! (f a))"
    (.fact (app "rewrite!" [app "f" [sym "a"]])) h

theorem strict_alias_arity_mismatch_error_of_check
    (h : parseLineErr? strictAliasCommandSyntax "(rewrite! (f a))" = true) :
    ∃ err, parseLineWith strictAliasCommandSyntax "(rewrite! (f a))" = .error err := by
  exact parseLineErr_true strictAliasCommandSyntax "(rewrite! (f a))" h

theorem strict_unknown_head_error_of_check
    (h : parseLineErr? strictDispatchSyntax "(unknown-head foo)" = true) :
    ∃ err, parseLineWith strictDispatchSyntax "(unknown-head foo)" = .error err := by
  exact parseLineErr_true strictDispatchSyntax "(unknown-head foo)" h

theorem strict_arity_mismatch_error_of_check
    (h : parseLineErr? strictDispatchSyntax "(= (f a))" = true) :
    ∃ err, parseLineWith strictDispatchSyntax "(= (f a))" = .error err := by
  exact parseLineErr_true strictDispatchSyntax "(= (f a))" h

theorem missing_close_paren_program_error_of_check
    (h : parseProgramErr? he "!(foo\n" = true) :
    ∃ err, parseProgramWith he "!(foo\n" = .error err := by
  exact parseProgramErr_true he "!(foo\n" h

#eval allChecks
#eval ("allChecksPass", allChecksPass)

end Algorithms.MeTTa.Simple.ParserConformance
