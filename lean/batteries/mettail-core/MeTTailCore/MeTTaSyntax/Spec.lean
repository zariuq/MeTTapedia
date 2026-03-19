namespace MeTTailCore.MeTTaSyntax

structure LexerSpec where
  lineCommentStart : Option String := some ";"
  supportsStringLiterals : Bool := true
  stringDelimiter : Char := '"'
  escapeChar : Char := '\\'
  sexprOpen : Char := '('
  sexprClose : Char := ')'
  allowHashInSymbol : Bool := true
  reserveHashInVariable : Bool := true
  trimAsciiWhitespace : Bool := true
deriving Repr, DecidableEq, BEq

structure EvalPrefixPolicy where
  evalPrefixToken : String := "!"
  allowWhitespaceAfterPrefix : Bool := true
  allowNewlineAfterPrefix : Bool := true
  /-- Whether tokens like `!name` are parsed as symbol atoms (as in HE docs). -/
  bangPrefixedWordIsSymbol : Bool := true
deriving Repr, DecidableEq, BEq

structure LoweringHeads where
  relationFactHead : String := "relation!"
  builtinFactHead : String := "builtin!"
deriving Repr, DecidableEq, BEq

structure CommandDispatchPolicy where
  fallbackUnknownHeadToFact : Bool := true
  fallbackArityMismatchToFact : Bool := true
  fallbackUnsupportedCommandToFact : Bool := true
deriving Repr, DecidableEq, BEq

structure ProgramPolicy where
  explicitQueryOnly : Bool := true
  allowImplicitLastQuery : Bool := false
  defaultSpace : String := "&self"
deriving Repr, DecidableEq, BEq

structure CommandHead where
  head : String
  command : String
  arityMin : Nat := 0
  arityMax : Option Nat := none
deriving Repr, DecidableEq, BEq

/-- Surface sugar for command heads only; core Pattern constructors remain canonical. -/
structure SugarAlias where
  alias : String
  canonical : String
deriving Repr, DecidableEq, BEq

/-- `(head &space ...)` forms lowered to `(in-space &space (canonicalHead ...))`. -/
structure EvalSpaceAlias where
  head : String
  canonicalHead : String
  arity : Nat
deriving Repr, DecidableEq, BEq

structure SyntaxSpec where
  schemaVersion : Nat := 3
  dialect : String
  lexer : LexerSpec
  evalPrefix : EvalPrefixPolicy
  loweringHeads : LoweringHeads := {}
  dispatchPolicy : CommandDispatchPolicy := {}
  programPolicy : ProgramPolicy := {}
  commandHeads : List CommandHead := []
  headAliases : List SugarAlias := []
  evalSpaceAliases : List EvalSpaceAlias := []
  predicateSpecialHeads : List String := []
deriving Repr, DecidableEq, BEq

structure GrammarToken where
  name : String
  pattern : String
  isRegex : Bool := false
deriving Repr, DecidableEq, BEq

structure GrammarProduction where
  lhs : String
  rhs : List String
deriving Repr, DecidableEq, BEq

structure GrammarSpec where
  schemaVersion : Nat := 2
  dialect : String
  startSymbol : String := "program"
  evalPrefixToken : String := "!"
  lineCommentStart : Option String := some ";"
  sexprOpen : String := "("
  sexprClose : String := ")"
  tokens : List GrammarToken := []
  productions : List GrammarProduction := []
deriving Repr, DecidableEq, BEq

private def jsonEscape (s : String) : String :=
  s.foldl
    (fun acc c =>
      acc ++
      match c with
      | '"' => "\\\""
      | '\\' => "\\\\"
      | '\n' => "\\n"
      | '\r' => "\\r"
      | '\t' => "\\t"
      | _ => String.singleton c)
    ""

private def jsonStr (s : String) : String :=
  "\"" ++ jsonEscape s ++ "\""

private def jsonBool (b : Bool) : String :=
  if b then "true" else "false"

private def jsonNat (n : Nat) : String :=
  toString n

private def jsonOptStr (s : Option String) : String :=
  match s with
  | some x => jsonStr x
  | none => "null"

private def jsonOptNat (n : Option Nat) : String :=
  match n with
  | some x => jsonNat x
  | none => "null"

private def charStr (c : Char) : String := String.singleton c

private def renderCommandHead (h : CommandHead) : String :=
  "{"
  ++ "\"head\":" ++ jsonStr h.head ++ ","
  ++ "\"command\":" ++ jsonStr h.command ++ ","
  ++ "\"arity_min\":" ++ jsonNat h.arityMin ++ ","
  ++ "\"arity_max\":" ++ jsonOptNat h.arityMax
  ++ "}"

private def renderSugarAlias (a : SugarAlias) : String :=
  "{"
  ++ "\"alias\":" ++ jsonStr a.alias ++ ","
  ++ "\"canonical\":" ++ jsonStr a.canonical
  ++ "}"

private def renderEvalSpaceAlias (a : EvalSpaceAlias) : String :=
  "{"
  ++ "\"head\":" ++ jsonStr a.head ++ ","
  ++ "\"canonical_head\":" ++ jsonStr a.canonicalHead ++ ","
  ++ "\"arity\":" ++ jsonNat a.arity
  ++ "}"

private def renderGrammarToken (t : GrammarToken) : String :=
  "{"
  ++ "\"name\":" ++ jsonStr t.name ++ ","
  ++ "\"pattern\":" ++ jsonStr t.pattern ++ ","
  ++ "\"is_regex\":" ++ jsonBool t.isRegex
  ++ "}"

private def renderGrammarProduction (p : GrammarProduction) : String :=
  "{"
  ++ "\"lhs\":" ++ jsonStr p.lhs ++ ","
  ++ "\"rhs\":[" ++ String.intercalate "," (p.rhs.map jsonStr) ++ "]"
  ++ "}"

def SyntaxSpec.renderJson (s : SyntaxSpec) : String :=
  let cmdJson := "[" ++ String.intercalate "," (s.commandHeads.map renderCommandHead) ++ "]"
  let aliasJson := "[" ++ String.intercalate "," (s.headAliases.map renderSugarAlias) ++ "]"
  let evalSpaceAliasJson := "[" ++ String.intercalate "," (s.evalSpaceAliases.map renderEvalSpaceAlias) ++ "]"
  let predSpecialJson := "[" ++ String.intercalate "," (s.predicateSpecialHeads.map jsonStr) ++ "]"
  "{"
  ++ "\"schema_version\":" ++ jsonNat s.schemaVersion ++ ","
  ++ "\"dialect\":" ++ jsonStr s.dialect ++ ","
  ++ "\"lexer\":{"
  ++ "\"line_comment_start\":" ++ jsonOptStr s.lexer.lineCommentStart ++ ","
  ++ "\"supports_string_literals\":" ++ jsonBool s.lexer.supportsStringLiterals ++ ","
  ++ "\"string_delimiter\":" ++ jsonStr (charStr s.lexer.stringDelimiter) ++ ","
  ++ "\"escape_char\":" ++ jsonStr (charStr s.lexer.escapeChar) ++ ","
  ++ "\"sexpr_open\":" ++ jsonStr (charStr s.lexer.sexprOpen) ++ ","
  ++ "\"sexpr_close\":" ++ jsonStr (charStr s.lexer.sexprClose) ++ ","
  ++ "\"allow_hash_in_symbol\":" ++ jsonBool s.lexer.allowHashInSymbol ++ ","
  ++ "\"reserve_hash_in_variable\":" ++ jsonBool s.lexer.reserveHashInVariable ++ ","
  ++ "\"trim_ascii_whitespace\":" ++ jsonBool s.lexer.trimAsciiWhitespace
  ++ "},"
  ++ "\"eval_prefix\":{"
  ++ "\"prefix\":" ++ jsonStr s.evalPrefix.evalPrefixToken ++ ","
  ++ "\"allow_whitespace_after_prefix\":" ++ jsonBool s.evalPrefix.allowWhitespaceAfterPrefix ++ ","
  ++ "\"allow_newline_after_prefix\":" ++ jsonBool s.evalPrefix.allowNewlineAfterPrefix ++ ","
  ++ "\"bang_prefixed_word_is_symbol\":" ++ jsonBool s.evalPrefix.bangPrefixedWordIsSymbol
  ++ "},"
  ++ "\"lowering_heads\":{"
  ++ "\"relation_fact_head\":" ++ jsonStr s.loweringHeads.relationFactHead ++ ","
  ++ "\"builtin_fact_head\":" ++ jsonStr s.loweringHeads.builtinFactHead
  ++ "},"
  ++ "\"dispatch_policy\":{"
  ++ "\"fallback_unknown_head_to_fact\":" ++ jsonBool s.dispatchPolicy.fallbackUnknownHeadToFact ++ ","
  ++ "\"fallback_arity_mismatch_to_fact\":" ++ jsonBool s.dispatchPolicy.fallbackArityMismatchToFact ++ ","
  ++ "\"fallback_unsupported_command_to_fact\":" ++ jsonBool s.dispatchPolicy.fallbackUnsupportedCommandToFact
  ++ "},"
  ++ "\"program_policy\":{"
  ++ "\"explicit_query_only\":" ++ jsonBool s.programPolicy.explicitQueryOnly ++ ","
  ++ "\"allow_implicit_last_query\":" ++ jsonBool s.programPolicy.allowImplicitLastQuery ++ ","
  ++ "\"default_space\":" ++ jsonStr s.programPolicy.defaultSpace
  ++ "},"
  ++ "\"command_heads\":" ++ cmdJson ++ ","
  ++ "\"head_aliases\":" ++ aliasJson ++ ","
  ++ "\"eval_space_aliases\":" ++ evalSpaceAliasJson ++ ","
  ++ "\"predicate_special_heads\":" ++ predSpecialJson
  ++ "}"

private def lowerAscii (s : String) : String :=
  String.ofList (s.toList.map Char.toLower)

private def jsEscapeSingle (s : String) : String :=
  s.foldl
    (fun acc c =>
      acc ++
      match c with
      | '\'' => "\\'"
      | '\\' => "\\\\"
      | '\n' => "\\n"
      | '\r' => "\\r"
      | '\t' => "\\t"
      | _ => String.singleton c)
    ""

def GrammarSpec.renderJson (g : GrammarSpec) : String :=
  let toks := "[" ++ String.intercalate "," (g.tokens.map renderGrammarToken) ++ "]"
  let prods := "[" ++ String.intercalate "," (g.productions.map renderGrammarProduction) ++ "]"
  "{"
  ++ "\"schema_version\":" ++ jsonNat g.schemaVersion ++ ","
  ++ "\"dialect\":" ++ jsonStr g.dialect ++ ","
  ++ "\"start_symbol\":" ++ jsonStr g.startSymbol ++ ","
  ++ "\"eval_prefix_token\":" ++ jsonStr g.evalPrefixToken ++ ","
  ++ "\"line_comment_start\":" ++ jsonOptStr g.lineCommentStart ++ ","
  ++ "\"sexpr_open\":" ++ jsonStr g.sexprOpen ++ ","
  ++ "\"sexpr_close\":" ++ jsonStr g.sexprClose ++ ","
  ++ "\"tokens\":" ++ toks ++ ","
  ++ "\"productions\":" ++ prods
  ++ "}"

def GrammarSpec.renderTreeSitterJs (g : GrammarSpec) : String :=
  let grammarName := "metta_" ++ lowerAscii g.dialect
  let extras :=
    match g.lineCommentStart with
    | some _ => "[/\\s/, $.comment]"
    | none => "[/\\s/]"
  let commentRule :=
    match g.lineCommentStart with
    | some c => s!"    comment: $ => token(seq('{jsEscapeSingle c}', /.*/)),\n"
    | none => ""
  "module.exports = grammar({\n"
  ++ s!"  name: '{grammarName}',\n"
  ++ s!"  extras: $ => {extras},\n"
  ++ "  rules: {\n"
  ++ "    source_file: $ => repeat($._top),\n"
  ++ "    _top: $ => choice($.eval_form, $.atom),\n"
  ++ s!"    eval_form: $ => seq('{jsEscapeSingle g.evalPrefixToken}', $.atom),\n"
  ++ "    atom: $ => choice($.list, $.variable, $.string, $.symbol),\n"
  ++ s!"    list: $ => seq('{jsEscapeSingle g.sexprOpen}', repeat($.atom), '{jsEscapeSingle g.sexprClose}'),\n"
  ++ "    variable: $ => /\\$[^\\s()\";]+/,\n"
  ++ "    string: $ => /\"([^\"\\\\]|\\\\.)*\"/,\n"
  ++ "    symbol: $ => /[^\\s()\";]+/,\n"
  ++ commentRule
  ++ "  }\n"
  ++ "});\n"

def GrammarSpec.checksum (g : GrammarSpec) : UInt64 :=
  let fnv64Offset : UInt64 := 14695981039346656037
  let fnv64Prime : UInt64 := 1099511628211
  let text := g.renderJson ++ "\n---\n" ++ g.renderTreeSitterJs
  text.toList.foldl
    (fun h c => (h ^^^ (UInt64.ofNat c.toNat)) * fnv64Prime)
    fnv64Offset

def GrammarSpec.checksumString (g : GrammarSpec) : String :=
  toString g.checksum

def SyntaxSpec.toGrammarSpec (s : SyntaxSpec) : GrammarSpec :=
  let lp := charStr s.lexer.sexprOpen
  let rp := charStr s.lexer.sexprClose
  let commandHeadChoices := s.commandHeads.map (fun h => h.head)
  { schemaVersion := s.schemaVersion
    dialect := s.dialect
    startSymbol := "program"
    evalPrefixToken := s.evalPrefix.evalPrefixToken
    lineCommentStart := s.lexer.lineCommentStart
    sexprOpen := lp
    sexprClose := rp
    tokens :=
      [ { name := "EVAL_PREFIX", pattern := s.evalPrefix.evalPrefixToken }
      , { name := "LPAREN", pattern := lp }
      , { name := "RPAREN", pattern := rp }
      , { name := "VARIABLE", pattern := "\\$[^\\s()\";]+", isRegex := true }
      , { name := "STRING", pattern := "\"([^\"\\\\]|\\\\.)*\"", isRegex := true }
      , { name := "SYMBOL", pattern := "[^\\s()\";]+", isRegex := true }
      ] ++
      (match s.lexer.lineCommentStart with
      | some c => [{ name := "LINE_COMMENT_START", pattern := c }]
      | none => [])
    productions :=
      [ { lhs := "program", rhs := ["top*"] }
      , { lhs := "top", rhs := ["eval_form"] }
      , { lhs := "top", rhs := ["atom"] }
      , { lhs := "eval_form", rhs := ["EVAL_PREFIX", "atom"] }
      , { lhs := "atom", rhs := ["symbol"] }
      , { lhs := "atom", rhs := ["variable"] }
      , { lhs := "atom", rhs := ["string"] }
      , { lhs := "atom", rhs := ["list"] }
      , { lhs := "list", rhs := ["LPAREN", "atom*", "RPAREN"] }
      , { lhs := "command_head", rhs := commandHeadChoices }
      ] }

def SyntaxSpec.canonicalHead (s : SyntaxSpec) (head : String) : String :=
  match s.headAliases.find? (fun a => a.alias == head) with
  | some a => a.canonical
  | none => head

theorem toGrammarSpec_schemaVersion (s : SyntaxSpec) :
    s.toGrammarSpec.schemaVersion = s.schemaVersion := by
  rfl

theorem toGrammarSpec_evalPrefixToken (s : SyntaxSpec) :
    s.toGrammarSpec.evalPrefixToken = s.evalPrefix.evalPrefixToken := by
  rfl

theorem toGrammarSpec_lineCommentStart (s : SyntaxSpec) :
    s.toGrammarSpec.lineCommentStart = s.lexer.lineCommentStart := by
  rfl

theorem toGrammarSpec_sexprOpen (s : SyntaxSpec) :
    s.toGrammarSpec.sexprOpen = String.singleton s.lexer.sexprOpen := by
  rfl

theorem toGrammarSpec_sexprClose (s : SyntaxSpec) :
    s.toGrammarSpec.sexprClose = String.singleton s.lexer.sexprClose := by
  rfl

def heCommandHeads : List CommandHead :=
  [ { head := "=", command := "defineEq", arityMin := 2, arityMax := some 2 }
  , { head := ":", command := "defineType", arityMin := 2, arityMax := some 2 }
  , { head := "add-atom!", command := "addAtom", arityMin := 1, arityMax := some 2 }
  , { head := "remove-atom!", command := "removeAtom", arityMin := 1, arityMax := some 2 }
  , { head := "new-space!", command := "newSpace", arityMin := 0, arityMax := some 1 }
  , { head := "declare-memoized!", command := "declareMemoized", arityMin := 1, arityMax := some 2 }
  , { head := "in-space", command := "inSpace", arityMin := 2, arityMax := some 2 }
  ]

def heHeadAliases : List SugarAlias :=
  [ { alias := "add-atom", canonical := "add-atom!" }
  , { alias := "remove-atom", canonical := "remove-atom!" }
  , { alias := "new-space", canonical := "new-space!" }
  , { alias := "declare-memoized", canonical := "declare-memoized!" }
  ]

def heEvalSpaceAliases : List EvalSpaceAlias :=
  [ { head := "match", canonicalHead := "match", arity := 2 }
  , { head := "unify", canonicalHead := "unify", arity := 2 }
  , { head := "type-check", canonicalHead := "type-check", arity := 2 }
  , { head := "cast", canonicalHead := "cast", arity := 2 }
  ]

def commonPredicateSpecialHeads : List String :=
  [ "is", "+", "-", "*", "/", "%", "==", "!="
  , "<", ">", "<=", ">=", "and", "or", "not"
  , "if", "let", "let*", "match", "find"
  , "succeedsPredicate", "translatePredicate", "Predicate"
  , "catch", "progn", "prog1", "foldall", "forall"
  , "case", "space", "superpose", "collapse", "msort"
  , "Expr", "quote"
  ]

def he : SyntaxSpec :=
  { dialect := "HE"
    lexer := {}
    evalPrefix := { bangPrefixedWordIsSymbol := true }
    commandHeads := heCommandHeads
    headAliases := heHeadAliases
    evalSpaceAliases := heEvalSpaceAliases
    predicateSpecialHeads := commonPredicateSpecialHeads }

def heGrammar : GrammarSpec :=
  he.toGrammarSpec

def pettaCommandHeads : List CommandHead :=
  [ { head := "=", command := "defineEq", arityMin := 2, arityMax := some 2 }
  , { head := "rule!", command := "defineRule", arityMin := 2, arityMax := none }
  , { head := ":", command := "defineType", arityMin := 2, arityMax := some 2 }
  , { head := "import!", command := "import", arityMin := 1, arityMax := some 2 }
  , { head := "add-atom!", command := "addAtom", arityMin := 2, arityMax := some 2 }
  , { head := "remove-atom!", command := "removeAtom", arityMin := 2, arityMax := some 2 }
  , { head := "new-space!", command := "newSpace", arityMin := 1, arityMax := some 1 }
  , { head := "set-fuel", command := "setFuel", arityMin := 1, arityMax := some 1 }
  ]

/-- PeTTa syntax spec — unified surface authority (schema v3).
    Command heads include all recognized PeTTa surface forms.
    Program policy: explicit query only (no implicit-last-query). -/
def petta : SyntaxSpec :=
  { dialect := "PeTTa"
    lexer := {}
    evalPrefix := { bangPrefixedWordIsSymbol := false }
    commandHeads := pettaCommandHeads
    programPolicy := { explicitQueryOnly := true
                       allowImplicitLastQuery := false
                       defaultSpace := "&self" }
    predicateSpecialHeads := commonPredicateSpecialHeads }

def pettaGrammar : GrammarSpec :=
  petta.toGrammarSpec

private def fnv64Offset : UInt64 := 14695981039346656037
private def fnv64Prime : UInt64 := 1099511628211

def checksumText (text : String) : UInt64 :=
  text.toList.foldl
    (fun h c => (h ^^^ (UInt64.ofNat c.toNat)) * fnv64Prime)
    fnv64Offset

def SyntaxSpec.checksum (s : SyntaxSpec) : UInt64 :=
  checksumText (s.renderJson)

def SyntaxSpec.checksumString (s : SyntaxSpec) : String :=
  toString s.checksum

-- ═══════════════════════════════════════════════════════════════════════
-- Atom encoding spec: lowering surface S-expressions to core constructors
-- ═══════════════════════════════════════════════════════════════════════

/-- A surface operator mapped to a nullary core constructor. -/
structure OperatorAlias where
  surfaceSymbol : String
  constructorLabel : String
deriving Repr, DecidableEq, BEq

/-- How integer literals are encoded as constructor-safe tokens. -/
inductive IntEncoding where
  | prefixed (prefix_ : String) (negPrefix : String)
deriving Repr, DecidableEq, BEq

/-- How string literals are encoded as constructor-safe tokens. -/
inductive StringEncoding where
  | prefixed (prefix_ : String)
  | hexPrefixed (prefix_ : String)
deriving Repr, DecidableEq, BEq

/-- Lowering rules from surface S-expressions to core runtime constructors.
    Constructor labels reference `GrammarRule.label` in the `LanguageDef`. -/
structure AtomEncodingSpec where
  symbolWrapper : String
  variableWrapper : String
  variableWrapsName : Bool
  intWrapper : String
  stringWrapper : String
  exprCons : String
  exprNil : String
  intEncoding : IntEncoding
  stringEncoding : StringEncoding
  operatorAliases : List OperatorAlias
  sugarForms : List (String × String × Nat) := []
deriving Repr, DecidableEq, BEq

end MeTTailCore.MeTTaSyntax
