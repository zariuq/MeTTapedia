import Lean.Data.Json
import MeTTailCore.Crypto.SHA256

/-!
# Full MM0 Syntax Authority

Lean-owned syntax specification for the full MM0 language, derived from
the authoritative spec at `mm0/mm0.md` (Mario Carneiro).

MM0 has **two-stage parsing**:
1. **Primary stage**: `.mm0` file structure — statements, binders, types
2. **Secondary stage**: math-string interpretation via notation declarations
   (delimiter, prefix, infixl, infixr, coercion, notation)

This module defines both stages as Lean structures, exports them as
JSON artifacts, and explicitly encodes the two-stage boundary.

Council: Knuth (spec is well-defined), Carneiro (two-stage is structural),
  Tao (primary is CF, secondary is operator-precedence),
  Pfenning (notation is well-studied), Tang (single-source in Lean).
-/

namespace Mettapedia.Languages.MM0.SyntaxSpec

-- ═══════════════════════════════════════════════════════════════════════
-- § Primary Stage: .mm0 File Grammar
-- ═══════════════════════════════════════════════════════════════════════

/-- Lexical token classes in the primary MM0 grammar. -/
inductive MM0TokenClass where
  | symbol       -- single characters: { * . : ; ( ) > } = _
  | identifier   -- [a-zA-Z_][a-zA-Z0-9_-]*
  | number       -- 0 | [1-9][0-9]*
  | stringLiteral -- "compiler.mm0"
  | mathString   -- $ [^$]* $
  | lineComment  -- -- to end of line
  | whitespace   -- spaces, tabs, newlines (ignored)
deriving Repr, DecidableEq, BEq

/-- Sort modifiers (applied before `sort` keyword). -/
structure SortModifiers where
  pure : Bool := false      -- no term formers
  strict : Bool := false    -- no bound variables
  provable : Bool := false  -- can be proven
  free : Bool := false      -- no dummy variables
deriving Repr, DecidableEq, BEq, Lean.ToJson, Lean.FromJson

/-- Statement kinds in the primary MM0 grammar. -/
inductive MM0StmtKind where
  | importStmt     -- import "foo.mm0";
  | sortDecl       -- sort <id> ;
  | termDecl       -- term <id> (<binders>) : <arrow-type> ;
  | defDecl        -- def <id> (<binders>) : <type> (= <formula>)? ;
  | axiomDecl      -- axiom <id> (<binders>) : <formula> ;
  | theoremDecl    -- theorem <id> (<binders>) : <formula> ;
  | notationDecl   -- delimiter | prefix | infixl | infixr | coercion | notation
  | inputStmt      -- input <kind> : <formula> ;
  | outputStmt     -- output <kind> : <formula> ;
deriving Repr, DecidableEq, BEq

/-- Binder syntax in type declarations. -/
inductive BinderKind where
  | bound   -- {x y: sort} — bound variable (curly braces)
  | regular -- (x y: sort) — regular variable (parentheses)
  | dummy   -- .x: sort — dummy variable (dot prefix, in defs only)
deriving Repr, DecidableEq, BEq, Lean.ToJson, Lean.FromJson

/-- Primary syntax specification for the .mm0 file format.
    This covers the outer structure but NOT math-string interpretation. -/
structure MM0PrimarySyntaxSpec where
  schemaVersion : Nat := 1
  language : String := "MM0"
  lineCommentStart : String := "--"
  stringLiteralDelimiter : String := "\""
  mathStringDelimiter : String := "$"
  identifierPattern : String := "[a-zA-Z_][a-zA-Z0-9_]*"
  numberPattern : String := "0|[1-9][0-9]*"
  symbolChars : String := "{*.;:()>=_}"
  whitespaceChars : List String := [" ", "\\n"]
  statementKinds : List String :=
    ["import", "sort", "term", "def", "axiom", "theorem",
     "delimiter", "prefix", "infixl", "infixr", "coercion", "notation",
     "input", "output"]
  pseudoKeywords : List String :=
    [ "axiom", "coercion", "def", "delimiter", "free", "import", "infixl", "infixr"
    , "input", "max", "notation", "output", "prec", "prefix", "provable"
    , "pure", "sort", "strict", "term", "theorem"
    ]
  sortModifierKeywords : List String := ["pure", "strict", "provable", "free"]
  binderKinds : List String := ["bound", "regular", "dummy"]
  maxPrecedenceKeyword : String := "max"
  notes : List String :=
    [ "Primary stage parses the .mm0 outer statement structure only, including import statements."
    , "Math strings remain opaque at the primary stage and are interpreted later."
    , "The MM0 spec only treats space and newline as whitespace for portability."
    ]
deriving Repr, Lean.ToJson, Lean.FromJson

-- ═══════════════════════════════════════════════════════════════════════
-- § Secondary Stage: Math-String Notation Parsing
-- ═══════════════════════════════════════════════════════════════════════

/-- Associativity for infix operators. -/
inductive Associativity where
  | left | right | none
deriving Repr, DecidableEq, BEq, Lean.ToJson, Lean.FromJson

/-- Notation kind in MM0. -/
inductive NotationKind where
  | delimiter                    -- tokenization boundary
  | prefix (prec : Nat)         -- prefix operator
  | infixl (prec : Nat)         -- left-associative infix
  | infixr (prec : Nat)         -- right-associative infix
  | coercion (src tgt : String)  -- implicit sort conversion
  | general                     -- arbitrary constant-variable sequence
deriving Repr, DecidableEq, BEq

/-- The secondary parsing contract: how math-strings are interpreted.
    This is NOT a static grammar — it's a dynamic system where notation
    declarations extend the active operator table during parsing.

    Positive example: the generic parser runtime can first parse statements,
    then use exported notation authority for formulas.

    Negative example: do NOT pretend this is a single static tree-sitter
    grammar. Math-string parsing depends on preceding notation declarations. -/
structure MM0SecondaryParseContract where
  schemaVersion : Nat := 1
  language : String := "MM0"
  description : String :=
    "Math strings ($...$) are parsed after primary statement parsing. " ++
    "Notation commands (delimiter, prefix, infixl, infixr, coercion, notation) " ++
    "extend the active operator table. Precedence levels are nonneg integers " ++
    "or 'max' (= 1024). The secondary parser is an operator-precedence parser " ++
    "that consults the current notation environment."
  isStaticGrammar : Bool := false  -- explicitly: NOT a static grammar
  isDynamicOperatorPrecedence : Bool := true
  maxPrecedenceValue : Nat := 1024
  notationKinds : List String :=
    ["delimiter", "prefix", "infixl", "infixr", "coercion", "notation"]
  delimiterSemantic : String :=
    "Delimiters control tokenization of math strings: " ++
    "split after left-delimiters, split before right-delimiters."
  coercionSemantic : String :=
    "Coercions form a DAG. Composite coercion paths are resolved " ++
    "by composition. Ambiguous coercion paths are errors."
  boundVariableSyntax : String := "{x y: sort}"
  dummyVariableSyntax : String := ".x: sort"
  notes : List String :=
    [ "Secondary parsing is driven by preceding notation declarations in the source file."
    , "This is an operator-precedence parser over math strings, not a static context-free grammar."
    , "Out-of-order notation support is implementation-defined; the authority here records the semantic shape, not one parser implementation trick."
    ]
deriving Repr, Lean.ToJson, Lean.FromJson

-- ═══════════════════════════════════════════════════════════════════════
-- § Syntax Authority Profile
-- ═══════════════════════════════════════════════════════════════════════

/-- Complete syntax authority for MM0, bundling both stages.
    Follows the HE pattern: primary + secondary + tokenizer authority. -/
structure MM0SyntaxAuthorityProfile where
  schemaVersion : Nat := 1
  language : String := "MM0"
  primarySyntax : MM0PrimarySyntaxSpec
  secondaryParseContract : MM0SecondaryParseContract
  twoStageParsing : Bool := true
  primaryAuthoritySource : String := "mm0/mm0.md (grammar section)"
  cReferenceVerifier : String := "mm0/mm0-c/verifier.c"
  rustReferenceCompiler : String := "mm0/mm0-rs/ (mm0-rs compile)"
  sharedArtifactSchema : String := "lean-projects/mettapedia/artifacts/parser_artifact_schema.json"
  notes : List String :=
    [ "Full MM0 has two-stage parsing: primary (.mm0 structure) + secondary (math-string notation)."
    , "The MMB binary format (.mmb) is the trust boundary for proof verification."
    , "The .mm0 text format is the human-readable spec and name-checking authority."
    , "MM0Lite (in mettapedia) is a MINIMAL formalization, not the full language."
    , "This authority covers the full MM0 as specified in mm0.md." ]
deriving Repr, Lean.ToJson, Lean.FromJson

-- ═══════════════════════════════════════════════════════════════════════
-- § Canonical Instances
-- ═══════════════════════════════════════════════════════════════════════

def mm0PrimarySyntax : MM0PrimarySyntaxSpec := {}

def mm0SecondaryContract : MM0SecondaryParseContract := {}

def mm0SyntaxAuthority : MM0SyntaxAuthorityProfile :=
  { primarySyntax := mm0PrimarySyntax
    secondaryParseContract := mm0SecondaryContract }

-- ═══════════════════════════════════════════════════════════════════════
-- § JSON Export
-- ═══════════════════════════════════════════════════════════════════════

def exportMM0SyntaxArtifacts (outDir : System.FilePath) : IO Unit := do
  IO.FS.createDirAll outDir
  let primaryJson := Lean.toJson mm0PrimarySyntax
  let secondaryJson := Lean.toJson mm0SecondaryContract
  let authorityJson := Lean.toJson mm0SyntaxAuthority
  IO.FS.writeFile (outDir / "mm0.syntax_spec.json") primaryJson.pretty
  IO.FS.writeFile (outDir / "mm0.syntax_spec.json.checksum")
    (MeTTailCore.Crypto.SHA256.sha256Hex primaryJson.pretty ++ "\n")
  IO.FS.writeFile (outDir / "mm0.secondary_parse_contract.json") secondaryJson.pretty
  IO.FS.writeFile (outDir / "mm0.secondary_parse_contract.json.checksum")
    (MeTTailCore.Crypto.SHA256.sha256Hex secondaryJson.pretty ++ "\n")
  IO.FS.writeFile (outDir / "mm0.syntax_authority_profile.json") authorityJson.pretty
  IO.FS.writeFile (outDir / "mm0.syntax_authority_profile.json.checksum")
    (MeTTailCore.Crypto.SHA256.sha256Hex authorityJson.pretty ++ "\n")

def checkMM0SyntaxArtifacts (outDir : System.FilePath) : IO Bool := do
  let ok1 ← (outDir / "mm0.syntax_spec.json").pathExists
  let ok2 ← (outDir / "mm0.secondary_parse_contract.json").pathExists
  let ok3 ← (outDir / "mm0.syntax_authority_profile.json").pathExists
  let ok4 ← (outDir / "mm0.syntax_spec.json.checksum").pathExists
  let ok5 ← (outDir / "mm0.secondary_parse_contract.json.checksum").pathExists
  let ok6 ← (outDir / "mm0.syntax_authority_profile.json.checksum").pathExists
  pure (ok1 && ok2 && ok3 && ok4 && ok5 && ok6)

end Mettapedia.Languages.MM0.SyntaxSpec
