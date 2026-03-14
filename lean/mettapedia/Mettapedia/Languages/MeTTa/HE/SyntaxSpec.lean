import MeTTailCore.MeTTaSyntax.Spec

/-!
# HE Syntax Authority

Authoritative Lean packaging for Hyperon Experimental MeTTa syntax and grammar.

This module does not invent a second parser.  Instead, it makes the syntax
authority explicit in Lean and ties it back to the human-written HE spec:

- upstream prose: `https://trueagi-io.github.io/hyperon-experimental/metta/`

The current plan is deliberately dual-layered:

1. **Compatibility syntax**
   - matches HE-as-implemented today
   - preserves parser-evolution quirks such as `!name` parsing as a symbol atom
2. **Canonical syntax**
   - the intended cleaned surface
   - removes the `!name` symbol quirk so `!` is purely an evaluation prefix

The old artifact filenames stay stable for the compatibility profile:

- `he.syntax_spec.json`
- `he.grammar_spec.json`

The canonical profile is exported alongside them with explicit `he-canonical.*`
names so downstream consumers can adopt it deliberately instead of silently.

This module also makes the tokenizer boundary explicit:

- grammar decides where `WORD` and `STRING` tokens come from
- a host tokenizer decides whether those tokens remain symbols or become
  grounded atoms
- that tokenizer step is part of HE syntax/semantics authority, but it is
  intentionally modeled as host-parameterized rather than hard-coded
-/

namespace Mettapedia.Languages.MeTTa.HE

open MeTTailCore.MeTTaSyntax

/-- Current HE syntax as implemented and already exported in shared syntax
artifacts. -/
def heCompatibilitySyntaxSpec : SyntaxSpec :=
  MeTTailCore.MeTTaSyntax.he

/-- Current HE grammar as implemented and already exported in shared syntax
artifacts. -/
def heCompatibilityGrammarSpec : GrammarSpec :=
  MeTTailCore.MeTTaSyntax.heGrammar

/--
Canonical HE syntax profile.

This deliberately removes the parser-evolution quirk that treats `!name` as a
plain symbol atom.  All other currently shared lexical and command-shape
choices are kept aligned for now.
-/
def heCanonicalSyntaxSpec : SyntaxSpec :=
  { heCompatibilitySyntaxSpec with
      evalPrefix :=
        { heCompatibilitySyntaxSpec.evalPrefix with
            bangPrefixedWordIsSymbol := false } }

/-- Canonical grammar derived from the canonical HE syntax profile. -/
def heCanonicalGrammarSpec : GrammarSpec :=
  heCanonicalSyntaxSpec.toGrammarSpec

theorem heCompatibilityGrammar_isShared :
    heCompatibilityGrammarSpec = MeTTailCore.MeTTaSyntax.heGrammar := by
  rfl

theorem heCompatibilityGrammar_fromCompatibilitySyntax :
    heCompatibilityGrammarSpec = heCompatibilitySyntaxSpec.toGrammarSpec := by
  rfl

theorem heCanonicalGrammar_fromCanonicalSyntax :
    heCanonicalGrammarSpec = heCanonicalSyntaxSpec.toGrammarSpec := by
  rfl

theorem heCompatibility_preservesBangWordSymbolQuirk :
    heCompatibilitySyntaxSpec.evalPrefix.bangPrefixedWordIsSymbol = true := by
  rfl

theorem heCanonical_removesBangWordSymbolQuirk :
    heCanonicalSyntaxSpec.evalPrefix.bangPrefixedWordIsSymbol = false := by
  rfl

theorem heCanonical_sharesLexerWithCompatibility :
    heCanonicalSyntaxSpec.lexer = heCompatibilitySyntaxSpec.lexer := by
  rfl

theorem heCanonical_sharesCommandHeadsWithCompatibility :
    heCanonicalSyntaxSpec.commandHeads = heCompatibilitySyntaxSpec.commandHeads := by
  rfl

theorem heCanonical_sharesEvalSpaceAliasesWithCompatibility :
    heCanonicalSyntaxSpec.evalSpaceAliases = heCompatibilitySyntaxSpec.evalSpaceAliases := by
  rfl

theorem heCanonical_sharesPredicateSpecialHeadsWithCompatibility :
    heCanonicalSyntaxSpec.predicateSpecialHeads =
      heCompatibilitySyntaxSpec.predicateSpecialHeads := by
  rfl

inductive HESyntaxAuthorityLayer where
  | compatibilitySyntax
  | canonicalSyntax
  | hostParameterizedTokenizer
deriving Repr, DecidableEq, BEq

/-- Host-parameterized tokenizer semantics for HE grounded-token construction. -/
structure HETokenizerAuthority where
  schemaVersion : Nat := 1
  dialect : String := "HE"
  wordTokenClass : String := "WORD"
  stringTokenClass : String := "STRING"
  tokenizerIsHostParameterized : Bool := true
  wordTokensMayRemainSymbols : Bool := true
  stringTokensMayRemainSymbols : Bool := true
  wordTokensMayBecomeGrounded : Bool := true
  stringTokensMayBecomeGrounded : Bool := true
  tokenizerEntriesAreRegexConstructorPairs : Bool := true
  tokenizerMayBeModuleExtended : Bool := true
  notes : List String
deriving Repr, DecidableEq, BEq

def heTokenizerAuthority : HETokenizerAuthority :=
  { notes :=
      [ "Grounded atoms are constructed from WORD or STRING tokens by a host tokenizer."
      , "A tokenizer entry is a pair of a token regexp and a constructor function."
      , "If no tokenizer entry matches, the token remains a symbol atom."
      , "Canonical and compatibility syntax profiles share this host-parameterized tokenizer boundary."
      , "Tokenizer authority here governs token construction policy, not parser acceptance."
      ] }

theorem heTokenizerAuthority_isHostParameterized :
    heTokenizerAuthority.tokenizerIsHostParameterized = true := by
  rfl

theorem heTokenizerAuthority_coversWordAndStringGrounding :
    heTokenizerAuthority.wordTokensMayBecomeGrounded = true ∧
    heTokenizerAuthority.stringTokensMayBecomeGrounded = true := by
  simp [heTokenizerAuthority]

theorem heCompatibility_allowsHashInSymbol :
    heCompatibilitySyntaxSpec.lexer.allowHashInSymbol = true := by
  rfl

theorem heCompatibility_reservesHashInVariable :
    heCompatibilitySyntaxSpec.lexer.reserveHashInVariable = true := by
  rfl

theorem heCompatibility_supportsStringLiterals :
    heCompatibilitySyntaxSpec.lexer.supportsStringLiterals = true := by
  rfl

theorem heCanonical_preservesHashReservation :
    heCanonicalSyntaxSpec.lexer.reserveHashInVariable =
      heCompatibilitySyntaxSpec.lexer.reserveHashInVariable := by
  rfl

theorem heCanonical_preservesStringLiteralSupport :
    heCanonicalSyntaxSpec.lexer.supportsStringLiterals =
      heCompatibilitySyntaxSpec.lexer.supportsStringLiterals := by
  rfl

theorem heTokenizerAuthority_wordMayRemainSymbol :
    heTokenizerAuthority.wordTokensMayRemainSymbols = true := by
  rfl

theorem heTokenizerAuthority_stringMayRemainSymbol :
    heTokenizerAuthority.stringTokensMayRemainSymbols = true := by
  rfl

theorem heTokenizerAuthority_wordMayBecomeGrounded :
    heTokenizerAuthority.wordTokensMayBecomeGrounded = true := by
  rfl

theorem heTokenizerAuthority_stringMayBecomeGrounded :
    heTokenizerAuthority.stringTokensMayBecomeGrounded = true := by
  rfl

theorem heTokenizerAuthority_entriesAreRegexConstructorPairs :
    heTokenizerAuthority.tokenizerEntriesAreRegexConstructorPairs = true := by
  rfl

theorem heTokenizerAuthority_mayBeModuleExtended :
    heTokenizerAuthority.tokenizerMayBeModuleExtended = true := by
  rfl

structure HESyntaxAuthorityProfile where
  schemaVersion : Nat := 1
  dialect : String := "HE"
  compatibilitySyntax : SyntaxSpec
  compatibilityGrammar : GrammarSpec
  canonicalSyntax : SyntaxSpec
  canonicalGrammar : GrammarSpec
  tokenizerAuthority : HETokenizerAuthority
  authorityLayers : List HESyntaxAuthorityLayer
  humanSpecSources : List String
  notes : List String
deriving Repr, DecidableEq, BEq

def heSyntaxAuthorityProfile : HESyntaxAuthorityProfile :=
  { compatibilitySyntax := heCompatibilitySyntaxSpec
    compatibilityGrammar := heCompatibilityGrammarSpec
    canonicalSyntax := heCanonicalSyntaxSpec
    canonicalGrammar := heCanonicalGrammarSpec
    tokenizerAuthority := heTokenizerAuthority
    authorityLayers :=
      [ .compatibilitySyntax
      , .canonicalSyntax
      , .hostParameterizedTokenizer
      ]
    humanSpecSources :=
      [ "https://trueagi-io.github.io/hyperon-experimental/metta/"
      ]
    notes :=
      [ "Compatibility syntax preserves the HE parser-evolution quirk where !name can be a symbol atom."
      , "Canonical syntax removes that quirk and treats ! as a pure evaluation prefix."
      , "Tokenizer behavior remains host-parameterized; syntax authority here covers lexical classes and the S-expression surface."
      , "WORD and STRING token classes are authoritative here; grounded-vs-symbol construction is delegated to the host tokenizer."
      , "Compatibility quirks, canonical surface, and host-parameterized tokenizer semantics are separate authority layers."
      , "Parser implementations should conform to this Lean syntax authority, not define it."
      ] }

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

private def jsonNat (n : Nat) : String :=
  toString n

private def jsonBool (b : Bool) : String :=
  if b then "true" else "false"

private def jsonArr (xs : List String) : String :=
  "[" ++ String.intercalate "," (xs.map jsonStr) ++ "]"

private def renderAuthorityLayer : HESyntaxAuthorityLayer → String
  | .compatibilitySyntax => "compatibility_syntax"
  | .canonicalSyntax => "canonical_syntax"
  | .hostParameterizedTokenizer => "host_parameterized_tokenizer"

private def renderTokenizerAuthority (t : HETokenizerAuthority) : String :=
  "{"
    ++ "\"schema_version\":" ++ jsonNat t.schemaVersion ++ ","
    ++ "\"dialect\":" ++ jsonStr t.dialect ++ ","
    ++ "\"word_token_class\":" ++ jsonStr t.wordTokenClass ++ ","
    ++ "\"string_token_class\":" ++ jsonStr t.stringTokenClass ++ ","
    ++ "\"tokenizer_is_host_parameterized\":" ++ jsonBool t.tokenizerIsHostParameterized ++ ","
    ++ "\"word_tokens_may_remain_symbols\":" ++ jsonBool t.wordTokensMayRemainSymbols ++ ","
    ++ "\"string_tokens_may_remain_symbols\":" ++ jsonBool t.stringTokensMayRemainSymbols ++ ","
    ++ "\"word_tokens_may_become_grounded\":" ++ jsonBool t.wordTokensMayBecomeGrounded ++ ","
    ++ "\"string_tokens_may_become_grounded\":" ++ jsonBool t.stringTokensMayBecomeGrounded ++ ","
    ++ "\"tokenizer_entries_are_regex_constructor_pairs\":" ++
      jsonBool t.tokenizerEntriesAreRegexConstructorPairs ++ ","
    ++ "\"tokenizer_may_be_module_extended\":" ++ jsonBool t.tokenizerMayBeModuleExtended ++ ","
    ++ "\"notes\":" ++ jsonArr t.notes
  ++ "}"

def HESyntaxAuthorityProfile.renderJson (p : HESyntaxAuthorityProfile) : String :=
  "{"
    ++ "\"schema_version\":" ++ jsonNat p.schemaVersion ++ ","
    ++ "\"dialect\":" ++ jsonStr p.dialect ++ ","
    ++ "\"compatibility_syntax_checksum\":" ++
      jsonStr p.compatibilitySyntax.checksumString ++ ","
    ++ "\"compatibility_grammar_checksum\":" ++
      jsonStr p.compatibilityGrammar.checksumString ++ ","
    ++ "\"canonical_syntax_checksum\":" ++
      jsonStr p.canonicalSyntax.checksumString ++ ","
    ++ "\"canonical_grammar_checksum\":" ++
      jsonStr p.canonicalGrammar.checksumString ++ ","
    ++ "\"tokenizer_authority\":" ++ renderTokenizerAuthority p.tokenizerAuthority ++ ","
    ++ "\"authority_layers\":[" ++
      String.intercalate "," (p.authorityLayers.map (fun l => jsonStr (renderAuthorityLayer l))) ++ "],"
    ++ "\"human_spec_sources\":" ++ jsonArr p.humanSpecSources ++ ","
    ++ "\"notes\":" ++ jsonArr p.notes
  ++ "}"

private def fnv64Offset : UInt64 := 14695981039346656037
private def fnv64Prime : UInt64 := 1099511628211

def checksumText (text : String) : UInt64 :=
  text.toList.foldl
    (fun h c => (h ^^^ (UInt64.ofNat c.toNat)) * fnv64Prime)
    fnv64Offset

def HESyntaxAuthorityProfile.checksum (p : HESyntaxAuthorityProfile) : UInt64 :=
  checksumText p.renderJson

def HESyntaxAuthorityProfile.checksumString (p : HESyntaxAuthorityProfile) : String :=
  toString p.checksum

private def writeSyntaxArtifact
    (outDir : System.FilePath) (stem : String) (spec : SyntaxSpec) : IO Unit := do
  let jsonPath := outDir / s!"{stem}.syntax_spec.json"
  let checksumPath := outDir / s!"{stem}.syntax_spec.checksum"
  IO.FS.writeFile jsonPath (spec.renderJson ++ "\n")
  IO.FS.writeFile checksumPath (spec.checksumString ++ "\n")

private def writeGrammarArtifact
    (outDir : System.FilePath) (stem : String) (spec : GrammarSpec) : IO Unit := do
  let jsonPath := outDir / s!"{stem}.grammar_spec.json"
  let checksumPath := outDir / s!"{stem}.grammar_spec.checksum"
  IO.FS.writeFile jsonPath (spec.renderJson ++ "\n")
  IO.FS.writeFile checksumPath (spec.checksumString ++ "\n")

def exportHeSyntaxAuthority (outDir : System.FilePath) : IO UInt32 := do
  let profile := heSyntaxAuthorityProfile
  let profileJsonPath := outDir / "he.syntax_authority_profile.json"
  let profileChecksumPath := outDir / "he.syntax_authority_profile.checksum"
  IO.FS.createDirAll outDir
  writeSyntaxArtifact outDir "he" heCompatibilitySyntaxSpec
  writeGrammarArtifact outDir "he" heCompatibilityGrammarSpec
  writeSyntaxArtifact outDir "he-canonical" heCanonicalSyntaxSpec
  writeGrammarArtifact outDir "he-canonical" heCanonicalGrammarSpec
  IO.FS.writeFile profileJsonPath (profile.renderJson ++ "\n")
  IO.FS.writeFile profileChecksumPath (profile.checksumString ++ "\n")
  IO.println s!"exported he syntax authority artifacts to {outDir}"
  pure 0

private def checkArtifactText (path : System.FilePath) (expected : String) :
    IO Bool := do
  let text ← IO.FS.readFile path
  pure (text.trimAscii.toString = expected.trimAscii.toString)

def checkHeSyntaxAuthority (outDir : System.FilePath) : IO UInt32 := do
  let profile := heSyntaxAuthorityProfile
  let checks ←
    [ (outDir / "he.syntax_spec.json", heCompatibilitySyntaxSpec.renderJson)
    , (outDir / "he.syntax_spec.checksum", heCompatibilitySyntaxSpec.checksumString)
    , (outDir / "he.grammar_spec.json", heCompatibilityGrammarSpec.renderJson)
    , (outDir / "he.grammar_spec.checksum", heCompatibilityGrammarSpec.checksumString)
    , (outDir / "he-canonical.syntax_spec.json", heCanonicalSyntaxSpec.renderJson)
    , (outDir / "he-canonical.syntax_spec.checksum", heCanonicalSyntaxSpec.checksumString)
    , (outDir / "he-canonical.grammar_spec.json", heCanonicalGrammarSpec.renderJson)
    , (outDir / "he-canonical.grammar_spec.checksum", heCanonicalGrammarSpec.checksumString)
    , (outDir / "he.syntax_authority_profile.json", profile.renderJson)
    , (outDir / "he.syntax_authority_profile.checksum", profile.checksumString)
    ].mapM (fun (path, expected) => do
      let ok ← checkArtifactText path expected
      pure (path, ok))
  let failures := checks.filter (fun (_, ok) => !ok)
  if failures.isEmpty then
    IO.println s!"[ok] he syntax authority artifacts match at {outDir}"
    pure 0
  else
    for (path, _) in failures do
      IO.println s!"[drift] he syntax authority mismatch at {path}"
    pure 3

section Canaries
#check @heCompatibilitySyntaxSpec
#check @heCompatibilityGrammarSpec
#check @heCanonicalSyntaxSpec
#check @heCanonicalGrammarSpec
#check @exportHeSyntaxAuthority
#check @checkHeSyntaxAuthority
end Canaries

end Mettapedia.Languages.MeTTa.HE
