import Mettapedia.Languages.Metamath.InferenceOneShotByteLog
import Mettapedia.Languages.Metamath.SourceGSLT
import Mettapedia.Languages.Metamath.VerifiedCheckerSemantics

open Mettapedia.GSLT.LanguageDef

/-!
# Metamath source-GSLT to verified-checker alignment

The generated parser is an untrusted proof producer.  Its ordered token ledger
and compact grammar proof are accepted only after two independent checks:

* the generic grammar checker reconstructs an exact `SourceGSLT` derivation;
* the serialized token sequence agrees with the token calls made by the
  verified `mm-lean4` reader on the same bytes.

The second check does not make the runtime reader the grammar authority.  It
is a lowering correspondence at the syntax/semantics boundary: both sides
must account for the same ordered source tokens before the verified checker
state can be used.  Comment calls are removed from the comparison because the
source GSLT treats comments as lexical trivia.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.SourceGSLTCheckerAlignment

open Mettapedia.GSLT.LanguageDef.GrammarInferenceExtraction
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceCheckerDAG
open Mettapedia.Languages.Metamath.InferenceOneShotByteLog
open Mettapedia.Languages.Metamath.SourceGSLT
open Mettapedia.Languages.Metamath.VerifiedCheckerSemantics
open Mettapedia.OSLF.Framework.GrammarDerives
open Mettapedia.OSLF.MeTTaIL.Syntax

private def tokenOfCall (call : TokenCall) : ByteSlice :=
  InferenceOneShotByteLog.Raw.TokenOrigin.token call.origin

/-- Project one verified-reader token call to the syntax ledger.  The opening
and closing delimiters and the body of a comment are lexical trivia. -/
def significantToken? (call : TokenCall) : Option String :=
  let token := tokenOfCall call
  match call.before.tokp with
  | .comment _ => none
  | _ =>
      if token.eqArray "$(".toAscii then none else some token.toString

/-- Keep each significant token together with the exact typed
`ParserState.feedToken` call that consumed it.  The pair is ordered by the
verified reader's execution trace. -/
def significantCall? (call : TokenCall) : Option (String × TokenCall) :=
  (significantToken? call).map fun token => (token, call)

/-- Chronological significant calls made by the verified reader. -/
def loggedSignificantCalls (bytes : ByteArray) : List (String × TokenCall) :=
  (checkBytesLogged bytes).calls.filterMap significantCall?

/-- Chronological non-comment tokens observed by the verified reader. -/
def loggedSignificantTokens (bytes : ByteArray) : List String :=
  (loggedSignificantCalls bytes).map (fun entry => entry.1)

/-- One exact lowering step from a classified source token to the verified
reader.  It records both byte agreement and the actual typed state
transition; the latter is not reconstructed by this bridge. -/
def TokenLoweringStep
    (sourceToken : ClassifiedToken) (entry : String × TokenCall) : Prop :=
  sourceToken.serialized = entry.1 ∧
    entry.2.after = entry.2.before.feedToken
      entry.2.origin.parserOffset entry.2.origin.token

/-- The source ledger lowers exactly to the verified reader when its tokens
pair one-for-one with the chronological typed calls and the logged final
database is the production checker's database. -/
structure TypedLoweringCertificate
    (bytes : ByteArray) (source : ClassifiedSource) : Prop where
  tokenCalls :
    List.Forall₂ TokenLoweringStep source.tokens
      (loggedSignificantCalls bytes)
  finalDatabase :
    (checkBytesLogged bytes).db = Metamath.Verify.checkBytes bytes

private theorem tokenLoweringSteps_of_map_eq :
    ∀ (tokens : List ClassifiedToken) (calls : List (String × TokenCall)),
      tokens.map ClassifiedToken.serialized = calls.map (fun entry => entry.1) →
        List.Forall₂ TokenLoweringStep tokens calls
  | [], [], _ => .nil
  | [], _ :: _, equality => by simp at equality
  | _ :: _, [], equality => by simp at equality
  | token :: tokens, call :: calls, equality => by
      simp only [List.map_cons, List.cons.injEq] at equality
      exact .cons ⟨equality.1, call.2.after_eq⟩
        (tokenLoweringSteps_of_map_eq tokens calls equality.2)

private theorem tokenLoweringSteps_map_eq
    {tokens : List ClassifiedToken} {calls : List (String × TokenCall)}
    (lowering : List.Forall₂ TokenLoweringStep tokens calls) :
    tokens.map ClassifiedToken.serialized =
      calls.map (fun entry => entry.1) := by
  induction lowering with
  | nil => rfl
  | cons step _ tail =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨step.1, tail⟩

/-- Executable equality at the lowering boundary. -/
def orderedTokenAgreement
    (bytes : ByteArray) (source : ClassifiedSource) : Bool :=
  source.ledger.tokens == loggedSignificantTokens bytes

theorem orderedTokenAgreement_sound
    {bytes : ByteArray} {source : ClassifiedSource}
    (accepted : orderedTokenAgreement bytes source = true) :
    source.ledger.tokens = loggedSignificantTokens bytes := by
  simpa [orderedTokenAgreement] using accepted

/-- Exact typed lowering is equivalent to exact ordered-token agreement.
The database component contributes no assumption: its equality is proved by
erasing the independently instrumented checker trace. -/
theorem typedLoweringCertificate_iff
    {bytes : ByteArray} {source : ClassifiedSource} :
    TypedLoweringCertificate bytes source ↔
      source.ledger.tokens = loggedSignificantTokens bytes := by
  constructor
  · intro lowering
    simpa [ClassifiedSource.ledger, loggedSignificantTokens] using
      tokenLoweringSteps_map_eq lowering.tokenCalls
  · intro equality
    refine
      { tokenCalls := ?_
        finalDatabase := checkBytesLogged_db_eq_checkBytes bytes }
    apply tokenLoweringSteps_of_map_eq
    simpa [ClassifiedSource.ledger, loggedSignificantTokens] using equality

/-- Complete proof-carrying input to the verified checker boundary.  The
native parser may produce these fields, but only the independent checks below
authorize their use. -/
structure CheckedParserOutput (bytes : ByteArray) where
  source : ClassifiedSource
  sourceValid : source.isValid = true
  lexicalValid : lexicallyValidSource source = true
  definition : ValidatedCalculusLanguageDef
  admitted :
    admitLexicalDAGDefinition sourceGrammar lexicalDeclarations source =
      some definition
  rootId : Nat
  blocks : List (List DAGNode)
  grammarChecked :
    checkDAGBlocks definition
      (dagRootJudgment source.ledger outerDatabaseSort) rootId blocks = true
  orderedTokensChecked : orderedTokenAgreement bytes source = true
  readerAccepted : (Metamath.Verify.checkBytes bytes).error? = none

namespace CheckedParserOutput

/-- The compact parser proof reconstructs an ordinary derivation of the exact
ordered ledger, together with its exact generic-proof erasure. -/
theorem syntaxExact {bytes : ByteArray}
    (output : CheckedParserOutput bytes) :
    ∃ (proof : RawProof)
        (derivation : Derivation output.definition
          (dagRootJudgment output.source.ledger outerDatabaseSort))
        (tree : Pattern),
      expandDAGBlocks? output.definition
          (dagRootJudgment output.source.ledger outerDatabaseSort)
          output.rootId output.blocks = some proof ∧
        derivation.erase = proof ∧
        Derives
          (lexicalizedLanguage sourceGrammar lexicalDeclarations output.source)
          outerDatabaseSort output.source.ledger.tokens tree :=
  checkedMetamathSourceBlocks_exact output.source output.definition
    output.admitted output.rootId output.blocks output.grammarChecked

/-- The parser ledger and verified reader consumed the same significant
tokens, in the same order and with the same multiplicity. -/
theorem orderedTokensExact {bytes : ByteArray}
    (output : CheckedParserOutput bytes) :
    output.source.ledger.tokens = loggedSignificantTokens bytes :=
  orderedTokenAgreement_sound output.orderedTokensChecked

/-- The exact source ledger is replayed by mm-lean4's typed token transition,
with neither token nor state evolution supplied by the generated parser. -/
theorem typedLoweringExact {bytes : ByteArray}
    (output : CheckedParserOutput bytes) :
    TypedLoweringCertificate bytes output.source :=
  typedLoweringCertificate_iff.mpr output.orderedTokensExact

/-- The instrumented typed lowering erases to the actual verified checker
entrypoint, for this exact byte array. -/
theorem loggedDB_eq_checkerDB {bytes : ByteArray}
    (_output : CheckedParserOutput bytes) :
    (checkBytesLogged bytes).db = Metamath.Verify.checkBytes bytes :=
  checkBytesLogged_db_eq_checkBytes bytes

/-- On a source carrying a checked parser certificate and exact ordered-ledger
alignment, implementation proof acceptance is equivalent to declarative
`Metamath.Spec.Provable`. -/
theorem implementationAcceptance_iff_specProvability
    {bytes : ByteArray} (output : CheckedParserOutput bytes)
    (label : String) (formula : Metamath.Verify.Formula) :
    ImplementationAccepts bytes label formula ↔
      DeclarativeAccepts bytes formula :=
  implementationAccepts_iff_declarativeAccepts
    bytes label formula output.readerAccepted

/-- Acceptance at the joined boundary: a generated-parser certificate has
been independently rechecked and lowered token-for-token to mm-lean4, and
the verified checker accepts the requested proof. -/
def GeneratedParserAndCheckerAccepts
    {bytes : ByteArray} (output : CheckedParserOutput bytes)
    (label : String) (formula : Metamath.Verify.Formula) : Prop :=
  TypedLoweringCertificate bytes output.source ∧
    ImplementationAccepts bytes label formula

/-- Acceptance equivalence for one proof-carrying parser output.  The reverse
direction cannot manufacture syntax evidence: it is indexed by an existing
`CheckedParserOutput`, whose grammar certificate and ordered lowering have
already passed their independent checkers. -/
theorem generatedParserAndCheckerAcceptance_iff_specProvability
    {bytes : ByteArray} (output : CheckedParserOutput bytes)
    (label : String) (formula : Metamath.Verify.Formula) :
    GeneratedParserAndCheckerAccepts output label formula ↔
      DeclarativeAccepts bytes formula := by
  constructor
  · intro accepted
    exact (output.implementationAcceptance_iff_specProvability
      label formula).mp accepted.2
  · intro provable
    exact ⟨output.typedLoweringExact,
      (output.implementationAcceptance_iff_specProvability
        label formula).mpr provable⟩

/-- One checked end-to-end semantic certificate for an exact source byte
array.  It keeps syntax evidence, exact ordered-token boundary agreement,
checker identity, and the operational/declarative equivalence together
without making the syntax `LanguageDef` depend on Metamath semantics. -/
def EndToEndCertificate
    {bytes : ByteArray} (output : CheckedParserOutput bytes)
    (label : String) (formula : Metamath.Verify.Formula) : Prop :=
  ∃ (rawProof : RawProof)
      (derivation : Derivation output.definition
        (dagRootJudgment output.source.ledger outerDatabaseSort))
      (tree : Pattern),
    expandDAGBlocks? output.definition
        (dagRootJudgment output.source.ledger outerDatabaseSort)
        output.rootId output.blocks = some rawProof ∧
      derivation.erase = rawProof ∧
      Derives
        (lexicalizedLanguage sourceGrammar lexicalDeclarations output.source)
        outerDatabaseSort output.source.ledger.tokens tree ∧
      TypedLoweringCertificate bytes output.source ∧
      (ImplementationAccepts bytes label formula ↔
        DeclarativeAccepts bytes formula)

/-- Compose the independently checked syntax certificate with mm-lean4's
proved operational/declarative equivalence. -/
theorem endToEndCertificate
    {bytes : ByteArray} (output : CheckedParserOutput bytes)
    (label : String) (formula : Metamath.Verify.Formula) :
    EndToEndCertificate output label formula := by
  rcases output.syntaxExact with
    ⟨rawProof, derivation, tree, expanded, erasure, syntaxDerives⟩
  exact ⟨rawProof, derivation, tree, expanded, erasure, syntaxDerives,
    output.typedLoweringExact,
    output.implementationAcceptance_iff_specProvability label formula⟩

end CheckedParserOutput

/-! ## Executable boundary examples -/

private def fixtureText : String :=
  "$( a comment $)\n$c wff $.\n$v p $.\nwp $f wff p $.\nax $a wff p $.\n"

private def fixtureSource : ClassifiedSource :=
  { identity := "metamath-source-alignment-fixture"
    tokens :=
      [{ serialized := "$c", literalName := none, className := "" },
       { serialized := "wff", literalName := none, className := "mm-symbol" },
       { serialized := "$.", literalName := none, className := "" },
       { serialized := "$v", literalName := none, className := "" },
       { serialized := "p", literalName := none, className := "mm-symbol" },
       { serialized := "$.", literalName := none, className := "" },
       { serialized := "wp", literalName := none, className := "mm-label" },
       { serialized := "$f", literalName := none, className := "" },
       { serialized := "wff", literalName := none, className := "mm-symbol" },
       { serialized := "p", literalName := none, className := "mm-symbol" },
       { serialized := "$.", literalName := none, className := "" },
       { serialized := "ax", literalName := none, className := "mm-label" },
       { serialized := "$a", literalName := none, className := "" },
       { serialized := "wff", literalName := none, className := "mm-symbol" },
       { serialized := "p", literalName := none, className := "mm-symbol" },
       { serialized := "$.", literalName := none, className := "" }] }

private def forgedClassSource : ClassifiedSource :=
  { identity := "metamath-forged-class-fixture"
    tokens :=
      [{ serialized := "contains space",
         literalName := none,
         className := "mm-symbol" }] }

private def reorderedFixtureSource : ClassifiedSource :=
  { fixtureSource with tokens := fixtureSource.tokens.reverse }

/- Positive: comments disappear, while every significant token remains in
source order. -/
#guard orderedTokenAgreement fixtureText.toUTF8 fixtureSource

/- Positive: all producer-supplied classes are independently justified by the
authored lexical policy. -/
#guard lexicallyValidSource fixtureSource

/- Negative: attaching `mm-symbol` to bytes outside that class is rejected. -/
#guard !lexicallyValidSource forgedClassSource

/- Negative: a ledger with the right multiset in the wrong order is rejected. -/
#guard !orderedTokenAgreement fixtureText.toUTF8 reorderedFixtureSource

end Mettapedia.Languages.Metamath.SourceGSLTCheckerAlignment
