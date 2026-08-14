import Algorithms.MeTTa.Simple.Parser
import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# Compile-time quotations for MeTTa expressions

This module connects the executable MeTTa parser to Mettapedia's richer
locally-nameless `Pattern` type.  A quotation such as

```lean
metta% petta "(request $channel (payload $value))"
```

is parsed while Lean elaborates the containing file and expands to an
ordinary `Mettapedia.OSLF.MeTTaIL.Syntax.Pattern` constructor tree.  The
kernel subsequently checks that tree like any handwritten Lean term; no
parser result or string remains in the theorem term.

The dialect is mandatory.  `petta` and `he` select the corresponding pinned
`MeTTailCore.MeTTaSyntax.SyntaxSpec`; there is no implicit default whose
meaning could drift.

Scope:

* the current executable expression parser recognizes atoms, `$`-variables,
  and S-expressions;
* it does not elaborate a raw expression into an intrinsically typed MeTTa
  Native term;
* parser correctness is a separate obligation from kernel checking of the
  expanded term.  The positive and negative computations below exercise the
  actual parser, while `metta%` turns parser failure into an elaboration
  error.
-/

namespace Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

open Lean

abbrev CoreCollType := MeTTailCore.MeTTaIL.Syntax.CollType
abbrev CorePattern := MeTTailCore.MeTTaIL.Syntax.Pattern
abbrev Pattern := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern
abbrev ParseError := Algorithms.MeTTa.Simple.Parser.ParseError
abbrev SyntaxSpec := MeTTailCore.MeTTaSyntax.SyntaxSpec

/-- The core executable AST embeds into the richer specification AST.
Core binders have no retained display names, so their metadata is set to
`none`/`[]`; the binding structure and every other constructor are retained. -/
def coreCollTypeToPatternCollType :
    CoreCollType → Mettapedia.OSLF.MeTTaIL.Syntax.CollType
  | .vec => .vec
  | .hashBag => .hashBag
  | .hashSet => .hashSet

mutual
  /-- Structural embedding of the executable parser's AST into Mettapedia's
  specification AST. -/
  def corePatternToPattern : CorePattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | .apply constructor arguments =>
        .apply constructor (corePatternsToPatterns arguments)
    | .lambda body => .lambda none (corePatternToPattern body)
    | .multiLambda count body =>
        .multiLambda count [] (corePatternToPattern body)
    | .subst body replacement =>
        .subst (corePatternToPattern body) (corePatternToPattern replacement)
    | .collection collectionType elements rest =>
        .collection (coreCollTypeToPatternCollType collectionType)
          (corePatternsToPatterns elements) rest

  def corePatternsToPatterns : List CorePattern → List Pattern
    | [] => []
    | pattern :: patterns =>
        corePatternToPattern pattern :: corePatternsToPatterns patterns
end

/-- Runtime form of the same boundary used by `metta%`. -/
def parsePatternWith (spec : SyntaxSpec) (source : String) :
    Except ParseError Pattern :=
  (Algorithms.MeTTa.Simple.Parser.parseExprWithDetailed spec source).map
    corePatternToPattern

/-- Parse one PeTTa expression into the Mettapedia pattern carrier. -/
def parsePeTTaPattern (source : String) : Except ParseError Pattern :=
  parsePatternWith MeTTailCore.MeTTaSyntax.petta source

/-- Parse one HE expression into the Mettapedia pattern carrier. -/
def parseHEPattern (source : String) : Except ParseError Pattern :=
  parsePatternWith MeTTailCore.MeTTaSyntax.he source

private def mkStringTerm (value : String) : TSyntax `term :=
  ⟨Syntax.mkStrLit value⟩

private def mkTermList : List (TSyntax `term) → MacroM (TSyntax `term)
  | [] => `([])
  | term :: terms => do
      let tail ← mkTermList terms
      `($term :: $tail)

private def quoteCollType : CoreCollType → MacroM (TSyntax `term)
  | .vec =>
      `(Mettapedia.OSLF.MeTTaIL.Syntax.CollType.vec)
  | .hashBag =>
      `(Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashBag)
  | .hashSet =>
      `(Mettapedia.OSLF.MeTTaIL.Syntax.CollType.hashSet)

private partial def quoteCorePattern : CorePattern → MacroM (TSyntax `term)
  | .bvar index =>
      `(Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.bvar $(quote index))
  | .fvar name =>
      `(Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar $(mkStringTerm name))
  | .apply constructor arguments => do
      let quotedArguments ← arguments.mapM quoteCorePattern
      let argumentList ← mkTermList quotedArguments
      `(Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.apply
          $(mkStringTerm constructor) $argumentList)
  | .lambda body => do
      let quotedBody ← quoteCorePattern body
      `(Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.lambda none $quotedBody)
  | .multiLambda count body => do
      let quotedBody ← quoteCorePattern body
      `(Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.multiLambda
          $(quote count) [] $quotedBody)
  | .subst body replacement => do
      let quotedBody ← quoteCorePattern body
      let quotedReplacement ← quoteCorePattern replacement
      `(Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.subst
          $quotedBody $quotedReplacement)
  | .collection collectionType elements rest => do
      let quotedCollectionType ← quoteCollType collectionType
      let quotedElements ← elements.mapM quoteCorePattern
      let elementList ← mkTermList quotedElements
      let quotedRest ← match rest with
        | none => `(none)
        | some name => `(some $(mkStringTerm name))
      `(Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.collection
          $quotedCollectionType $elementList $quotedRest)

private def expandQuotation (spec : SyntaxSpec) (source : TSyntax `str) :
    MacroM (TSyntax `term) := do
  match Algorithms.MeTTa.Simple.Parser.parseExprWithDetailed spec source.getString with
  | .ok pattern => quoteCorePattern pattern
  | .error error =>
      Macro.throwErrorAt source
        s!"MeTTa expression parse failed: {error.render}"

scoped syntax (name := mettaPatternQuotation)
  "metta% " (&"petta" <|> &"he") str : term

scoped macro_rules
  | `(metta% petta $source:str) =>
      expandQuotation MeTTailCore.MeTTaSyntax.petta source
  | `(metta% he $source:str) =>
      expandQuotation MeTTailCore.MeTTaSyntax.he source

/-! ## Executable and elaborated controls -/

open scoped MeTTaSyntaxQuotation

/-- Positive: authored PeTTa syntax expands to the exact specification AST. -/
example :
    metta% petta "(request $channel (payload $value))" =
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.apply "request"
        [ Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar "channel"
        , Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.apply "payload"
            [Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar "value"] ] :=
  rfl

/-- Positive: the HE selector reaches the same expression parser with an
explicitly different dialect specification. -/
example :
    metta% he "(answer ticket-7 ok)" =
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.apply "answer"
        [ Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.apply "ticket-7" []
        , Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.apply "ok" [] ] :=
  rfl

/-- Negative executable fixture: malformed MeTTa is rejected by the runtime
parser boundary.  Concrete string parsing remains an executable boundary, so
this is a `Bool` fixture rather than a theorem about kernel reduction.  The
corresponding `metta%` form fails during elaboration. -/
def malformedPeTTaRejected : Bool :=
  !(parsePeTTaPattern "(request $channel").isOk

end Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation
