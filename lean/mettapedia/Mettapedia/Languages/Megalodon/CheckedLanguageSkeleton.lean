import Mettapedia.GSLT.CheckedLanguage
import Mettapedia.OSLF.Framework.GrammarDerives

/-!
# Checked-language port for Megalodon

Megalodon's dynamic-operator presentation is not yet connected to a verified
Lean checker.  This module therefore instantiates only the honest stage
signature, not `CheckedLanguage` itself.

The parser-facing root is required to be syntax-only.  Dynamic operator
resolution and checking belong behind the explicit lowering boundary.
-/

set_option autoImplicit false

universe uState uClaim

namespace Mettapedia.Languages.Megalodon.CheckedLanguageSkeleton

open Mettapedia.GSLT
open Mettapedia.OSLF.Framework.GrammarDerives
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The syntax half of a future Megalodon port.  `Lexes` is explicit because
byte-to-token correctness is distinct from the grammar derivation. -/
structure SyntaxPort where
  language : LanguageDef
  startSort : String
  Lexes : ByteArray → List String → Prop
  equations_empty : language.equations = []
  rewrites_empty : language.rewrites = []

/-- A Megalodon syntax certificate accounts for both lexical projection and
a derivation in the exact authored syntax `LanguageDef`. -/
structure SyntaxCertificate (syntaxPort : SyntaxPort) (input : ByteArray) where
  tokens : List String
  tree : Pattern
  lexical : syntaxPort.Lexes input tokens
  derivation : Derives syntaxPort.language syntaxPort.startSort tokens tree

/-- The still-language-specific semantic boundary.  An implementation must
supply these carriers and relations rather than hiding them in parser
actions. -/
structure SemanticsPort (syntaxPort : SyntaxPort) where
  State : Type uState
  Claim : Type uClaim
  canonicalState : ByteArray → State
  Lowering : {input : ByteArray} →
    SyntaxCertificate syntaxPort input → State → Prop
  CheckerAccepts : State → Claim → Prop
  DeclarativeAccepts : ByteArray → Claim → Prop

/-- Megalodon's concrete use of the generic checked-language stage
signature.  This is intentionally only a skeleton until the checker laws are
proved. -/
def skeleton (syntaxPort : SyntaxPort)
    (semantics : SemanticsPort syntaxPort) :
    CheckedLanguageSkeleton where
  Input := ByteArray
  SyntaxCertificate := SyntaxCertificate syntaxPort
  SemanticState := semantics.State
  Claim := semantics.Claim
  canonicalState := semantics.canonicalState
  Lowering := semantics.Lowering
  CheckerAccepts := semantics.CheckerAccepts
  DeclarativeAccepts := semantics.DeclarativeAccepts

/-- Positive boundary fact: every admitted syntax certificate contains an
actual derivation in the selected authored root. -/
theorem certificate_derives
    {syntaxPort : SyntaxPort} {input : ByteArray}
    (certificate : SyntaxCertificate syntaxPort input) :
    Derives syntaxPort.language syntaxPort.startSort certificate.tokens
      certificate.tree :=
  certificate.derivation

/-- The two missing crown laws are stated openly.  Supplying this structure,
rather than merely the carrier skeleton, is what earns a full
`CheckedLanguage`. -/
structure AdequatePort (syntaxPort : SyntaxPort)
    extends SemanticsPort syntaxPort where
  lowering_exact : ∀ {input : ByteArray}
    (certificate : SyntaxCertificate syntaxPort input),
      Lowering certificate (canonicalState input)
  checker_adequate : ∀ {input : ByteArray}
    (_certificate : SyntaxCertificate syntaxPort input) (claim : Claim),
      CheckerAccepts (canonicalState input) claim ↔
        DeclarativeAccepts input claim

/-- Once Megalodon supplies its actual lowering and adequacy proofs, the
generic composition theorem is reused without a language-specific reproof. -/
def AdequatePort.toCheckedLanguage
    {syntaxPort : SyntaxPort} (port : AdequatePort syntaxPort) :
    CheckedLanguage where
  toCheckedLanguageSkeleton := skeleton syntaxPort port.toSemanticsPort
  lowering_exact := port.lowering_exact
  checker_adequate := port.checker_adequate

theorem AdequatePort.certificatePipelineAccepts_iff_declarative
    {syntaxPort : SyntaxPort} (port : AdequatePort syntaxPort)
    {input : ByteArray} (certificate : SyntaxCertificate syntaxPort input)
    (claim : port.Claim) :
    (skeleton syntaxPort port.toSemanticsPort).CertificatePipelineAccepts
        certificate claim ↔
      port.DeclarativeAccepts input claim := by
  exact port.toCheckedLanguage.certificatePipelineAccepts_iff_declarative
    certificate claim

/-- Negative boundary fact: declarative truth cannot manufacture a parser
certificate. -/
theorem AdequatePort.not_pipelineAccepts_of_no_syntax
    {syntaxPort : SyntaxPort} (port : AdequatePort syntaxPort)
    {input : ByteArray} {claim : port.Claim}
    (noSyntax : ¬ Nonempty (SyntaxCertificate syntaxPort input)) :
    ¬ (skeleton syntaxPort port.toSemanticsPort).PipelineAccepts input claim := by
  exact port.toCheckedLanguage.not_pipelineAccepts_of_not_parserAccepts
    noSyntax

end Mettapedia.Languages.Megalodon.CheckedLanguageSkeleton
