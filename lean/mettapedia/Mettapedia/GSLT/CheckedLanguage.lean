/-!
# Proof-carrying checked-language composition

This module separates four stages that are often conflated:

* a syntax certificate produced for an input;
* a lowering relation from that certificate to a semantic state;
* an executable checker judgment over the semantic state;
* an independent declarative judgment over the input.

`CheckedLanguage` adds two laws to this signature: every admitted syntax
certificate lowers to the canonical semantic state, and checker acceptance at
that state is equivalent to the declarative judgment.  The laws are indexed
by an existing syntax certificate; they do not claim that every byte string
has a parse.
-/

set_option autoImplicit false

universe uInput uCertificate uState uClaim

namespace Mettapedia.GSLT

/-- The carrier-level signature of a proof-carrying parser/checker pipeline.
It intentionally contains no correctness laws, so incomplete language ports
can use it without being mislabeled as checked languages. -/
structure CheckedLanguageSkeleton where
  Input : Type uInput
  SyntaxCertificate : Input → Type uCertificate
  SemanticState : Type uState
  Claim : Type uClaim
  canonicalState : Input → SemanticState
  Lowering : {input : Input} →
    SyntaxCertificate input → SemanticState → Prop
  CheckerAccepts : SemanticState → Claim → Prop
  DeclarativeAccepts : Input → Claim → Prop

namespace CheckedLanguageSkeleton

def ParserAccepts (language : CheckedLanguageSkeleton)
    (input : language.Input) : Prop :=
  Nonempty (language.SyntaxCertificate input)

def CertificatePipelineAccepts (language : CheckedLanguageSkeleton)
    {input : language.Input} (certificate : language.SyntaxCertificate input)
    (claim : language.Claim) : Prop :=
  language.Lowering certificate (language.canonicalState input) ∧
    language.CheckerAccepts (language.canonicalState input) claim

def PipelineAccepts (language : CheckedLanguageSkeleton)
    (input : language.Input) (claim : language.Claim) : Prop :=
  ∃ certificate : language.SyntaxCertificate input,
    language.CertificatePipelineAccepts certificate claim

end CheckedLanguageSkeleton

/-- A checked-language composition.  The operational/declarative theorem is
certificate-indexed because parser completeness is a distinct property from
checker adequacy. -/
structure CheckedLanguage extends CheckedLanguageSkeleton where
  lowering_exact : ∀ {input : Input}
    (certificate : SyntaxCertificate input),
      Lowering certificate (canonicalState input)
  checker_adequate : ∀ {input : Input}
    (_certificate : SyntaxCertificate input) (claim : Claim),
      CheckerAccepts (canonicalState input) claim ↔
        DeclarativeAccepts input claim

namespace CheckedLanguage

/-- The commuting-square theorem for one concrete syntax certificate. -/
theorem certificatePipelineAccepts_iff_declarative
    (language : CheckedLanguage)
    {input : language.Input}
    (certificate : language.SyntaxCertificate input)
    (claim : language.Claim) :
    language.toCheckedLanguageSkeleton.CertificatePipelineAccepts
        certificate claim ↔
      language.DeclarativeAccepts input claim := by
  constructor
  · intro accepted
    exact (language.checker_adequate certificate claim).mp accepted.2
  · intro accepted
    exact ⟨language.lowering_exact certificate,
      (language.checker_adequate certificate claim).mpr accepted⟩

/-- A whole pipeline accepts exactly when a parser certificate exists and
the declarative judgment holds.  This theorem does not manufacture a parser
certificate from semantic provability. -/
theorem pipelineAccepts_iff_parserAccepts_and_declarative
    (language : CheckedLanguage)
    (input : language.Input) (claim : language.Claim) :
    language.toCheckedLanguageSkeleton.PipelineAccepts input claim ↔
      language.toCheckedLanguageSkeleton.ParserAccepts input ∧
        language.DeclarativeAccepts input claim := by
  constructor
  · rintro ⟨certificate, accepted⟩
    exact ⟨⟨certificate⟩,
      (language.certificatePipelineAccepts_iff_declarative
        certificate claim).mp accepted⟩
  · rintro ⟨⟨certificate⟩, accepted⟩
    exact ⟨certificate,
      (language.certificatePipelineAccepts_iff_declarative
        certificate claim).mpr accepted⟩

/-- Negative boundary example: semantic truth alone cannot make the pipeline
accept when no syntax certificate exists. -/
theorem not_pipelineAccepts_of_not_parserAccepts
    (language : CheckedLanguage)
    {input : language.Input} {claim : language.Claim}
    (noParser : ¬ language.toCheckedLanguageSkeleton.ParserAccepts input) :
    ¬ language.toCheckedLanguageSkeleton.PipelineAccepts input claim := by
  intro accepted
  exact noParser <|
    (language.pipelineAccepts_iff_parserAccepts_and_declarative
      input claim).mp accepted |>.1

end CheckedLanguage

end Mettapedia.GSLT
