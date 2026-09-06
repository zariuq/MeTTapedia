import Mettapedia.Languages.SUMO.Native.NIKAuthority
import Mettapedia.Languages.SUMO.Native.DomainGuardElaboration

/-!
# Finite native SUMO theories assembled from SUO-KIF source

This module retains source identity and spans while elaborating complete
SUO-KIF files into closed native formulas.  The combined declaration inventory
determines formula-valued argument positions, subclass and subrelation
inheritance, and implicit object/row domain restrictions before any file is
elaborated.  Every lexical, structural, declaration, elaboration, and
unresolved-domain failure remains an explicit source-located issue.

The resulting ordered sentence list is the exact assumption context consumed
by the contextual native SUMO NIK authority.  Source membership licenses the
hypothesis rule; it does not assert consistency or intended truth.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.SUMO.Native.SourceTheory

open Mettapedia.Languages.SUMO.Native
open Mettapedia.Languages.SUMO.Native.SourceElaboration

/-- One named SUO-KIF source text.  The identifier need not be a file path. -/
structure SourceText where
  sourceId : String
  text : String
  deriving Repr

/-- Stable source identity and exact span of an elaborated sentence. -/
structure Origin where
  sourceId : String
  span : KIF.SourceSpan
  deriving DecidableEq, Repr

/-- One source-located closed formula in the native SUMO calculus. -/
structure Entry where
  origin : Origin
  sentence : Sentence String String
  deriving DecidableEq, Repr

inductive IssueKind where
  | lexical (kind : KIF.LexErrorKind)
  | structural (kind : KIF.ParseErrorKind)
  | declaration (kind : KIF.DeclarationErrorKind)
  | elaboration (kind : ElaborationIssueKind)
  | domainGuard (kind : DomainGuardElaboration.GuardIssueKind)
  deriving DecidableEq, Repr

structure Issue where
  origin : Origin
  kind : IssueKind
  deriving DecidableEq, Repr

/-- A finite native theory together with the signature facts used during
elaboration and every source-located issue. -/
structure Theory where
  signature : SourceSignature
  entries : List Entry
  issues : List Issue
  deriving Repr

namespace Theory

/-- The exact ordered context consumed by native derivations. -/
def assumptions (theory : Theory) : List NIKAuthority.Claim :=
  theory.entries.map Entry.sentence

/-- Whether every supplied source passed every assembly phase. -/
def clean (theory : Theory) : Bool :=
  theory.issues.isEmpty

/-- Ask for one consequence of this exact finite source theory. -/
def entailmentClaim (theory : Theory) (conclusion : NIKAuthority.Claim) :
    NIKAuthority.EntailmentClaim :=
  { assumptions := theory.assumptions
    conclusion := conclusion }

theorem entry_sentence_mem_assumptions
    {theory : Theory} {entry : Entry} (member : entry ∈ theory.entries) :
    entry.sentence ∈ theory.assumptions := by
  exact List.mem_map.mpr ⟨entry, member, rfl⟩

/-- Every source entry is accepted through the native hypothesis rule with
its source theory retained as the exact context. -/
theorem entry_has_native_nikEvidence
    {theory : Theory} {entry : Entry} (member : entry ∈ theory.entries) :
    Nonempty
      (NIKAuthority.EntailmentNIKEvidence
        (theory.entailmentClaim entry.sentence)) := by
  apply (NIKAuthority.nonempty_entailmentEvidence_iff_derivable _).mpr
  exact .hypothesis (entry_sentence_mem_assumptions member)

end Theory

private structure ParsedUnit where
  sourceId : String
  parsed : KIF.Parsed
  declarations : List KIF.SuoDeclaration

private def issue
    (sourceId : String) (span : KIF.SourceSpan) (kind : IssueKind) : Issue :=
  ⟨⟨sourceId, span⟩, kind⟩

private def parseSource (source : SourceText) :
    Option ParsedUnit × List Issue :=
  match KIF.lex source.text with
  | .error failure =>
      (none, [issue source.sourceId failure.span (.lexical failure.kind)])
  | .ok lexed =>
      let parsed := KIF.parse lexed
      let inventory := KIF.declarationInventory parsed
      let structuralIssues := parsed.errors.map fun failure =>
        issue source.sourceId failure.span (.structural failure.kind)
      let declarationIssues := inventory.errors.map fun failure =>
        issue source.sourceId failure.span (.declaration failure.kind)
      (some ⟨source.sourceId, parsed, inventory.declarations⟩,
        structuralIssues ++ declarationIssues)

private def parseSources :
    List SourceText -> List ParsedUnit × List Issue
  | [] => ([], [])
  | source :: rest =>
      let (unit, sourceIssues) := parseSource source
      let (units, restIssues) := parseSources rest
      let allUnits := match unit with
        | some parsed => parsed :: units
        | none => units
      (allUnits, sourceIssues ++ restIssues)

private def elaborateForms
    (signature : SourceSignature) (sourceId : String) :
    List KIF.Term -> List Entry × List Issue
  | [] => ([], [])
  | source :: rest =>
      let (entries, issues) := elaborateForms signature sourceId rest
      match DomainGuardElaboration.elaborateSentence signature source with
      | .ok result =>
          let guardIssues := result.issues.map fun guardIssue =>
            issue sourceId source.span (.domainGuard guardIssue)
          (⟨⟨sourceId, source.span⟩, result.sentence⟩ :: entries,
            guardIssues ++ issues)
      | .error failure =>
          (entries,
            issue sourceId failure.span (.elaboration failure.kind) :: issues)

private def elaborateUnits
    (signature : SourceSignature) :
    List ParsedUnit -> List Entry × List Issue
  | [] => ([], [])
  | unit :: rest =>
      let (sourceEntries, sourceIssues) :=
        elaborateForms signature unit.sourceId unit.parsed.forms
      let (restEntries, restIssues) := elaborateUnits signature rest
      (sourceEntries ++ restEntries, sourceIssues ++ restIssues)

/-- Parse all sources, derive their combined formula-argument signature, and
elaborate every recoverable top-level form into the native calculus. -/
def assemble (sources : List SourceText) : Theory :=
  let (units, initialIssues) := parseSources sources
  let declarations := units.flatMap ParsedUnit.declarations
  let forms := units.flatMap fun unit => unit.parsed.forms
  let signature := SourceSignature.ofDeclarationsAndForms declarations forms
  let (entries, elaborationIssues) := elaborateUnits signature units
  { signature := signature
    entries := entries
    issues := initialIssues ++ elaborationIssues }

/-! ## Negative control -/

def emptyClaim : NIKAuthority.EntailmentClaim :=
  { assumptions := []
    conclusion := .top }

/-- A hypothesis certificate cannot manufacture an assumption in an empty
source theory. -/
theorem empty_source_hypothesis_rejected :
    NIKAuthority.entailmentChecker.check emptyClaim
      (.hypothesis 0 : NIKAuthority.Evidence) = false := by
  decide

end Mettapedia.Languages.SUMO.Native.SourceTheory
