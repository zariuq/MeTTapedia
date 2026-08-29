import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookup

/-!
# Compiler adapter for speculative compressed-verifier lookup

This module exposes the concrete, independently executable presentation pass
used by the MM-to-MM2 compiler.  It accepts a supplied compressed-verifier
body and its supplied persistent code rows.  It returns the transformed body
and persistent rows or fails closed when the expected terminal/proof/assertion
surface is absent, duplicated, or malformed.

The source-data transformation remains unchanged.  Compact proof bytes and
heap rows stay dynamic input; this pass transforms verifier code only.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativePresentation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookup
open Mettapedia.Languages.ProcessCalculi.MORK.SpeculativeLookupRuleSurface

/-! ## Input-sensitive compiler artifact -/

structure CompiledPresentation where
  selected : SelectedArtifact
  sourceStaticRows : List Atom
  targetStaticRows : List Atom
deriving DecidableEq

def CompiledPresentation.sourceRules
    (artifact : CompiledPresentation) : List Atom :=
  artifact.selected.artifact.sourceRules

def CompiledPresentation.targetRules
    (artifact : CompiledPresentation) : List Atom :=
  artifact.selected.artifact.targetRules

private def terminalCaptureRow (rule : Atom) : Atom :=
  compressedOwnedRuntimeRuleRow "terminal" rule

private def directProofHandlerRow (rule : Atom) : Atom :=
  .expression
    [.symbol "mm-compressed-owned-speculative-lookup-handler",
      .symbol "proof", rule]

private def directAssertionHandlerRow (rule : Atom) : Atom :=
  .expression
    [.symbol "mm-compressed-owned-speculative-lookup-handler",
      .symbol "assertion", rule]

/-- Transform supplied compact-verifier code and persistent code rows.  The
function does not inspect filenames, source labels, proof bytes, or expected
verdicts. -/
def transformCompressedVerifierPresentation?
    (sourceRules sourceStaticRows : List Atom) :
    Option CompiledPresentation := do
  let selected <-
    buildSelectedStrict? compressedSpeculativeLookupProfile
      compressedSpeculativeLookupSelection sourceRules
  let artifact := selected.artifact
  let proofHandler := directProofHandlerRow artifact.directProofRule
  let assertionHandler := directAssertionHandlerRow artifact.directOpaqueRule
  if proofHandler ∈ sourceStaticRows then none
  else if assertionHandler ∈ sourceStaticRows then none
  else if proofHandler == assertionHandler then none
  else do
    let retainedRows <-
      replaceExactlyOne? (terminalCaptureRow artifact.sourceTerminalRule)
        (terminalCaptureRow artifact.targetTerminalRule) sourceStaticRows
    let targetStaticRows := retainedRows ++
      [proofHandler, assertionHandler]
    pure { selected, sourceStaticRows, targetStaticRows }

/-- Every successful result retains the exact supplied rule presentation as
its source.  This is the input-sensitivity boundary used by downstream
compiler composition. -/
theorem transformCompressedVerifierPresentation?_sourceRules
    {sourceRules sourceStaticRows : List Atom}
    {output : CompiledPresentation}
    (built : transformCompressedVerifierPresentation?
      sourceRules sourceStaticRows = some output) :
    output.sourceRules = sourceRules := by
  rw [transformCompressedVerifierPresentation?] at built
  obtain ⟨selected, selectedBuilt, built⟩ :=
    Option.bind_eq_some_iff.mp built
  dsimp only at built
  split at built
  · simp at built
  · split at built
    · simp at built
    · split at built
      · simp at built
      · obtain ⟨retainedRows, _rowsBuilt, built⟩ :=
          Option.bind_eq_some_iff.mp built
        cases built
        exact
          Mettapedia.Languages.ProcessCalculi.MORK.SpeculativeLookupRuleSurface.buildSelectedStrict?_sourceRules
            compressedSpeculativeLookupProfile compressedSpeculativeLookupSelection
            sourceRules selected selectedBuilt

/-- A successful presentation transform preserves the supplied rule
occurrences and adds exactly the two derived direct-handler occurrences. -/
theorem transformCompressedVerifierPresentation?_targetRules_length
    {sourceRules sourceStaticRows : List Atom}
    {output : CompiledPresentation}
    (built : transformCompressedVerifierPresentation?
      sourceRules sourceStaticRows = some output) :
    output.targetRules.length = sourceRules.length + 2 := by
  rw [transformCompressedVerifierPresentation?] at built
  obtain ⟨selected, selectedBuilt, built⟩ :=
    Option.bind_eq_some_iff.mp built
  dsimp only at built
  split at built
  · simp at built
  · split at built
    · simp at built
    · split at built
      · simp at built
      · obtain ⟨retainedRows, _rowsBuilt, built⟩ :=
          Option.bind_eq_some_iff.mp built
        cases built
        exact
          Mettapedia.Languages.ProcessCalculi.MORK.SpeculativeLookupRuleSurface.buildSelectedStrict?_targetRules_length
            compressedSpeculativeLookupProfile compressedSpeculativeLookupSelection
            sourceRules selected selectedBuilt

/-! ## Exact base-instance controls -/

/-- Independently stated expected result for the maintained compact-verifier
presentation.  The theorem below checks the compiler against this record. -/
def baseCompiledPresentation : CompiledPresentation where
  selected := compressedSpeculativeLookupSelectedArtifact
  sourceStaticRows := compressedVerifierStaticRows
  targetStaticRows := compressedVerifierStaticRowsWithSpeculativeLookup

theorem transformCompressedVerifierPresentation?_base_exact :
    transformCompressedVerifierPresentation? compressedVerifierRules
      compressedVerifierStaticRows = some baseCompiledPresentation := by
  have proofFresh :
      directProofHandlerRow
          compressedSpeculativeLookupSelectedArtifact.artifact.directProofRule ∉
        compressedVerifierStaticRows := by
    simpa [directProofHandlerRow, compressedDirectProofHandlerRow,
      compressedDirectProofRule, compressedSpeculativeLookupArtifact] using
      compressedDirectHandlerRows_fresh.1
  have assertionFresh :
      directAssertionHandlerRow
          compressedSpeculativeLookupSelectedArtifact.artifact.directOpaqueRule ∉
        compressedVerifierStaticRows := by
    simpa [directAssertionHandlerRow, compressedDirectAssertionHandlerRow,
      compressedDirectAssertionRule, compressedSpeculativeLookupArtifact] using
      compressedDirectHandlerRows_fresh.2.1
  have handlersDistinct :
      directProofHandlerRow
          compressedSpeculativeLookupSelectedArtifact.artifact.directProofRule !=
        directAssertionHandlerRow
          compressedSpeculativeLookupSelectedArtifact.artifact.directOpaqueRule := by
    change compressedDirectProofHandlerRow != compressedDirectAssertionHandlerRow
    exact compressedDirectHandlerRows_fresh.2.2
  have handlersDoNotCollide :
      ¬ (directProofHandlerRow
            compressedSpeculativeLookupSelectedArtifact.artifact.directProofRule ==
          directAssertionHandlerRow
            compressedSpeculativeLookupSelectedArtifact.artifact.directOpaqueRule) =
        true := by
    intro collide
    simp [bne, collide] at handlersDistinct
  rw [transformCompressedVerifierPresentation?,
    compressedSpeculativeLookup_build_exact]
  simp only [bind, Option.bind]
  rw [if_neg proofFresh, if_neg assertionFresh]
  rw [if_neg handlersDoNotCollide]
  rw [show
    replaceExactlyOne?
        (terminalCaptureRow
          compressedSpeculativeLookupSelectedArtifact.artifact.sourceTerminalRule)
        (terminalCaptureRow
          compressedSpeculativeLookupSelectedArtifact.artifact.targetTerminalRule)
        compressedVerifierStaticRows =
      some compressedSpeculativeStaticRowsBase by
    change
      replaceExactlyOne?
          (terminalCaptureRow
            compressedSpeculativeLookupArtifact.sourceTerminalRule)
          (terminalCaptureRow
            compressedSpeculativeLookupArtifact.targetTerminalRule)
          compressedVerifierStaticRows =
        some compressedSpeculativeStaticRowsBase
    rw [compressedSpeculativeLookup_selection_exact.1]
    change
      replaceExactlyOne?
          (terminalCaptureRow compressedTerminalRule)
          (terminalCaptureRow compressedSpeculativeTerminalRule)
          compressedVerifierStaticRows =
        some compressedSpeculativeStaticRowsBase
    simpa [terminalCaptureRow, sourceTerminalCaptureRow,
      targetTerminalCaptureRow] using
      compressedSpeculativeStaticRowsBase_build_exact]
  rfl

/-- The source side of the compiler artifact is the supplied verifier rule
list, not a separately reconstructed inventory. -/
theorem baseCompiledPresentation_sourceRules :
    baseCompiledPresentation.sourceRules = compressedVerifierRules := by
  rfl

/-- The compiler's target rule list is exactly the already-qualified concrete
speculative transform. -/
theorem baseCompiledPresentation_targetRules :
    baseCompiledPresentation.targetRules =
      compressedSpeculativeLookupArtifact.targetRules := by
  rfl

/-- Its persistent rows are exactly the target terminal replacement followed
by the two derived handler rows. -/
theorem baseCompiledPresentation_targetStaticRows :
    baseCompiledPresentation.targetStaticRows =
      compressedVerifierStaticRowsWithSpeculativeLookup := by
  rfl

/-- A rule inventory without its matching persistent terminal capture is
rejected instead of producing a partially wired target. -/
theorem missing_terminal_capture_is_rejected :
    transformCompressedVerifierPresentation? compressedVerifierRules [] =
      none := by
  rfl

#print axioms baseCompiledPresentation_sourceRules
#print axioms transformCompressedVerifierPresentation?_sourceRules
#print axioms transformCompressedVerifierPresentation?_targetRules_length
#print axioms transformCompressedVerifierPresentation?_base_exact
#print axioms baseCompiledPresentation_targetRules
#print axioms baseCompiledPresentation_targetStaticRows
#print axioms missing_terminal_capture_is_rejected

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativePresentation
