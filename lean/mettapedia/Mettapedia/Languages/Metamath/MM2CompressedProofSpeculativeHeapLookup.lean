import Mettapedia.Languages.Metamath.MM2CompressedProofExecution
import Mettapedia.Languages.ProcessCalculi.MORK.SpeculativeLookupRuleSurface

/-!
# Speculative compressed-heap lookup in the generated MM2 verifier

This module applies the reusable strict MM2 surface transformation to the
actual finite compressed-proof verifier presentation.  The target presentation
retains its cursor proof and assertion handlers and derives two one-shot direct
handlers from those supplied rules.

At each terminal compact index the transformed terminal rule reinstalls the
direct handlers.  A direct proof or assertion cell therefore resolves without
walking from cursor zero.  When neither direct handler matches, both executable
occurrences are consumed without changing the lookup request and the retained
cursor machine continues exactly as before.

The compact source-data transform is unchanged.  In particular, no compressed
proof is decompressed or verified by the translator.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookup

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReloadingRuleSurface
open Mettapedia.Languages.ProcessCalculi.MORK.SpeculativeLookupRuleSurface

/-! ## Target surface profile -/

private def exactCursorLookupPremise : Atom :=
  .expression
    [.symbol "mm-compressed-heap-lookup", .var "scope-owner",
      .var "proof-owner", .var "word-position", .var "remaining-bytes",
      .var "compressed-index", .var "compressed-index"]

private def directLookupPremise : Atom :=
  .expression
    [.symbol "mm-compressed-heap-lookup", .var "scope-owner",
      .var "proof-owner", .var "word-position", .var "remaining-bytes",
      .var "compressed-index", .var "speculative-cursor"]

private def directProofLocation : Atom :=
  .expression [.symbol "00", .symbol "mm-compressed-direct-0-proof"]

private def directAssertionLocation : Atom :=
  .expression [.symbol "00", .symbol "mm-compressed-direct-1-assertion"]

private def directProofCaptureVariable : Atom :=
  .var "compressed-direct-proof-handler"

private def directAssertionCaptureVariable : Atom :=
  .var "compressed-direct-assertion-handler"

private def directProofCaptureRow : Atom :=
  .expression
    [.symbol "mm-compressed-owned-speculative-lookup-handler",
      .symbol "proof", directProofCaptureVariable]

private def directAssertionCaptureRow : Atom :=
  .expression
    [.symbol "mm-compressed-owned-speculative-lookup-handler",
      .symbol "assertion", directAssertionCaptureVariable]

def compressedSpeculativeLookupProfile : Profile where
  exactLookupPremise := exactCursorLookupPremise
  directLookupPremise := directLookupPremise
  directProofLocation := directProofLocation
  directOpaqueLocation := directAssertionLocation
  directProofCaptureRow := directProofCaptureRow
  directProofCaptureVariable := directProofCaptureVariable
  directOpaqueCaptureRow := directAssertionCaptureRow
  directOpaqueCaptureVariable := directAssertionCaptureVariable

/-! ## Transformation of the supplied verifier presentation -/

def compressedSpeculativeLookupSelection : Selection where
  terminalPosition := 5
  proofPosition := 6
  opaquePosition := 7

private theorem compressedSpeculativeLookup_buildable :
    (buildSelectedStrict? compressedSpeculativeLookupProfile
      compressedSpeculativeLookupSelection compressedVerifierRules).isSome =
        true := by
  decide +kernel

def compressedSpeculativeLookupSelectedArtifact :
    SpeculativeLookupRuleSurface.SelectedArtifact :=
  (buildSelectedStrict? compressedSpeculativeLookupProfile
    compressedSpeculativeLookupSelection compressedVerifierRules).get
      (by simpa using compressedSpeculativeLookup_buildable)

/-- Exact computational receipt for the strict positional compiler. -/
theorem compressedSpeculativeLookup_build_exact :
    buildSelectedStrict? compressedSpeculativeLookupProfile
        compressedSpeculativeLookupSelection compressedVerifierRules =
      some compressedSpeculativeLookupSelectedArtifact := by
  unfold compressedSpeculativeLookupSelectedArtifact
  exact
    (Option.some_get (by simpa using compressedSpeculativeLookup_buildable)).symm

def compressedSpeculativeLookupArtifact :
    SpeculativeLookupRuleSurface.Artifact :=
  compressedSpeculativeLookupSelectedArtifact.artifact

/-- The transformation consumes the complete supplied verifier presentation,
not a separately selected or reconstructed rule list. -/
theorem compressedSpeculativeLookupArtifact_sourceRules :
    compressedSpeculativeLookupArtifact.sourceRules =
      compressedVerifierRules := by
  rfl

/-- The three occurrence positions select the authored terminal, proof-cell,
and assertion-cell handlers from the supplied verifier presentation. -/
theorem compressedSpeculativeLookup_selection_exact :
    compressedSpeculativeLookupArtifact.sourceTerminalRule =
        compressedTerminalRule ∧
      compressedSpeculativeLookupArtifact.sourceProofRule =
        compressedProofStepRule ∧
      compressedSpeculativeLookupArtifact.sourceOpaqueRule =
        compressedAssertionLaunchRule := by
  decide +kernel

/-- Exactly two direct-handler occurrences are added; every supplied rule
occurrence, including duplicates, remains represented in the target. -/
theorem compressedSpeculativeLookupArtifact_target_length :
    compressedSpeculativeLookupArtifact.targetRules.length =
      compressedVerifierRules.length + 2 := by
  rfl

def compressedDirectProofRule : Atom :=
  compressedSpeculativeLookupArtifact.directProofRule

def compressedDirectAssertionRule : Atom :=
  compressedSpeculativeLookupArtifact.directOpaqueRule

def compressedSpeculativeTerminalRule : Atom :=
  compressedSpeculativeLookupArtifact.targetTerminalRule

/-- The transformed finite inventory has one strict terminal replacement,
contains both derived handlers, and retains both original cursor handlers. -/
theorem compressedSpeculativeLookup_inventory_exact :
    compressedTerminalRule ∉ compressedSpeculativeLookupArtifact.targetRules ∧
      compressedSpeculativeTerminalRule ∈
        compressedSpeculativeLookupArtifact.targetRules ∧
      compressedDirectProofRule ∈
        compressedSpeculativeLookupArtifact.targetRules ∧
      compressedDirectAssertionRule ∈
        compressedSpeculativeLookupArtifact.targetRules ∧
      compressedProofStepRule ∈
        compressedSpeculativeLookupArtifact.targetRules ∧
      compressedAssertionLaunchRule ∈
        compressedSpeculativeLookupArtifact.targetRules := by
  decide +kernel

/-! ## Persistent code rows -/

def sourceTerminalCaptureRow : Atom :=
  compressedOwnedRuntimeRuleRow "terminal" compressedTerminalRule

def targetTerminalCaptureRow : Atom :=
  compressedOwnedRuntimeRuleRow "terminal" compressedSpeculativeTerminalRule

def compressedDirectProofHandlerRow : Atom :=
  .expression
    [.symbol "mm-compressed-owned-speculative-lookup-handler",
      .symbol "proof", compressedDirectProofRule]

def compressedDirectAssertionHandlerRow : Atom :=
  .expression
    [.symbol "mm-compressed-owned-speculative-lookup-handler",
      .symbol "assertion", compressedDirectAssertionRule]

private theorem compressedSpeculativeStaticRows_replaceable :
    (replaceExactlyOne? sourceTerminalCaptureRow targetTerminalCaptureRow
      compressedVerifierStaticRows).isSome =
        true := by
  rfl

def compressedSpeculativeStaticRowsBase : List Atom :=
  (replaceExactlyOne? sourceTerminalCaptureRow targetTerminalCaptureRow
    compressedVerifierStaticRows).get
      (by simpa using compressedSpeculativeStaticRows_replaceable)

/-- Exact receipt for the single persistent-row replacement. -/
theorem compressedSpeculativeStaticRowsBase_build_exact :
    replaceExactlyOne? sourceTerminalCaptureRow targetTerminalCaptureRow
        compressedVerifierStaticRows =
      some compressedSpeculativeStaticRowsBase := by
  unfold compressedSpeculativeStaticRowsBase
  exact
    (Option.some_get
      (by simpa using compressedSpeculativeStaticRows_replaceable)).symm

/-- Persistent verifier-owned rows install the transformed terminal and supply
the two opaque one-shot handlers it captures.  Cursor reload rows are retained
unchanged and deliberately do not reinstall direct probes during fallback. -/
def compressedVerifierStaticRowsWithSpeculativeLookup : List Atom :=
  compressedSpeculativeStaticRowsBase ++
    [compressedDirectProofHandlerRow, compressedDirectAssertionHandlerRow]

/-- The two injected handler rows are mutually distinct and fresh for the
authored persistent verifier inventory. -/
theorem compressedDirectHandlerRows_fresh :
    compressedDirectProofHandlerRow ∉ compressedVerifierStaticRows ∧
      compressedDirectAssertionHandlerRow ∉ compressedVerifierStaticRows ∧
      compressedDirectProofHandlerRow != compressedDirectAssertionHandlerRow := by
  decide +kernel

theorem compressedVerifierStaticRowsWithSpeculativeLookup_exact :
    sourceTerminalCaptureRow ∉
        compressedVerifierStaticRowsWithSpeculativeLookup ∧
      targetTerminalCaptureRow ∈
        compressedVerifierStaticRowsWithSpeculativeLookup ∧
      compressedDirectProofHandlerRow ∈
        compressedVerifierStaticRowsWithSpeculativeLookup ∧
      compressedDirectAssertionHandlerRow ∈
        compressedVerifierStaticRowsWithSpeculativeLookup := by
  decide +kernel

#print axioms compressedSpeculativeLookupArtifact_sourceRules
#print axioms compressedSpeculativeLookup_build_exact
#print axioms compressedSpeculativeLookup_selection_exact
#print axioms compressedSpeculativeLookupArtifact_target_length
#print axioms compressedSpeculativeLookup_inventory_exact
#print axioms compressedVerifierStaticRowsWithSpeculativeLookup_exact
#print axioms compressedSpeculativeStaticRowsBase_build_exact
#print axioms compressedDirectHandlerRows_fresh

end Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookup
