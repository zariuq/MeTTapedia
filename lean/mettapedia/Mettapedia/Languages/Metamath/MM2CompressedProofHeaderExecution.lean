import Mettapedia.Languages.Metamath.MM2CompressedProofData

/-!
# Incremental compressed-proof header loading in MM2

The loader consumes the source-derived mandatory prefix and explicit label
suffix in order.  It allocates distinct heap and node identities, rejects an
explicit duplicate of a mandatory hypothesis, and releases body scanning only
after the exact header-end position is reached.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofHeaderExecution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2DataEncoding
open Mettapedia.Languages.ProcessCalculi.MORK

private def sinkSurface : Sink → Atom
  | .add atom => .expression [.symbol "+", atom]
  | .remove atom => .expression [.symbol "-", atom]
  | .head count atom =>
      .expression [.symbol "head", natAtom count, atom]
  | .tail count atom =>
      .expression [.symbol "tail", natAtom count, atom]

private def inputSurface (patterns : List Atom) : Atom :=
  .expression (.symbol "," :: patterns)

private def outputSurface (sinks : List Sink) : Atom :=
  .expression (.symbol "O" :: sinks.map sinkSurface)

private def duplicateLocation : Atom :=
  .expression [.symbol "02", .symbol "mm-compressed-header-duplicate"]

private def mandatoryLocation : Atom :=
  .expression [.symbol "03", .symbol "mm-compressed-header-mandatory"]

private def explicitHypothesisLocation : Atom :=
  .expression [.symbol "03", .symbol "mm-compressed-header-hypothesis"]

private def explicitAssertionLocation : Atom :=
  .expression [.symbol "03", .symbol "mm-compressed-header-assertion"]

private def finishLocation : Atom :=
  .expression [.symbol "04", .symbol "mm-compressed-header-finish"]

private def headerControlTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-header-control", .var "scope-owner",
      .var "proof-owner", .var "header-position"]

private def machineTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-machine", .var "scope-owner",
      .var "proof-owner", .var "heap-next", .var "node-next",
      .var "stack-position"]

private def nextMachineTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-machine", .var "scope-owner",
      .var "proof-owner", .var "next-heap", .var "next-node",
      .var "stack-position"]

private def assertionNextMachineTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-machine", .var "scope-owner",
      .var "proof-owner", .var "next-heap", .var "node-next",
      .var "stack-position"]

private def nextHeaderControlTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-header-control", .var "scope-owner",
      .var "proof-owner", .var "next-header-position"]

private def mandatoryRowTemplate : Atom :=
  .expression
    [.symbol "mm-linked-row", stringAtom "compressed-header-item",
      .var "proof-owner", .var "header-position",
      .var "next-header-position",
      .expression
        [.symbol "mm-compressed-header-mandatory",
          .var "hypothesis-label", .var "hypothesis-formula"]]

private def explicitRowTemplate : Atom :=
  .expression
    [.symbol "mm-linked-row", stringAtom "compressed-header-item",
      .var "proof-owner", .var "header-position",
      .var "next-header-position",
      .expression
        [.symbol "mm-compressed-header-explicit", .var "hypothesis-label"]]

private def hypothesisLookupTemplate : Atom :=
  .expression
    [.symbol "mm-hypothesis-lookup", .var "scope-owner",
      .var "hypothesis-label", .var "hypothesis-formula"]

private def assertionHeaderTemplate : Atom :=
  .expression
    [.symbol "mm-assertion-header", .var "scope-owner",
      .var "assertion-position", .var "hypothesis-label",
      .var "assertion-hypothesis-count"]

private def heapSuccessorTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-index-successor",
      .expression [.symbol "mm-compressed-heap-owner", .var "proof-owner"],
      .var "heap-next", .var "next-heap"]

private def nodeSuccessorTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-index-successor",
      .expression [.symbol "mm-compressed-node-owner", .var "proof-owner"],
      .var "node-next", .var "next-node"]

private def headerOccurrenceTemplate : Atom :=
  compressedHeaderOccurrenceSurface (.var "proof-owner")
    (.var "header-position")

private def proofNodeTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-node", .var "proof-owner", .var "node-next",
      .var "hypothesis-formula", headerOccurrenceTemplate]

private def heapProofTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-heap-proof", .var "proof-owner",
      .var "heap-next", .var "node-next"]

private def heapAssertionTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-heap-assertion", .var "proof-owner",
      .var "heap-next", .var "assertion-position",
      .var "hypothesis-label"]

private def mandatoryLabelTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-mandatory-label", .var "proof-owner",
      .var "hypothesis-label"]

private def duplicateFaultTemplate : Atom :=
  .expression
    [.symbol "mm-proof-fault", .var "scope-owner", .var "proof-owner",
      .var "header-position", .symbol "compressed-duplicate-mandatory-label",
      .var "hypothesis-label", .var "hypothesis-label",
      .var "hypothesis-label"]

private def duplicateSelf : Atom :=
  .expression
    [.symbol "exec", duplicateLocation,
      .var "duplicate-input", .var "duplicate-output"]

private def duplicatePatterns : List Atom :=
  [duplicateSelf, headerControlTemplate, explicitRowTemplate,
   mandatoryLabelTemplate]

private def duplicateSinks : List Sink :=
  [.remove headerControlTemplate,
   .add duplicateFaultTemplate]

def compressedHeaderDuplicateRule : Atom :=
  .expression
    [.symbol "exec", duplicateLocation, inputSurface duplicatePatterns,
      outputSurface duplicateSinks]

def compressedHeaderDuplicateDirective : SourceExecFact where
  atom := compressedHeaderDuplicateRule
  loc := duplicateLocation
  rule :=
    { priority := 2
      name := "mm-compressed-header-duplicate"
      input := .compat (mkPattern duplicatePatterns)
      guards := []
      tmpl := mkTemplate duplicateSinks }

theorem extract_compressedHeaderDuplicateRule_exact :
    extractSupportedSourceExecFact compressedHeaderDuplicateRule =
      some compressedHeaderDuplicateDirective := by
  rfl

private def mandatorySelf : Atom :=
  .expression
    [.symbol "exec", mandatoryLocation,
      .var "mandatory-input", .var "mandatory-output"]

private def mandatoryPatterns : List Atom :=
  [mandatorySelf, headerControlTemplate, mandatoryRowTemplate,
   hypothesisLookupTemplate, machineTemplate, heapSuccessorTemplate,
   nodeSuccessorTemplate]

private def mandatorySinks : List Sink :=
  [.add mandatorySelf,
   .remove headerControlTemplate,
   .remove mandatoryRowTemplate,
   .remove machineTemplate,
   .add nextHeaderControlTemplate,
   .add nextMachineTemplate,
   .add proofNodeTemplate,
   .add heapProofTemplate,
   .add mandatoryLabelTemplate]

def compressedHeaderMandatoryRule : Atom :=
  .expression
    [.symbol "exec", mandatoryLocation, inputSurface mandatoryPatterns,
      outputSurface mandatorySinks]

def compressedHeaderMandatoryDirective : SourceExecFact where
  atom := compressedHeaderMandatoryRule
  loc := mandatoryLocation
  rule :=
    { priority := 3
      name := "mm-compressed-header-mandatory"
      input := .compat (mkPattern mandatoryPatterns)
      guards := []
      tmpl := mkTemplate mandatorySinks }

theorem extract_compressedHeaderMandatoryRule_exact :
    extractSupportedSourceExecFact compressedHeaderMandatoryRule =
      some compressedHeaderMandatoryDirective := by
  rfl

private def explicitHypothesisSelf : Atom :=
  .expression
    [.symbol "exec", explicitHypothesisLocation,
      .var "hypothesis-input", .var "hypothesis-output"]

private def explicitHypothesisPatterns : List Atom :=
  [explicitHypothesisSelf, headerControlTemplate, explicitRowTemplate,
   hypothesisLookupTemplate, machineTemplate, heapSuccessorTemplate,
   nodeSuccessorTemplate]

private def explicitHypothesisSinks : List Sink :=
  [.add explicitHypothesisSelf,
   .remove headerControlTemplate,
   .remove explicitRowTemplate,
   .remove machineTemplate,
   .add nextHeaderControlTemplate,
   .add nextMachineTemplate,
   .add proofNodeTemplate,
   .add heapProofTemplate]

def compressedHeaderExplicitHypothesisRule : Atom :=
  .expression
    [.symbol "exec", explicitHypothesisLocation,
      inputSurface explicitHypothesisPatterns,
      outputSurface explicitHypothesisSinks]

def compressedHeaderExplicitHypothesisDirective : SourceExecFact where
  atom := compressedHeaderExplicitHypothesisRule
  loc := explicitHypothesisLocation
  rule :=
    { priority := 3
      name := "mm-compressed-header-hypothesis"
      input := .compat (mkPattern explicitHypothesisPatterns)
      guards := []
      tmpl := mkTemplate explicitHypothesisSinks }

theorem extract_compressedHeaderExplicitHypothesisRule_exact :
    extractSupportedSourceExecFact compressedHeaderExplicitHypothesisRule =
      some compressedHeaderExplicitHypothesisDirective := by
  rfl

private def explicitAssertionSelf : Atom :=
  .expression
    [.symbol "exec", explicitAssertionLocation,
      .var "assertion-input", .var "assertion-output"]

private def explicitAssertionPatterns : List Atom :=
  [explicitAssertionSelf, headerControlTemplate, explicitRowTemplate,
   assertionHeaderTemplate, machineTemplate, heapSuccessorTemplate]

private def explicitAssertionSinks : List Sink :=
  [.add explicitAssertionSelf,
   .remove headerControlTemplate,
   .remove explicitRowTemplate,
   .remove machineTemplate,
   .add nextHeaderControlTemplate,
   .add assertionNextMachineTemplate,
   .add heapAssertionTemplate]

def compressedHeaderExplicitAssertionRule : Atom :=
  .expression
    [.symbol "exec", explicitAssertionLocation,
      inputSurface explicitAssertionPatterns,
      outputSurface explicitAssertionSinks]

def compressedHeaderExplicitAssertionDirective : SourceExecFact where
  atom := compressedHeaderExplicitAssertionRule
  loc := explicitAssertionLocation
  rule :=
    { priority := 3
      name := "mm-compressed-header-assertion"
      input := .compat (mkPattern explicitAssertionPatterns)
      guards := []
      tmpl := mkTemplate explicitAssertionSinks }

theorem extract_compressedHeaderExplicitAssertionRule_exact :
    extractSupportedSourceExecFact compressedHeaderExplicitAssertionRule =
      some compressedHeaderExplicitAssertionDirective := by
  rfl

private def headerEndTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-header-end", .var "proof-owner",
      .var "header-position"]

private def bodyControlTemplate : Atom :=
  .expression
    [.symbol "mm-compressed-control", .var "scope-owner",
      .var "proof-owner", natAtom 0, .var "stack-position"]

private def finishSelf : Atom :=
  .expression
    [.symbol "exec", finishLocation,
      .var "finish-input", .var "finish-output"]

private def finishPatterns : List Atom :=
  [finishSelf, headerControlTemplate, headerEndTemplate, machineTemplate]

private def finishSinks : List Sink :=
  [.remove headerControlTemplate,
   .remove headerEndTemplate,
   .add bodyControlTemplate]

def compressedHeaderFinishRule : Atom :=
  .expression
    [.symbol "exec", finishLocation, inputSurface finishPatterns,
      outputSurface finishSinks]

def compressedHeaderFinishDirective : SourceExecFact where
  atom := compressedHeaderFinishRule
  loc := finishLocation
  rule :=
    { priority := 4
      name := "mm-compressed-header-finish"
      input := .compat (mkPattern finishPatterns)
      guards := []
      tmpl := mkTemplate finishSinks }

theorem extract_compressedHeaderFinishRule_exact :
    extractSupportedSourceExecFact compressedHeaderFinishRule =
      some compressedHeaderFinishDirective := by
  rfl

def compressedHeaderRules : List Atom :=
  [compressedHeaderDuplicateRule, compressedHeaderMandatoryRule,
   compressedHeaderExplicitHypothesisRule,
   compressedHeaderExplicitAssertionRule, compressedHeaderFinishRule]

def compressedHeaderDirectives : List SourceExecFact :=
  [compressedHeaderDuplicateDirective, compressedHeaderMandatoryDirective,
   compressedHeaderExplicitHypothesisDirective,
   compressedHeaderExplicitAssertionDirective,
   compressedHeaderFinishDirective]

theorem compressedHeaderRules_extract_exact :
    compressedHeaderRules.filterMap extractSupportedSourceExecFact =
      compressedHeaderDirectives := by
  rfl

/-- Header loading followed by the incremental compact-body microkernel.
This is an inventory composition, not yet a claim of whole-verifier
completeness. -/
def compressedVerifierRulesWithHeader : List Atom :=
  compressedHeaderRules ++ compressedVerifierRules

#print axioms extract_compressedHeaderDuplicateRule_exact
#print axioms extract_compressedHeaderMandatoryRule_exact
#print axioms extract_compressedHeaderExplicitHypothesisRule_exact
#print axioms extract_compressedHeaderExplicitAssertionRule_exact
#print axioms extract_compressedHeaderFinishRule_exact
#print axioms compressedHeaderRules_extract_exact

end Mettapedia.Languages.Metamath.MM2CompressedProofHeaderExecution
