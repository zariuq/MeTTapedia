/-!
# GF Authority Audit

Manual classification of the remaining GF modules after the syntax-only
authority split.

This file is intentionally lightweight: the lists are the maintained audit
surface that tells us which modules are candidates for immediate retargeting
to the real `GFCore.check` / PGF-witness lane, which ones remain legacy
semantic research, and which ones are plausible purge candidates if we decide
to simplify the tree further.
-/

namespace Mettapedia.Languages.GF.GFAuthorityAudit

/-- Real generated GF syntax slices currently present in-tree. -/
def generatedSyntaxSlicesInTree : List String :=
  [ "PaperAmbiguity" ]

/-- The current grounded coverage boundary is exactly the generated witness
    languages present for `PaperAmbiguity`. This is the "do as much as there is
    Czech grammar" line: expand when more real Czech-generated material exists,
    not by inventing semantics. -/
def groundedCoverageBoundaryLanguages : List String :=
  [ "PaperAmbiguityEng"
  , "PaperAmbiguityCze"
  ]

/-- Legacy consumers that look worth retargeting to the real checked/witnessed
    GF path now, because their claim surface is mostly diagnostic/example-level. -/
def realGFRetargetableNow : List String :=
  []

/-- Modules that still study the authored semantic overlay or hand-crafted
    world-model stack and should stay explicitly legacy for now. -/
def legacySemanticResearchLane : List String :=
  [ "Mettapedia/Languages/GF/GFKernelAgreement.lean"
  , "Mettapedia/Languages/GF/GFToFOLSetBridge.lean"
  , "Mettapedia/Languages/GF/IdentityEvidenceSemantics.lean"
  , "Mettapedia/Languages/GF/LinguisticInvariance.lean"
  , "Mettapedia/Languages/GF/OSLFToNTT.lean"
  , "Mettapedia/Languages/GF/Typing.lean"
  , "Mettapedia/Languages/GF/VisibleLayer.lean"
  , "Mettapedia/Languages/GF/WorldModelSemantics.lean"
  , "Mettapedia/Languages/GF/WorldModelVisibleBridge.lean"
  , "Mettapedia/Languages/GF/UGCommonViewCore.lean"
  , "Mettapedia/Languages/GF/UGCoreFamily.lean"
  , "Mettapedia/Languages/GF/UniversalGrammarCore.lean"
  , "Mettapedia/Languages/GF/SUMO/SumoOSLFBridge.lean"
  , "Mettapedia/Languages/GF/OSLFBridge_handcrafted.lean"
  ]

/-- Legacy files that are plausible future deletions, but are not deletion-safe
    yet because value remains to be extracted or downstream imports still point
    at them. -/
def deletionCandidatesBlocked : List String :=
  []

/-- Legacy files already retired after their remaining code dependencies were
    removed. -/
def retiredLegacyFiles : List String :=
  [ "Mettapedia/Languages/GF/Examples/EveryManWalks.lean"
  , "Mettapedia/Languages/GF/Examples/ScopeAmbiguity.lean"
  , "Mettapedia/Languages/GF/Examples/ScopeLinearExtension.lean"
  , "Mettapedia/Languages/GF/HandCrafted/English/ContextualDisambiguation.lean"
  , "Mettapedia/Languages/GF/HandCrafted/English/InterfaceContrast.lean"
  , "Mettapedia/Languages/GF/HandCrafted/English/InterfaceRefinement.lean"
  , "Mettapedia/Languages/GF/HandCrafted/English/SemanticHighlights.lean"
  , "Mettapedia/Languages/GF/HandCrafted/English/Infrapolitics.lean"
  , "Mettapedia/Languages/GF/PaperAmbiguitySemanticBridge.lean"
  ]

/-- Archived copies of retired legacy files, preserved for design reference
    but intentionally kept outside the live GF authority path.

    These are archival snapshots, not revived modules: they are not imported
    by the active tree, and some still carry their original import paths. If
    we ever want to reactivate one, we should retarget it deliberately rather
    than treating the archive as buildable authority. -/
def archivedLegacyFiles : List String :=
  [ "Mettapedia/Languages/GF/ArchivedLegacy/Examples/EveryManWalks.lean"
  , "Mettapedia/Languages/GF/ArchivedLegacy/Examples/ScopeAmbiguity.lean"
  , "Mettapedia/Languages/GF/ArchivedLegacy/Examples/ScopeLinearExtension.lean"
  , "Mettapedia/Languages/GF/ArchivedLegacy/HandCrafted/English/ContextualDisambiguation.lean"
  , "Mettapedia/Languages/GF/ArchivedLegacy/HandCrafted/English/InterfaceContrast.lean"
  , "Mettapedia/Languages/GF/ArchivedLegacy/HandCrafted/English/InterfaceRefinement.lean"
  , "Mettapedia/Languages/GF/ArchivedLegacy/HandCrafted/English/SemanticHighlights.lean"
  , "Mettapedia/Languages/GF/ArchivedLegacy/HandCrafted/English/Infrapolitics.lean"
  , "Mettapedia/Languages/GF/ArchivedLegacy/PaperAmbiguitySemanticBridge.lean"
  ]

/-- Why the blocked deletions are still blocked. -/
def deletionCandidateBlockers : List (String × String) :=
  []

example : generatedSyntaxSlicesInTree.length = 1 := by decide
example : groundedCoverageBoundaryLanguages.length = 2 := by decide
example : realGFRetargetableNow.length = 0 := by decide
example : legacySemanticResearchLane.length = 14 := by decide
example : deletionCandidatesBlocked.length = 0 := by decide
example : retiredLegacyFiles.length = 9 := by decide
example : archivedLegacyFiles.length = 9 := by decide
example : deletionCandidateBlockers.length = 0 := by decide

example : "PaperAmbiguity" ∈ generatedSyntaxSlicesInTree := by decide
example : "PaperAmbiguityCze" ∈ groundedCoverageBoundaryLanguages := by decide
example : "Mettapedia/Languages/GF/OSLFToNTT.lean" ∈ legacySemanticResearchLane := by decide
example : "Mettapedia/Languages/GF/Examples/EveryManWalks.lean" ∈ retiredLegacyFiles := by decide
example : "Mettapedia/Languages/GF/Examples/ScopeAmbiguity.lean" ∈ retiredLegacyFiles := by decide
example : "Mettapedia/Languages/GF/PaperAmbiguitySemanticBridge.lean" ∈ retiredLegacyFiles := by decide
example : "Mettapedia/Languages/GF/ArchivedLegacy/PaperAmbiguitySemanticBridge.lean" ∈ archivedLegacyFiles := by decide

end Mettapedia.Languages.GF.GFAuthorityAudit
