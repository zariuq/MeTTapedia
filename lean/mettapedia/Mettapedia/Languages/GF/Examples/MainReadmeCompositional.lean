/-
Compatibility shim.
Canonical location: `Mettapedia/DocText/MainReadmeCompositional.lean`.
-/

import Mettapedia.DocText.MainReadmeCompositional

namespace Mettapedia.Languages.GF.Examples.MainReadmeCompositional

export Mettapedia.DocText.MainReadmeCompositional
  ( TopDir RepoId RepoPath topDirToken repoPath renderRepoPath repoDisplayName
    Tooling Claim renderClaim RepoEntry Section mainSections
    allMainReadmeClaims canonicalMainReadmeClaims parseClaimLine?
    ParsedReadmeLine parseStructuredLine? claimRenderedBuckets ambiguousClaimRenderings
    mainReadmeStructuredLines mainReadmeBlocks ParsedMainStructuredLine
    parseSelectedStructuredMainLine? selectedStructuredMainReadmeLines
    mainHardAuditPasses main_hard_audit mainReadmeMarkdown
    intro_sentence mmlean4_sentence status_sentence path_rendering
    parse_roundtrip_intro parse_roundtrip_mmlean4 parse_roundtrip_status
    parse_roundtrip_section_heading parse_roundtrip_entry )

end Mettapedia.Languages.GF.Examples.MainReadmeCompositional
