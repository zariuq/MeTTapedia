/-
Compatibility shim.
Canonical location: `Mettapedia/DocText/OSLFReadmeCompositional.lean`.
-/

import Mettapedia.DocText.OSLFReadmeCompositional

namespace Mettapedia.Languages.GF.Examples.OSLFReadmeCompositional

export Mettapedia.DocText.OSLFReadmeCompositional
  ( OSLFClaim renderOSLFClaim oslfReadmeBlocks oslfReadmeMarkdown
    anchor_oslf_turns anchor_oslf_is_construction anchor_takes_rewrite
    anchor_not_parser anchor_coremain_recommended anchor_core_derive
    anchor_outcome anchor_not_proof
    allOSLFClaims parseOSLFClaimLine? parseSelectedStructuredOSLFLine?
    selectedStructuredOSLFLines oslfHardAuditPasses oslf_hard_audit
    claimRenderedBuckets ambiguousClaimRenderings )

end Mettapedia.Languages.GF.Examples.OSLFReadmeCompositional
