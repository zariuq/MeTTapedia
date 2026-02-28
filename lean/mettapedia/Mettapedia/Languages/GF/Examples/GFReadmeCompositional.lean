/-
Compatibility shim.
Canonical location: `Mettapedia/DocText/GFReadmeCompositional.lean`.
-/

import Mettapedia.DocText.GFReadmeCompositional

namespace Mettapedia.Languages.GF.Examples.GFReadmeCompositional

export Mettapedia.DocText.GFReadmeCompositional
  ( GFClaim renderGFClaim allGFClaims parseGFClaimLine?
    gfReadmeBlocks gfReadmeMarkdown
    ParsedGFStructuredLine parseSelectedStructuredGFLine?
    selectedStructuredGFLines gfHardAuditPasses gf_hard_audit
    claimSurfaceBuckets ambiguousClaimSurfaces
    anchor_formalization anchor_no_sorries )

end Mettapedia.Languages.GF.Examples.GFReadmeCompositional
