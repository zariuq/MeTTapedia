import Mettapedia.CognitiveArchitecture.GodelClaw.Core
import Mettapedia.CognitiveArchitecture.GodelClaw.EpistemicLove

/-!
# GodelClaw Ethics Foundation

This folder is the preferred home for the universal-loving-care lane inside
`GodelClaw`.

It consolidates the already-existing pieces without moving or deleting the
legacy files:

- the abstract core-value declaration,
- the epistemic universal loving care definition,
- the paraconsistent desire bridge through `BinaryEvidence`.

**Positive example.**  An agent can treat epistemic universal loving care as a
core value while representing conflicting known desires in a graded,
non-explosive way.

**Negative example.**  Classical desire closure still explodes on contradictory
known desires; this module does not deny that result.
-/

namespace Mettapedia.CognitiveArchitecture.GodelClaw.Ethics

export Mettapedia.CognitiveArchitecture.GodelClaw
  (CoreValueDeclaration UniversalLovingCare oruzisCore SeedIdentity
   ValuePreserving id_is_value_preserving)

export Mettapedia.CognitiveArchitecture.GodelClaw.EpistemicLove
  (Formula LoveSig fulfills EpistemicUniversalLove epistemicLoveAsCore
   GradedDesire contradictory_desires_coexist desire_negation_conserves_total
   desire_strengths_complement)

end Mettapedia.CognitiveArchitecture.GodelClaw.Ethics
