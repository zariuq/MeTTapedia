import Mettapedia.GSLT.Parsing.ClassAwareForestCatalogueCoverage

/-! Valid parser certificates retain their identity in catalogue trees.
Restoration is checked against replayed input seams, so malformed arbitrary
certificate data is not silently repaired by this inverse law. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareForestCatalogue

open ClassAwareParserPackCertificate ClassAwareParserPackCorrespondence
open ParserProfileSemantics PresentationExprSemantics

theorem certificate_identity {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {sort : String} {start stop : Nat} {firstTree secondTree : CST}
    {first second : Certificate}
    (left : Replays profile plan input first sort start stop firstTree)
    (right : Replays profile plan input second sort start stop secondTree)
    (same : ofCertificate sort first = ofCertificate sort second) : first = second := by
  have restored := congrArg restore same
  rw [restore_replayed left, restore_replayed right] at restored
  exact Option.some.inj restored

theorem distinct_productions_stay_distinct {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {sort : String} {start stop : Nat} {firstTree secondTree : CST}
    {first second : Certificate}
    (left : Replays profile plan input first sort start stop firstTree)
    (right : Replays profile plan input second sort start stop secondTree)
    (different : first ≠ second) : ofCertificate sort first ≠ ofCertificate sort second :=
  fun same => different (certificate_identity left right same)

#print axioms certificate_identity

end Mettapedia.GSLT.Parsing.ClassAwareForestCatalogue
