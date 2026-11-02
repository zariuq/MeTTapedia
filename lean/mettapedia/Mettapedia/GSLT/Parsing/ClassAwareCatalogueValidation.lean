import Mettapedia.GSLT.Parsing.ClassAwareForestCatalogueCoverage
import Mettapedia.GSLT.Parsing.ClassAwareNativeForestQualification

/-! A native certificate list is complete only when its occurrence multiset
equals the closed selected catalogue. Membership alone would accept duplicated
outputs in place of a missing alternative. Unfinished construction stays none. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareCatalogueValidation

open ClassAwarePackedForest ClassAwareParserPackCertificate ClassAwareParserPackCorrespondence
open ClassAwareForestCatalogue PackedForestCatalogue ParserProfileSemantics PresentationExprSemantics

def certificates? (forest : Forest) (allow : Family → Bool) (key : NodeKey) (rounds : Nat) :
    Option (List Certificate) :=
  (ClassAwareForestCatalogue.catalogue? forest allow rounds).map fun store => (lookup store key).filterMap restore

def validate? (forest : Forest) (allow : Family → Bool) (key : NodeKey) (rounds : Nat)
    (native : List Certificate) : Option Bool :=
  (certificates? forest allow key rounds).map fun reference => decide (native.Perm reference)

theorem validate?_covers {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {sort : String} {start stop : Nat} {tree : CST} {certificate : Certificate}
    {forest : Forest} {allow : Family → Bool} {rounds : Nat} {native : List Certificate}
    (accepted : validate? forest allow ⟨sort, start, stop⟩ rounds native = some true)
    (replayed : Replays profile plan input certificate sort start stop tree)
    (present : ClassAwarePackedForest.Unfolds forest sort certificate)
    (selected : ∀ family ∈ certificateFamilies sort certificate, allow family = true) :
    certificate ∈ native := by
  obtain ⟨reference, built, compared⟩ := Option.map_eq_some_iff.mp accepted
  have permutation : native.Perm reference := of_decide_eq_true compared
  obtain ⟨store, finished, rfl⟩ := Option.map_eq_some_iff.mp built
  exact permutation.mem_iff.mpr (certificate_covered forest allow rounds store finished replayed present selected)

theorem validate?_root_complete {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {forest : Forest} {allow : Family → Bool} {rounds : Nat} {native : List Certificate}
    (complete : ClassAwareNativeForestQualification.RootParserComplete forest profile plan input)
    (accepted : validate? forest allow ⟨plan.lexical.startSort, 0, input.length⟩ rounds native = some true)
    {tree : CST} (source : ParserPackRootDerives profile plan input tree)
    (selected : ∀ family ∈ certificateFamilies plan.lexical.startSort (Certificate.ofDerivation source), allow family = true) :
    Certificate.ofDerivation source ∈ native :=
  validate?_covers accepted (Replays.ofDerivation source) (complete tree source).2 selected

theorem pending_is_not_complete (forest : Forest) (allow : Family → Bool) (key : NodeKey) (native : List Certificate) :
    validate? forest allow key 0 native = none := rfl

#print axioms validate?_covers
#print axioms validate?_root_complete

end Mettapedia.GSLT.Parsing.ClassAwareCatalogueValidation
