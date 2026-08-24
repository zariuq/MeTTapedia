import Mettapedia.Languages.MeTTa.Prime.GSLTILTypedEvidenceWorldNIKSelection

/-!
# Policy-relative reflection for typed proof-world routes

Global injectivity of a proof-world route is sufficient for replaying every
source distinction, but it is not necessary for every consumer.  A consumer
declares a dependent policy family on source histories.  The route is eligible
for that family exactly when the complete policy vector factors through the
mapped target history.

This is the observer-relative reflection boundary.  It lets a forward route
which forgets proof identity remain a valid native realization for length,
multiplicity, or another invariant it actually preserves.  The same route is
ineligible for a source-history policy separated by one of its collisions.
NIK may therefore compare exact candidates using supplied executable policy
runners without imposing global injectivity as a universal gate.

The fibrewise characterization is a specification theorem.  Runtime admission
retains a concrete `ReadoutRealization`; it does not use classical existence as
an executable oracle.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.GSLTILTypedEvidenceRoutePolicySelection

open Mettapedia.GSLT.Core
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.GSLTIL.EvidenceWorlds
open Mettapedia.GSLT.LanguageDef.GSLTIL.TypedEvidenceRoutes
open Mettapedia.GSLT.LanguageDef.GSLTIL.TypedEvidenceRoutes.TypedEvidenceRoute
open Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyCapabilitySelection

variable {sourcePresentation middlePresentation targetPresentation :
  ValidatedLanguageDef}
variable {source : EvidenceProfileOver sourcePresentation}
  {middle : EvidenceProfileOver middlePresentation}
  {target : EvidenceProfileOver targetPresentation}

abbrev SourceHistory (source : EvidenceProfileOver sourcePresentation)
    (command : source.profile.Command) :=
  List (source.profile.World command)

abbrev TargetHistory (target : EvidenceProfileOver targetPresentation)
    (command : target.profile.Command) :=
  List (target.profile.World command)

/-- Executable evidence that a mapped target history retains every answer in
one declared source-policy family. -/
abbrev RoutePolicyRealization
    (route : TypedEvidenceRoute source target)
    (command : source.profile.Command)
    (family : PolicyFamily (SourceHistory source command)) :=
  family.ReadoutRealization (route.atCommand command).mapHistory

namespace RoutePolicyRealization

/-- Install retained route-policy runners directly into NIK's ordinary
policy-catalog interface.  The unit index represents this one route; native
comparison with other routes remains the responsibility of the surrounding
recognized family. -/
def toNIKCatalog
    {route : TypedEvidenceRoute source target}
    {command : source.profile.Command}
    {family : PolicyFamily (SourceHistory source command)}
    (realization : RoutePolicyRealization route command family) :
    PolicyReadoutCatalog Unit (SourceHistory source command) family where
  Key := fun _ => TargetHistory target (route.mapCommand command)
  readout := fun _ => (route.atCommand command).mapHistory
  Supports := fun _ _ => True
  runner := fun _ policy _ => realization.run policy
  agrees := fun _ policy _ history => realization.agrees policy history
  supports_mono := by
    intro weaker stronger related policy supported
    exact supported

@[simp] theorem toNIKCatalog_readout
    {route : TypedEvidenceRoute source target}
    {command : source.profile.Command}
    {family : PolicyFamily (SourceHistory source command)}
    (realization : RoutePolicyRealization route command family)
    (history : SourceHistory source command) :
    (realization.toNIKCatalog.readout () history) =
      (route.atCommand command).mapHistory history :=
  rfl

/-- The NIK catalog obtained from a retained realization factors onto the
canonical answer vector for any exact subset request. -/
theorem toNIKCatalog_requestedVector_factors
    {route : TypedEvidenceRoute source target}
    {command : source.profile.Command}
    {family : PolicyFamily (SourceHistory source command)}
    (realization : RoutePolicyRealization route command family)
    (required : Set family.Policy) :
    NonFactorization.Factors
      (realization.toNIKCatalog.readout ())
      (realization.toNIKCatalog.requestedFamily required).vector := by
  apply realization.toNIKCatalog.requestedVector_factors
  intro policy member
  trivial

end RoutePolicyRealization

/-- Propositional route eligibility is inhabited executable policy runners. -/
def SupportsSourcePolicies
    (route : TypedEvidenceRoute source target)
    (command : source.profile.Command)
    (family : PolicyFamily (SourceHistory source command)) : Prop :=
  family.SupportsReadout (route.atCommand command).mapHistory

/-- Exact constructive criterion: the canonical policy vector must factor
through the route's mapped target history. -/
theorem supportsSourcePolicies_iff_vectorFactors
    (route : TypedEvidenceRoute source target)
    (command : source.profile.Command)
    (family : PolicyFamily (SourceHistory source command)) :
    SupportsSourcePolicies route command family ↔
      NonFactorization.Factors
        (route.atCommand command).mapHistory family.vector :=
  family.supportsReadout_iff_vectorFactors
    (route.atCommand command).mapHistory

/-- Extensional characterization: a route supports a family exactly when
every collision it creates is indistinguishable to every requested policy.
The reverse direction is classical and is not the production admission
algorithm. -/
theorem supportsSourcePolicies_iff_compatible
    (route : TypedEvidenceRoute source target)
    (command : source.profile.Command)
    (family : PolicyFamily (SourceHistory source command)) :
    SupportsSourcePolicies route command family ↔
      family.CompatibleReadout (route.atCommand command).mapHistory := by
  letI : Nonempty (SourceHistory source command) := ⟨[]⟩
  exact family.supportsReadout_iff_compatible
    (route.atCommand command).mapHistory

/-- Global world reflection implies policy-relative support for every family.
This is sufficient, but the collapse canary below proves it is not necessary. -/
theorem reflectsWorlds_supports_every_family
    (route : TypedEvidenceRoute source target)
    (command : source.profile.Command)
    (reflects : route.ReflectsWorlds)
    (family : PolicyFamily (SourceHistory source command)) :
    SupportsSourcePolicies route command family := by
  rw [supportsSourcePolicies_iff_compatible]
  intro first second sameTarget
  have sameSource : first = second :=
    EvidenceWorldMap.mapHistory_injective (route.atCommand command)
      (reflects command) sameTarget
  subst second
  exact family.policyEquivalent_refl first

/-- Composition cannot manufacture support for a source policy family.  If a
composite route supports the family, its strictly finer prefix already does. -/
theorem prefix_supports_of_composite_supports
    (earlier : TypedEvidenceRoute source middle)
    (later : TypedEvidenceRoute middle target)
    (command : source.profile.Command)
    (family : PolicyFamily (SourceHistory source command))
    (supported : SupportsSourcePolicies
      (TypedEvidenceRoute.comp earlier later) command family) :
    SupportsSourcePolicies earlier command family := by
  apply family.supportsReadout_of_refinement
    (coarseSupports := supported)
  refine ⟨(later.atCommand (earlier.mapCommand command)).mapHistory, fun history => ?_⟩
  exact (atCommand_comp_mapHistory earlier later command history).symm

/-- Identity has a direct executable realization for every source policy
family; no choice or boundary replay is involved. -/
def identityPolicyRealization
    (command : source.profile.Command)
    (family : PolicyFamily (SourceHistory source command)) :
    RoutePolicyRealization (TypedEvidenceRoute.id source) command family where
  run := family.decide
  agrees := by
    intro policy history
    rw [atCommand_id_mapHistory]

theorem identity_supports_every_family
    (command : source.profile.Command)
    (family : PolicyFamily (SourceHistory source command)) :
    SupportsSourcePolicies (TypedEvidenceRoute.id source) command family :=
  ⟨identityPolicyRealization command family⟩

/-! ## One lossy route, one admitted family, and one refusing family -/

namespace Canary

open Mettapedia.Languages.MeTTa.Prime.GSLTILTypedEvidenceWorldPrograms.SignatureEvidenceInterpretation.Canary
open Mettapedia.Languages.MeTTa.Prime.GSLTILTypedEvidenceWorldNIKSelection.Canary

abbrev RichHistory := List (richProfile.World ())

inductive LengthPolicy where
  | length
deriving DecidableEq

def lengthFamily : PolicyFamily RichHistory where
  Policy := LengthPolicy
  Result := fun _ => Nat
  decide := fun _ => List.length

/-- The non-injective route still supplies a direct runner for history length. -/
def collapseLengthRealization :
    RoutePolicyRealization collapseRoute () lengthFamily where
  run := fun _ => List.length
  agrees := by
    intro policy history
    exact EvidenceWorldMap.mapHistory_length collapsePromoteTransport history

theorem collapse_supports_length :
    SupportsSourcePolicies collapseRoute () lengthFamily :=
  ⟨collapseLengthRealization⟩

inductive CompletePolicy where
  | complete
deriving DecidableEq

def completeSourceFamily : PolicyFamily RichHistory where
  Policy := CompletePolicy
  Result := fun _ => RichHistory
  decide := fun _ => _root_.id

/-- The rich route supports complete source-history replay directly. -/
def richCompleteRealization :
    RoutePolicyRealization richRoute () completeSourceFamily where
  run := fun _ => _root_.id
  agrees := by
    intro policy history
    exact richRoute_atCommand_mapHistory history

theorem rich_supports_complete_source :
    SupportsSourcePolicies richRoute () completeSourceFamily :=
  ⟨richCompleteRealization⟩

theorem sourceSingletonHistories_distinct :
    ([firstWorld] : RichHistory) ≠ [secondWorld] := by
  intro equal
  exact sourceWorlds_distinct (List.cons.inj equal).1

/-- The same collapsing route is refused for complete source-history replay. -/
theorem collapse_refuses_complete_source :
    ¬ SupportsSourcePolicies collapseRoute () completeSourceFamily := by
  apply completeSourceFamily.not_supportsReadout_of_policy_collision
      collapsePromoteTransport.mapHistory
      (first := [firstWorld]) (second := [secondWorld]) (by rfl)
      .complete
  exact sourceSingletonHistories_distinct

/-- Lossiness is request-relative: the route is useful for one exact family
and forbidden for another, while the rich route supports both. -/
theorem policy_relative_reflection_boundary :
    SupportsSourcePolicies collapseRoute () lengthFamily /\
      ¬ SupportsSourcePolicies collapseRoute () completeSourceFamily /\
      SupportsSourcePolicies richRoute () completeSourceFamily :=
  ⟨collapse_supports_length, collapse_refuses_complete_source,
    rich_supports_complete_source⟩

end Canary

#print axioms supportsSourcePolicies_iff_vectorFactors
#print axioms supportsSourcePolicies_iff_compatible
#print axioms RoutePolicyRealization.toNIKCatalog
#print axioms RoutePolicyRealization.toNIKCatalog_requestedVector_factors
#print axioms reflectsWorlds_supports_every_family
#print axioms prefix_supports_of_composite_supports
#print axioms identityPolicyRealization
#print axioms Canary.collapse_supports_length
#print axioms Canary.rich_supports_complete_source
#print axioms Canary.collapse_refuses_complete_source
#print axioms Canary.policy_relative_reflection_boundary

end Mettapedia.Languages.MeTTa.Prime.GSLTILTypedEvidenceRoutePolicySelection
