import Mettapedia.Languages.MeTTa.Prime.GSLTILTypedEvidenceRoutePolicySelection

/-!
# Compositional policy reflection for typed proof-world routes

A policy realization for a prefix route leaves a residual policy family on
the intermediate histories: its decisions are exactly the prefix runners.
If a suffix realizes that residual family, the two executable realizations
compose and agree with the original source policies.

The converse has an exact boundary.  Composite support determines support of
the residual family only when the prefix history map is surjective.  Without
that coverage, a prefix runner may make observable choices on unreachable
intermediate histories; a later route may collapse those choices while the
source-to-target composite remains fully adequate.  The checked counterexample
below prevents a global converse from being assumed by NIK or a compiler.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.GSLTILTypedEvidenceRoutePolicyComposition

open Mettapedia.GSLT.Core
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.GSLTIL.EvidenceWorlds
open Mettapedia.GSLT.LanguageDef.GSLTIL.TypedEvidenceRoutes
open Mettapedia.GSLT.LanguageDef.GSLTIL.TypedEvidenceRoutes.TypedEvidenceRoute
open Mettapedia.Languages.MeTTa.Prime.FiniteLanguageOperationSignature
open Mettapedia.Languages.MeTTa.Prime.LanguageDef
open Mettapedia.Languages.MeTTa.Prime.GSLTILTypedEvidenceRoutePolicySelection

variable {sourcePresentation middlePresentation targetPresentation :
  ValidatedLanguageDef}
variable {source : EvidenceProfileOver sourcePresentation}
  {middle : EvidenceProfileOver middlePresentation}
  {target : EvidenceProfileOver targetPresentation}

namespace RoutePolicyRealization

/-- The policy family which remains to be preserved after a prefix has
already supplied runners for the original source policies. -/
def residualFamily
    {earlier : TypedEvidenceRoute source middle}
    {command : source.profile.Command}
    {family : PolicyFamily (SourceHistory source command)}
    (realization : RoutePolicyRealization earlier command family) :
    PolicyFamily (SourceHistory middle (earlier.mapCommand command)) where
  Policy := family.Policy
  Result := family.Result
  decide := realization.run

@[simp] theorem residualFamily_decide
    {earlier : TypedEvidenceRoute source middle}
    {command : source.profile.Command}
    {family : PolicyFamily (SourceHistory source command)}
    (realization : RoutePolicyRealization earlier command family)
    (policy : family.Policy)
    (history : SourceHistory middle (earlier.mapCommand command)) :
    (residualFamily realization).decide policy history =
      realization.run policy history :=
  rfl

/-- Constructive forward composition: the suffix runners consume the mapped
intermediate history and reconstruct the prefix runners' answers. -/
def compose
    {earlier : TypedEvidenceRoute source middle}
    {later : TypedEvidenceRoute middle target}
    {command : source.profile.Command}
    {family : PolicyFamily (SourceHistory source command)}
    (earlierRealization : RoutePolicyRealization earlier command family)
    (laterRealization : RoutePolicyRealization later
      (earlier.mapCommand command) (residualFamily earlierRealization)) :
    RoutePolicyRealization (TypedEvidenceRoute.comp earlier later)
      command family where
  run := laterRealization.run
  agrees := by
    intro policy history
    calc
      laterRealization.run policy
          (((TypedEvidenceRoute.comp earlier later).atCommand command).mapHistory
            history) =
        laterRealization.run policy
          ((later.atCommand (earlier.mapCommand command)).mapHistory
            ((earlier.atCommand command).mapHistory history)) :=
        congrArg (laterRealization.run policy)
          (atCommand_comp_mapHistory earlier later command history)
      _ = earlierRealization.run policy
          ((earlier.atCommand command).mapHistory history) :=
        laterRealization.agrees policy
          ((earlier.atCommand command).mapHistory history)
      _ = family.decide policy history :=
        earlierRealization.agrees policy history

/-- Two retained executable realizations therefore witness support of their
composite route. -/
theorem compose_supports
    {earlier : TypedEvidenceRoute source middle}
    {later : TypedEvidenceRoute middle target}
    {command : source.profile.Command}
    {family : PolicyFamily (SourceHistory source command)}
    (earlierRealization : RoutePolicyRealization earlier command family)
    (laterRealization : RoutePolicyRealization later
      (earlier.mapCommand command) (residualFamily earlierRealization)) :
    SupportsSourcePolicies (TypedEvidenceRoute.comp earlier later)
      command family :=
  ⟨compose earlierRealization laterRealization⟩

/-! ## Exact composition on the reached intermediate image -/

/-- Intermediate histories which are actually reached by the prefix.  The
reachability witness is retained propositionally; the history itself remains
the runtime state consumed by the suffix. -/
abbrev ReachedHistory
    (earlier : TypedEvidenceRoute source middle)
    (command : source.profile.Command) :=
  { middleHistory : SourceHistory middle (earlier.mapCommand command) //
    ∃ sourceHistory : SourceHistory source command,
      (earlier.atCommand command).mapHistory sourceHistory = middleHistory }

/-- The prefix residual family restricted to histories the composed program
can actually reach. -/
def reachedResidualFamily
    {earlier : TypedEvidenceRoute source middle}
    {command : source.profile.Command}
    {family : PolicyFamily (SourceHistory source command)}
    (earlierRealization : RoutePolicyRealization earlier command family) :
    PolicyFamily (ReachedHistory earlier command) where
  Policy := family.Policy
  Result := family.Result
  decide := fun policy reached => earlierRealization.run policy reached.1

/-- Restrict the suffix history map to the propositionally certified reached
image of the prefix.  Source provenance is retained by the stronger companion
carrier in `GSLTILTypedEvidenceRouteProvenance`. -/
def suffixReadoutOnReached
    (earlier : TypedEvidenceRoute source middle)
    (later : TypedEvidenceRoute middle target)
    (command : source.profile.Command) :
    ReachedHistory earlier command →
      SourceHistory target
        (later.mapCommand (earlier.mapCommand command)) :=
  fun reached =>
    (later.atCommand (earlier.mapCommand command)).mapHistory reached.1

/-- Every composite realization gives a realization of the suffix on exactly
the reached intermediate histories, with no surjectivity assumption. -/
def reachedSuffixOfComposite
    {earlier : TypedEvidenceRoute source middle}
    {later : TypedEvidenceRoute middle target}
    {command : source.profile.Command}
    {family : PolicyFamily (SourceHistory source command)}
    (earlierRealization : RoutePolicyRealization earlier command family)
    (compositeRealization : RoutePolicyRealization
      (TypedEvidenceRoute.comp earlier later) command family) :
    (reachedResidualFamily earlierRealization).ReadoutRealization
      (suffixReadoutOnReached earlier later command) where
  run := compositeRealization.run
  agrees := by
    intro policy reached
    rcases reached with ⟨middleHistory, sourceHistory, reaches⟩
    subst middleHistory
    calc
      compositeRealization.run policy
          ((later.atCommand (earlier.mapCommand command)).mapHistory
            ((earlier.atCommand command).mapHistory sourceHistory)) =
        compositeRealization.run policy
          (((TypedEvidenceRoute.comp earlier later).atCommand command).mapHistory
            sourceHistory) :=
        congrArg (compositeRealization.run policy)
          (atCommand_comp_mapHistory earlier later command sourceHistory).symm
      _ = family.decide policy sourceHistory :=
        compositeRealization.agrees policy sourceHistory
      _ = earlierRealization.run policy
          ((earlier.atCommand command).mapHistory sourceHistory) :=
        (earlierRealization.agrees policy sourceHistory).symm

/-- Conversely, executable suffix runners on the reached image compose with
the prefix realization into a source-to-target realization. -/
def composeFromReachedSuffix
    {earlier : TypedEvidenceRoute source middle}
    {later : TypedEvidenceRoute middle target}
    {command : source.profile.Command}
    {family : PolicyFamily (SourceHistory source command)}
    (earlierRealization : RoutePolicyRealization earlier command family)
    (reachedSuffix :
      (reachedResidualFamily earlierRealization).ReadoutRealization
        (suffixReadoutOnReached earlier later command)) :
    RoutePolicyRealization (TypedEvidenceRoute.comp earlier later)
      command family where
  run := reachedSuffix.run
  agrees := by
    intro policy sourceHistory
    let reached : ReachedHistory earlier command :=
      ⟨(earlier.atCommand command).mapHistory sourceHistory,
        ⟨sourceHistory, rfl⟩⟩
    calc
      reachedSuffix.run policy
          (((TypedEvidenceRoute.comp earlier later).atCommand command).mapHistory
            sourceHistory) =
        reachedSuffix.run policy
          (suffixReadoutOnReached earlier later command reached) :=
        congrArg (reachedSuffix.run policy)
          (atCommand_comp_mapHistory earlier later command sourceHistory)
      _ = (reachedResidualFamily earlierRealization).decide policy reached :=
        reachedSuffix.agrees policy reached
      _ = earlierRealization.run policy
          ((earlier.atCommand command).mapHistory sourceHistory) :=
        rfl
      _ = family.decide policy sourceHistory :=
        earlierRealization.agrees policy sourceHistory

/-- **Exact reached-image composition theorem.**  Composite support is
equivalent to suffix support on the histories the prefix can actually reach.
No ambient surjectivity or arbitrary off-image behavior is required. -/
theorem composite_supports_iff_reached_suffix_supports
    {earlier : TypedEvidenceRoute source middle}
    {later : TypedEvidenceRoute middle target}
    {command : source.profile.Command}
    {family : PolicyFamily (SourceHistory source command)}
    (earlierRealization : RoutePolicyRealization earlier command family) :
    SupportsSourcePolicies (TypedEvidenceRoute.comp earlier later)
        command family ↔
      (reachedResidualFamily earlierRealization).SupportsReadout
        (suffixReadoutOnReached earlier later command) := by
  constructor
  · rintro ⟨compositeRealization⟩
    exact ⟨reachedSuffixOfComposite earlierRealization compositeRealization⟩
  · rintro ⟨reachedSuffix⟩
    exact ⟨composeFromReachedSuffix earlierRealization reachedSuffix⟩

/-- Strongest true converse.  Surjectivity lets a composite runner determine
the suffix runner on every intermediate history, not merely on the prefix
image. -/
def suffixOfCompositeOfSurjective
    {earlier : TypedEvidenceRoute source middle}
    {later : TypedEvidenceRoute middle target}
    {command : source.profile.Command}
    {family : PolicyFamily (SourceHistory source command)}
    (earlierRealization : RoutePolicyRealization earlier command family)
    (surjective : Function.Surjective
      (earlier.atCommand command).mapHistory)
    (compositeRealization : RoutePolicyRealization
      (TypedEvidenceRoute.comp earlier later) command family) :
    RoutePolicyRealization later (earlier.mapCommand command)
      (residualFamily earlierRealization) where
  run := compositeRealization.run
  agrees := by
    intro policy middleHistory
    obtain ⟨sourceHistory, image⟩ := surjective middleHistory
    subst middleHistory
    calc
      compositeRealization.run policy
          ((later.atCommand (earlier.mapCommand command)).mapHistory
            ((earlier.atCommand command).mapHistory sourceHistory)) =
        compositeRealization.run policy
          (((TypedEvidenceRoute.comp earlier later).atCommand command).mapHistory
            sourceHistory) :=
        congrArg (compositeRealization.run policy)
          (atCommand_comp_mapHistory earlier later command sourceHistory).symm
      _ = family.decide policy sourceHistory :=
        compositeRealization.agrees policy sourceHistory
      _ = earlierRealization.run policy
          ((earlier.atCommand command).mapHistory sourceHistory) :=
        (earlierRealization.agrees policy sourceHistory).symm

/-- Under prefix-history coverage, composite support is exactly suffix support
for the residual family generated by the retained prefix realization. -/
theorem composite_supports_iff_suffix_supports_of_surjective
    {earlier : TypedEvidenceRoute source middle}
    {later : TypedEvidenceRoute middle target}
    {command : source.profile.Command}
    {family : PolicyFamily (SourceHistory source command)}
    (earlierRealization : RoutePolicyRealization earlier command family)
    (surjective : Function.Surjective
      (earlier.atCommand command).mapHistory) :
    SupportsSourcePolicies (TypedEvidenceRoute.comp earlier later)
        command family ↔
      SupportsSourcePolicies later (earlier.mapCommand command)
        (residualFamily earlierRealization) := by
  constructor
  · rintro ⟨compositeRealization⟩
    exact ⟨suffixOfCompositeOfSurjective earlierRealization
      surjective compositeRealization⟩
  · rintro ⟨laterRealization⟩
    exact compose_supports earlierRealization laterRealization

end RoutePolicyRealization

/-! ## Positive composition and the missing-coverage counterexample -/

namespace Canary

open Mettapedia.Languages.MeTTa.Prime.GSLTILTypedEvidenceWorldPrograms.SignatureEvidenceInterpretation.Canary
open Mettapedia.Languages.MeTTa.Prime.GSLTILTypedEvidenceWorldNIKSelection.Canary
open Mettapedia.Languages.MeTTa.Prime.GSLTILTypedEvidenceRoutePolicySelection.Canary
open RoutePolicyRealization

/-- A positive compositional control: the lossy route's exact length runner
survives a following identity route by executable realization composition. -/
def collapseThenIdentityLengthRealization :
    RoutePolicyRealization
      (TypedEvidenceRoute.comp collapseRoute
        (TypedEvidenceRoute.id (thinAt currentPrimePresentation)))
      () lengthFamily :=
  compose collapseLengthRealization
    (identityPolicyRealization
      (source := thinAt currentPrimePresentation) ()
      (residualFamily collapseLengthRealization))

theorem collapse_then_identity_supports_length :
    SupportsSourcePolicies
      (TypedEvidenceRoute.comp collapseRoute
        (TypedEvidenceRoute.id (thinAt currentPrimePresentation)))
      () lengthFamily :=
  ⟨collapseThenIdentityLengthRealization⟩

/-- The unique source proof world used by the non-surjective prefix. -/
def thinWorld : thinProfile.World () :=
  ⟨internal, ThinEvidence.only⟩

theorem thinWorld_unique (world : thinProfile.World ()) : world = thinWorld := by
  rcases world with ⟨result, evidence⟩
  cases evidence
  rfl

/-- Embed the thin source into only the first proof-history world.  The second
middle world is deliberately unreachable. -/
def embedFirstRoute :
    TypedEvidenceRoute
      (thinAt currentZeroPresentation)
      (richAt currentZeroPresentation) where
  structural := StructuralMorphism.id currentZeroPresentation
  mapCommand := _root_.id
  mapInternal := _root_.id
  mapInternal_structural := fun value => (mapPattern_id value).symm
  surface_natural := fun _ => rfl
  mapEvidence := by
    intro command result evidence
    cases evidence
    exact RichEvidence.first

@[simp] theorem embedFirstRoute_mapWorld
    (world : thinProfile.World ()) :
    (embedFirstRoute.atCommand ()).mapWorld world = firstWorld := by
  rw [thinWorld_unique world]
  rfl

/-- The prefix is not history-surjective: no source history reaches the second
middle proof world. -/
theorem embedFirstRoute_not_history_surjective :
    ¬ Function.Surjective (embedFirstRoute.atCommand ()).mapHistory := by
  intro surjective
  obtain ⟨sourceHistory, mapsToSecond⟩ := surjective [secondWorld]
  have sourceLength : sourceHistory.length = 1 := by
    calc
      sourceHistory.length =
          ((embedFirstRoute.atCommand ()).mapHistory sourceHistory).length :=
        (EvidenceWorldMap.mapHistory_length
          (embedFirstRoute.atCommand ()) sourceHistory).symm
      _ = 1 := by
        rw [mapsToSecond]
        rfl
  obtain ⟨head, shape⟩ := List.length_eq_one_iff.mp sourceLength
  rw [shape] at mapsToSecond
  have headsEqual :
      (embedFirstRoute.atCommand ()).mapWorld head = secondWorld :=
    (List.cons.inj mapsToSecond).1
  rw [embedFirstRoute_mapWorld] at headsEqual
  exact sourceWorlds_distinct headsEqual

inductive ConstantPolicy where
  | value
deriving DecidableEq

def constantFalseFamily :
    PolicyFamily (List (thinProfile.World ())) where
  Policy := ConstantPolicy
  Result := fun _ => Bool
  decide := fun _ _ => false

def isSecondWorld : richProfile.World () → Bool
  | ⟨_, RichEvidence.first⟩ => false
  | ⟨_, RichEvidence.second⟩ => true

def containsSecond (history : List (richProfile.World ())) : Bool :=
  history.any isSecondWorld

@[simp] theorem containsSecond_embedFirst
    (history : List (thinProfile.World ())) :
    containsSecond ((embedFirstRoute.atCommand ()).mapHistory history) = false := by
  induction history with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      change
        (isSecondWorld ((embedFirstRoute.atCommand ()).mapWorld head) ||
          containsSecond ((embedFirstRoute.atCommand ()).mapHistory tail)) = false
      rw [embedFirstRoute_mapWorld, inductionHypothesis]
      rfl

/-- Agreement constrains this prefix runner on reachable histories.  Its
choice on the unreachable second world is intentionally observable. -/
def adversarialPrefixRealization :
    RoutePolicyRealization embedFirstRoute () constantFalseFamily where
  run := fun _ => containsSecond
  agrees := by
    intro policy history
    exact containsSecond_embedFirst history

/-- The source-to-target composite is still adequate for the original
constant policy. -/
def compositeConstantRealization :
    RoutePolicyRealization
      (TypedEvidenceRoute.comp embedFirstRoute collapseRoute)
      () constantFalseFamily where
  run := fun _ _ => false
  agrees := by
    intro policy history
    rfl

theorem composite_supports_constant :
    SupportsSourcePolicies
      (TypedEvidenceRoute.comp embedFirstRoute collapseRoute)
      () constantFalseFamily :=
  ⟨compositeConstantRealization⟩

/-- The suffix does not support the fixed prefix realization's residual
family: it identifies the reachable first world with the unreachable second
world, on which that runner gives a different answer. -/
theorem suffix_refuses_residual_without_prefix_coverage :
    ¬ SupportsSourcePolicies collapseRoute ()
      (residualFamily adversarialPrefixRealization) := by
  apply (residualFamily adversarialPrefixRealization)
    |>.not_supportsReadout_of_policy_collision
      collapsePromoteTransport.mapHistory
      (first := [firstWorld]) (second := [secondWorld]) (by rfl)
      .value
  change false ≠ true
  decide

/-- The surjectivity hypothesis in the converse is necessary. -/
theorem no_unconditional_composite_suffix_converse :
    SupportsSourcePolicies
        (TypedEvidenceRoute.comp embedFirstRoute collapseRoute)
        () constantFalseFamily /\
      ¬ SupportsSourcePolicies collapseRoute ()
        (residualFamily adversarialPrefixRealization) /\
      ¬ Function.Surjective (embedFirstRoute.atCommand ()).mapHistory :=
  ⟨composite_supports_constant,
    suffix_refuses_residual_without_prefix_coverage,
    embedFirstRoute_not_history_surjective⟩

/-- The same counterexample satisfies the exact reached-image theorem: only
the overstrong ambient suffix claim is refused. -/
theorem counterexample_supports_reached_suffix :
    (reachedResidualFamily adversarialPrefixRealization).SupportsReadout
      (suffixReadoutOnReached embedFirstRoute collapseRoute ()) :=
  (composite_supports_iff_reached_suffix_supports
    adversarialPrefixRealization).mp composite_supports_constant

end Canary

#print axioms RoutePolicyRealization.residualFamily
#print axioms RoutePolicyRealization.compose
#print axioms RoutePolicyRealization.compose_supports
#print axioms RoutePolicyRealization.reachedSuffixOfComposite
#print axioms RoutePolicyRealization.composeFromReachedSuffix
#print axioms RoutePolicyRealization.composite_supports_iff_reached_suffix_supports
#print axioms RoutePolicyRealization.suffixOfCompositeOfSurjective
#print axioms RoutePolicyRealization.composite_supports_iff_suffix_supports_of_surjective
#print axioms Canary.collapse_then_identity_supports_length
#print axioms Canary.embedFirstRoute_not_history_surjective
#print axioms Canary.composite_supports_constant
#print axioms Canary.suffix_refuses_residual_without_prefix_coverage
#print axioms Canary.no_unconditional_composite_suffix_converse
#print axioms Canary.counterexample_supports_reached_suffix

end Mettapedia.Languages.MeTTa.Prime.GSLTILTypedEvidenceRoutePolicyComposition
