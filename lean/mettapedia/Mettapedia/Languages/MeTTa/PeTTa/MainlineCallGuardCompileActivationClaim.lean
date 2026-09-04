import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompilePremiseClaim
import Mettapedia.OSLF.Framework.SelectedNativeTypeOccurrenceStepClaim

/-!
# Exact guarded activation through generated premise claims

The occurrence-step claim already gives the exact behavioral meaning of one
selected cold rewrite: source matching, ordered authored-premise execution,
and structural target reconstruction.  The generated premise-claim row gives
an independent meaning to the middle component.

This module connects the two without duplicating either authority.  The only
explicit coverage certificate says that source matching bound every variable
used by the selected relation-query row.  Under that certificate, an exact
occurrence activation is equivalent to a source match plus the complete
ordered row of independently meaningful generated claims.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileActivationClaim

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus
open Mettapedia.OSLF.Framework.SelectedNativeTypeBoundRelationPremise
open Mettapedia.OSLF.Framework.SelectedNativeTypeBoundRelationEvidence
open Mettapedia.OSLF.Framework.SelectedNativeTypeBoundRelationClaim
open Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedOccurrenceSemantics
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileNTT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompilePremiseClaim

/-- One exact selected star/box occurrence of the cold compiler. -/
abbrev Occurrence :=
  SelectedNativeTypeContextualCalculus.Occurrence demand

/-- Claim-facing activation evidence.  It contains no completed guard result:
the target is still reconstructed from the matched source bindings. -/
structure ClaimActivation (slot : Occurrence) (before : Pattern) where
  bindings : Bindings
  matched : bindings ∈
    matchPatternForRule language (typingAt demand slot).site.rewrite before
  bound : ∀ view ∈ viewsAt premiseProfile slot,
    BoundArguments view bindings
  meanings : GroundMeanings premiseProfile relationEnv slot bindings

namespace ClaimActivation

/-- Structural target projection from the exact authored right-hand side. -/
def target {slot : Occurrence} {before : Pattern}
    (activation : ClaimActivation slot before) : Pattern :=
  applyBindingsForRule language (typingAt demand slot).site.rewrite
    activation.bindings

/-- A premise-free selected occurrence needs only its genuine source match.
The generated claim row is empty by exact decoding, rather than by a second
hand-authored classification. -/
def ofPremiseFree {slot : Occurrence} {before : Pattern}
    {bindings : Bindings}
    (premisesEmpty : (typingAt demand slot).site.rewrite.premises = [])
    (matched : bindings ∈
      matchPatternForRule language (typingAt demand slot).site.rewrite before) :
    ClaimActivation slot before := by
  have viewsEmpty : viewsAt premiseProfile slot = [] := by
    apply List.map_eq_nil_iff.mp
    simpa only [premisesEmpty] using viewsAt_encoded premiseProfile slot
  exact {
    bindings := bindings
    matched := matched
    bound := by
      intro view membership
      rw [viewsEmpty] at membership
      exact (List.not_mem_nil membership).elim
    meanings := by
      intro premise
      have impossible := premise.isLt
      have lengthZero : (viewsAt premiseProfile slot).length = 0 :=
        congrArg List.length viewsEmpty
      omega }

end ClaimActivation

/-- An ordinary proof-relevant selected activation together with evidence
that its matched environment grounds the generated premise row. -/
structure PremiseBoundSelectedActivation (slot : Occurrence)
    (before : Pattern) where
  activation : SelectedOccurrenceActivation relationEnv
    (typingAt demand slot) before
  bound : ∀ view ∈ viewsAt premiseProfile slot,
    BoundArguments view activation.initialBindings

namespace PremiseBoundSelectedActivation

/-- The exact echo-query contract makes every successful selected premise row
preserve the initial match environment. -/
theorem finalBindings_eq_initial {slot : Occurrence} {before : Pattern}
    (bounded : PremiseBoundSelectedActivation slot before) :
    bounded.activation.finalBindings = bounded.activation.initialBindings :=
  ((selectedPremisesAt_iff_claimMeanings slot bounded.bound).mp
    bounded.activation.premises).2

/-- Forget the source `PremisesAt` derivation only after recovering its
independent generated-claim meanings. -/
def toClaim {slot : Occurrence} {before : Pattern}
    (bounded : PremiseBoundSelectedActivation slot before) :
    ClaimActivation slot before where
  bindings := bounded.activation.initialBindings
  matched := bounded.activation.matched
  bound := bounded.bound
  meanings := ((selectedPremisesAt_iff_claimMeanings slot bounded.bound).mp
    bounded.activation.premises).1

/-- Claim reconstruction and source-premise execution compute the same exact
authored target. -/
@[simp] theorem toClaim_target {slot : Occurrence} {before : Pattern}
    (bounded : PremiseBoundSelectedActivation slot before) :
    bounded.toClaim.target = bounded.activation.target := by
  change applyBindingsForRule language
      (typingAt demand slot).site.rewrite bounded.activation.initialBindings =
    applyBindingsForRule language
      (typingAt demand slot).site.rewrite bounded.activation.finalBindings
  rw [bounded.finalBindings_eq_initial]

end PremiseBoundSelectedActivation

namespace ClaimActivation

/-- Reconstruct ordinary selected-premise evidence from the independently
meaningful claim row.  The cold relation environment remains the only query
authority. -/
def toPremiseBound {slot : Occurrence} {before : Pattern}
    (claim : ClaimActivation slot before) :
    PremiseBoundSelectedActivation slot before where
  activation := {
    premiseFuel := 0
    initialBindings := claim.bindings
    finalBindings := claim.bindings
    matched := claim.matched
    premises := (selectedPremisesAt_iff_claimMeanings slot claim.bound).mpr
      ⟨claim.meanings, rfl⟩ }
  bound := claim.bound

@[simp] theorem toPremiseBound_target {slot : Occurrence} {before : Pattern}
    (claim : ClaimActivation slot before) :
    claim.toPremiseBound.activation.target = claim.target := by
  rfl

end ClaimActivation

/-- Exact occurrence execution restricted to match environments that ground
the selected generated premise row. -/
def PremiseBoundOccursAt (slot : Occurrence) (before after : Pattern) : Prop :=
  ∃ bounded : PremiseBoundSelectedActivation slot before,
    bounded.activation.target = after

/-- The same restricted occurrence execution, presented entirely through
source matching and independently meaningful generated premise claims. -/
def ClaimedOccursAt (slot : Occurrence) (before after : Pattern) : Prop :=
  ∃ claim : ClaimActivation slot before, claim.target = after

/-- Exact two-way factorization of a covered occurrence activation. -/
theorem premiseBoundOccursAt_iff_claimedOccursAt
    (slot : Occurrence) (before after : Pattern) :
    PremiseBoundOccursAt slot before after ↔
      ClaimedOccursAt slot before after := by
  constructor
  · rintro ⟨bounded, targetEq⟩
    exact ⟨bounded.toClaim, bounded.toClaim_target.trans targetEq⟩
  · rintro ⟨claim, targetEq⟩
    exact ⟨claim.toPremiseBound,
      claim.toPremiseBound_target.trans targetEq⟩

/-- Proof-relevant coverage certificate for one source state.  It records
only binding support, not query truth or a target verdict. -/
def PremiseBindingCoverage (slot : Occurrence) (before : Pattern) : Type :=
  ∀ activation : SelectedOccurrenceActivation relationEnv
      (typingAt demand slot) before,
    ∀ view ∈ viewsAt premiseProfile slot,
      BoundArguments view activation.initialBindings

/-- Under explicit source-binding coverage, the existing occurrence-indexed
behavioral meaning is exactly the generated-claim activation relation. -/
theorem occurrenceMeaning_iff_claimedOccursAt
    (slot : Occurrence) (before after : Pattern)
    (coverage : PremiseBindingCoverage slot before) :
    Mettapedia.OSLF.Framework.SelectedNativeTypeOccurrenceStepClaim.View.Meaning
      relationEnv { occurrence := slot, before := before, after := after } ↔
      ClaimedOccursAt slot before after := by
  constructor
  · intro meaning
    obtain ⟨activation, targetEq⟩ :=
      (Mettapedia.OSLF.Framework.SelectedNativeTypeOccurrenceStepClaim.View.meaning_iff_exists_activation
        { occurrence := slot, before := before, after := after }).mp meaning
    exact (premiseBoundOccursAt_iff_claimedOccursAt slot before after).mp
      ⟨⟨activation, coverage activation⟩, targetEq⟩
  · intro claimed
    obtain ⟨bounded, targetEq⟩ :=
      (premiseBoundOccursAt_iff_claimedOccursAt slot before after).mpr claimed
    exact (Mettapedia.OSLF.Framework.SelectedNativeTypeOccurrenceStepClaim.View.meaning_iff_exists_activation
      { occurrence := slot, before := before, after := after }).mpr
        ⟨bounded.activation, targetEq⟩

/-- Generated claim activation is unconditionally sound for the exact
occurrence-indexed cold behavior. -/
theorem claimedOccursAt_implies_occurrenceMeaning
    (slot : Occurrence) (before after : Pattern) :
    ClaimedOccursAt slot before after →
      Mettapedia.OSLF.Framework.SelectedNativeTypeOccurrenceStepClaim.View.Meaning
        relationEnv { occurrence := slot, before := before, after := after } := by
  rintro ⟨claim, targetEq⟩
  exact (Mettapedia.OSLF.Framework.SelectedNativeTypeOccurrenceStepClaim.View.meaning_iff_exists_activation
    { occurrence := slot, before := before, after := after }).mpr
      ⟨claim.toPremiseBound.activation,
        claim.toPremiseBound_target.trans targetEq⟩

/-- Negative control schema: matching plus binding coverage cannot activate a
row when its independent generated premise meanings are absent. -/
theorem not_claimedOccursAt_of_no_ground_meanings
    (slot : Occurrence) (before after : Pattern)
    (blocked : ∀ bindings,
      bindings ∈ matchPatternForRule language
          (typingAt demand slot).site.rewrite before →
      (∀ view ∈ viewsAt premiseProfile slot,
        BoundArguments view bindings) →
      ¬ GroundMeanings premiseProfile relationEnv slot bindings) :
    ¬ ClaimedOccursAt slot before after := by
  rintro ⟨claim, _targetEq⟩
  exact blocked claim.bindings claim.matched claim.bound claim.meanings

namespace Canary

/-- The first selected slot is the star endpoint of the authored finish
transition. -/
private abbrev finishStar : Occurrence :=
  ⟨0, by
    change 0 < selectedOccurrences.length
    rw [selectedOccurrences_count]
    decide⟩

private def finishBefore : Pattern :=
  (typingAt demand finishStar).site.rewrite.left

/-- Use the real source matcher, not a separately transcribed environment. -/
private def finishBindings : Bindings :=
  (matchPatternForRule language (typingAt demand finishStar).site.rewrite
    finishBefore).head!

private theorem finish_premises_empty :
    (typingAt demand finishStar).site.rewrite.premises = [] := by
  decide +kernel

private theorem finishBindings_matches :
    finishBindings ∈ matchPatternForRule language
      (typingAt demand finishStar).site.rewrite finishBefore := by
  decide +kernel

private def finishClaim : ClaimActivation finishStar finishBefore :=
  ClaimActivation.ofPremiseFree finish_premises_empty finishBindings_matches

/-- Positive control: a real premise-free source match yields an exact
generated-claim activation and its structurally reconstructed target. -/
theorem finish_has_claimed_occurrence :
    ClaimedOccursAt finishStar finishBefore finishClaim.target :=
  ⟨finishClaim, rfl⟩

/-- Premise-free source occurrences satisfy the coverage contract
vacuously, as derived from their decoded authored premise row. -/
private def finishCoverage : PremiseBindingCoverage finishStar finishBefore := by
  intro _activation view membership
  have viewsEmpty : viewsAt premiseProfile finishStar = [] := by
    apply List.map_eq_nil_iff.mp
    simpa only [finish_premises_empty] using
      viewsAt_encoded premiseProfile finishStar
  rw [viewsEmpty] at membership
  exact (List.not_mem_nil membership).elim

/-- For the concrete finish transition, the generated presentation and the
exact occurrence-indexed behavioral meaning coincide without a residual
coverage assumption. -/
theorem finish_occurrenceMeaning_iff_claimedOccursAt (after : Pattern) :
    Mettapedia.OSLF.Framework.SelectedNativeTypeOccurrenceStepClaim.View.Meaning
      relationEnv
        { occurrence := finishStar, before := finishBefore, after := after } ↔
      ClaimedOccursAt finishStar finishBefore after :=
  occurrenceMeaning_iff_claimedOccursAt finishStar finishBefore after
    finishCoverage

end Canary

#print axioms PremiseBoundSelectedActivation.finalBindings_eq_initial
#print axioms PremiseBoundSelectedActivation.toClaim_target
#print axioms ClaimActivation.toPremiseBound_target
#print axioms premiseBoundOccursAt_iff_claimedOccursAt
#print axioms occurrenceMeaning_iff_claimedOccursAt
#print axioms claimedOccursAt_implies_occurrenceMeaning
#print axioms not_claimedOccursAt_of_no_ground_meanings
#print axioms Canary.finish_has_claimed_occurrence
#print axioms Canary.finish_occurrenceMeaning_iff_claimedOccursAt

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileActivationClaim
