import Mettapedia.Logic.MarkovLogicInfiniteCredalBridge
import Mettapedia.Logic.PLNTruthTower

/-!
# Infinite MLN Query Envelopes as PLN Width-Complement ITVs

This file connects the concrete binary DLR query-outcome projection to the
typed PLN interval layer.  The mathematical content is deliberately narrow:
the DLR query-outcome credal set is already packaged as a one-window projective
credal specification, and finite `Bool` state space lets the existing
width-complement ITV source discharge boundedness automatically.
-/

namespace Mettapedia.Logic.MarkovLogicPLNTruthBridge

open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicInfiniteSpecification
open Mettapedia.Logic.MarkovLogicInfiniteUniqueness
open Mettapedia.Logic.MarkovLogicInfiniteCredalBridge
open Mettapedia.Logic.PLNIndefiniteTruth
open Mettapedia.Logic.PLNTruthTower
open Mettapedia.ProbabilityTheory.ImpreciseProbability
open Mettapedia.ProbabilityTheory.ImpreciseProbability.ProjectiveCredal

variable {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]

/-- The true-atom gamble on `Bool` is a unit-valued gamble. -/
theorem boolTrueAtomGamble_mem_Icc (b : Bool) :
    PrecisePrevision.FiniteWeights.atomGamble true b ∈ Set.Icc (0 : ℝ) 1 := by
  cases b <;> simp [PrecisePrevision.FiniteWeights.atomGamble]

/-- Source data for viewing a finite DLR query-outcome credal envelope as a PLN
ITV whose credibility is the complement of envelope width. -/
noncomputable def dlrQueryOutcomeWidthComplementITVSource
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (q : ConstraintQuery Atom) :
    ProjectiveCredalWidthComplementITVSource.{0, 0} PUnit Bool :=
  ProjectiveCredalWidthComplementITVSource.finite
    (dlrQueryOutcomeProjectiveSpec M q)
    (dlrQueryOutcomeProjectiveSpec_hasCompatibleCompletion M q)
    (PrecisePrevision.FiniteWeights.atomGamble true)
    boolTrueAtomGamble_mem_Icc

/-- The untyped PLN ITV associated with the DLR query-outcome envelope under
the width-complement convention. -/
noncomputable def dlrQueryOutcomeWidthComplementITV
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (q : ConstraintQuery Atom) : ITV :=
  projectiveCredalWidthComplementITV
    (dlrQueryOutcomeWidthComplementITVSource M q)

/-- The typed PLN ITV associated with the DLR query-outcome envelope under the
width-complement convention. -/
noncomputable def dlrQueryOutcomeTypedWidthComplementITV
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (q : ConstraintQuery Atom) :
    TypedITV (projectiveCredalWidthComplementITVSemantics.{0, 0} PUnit Bool) :=
  TypedITV.fromProjectiveCredalWidthComplement
    (dlrQueryOutcomeWidthComplementITVSource M q)

@[simp] theorem dlrQueryOutcomeWidthComplementITV_lower
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (q : ConstraintQuery Atom) :
    (dlrQueryOutcomeWidthComplementITV M q).lower =
      infiniteMLNLowerQueryEnvelope M q := by
  unfold dlrQueryOutcomeWidthComplementITV projectiveCredalWidthComplementITV
  unfold dlrQueryOutcomeWidthComplementITVSource
  unfold ProjectiveCredalWidthComplementITVSource.finite
  change (dlrQueryOutcomeProjectiveSpec M q).globalNaturalExtension
      (PrecisePrevision.FiniteWeights.atomGamble true) =
    infiniteMLNLowerQueryEnvelope M q
  exact
    dlrQueryOutcomeProjectiveSpec_globalNaturalExtension_true_atom_eq_infiniteMLNLower
      M q

@[simp] theorem dlrQueryOutcomeWidthComplementITV_upper
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (q : ConstraintQuery Atom) :
    (dlrQueryOutcomeWidthComplementITV M q).upper =
      infiniteMLNUpperQueryEnvelope M q := by
  unfold dlrQueryOutcomeWidthComplementITV projectiveCredalWidthComplementITV
  unfold dlrQueryOutcomeWidthComplementITVSource
  unfold ProjectiveCredalWidthComplementITVSource.finite
  change upperEnvelope (dlrQueryOutcomeProjectiveSpec M q).projectiveLimitCredalSet
      (PrecisePrevision.FiniteWeights.atomGamble true) =
    infiniteMLNUpperQueryEnvelope M q
  exact dlrQueryOutcomeProjectiveSpec_upperEnvelope_true_atom_eq_infiniteMLNUpper
    M q

@[simp] theorem dlrQueryOutcomeWidthComplementITV_width
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (q : ConstraintQuery Atom) :
    (dlrQueryOutcomeWidthComplementITV M q).width =
      infiniteMLNQueryEnvelopeWidth M q := by
  unfold dlrQueryOutcomeWidthComplementITV projectiveCredalWidthComplementITV
  unfold ITV.width
  unfold dlrQueryOutcomeWidthComplementITVSource
  unfold ProjectiveCredalWidthComplementITVSource.finite
  change (dlrQueryOutcomeProjectiveSpec M q).globalEnvelopeWidth
      (PrecisePrevision.FiniteWeights.atomGamble true) =
    infiniteMLNQueryEnvelopeWidth M q
  exact
    dlrQueryOutcomeProjectiveSpec_globalEnvelopeWidth_true_atom_eq_infiniteMLNWidth
      M q

@[simp] theorem dlrQueryOutcomeWidthComplementITV_credibility
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (q : ConstraintQuery Atom) :
    (dlrQueryOutcomeWidthComplementITV M q).credibility =
      1 - infiniteMLNQueryEnvelopeWidth M q := by
  have hWidth :
      credalEnvelopeWidth
          (dlrQueryOutcomeProjectiveSpec M q).projectiveLimitCredalSet
          (PrecisePrevision.FiniteWeights.atomGamble true) =
        infiniteMLNQueryEnvelopeWidth M q := by
    simpa [ProjectiveLocalCredalSpec.globalEnvelopeWidth] using
      dlrQueryOutcomeProjectiveSpec_globalEnvelopeWidth_true_atom_eq_infiniteMLNWidth
        M q
  unfold dlrQueryOutcomeWidthComplementITV projectiveCredalWidthComplementITV
  unfold dlrQueryOutcomeWidthComplementITVSource
  unfold ProjectiveCredalWidthComplementITVSource.finite
  change (dlrQueryOutcomeProjectiveSpec M q).globalEnvelopeWidthComplement
      (PrecisePrevision.FiniteWeights.atomGamble true) =
    1 - infiniteMLNQueryEnvelopeWidth M q
  unfold ProjectiveLocalCredalSpec.globalEnvelopeWidthComplement
  unfold credalEnvelopeWidthComplement
  rw [hWidth]

theorem dlrQueryOutcomeWidthComplementITV_width_add_credibility
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (q : ConstraintQuery Atom) :
    (dlrQueryOutcomeWidthComplementITV M q).width +
        (dlrQueryOutcomeWidthComplementITV M q).credibility = 1 := by
  simpa [dlrQueryOutcomeWidthComplementITV] using
    projectiveCredalWidthComplementITV_width_add_credibility
      (dlrQueryOutcomeWidthComplementITVSource M q)

theorem dlrQueryOutcomeWidthComplementITV_width_pos_of_queryStrictWidth
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (q : ConstraintQuery Atom)
    (hWidth : dlrQueryHasStrictWidth M q) :
    0 < (dlrQueryOutcomeWidthComplementITV M q).width := by
  rw [dlrQueryOutcomeWidthComplementITV_width]
  exact infiniteMLNQueryEnvelopeWidth_pos_of_strictWidth M q hWidth

@[simp] theorem dlrQueryOutcomeTypedWidthComplementITV_lower
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (q : ConstraintQuery Atom) :
    (dlrQueryOutcomeTypedWidthComplementITV M q).lower =
      infiniteMLNLowerQueryEnvelope M q := by
  unfold dlrQueryOutcomeTypedWidthComplementITV
  unfold TypedITV.lower TypedITV.value projectiveCredalWidthComplementITVSemantics
  unfold projectiveCredalWidthComplementITV
  unfold dlrQueryOutcomeWidthComplementITVSource
  unfold ProjectiveCredalWidthComplementITVSource.finite
  change (dlrQueryOutcomeProjectiveSpec M q).globalNaturalExtension
      (PrecisePrevision.FiniteWeights.atomGamble true) =
    infiniteMLNLowerQueryEnvelope M q
  exact
    dlrQueryOutcomeProjectiveSpec_globalNaturalExtension_true_atom_eq_infiniteMLNLower
      M q

@[simp] theorem dlrQueryOutcomeTypedWidthComplementITV_upper
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (q : ConstraintQuery Atom) :
    (dlrQueryOutcomeTypedWidthComplementITV M q).upper =
      infiniteMLNUpperQueryEnvelope M q := by
  unfold dlrQueryOutcomeTypedWidthComplementITV
  unfold TypedITV.upper TypedITV.value projectiveCredalWidthComplementITVSemantics
  unfold projectiveCredalWidthComplementITV
  unfold dlrQueryOutcomeWidthComplementITVSource
  unfold ProjectiveCredalWidthComplementITVSource.finite
  change upperEnvelope (dlrQueryOutcomeProjectiveSpec M q).projectiveLimitCredalSet
      (PrecisePrevision.FiniteWeights.atomGamble true) =
    infiniteMLNUpperQueryEnvelope M q
  exact dlrQueryOutcomeProjectiveSpec_upperEnvelope_true_atom_eq_infiniteMLNUpper
    M q

@[simp] theorem dlrQueryOutcomeTypedWidthComplementITV_width
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (q : ConstraintQuery Atom) :
    (dlrQueryOutcomeTypedWidthComplementITV M q).width =
      infiniteMLNQueryEnvelopeWidth M q := by
  unfold dlrQueryOutcomeTypedWidthComplementITV
  unfold TypedITV.width TypedITV.value projectiveCredalWidthComplementITVSemantics
  unfold projectiveCredalWidthComplementITV ITV.width
  unfold dlrQueryOutcomeWidthComplementITVSource
  unfold ProjectiveCredalWidthComplementITVSource.finite
  change (dlrQueryOutcomeProjectiveSpec M q).globalEnvelopeWidth
      (PrecisePrevision.FiniteWeights.atomGamble true) =
    infiniteMLNQueryEnvelopeWidth M q
  exact
    dlrQueryOutcomeProjectiveSpec_globalEnvelopeWidth_true_atom_eq_infiniteMLNWidth
      M q

@[simp] theorem dlrQueryOutcomeTypedWidthComplementITV_credibility
    (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
    [Nonempty (DLRCompletion M)]
    (q : ConstraintQuery Atom) :
    (dlrQueryOutcomeTypedWidthComplementITV M q).credibility =
      1 - infiniteMLNQueryEnvelopeWidth M q := by
  have hWidth :
      credalEnvelopeWidth
          (dlrQueryOutcomeProjectiveSpec M q).projectiveLimitCredalSet
          (PrecisePrevision.FiniteWeights.atomGamble true) =
        infiniteMLNQueryEnvelopeWidth M q := by
    simpa [ProjectiveLocalCredalSpec.globalEnvelopeWidth] using
      dlrQueryOutcomeProjectiveSpec_globalEnvelopeWidth_true_atom_eq_infiniteMLNWidth
        M q
  unfold dlrQueryOutcomeTypedWidthComplementITV
  unfold TypedITV.credibility TypedITV.value
    projectiveCredalWidthComplementITVSemantics
  unfold projectiveCredalWidthComplementITV
  unfold dlrQueryOutcomeWidthComplementITVSource
  unfold ProjectiveCredalWidthComplementITVSource.finite
  change (dlrQueryOutcomeProjectiveSpec M q).globalEnvelopeWidthComplement
      (PrecisePrevision.FiniteWeights.atomGamble true) =
    1 - infiniteMLNQueryEnvelopeWidth M q
  unfold ProjectiveLocalCredalSpec.globalEnvelopeWidthComplement
  unfold credalEnvelopeWidthComplement
  rw [hWidth]

/-- Proof-carrying profile for the PLN-facing DLR query-outcome ITV bridge. -/
structure DLRQueryOutcomePLNBridgeProfile where
  boolTrueAtomInUnit :
    ∀ b : Bool,
      PrecisePrevision.FiniteWeights.atomGamble true b ∈ Set.Icc (0 : ℝ) 1
  lowerEqQueryLower :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (q : ConstraintQuery Atom),
      (dlrQueryOutcomeWidthComplementITV M q).lower =
        infiniteMLNLowerQueryEnvelope M q
  upperEqQueryUpper :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (q : ConstraintQuery Atom),
      (dlrQueryOutcomeWidthComplementITV M q).upper =
        infiniteMLNUpperQueryEnvelope M q
  widthEqQueryEnvelopeWidth :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (q : ConstraintQuery Atom),
      (dlrQueryOutcomeWidthComplementITV M q).width =
        infiniteMLNQueryEnvelopeWidth M q
  credibilityEqWidthComplement :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (q : ConstraintQuery Atom),
      (dlrQueryOutcomeWidthComplementITV M q).credibility =
        1 - infiniteMLNQueryEnvelopeWidth M q
  widthAddCredibility :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (q : ConstraintQuery Atom),
      (dlrQueryOutcomeWidthComplementITV M q).width +
          (dlrQueryOutcomeWidthComplementITV M q).credibility = 1
  strictWidthGivesPositiveITVWidth :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (q : ConstraintQuery Atom),
      dlrQueryHasStrictWidth M q →
        0 < (dlrQueryOutcomeWidthComplementITV M q).width
  typedLowerEqQueryLower :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (q : ConstraintQuery Atom),
      (dlrQueryOutcomeTypedWidthComplementITV M q).lower =
        infiniteMLNLowerQueryEnvelope M q
  typedUpperEqQueryUpper :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (q : ConstraintQuery Atom),
      (dlrQueryOutcomeTypedWidthComplementITV M q).upper =
        infiniteMLNUpperQueryEnvelope M q
  typedWidthEqQueryEnvelopeWidth :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (q : ConstraintQuery Atom),
      (dlrQueryOutcomeTypedWidthComplementITV M q).width =
        infiniteMLNQueryEnvelopeWidth M q
  typedCredibilityEqWidthComplement :
    ∀ {Atom ClauseId : Type*} [DecidableEq Atom] [DecidableEq ClauseId]
      (M : ClassicalInfiniteGroundMLNSpec Atom ClauseId)
      [Nonempty (DLRCompletion M)]
      (q : ConstraintQuery Atom),
      (dlrQueryOutcomeTypedWidthComplementITV M q).credibility =
        1 - infiniteMLNQueryEnvelopeWidth M q

/-- Current PLN-facing DLR query-outcome ITV bridge profile. -/
noncomputable def dlrQueryOutcomePLNBridgeProfile :
    DLRQueryOutcomePLNBridgeProfile where
  boolTrueAtomInUnit :=
    boolTrueAtomGamble_mem_Icc
  lowerEqQueryLower :=
    dlrQueryOutcomeWidthComplementITV_lower
  upperEqQueryUpper :=
    dlrQueryOutcomeWidthComplementITV_upper
  widthEqQueryEnvelopeWidth :=
    dlrQueryOutcomeWidthComplementITV_width
  credibilityEqWidthComplement :=
    dlrQueryOutcomeWidthComplementITV_credibility
  widthAddCredibility :=
    dlrQueryOutcomeWidthComplementITV_width_add_credibility
  strictWidthGivesPositiveITVWidth :=
    dlrQueryOutcomeWidthComplementITV_width_pos_of_queryStrictWidth
  typedLowerEqQueryLower :=
    dlrQueryOutcomeTypedWidthComplementITV_lower
  typedUpperEqQueryUpper :=
    dlrQueryOutcomeTypedWidthComplementITV_upper
  typedWidthEqQueryEnvelopeWidth :=
    dlrQueryOutcomeTypedWidthComplementITV_width
  typedCredibilityEqWidthComplement :=
    dlrQueryOutcomeTypedWidthComplementITV_credibility

end Mettapedia.Logic.MarkovLogicPLNTruthBridge
