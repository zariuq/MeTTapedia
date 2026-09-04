import Mettapedia.GSLT.LanguageDef.ContextualInferenceSemantics
import Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedIntroduction
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileBindingCoverage

/-!
# Coherent guarded-context semantics for the cold PeTTa call guard

The guarded source-indexed introduction syntax retains the exact authored
variable row and ordered relation-premise row.  This module gives that guard
row one proof-relevant interpretation.

A semantic world contains one source match and one binding environment, but
no relation answers.  Each guard formula contributes the meaning of its exact
authored premise occurrence at that same world.  Ordered context evidence can
therefore be assembled into one `ClaimActivation`; evidence from different
matches cannot be spliced.

The resulting guarded-support relation is proved equivalent to the existing
occurrence-indexed cold behavior.  Generated derivability and checker
acceptance do not occur in these definitions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileGuardedContextSemantics

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ContextualInference
open Mettapedia.GSLT.LanguageDef.ContextualInferenceSemantics
open Mettapedia.OSLF.Framework
open Mettapedia.OSLF.Framework.SelectedNativeTypeContextualCalculus
open Mettapedia.OSLF.Framework.SelectedNativeTypeBoundRelationClaim
open Mettapedia.OSLF.Framework.SelectedNativeTypeGuardedSourceIndexedIntroduction
open Mettapedia.OSLF.Framework.SelectedNativeTypeSourceIndexedIntroduction
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileNTT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompilePremiseClaim
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileActivationClaim
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileBindingCoverage

/-- One exact selected star/box occurrence of the cold compiler. -/
abbrev Occurrence :=
  SelectedNativeTypeContextualCalculus.Occurrence demand

/-- A candidate activation contains the common matcher world shared by every
guard formula, but contains no premise truth. -/
structure ActivationEnvironment (slot : Occurrence) (before : Pattern) where
  bindings : Bindings
  matched : bindings ∈
    matchPatternForRule language (typingAt demand slot).site.rewrite before
  bound : ∀ view ∈ viewsAt premiseProfile slot,
    SelectedNativeTypeBoundRelationEvidence.BoundArguments view bindings

namespace ActivationEnvironment

/-- Forget relation meanings from one complete activation while retaining its
single matcher world. -/
def ofClaim {slot : Occurrence} {before : Pattern}
    (claim : ClaimActivation slot before) :
    ActivationEnvironment slot before where
  bindings := claim.bindings
  matched := claim.matched
  bound := claim.bound

/-- Add the complete ordered guard meaning to one candidate world. -/
def toClaim {slot : Occurrence} {before : Pattern}
    (environment : ActivationEnvironment slot before)
    (meanings : GroundMeanings premiseProfile relationEnv slot
      environment.bindings) : ClaimActivation slot before where
  bindings := environment.bindings
  matched := environment.matched
  bound := environment.bound
  meanings := meanings

@[simp] theorem ofClaim_bindings {slot : Occurrence} {before : Pattern}
    (claim : ClaimActivation slot before) :
    (ofClaim claim).bindings = claim.bindings :=
  rfl

@[simp] theorem toClaim_target {slot : Occurrence} {before : Pattern}
    (environment : ActivationEnvironment slot before)
    (meanings : GroundMeanings premiseProfile relationEnv slot
      environment.bindings) :
    (environment.toClaim meanings).target =
      applyBindingsForRule language (typingAt demand slot).site.rewrite
        environment.bindings :=
  rfl

end ActivationEnvironment

/-- Evidence for one exact authored guard formula at one common matcher
world.  The premise coordinate and its independent relation meaning remain
proof-relevant. -/
structure GuardFormulaEvidence {slot : Occurrence} {before : Pattern}
    (environment : ActivationEnvironment slot before) (formula : Pattern) :
    Type where
  premise : Fin (viewsAt premiseProfile slot).length
  formula_eq : formula = authoredClaim premiseProfile slot premise
  meaning :
    (groundedView premiseProfile slot premise environment.bindings).Meaning
      relationEnv

/-- Context model for one exact source occurrence and source state.  Ambient
context holes remain available, but explicit formulas are interpreted only
as exact guard claims. -/
def guardModel (slot : Occurrence) (before : Pattern) :
    ContextualInferenceSemantics.Model where
  World := ActivationEnvironment slot before
  FormulaEvidence := fun environment formula =>
    GuardFormulaEvidence environment formula
  HoleEvidence := fun _environment _name => Unit

/-- Exact positional lookup in the generated authored guard row. -/
@[simp] theorem authoredClaims_get (slot : Occurrence)
    (premise : Fin (viewsAt premiseProfile slot).length) :
    (authoredClaims premiseProfile slot).get
        ⟨premise.val, by
          rw [length_authoredClaims]
          exact premise.isLt⟩ =
      authoredClaim premiseProfile slot premise := by
  simp [authoredClaims]

/-- The private premise coordinate makes two guard formulas at one occurrence
equal only when their exact authored positions agree. -/
theorem authoredClaim_premise_injective (slot : Occurrence)
    {first second : Fin (viewsAt premiseProfile slot).length}
    (equal : authoredClaim premiseProfile slot first =
      authoredClaim premiseProfile slot second) :
    first = second := by
  apply Fin.ext
  have labels := (Pattern.apply.inj equal).1
  exact (Naming.label_eq_iff _ _ _ _).mp labels |>.2

/-- Complete ordered relation meaning constructs evidence at every exact
guard-row position. -/
def guardRowEvidenceOfMeanings {slot : Occurrence} {before : Pattern}
    (environment : ActivationEnvironment slot before)
    (meanings : GroundMeanings premiseProfile relationEnv slot
      environment.bindings) :
    FormulaRowEvidence (guardModel slot before) environment
      (authoredClaims premiseProfile slot) := by
  apply FormulaRowEvidence.ofIndexed
  intro rowIndex
  let premise : Fin (viewsAt premiseProfile slot).length :=
    ⟨rowIndex.val, by simpa using rowIndex.isLt⟩
  have formulaExact :
      (authoredClaims premiseProfile slot).get rowIndex =
        authoredClaim premiseProfile slot premise := by
    simp [authoredClaims, premise]
  exact
    { premise := premise
      formula_eq := formulaExact
      meaning := meanings premise }

/-- Ordered guard-row evidence reconstructs the complete relation meaning at
the one shared matcher world. -/
def meaningsOfGuardRowEvidence {slot : Occurrence} {before : Pattern}
    (environment : ActivationEnvironment slot before)
    (evidence : FormulaRowEvidence (guardModel slot before) environment
      (authoredClaims premiseProfile slot)) :
    GroundMeanings premiseProfile relationEnv slot environment.bindings := by
  intro premise
  let rowIndex : Fin (authoredClaims premiseProfile slot).length :=
    ⟨premise.val, by
      rw [length_authoredClaims]
      exact premise.isLt⟩
  have evidenceAt := evidence.get rowIndex
  change GuardFormulaEvidence environment
    ((authoredClaims premiseProfile slot).get rowIndex) at evidenceAt
  have formulaExact :
      (authoredClaims premiseProfile slot).get rowIndex =
        authoredClaim premiseProfile slot premise := by
    simp [authoredClaims, rowIndex]
  have samePremise : premise = evidenceAt.premise :=
    authoredClaim_premise_injective slot
      (formulaExact.symm.trans evidenceAt.formula_eq)
  simpa only [samePremise] using evidenceAt.meaning

/-- Exact correspondence between ordered context evidence and the complete
independent meaning of the authored relation row. -/
theorem guardRowSatisfies_iff_groundMeanings
    {slot : Occurrence} {before : Pattern}
    (environment : ActivationEnvironment slot before) :
    FormulaRowSatisfies (guardModel slot before) environment
        (authoredClaims premiseProfile slot) ↔
      GroundMeanings premiseProfile relationEnv slot environment.bindings := by
  constructor
  · rintro ⟨evidence⟩
    exact meaningsOfGuardRowEvidence environment evidence
  · intro meanings
    exact ⟨guardRowEvidenceOfMeanings environment meanings⟩

/-- The retained conclusion guard context has exactly the same meaning as the
complete ordered cold premise row.  The ambient relation hole contributes no
guard authority. -/
theorem guardContextSatisfies_iff_groundMeanings
    {slot : Occurrence} {before : Pattern}
    (environment : ActivationEnvironment slot before) :
    ContextSatisfies (guardModel slot before) environment
        (guardedConclusionRelationContext premiseProfile slot) ↔
      GroundMeanings premiseProfile relationEnv slot environment.bindings := by
  change
    ContextSatisfies (guardModel slot before) environment
        (ContextSchema.prepend (authoredClaims premiseProfile slot) delta) ↔ _
  rw [contextSatisfies_prepend_iff,
    guardRowSatisfies_iff_groundMeanings]
  constructor
  · exact And.left
  · intro meanings
    exact ⟨meanings, ⟨.hole "Delta" ()⟩⟩

/-- Behavior presented by one common source match plus its retained guarded
context and exact structural target. -/
def GuardedSupportOccursAt (slot : Occurrence)
    (before after : Pattern) : Prop :=
  ∃ environment : ActivationEnvironment slot before,
    ContextSatisfies (guardModel slot before) environment
        (guardedConclusionRelationContext premiseProfile slot) ∧
      applyBindingsForRule language (typingAt demand slot).site.rewrite
        environment.bindings = after

/-- Retained contextual support is exactly one bundled claim activation; no
guard evidence may be assembled from different matches. -/
theorem guardedSupportOccursAt_iff_claimedOccursAt
    (slot : Occurrence) (before after : Pattern) :
    GuardedSupportOccursAt slot before after ↔
      ClaimedOccursAt slot before after := by
  constructor
  · rintro ⟨environment, support, targetEq⟩
    let meanings :=
      (guardContextSatisfies_iff_groundMeanings environment).mp support
    exact ⟨environment.toClaim meanings,
      ActivationEnvironment.toClaim_target environment meanings |>.trans
        targetEq⟩
  · rintro ⟨claim, targetEq⟩
    let environment := ActivationEnvironment.ofClaim claim
    have support :
        ContextSatisfies (guardModel slot before) environment
          (guardedConclusionRelationContext premiseProfile slot) :=
      (guardContextSatisfies_iff_groundMeanings environment).mpr claim.meanings
    exact ⟨environment, support, targetEq⟩

/-- Crown semantic bridge: the retained guarded context is exactly the
already-proved occurrence-indexed cold behavior. -/
theorem guardedSupportOccursAt_iff_occurrenceMeaning
    (slot : Occurrence) (before after : Pattern) :
    GuardedSupportOccursAt slot before after ↔
      Mettapedia.OSLF.Framework.SelectedNativeTypeOccurrenceStepClaim.View.Meaning
        relationEnv { occurrence := slot, before := before, after := after } := by
  rw [guardedSupportOccursAt_iff_claimedOccursAt]
  exact (occurrenceMeaning_iff_claimedOccursAt_exact slot before after).symm

/-! ## Negative controls -/

/-- A candidate source match cannot satisfy the retained guard context when
one of its exact independent premise meanings is absent. -/
theorem not_guardContextSatisfies_of_missing_meaning
    {slot : Occurrence} {before : Pattern}
    (environment : ActivationEnvironment slot before)
    (blocked : ¬ GroundMeanings premiseProfile relationEnv slot
      environment.bindings) :
    ¬ ContextSatisfies (guardModel slot before) environment
      (guardedConclusionRelationContext premiseProfile slot) := by
  rw [guardContextSatisfies_iff_groundMeanings]
  exact blocked

/-- Exact target mismatch cannot be hidden by a satisfying guard context. -/
theorem not_guardedSupportOccursAt_of_target_ne
    (slot : Occurrence) (before after : Pattern)
    (different : ∀ environment : ActivationEnvironment slot before,
      applyBindingsForRule language (typingAt demand slot).site.rewrite
        environment.bindings ≠ after) :
    ¬ GuardedSupportOccursAt slot before after := by
  rintro ⟨environment, _support, targetEq⟩
  exact different environment targetEq

#print axioms authoredClaim_premise_injective
#print axioms guardRowSatisfies_iff_groundMeanings
#print axioms guardContextSatisfies_iff_groundMeanings
#print axioms guardedSupportOccursAt_iff_claimedOccursAt
#print axioms guardedSupportOccursAt_iff_occurrenceMeaning
#print axioms not_guardContextSatisfies_of_missing_meaning
#print axioms not_guardedSupportOccursAt_of_target_ne

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardCompileGuardedContextSemantics
