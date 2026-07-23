import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Selection
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ScopeObservation
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.FreshnessCore

/-!
# Equivariance of branch-valued type selection

Function signatures are alpha-localized at the specification boundary while
the repaired runtime scans the corresponding raw signatures.  This module
transports the complete branch-valued applicability derivation across one
finite permutation.  Success order, failed alternatives, and diagnostic
ledger order remain explicit; only private type-variable spelling changes.

The carrier is semantic.  It relates finite presentations by conjugating
their valuation theories rather than inventing a syntactic renaming operation
on the oriented `TypeSubst` representation.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.SelectionEquivariance

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Bindings.ScopeObservation
open Spec.Type.Presentation
open Spec.Type.Presentation.Alpha
open Spec.Type.Presentation.ApplicationEquivariance
open Spec.Type.Presentation.Completeness
open Spec.Type.Presentation.Exact
open Spec.Type.Presentation.ExactNormal
open Spec.Type.Presentation.Freshness
open Spec.Type.Presentation.MatchSolutionTheory
open Spec.Type.Presentation.PrincipalAlpha
open Spec.Type.Presentation.ScopeObservation
open Spec.Type.Presentation.Selection
open Spec.Type.Presentation.Theory
open Spec.Type.RuntimeRefinement

/-- Two finite presentations are the same constraint theory after renaming
the left-hand variables by `permutation`.  The right valuation therefore
corresponds to the left valuation precomposed with that permutation. -/
def TypePresentationPermutationEquiv
    (permutation : Equiv.Perm String) (left right : TypeSubst) : Prop :=
  ∀ valuation,
    TypeSubstSatisfied valuation right ↔
      TypeSubstSatisfied (valuation ∘ permutation) left

/-- Normality and semantic permutation equivalence travel together through
the branch scan.  Normality is construction evidence needed by the exact
presentation completeness theorem, not an assumption hidden in the
equivalence carrier. -/
structure TypePresentationPermutationState
    (permutation : Equiv.Perm String) (left right : TypeSubst) : Prop where
  leftNormal : left.Normal
  rightNormal : right.Normal
  theory : TypePresentationPermutationEquiv permutation left right

/-- Empty presentations are fixed by every type-variable permutation. -/
theorem TypePresentationPermutationState.empty
    (permutation : Equiv.Perm String) :
    TypePresentationPermutationState permutation [] [] := by
  refine ⟨TypeSubst.normal_empty, TypeSubst.normal_empty, ?_⟩
  intro valuation
  simp [TypeSubstSatisfied]

/-- A permutation-fixed atom is also fixed by the inverse permutation. -/
theorem renameTypeVars_symm_eq_of_eq
    (permutation : Equiv.Perm String) {atom : Atom}
    (fixed : renameTypeVars permutation atom = atom) :
    renameTypeVars permutation.symm atom = atom := by
  calc
    renameTypeVars permutation.symm atom =
        renameTypeVars permutation.symm
          (renameTypeVars permutation atom) := by rw [fixed]
    _ = renameTypeVars (permutation.symm ∘ permutation) atom :=
      renameTypeVars_comp _ _ _
    _ = atom := by
      rw [show permutation.symm ∘ permutation = id by funext name; simp]
      exact renameTypeVars_id atom

/-- Semantic permutation equivalence is symmetric after inverting the
permutation. -/
theorem TypePresentationPermutationState.symm
    {permutation : Equiv.Perm String} {left right : TypeSubst}
    (state : TypePresentationPermutationState permutation left right) :
    TypePresentationPermutationState permutation.symm right left := by
  refine ⟨state.rightNormal, state.leftNormal, ?_⟩
  intro valuation
  have forward := state.theory (valuation ∘ permutation.symm)
  have composition :
      (valuation ∘ permutation.symm) ∘ permutation = valuation := by
    funext name
    simp
  rw [composition] at forward
  exact forward.symm

/-- Applying permutation-related normal presentations to corresponding atoms
produces alpha-equivalent observations. -/
theorem TypePresentationPermutationState.observedTypeAlpha
    {permutation : Equiv.Perm String} {left right : TypeSubst}
    (state : TypePresentationPermutationState permutation left right)
    (atom : Atom) :
    ObservedTypeAlphaRel
      (left.apply atom)
      (right.apply (renameTypeVars permutation atom)) := by
  let rightCanonical := presentedValuation right
  have rightSatisfied : TypeSubstSatisfied rightCanonical right :=
    normal_presentedValuation_satisfied state.rightNormal
  have leftSatisfied : TypeSubstSatisfied
      (rightCanonical ∘ permutation) left :=
    (state.theory rightCanonical).mp rightSatisfied
  have rightInstance : ∃ forward : String → Atom,
      applyTypeValuation forward (left.apply atom) =
        right.apply (renameTypeVars permutation atom) := by
    refine ⟨rightCanonical ∘ permutation, ?_⟩
    calc
      applyTypeValuation (rightCanonical ∘ permutation) (left.apply atom) =
          applyTypeValuation (rightCanonical ∘ permutation) atom := by
        simpa [applyTypeValuation_presented_eq_apply] using
          typeSubst_factorization leftSatisfied atom
      _ = applyTypeValuation rightCanonical
          (renameTypeVars permutation atom) := by
        symm
        exact applyTypeValuation_renameTypeVars
          rightCanonical permutation atom
      _ = right.apply (renameTypeVars permutation atom) := by
        simp [rightCanonical, applyTypeValuation_presented_eq_apply]
  let leftCanonical := presentedValuation left
  have leftCanonicalSatisfied : TypeSubstSatisfied leftCanonical left :=
    normal_presentedValuation_satisfied state.leftNormal
  let transportedLeft : String → Atom := leftCanonical ∘ permutation.symm
  have rightTransportedSatisfied : TypeSubstSatisfied transportedLeft right := by
    apply (state.theory transportedLeft).mpr
    simpa [transportedLeft, Function.comp_def] using leftCanonicalSatisfied
  have leftInstance : ∃ backward : String → Atom,
      applyTypeValuation backward
          (right.apply (renameTypeVars permutation atom)) =
        left.apply atom := by
    refine ⟨transportedLeft, ?_⟩
    calc
      applyTypeValuation transportedLeft
          (right.apply (renameTypeVars permutation atom)) =
          applyTypeValuation transportedLeft
            (renameTypeVars permutation atom) := by
        simpa [applyTypeValuation_presented_eq_apply] using
          typeSubst_factorization rightTransportedSatisfied
            (renameTypeVars permutation atom)
      _ = applyTypeValuation
          (transportedLeft ∘ permutation) atom :=
        applyTypeValuation_renameTypeVars
          transportedLeft permutation atom
      _ = applyTypeValuation leftCanonical atom := by
        apply applyTypeValuation_congr_of_typeVars atom
        intro name _
        simp [transportedLeft]
      _ = left.apply atom := by
        simp [leftCanonical, applyTypeValuation_presented_eq_apply]
  exact observedTypeAlpha_of_mutual_instances rightInstance leftInstance

/-- If the permutation fixes a public observation scope, semantic
permutation equivalence specializes to ordinary scoped theory equivalence. -/
theorem TypePresentationPermutationState.theoryEquivAt
    {permutation : Equiv.Perm String} {left right : TypeSubst}
    (state : TypePresentationPermutationState permutation left right)
    (scope : List String)
    (scopeFixed : ∀ name, name ∈ scope → permutation name = name) :
    TypePresentationTheoryEquivAt scope left right := by
  constructor
  · intro leftModel leftSatisfied
    let rightModel : String → Atom := leftModel ∘ permutation.symm
    have rightSatisfied : TypeSubstSatisfied rightModel right := by
      apply (state.theory rightModel).mpr
      simpa [rightModel, Function.comp_def] using leftSatisfied
    refine ⟨rightModel, rightSatisfied, ?_⟩
    intro name member
    have inverseFixed : permutation.symm name = name := by
      apply permutation.injective
      simp [scopeFixed name member]
    simp [rightModel, inverseFixed]
  · intro rightModel rightSatisfied
    let leftModel : String → Atom := rightModel ∘ permutation
    have leftSatisfied : TypeSubstSatisfied leftModel left :=
      (state.theory rightModel).mp rightSatisfied
    refine ⟨leftModel, leftSatisfied, ?_⟩
    intro name member
    simp [leftModel, scopeFixed name member]

/-- Post-composing a raw-signature runtime simulation with a public-fixed
signature localization yields the corresponding localized simulation. -/
theorem TypePresentationPermutationState.composeScopedRuntime
    {permutation : Equiv.Perm String} {raw localized : TypeSubst}
    {scope : List String} {runtime : Metta.Bindings}
    (state : TypePresentationPermutationState permutation raw localized)
    (scopeFixed : ∀ name, name ∈ scope → permutation name = name)
    (runtimeState : ScopedTypePresentationSimulationState
      scope raw runtime) :
    ScopedTypePresentationSimulationState scope localized runtime := by
  rcases runtimeState with
    ⟨_rawNormal, branchPresentation, specBindings,
      branchState, rawBranchEquiv⟩
  exact ⟨state.rightNormal, branchPresentation, specBindings, branchState,
    (state.theoryEquivAt scope scopeFixed).symm.trans rawBranchEquiv⟩

/-- Extending corresponding incoming theories by corresponding type
constraints preserves semantic permutation equivalence of the exact finite
outputs. -/
theorem CorePlusR2TypePresentationMatchRel.output_permutationState
    {permutation : Equiv.Perm String}
    {leftIncoming rightIncoming leftOutput rightOutput : TypeSubst}
    {leftExpected actual : Atom}
    (state : TypePresentationPermutationState permutation
      leftIncoming rightIncoming)
    (actualFixed : renameTypeVars permutation actual = actual)
    (leftDerivation : CorePlusR2TypePresentationMatchRel
      leftIncoming leftExpected actual leftOutput)
    (rightDerivation : CorePlusR2TypePresentationMatchRel
      rightIncoming (renameTypeVars permutation leftExpected)
        actual rightOutput) :
    TypePresentationPermutationState permutation leftOutput rightOutput := by
  refine ⟨leftDerivation.output_normal state.leftNormal,
    rightDerivation.output_normal state.rightNormal, ?_⟩
  intro valuation
  rw [CorePlusR2TypePresentationMatchRel.solutions
      rightDerivation state.rightNormal valuation,
    CorePlusR2TypePresentationMatchRel.solutions
      leftDerivation state.leftNormal (valuation ∘ permutation),
    state.theory valuation]
  apply and_congr Iff.rfl
  have renamed := corePlusR2TypeConsistent_rename_iff
    valuation permutation leftExpected actual
  simpa [actualFixed] using renamed

/-- Fully simultaneous constraint renaming is the primitive equivariance
step.  The argument-specific theorem above is its public-fixed specialization;
the expected-return scan uses this general form because the declared return
is localized together with the formal list. -/
theorem CorePlusR2TypePresentationMatchRel.output_both_permutationState
    {permutation : Equiv.Perm String}
    {leftIncoming rightIncoming leftOutput rightOutput : TypeSubst}
    {leftExpected leftActual : Atom}
    (state : TypePresentationPermutationState permutation
      leftIncoming rightIncoming)
    (leftDerivation : CorePlusR2TypePresentationMatchRel
      leftIncoming leftExpected leftActual leftOutput)
    (rightDerivation : CorePlusR2TypePresentationMatchRel
      rightIncoming (renameTypeVars permutation leftExpected)
        (renameTypeVars permutation leftActual) rightOutput) :
    TypePresentationPermutationState permutation leftOutput rightOutput := by
  refine ⟨leftDerivation.output_normal state.leftNormal,
    rightDerivation.output_normal state.rightNormal, ?_⟩
  intro valuation
  rw [CorePlusR2TypePresentationMatchRel.solutions
      rightDerivation state.rightNormal valuation,
    CorePlusR2TypePresentationMatchRel.solutions
      leftDerivation state.leftNormal (valuation ∘ permutation),
    state.theory valuation]
  exact and_congr Iff.rfl
    (corePlusR2TypeConsistent_rename_iff
      valuation permutation leftExpected leftActual)

/-- A successful exact match reconstructs across a simultaneous permutation
of both constraint atoms. -/
theorem CorePlusR2TypePresentationMatchRel.map_both_permutation
    {permutation : Equiv.Perm String}
    {leftIncoming rightIncoming leftOutput : TypeSubst}
    {leftExpected leftActual : Atom}
    (state : TypePresentationPermutationState permutation
      leftIncoming rightIncoming)
    (leftDerivation : CorePlusR2TypePresentationMatchRel
      leftIncoming leftExpected leftActual leftOutput) :
    ∃ rightOutput,
      CorePlusR2TypePresentationMatchRel rightIncoming
        (renameTypeVars permutation leftExpected)
        (renameTypeVars permutation leftActual) rightOutput ∧
      TypePresentationPermutationState permutation leftOutput rightOutput := by
  let leftCanonical := presentedValuation leftOutput
  have leftOutputSatisfied : TypeSubstSatisfied leftCanonical leftOutput :=
    normal_presentedValuation_satisfied
      (leftDerivation.output_normal state.leftNormal)
  obtain ⟨leftIncomingSatisfied, leftConsistent⟩ :=
    (CorePlusR2TypePresentationMatchRel.solutions
      leftDerivation state.leftNormal leftCanonical).mp leftOutputSatisfied
  let rightModel : String → Atom := leftCanonical ∘ permutation.symm
  have rightIncomingSatisfied :
      TypeSubstSatisfied rightModel rightIncoming := by
    apply (state.theory rightModel).mpr
    simpa [rightModel, Function.comp_def] using leftIncomingSatisfied
  have modelEquation : rightModel ∘ permutation = leftCanonical := by
    funext name
    simp [rightModel]
  have rightConsistent : CorePlusR2TypeConsistent rightModel
      (renameTypeVars permutation leftExpected)
      (renameTypeVars permutation leftActual) := by
    apply (corePlusR2TypeConsistent_rename_iff
      rightModel permutation leftExpected leftActual).mpr
    simpa [modelEquation] using leftConsistent
  obtain ⟨rightOutput, rightDerivation, _rightNormal, _rightSatisfied⟩ :=
    CorePlusR2TypePresentationMatchRel.exists_of_satisfied
      state.rightNormal rightIncomingSatisfied
        (renameTypeVars permutation leftExpected)
        (renameTypeVars permutation leftActual) rightConsistent
  exact ⟨rightOutput, rightDerivation,
    Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.SelectionEquivariance.CorePlusR2TypePresentationMatchRel.output_both_permutationState
      state leftDerivation rightDerivation⟩

/-- Exact failure is invariant under simultaneous permutation of the two
constraint atoms. -/
theorem corePlusR2TypePresentationMatch_none_map_both_permutation
    {permutation : Equiv.Perm String}
    {leftIncoming rightIncoming : TypeSubst}
    {leftExpected leftActual : Atom}
    (state : TypePresentationPermutationState permutation
      leftIncoming rightIncoming)
    (leftFailure : ∀ output,
      ¬CorePlusR2TypePresentationMatchRel
        leftIncoming leftExpected leftActual output) :
    ∀ output,
      ¬CorePlusR2TypePresentationMatchRel rightIncoming
        (renameTypeVars permutation leftExpected)
        (renameTypeVars permutation leftActual) output := by
  intro rightOutput rightDerivation
  have reverseState := state.symm
  obtain ⟨leftOutput, leftDerivation, _⟩ :=
    Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.SelectionEquivariance.CorePlusR2TypePresentationMatchRel.map_both_permutation
      reverseState rightDerivation
  have expectedEquation :
      renameTypeVars permutation.symm
          (renameTypeVars permutation leftExpected) = leftExpected := by
    rw [renameTypeVars_comp]
    have composition : permutation.symm ∘ permutation = id := by
      funext name
      simp
    rw [composition, renameTypeVars_id]
  have actualEquation :
      renameTypeVars permutation.symm
          (renameTypeVars permutation leftActual) = leftActual := by
    rw [renameTypeVars_comp]
    have composition : permutation.symm ∘ permutation = id := by
      funext name
      simp
    rw [composition, renameTypeVars_id]
  rw [expectedEquation, actualEquation] at leftDerivation
  exact leftFailure leftOutput leftDerivation

/-- One successful exact match against a raw formal reconstructs a matching
output for the alpha-localized formal, retaining the semantic permutation
state. -/
theorem CorePlusR2TypePresentationMatchRel.map_expected_permutation
    {permutation : Equiv.Perm String}
    {leftIncoming rightIncoming leftOutput : TypeSubst}
    {leftExpected actual : Atom}
    (state : TypePresentationPermutationState permutation
      leftIncoming rightIncoming)
    (actualFixed : renameTypeVars permutation actual = actual)
    (leftDerivation : CorePlusR2TypePresentationMatchRel
      leftIncoming leftExpected actual leftOutput) :
    ∃ rightOutput,
      CorePlusR2TypePresentationMatchRel
        rightIncoming (renameTypeVars permutation leftExpected)
          actual rightOutput ∧
      TypePresentationPermutationState permutation leftOutput rightOutput := by
  let leftCanonical := presentedValuation leftOutput
  have leftOutputSatisfied : TypeSubstSatisfied leftCanonical leftOutput :=
    normal_presentedValuation_satisfied
      (leftDerivation.output_normal state.leftNormal)
  obtain ⟨leftIncomingSatisfied, leftConsistent⟩ :=
    (CorePlusR2TypePresentationMatchRel.solutions
      leftDerivation state.leftNormal leftCanonical).mp leftOutputSatisfied
  let rightModel : String → Atom := leftCanonical ∘ permutation.symm
  have rightIncomingSatisfied :
      TypeSubstSatisfied rightModel rightIncoming := by
    apply (state.theory rightModel).mpr
    simpa [rightModel, Function.comp_def] using leftIncomingSatisfied
  have rightConsistent : CorePlusR2TypeConsistent rightModel
      (renameTypeVars permutation leftExpected) actual := by
    have modelEquation : rightModel ∘ permutation = leftCanonical := by
      funext name
      simp [rightModel]
    have renamed := (corePlusR2TypeConsistent_rename_iff
      rightModel permutation leftExpected actual).mpr
        (by simpa [modelEquation] using leftConsistent)
    simpa [actualFixed] using renamed
  obtain ⟨rightOutput, rightDerivation, _rightNormal, _rightSatisfied⟩ :=
    CorePlusR2TypePresentationMatchRel.exists_of_satisfied
      state.rightNormal rightIncomingSatisfied
        (renameTypeVars permutation leftExpected) actual rightConsistent
  exact ⟨rightOutput, rightDerivation,
    Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.SelectionEquivariance.CorePlusR2TypePresentationMatchRel.output_permutationState
      state actualFixed leftDerivation rightDerivation⟩

/-- Exact failure is preserved when a raw formal is alpha-localized while
the actual candidate is fixed. -/
theorem corePlusR2TypePresentationMatch_none_map_expected_permutation
    {permutation : Equiv.Perm String}
    {leftIncoming rightIncoming : TypeSubst}
    {leftExpected actual : Atom}
    (state : TypePresentationPermutationState permutation
      leftIncoming rightIncoming)
    (actualFixed : renameTypeVars permutation actual = actual)
    (leftFailure : ∀ output,
      ¬CorePlusR2TypePresentationMatchRel
        leftIncoming leftExpected actual output) :
    ∀ output,
      ¬CorePlusR2TypePresentationMatchRel rightIncoming
        (renameTypeVars permutation leftExpected) actual output := by
  intro rightOutput rightDerivation
  have reverseState := state.symm
  have inverseActualFixed :=
    renameTypeVars_symm_eq_of_eq permutation actualFixed
  have reverseExpected :
      renameTypeVars permutation.symm
          (renameTypeVars permutation leftExpected) = leftExpected := by
    rw [renameTypeVars_comp]
    have composition : permutation.symm ∘ permutation = id := by
      funext name
      simp
    rw [composition, renameTypeVars_id]
  obtain ⟨leftOutput, leftDerivation, _⟩ :=
    Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.SelectionEquivariance.CorePlusR2TypePresentationMatchRel.map_expected_permutation
      reverseState inverseActualFixed rightDerivation
  rw [reverseExpected] at leftDerivation
  exact leftFailure leftOutput leftDerivation

/-! ## One argument and the diagnostic ledger -/

/-- Pointwise semantic permutation correspondence for an ordered list of
branch presentations. -/
def TypePresentationPermutationStates
    (permutation : Equiv.Perm String) :
    List TypeSubst → List TypeSubst → Prop :=
  List.Forall₂ (TypePresentationPermutationState permutation)

/-- Signature localization may rename the displayed formal type, while the
candidate type is fixed by the public-fixed permutation.  Position remains
literal. -/
structure ArgumentTypeDiagnosticAlphaRel
    (left right : ArgumentTypeDiagnostic) : Prop where
  position : left.position = right.position
  expected : ObservedTypeAlphaRel left.expected right.expected
  actual : ObservedTypeAlphaRel left.actual right.actual

/-- Return diagnostics retain the boundary expected type literally and
compare the presentation-applied declared return up to alpha. -/
structure ExpectedReturnDiagnosticAlphaRel
    (left right : ExpectedReturnDiagnostic) : Prop where
  expected : left.expected = right.expected
  actual : ObservedTypeAlphaRel left.actual right.actual

/-- Exact branch outcomes preserve success order, failure multiplicity, and
diagnostic order under signature localization. -/
structure ArgumentCandidateListsBranchOutcomePermutationRel
    (permutation : Equiv.Perm String)
    (left right : ArgumentCandidateListsBranchOutcome) : Prop where
  successes : TypePresentationPermutationStates permutation
    left.successes right.successes
  errors : List.Forall₂ ArgumentTypeDiagnosticAlphaRel
    left.errors right.errors

/-- Expected-return filtering preserves its selected presentation and
ordered mismatch ledger under signature localization. -/
structure ExpectedReturnBranchOutcomePermutationRel
    (permutation : Equiv.Perm String)
    (left right : ExpectedReturnBranchOutcome) : Prop where
  selected : Option.Rel (TypePresentationPermutationState permutation)
    left.selected right.selected
  errors : List.Forall₂ ExpectedReturnDiagnosticAlphaRel
    left.errors right.errors

/-! ## Extending one private signature renaming while fixing candidates -/

/-- Two independently freshened presentations of one signature admit one
global permutation that maps the complete signature and fixes every already
prepared candidate atom.  Separation from the candidate family is the exact
side condition: no ordering or pairwise-disjointness assumption is imposed
inside that family.

This is the signature-localization boundary used by the branch scan.  It is
stronger than an arbitrary alpha witness because argument candidates must
remain literal for diagnostic order and multiplicity. -/
theorem TypeCandidateAlphaVariantRel.exists_permutation_fixing_family
    {leftAvoid rightAvoid : List String}
    {source left right : Atom} {family : List Atom}
    (leftVariant : TypeCandidateAlphaVariantRel leftAvoid source left)
    (rightVariant : TypeCandidateAlphaVariantRel rightAvoid source right)
    (leftSeparated : FreshFamiliesSeparated [left] family)
    (rightSeparated : FreshFamiliesSeparated [right] family) :
    ∃ permutation : Equiv.Perm String,
      right = renameTypeVars permutation left ∧
        ∀ candidate ∈ family,
          renameTypeVars permutation candidate = candidate := by
  classical
  rcases leftVariant with
    ⟨leftRename, leftInjective, leftEquation, _leftFresh⟩
  rcases rightVariant with
    ⟨rightRename, rightInjective, rightEquation, _rightFresh⟩
  let SourceVariable :=
    {name : String // name ∈ TypeSubst.typeVars source}
  let FixedVariable :=
    {name : String // name ∈ TypeSubst.typeVarsList family}
  let ScopedVariable := Sum SourceVariable FixedVariable
  let leftImage : ScopedVariable → String
    | .inl name => leftRename name.1
    | .inr name => name.1
  let rightImage : ScopedVariable → String
    | .inl name => rightRename name.1
    | .inr name => name.1
  have leftTargetMember (name : SourceVariable) :
      leftRename name.1 ∈ TypeSubst.typeVars left := by
    rw [leftEquation, typeVars_renameTypeVars]
    exact List.mem_map.mpr ⟨name.1, name.2, rfl⟩
  have rightTargetMember (name : SourceVariable) :
      rightRename name.1 ∈ TypeSubst.typeVars right := by
    rw [rightEquation, typeVars_renameTypeVars]
    exact List.mem_map.mpr ⟨name.1, name.2, rfl⟩
  have leftImageInjective : Function.Injective leftImage := by
    intro first second equality
    cases first with
    | inl first =>
        cases second with
        | inl second =>
            apply congrArg Sum.inl
            apply Subtype.ext
            exact leftInjective (by simpa [leftImage] using equality)
        | inr second =>
            exfalso
            have forbidden : leftRename first.1 ∉
                TypeSubst.typeVarsList family :=
              leftSeparated _ (by
                simp [TypeSubst.typeVarsList, leftTargetMember first])
            apply forbidden
            have imageEquality : leftRename first.1 = second.1 := by
              simpa [leftImage] using equality
            rw [imageEquality]
            exact second.2
    | inr first =>
        cases second with
        | inl second =>
            exfalso
            have forbidden : leftRename second.1 ∉
                TypeSubst.typeVarsList family :=
              leftSeparated _ (by
                simp [TypeSubst.typeVarsList, leftTargetMember second])
            apply forbidden
            have imageEquality : first.1 = leftRename second.1 := by
              simpa [leftImage] using equality
            rw [← imageEquality]
            exact first.2
        | inr second =>
            apply congrArg Sum.inr
            apply Subtype.ext
            simpa [leftImage] using equality
  have rightImageInjective : Function.Injective rightImage := by
    intro first second equality
    cases first with
    | inl first =>
        cases second with
        | inl second =>
            apply congrArg Sum.inl
            apply Subtype.ext
            exact rightInjective (by simpa [rightImage] using equality)
        | inr second =>
            exfalso
            have forbidden : rightRename first.1 ∉
                TypeSubst.typeVarsList family :=
              rightSeparated _ (by
                simp [TypeSubst.typeVarsList, rightTargetMember first])
            apply forbidden
            have imageEquality : rightRename first.1 = second.1 := by
              simpa [rightImage] using equality
            rw [imageEquality]
            exact second.2
    | inr first =>
        cases second with
        | inl second =>
            exfalso
            have forbidden : rightRename second.1 ∉
                TypeSubst.typeVarsList family :=
              rightSeparated _ (by
                simp [TypeSubst.typeVarsList, rightTargetMember second])
            apply forbidden
            have imageEquality : first.1 = rightRename second.1 := by
              simpa [rightImage] using equality
            rw [← imageEquality]
            exact first.2
        | inr second =>
            apply congrArg Sum.inr
            apply Subtype.ext
            simpa [rightImage] using equality
  obtain ⟨permutation, extensionLaw⟩ :=
    Equiv.Perm.exists_extending_pair leftImage rightImage
      leftImageInjective rightImageInjective
  have sourceAgreement : ∀ name,
      name ∈ TypeSubst.typeVars source →
        permutation (leftRename name) = rightRename name := by
    intro name member
    simpa [leftImage, rightImage] using
      extensionLaw (Sum.inl ⟨name, member⟩)
  have fixedAgreement : ∀ name,
      name ∈ TypeSubst.typeVarsList family → permutation name = name := by
    intro name member
    simpa [leftImage, rightImage] using
      extensionLaw (Sum.inr ⟨name, member⟩)
  refine ⟨permutation, ?_, ?_⟩
  · rw [leftEquation, rightEquation, renameTypeVars_comp]
    apply renameTypeVars_congr_on_typeVars source
    intro name member
    exact (sourceAgreement name member).symm
  · intro candidate member
    calc
      renameTypeVars permutation candidate =
          renameTypeVars id candidate := by
        apply renameTypeVars_congr_on_typeVars candidate
        intro name occurrence
        simpa using fixedAgreement name
          (Spec.Type.Presentation.Freshness.typeVars_mem_typeVarsList_of_mem
            member name occurrence)
      _ = candidate := renameTypeVars_id candidate

/-- Localizing the formal of one argument preserves the complete
all-candidate classification.  Candidate order and the failed-actual list
remain literal because the permutation fixes every candidate atom. -/
theorem ActualTypeCandidateBranchesRel.map_expected_permutation
    {permutation : Equiv.Perm String}
    {leftIncoming rightIncoming : TypeSubst}
    {leftExpected : Atom} {candidates : List Atom}
    {leftOutputs : List TypeSubst} {failedActuals : List Atom}
    (state : TypePresentationPermutationState permutation
      leftIncoming rightIncoming)
    (candidatesFixed : ∀ candidate ∈ candidates,
      renameTypeVars permutation candidate = candidate)
    (scan : ActualTypeCandidateBranchesRel leftIncoming leftExpected
      candidates leftOutputs failedActuals) :
    ∃ rightOutputs,
      ActualTypeCandidateBranchesRel rightIncoming
        (renameTypeVars permutation leftExpected)
        candidates rightOutputs failedActuals ∧
      TypePresentationPermutationStates permutation
        leftOutputs rightOutputs := by
  induction scan with
  | nil => exact ⟨[], .nil, .nil⟩
  | @matched candidate candidates leftOutput leftOutputs failedActuals
      leftMatch tail inductionHypothesis =>
      have candidateFixed := candidatesFixed candidate (by simp)
      obtain ⟨rightOutput, rightMatch, outputState⟩ :=
        Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.SelectionEquivariance.CorePlusR2TypePresentationMatchRel.map_expected_permutation
          state candidateFixed leftMatch
      obtain ⟨rightOutputs, rightTail, tailStates⟩ :=
        inductionHypothesis (fun item member =>
          candidatesFixed item (by simp [member]))
      exact ⟨rightOutput :: rightOutputs,
        .matched rightMatch rightTail,
        .cons outputState tailStates⟩
  | @failed candidate candidates leftOutputs failedActuals
      leftFailure tail inductionHypothesis =>
      have candidateFixed := candidatesFixed candidate (by simp)
      have rightFailure :=
        corePlusR2TypePresentationMatch_none_map_expected_permutation
          state candidateFixed leftFailure
      obtain ⟨rightOutputs, rightTail, tailStates⟩ :=
        inductionHypothesis (fun item member =>
          candidatesFixed item (by simp [member]))
      exact ⟨rightOutputs, .failed rightFailure rightTail, tailStates⟩

/-- One diagnostic block is pointwise alpha-equivalent when only its
displayed formal type changes. -/
theorem argumentTypeDiagnosticBlock_alpha
    (position : Nat) {leftExpected rightExpected : Atom}
    (expectedAlpha : ObservedTypeAlphaRel leftExpected rightExpected)
    (actuals : List Atom) :
    List.Forall₂ ArgumentTypeDiagnosticAlphaRel
      (argumentTypeDiagnosticBlock position leftExpected actuals)
      (argumentTypeDiagnosticBlock position rightExpected actuals) := by
  induction actuals with
  | nil => exact .nil
  | cons actual actuals inductionHypothesis =>
      exact .cons ⟨rfl, expectedAlpha, .refl actual⟩ inductionHypothesis

/-- Flattening aligned localized branch outcomes preserves the ordered list
of successful presentation states. -/
theorem branchOutcomePermutationRel_flatMap_successes
    {permutation : Equiv.Perm String}
    {leftOutcomes rightOutcomes : List ArgumentCandidateListsBranchOutcome}
    (outcomes : List.Forall₂
      (ArgumentCandidateListsBranchOutcomePermutationRel permutation)
      leftOutcomes rightOutcomes) :
    TypePresentationPermutationStates permutation
      (leftOutcomes.flatMap (·.successes))
      (rightOutcomes.flatMap (·.successes)) := by
  induction outcomes with
  | nil => exact .nil
  | cons head _ inductionHypothesis =>
      exact List.rel_append head.successes inductionHypothesis

/-- Flattening aligned localized branch outcomes preserves the diagnostic
ledger exactly in list shape and up to field-wise alpha. -/
theorem branchOutcomePermutationRel_flatMap_errors
    {permutation : Equiv.Perm String}
    {leftOutcomes rightOutcomes : List ArgumentCandidateListsBranchOutcome}
    (outcomes : List.Forall₂
      (ArgumentCandidateListsBranchOutcomePermutationRel permutation)
      leftOutcomes rightOutcomes) :
    List.Forall₂ ArgumentTypeDiagnosticAlphaRel
      (leftOutcomes.flatMap (·.errors))
      (rightOutcomes.flatMap (·.errors)) := by
  induction outcomes with
  | nil => exact .nil
  | cons head _ inductionHypothesis =>
      exact List.rel_append head.errors inductionHypothesis

/-! ## Complete argument branch-scan equivariance -/

mutual

  /-- The full branch-valued argument scan is functorial under one
  permutation of all raw formals that fixes every already-prepared actual
  candidate.  No success, failure, or diagnostic position is discarded. -/
  theorem ArgumentCandidateListsBranchScanRel.map_formals_permutation
      {permutation : Equiv.Perm String}
      {leftFormals : List Atom} {candidateLists : List (List Atom)}
      {position : Nat} {leftIncoming rightIncoming : TypeSubst}
      {leftOutcome : ArgumentCandidateListsBranchOutcome}
      (state : TypePresentationPermutationState permutation
        leftIncoming rightIncoming)
      (candidatesFixed : ∀ candidate ∈ candidateLists.flatten,
        renameTypeVars permutation candidate = candidate)
      (scan : ArgumentCandidateListsBranchScanRel leftFormals candidateLists
        position leftIncoming leftOutcome) :
      ∃ rightOutcome,
        ArgumentCandidateListsBranchScanRel
          (leftFormals.map (renameTypeVars permutation))
          candidateLists position rightIncoming rightOutcome ∧
        ArgumentCandidateListsBranchOutcomePermutationRel permutation
          leftOutcome rightOutcome := by
    cases scan with
    | noArguments formals position incoming =>
        exact ⟨⟨[rightIncoming], []⟩,
          .noArguments _ position rightIncoming,
          ⟨.cons state .nil, .nil⟩⟩
    | noFormal candidates remaining position incoming =>
        exact ⟨⟨[rightIncoming], []⟩,
          .noFormal candidates remaining position rightIncoming,
          ⟨.cons state .nil, .nil⟩⟩
    | @step formal formals candidates remaining position incoming
        headSuccesses failedActuals tailOutcomes headScan tailScans =>
        have headCandidatesFixed : ∀ candidate ∈ candidates,
            renameTypeVars permutation candidate = candidate := by
          intro candidate member
          exact candidatesFixed candidate
            (List.mem_flatten.mpr ⟨candidates, by simp, member⟩)
        obtain ⟨rightHeadSuccesses, rightHeadScan, headStates⟩ :=
          Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.SelectionEquivariance.ActualTypeCandidateBranchesRel.map_expected_permutation
            state headCandidatesFixed headScan
        have remainingFixed : ∀ candidate ∈ remaining.flatten,
            renameTypeVars permutation candidate = candidate := by
          intro candidate member
          exact candidatesFixed candidate (by
            apply List.mem_flatten.mpr
            obtain ⟨family, familyMember, candidateMember⟩ :=
              List.mem_flatten.mp member
            exact ⟨family, by simp [familyMember], candidateMember⟩)
        obtain ⟨rightTailOutcomes, rightTailScans, tailOutcomeRelations⟩ :=
          ArgumentCandidateListsBranchTailsRel.map_formals_permutation
            headStates remainingFixed tailScans
        let rightOutcome : ArgumentCandidateListsBranchOutcome :=
          ⟨rightTailOutcomes.flatMap (·.successes),
            rightTailOutcomes.flatMap (·.errors) ++
              argumentTypeDiagnosticBlock (position + 1)
                (rightIncoming.apply
                  (renameTypeVars permutation formal)) failedActuals⟩
        refine ⟨rightOutcome, ?_, ?_⟩
        · exact .step rightHeadScan rightTailScans
        · refine ⟨branchOutcomePermutationRel_flatMap_successes
              tailOutcomeRelations,
            List.rel_append
              (branchOutcomePermutationRel_flatMap_errors
                tailOutcomeRelations) ?_⟩
          exact argumentTypeDiagnosticBlock_alpha (position + 1)
            (state.observedTypeAlpha formal) failedActuals

  /-- Mutual tail transport keeps the row-major DFS list shape while
  applying the same signature permutation to every branch state. -/
  theorem ArgumentCandidateListsBranchTailsRel.map_formals_permutation
      {permutation : Equiv.Perm String}
      {leftFormals : List Atom} {remaining : List (List Atom)}
      {position : Nat} {leftIncoming rightIncoming : List TypeSubst}
      {leftOutcomes : List ArgumentCandidateListsBranchOutcome}
      (states : TypePresentationPermutationStates permutation
        leftIncoming rightIncoming)
      (candidatesFixed : ∀ candidate ∈ remaining.flatten,
        renameTypeVars permutation candidate = candidate)
      (scans : ArgumentCandidateListsBranchTailsRel leftFormals remaining
        position leftIncoming leftOutcomes) :
      ∃ rightOutcomes,
        ArgumentCandidateListsBranchTailsRel
          (leftFormals.map (renameTypeVars permutation))
          remaining position rightIncoming rightOutcomes ∧
        List.Forall₂
          (ArgumentCandidateListsBranchOutcomePermutationRel permutation)
          leftOutcomes rightOutcomes := by
    cases scans with
    | nil =>
        cases states
        exact ⟨[], .nil, .nil⟩
    | @cons formals remaining position leftNext leftNexts
        leftOutcome leftOutcomes head tail =>
        cases states with
        | cons headState tailStates =>
            obtain ⟨rightOutcome, rightHead, headOutcomeRel⟩ :=
              Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.SelectionEquivariance.ArgumentCandidateListsBranchScanRel.map_formals_permutation
                headState candidatesFixed head
            obtain ⟨rightOutcomes, rightTail, tailOutcomeRels⟩ :=
              ArgumentCandidateListsBranchTailsRel.map_formals_permutation
                tailStates candidatesFixed tail
            exact ⟨rightOutcome :: rightOutcomes,
              .cons rightHead rightTail,
              .cons headOutcomeRel tailOutcomeRels⟩

end

/-! ## Expected-return gate equivariance -/

/-- The expected-return branch scan is functorial under the same signature
permutation as the argument scan.  The boundary expected type is required to
be fixed; the raw declared return is renamed.  First-success commit and every
preceding return diagnostic are retained. -/
theorem ExpectedReturnBranchScanRel.map_return_permutation
    {permutation : Equiv.Perm String}
    {expected leftReturn : Atom}
    {leftBranches rightBranches : List TypeSubst}
    {leftOutcome : ExpectedReturnBranchOutcome}
    (expectedFixed : renameTypeVars permutation expected = expected)
    (states : TypePresentationPermutationStates permutation
      leftBranches rightBranches)
    (scan : ExpectedReturnBranchScanRel expected leftReturn
      leftBranches leftOutcome) :
    ∃ rightOutcome,
      ExpectedReturnBranchScanRel expected
        (renameTypeVars permutation leftReturn)
        rightBranches rightOutcome ∧
      ExpectedReturnBranchOutcomePermutationRel permutation
        leftOutcome rightOutcome := by
  induction scan generalizing rightBranches with
  | nil =>
      cases states
      exact ⟨⟨none, []⟩, .nil, ⟨Option.Rel.none, .nil⟩⟩
  | @matched leftIncoming leftOutput leftBranches leftMatch =>
      cases states with
      | cons headState tailStates =>
          obtain ⟨rightOutput, rightMatch, outputState⟩ :=
            Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.SelectionEquivariance.CorePlusR2TypePresentationMatchRel.map_both_permutation
              headState leftMatch
          rw [expectedFixed] at rightMatch
          exact ⟨⟨some rightOutput, []⟩,
            .matched rightMatch,
            ⟨Option.Rel.some outputState, .nil⟩⟩
  | @failed leftIncoming leftBranches tail leftFailure tailScan
      inductionHypothesis =>
      cases states with
      | cons headState tailStates =>
          have rightFailure :=
            corePlusR2TypePresentationMatch_none_map_both_permutation
              headState leftFailure
          rw [expectedFixed] at rightFailure
          obtain ⟨rightTail, rightTailScan, tailRelation⟩ :=
            inductionHypothesis tailStates
          refine ⟨_, .failed rightFailure rightTailScan, ?_⟩
          exact ⟨tailRelation.selected,
            .cons ⟨rfl, headState.observedTypeAlpha leftReturn⟩
              tailRelation.errors⟩

end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.SelectionEquivariance
