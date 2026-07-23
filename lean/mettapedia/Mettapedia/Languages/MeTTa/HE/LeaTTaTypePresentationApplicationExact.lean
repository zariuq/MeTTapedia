import Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationFoldConformance
import Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationCompleteness
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ApplicationEquivariance
import Mathlib.Logic.Equiv.Fintype

/-!
# Exact application-candidate correspondence

This module seals one freshened arrow candidate in both directions.  A
successful repaired-LeaTTa argument fold yields an executable-independent
finite presentation whose emitted return is alpha-exactly the runtime
instantiation.  Conversely, every spec presentation over disjoint fresh
type scopes is realized by the runtime, and its own return presentation is
alpha-exactly the selected runtime result.

The converse compares finite presentations through their complete solution
theories.  It does not equate a finite substitution with LeaTTa's binding
record or choose an equality-class representative.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationApplicationExact

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation
open Spec.Type.Presentation.Theory
open Spec.Type.Presentation.MatchSolutionTheory
open Spec.Type.Presentation.Alpha
open Spec.Type.Presentation.Exact
open Spec.Type.Presentation.ExactNormal
open Spec.Type.RuntimeRefinement
open LeaTTaBridge
open LeaTTaSpecConformance
open LeaTTaTypeConformance
open LeaTTaTypePresentationFoldConformance
open LeaTTaTypePresentationCompleteness
open LeaTTaTypePresentationExactConformance
open Spec.Type.Presentation.ApplicationEquivariance

/-! ## Alpha transport at a freshening boundary -/

mutual

private theorem renameTypeVars_comp
    (outer inner : String → String) (atom : Atom) :
    renameTypeVars outer (renameTypeVars inner atom) =
      renameTypeVars (outer ∘ inner) atom := by
  cases atom with
  | symbol name => simp [renameTypeVars]
  | var name => simp [renameTypeVars, Function.comp_apply]
  | grounded value => simp [renameTypeVars]
  | expression atoms =>
      simp only [renameTypeVars, Atom.expression.injEq]
      exact renameTypeVarsList_comp outer inner atoms

private theorem renameTypeVarsList_comp
    (outer inner : String → String) (atoms : List Atom) :
    (atoms.map (renameTypeVars inner)).map
        (renameTypeVars outer) =
      atoms.map (renameTypeVars (outer ∘ inner)) := by
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨renameTypeVars_comp outer inner atom,
        renameTypeVarsList_comp outer inner atoms⟩

end

mutual

private theorem renameTypeVars_congr_of_typeVars
    {left right : String → String} (atom : Atom)
    (agrees : ∀ name, name ∈ TypeSubst.typeVars atom →
      left name = right name) :
    renameTypeVars left atom = renameTypeVars right atom := by
  cases atom with
  | symbol name => simp [renameTypeVars]
  | var name =>
      simp only [renameTypeVars, Atom.var.injEq]
      exact agrees name (by simp [TypeSubst.typeVars])
  | grounded value => simp [renameTypeVars]
  | expression atoms =>
      simp only [renameTypeVars, Atom.expression.injEq]
      apply renameTypeVarsList_congr_of_typeVars
      intro name member
      exact agrees name (by simpa [TypeSubst.typeVars] using member)

private theorem renameTypeVarsList_congr_of_typeVars
    {left right : String → String} (atoms : List Atom)
    (agrees : ∀ name, name ∈ TypeSubst.typeVarsList atoms →
      left name = right name) :
    atoms.map (renameTypeVars left) =
      atoms.map (renameTypeVars right) := by
  cases atoms with
  | nil => rfl
  | cons atom atoms =>
      simp only [List.map_cons, List.cons.injEq]
      constructor
      · apply renameTypeVars_congr_of_typeVars atom
        intro name member
        exact agrees name (by
          simp only [TypeSubst.typeVarsList, List.mem_append]
          exact Or.inl member)
      · apply renameTypeVarsList_congr_of_typeVars atoms
        intro name member
        exact agrees name (by
          simp only [TypeSubst.typeVarsList, List.mem_append]
          exact Or.inr member)

end

/-- Alpha-equivalent recursive observations may be transported through any
lawful freshening of one representative.  The finite renaming between the
two observed variable images extends to a total permutation; no canonical
private spelling is selected. -/
theorem ObservedTypeAlphaRel.transport_variant
    {avoid : List String} {left right target : Atom}
    (alpha : ObservedTypeAlphaRel left right)
    (variant : TypeCandidateAlphaVariantRel avoid right target) :
    TypeCandidateAlphaVariantRel avoid left target := by
  have targetVarsFresh :=
    Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationExactConformance.TypeCandidateAlphaVariantRel.target_vars_fresh
      variant
  rcases alpha with
    ⟨source,
      ⟨leftRename, leftInjective, leftEquation⟩,
      ⟨rightRename, rightInjective, rightEquation⟩⟩
  rcases variant with
    ⟨targetRename, targetInjective, targetEquation, targetFresh⟩
  let SourceVariable :=
    {name : String // name ∈ TypeSubst.typeVars source}
  let leftImage : SourceVariable → String :=
    fun name => leftRename name.1
  let targetImage : SourceVariable → String :=
    fun name => targetRename (rightRename name.1)
  have leftImageInjective : Function.Injective leftImage := by
    intro first second equal
    apply Subtype.ext
    exact leftInjective equal
  have targetImageInjective : Function.Injective targetImage := by
    intro first second equal
    apply Subtype.ext
    exact rightInjective (targetInjective equal)
  obtain ⟨permutation, extensionLaw⟩ :=
    Equiv.Perm.exists_extending_pair
      leftImage targetImage leftImageInjective targetImageInjective
  have presentation :
      target = renameTypeVars permutation left := by
    rw [leftEquation, targetEquation, rightEquation,
      renameTypeVars_comp, renameTypeVars_comp]
    apply renameTypeVars_congr_of_typeVars source
    intro name member
    exact (extensionLaw ⟨name, member⟩).symm
  refine ⟨permutation, permutation.injective, presentation, ?_⟩
  intro name member
  have targetMember : permutation name ∈ TypeSubst.typeVars target := by
    rw [presentation, typeVars_renameTypeVars]
    exact List.mem_map.mpr ⟨name, member, rfl⟩
  exact targetVarsFresh (permutation name) targetMember

/-- Pointwise alpha-equivalent recursive argument observations may reuse the
same fresh targets and growing avoid sets. -/
theorem ArgumentAlphaVariantsRel.transport_left
    {avoid : List String} {left right targets : List Atom}
    (alpha : List.Forall₂ ObservedTypeAlphaRel left right)
    (variants : ArgumentAlphaVariantsRel avoid right targets) :
    ArgumentAlphaVariantsRel avoid left targets := by
  induction alpha generalizing avoid targets with
  | nil =>
      cases variants
      exact ArgumentAlphaVariantsRel.nil avoid
  | @cons leftHead rightHead leftTail rightTail headAlpha tailAlpha ih =>
      cases variants with
      | @cons _ _ target _ targets headVariant tailVariants =>
          exact ArgumentAlphaVariantsRel.cons
            (Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationApplicationExact.ObservedTypeAlphaRel.transport_variant
              headAlpha headVariant)
            (ih tailVariants)

/-- Forget left-to-right scope growth while retaining the pointwise alpha
variant evidence at any common root scope.  Later candidates avoid strictly
more names, so every tail witness restricts to the root by monotonicity. -/
theorem argumentAlphaVariantsRel_toForall₂At
    {root avoid : List String} {sources targets : List Atom}
    (variants : ArgumentAlphaVariantsRel avoid sources targets)
    (subset : ∀ name, name ∈ root → name ∈ avoid) :
    List.Forall₂ (TypeCandidateAlphaVariantRel root)
      sources targets := by
  induction variants with
  | nil => exact .nil
  | @cons avoid source target sources targets head tail inductionHypothesis =>
      apply List.Forall₂.cons
      · rcases head with ⟨rename, injective, equation, fresh⟩
        exact ⟨rename, injective, equation,
          fun name member rootMember =>
            fresh name member (subset (rename name) rootMember)⟩
      · exact inductionHypothesis (fun name member =>
          List.mem_append_left _ (subset name member))

/-- Pointwise view of a left-to-right alpha presentation at its initial
avoid scope. -/
theorem argumentAlphaVariantsRel_toForall₂
    {avoid : List String} {sources targets : List Atom}
    (variants : ArgumentAlphaVariantsRel avoid sources targets) :
    List.Forall₂ (TypeCandidateAlphaVariantRel avoid)
      sources targets :=
  argumentAlphaVariantsRel_toForall₂At variants
    (fun _ member => member)

/-- Operator candidates have independent scopes, so pointwise alpha
transport preserves their shared avoid boundary directly. -/
theorem OperatorAlphaVariantsRel.transport_left
    {avoid : List String} {left right targets : List Atom}
    (alpha : List.Forall₂ ObservedTypeAlphaRel left right)
    (variants : OperatorAlphaVariantsRel avoid right targets) :
    OperatorAlphaVariantsRel avoid left targets := by
  induction alpha generalizing targets with
  | nil =>
      cases variants
      exact OperatorAlphaVariantsRel.nil
  | @cons leftHead rightHead leftTail rightTail headAlpha tailAlpha ih =>
      cases variants with
      | @cons _ target _ targets headVariant tailVariants =>
          exact OperatorAlphaVariantsRel.cons
            (Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationApplicationExact.ObservedTypeAlphaRel.transport_variant
              headAlpha headVariant)
            (ih tailVariants)

/-- Alpha siblings compose.  The middle-to-right finite renaming first
extends to a permutation; the existing transport theorem then carries the
left presentation through that same target. -/
theorem ObservedTypeAlphaRel.trans
    {left middle right : Atom}
    (leftMiddle : ObservedTypeAlphaRel left middle)
    (middleRight : ObservedTypeAlphaRel middle right) :
    ObservedTypeAlphaRel left right := by
  have rightReflexiveVariant :
      TypeCandidateAlphaVariantRel [] right right := by
    rcases TypeVariableRenamingOf.refl right with
      ⟨rename, injective, equation⟩
    refine ⟨rename, injective, equation, ?_⟩
    intro name member
    simp
  have middleRightVariant :
      TypeCandidateAlphaVariantRel [] middle right :=
    Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationApplicationExact.ObservedTypeAlphaRel.transport_variant
      middleRight rightReflexiveVariant
  have leftRightVariant :
      TypeCandidateAlphaVariantRel [] left right :=
    Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationApplicationExact.ObservedTypeAlphaRel.transport_variant
      leftMiddle middleRightVariant
  exact ⟨left, TypeVariableRenamingOf.refl left,
    leftRightVariant.toTypeVariableRenamingOf⟩

/-- Pointwise alpha exactness composes without changing list order or
multiplicity. -/
theorem observedTypeAlphaList_trans
    {left middle right : List Atom}
    (leftMiddle : List.Forall₂ ObservedTypeAlphaRel left middle)
    (middleRight : List.Forall₂ ObservedTypeAlphaRel middle right) :
    List.Forall₂ ObservedTypeAlphaRel left right := by
  induction leftMiddle generalizing right with
  | nil =>
      cases middleRight
      exact List.Forall₂.nil
  | @cons leftHead middleHead leftTail middleTail headAlpha tailAlpha ih =>
      cases middleRight with
      | @cons _ rightHead _ rightTail middleHeadAlpha middleTailAlpha =>
          exact List.Forall₂.cons
            (Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationApplicationExact.ObservedTypeAlphaRel.trans
              headAlpha middleHeadAlpha)
            (ih middleTailAlpha)

/-! ## Combining independently freshened application scopes -/

/-- Two lawful fresh presentations of one schematic candidate are alpha
siblings, even when their finite avoid sets differ. -/
theorem TypeCandidateAlphaVariantRel.common_source_alpha
    {leftAvoid rightAvoid : List String} {source left right : Atom}
    (leftVariant : TypeCandidateAlphaVariantRel
      leftAvoid source left)
    (rightVariant : TypeCandidateAlphaVariantRel
      rightAvoid source right) :
    ObservedTypeAlphaRel left right :=
  ⟨source, leftVariant.toTypeVariableRenamingOf,
    rightVariant.toTypeVariableRenamingOf⟩

/-- Every target variable emitted by a left-to-right argument freshening lies
outside the initial avoid set. -/
theorem ArgumentAlphaVariantsRel.targets_fresh
    {avoid : List String} {sources targets : List Atom}
    (variants : ArgumentAlphaVariantsRel avoid sources targets) :
    ∀ name ∈ TypeSubst.typeVarsList targets, name ∉ avoid := by
  induction variants with
  | nil => simp [TypeSubst.typeVarsList]
  | @cons avoid source target sources targets headVariant tailVariants ih =>
      intro name member
      rw [TypeSubst.typeVarsList] at member
      rcases List.mem_append.mp member with headMember | tailMember
      · exact
          Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationExactConformance.TypeCandidateAlphaVariantRel.target_vars_fresh
            headVariant name headMember
      · intro avoidMember
        exact (ih name tailMember)
          (List.mem_append_left _ avoidMember)

/-- Two independent left-to-right freshenings of the same raw argument list
form pairwise-disjoint local alpha scopes. -/
theorem ArgumentAlphaVariantsRel.common_source_scoped_alpha
    {leftAvoid rightAvoid : List String} {sources left right : List Atom}
    (leftVariants : ArgumentAlphaVariantsRel
      leftAvoid sources left)
    (rightVariants : ArgumentAlphaVariantsRel
      rightAvoid sources right) :
    ScopedObservedTypeListAlphaRel left right := by
  induction leftVariants generalizing rightAvoid right with
  | nil =>
      cases rightVariants
      exact ScopedObservedTypeListAlphaRel.nil
  | @cons leftAvoid source leftHead sources leftTail
      leftHeadVariant leftTailVariants ih =>
      cases rightVariants with
      | @cons _ _ rightHead _ rightTail
          rightHeadVariant rightTailVariants =>
          apply ScopedObservedTypeListAlphaRel.cons
            (TypeCandidateAlphaVariantRel.common_source_alpha
              leftHeadVariant rightHeadVariant)
          · intro name headMember tailMember
            exact
              (ArgumentAlphaVariantsRel.targets_fresh
                leftTailVariants name tailMember)
                (List.mem_append_right leftAvoid headMember)
          · intro name headMember tailMember
            exact
              (ArgumentAlphaVariantsRel.targets_fresh
                rightTailVariants name tailMember)
                (List.mem_append_right rightAvoid headMember)
          · exact ih rightTailVariants

/-- One operator scope and all independently freshened argument scopes admit
one common permutation between any two lawful presentations. -/
theorem application_scopes_exist_permutation
    {leftAvoid rightAvoid : List String}
    {rawArguments leftArguments rightArguments : List Atom}
    {rawOperator leftOperator rightOperator : Atom}
    (leftArgumentsVariant : ArgumentAlphaVariantsRel
      leftAvoid rawArguments leftArguments)
    (rightArgumentsVariant : ArgumentAlphaVariantsRel
      rightAvoid rawArguments rightArguments)
    (leftOperatorVariant : TypeCandidateAlphaVariantRel
      (leftAvoid ++ TypeSubst.typeVarsList leftArguments)
      rawOperator leftOperator)
    (rightOperatorVariant : TypeCandidateAlphaVariantRel
      (rightAvoid ++ TypeSubst.typeVarsList rightArguments)
      rawOperator rightOperator) :
    ∃ permutation : Equiv.Perm String,
      rightOperator = renameTypeVars permutation leftOperator ∧
        rightArguments =
          leftArguments.map (renameTypeVars permutation) := by
  have scopedArguments :=
    ArgumentAlphaVariantsRel.common_source_scoped_alpha
      leftArgumentsVariant rightArgumentsVariant
  have scopedAll : ScopedObservedTypeListAlphaRel
      (leftOperator :: leftArguments)
      (rightOperator :: rightArguments) := by
    apply ScopedObservedTypeListAlphaRel.cons
      (TypeCandidateAlphaVariantRel.common_source_alpha
        leftOperatorVariant rightOperatorVariant)
    · intro name operatorMember argumentMember
      exact
        (Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationExactConformance.TypeCandidateAlphaVariantRel.target_vars_fresh
          leftOperatorVariant name operatorMember)
          (List.mem_append_right leftAvoid argumentMember)
    · intro name operatorMember argumentMember
      exact
        (Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationExactConformance.TypeCandidateAlphaVariantRel.target_vars_fresh
          rightOperatorVariant name operatorMember)
          (List.mem_append_right rightAvoid argumentMember)
    · exact scopedArguments
  obtain ⟨permutation, equation⟩ :=
    scopedAll.exists_permutation
  have parts := List.cons.inj equation
  exact ⟨permutation, parts.1, parts.2⟩

/-- A successful candidate presentation transports between any two lawful
freshenings of the same raw operator and argument scopes.  The output package
is compared observationally through the complete presentation theory. -/
theorem applicationPackageSuccess_transport_common_scopes
    {leftAvoid rightAvoid : List String}
    {rawArguments leftArguments rightArguments : List Atom}
    {rawOperator leftOperator rightOperator : Atom}
    {leftResult : TypePackage}
    (leftArgumentsVariant : ArgumentAlphaVariantsRel
      leftAvoid rawArguments leftArguments)
    (rightArgumentsVariant : ArgumentAlphaVariantsRel
      rightAvoid rawArguments rightArguments)
    (leftOperatorVariant : TypeCandidateAlphaVariantRel
      (leftAvoid ++ TypeSubst.typeVarsList leftArguments)
      rawOperator leftOperator)
    (rightOperatorVariant : TypeCandidateAlphaVariantRel
      (rightAvoid ++ TypeSubst.typeVarsList rightArguments)
      rawOperator rightOperator)
    (leftSuccess : ApplicationPackageSuccessRel
      leftArguments leftOperator leftResult) :
    ∃ rightResult,
      ApplicationPackageSuccessRel
          rightArguments rightOperator rightResult ∧
        ObservedTypeAlphaRel leftResult.observed rightResult.observed := by
  obtain ⟨permutation, operatorEquation, argumentsEquation⟩ :=
    application_scopes_exist_permutation
      leftArgumentsVariant rightArgumentsVariant
      leftOperatorVariant rightOperatorVariant
  cases leftSuccess with
  | @mk _ returnType expectedTypes _ substitution shape fold =>
      have renamedShape :
          rightOperator =
            .expression
              (.symbol "->" ::
                (expectedTypes.map (renameTypeVars permutation) ++
                  [renameTypeVars permutation returnType])) := by
        rw [operatorEquation, shape]
        simp [renameTypeVars, List.map_append]
      obtain ⟨rightSubstitution, rightFold⟩ :=
        (presentationArgumentList_success_perm_iff
          permutation expectedTypes leftArguments).mpr
            ⟨substitution, fold⟩
      have rightFoldAtArguments :
          PresentationArgumentListMatchRel
            (expectedTypes.map (renameTypeVars permutation))
            rightArguments [] rightSubstitution := by
        rw [argumentsEquation]
        exact rightFold
      refine ⟨inferredPackage rightSubstitution
          (renameTypeVars permutation returnType), ?_, ?_⟩
      · exact ApplicationPackageSuccessRel.mk
          renamedShape rightFoldAtArguments
      · simpa [inferredPackage] using
          (PresentationArgumentListMatchRel.output_alpha_of_perm
            permutation fold rightFold returnType)

/-- Candidate success existence is invariant across any two lawful
freshenings of the same raw application scopes. -/
theorem applicationPackageSuccess_exists_iff_common_scopes
    {leftAvoid rightAvoid : List String}
    {rawArguments leftArguments rightArguments : List Atom}
    {rawOperator leftOperator rightOperator : Atom}
    (leftArgumentsVariant : ArgumentAlphaVariantsRel
      leftAvoid rawArguments leftArguments)
    (rightArgumentsVariant : ArgumentAlphaVariantsRel
      rightAvoid rawArguments rightArguments)
    (leftOperatorVariant : TypeCandidateAlphaVariantRel
      (leftAvoid ++ TypeSubst.typeVarsList leftArguments)
      rawOperator leftOperator)
    (rightOperatorVariant : TypeCandidateAlphaVariantRel
      (rightAvoid ++ TypeSubst.typeVarsList rightArguments)
      rawOperator rightOperator) :
    (∃ result,
      ApplicationPackageSuccessRel
        leftArguments leftOperator result) ↔
      ∃ result,
        ApplicationPackageSuccessRel
          rightArguments rightOperator result := by
  constructor
  · rintro ⟨leftResult, leftSuccess⟩
    obtain ⟨rightResult, rightSuccess, _alpha⟩ :=
      applicationPackageSuccess_transport_common_scopes
        leftArgumentsVariant rightArgumentsVariant
        leftOperatorVariant rightOperatorVariant leftSuccess
    exact ⟨rightResult, rightSuccess⟩
  · rintro ⟨rightResult, rightSuccess⟩
    obtain ⟨leftResult, leftSuccess, _alpha⟩ :=
      applicationPackageSuccess_transport_common_scopes
        rightArgumentsVariant leftArgumentsVariant
        rightOperatorVariant leftOperatorVariant rightSuccess
    exact ⟨leftResult, leftSuccess⟩

/-! ## Transport with explicitly separated scope families -/

/-- Independently chosen argument and operator presentations combine into
one permutation when their cross-family separation is stated explicitly.
Unlike `application_scopes_exist_permutation`, this theorem does not encode
separation indirectly in either alpha variant's avoid list. -/
theorem application_scopes_exist_permutation_of_separated
    {leftArgumentAvoid rightArgumentAvoid : List String}
    {leftOperatorAvoid rightOperatorAvoid : List String}
    {rawArguments leftArguments rightArguments : List Atom}
    {rawOperator leftOperator rightOperator : Atom}
    (leftArgumentsVariant : ArgumentAlphaVariantsRel
      leftArgumentAvoid rawArguments leftArguments)
    (rightArgumentsVariant : ArgumentAlphaVariantsRel
      rightArgumentAvoid rawArguments rightArguments)
    (leftOperatorVariant : TypeCandidateAlphaVariantRel
      leftOperatorAvoid rawOperator leftOperator)
    (rightOperatorVariant : TypeCandidateAlphaVariantRel
      rightOperatorAvoid rawOperator rightOperator)
    (leftSeparated : AtomVarsFreshFromAtoms
      leftOperator leftArguments)
    (rightSeparated : AtomVarsFreshFromAtoms
      rightOperator rightArguments) :
    ∃ permutation : Equiv.Perm String,
      rightOperator = renameTypeVars permutation leftOperator ∧
      rightArguments =
        leftArguments.map (renameTypeVars permutation) := by
  have scopedArguments :=
    ArgumentAlphaVariantsRel.common_source_scoped_alpha
      leftArgumentsVariant rightArgumentsVariant
  have scopedAll : ScopedObservedTypeListAlphaRel
      (leftOperator :: leftArguments)
      (rightOperator :: rightArguments) := by
    exact ScopedObservedTypeListAlphaRel.cons
      (TypeCandidateAlphaVariantRel.common_source_alpha
        leftOperatorVariant rightOperatorVariant)
      leftSeparated rightSeparated scopedArguments
  obtain ⟨permutation, equation⟩ :=
    scopedAll.exists_permutation
  have parts := List.cons.inj equation
  exact ⟨permutation, parts.1, parts.2⟩

/-- Candidate success transports across alpha presentations whose argument
and operator families are explicitly separated. -/
theorem applicationPackageSuccess_transport_separated_scopes
    {leftArgumentAvoid rightArgumentAvoid : List String}
    {leftOperatorAvoid rightOperatorAvoid : List String}
    {rawArguments leftArguments rightArguments : List Atom}
    {rawOperator leftOperator rightOperator : Atom}
    {leftResult : TypePackage}
    (leftArgumentsVariant : ArgumentAlphaVariantsRel
      leftArgumentAvoid rawArguments leftArguments)
    (rightArgumentsVariant : ArgumentAlphaVariantsRel
      rightArgumentAvoid rawArguments rightArguments)
    (leftOperatorVariant : TypeCandidateAlphaVariantRel
      leftOperatorAvoid rawOperator leftOperator)
    (rightOperatorVariant : TypeCandidateAlphaVariantRel
      rightOperatorAvoid rawOperator rightOperator)
    (leftSeparated : AtomVarsFreshFromAtoms
      leftOperator leftArguments)
    (rightSeparated : AtomVarsFreshFromAtoms
      rightOperator rightArguments)
    (leftSuccess : ApplicationPackageSuccessRel
      leftArguments leftOperator leftResult) :
    ∃ rightResult,
      ApplicationPackageSuccessRel
          rightArguments rightOperator rightResult ∧
        ObservedTypeAlphaRel leftResult.observed rightResult.observed := by
  obtain ⟨permutation, operatorEquation, argumentsEquation⟩ :=
    application_scopes_exist_permutation_of_separated
      leftArgumentsVariant rightArgumentsVariant
      leftOperatorVariant rightOperatorVariant
      leftSeparated rightSeparated
  cases leftSuccess with
  | @mk _ returnType expectedTypes _ substitution shape fold =>
      have renamedShape :
          rightOperator =
            .expression
              (.symbol "->" ::
                (expectedTypes.map (renameTypeVars permutation) ++
                  [renameTypeVars permutation returnType])) := by
        rw [operatorEquation, shape]
        simp [renameTypeVars, List.map_append]
      obtain ⟨rightSubstitution, rightFold⟩ :=
        (presentationArgumentList_success_perm_iff
          permutation expectedTypes leftArguments).mpr
            ⟨substitution, fold⟩
      have rightFoldAtArguments :
          PresentationArgumentListMatchRel
            (expectedTypes.map (renameTypeVars permutation))
            rightArguments [] rightSubstitution := by
        rw [argumentsEquation]
        exact rightFold
      refine ⟨inferredPackage rightSubstitution
          (renameTypeVars permutation returnType), ?_, ?_⟩
      · exact ApplicationPackageSuccessRel.mk
          renamedShape rightFoldAtArguments
      · simpa [inferredPackage] using
          (PresentationArgumentListMatchRel.output_alpha_of_perm
            permutation fold rightFold returnType)

/-- Success existence is invariant under explicitly separated alpha scope
families. -/
theorem applicationPackageSuccess_exists_iff_separated_scopes
    {leftArgumentAvoid rightArgumentAvoid : List String}
    {leftOperatorAvoid rightOperatorAvoid : List String}
    {rawArguments leftArguments rightArguments : List Atom}
    {rawOperator leftOperator rightOperator : Atom}
    (leftArgumentsVariant : ArgumentAlphaVariantsRel
      leftArgumentAvoid rawArguments leftArguments)
    (rightArgumentsVariant : ArgumentAlphaVariantsRel
      rightArgumentAvoid rawArguments rightArguments)
    (leftOperatorVariant : TypeCandidateAlphaVariantRel
      leftOperatorAvoid rawOperator leftOperator)
    (rightOperatorVariant : TypeCandidateAlphaVariantRel
      rightOperatorAvoid rawOperator rightOperator)
    (leftSeparated : AtomVarsFreshFromAtoms
      leftOperator leftArguments)
    (rightSeparated : AtomVarsFreshFromAtoms
      rightOperator rightArguments) :
    (∃ result,
      ApplicationPackageSuccessRel
        leftArguments leftOperator result) ↔
      ∃ result,
        ApplicationPackageSuccessRel
          rightArguments rightOperator result := by
  constructor
  · rintro ⟨leftResult, leftSuccess⟩
    obtain ⟨rightResult, rightSuccess, _⟩ :=
      applicationPackageSuccess_transport_separated_scopes
        leftArgumentsVariant rightArgumentsVariant
        leftOperatorVariant rightOperatorVariant
        leftSeparated rightSeparated leftSuccess
    exact ⟨rightResult, rightSuccess⟩
  · rintro ⟨rightResult, rightSuccess⟩
    obtain ⟨leftResult, leftSuccess, _⟩ :=
      applicationPackageSuccess_transport_separated_scopes
        rightArgumentsVariant leftArgumentsVariant
        rightOperatorVariant leftOperatorVariant
        rightSeparated leftSeparated rightSuccess
    exact ⟨leftResult, leftSuccess⟩

/-- Option-level alpha agreement for one application matrix cell. -/
def ApplicationPackageOutcomeAlphaRel :
    Option TypePackage → Option TypePackage → Prop
  | none, none => True
  | some left, some right =>
      ObservedTypeAlphaRel left.observed right.observed
  | _, _ => False

/-- A complete positive-or-negative matrix cell transports across explicitly
separated alpha scope families. -/
theorem applicationPackageOutcome_transport_separated_scopes
    {leftArgumentAvoid rightArgumentAvoid : List String}
    {leftOperatorAvoid rightOperatorAvoid : List String}
    {rawArguments leftArguments rightArguments : List Atom}
    {rawOperator leftOperator rightOperator : Atom}
    {leftOutcome : Option TypePackage}
    (leftArgumentsVariant : ArgumentAlphaVariantsRel
      leftArgumentAvoid rawArguments leftArguments)
    (rightArgumentsVariant : ArgumentAlphaVariantsRel
      rightArgumentAvoid rawArguments rightArguments)
    (leftOperatorVariant : TypeCandidateAlphaVariantRel
      leftOperatorAvoid rawOperator leftOperator)
    (rightOperatorVariant : TypeCandidateAlphaVariantRel
      rightOperatorAvoid rawOperator rightOperator)
    (leftSeparated : AtomVarsFreshFromAtoms
      leftOperator leftArguments)
    (rightSeparated : AtomVarsFreshFromAtoms
      rightOperator rightArguments)
    (leftRel : ApplicationPackageOutcomeRel
      leftArguments leftOperator leftOutcome) :
    ∃ rightOutcome,
      ApplicationPackageOutcomeRel
          rightArguments rightOperator rightOutcome ∧
        ApplicationPackageOutcomeAlphaRel
          leftOutcome rightOutcome := by
  cases leftRel with
  | failure noLeftSuccess =>
      refine ⟨none, ApplicationPackageOutcomeRel.failure ?_, trivial⟩
      intro rightResult rightSuccess
      obtain ⟨leftResult, leftSuccess⟩ :=
        (applicationPackageSuccess_exists_iff_separated_scopes
          leftArgumentsVariant rightArgumentsVariant
          leftOperatorVariant rightOperatorVariant
          leftSeparated rightSeparated).mpr
            ⟨rightResult, rightSuccess⟩
      exact noLeftSuccess leftResult leftSuccess
  | success leftSuccess =>
      obtain ⟨rightResult, rightSuccess, alpha⟩ :=
        applicationPackageSuccess_transport_separated_scopes
          leftArgumentsVariant rightArgumentsVariant
          leftOperatorVariant rightOperatorVariant
          leftSeparated rightSeparated leftSuccess
      exact ⟨some rightResult,
        ApplicationPackageOutcomeRel.success rightSuccess, alpha⟩

/-- The complete ordered filter-map scan transports across two lawful
freshenings of the same raw operator and argument lists, preserving order,
multiplicity, failure positions, and observed outputs up to private alpha. -/
theorem ApplicationPackageScanRel.transport_common_scopes
    {leftAvoid rightAvoid : List String}
    {rawArguments leftArguments rightArguments : List Atom}
    {rawOperators leftOperators rightOperators : List Atom}
    {leftResults : List TypePackage}
    (leftArgumentsVariant : ArgumentAlphaVariantsRel
      leftAvoid rawArguments leftArguments)
    (rightArgumentsVariant : ArgumentAlphaVariantsRel
      rightAvoid rawArguments rightArguments)
    (leftOperatorVariants : OperatorAlphaVariantsRel
      (leftAvoid ++ TypeSubst.typeVarsList leftArguments)
      rawOperators leftOperators)
    (rightOperatorVariants : OperatorAlphaVariantsRel
      (rightAvoid ++ TypeSubst.typeVarsList rightArguments)
      rawOperators rightOperators)
    (leftScan : ApplicationPackageScanRel
      leftArguments leftOperators leftResults) :
    ∃ rightResults,
      ApplicationPackageScanRel
          rightArguments rightOperators rightResults ∧
        List.Forall₂ ObservedTypeAlphaRel
          (observedTypes leftResults) (observedTypes rightResults) := by
  induction leftOperatorVariants generalizing rightOperators leftResults with
  | nil =>
      cases rightOperatorVariants
      cases leftScan
      exact ⟨[], ApplicationPackageScanRel.nil, List.Forall₂.nil⟩
  | @cons rawOperator leftOperator rawOperators leftOperators
      leftOperatorVariant leftTailVariants ih =>
      cases rightOperatorVariants with
      | @cons _ rightOperator _ rightOperators
          rightOperatorVariant rightTailVariants =>
          cases leftScan with
          | @skip _ _ leftResults leftOutcome leftTailScan =>
              cases leftOutcome with
              | failure noLeftSuccess =>
                  have noRightSuccess : ∀ result,
                      ¬ApplicationPackageSuccessRel
                        rightArguments rightOperator result := by
                    intro result rightSuccess
                    obtain ⟨leftResult, leftSuccess⟩ :=
                      (applicationPackageSuccess_exists_iff_common_scopes
                        leftArgumentsVariant rightArgumentsVariant
                        leftOperatorVariant rightOperatorVariant).mpr
                          ⟨result, rightSuccess⟩
                    exact noLeftSuccess leftResult leftSuccess
                  obtain ⟨rightResults, rightTailScan, tailAlpha⟩ :=
                    ih rightTailVariants leftTailScan
                  exact ⟨rightResults,
                    ApplicationPackageScanRel.skip
                      (ApplicationPackageOutcomeRel.failure noRightSuccess)
                      rightTailScan,
                    tailAlpha⟩
          | @emit _ _ leftResult leftResults
              leftOutcome leftTailScan =>
              cases leftOutcome with
              | success leftSuccess =>
                  obtain ⟨rightResult, rightSuccess, headAlpha⟩ :=
                    applicationPackageSuccess_transport_common_scopes
                      leftArgumentsVariant rightArgumentsVariant
                      leftOperatorVariant rightOperatorVariant leftSuccess
                  obtain ⟨rightResults, rightTailScan, tailAlpha⟩ :=
                    ih rightTailVariants leftTailScan
                  exact ⟨rightResult :: rightResults,
                    ApplicationPackageScanRel.emit
                      (ApplicationPackageOutcomeRel.success rightSuccess)
                      rightTailScan,
                    by
                      simpa [observedTypes] using
                        List.Forall₂.cons headAlpha tailAlpha⟩

/-- One successful repaired runtime arrow candidate has a finite spec
presentation with an alpha-exact return observation. -/
theorem applicationCandidate_sound
    {expectedTypes actualTypes : List Atom} {returnType : Atom}
    {leaOutput : Metta.Bindings}
    (success : Metta.Minimal.matchApplicationTypeArguments
      Metta.Bindings.empty (toLeaTTaAtoms expectedTypes)
        (toLeaTTaAtoms actualTypes) = some leaOutput) :
    ∃ result,
      ApplicationPackageSuccessRel actualTypes
          (.expression
            (.symbol "->" :: (expectedTypes ++ [returnType]))) result ∧
        ObservedTypeAlphaRel result.observed
          (fromLeaTTaAtom
            (Metta.instantiate leaOutput (toLeaTTaAtom returnType))) := by
  obtain ⟨presentation, specOutput, fold, state, alpha⟩ :=
    matchApplicationTypeArguments_exact_return success
  refine ⟨inferredPackage presentation returnType, ?_, ?_⟩
  · exact ApplicationPackageSuccessRel.mk rfl fold
  · simpa [inferredPackage] using alpha

/-- A spec arrow-candidate presentation over fresh disjoint scopes is
realized by repaired LeaTTa, with the spec and runtime returns alpha-exact. -/
theorem applicationCandidate_complete
    {expectedTypes actualTypes : List Atom} {returnType : Atom}
    {result : TypePackage}
    (specSuccess : ApplicationPackageSuccessRel actualTypes
      (.expression
        (.symbol "->" :: (expectedTypes ++ [returnType]))) result)
    (disjoint : AtomListsVarsDisjoint expectedTypes actualTypes) :
    ∃ leaOutput,
      Metta.Minimal.matchApplicationTypeArguments Metta.Bindings.empty
          (toLeaTTaAtoms expectedTypes) (toLeaTTaAtoms actualTypes) =
        some leaOutput ∧
      ObservedTypeAlphaRel result.observed
        (fromLeaTTaAtom
          (Metta.instantiate leaOutput (toLeaTTaAtom returnType))) := by
  cases specSuccess with
  | @mk operatorType declaredReturn expected actual substitution shape fold =>
      have shapeParts :
          expectedTypes = expected ∧ returnType = declaredReturn := by
        have atoms := Atom.expression.inj shape
        have tails := List.cons.inj atoms
        apply List.concat_inj.mp
        simpa only [List.concat_eq_append] using tails.2
      rcases shapeParts with ⟨rfl, rfl⟩
      obtain ⟨leaOutput, runtimeSuccess⟩ :=
        matchApplicationTypeArguments_complete fold disjoint
      obtain ⟨runtimePresentation, specOutput, runtimeFold,
          runtimeState⟩ :=
        matchApplicationTypeArguments_presentation_sound
          expectedTypes actualTypes typePresentationSimulationState_empty
            runtimeSuccess
      have specNormal : substitution.Normal :=
        PresentationArgumentListMatchRel.output_normal
          fold TypeSubst.normal_empty
      have specSolutions : ∀ valuation,
          TypeSubstSatisfied valuation substitution ↔
            TypeBindingSatisfied valuation specOutput := by
        intro valuation
        calc
          TypeSubstSatisfied valuation substitution ↔
              TypeSubstSatisfied valuation ([] : TypeSubst) ∧
                List.Forall₂ (CorePlusR2TypeConsistent valuation)
                  expectedTypes actualTypes :=
            PresentationArgumentListMatchRel.solutions
              fold TypeSubst.normal_empty valuation
          _ ↔ TypeSubstSatisfied valuation runtimePresentation :=
            (PresentationArgumentListMatchRel.solutions
              runtimeFold TypeSubst.normal_empty valuation).symm
          _ ↔ TypeBindingSatisfied valuation specOutput :=
            runtimeState.specSolutions valuation
      let specState : TypePresentationSimulationState
          substitution specOutput leaOutput :=
        ⟨specNormal, specSolutions, runtimeState.semantic⟩
      refine ⟨leaOutput, runtimeSuccess, ?_⟩
      simpa [inferredPackage] using
        (specState.returnAlpha returnType)

/-! ## Exact one-candidate outcome -/

/-- Native presentation of the repaired runtime's one-candidate application
filter.  It is used only in the conformance layer; the spec relation remains
independent of executable definitions. -/
def runtimeApplicationCandidate
    (actualTypes : List Atom) (operatorType : Atom) : Option Metta.Atom :=
  match operatorType with
  | .expression (.symbol "->" :: types) =>
      match types.getLast? with
      | none => none
      | some returnType =>
          match Metta.Minimal.matchApplicationTypeArguments
              Metta.Bindings.empty (toLeaTTaAtoms types.dropLast)
                (toLeaTTaAtoms actualTypes) with
          | some bindings =>
              some (Metta.instantiate bindings (toLeaTTaAtom returnType))
          | none => none
  | _ => none

private theorem arrowExpected_disjoint
    {expectedTypes actualTypes : List Atom} {returnType : Atom}
    (disjoint : VarsDisjoint
      (.expression
        (.symbol "->" :: (expectedTypes ++ [returnType])))
      (.expression actualTypes)) :
    AtomListsVarsDisjoint expectedTypes actualTypes := by
  have allDisjoint : AtomListsVarsDisjoint
      (.symbol "->" :: (expectedTypes ++ [returnType])) actualTypes :=
    varsDisjoint_expression_iff.mp disjoint
  intro name expectedMember actualMember
  have expectedIn : ∃ expected ∈ expectedTypes,
      name ∈ (toLeaTTaAtom expected).vars := by
    simpa [toLeaTTaAtoms_eq_map, List.mem_flatten, List.mem_map]
      using expectedMember
  exact allDisjoint name
    (by simp [toLeaTTaAtoms_eq_map, expectedIn]) actualMember

/-- A successful concrete candidate produces a spec success outcome with
an alpha-exact observed return. -/
theorem runtimeApplicationCandidate_sound
    {actualTypes : List Atom} {operatorType : Atom}
    {leaResult : Metta.Atom}
    (runtimeSuccess :
      runtimeApplicationCandidate actualTypes operatorType = some leaResult) :
    ∃ result,
      ApplicationPackageOutcomeRel actualTypes operatorType (some result) ∧
        ObservedTypeAlphaRel result.observed (fromLeaTTaAtom leaResult) := by
  cases operatorType with
  | symbol name => simp [runtimeApplicationCandidate] at runtimeSuccess
  | var name => simp [runtimeApplicationCandidate] at runtimeSuccess
  | grounded value => simp [runtimeApplicationCandidate] at runtimeSuccess
  | expression atoms =>
      cases atoms with
      | nil => simp [runtimeApplicationCandidate] at runtimeSuccess
      | cons head types =>
          cases head with
          | var name => simp [runtimeApplicationCandidate] at runtimeSuccess
          | grounded value =>
              simp [runtimeApplicationCandidate] at runtimeSuccess
          | expression children =>
              simp [runtimeApplicationCandidate] at runtimeSuccess
          | symbol name =>
              by_cases arrow : name = "->"
              · subst name
                cases lastEquation : types.getLast? with
                | none =>
                    simp [runtimeApplicationCandidate, lastEquation] at runtimeSuccess
                | some returnType =>
                    simp only [runtimeApplicationCandidate, lastEquation]
                      at runtimeSuccess
                    have nonempty : types ≠ [] := by
                      intro empty
                      subst types
                      simp at lastEquation
                    have splitTypes :
                        types.dropLast ++ [returnType] = types := by
                      have canonicalLast :=
                        List.getLast?_eq_some_getLast nonempty
                      have returnEq : returnType = types.getLast nonempty := by
                        rw [lastEquation] at canonicalLast
                        exact Option.some.inj canonicalLast
                      subst returnType
                      exact List.dropLast_append_getLast nonempty
                    cases foldEquation :
                        Metta.Minimal.matchApplicationTypeArguments
                          Metta.Bindings.empty
                            (toLeaTTaAtoms types.dropLast)
                            (toLeaTTaAtoms actualTypes) with
                    | none =>
                        rw [foldEquation] at runtimeSuccess
                        contradiction
                    | some bindings =>
                        have resultEquation :
                            Metta.instantiate bindings
                                (toLeaTTaAtom returnType) = leaResult := by
                          rw [foldEquation] at runtimeSuccess
                          exact Option.some.inj runtimeSuccess
                        obtain ⟨result, specSuccess, alpha⟩ :=
                          applicationCandidate_sound foldEquation
                        subst leaResult
                        refine ⟨result,
                          ApplicationPackageOutcomeRel.success ?_, alpha⟩
                        simpa [splitTypes] using specSuccess
              · simp [runtimeApplicationCandidate, arrow] at runtimeSuccess

/-- Every spec success over disjoint scopes is emitted by the concrete
candidate filter, with the same observed return up to private alpha names. -/
theorem runtimeApplicationCandidate_complete
    {actualTypes : List Atom} {operatorType : Atom} {result : TypePackage}
    (specSuccess : ApplicationPackageSuccessRel
      actualTypes operatorType result)
    (disjoint : VarsDisjoint operatorType (.expression actualTypes)) :
    ∃ leaResult,
      runtimeApplicationCandidate actualTypes operatorType = some leaResult ∧
        ObservedTypeAlphaRel result.observed
          (fromLeaTTaAtom leaResult) := by
  cases specSuccess with
  | @mk _ returnType expectedTypes _ substitution shape fold =>
      subst operatorType
      have scopeDisjoint := arrowExpected_disjoint disjoint
      have rebuilt : ApplicationPackageSuccessRel actualTypes
          (.expression
            (.symbol "->" :: (expectedTypes ++ [returnType])))
          (inferredPackage substitution returnType) :=
        ApplicationPackageSuccessRel.mk
          (returnType := returnType) rfl fold
      obtain ⟨leaOutput, runtimeFold, alpha⟩ :=
        applicationCandidate_complete (returnType := returnType)
          rebuilt scopeDisjoint
      refine ⟨Metta.instantiate leaOutput (toLeaTTaAtom returnType), ?_,
        alpha⟩
      simp only [runtimeApplicationCandidate]
      rw [show (expectedTypes ++ [returnType]).getLast? =
        some returnType by simp]
      rw [show (expectedTypes ++ [returnType]).dropLast =
        expectedTypes by simp]
      rw [runtimeFold]

/-- Candidate failure is exact once the operator and actual scopes are
disjoint: the runtime returns `none` exactly when no spec success package
exists. -/
theorem runtimeApplicationCandidate_none_iff
    {actualTypes : List Atom} {operatorType : Atom}
    (disjoint : VarsDisjoint operatorType (.expression actualTypes)) :
    runtimeApplicationCandidate actualTypes operatorType = none ↔
      ∀ result, ¬ApplicationPackageSuccessRel
        actualTypes operatorType result := by
  constructor
  · intro runtimeNone result specSuccess
    obtain ⟨leaResult, runtimeSome, _alpha⟩ :=
      runtimeApplicationCandidate_complete specSuccess disjoint
    rw [runtimeNone] at runtimeSome
    contradiction
  · intro noSpec
    cases runtimeSome : runtimeApplicationCandidate actualTypes operatorType with
    | none => rfl
    | some leaResult =>
        obtain ⟨result, specOutcome, _alpha⟩ :=
          runtimeApplicationCandidate_sound runtimeSome
        cases specOutcome with
        | success specSuccess => exact (noSpec result specSuccess).elim

/-- Complete exact outcome for one candidate, including the negative branch
used by ordered scans. -/
theorem runtimeApplicationCandidate_outcome
    {actualTypes : List Atom} {operatorType : Atom}
    (disjoint : VarsDisjoint operatorType (.expression actualTypes)) :
    ∃ specResult,
      ApplicationPackageOutcomeRel actualTypes operatorType specResult ∧
        match specResult, runtimeApplicationCandidate actualTypes operatorType with
        | none, none => True
        | some package, some leaResult =>
            ObservedTypeAlphaRel package.observed (fromLeaTTaAtom leaResult)
        | _, _ => False := by
  cases runtimeEquation : runtimeApplicationCandidate actualTypes operatorType with
  | none =>
      refine ⟨none, ApplicationPackageOutcomeRel.failure ?_, trivial⟩
      exact (runtimeApplicationCandidate_none_iff disjoint).mp runtimeEquation
  | some leaResult =>
      obtain ⟨result, outcome, alpha⟩ :=
        runtimeApplicationCandidate_sound runtimeEquation
      exact ⟨some result, outcome, alpha⟩

/-! ## Exact ordered candidate scan -/

/-- Concrete ordered `filterMap` corresponding to the spec application
package scan.  Inputs are native atoms so alpha-scope reasoning remains on
the independent side of the bridge; outputs are concrete LeaTTa atoms. -/
def runtimeApplicationCandidates
    (actualTypes operatorTypes : List Atom) : List Metta.Atom :=
  operatorTypes.filterMap (runtimeApplicationCandidate actualTypes)

/-- Every concrete ordered candidate scan has a spec package scan with the
same order, multiplicity, and alpha-exact observations. -/
theorem runtimeApplicationCandidates_sound
    {actualTypes operatorTypes : List Atom}
    (disjoint : ∀ operatorType ∈ operatorTypes,
      VarsDisjoint operatorType (.expression actualTypes)) :
    ∃ results,
      ApplicationPackageScanRel actualTypes operatorTypes results ∧
        List.Forall₂ ObservedTypeAlphaRel (observedTypes results)
          (fromLeaTTaAtoms
            (runtimeApplicationCandidates actualTypes operatorTypes)) := by
  induction operatorTypes with
  | nil =>
      exact ⟨[], ApplicationPackageScanRel.nil, List.Forall₂.nil⟩
  | cons operatorType operatorTypes ih =>
      have headDisjoint := disjoint operatorType (by simp)
      have tailDisjoint : ∀ candidate ∈ operatorTypes,
          VarsDisjoint candidate (.expression actualTypes) := by
        intro candidate member
        exact disjoint candidate (by simp [member])
      obtain ⟨tailResults, tailScan, tailAlpha⟩ := ih tailDisjoint
      cases runtimeEquation :
          runtimeApplicationCandidate actualTypes operatorType with
      | none =>
          have noSpec :=
            (runtimeApplicationCandidate_none_iff headDisjoint).mp
              runtimeEquation
          refine ⟨tailResults,
            ApplicationPackageScanRel.skip
              (ApplicationPackageOutcomeRel.failure noSpec) tailScan, ?_⟩
          simpa [runtimeApplicationCandidates, runtimeEquation,
            observedTypes] using tailAlpha
      | some leaResult =>
          obtain ⟨result, outcome, alpha⟩ :=
            runtimeApplicationCandidate_sound runtimeEquation
          refine ⟨result :: tailResults,
            ApplicationPackageScanRel.emit outcome tailScan, ?_⟩
          simpa [runtimeApplicationCandidates, runtimeEquation,
            observedTypes] using List.Forall₂.cons alpha tailAlpha

/-- Conversely, every spec ordered scan over disjoint scopes is realized
pointwise by the concrete filter.  Thus negative scan premises quantify over
the exact candidate list rather than a permissive over-approximation. -/
theorem runtimeApplicationCandidates_complete
    {actualTypes operatorTypes : List Atom} {results : List TypePackage}
    (scan : ApplicationPackageScanRel actualTypes operatorTypes results)
    (disjoint : ∀ operatorType ∈ operatorTypes,
      VarsDisjoint operatorType (.expression actualTypes)) :
    List.Forall₂ ObservedTypeAlphaRel (observedTypes results)
      (fromLeaTTaAtoms
        (runtimeApplicationCandidates actualTypes operatorTypes)) := by
  induction scan with
  | nil => exact List.Forall₂.nil
  | @skip operatorType operatorTypes results outcome tailScan ih =>
      cases outcome with
      | failure noSpec =>
          have headDisjoint := disjoint operatorType (by simp)
          have runtimeNone :=
            (runtimeApplicationCandidate_none_iff headDisjoint).mpr noSpec
          have tailDisjoint : ∀ candidate ∈ operatorTypes,
              VarsDisjoint candidate (.expression actualTypes) := by
            intro candidate member
            exact disjoint candidate (by simp [member])
          simpa [runtimeApplicationCandidates, runtimeNone,
            observedTypes] using ih tailDisjoint
  | @emit operatorType operatorTypes result results outcome tailScan ih =>
      cases outcome with
      | success specSuccess =>
          have headDisjoint := disjoint operatorType (by simp)
          obtain ⟨leaResult, runtimeSome, alpha⟩ :=
            runtimeApplicationCandidate_complete specSuccess headDisjoint
          have tailDisjoint : ∀ candidate ∈ operatorTypes,
              VarsDisjoint candidate (.expression actualTypes) := by
            intro candidate member
            exact disjoint candidate (by simp [member])
          simpa [runtimeApplicationCandidates, runtimeSome,
            observedTypes] using
              List.Forall₂.cons alpha (ih tailDisjoint)

/-! ## Boundary examples -/

/-- Positive: two distinct private sibling spellings can be transported
through a lawful identity freshening of one representative. -/
theorem private_sibling_variant_transport :
    TypeCandidateAlphaVariantRel []
      (.var "alpha#t") (.var "beta#t") := by
  apply ObservedTypeAlphaRel.transport_variant
      private_variables_alpha_siblings
  exact ⟨id, Function.injective_id,
    by simp [renameTypeVars], by simp⟩

/-- Negative: alpha transport never permits a target variable that violates
the declared finite avoid set. -/
theorem avoided_variable_not_variant :
    ¬TypeCandidateAlphaVariantRel ["public"]
      (.var "t") (.var "public") := by
  intro variant
  have fresh :=
    Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationExactConformance.TypeCandidateAlphaVariantRel.target_vars_fresh
      variant
  exact fresh "public" (by simp [TypeSubst.typeVars]) (by simp)

/-- Positive: a closed nullary arrow is realized without introducing a
private substitution. -/
theorem closed_nullary_candidate_complete :
    ∃ leaOutput,
      Metta.Minimal.matchApplicationTypeArguments Metta.Bindings.empty
          [] [] = some leaOutput ∧
        ObservedTypeAlphaRel (.symbol "R")
          (fromLeaTTaAtom
            (Metta.instantiate leaOutput (.sym "R"))) := by
  have success : ApplicationPackageSuccessRel []
      (.expression [.symbol "->", .symbol "R"])
      (inferredPackage [] (.symbol "R")) := by
    exact ApplicationPackageSuccessRel.mk
      (operatorType := .expression [.symbol "->", .symbol "R"])
      (returnType := .symbol "R") (expectedTypes := [])
      (actualTypes := []) (substitution := []) rfl
      (PresentationArgumentListMatchRel.nil [])
  have realized := applicationCandidate_complete
    (expectedTypes := []) (actualTypes := [])
    (returnType := .symbol "R") success
    (by simp [AtomListsVarsDisjoint, toLeaTTaAtoms])
  simpa [inferredPackage, toLeaTTaAtom, toLeaTTaAtoms] using realized

/-- Negative: unequal arities have no spec success package. -/
theorem unequal_arity_has_no_success (expected returnType : Atom) :
    ¬∃ result,
      ApplicationPackageSuccessRel []
        (.expression [.symbol "->", expected, returnType]) result := by
  rintro ⟨result, success⟩
  cases success with
  | mk shape fold =>
      cases fold with
      | nil => simp at shape

end Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationApplicationExact
