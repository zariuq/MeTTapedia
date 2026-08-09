import Mettapedia.Languages.MeTTa.HE.LeaTTaSpecTypeService
import Mettapedia.Languages.MeTTa.HE.LeaTTaBranchLocalTypeScanConformance
import Mettapedia.Languages.MeTTa.HE.LeaTTaSelectedTypePolicyConformance
import Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationSelectionConformance
import Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.SelectionEquivariance

/-!
# Exact prepared type-service instance for repaired LeaTTa

This module assembles the executable-independent pieces consumed by the
repaired runtime type service.  Operator signatures are alpha-localized at
the selection boundary, because the runtime keeps their type bindings private
while the published evaluator relation threads applicability bindings through
evaluation.  No caller-freshness premise is exposed by the service.

Argument preparation remains abstract.  One oracle relates source arguments
to prepared arguments, exact package lookup supplies every ordered candidate,
and a static freshness witness relates those packages to the independently
freshened candidates consumed by the branch scan.  The concrete `World` and
the executable preparation function occur only in the later realization
theorem, never in the relations below.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaTypeServiceConformance

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Bindings.ScopeObservation
open Spec.Eval
open Spec.Type
open Spec.Type.Presentation
open Spec.Type.Presentation.Alpha
open Spec.Type.Presentation.ApplicationEquivariance
open Spec.Type.Presentation.Completeness
open Spec.Type.Presentation.Exact
open Spec.Type.Presentation.ExactNormal
open Spec.Type.Presentation.Freshness
open Spec.Type.Presentation.MatchSolutionTheory
open Spec.Type.Presentation.PrincipalAlpha
open Spec.Type.Presentation.Selection
open Spec.Type.Presentation.SelectionEquivariance
open Spec.Type.Presentation.ScopeObservation
open Spec.Type.Presentation.Theory
open Spec.Type.RuntimeRefinement
open LeaTTaBridge
open LeaTTaBranchLocalTypeScanConformance
open LeaTTaSpecConformance
open LeaTTaSpecTypeService
open LeaTTaSelectedTypePolicyConformance
open LeaTTaTypeConformance
open LeaTTaTypePresentationApplicationExact
open LeaTTaTypePresentationExactConformance
open LeaTTaTypePresentationFoldConformance
open LeaTTaTypePresentationRecursiveExact
open LeaTTaTypePresentationSelectionConformance

/-! ## Runtime seed scope -/

/-- Post-instantiation caller variables whose selected applicability
assignments seed runtime application evaluation.  This scope deliberately
omits space variables: it describes runtime seeding, not seal observation. -/
def typeServiceRuntimeSeedScope
    (expression expectedType : Atom) : List String :=
  (TypeSubst.typeVars expectedType ++
    TypeSubst.typeVars expression).eraseDups

/-- The executable's visible selected-binding scope is exactly the abstract
runtime-seed scope after structural translation.  This is an equality of
ordered, duplicate-free lists, not merely a membership coincidence. -/
theorem typeServiceRuntimeSeedScope_eq_expectedApplicationVisibleScope
    (expression expectedType : Atom) :
    typeServiceRuntimeSeedScope expression expectedType =
      Metta.Minimal.expectedApplicationVisibleScope
        (toLeaTTaAtom expression) (toLeaTTaAtom expectedType) := by
  simp [typeServiceRuntimeSeedScope,
    Metta.Minimal.expectedApplicationVisibleScope,
    LeaTTaTypePresentationExactConformance.toLeaTTaAtom_vars_eq_typeVars]

/-- Runtime seeding observes only the post-instantiation expression and
expected type.  Every such name lies in the larger type-service scope, which
also contains the space theory used to protect private selection names. -/
theorem typeServiceRuntimeSeedScope_subset_observationScope
    (space : Space) (expression expectedType : Atom) :
    ∀ name, name ∈ typeServiceRuntimeSeedScope expression expectedType →
      name ∈ typeServiceObservationScope space expression expectedType := by
  intro name member
  simp only [typeServiceRuntimeSeedScope, List.mem_eraseDups,
    List.mem_append] at member
  rw [typeServiceObservationScope, typeVarsList_append]
  apply List.mem_append_right
  simp only [TypeSubst.typeVarsList, List.append_nil,
    List.mem_append]
  exact member.symm

/-! ## Exact type-cast scan -/

/-- A left-to-right alpha presentation proved fresh at a larger public scope
is also a presentation at every pointwise smaller scope.  The growing tail
scope retains each emitted target exactly, so this is stronger than applying
candidate-wise monotonicity after forgetting the fold structure. -/
theorem argumentAlphaVariantsRel_mono
    {small large : List String} {sources targets : List Atom}
    (variants : ArgumentAlphaVariantsRel large sources targets)
    (subset : ∀ name, name ∈ small → name ∈ large) :
    ArgumentAlphaVariantsRel small sources targets := by
  induction variants generalizing small with
  | nil => exact .nil small
  | @cons large source target sources targets head tail ih =>
      exact ArgumentAlphaVariantsRel.cons
        (TypeCandidateAlphaVariantRel.mono head subset)
        (ih (fun name member => by
          rw [List.mem_append] at member ⊢
          rcases member with member | member
          · exact Or.inl (subset name member)
          · exact Or.inr member))

/-- Operator candidates are localized independently at one common avoid
boundary, so weakening that boundary is pointwise. -/
theorem operatorAlphaVariantsRel_mono
    {small large : List String} {sources targets : List Atom}
    (variants : OperatorAlphaVariantsRel large sources targets)
    (subset : ∀ name, name ∈ small → name ∈ large) :
    OperatorAlphaVariantsRel small sources targets := by
  induction variants with
  | nil => exact .nil
  | cons head _ inductionHypothesis =>
      exact .cons (TypeCandidateAlphaVariantRel.mono head subset)
        inductionHypothesis

/-- A left-to-right alpha presentation preserves list arity exactly. -/
theorem argumentAlphaVariantsRel_length_eq
    {avoid : List String} {sources targets : List Atom}
    (variants : ArgumentAlphaVariantsRel avoid sources targets) :
    sources.length = targets.length := by
  induction variants with
  | nil => rfl
  | cons _ _ inductionHypothesis => simp [inductionHypothesis]

/-- Runtime failure of one fresh candidate excludes every native core-plus-R2
match, not only every finite-presentation derivation.  The presentation state
is used solely to turn a hypothetical native model into the complete finite
derivation required by matcher completeness. -/
theorem matchType_none_no_corePlusR2
    {presentation : TypeSubst} {incoming : Bindings}
    {runtime : Metta.Bindings} {expected actual : Atom}
    (state : TypePresentationSimulationState presentation incoming runtime)
    (disjoint : VarsDisjoint expected actual)
    (failure : Metta.Minimal.matchType runtime
      (toLeaTTaAtom expected) (toLeaTTaAtom actual) = none) :
    ∀ output, ¬CorePlusR2TypeMatchRel expected actual incoming output := by
  have noPresentation :=
    (matchType_eq_none_iff_no_presentation state expected actual disjoint).mp
      failure
  intro output derivation
  obtain ⟨valuation, outputSatisfied⟩ := derivation.satisfiable
  obtain ⟨incomingSatisfied, consistent⟩ :=
    (derivation.solutions valuation).mp outputSatisfied
  have presentationSatisfied :
      TypeSubstSatisfied valuation presentation :=
    (state.specSolutions valuation).mpr incomingSatisfied
  obtain ⟨presentationOutput, presentationDerivation, _, _⟩ :=
    CorePlusR2TypePresentationMatchRel.exists_of_satisfied
      state.normal presentationSatisfied expected actual consistent
  exact noPresentation presentationOutput presentationDerivation

/-- A successful runtime cast scan exposes the exact first successful native
match and every earlier native failure.  Every candidate is tested against
the same incoming binding state; selection commits at the first success. -/
theorem matchExpectedType_success_corePlusR2_exact
    {presentation : TypeSubst} {incoming : Bindings}
    {runtime runtimeOutput : Metta.Bindings}
    (state : TypePresentationSimulationState presentation incoming runtime)
    (expected : Atom) :
    ∀ candidates : List Atom,
      (∀ candidate ∈ candidates, VarsDisjoint expected candidate) →
      Metta.Minimal.matchExpectedType runtime (toLeaTTaAtom expected)
          (toLeaTTaAtoms candidates) = .inr runtimeOutput →
      ∃ before actual after presentationOutput output,
        candidates = before ++ actual :: after ∧
          (∀ earlier ∈ before, ∀ candidateOutput,
            ¬CorePlusR2TypeMatchRel
              expected earlier incoming candidateOutput) ∧
          CorePlusR2TypeMatchRel expected actual incoming output ∧
          TypePresentationSimulationState
            presentationOutput output runtimeOutput := by
  intro candidates
  induction candidates with
  | nil => simp [Metta.Minimal.matchExpectedType, toLeaTTaAtoms]
  | cons candidate candidates ih =>
      intro disjoint selected
      cases runtimeEquation : Metta.Minimal.matchType runtime
          (toLeaTTaAtom expected) (toLeaTTaAtom candidate) with
      | some headOutput =>
          change
            (match Metta.Minimal.matchType runtime
                (toLeaTTaAtom expected) (toLeaTTaAtom candidate) with
              | some output => Sum.inr output
              | none =>
                  match Metta.Minimal.matchExpectedType runtime
                      (toLeaTTaAtom expected) (toLeaTTaAtoms candidates) with
                  | Sum.inr output => Sum.inr output
                  | Sum.inl rejected =>
                      Sum.inl (toLeaTTaAtom candidate :: rejected)) =
              Sum.inr runtimeOutput at selected
          have outputEquation : headOutput = runtimeOutput := by
            rw [runtimeEquation] at selected
            exact Sum.inr.inj selected
          subst headOutput
          obtain ⟨presentationOutput, output, _presentationDerivation,
              derivation, outputState⟩ :=
            state.matchTypeFull expected candidate runtimeEquation
          exact ⟨[], candidate, candidates, presentationOutput, output,
            by simp, by simp,
            derivation, outputState⟩
      | none =>
          change
            (match Metta.Minimal.matchType runtime
                (toLeaTTaAtom expected) (toLeaTTaAtom candidate) with
              | some output => Sum.inr output
              | none =>
                  match Metta.Minimal.matchExpectedType runtime
                      (toLeaTTaAtom expected) (toLeaTTaAtoms candidates) with
                  | Sum.inr output => Sum.inr output
                  | Sum.inl rejected =>
                      Sum.inl (toLeaTTaAtom candidate :: rejected)) =
              Sum.inr runtimeOutput at selected
          cases tailEquation : Metta.Minimal.matchExpectedType runtime
              (toLeaTTaAtom expected) (toLeaTTaAtoms candidates) with
          | inl rejected =>
              rw [runtimeEquation, tailEquation] at selected
              contradiction
          | inr tailOutput =>
              have outputEquation : tailOutput = runtimeOutput := by
                rw [runtimeEquation, tailEquation] at selected
                exact Sum.inr.inj selected
              subst tailOutput
              obtain ⟨before, actual, after, presentationOutput, output,
                  split, beforeFailed,
                  selectedMatch, outputState⟩ :=
                ih (fun item member => disjoint item (by simp [member]))
                  tailEquation
              refine ⟨candidate :: before, actual, after,
                presentationOutput, output, ?_, ?_,
                selectedMatch, outputState⟩
              · simp [split]
              · intro earlier member candidateOutput
                rcases List.mem_cons.mp member with headEquation | member
                · subst earlier
                  exact matchType_none_no_corePlusR2 state
                    (disjoint _ (by simp)) runtimeEquation candidateOutput
                · exact beforeFailed earlier member candidateOutput

/-- A failed runtime cast scan returns the translated complete input list in
order, and every native member is a genuine core-plus-R2 failure. -/
theorem matchExpectedType_failure_corePlusR2_exact
    {presentation : TypeSubst} {incoming : Bindings}
    {runtime : Metta.Bindings}
    (state : TypePresentationSimulationState presentation incoming runtime)
    (expected : Atom) :
    ∀ candidates : List Atom, ∀ rejected : List Metta.Atom,
      (∀ candidate ∈ candidates, VarsDisjoint expected candidate) →
      Metta.Minimal.matchExpectedType runtime (toLeaTTaAtom expected)
          (toLeaTTaAtoms candidates) = .inl rejected →
      rejected = toLeaTTaAtoms candidates ∧
        ∀ candidate ∈ candidates, ∀ output,
          ¬CorePlusR2TypeMatchRel expected candidate incoming output := by
  intro candidates
  induction candidates with
  | nil =>
      intro rejected _ failed
      simpa [Metta.Minimal.matchExpectedType, toLeaTTaAtoms] using failed.symm
  | cons headCandidate candidates ih =>
      intro rejected disjoint failed
      cases runtimeEquation : Metta.Minimal.matchType runtime
          (toLeaTTaAtom expected) (toLeaTTaAtom headCandidate) with
      | some output =>
          change
            (match Metta.Minimal.matchType runtime
                (toLeaTTaAtom expected) (toLeaTTaAtom headCandidate) with
              | some output => Sum.inr output
              | none =>
                  match Metta.Minimal.matchExpectedType runtime
                      (toLeaTTaAtom expected) (toLeaTTaAtoms candidates) with
                  | Sum.inr output => Sum.inr output
                  | Sum.inl tailRejected =>
                      Sum.inl (toLeaTTaAtom headCandidate :: tailRejected)) =
              Sum.inl rejected at failed
          rw [runtimeEquation] at failed
          contradiction
      | none =>
          change
            (match Metta.Minimal.matchType runtime
                (toLeaTTaAtom expected) (toLeaTTaAtom headCandidate) with
              | some output => Sum.inr output
              | none =>
                  match Metta.Minimal.matchExpectedType runtime
                      (toLeaTTaAtom expected) (toLeaTTaAtoms candidates) with
                  | Sum.inr output => Sum.inr output
                  | Sum.inl tailRejected =>
                      Sum.inl (toLeaTTaAtom headCandidate :: tailRejected)) =
              Sum.inl rejected at failed
          cases tailEquation : Metta.Minimal.matchExpectedType runtime
              (toLeaTTaAtom expected) (toLeaTTaAtoms candidates) with
          | inr output =>
              rw [runtimeEquation, tailEquation] at failed
              contradiction
          | inl tailRejected =>
              rw [runtimeEquation, tailEquation] at failed
              have rejectedEquation :
                  rejected = toLeaTTaAtom headCandidate :: tailRejected :=
                (Sum.inl.inj failed).symm
              obtain ⟨tailExact, tailFailed⟩ := ih tailRejected
                (fun item member => disjoint item (by simp [member]))
                tailEquation
              constructor
              · rw [rejectedEquation, tailExact]
                rfl
              · intro item member output
                rcases List.mem_cons.mp member with headEquation | member
                · subst item
                  exact matchType_none_no_corePlusR2 state
                    (disjoint _ (by simp)) runtimeEquation output
                · exact tailFailed item member output

/-- Observable correspondence for `mettaTypeCast`.  Success carries the
native output binding theory; failure preserves the exact candidate order and
multiplicity and supplies one spec `BadType` derivation per rejected type. -/
inductive PreparedTypeCastOutcomeRuntimeRel
    (oracle : TypePreparationOracle) (space : Space)
    (atom expectedType : Atom) (incoming : Bindings) :
    Sum (List Metta.Atom) Metta.Bindings →
      (protectedScope : List String := []) → Prop where
  | success {presentation : TypeSubst} {output : Bindings}
      {runtimeOutput : Metta.Bindings} :
      PreparedTypeCastRel oracle space atom expectedType incoming
        (atom, output) protectedScope →
      TypePresentationSimulationState presentation output runtimeOutput →
      PreparedTypeCastOutcomeRuntimeRel oracle space atom expectedType incoming
        (.inr runtimeOutput) protectedScope
  | failure {sourceCandidates candidates : List Atom} :
      PreparedPackagesPresent oracle space atom sourceCandidates →
      ArgumentAlphaVariantsRel
        (protectedScope ++
          typeServicePrivateAvoid space atom expectedType incoming)
        sourceCandidates candidates →
      candidates ≠ [] →
      (∀ candidateType ∈ candidates, ∀ candidate,
        ¬CorePlusR2TypeMatchRel
          expectedType candidateType incoming candidate) →
      PreparedTypeCastOutcomeRuntimeRel oracle space atom expectedType incoming
        (.inl (toLeaTTaAtoms candidates)) protectedScope

/-! ## Prepared argument-package seam -/

/-- The operator-localization carrier is the ordered `Forall₂` relation at
its fixed avoid set.  This projection lets generic list combinators consume
the carrier without unfolding its constructors at every boundary. -/
theorem operatorAlphaVariantsRel_toForall₂
    {avoid : List String} {sources targets : List Atom}
    (variants : OperatorAlphaVariantsRel avoid sources targets) :
    List.Forall₂ (TypeCandidateAlphaVariantRel avoid) sources targets := by
  induction variants with
  | nil => exact .nil
  | cons head _ inductionHypothesis =>
      exact .cons head inductionHypothesis

/-- A concrete runtime world realizes an abstract preparation oracle when
every source atom has an independent prepared witness whose translation is
the runtime preparation result.  This is an implementation-side law, not a
field of the oracle. -/
def TypePreparationRuntimeRealization
    (oracle : TypePreparationOracle) (space : Space)
    (world : Metta.Minimal.World) : Prop :=
  ∀ atom, ∃ prepared,
    oracle.prepare space atom prepared ∧
      Metta.Minimal.typePrep world (toLeaTTaAtom atom) =
        toLeaTTaAtom prepared

/-- Exact package and preparation evidence for one argument before its
ordered candidate family is alpha-localized. -/
def RuntimePreparedArgumentFamilyRel
    (oracle : TypePreparationOracle) (space : Space)
    (env : Metta.Minimal.MinEnv) (world : Metta.Minimal.World)
    (argument : Atom) (rawCandidates : List Atom) : Prop :=
  ∃ prepared packages,
    oracle.prepare space argument prepared ∧
      Metta.Minimal.typePrep world (toLeaTTaAtom argument) =
        toLeaTTaAtom prepared ∧
      RuntimeTypePackagesRel space prepared packages ∧
      rawCandidates = fromLeaTTaAtoms
        (Metta.Minimal.getTypes env (toLeaTTaAtom prepared)) ∧
      List.Forall₂ ObservedTypeAlphaRel
        (observedTypes packages) rawCandidates

/-- Every source argument has one exact runtime-prepared raw family under a
realized abstract oracle. -/
theorem runtimePreparedArgumentFamily_exists
    {oracle : TypePreparationOracle} {space : Space}
    {env : Metta.Minimal.MinEnv} {world : Metta.Minimal.World}
    (index : TypeEnvironmentRel space env)
    (realization : TypePreparationRuntimeRealization oracle space world)
    (argument : Atom) :
    ∃ rawCandidates,
      RuntimePreparedArgumentFamilyRel oracle space env world
        argument rawCandidates := by
  obtain ⟨prepared, preparation, preparationEquation⟩ :=
    realization argument
  obtain ⟨packages, packageRelation, packageAlpha⟩ :=
    runtimeGetTypes_has_exact_package_presentation index prepared
  exact ⟨_, prepared, packages, preparation, preparationEquation,
    packageRelation, rfl, packageAlpha⟩

/-- Pointwise extension of exact runtime preparation to an ordered argument
list. -/
theorem runtimePreparedArgumentFamilies_exists
    {oracle : TypePreparationOracle} {space : Space}
    {env : Metta.Minimal.MinEnv} {world : Metta.Minimal.World}
    (index : TypeEnvironmentRel space env)
    (realization : TypePreparationRuntimeRealization oracle space world) :
    ∀ arguments, ∃ rawFamilies,
      List.Forall₂
        (RuntimePreparedArgumentFamilyRel oracle space env world)
        arguments rawFamilies := by
  intro arguments
  induction arguments with
  | nil => exact ⟨[], .nil⟩
  | cons argument arguments inductionHypothesis =>
      obtain ⟨rawCandidates, head⟩ :=
        runtimePreparedArgumentFamily_exists index realization argument
      obtain ⟨rawFamilies, tail⟩ := inductionHypothesis
      exact ⟨rawCandidates :: rawFamilies, .cons head tail⟩

/-- Transport a lawful alpha presentation across an observationally equal
source package. -/
theorem observedAlpha_alphaVariant_transport
    {avoid : List String} {observed raw target : Atom}
    (alpha : ObservedTypeAlphaRel observed raw)
    (variant : TypeCandidateAlphaVariantRel avoid raw target) :
    TypeCandidateAlphaVariantRel avoid observed target :=
  ObservedTypeAlphaRel.transport_variant alpha variant

/-- Ordered list companion of `observedAlpha_alphaVariant_transport`. -/
theorem observedAlphaList_alphaVariants_transport
    {avoid : List String} {observed raw targets : List Atom}
    (alpha : List.Forall₂ ObservedTypeAlphaRel observed raw)
    (variants : List.Forall₂
      (TypeCandidateAlphaVariantRel avoid) raw targets) :
    List.Forall₂ (TypeCandidateAlphaVariantRel avoid)
      observed targets := by
  induction alpha generalizing targets with
  | nil => cases variants; exact .nil
  | cons head _ inductionHypothesis =>
      cases variants with
      | cons variant variants =>
          exact .cons
            (observedAlpha_alphaVariant_transport head variant)
            (inductionHypothesis variants)

/-- Transport an ordered operator-candidate localization across an
observationally alpha-equivalent source presentation.  The target list is
unchanged, so declaration order and multiplicity remain literal. -/
theorem operatorAlphaVariants_transport_sources
    {avoid : List String} {observed raw targets : List Atom}
    (alpha : List.Forall₂ ObservedTypeAlphaRel observed raw)
    (variants : OperatorAlphaVariantsRel avoid raw targets) :
    OperatorAlphaVariantsRel avoid observed targets := by
  induction alpha generalizing targets with
  | nil =>
      cases variants
      exact .nil
  | cons head _ inductionHypothesis =>
      cases variants with
      | cons headVariant tailVariants =>
          exact .cons
            (observedAlpha_alphaVariant_transport head headVariant)
            (inductionHypothesis tailVariants)

/-- Deterministic operator freshening records the terminal generator counter
for every translated candidate.  This provenance stays on the realization
side and is consumed only by cross-family separation. -/
theorem freshenOperatorTypes_generatedAt
    (avoid : List String) (position : Nat) (sources : List Atom) :
    CandidateFamilyGeneratedAt position
      (fromLeaTTaAtoms
        ((toLeaTTaAtoms sources).map
          (Metta.Minimal.freshenTypeCandidate avoid position))) := by
  intro candidate candidateMember
  induction sources with
  | nil => simp at candidateMember
  | cons source sources inductionHypothesis =>
      simp only [toLeaTTaAtoms, List.map_cons, fromLeaTTaAtoms,
        List.mem_cons] at candidateMember
      rcases candidateMember with rfl | tailMember
      · refine ⟨avoid, source, ?_⟩
        simp only [Metta.Minimal.freshenTypeCandidate]
        rw [← LeaTTaTypePresentationExactConformance.toLeaTTaAtom_renameTypeVars,
          fromLeaTTaAtom_toLeaTTaAtom]
      · exact inductionHypothesis tailMember

/-- A candidate localized away from a finite name scope is separated from
the corresponding singleton variable atoms. -/
theorem TypeCandidateAlphaVariantRel.separated_from_variable_atoms
    {avoid scope : List String} {source target : Atom}
    (variant : TypeCandidateAlphaVariantRel avoid source target)
    (covered : ∀ name, name ∈ scope → name ∈ avoid) :
    FreshFamiliesSeparated [target] (scope.map Atom.var) := by
  intro name targetOccurrence scopeOccurrence
  have targetMember : name ∈ TypeSubst.typeVars target := by
    simpa [TypeSubst.typeVarsList] using targetOccurrence
  have scopeMember : name ∈ scope := by
    obtain ⟨variableAtom, variableAtomMember, variableOccurrence⟩ :=
      exists_mem_of_mem_typeVarsList scopeOccurrence
    obtain ⟨sourceName, sourceNameMember, rfl⟩ :=
      List.mem_map.mp variableAtomMember
    have nameEquation : name = sourceName := by
      simpa [TypeSubst.typeVars] using variableOccurrence
    simpa [nameEquation] using sourceNameMember
  exact TypeCandidateAlphaVariantRel.target_vars_fresh variant name
    targetMember (covered name scopeMember)

/-- Separation from two ordered right families composes without forgetting
either family's order or multiplicity. -/
theorem FreshFamiliesSeparated.append_right
    {left first second : List Atom}
    (firstSeparated : FreshFamiliesSeparated left first)
    (secondSeparated : FreshFamiliesSeparated left second) :
    FreshFamiliesSeparated left (first ++ second) := by
  intro name leftOccurrence rightOccurrence
  rw [typeVarsList_append, List.mem_append] at rightOccurrence
  rcases rightOccurrence with firstOccurrence | secondOccurrence
  · exact firstSeparated name leftOccurrence firstOccurrence
  · exact secondSeparated name leftOccurrence secondOccurrence

/-- Every formal-variable occurrence is an occurrence of the complete arrow
atom that contains it. -/
theorem FunctionTypeRel.argumentVars_subset
    {functionType returnType : Atom} {argumentTypes : List Atom}
    (function : FunctionTypeRel functionType argumentTypes returnType) :
    ∀ name, name ∈ TypeSubst.typeVarsList argumentTypes →
      name ∈ TypeSubst.typeVars functionType := by
  intro name member
  rw [FunctionTypeRel] at function
  rw [function]
  rw [TypeSubst.typeVars, TypeSubst.typeVarsList, List.mem_append]
  apply Or.inr
  rw [typeVarsList_append, List.mem_append]
  exact Or.inl member

/-- The return-variable support is also contained in the complete arrow. -/
theorem FunctionTypeRel.returnVars_subset
    {functionType returnType : Atom} {argumentTypes : List Atom}
    (function : FunctionTypeRel functionType argumentTypes returnType) :
    ∀ name, name ∈ TypeSubst.typeVars returnType →
      name ∈ TypeSubst.typeVars functionType := by
  intro name member
  rw [FunctionTypeRel] at function
  rw [function]
  rw [TypeSubst.typeVars, TypeSubst.typeVarsList, List.mem_append]
  apply Or.inr
  rw [typeVarsList_append, List.mem_append]
  apply Or.inr
  simpa [TypeSubst.typeVarsList] using member

/-- Runtime preparation, exact package lookup, and the two independent
operator-localization passes share one ordered raw candidate list.

The specification candidates avoid the complete service boundary, while the
runtime candidates use `functionTypeSelectionAvoid`.  Both are retained as
alpha variants of the same decoded `getTypes` list; later singleton
classification may therefore construct one coherent permutation without
identifying either side's private spelling. -/
theorem runtimePreparedOperatorCandidates_avoiding_exists
    {oracle : TypePreparationOracle} {space : Space}
    {env : Metta.Minimal.MinEnv} {world : Metta.Minimal.World}
    (index : TypeEnvironmentRel space env)
    (realization : TypePreparationRuntimeRealization oracle space world)
    (operator expectedType : Atom) (arguments : List Atom)
    (incoming : Bindings) (liveAvoid : List String) :
    let expression := Atom.expression (operator :: arguments)
    let rawRuntime := Metta.Minimal.getTypes env
      (Metta.Minimal.typePrep world (toLeaTTaAtom operator))
    let runtimeCandidates :=
      Metta.Minimal.freshenFunctionTypeCandidatesAvoiding env
        (toLeaTTaAtom expression) (toLeaTTaAtoms arguments)
        (toLeaTTaAtom expectedType) liveAvoid rawRuntime
    let specAvoid := typeServicePrivateAvoid space expression expectedType incoming
    let runtimeAvoid := Metta.Minimal.functionTypeSelectionAvoiding env
      (toLeaTTaAtom expression) (toLeaTTaAtoms arguments)
      (toLeaTTaAtom expectedType) liveAvoid rawRuntime
    ∃ prepared packages rawCandidates specCandidates,
      oracle.prepare space operator prepared ∧
      Metta.Minimal.typePrep world (toLeaTTaAtom operator) =
        toLeaTTaAtom prepared ∧
      RuntimeTypePackagesRel space prepared packages ∧
      rawCandidates = fromLeaTTaAtoms rawRuntime ∧
      List.Forall₂ ObservedTypeAlphaRel
        (observedTypes packages) rawCandidates ∧
      specCandidates = fromLeaTTaAtoms
        ((toLeaTTaAtoms rawCandidates).map
          (Metta.Minimal.freshenTypeCandidate specAvoid arguments.length)) ∧
      OperatorAlphaVariantsRel specAvoid rawCandidates specCandidates ∧
      OperatorAlphaVariantsRel specAvoid
        (observedTypes packages) specCandidates ∧
      OperatorAlphaVariantsRel runtimeAvoid rawCandidates
        (fromLeaTTaAtoms runtimeCandidates) ∧
      CandidateFamilyGeneratedAt arguments.length specCandidates ∧
      CandidateFamilyGeneratedAt arguments.length
        (fromLeaTTaAtoms runtimeCandidates) ∧
      toLeaTTaAtoms (fromLeaTTaAtoms runtimeCandidates) =
        runtimeCandidates := by
  dsimp only
  obtain ⟨prepared, preparation, preparationEquation⟩ :=
    realization operator
  obtain ⟨packages, packageRelation, packageAlpha⟩ :=
    runtimeGetTypes_has_exact_package_presentation index prepared
  let expression := Atom.expression (operator :: arguments)
  let rawRuntime := Metta.Minimal.getTypes env
    (Metta.Minimal.typePrep world (toLeaTTaAtom operator))
  let rawCandidates := fromLeaTTaAtoms rawRuntime
  let specAvoid := typeServicePrivateAvoid space expression expectedType incoming
  let runtimeAvoid := Metta.Minimal.functionTypeSelectionAvoiding env
    (toLeaTTaAtom expression) (toLeaTTaAtoms arguments)
    (toLeaTTaAtom expectedType) liveAvoid rawRuntime
  let specCandidates := fromLeaTTaAtoms
    ((toLeaTTaAtoms rawCandidates).map
      (Metta.Minimal.freshenTypeCandidate specAvoid arguments.length))
  have packageAlpha' : List.Forall₂ ObservedTypeAlphaRel
      (observedTypes packages) rawCandidates := by
    simpa [rawCandidates, rawRuntime, preparationEquation] using packageAlpha
  have specVariants : OperatorAlphaVariantsRel specAvoid rawCandidates
      specCandidates := by
    simpa [specCandidates] using
      (freshenOperatorTypes_alphaVariants specAvoid arguments.length
        rawCandidates)
  have rawRoundtrip : toLeaTTaAtoms rawCandidates = rawRuntime := by
    dsimp [rawCandidates, rawRuntime]
    rw [preparationEquation]
    exact runtimeOperatorTypes_roundtrip index prepared
  have runtimeCandidatesEquation :
      Metta.Minimal.freshenFunctionTypeCandidatesAvoiding env
          (toLeaTTaAtom expression) (toLeaTTaAtoms arguments)
          (toLeaTTaAtom expectedType) liveAvoid rawRuntime =
        (toLeaTTaAtoms rawCandidates).map
          (Metta.Minimal.freshenTypeCandidate runtimeAvoid arguments.length) := by
    dsimp only [Metta.Minimal.freshenFunctionTypeCandidatesAvoiding]
    have avoidEquation :
        Metta.Minimal.functionTypeSelectionAvoiding env
            (toLeaTTaAtom expression) (toLeaTTaAtoms arguments)
            (toLeaTTaAtom expectedType) liveAvoid rawRuntime = runtimeAvoid := rfl
    have argumentsLength : (toLeaTTaAtoms arguments).length = arguments.length := by
      rw [toLeaTTaAtoms_eq_map, List.length_map]
    rw [avoidEquation, argumentsLength, rawRoundtrip]
  have runtimeVariants : OperatorAlphaVariantsRel runtimeAvoid rawCandidates
      (fromLeaTTaAtoms
        (Metta.Minimal.freshenFunctionTypeCandidatesAvoiding env
          (toLeaTTaAtom expression) (toLeaTTaAtoms arguments)
          (toLeaTTaAtom expectedType) liveAvoid rawRuntime)) := by
    rw [runtimeCandidatesEquation]
    exact freshenOperatorTypes_alphaVariants runtimeAvoid arguments.length
      rawCandidates
  have specGenerated : CandidateFamilyGeneratedAt arguments.length
      specCandidates := by
    dsimp [specCandidates]
    exact freshenOperatorTypes_generatedAt specAvoid arguments.length
      rawCandidates
  have runtimeGenerated : CandidateFamilyGeneratedAt arguments.length
      (fromLeaTTaAtoms
        (Metta.Minimal.freshenFunctionTypeCandidatesAvoiding env
          (toLeaTTaAtom expression) (toLeaTTaAtoms arguments)
          (toLeaTTaAtom expectedType) liveAvoid rawRuntime)) := by
    rw [runtimeCandidatesEquation]
    exact freshenOperatorTypes_generatedAt runtimeAvoid arguments.length
      rawCandidates
  have runtimeRoundtrip :
      toLeaTTaAtoms
          (fromLeaTTaAtoms
            (Metta.Minimal.freshenFunctionTypeCandidatesAvoiding env
              (toLeaTTaAtom expression) (toLeaTTaAtoms arguments)
              (toLeaTTaAtom expectedType) liveAvoid rawRuntime)) =
        Metta.Minimal.freshenFunctionTypeCandidatesAvoiding env
          (toLeaTTaAtom expression) (toLeaTTaAtoms arguments)
          (toLeaTTaAtom expectedType) liveAvoid rawRuntime := by
    rw [runtimeCandidatesEquation, rawRoundtrip]
    dsimp [rawRuntime]
    rw [preparationEquation]
    exact runtimeFreshenedOperatorTypes_roundtrip index prepared
      runtimeAvoid arguments.length
  exact ⟨prepared, packages, rawCandidates, specCandidates,
    preparation, preparationEquation, packageRelation, rfl, packageAlpha',
    rfl, specVariants,
    operatorAlphaVariants_transport_sources packageAlpha' specVariants,
    runtimeVariants, specGenerated, runtimeGenerated, runtimeRoundtrip⟩

/-- Pointwise observed alpha-equivalence is symmetric without changing list
order or multiplicity. -/
theorem observedAlphaList_symm
    {left right : List Atom}
    (alpha : List.Forall₂ ObservedTypeAlphaRel left right) :
    List.Forall₂ ObservedTypeAlphaRel right left := by
  induction alpha with
  | nil => exact .nil
  | cons head _ inductionHypothesis =>
      exact .cons head.symm inductionHypothesis

/-- Recover the abstract preparation and exact package lists from pointwise
runtime-family evidence, preserving argument order. -/
theorem runtimePreparedArgumentFamilies_packageData
    {oracle : TypePreparationOracle} {space : Space}
    {env : Metta.Minimal.MinEnv} {world : Metta.Minimal.World}
    {arguments : List Atom} {rawFamilies : List (List Atom)}
    (families : List.Forall₂
      (RuntimePreparedArgumentFamilyRel oracle space env world)
      arguments rawFamilies) :
    ∃ preparedArguments packageLists,
      List.Forall₂ (oracle.prepare space)
        arguments preparedArguments ∧
      List.Forall₂ (RuntimeTypePackagesRel space)
        preparedArguments packageLists ∧
      List.Forall₂
        (fun packages rawCandidates =>
          List.Forall₂ ObservedTypeAlphaRel
            (observedTypes packages) rawCandidates)
        packageLists rawFamilies := by
  induction families with
  | nil => exact ⟨[], [], .nil, .nil, .nil⟩
  | @cons argument rawCandidates arguments rawFamilies head tail
      inductionHypothesis =>
      rcases head with
        ⟨prepared, packages, preparation, _preparationEquation,
          packageRelation, _rawEquation, packageAlpha⟩
      obtain ⟨preparedArguments, packageLists, preparations,
        packageRelations, packageAlphas⟩ := inductionHypothesis
      exact ⟨prepared :: preparedArguments, packages :: packageLists,
        .cons preparation preparations,
        .cons packageRelation packageRelations,
        .cons packageAlpha packageAlphas⟩

/-- Compose package-to-raw alpha observations with raw-to-static variants
for every argument position. -/
theorem packageAlphaLists_alphaVariants_transport
    {avoid : List String}
    {packageLists : List (List TypePackage)}
    {rawFamilies targetFamilies : List (List Atom)}
    (alpha : List.Forall₂
      (fun packages rawCandidates =>
        List.Forall₂ ObservedTypeAlphaRel
          (observedTypes packages) rawCandidates)
      packageLists rawFamilies)
    (variants : List.Forall₂
      (fun rawCandidates targets =>
        List.Forall₂ (TypeCandidateAlphaVariantRel avoid)
          rawCandidates targets)
      rawFamilies targetFamilies) :
    List.Forall₂
      (fun packages targets =>
        List.Forall₂ (TypeCandidateAlphaVariantRel avoid)
          (observedTypes packages) targets)
      packageLists targetFamilies := by
  induction alpha generalizing targetFamilies with
  | nil => cases variants; exact .nil
  | cons head _ inductionHypothesis =>
      cases variants with
      | cons headVariants tailVariants =>
          exact .cons
            (observedAlphaList_alphaVariants_transport head headVariants)
            (inductionHypothesis tailVariants)

/-- One source argument, its abstractly prepared package list, and the exact
ordered static candidate family selected for the independent scan.  This is
the pointwise view consumed by the node-local runtime bridge. -/
def PreparedArgumentCandidateFamilyRel
    (oracle : TypePreparationOracle) (space : Space)
    (forbidden : List String) (argument : Atom)
    (candidates : List Atom) : Prop :=
  ∃ prepared packages,
    oracle.prepare space argument prepared ∧
      RuntimeTypePackagesRel space prepared packages ∧
      List.Forall₂ (TypeCandidateAlphaVariantRel forbidden)
        (observedTypes packages) candidates

/-- Ordered prepared arguments, their exact package lists, and the fresh
candidate families consumed by one function signature.

The oracle and package relations retain source order.  Each target candidate
is an injective alpha-variant avoiding the complete public boundary.  The
static `PreparedArgumentCandidateLists` witness additionally separates the
function-formal scope, the initial private substitution, and distinct
argument-position families. -/
def PreparedArgumentPackageCandidates
    (oracle : TypePreparationOracle) (space : Space)
    (forbidden : List String) (formals arguments : List Atom)
    (candidateLists : List (List Atom)) : Prop :=
  ∃ preparedArguments packageLists,
    List.Forall₂ (oracle.prepare space) arguments preparedArguments ∧
    List.Forall₂ (RuntimeTypePackagesRel space)
      preparedArguments packageLists ∧
    List.Forall₂
      (fun packageList candidates =>
        List.Forall₂ (TypeCandidateAlphaVariantRel forbidden)
          (observedTypes packageList) candidates)
      packageLists candidateLists ∧
    PreparedArgumentCandidateLists formals [] candidateLists
      (candidateLists.map toLeaTTaAtoms)

/-- Choosing the realization-side generated families discharges the whole
static prepared-package seam without strengthening the specification. -/
theorem preparedArgumentPackageCandidates_of_runtimeFamilies
    {oracle : TypePreparationOracle} {space : Space}
    {env : Metta.Minimal.MinEnv} {world : Metta.Minimal.World}
    {forbidden : List String} {formals arguments : List Atom}
    {rawFamilies : List (List Atom)}
    (families : List.Forall₂
      (RuntimePreparedArgumentFamilyRel oracle space env world)
      arguments rawFamilies) :
    let avoid := forbidden ++ TypeSubst.typeVarsList formals
    let candidateLists :=
      freshenArgumentCandidateFamilies avoid 0 rawFamilies
    PreparedArgumentPackageCandidates oracle space forbidden
      formals arguments candidateLists := by
  dsimp only
  let avoid := forbidden ++ TypeSubst.typeVarsList formals
  let candidateLists := freshenArgumentCandidateFamilies avoid 0 rawFamilies
  obtain ⟨preparedArguments, packageLists, preparations,
      packageRelations, packageAlphas⟩ :=
    runtimePreparedArgumentFamilies_packageData families
  have generatedVariants : List.Forall₂
      (fun rawCandidates targets =>
        List.Forall₂ (TypeCandidateAlphaVariantRel avoid)
          rawCandidates targets)
      rawFamilies candidateLists := by
    exact freshenArgumentCandidateFamilies_alphaVariants avoid 0 rawFamilies
  have publicVariants : List.Forall₂
      (fun rawCandidates targets =>
        List.Forall₂ (TypeCandidateAlphaVariantRel forbidden)
          rawCandidates targets)
      rawFamilies candidateLists := by
    exact generatedVariants.imp fun _ _ variants =>
      candidateFamilyAlphaVariants_mono variants
        (fun name member => List.mem_append_left _ member)
  exact ⟨preparedArguments, packageLists, preparations, packageRelations,
    packageAlphaLists_alphaVariants_transport packageAlphas publicVariants,
    freshenArgumentCandidateFamilies_prepared forbidden formals rawFamilies⟩

/-- Implementation-side provenance for the particular existential static
family chosen at realization.  The specification sees only
`PreparedArgumentPackageCandidates`; the generator equation remains confined
to this bridge. -/
def RuntimePreparedArgumentPackageCandidates
    (oracle : TypePreparationOracle) (space : Space)
    (env : Metta.Minimal.MinEnv) (world : Metta.Minimal.World)
    (forbidden : List String) (formals arguments : List Atom)
    (candidateLists : List (List Atom)) : Prop :=
  ∃ rawFamilies,
    List.Forall₂
      (RuntimePreparedArgumentFamilyRel oracle space env world)
      arguments rawFamilies ∧
    candidateLists = freshenArgumentCandidateFamilies
      (forbidden ++ TypeSubst.typeVarsList formals) 0 rawFamilies

/-- The concrete bridge provenance forgets to the generator-free prepared
package relation consumed by the specification. -/
theorem RuntimePreparedArgumentPackageCandidates.prepared
    {oracle : TypePreparationOracle} {space : Space}
    {env : Metta.Minimal.MinEnv} {world : Metta.Minimal.World}
    {forbidden : List String} {formals arguments : List Atom}
    {candidateLists : List (List Atom)}
    (runtimePrepared : RuntimePreparedArgumentPackageCandidates oracle space
      env world forbidden formals arguments candidateLists) :
    PreparedArgumentPackageCandidates oracle space forbidden
      formals arguments candidateLists := by
  obtain ⟨rawFamilies, families, rfl⟩ := runtimePrepared
  exact preparedArgumentPackageCandidates_of_runtimeFamilies families

/-- The realization-chosen argument families are separated from a function
signature localized at the immediately following position.  This is the
producer-side proof of the shared `FreshFamiliesSeparated` clause; neither
the abstract preparation oracle nor the specification carrier mentions the
concrete generator. -/
theorem RuntimePreparedArgumentPackageCandidates.freshLocalizedCandidateSeparated
    {oracle : TypePreparationOracle} {space : Space}
    {env : Metta.Minimal.MinEnv} {world : Metta.Minimal.World}
    {forbidden : List String} {formals arguments : List Atom}
    {candidateLists : List (List Atom)}
    (runtimePrepared : RuntimePreparedArgumentPackageCandidates oracle space
      env world forbidden formals arguments candidateLists)
    (arity : arguments.length = formals.length)
    (signatureAvoid : List String) (candidate : Atom) :
    FreshFamiliesSeparated
      [renameTypeVars
        (Metta.Minimal.captureAvoidingName signatureAvoid formals.length)
        candidate]
      candidateLists.flatten := by
  obtain ⟨rawFamilies, families, rfl⟩ := runtimePrepared
  have rawLength : rawFamilies.length = formals.length := by
    calc
      rawFamilies.length = arguments.length := families.length_eq.symm
      _ = formals.length := arity
  have separated :=
    freshenCandidateFamily_separated_from_argumentFamilies
      signatureAvoid
      (forbidden ++ TypeSubst.typeVarsList formals)
      0 [candidate] rawFamilies
  simpa [freshenCandidateFamily, rawLength] using separated

/-- A realized preparation oracle supplies one generator-chosen family list
for every ordered argument list. -/
theorem runtimePreparedArgumentPackageCandidates_exists
    {oracle : TypePreparationOracle} {space : Space}
    {env : Metta.Minimal.MinEnv} {world : Metta.Minimal.World}
    (index : TypeEnvironmentRel space env)
    (realization : TypePreparationRuntimeRealization oracle space world)
    (forbidden : List String) (formals arguments : List Atom) :
    ∃ candidateLists,
      RuntimePreparedArgumentPackageCandidates oracle space env world
        forbidden formals arguments candidateLists := by
  obtain ⟨rawFamilies, families⟩ :=
    runtimePreparedArgumentFamilies_exists index realization arguments
  exact ⟨freshenArgumentCandidateFamilies
      (forbidden ++ TypeSubst.typeVarsList formals) 0 rawFamilies,
    rawFamilies, families, rfl⟩

/-- Prepared candidate families preserve the number of source arguments. -/
theorem PreparedArgumentPackageCandidates.arguments_length
    {oracle : TypePreparationOracle} {space : Space}
    {forbidden : List String} {formals arguments : List Atom}
    {candidateLists : List (List Atom)}
    (prepared : PreparedArgumentPackageCandidates oracle space forbidden
      formals arguments candidateLists) :
    candidateLists.length = arguments.length := by
  obtain ⟨preparedArguments, packageLists, prepares, packages, alpha, _⟩ :=
    prepared
  calc
    candidateLists.length = packageLists.length := alpha.length_eq.symm
    _ = preparedArguments.length := packages.length_eq.symm
    _ = arguments.length := prepares.length_eq.symm

/-- Re-index prepared argument packages by a function signature that is
separated from the complete candidate family.

Package lookup, argument preparation, order, and family-to-family separation
do not depend on the spelling of the function's private variables.  Only the
formal-avoidance field changes, and full arrow/candidate separation supplies
exactly that fact.  This is the boundary used after an independently
freshened runtime signature is transported to the specification spelling. -/
theorem PreparedArgumentPackageCandidates.reformalize
    {oracle : TypePreparationOracle} {space : Space}
    {forbidden : List String} {oldFormals newFormals arguments : List Atom}
    {candidateLists : List (List Atom)} {functionType returnType : Atom}
    (prepared : PreparedArgumentPackageCandidates oracle space forbidden
      oldFormals arguments candidateLists)
    (arrow : FunctionTypeRel functionType newFormals returnType)
    (separated : FreshFamiliesSeparated [functionType]
      candidateLists.flatten) :
    PreparedArgumentPackageCandidates oracle space forbidden
      newFormals arguments candidateLists := by
  obtain ⟨preparedArguments, packageLists, preparations, packages,
      variants, static⟩ := prepared
  refine ⟨preparedArguments, packageLists, preparations, packages,
    variants, ?_⟩
  refine
    { link := static.link
      avoidFormals := ?_
      avoidInitial := static.avoidInitial
      families := static.families }
  have candidateAvoidsArrow := separated.symm
  intro name candidateOccurrence formalOccurrence
  apply candidateAvoidsArrow name candidateOccurrence
  obtain ⟨formal, formalMember, occurrence⟩ :=
    exists_mem_of_mem_typeVarsList formalOccurrence
  apply typeVars_mem_typeVarsList_of_mem
    (atom := functionType) (atoms := [functionType]) (by simp) name
  rw [FunctionTypeRel] at arrow
  rw [arrow]
  simp only [TypeSubst.typeVars]
  apply typeVars_mem_typeVarsList_of_mem
    (atom := formal)
    (atoms := .symbol "->" :: (newFormals ++ [returnType]))
  · simp [formalMember]
  · exact occurrence

/-- Whole-list preparation exposes the pointwise family relation without
changing order, multiplicity, or grouping. -/
theorem PreparedArgumentPackageCandidates.familyRel
    {oracle : TypePreparationOracle} {space : Space}
    {forbidden : List String} {formals arguments : List Atom}
    {candidateLists : List (List Atom)}
    (prepared : PreparedArgumentPackageCandidates oracle space forbidden
      formals arguments candidateLists) :
    List.Forall₂
      (PreparedArgumentCandidateFamilyRel oracle space forbidden)
      arguments candidateLists := by
  obtain ⟨preparedArguments, packageLists, preparations, packages,
      variants, staticPrepared⟩ := prepared
  clear staticPrepared formals
  induction preparations generalizing packageLists candidateLists with
  | nil =>
      cases packages
      cases variants
      exact .nil
  | @cons argument preparedArgument arguments preparedArguments
      preparation preparations inductionHypothesis =>
      cases packages with
      | cons packageRel packageRels =>
          cases variants with
          | cons headVariants tailVariants =>
              exact .cons
                ⟨preparedArgument, _, preparation, packageRel,
                  headVariants⟩
                (inductionHypothesis (packageLists := _)
                  (candidateLists := _) packageRels tailVariants)

/-- A finite candidate alpha-variant is an alpha observation of its source.
This forgets only the avoidance certificate; declaration order and
multiplicity remain in the surrounding `Forall₂`. -/
private theorem candidateAlphaVariants_observed
    {avoid : List String} {sources targets : List Atom}
    (variants : List.Forall₂ (TypeCandidateAlphaVariantRel avoid)
      sources targets) :
    List.Forall₂ ObservedTypeAlphaRel sources targets := by
  induction variants with
  | nil => exact .nil
  | @cons source target sources targets head tail inductionHypothesis =>
      exact .cons
        ⟨source, TypeVariableRenamingOf.refl source,
          head.toTypeVariableRenamingOf⟩
        inductionHypothesis

/-- Pointwise candidate-family freshening retains the ordered family shape
and forgets only the avoidance certificates. -/
private theorem candidateAlphaVariantFamilies_observed
    {avoid : List String} {packages : List (List TypePackage)}
    {candidates : List (List Atom)}
    (variants : List.Forall₂
      (fun package family =>
        List.Forall₂ (TypeCandidateAlphaVariantRel avoid)
          (observedTypes package) family)
      packages candidates) :
    List.Forall₂
      (fun package family => List.Forall₂ ObservedTypeAlphaRel
        (observedTypes package) family)
      packages candidates := by
  induction variants with
  | nil => exact .nil
  | cons head _ inductionHypothesis =>
      exact .cons (candidateAlphaVariants_observed head) inductionHypothesis

/-- Pointwise private variants make the flattened target families avoid the
declared public scope.  Flattening changes only grouping, never the finite
freshness obligation. -/
private theorem candidateAlphaVariantFamilies_avoid
    {avoid : List String} {packages : List (List TypePackage)}
    {candidates : List (List Atom)}
    (variants : List.Forall₂
      (fun package family =>
        List.Forall₂ (TypeCandidateAlphaVariantRel avoid)
          (observedTypes package) family)
      packages candidates) :
    AtomsAvoid candidates.flatten avoid := by
  induction variants with
  | nil => simp [AtomsAvoid, TypeSubst.typeVarsList]
  | @cons package family packages families head tail inductionHypothesis =>
      have headAvoids := candidateFamilyAlphaVariants_avoids head
      intro name occurrence avoidMember
      simp only [List.flatten_cons, typeVarsList_append,
        List.mem_append] at occurrence
      rcases occurrence with headOccurrence | tailOccurrence
      · exact headAvoids name headOccurrence avoidMember
      · exact inductionHypothesis name tailOccurrence avoidMember

/-- Three aligned family presentations compose pointwise without changing
argument positions, declaration order, or multiplicity. -/
private theorem observedTypeAlphaFamilies_triangle
    {leftPackages rightPackages : List (List TypePackage)}
    {leftCandidates rightCandidates : List (List Atom)}
    (left : List.Forall₂
      (fun package family => List.Forall₂ ObservedTypeAlphaRel
        (observedTypes package) family)
      leftPackages leftCandidates)
    (middle : List.Forall₂
      (fun leftPackage rightPackage => List.Forall₂ ObservedTypeAlphaRel
        (observedTypes leftPackage) (observedTypes rightPackage))
      leftPackages rightPackages)
    (right : List.Forall₂
      (fun package family => List.Forall₂ ObservedTypeAlphaRel
        (observedTypes package) family)
      rightPackages rightCandidates) :
    List.Forall₂ (List.Forall₂ ObservedTypeAlphaRel)
      leftCandidates rightCandidates := by
  induction left generalizing rightPackages rightCandidates with
  | nil =>
      cases middle
      cases right
      exact .nil
  | @cons leftPackage leftCandidates leftPackages leftCandidateLists
      leftHead leftTail inductionHypothesis =>
      cases middle with
      | @cons _ rightPackage _ rightPackages middleHead middleTail =>
          cases right with
          | @cons _ rightCandidates _ rightCandidateLists rightHead rightTail =>
              exact .cons
                (observedTypeAlphaList_trans
                  (observedTypeAlphaList_trans
                    (observedAlphaList_symm leftHead) middleHead)
                  rightHead)
                (inductionHypothesis middleTail rightTail)

/-- Functional preparation and exact package lookup make the ordered package
families unique up to private alpha spelling.  This theorem deliberately
retains the list-of-lists shape: argument positions and declaration order are
observable by the branch search. -/
private theorem preparedPackageFamilies_alpha_unique
    {oracle : TypePreparationOracle}
    (functional : TypePreparationFunctional oracle)
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env) :
    ∀ {arguments leftPrepared rightPrepared : List Atom}
        {leftPackages rightPackages : List (List TypePackage)},
      List.Forall₂ (oracle.prepare space) arguments leftPrepared →
      List.Forall₂ (oracle.prepare space) arguments rightPrepared →
      List.Forall₂ (RuntimeTypePackagesRel space)
        leftPrepared leftPackages →
      List.Forall₂ (RuntimeTypePackagesRel space)
        rightPrepared rightPackages →
      List.Forall₂
        (fun left right => List.Forall₂ ObservedTypeAlphaRel
          (observedTypes left) (observedTypes right))
        leftPackages rightPackages := by
  intro arguments leftPrepared rightPrepared leftPackages rightPackages
    leftPreparation
  induction leftPreparation generalizing rightPrepared leftPackages
      rightPackages with
  | nil =>
      intro rightPreparation leftRelations rightRelations
      cases rightPreparation
      cases leftRelations
      cases rightRelations
      exact .nil
  | @cons argument leftHead arguments leftTail leftHeadPreparation
      leftTailPreparation inductionHypothesis =>
      intro rightPreparation leftRelations rightRelations
      cases rightPreparation with
      | @cons _ rightHead _ rightTail rightHeadPreparation
          rightTailPreparation =>
          cases leftRelations with
          | @cons _ leftPackage _ leftPackageTail leftPackageRelation
              leftPackageRelations =>
              cases rightRelations with
              | @cons _ rightPackage _ rightPackageTail rightPackageRelation
                  rightPackageRelations =>
                  have preparedEquation : leftHead = rightHead :=
                    functional space argument leftHead rightHead
                      leftHeadPreparation rightHeadPreparation
                  subst rightHead
                  exact .cons
                    (runtimeTypePackages_alpha_unique index
                      leftPackageRelation rightPackageRelation)
                    (inductionHypothesis rightTailPreparation
                      leftPackageRelations rightPackageRelations)

/-- Any two lawful prepared candidate-family presentations for the same
ordered source arguments are pointwise alpha-equivalent.  This is the exact
negative bridge: a different private spelling cannot add or remove a
declaration-position candidate. -/
theorem PreparedArgumentPackageCandidates.alpha_unique
    {oracle : TypePreparationOracle}
    (functional : TypePreparationFunctional oracle)
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env)
    {leftForbidden rightForbidden : List String}
    {leftFormals rightFormals arguments : List Atom}
    {leftCandidates rightCandidates : List (List Atom)}
    (left : PreparedArgumentPackageCandidates oracle space leftForbidden
      leftFormals arguments leftCandidates)
    (right : PreparedArgumentPackageCandidates oracle space rightForbidden
      rightFormals arguments rightCandidates) :
    List.Forall₂ (List.Forall₂ ObservedTypeAlphaRel)
      leftCandidates rightCandidates := by
  obtain ⟨leftPrepared, leftPackages, leftPreparation, leftPackageRelations,
      leftVariants, _leftStatic⟩ := left
  obtain ⟨rightPrepared, rightPackages, rightPreparation,
      rightPackageRelations, rightVariants, _rightStatic⟩ := right
  have packageAlpha := preparedPackageFamilies_alpha_unique functional index
    leftPreparation rightPreparation leftPackageRelations
      rightPackageRelations
  exact observedTypeAlphaFamilies_triangle
    (candidateAlphaVariantFamilies_observed leftVariants)
    packageAlpha
    (candidateAlphaVariantFamilies_observed rightVariants)

/-- Every candidate in a lawful prepared package family avoids the public
scope named at preparation. -/
theorem PreparedArgumentPackageCandidates.candidatesAvoid
    {oracle : TypePreparationOracle} {space : Space}
    {forbidden : List String} {formals arguments : List Atom}
    {candidateLists : List (List Atom)}
    (prepared : PreparedArgumentPackageCandidates oracle space forbidden
      formals arguments candidateLists) :
    AtomsAvoid candidateLists.flatten forbidden := by
  obtain ⟨_preparedArguments, packageLists, _preparations,
      _packageRelations, variants, _static⟩ := prepared
  exact candidateAlphaVariantFamilies_avoid variants

/-- Alpha-renaming cannot turn the exact type service's nonempty package
readout into an empty candidate family. -/
private theorem preparedCandidateFamily_nonempty
    {space : Space} {prepared : Atom} {packages : List TypePackage}
    {avoid : List String} {candidates : List Atom}
    (packageRelation : RuntimeTypePackagesRel space prepared packages)
    (variants : List.Forall₂ (TypeCandidateAlphaVariantRel avoid)
      (observedTypes packages) candidates) :
    candidates ≠ [] := by
  intro candidatesEmpty
  have packagesLength : packages.length = 0 := by
    have alignedLength := variants.length_eq
    simpa [observedTypes, candidatesEmpty] using alignedLength
  have packagesEmpty : packages = [] := by simpa using packagesLength
  exact packageRelation.nonempty packagesEmpty

/-- Every argument position in exact package preparation has at least one
candidate; the explicit undefined package supplies the fallback when lookup
or inference finds no declared type. -/
theorem PreparedArgumentPackageCandidates.familiesNonempty
    {oracle : TypePreparationOracle} {space : Space}
    {forbidden : List String} {formals arguments : List Atom}
    {candidateLists : List (List Atom)}
    (prepared : PreparedArgumentPackageCandidates oracle space forbidden
      formals arguments candidateLists) :
    ∀ family ∈ candidateLists, family ≠ [] := by
  obtain ⟨preparedArguments, packageLists, preparations,
      packageRelations, variants, _static⟩ := prepared
  clear _static
  intro family familyMember
  induction variants generalizing arguments preparedArguments with
  | nil => simp at familyMember
  | @cons packages candidates packageTail candidateTail head tail
      inductionHypothesis =>
      cases packageRelations with
      | @cons prepared packages preparedTail packageTail packageRelation
          packageRelations =>
          cases preparations with
          | @cons argument prepared arguments preparedTail preparation preparations =>
              rcases List.mem_cons.mp familyMember with rfl | tailMember
              · exact preparedCandidateFamily_nonempty packageRelation head
              · exact inductionHypothesis preparedTail preparations
                  packageRelations tailMember

/-- The shared arrow and expected type may overlap with each other, but their
combined public scope is disjoint from every privately prepared argument
candidate.  Packaging them as one atom lets the global alpha-permutation fix
both without imposing a false disjointness premise between public types. -/
theorem PreparedArgumentPackageCandidates.applicationScopeSeparated
    {oracle : TypePreparationOracle} {space : Space}
    {expression candidate expectedType : Atom} {bindings : Bindings}
    {formals arguments : List Atom} {candidateLists : List (List Atom)}
    (prepared : PreparedArgumentPackageCandidates oracle space
      (typeServicePrivateAvoid space expression expectedType bindings)
      formals arguments candidateLists)
    (candidateSeparated : FreshFamiliesSeparated [candidate]
      candidateLists.flatten) :
    FreshFamiliesSeparated [.expression [candidate, expectedType]]
      candidateLists.flatten := by
  intro name publicOccurrence candidateOccurrence
  simp only [TypeSubst.typeVarsList, TypeSubst.typeVars,
    List.mem_append, List.not_mem_nil, or_false] at publicOccurrence
  rcases publicOccurrence with candidateOccurrence' | expectedOccurrence
  · exact candidateSeparated name
      (by simpa [TypeSubst.typeVarsList] using candidateOccurrence')
      candidateOccurrence
  · have expectedInObservation : name ∈
        TypeSubst.typeVarsList (space.atoms ++ [expression, expectedType]) :=
      typeVars_mem_typeVarsList_of_mem (atom := expectedType)
        (atoms := space.atoms ++ [expression, expectedType]) (by simp)
          name expectedOccurrence
    have expectedInPrivate : name ∈
        typeServicePrivateAvoid space expression expectedType bindings := by
      exact List.mem_append_left _ expectedInObservation
    exact prepared.candidatesAvoid name candidateOccurrence expectedInPrivate

/-- Selecting one declared candidate from every aligned family preserves the
positionwise alpha relation.  The right witnesses are chosen at the same list
indices; no permutation, deduplication, or membership quotient is used. -/
theorem candidateChoices_alpha
    {leftFamilies rightFamilies : List (List Atom)}
    {leftChoices : List Atom}
    (families : List.Forall₂ (List.Forall₂ ObservedTypeAlphaRel)
      leftFamilies rightFamilies)
    (choices : List.Forall₂ (fun choice family => choice ∈ family)
      leftChoices leftFamilies) :
    ∃ rightChoices,
      List.Forall₂ (fun choice family => choice ∈ family)
          rightChoices rightFamilies ∧
        List.Forall₂ ObservedTypeAlphaRel leftChoices rightChoices := by
  induction families generalizing leftChoices with
  | nil =>
      cases choices
      exact ⟨[], .nil, .nil⟩
  | @cons leftFamily rightFamily leftFamilies rightFamilies
      headAlpha tailAlpha inductionHypothesis =>
      cases choices with
      | @cons leftChoice _ leftChoices _ leftMember tailChoices =>
          have existsRight : ∃ rightChoice,
              rightChoice ∈ rightFamily ∧
                ObservedTypeAlphaRel leftChoice rightChoice := by
            induction headAlpha with
            | nil => simp at leftMember
            | @cons leftHead rightHead leftTail rightTail
                headRelation tailRelation headInduction =>
                rcases List.mem_cons.mp leftMember with rfl | tailMember
                · exact ⟨rightHead, by simp, headRelation⟩
                · obtain ⟨rightChoice, rightMember, relation⟩ :=
                    headInduction tailMember
                  exact ⟨rightChoice, by simp [rightMember], relation⟩
          obtain ⟨rightHead, rightHeadMember, headRelation⟩ := existsRight
          obtain ⟨rightTail, rightTailMembers, tailRelations⟩ :=
            inductionHypothesis tailChoices
          exact ⟨rightHead :: rightTail,
            .cons rightHeadMember rightTailMembers,
            .cons headRelation tailRelations⟩

/-- Two lawful package preparations yield aligned concrete choices related by
one global permutation that fixes the shared function signature.  The single
permutation, rather than one renaming per argument, is load-bearing for
dependent arrows: repeated variables across formal and return positions keep
one identity. -/
theorem preparedApplicationChoicePermutation
    {oracle : TypePreparationOracle}
    (functional : TypePreparationFunctional oracle)
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env)
    {leftForbidden rightForbidden : List String}
    {candidate : Atom} {formals arguments : List Atom}
    {leftCandidates rightCandidates : List (List Atom)}
    (leftPrepared : PreparedArgumentPackageCandidates oracle space
      leftForbidden formals arguments leftCandidates)
    (rightPrepared : PreparedArgumentPackageCandidates oracle space
      rightForbidden formals arguments rightCandidates)
    (leftSeparated : FreshFamiliesSeparated [candidate]
      leftCandidates.flatten)
    (rightSeparated : FreshFamiliesSeparated [candidate]
      rightCandidates.flatten)
    {leftChoices : List Atom}
    (leftChoiceMembers : List.Forall₂
      (fun choice family => choice ∈ family)
      leftChoices leftCandidates) :
    ∃ rightChoices, ∃ permutation : Equiv.Perm String,
      List.Forall₂ (fun choice family => choice ∈ family)
          rightChoices rightCandidates ∧
        renameTypeVars permutation candidate = candidate ∧
        rightChoices = leftChoices.map (renameTypeVars permutation) := by
  have familyAlpha := leftPrepared.alpha_unique functional index rightPrepared
  obtain ⟨rightChoices, rightChoiceMembers, choiceAlpha⟩ :=
    candidateChoices_alpha familyAlpha leftChoiceMembers
  have leftChoicesSubset : ∀ atom, atom ∈ leftChoices →
      atom ∈ leftCandidates.flatten := by
    intro atom atomMember
    obtain ⟨family, familyMember, member⟩ :=
      alignedChoice_exists_family leftChoiceMembers atomMember
    exact List.mem_flatten.mpr ⟨family, familyMember, member⟩
  have rightChoicesSubset : ∀ atom, atom ∈ rightChoices →
      atom ∈ rightCandidates.flatten := by
    intro atom atomMember
    obtain ⟨family, familyMember, member⟩ :=
      alignedChoice_exists_family rightChoiceMembers atomMember
    exact List.mem_flatten.mpr ⟨family, familyMember, member⟩
  have leftStatic : PreparedArgumentCandidateLists formals []
      leftCandidates (leftCandidates.map toLeaTTaAtoms) := by
    rcases leftPrepared with ⟨_, _, _, _, _, static⟩
    exact static
  have rightStatic : PreparedArgumentCandidateLists formals []
      rightCandidates (rightCandidates.map toLeaTTaAtoms) := by
    rcases rightPrepared with ⟨_, _, _, _, _, static⟩
    exact static
  have leftPairwise : (candidate :: leftChoices).Pairwise
      (fun left right => FreshFamiliesSeparated [left] [right]) := by
    rw [List.pairwise_cons]
    constructor
    · intro choice choiceMember
      exact leftSeparated.mono
        (fun atom member => member)
        (fun atom member => by
          have equation : atom = choice := List.mem_singleton.mp member
          subst atom
          exact leftChoicesSubset choice choiceMember)
    · exact chosenCandidates_pairwiseSeparated
        leftChoiceMembers leftStatic.families
  have rightPairwise : (candidate :: rightChoices).Pairwise
      (fun left right => FreshFamiliesSeparated [left] [right]) := by
    rw [List.pairwise_cons]
    constructor
    · intro choice choiceMember
      exact rightSeparated.mono
        (fun atom member => member)
        (fun atom member => by
          have equation : atom = choice := List.mem_singleton.mp member
          subst atom
          exact rightChoicesSubset choice choiceMember)
    · exact chosenCandidates_pairwiseSeparated
        rightChoiceMembers rightStatic.families
  have alphaWithCandidate : List.Forall₂ ObservedTypeAlphaRel
      (candidate :: leftChoices) (candidate :: rightChoices) :=
    .cons (ObservedTypeAlphaRel.refl candidate) choiceAlpha
  have hScoped : ScopedObservedTypeListAlphaRel
      (candidate :: leftChoices) (candidate :: rightChoices) :=
    ScopedObservedTypeListAlphaRel.of_forall₂_pairwiseSeparated
      alphaWithCandidate
      leftPairwise rightPairwise
  obtain ⟨permutation, equation⟩ := hScoped.exists_permutation
  have parts := List.cons.inj equation
  exact ⟨rightChoices, permutation, rightChoiceMembers,
    parts.1.symm, parts.2⟩

/-- Forgetting package lookup and preparation evidence retains the static
freshness contract consumed by the independent branch scan. -/
theorem PreparedArgumentPackageCandidates.staticPrepared
    {oracle : TypePreparationOracle} {space : Space}
    {forbidden : List String} {formals arguments : List Atom}
    {candidateLists : List (List Atom)}
    (prepared : PreparedArgumentPackageCandidates oracle space forbidden
      formals arguments candidateLists) :
    PreparedArgumentCandidateLists formals [] candidateLists
      (candidateLists.map toLeaTTaAtoms) := by
  obtain ⟨_, _, _, _, _, staticPrepared⟩ := prepared
  exact staticPrepared

/-- The abstract preparation service supplies the position-indexed family
relation expected by the two-history recursive correspondence.  Position is
scan structure, not part of package lookup. -/
theorem PreparedArgumentPackageCandidates.positionedFamilyRel
    {oracle : TypePreparationOracle} {space : Space}
    {forbidden : List String} {formals arguments : List Atom}
    {candidateLists : List (List Atom)}
    (prepared : PreparedArgumentPackageCandidates oracle space forbidden
      formals arguments candidateLists) (position : Nat) :
    PositionedArgumentCandidateFamiliesRel
      (fun _ => PreparedArgumentCandidateFamilyRel oracle space forbidden)
      position arguments candidateLists :=
  PositionedArgumentCandidateFamiliesRel.ofForall₂ prepared.familyRel
    position

/-- Implementation-side refinement of one prepared static family with the
position at which the realization generator produced it.  The preparation
relation remains the semantic content; generated-at provenance is consumed
only by the concrete correspondence proof. -/
def RealizedPreparedArgumentCandidateFamilyRel
    (oracle : TypePreparationOracle) (space : Space)
    (forbidden : List String) (position : Nat)
    (argument : Atom) (candidates : List Atom) : Prop :=
  PreparedArgumentCandidateFamilyRel oracle space forbidden
      argument candidates ∧
    CandidateFamilyGeneratedAt position candidates

/-- Concrete realization invariant for the two independently generated
candidate histories.  It records only positional provenance; the semantic
scan and its recursive state remain generator-free. -/
def GeneratedTwoHistoryScanInvariant : TwoHistoryScanStateInvariant :=
  fun position staticHistory runtimeHistory _ _ =>
    CandidateGenerationHistory position staticHistory ∧
      CandidateGenerationHistory position runtimeHistory

/-- The empty histories establish the concrete realization invariant. -/
theorem generatedTwoHistoryScanInvariant_empty :
    GeneratedTwoHistoryScanInvariant 0 [] [] [] Metta.Bindings.empty :=
  ⟨CandidateGenerationHistory.nil, CandidateGenerationHistory.nil⟩

/-- Empty histories establish the generator invariant independently of the
caller presentation and runtime bindings. -/
theorem generatedTwoHistoryScanInvariant_initial
    (presentation : TypeSubst) (runtimeBindings : Metta.Bindings) :
    GeneratedTwoHistoryScanInvariant 0 [] [] presentation runtimeBindings :=
  ⟨CandidateGenerationHistory.nil, CandidateGenerationHistory.nil⟩

/-- An exact caller presentation/runtime state initializes the two-history
scan when its presentation support is public at the application boundary. -/
theorem twoHistoryScopedTypePresentationSimulationState_initial
    (theoryScope publicScope : List String)
    {presentation : TypeSubst} {incoming : Bindings}
    {runtimeBindings : Metta.Bindings}
    (state : TypePresentationSimulationState presentation incoming
      runtimeBindings)
    (supported : ∀ name,
      name ∈ specBindingVars (⟨presentation, []⟩ : Bindings) →
        name ∈ publicScope) :
    TwoHistoryScopedTypePresentationSimulationState theoryScope publicScope
      0 [] [] presentation presentation runtimeBindings := by
  exact ⟨rfl, rfl, .nil, state.normal, incoming, state,
    TypePresentationTheoryEquivAt.refl theoryScope presentation,
    (by
      intro name member
      exact List.mem_append_left _ (supported name member)),
    (by
      intro name member
      exact List.mem_append_left _ (supported name member))⟩

/-- Selecting one generated sibling on each side preserves positional
provenance. -/
theorem GeneratedTwoHistoryScanInvariant.snoc
    {position : Nat} {staticHistory runtimeHistory : List Atom}
    {specPresentation : TypeSubst} {runtimeBindings : Metta.Bindings}
    {specCandidate runtimeCandidate : Atom}
    (invariant : GeneratedTwoHistoryScanInvariant position staticHistory
      runtimeHistory specPresentation runtimeBindings)
    (specGenerated : CandidateGeneratedAt position specCandidate)
    (runtimeGenerated : CandidateGeneratedAt position runtimeCandidate) :
    GeneratedTwoHistoryScanInvariant (position + 1)
      (staticHistory ++ [specCandidate])
      (runtimeHistory ++ [runtimeCandidate]) specPresentation
        runtimeBindings :=
  ⟨CandidateGenerationHistory.snoc invariant.1 specGenerated,
    CandidateGenerationHistory.snoc invariant.2 runtimeGenerated⟩

/-- Decode one exact runtime candidate-family equation into its native
generator presentation.  The type-environment index supplies the only
round-trip fact needed at this executable boundary. -/
theorem RuntimeArgumentCandidatesAt.decode_generated
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env)
    {world : Metta.Minimal.World} {runtimeFormals : List Metta.Atom}
    {boundaryScope : List String} {position : Nat}
    {runtimeBindings : Metta.Bindings} {argument : Atom}
    {remaining : List Atom} {runtimeCandidates : List Metta.Atom}
    {prepared : Atom}
    (preparationEquation :
      Metta.Minimal.typePrep world (toLeaTTaAtom argument) =
        toLeaTTaAtom prepared)
    (candidatesAt : RuntimeArgumentCandidatesAt env world runtimeFormals
      boundaryScope position runtimeBindings argument remaining
        runtimeCandidates) :
    ∃ rawCandidates runtimeAvoid decodedRuntimeCandidates,
      rawCandidates = fromLeaTTaAtoms
        (Metta.Minimal.getTypes env (toLeaTTaAtom prepared)) ∧
      runtimeAvoid = boundaryScope ++ Metta.Minimal.typeInferenceAvoid env
        (.expr (toLeaTTaAtom argument :: toLeaTTaAtoms remaining))
        (runtimeFormals ++
          Metta.Minimal.getTypes env (toLeaTTaAtom prepared)) ++
          runtimeBindings.vars ∧
      decodedRuntimeCandidates = freshenCandidateFamily runtimeAvoid
        position rawCandidates ∧
      toLeaTTaAtoms decodedRuntimeCandidates = runtimeCandidates ∧
      CandidateFamilyGeneratedAt position decodedRuntimeCandidates := by
  unfold RuntimeArgumentCandidatesAt at candidatesAt
  dsimp only at candidatesAt
  rw [preparationEquation] at candidatesAt
  let rawCandidates := fromLeaTTaAtoms
    (Metta.Minimal.getTypes env (toLeaTTaAtom prepared))
  let runtimeAvoid := boundaryScope ++ Metta.Minimal.typeInferenceAvoid env
    (.expr (toLeaTTaAtom argument :: toLeaTTaAtoms remaining))
    (runtimeFormals ++ Metta.Minimal.getTypes env
      (toLeaTTaAtom prepared)) ++ runtimeBindings.vars
  let decodedRuntimeCandidates := freshenCandidateFamily runtimeAvoid
    position rawCandidates
  refine ⟨rawCandidates, runtimeAvoid, decodedRuntimeCandidates,
    rfl, rfl, rfl, ?_, ?_⟩
  · calc
      toLeaTTaAtoms decodedRuntimeCandidates =
          (toLeaTTaAtoms rawCandidates).map
            (Metta.Minimal.freshenTypeCandidate runtimeAvoid position) :=
        toLeaTTaAtoms_freshenCandidateFamily runtimeAvoid position
          rawCandidates
      _ = (Metta.Minimal.getTypes env
            (toLeaTTaAtom prepared)).map
              (Metta.Minimal.freshenTypeCandidate runtimeAvoid position) := by
        rw [runtimeOperatorTypes_roundtrip index prepared]
      _ = runtimeCandidates := candidatesAt
  · exact freshenCandidateFamily_generatedAt runtimeAvoid position
      rawCandidates

/-- Functional abstract preparation and an exact type-environment index
realize node-local candidate coverage.  The producer retains both generated
families long enough to prove the opaque invariant extension; no generator
evidence escapes into the recursive scan. -/
theorem realizedPreparedArgumentCandidateCoverage
    {oracle : TypePreparationOracle} {space : Space}
    {env : Metta.Minimal.MinEnv} {world : Metta.Minimal.World}
    {forbidden boundaryScope theoryScope publicScope : List String}
    {runtimeFormals : List Metta.Atom} {terminalSignature : Atom}
    (functional : TypePreparationFunctional oracle)
    (index : TypeEnvironmentRel space env)
    (realization : TypePreparationRuntimeRealization oracle space world)
    (signatureGenerated : CandidateGeneratedAt runtimeFormals.length
      terminalSignature)
    (publicStaticProtected : ∀ name, name ∈ publicScope →
      name ∈ forbidden ∨ name ∈ TypeSubst.typeVars terminalSignature)
    (theoryStaticProtected : ∀ name, name ∈ theoryScope →
      name ∈ forbidden ∨ name ∈ TypeSubst.typeVars terminalSignature)
    (publicRuntimeCovered : ∀ name, name ∈ publicScope →
      (name ∈ boundaryScope ∨
        name ∈ runtimeFormals.flatMap Metta.Atom.vars ∨
        name ∈ env.atoms.flatMap Metta.Atom.vars) ∨
          name ∈ TypeSubst.typeVars terminalSignature)
    (theoryRuntimeCovered : ∀ name, name ∈ theoryScope →
      (name ∈ boundaryScope ∨
        name ∈ runtimeFormals.flatMap Metta.Atom.vars ∨
        name ∈ env.atoms.flatMap Metta.Atom.vars) ∨
          name ∈ TypeSubst.typeVars terminalSignature) :
    TwoHistoryNodeLocalArgumentCandidateCoverage
      (RealizedPreparedArgumentCandidateFamilyRel oracle space forbidden)
      GeneratedTwoHistoryScanInvariant env world runtimeFormals boundaryScope
        theoryScope publicScope := by
  intro formal argument remaining position staticHistory runtimeHistory
    specIncoming branchIncoming runtimeIncoming specCandidates
    runtimeCandidates state family invariant positionBound formalRuntimeMember
    specCandidatesAvoidFormal candidatesAt
  rcases family with ⟨preparedFamily, specCandidatesGenerated⟩
  rcases preparedFamily with ⟨staticPrepared, packages,
    staticPreparation, packageRelation, staticVariants⟩
  obtain ⟨runtimePrepared, runtimePreparation,
      runtimePreparationEquation⟩ := realization argument
  have preparedEquation := functional space argument staticPrepared
    runtimePrepared staticPreparation runtimePreparation
  subst runtimePrepared
  obtain ⟨rawCandidates, runtimeAvoid, decodedRuntimeCandidates,
      rawCandidatesEquation, runtimeAvoidEquation, decodedEquation,
      runtimeCandidatesEquation, runtimeCandidatesGenerated⟩ :=
    RuntimeArgumentCandidatesAt.decode_generated index
      runtimePreparationEquation candidatesAt
  have packageToRaw : List.Forall₂ ObservedTypeAlphaRel
      (observedTypes packages) rawCandidates := by
    rw [rawCandidatesEquation]
    exact runtimeTypePackages_complete index packageRelation
  have rawToStatic : List.Forall₂
      (TypeCandidateAlphaVariantRel forbidden)
      rawCandidates specCandidates :=
    observedAlphaList_alphaVariants_transport
      (observedAlphaList_symm packageToRaw) staticVariants
  have runtimeVariants : List.Forall₂
      (TypeCandidateAlphaVariantRel runtimeAvoid)
      rawCandidates decodedRuntimeCandidates := by
    rw [decodedEquation]
    exact freshenCandidateFamily_alphaVariants runtimeAvoid position
      rawCandidates
  have staticAvoidsForbidden : AtomsAvoid specCandidates forbidden :=
    candidateFamilyAlphaVariants_avoids staticVariants
  have generatedFamilyAvoidsSignature
      {candidates : List Atom}
      (generated : CandidateFamilyGeneratedAt position candidates) :
      AtomsAvoid candidates (TypeSubst.typeVars terminalSignature) := by
    intro name candidateOccurrence signatureOccurrence
    obtain ⟨candidate, candidateMember, candidateVariable⟩ :=
      exists_mem_of_mem_typeVarsList candidateOccurrence
    have disjoint := CandidateGeneratedAt.varsDisjoint_of_position_ne
      (Nat.ne_of_gt positionBound) signatureGenerated
        (generated candidate candidateMember)
    apply disjoint name
    · rw [LeaTTaTypePresentationExactConformance.toLeaTTaAtom_vars_eq_typeVars]
      exact signatureOccurrence
    · rw [LeaTTaTypePresentationExactConformance.toLeaTTaAtom_vars_eq_typeVars]
      exact candidateVariable
  have staticAvoidsSignature : AtomsAvoid specCandidates
      (TypeSubst.typeVars terminalSignature) :=
    generatedFamilyAvoidsSignature specCandidatesGenerated
  have staticAvoidsPublic : AtomsAvoid specCandidates publicScope := by
    intro name occurrence publicMember
    rcases publicStaticProtected name publicMember with
      forbiddenMember | signatureMember
    · exact staticAvoidsForbidden name occurrence forbiddenMember
    · exact staticAvoidsSignature name occurrence signatureMember
  have staticAvoidsTheory : AtomsAvoid specCandidates theoryScope := by
    intro name occurrence theoryMember
    rcases theoryStaticProtected name theoryMember with
      forbiddenMember | signatureMember
    · exact staticAvoidsForbidden name occurrence forbiddenMember
    · exact staticAvoidsSignature name occurrence signatureMember
  have staticAvoidsNode := state.currentFamily_avoids_nodeScope
    invariant.1 invariant.2 specCandidatesGenerated staticAvoidsPublic
      staticAvoidsTheory specCandidatesAvoidFormal
  have runtimeAvoidsAll : AtomsAvoid decodedRuntimeCandidates runtimeAvoid := by
    rw [decodedEquation]
    exact freshenCandidateFamily_avoids runtimeAvoid position rawCandidates
  have runtimeCoveredInAvoid : ∀ name,
      (name ∈ boundaryScope ∨
        name ∈ runtimeFormals.flatMap Metta.Atom.vars ∨
        name ∈ env.atoms.flatMap Metta.Atom.vars) →
      name ∈ runtimeAvoid := by
    intro name covered
    rcases covered with boundaryMember | formalMember | environmentMember
    · simp [runtimeAvoidEquation, Metta.Minimal.typeInferenceAvoid,
        boundaryMember]
    · simp [runtimeAvoidEquation, Metta.Minimal.typeInferenceAvoid,
        List.flatMap_append, formalMember]
    · simp [runtimeAvoidEquation, Metta.Minimal.typeInferenceAvoid,
        environmentMember]
  have runtimeAvoidsSignature : AtomsAvoid decodedRuntimeCandidates
      (TypeSubst.typeVars terminalSignature) :=
    generatedFamilyAvoidsSignature runtimeCandidatesGenerated
  have runtimeAvoidsPublic : AtomsAvoid decodedRuntimeCandidates
      publicScope := by
    intro name occurrence publicMember
    rcases publicRuntimeCovered name publicMember with
      covered | signatureMember
    · exact runtimeAvoidsAll name occurrence
        (runtimeCoveredInAvoid name covered)
    · exact runtimeAvoidsSignature name occurrence signatureMember
  have runtimeAvoidsTheory : AtomsAvoid decodedRuntimeCandidates
      theoryScope := by
    intro name occurrence theoryMember
    rcases theoryRuntimeCovered name theoryMember with
      covered | signatureMember
    · exact runtimeAvoidsAll name occurrence
        (runtimeCoveredInAvoid name covered)
    · exact runtimeAvoidsSignature name occurrence signatureMember
  have runtimeAvoidsFormal : AtomsAvoid decodedRuntimeCandidates
      (TypeSubst.typeVars formal) := by
    intro name occurrence formalOccurrence
    apply runtimeAvoidsAll name occurrence
    have formalRuntimeOccurrence :
        name ∈ (toLeaTTaAtom formal).vars := by
      rw [LeaTTaTypePresentationExactConformance.toLeaTTaAtom_vars_eq_typeVars]
      exact formalOccurrence
    have runtimeFormalOccurrence :
        name ∈ runtimeFormals.flatMap Metta.Atom.vars :=
      List.mem_flatMap.mpr ⟨toLeaTTaAtom formal, formalRuntimeMember,
        formalRuntimeOccurrence⟩
    exact runtimeCoveredInAvoid name
      (Or.inr (Or.inl runtimeFormalOccurrence))
  have runtimeAvoidsNode := state.currentFamily_avoids_nodeScope
    invariant.1 invariant.2 runtimeCandidatesGenerated
      runtimeAvoidsPublic runtimeAvoidsTheory runtimeAvoidsFormal
  have staticScoped : List.Forall₂
      (TypeCandidateAlphaVariantRel
        (twoHistoryCandidateNodeScope specIncoming branchIncoming
          theoryScope formal)) rawCandidates specCandidates :=
    candidateFamilyAlphaVariants_changeScope rawToStatic staticAvoidsNode
  have runtimeScoped : List.Forall₂
      (TypeCandidateAlphaVariantRel
        (twoHistoryCandidateNodeScope specIncoming branchIncoming
          theoryScope formal)) rawCandidates decodedRuntimeCandidates :=
    candidateFamilyAlphaVariants_changeScope runtimeVariants
      runtimeAvoidsNode
  refine ⟨decodedRuntimeCandidates, runtimeCandidatesEquation,
    privateCandidateFamilyAlpha_of_variants staticScoped runtimeScoped, ?_⟩
  intro specCandidate runtimeCandidate _formal specOutput branchOutput
    runtimeOutput specMember runtimeMember _alpha _matched _nextState
  exact invariant.snoc
    (specCandidatesGenerated specCandidate specMember)
    (runtimeCandidatesGenerated runtimeCandidate runtimeMember)

/-- Generator-chosen package preparation exposes the exact positioned
family provenance needed by the branch-local runtime realization. -/
theorem RuntimePreparedArgumentPackageCandidates.positionedFamilyRel
    {oracle : TypePreparationOracle} {space : Space}
    {env : Metta.Minimal.MinEnv} {world : Metta.Minimal.World}
    {forbidden : List String} {formals arguments : List Atom}
    {candidateLists : List (List Atom)}
    (runtimePrepared : RuntimePreparedArgumentPackageCandidates oracle space
      env world forbidden formals arguments candidateLists) :
    PositionedArgumentCandidateFamiliesRel
      (RealizedPreparedArgumentCandidateFamilyRel oracle space forbidden)
      0 arguments candidateLists := by
  obtain ⟨rawFamilies, families, rfl⟩ := runtimePrepared
  have prepared :=
    preparedArgumentPackageCandidates_of_runtimeFamilies
      (forbidden := forbidden) (formals := formals) families
  exact (prepared.positionedFamilyRel 0).and
    (freshenArgumentCandidateFamilies_positionedGenerated families
      (forbidden ++ TypeSubst.typeVarsList formals) 0)

/-- A prepared family whose global forbidden scope covers an initial
presentation also satisfies the exact static preparation contract from that
presentation. -/
theorem PreparedArgumentPackageCandidates.staticPreparedFrom
    {oracle : TypePreparationOracle} {space : Space}
    {forbidden : List String} {formals arguments : List Atom}
    {candidateLists : List (List Atom)}
    (prepared : PreparedArgumentPackageCandidates oracle space forbidden
      formals arguments candidateLists)
    (initial : TypeSubst)
    (covered : ∀ name,
      name ∈ specBindingVars (⟨initial, []⟩ : Bindings) →
        name ∈ forbidden) :
    PreparedArgumentCandidateLists formals initial candidateLists
      (candidateLists.map toLeaTTaAtoms) := by
  have base := prepared.staticPrepared
  refine
    { link := base.link
      avoidFormals := base.avoidFormals
      avoidInitial := ?_
      families := base.families }
  constructor
  · intro name keyMember candidateOccurrence
    obtain ⟨entry, entryMember, keyEquation⟩ :=
      List.mem_map.mp keyMember
    rcases entry with ⟨key, value⟩
    simp only at keyEquation
    subst key
    exact prepared.candidatesAvoid name candidateOccurrence (covered name (by
      simp [specBindingVars]
      exact ⟨name, value, entryMember, Or.inl rfl⟩))
  · intro key value assignmentMember name valueMember candidateOccurrence
    exact prepared.candidatesAvoid name candidateOccurrence (covered name (by
      simp [specBindingVars]
      exact ⟨key, value, assignmentMember, Or.inr valueMember⟩))

/-- Generic assembly of abstract package preparation with the executable
branch scan.  Concrete freshening enters only through the node-local coverage
hypothesis; neither the specification scan nor this theorem mentions a name
generator. -/
theorem preparedArgumentBranches_runtimeConformance
    {oracle : TypePreparationOracle} {space : Space}
    {invariant : TwoHistoryScanStateInvariant}
    {env : Metta.Minimal.MinEnv} {world : Metta.Minimal.World}
    {forbidden boundaryScope theoryScope publicScope : List String}
    {formals arguments : List Atom}
    {candidateLists : List (List Atom)}
    {specIncoming branchIncoming : TypeSubst}
    {runtimeIncoming : Metta.Bindings}
    (prepared : PreparedArgumentPackageCandidates oracle space forbidden
      formals arguments candidateLists)
    (coverage : TwoHistoryNodeLocalArgumentCandidateCoverage
      (fun _ => PreparedArgumentCandidateFamilyRel oracle space forbidden)
      invariant env world (toLeaTTaAtoms formals) boundaryScope theoryScope
        publicScope)
    (initialState : TwoHistoryScopedTypePresentationSimulationState theoryScope
      publicScope 0 [] [] specIncoming branchIncoming runtimeIncoming)
    (initialInvariant : invariant 0 [] [] specIncoming runtimeIncoming)
    (initialStaticCovered : ∀ name,
      name ∈ specBindingVars (⟨specIncoming, []⟩ : Bindings) →
        name ∈ forbidden)
    (formalsObserved : ∀ name,
      name ∈ TypeSubst.typeVarsList formals → name ∈ theoryScope)
    (formalsPublic : ∀ name,
      name ∈ TypeSubst.typeVarsList formals → name ∈ publicScope) :
    ∃ specOutcome,
      ArgumentCandidateListsBranchScanRel formals candidateLists 0 specIncoming
          specOutcome ∧
        ScopedArgumentBranchOutcomeRuntimeRel theoryScope specOutcome
          (Metta.Minimal.typeCheckArgsBranchesScoped env world
            (toLeaTTaAtoms formals) boundaryScope 0 runtimeIncoming
              (toLeaTTaAtoms arguments)) := by
  have runtimeScan := typeCheckArgsBranchesScoped_runtimeBranchLocal env world
    (toLeaTTaAtoms formals) boundaryScope arguments formals 0
      runtimeIncoming (by simp)
  exact runtimeBranchLocalArgumentScan_twoHistory coverage
    formalsObserved formalsPublic initialState initialInvariant (by simp)
    (prepared.staticPreparedFrom specIncoming initialStaticCovered)
    (prepared.positionedFamilyRel 0) runtimeScan

/-- Concrete package preparation composes with branch-local scan
conformance once the implementation proves node-local alpha coverage.  This
is the final repair-independent boundary: repair #17 affects only the
coverage theorem, not the scan or package semantics assembled here. -/
theorem runtimePreparedArgumentBranches_runtimeConformance
    {oracle : TypePreparationOracle} {space : Space}
    {invariant : TwoHistoryScanStateInvariant}
    {env : Metta.Minimal.MinEnv} {world : Metta.Minimal.World}
    {forbidden boundaryScope theoryScope publicScope : List String}
    {formals arguments : List Atom}
    {candidateLists : List (List Atom)}
    {specIncoming branchIncoming : TypeSubst}
    {runtimeIncoming : Metta.Bindings}
    (runtimePrepared : RuntimePreparedArgumentPackageCandidates oracle space
      env world forbidden formals arguments candidateLists)
    (coverage : TwoHistoryNodeLocalArgumentCandidateCoverage
      (RealizedPreparedArgumentCandidateFamilyRel oracle space forbidden)
      invariant env world (toLeaTTaAtoms formals) boundaryScope theoryScope
        publicScope)
    (initialState : TwoHistoryScopedTypePresentationSimulationState theoryScope
      publicScope 0 [] [] specIncoming branchIncoming runtimeIncoming)
    (initialInvariant : invariant 0 [] [] specIncoming runtimeIncoming)
    (initialStaticCovered : ∀ name,
      name ∈ specBindingVars (⟨specIncoming, []⟩ : Bindings) →
        name ∈ forbidden)
    (formalsObserved : ∀ name,
      name ∈ TypeSubst.typeVarsList formals → name ∈ theoryScope)
    (formalsPublic : ∀ name,
      name ∈ TypeSubst.typeVarsList formals → name ∈ publicScope) :
    ∃ specOutcome,
      ArgumentCandidateListsBranchScanRel formals candidateLists 0 specIncoming
          specOutcome ∧
        ScopedArgumentBranchOutcomeRuntimeRel theoryScope specOutcome
          (Metta.Minimal.typeCheckArgsBranchesScoped env world
            (toLeaTTaAtoms formals) boundaryScope 0 runtimeIncoming
              (toLeaTTaAtoms arguments)) := by
  have runtimeScan := typeCheckArgsBranchesScoped_runtimeBranchLocal env world
    (toLeaTTaAtoms formals) boundaryScope arguments formals 0
      runtimeIncoming (by simp)
  exact runtimeBranchLocalArgumentScan_twoHistory coverage
    formalsObserved formalsPublic initialState initialInvariant (by simp)
    (runtimePrepared.prepared.staticPreparedFrom specIncoming
      initialStaticCovered)
    runtimePrepared.positionedFamilyRel runtimeScan

/-- The exact concrete package preparation realizes the complete
branch-valued argument scan under the smallest explicit scope inclusions.
Preparation functionality and the type-environment index are laws of the
instance, not fields smuggled into the semantic candidate carrier. -/
theorem runtimePreparedArgumentBranches_exactConformance
    {oracle : TypePreparationOracle} {space : Space}
    {env : Metta.Minimal.MinEnv} {world : Metta.Minimal.World}
    {forbidden boundaryScope theoryScope publicScope : List String}
    {formals arguments : List Atom} {terminalSignature : Atom}
    {candidateLists : List (List Atom)}
    {specIncoming branchIncoming : TypeSubst}
    {runtimeIncoming : Metta.Bindings}
    (functional : TypePreparationFunctional oracle)
    (index : TypeEnvironmentRel space env)
    (realization : TypePreparationRuntimeRealization oracle space world)
    (runtimePrepared : RuntimePreparedArgumentPackageCandidates oracle space
      env world forbidden formals arguments candidateLists)
    (initialState : TwoHistoryScopedTypePresentationSimulationState theoryScope
      publicScope 0 [] [] specIncoming branchIncoming runtimeIncoming)
    (initialStaticCovered : ∀ name,
      name ∈ specBindingVars (⟨specIncoming, []⟩ : Bindings) →
        name ∈ forbidden)
    (signatureGenerated : CandidateGeneratedAt formals.length
      terminalSignature)
    (publicStaticProtected : ∀ name, name ∈ publicScope →
      name ∈ forbidden ∨ name ∈ TypeSubst.typeVars terminalSignature)
    (theoryStaticProtected : ∀ name, name ∈ theoryScope →
      name ∈ forbidden ∨ name ∈ TypeSubst.typeVars terminalSignature)
    (publicRuntimeCovered : ∀ name, name ∈ publicScope →
      (name ∈ boundaryScope ∨
        name ∈ (toLeaTTaAtoms formals).flatMap Metta.Atom.vars ∨
        name ∈ env.atoms.flatMap Metta.Atom.vars) ∨
          name ∈ TypeSubst.typeVars terminalSignature)
    (theoryRuntimeCovered : ∀ name, name ∈ theoryScope →
      (name ∈ boundaryScope ∨
        name ∈ (toLeaTTaAtoms formals).flatMap Metta.Atom.vars ∨
        name ∈ env.atoms.flatMap Metta.Atom.vars) ∨
          name ∈ TypeSubst.typeVars terminalSignature)
    (formalsObserved : ∀ name,
      name ∈ TypeSubst.typeVarsList formals → name ∈ theoryScope)
    (formalsPublic : ∀ name,
      name ∈ TypeSubst.typeVarsList formals → name ∈ publicScope) :
    ∃ specOutcome,
      ArgumentCandidateListsBranchScanRel formals candidateLists 0 specIncoming
          specOutcome ∧
        ScopedArgumentBranchOutcomeRuntimeRel theoryScope specOutcome
          (Metta.Minimal.typeCheckArgsBranchesScoped env world
            (toLeaTTaAtoms formals) boundaryScope 0 runtimeIncoming
              (toLeaTTaAtoms arguments)) := by
  have signatureGeneratedRuntime : CandidateGeneratedAt
      (toLeaTTaAtoms formals).length terminalSignature := by
    simpa [toLeaTTaAtoms_eq_map] using signatureGenerated
  exact runtimePreparedArgumentBranches_runtimeConformance runtimePrepared
    (realizedPreparedArgumentCandidateCoverage functional index realization
      signatureGeneratedRuntime publicStaticProtected theoryStaticProtected
        publicRuntimeCovered theoryRuntimeCovered)
    initialState
    (generatedTwoHistoryScanInvariant_initial specIncoming runtimeIncoming)
    initialStaticCovered formalsObserved formalsPublic

/-! ## Localized-signature observation composition -/

/-- Field-wise diagnostic alpha from a raw spec signature to its localized
presentation composes with the existing raw-spec/runtime diagnostic bridge.
Position remains literal. -/
theorem argumentTypeDiagnosticAlpha_composeRuntime
    {raw localized : ArgumentTypeDiagnostic}
    {runtime : Metta.Minimal.TypeCheckArgsError}
    (localization : ArgumentTypeDiagnosticAlphaRel raw localized)
    (runtimeRel : ArgumentTypeDiagnosticRuntimeRel raw runtime) :
    ArgumentTypeDiagnosticRuntimeRel localized runtime := by
  exact
    { position := localization.position.symm.trans runtimeRel.position
      expected :=
        Spec.Type.Presentation.ScopeObservation.ObservedTypeAlphaRel.trans
          localization.expected.symm runtimeRel.expected
      actual :=
        Spec.Type.Presentation.ScopeObservation.ObservedTypeAlphaRel.trans
          localization.actual.symm runtimeRel.actual }

/-- Return diagnostics compose across signature localization without
weakening the literal boundary-expected field. -/
theorem expectedReturnDiagnosticAlpha_composeRuntime
    {raw localized : ExpectedReturnDiagnostic}
    {runtime : Metta.Minimal.ExpectedFunctionTypeError}
    (localization : ExpectedReturnDiagnosticAlphaRel raw localized)
    (runtimeRel : ExpectedReturnDiagnosticRuntimeRel raw runtime) :
    ExpectedReturnDiagnosticRuntimeRel localized runtime := by
  rcases localization with ⟨expected, actual⟩
  cases runtimeRel with
  | badReturn runtimeActual =>
      cases expected
      exact .badReturn
        (Spec.Type.Presentation.ScopeObservation.ObservedTypeAlphaRel.trans
          actual.symm runtimeActual)

/-- Compose two pointwise relations that share their source list. -/
private theorem forall₂_fork_comp
    {α β γ : Type*} {R : α → β → Prop} {S : α → γ → Prop}
    {T : β → γ → Prop} {left : List α} {middle : List β} {right : List γ}
    (compose : ∀ {a b c}, R a b → S a c → T b c)
    (leftMiddle : List.Forall₂ R left middle)
    (leftRight : List.Forall₂ S left right) :
    List.Forall₂ T middle right := by
  induction leftMiddle generalizing right with
  | nil =>
      cases leftRight
      exact .nil
  | cons head tail inductionHypothesis =>
      cases leftRight with
      | cons rightHead rightTail =>
          exact .cons (compose head rightHead)
            (inductionHypothesis rightTail)

/-- Option companion of `forall₂_fork_comp`. -/
private theorem optionRel_fork_comp
    {α β γ : Type*} {R : α → β → Prop} {S : α → γ → Prop}
    {T : β → γ → Prop} {left : Option α} {middle : Option β}
    {right : Option γ}
    (compose : ∀ {a b c}, R a b → S a c → T b c)
    (leftMiddle : Option.Rel R left middle)
    (leftRight : Option.Rel S left right) :
    Option.Rel T middle right := by
  cases leftMiddle with
  | none =>
      cases leftRight
      exact .none
  | some middleRel =>
      cases leftRight with
      | some rightRel => exact .some (compose middleRel rightRel)

/-- Map the witness relation of two aligned options without inspecting the
options themselves. -/
private theorem optionRel_map
    {α β : Type*} {R S : α → β → Prop}
    (map : ∀ {a b}, R a b → S a b) :
    ∀ {left : Option α} {right : Option β},
      Option.Rel R left right → Option.Rel S left right
  | none, none, .none => .none
  | some _, some _, .some relation => .some (map relation)

/-- Pointwise localized presentation states compose with pointwise scoped
runtime states. -/
theorem localizedStates_compose_scopedRuntime
    {permutation : Equiv.Perm String} {scope : List String}
    {raw localized : List TypeSubst}
    {runtime : List Metta.Bindings}
    (scopeFixed : ∀ name, name ∈ scope → permutation name = name)
    (localization : TypePresentationPermutationStates permutation
      raw localized)
    (runtimeStates : ScopedTypePresentationSimulationStates scope
      raw runtime) :
    ScopedTypePresentationSimulationStates scope localized runtime := by
  induction localization generalizing runtime with
  | nil =>
      cases runtimeStates
      exact .nil
  | cons head tail inductionHypothesis =>
      cases runtimeStates with
      | cons runtimeHead runtimeTail =>
          exact .cons
            (head.composeScopedRuntime scopeFixed runtimeHead)
            (inductionHypothesis runtimeTail)

/-- The complete localized argument outcome composes with the raw-signature
runtime correspondence; order and multiplicity are inherited from the two
pointwise relations. -/
theorem localizedArgumentOutcome_compose_scopedRuntime
    {permutation : Equiv.Perm String} {scope : List String}
    {raw localized : ArgumentCandidateListsBranchOutcome}
    {runtime : Metta.Minimal.TypeCheckArgsBranchResult}
    (scopeFixed : ∀ name, name ∈ scope → permutation name = name)
    (localization : ArgumentCandidateListsBranchOutcomePermutationRel
      permutation raw localized)
    (runtimeRel : ScopedArgumentBranchOutcomeRuntimeRel
      scope raw runtime) :
    ScopedArgumentBranchOutcomeRuntimeRel scope localized runtime := by
  refine ⟨localizedStates_compose_scopedRuntime scopeFixed
      localization.successes runtimeRel.successes, ?_⟩
  exact forall₂_fork_comp
    (R := ArgumentTypeDiagnosticAlphaRel)
    (S := ArgumentTypeDiagnosticRuntimeRel)
    (T := ArgumentTypeDiagnosticRuntimeRel)
    (fun localizedAlpha rawRuntime =>
      argumentTypeDiagnosticAlpha_composeRuntime
        localizedAlpha rawRuntime)
    localization.errors runtimeRel.errors

/-- The complete localized return-gate outcome composes with the raw
runtime correspondence, retaining first-success commit and diagnostic order. -/
theorem localizedReturnOutcome_compose_scopedRuntime
    {permutation : Equiv.Perm String} {scope : List String}
    {raw localized : ExpectedReturnBranchOutcome}
    {runtime : Metta.Minimal.ExpectedReturnBranchScanResult}
    (scopeFixed : ∀ name, name ∈ scope → permutation name = name)
    (localization : ExpectedReturnBranchOutcomePermutationRel
      permutation raw localized)
    (runtimeRel : ScopedExpectedReturnBranchOutcomeRuntimeRel
      scope raw runtime) :
    ScopedExpectedReturnBranchOutcomeRuntimeRel scope localized runtime := by
  constructor
  · exact optionRel_fork_comp
      (fun localizedState rawRuntime =>
        localizedState.composeScopedRuntime scopeFixed rawRuntime)
      localization.selected runtimeRel.selected
  · exact forall₂_fork_comp
      (R := ExpectedReturnDiagnosticAlphaRel)
      (S := ExpectedReturnDiagnosticRuntimeRel)
      (T := ExpectedReturnDiagnosticRuntimeRel)
      (fun localizedAlpha rawRuntime =>
        expectedReturnDiagnosticAlpha_composeRuntime
          localizedAlpha rawRuntime)
      localization.errors runtimeRel.errors

/-- One localized selected presentation retains the raw-signature
presentation from which it was transported.  The same permutation therefore
relates both the selected arrow and the binding theory observed by the
runtime; these two witnesses must not be re-existentialized independently. -/
def CoherentLocalizedTypePresentationSimulationState
    (permutation : Equiv.Perm String) (theoryScope scope : List String)
    (localized : TypeSubst) (runtime : Metta.Bindings) : Prop :=
  (∀ name, name ∈ scope → name ∈ theoryScope) ∧
    ∃ raw,
      TypePresentationPermutationState permutation raw localized ∧
      ScopedTypePresentationSimulationState theoryScope raw runtime

/-- The expected-return boundary keeps signature localization correlated
with the selected runtime binding state.  Diagnostics retain their existing
fieldwise observation relation and exact order. -/
structure CoherentLocalizedExpectedReturnRuntimeRel
    (permutation : Equiv.Perm String) (theoryScope scope : List String)
    (localized : ExpectedReturnBranchOutcome)
    (runtime : Metta.Minimal.ExpectedReturnBranchScanResult) : Prop where
  selected : Option.Rel
    (CoherentLocalizedTypePresentationSimulationState
      permutation theoryScope scope)
    localized.selected runtime.selected
  errors : List.Forall₂ ExpectedReturnDiagnosticRuntimeRel
    localized.errors runtime.errors

/-- Forgetting the shared signature permutation recovers the ordinary scoped
return-outcome boundary. -/
theorem CoherentLocalizedExpectedReturnRuntimeRel.toScoped
    {permutation : Equiv.Perm String} {theoryScope scope : List String}
    {localized : ExpectedReturnBranchOutcome}
    {runtime : Metta.Minimal.ExpectedReturnBranchScanResult}
    (scopeFixed : ∀ name, name ∈ scope → permutation name = name)
    (relation : CoherentLocalizedExpectedReturnRuntimeRel permutation
      theoryScope scope localized runtime) :
    ScopedExpectedReturnBranchOutcomeRuntimeRel scope localized runtime := by
  constructor
  · exact optionRel_map
      (fun state => by
        rcases state with
          ⟨scopeInTheory, raw, localization, rawRuntime⟩
        exact localization.composeScopedRuntime scopeFixed
          (rawRuntime.mono scopeInTheory))
      relation.selected
  · exact relation.errors

/-- Compose localization with raw runtime correspondence while retaining the
shared presentation permutation as producer evidence. -/
theorem localizedReturnOutcome_compose_coherentRuntime
    {permutation : Equiv.Perm String}
    {theoryScope scope : List String}
    {raw localized : ExpectedReturnBranchOutcome}
    {runtime : Metta.Minimal.ExpectedReturnBranchScanResult}
    (scopeInTheory : ∀ name, name ∈ scope → name ∈ theoryScope)
    (localization : ExpectedReturnBranchOutcomePermutationRel
      permutation raw localized)
    (runtimeRel : ScopedExpectedReturnBranchOutcomeRuntimeRel
      theoryScope raw runtime) :
    CoherentLocalizedExpectedReturnRuntimeRel permutation theoryScope scope
      localized runtime := by
  constructor
  · exact optionRel_fork_comp
      (fun {rawPresentation localizedPresentation runtimeBindings}
          (localizedState : TypePresentationPermutationState permutation
            rawPresentation localizedPresentation)
          (rawRuntime : ScopedTypePresentationSimulationState theoryScope
            rawPresentation runtimeBindings) =>
        ⟨scopeInTheory, rawPresentation, localizedState, rawRuntime⟩)
      localization.selected runtimeRel.selected
  · exact forall₂_fork_comp
      (R := ExpectedReturnDiagnosticAlphaRel)
      (S := ExpectedReturnDiagnosticRuntimeRel)
      (T := ExpectedReturnDiagnosticRuntimeRel)
      (fun localizedAlpha rawRuntime =>
        expectedReturnDiagnosticAlpha_composeRuntime
          localizedAlpha rawRuntime)
      localization.errors runtimeRel.errors

/-- Complete prepared argument applicability and the expected-return gate
transport together under one coherent signature permutation.

The runtime is proved once against its own fresh signature spelling.  The
specification then localizes the complete arrow in one post-hoc transport:
argument branches, failed actuals, return failures, and first-success commit
all retain their list structure.  No second scan induction is introduced. -/
theorem localizedPreparedApplicationBranches_exactConformance
    {oracle : TypePreparationOracle} {space : Space}
    {env : Metta.Minimal.MinEnv} {world : Metta.Minimal.World}
    {forbidden boundaryScope rawTheoryScope publicScope
      observationScope : List String}
    {rawFormals arguments : List Atom}
    {rawReturn expected terminalSignature : Atom}
    {candidateLists : List (List Atom)} {permutation : Equiv.Perm String}
    {initialPresentation branchPresentation : TypeSubst}
    {runtimeInitial : Metta.Bindings}
    (functional : TypePreparationFunctional oracle)
    (index : TypeEnvironmentRel space env)
    (realization : TypePreparationRuntimeRealization oracle space world)
    (runtimePrepared : RuntimePreparedArgumentPackageCandidates oracle space
      env world forbidden rawFormals arguments candidateLists)
    (initialState : TwoHistoryScopedTypePresentationSimulationState
      rawTheoryScope publicScope 0 [] [] initialPresentation
        branchPresentation runtimeInitial)
    (initialStaticCovered : ∀ name,
      name ∈ specBindingVars (⟨initialPresentation, []⟩ : Bindings) →
        name ∈ forbidden)
    (initialPermutation : TypePresentationPermutationState permutation
      initialPresentation initialPresentation)
    (signatureGenerated : CandidateGeneratedAt rawFormals.length
      terminalSignature)
    (publicStaticProtected : ∀ name, name ∈ publicScope →
      name ∈ forbidden ∨ name ∈ TypeSubst.typeVars terminalSignature)
    (theoryStaticProtected : ∀ name, name ∈ rawTheoryScope →
      name ∈ forbidden ∨ name ∈ TypeSubst.typeVars terminalSignature)
    (publicRuntimeCovered : ∀ name, name ∈ publicScope →
      (name ∈ boundaryScope ∨
        name ∈ (toLeaTTaAtoms rawFormals).flatMap Metta.Atom.vars ∨
        name ∈ env.atoms.flatMap Metta.Atom.vars) ∨
          name ∈ TypeSubst.typeVars terminalSignature)
    (theoryRuntimeCovered : ∀ name, name ∈ rawTheoryScope →
      (name ∈ boundaryScope ∨
        name ∈ (toLeaTTaAtoms rawFormals).flatMap Metta.Atom.vars ∨
        name ∈ env.atoms.flatMap Metta.Atom.vars) ∨
          name ∈ TypeSubst.typeVars terminalSignature)
    (formalsObserved : ∀ name,
      name ∈ TypeSubst.typeVarsList rawFormals → name ∈ rawTheoryScope)
    (formalsPublic : ∀ name,
      name ∈ TypeSubst.typeVarsList rawFormals → name ∈ publicScope)
    (observationInTheory : ∀ name, name ∈ observationScope →
      name ∈ rawTheoryScope)
    (scopeFixed : ∀ name, name ∈ observationScope →
      permutation name = name)
    (candidatesFixed : ∀ candidate ∈ candidateLists.flatten,
      renameTypeVars permutation candidate = candidate)
    (expectedFixed : renameTypeVars permutation expected = expected)
    (returnConstraintObserved : ∀ name,
      name ∈ TypeSubst.typeVars expected ++ TypeSubst.typeVars rawReturn →
        name ∈ rawTheoryScope)
    (returnObserved : ∀ name,
      name ∈ TypeSubst.typeVars rawReturn → name ∈ rawTheoryScope)
    (returnDisjoint : VarsDisjoint expected rawReturn) :
    ∃ localizedArguments localizedReturn,
      ArgumentCandidateListsBranchScanRel
          (rawFormals.map (renameTypeVars permutation)) candidateLists 0
          initialPresentation
          localizedArguments ∧
        ScopedArgumentBranchOutcomeRuntimeRel observationScope localizedArguments
          (Metta.Minimal.typeCheckArgsBranchesScoped env world
            (toLeaTTaAtoms rawFormals) boundaryScope 0 runtimeInitial
              (toLeaTTaAtoms arguments)) ∧
        ExpectedReturnBranchScanRel expected
          (renameTypeVars permutation rawReturn)
          localizedArguments.successes localizedReturn ∧
        CoherentLocalizedExpectedReturnRuntimeRel permutation rawTheoryScope
          observationScope localizedReturn
          (Metta.Minimal.scanExpectedReturnBranches
            (toLeaTTaAtom expected) (toLeaTTaAtom rawReturn)
            (Metta.Minimal.typeCheckArgsBranchesScoped env world
              (toLeaTTaAtoms rawFormals) boundaryScope 0 runtimeInitial
                (toLeaTTaAtoms arguments)).successes) := by
  obtain ⟨rawArguments, rawArgumentScan, rawArgumentRuntime⟩ :=
    runtimePreparedArgumentBranches_exactConformance functional index
      realization runtimePrepared initialState initialStaticCovered
      signatureGenerated publicStaticProtected
      theoryStaticProtected publicRuntimeCovered theoryRuntimeCovered
      formalsObserved formalsPublic
  obtain ⟨localizedArguments, localizedArgumentScan,
      argumentPermutation⟩ :=
    ArgumentCandidateListsBranchScanRel.map_formals_permutation
      initialPermutation
      candidatesFixed rawArgumentScan
  have rawArgumentRuntimeObserved : ScopedArgumentBranchOutcomeRuntimeRel
      observationScope rawArguments
      (Metta.Minimal.typeCheckArgsBranchesScoped env world
        (toLeaTTaAtoms rawFormals) boundaryScope 0 runtimeInitial
          (toLeaTTaAtoms arguments)) :=
    { successes := scopedTypePresentationSimulationStates_mono
        rawArgumentRuntime.successes observationInTheory
      errors := rawArgumentRuntime.errors }
  have localizedArgumentRuntime : ScopedArgumentBranchOutcomeRuntimeRel
      observationScope localizedArguments
      (Metta.Minimal.typeCheckArgsBranchesScoped env world
        (toLeaTTaAtoms rawFormals) boundaryScope 0 runtimeInitial
          (toLeaTTaAtoms arguments)) :=
    localizedArgumentOutcome_compose_scopedRuntime scopeFixed
      argumentPermutation rawArgumentRuntimeObserved
  obtain ⟨rawReturnOutcome, rawReturnScan, rawReturnRuntime⟩ :=
    scanExpectedReturnBranches_presentation_scoped rawTheoryScope expected
      rawReturn returnConstraintObserved returnObserved returnDisjoint
      rawArgumentRuntime.successes
  obtain ⟨localizedReturn, localizedReturnScan, returnPermutation⟩ :=
    ExpectedReturnBranchScanRel.map_return_permutation expectedFixed
      argumentPermutation.successes rawReturnScan
  have localizedReturnRuntime : CoherentLocalizedExpectedReturnRuntimeRel
      permutation rawTheoryScope observationScope localizedReturn
      (Metta.Minimal.scanExpectedReturnBranches
        (toLeaTTaAtom expected) (toLeaTTaAtom rawReturn)
        (Metta.Minimal.typeCheckArgsBranchesScoped env world
          (toLeaTTaAtoms rawFormals) boundaryScope 0 runtimeInitial
            (toLeaTTaAtoms arguments)).successes) :=
    localizedReturnOutcome_compose_coherentRuntime
      observationInTheory returnPermutation rawReturnRuntime
  exact ⟨localizedArguments, localizedReturn, localizedArgumentScan,
    localizedArgumentRuntime, localizedReturnScan, localizedReturnRuntime⟩

/-! ## Exact candidate applicability -/

/-- Embed one argument mismatch into the evaluator error vocabulary. -/
def argumentTypeDiagnosticAtom (expression : Atom)
    (diagnostic : ArgumentTypeDiagnostic) : Atom :=
  mkError expression
    (.badArgType diagnostic.position diagnostic.expected diagnostic.actual)

/-- Embed one expected-return mismatch into the evaluator error vocabulary. -/
def expectedReturnDiagnosticAtom (expression : Atom)
    (diagnostic : ExpectedReturnDiagnostic) : Atom :=
  mkError expression (.badType diagnostic.expected diagnostic.actual)

/-- The complete ordered error ledger for one function candidate.  Later
argument blocks already precede earlier blocks in `argumentOutcome`; return
errors are appended afterward, matching the published traversal. -/
def candidateApplicabilityErrors (expression : Atom)
    (argumentOutcome : ArgumentCandidateListsBranchOutcome)
    (returnOutcome : ExpectedReturnBranchOutcome) : List Atom :=
  argumentOutcome.errors.map (argumentTypeDiagnosticAtom expression) ++
    returnOutcome.errors.map (expectedReturnDiagnosticAtom expression)

/-- An arity-aligned exact prepared traversal that finds no applicable return
branch emits a nonempty observable error ledger.  Nonempty exact type lookup
rules out the otherwise-degenerate empty-family case. -/
theorem candidateApplicabilityErrors_nonempty
    {oracle : TypePreparationOracle} {space : Space}
    {expression expectedType : Atom} {bindings : Bindings}
    {returnType : Atom} {arguments argumentTypes : List Atom}
    {candidateLists : List (List Atom)}
    {initialPresentation : TypeSubst}
    {argumentOutcome : ArgumentCandidateListsBranchOutcome}
    {returnOutcome : ExpectedReturnBranchOutcome}
    (arity : arguments.length = argumentTypes.length)
    (prepared : PreparedArgumentPackageCandidates oracle space
      (typeServicePrivateAvoid space expression expectedType bindings)
      argumentTypes arguments candidateLists)
    (argumentScan : ArgumentCandidateListsBranchScanRel argumentTypes
      candidateLists 0 initialPresentation argumentOutcome)
    (returnScan : ExpectedReturnBranchScanRel expectedType returnType
      argumentOutcome.successes returnOutcome)
    (notSelected : returnOutcome.selected = none) :
    candidateApplicabilityErrors expression argumentOutcome returnOutcome ≠ [] := by
  have lengthEquation : argumentTypes.length = candidateLists.length := by
    calc
      argumentTypes.length = arguments.length := arity.symm
      _ = candidateLists.length := prepared.arguments_length.symm
  rcases argumentScan.successes_or_errors_nonempty lengthEquation
      prepared.familiesNonempty with argumentsSucceed | argumentErrors
  · have returnErrors := returnScan.errors_nonempty_of_selected_none
        argumentsSucceed notSelected
    obtain ⟨diagnostic, diagnosticMember⟩ :=
      List.exists_mem_of_ne_nil returnOutcome.errors returnErrors
    intro empty
    have member : expectedReturnDiagnosticAtom expression diagnostic ∈
        candidateApplicabilityErrors expression argumentOutcome returnOutcome := by
      unfold candidateApplicabilityErrors
      exact List.mem_append.mpr (Or.inr
        (List.mem_map.mpr ⟨diagnostic, diagnosticMember, rfl⟩))
    rw [empty] at member
    simp at member
  · obtain ⟨diagnostic, diagnosticMember⟩ :=
      List.exists_mem_of_ne_nil argumentOutcome.errors argumentErrors
    intro empty
    have member : argumentTypeDiagnosticAtom expression diagnostic ∈
        candidateApplicabilityErrors expression argumentOutcome returnOutcome := by
      unfold candidateApplicabilityErrors
      exact List.mem_append.mpr (Or.inl
        (List.mem_map.mpr ⟨diagnostic, diagnosticMember, rfl⟩))
    rw [empty] at member
    simp at member

/-- Field-wise correspondence between one specification error atom and one
runtime expected-selection error.  Arity and the public fields are literal;
only private type spellings inside the existing diagnostic relations are
quotiented by alpha-renaming. -/
inductive CandidateErrorAtomRuntimeRel (expression : Atom) :
    Atom → Metta.Minimal.ExpectedFunctionTypeError → Prop where
  | incorrectArity :
      CandidateErrorAtomRuntimeRel expression
        (mkError expression .incorrectNumberOfArguments)
        (.ordinary .incorrectArity)
  | badArgument {diagnostic : ArgumentTypeDiagnostic}
      {runtime : Metta.Minimal.TypeCheckArgsError} :
      ArgumentTypeDiagnosticRuntimeRel diagnostic runtime →
      CandidateErrorAtomRuntimeRel expression
        (argumentTypeDiagnosticAtom expression diagnostic)
        (.ordinary runtime.toFunctionTypeError)
  | badReturn {diagnostic : ExpectedReturnDiagnostic}
      {runtime : Metta.Minimal.ExpectedFunctionTypeError} :
      ExpectedReturnDiagnosticRuntimeRel diagnostic runtime →
      CandidateErrorAtomRuntimeRel expression
        (expectedReturnDiagnosticAtom expression diagnostic) runtime

/-- One candidate's complete error block, preserving order and multiplicity. -/
def CandidateErrorBlockRuntimeRel (expression : Atom)
    (specErrors : List Atom)
    (runtimeErrors : List Metta.Minimal.ExpectedFunctionTypeError) : Prop :=
  List.Forall₂ (CandidateErrorAtomRuntimeRel expression)
    specErrors runtimeErrors

/-- Pointwise candidate-error blocks.  This is the classification-layer
carrier: block boundaries remain explicit until the outcome readout flattens
them. -/
def CandidateErrorBlocksRuntimeRel (expression : Atom)
    (specBlocks : List (List Atom))
    (runtimeBlocks : List (List Metta.Minimal.ExpectedFunctionTypeError)) :
    Prop :=
  List.Forall₂ (CandidateErrorBlockRuntimeRel expression)
    specBlocks runtimeBlocks

/-- Flattening pointwise candidate blocks preserves the exact atom-level
error correspondence and source order. -/
theorem CandidateErrorBlocksRuntimeRel.flatten
    {expression : Atom}
    {specBlocks : List (List Atom)}
    {runtimeBlocks : List (List Metta.Minimal.ExpectedFunctionTypeError)}
    (blocks : CandidateErrorBlocksRuntimeRel expression
      specBlocks runtimeBlocks) :
    CandidateErrorBlockRuntimeRel expression
      specBlocks.flatten runtimeBlocks.flatten := by
  induction blocks with
  | nil => exact .nil
  | cons head _ inductionHypothesis =>
      exact List.rel_append head inductionHypothesis

/-- Mapping the ordered argument ledger into evaluator errors preserves the
field-wise diagnostic correspondence. -/
theorem argumentErrorAtoms_runtime
    (expression : Atom)
    {spec : List ArgumentTypeDiagnostic}
    {runtime : List Metta.Minimal.TypeCheckArgsError}
    (correspondence : List.Forall₂ ArgumentTypeDiagnosticRuntimeRel
      spec runtime) :
    CandidateErrorBlockRuntimeRel expression
      (spec.map (argumentTypeDiagnosticAtom expression))
      (runtime.map fun diagnostic =>
        .ordinary diagnostic.toFunctionTypeError) := by
  induction correspondence with
  | nil => exact .nil
  | cons head _ inductionHypothesis =>
      exact .cons (.badArgument head) inductionHypothesis

/-- Mapping the ordered return ledger into evaluator errors preserves the
field-wise diagnostic correspondence. -/
theorem returnErrorAtoms_runtime
    (expression : Atom)
    {spec : List ExpectedReturnDiagnostic}
    {runtime : List Metta.Minimal.ExpectedFunctionTypeError}
    (correspondence : List.Forall₂ ExpectedReturnDiagnosticRuntimeRel
      spec runtime) :
    CandidateErrorBlockRuntimeRel expression
      (spec.map (expectedReturnDiagnosticAtom expression)) runtime := by
  induction correspondence with
  | nil => exact .nil
  | cons head _ inductionHypothesis =>
      exact .cons (.badReturn head) inductionHypothesis

/-- The complete argument-then-return ledger is one ordered runtime failure
block.  Candidate-level scan composition may flatten blocks later, but this
boundary never forgets their grouping. -/
theorem candidateApplicabilityErrors_runtime
    (expression : Atom)
    {scope : List String}
    {specArguments : ArgumentCandidateListsBranchOutcome}
    {runtimeArguments : Metta.Minimal.TypeCheckArgsBranchResult}
    {specReturn : ExpectedReturnBranchOutcome}
    {runtimeReturn : Metta.Minimal.ExpectedReturnBranchScanResult}
    (arguments : ScopedArgumentBranchOutcomeRuntimeRel
      scope specArguments runtimeArguments)
    (returnGate : ScopedExpectedReturnBranchOutcomeRuntimeRel
      scope specReturn runtimeReturn) :
    CandidateErrorBlockRuntimeRel expression
      (candidateApplicabilityErrors expression specArguments specReturn)
      ((runtimeArguments.errors.map fun diagnostic =>
          .ordinary diagnostic.toFunctionTypeError) ++ runtimeReturn.errors) := by
  exact List.rel_append
    (argumentErrorAtoms_runtime expression arguments.errors)
    (returnErrorAtoms_runtime expression returnGate.errors)

/-! ## Runtime scan outcome boundary -/

/-- One expected-aware candidate step is completely characterized by its
singleton scan.  A selected candidate commits immediately; a tuple-eligible
non-function marks the tail; a failed function prepends its complete error
block.  This is the sole downstream interface to the executable scan
recursion. -/
theorem scanFunctionTypeCandidatesForExpected_cons
    (env : Metta.Minimal.MinEnv) (world : Metta.Minimal.World)
    (expression : Metta.Atom) (arguments : List Metta.Atom)
    (expected : Metta.Atom) (allowExtraArguments : Bool)
    (candidate : Metta.Atom) (candidates : List Metta.Atom) :
    Metta.Minimal.scanFunctionTypeCandidatesForExpected env world expression
        arguments expected allowExtraArguments (candidate :: candidates) =
      match Metta.Minimal.scanFunctionTypeCandidatesForExpected env world
          expression arguments expected allowExtraArguments [candidate] with
      | .selected function => .selected function
      | .exhausted errors tupleEligible =>
          if tupleEligible then
            Metta.Minimal.ExpectedFunctionTypeScanOutcome.markTupleEligible
              (Metta.Minimal.scanFunctionTypeCandidatesForExpected env world
                expression arguments expected allowExtraArguments candidates)
          else
            Metta.Minimal.ExpectedFunctionTypeScanOutcome.prependErrors errors
              (Metta.Minimal.scanFunctionTypeCandidatesForExpected env world
                expression arguments expected allowExtraArguments candidates) := by
  simp only [Metta.Minimal.scanFunctionTypeCandidatesForExpected]
  split <;>
    simp_all [Metta.Minimal.ExpectedFunctionTypeScanOutcome.markTupleEligible,
      Metta.Minimal.ExpectedFunctionTypeScanOutcome.prependErrors,
      Metta.Minimal.ExpectedFunctionTypeScanOutcome.prependError]
  all_goals
    split <;>
      try simp_all
  all_goals
    split <;>
      try simp_all
  all_goals
    split <;>
      try simp_all

/-- Seeded expected-aware scanning has the same head/tail assembly law as
the compatibility scan.  The initial binding is threaded unchanged into the
singleton and tail calls. -/
theorem scanFunctionTypeCandidatesForExpectedFrom_cons
    (env : Metta.Minimal.MinEnv) (world : Metta.Minimal.World)
    (expression : Metta.Atom) (arguments : List Metta.Atom)
    (expected : Metta.Atom) (allowExtraArguments : Bool)
    (initial : Metta.Bindings)
    (candidate : Metta.Atom) (candidates : List Metta.Atom) :
    Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom env world expression
        arguments expected allowExtraArguments initial (candidate :: candidates) =
      match Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom env world
          expression arguments expected allowExtraArguments initial [candidate] with
      | .selected function => .selected function
      | .exhausted errors tupleEligible =>
          if tupleEligible then
            Metta.Minimal.ExpectedFunctionTypeScanOutcome.markTupleEligible
              (Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom env world
                expression arguments expected allowExtraArguments initial candidates)
          else
            Metta.Minimal.ExpectedFunctionTypeScanOutcome.prependErrors errors
              (Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom env world
                expression arguments expected allowExtraArguments initial candidates) := by
  simp only [Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom]
  split <;>
    simp_all [Metta.Minimal.ExpectedFunctionTypeScanOutcome.markTupleEligible,
      Metta.Minimal.ExpectedFunctionTypeScanOutcome.prependErrors,
      Metta.Minimal.ExpectedFunctionTypeScanOutcome.prependError]
  all_goals
    split <;>
      try simp_all
  all_goals
    split <;>
      try simp_all
  all_goals
    split <;>
      try simp_all

/-- A successful singleton runtime scan retains the candidate literally in
the selected record.  This is the executable projection needed by aligned
evaluator realizations; it does not inspect or compare binding payloads. -/
theorem scanFunctionTypeCandidatesForExpectedFrom_singleton_functionType
    {env : Metta.Minimal.MinEnv} {world : Metta.Minimal.World}
    {expression : Metta.Atom} {arguments : List Metta.Atom}
    {expected : Metta.Atom} {allowExtraArguments : Bool}
    {initial : Metta.Bindings} {candidate : Metta.Atom}
    {runtime : Metta.Minimal.SelectedFunctionType}
    (scan : Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom env world
      expression arguments expected allowExtraArguments initial [candidate] =
        .selected runtime) :
    runtime.functionType = candidate := by
  cases candidate with
  | sym name =>
      simp [Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom,
        Metta.Minimal.ExpectedFunctionTypeScanOutcome.markTupleEligible] at scan
  | var name =>
      simp [Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom,
        Metta.Minimal.ExpectedFunctionTypeScanOutcome.markTupleEligible] at scan
  | gnd value =>
      simp [Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom,
        Metta.Minimal.ExpectedFunctionTypeScanOutcome.markTupleEligible] at scan
  | expr atoms =>
      cases atoms with
      | nil =>
          simp [Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom,
            Metta.Minimal.ExpectedFunctionTypeScanOutcome.markTupleEligible]
            at scan
      | cons head signature =>
          cases head with
          | sym name =>
              by_cases arrow : name = "->"
              · subst name
                simp only [Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom]
                  at scan
                split at scan
                · simp [
                    Metta.Minimal.ExpectedFunctionTypeScanOutcome.markTupleEligible]
                    at scan
                · split at scan
                  · split at scan
                    · cases scan
                      rfl
                    · simp [
                        Metta.Minimal.ExpectedFunctionTypeScanOutcome.prependErrors]
                        at scan
                  · simp [
                      Metta.Minimal.ExpectedFunctionTypeScanOutcome.prependError]
                      at scan
              · simp [Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom,
                  Metta.Minimal.ExpectedFunctionTypeScanOutcome.markTupleEligible,
                  arrow] at scan
          | var name =>
              simp [Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom,
                Metta.Minimal.ExpectedFunctionTypeScanOutcome.markTupleEligible]
                at scan
          | gnd value =>
              simp [Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom,
                Metta.Minimal.ExpectedFunctionTypeScanOutcome.markTupleEligible]
                at scan
          | expr nested =>
              simp [Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom,
                Metta.Minimal.ExpectedFunctionTypeScanOutcome.markTupleEligible]
                at scan

/-- One selected specification policy and one runtime selection have a single
coherent alpha witness for the complete arrow.  The runtime shape equation
ties its separately stored formal and return fields back to that same arrow;
dependent occurrences therefore cannot be renamed independently. -/
structure SelectedTypePolicyRuntimeRel
    (policy : SelectedTypePolicy)
    (runtime : Metta.Minimal.SelectedFunctionType) : Prop where
  arrow : ObservedTypeAlphaRel policy.functionType
    (fromLeaTTaAtom runtime.functionType)
  runtimeShape :
    fromLeaTTaAtom runtime.functionType =
      .expression (.symbol "->" ::
        (fromLeaTTaAtoms runtime.argumentTypes ++
          [fromLeaTTaAtom runtime.returnType]))

/-- Literal agreement of the selected specification policy with the decoded
runtime record.  This stronger evaluator-facing boundary is available only
when both scans consume the same fresh candidate; the general type-service
boundary above correctly retains merely coherent alpha agreement. -/
structure SelectedTypePolicyRuntimeExactRel
    (policy : SelectedTypePolicy)
    (runtime : Metta.Minimal.SelectedFunctionType) : Prop where
  functionType :
    policy.functionType = fromLeaTTaAtom runtime.functionType
  runtimeFunctionType :
    toLeaTTaAtom policy.functionType = runtime.functionType
  argumentTypes :
    policy.argumentTypes = fromLeaTTaAtoms runtime.argumentTypes
  returnType :
    policy.returnType = fromLeaTTaAtom runtime.returnType

/-- A selected arrow and its output presentation share one producer-owned
localization witness.  This is stronger than pairing an arrow-level alpha
fact with an unrelated scoped presentation: the same permutation acts on
the complete arrow and on the selected finite binding theory. -/
def SelectedTypePolicyPresentationRuntimeRel
    (scope : List String) (policy : SelectedTypePolicy)
    (presentation : TypeSubst)
    (runtime : Metta.Minimal.SelectedFunctionType) : Prop :=
  ∃ permutation : Equiv.Perm String, ∃ theoryScope : List String,
    ∃ rawPresentation : TypeSubst,
    FunctionTypeRel
        (fromLeaTTaAtom runtime.functionType)
        (fromLeaTTaAtoms runtime.argumentTypes)
        (fromLeaTTaAtom runtime.returnType) ∧
      policy.functionType =
        renameTypeVars permutation (fromLeaTTaAtom runtime.functionType) ∧
      policy.argumentTypes =
        (fromLeaTTaAtoms runtime.argumentTypes).map
          (renameTypeVars permutation) ∧
      policy.returnType =
        renameTypeVars permutation (fromLeaTTaAtom runtime.returnType) ∧
      (∀ name, name ∈ scope → permutation name = name) ∧
      (∀ name, name ∈ scope → name ∈ theoryScope) ∧
      (∀ name,
        name ∈ TypeSubst.typeVars (fromLeaTTaAtom runtime.functionType) →
          name ∈ theoryScope) ∧
      TypePresentationPermutationState permutation rawPresentation
        presentation ∧
      ScopedTypePresentationSimulationState theoryScope rawPresentation
        runtime.typeBindings

/-- The coherent carrier projects to the established selected-policy
boundary without choosing a second arrow permutation. -/
theorem SelectedTypePolicyPresentationRuntimeRel.policyRuntime
    {scope : List String} {policy : SelectedTypePolicy}
    {presentation : TypeSubst}
    {runtime : Metta.Minimal.SelectedFunctionType}
    (relation : SelectedTypePolicyPresentationRuntimeRel scope policy
      presentation runtime) :
    SelectedTypePolicyRuntimeRel policy runtime := by
  rcases relation with
    ⟨permutation, _theoryScope, _rawPresentation, runtimeFunction,
      functionType, _argumentTypes, _returnType, _scopeFixed,
      _scopeInTheory, _functionTypeObserved, _presentation,
      _runtimePresentation⟩
  constructor
  · rw [functionType]
    exact ⟨fromLeaTTaAtom runtime.functionType,
      ⟨permutation, permutation.injective, rfl⟩,
      TypeVariableRenamingOf.refl _⟩
  · exact runtimeFunction

/-- The same coherent carrier projects to the localized scoped presentation
state used by existing type-service consumers. -/
theorem SelectedTypePolicyPresentationRuntimeRel.scopedPresentation
    {scope : List String} {policy : SelectedTypePolicy}
    {presentation : TypeSubst}
    {runtime : Metta.Minimal.SelectedFunctionType}
    (relation : SelectedTypePolicyPresentationRuntimeRel scope policy
      presentation runtime) :
    ScopedTypePresentationSimulationState scope presentation
      runtime.typeBindings := by
  rcases relation with
    ⟨permutation, theoryScope, rawPresentation, _runtimeFunction,
      _functionType, _argumentTypes, _returnType, scopeFixed,
      scopeInTheory, _functionTypeObserved, presentationState,
      runtimePresentation⟩
  exact presentationState.composeScopedRuntime scopeFixed
    (runtimePresentation.mono scopeInTheory)

/-- The selected producer retains scoped equivalence at every variable of
the complete runtime arrow.  This stronger projection is consumed by the
operator-head cast; ordinary evaluator observations use
`scopedPresentation`. -/
theorem SelectedTypePolicyPresentationRuntimeRel.functionTypePresentation
    {scope : List String} {policy : SelectedTypePolicy}
    {presentation : TypeSubst}
    {runtime : Metta.Minimal.SelectedFunctionType}
    (relation : SelectedTypePolicyPresentationRuntimeRel scope policy
      presentation runtime) :
    ∃ theoryScope rawPresentation permutation,
      (∀ name, name ∈ scope → name ∈ theoryScope) ∧
      (∀ name,
        name ∈ TypeSubst.typeVars (fromLeaTTaAtom runtime.functionType) →
          name ∈ theoryScope) ∧
      TypePresentationPermutationState permutation rawPresentation
        presentation ∧
      ScopedTypePresentationSimulationState theoryScope rawPresentation
        runtime.typeBindings := by
  rcases relation with
    ⟨permutation, theoryScope, rawPresentation, _runtimeFunction,
      _functionType, _argumentTypes, _returnType, _scopeFixed,
      scopeInTheory, functionTypeObserved, presentationState,
      runtimePresentation⟩
  exact ⟨theoryScope, rawPresentation, permutation, scopeInTheory,
    functionTypeObserved, presentationState, runtimePresentation⟩

/-- Coherent selected-policy evidence weakens with its public observation
scope while retaining the same signature and presentation permutation. -/
theorem SelectedTypePolicyPresentationRuntimeRel.mono
    {large small : List String} {policy : SelectedTypePolicy}
    {presentation : TypeSubst}
    {runtime : Metta.Minimal.SelectedFunctionType}
    (relation : SelectedTypePolicyPresentationRuntimeRel large policy
      presentation runtime)
    (subset : ∀ name, name ∈ small → name ∈ large) :
    SelectedTypePolicyPresentationRuntimeRel small policy presentation
      runtime := by
  rcases relation with
    ⟨permutation, theoryScope, rawPresentation, runtimeFunction,
      functionType, argumentTypes, returnType, scopeFixed, scopeInTheory,
      functionTypeObserved, presentationState, runtimePresentation⟩
  exact ⟨permutation, theoryScope, rawPresentation, runtimeFunction,
    functionType,
    argumentTypes, returnType,
    fun name member => scopeFixed name (subset name member),
    fun name member => scopeInTheory name (subset name member),
    functionTypeObserved, presentationState, runtimePresentation⟩

/-- The runtime fields of a coherent selected policy form one spec function
type. -/
theorem SelectedTypePolicyRuntimeRel.runtimeFunctionType
    {policy : SelectedTypePolicy}
    {runtime : Metta.Minimal.SelectedFunctionType}
    (relation : SelectedTypePolicyRuntimeRel policy runtime) :
    FunctionTypeRel (fromLeaTTaAtom runtime.functionType)
      (fromLeaTTaAtoms runtime.argumentTypes)
      (fromLeaTTaAtom runtime.returnType) := by
  simpa [FunctionTypeRel] using relation.runtimeShape

/-- One arrow-level alpha witness determines both selected projections.
The argument and return equations are consequences of the same finite
permutation, so a dependent variable cannot be renamed inconsistently
between the domain and codomain. -/
theorem SelectedTypePolicyRuntimeRel.exists_coherent_permutation
    {policy : SelectedTypePolicy}
    {runtime : Metta.Minimal.SelectedFunctionType}
    (relation : SelectedTypePolicyRuntimeRel policy runtime) :
    ∃ permutation : Equiv.Perm String,
      fromLeaTTaAtom runtime.functionType =
          renameTypeVars permutation policy.functionType ∧
        fromLeaTTaAtoms runtime.argumentTypes =
          policy.argumentTypes.map (renameTypeVars permutation) ∧
        fromLeaTTaAtom runtime.returnType =
          renameTypeVars permutation policy.returnType := by
  obtain ⟨permutation, functionEquation⟩ :=
    Spec.Type.Presentation.ScopeObservation.ObservedTypeAlphaRel.exists_permutation
      relation.arrow
  have renamedFunction :
      FunctionTypeRel
        (renameTypeVars permutation policy.functionType)
        (fromLeaTTaAtoms runtime.argumentTypes)
        (fromLeaTTaAtom runtime.returnType) := by
    rw [← functionEquation]
    exact relation.runtimeFunctionType
  obtain ⟨sourceArguments, sourceReturn, sourceFunction,
      argumentsEquation, returnEquation⟩ :=
    (functionTypeRel_renameTypeVars_iff permutation
      policy.functionType (fromLeaTTaAtoms runtime.argumentTypes)
        (fromLeaTTaAtom runtime.returnType)).mp renamedFunction
  have partsEquation :
      policy.argumentTypes ++ [policy.returnType] =
        sourceArguments ++ [sourceReturn] := by
    rw [FunctionTypeRel] at sourceFunction
    rw [policy.isFunction] at sourceFunction
    simpa using sourceFunction
  have sourceArgumentsEquation :
      sourceArguments = policy.argumentTypes := by
    have dropped := congrArg List.dropLast partsEquation
    simpa [List.dropLast_concat] using dropped.symm
  have sourceReturnEquation : sourceReturn = policy.returnType := by
    have last := congrArg List.getLast? partsEquation
    simpa [List.getLast?_concat] using last.symm
  subst sourceArguments
  subst sourceReturn
  exact ⟨permutation, functionEquation, argumentsEquation, returnEquation⟩

/-- A single permutation of a published arrow induces the coherent policy
boundary for the runtime's separately stored arrow fields.  The witness is
arrow-level: argument and return occurrences cannot choose independent
private spellings. -/
theorem selectedTypePolicyRuntimeRel_of_permutation
    (permutation : Equiv.Perm String)
    {functionType : Atom} {argumentTypes : List Atom} {returnType : Atom}
    (isFunction : FunctionTypeRel functionType argumentTypes returnType)
    (runtimeBindings : Metta.Bindings) :
    SelectedTypePolicyRuntimeRel
      ⟨renameTypeVars permutation functionType,
        argumentTypes.map (renameTypeVars permutation),
        renameTypeVars permutation returnType,
        (functionTypeRel_renameTypeVars_iff permutation functionType
          (argumentTypes.map (renameTypeVars permutation))
          (renameTypeVars permutation returnType)).2
            ⟨argumentTypes, returnType, isFunction, rfl, rfl⟩⟩
      ⟨toLeaTTaAtom functionType, toLeaTTaAtoms argumentTypes,
        toLeaTTaAtom returnType, runtimeBindings⟩ := by
  constructor
  · exact ⟨functionType,
      ⟨permutation, permutation.injective, rfl⟩,
      by simpa using (TypeVariableRenamingOf.refl functionType)⟩
  · dsimp
    rw [fromLeaTTaAtom_toLeaTTaAtom,
      fromLeaTTaAtoms_toLeaTTaAtoms,
      fromLeaTTaAtom_toLeaTTaAtom]
    exact isFunction

/-- A normal finite presentation denotes exactly one specification binding
record.  This is intra-specification exactness: it does not identify the
finite presentation with any runtime spelling. -/
structure TypeBindingPresentationRel
    (presentation : TypeSubst) (bindings : Bindings) : Prop where
  normal : presentation.Normal
  solutions : ∀ valuation,
    TypeSubstSatisfied valuation presentation ↔
      TypeBindingSatisfied valuation bindings

/-- An input presentation additionally exposes no names beyond the binding
theory it represents.  This is the precise freshness fact needed when
candidate-local alpha renaming is transported over caller-visible bindings. -/
structure InitialTypeBindingPresentationRel
    (presentation : TypeSubst) (bindings : Bindings) : Prop
    extends TypeBindingPresentationRel presentation bindings where
  support : ∀ name,
    name ∈ specBindingVars (⟨presentation, []⟩ : Bindings) →
      name ∈ specBindingVars bindings

/-- The binding record formed from a finite presentation represents that
presentation literally. -/
theorem typeBindingPresentationRel_canonical
    {presentation : TypeSubst} (normal : presentation.Normal) :
    TypeBindingPresentationRel presentation
      (⟨presentation, []⟩ : Bindings) := by
  refine ⟨normal, ?_⟩
  intro valuation
  simp [TypeSubstSatisfied, TypeBindingSatisfied]

/-- Every binding theory represented by a normal finite presentation has a
model.  This rules out contradictory output records at the carrier boundary,
independently of how the successful branch was assembled. -/
theorem TypeBindingPresentationRel.satisfiable
    {presentation : TypeSubst} {bindings : Bindings}
    (relation : TypeBindingPresentationRel presentation bindings) :
    ∃ valuation, TypeBindingSatisfied valuation bindings := by
  let valuation := presentedValuation presentation
  exact ⟨valuation, (relation.solutions valuation).mp
    (normal_presentedValuation_satisfied relation.normal)⟩

/-- The assignment-only presentation is also the canonical supported input
representation of its own binding record. -/
theorem initialTypeBindingPresentationRel_canonical
    {presentation : TypeSubst} (normal : presentation.Normal) :
    InitialTypeBindingPresentationRel presentation
      (⟨presentation, []⟩ : Bindings) := by
  exact ⟨typeBindingPresentationRel_canonical normal,
    fun _ member => member⟩

/-- Package all assigned keys and value variables of a presentation into one
atom.  It is used only as a protected alpha-renaming scope. -/
def typePresentationScopeAtom (presentation : TypeSubst) : Atom :=
  .expression (presentation.map fun entry =>
    .expression [.var entry.1, entry.2])

/-- The scope atom lists exactly the variables observed by the corresponding
assignment-only binding theory. -/
theorem typeVars_typePresentationScopeAtom
    (presentation : TypeSubst) :
    TypeSubst.typeVars (typePresentationScopeAtom presentation) =
      specBindingVars (⟨presentation, []⟩ : Bindings) := by
  induction presentation with
  | nil => rfl
  | cons entry tail inductionHypothesis =>
      rcases entry with ⟨key, value⟩
      simp only [typePresentationScopeAtom, List.map_cons,
        TypeSubst.typeVars, TypeSubst.typeVarsList, specBindingVars,
        List.flatMap_cons, List.append_nil]
      have tailEquation :
          TypeSubst.typeVarsList
              (tail.map fun entry =>
                Atom.expression [Atom.var entry.1, entry.2]) =
            tail.flatMap fun entry =>
              entry.1 :: TypeSubst.typeVars entry.2 := by
        simpa only [typePresentationScopeAtom, TypeSubst.typeVars,
          specBindingVars, List.append_nil, List.flatMap_nil] using
          inductionHypothesis
      rw [tailEquation]
      simp

/-- A permutation fixing every name mentioned by a normal presentation acts
as the identity permutation state on that presentation. -/
theorem typePresentationPermutationState_of_support_fixed
    {permutation : Equiv.Perm String} {presentation : TypeSubst}
    (normal : presentation.Normal)
    (fixed : ∀ name,
      name ∈ specBindingVars (⟨presentation, []⟩ : Bindings) →
        permutation name = name) :
    TypePresentationPermutationState permutation presentation presentation := by
  refine ⟨normal, normal, ?_⟩
  intro valuation
  constructor
  · intro satisfied name value assignmentMember
    have keySupport : name ∈
        specBindingVars (⟨presentation, []⟩ : Bindings) := by
      simp [specBindingVars]
      exact ⟨name, value, assignmentMember, Or.inl rfl⟩
    rw [Function.comp_apply, fixed name keySupport]
    rw [satisfied name value assignmentMember]
    apply Eq.symm
    apply applyTypeValuation_congr_of_typeVars value
    intro valueName valueMember
    have valueSupport : valueName ∈
        specBindingVars (⟨presentation, []⟩ : Bindings) := by
      simp [specBindingVars]
      exact ⟨name, value, assignmentMember, Or.inr valueMember⟩
    simp [Function.comp_apply, fixed valueName valueSupport]
  · intro satisfied name value assignmentMember
    have keySupport : name ∈
        specBindingVars (⟨presentation, []⟩ : Bindings) := by
      simp [specBindingVars]
      exact ⟨name, value, assignmentMember, Or.inl rfl⟩
    have equation := satisfied name value assignmentMember
    rw [Function.comp_apply, fixed name keySupport] at equation
    rw [equation]
    apply applyTypeValuation_congr_of_typeVars value
    intro valueName valueMember
    have valueSupport : valueName ∈
        specBindingVars (⟨presentation, []⟩ : Bindings) := by
      simp [specBindingVars]
      exact ⟨name, value, assignmentMember, Or.inr valueMember⟩
    simp [Function.comp_apply, fixed valueName valueSupport]

/-- Exact presentation simulation exposes its specification-side representation. -/
theorem TypePresentationSimulationState.toTypeBindingPresentationRel
    {presentation : TypeSubst} {bindings : Bindings}
    {runtime : Metta.Bindings}
    (state : TypePresentationSimulationState presentation bindings runtime) :
    TypeBindingPresentationRel presentation bindings :=
  ⟨state.normal, state.specSolutions⟩

/-- Direct correspondence between the published candidate-scan outcome and
the repaired expected-selection outcome.  A successful outcome existentially
carries the finite presentation witnessing both the whole spec binding
extension and LeaTTa's selected binding record.  Exhaustion compares the flat
observable error lists; candidate-block structure remains in the preceding
classification layer. -/
inductive FunctionCandidateScanOutcomeRuntimeRel
    (observationScope : List String)
    (expression : Atom) (incoming : Bindings) :
    FunctionCandidateScanOutcome →
      Metta.Minimal.ExpectedFunctionTypeScanOutcome → Prop where
  | success {policy : SelectedTypePolicy} {output : Bindings}
      {runtime : Metta.Minimal.SelectedFunctionType}
      {presentation : TypeSubst} :
      SelectedTypePolicyPresentationRuntimeRel observationScope policy
        presentation runtime →
      PresentationExtensionRel incoming presentation output →
      (∀ valuation,
        TypeSubstSatisfied valuation presentation ↔
          TypeBindingSatisfied valuation output) →
      FunctionCandidateScanOutcomeRuntimeRel observationScope expression incoming
        (.success policy output) (.selected runtime)
  | exhausted {specErrors : List Atom}
      {runtimeErrors : List Metta.Minimal.ExpectedFunctionTypeError}
      {specTuple runtimeTuple : Bool} :
      CandidateErrorBlockRuntimeRel expression specErrors runtimeErrors →
      specTuple = runtimeTuple →
      FunctionCandidateScanOutcomeRuntimeRel observationScope expression incoming
        (.exhausted specErrors specTuple)
        (.exhausted runtimeErrors runtimeTuple)

/-- Candidate-scan correspondence is contravariant in its observation scope.
Only successful selection carries a scoped presentation; exhausted scans
retain the same exact error list and tuple flag at every scope. -/
theorem FunctionCandidateScanOutcomeRuntimeRel.mono
    {large small : List String} {expression : Atom} {incoming : Bindings}
    {specOutcome : FunctionCandidateScanOutcome}
    {runtimeOutcome : Metta.Minimal.ExpectedFunctionTypeScanOutcome}
    (relation : FunctionCandidateScanOutcomeRuntimeRel large expression
      incoming specOutcome runtimeOutcome)
    (subset : ∀ name, name ∈ small → name ∈ large) :
    FunctionCandidateScanOutcomeRuntimeRel small expression incoming
      specOutcome runtimeOutcome := by
  cases relation with
  | success coherent extension solutions =>
      exact .success (coherent.mono subset) extension solutions
  | exhausted errors tuple =>
      exact .exhausted errors tuple

/-- One fully applicable alpha-localized function signature.

The successful presentation is related to the evaluator-visible binding
output by exact solution-theory conjunction.  It may contain caller-visible
assignments; privacy and scoped inertness are derived later only for the
fresh subpresentation retained outside the runtime seed. -/
def PreparedCandidateSuccessRel
    (oracle : TypePreparationOracle)
    (space : Space) (expression candidate expectedType : Atom)
    (bindings : Bindings) (initialPresentation : TypeSubst)
    (policy : SelectedTypePolicy) (output : Bindings) : Prop :=
  ∃ operator arguments argumentTypes returnType candidateLists
      argumentOutcome returnOutcome privatePresentation,
    expression = .expression (operator :: arguments) ∧
    ∃ functionType : FunctionTypeRel candidate argumentTypes returnType,
      arguments.length = argumentTypes.length ∧
      PreparedArgumentPackageCandidates oracle space
        (typeServicePrivateAvoid space expression expectedType bindings)
        argumentTypes arguments candidateLists ∧
      FreshFamiliesSeparated [candidate] candidateLists.flatten ∧
      ArgumentCandidateListsBranchScanRel argumentTypes candidateLists 0
        initialPresentation argumentOutcome ∧
      ExpectedReturnBranchScanRel expectedType returnType
        argumentOutcome.successes returnOutcome ∧
      returnOutcome.selected = some privatePresentation ∧
      policy = ⟨candidate, argumentTypes, returnType, functionType⟩ ∧
      PresentationExtensionRel bindings privatePresentation output

/-- A successful prepared applicability path retains the candidate's arrow
and its unique domain/codomain projections literally in the selected policy. -/
theorem PreparedCandidateSuccessRel.policyFields
    {oracle : TypePreparationOracle}
    {space : Space} {expression candidate expectedType : Atom}
    {bindings output : Bindings} {initialPresentation : TypeSubst}
    {policy : SelectedTypePolicy}
    (success : PreparedCandidateSuccessRel oracle space expression candidate
      expectedType bindings initialPresentation policy output) :
    policy.functionType = candidate ∧
      FunctionTypeRel candidate policy.argumentTypes policy.returnType := by
  rcases success with
    ⟨_operator, _arguments, argumentTypes, returnType, _candidateLists,
      _argumentOutcome, _returnOutcome, _privatePresentation,
      _expressionEquation, functionType, _arity, _prepared, _separated,
      _argumentScan, _returnScan, _selected, policyEquation, _extension⟩
  subst policy
  exact ⟨rfl, functionType⟩

/-- A successful prepared candidate exposes one concrete declaration-ordered
actual-type choice, its complete argument presentation fold, and the return
constraint that commits that branch.  This existential path is the minimal
positive witness used to prove alpha-invariance of exact negatives; the
diagnostic ledger stays in the richer branch relations above. -/
theorem PreparedCandidateSuccessRel.exists_application_witness
    {oracle : TypePreparationOracle}
    {space : Space} {expression candidate expectedType : Atom}
    {bindings output : Bindings} {initialPresentation : TypeSubst}
    {policy : SelectedTypePolicy}
    (success : PreparedCandidateSuccessRel oracle space expression candidate
      expectedType bindings initialPresentation policy output) :
    ∃ operator arguments argumentTypes returnType candidateLists
        argumentPresentation actualTypes privatePresentation,
      expression = .expression (operator :: arguments) ∧
      FunctionTypeRel candidate argumentTypes returnType ∧
      PreparedArgumentPackageCandidates oracle space
        (typeServicePrivateAvoid space expression expectedType bindings)
        argumentTypes arguments candidateLists ∧
      FreshFamiliesSeparated [candidate] candidateLists.flatten ∧
      List.Forall₂ (fun actual candidates => actual ∈ candidates)
        actualTypes candidateLists ∧
      PresentationArgumentListMatchRel argumentTypes actualTypes
        initialPresentation
        argumentPresentation ∧
      CorePlusR2TypePresentationMatchRel argumentPresentation expectedType
        returnType privatePresentation := by
  rcases success with
    ⟨operator, arguments, argumentTypes, returnType, candidateLists,
      argumentOutcome, returnOutcome, privatePresentation,
      expressionEquation, functionType, arity, prepared, separated,
      argumentScan, returnScan, selected, _policyEquation, _extension⟩
  obtain ⟨argumentPresentation, argumentMember, returnMatch⟩ :=
    returnScan.exists_match_of_selected selected
  have lengthEquation : argumentTypes.length = candidateLists.length := by
    rw [← arity]
    exact prepared.arguments_length.symm
  obtain ⟨actualTypes, actualChoices, argumentMatch⟩ :=
    argumentScan.exists_choice_of_mem_success lengthEquation argumentMember
  exact ⟨operator, arguments, argumentTypes, returnType, candidateLists,
    argumentPresentation, actualTypes, privatePresentation,
    expressionEquation, functionType, prepared, separated, actualChoices,
    argumentMatch, returnMatch⟩

/-- The presentation selected by one concrete successful applicability path
already denotes the complete specification output.  The argument fold starts
from an exact presentation of the incoming theory, so the selected
presentation entails the incoming conjunct recorded by
`PresentationExtensionRel`. -/
theorem preparedCandidateSelectedPresentation_exact_output
    {expectedType returnType : Atom} {bindings output : Bindings}
    {initialPresentation privatePresentation : TypeSubst}
    {argumentTypes : List Atom} {candidateLists : List (List Atom)}
    {argumentOutcome : ArgumentCandidateListsBranchOutcome}
    {returnOutcome : ExpectedReturnBranchOutcome}
    (lengthEquation : argumentTypes.length = candidateLists.length)
    (initial : InitialTypeBindingPresentationRel initialPresentation bindings)
    (argumentScan : ArgumentCandidateListsBranchScanRel argumentTypes
      candidateLists 0 initialPresentation argumentOutcome)
    (returnScan : ExpectedReturnBranchScanRel expectedType returnType
      argumentOutcome.successes returnOutcome)
    (selected : returnOutcome.selected = some privatePresentation)
    (extension : PresentationExtensionRel bindings privatePresentation output) :
    ∀ valuation,
      TypeSubstSatisfied valuation privatePresentation ↔
        TypeBindingSatisfied valuation output := by
  obtain ⟨argumentPresentation, argumentMember, returnMatch⟩ :=
    returnScan.exists_match_of_selected selected
  obtain ⟨actualTypes, _actualChoices, argumentMatch⟩ :=
    argumentScan.exists_choice_of_mem_success lengthEquation argumentMember
  have argumentNormal : argumentPresentation.Normal :=
    Spec.Type.Presentation.ExactNormal.PresentationArgumentListMatchRel.output_normal
      argumentMatch initial.normal
  intro valuation
  constructor
  · intro privateSatisfied
    have argumentSatisfied :
        TypeSubstSatisfied valuation argumentPresentation :=
      ((CorePlusR2TypePresentationMatchRel.solutions
        returnMatch argumentNormal valuation).mp privateSatisfied).1
    have initialSatisfied :
        TypeSubstSatisfied valuation initialPresentation :=
      ((presentationArgumentList_solutions argumentMatch
        initial.normal valuation).mp argumentSatisfied).1
    have incomingSatisfied : TypeBindingSatisfied valuation bindings :=
      (initial.solutions valuation).mp initialSatisfied
    exact (extension valuation).mpr ⟨incomingSatisfied, privateSatisfied⟩
  · intro outputSatisfied
    exact ((extension valuation).mp outputSatisfied).2

/-- The final presentation selected by a successful prepared applicability
path represents the complete specification output, not merely a private
delta.  The argument and return matches both extend the initial
presentation, so the incoming conjunct in `PresentationExtensionRel` is
already entailed by the selected presentation. -/
theorem PreparedCandidateSuccessRel.exists_exact_output_presentation
    {oracle : TypePreparationOracle}
    {space : Space} {expression candidate expectedType : Atom}
    {bindings output : Bindings} {initialPresentation : TypeSubst}
    {policy : SelectedTypePolicy}
    (success : PreparedCandidateSuccessRel oracle space expression candidate
      expectedType bindings initialPresentation policy output)
    (initial : InitialTypeBindingPresentationRel initialPresentation
      bindings) :
    ∃ presentation,
      presentation.Normal ∧
        ∀ valuation,
          TypeSubstSatisfied valuation presentation ↔
            TypeBindingSatisfied valuation output := by
  rcases success with
    ⟨operator, arguments, argumentTypes, returnType, candidateLists,
      argumentOutcome, returnOutcome, privatePresentation,
      _expressionEquation, _functionType, arity, prepared, _separated,
      argumentScan, returnScan, selected, _policyEquation, extension⟩
  obtain ⟨argumentPresentation, argumentMember, returnMatch⟩ :=
    returnScan.exists_match_of_selected selected
  have lengthEquation : argumentTypes.length = candidateLists.length := by
    rw [← arity]
    exact prepared.arguments_length.symm
  obtain ⟨actualTypes, _actualChoices, argumentMatch⟩ :=
    argumentScan.exists_choice_of_mem_success lengthEquation argumentMember
  have argumentNormal : argumentPresentation.Normal :=
    Spec.Type.Presentation.ExactNormal.PresentationArgumentListMatchRel.output_normal
      argumentMatch initial.normal
  have privateNormal : privatePresentation.Normal :=
    returnMatch.output_normal argumentNormal
  refine ⟨privatePresentation, privateNormal, ?_⟩
  exact preparedCandidateSelectedPresentation_exact_output
    lengthEquation initial argumentScan returnScan selected extension

/-- Every successful prepared applicability output is semantically
inhabited.  This is the non-vacuity fact needed when the evaluator replays
the selected function type while constructing `InterpretFunctionRel`. -/
theorem PreparedCandidateSuccessRel.output_satisfiable
    {oracle : TypePreparationOracle}
    {space : Space} {expression candidate expectedType : Atom}
    {bindings output : Bindings} {initialPresentation : TypeSubst}
    {policy : SelectedTypePolicy}
    (success : PreparedCandidateSuccessRel oracle space expression candidate
      expectedType bindings initialPresentation policy output)
    (initial : InitialTypeBindingPresentationRel initialPresentation
      bindings) :
    ∃ valuation, TypeBindingSatisfied valuation output := by
  obtain ⟨presentation, normal, exactOutput⟩ :=
    success.exists_exact_output_presentation initial
  exact ⟨presentedValuation presentation,
    (exactOutput _).mp (normal_presentedValuation_satisfied normal)⟩

/-- An exhausted canonical prepared traversal excludes every alternative
lawful preparation of the same candidate.  The proof transports only the
finite satisfiability witness: private candidate spellings are aligned by one
permutation fixing the complete arrow and expected type, then completeness of
the already-built canonical branch scan supplies the contradiction. -/
theorem PreparedCandidateSuccessRel.not_of_inapplicable
    {oracle : TypePreparationOracle}
    (functional : TypePreparationFunctional oracle)
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env)
    {expression candidate expectedType : Atom} {bindings : Bindings}
    {operator returnType : Atom} {arguments argumentTypes : List Atom}
    {candidateLists : List (List Atom)}
    {initialPresentation : TypeSubst}
    {argumentOutcome : ArgumentCandidateListsBranchOutcome}
    {returnOutcome : ExpectedReturnBranchOutcome}
    (expressionEquation : expression = .expression (operator :: arguments))
    (functionType : FunctionTypeRel candidate argumentTypes returnType)
    (prepared : PreparedArgumentPackageCandidates oracle space
      (typeServicePrivateAvoid space expression expectedType bindings)
      argumentTypes arguments candidateLists)
    (separated : FreshFamiliesSeparated [candidate] candidateLists.flatten)
    (initial : InitialTypeBindingPresentationRel initialPresentation bindings)
    (argumentScan : ArgumentCandidateListsBranchScanRel argumentTypes
      candidateLists 0 initialPresentation argumentOutcome)
    (returnScan : ExpectedReturnBranchScanRel expectedType returnType
      argumentOutcome.successes returnOutcome)
    (notSelected : returnOutcome.selected = none) :
    ∀ policy output,
      ¬PreparedCandidateSuccessRel oracle space expression candidate
        expectedType bindings initialPresentation policy output := by
  intro policy output success
  obtain ⟨successOperator, successArguments, successArgumentTypes,
      successReturnType, successCandidateLists, argumentPresentation,
      successActualTypes, privatePresentation, successExpression,
      successFunctionType, successPrepared, successSeparated,
      successChoiceMembers, argumentMatch, returnMatch⟩ :=
    success.exists_application_witness
  have argumentsEquation : successArguments = arguments := by
    rw [expressionEquation] at successExpression
    exact (List.cons.inj (Atom.expression.inj successExpression)).2.symm
  subst successArguments
  have signatureParts := successFunctionType.unique functionType
  have argumentTypesEquation : successArgumentTypes = argumentTypes :=
    signatureParts.1
  have returnTypeEquation : successReturnType = returnType := signatureParts.2
  subst successArgumentTypes
  subst successReturnType
  let valuation := presentedValuation privatePresentation
  have argumentNormal : argumentPresentation.Normal :=
    Spec.Type.Presentation.ExactNormal.PresentationArgumentListMatchRel.output_normal
      argumentMatch initial.normal
  have privateNormal : privatePresentation.Normal :=
    returnMatch.output_normal argumentNormal
  have privateSatisfied : TypeSubstSatisfied valuation privatePresentation :=
    normal_presentedValuation_satisfied privateNormal
  have returnTheory := CorePlusR2TypePresentationMatchRel.solutions
    returnMatch argumentNormal valuation
  have argumentSatisfied :
      TypeSubstSatisfied valuation argumentPresentation :=
    (returnTheory.mp privateSatisfied).1
  have initialSatisfied :
      TypeSubstSatisfied valuation initialPresentation :=
    ((presentationArgumentList_solutions argumentMatch
      initial.normal valuation).mp argumentSatisfied).1
  have returnConsistent :
      CorePlusR2TypeConsistent valuation expectedType returnType :=
    (returnTheory.mp privateSatisfied).2
  have argumentConsistent : List.Forall₂
      (CorePlusR2TypeConsistent valuation) argumentTypes successActualTypes :=
    ((presentationArgumentList_solutions argumentMatch
      initial.normal valuation).mp argumentSatisfied).2
  let fixedApplication : Atom := .expression
    [candidate, expectedType, typePresentationScopeAtom initialPresentation]
  have successApplicationSeparated : FreshFamiliesSeparated
      [fixedApplication] successCandidateLists.flatten := by
    intro name fixedMember candidateMember
    have fixedMember' :
        name ∈ TypeSubst.typeVars candidate ∨
          name ∈ TypeSubst.typeVars expectedType ∨
          name ∈ TypeSubst.typeVars
            (typePresentationScopeAtom initialPresentation) := by
      simpa [fixedApplication, FreshFamiliesSeparated, AtomsAvoid,
        TypeSubst.typeVarsList, TypeSubst.typeVars] using fixedMember
    rcases fixedMember' with candidateMember' |
      (expectedMember | presentationMember)
    · exact successSeparated name (by
        simpa [TypeSubst.typeVarsList] using candidateMember') candidateMember
    · exact successPrepared.candidatesAvoid name candidateMember
        (List.mem_append_left _ (typeVars_mem_typeVarsList_of_mem
          (atom := expectedType)
          (atoms := space.atoms ++ [expression, expectedType]) (by simp)
          name expectedMember))
    · exact successPrepared.candidatesAvoid name candidateMember
        (List.mem_append_right _ (initial.support name (by
          rw [← typeVars_typePresentationScopeAtom initialPresentation]
          exact presentationMember)))
  have canonicalApplicationSeparated : FreshFamiliesSeparated
      [fixedApplication] candidateLists.flatten := by
    intro name fixedMember candidateMember
    have fixedMember' :
        name ∈ TypeSubst.typeVars candidate ∨
          name ∈ TypeSubst.typeVars expectedType ∨
          name ∈ TypeSubst.typeVars
            (typePresentationScopeAtom initialPresentation) := by
      simpa [fixedApplication, FreshFamiliesSeparated, AtomsAvoid,
        TypeSubst.typeVarsList, TypeSubst.typeVars] using fixedMember
    rcases fixedMember' with candidateMember' |
      (expectedMember | presentationMember)
    · exact separated name (by
        simpa [TypeSubst.typeVarsList] using candidateMember') candidateMember
    · exact prepared.candidatesAvoid name candidateMember
        (List.mem_append_left _ (typeVars_mem_typeVarsList_of_mem
          (atom := expectedType)
          (atoms := space.atoms ++ [expression, expectedType]) (by simp)
          name expectedMember))
    · exact prepared.candidatesAvoid name candidateMember
        (List.mem_append_right _ (initial.support name (by
          rw [← typeVars_typePresentationScopeAtom initialPresentation]
          exact presentationMember)))
  obtain ⟨canonicalActualTypes, permutation, canonicalChoiceMembers,
      fixedApplicationEquation, canonicalActualTypesEquation⟩ :=
    preparedApplicationChoicePermutation functional index successPrepared
      prepared successApplicationSeparated canonicalApplicationSeparated
        successChoiceMembers
  have fixedParts :
      [renameTypeVars permutation candidate,
          renameTypeVars permutation expectedType,
          renameTypeVars permutation
            (typePresentationScopeAtom initialPresentation)] =
        [candidate, expectedType,
          typePresentationScopeAtom initialPresentation] := by
    exact Atom.expression.inj (by
      simpa [fixedApplication, renameTypeVars] using fixedApplicationEquation)
  have candidateFixed : renameTypeVars permutation candidate = candidate :=
    (List.cons.inj fixedParts).1
  have expectedFixed :
      renameTypeVars permutation expectedType = expectedType :=
    (List.cons.inj (List.cons.inj fixedParts).2).1
  have presentationScopeFixed :
      renameTypeVars permutation
          (typePresentationScopeAtom initialPresentation) =
        typePresentationScopeAtom initialPresentation :=
    (List.cons.inj (List.cons.inj
      (List.cons.inj fixedParts).2).2).1
  have permutationFixesInitial (name : String)
      (member : name ∈
        specBindingVars (⟨initialPresentation, []⟩ : Bindings)) :
      permutation name = name := by
    have scopeMember : name ∈ TypeSubst.typeVars
        (typePresentationScopeAtom initialPresentation) :=
      (by rw [typeVars_typePresentationScopeAtom initialPresentation]
          exact member)
    have appliedEquation :
        applyTypeValuation (fun name' => .var (permutation name'))
            (typePresentationScopeAtom initialPresentation) =
          typePresentationScopeAtom initialPresentation := by
      have renameAsValuation := applyTypeValuation_renameTypeVars
        (fun name' => .var name') permutation
          (typePresentationScopeAtom initialPresentation)
      simpa [Function.comp_def, presentationScopeFixed] using
        renameAsValuation.symm
    have fixedVariable := valuation_fixes_variable_of_apply_eq_self
      (fun name' => .var (permutation name'))
      (typePresentationScopeAtom initialPresentation) name
      appliedEquation scopeMember
    exact Atom.var.inj fixedVariable
  have renamedFunctionType : FunctionTypeRel candidate
      (argumentTypes.map (renameTypeVars permutation))
      (renameTypeVars permutation returnType) := by
    rw [← candidateFixed]
    exact (functionTypeRel_renameTypeVars_iff permutation candidate
      (argumentTypes.map (renameTypeVars permutation))
      (renameTypeVars permutation returnType)).2
        ⟨argumentTypes, returnType, functionType, rfl, rfl⟩
  have renamedSignatureParts := renamedFunctionType.unique functionType
  have argumentTypesFixed :
      argumentTypes.map (renameTypeVars permutation) = argumentTypes :=
    renamedSignatureParts.1
  have returnTypeFixed :
      renameTypeVars permutation returnType = returnType :=
    renamedSignatureParts.2
  let transportedValuation : String → Atom := valuation ∘ permutation.symm
  have transportedInitial :
      TypeSubstSatisfied transportedValuation initialPresentation := by
    intro name value assignmentMember
    have keySupport : name ∈
        specBindingVars (⟨initialPresentation, []⟩ : Bindings) := by
      simp [specBindingVars]
      exact ⟨name, value, assignmentMember, Or.inl rfl⟩
    have inverseFix (name' : String)
        (support : name' ∈
          specBindingVars (⟨initialPresentation, []⟩ : Bindings)) :
        permutation.symm name' = name' := by
      calc
        permutation.symm name' =
            permutation.symm (permutation name') := by
              rw [permutationFixesInitial name' support]
        _ = name' := permutation.left_inv name'
    have valueAgreement :
        applyTypeValuation transportedValuation value =
          applyTypeValuation valuation value := by
      apply applyTypeValuation_congr_of_typeVars value
      intro name' variableMember
      have variableSupport : name' ∈
          specBindingVars (⟨initialPresentation, []⟩ : Bindings) := by
        simp [specBindingVars]
        exact ⟨name, value, assignmentMember, Or.inr variableMember⟩
      simp [transportedValuation, Function.comp_def,
        inverseFix name' variableSupport]
    rw [valueAgreement]
    simpa [transportedValuation, Function.comp_def,
      inverseFix name keySupport] using
        initialSatisfied name value assignmentMember
  have transportedArguments : List.Forall₂
      (CorePlusR2TypeConsistent transportedValuation)
      (argumentTypes.map (renameTypeVars permutation))
      (successActualTypes.map (renameTypeVars permutation)) := by
    apply (argumentConsistency_rename_iff transportedValuation permutation
      argumentTypes successActualTypes).mpr
    simpa [transportedValuation, Function.comp_def] using argumentConsistent
  have canonicalArguments : List.Forall₂
      (CorePlusR2TypeConsistent transportedValuation)
      argumentTypes canonicalActualTypes := by
    rw [canonicalActualTypesEquation, ← argumentTypesFixed]
    exact transportedArguments
  obtain ⟨canonicalPresentation, canonicalMember, canonicalNormal,
      canonicalSatisfied⟩ :=
    argumentScan.exists_satisfied_success canonicalChoiceMembers
      initial.normal transportedInitial canonicalArguments
  have transportedReturn : CorePlusR2TypeConsistent transportedValuation
      (renameTypeVars permutation expectedType)
      (renameTypeVars permutation returnType) := by
    apply (corePlusR2TypeConsistent_rename_iff transportedValuation permutation
      expectedType returnType).mpr
    simpa [transportedValuation, Function.comp_def] using returnConsistent
  have canonicalReturn : CorePlusR2TypeConsistent transportedValuation
      expectedType returnType := by
    simpa only [expectedFixed, returnTypeFixed] using transportedReturn
  obtain ⟨selected, selectedEquation⟩ :=
    returnScan.exists_selected_of_consistent_branch canonicalMember
      canonicalNormal canonicalSatisfied canonicalReturn
  rw [notSelected] at selectedEquation
  contradiction

/-- Assemble one successful candidate from the already exact argument and
return workers.  All executable-independent facts stay intra-specification;
the only cross-boundary facts are the coherent selected-arrow observation
and the scoped presentation state carried by the return worker.

This is the success half of the concrete singleton classifier.  It is kept
separate from the outer candidate-list induction so signature preparation is
proved once per candidate and scan order is proved once per list. -/
theorem preparedCandidateSuccess_runtime
    {oracle : TypePreparationOracle}
    {space : Space} {observationScope : List String}
    {expression expectedType : Atom} {bindings : Bindings}
    {operator : Atom} {arguments argumentTypes : List Atom}
    {candidate returnType : Atom}
    {candidateLists : List (List Atom)}
    {initialPresentation : TypeSubst}
    {argumentOutcome : ArgumentCandidateListsBranchOutcome}
    {returnOutcome : ExpectedReturnBranchOutcome}
    {privatePresentation : TypeSubst}
    {runtime : Metta.Minimal.SelectedFunctionType}
    (expressionEquation :
      expression = .expression (operator :: arguments))
    (functionType : FunctionTypeRel candidate argumentTypes returnType)
    (arity : arguments.length = argumentTypes.length)
    (prepared : PreparedArgumentPackageCandidates oracle space
      (typeServicePrivateAvoid space expression expectedType bindings)
      argumentTypes arguments candidateLists)
    (separated : FreshFamiliesSeparated [candidate] candidateLists.flatten)
    (initial : InitialTypeBindingPresentationRel initialPresentation bindings)
    (argumentScan : ArgumentCandidateListsBranchScanRel argumentTypes
      candidateLists 0 initialPresentation argumentOutcome)
    (returnScan : ExpectedReturnBranchScanRel expectedType returnType
      argumentOutcome.successes returnOutcome)
    (specSelected : returnOutcome.selected = some privatePresentation)
    (coherent : SelectedTypePolicyPresentationRuntimeRel observationScope
      ⟨candidate, argumentTypes, returnType, functionType⟩
      privatePresentation runtime) :
    ∃ output,
      PreparedCandidateSuccessRel oracle space expression candidate
          expectedType bindings initialPresentation
          ⟨candidate, argumentTypes, returnType, functionType⟩ output ∧
        FunctionCandidateScanOutcomeRuntimeRel observationScope expression
          bindings
          (.success ⟨candidate, argumentTypes, returnType, functionType⟩
            output)
          (.selected runtime) := by
  let output : Bindings :=
    ⟨bindings.assignments ++ privatePresentation, bindings.equalities⟩
  refine ⟨output, ?_, ?_⟩
  · exact ⟨operator, arguments, argumentTypes, returnType,
      candidateLists, argumentOutcome, returnOutcome, privatePresentation,
      expressionEquation, functionType, arity, prepared, separated,
      argumentScan, returnScan, specSelected, rfl,
      presentationExtension_append bindings privatePresentation⟩
  · have lengthEquation : argumentTypes.length = candidateLists.length := by
      rw [← arity]
      exact prepared.arguments_length.symm
    have extension : PresentationExtensionRel bindings privatePresentation
        output :=
      presentationExtension_append bindings privatePresentation
    exact .success coherent extension
      (preparedCandidateSelectedPresentation_exact_output
        lengthEquation initial argumentScan returnScan specSelected extension)

/-- A concrete failed applicability traversal for one syntactic function.
The separate negative-success field in `PreparedCandidateFailureRel` makes
the exact-negative obligation explicit across all lawful oracle recoveries. -/
inductive PreparedCandidateFailureCaseRel
    (oracle : TypePreparationOracle)
    (space : Space) (expression candidate expectedType : Atom)
    (bindings : Bindings) (initialPresentation : TypeSubst) :
    List Atom → Prop where
  | wrongArity {operator returnType : Atom}
      {arguments argumentTypes : List Atom} :
      expression = .expression (operator :: arguments) →
      FunctionTypeRel candidate argumentTypes returnType →
      arguments.length ≠ argumentTypes.length →
      PreparedCandidateFailureCaseRel oracle space expression candidate
        expectedType bindings initialPresentation
        [mkError expression .incorrectNumberOfArguments]
  | inapplicable {operator returnType : Atom}
      {arguments argumentTypes : List Atom}
      {candidateLists : List (List Atom)}
      {argumentOutcome : ArgumentCandidateListsBranchOutcome}
      {returnOutcome : ExpectedReturnBranchOutcome} :
      expression = .expression (operator :: arguments) →
      FunctionTypeRel candidate argumentTypes returnType →
      arguments.length = argumentTypes.length →
      PreparedArgumentPackageCandidates oracle space
        (typeServicePrivateAvoid space expression expectedType bindings)
        argumentTypes arguments candidateLists →
      FreshFamiliesSeparated [candidate] candidateLists.flatten →
      ArgumentCandidateListsBranchScanRel argumentTypes candidateLists 0
        initialPresentation argumentOutcome →
      ExpectedReturnBranchScanRel expectedType returnType
        argumentOutcome.successes returnOutcome →
      returnOutcome.selected = none →
      PreparedCandidateFailureCaseRel oracle space expression candidate
        expectedType bindings initialPresentation
        (candidateApplicabilityErrors expression argumentOutcome returnOutcome)

/-- Exact failed-candidate evidence.  Failure includes both a concrete
ordered traversal and the global negative needed by the generic candidate
scan; concrete runtime functionality and alpha invariance discharge that
negative in the realization theorem. -/
structure PreparedCandidateFailureRel
    (oracle : TypePreparationOracle)
    (space : Space) (expression candidate expectedType : Atom)
    (bindings : Bindings) (initialPresentation : TypeSubst)
    (errors : List Atom) : Prop where
  failure : PreparedCandidateFailureCaseRel oracle space expression candidate
    expectedType bindings initialPresentation errors
  nonempty : errors ≠ []
  noSuccess : ∀ policy output,
    ¬PreparedCandidateSuccessRel oracle space expression candidate
      expectedType bindings initialPresentation policy output

/-- Arity rejection is globally exact: the unique arrow decomposition makes
every successful prepared traversal carry the same formal-list length, so a
runtime arity mismatch cannot coexist with any specification success. -/
theorem preparedCandidateFailure_wrongArity
    {oracle : TypePreparationOracle}
    {space : Space} {expression candidate expectedType : Atom}
    {bindings : Bindings} {initialPresentation : TypeSubst}
    {operator returnType : Atom}
    {arguments argumentTypes : List Atom}
    (expressionEquation : expression = .expression (operator :: arguments))
    (functionType : FunctionTypeRel candidate argumentTypes returnType)
    (arity : arguments.length ≠ argumentTypes.length) :
    PreparedCandidateFailureRel oracle space expression candidate expectedType
      bindings initialPresentation
        [mkError expression .incorrectNumberOfArguments] := by
  refine ⟨PreparedCandidateFailureCaseRel.wrongArity expressionEquation
      functionType arity, by simp, ?_⟩
  intro policy output success
  rcases success with
    ⟨_successOperator, successArguments, successArgumentTypes,
      successReturn, _candidateLists, _argumentOutcome, _returnOutcome,
      _privatePresentation, successExpression, successFunction,
      successArity, _⟩
  have argumentsEquation : successArguments = arguments := by
    rw [expressionEquation] at successExpression
    exact (List.cons.inj (Atom.expression.inj successExpression)).2.symm
  have formalsEquation : successArgumentTypes = argumentTypes :=
    (successFunction.unique functionType).1
  apply arity
  rw [← argumentsEquation, ← formalsEquation]
  exact successArity

/-- An arity-aligned canonical traversal with no selected return branch is an
exact candidate failure: its ledger is nonempty and alpha-equivalent lawful
preparations cannot hide a successful application. -/
theorem preparedCandidateFailure_inapplicable
    {oracle : TypePreparationOracle}
    (functional : TypePreparationFunctional oracle)
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env)
    {expression candidate expectedType : Atom} {bindings : Bindings}
    {operator returnType : Atom} {arguments argumentTypes : List Atom}
    {candidateLists : List (List Atom)}
    {initialPresentation : TypeSubst}
    {argumentOutcome : ArgumentCandidateListsBranchOutcome}
    {returnOutcome : ExpectedReturnBranchOutcome}
    (expressionEquation : expression = .expression (operator :: arguments))
    (functionType : FunctionTypeRel candidate argumentTypes returnType)
    (arity : arguments.length = argumentTypes.length)
    (prepared : PreparedArgumentPackageCandidates oracle space
      (typeServicePrivateAvoid space expression expectedType bindings)
      argumentTypes arguments candidateLists)
    (separated : FreshFamiliesSeparated [candidate] candidateLists.flatten)
    (initial : InitialTypeBindingPresentationRel initialPresentation bindings)
    (argumentScan : ArgumentCandidateListsBranchScanRel argumentTypes
      candidateLists 0 initialPresentation argumentOutcome)
    (returnScan : ExpectedReturnBranchScanRel expectedType returnType
      argumentOutcome.successes returnOutcome)
    (notSelected : returnOutcome.selected = none) :
    PreparedCandidateFailureRel oracle space expression candidate expectedType
      bindings initialPresentation
      (candidateApplicabilityErrors expression argumentOutcome returnOutcome) := by
  refine ⟨PreparedCandidateFailureCaseRel.inapplicable expressionEquation
      functionType arity prepared separated argumentScan returnScan notSelected,
    candidateApplicabilityErrors_nonempty arity prepared argumentScan returnScan
      notSelected, ?_⟩
  exact PreparedCandidateSuccessRel.not_of_inapplicable functional index
    expressionEquation functionType prepared separated initial argumentScan
      returnScan notSelected

/-- Assemble one exact inapplicable-candidate failure and its runtime error
block from the already-complete argument and return workers.  The theorem
keeps candidate failure as a block: flattening belongs only to the outer
ordered candidate scan. -/
theorem preparedCandidateFailure_runtime
    {oracle : TypePreparationOracle}
    (functional : TypePreparationFunctional oracle)
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env)
    {observationScope : List String}
    {expression candidate expectedType : Atom} {bindings : Bindings}
    {operator returnType : Atom} {arguments argumentTypes : List Atom}
    {candidateLists : List (List Atom)}
    {initialPresentation : TypeSubst}
    {argumentOutcome : ArgumentCandidateListsBranchOutcome}
    {returnOutcome : ExpectedReturnBranchOutcome}
    {runtimeArgumentOutcome : Metta.Minimal.TypeCheckArgsBranchResult}
    {runtimeReturnOutcome : Metta.Minimal.ExpectedReturnBranchScanResult}
    (expressionEquation : expression = .expression (operator :: arguments))
    (functionType : FunctionTypeRel candidate argumentTypes returnType)
    (arity : arguments.length = argumentTypes.length)
    (prepared : PreparedArgumentPackageCandidates oracle space
      (typeServicePrivateAvoid space expression expectedType bindings)
      argumentTypes arguments candidateLists)
    (separated : FreshFamiliesSeparated [candidate] candidateLists.flatten)
    (initial : InitialTypeBindingPresentationRel initialPresentation bindings)
    (argumentScan : ArgumentCandidateListsBranchScanRel argumentTypes
      candidateLists 0 initialPresentation argumentOutcome)
    (argumentRuntime : ScopedArgumentBranchOutcomeRuntimeRel
      observationScope argumentOutcome runtimeArgumentOutcome)
    (returnScan : ExpectedReturnBranchScanRel expectedType returnType
      argumentOutcome.successes returnOutcome)
    (returnRuntime : ScopedExpectedReturnBranchOutcomeRuntimeRel
      observationScope returnOutcome runtimeReturnOutcome)
    (notSelected : returnOutcome.selected = none) :
    PreparedCandidateFailureRel oracle space expression candidate expectedType
        bindings initialPresentation
        (candidateApplicabilityErrors expression argumentOutcome returnOutcome) ∧
      CandidateErrorBlockRuntimeRel expression
        (candidateApplicabilityErrors expression argumentOutcome returnOutcome)
        ((runtimeArgumentOutcome.errors.map fun diagnostic =>
            .ordinary diagnostic.toFunctionTypeError) ++
          runtimeReturnOutcome.errors) := by
  exact ⟨preparedCandidateFailure_inapplicable functional index
      expressionEquation functionType arity prepared separated initial
        argumentScan returnScan notSelected,
    candidateApplicabilityErrors_runtime expression argumentRuntime
      returnRuntime⟩

/-- One alpha-localized candidate has either one exact success package or one
nonempty exact failure block. -/
def PreparedCandidateApplicabilityRel
    (oracle : TypePreparationOracle)
    (space : Space) (expression candidate expectedType : Atom)
    (bindings : Bindings) (initialPresentation : TypeSubst) :
    SelectedTypeApplicabilityOutcome → Prop
  | .success policy output =>
      PreparedCandidateSuccessRel oracle space expression candidate
        expectedType bindings initialPresentation policy output
  | .error errors =>
      PreparedCandidateFailureRel oracle space expression candidate
        expectedType bindings initialPresentation errors

/-- Failure evidence exposes the negative-success fact required by the
generic ordered scan without reopening its concrete traversal. -/
theorem PreparedCandidateApplicabilityRel.no_success_of_error
    {oracle : TypePreparationOracle}
    {space : Space} {expression candidate expectedType : Atom}
    {bindings : Bindings} {initialPresentation : TypeSubst}
    {errors : List Atom}
    (failure : PreparedCandidateApplicabilityRel oracle space expression
      candidate expectedType bindings initialPresentation (.error errors)) :
    ∀ policy output,
      ¬PreparedCandidateApplicabilityRel oracle space expression candidate
        expectedType bindings initialPresentation (.success policy output) :=
  failure.noSuccess

/-- Every function-candidate failure contributes at least one error atom. -/
theorem PreparedCandidateApplicabilityRel.error_nonempty
    {oracle : TypePreparationOracle}
    {space : Space} {expression candidate expectedType : Atom}
    {bindings : Bindings} {initialPresentation : TypeSubst}
    {errors : List Atom}
    (failure : PreparedCandidateApplicabilityRel oracle space expression
      candidate expectedType bindings initialPresentation (.error errors)) :
    errors ≠ [] :=
  failure.nonempty

/-- Successful prepared applicability exposes the arrow decomposition needed
by the generic candidate scan. -/
theorem PreparedCandidateApplicabilityRel.functionType_of_success
    {oracle : TypePreparationOracle}
    {space : Space} {expression candidate expectedType : Atom}
    {bindings output : Bindings} {initialPresentation : TypeSubst}
    {policy : SelectedTypePolicy}
    (success : PreparedCandidateApplicabilityRel oracle space expression
      candidate expectedType bindings initialPresentation
        (.success policy output)) :
    ∃ argumentTypes returnType,
      FunctionTypeRel candidate argumentTypes returnType := by
  rcases success with
    ⟨_operator, _arguments, argumentTypes, returnType, _candidateLists,
      _argumentOutcome, _returnOutcome, _presentation, _expressionEquation,
      function, _⟩
  exact ⟨argumentTypes, returnType, function⟩

/-- Exact classification of one aligned specification/runtime candidate.
The runtime side is observed through its singleton scan: selection carries
the direct scoped outcome boundary, a malformed candidate is tuple-eligible,
and a failed function carries one nonempty ordered error block. -/
def PreparedCandidateSingletonRuntimeRel
    (oracle : TypePreparationOracle)
    (space : Space) (observationScope : List String)
    (expression expectedType : Atom) (incoming : Bindings)
    (initialPresentation : TypeSubst)
    (env : Metta.Minimal.MinEnv) (world : Metta.Minimal.World)
    (runtimeInitial : Metta.Bindings)
    (runtimeExpression : Metta.Atom)
    (runtimeArguments : List Metta.Atom) (runtimeExpected : Metta.Atom)
    (allowExtraArguments : Bool)
    (candidate : Atom) (runtimeCandidate : Metta.Atom) : Prop :=
  match Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom env world
      runtimeExpression runtimeArguments runtimeExpected allowExtraArguments
        runtimeInitial [runtimeCandidate] with
  | .selected runtime =>
      ∃ policy output,
        PreparedCandidateApplicabilityRel oracle space expression candidate
            expectedType incoming initialPresentation
              (.success policy output) ∧
          FunctionCandidateScanOutcomeRuntimeRel observationScope expression
            incoming (.success policy output) (.selected runtime)
  | .exhausted runtimeErrors true =>
      runtimeErrors = [] ∧
        ¬∃ argumentTypes returnType,
          FunctionTypeRel candidate argumentTypes returnType
  | .exhausted runtimeErrors false =>
      ∃ argumentTypes returnType specErrors,
        FunctionTypeRel candidate argumentTypes returnType ∧
          PreparedCandidateApplicabilityRel oracle space expression candidate
            expectedType incoming initialPresentation (.error specErrors) ∧
          CandidateErrorBlockRuntimeRel expression specErrors runtimeErrors

/-- A concrete singleton selection is classified directly from the exact
successful applicability package.  The executable scan equation is retained
at this boundary and is not re-unfolded by the outer candidate-list proof. -/
theorem PreparedCandidateSingletonRuntimeRel.ofSelected
    {oracle : TypePreparationOracle}
    {space : Space} {observationScope : List String}
    {expression expectedType : Atom} {incoming : Bindings}
    {initialPresentation : TypeSubst}
    {env : Metta.Minimal.MinEnv} {world : Metta.Minimal.World}
    {runtimeInitial : Metta.Bindings}
    {runtimeExpression : Metta.Atom}
    {runtimeArguments : List Metta.Atom} {runtimeExpected : Metta.Atom}
    {allowExtraArguments : Bool}
    {candidate : Atom} {runtimeCandidate : Metta.Atom}
    {runtime : Metta.Minimal.SelectedFunctionType}
    {policy : SelectedTypePolicy} {output : Bindings}
    (scanEquation :
      Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom env world
        runtimeExpression runtimeArguments runtimeExpected allowExtraArguments
          runtimeInitial [runtimeCandidate] = .selected runtime)
    (applicable : PreparedCandidateApplicabilityRel oracle space expression
      candidate expectedType incoming initialPresentation
        (.success policy output))
    (outcome : FunctionCandidateScanOutcomeRuntimeRel observationScope
      expression incoming (.success policy output) (.selected runtime)) :
    PreparedCandidateSingletonRuntimeRel oracle space observationScope
      expression expectedType incoming initialPresentation env world
      runtimeInitial runtimeExpression runtimeArguments runtimeExpected
      allowExtraArguments candidate runtimeCandidate := by
  unfold PreparedCandidateSingletonRuntimeRel
  rw [scanEquation]
  exact ⟨policy, output, applicable, outcome⟩

/-- A singleton non-function classification records tuple eligibility and no
errors exactly.  Shape rejection remains specification-side and therefore
does not depend on executable pattern matching after this boundary. -/
theorem PreparedCandidateSingletonRuntimeRel.ofNonFunction
    {oracle : TypePreparationOracle}
    {space : Space} {observationScope : List String}
    {expression expectedType : Atom} {incoming : Bindings}
    {initialPresentation : TypeSubst}
    {env : Metta.Minimal.MinEnv} {world : Metta.Minimal.World}
    {runtimeInitial : Metta.Bindings}
    {runtimeExpression : Metta.Atom}
    {runtimeArguments : List Metta.Atom} {runtimeExpected : Metta.Atom}
    {allowExtraArguments : Bool}
    {candidate : Atom} {runtimeCandidate : Metta.Atom}
    (scanEquation :
      Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom env world
        runtimeExpression runtimeArguments runtimeExpected allowExtraArguments
          runtimeInitial [runtimeCandidate] = .exhausted [] true)
    (notFunction : ¬∃ argumentTypes returnType,
      FunctionTypeRel candidate argumentTypes returnType) :
    PreparedCandidateSingletonRuntimeRel oracle space observationScope
      expression expectedType incoming initialPresentation env world
      runtimeInitial runtimeExpression runtimeArguments runtimeExpected
      allowExtraArguments candidate runtimeCandidate := by
  unfold PreparedCandidateSingletonRuntimeRel
  rw [scanEquation]
  exact ⟨rfl, notFunction⟩

/-- Structural translation preserves the executable singleton outcome for a
non-arrow candidate.  This is the shared computation behind both literal and
independently alpha-localized non-function classifications. -/
theorem scanFunctionTypeCandidatesForExpectedFrom_singleton_nonFunction
    {env : Metta.Minimal.MinEnv} {world : Metta.Minimal.World}
    {runtimeInitial : Metta.Bindings}
    {runtimeExpression : Metta.Atom}
    {runtimeArguments : List Metta.Atom} {runtimeExpected : Metta.Atom}
    {allowExtraArguments : Bool} {candidate : Atom}
    (notFunction : ¬∃ argumentTypes returnType,
      FunctionTypeRel candidate argumentTypes returnType) :
    Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom env world
      runtimeExpression runtimeArguments runtimeExpected allowExtraArguments
        runtimeInitial [toLeaTTaAtom candidate] = .exhausted [] true := by
  cases candidate with
    | symbol name =>
        simp [Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom,
          Metta.Minimal.ExpectedFunctionTypeScanOutcome.markTupleEligible,
          toLeaTTaAtom]
    | var name =>
        simp [Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom,
          Metta.Minimal.ExpectedFunctionTypeScanOutcome.markTupleEligible,
          toLeaTTaAtom]
    | grounded value =>
        simp [Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom,
          Metta.Minimal.ExpectedFunctionTypeScanOutcome.markTupleEligible,
          toLeaTTaAtom]
    | expression atoms =>
        cases atoms with
        | nil =>
            simp [Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom,
              Metta.Minimal.ExpectedFunctionTypeScanOutcome.markTupleEligible,
              toLeaTTaAtom, toLeaTTaAtoms]
        | cons head signature =>
            cases head with
            | symbol name =>
                by_cases arrowHead : name = "->"
                · subst name
                  rcases signature.eq_nil_or_concat with rfl |
                    ⟨argumentTypes, returnType, rfl⟩
                  · simp [Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom,
                      Metta.Minimal.ExpectedFunctionTypeScanOutcome.markTupleEligible,
                      toLeaTTaAtom, toLeaTTaAtoms]
                  · exfalso
                    apply notFunction
                    exact ⟨argumentTypes, returnType, by simp [FunctionTypeRel]⟩
                · simp [Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom,
                    Metta.Minimal.ExpectedFunctionTypeScanOutcome.markTupleEligible,
                    toLeaTTaAtom, toLeaTTaAtoms, arrowHead]
            | var name =>
                simp [Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom,
                  Metta.Minimal.ExpectedFunctionTypeScanOutcome.markTupleEligible,
                  toLeaTTaAtom, toLeaTTaAtoms]
            | grounded value =>
                simp [Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom,
                  Metta.Minimal.ExpectedFunctionTypeScanOutcome.markTupleEligible,
                  toLeaTTaAtom, toLeaTTaAtoms]
            | expression nested =>
                simp [Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom,
                  Metta.Minimal.ExpectedFunctionTypeScanOutcome.markTupleEligible,
                  toLeaTTaAtom, toLeaTTaAtoms]

/-- A private alpha presentation cannot create or destroy arrow structure. -/
theorem TypeCandidateAlphaVariantRel.notFunction
    {avoid : List String} {source target : Atom}
    (variant : TypeCandidateAlphaVariantRel avoid source target)
    (notFunction : ¬∃ argumentTypes returnType,
      FunctionTypeRel source argumentTypes returnType) :
    ¬∃ argumentTypes returnType,
      FunctionTypeRel target argumentTypes returnType := by
  rintro ⟨argumentTypes, returnType, targetFunction⟩
  rcases variant with ⟨rename, _injective, rfl, _fresh⟩
  obtain ⟨sourceArguments, sourceReturn, sourceFunction, _⟩ :=
    (functionTypeRel_renameTypeVars_iff rename source
      argumentTypes returnType).1 targetFunction
  exact notFunction ⟨sourceArguments, sourceReturn, sourceFunction⟩

/-- Structural translation preserves the non-arrow singleton case exactly.
This is the literal leaf classifier used by the generated candidate-list
assembly. -/
theorem PreparedCandidateSingletonRuntimeRel.ofTranslatedNonFunction
    {oracle : TypePreparationOracle}
    {space : Space} {observationScope : List String}
    {expression expectedType : Atom} {incoming : Bindings}
    {initialPresentation : TypeSubst}
    {env : Metta.Minimal.MinEnv} {world : Metta.Minimal.World}
    {runtimeInitial : Metta.Bindings}
    {runtimeExpression : Metta.Atom}
    {runtimeArguments : List Metta.Atom} {runtimeExpected : Metta.Atom}
    {allowExtraArguments : Bool} {candidate : Atom}
    (notFunction : ¬∃ argumentTypes returnType,
      FunctionTypeRel candidate argumentTypes returnType) :
    PreparedCandidateSingletonRuntimeRel oracle space observationScope
      expression expectedType incoming initialPresentation env world
      runtimeInitial runtimeExpression runtimeArguments runtimeExpected
      allowExtraArguments candidate (toLeaTTaAtom candidate) := by
  exact PreparedCandidateSingletonRuntimeRel.ofNonFunction
    (scanFunctionTypeCandidatesForExpectedFrom_singleton_nonFunction notFunction)
    notFunction

/-- Two independently localized presentations of one non-arrow source form
the exact singleton classification.  Only their shared source shape matters;
private spellings remain irrelevant and no synthetic error is introduced. -/
theorem PreparedCandidateSingletonRuntimeRel.ofAlphaNonFunction
    {oracle : TypePreparationOracle}
    {space : Space} {observationScope : List String}
    {expression expectedType : Atom} {incoming : Bindings}
    {initialPresentation : TypeSubst}
    {env : Metta.Minimal.MinEnv} {world : Metta.Minimal.World}
    {runtimeInitial : Metta.Bindings}
    {runtimeExpression : Metta.Atom}
    {runtimeArguments : List Metta.Atom} {runtimeExpected : Metta.Atom}
    {allowExtraArguments : Bool}
    {specAvoid runtimeAvoid : List String}
    {source specCandidate runtimeCandidate : Atom}
    (specVariant : TypeCandidateAlphaVariantRel specAvoid source specCandidate)
    (runtimeVariant : TypeCandidateAlphaVariantRel runtimeAvoid source
      runtimeCandidate)
    (notFunction : ¬∃ argumentTypes returnType,
      FunctionTypeRel source argumentTypes returnType) :
    PreparedCandidateSingletonRuntimeRel oracle space observationScope
      expression expectedType incoming initialPresentation env world
      runtimeInitial runtimeExpression runtimeArguments runtimeExpected
      allowExtraArguments specCandidate (toLeaTTaAtom runtimeCandidate) := by
  have runtimeNotFunction :=
    TypeCandidateAlphaVariantRel.notFunction runtimeVariant notFunction
  exact PreparedCandidateSingletonRuntimeRel.ofNonFunction
    (scanFunctionTypeCandidatesForExpectedFrom_singleton_nonFunction
      runtimeNotFunction)
    (TypeCandidateAlphaVariantRel.notFunction specVariant notFunction)

/-- Wrong arity yields the singleton incorrect-arity block on both sides and
is globally incompatible with a prepared success by arrow uniqueness. -/
theorem PreparedCandidateSingletonRuntimeRel.ofWrongArity
    {oracle : TypePreparationOracle}
    {space : Space} {observationScope : List String}
    {expression expectedType : Atom} {incoming : Bindings}
    {initialPresentation : TypeSubst}
    {env : Metta.Minimal.MinEnv} {world : Metta.Minimal.World}
    {runtimeInitial : Metta.Bindings}
    {runtimeExpression : Metta.Atom}
    {runtimeArguments : List Metta.Atom} {runtimeExpected : Metta.Atom}
    {allowExtraArguments : Bool}
    {candidate : Atom} {runtimeCandidate : Metta.Atom}
    {operator returnType : Atom} {arguments argumentTypes : List Atom}
    (scanEquation :
      Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom env world
        runtimeExpression runtimeArguments runtimeExpected allowExtraArguments
          runtimeInitial [runtimeCandidate] =
        .exhausted [.ordinary .incorrectArity] false)
    (expressionEquation : expression = .expression (operator :: arguments))
    (functionType : FunctionTypeRel candidate argumentTypes returnType)
    (arity : arguments.length ≠ argumentTypes.length) :
    PreparedCandidateSingletonRuntimeRel oracle space observationScope
      expression expectedType incoming initialPresentation env world
      runtimeInitial runtimeExpression runtimeArguments runtimeExpected
      allowExtraArguments candidate runtimeCandidate := by
  unfold PreparedCandidateSingletonRuntimeRel
  rw [scanEquation]
  exact ⟨argumentTypes, returnType,
    [mkError expression .incorrectNumberOfArguments], functionType,
    preparedCandidateFailure_wrongArity expressionEquation functionType arity,
    .cons .incorrectArity .nil⟩

/-- A translated arrow with the wrong strict arity produces exactly one
ordinary incorrect-arity diagnostic. -/
theorem scanFunctionTypeCandidatesForExpectedFrom_singleton_wrongArity
    {env : Metta.Minimal.MinEnv} {world : Metta.Minimal.World}
    {runtimeInitial : Metta.Bindings}
    {expression expectedType candidate returnType : Atom}
    {arguments argumentTypes : List Atom}
    (functionType : FunctionTypeRel candidate argumentTypes returnType)
    (arity : arguments.length ≠ argumentTypes.length) :
    Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom env world
      (toLeaTTaAtom expression) (toLeaTTaAtoms arguments)
      (toLeaTTaAtom expectedType) false runtimeInitial
        [toLeaTTaAtom candidate] =
        .exhausted [.ordinary .incorrectArity] false := by
  have candidateEquation :
      toLeaTTaAtom candidate =
        .expr (.sym "->" ::
          (toLeaTTaAtoms argumentTypes ++ [toLeaTTaAtom returnType])) := by
    rw [FunctionTypeRel] at functionType
    rw [functionType]
    simp [toLeaTTaAtom, toLeaTTaAtoms, List.map_append]
  simp [Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom,
    candidateEquation, arity,
    Metta.Minimal.ExpectedFunctionTypeScanOutcome.prependError,
    toLeaTTaAtoms_eq_map]

/-- Under strict arity, structural translation exposes the same singleton
incorrect-arity block as the published classifier. -/
theorem PreparedCandidateSingletonRuntimeRel.ofTranslatedWrongArity
    {oracle : TypePreparationOracle}
    {space : Space} {observationScope : List String}
    {expression expectedType : Atom} {incoming : Bindings}
    {initialPresentation : TypeSubst}
    {env : Metta.Minimal.MinEnv} {world : Metta.Minimal.World}
    {runtimeInitial : Metta.Bindings}
    {operator returnType candidate : Atom}
    {arguments argumentTypes : List Atom}
    (expressionEquation : expression = .expression (operator :: arguments))
    (functionType : FunctionTypeRel candidate argumentTypes returnType)
    (arity : arguments.length ≠ argumentTypes.length) :
    PreparedCandidateSingletonRuntimeRel oracle space observationScope
      expression expectedType incoming initialPresentation env world
      runtimeInitial (toLeaTTaAtom expression) (toLeaTTaAtoms arguments)
      (toLeaTTaAtom expectedType) false candidate (toLeaTTaAtom candidate) := by
  apply PreparedCandidateSingletonRuntimeRel.ofWrongArity
    (operator := operator) (arguments := arguments)
    (argumentTypes := argumentTypes) (returnType := returnType)
  · exact scanFunctionTypeCandidatesForExpectedFrom_singleton_wrongArity
      functionType arity
  · exact expressionEquation
  · exact functionType
  · exact arity

/-- Independent alpha-localizations of a wrong-arity arrow preserve both
the strict rejection and the single observable diagnostic. -/
theorem PreparedCandidateSingletonRuntimeRel.ofAlphaWrongArity
    {oracle : TypePreparationOracle}
    {space : Space} {observationScope : List String}
    {expression expectedType operator source returnType : Atom}
    {incoming : Bindings} {initialPresentation : TypeSubst}
    {arguments argumentTypes : List Atom}
    {env : Metta.Minimal.MinEnv} {world : Metta.Minimal.World}
    {runtimeInitial : Metta.Bindings}
    {specAvoid runtimeAvoid : List String}
    {specCandidate runtimeCandidate : Atom}
    (expressionEquation : expression = .expression (operator :: arguments))
    (functionType : FunctionTypeRel source argumentTypes returnType)
    (arity : arguments.length ≠ argumentTypes.length)
    (specVariant : TypeCandidateAlphaVariantRel specAvoid source specCandidate)
    (runtimeVariant : TypeCandidateAlphaVariantRel runtimeAvoid source
      runtimeCandidate) :
    PreparedCandidateSingletonRuntimeRel oracle space observationScope
      expression expectedType incoming initialPresentation env world
      runtimeInitial (toLeaTTaAtom expression) (toLeaTTaAtoms arguments)
      (toLeaTTaAtom expectedType) false specCandidate
      (toLeaTTaAtom runtimeCandidate) := by
  rcases specVariant with
    ⟨specRename, _specInjective, rfl, _specFresh⟩
  rcases runtimeVariant with
    ⟨runtimeRename, _runtimeInjective, rfl, _runtimeFresh⟩
  have specFunction : FunctionTypeRel (renameTypeVars specRename source)
      (argumentTypes.map (renameTypeVars specRename))
      (renameTypeVars specRename returnType) :=
    (functionTypeRel_renameTypeVars_iff specRename source _ _).2
      ⟨argumentTypes, returnType, functionType, rfl, rfl⟩
  have runtimeFunction : FunctionTypeRel (renameTypeVars runtimeRename source)
      (argumentTypes.map (renameTypeVars runtimeRename))
      (renameTypeVars runtimeRename returnType) :=
    (functionTypeRel_renameTypeVars_iff runtimeRename source _ _).2
      ⟨argumentTypes, returnType, functionType, rfl, rfl⟩
  have specArity : arguments.length ≠
      (argumentTypes.map (renameTypeVars specRename)).length := by
    simpa using arity
  have runtimeArity : arguments.length ≠
      (argumentTypes.map (renameTypeVars runtimeRename)).length := by
    simpa using arity
  apply PreparedCandidateSingletonRuntimeRel.ofWrongArity
    (operator := operator) (arguments := arguments)
    (argumentTypes := argumentTypes.map (renameTypeVars specRename))
    (returnType := renameTypeVars specRename returnType)
  · exact scanFunctionTypeCandidatesForExpectedFrom_singleton_wrongArity
      runtimeFunction runtimeArity
  · exact expressionEquation
  · exact specFunction
  · exact specArity

/-- A singleton arity-aligned function whose complete branch traversal has no
surviving return presentation is classified by the exact nonempty error block
assembled by `preparedCandidateFailure_runtime`. -/
theorem PreparedCandidateSingletonRuntimeRel.ofInapplicable
    {oracle : TypePreparationOracle}
    (functional : TypePreparationFunctional oracle)
    {space : Space} {observationScope : List String}
    {expression expectedType : Atom} {incoming : Bindings}
    {initialPresentation : TypeSubst}
    (initial : InitialTypeBindingPresentationRel initialPresentation incoming)
    {env : Metta.Minimal.MinEnv} (index : TypeEnvironmentRel space env)
    {world : Metta.Minimal.World}
    {runtimeInitial : Metta.Bindings}
    {runtimeExpression : Metta.Atom}
    {runtimeArguments : List Metta.Atom} {runtimeExpected : Metta.Atom}
    {allowExtraArguments : Bool}
    {candidate : Atom} {runtimeCandidate : Metta.Atom}
    {operator returnType : Atom} {arguments argumentTypes : List Atom}
    {candidateLists : List (List Atom)}
    {argumentOutcome : ArgumentCandidateListsBranchOutcome}
    {returnOutcome : ExpectedReturnBranchOutcome}
    {runtimeArgumentOutcome : Metta.Minimal.TypeCheckArgsBranchResult}
    {runtimeReturnOutcome : Metta.Minimal.ExpectedReturnBranchScanResult}
    (scanEquation :
      Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom env world
        runtimeExpression runtimeArguments runtimeExpected allowExtraArguments
          runtimeInitial [runtimeCandidate] =
        .exhausted
          ((runtimeArgumentOutcome.errors.map fun diagnostic =>
              .ordinary diagnostic.toFunctionTypeError) ++
            runtimeReturnOutcome.errors)
          false)
    (expressionEquation : expression = .expression (operator :: arguments))
    (functionType : FunctionTypeRel candidate argumentTypes returnType)
    (arity : arguments.length = argumentTypes.length)
    (prepared : PreparedArgumentPackageCandidates oracle space
      (typeServicePrivateAvoid space expression expectedType incoming)
      argumentTypes arguments candidateLists)
    (separated : FreshFamiliesSeparated [candidate] candidateLists.flatten)
    (argumentScan : ArgumentCandidateListsBranchScanRel argumentTypes
      candidateLists 0 initialPresentation argumentOutcome)
    (argumentRuntime : ScopedArgumentBranchOutcomeRuntimeRel
      observationScope argumentOutcome runtimeArgumentOutcome)
    (returnScan : ExpectedReturnBranchScanRel expectedType returnType
      argumentOutcome.successes returnOutcome)
    (returnRuntime : ScopedExpectedReturnBranchOutcomeRuntimeRel
      observationScope returnOutcome runtimeReturnOutcome)
    (notSelected : returnOutcome.selected = none) :
    PreparedCandidateSingletonRuntimeRel oracle space observationScope
      expression expectedType incoming initialPresentation env world
      runtimeInitial runtimeExpression runtimeArguments runtimeExpected
      allowExtraArguments candidate runtimeCandidate := by
  obtain ⟨failure, errorsRuntime⟩ :=
    preparedCandidateFailure_runtime functional index expressionEquation
      functionType arity prepared separated initial argumentScan argumentRuntime
        returnScan returnRuntime notSelected
  unfold PreparedCandidateSingletonRuntimeRel
  rw [scanEquation]
  exact ⟨argumentTypes, returnType,
    candidateApplicabilityErrors expression argumentOutcome returnOutcome,
    functionType, failure, errorsRuntime⟩

/-- A strict-arity runtime function candidate is classified completely from
the localized branch and return correspondences.

The theorem performs no second argument-scan induction.  It obtains the one
specification traversal corresponding to the runtime's branch-valued worker,
then cases only on the related optional selected return.  `some` assembles the
successful policy and presentation; `none` assembles the complete nonempty
argument-plus-return error block. -/
theorem PreparedCandidateSingletonRuntimeRel.ofStrictFunction
    {oracle : TypePreparationOracle}
    (functional : TypePreparationFunctional oracle)
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env)
    {world : Metta.Minimal.World}
    (realization : TypePreparationRuntimeRealization oracle space world)
    {expression expectedType incomingFunction returnType : Atom}
    {incoming : Bindings}
    {initialPresentation : TypeSubst} {runtimeInitial : Metta.Bindings}
    (initial : InitialTypeBindingPresentationRel initialPresentation incoming)
    (inputState : TypePresentationSimulationState initialPresentation
      incoming runtimeInitial)
    {operator : Atom} {arguments argumentTypes : List Atom}
    {candidateLists : List (List Atom)}
    {permutation : Equiv.Perm String}
    {rawTheoryScope publicScope observationScope : List String}
    (expressionEquation : expression = .expression (operator :: arguments))
    (functionType : FunctionTypeRel incomingFunction argumentTypes returnType)
    (arity : arguments.length = argumentTypes.length)
    (runtimePrepared : RuntimePreparedArgumentPackageCandidates oracle space
      env world
      (typeServicePrivateAvoid space expression expectedType incoming)
      argumentTypes arguments candidateLists)
    (separated : FreshFamiliesSeparated
      [renameTypeVars permutation incomingFunction] candidateLists.flatten)
    (signatureGenerated : CandidateGeneratedAt argumentTypes.length
      incomingFunction)
    (publicStaticProtected : ∀ name, name ∈ publicScope →
      name ∈ typeServicePrivateAvoid space expression expectedType incoming ∨
        name ∈ TypeSubst.typeVars incomingFunction)
    (theoryStaticProtected : ∀ name, name ∈ rawTheoryScope →
      name ∈ typeServicePrivateAvoid space expression expectedType incoming ∨
        name ∈ TypeSubst.typeVars incomingFunction)
    (publicRuntimeCovered : ∀ name, name ∈ publicScope →
      (name ∈ Metta.Minimal.applicationTypeInferenceScopeFrom
          (toLeaTTaAtom expectedType) (toLeaTTaAtoms arguments)
            runtimeInitial ∨
        name ∈ (toLeaTTaAtoms argumentTypes).flatMap Metta.Atom.vars ∨
        name ∈ env.atoms.flatMap Metta.Atom.vars) ∨
          name ∈ TypeSubst.typeVars incomingFunction)
    (theoryRuntimeCovered : ∀ name, name ∈ rawTheoryScope →
      (name ∈ Metta.Minimal.applicationTypeInferenceScopeFrom
          (toLeaTTaAtom expectedType) (toLeaTTaAtoms arguments)
            runtimeInitial ∨
        name ∈ (toLeaTTaAtoms argumentTypes).flatMap Metta.Atom.vars ∨
        name ∈ env.atoms.flatMap Metta.Atom.vars) ∨
          name ∈ TypeSubst.typeVars incomingFunction)
    (formalsObserved : ∀ name,
      name ∈ TypeSubst.typeVarsList argumentTypes →
        name ∈ rawTheoryScope)
    (formalsPublic : ∀ name,
      name ∈ TypeSubst.typeVarsList argumentTypes →
        name ∈ publicScope)
    (observationInTheory : ∀ name, name ∈ observationScope →
      name ∈ rawTheoryScope)
    (initialPublic : ∀ name,
      name ∈ specBindingVars (⟨initialPresentation, []⟩ : Bindings) →
        name ∈ publicScope)
    (initialFixed : ∀ name,
      name ∈ specBindingVars (⟨initialPresentation, []⟩ : Bindings) →
        permutation name = name)
    (scopeFixed : ∀ name, name ∈ observationScope →
      permutation name = name)
    (candidatesFixed : ∀ candidate ∈ candidateLists.flatten,
      renameTypeVars permutation candidate = candidate)
    (expectedFixed : renameTypeVars permutation expectedType = expectedType)
    (returnConstraintObserved : ∀ name,
      name ∈ TypeSubst.typeVars expectedType ++
          TypeSubst.typeVars returnType →
        name ∈ rawTheoryScope)
    (returnObserved : ∀ name,
      name ∈ TypeSubst.typeVars returnType → name ∈ rawTheoryScope)
    (returnDisjoint : VarsDisjoint expectedType returnType) :
    PreparedCandidateSingletonRuntimeRel oracle space observationScope
      expression expectedType incoming initialPresentation env world
      runtimeInitial (toLeaTTaAtom expression) (toLeaTTaAtoms arguments)
      (toLeaTTaAtom expectedType) false
      (renameTypeVars permutation incomingFunction)
      (toLeaTTaAtom incomingFunction) := by
  have initialStaticCovered : ∀ name,
      name ∈ specBindingVars (⟨initialPresentation, []⟩ : Bindings) →
        name ∈ typeServicePrivateAvoid space expression expectedType incoming := by
    intro name member
    exact List.mem_append_right _ (initial.support name member)
  have initialTwoHistory : TwoHistoryScopedTypePresentationSimulationState
      rawTheoryScope publicScope 0 [] [] initialPresentation
        initialPresentation runtimeInitial :=
    twoHistoryScopedTypePresentationSimulationState_initial
      rawTheoryScope publicScope inputState initialPublic
  have initialPermutation : TypePresentationPermutationState permutation
      initialPresentation initialPresentation :=
    typePresentationPermutationState_of_support_fixed initial.normal initialFixed
  obtain ⟨argumentOutcome, returnOutcome, argumentScan, argumentRuntime,
      returnScan, returnRuntime⟩ :=
    localizedPreparedApplicationBranches_exactConformance functional index
      realization runtimePrepared initialTwoHistory initialStaticCovered
      initialPermutation signatureGenerated publicStaticProtected
      theoryStaticProtected publicRuntimeCovered theoryRuntimeCovered
      formalsObserved formalsPublic observationInTheory scopeFixed
      candidatesFixed expectedFixed returnConstraintObserved returnObserved
      returnDisjoint
  have localizedFunction : FunctionTypeRel
      (renameTypeVars permutation incomingFunction)
      (argumentTypes.map (renameTypeVars permutation))
      (renameTypeVars permutation returnType) :=
    (functionTypeRel_renameTypeVars_iff permutation incomingFunction
      (argumentTypes.map (renameTypeVars permutation))
      (renameTypeVars permutation returnType)).2
        ⟨argumentTypes, returnType, functionType, rfl, rfl⟩
  have localizedPrepared : PreparedArgumentPackageCandidates oracle space
      (typeServicePrivateAvoid space expression expectedType incoming)
      (argumentTypes.map (renameTypeVars permutation)) arguments
      candidateLists :=
    runtimePrepared.prepared.reformalize localizedFunction separated
  have localizedArity :
      arguments.length =
        (argumentTypes.map (renameTypeVars permutation)).length := by
    simpa using arity
  have runtimeFunctionEquation :
      toLeaTTaAtom incomingFunction =
        .expr (.sym "->" ::
          (toLeaTTaAtoms argumentTypes ++ [toLeaTTaAtom returnType])) := by
    rw [FunctionTypeRel] at functionType
    rw [functionType]
    simp [toLeaTTaAtoms, toLeaTTaAtom, List.map_append]
  let runtimeArgumentOutcome :=
    Metta.Minimal.typeCheckArgsBranchesScoped env world
      (toLeaTTaAtoms argumentTypes)
      (Metta.Minimal.applicationTypeInferenceScopeFrom
        (toLeaTTaAtom expectedType) (toLeaTTaAtoms arguments)
          runtimeInitial)
      0 runtimeInitial (toLeaTTaAtoms arguments)
  let runtimeReturnOutcome :=
    Metta.Minimal.scanExpectedReturnBranches
      (toLeaTTaAtom expectedType) (toLeaTTaAtom returnType)
      runtimeArgumentOutcome.successes
  change ScopedArgumentBranchOutcomeRuntimeRel observationScope
      argumentOutcome runtimeArgumentOutcome at argumentRuntime
  change CoherentLocalizedExpectedReturnRuntimeRel permutation rawTheoryScope
      observationScope returnOutcome runtimeReturnOutcome at returnRuntime
  have scopedReturnRuntime : ScopedExpectedReturnBranchOutcomeRuntimeRel
      observationScope returnOutcome runtimeReturnOutcome :=
    returnRuntime.toScoped scopeFixed
  have selectedRelation := returnRuntime.selected
  cases specSelected : returnOutcome.selected with
  | none =>
      cases runtimeSelected : runtimeReturnOutcome.selected with
      | none =>
          have runtimeSelectedDirect :
              (Metta.Minimal.scanExpectedReturnBranches
                (toLeaTTaAtom expectedType) (toLeaTTaAtom returnType)
                (Metta.Minimal.typeCheckArgsBranchesScoped env world
                  (toLeaTTaAtoms argumentTypes)
                  (Metta.Minimal.applicationTypeInferenceScopeFrom
                    (toLeaTTaAtom expectedType) (toLeaTTaAtoms arguments)
                      runtimeInitial)
                  0 runtimeInitial
                  (toLeaTTaAtoms arguments)).successes).selected = none := by
            simpa [runtimeReturnOutcome, runtimeArgumentOutcome] using
              runtimeSelected
          simp only [toLeaTTaAtoms_eq_map] at runtimeSelectedDirect
          have scanEquation :
              Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom env world
                (toLeaTTaAtom expression) (toLeaTTaAtoms arguments)
                (toLeaTTaAtom expectedType) false
                runtimeInitial [toLeaTTaAtom incomingFunction] =
              .exhausted
                ((runtimeArgumentOutcome.errors.map fun diagnostic =>
                    .ordinary diagnostic.toFunctionTypeError) ++
                  runtimeReturnOutcome.errors)
                false := by
            simp [Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom,
              runtimeFunctionEquation, arity]
            rw [runtimeSelectedDirect]
            simp [Metta.Minimal.ExpectedFunctionTypeScanOutcome.prependErrors,
              runtimeReturnOutcome, runtimeArgumentOutcome,
              toLeaTTaAtoms_eq_map]
          exact PreparedCandidateSingletonRuntimeRel.ofInapplicable
            functional initial index scanEquation expressionEquation
            localizedFunction localizedArity localizedPrepared separated
            argumentScan argumentRuntime returnScan scopedReturnRuntime
              specSelected
      | some runtimeBindings =>
          rw [specSelected, runtimeSelected] at selectedRelation
          cases selectedRelation
  | some privatePresentation =>
      cases runtimeSelected : runtimeReturnOutcome.selected with
      | none =>
          rw [specSelected, runtimeSelected] at selectedRelation
          cases selectedRelation
      | some runtimeBindings =>
          have runtimeSelectedDirect :
              (Metta.Minimal.scanExpectedReturnBranches
                (toLeaTTaAtom expectedType) (toLeaTTaAtom returnType)
                (Metta.Minimal.typeCheckArgsBranchesScoped env world
                  (toLeaTTaAtoms argumentTypes)
                  (Metta.Minimal.applicationTypeInferenceScopeFrom
                    (toLeaTTaAtom expectedType) (toLeaTTaAtoms arguments)
                      runtimeInitial)
                  0 runtimeInitial
                  (toLeaTTaAtoms arguments)).successes).selected =
                some runtimeBindings := by
            simpa [runtimeReturnOutcome, runtimeArgumentOutcome] using
              runtimeSelected
          simp only [toLeaTTaAtoms_eq_map] at runtimeSelectedDirect
          let runtime : Metta.Minimal.SelectedFunctionType :=
            ⟨toLeaTTaAtom incomingFunction, toLeaTTaAtoms argumentTypes,
              toLeaTTaAtom returnType, runtimeBindings⟩
          have scanEquation :
              Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom env world
                (toLeaTTaAtom expression) (toLeaTTaAtoms arguments)
                (toLeaTTaAtom expectedType) false
                runtimeInitial [toLeaTTaAtom incomingFunction] =
                  .selected runtime := by
            simp [Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom,
              runtimeFunctionEquation, arity]
            rw [runtimeSelectedDirect]
            simp [runtime, toLeaTTaAtoms_eq_map, runtimeFunctionEquation]
          rw [specSelected, runtimeSelected] at selectedRelation
          cases selectedRelation with
          | some selectedCoherent =>
              have coherent : SelectedTypePolicyPresentationRuntimeRel
                  observationScope
                  ⟨renameTypeVars permutation incomingFunction,
                    argumentTypes.map (renameTypeVars permutation),
                    renameTypeVars permutation returnType,
                    localizedFunction⟩
                  privatePresentation runtime := by
                rcases selectedCoherent with
                  ⟨scopeInTheory, rawPresentation,
                    presentationPermutation, rawRuntime⟩
                refine ⟨permutation, rawTheoryScope, rawPresentation,
                  ?_, ?_, ?_, ?_, scopeFixed, scopeInTheory, ?_,
                  presentationPermutation, ?_⟩
                · change FunctionTypeRel
                    (fromLeaTTaAtom (toLeaTTaAtom incomingFunction))
                    (fromLeaTTaAtoms (toLeaTTaAtoms argumentTypes))
                    (fromLeaTTaAtom (toLeaTTaAtom returnType))
                  rw [fromLeaTTaAtom_toLeaTTaAtom,
                    fromLeaTTaAtoms_toLeaTTaAtoms,
                    fromLeaTTaAtom_toLeaTTaAtom]
                  exact functionType
                · simp [runtime]
                · simp [runtime]
                · simp [runtime]
                · intro name member
                  have incomingMember :
                      name ∈ TypeSubst.typeVars incomingFunction := by
                    simpa [runtime] using member
                  have sourceShape := functionType
                  rw [FunctionTypeRel] at sourceShape
                  rw [sourceShape] at incomingMember
                  have tailMember : name ∈
                      TypeSubst.typeVarsList (argumentTypes ++ [returnType]) := by
                    simpa [TypeSubst.typeVars, TypeSubst.typeVarsList] using
                      incomingMember
                  rw [typeVarsList_append, List.mem_append] at tailMember
                  rcases tailMember with argumentMember | returnMember
                  · exact formalsObserved name argumentMember
                  · exact returnObserved name (by
                      simpa [TypeSubst.typeVarsList] using returnMember)
                · simpa [runtime] using rawRuntime
              obtain ⟨output, applicable, outcome⟩ :=
                preparedCandidateSuccess_runtime expressionEquation
                  localizedFunction localizedArity localizedPrepared separated
                  initial argumentScan returnScan specSelected coherent
              exact PreparedCandidateSingletonRuntimeRel.ofSelected
                scanEquation applicable outcome

/-- Two independently generated presentations of one strict-arity arrow are
classified without identifying their private spellings.  The common
permutation fixes the call-boundary variable atoms and every prepared
argument candidate; terminal-position provenance supplies the remaining
signature/candidate separation. -/
theorem PreparedCandidateSingletonRuntimeRel.ofAlphaStrictFunction
    {oracle : TypePreparationOracle}
    (functional : TypePreparationFunctional oracle)
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env)
    {world : Metta.Minimal.World}
    (realization : TypePreparationRuntimeRealization oracle space world)
    {expression expectedType operator source returnType : Atom}
    {incoming : Bindings} {initialPresentation : TypeSubst}
    {runtimeInitial : Metta.Bindings}
    (initial : InitialTypeBindingPresentationRel initialPresentation incoming)
    (inputState : TypePresentationSimulationState initialPresentation
      incoming runtimeInitial)
    {arguments argumentTypes : List Atom}
    {observationScope : List String}
    {runtimeAvoid : List String} {specCandidate runtimeCandidate : Atom}
    (expressionEquation : expression = .expression (operator :: arguments))
    (functionType : FunctionTypeRel source argumentTypes returnType)
    (arity : arguments.length = argumentTypes.length)
    (specVariant : TypeCandidateAlphaVariantRel
      (typeServicePrivateAvoid space expression expectedType incoming)
      source specCandidate)
    (runtimeVariant : TypeCandidateAlphaVariantRel runtimeAvoid source
      runtimeCandidate)
    (runtimeCallCovered : ∀ name,
      name ∈ TypeSubst.typeVars expectedType ++
          TypeSubst.typeVarsList arguments →
        name ∈ runtimeAvoid)
    (runtimeInitialAvoidCovered : ∀ name,
      name ∈ specBindingVars
          (⟨initialPresentation, []⟩ : Bindings) →
        name ∈ runtimeAvoid)
    (runtimeInitialBindingCovered : ∀ name,
      name ∈ specBindingVars
          (⟨initialPresentation, []⟩ : Bindings) →
        name ∈ runtimeInitial.vars)
    (specObservationCovered : ∀ name, name ∈ observationScope →
      name ∈ typeServicePrivateAvoid space expression expectedType incoming)
    (runtimeObservationCovered : ∀ name, name ∈ observationScope →
      name ∈ runtimeAvoid)
    (runtimeObservationProtected : ∀ name, name ∈ observationScope →
      name ∈ Metta.Minimal.applicationTypeInferenceScope
          (toLeaTTaAtom expectedType) (toLeaTTaAtoms arguments) ∨
        name ∈ env.atoms.flatMap Metta.Atom.vars)
    (specGenerated : CandidateGeneratedAt arguments.length specCandidate)
    (runtimeGenerated : CandidateGeneratedAt arguments.length
      runtimeCandidate) :
    PreparedCandidateSingletonRuntimeRel oracle space observationScope
      expression expectedType incoming initialPresentation env world
      runtimeInitial (toLeaTTaAtom expression)
      (toLeaTTaAtoms arguments) (toLeaTTaAtom expectedType) false
      specCandidate (toLeaTTaAtom runtimeCandidate) := by
  let applicationScope :=
    TypeSubst.typeVars expectedType ++ TypeSubst.typeVarsList arguments
  let callScope := applicationScope ++
    specBindingVars (⟨initialPresentation, []⟩ : Bindings)
  let fixedScope := callScope ++ observationScope
  have runtimeVariantCopy := runtimeVariant
  rcases runtimeVariantCopy with
    ⟨runtimeRename, _runtimeInjective, runtimeEquation, _runtimeFresh⟩
  have runtimeFunction : FunctionTypeRel runtimeCandidate
      (argumentTypes.map (renameTypeVars runtimeRename))
      (renameTypeVars runtimeRename returnType) := by
    rw [runtimeEquation]
    exact (functionTypeRel_renameTypeVars_iff runtimeRename source _ _).2
      ⟨argumentTypes, returnType, functionType, rfl, rfl⟩
  have runtimeArity : arguments.length =
      (argumentTypes.map (renameTypeVars runtimeRename)).length := by
    simpa using arity
  obtain ⟨candidateLists, runtimePrepared⟩ :=
    runtimePreparedArgumentPackageCandidates_exists index realization
      (typeServicePrivateAvoid space expression expectedType incoming)
      (argumentTypes.map (renameTypeVars runtimeRename)) arguments
  have specSeparated : FreshFamiliesSeparated [specCandidate]
      candidateLists.flatten := by
    rcases specGenerated with ⟨signatureAvoid, signatureSource,
      signatureEquation⟩
    have separated := runtimePrepared.freshLocalizedCandidateSeparated
      runtimeArity signatureAvoid signatureSource
    simpa only [← runtimeArity, ← signatureEquation] using separated
  have runtimeSeparated : FreshFamiliesSeparated [runtimeCandidate]
      candidateLists.flatten := by
    rcases runtimeGenerated with ⟨signatureAvoid, signatureSource,
      signatureEquation⟩
    have separated := runtimePrepared.freshLocalizedCandidateSeparated
      runtimeArity signatureAvoid signatureSource
    simpa only [← runtimeArity, ← signatureEquation] using separated
  have specCallCovered : ∀ name, name ∈ callScope →
      name ∈ typeServicePrivateAvoid space expression expectedType incoming := by
    intro name member
    dsimp [callScope, applicationScope] at member
    rw [typeServicePrivateAvoid]
    rcases List.mem_append.mp member with applicationMember | initialMember
    · apply List.mem_append_left
      rw [typeServiceObservationScope]
      rcases List.mem_append.mp applicationMember with
        expectedMember | argumentMember
      · exact typeVars_mem_typeVarsList_of_mem
          (atoms := space.atoms ++ [expression, expectedType])
          (atom := expectedType) (by simp) name expectedMember
      · have expressionMember : name ∈ TypeSubst.typeVars expression := by
          rw [expressionEquation]
          simp only [TypeSubst.typeVars, TypeSubst.typeVarsList,
            List.mem_append]
          exact Or.inr argumentMember
        exact typeVars_mem_typeVarsList_of_mem
          (atoms := space.atoms ++ [expression, expectedType])
          (atom := expression) (by simp) name expressionMember
    · exact List.mem_append_right _ (initial.support name initialMember)
  have specFixedSeparated : FreshFamiliesSeparated [specCandidate]
      (fixedScope.map Atom.var) :=
    TypeCandidateAlphaVariantRel.separated_from_variable_atoms
      specVariant (by
        intro name member
        rw [List.mem_append] at member
        exact member.elim (specCallCovered name) (specObservationCovered name))
  have runtimeFixedSeparated : FreshFamiliesSeparated [runtimeCandidate]
      (fixedScope.map Atom.var) :=
    TypeCandidateAlphaVariantRel.separated_from_variable_atoms runtimeVariant (by
      intro name member
      rw [List.mem_append] at member
      exact member.elim
        (fun callMember => by
          rcases List.mem_append.mp callMember with
            applicationMember | initialMember
          · exact runtimeCallCovered name
              (by simpa [applicationScope] using applicationMember)
          · exact runtimeInitialAvoidCovered name initialMember)
        (runtimeObservationCovered name))
  have specCombined : FreshFamiliesSeparated [specCandidate]
      (candidateLists.flatten ++ fixedScope.map Atom.var) :=
    FreshFamiliesSeparated.append_right specSeparated specFixedSeparated
  have runtimeCombined : FreshFamiliesSeparated [runtimeCandidate]
      (candidateLists.flatten ++ fixedScope.map Atom.var) :=
    FreshFamiliesSeparated.append_right runtimeSeparated runtimeFixedSeparated
  obtain ⟨permutation, specPermutation, familyFixed⟩ :=
    Spec.Type.Presentation.SelectionEquivariance.TypeCandidateAlphaVariantRel.exists_permutation_fixing_family
      runtimeVariant specVariant runtimeCombined specCombined
  have candidatesFixed : ∀ candidate ∈ candidateLists.flatten,
      renameTypeVars permutation candidate = candidate := by
    intro candidate member
    exact familyFixed candidate (List.mem_append_left _ member)
  have callScopeFixed : ∀ name, name ∈ callScope → permutation name = name := by
    intro name member
    have variableFixed := familyFixed (.var name) (by
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨name,
        List.mem_append_left observationScope member, rfl⟩)
    simpa [renameTypeVars] using variableFixed
  have observationScopeFixed : ∀ name, name ∈ observationScope →
      permutation name = name := by
    intro name member
    have variableFixed := familyFixed (.var name) (by
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨name,
        List.mem_append_right callScope member, rfl⟩)
    simpa [renameTypeVars] using variableFixed
  have expectedFixed : renameTypeVars permutation expectedType = expectedType := by
    calc
      renameTypeVars permutation expectedType =
          renameTypeVars id expectedType :=
        renameTypeVars_congr_on_typeVars expectedType
          (fun name member => callScopeFixed name
            (List.mem_append_left _
              (List.mem_append_left _ member)))
      _ = expectedType := renameTypeVars_id expectedType
  have returnDisjoint : VarsDisjoint expectedType
      (renameTypeVars runtimeRename returnType) := by
    intro name expectedOccurrence returnOccurrence
    rw [LeaTTaTypePresentationExactConformance.toLeaTTaAtom_vars_eq_typeVars]
      at expectedOccurrence returnOccurrence
    have returnInSignature : name ∈ TypeSubst.typeVars runtimeCandidate :=
      FunctionTypeRel.returnVars_subset runtimeFunction name returnOccurrence
    exact TypeCandidateAlphaVariantRel.target_vars_fresh runtimeVariant name
      returnInSignature
      (runtimeCallCovered name (List.mem_append_left _ expectedOccurrence))
  have applicationBoundaryEquation :
      Metta.Minimal.applicationTypeInferenceScope
          (toLeaTTaAtom expectedType) (toLeaTTaAtoms arguments) =
        applicationScope := by
    simp only [Metta.Minimal.applicationTypeInferenceScope, applicationScope,
      LeaTTaTypePresentationExactConformance.toLeaTTaAtom_vars_eq_typeVars]
    exact congrArg₂ (· ++ ·) rfl
      (LeaTTaTypePresentationExactConformance.toLeaTTaAtoms_vars_eq_typeVars
        arguments)
  have localizedSeparated : FreshFamiliesSeparated
      [renameTypeVars permutation runtimeCandidate] candidateLists.flatten := by
    rw [← specPermutation]
    exact specSeparated
  have runtimeGenerated' : CandidateGeneratedAt
      (argumentTypes.map (renameTypeVars runtimeRename)).length
      runtimeCandidate := by
    rw [← runtimeArity]
    exact runtimeGenerated
  have classified : PreparedCandidateSingletonRuntimeRel oracle space
      observationScope
      expression expectedType incoming initialPresentation env world
      runtimeInitial (toLeaTTaAtom expression)
      (toLeaTTaAtoms arguments) (toLeaTTaAtom expectedType) false
      (renameTypeVars permutation runtimeCandidate)
      (toLeaTTaAtom runtimeCandidate) := by
    apply PreparedCandidateSingletonRuntimeRel.ofStrictFunction
      (permutation := permutation) functional index
      realization initial inputState expressionEquation runtimeFunction
      runtimeArity runtimePrepared
      localizedSeparated runtimeGenerated'
      (rawTheoryScope :=
        (observationScope ++ callScope) ++
          TypeSubst.typeVars runtimeCandidate)
      (publicScope := callScope ++ TypeSubst.typeVarsList
        (argumentTypes.map (renameTypeVars runtimeRename)))
      (observationScope := observationScope)
    · intro name member
      rcases List.mem_append.mp member with callMember | formalMember
      · exact Or.inl (specCallCovered name callMember)
      · exact Or.inr
          (FunctionTypeRel.argumentVars_subset runtimeFunction name formalMember)
    · intro name member
      rcases List.mem_append.mp member with observedOrCall | signatureMember
      · rcases List.mem_append.mp observedOrCall with
          observationMember | callMember
        · exact Or.inl (specObservationCovered name observationMember)
        · exact Or.inl (specCallCovered name callMember)
      · exact Or.inr signatureMember
    · intro name member
      rcases List.mem_append.mp member with callMember | formalMember
      · rcases List.mem_append.mp callMember with
          applicationMember | initialMember
        · apply Or.inl
          apply Or.inl
          rw [Metta.Minimal.applicationTypeInferenceScopeFrom,
            applicationBoundaryEquation]
          exact List.mem_append_left _ applicationMember
        · apply Or.inl
          apply Or.inl
          rw [Metta.Minimal.applicationTypeInferenceScopeFrom]
          exact List.mem_append_right _
            (runtimeInitialBindingCovered name initialMember)
      · exact Or.inl (Or.inr (Or.inl (by
          rw [LeaTTaTypePresentationExactConformance.toLeaTTaAtoms_vars_eq_typeVars]
          exact formalMember)))
    · intro name member
      rcases List.mem_append.mp member with observedOrCall | signatureMember
      · rcases List.mem_append.mp observedOrCall with
          observationMember | callMember
        · exact Or.inl ((runtimeObservationProtected name observationMember).elim
            (fun boundaryMember => Or.inl (by
              rw [Metta.Minimal.applicationTypeInferenceScopeFrom]
              exact List.mem_append_left _ boundaryMember))
            (fun environmentMember => Or.inr (Or.inr environmentMember)))
        · rcases List.mem_append.mp callMember with
            applicationMember | initialMember
          · apply Or.inl
            apply Or.inl
            rw [Metta.Minimal.applicationTypeInferenceScopeFrom,
              applicationBoundaryEquation]
            exact List.mem_append_left _ applicationMember
          · apply Or.inl
            apply Or.inl
            rw [Metta.Minimal.applicationTypeInferenceScopeFrom]
            exact List.mem_append_right _
              (runtimeInitialBindingCovered name initialMember)
      · exact Or.inr signatureMember
    · intro name member
      exact List.mem_append_right _
        (FunctionTypeRel.argumentVars_subset runtimeFunction name member)
    · intro _ member
      exact List.mem_append_right _ member
    · intro name member
      exact List.mem_append_left _
        (List.mem_append_left _ member)
    · intro name member
      exact List.mem_append_left _ (List.mem_append_right _ member)
    · intro name member
      exact callScopeFixed name (List.mem_append_right _ member)
    · exact observationScopeFixed
    · exact candidatesFixed
    · exact expectedFixed
    · intro name member
      rw [List.mem_append] at member
      rcases member with expectedMember | returnMember
      · exact List.mem_append_left _
          (List.mem_append_right observationScope
            (List.mem_append_left _
              (List.mem_append_left _ expectedMember)))
      · exact List.mem_append_right _
          (FunctionTypeRel.returnVars_subset runtimeFunction name
            returnMember)
    · intro name member
      exact List.mem_append_right _
        (FunctionTypeRel.returnVars_subset runtimeFunction name member)
    · exact returnDisjoint
  simpa only [← specPermutation] using classified

/-- Two ordered localization passes over the same raw operator list classify
every candidate pointwise.  Shape is decided on the shared raw source: a
non-arrow is tuple-eligible, a wrong-arity arrow contributes the exact arity
diagnostic, and an aligned arrow delegates to the complete prepared branch
and return classifier. -/
theorem alphaPreparedSingletonClassifications
    {oracle : TypePreparationOracle}
    (functional : TypePreparationFunctional oracle)
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env)
    {world : Metta.Minimal.World}
    (realization : TypePreparationRuntimeRealization oracle space world)
    {expression expectedType operator : Atom} {incoming : Bindings}
    {initialPresentation : TypeSubst} {runtimeInitial : Metta.Bindings}
    (initial : InitialTypeBindingPresentationRel initialPresentation incoming)
    (inputState : TypePresentationSimulationState initialPresentation
      incoming runtimeInitial)
    {arguments : List Atom} {observationScope runtimeAvoid : List String}
    {rawCandidates specCandidates runtimeCandidates : List Atom}
    (expressionEquation : expression = .expression (operator :: arguments))
    (runtimeCallCovered : ∀ name,
      name ∈ TypeSubst.typeVars expectedType ++
          TypeSubst.typeVarsList arguments →
        name ∈ runtimeAvoid)
    (specObservationCovered : ∀ name, name ∈ observationScope →
      name ∈ typeServicePrivateAvoid space expression expectedType incoming)
    (runtimeObservationCovered : ∀ name, name ∈ observationScope →
      name ∈ runtimeAvoid)
    (runtimeObservationProtected : ∀ name, name ∈ observationScope →
      name ∈ Metta.Minimal.applicationTypeInferenceScope
          (toLeaTTaAtom expectedType) (toLeaTTaAtoms arguments) ∨
        name ∈ env.atoms.flatMap Metta.Atom.vars)
    (runtimeInitialAvoidCovered : ∀ name,
      name ∈ specBindingVars (⟨initialPresentation, []⟩ : Bindings) →
        name ∈ runtimeAvoid)
    (runtimeInitialBindingCovered : ∀ name,
      name ∈ specBindingVars (⟨initialPresentation, []⟩ : Bindings) →
        name ∈ runtimeInitial.vars)
    (specVariants : List.Forall₂
      (TypeCandidateAlphaVariantRel
        (typeServicePrivateAvoid space expression expectedType incoming))
      rawCandidates specCandidates)
    (runtimeVariants : List.Forall₂
      (TypeCandidateAlphaVariantRel runtimeAvoid)
      rawCandidates runtimeCandidates)
    (specGenerated : CandidateFamilyGeneratedAt arguments.length
      specCandidates)
    (runtimeGenerated : CandidateFamilyGeneratedAt arguments.length
      runtimeCandidates) :
    List.Forall₂
      (PreparedCandidateSingletonRuntimeRel oracle space
        observationScope
        expression expectedType incoming initialPresentation env world
        runtimeInitial (toLeaTTaAtom expression)
        (toLeaTTaAtoms arguments) (toLeaTTaAtom expectedType) false)
      specCandidates (toLeaTTaAtoms runtimeCandidates) := by
  induction specVariants generalizing runtimeCandidates with
  | nil =>
      cases runtimeVariants
      exact .nil
  | @cons source specCandidate rawTail specTail specVariant specTailVariants
      inductionHypothesis =>
      cases runtimeVariants with
      | @cons _ runtimeCandidate _ runtimeTail runtimeVariant
          runtimeTailVariants =>
          have specHeadGenerated : CandidateGeneratedAt arguments.length
              specCandidate :=
            specGenerated specCandidate (by simp)
          have runtimeHeadGenerated : CandidateGeneratedAt arguments.length
              runtimeCandidate :=
            runtimeGenerated runtimeCandidate (by simp)
          have specTailGenerated : CandidateFamilyGeneratedAt arguments.length
              specTail := by
            intro candidate member
            exact specGenerated candidate (by simp [member])
          have runtimeTailGenerated : CandidateFamilyGeneratedAt
              arguments.length runtimeTail := by
            intro candidate member
            exact runtimeGenerated candidate (by simp [member])
          have headClassification : PreparedCandidateSingletonRuntimeRel
              oracle space observationScope
              expression expectedType incoming initialPresentation env world
              runtimeInitial
              (toLeaTTaAtom expression) (toLeaTTaAtoms arguments)
              (toLeaTTaAtom expectedType) false specCandidate
              (toLeaTTaAtom runtimeCandidate) := by
            by_cases functionShape : ∃ argumentTypes returnType,
                FunctionTypeRel source argumentTypes returnType
            · obtain ⟨argumentTypes, returnType, functionType⟩ := functionShape
              by_cases arity : arguments.length = argumentTypes.length
              · exact PreparedCandidateSingletonRuntimeRel.ofAlphaStrictFunction
                  functional index realization initial inputState
                  expressionEquation functionType arity specVariant
                  runtimeVariant runtimeCallCovered
                  runtimeInitialAvoidCovered runtimeInitialBindingCovered
                  specObservationCovered runtimeObservationCovered
                  runtimeObservationProtected
                  specHeadGenerated runtimeHeadGenerated
              · exact PreparedCandidateSingletonRuntimeRel.ofAlphaWrongArity
                  expressionEquation functionType arity specVariant
                  runtimeVariant
            · exact PreparedCandidateSingletonRuntimeRel.ofAlphaNonFunction
                specVariant runtimeVariant functionShape
          exact .cons headClassification
            (inductionHypothesis runtimeTailVariants specTailGenerated
              runtimeTailGenerated)

/-- Exact failed-candidate classifications assemble both the published
exhausted scan and its flat runtime readout.  Candidate blocks stay explicit
in the hypotheses; only the final outcome applies row-major flattening. -/
theorem FunctionCandidateScanOutcomeRuntimeRel.ofAllFailures
    {oracle : TypePreparationOracle}
    {space : Space} {observationScope : List String}
    {expression expectedType : Atom}
    {incoming : Bindings} {initialPresentation : TypeSubst}
    {candidates : List Atom}
    {summaries : List (List Atom × Bool)}
    {runtimeBlocks : List
      (List Metta.Minimal.ExpectedFunctionTypeError)}
    {runtimeErrors : List Metta.Minimal.ExpectedFunctionTypeError}
    {runtimeTuple : Bool}
    (failures : List.Forall₂
      (FunctionCandidateFailureRel
        (fun space expression candidate expectedType bindings outcome =>
          PreparedCandidateApplicabilityRel oracle space expression candidate
            expectedType bindings initialPresentation outcome)
        space expression expectedType incoming)
      candidates summaries)
    (blocks : CandidateErrorBlocksRuntimeRel expression
      (summaries.map Prod.fst) runtimeBlocks)
    (runtimeErrorsEquation : runtimeErrors = runtimeBlocks.flatten)
    (tupleEquation :
      functionCandidateFailureTupleEligible summaries = runtimeTuple) :
    FunctionCandidateScanRel
        (fun space expression candidate expectedType bindings outcome =>
          PreparedCandidateApplicabilityRel oracle space expression candidate
            expectedType bindings initialPresentation outcome)
        space expression expectedType incoming candidates
        (.exhausted (functionCandidateFailureErrors summaries)
          (functionCandidateFailureTupleEligible summaries)) ∧
      FunctionCandidateScanOutcomeRuntimeRel observationScope expression incoming
        (.exhausted (functionCandidateFailureErrors summaries)
          (functionCandidateFailureTupleEligible summaries))
        (.exhausted runtimeErrors runtimeTuple) := by
  constructor
  · exact FunctionCandidateScanRel.of_all_failures failures
  · apply FunctionCandidateScanOutcomeRuntimeRel.exhausted
    · rw [functionCandidateFailureErrors_eq_flatten_map_fst,
        runtimeErrorsEquation]
      exact blocks.flatten
    · exact tupleEquation

/-- An ordered scan may retain one additional producer-supplied fact about
its selected policy/runtime pair.  Exhaustion has no selected pair and
therefore carries only the established flat-error correspondence. -/
inductive FunctionCandidateScanOutcomeRuntimeRelWith
    (Success : SelectedTypePolicy →
      Metta.Minimal.SelectedFunctionType → Prop)
    (observationScope : List String)
    (expression : Atom) (incoming : Bindings) :
    FunctionCandidateScanOutcome →
      Metta.Minimal.ExpectedFunctionTypeScanOutcome → Prop where
  | success {policy : SelectedTypePolicy} {output : Bindings}
      {runtime : Metta.Minimal.SelectedFunctionType} :
      FunctionCandidateScanOutcomeRuntimeRel observationScope expression
        incoming (.success policy output) (.selected runtime) →
      Success policy runtime →
      FunctionCandidateScanOutcomeRuntimeRelWith Success observationScope
        expression incoming (.success policy output) (.selected runtime)
  | exhausted {specErrors : List Atom}
      {runtimeErrors : List Metta.Minimal.ExpectedFunctionTypeError}
      {specTuple runtimeTuple : Bool} :
      FunctionCandidateScanOutcomeRuntimeRel observationScope expression
        incoming (.exhausted specErrors specTuple)
          (.exhausted runtimeErrors runtimeTuple) →
      FunctionCandidateScanOutcomeRuntimeRelWith Success observationScope
        expression incoming (.exhausted specErrors specTuple)
          (.exhausted runtimeErrors runtimeTuple)

/-- Forgetting the selected-pair refinement recovers the ordinary outcome
correspondence. -/
theorem FunctionCandidateScanOutcomeRuntimeRelWith.toRuntimeRel
    {Success : SelectedTypePolicy →
      Metta.Minimal.SelectedFunctionType → Prop}
    {observationScope : List String} {expression : Atom}
    {incoming : Bindings} {specOutcome : FunctionCandidateScanOutcome}
    {runtimeOutcome : Metta.Minimal.ExpectedFunctionTypeScanOutcome}
    (relation : FunctionCandidateScanOutcomeRuntimeRelWith Success
      observationScope expression incoming specOutcome runtimeOutcome) :
    FunctionCandidateScanOutcomeRuntimeRel observationScope expression
      incoming specOutcome runtimeOutcome := by
  cases relation with
  | success base _ => exact base
  | exhausted base => exact base

/-- Refined scan correspondence weakens its public observation scope without
discarding the selected-pair fact. -/
theorem FunctionCandidateScanOutcomeRuntimeRelWith.mono
    {Success : SelectedTypePolicy →
      Metta.Minimal.SelectedFunctionType → Prop}
    {large small : List String} {expression : Atom}
    {incoming : Bindings} {specOutcome : FunctionCandidateScanOutcome}
    {runtimeOutcome : Metta.Minimal.ExpectedFunctionTypeScanOutcome}
    (relation : FunctionCandidateScanOutcomeRuntimeRelWith Success large
      expression incoming specOutcome runtimeOutcome)
    (subset : ∀ name, name ∈ small → name ∈ large) :
    FunctionCandidateScanOutcomeRuntimeRelWith Success small expression
      incoming specOutcome runtimeOutcome := by
  cases relation with
  | success base selected => exact .success (base.mono subset) selected
  | exhausted base => exact .exhausted (base.mono subset)

/-- An evaluator-aligned successful selection observes its complete selected
arrow in addition to the caller scope.  The ordinary coherent carrier stores
one permutation for both the selected arrow and its presentation.  Literal
arrow agreement from the aligned scan therefore forces that permutation to
fix every variable of the arrow, so no stronger runtime-binding carrier is
needed at the subsequent operator-head cast. -/
theorem FunctionCandidateScanOutcomeRuntimeRelWith.successBindingAtFunctionType
    {observationScope : List String} {expression : Atom}
    {incoming output : Bindings} {policy : SelectedTypePolicy}
    {runtime : Metta.Minimal.SelectedFunctionType}
    (relation : FunctionCandidateScanOutcomeRuntimeRelWith
      SelectedTypePolicyRuntimeExactRel observationScope expression incoming
      (.success policy output) (.selected runtime)) :
    ∃ presentation,
      (∀ valuation,
        TypeSubstSatisfied valuation presentation ↔
          TypeBindingSatisfied valuation output) ∧
      ScopedTypePresentationSimulationState
        (observationScope ++ TypeSubst.typeVars policy.functionType)
        presentation runtime.typeBindings := by
  cases relation with
  | success base aligned =>
      cases base with
      | success coherent _extension solutions =>
          rcases coherent with
            ⟨permutation, theoryScope, rawPresentation, _runtimeFunction,
              functionType, _argumentTypes, _returnType, scopeFixed,
              scopeInTheory, functionTypeObserved, presentationState,
              runtimePresentation⟩
          have rawFixed :
              renameTypeVars permutation
                  (fromLeaTTaAtom runtime.functionType) =
                fromLeaTTaAtom runtime.functionType :=
            functionType.symm.trans aligned.functionType
          have functionVarsFixed : ∀ name,
              name ∈ TypeSubst.typeVars policy.functionType →
                permutation name = name := by
            intro name member
            apply renameTypeVars_eq_self_fixed_on_typeVars permutation
              (fromLeaTTaAtom runtime.functionType) rawFixed
            simpa [aligned.functionType] using member
          have combinedFixed : ∀ name,
              name ∈ observationScope ++
                  TypeSubst.typeVars policy.functionType →
                permutation name = name := by
            intro name member
            rcases List.mem_append.mp member with publicMember | typeMember
            · exact scopeFixed name publicMember
            · exact functionVarsFixed name typeMember
          have combinedInTheory : ∀ name,
              name ∈ observationScope ++
                  TypeSubst.typeVars policy.functionType →
                name ∈ theoryScope := by
            intro name member
            rcases List.mem_append.mp member with publicMember | typeMember
            · exact scopeInTheory name publicMember
            · apply functionTypeObserved
              simpa [aligned.functionType] using typeMember
          exact ⟨_, solutions,
            presentationState.composeScopedRuntime combinedFixed
              (runtimePresentation.mono combinedInTheory)⟩

/-- Pointwise singleton classifications assemble into the complete ordered
runtime scan while threading any fact proved at the selected singleton.
This is the sole induction over candidate order: ordinary and evaluator-
aligned scans are projections of the same theorem. -/
theorem scanFunctionTypeCandidatesForExpected_runtime_with_success
    {oracle : TypePreparationOracle}
    {space : Space} {observationScope : List String}
    {expression expectedType : Atom} {incoming : Bindings}
    {initialPresentation : TypeSubst}
    {env : Metta.Minimal.MinEnv} {world : Metta.Minimal.World}
    {runtimeInitial : Metta.Bindings}
    {runtimeExpression : Metta.Atom}
    {runtimeArguments : List Metta.Atom} {runtimeExpected : Metta.Atom}
    {allowExtraArguments : Bool}
    {candidates : List Atom} {runtimeCandidates : List Metta.Atom}
    {Success : SelectedTypePolicy →
      Metta.Minimal.SelectedFunctionType → Prop}
    {CandidatePair : Atom → Metta.Atom → Prop}
    (classifications : List.Forall₂
      (PreparedCandidateSingletonRuntimeRel oracle space observationScope
        expression expectedType incoming initialPresentation env world
        runtimeInitial runtimeExpression
        runtimeArguments runtimeExpected allowExtraArguments)
      candidates runtimeCandidates)
    (pairs : List.Forall₂ CandidatePair candidates runtimeCandidates)
    (selectedWitness : ∀ {candidate runtimeCandidate policy output runtime},
      CandidatePair candidate runtimeCandidate →
      Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom env world
          runtimeExpression runtimeArguments runtimeExpected
          allowExtraArguments runtimeInitial [runtimeCandidate] =
        .selected runtime →
      PreparedCandidateApplicabilityRel oracle space expression candidate
        expectedType incoming initialPresentation (.success policy output) →
      FunctionCandidateScanOutcomeRuntimeRel observationScope expression
        incoming (.success policy output) (.selected runtime) →
      Success policy runtime) :
    ∃ outcome,
      FunctionCandidateScanRel
          (fun space expression candidate expectedType bindings outcome =>
            PreparedCandidateApplicabilityRel oracle space expression candidate
              expectedType bindings initialPresentation outcome)
          space expression expectedType incoming candidates outcome ∧
        FunctionCandidateScanOutcomeRuntimeRelWith Success observationScope
          expression incoming outcome
          (Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom env world
            runtimeExpression runtimeArguments runtimeExpected
            allowExtraArguments runtimeInitial runtimeCandidates) := by
  induction classifications with
  | nil =>
      cases pairs
      exact ⟨.exhausted [] false, .nil,
        .exhausted (.exhausted .nil rfl)⟩
  | @cons candidate runtimeCandidate candidates runtimeCandidates
      head _ inductionHypothesis =>
      cases pairs
      rename_i pairHead pairTail
      obtain ⟨tailOutcome, tailScan, tailRuntime⟩ :=
        inductionHypothesis pairTail
      generalize tailRuntimeEquation :
          Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom env world
            runtimeExpression runtimeArguments runtimeExpected
            allowExtraArguments runtimeInitial runtimeCandidates = tailRuntimeOutcome
        at tailRuntime ⊢
      unfold PreparedCandidateSingletonRuntimeRel at head
      generalize singletonEquation :
          Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom env world
            runtimeExpression runtimeArguments runtimeExpected
            allowExtraArguments runtimeInitial [runtimeCandidate] = singletonOutcome at head
      cases singletonOutcome with
      | selected runtime =>
          obtain ⟨policy, output, applicable, selectedRuntime⟩ := head
          obtain ⟨argumentTypes, returnType, isFunction⟩ :=
            PreparedCandidateApplicabilityRel.functionType_of_success applicable
          refine ⟨.success policy output,
            FunctionCandidateScanRel.functionSuccess isFunction applicable, ?_⟩
          rw [scanFunctionTypeCandidatesForExpectedFrom_cons, singletonEquation]
          exact .success selectedRuntime
            (selectedWitness pairHead singletonEquation applicable
              selectedRuntime)
      | exhausted runtimeErrors tupleEligible =>
          cases tupleEligible with
          | false =>
              obtain ⟨argumentTypes, returnType, specErrors, isFunction,
                failed, errorBlock⟩ := head
              have noSuccess :=
                PreparedCandidateApplicabilityRel.no_success_of_error failed
              have nonempty :=
                PreparedCandidateApplicabilityRel.error_nonempty failed
              cases tailRuntime with
              | @success policy output runtime base tailWitness =>
                  cases base with
                  | @success _ _ _ presentation coherent
                      presentationExtension presentationSolutions =>
                  refine ⟨.success policy output,
                    FunctionCandidateScanRel.functionFailureThenSuccess
                      isFunction noSuccess failed nonempty tailScan, ?_⟩
                  rw [scanFunctionTypeCandidatesForExpectedFrom_cons,
                    singletonEquation, tailRuntimeEquation]
                  simp only [Metta.Minimal.ExpectedFunctionTypeScanOutcome.prependErrors]
                  exact .success
                    (.success coherent presentationExtension
                      presentationSolutions) tailWitness
              | @exhausted specTailErrors runtimeTailErrors specTuple
                  runtimeTuple base =>
                  cases base with
                  | exhausted tailErrors tupleEquation =>
                  refine ⟨.exhausted (specErrors ++ specTailErrors) specTuple,
                    FunctionCandidateScanRel.functionFailureExhausted
                      isFunction noSuccess failed nonempty tailScan, ?_⟩
                  rw [scanFunctionTypeCandidatesForExpectedFrom_cons,
                    singletonEquation, tailRuntimeEquation]
                  simp only [Metta.Minimal.ExpectedFunctionTypeScanOutcome.prependErrors]
                  exact .exhausted
                    (.exhausted (List.rel_append errorBlock tailErrors)
                      tupleEquation)
          | true =>
              obtain ⟨noFunctionErrors, notFunction⟩ := head
              cases tailRuntime with
              | @success policy output runtime base tailWitness =>
                  cases base with
                  | @success _ _ _ presentation coherent
                      presentationExtension presentationSolutions =>
                  refine ⟨.success policy output,
                    FunctionCandidateScanRel.nonFunctionSuccess
                      notFunction tailScan, ?_⟩
                  rw [scanFunctionTypeCandidatesForExpectedFrom_cons,
                    singletonEquation, tailRuntimeEquation]
                  simp only [Metta.Minimal.ExpectedFunctionTypeScanOutcome.markTupleEligible]
                  exact .success
                    (.success coherent presentationExtension
                      presentationSolutions) tailWitness
              | @exhausted specTailErrors runtimeTailErrors specTuple
                  runtimeTuple base =>
                  cases base with
                  | exhausted tailErrors _ =>
                  refine ⟨.exhausted specTailErrors true,
                    FunctionCandidateScanRel.nonFunctionExhausted
                      notFunction tailScan, ?_⟩
                  rw [scanFunctionTypeCandidatesForExpectedFrom_cons,
                    singletonEquation, tailRuntimeEquation]
                  simp only [Metta.Minimal.ExpectedFunctionTypeScanOutcome.markTupleEligible]
                  exact .exhausted (.exhausted tailErrors rfl)

/-- If the specification singleton is the decoding of the runtime singleton,
selection preserves the whole arrow literally.  The selected record stores
the scanned candidate unchanged, and uniqueness of arrow decomposition then
fixes the domain and codomain fields as well. -/
theorem selectedTypePolicyRuntimeExactRel_of_aligned_singleton
    {oracle : TypePreparationOracle}
    {space : Space} {observationScope : List String}
    {expression expectedType : Atom} {incoming : Bindings}
    {initialPresentation : TypeSubst}
    {env : Metta.Minimal.MinEnv} {world : Metta.Minimal.World}
    {runtimeInitial : Metta.Bindings}
    {runtimeExpression : Metta.Atom}
    {runtimeArguments : List Metta.Atom} {runtimeExpected : Metta.Atom}
    {allowExtraArguments : Bool}
    {candidate : Atom} {runtimeCandidate : Metta.Atom}
    {policy : SelectedTypePolicy} {output : Bindings}
    {runtime : Metta.Minimal.SelectedFunctionType}
    (aligned : runtimeCandidate = toLeaTTaAtom candidate)
    (scan : Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom env world
      runtimeExpression runtimeArguments runtimeExpected allowExtraArguments
        runtimeInitial [runtimeCandidate] = .selected runtime)
    (applicable : PreparedCandidateApplicabilityRel oracle space expression
      candidate expectedType incoming initialPresentation
        (.success policy output))
    (outcome : FunctionCandidateScanOutcomeRuntimeRel observationScope
      expression incoming (.success policy output) (.selected runtime)) :
    SelectedTypePolicyRuntimeExactRel policy runtime := by
  have runtimeCandidateEquation :
      runtime.functionType = runtimeCandidate :=
    scanFunctionTypeCandidatesForExpectedFrom_singleton_functionType scan
  have decodedFunctionType :
      fromLeaTTaAtom runtime.functionType = candidate := by
    rw [runtimeCandidateEquation, aligned,
      fromLeaTTaAtom_toLeaTTaAtom]
  have policyFields := PreparedCandidateSuccessRel.policyFields applicable
  have runtimeArrow : FunctionTypeRel candidate
      (fromLeaTTaAtoms runtime.argumentTypes)
      (fromLeaTTaAtom runtime.returnType) := by
    cases outcome with
    | success coherent _extension _solutions =>
        rw [← decodedFunctionType]
        exact coherent.policyRuntime.runtimeShape
  have uniqueFields := policyFields.2.unique runtimeArrow
  exact ⟨policyFields.1.trans decodedFunctionType.symm,
    by rw [policyFields.1, ← aligned, ← runtimeCandidateEquation],
    uniqueFields.1, uniqueFields.2⟩

/-- Ordinary outcome correspondence is the trivial selected-witness
specialization of the single refined scan induction. -/
theorem scanFunctionTypeCandidatesForExpected_runtime
    {oracle : TypePreparationOracle}
    {space : Space} {observationScope : List String}
    {expression expectedType : Atom} {incoming : Bindings}
    {initialPresentation : TypeSubst}
    {env : Metta.Minimal.MinEnv} {world : Metta.Minimal.World}
    {runtimeInitial : Metta.Bindings}
    {runtimeExpression : Metta.Atom}
    {runtimeArguments : List Metta.Atom} {runtimeExpected : Metta.Atom}
    {allowExtraArguments : Bool}
    {candidates : List Atom} {runtimeCandidates : List Metta.Atom}
    (classifications : List.Forall₂
      (PreparedCandidateSingletonRuntimeRel oracle space observationScope
        expression expectedType incoming initialPresentation env world
        runtimeInitial runtimeExpression
        runtimeArguments runtimeExpected allowExtraArguments)
      candidates runtimeCandidates) :
    ∃ outcome,
      FunctionCandidateScanRel
          (fun space expression candidate expectedType bindings outcome =>
            PreparedCandidateApplicabilityRel oracle space expression candidate
              expectedType bindings initialPresentation outcome)
          space expression expectedType incoming candidates outcome ∧
        FunctionCandidateScanOutcomeRuntimeRel observationScope expression
          incoming outcome
          (Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom env world
            runtimeExpression runtimeArguments runtimeExpected
            allowExtraArguments runtimeInitial runtimeCandidates) := by
  have pairs : List.Forall₂ (fun _ _ => True)
      candidates runtimeCandidates :=
    classifications.imp fun _ _ _ => trivial
  obtain ⟨outcome, scan, refined⟩ :=
    scanFunctionTypeCandidatesForExpected_runtime_with_success
      (Success := fun _ _ => True) classifications pairs
      (by intros; trivial)
  exact ⟨outcome, scan, refined.toRuntimeRel⟩

/-! ## Alpha-localized package scan and service instance -/

/-- Exact ordered candidate scan recovered from a package list.  The package
observations are alpha-localized against the complete call boundary before
the generic first-success scan consumes them. -/
def PreparedPackageCandidateScanRel
    (oracle : TypePreparationOracle)
    (space : Space) (expression expectedType : Atom)
    (bindings : Bindings) (packages : List TypePackage)
    (outcome : FunctionCandidateScanOutcome) : Prop :=
  ∃ initialPresentation candidates,
    InitialTypeBindingPresentationRel initialPresentation bindings ∧
      OperatorAlphaVariantsRel
        (typeServicePrivateAvoid space expression expectedType bindings)
        (observedTypes packages) candidates ∧
      FunctionCandidateScanRel
        (fun space expression candidate expectedType bindings outcome =>
          PreparedCandidateApplicabilityRel oracle space expression candidate
            expectedType bindings initialPresentation outcome)
        space expression expectedType bindings candidates outcome

/-- A successful package-facing scan inherits the selected applicability
path's concrete model.  Consumers need not reopen the generic candidate-list
induction merely to establish that its committed binding output is
satisfiable. -/
theorem PreparedPackageCandidateScanRel.success_output_satisfiable
    {oracle : TypePreparationOracle}
    {space : Space} {expression expectedType : Atom}
    {bindings output : Bindings} {packages : List TypePackage}
    {policy : SelectedTypePolicy}
    (scan : PreparedPackageCandidateScanRel oracle space expression
      expectedType bindings packages (.success policy output)) :
    ∃ valuation, TypeBindingSatisfied valuation output := by
  rcases scan with
    ⟨initialPresentation, candidates, initial, _variants, candidateScan⟩
  obtain ⟨_candidate, _member, success⟩ :=
    candidateScan.success_candidate
  exact PreparedCandidateSuccessRel.output_satisfiable success initial

/-- Ordered package presentation plus pointwise singleton classification is
the complete runtime candidate scan.  Candidate preparation is discharged
pointwise; this theorem is the sole assembly point that combines it with the
generic first-success list induction and the package-facing service carrier. -/
theorem preparedPackageCandidateScan_runtime
    {oracle : TypePreparationOracle}
    {space : Space} {observationScope : List String}
    {expression expectedType : Atom} {incoming : Bindings}
    {initialPresentation : TypeSubst}
    {env : Metta.Minimal.MinEnv} {world : Metta.Minimal.World}
    {runtimeInitial : Metta.Bindings}
    {runtimeExpression : Metta.Atom}
    {runtimeArguments : List Metta.Atom} {runtimeExpected : Metta.Atom}
    {allowExtraArguments : Bool}
    {packages : List TypePackage}
    {candidates : List Atom} {runtimeCandidates : List Metta.Atom}
    (initial : InitialTypeBindingPresentationRel initialPresentation incoming)
    (variants : OperatorAlphaVariantsRel
      (typeServicePrivateAvoid space expression expectedType incoming)
      (observedTypes packages) candidates)
    (classifications : List.Forall₂
      (PreparedCandidateSingletonRuntimeRel oracle space observationScope
        expression expectedType incoming initialPresentation env world
        runtimeInitial runtimeExpression
        runtimeArguments runtimeExpected allowExtraArguments)
      candidates runtimeCandidates) :
    ∃ outcome,
      PreparedPackageCandidateScanRel oracle space expression expectedType
          incoming packages outcome ∧
        FunctionCandidateScanOutcomeRuntimeRel observationScope expression
          incoming outcome
          (Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom env world
            runtimeExpression runtimeArguments runtimeExpected
            allowExtraArguments runtimeInitial runtimeCandidates) := by
  obtain ⟨outcome, scan, runtime⟩ :=
    scanFunctionTypeCandidatesForExpected_runtime classifications
  exact ⟨outcome, ⟨initialPresentation, candidates, initial,
    variants, scan⟩, runtime⟩

/-- Evaluator-facing package assembly chooses the decoded runtime-fresh list
as the specification's existential candidate presentation.  The ordinary
package scan remains unchanged, while successful selection additionally
retains literal agreement of every arrow field. -/
theorem preparedPackageCandidateScan_runtime_aligned
    {oracle : TypePreparationOracle}
    {space : Space} {observationScope : List String}
    {expression expectedType : Atom} {incoming : Bindings}
    {initialPresentation : TypeSubst}
    {env : Metta.Minimal.MinEnv} {world : Metta.Minimal.World}
    {runtimeInitial : Metta.Bindings}
    {runtimeExpression : Metta.Atom}
    {runtimeArguments : List Metta.Atom} {runtimeExpected : Metta.Atom}
    {allowExtraArguments : Bool}
    {packages : List TypePackage}
    {runtimeCandidates : List Metta.Atom}
    (initial : InitialTypeBindingPresentationRel initialPresentation incoming)
    (variants : OperatorAlphaVariantsRel
      (typeServicePrivateAvoid space expression expectedType incoming)
      (observedTypes packages) (fromLeaTTaAtoms runtimeCandidates))
    (classifications : List.Forall₂
      (PreparedCandidateSingletonRuntimeRel oracle space observationScope
        expression expectedType incoming initialPresentation env world
        runtimeInitial runtimeExpression
        runtimeArguments runtimeExpected allowExtraArguments)
      (fromLeaTTaAtoms runtimeCandidates) runtimeCandidates)
    (roundtrip :
      toLeaTTaAtoms (fromLeaTTaAtoms runtimeCandidates) = runtimeCandidates) :
    ∃ outcome,
      PreparedPackageCandidateScanRel oracle space expression expectedType
          incoming packages outcome ∧
        FunctionCandidateScanOutcomeRuntimeRelWith
          SelectedTypePolicyRuntimeExactRel observationScope expression
          incoming outcome
          (Metta.Minimal.scanFunctionTypeCandidatesForExpectedFrom env world
            runtimeExpression runtimeArguments runtimeExpected
            allowExtraArguments runtimeInitial runtimeCandidates) := by
  have pairs : List.Forall₂
      (fun candidate runtimeCandidate =>
        runtimeCandidate = toLeaTTaAtom candidate)
      (fromLeaTTaAtoms runtimeCandidates) runtimeCandidates := by
    have mapped : List.Forall₂
        (fun candidate runtimeCandidate =>
          runtimeCandidate = toLeaTTaAtom candidate)
        (fromLeaTTaAtoms runtimeCandidates)
        (toLeaTTaAtoms (fromLeaTTaAtoms runtimeCandidates)) := by
      induction fromLeaTTaAtoms runtimeCandidates with
      | nil => exact .nil
      | cons candidate candidates inductionHypothesis =>
          exact .cons rfl inductionHypothesis
    rwa [roundtrip] at mapped
  obtain ⟨outcome, scan, runtime⟩ :=
    scanFunctionTypeCandidatesForExpected_runtime_with_success
      (Success := SelectedTypePolicyRuntimeExactRel)
      classifications pairs
      (fun aligned singleton applicable relation =>
        selectedTypePolicyRuntimeExactRel_of_aligned_singleton aligned
          singleton applicable relation)
  exact ⟨outcome, ⟨initialPresentation,
    fromLeaTTaAtoms runtimeCandidates, initial, variants, scan⟩, runtime⟩

/-- The concrete repaired selector realizes the prepared package scan at any
observation scope protected by the runtime's public-call or environment
freshness inputs.  Runtime preparation, exact package lookup, both independent
alpha-localization passes, pointwise applicability, and ordered first-success
assembly are composed here; the executable candidate list is recovered
literally by the freshened-list round trip. -/
theorem preparedPackageCandidateScan_runtime_scoped_avoiding
    {oracle : TypePreparationOracle}
    (functional : TypePreparationFunctional oracle)
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env)
    {world : Metta.Minimal.World}
    (realization : TypePreparationRuntimeRealization oracle space world)
    {observationScope : List String}
    (operator expectedType : Atom) (arguments : List Atom)
    (incoming : Bindings) {initialPresentation : TypeSubst}
    {runtimeInitial : Metta.Bindings}
    (initial : InitialTypeBindingPresentationRel initialPresentation incoming)
    (inputState : TypePresentationSimulationState initialPresentation
      incoming runtimeInitial)
    (bindingSupport : ∀ name, name ∈ specBindingVars incoming →
      name ∈ runtimeInitial.vars)
    (specObservationCovered : ∀ name, name ∈ observationScope →
      name ∈ typeServicePrivateAvoid space
        (.expression (operator :: arguments)) expectedType incoming)
    (runtimeObservationProtected : ∀ name, name ∈ observationScope →
      name ∈ Metta.Minimal.applicationTypeInferenceScope
          (toLeaTTaAtom expectedType) (toLeaTTaAtoms arguments) ∨
        name ∈ env.atoms.flatMap Metta.Atom.vars) :
    let expression := Atom.expression (operator :: arguments)
    ∃ prepared packages outcome,
      oracle.prepare space operator prepared ∧
      RuntimeTypePackagesRel space prepared packages ∧
      PreparedPackageCandidateScanRel oracle space expression expectedType
        incoming packages outcome ∧
      FunctionCandidateScanOutcomeRuntimeRel
        observationScope
        expression incoming outcome
        (Metta.Minimal.selectFunctionTypeForExpectedFrom env world
          (toLeaTTaAtom operator) (toLeaTTaAtoms arguments)
          (toLeaTTaAtom expectedType) runtimeInitial) := by
  dsimp only
  let expression := Atom.expression (operator :: arguments)
  let rawRuntime := Metta.Minimal.getTypes env
    (Metta.Minimal.typePrep world (toLeaTTaAtom operator))
  let runtimeCandidates :=
    Metta.Minimal.freshenFunctionTypeCandidatesAvoiding env
      (toLeaTTaAtom expression) (toLeaTTaAtoms arguments)
      (toLeaTTaAtom expectedType) runtimeInitial.vars rawRuntime
  let runtimeAvoid := Metta.Minimal.functionTypeSelectionAvoiding env
    (toLeaTTaAtom expression) (toLeaTTaAtoms arguments)
    (toLeaTTaAtom expectedType) runtimeInitial.vars rawRuntime
  obtain ⟨prepared, packages, rawCandidates, specCandidates,
      preparation, _preparationEquation, packageRelation, _rawEquation,
      _packageAlpha, _specEquation, specVariants, packageVariants,
      runtimeVariants, specGenerated, runtimeGenerated,
      runtimeRoundtrip⟩ :=
    runtimePreparedOperatorCandidates_avoiding_exists index realization
      operator expectedType arguments incoming runtimeInitial.vars
  have runtimeCallCovered : ∀ name,
      name ∈ TypeSubst.typeVars expectedType ++
          TypeSubst.typeVarsList arguments →
        name ∈ runtimeAvoid := by
    intro name member
    apply List.mem_append_right
    apply List.mem_append_left
    simpa only [Metta.Minimal.applicationTypeInferenceScope,
      LeaTTaTypePresentationExactConformance.toLeaTTaAtom_vars_eq_typeVars,
      LeaTTaTypePresentationExactConformance.toLeaTTaAtoms_vars_eq_typeVars]
      using member
  have runtimeInitialBindingCovered : ∀ name,
      name ∈ specBindingVars
          (⟨initialPresentation, []⟩ : Bindings) →
        name ∈ runtimeInitial.vars := by
    intro name member
    exact bindingSupport name (initial.support name member)
  have runtimeInitialAvoidCovered : ∀ name,
      name ∈ specBindingVars
          (⟨initialPresentation, []⟩ : Bindings) →
        name ∈ runtimeAvoid := by
    intro name member
    dsimp [runtimeAvoid, Metta.Minimal.functionTypeSelectionAvoiding]
    exact List.mem_append_left _
      (runtimeInitialBindingCovered name member)
  have runtimeObservationCovered : ∀ name, name ∈ observationScope →
      name ∈ runtimeAvoid := by
    intro name member
    rcases runtimeObservationProtected name member with
      boundaryMember | environmentMember
    · exact List.mem_append_right _ (List.mem_append_left _ boundaryMember)
    · apply List.mem_append_right
      apply List.mem_append_right
      exact List.mem_append_left _
        (List.mem_append_left _ environmentMember)
  have specVariants' : OperatorAlphaVariantsRel
      (typeServicePrivateAvoid space expression expectedType incoming)
      rawCandidates specCandidates := by
    simpa [expression] using specVariants
  have packageVariants' : OperatorAlphaVariantsRel
      (typeServicePrivateAvoid space expression expectedType incoming)
    (observedTypes packages) specCandidates := by
    simpa [expression] using packageVariants
  have runtimeVariants' : OperatorAlphaVariantsRel runtimeAvoid
      rawCandidates (fromLeaTTaAtoms runtimeCandidates) := by
    simpa [runtimeCandidates, runtimeAvoid, expression, rawRuntime] using
      runtimeVariants
  have classifications :=
    alphaPreparedSingletonClassifications functional index realization
      (expression := expression) (operator := operator)
      (expectedType := expectedType) (arguments := arguments)
      (incoming := incoming) (runtimeAvoid := runtimeAvoid)
      (observationScope := observationScope)
      (rawCandidates := rawCandidates) (specCandidates := specCandidates)
      (runtimeCandidates := fromLeaTTaAtoms runtimeCandidates)
      initial inputState rfl runtimeCallCovered
      specObservationCovered runtimeObservationCovered
      runtimeObservationProtected
      runtimeInitialAvoidCovered runtimeInitialBindingCovered
      (operatorAlphaVariantsRel_toForall₂ specVariants')
      (operatorAlphaVariantsRel_toForall₂ runtimeVariants')
      specGenerated runtimeGenerated
  rw [runtimeRoundtrip] at classifications
  obtain ⟨outcome, packageScan, runtime⟩ :=
    preparedPackageCandidateScan_runtime initial packageVariants'
      classifications
  refine ⟨prepared, packages, outcome, preparation, packageRelation,
    packageScan, ?_⟩
  simpa [expression, rawRuntime, runtimeCandidates, toLeaTTaAtom,
    toLeaTTaAtoms,
    Metta.Minimal.selectFunctionTypeForExpectedFrom] using runtime

/-- Evaluator-aligned specialization of the scoped selector realization.
When the executable's signature-freshening avoid set covers the complete
specification-private boundary, its decoded fresh candidates may serve as the
specification's existential presentation.  This retains exact selected arrow
fields without identifying private spellings in the general type service. -/
theorem preparedPackageCandidateScan_runtime_scoped_aligned
    {oracle : TypePreparationOracle}
    (functional : TypePreparationFunctional oracle)
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env)
    {world : Metta.Minimal.World}
    (realization : TypePreparationRuntimeRealization oracle space world)
    {observationScope : List String}
    (operator expectedType : Atom) (arguments : List Atom)
    (incoming : Bindings) {initialPresentation : TypeSubst}
    {runtimeInitial : Metta.Bindings}
    (initial : InitialTypeBindingPresentationRel initialPresentation incoming)
    (inputState : TypePresentationSimulationState initialPresentation
      incoming runtimeInitial)
    (bindingSupport : ∀ name, name ∈ specBindingVars incoming →
      name ∈ runtimeInitial.vars)
    (specObservationCovered : ∀ name, name ∈ observationScope →
      name ∈ typeServicePrivateAvoid space
        (.expression (operator :: arguments)) expectedType incoming)
    (runtimeObservationProtected : ∀ name, name ∈ observationScope →
      name ∈ Metta.Minimal.applicationTypeInferenceScope
          (toLeaTTaAtom expectedType) (toLeaTTaAtoms arguments) ∨
        name ∈ env.atoms.flatMap Metta.Atom.vars)
    (runtimePrivateAvoidCovered :
      let expression := Atom.expression (operator :: arguments)
      let rawRuntime := Metta.Minimal.getTypes env
        (Metta.Minimal.typePrep world (toLeaTTaAtom operator))
      ∀ name,
        name ∈ typeServicePrivateAvoid space expression expectedType incoming →
          name ∈ Metta.Minimal.functionTypeSelectionAvoiding env
            (toLeaTTaAtom expression) (toLeaTTaAtoms arguments)
            (toLeaTTaAtom expectedType) runtimeInitial.vars rawRuntime) :
    let expression := Atom.expression (operator :: arguments)
    ∃ prepared packages outcome,
      oracle.prepare space operator prepared ∧
      RuntimeTypePackagesRel space prepared packages ∧
      PreparedPackageCandidateScanRel oracle space expression expectedType
        incoming packages outcome ∧
      FunctionCandidateScanOutcomeRuntimeRelWith
        SelectedTypePolicyRuntimeExactRel observationScope expression incoming
        outcome
        (Metta.Minimal.selectFunctionTypeForExpectedFrom env world
          (toLeaTTaAtom operator) (toLeaTTaAtoms arguments)
          (toLeaTTaAtom expectedType) runtimeInitial) := by
  dsimp only at runtimePrivateAvoidCovered ⊢
  let expression := Atom.expression (operator :: arguments)
  let rawRuntime := Metta.Minimal.getTypes env
    (Metta.Minimal.typePrep world (toLeaTTaAtom operator))
  let runtimeCandidates :=
    Metta.Minimal.freshenFunctionTypeCandidatesAvoiding env
      (toLeaTTaAtom expression) (toLeaTTaAtoms arguments)
      (toLeaTTaAtom expectedType) runtimeInitial.vars rawRuntime
  let runtimeAvoid := Metta.Minimal.functionTypeSelectionAvoiding env
    (toLeaTTaAtom expression) (toLeaTTaAtoms arguments)
    (toLeaTTaAtom expectedType) runtimeInitial.vars rawRuntime
  obtain ⟨prepared, packages, rawCandidates, _specCandidates,
      preparation, _preparationEquation, packageRelation, _rawEquation,
      packageAlpha, _specEquation, _specVariants, _packageVariants,
      runtimeVariants, _specGenerated, runtimeGenerated,
      runtimeRoundtrip⟩ :=
    runtimePreparedOperatorCandidates_avoiding_exists index realization
      operator expectedType arguments incoming runtimeInitial.vars
  have runtimeCallCovered : ∀ name,
      name ∈ TypeSubst.typeVars expectedType ++
          TypeSubst.typeVarsList arguments →
        name ∈ runtimeAvoid := by
    intro name member
    apply List.mem_append_right
    apply List.mem_append_left
    simpa only [Metta.Minimal.applicationTypeInferenceScope,
      LeaTTaTypePresentationExactConformance.toLeaTTaAtom_vars_eq_typeVars,
      LeaTTaTypePresentationExactConformance.toLeaTTaAtoms_vars_eq_typeVars]
      using member
  have runtimeInitialBindingCovered : ∀ name,
      name ∈ specBindingVars
          (⟨initialPresentation, []⟩ : Bindings) →
        name ∈ runtimeInitial.vars := by
    intro name member
    exact bindingSupport name (initial.support name member)
  have runtimeInitialAvoidCovered : ∀ name,
      name ∈ specBindingVars
          (⟨initialPresentation, []⟩ : Bindings) →
        name ∈ runtimeAvoid := by
    intro name member
    dsimp [runtimeAvoid, Metta.Minimal.functionTypeSelectionAvoiding]
    exact List.mem_append_left _
      (runtimeInitialBindingCovered name member)
  have runtimeObservationCovered : ∀ name, name ∈ observationScope →
      name ∈ runtimeAvoid := by
    intro name member
    rcases runtimeObservationProtected name member with
      boundaryMember | environmentMember
    · exact List.mem_append_right _ (List.mem_append_left _ boundaryMember)
    · apply List.mem_append_right
      apply List.mem_append_right
      exact List.mem_append_left _
        (List.mem_append_left _ environmentMember)
  have runtimeVariants' : OperatorAlphaVariantsRel runtimeAvoid
      rawCandidates (fromLeaTTaAtoms runtimeCandidates) := by
    simpa [runtimeCandidates, runtimeAvoid, expression, rawRuntime] using
      runtimeVariants
  have alignedVariants : OperatorAlphaVariantsRel
      (typeServicePrivateAvoid space expression expectedType incoming)
      rawCandidates (fromLeaTTaAtoms runtimeCandidates) :=
    operatorAlphaVariantsRel_mono runtimeVariants'
      (by simpa [runtimeAvoid, expression, rawRuntime] using
        runtimePrivateAvoidCovered)
  have packageVariants : OperatorAlphaVariantsRel
      (typeServicePrivateAvoid space expression expectedType incoming)
      (observedTypes packages) (fromLeaTTaAtoms runtimeCandidates) :=
    operatorAlphaVariants_transport_sources packageAlpha alignedVariants
  have classifications :=
    alphaPreparedSingletonClassifications functional index realization
      (expression := expression) (operator := operator)
      (expectedType := expectedType) (arguments := arguments)
      (incoming := incoming) (runtimeAvoid := runtimeAvoid)
      (observationScope := observationScope)
      (rawCandidates := rawCandidates)
      (specCandidates := fromLeaTTaAtoms runtimeCandidates)
      (runtimeCandidates := fromLeaTTaAtoms runtimeCandidates)
      initial inputState rfl runtimeCallCovered
      specObservationCovered runtimeObservationCovered
      runtimeObservationProtected
      runtimeInitialAvoidCovered runtimeInitialBindingCovered
      (operatorAlphaVariantsRel_toForall₂ alignedVariants)
      (operatorAlphaVariantsRel_toForall₂ runtimeVariants')
      runtimeGenerated runtimeGenerated
  rw [runtimeRoundtrip] at classifications
  obtain ⟨outcome, packageScan, runtime⟩ :=
    preparedPackageCandidateScan_runtime_aligned initial packageVariants
      classifications runtimeRoundtrip
  refine ⟨prepared, packages, outcome, preparation, packageRelation,
    packageScan, ?_⟩
  simpa [expression, rawRuntime, runtimeCandidates, toLeaTTaAtom,
    toLeaTTaAtoms,
    Metta.Minimal.selectFunctionTypeForExpectedFrom] using runtime

/-- Public-call specialization of
`preparedPackageCandidateScan_runtime_scoped_avoiding`.  The expected type and every
source argument are exactly the fixed boundary threaded by the runtime
argument worker. -/
theorem preparedPackageCandidateScan_runtime_callScope
    {oracle : TypePreparationOracle}
    (functional : TypePreparationFunctional oracle)
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env)
    {world : Metta.Minimal.World}
    (realization : TypePreparationRuntimeRealization oracle space world)
    (operator expectedType : Atom) (arguments : List Atom)
    (incoming : Bindings) {initialPresentation : TypeSubst}
    {runtimeInitial : Metta.Bindings}
    (initial : InitialTypeBindingPresentationRel initialPresentation incoming)
    (inputState : TypePresentationSimulationState initialPresentation
      incoming runtimeInitial)
    (bindingSupport : ∀ name, name ∈ specBindingVars incoming →
      name ∈ runtimeInitial.vars) :
    let expression := Atom.expression (operator :: arguments)
    ∃ prepared packages outcome,
      oracle.prepare space operator prepared ∧
      RuntimeTypePackagesRel space prepared packages ∧
      PreparedPackageCandidateScanRel oracle space expression expectedType
        incoming packages outcome ∧
      FunctionCandidateScanOutcomeRuntimeRel
        (TypeSubst.typeVars expectedType ++
          TypeSubst.typeVarsList arguments)
        expression incoming outcome
        (Metta.Minimal.selectFunctionTypeForExpectedFrom env world
          (toLeaTTaAtom operator) (toLeaTTaAtoms arguments)
          (toLeaTTaAtom expectedType) runtimeInitial) := by
  apply preparedPackageCandidateScan_runtime_scoped_avoiding functional index
    realization operator expectedType arguments incoming initial inputState
      bindingSupport
  · intro name member
    apply List.mem_append_left
    rw [typeServiceObservationScope]
    rcases List.mem_append.mp member with expectedMember | argumentMember
    · exact typeVars_mem_typeVarsList_of_mem
        (atoms := space.atoms ++
          [Atom.expression (operator :: arguments), expectedType])
        (atom := expectedType) (by simp) name expectedMember
    · have expressionMember : name ∈
          TypeSubst.typeVars (Atom.expression (operator :: arguments)) := by
        simp only [TypeSubst.typeVars, TypeSubst.typeVarsList,
          List.mem_append]
        exact Or.inr argumentMember
      exact typeVars_mem_typeVarsList_of_mem
        (atoms := space.atoms ++
          [Atom.expression (operator :: arguments), expectedType])
        (atom := Atom.expression (operator :: arguments)) (by simp)
        name expressionMember
  · intro name member
    apply Or.inl
    simpa only [Metta.Minimal.applicationTypeInferenceScope,
      LeaTTaTypePresentationExactConformance.toLeaTTaAtom_vars_eq_typeVars,
      LeaTTaTypePresentationExactConformance.toLeaTTaAtoms_vars_eq_typeVars]
      using member

/-- At a symbol-headed application, the complete type-service observation
scope is protected by exactly two runtime sources: the expected/argument
boundary and the translated environment atoms.  The operator contributes no
variables.  Keeping the atom-list equation explicit is important:
`TypeEnvironmentRel` relates the two type indexes, not the environment's
entire stored atom list. -/
theorem typeServiceObservationScope_symbol_runtimeProtected
    {space : Space} {env : Metta.Minimal.MinEnv}
    (atomsEquation : env.atoms = toLeaTTaAtoms space.atoms)
    (operator : String) (arguments : List Atom) (expectedType : Atom) :
    ∀ name,
      name ∈ typeServiceObservationScope space
          (.expression (.symbol operator :: arguments)) expectedType →
        name ∈ Metta.Minimal.applicationTypeInferenceScope
            (toLeaTTaAtom expectedType) (toLeaTTaAtoms arguments) ∨
          name ∈ env.atoms.flatMap Metta.Atom.vars := by
  intro name member
  rw [typeServiceObservationScope, typeVarsList_append,
    List.mem_append] at member
  rcases member with spaceMember | boundaryMember
  · apply Or.inr
    rw [atomsEquation,
      LeaTTaTypePresentationExactConformance.toLeaTTaAtoms_vars_eq_typeVars]
    exact spaceMember
  · apply Or.inl
    simp only [TypeSubst.typeVarsList, TypeSubst.typeVars,
      List.nil_append, List.append_nil, List.mem_append] at boundaryMember
    simp only [Metta.Minimal.applicationTypeInferenceScope,
      LeaTTaTypePresentationExactConformance.toLeaTTaAtom_vars_eq_typeVars,
      LeaTTaTypePresentationExactConformance.toLeaTTaAtoms_vars_eq_typeVars,
      List.mem_append]
    exact boundaryMember.symm

/-- At a symbol-headed application, runtime signature freshening protects the
entire specification-private boundary.  Space and call variables are covered
by the stored environment and public application scope; incoming binding
support is covered by the live-avoid prefix added by repair #18. -/
theorem typeServicePrivateAvoid_symbol_runtimeSelectionProtected
    {space : Space} {env : Metta.Minimal.MinEnv}
    (atomsEquation : env.atoms = toLeaTTaAtoms space.atoms)
    {incoming : Bindings} {runtimeInitial : Metta.Bindings}
    (bindingSupport : ∀ name, name ∈ specBindingVars incoming →
      name ∈ runtimeInitial.vars)
    (operator : String) (arguments : List Atom) (expectedType : Atom)
    (rawCandidates : List Metta.Atom) :
    ∀ name,
      name ∈ typeServicePrivateAvoid space
          (.expression (.symbol operator :: arguments)) expectedType
          incoming →
        name ∈ Metta.Minimal.functionTypeSelectionAvoiding env
          (toLeaTTaAtom (.expression (.symbol operator :: arguments)))
          (toLeaTTaAtoms arguments) (toLeaTTaAtom expectedType)
          runtimeInitial.vars rawCandidates := by
  intro name member
  rw [typeServicePrivateAvoid, List.mem_append] at member
  rcases member with observationMember | bindingMember
  · rcases typeServiceObservationScope_symbol_runtimeProtected
        atomsEquation operator arguments expectedType name observationMember with
      boundaryMember | environmentMember
    · simp only [Metta.Minimal.functionTypeSelectionAvoiding,
        Metta.Minimal.functionTypeSelectionAvoid, List.mem_append]
      exact Or.inr (Or.inl boundaryMember)
    · simp [Metta.Minimal.functionTypeSelectionAvoiding,
        Metta.Minimal.functionTypeSelectionAvoid,
        Metta.Minimal.typeInferenceAvoid, environmentMember]
  · simp [Metta.Minimal.functionTypeSelectionAvoiding,
      bindingSupport name bindingMember]

/-- Exact prepared package selection at the full seal observation scope for a
symbol-headed application.  This is the concrete evaluator boundary: the
type-index relation supplies lookup correspondence, while `atomsEquation`
supplies the independently necessary environment-observation correspondence.
-/
theorem preparedPackageCandidateScan_runtime_symbol_avoiding
    {oracle : TypePreparationOracle}
    (functional : TypePreparationFunctional oracle)
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env)
    (atomsEquation : env.atoms = toLeaTTaAtoms space.atoms)
    {world : Metta.Minimal.World}
    (realization : TypePreparationRuntimeRealization oracle space world)
    (operator : String) (expectedType : Atom) (arguments : List Atom)
    (incoming : Bindings) {initialPresentation : TypeSubst}
    {runtimeInitial : Metta.Bindings}
    (initial : InitialTypeBindingPresentationRel initialPresentation incoming)
    (inputState : TypePresentationSimulationState initialPresentation
      incoming runtimeInitial)
    (bindingSupport : ∀ name, name ∈ specBindingVars incoming →
      name ∈ runtimeInitial.vars) :
    let expression := Atom.expression (.symbol operator :: arguments)
    ∃ prepared packages outcome,
      oracle.prepare space (.symbol operator) prepared ∧
      RuntimeTypePackagesRel space prepared packages ∧
      PreparedPackageCandidateScanRel oracle space expression expectedType
        incoming packages outcome ∧
      FunctionCandidateScanOutcomeRuntimeRel
        (typeServiceObservationScope space expression expectedType)
        expression incoming outcome
        (Metta.Minimal.selectFunctionTypeForExpectedFrom env world
          (.sym operator) (toLeaTTaAtoms arguments)
          (toLeaTTaAtom expectedType) runtimeInitial) := by
  apply preparedPackageCandidateScan_runtime_scoped_avoiding functional index
    realization (.symbol operator) expectedType arguments incoming initial
      inputState bindingSupport
  · intro name member
    exact List.mem_append_left _ member
  · exact typeServiceObservationScope_symbol_runtimeProtected
      atomsEquation operator arguments expectedType

/-- Evaluator-facing symbol specialization retaining exact selected arrow
fields.  Unlike the general type-service theorem, this boundary has both the
stored-atom equation and live-binding support needed to reuse the runtime's
fresh candidates as the specification presentation. -/
theorem preparedPackageCandidateScan_runtime_symbol_aligned
    {oracle : TypePreparationOracle}
    (functional : TypePreparationFunctional oracle)
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env)
    (atomsEquation : env.atoms = toLeaTTaAtoms space.atoms)
    {world : Metta.Minimal.World}
    (realization : TypePreparationRuntimeRealization oracle space world)
    (operator : String) (expectedType : Atom) (arguments : List Atom)
    (incoming : Bindings) {initialPresentation : TypeSubst}
    {runtimeInitial : Metta.Bindings}
    (initial : InitialTypeBindingPresentationRel initialPresentation incoming)
    (inputState : TypePresentationSimulationState initialPresentation
      incoming runtimeInitial)
    (bindingSupport : ∀ name, name ∈ specBindingVars incoming →
      name ∈ runtimeInitial.vars) :
    let expression := Atom.expression (.symbol operator :: arguments)
    ∃ prepared packages outcome,
      oracle.prepare space (.symbol operator) prepared ∧
      RuntimeTypePackagesRel space prepared packages ∧
      PreparedPackageCandidateScanRel oracle space expression expectedType
        incoming packages outcome ∧
      FunctionCandidateScanOutcomeRuntimeRelWith
        SelectedTypePolicyRuntimeExactRel
        (typeServiceObservationScope space expression expectedType)
        expression incoming outcome
        (Metta.Minimal.selectFunctionTypeForExpectedFrom env world
          (.sym operator) (toLeaTTaAtoms arguments)
          (toLeaTTaAtom expectedType) runtimeInitial) := by
  apply preparedPackageCandidateScan_runtime_scoped_aligned functional index
    realization (.symbol operator) expectedType arguments incoming initial
      inputState bindingSupport
  · intro name member
    exact List.mem_append_left _ member
  · exact typeServiceObservationScope_symbol_runtimeProtected
      atomsEquation operator arguments expectedType
  · exact typeServicePrivateAvoid_symbol_runtimeSelectionProtected
      atomsEquation bindingSupport operator arguments expectedType _

/-- Canonical-environment specialization of
`preparedPackageCandidateScan_runtime_symbol_avoiding`.  Building the runtime
environment from the translated spec space supplies both independent boundary
facts definitionally: the ordered type indexes and the stored atom list. -/
theorem preparedPackageCandidateScan_runtime_ofAtomsGT_avoiding
    {oracle : TypePreparationOracle}
    (functional : TypePreparationFunctional oracle)
    (space : Space) (groundingTable : Metta.GroundingTable)
    {world : Metta.Minimal.World}
    (realization : TypePreparationRuntimeRealization oracle space world)
    (operator : String) (expectedType : Atom) (arguments : List Atom)
    (incoming : Bindings) {initialPresentation : TypeSubst}
    {runtimeInitial : Metta.Bindings}
    (initial : InitialTypeBindingPresentationRel initialPresentation incoming)
    (inputState : TypePresentationSimulationState initialPresentation
      incoming runtimeInitial)
    (bindingSupport : ∀ name, name ∈ specBindingVars incoming →
      name ∈ runtimeInitial.vars) :
    let env := Metta.Minimal.MinEnv.ofAtomsGT
      (toLeaTTaAtoms space.atoms) groundingTable
    let expression := Atom.expression (.symbol operator :: arguments)
    ∃ prepared packages outcome,
      oracle.prepare space (.symbol operator) prepared ∧
      RuntimeTypePackagesRel space prepared packages ∧
      PreparedPackageCandidateScanRel oracle space expression expectedType
        incoming packages outcome ∧
      FunctionCandidateScanOutcomeRuntimeRel
        (typeServiceObservationScope space expression expectedType)
        expression incoming outcome
        (Metta.Minimal.selectFunctionTypeForExpectedFrom env world
          (.sym operator) (toLeaTTaAtoms arguments)
          (toLeaTTaAtom expectedType) runtimeInitial) := by
  dsimp only
  exact preparedPackageCandidateScan_runtime_symbol_avoiding functional
    (typeEnvironmentRel_ofAtomsGT space groundingTable) rfl realization
    operator expectedType arguments incoming initial inputState
      bindingSupport

/-- Canonical-environment evaluator specialization retaining the exact
selected arrow refinement. -/
theorem preparedPackageCandidateScan_runtime_ofAtomsGT_aligned
    {oracle : TypePreparationOracle}
    (functional : TypePreparationFunctional oracle)
    (space : Space) (groundingTable : Metta.GroundingTable)
    {world : Metta.Minimal.World}
    (realization : TypePreparationRuntimeRealization oracle space world)
    (operator : String) (expectedType : Atom) (arguments : List Atom)
    (incoming : Bindings) {initialPresentation : TypeSubst}
    {runtimeInitial : Metta.Bindings}
    (initial : InitialTypeBindingPresentationRel initialPresentation incoming)
    (inputState : TypePresentationSimulationState initialPresentation
      incoming runtimeInitial)
    (bindingSupport : ∀ name, name ∈ specBindingVars incoming →
      name ∈ runtimeInitial.vars) :
    let env := Metta.Minimal.MinEnv.ofAtomsGT
      (toLeaTTaAtoms space.atoms) groundingTable
    let expression := Atom.expression (.symbol operator :: arguments)
    ∃ prepared packages outcome,
      oracle.prepare space (.symbol operator) prepared ∧
      RuntimeTypePackagesRel space prepared packages ∧
      PreparedPackageCandidateScanRel oracle space expression expectedType
        incoming packages outcome ∧
      FunctionCandidateScanOutcomeRuntimeRelWith
        SelectedTypePolicyRuntimeExactRel
        (typeServiceObservationScope space expression expectedType)
        expression incoming outcome
        (Metta.Minimal.selectFunctionTypeForExpectedFrom env world
          (.sym operator) (toLeaTTaAtoms arguments)
          (toLeaTTaAtom expectedType) runtimeInitial) := by
  dsimp only
  exact preparedPackageCandidateScan_runtime_symbol_aligned functional
    (typeEnvironmentRel_ofAtomsGT space groundingTable) rfl realization
    operator expectedType arguments incoming initial inputState
      bindingSupport

/-! ## Concrete type-cast field -/

/-- Every executable-independent private name protected by one cast boundary
is protected by the repaired runtime avoid set.  The only non-structural
premise is binding support: native binding variables must occur in the
runtime binding carrier paired with them by the surrounding simulation. -/
theorem typeServicePrivateAvoid_runtimeTypeCastProtected
    {space : Space} {env : Metta.Minimal.MinEnv}
    (atomsEquation : env.atoms = toLeaTTaAtoms space.atoms)
    {atom expectedType : Atom} {incoming : Bindings}
    {runtimeBindings : Metta.Bindings}
    (bindingSupport : ∀ name, name ∈ specBindingVars incoming →
      name ∈ runtimeBindings.vars)
    (prepared : Atom) (rawTypes : List Metta.Atom) :
    ∀ name,
      name ∈ typeServicePrivateAvoid space atom expectedType incoming →
      name ∈ Metta.Minimal.typeCastInferenceAvoid env
        (toLeaTTaAtom prepared) (toLeaTTaAtom atom)
        (toLeaTTaAtom expectedType) runtimeBindings rawTypes := by
  intro name member
  rw [typeServicePrivateAvoid, List.mem_append] at member
  rcases member with observationMember | bindingMember
  · rw [typeServiceObservationScope, typeVarsList_append,
      List.mem_append] at observationMember
    rcases observationMember with spaceMember | boundaryMember
    · have runtimeSpaceMember :
          name ∈ env.atoms.flatMap Metta.Atom.vars := by
        rw [atomsEquation,
          LeaTTaTypePresentationExactConformance.toLeaTTaAtoms_vars_eq_typeVars]
        exact spaceMember
      simp [Metta.Minimal.typeCastInferenceAvoid,
        Metta.Minimal.typeInferenceAvoid, runtimeSpaceMember]
    · simp only [TypeSubst.typeVarsList,
        List.append_nil, List.mem_append] at boundaryMember
      rcases boundaryMember with atomMember | expectedMember
      · have runtimeAtomMember :
            name ∈ (toLeaTTaAtom atom).vars := by
          simpa [LeaTTaTypePresentationExactConformance.toLeaTTaAtom_vars_eq_typeVars]
            using atomMember
        simp [Metta.Minimal.typeCastInferenceAvoid,
          Metta.Minimal.typeInferenceAvoid, runtimeAtomMember]
      · have runtimeExpectedMember :
            name ∈ (toLeaTTaAtom expectedType).vars := by
          simpa [LeaTTaTypePresentationExactConformance.toLeaTTaAtom_vars_eq_typeVars]
            using expectedMember
        simp [Metta.Minimal.typeCastInferenceAvoid,
          Metta.Minimal.typeInferenceAvoid, runtimeExpectedMember]
  · have runtimeBindingMember := bindingSupport name bindingMember
    simp [Metta.Minimal.typeCastInferenceAvoid,
      Metta.Minimal.typeInferenceAvoid, runtimeBindingMember]

/-- Exact correspondence of the complete repaired `mettaTypeCast` call.

The theorem is stated at an arbitrary indexed runtime environment.  Abstract
preparation is realized pointwise, candidate lookup is recovered through the
package relation, private candidates are freshened against the complete live
boundary, and first-success/all-failure behavior is exact. -/
theorem preparedTypeCast_runtime
    {oracle : TypePreparationOracle}
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env)
    (atomsEquation : env.atoms = toLeaTTaAtoms space.atoms)
    {world : Metta.Minimal.World}
    (realization : TypePreparationRuntimeRealization oracle space world)
    {presentation : TypeSubst} {incoming : Bindings}
    {runtimeBindings : Metta.Bindings}
    (state : TypePresentationSimulationState
      presentation incoming runtimeBindings)
    (bindingSupport : ∀ name, name ∈ specBindingVars incoming →
      name ∈ runtimeBindings.vars)
    (atom expectedType : Atom) (protectedScope : List String := []) :
    PreparedTypeCastOutcomeRuntimeRel oracle space atom expectedType incoming
      (Metta.Minimal.mettaTypeCastAvoiding protectedScope env world
        runtimeBindings (toLeaTTaAtom atom) (toLeaTTaAtom expectedType))
      protectedScope := by
  obtain ⟨prepared, preparation, preparationEquation⟩ := realization atom
  let rawRuntimeTypes :=
    Metta.Minimal.getTypes env (toLeaTTaAtom prepared)
  let runtimeAvoid := protectedScope ++
    Metta.Minimal.typeCastInferenceAvoid env
      (toLeaTTaAtom prepared) (toLeaTTaAtom atom)
      (toLeaTTaAtom expectedType) runtimeBindings rawRuntimeTypes
  let runtimeCandidates := Metta.Minimal.freshenArgumentTypes
    runtimeAvoid 0 rawRuntimeTypes
  let sourceCandidates := fromLeaTTaAtoms rawRuntimeTypes
  let candidates := fromLeaTTaAtoms runtimeCandidates
  have sourcePresentation : PreparedPackagesPresent oracle space atom
      sourceCandidates := by
    refine ⟨prepared, preparation, ?_⟩
    exact packagesPresent_runtimeGetTypes index prepared
  have rawRoundtrip : toLeaTTaAtoms sourceCandidates = rawRuntimeTypes := by
    exact runtimeOperatorTypes_roundtrip index prepared
  have candidateRoundtrip :
      toLeaTTaAtoms candidates = runtimeCandidates := by
    exact runtimeFreshenedArgumentTypes_roundtrip
      index prepared runtimeAvoid 0
  have runtimeVariants : ArgumentAlphaVariantsRel runtimeAvoid
      sourceCandidates candidates := by
    have variants := freshenArgumentTypes_alphaVariants
      runtimeAvoid 0 sourceCandidates
    rw [rawRoundtrip] at variants
    exact variants
  have privateProtected : ∀ name,
      name ∈ protectedScope ++
        typeServicePrivateAvoid space atom expectedType incoming →
        name ∈ runtimeAvoid := by
    intro name member
    rcases List.mem_append.mp member with protectedMember | privateMember
    · exact List.mem_append_left _ protectedMember
    · exact List.mem_append_right _
        (typeServicePrivateAvoid_runtimeTypeCastProtected atomsEquation
          bindingSupport prepared rawRuntimeTypes name privateMember)
  have variants : ArgumentAlphaVariantsRel
      (protectedScope ++
        typeServicePrivateAvoid space atom expectedType incoming)
      sourceCandidates candidates :=
    argumentAlphaVariantsRel_mono runtimeVariants privateProtected
  have disjoint : ∀ candidate ∈ candidates,
      VarsDisjoint expectedType candidate := by
    intro candidate candidateMember name expectedMember candidateOccurrence
    have candidateNativeOccurrence :
        name ∈ TypeSubst.typeVars candidate := by
      simpa [LeaTTaTypePresentationExactConformance.toLeaTTaAtom_vars_eq_typeVars]
        using candidateOccurrence
    have allCandidateOccurrence :
        name ∈ TypeSubst.typeVarsList candidates :=
      typeVars_mem_typeVarsList_of_mem candidateMember name
        candidateNativeOccurrence
    have expectedProtected : name ∈
        protectedScope ++
          typeServicePrivateAvoid space atom expectedType incoming := by
      apply List.mem_append_right
      apply List.mem_append_left
      rw [typeServiceObservationScope]
      exact typeVars_mem_typeVarsList_of_mem
        (atoms := space.atoms ++ [atom, expectedType])
        (atom := expectedType) (by simp) name
        (by
          simpa [LeaTTaTypePresentationExactConformance.toLeaTTaAtom_vars_eq_typeVars]
            using expectedMember)
    exact
      LeaTTaTypePresentationApplicationExact.ArgumentAlphaVariantsRel.targets_fresh
        variants name allCandidateOccurrence expectedProtected
  have sourceNonempty : sourceCandidates ≠ [] := by
    intro empty
    have runtimeEmpty : rawRuntimeTypes = [] := by
      rw [← rawRoundtrip, empty]
      rfl
    exact Metta.getTypes_ne_nil env (toLeaTTaAtom prepared) runtimeEmpty
  have candidatesNonempty : candidates ≠ [] := by
    intro empty
    have lengthEquation := argumentAlphaVariantsRel_length_eq variants
    rw [empty] at lengthEquation
    exact sourceNonempty (List.eq_nil_of_length_eq_zero lengthEquation)
  have castShape :
      Metta.Minimal.mettaTypeCastAvoiding protectedScope env world
          runtimeBindings (toLeaTTaAtom atom) (toLeaTTaAtom expectedType) =
        Metta.Minimal.matchExpectedType runtimeBindings
          (toLeaTTaAtom expectedType) runtimeCandidates := by
    simp [Metta.Minimal.mettaTypeCastAvoiding, preparationEquation,
      rawRuntimeTypes, runtimeAvoid, runtimeCandidates]
  rw [castShape, ← candidateRoundtrip]
  cases castEquation : Metta.Minimal.matchExpectedType runtimeBindings
      (toLeaTTaAtom expectedType) (toLeaTTaAtoms candidates) with
  | inr runtimeOutput =>
      obtain ⟨before, actualType, after, presentationOutput, output,
          split, beforeFailed, selectedMatch, outputState⟩ :=
        matchExpectedType_success_corePlusR2_exact state expectedType
          candidates disjoint castEquation
      exact .success
        (.success sourcePresentation variants
          (FirstTypeCastSuccessRel.of_split split beforeFailed selectedMatch))
        outputState
  | inl rejected =>
      obtain ⟨rejectedEquation, allFailed⟩ :=
        matchExpectedType_failure_corePlusR2_exact state expectedType
          candidates rejected disjoint castEquation
      rw [rejectedEquation]
      exact PreparedTypeCastOutcomeRuntimeRel.failure sourcePresentation
        variants candidatesNonempty allFailed

/-- The repaired runtime service at the package boundary.  Lookup, type cast,
and expected-aware candidate selection are all the exact prepared relations;
no caller may mix them with a weaker positive or negative candidate interface. -/
def preparedPackageTypeService
    (oracle : TypePreparationOracle) :
    EvalTypeService :=
  packageRecoveringTypeService oracle
    (fun protectedScope space atom expectedType bindings result =>
      PreparedTypeCastRel oracle space atom expectedType bindings result
        protectedScope)
    (PreparedPackageCandidateScanRel oracle)

/-- The exact prepared cast relation is definitionally the cast field of the
repaired package service. -/
@[simp] theorem preparedPackageTypeService_typeCast_eq
    (oracle : TypePreparationOracle) :
    (preparedPackageTypeService oracle).typeCast =
      (fun protectedScope space atom expectedType bindings result =>
        PreparedTypeCastRel oracle space atom expectedType bindings result
          protectedScope) := rfl

/-- **Concrete lookup field of the repaired evaluator service.** -/
theorem preparedPackageTypeService_typesOf_runtime_ofAtomsGT
    {oracle : TypePreparationOracle}
    (space : Space) (groundingTable : Metta.GroundingTable)
    {world : Metta.Minimal.World}
    (realization : TypePreparationRuntimeRealization oracle space world)
    (atom : Atom) :
    let env := Metta.Minimal.MinEnv.ofAtomsGT
      (toLeaTTaAtoms space.atoms) groundingTable
    (preparedPackageTypeService oracle).typesOf space atom
      (fromLeaTTaAtoms
        (Metta.Minimal.getTypes env
          (Metta.Minimal.typePrep world (toLeaTTaAtom atom)))) := by
  dsimp only
  let env := Metta.Minimal.MinEnv.ofAtomsGT
    (toLeaTTaAtoms space.atoms) groundingTable
  obtain ⟨prepared, preparation, preparationEquation⟩ := realization atom
  exact preparedPackagesPresent_runtimeGetTypes
    (typeEnvironmentRel_ofAtomsGT space groundingTable) world atom prepared
      preparation preparationEquation

/-- **Concrete cast field of the repaired evaluator service.**

The surrounding evaluator maintains both the complete presentation state
needed for exact negative evidence and the elementary support inclusion
needed by runtime freshening. -/
theorem preparedPackageTypeService_typeCast_runtime_ofAtomsGT
    {oracle : TypePreparationOracle}
    (space : Space) (groundingTable : Metta.GroundingTable)
    {world : Metta.Minimal.World}
    (realization : TypePreparationRuntimeRealization oracle space world)
    {presentation : TypeSubst} {incoming : Bindings}
    {runtimeBindings : Metta.Bindings}
    (state : TypePresentationSimulationState
      presentation incoming runtimeBindings)
    (bindingSupport : ∀ name, name ∈ specBindingVars incoming →
      name ∈ runtimeBindings.vars)
    (protectedScope : List String) (atom expectedType : Atom) :
    let env := Metta.Minimal.MinEnv.ofAtomsGT
      (toLeaTTaAtoms space.atoms) groundingTable
    PreparedTypeCastOutcomeRuntimeRel oracle space atom expectedType incoming
      (Metta.Minimal.mettaTypeCastAvoiding protectedScope env world
        runtimeBindings (toLeaTTaAtom atom) (toLeaTTaAtom expectedType))
      protectedScope := by
  dsimp only
  exact preparedTypeCast_runtime
    (typeEnvironmentRel_ofAtomsGT space groundingTable) rfl realization
      state bindingSupport atom expectedType protectedScope

/-- **Concrete candidate-scan field of the repaired evaluator service.**

For a canonical runtime environment and a symbol-headed application, the
actual prepared `getTypes` list is recovered through one exact package list;
the package scan produces a specification outcome related to the executable's
expected-aware selector at the complete seal observation scope.  Type-cast
correspondence is supplied independently by the preceding field theorem. -/
theorem preparedPackageTypeService_candidateScan_runtime_ofAtomsGT_avoiding
    {oracle : TypePreparationOracle}
    (functional : TypePreparationFunctional oracle)
    (space : Space) (groundingTable : Metta.GroundingTable)
    {world : Metta.Minimal.World}
    (realization : TypePreparationRuntimeRealization oracle space world)
    (operator : String) (expectedType : Atom) (arguments : List Atom)
    (incoming : Bindings) {initialPresentation : TypeSubst}
    {runtimeInitial : Metta.Bindings}
    (initial : InitialTypeBindingPresentationRel initialPresentation incoming)
    (inputState : TypePresentationSimulationState initialPresentation
      incoming runtimeInitial)
    (bindingSupport : ∀ name, name ∈ specBindingVars incoming →
      name ∈ runtimeInitial.vars) :
    let env := Metta.Minimal.MinEnv.ofAtomsGT
      (toLeaTTaAtoms space.atoms) groundingTable
    let expression := Atom.expression (.symbol operator :: arguments)
    let presented := fromLeaTTaAtoms
      (Metta.Minimal.getTypes env
        (Metta.Minimal.typePrep world (.sym operator)))
    ∃ outcome,
      (preparedPackageTypeService oracle).candidateScan
        space expression expectedType incoming presented outcome ∧
      FunctionCandidateScanOutcomeRuntimeRel
        (typeServiceObservationScope space expression expectedType)
        expression incoming outcome
        (Metta.Minimal.selectFunctionTypeForExpectedFrom env world
          (.sym operator) (toLeaTTaAtoms arguments)
          (toLeaTTaAtom expectedType) runtimeInitial) := by
  dsimp only
  let env := Metta.Minimal.MinEnv.ofAtomsGT
    (toLeaTTaAtoms space.atoms) groundingTable
  have index : TypeEnvironmentRel space env := by
    exact typeEnvironmentRel_ofAtomsGT space groundingTable
  obtain ⟨prepared, packages, outcome, preparation, packageRelation,
      packageScan, runtime⟩ :=
    preparedPackageCandidateScan_runtime_symbol_avoiding functional index rfl
      realization operator expectedType arguments incoming initial inputState
        bindingSupport
  obtain ⟨realizedPrepared, realizedPreparation,
      preparationEquation⟩ := realization (.symbol operator)
  have preparedEquation : prepared = realizedPrepared :=
    functional space (.symbol operator) prepared realizedPrepared
      preparation realizedPreparation
  subst realizedPrepared
  have runtimePresentation : PackagesPresent space prepared
      (fromLeaTTaAtoms
        (Metta.Minimal.getTypes env
          (Metta.Minimal.typePrep world (.sym operator)))) := by
    have preparationEquation' :
        Metta.Minimal.typePrep world (.sym operator) =
          toLeaTTaAtom prepared := by
      simpa [toLeaTTaAtom] using preparationEquation
    rw [preparationEquation']
    exact packagesPresent_runtimeGetTypes index prepared
  obtain ⟨runtimePackages, runtimePackageRelation, runtimeAlpha⟩ :=
    runtimePresentation
  have packageAlpha : List.Forall₂ ObservedTypeAlphaRel
      (observedTypes packages)
      (fromLeaTTaAtoms
        (Metta.Minimal.getTypes env
          (Metta.Minimal.typePrep world (.sym operator)))) :=
    observedTypeAlphaList_trans
      (runtimeTypePackages_alpha_unique index packageRelation
        runtimePackageRelation)
      runtimeAlpha
  refine ⟨outcome, ?_, runtime⟩
  exact ⟨.symbol operator, arguments, prepared, packages, rfl,
    preparation, packageRelation, packageAlpha, packageScan⟩

/-- Evaluator-aligned companion of the concrete candidate-scan field.  It
recovers the same package-facing service derivation and retains the selected
arrow's literal runtime agreement for the head-cast seam. -/
theorem preparedPackageTypeService_candidateScan_runtime_ofAtomsGT_aligned
    {oracle : TypePreparationOracle}
    (functional : TypePreparationFunctional oracle)
    (space : Space) (groundingTable : Metta.GroundingTable)
    {world : Metta.Minimal.World}
    (realization : TypePreparationRuntimeRealization oracle space world)
    (operator : String) (expectedType : Atom) (arguments : List Atom)
    (incoming : Bindings) {initialPresentation : TypeSubst}
    {runtimeInitial : Metta.Bindings}
    (initial : InitialTypeBindingPresentationRel initialPresentation incoming)
    (inputState : TypePresentationSimulationState initialPresentation
      incoming runtimeInitial)
    (bindingSupport : ∀ name, name ∈ specBindingVars incoming →
      name ∈ runtimeInitial.vars) :
    let env := Metta.Minimal.MinEnv.ofAtomsGT
      (toLeaTTaAtoms space.atoms) groundingTable
    let expression := Atom.expression (.symbol operator :: arguments)
    let presented := fromLeaTTaAtoms
      (Metta.Minimal.getTypes env
        (Metta.Minimal.typePrep world (.sym operator)))
    ∃ outcome,
      (preparedPackageTypeService oracle).candidateScan
        space expression expectedType incoming presented outcome ∧
      FunctionCandidateScanOutcomeRuntimeRelWith
        SelectedTypePolicyRuntimeExactRel
        (typeServiceObservationScope space expression expectedType)
        expression incoming outcome
        (Metta.Minimal.selectFunctionTypeForExpectedFrom env world
          (.sym operator) (toLeaTTaAtoms arguments)
          (toLeaTTaAtom expectedType) runtimeInitial) := by
  dsimp only
  let env := Metta.Minimal.MinEnv.ofAtomsGT
    (toLeaTTaAtoms space.atoms) groundingTable
  have index : TypeEnvironmentRel space env := by
    exact typeEnvironmentRel_ofAtomsGT space groundingTable
  obtain ⟨prepared, packages, outcome, preparation, packageRelation,
      packageScan, runtime⟩ :=
    preparedPackageCandidateScan_runtime_symbol_aligned functional index rfl
      realization operator expectedType arguments incoming initial inputState
        bindingSupport
  obtain ⟨realizedPrepared, realizedPreparation,
      preparationEquation⟩ := realization (.symbol operator)
  have preparedEquation : prepared = realizedPrepared :=
    functional space (.symbol operator) prepared realizedPrepared
      preparation realizedPreparation
  subst realizedPrepared
  have runtimePresentation : PackagesPresent space prepared
      (fromLeaTTaAtoms
        (Metta.Minimal.getTypes env
          (Metta.Minimal.typePrep world (.sym operator)))) := by
    have preparationEquation' :
        Metta.Minimal.typePrep world (.sym operator) =
          toLeaTTaAtom prepared := by
      simpa [toLeaTTaAtom] using preparationEquation
    rw [preparationEquation']
    exact packagesPresent_runtimeGetTypes index prepared
  obtain ⟨runtimePackages, runtimePackageRelation, runtimeAlpha⟩ :=
    runtimePresentation
  have packageAlpha : List.Forall₂ ObservedTypeAlphaRel
      (observedTypes packages)
      (fromLeaTTaAtoms
        (Metta.Minimal.getTypes env
          (Metta.Minimal.typePrep world (.sym operator)))) :=
    observedTypeAlphaList_trans
      (runtimeTypePackages_alpha_unique index packageRelation
        runtimePackageRelation)
      runtimeAlpha
  refine ⟨outcome, ?_, runtime⟩
  exact ⟨.symbol operator, arguments, prepared, packages, rfl,
    preparation, packageRelation, packageAlpha, packageScan⟩

/-! ## Complete runtime service boundary -/

/-- The three exact field correspondences required by one concrete repaired
runtime type service.  This is a theorem-facing bundle, not a second service:
all data still comes from `preparedPackageTypeService`, while the fields record
that its lookup, cast, and expected-aware scan are realized by the same
`MinEnv.ofAtomsGT` environment and preparation oracle. -/
structure PreparedPackageTypeServiceRuntimeConformance
    (oracle : TypePreparationOracle)
    (space : Space) (groundingTable : Metta.GroundingTable)
    (world : Metta.Minimal.World) : Prop where
  typesOf : ∀ atom,
    let env := Metta.Minimal.MinEnv.ofAtomsGT
      (toLeaTTaAtoms space.atoms) groundingTable
    (preparedPackageTypeService oracle).typesOf space atom
      (fromLeaTTaAtoms
        (Metta.Minimal.getTypes env
          (Metta.Minimal.typePrep world (toLeaTTaAtom atom))))
  typeCast : ∀ {presentation : TypeSubst} {incoming : Bindings}
      {runtimeBindings : Metta.Bindings},
    TypePresentationSimulationState presentation incoming runtimeBindings →
    (∀ name, name ∈ specBindingVars incoming →
      name ∈ runtimeBindings.vars) →
    ∀ protectedScope atom expectedType,
      let env := Metta.Minimal.MinEnv.ofAtomsGT
        (toLeaTTaAtoms space.atoms) groundingTable
      PreparedTypeCastOutcomeRuntimeRel oracle space atom expectedType incoming
        (Metta.Minimal.mettaTypeCastAvoiding protectedScope env world
          runtimeBindings (toLeaTTaAtom atom) (toLeaTTaAtom expectedType))
        protectedScope
  candidateScan : ∀ operator expectedType arguments incoming
      {initialPresentation : TypeSubst}
      {runtimeInitial : Metta.Bindings},
    InitialTypeBindingPresentationRel initialPresentation incoming →
    TypePresentationSimulationState initialPresentation incoming
      runtimeInitial →
    (∀ name, name ∈ specBindingVars incoming →
      name ∈ runtimeInitial.vars) →
    let env := Metta.Minimal.MinEnv.ofAtomsGT
      (toLeaTTaAtoms space.atoms) groundingTable
    let expression := Atom.expression (.symbol operator :: arguments)
    let presented := fromLeaTTaAtoms
      (Metta.Minimal.getTypes env
        (Metta.Minimal.typePrep world (.sym operator)))
    ∃ outcome,
      (preparedPackageTypeService oracle).candidateScan
        space expression expectedType incoming presented outcome ∧
      FunctionCandidateScanOutcomeRuntimeRel
        (typeServiceObservationScope space expression expectedType)
        expression incoming outcome
        (Metta.Minimal.selectFunctionTypeForExpectedFrom env world
          (.sym operator) (toLeaTTaAtoms arguments)
          (toLeaTTaAtom expectedType) runtimeInitial)

/-- **A1 capstone.** One functional preparation realization supplies the
complete repaired runtime type-service boundary over a canonical environment.
No field is assumed: each is discharged by the corresponding exact theorem
above. -/
theorem preparedPackageTypeService_runtimeConformance_ofAtomsGT
    {oracle : TypePreparationOracle}
    (functional : TypePreparationFunctional oracle)
    (space : Space) (groundingTable : Metta.GroundingTable)
    {world : Metta.Minimal.World}
    (realization : TypePreparationRuntimeRealization oracle space world) :
    PreparedPackageTypeServiceRuntimeConformance
      oracle space groundingTable world where
  typesOf atom :=
    preparedPackageTypeService_typesOf_runtime_ofAtomsGT
      space groundingTable realization atom
  typeCast state bindingSupport protectedScope atom expectedType :=
    preparedPackageTypeService_typeCast_runtime_ofAtomsGT
      space groundingTable realization state bindingSupport protectedScope
        atom expectedType
  candidateScan operator expectedType arguments incoming initialPresentation
      runtimeInitial initial inputState bindingSupport :=
    preparedPackageTypeService_candidateScan_runtime_ofAtomsGT_avoiding
      functional space groundingTable realization operator expectedType
        arguments incoming (initialPresentation := initialPresentation)
          (runtimeInitial := runtimeInitial) initial inputState bindingSupport

/-! ## Boundary canaries -/

private def identityPreparation : TypePreparationOracle where
  prepare := fun _ atom prepared => prepared = atom

private def nullaryExpression : Atom :=
  .expression [.symbol "f"]

private def nullaryFunctionType : Atom :=
  .expression [.symbol "->", .symbol "R"]

private def nullaryPolicy : SelectedTypePolicy :=
  ⟨nullaryFunctionType, [], .symbol "R", rfl⟩

private theorem noArgumentPreparation :
    PreparedArgumentPackageCandidates identityPreparation Space.empty []
      [] [] [] := by
  refine ⟨[], [], .nil, .nil, .nil, ?_⟩
  exact
    { link := rfl
      avoidFormals := by simp [AtomsAvoid, TypeSubst.typeVarsList]
      avoidInitial := by
        constructor <;> simp [TypeSubst.typeVarsList]
      families := by simp }

private theorem nullaryApplicabilitySuccess :
    PreparedCandidateApplicabilityRel identityPreparation Space.empty
      nullaryExpression nullaryFunctionType Atom.undefinedType Bindings.empty
      [] (.success nullaryPolicy Bindings.empty) := by
  refine ⟨.symbol "f", [], [], .symbol "R", [], ⟨[[]], []⟩,
    ⟨some [], []⟩, [], rfl, ?_⟩
  refine ⟨rfl, rfl, noArgumentPreparation, ?_, ?_, ?_, rfl, rfl, ?_⟩
  · simp [FreshFamiliesSeparated, AtomsAvoid, TypeSubst.typeVarsList]
  · exact .noArguments [] 0 []
  · exact .matched (.undefinedLeft [] (.symbol "R"))
  · exact presentationExtension_append Bindings.empty []

private theorem nullaryOperatorLocalization :
    OperatorAlphaVariantsRel [] [nullaryFunctionType]
      [nullaryFunctionType] := by
  apply OperatorAlphaVariantsRel.cons
  · refine ⟨id, fun {_ _} equality => equality, ?_, ?_⟩
    · simp [nullaryFunctionType, renameTypeVars]
    · simp [nullaryFunctionType, TypeSubst.typeVars]
  · exact .nil

/-- Positive: a closed nullary arrow is selected through the exact package
service and exposes an inert empty private presentation. -/
theorem prepared_package_scan_selects_closed_nullary :
    PreparedPackageCandidateScanRel identityPreparation Space.empty
      nullaryExpression Atom.undefinedType Bindings.empty
      [publishedPackage nullaryFunctionType]
      (.success nullaryPolicy Bindings.empty) := by
  refine ⟨[], [nullaryFunctionType],
    initialTypeBindingPresentationRel_canonical TypeSubst.normal_empty, ?_, ?_⟩
  · simpa [typeServicePrivateAvoid, typeServiceObservationScope,
      nullaryExpression, Bindings.empty, observedTypes, publishedPackage,
      Space.empty, TypeSubst.typeVars, TypeSubst.typeVarsList,
      specBindingVars, Atom.undefinedType,
      Spec.Type.Presentation.RuntimeTypePackage.published] using
      nullaryOperatorLocalization
  · exact FunctionCandidateScanRel.functionSuccess
      (argumentTypes := []) (returnType := .symbol "R") rfl
      nullaryApplicabilitySuccess

/-- Negative: a bare arrow has no return component, so it cannot fabricate a
function policy; it remains the tuple-eligible non-function case. -/
theorem prepared_package_scan_rejects_bare_arrow :
    PreparedPackageCandidateScanRel identityPreparation Space.empty
      nullaryExpression Atom.undefinedType Bindings.empty
      [publishedPackage (.expression [.symbol "->"])]
      (.exhausted [] true) := by
  let bareArrow : Atom := .expression [.symbol "->"]
  have localized : OperatorAlphaVariantsRel [] [bareArrow] [bareArrow] := by
    apply OperatorAlphaVariantsRel.cons
    · refine ⟨id, fun {_ _} equality => equality, ?_, ?_⟩
      · simp [bareArrow, renameTypeVars]
      · simp [bareArrow, TypeSubst.typeVars]
    · exact .nil
  refine ⟨[], [bareArrow],
    initialTypeBindingPresentationRel_canonical TypeSubst.normal_empty, ?_, ?_⟩
  · simpa [bareArrow, typeServicePrivateAvoid,
      typeServiceObservationScope, nullaryExpression, Bindings.empty,
      Space.empty, TypeSubst.typeVars, TypeSubst.typeVarsList,
      specBindingVars, Atom.undefinedType,
      observedTypes, publishedPackage,
      Spec.Type.Presentation.RuntimeTypePackage.published] using localized
  · apply FunctionCandidateScanRel.nonFunctionExhausted
    · rintro ⟨argumentTypes, returnType, function⟩
      simp [bareArrow, FunctionTypeRel] at function
    · exact .nil

end Mettapedia.Languages.MeTTa.HE.LeaTTaTypeServiceConformance
