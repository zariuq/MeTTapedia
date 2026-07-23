import Mettapedia.Languages.MeTTa.HE.LeaTTaEvaluatorConfigurationConformance

/-!
# Scoped conformance of the selected operator-head cast

The expected-aware application worker evaluates a selected symbol head by
casting it against the selected arrow.  Candidate selection and this second
cast freshen private type variables independently, so their binding records
must be compared through finite solution theories at the protected evaluator
scope rather than by literal private-name equality.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaOperatorHeadCastConformance

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open LeaTTaBridge
open LeaTTaBranchLocalTypeScanConformance
open LeaTTaEvaluatorConfigurationConformance
open LeaTTaMinimalInstructionConformance
open LeaTTaSpecTypeService
open LeaTTaTypeConformance
open LeaTTaTypePresentationApplicationExact
open LeaTTaTypePresentationExactConformance
open LeaTTaTypePresentationFoldConformance
open LeaTTaTypePresentationRecursiveExact
open LeaTTaTypeServiceConformance
open Spec.Eval
open Spec.Eval.Minimal
open Spec.Type
open Spec.Bindings.ScopeObservation
open Spec.Type.Presentation
open Spec.Type.Presentation.Alpha
open Spec.Type.Presentation.Exact
open Spec.Type.Presentation.Freshness
open Spec.Type.Presentation.MatchSolutionTheory
open Spec.Type.Presentation.ScopeObservation
open Spec.Type.Presentation.Theory
open Spec.Type.RuntimeRefinement

/-- Pointwise private-alpha candidates extend two scope-equivalent input
theories by equivalent constraints.  Freshness is deliberately supplied in
the representation native to each side: finite-presentation support on the
specification side and runtime binding support on the executable side. -/
theorem privateCandidateFamilyAlpha_constraintTheories
    {fixedScope observationScope : List String}
    {leftIncoming rightIncoming : TypeSubst}
    {rightSpec : Bindings} {runtimeBindings : Metta.Bindings}
    {expected : Atom} {leftCandidates rightCandidates : List Atom}
    (incomingTheory : TypePresentationTheoryEquivAt fixedScope
      leftIncoming rightIncoming)
    (rightState : TypePresentationSimulationState
      rightIncoming rightSpec runtimeBindings)
    (candidates : PrivateCandidateFamilyAlphaRel fixedScope
      leftCandidates rightCandidates)
    (leftFresh : ∀ candidate ∈ leftCandidates, ∀ name,
      name ∈ TypeSubst.typeVars candidate →
        name ∉ specBindingVars (⟨leftIncoming, []⟩ : Bindings))
    (rightFresh : ∀ candidate ∈ rightCandidates, ∀ name,
      name ∈ TypeSubst.typeVars candidate →
        name ∉ runtimeBindings.vars)
    (expectedObserved : ∀ name,
      name ∈ TypeSubst.typeVars expected → name ∈ fixedScope)
    (observationObserved : ∀ name,
      name ∈ observationScope → name ∈ fixedScope) :
    List.Forall₂
      (fun leftActual rightActual =>
        TypeConstraintTheoryEquivAt observationScope
          leftIncoming expected leftActual
          rightIncoming expected rightActual)
      leftCandidates rightCandidates := by
  induction candidates with
  | nil => exact .nil
  | @cons leftActual rightActual leftTail rightTail head tail ih =>
      apply List.Forall₂.cons
      · apply TypeConstraintTheoryEquivAt.of_scopedIncoming_privateCandidateAlpha_runtimeSupport
          incomingTheory rightState head
        · exact leftFresh leftActual (by simp)
        · exact rightFresh rightActual (by simp)
        · intro name member
          exact member
        · exact expectedObserved
        · exact observationObserved
      · apply ih
        · intro candidate member
          exact leftFresh candidate (by simp [member])
        · intro candidate member
          exact rightFresh candidate (by simp [member])

/-- The reusable preparation seam shared by the success and failure arms of
the protected operator-head cast.  It retains exact finite presentations on
each side, pointwise constraint equivalence across the boundary, and the
literal runtime cast equation. -/
def PreparedTypeCastCandidateAlignment
    (oracle : TypePreparationOracle) (space : Space)
    (env : Metta.Minimal.MinEnv) (world : Metta.Minimal.World)
    (protectedScope : List String) (atom expectedType : Atom)
    (incoming : Bindings) (runtimeIncoming : Metta.Bindings) : Prop :=
  ∃ sourceCandidates specCandidates runtimeCandidates : List Atom,
    ∃ leftPresentation rightPresentation : TypeSubst,
    ∃ rightBindings : Bindings,
      PreparedPackagesPresent oracle space atom sourceCandidates ∧
      ArgumentAlphaVariantsRel
        (protectedScope ++
          typeServicePrivateAvoid space atom expectedType incoming)
        sourceCandidates specCandidates ∧
      TypeBindingPresentationRel leftPresentation incoming ∧
      TypeBindingPresentationRel rightPresentation rightBindings ∧
      TypePresentationSimulationState
        rightPresentation rightBindings runtimeIncoming ∧
      PrivateCandidateFamilyAlphaRel
        (protectedScope ++ TypeSubst.typeVars expectedType)
        specCandidates runtimeCandidates ∧
      List.Forall₂
        (fun leftActual rightActual =>
          TypeConstraintTheoryEquivAt protectedScope
            leftPresentation expectedType leftActual
            rightPresentation expectedType rightActual)
        specCandidates runtimeCandidates ∧
      (∀ candidate ∈ runtimeCandidates,
        VarsDisjoint expectedType candidate) ∧
      Metta.Minimal.mettaTypeCastAvoiding protectedScope env world
          runtimeIncoming (toLeaTTaAtom atom) (toLeaTTaAtom expectedType) =
        Metta.Minimal.matchExpectedType runtimeIncoming
          (toLeaTTaAtom expectedType) (toLeaTTaAtoms runtimeCandidates)

/-- Realize the common candidate-alignment seam once.  The specification and
runtime freshen independently, so the returned correspondence is pointwise
private alpha plus scoped constraint theory rather than list equality. -/
theorem preparedTypeCast_candidateAlignment
    {oracle : TypePreparationOracle}
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env)
    {world : Metta.Minimal.World}
    (realization : TypePreparationRuntimeRealization oracle space world)
    {protectedScope : List String} {atom expectedType : Atom}
    {incoming : Bindings} {runtimeIncoming : Metta.Bindings}
    (input : ScopedEvaluatorBindingRuntimeRel
      (protectedScope ++ TypeSubst.typeVars expectedType)
      incoming runtimeIncoming) :
    PreparedTypeCastCandidateAlignment oracle space env world protectedScope
      atom expectedType incoming runtimeIncoming := by
  rcases input with
    ⟨inputPresentation, inputSolutions, inputScoped⟩
  rcases inputScoped with
    ⟨inputNormal, runtimePresentation, runtimeSpecBindings,
      runtimeInputState, inputTheory⟩
  obtain ⟨prepared, preparation, preparationEquation⟩ := realization atom
  let rawRuntimeTypes :=
    Metta.Minimal.getTypes env (toLeaTTaAtom prepared)
  let runtimeAvoid := protectedScope ++
    Metta.Minimal.typeCastInferenceAvoid env
      (toLeaTTaAtom prepared) (toLeaTTaAtom atom)
      (toLeaTTaAtom expectedType) runtimeIncoming rawRuntimeTypes
  let runtimeFresh := Metta.Minimal.freshenArgumentTypes
    runtimeAvoid 0 rawRuntimeTypes
  let sourceCandidates := fromLeaTTaAtoms rawRuntimeTypes
  let runtimeCandidates := fromLeaTTaAtoms runtimeFresh
  let specAvoid :=
    (protectedScope ++
      typeServicePrivateAvoid space atom expectedType incoming) ++
      specBindingVars (⟨inputPresentation, []⟩ : Bindings)
  let specCandidates := fromLeaTTaAtoms
    (Metta.Minimal.freshenArgumentTypes specAvoid 0
      (toLeaTTaAtoms sourceCandidates))
  have sourcePresent : PreparedPackagesPresent oracle space atom
      sourceCandidates := by
    refine ⟨prepared, preparation, ?_⟩
    exact packagesPresent_runtimeGetTypes index prepared
  have rawRoundtrip : toLeaTTaAtoms sourceCandidates = rawRuntimeTypes :=
    runtimeOperatorTypes_roundtrip index prepared
  have runtimeRoundtrip :
      toLeaTTaAtoms runtimeCandidates = runtimeFresh :=
    runtimeFreshenedArgumentTypes_roundtrip index prepared runtimeAvoid 0
  have runtimeVariants : ArgumentAlphaVariantsRel runtimeAvoid
      sourceCandidates runtimeCandidates := by
    have variants := freshenArgumentTypes_alphaVariants
      runtimeAvoid 0 sourceCandidates
    rw [rawRoundtrip] at variants
    exact variants
  have specVariantsLarge : ArgumentAlphaVariantsRel specAvoid
      sourceCandidates specCandidates := by
    have variants := freshenArgumentTypes_alphaVariants
      specAvoid 0 sourceCandidates
    simpa [specCandidates] using variants
  have specVariants : ArgumentAlphaVariantsRel
      (protectedScope ++
        typeServicePrivateAvoid space atom expectedType incoming)
      sourceCandidates specCandidates :=
    argumentAlphaVariantsRel_mono specVariantsLarge
      (fun name member => List.mem_append_left _ member)
  let constraintScope :=
    protectedScope ++ TypeSubst.typeVars expectedType
  have specVariantsConstraint : ArgumentAlphaVariantsRel constraintScope
      sourceCandidates specCandidates :=
    argumentAlphaVariantsRel_mono specVariantsLarge (by
      intro name member
      rcases List.mem_append.mp member with protectedMember | expectedMember
      · exact List.mem_append_left _
          (List.mem_append_left _ protectedMember)
      · apply List.mem_append_left
        apply List.mem_append_right
        apply List.mem_append_left
        rw [typeServiceObservationScope]
        exact Spec.Type.Presentation.Freshness.typeVars_mem_typeVarsList_of_mem
          (atoms := space.atoms ++ [atom, expectedType])
          (atom := expectedType) (by simp) name expectedMember)
  have runtimeVariantsConstraint : ArgumentAlphaVariantsRel constraintScope
      sourceCandidates runtimeCandidates :=
    argumentAlphaVariantsRel_mono runtimeVariants (by
      intro name member
      rcases List.mem_append.mp member with protectedMember | expectedMember
      · exact List.mem_append_left _ protectedMember
      · apply List.mem_append_right
        unfold Metta.Minimal.typeCastInferenceAvoid
        apply List.mem_append_left
        apply List.mem_append_left
        apply List.mem_append_left
        simpa [LeaTTaTypePresentationExactConformance.toLeaTTaAtom_vars_eq_typeVars]
          using expectedMember)
  have candidateAlpha : PrivateCandidateFamilyAlphaRel constraintScope
      specCandidates runtimeCandidates :=
    privateCandidateFamilyAlpha_of_variants
      (argumentAlphaVariantsRel_toForall₂ specVariantsConstraint)
      (argumentAlphaVariantsRel_toForall₂ runtimeVariantsConstraint)
  have specTargetsFresh : ∀ name,
      name ∈ TypeSubst.typeVarsList specCandidates →
        name ∉ specBindingVars
          (⟨inputPresentation, []⟩ : Bindings) := by
    intro name member support
    exact (LeaTTaTypePresentationApplicationExact.ArgumentAlphaVariantsRel.targets_fresh
      specVariantsLarge name member)
      (List.mem_append_right _ support)
  have runtimeTargetsFresh : ∀ name,
      name ∈ TypeSubst.typeVarsList runtimeCandidates →
        name ∉ runtimeIncoming.vars := by
    intro name member support
    exact (LeaTTaTypePresentationApplicationExact.ArgumentAlphaVariantsRel.targets_fresh
      runtimeVariants name member)
      (List.mem_append_right protectedScope
        (by simp [Metta.Minimal.typeCastInferenceAvoid, support]))
  have constraints : List.Forall₂
      (fun leftActual rightActual =>
        TypeConstraintTheoryEquivAt protectedScope
          inputPresentation expectedType leftActual
          runtimePresentation expectedType rightActual)
      specCandidates runtimeCandidates := by
    apply privateCandidateFamilyAlpha_constraintTheories
      inputTheory runtimeInputState candidateAlpha
    · intro candidate candidateMember name nameMember
      exact specTargetsFresh name
        (Spec.Type.Presentation.Freshness.typeVars_mem_typeVarsList_of_mem
          candidateMember name nameMember)
    · intro candidate candidateMember name nameMember
      exact runtimeTargetsFresh name
        (Spec.Type.Presentation.Freshness.typeVars_mem_typeVarsList_of_mem
          candidateMember name nameMember)
    · intro name member
      exact List.mem_append_right protectedScope member
    · intro name member
      exact List.mem_append_left _ member
  have runtimeDisjoint : ∀ candidate ∈ runtimeCandidates,
      VarsDisjoint expectedType candidate := by
    intro candidate candidateMember name expectedMember candidateMember'
    have allCandidateMember : name ∈
        TypeSubst.typeVarsList runtimeCandidates :=
      Spec.Type.Presentation.Freshness.typeVars_mem_typeVarsList_of_mem
        candidateMember name (by
          simpa [LeaTTaTypePresentationExactConformance.toLeaTTaAtom_vars_eq_typeVars]
            using candidateMember')
    exact (LeaTTaTypePresentationApplicationExact.ArgumentAlphaVariantsRel.targets_fresh
      runtimeVariants name allCandidateMember)
      (List.mem_append_right protectedScope
        (by simp [Metta.Minimal.typeCastInferenceAvoid, expectedMember]))
  have castShape :
      Metta.Minimal.mettaTypeCastAvoiding protectedScope env world
          runtimeIncoming (toLeaTTaAtom atom) (toLeaTTaAtom expectedType) =
        Metta.Minimal.matchExpectedType runtimeIncoming
          (toLeaTTaAtom expectedType) runtimeFresh := by
    simp [Metta.Minimal.mettaTypeCastAvoiding, preparationEquation,
      rawRuntimeTypes, runtimeAvoid, runtimeFresh]
  have castEquation :
      Metta.Minimal.mettaTypeCastAvoiding protectedScope env world
          runtimeIncoming (toLeaTTaAtom atom) (toLeaTTaAtom expectedType) =
        Metta.Minimal.matchExpectedType runtimeIncoming
          (toLeaTTaAtom expectedType) (toLeaTTaAtoms runtimeCandidates) := by
    rw [runtimeRoundtrip]
    exact castShape
  exact ⟨sourceCandidates, specCandidates, runtimeCandidates,
    inputPresentation, runtimePresentation, runtimeSpecBindings,
    sourcePresent, specVariants, ⟨inputNormal, inputSolutions⟩,
    LeaTTaTypeServiceConformance.TypePresentationSimulationState.toTypeBindingPresentationRel
      runtimeInputState,
    runtimeInputState,
    candidateAlpha, constraints, runtimeDisjoint, castEquation⟩

/-- Pointwise private-alpha correspondence preserves membership from the
runtime family back to the specification family at the same list position. -/
theorem PrivateCandidateFamilyAlphaRel.exists_left_of_mem_right
    {fixedScope : List String} {leftCandidates rightCandidates : List Atom}
    (relation : PrivateCandidateFamilyAlphaRel
      fixedScope leftCandidates rightCandidates) :
    ∀ {right}, right ∈ rightCandidates →
      ∃ left, left ∈ leftCandidates ∧
        PrivateCandidateAlphaRel fixedScope left right := by
  intro right member
  induction relation with
  | nil => simp at member
  | @cons leftHead rightHead leftTail rightTail head tail ih =>
      rcases List.mem_cons.mp member with rfl | tailMember
      · exact ⟨leftHead, by simp, head⟩
      · obtain ⟨left, leftMember, related⟩ := ih tailMember
        exact ⟨left, by simp [leftMember], related⟩

/-- Pointwise equivalence of complete input-plus-constraint theories
transports an all-failed cast ledger from right to left without reopening the
matcher implementation. -/
theorem typeCastAllFailures_left_of_constraints
    {scope : List String}
    {leftPresentation rightPresentation : TypeSubst}
    {leftBindings rightBindings : Bindings}
    {leftExpected rightExpected : Atom}
    {leftCandidates rightCandidates : List Atom}
    (leftState : TypeBindingPresentationRel
      leftPresentation leftBindings)
    (rightState : TypeBindingPresentationRel
      rightPresentation rightBindings)
    (constraints : List.Forall₂ (fun leftActual rightActual =>
      TypeConstraintTheoryEquivAt scope
        leftPresentation leftExpected leftActual
        rightPresentation rightExpected rightActual)
      leftCandidates rightCandidates)
    (rightFailed : ∀ rightActual ∈ rightCandidates, ∀ output,
      ¬CorePlusR2TypeMatchRel
        rightExpected rightActual rightBindings output) :
    ∀ leftActual ∈ leftCandidates, ∀ output,
      ¬CorePlusR2TypeMatchRel
        leftExpected leftActual leftBindings output := by
  induction constraints with
  | nil => simp
  | @cons leftHead rightHead leftTail rightTail head tail ih =>
      intro leftActual member output leftMatch
      rcases List.mem_cons.mp member with rfl | tailMember
      · obtain ⟨rightOutput, rightMatch⟩ :=
          typeBindingPresentationRel_constraintMatch_exists
            leftState rightState head leftMatch
        exact rightFailed rightHead (by simp) rightOutput rightMatch
      · exact ih
          (fun rightActual rightMember =>
            rightFailed rightActual (by simp [rightMember]))
          leftActual tailMember output leftMatch

/-- A failed protected runtime cast yields the exact specification failure
ledger over its independently fresh candidate family.  Candidate order and
multiplicity remain visible through the runtime-list equation; diagnostic
actual types are related fieldwise by private alpha. -/
theorem preparedTypeCast_runtime_scoped_failure
    {oracle : TypePreparationOracle}
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env)
    {world : Metta.Minimal.World}
    (realization : TypePreparationRuntimeRealization oracle space world)
    {protectedScope : List String} {atom expectedType : Atom}
    {incoming : Bindings} {runtimeIncoming : Metta.Bindings}
    {rejected : List Metta.Atom}
    (input : ScopedEvaluatorBindingRuntimeRel
      (protectedScope ++ TypeSubst.typeVars expectedType)
      incoming runtimeIncoming)
    (castFailure : Metta.Minimal.mettaTypeCastAvoiding protectedScope env world
      runtimeIncoming (toLeaTTaAtom atom) (toLeaTTaAtom expectedType) =
        .inl rejected) :
    ∃ specCandidates runtimeCandidates,
      rejected = toLeaTTaAtoms runtimeCandidates ∧
        PrivateCandidateFamilyAlphaRel
          (protectedScope ++ TypeSubst.typeVars expectedType)
          specCandidates runtimeCandidates ∧
        ∀ runtimeActual ∈ runtimeCandidates,
          ∃ specActual,
            specActual ∈ specCandidates ∧
              PrivateCandidateAlphaRel
                (protectedScope ++ TypeSubst.typeVars expectedType)
                specActual runtimeActual ∧
              PreparedTypeCastRel oracle space atom expectedType incoming
                (mkError atom (.badType expectedType specActual), incoming)
                protectedScope := by
  rcases preparedTypeCast_candidateAlignment index realization input with
    ⟨sourceCandidates, specCandidates, runtimeCandidates,
      _leftPresentation, _rightPresentation, _rightBindings,
      sourcePresent, specVariants, leftInput, rightInput, runtimeInputState,
      candidateAlpha, constraints, runtimeDisjoint, castEquation⟩
  rw [castEquation] at castFailure
  obtain ⟨rejectedEquation, runtimeAllFailed⟩ :=
    matchExpectedType_failure_corePlusR2_exact runtimeInputState expectedType
      runtimeCandidates rejected runtimeDisjoint castFailure
  have specAllFailed : ∀ candidate ∈ specCandidates, ∀ output,
      ¬CorePlusR2TypeMatchRel expectedType candidate incoming output :=
    typeCastAllFailures_left_of_constraints leftInput rightInput constraints
      runtimeAllFailed
  refine ⟨specCandidates, runtimeCandidates, rejectedEquation,
    candidateAlpha, ?_⟩
  intro runtimeActual runtimeMember
  obtain ⟨specActual, specMember, actualAlpha⟩ :=
    PrivateCandidateFamilyAlphaRel.exists_left_of_mem_right
      candidateAlpha runtimeMember
  exact ⟨specActual, specMember, actualAlpha,
    PreparedTypeCastRel.failure sourcePresent specVariants specMember
      specAllFailed⟩

/-- A successful protected runtime cast can be replayed by the prepared
specification service from any input binding theory that agrees with the
runtime on the protected scope and on every variable of the expected type.

The specification candidate family is chosen fresh from its own finite input
presentation.  The runtime family is fresh from the runtime binding support.
Pointwise constraint transport then preserves declaration order and the first
successful candidate without identifying either family of private names. -/
theorem preparedTypeCast_runtime_scoped_success
    {oracle : TypePreparationOracle}
    {space : Space} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env)
    {world : Metta.Minimal.World}
    (realization : TypePreparationRuntimeRealization oracle space world)
    {protectedScope : List String} {atom expectedType : Atom}
    {incoming : Bindings}
    {runtimeIncoming runtimeOutput : Metta.Bindings}
    (input : ScopedEvaluatorBindingRuntimeRel
      (protectedScope ++ TypeSubst.typeVars expectedType)
      incoming runtimeIncoming)
    (castSuccess : Metta.Minimal.mettaTypeCastAvoiding protectedScope env world
      runtimeIncoming (toLeaTTaAtom atom) (toLeaTTaAtom expectedType) =
        .inr runtimeOutput) :
    ∃ output presentation,
      PreparedTypeCastRel oracle space atom expectedType incoming
          (atom, output) protectedScope ∧
        (∀ valuation,
          TypeSubstSatisfied valuation presentation ↔
            TypeBindingSatisfied valuation output) ∧
        ScopedTypePresentationSimulationState protectedScope
          presentation runtimeOutput := by
  rcases preparedTypeCast_candidateAlignment index realization input with
    ⟨sourceCandidates, specCandidates, runtimeCandidates,
      inputPresentation, runtimePresentation, runtimeSpecBindings,
      sourcePresent, specVariants, inputState, runtimeInput,
      runtimeInputState, _candidateAlpha, candidateConstraints,
      runtimeDisjoint, castEquation⟩
  rw [castEquation] at castSuccess
  obtain ⟨before, actualType, after, runtimeOutputPresentation,
      runtimeSpecOutput, split, beforeFailed, selectedMatch,
      runtimeOutputState⟩ :=
    matchExpectedType_success_corePlusR2_exact runtimeInputState expectedType
      runtimeCandidates runtimeDisjoint castSuccess
  have runtimeFirst : FirstTypeCastSuccessRel expectedType
      runtimeSpecBindings runtimeCandidates runtimeSpecOutput :=
    FirstTypeCastSuccessRel.of_split split beforeFailed selectedMatch
  obtain ⟨output, outputPresentation, specFirst, outputSolutions,
      outputScoped⟩ :=
    FirstTypeCastSuccessRel.exists_left_outputsScoped_of_constraints
      inputState runtimeInput
      runtimeOutputState candidateConstraints runtimeFirst
  exact ⟨output, outputPresentation,
    PreparedTypeCastRel.success sourcePresent specVariants specFirst,
    outputSolutions, outputScoped⟩

/-- A successful evaluator-aligned selection supplies the exact protected
operator-head cast required by `InterpretFunctionRel`.  The head symbol is
binding-neutral as syntax, while the selected binding theory may gain public
type information and may rename only private variables across the runtime
boundary. -/
theorem selectedOperatorHead_castSuccess
    {services : Services} {oracle : TypePreparationOracle}
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch}
    {live : List Atom}
    {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env)
    {world : Metta.Minimal.World}
    (realization : TypePreparationRuntimeRealization oracle space world)
    {observationScope : List String} {expression : Atom}
    {incoming selectedBindings : Bindings}
    {operator : String} {policy : Spec.Eval.SelectedTypePolicy}
    {runtime : Metta.Minimal.SelectedFunctionType}
    {runtimeOutput : Metta.Bindings}
    (selection : FunctionCandidateScanOutcomeRuntimeRelWith
      SelectedTypePolicyRuntimeExactRel observationScope expression incoming
        (.success policy selectedBindings) (.selected runtime))
    (operatorNotEmpty : operator ≠ "Empty")
    (castSuccess : Metta.Minimal.mettaTypeCastAvoiding observationScope env world
      runtime.typeBindings (.sym operator) runtime.functionType =
        .inr runtimeOutput) :
    ∃ output,
      EvalAtomRawRel space dispatch live
          (protectedScope := observationScope)
          (typing := preparedPackageTypeService oracle)
          (.symbol operator) policy.functionType selectedBindings
          (.symbol operator, output) ∧
        ScopedEvaluatorResultRuntimeRel services observationScope
          (.symbol operator, output) (.sym operator, runtimeOutput) := by
  obtain ⟨inputPresentation, inputSolutions, inputScoped⟩ :=
    selection.successBindingAtFunctionType
  cases selection with
  | success _base aligned =>
      have runtimeCast :
          Metta.Minimal.mettaTypeCastAvoiding observationScope env world
              runtime.typeBindings (toLeaTTaAtom (.symbol operator))
                (toLeaTTaAtom policy.functionType) =
            .inr runtimeOutput := by
        simpa [toLeaTTaAtom, aligned.runtimeFunctionType] using castSuccess
      obtain ⟨output, outputPresentation, serviceCast,
          outputSolutions, outputScoped⟩ :=
        preparedTypeCast_runtime_scoped_success index realization
          ⟨inputPresentation, inputSolutions, inputScoped⟩ runtimeCast
      have headCast :
          EvalAtomRawRel space dispatch live
            (protectedScope := observationScope)
            (typing := preparedPackageTypeService oracle)
            (.symbol operator) policy.functionType selectedBindings
            (.symbol operator, output) := by
        apply EvalAtomRawRel.cast
            (.symbol operator) policy.functionType Atom.symbolType
            selectedBindings (.symbol operator, output)
        · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty,
            operatorNotEmpty]
        · exact MetaTypeRel.symbol operator
        · have functionShape := policy.isFunction
          unfold FunctionTypeRel at functionShape
          rw [functionShape]
          simp [Atom.atomType, Atom.symbolType, Atom.variableType]
        · exact Or.inl ⟨operator, rfl⟩
        · simpa using serviceCast
      refine ⟨output, headCast, ?_⟩
      apply ScopedEvaluatorResultRuntimeRel.ofScopedUnchangedAtom
        outputSolutions outputScoped
        (LeaTTaMinimalInstructionConformance.AtomRuntimeRel.symbol
          (services := services) operator)
      simp [TypeSubst.apply]

/-- A structured operator-head `BadType` diagnostic can cross an already
scoped binding boundary.  Exactness stays on the specification side; the
expected field is literal and the rejected actual field alone is private
alpha-related. -/
theorem scopedOperatorBadType_privateCandidate
    {services : Services} {scope fixedScope : List String}
    {bindings : Bindings} {runtimeBindings : Metta.Bindings}
    {operator : String} {expected leftActual rightActual : Atom}
    {runtimeExpected : Metta.Atom}
    (state : ScopedEvaluatorBindingRuntimeRel scope bindings runtimeBindings)
    (expectedEquation : runtimeExpected = toLeaTTaAtom expected)
    (actualAlpha : PrivateCandidateAlphaRel
      fixedScope leftActual rightActual) :
    ScopedEvaluatorResultRuntimeRel services scope
      (mkError (.symbol operator) (.badType expected leftActual), bindings)
      (Metta.Minimal.badTypeAtom (.sym operator) runtimeExpected
        (toLeaTTaAtom rightActual), runtimeBindings) := by
  rcases state with ⟨presentation, solutions, runtimeState⟩
  refine ⟨presentation, solutions, runtimeState, Or.inr ?_, ?_⟩
  · apply EvaluatorDiagnosticAtomObservationRel.badType
    · exact ⟨.symbol operator, .sym operator,
        by simpa [TypeSubst.apply] using
          (ObservedTypeAlphaRel.refl (.symbol operator)),
        LeaTTaMinimalInstructionConformance.AtomRuntimeRel.symbol operator,
        rfl⟩
    · rw [expectedEquation]
      exact ScopedEvaluatorResultRuntimeRel.structuralAtom expected
    · exact ScopedEvaluatorResultRuntimeRel.structuralPrivateCandidate
        actualAlpha
  · simp [IsErrorRel, mkError, Atom.error,
      Metta.Minimal.badTypeAtom, Metta.Atom.isError]

/-- The failed selected operator-head cast produces exactly the published
`EvalAtomRawRel.cast` error alternatives, with ordered runtime candidates
retained by the failure bridge and fieldwise diagnostic observation. -/
theorem selectedOperatorHead_castFailure
    {services : Services} {oracle : TypePreparationOracle}
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch}
    {live : List Atom} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env)
    {world : Metta.Minimal.World}
    (realization : TypePreparationRuntimeRealization oracle space world)
    {observationScope : List String} {expression : Atom}
    {incoming selectedBindings : Bindings}
    {operator : String} {policy : Spec.Eval.SelectedTypePolicy}
    {runtime : Metta.Minimal.SelectedFunctionType}
    {rejected : List Metta.Atom}
    (selection : FunctionCandidateScanOutcomeRuntimeRelWith
      SelectedTypePolicyRuntimeExactRel observationScope expression incoming
        (.success policy selectedBindings) (.selected runtime))
    (operatorNotEmpty : operator ≠ "Empty")
    (castFailure : Metta.Minimal.mettaTypeCastAvoiding observationScope env world
      runtime.typeBindings (.sym operator) runtime.functionType =
        .inl rejected) :
    ∃ runtimeCandidates,
      rejected = toLeaTTaAtoms runtimeCandidates ∧
        ∀ runtimeActual ∈ runtimeCandidates,
          ∃ result,
            EvalAtomRawRel space dispatch live
              (protectedScope := observationScope)
              (typing := preparedPackageTypeService oracle)
              (.symbol operator) policy.functionType selectedBindings result ∧
            ScopedEvaluatorResultRuntimeRel services observationScope result
              (Metta.Minimal.badTypeAtom (.sym operator)
                runtime.functionType (toLeaTTaAtom runtimeActual),
                runtime.typeBindings) := by
  obtain ⟨inputPresentation, inputSolutions, inputScoped⟩ :=
    selection.successBindingAtFunctionType
  cases selection with
  | success _base aligned =>
      have runtimeCast :
          Metta.Minimal.mettaTypeCastAvoiding observationScope env world
              runtime.typeBindings (toLeaTTaAtom (.symbol operator))
                (toLeaTTaAtom policy.functionType) =
            .inl rejected := by
        simpa [toLeaTTaAtom, aligned.runtimeFunctionType] using castFailure
      obtain ⟨specCandidates, runtimeCandidates, rejectedEquation,
          _candidateAlpha, failures⟩ :=
        preparedTypeCast_runtime_scoped_failure index realization
          ⟨inputPresentation, inputSolutions, inputScoped⟩ runtimeCast
      refine ⟨runtimeCandidates, rejectedEquation, ?_⟩
      intro runtimeActual runtimeMember
      obtain ⟨specActual, _specMember, actualAlpha, serviceCast⟩ :=
        failures runtimeActual runtimeMember
      let result : ResultPair :=
        (mkError (.symbol operator)
          (.badType policy.functionType specActual), selectedBindings)
      have headCast : EvalAtomRawRel space dispatch live
          (protectedScope := observationScope)
          (typing := preparedPackageTypeService oracle)
          (.symbol operator) policy.functionType selectedBindings result := by
        apply EvalAtomRawRel.cast
            (.symbol operator) policy.functionType Atom.symbolType
            selectedBindings result
        · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty,
            operatorNotEmpty]
        · exact MetaTypeRel.symbol operator
        · have functionShape := policy.isFunction
          unfold FunctionTypeRel at functionShape
          rw [functionShape]
          simp [Atom.atomType, Atom.symbolType, Atom.variableType]
        · exact Or.inl ⟨operator, rfl⟩
        · simpa [result] using serviceCast
      refine ⟨result, headCast, ?_⟩
      have inputPublic : ScopedEvaluatorBindingRuntimeRel observationScope
          selectedBindings runtime.typeBindings :=
        ScopedEvaluatorBindingRuntimeRel.mono
          (⟨inputPresentation, inputSolutions, inputScoped⟩ :
            ScopedEvaluatorBindingRuntimeRel
              (observationScope ++ TypeSubst.typeVars policy.functionType)
              selectedBindings runtime.typeBindings)
          (fun name member => List.mem_append_left _ member)
      simpa [result] using scopedOperatorBadType_privateCandidate
        (services := services) inputPublic aligned.runtimeFunctionType.symm
          actualAlpha

/-- A failed runtime operator-head cast is already a complete published
`InterpretFunctionRel.headError` derivation.  Application seeding is a later
runtime-only transport of the emitted diagnostic binding payload; it does not
change the specification-side head failure. -/
theorem selectedOperatorHead_castFailure_interpretFunction
    {services : Services} {oracle : TypePreparationOracle}
    {space : Space} {dispatch : Spec.Eval.GroundedDispatch}
    {live : List Atom} {env : Metta.Minimal.MinEnv}
    (index : TypeEnvironmentRel space env)
    {world : Metta.Minimal.World}
    (realization : TypePreparationRuntimeRealization oracle space world)
    {expression returnType : Atom} {arguments : List Atom}
    {incoming selectedBindings : Bindings}
    {operator : String} {policy : Spec.Eval.SelectedTypePolicy}
    {runtime : Metta.Minimal.SelectedFunctionType}
    {rejected : List Metta.Atom}
    (expressionShape :
      expression = .expression (.symbol operator :: arguments))
    (selection : FunctionCandidateScanOutcomeRuntimeRelWith
      SelectedTypePolicyRuntimeExactRel
        (expectedApplicationScope expression returnType)
        expression incoming (.success policy selectedBindings)
          (.selected runtime))
    (operatorNotEmpty : operator ≠ "Empty")
    (castFailure : Metta.Minimal.mettaTypeCastAvoiding
      (expectedApplicationScope expression returnType) env world
        runtime.typeBindings (.sym operator) runtime.functionType =
          .inl rejected) :
    ∃ runtimeCandidates,
      rejected = toLeaTTaAtoms runtimeCandidates ∧
        ∀ runtimeActual ∈ runtimeCandidates,
          ∃ result,
            InterpretFunctionRel space dispatch live
              (typing := preparedPackageTypeService oracle)
              expression policy.functionType returnType selectedBindings
                result ∧
            ScopedEvaluatorResultRuntimeRel services
              (expectedApplicationScope expression returnType) result
              (Metta.Minimal.badTypeAtom (.sym operator)
                runtime.functionType (toLeaTTaAtom runtimeActual),
                runtime.typeBindings) := by
  obtain ⟨runtimeCandidates, rejectedEquation, failures⟩ :=
    selectedOperatorHead_castFailure index realization selection
      operatorNotEmpty castFailure
  refine ⟨runtimeCandidates, rejectedEquation, ?_⟩
  intro runtimeActual runtimeMember
  obtain ⟨result, headCast, resultRuntime⟩ :=
    failures runtimeActual runtimeMember
  have headError : IsEmptyOrErrorRel result.1 := by
    apply Or.inr
    apply (ScopedEvaluatorResultRuntimeRel.isError_iff
      (services := services) resultRuntime).mpr
    simp [Metta.Minimal.badTypeAtom, Metta.Atom.isError]
  refine ⟨result, ?_, resultRuntime⟩
  exact InterpretFunctionRel.headError
    expression policy.functionType returnType (.symbol operator)
      policy.returnType arguments policy.argumentTypes selectedBindings result
      expressionShape policy.isFunction headCast headError

end Mettapedia.Languages.MeTTa.HE.LeaTTaOperatorHeadCastConformance
