import Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationExactConformance
import Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationPrincipalAlpha

/-!
# Exact finite-presentation simulation of the application type fold

The repaired runtime carries equality-class bindings, while exact spec type
packages carry a normal finite substitution.  The simulation state relates
the finite presentation to the already-sealed native spec binding theory,
and relates that theory to LeaTTa independently through `TypeBindingState`.

Each successful runtime type match is reconstructed as one presentation
step by semantic completeness.  The resulting finite presentation is not
identified with LeaTTa's binding list; their declared-return observations
are related only up to the alpha theorem for mutually principal models.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationFoldConformance

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation
open Spec.Type.Presentation.Theory
open Spec.Type.Presentation.MatchSolutionTheory
open Spec.Type.Presentation.Completeness
open Spec.Type.Presentation.Alpha
open Spec.Type.Presentation.PrincipalAlpha
open Spec.Type.Presentation.Exact
open Spec.Type.RuntimeRefinement
open LeaTTaBridge
open LeaTTaSpecConformance
open LeaTTaTypeConformance

/-- The exact presentation carried alongside the semantic spec/LeaTTa
binding state.  `specSolutions` is representation-independent equality of
native solution sets; it does not identify the finite substitution with the
spec binding record. -/
structure TypePresentationSimulationState
    (presentation : TypeSubst) (spec : Bindings)
    (lea : Metta.Bindings) : Prop where
  normal : presentation.Normal
  specSolutions : ∀ valuation,
    TypeSubstSatisfied valuation presentation ↔
      TypeBindingSatisfied valuation spec
  semantic : TypeBindingState spec lea

/-- Empty finite, spec, and runtime presentations establish the simulation
state used at every application-inference boundary. -/
theorem typePresentationSimulationState_empty :
    TypePresentationSimulationState [] Bindings.empty
      Metta.Bindings.empty := by
  refine ⟨TypeSubst.normal_empty, ?_, typeBindingState_empty⟩
  intro valuation
  simp [TypeSubstSatisfied, TypeBindingSatisfied, Bindings.empty]

/-- A finite presentation paired with a reachable runtime binding theory is
semantically supported by the variables occurring in that runtime theory.
The presentation may use different private spellings syntactically; only
its complete solution theory is asserted to be insensitive away from the
runtime support. -/
theorem TypePresentationSimulationState.satisfied_congr_on_runtimeVars
    {presentation : TypeSubst} {spec : Bindings}
    {runtime : Metta.Bindings}
    (state : TypePresentationSimulationState presentation spec runtime)
    {left right : String → Atom}
    (agrees : ∀ name, name ∈ runtime.vars → left name = right name) :
    TypeSubstSatisfied left presentation ↔
      TypeSubstSatisfied right presentation := by
  rw [state.specSolutions left, state.specSolutions right]
  exact state.semantic.specSatisfied_congr_on_runtimeVars agrees

/-- Full one-step presentation simulation.  Besides the finite-presentation
derivation, retain the native core-plus-R2 match consumed by type-service
relations; projecting it away would force later boundaries to reconstruct the
same match from solution semantics.  The resulting normal finite presentation
has exactly the same native specification solution theory. -/
theorem TypePresentationSimulationState.matchTypeFull
    {presentation : TypeSubst} {spec : Bindings}
    {lea leaOutput : Metta.Bindings}
    (state : TypePresentationSimulationState presentation spec lea)
    (expected actual : Atom)
    (success : Metta.Minimal.matchType lea
      (toLeaTTaAtom expected) (toLeaTTaAtom actual) = some leaOutput) :
    ∃ presentationOutput specOutput,
      CorePlusR2TypePresentationMatchRel
          presentation expected actual presentationOutput ∧
        CorePlusR2TypeMatchRel expected actual spec specOutput ∧
        TypePresentationSimulationState
          presentationOutput specOutput leaOutput := by
  obtain ⟨specOutput, specMatch, semanticOutput⟩ :=
    matchType_corePlusR2_sound state.semantic success
  obtain ⟨valuation, outputSatisfied⟩ :=
    semanticOutput.specSatisfiable
  have parts := (specMatch.solutions valuation).mp outputSatisfied
  have presentationSatisfied :
      TypeSubstSatisfied valuation presentation :=
    (state.specSolutions valuation).mpr parts.1
  obtain ⟨presentationOutput, presentationMatch,
      outputNormal, _outputSatisfied⟩ :=
    CorePlusR2TypePresentationMatchRel.exists_of_satisfied
      state.normal presentationSatisfied expected actual parts.2
  refine ⟨presentationOutput, specOutput, presentationMatch, specMatch,
    ⟨outputNormal, ?_, semanticOutput⟩⟩
  intro otherValuation
  rw [Spec.Type.Presentation.MatchSolutionTheory.CorePlusR2TypePresentationMatchRel.solutions
        presentationMatch state.normal otherValuation,
    state.specSolutions otherValuation,
    ← specMatch.solutions otherValuation]

/-- Present any satisfiable native core-plus-R2 match as one exact normal
finite substitution extending the incoming presentation.  Unlike
`matchTypeFull`, this theorem is executable-independent: it starts from the
specification match relation itself and retains exactly the finite evidence
needed by alpha-transport and evaluator completeness. -/
theorem TypePresentationSimulationState.presentCorePlusR2
    {presentation : TypeSubst} {spec specOutput : Bindings}
    {runtime : Metta.Bindings} {expected actual : Atom}
    (state : TypePresentationSimulationState presentation spec runtime)
    (derivation : CorePlusR2TypeMatchRel expected actual spec specOutput) :
    ∃ presentationOutput,
      CorePlusR2TypePresentationMatchRel
          presentation expected actual presentationOutput ∧
        presentationOutput.Normal ∧
        ∀ valuation,
          TypeSubstSatisfied valuation presentationOutput ↔
            TypeBindingSatisfied valuation specOutput := by
  obtain ⟨valuation, outputSatisfied⟩ := derivation.satisfiable
  obtain ⟨incomingSatisfied, consistent⟩ :=
    (derivation.solutions valuation).mp outputSatisfied
  have presentationSatisfied :
      TypeSubstSatisfied valuation presentation :=
    (state.specSolutions valuation).mpr incomingSatisfied
  obtain ⟨presentationOutput, presentationMatch,
      outputNormal, _outputSatisfied⟩ :=
    CorePlusR2TypePresentationMatchRel.exists_of_satisfied
      state.normal presentationSatisfied expected actual consistent
  refine ⟨presentationOutput, presentationMatch, outputNormal, ?_⟩
  intro otherValuation
  rw [Spec.Type.Presentation.MatchSolutionTheory.CorePlusR2TypePresentationMatchRel.solutions
        presentationMatch state.normal otherValuation,
    state.specSolutions otherValuation,
    ← derivation.solutions otherValuation]

/-- Compatibility projection for consumers that need only the finite
presentation derivation and the resulting simulation state. -/
theorem TypePresentationSimulationState.matchType
    {presentation : TypeSubst} {spec : Bindings}
    {lea leaOutput : Metta.Bindings}
    (state : TypePresentationSimulationState presentation spec lea)
    (expected actual : Atom)
    (success : Metta.Minimal.matchType lea
      (toLeaTTaAtom expected) (toLeaTTaAtom actual) = some leaOutput) :
    ∃ presentationOutput specOutput,
      CorePlusR2TypePresentationMatchRel
          presentation expected actual presentationOutput ∧
        TypePresentationSimulationState
          presentationOutput specOutput leaOutput := by
  obtain ⟨presentationOutput, specOutput, presentationMatch,
      _specMatch, outputState⟩ :=
    state.matchTypeFull expected actual success
  exact ⟨presentationOutput, specOutput, presentationMatch, outputState⟩

/-- The finite presentation and LeaTTa's canonical runtime resolver observe
any declared type up to alpha-renaming. -/
theorem TypePresentationSimulationState.returnAlpha
    {presentation : TypeSubst} {spec : Bindings}
    {lea : Metta.Bindings}
    (state : TypePresentationSimulationState presentation spec lea)
    (declared : Atom) :
    ObservedTypeAlphaRel
      (presentation.apply declared)
      (fromLeaTTaAtom
        (Metta.instantiate lea (toLeaTTaAtom declared))) := by
  let leaModel := leaClassSolution lea
  let nativeModel : String → Atom :=
    fun name => fromLeaTTaAtom (leaModel name)
  have nativeModelSatisfied :
      TypeSubstSatisfied nativeModel presentation := by
    have specModel : HEBindingSatisfied leaModel spec :=
      (state.semantic.theory leaModel).mpr state.semantic.runtime.canonical.1
    have nativeSpecModel :=
      specTypeBindingSatisfied_of_heBindingSatisfied specModel
    exact (state.specSolutions nativeModel).mpr nativeSpecModel
  have presentationRefinesModel :
      ∃ post : String → Atom, ∀ name,
        presentedValuation presentation name =
          applyTypeValuation post (nativeModel name) := by
    let presentationModel := presentedValuation presentation
    let leaPresentationModel : String → Metta.Atom :=
      fun name => toLeaTTaAtom (presentationModel name)
    have presentationSatisfied :
        TypeSubstSatisfied presentationModel presentation :=
      normal_presentedValuation_satisfied state.normal
    have specPresentationSatisfied :
        TypeBindingSatisfied presentationModel spec :=
      (state.specSolutions presentationModel).mp presentationSatisfied
    have heaPresentationSatisfied :
        HEBindingSatisfied leaPresentationModel spec :=
      heBindingSatisfied_of_specTypeBindingSatisfied
        specPresentationSatisfied
    have leaPresentationSatisfied :
        LeaBindingSatisfied leaPresentationModel lea :=
      (state.semantic.theory leaPresentationModel).mp
        heaPresentationSatisfied
    obtain ⟨leaPost, hleaPost⟩ :=
      state.semantic.runtime.canonical.2
        leaPresentationModel leaPresentationSatisfied
    refine ⟨fun name => fromLeaTTaAtom (leaPost name), ?_⟩
    intro name
    have decoded := congrArg fromLeaTTaAtom (hleaPost name)
    rw [fromLeaTTaAtom_applyClassSolution_any] at decoded
    simpa [leaPresentationModel, presentationModel,
      nativeModel, leaModel] using decoded
  have alpha := observedTypeAlpha_of_mutuallyPrincipal state.normal
    nativeModelSatisfied presentationRefinesModel declared
  simpa [nativeModel, leaModel, ← fromLeaTTaAtom_applyClassSolution,
    applyClassSolution_lea_eq_instantiate] using alpha

/-- Repaired LeaTTa's left-to-right argument-type fold is realized by the
executable-independent finite-presentation fold, preserving the complete
simulation state. -/
theorem matchApplicationTypeArguments_presentation_sound :
    ∀ (expectedTypes actualTypes : List Atom)
      {presentation : TypeSubst} {spec : Bindings}
      {lea leaOutput : Metta.Bindings},
      TypePresentationSimulationState presentation spec lea →
      Metta.Minimal.matchApplicationTypeArguments lea
        (toLeaTTaAtoms expectedTypes) (toLeaTTaAtoms actualTypes) =
          some leaOutput →
      ∃ presentationOutput specOutput,
        PresentationArgumentListMatchRel expectedTypes actualTypes
            presentation presentationOutput ∧
          TypePresentationSimulationState
            presentationOutput specOutput leaOutput := by
  intro expectedTypes
  induction expectedTypes with
  | nil =>
      intro actualTypes presentation spec lea leaOutput state success
      cases actualTypes with
      | nil =>
          have same : lea = leaOutput := by
            simpa [toLeaTTaAtoms,
              Metta.Minimal.matchApplicationTypeArguments] using success
          subst leaOutput
          exact ⟨presentation, spec,
            PresentationArgumentListMatchRel.nil presentation, state⟩
      | cons actual actualTypes =>
          simp [toLeaTTaAtoms,
            Metta.Minimal.matchApplicationTypeArguments] at success
  | cons expected expectedTypes inductionHypothesis =>
      intro actualTypes presentation spec lea leaOutput state success
      cases actualTypes with
      | nil =>
          simp [toLeaTTaAtoms,
            Metta.Minimal.matchApplicationTypeArguments] at success
      | cons actual actualTypes =>
          simp only [toLeaTTaAtoms,
            Metta.Minimal.matchApplicationTypeArguments] at success
          generalize nextEquation : Metta.Minimal.matchType lea
            (toLeaTTaAtom expected) (toLeaTTaAtom actual) = next at success
          cases next with
          | none => simp at success
          | some leaNext =>
              obtain ⟨presentationNext, specNext,
                  headMatch, nextState⟩ :=
                state.matchType expected actual nextEquation
              obtain ⟨presentationOutput, specOutput,
                  tailMatch, outputState⟩ :=
                inductionHypothesis actualTypes nextState success
              exact ⟨presentationOutput, specOutput,
                PresentationArgumentListMatchRel.cons headMatch tailMatch,
                outputState⟩

/-- End-to-end fold boundary from empty input: the exact spec argument
presentation exists, and its emitted return is alpha-exactly LeaTTa's
instantiated return. -/
theorem matchApplicationTypeArguments_exact_return
    {expectedTypes actualTypes : List Atom}
    {leaOutput : Metta.Bindings} {returnType : Atom}
    (success : Metta.Minimal.matchApplicationTypeArguments
      Metta.Bindings.empty (toLeaTTaAtoms expectedTypes)
        (toLeaTTaAtoms actualTypes) = some leaOutput) :
    ∃ presentation specOutput,
      PresentationArgumentListMatchRel
          expectedTypes actualTypes [] presentation ∧
        TypePresentationSimulationState
          presentation specOutput leaOutput ∧
        ObservedTypeAlphaRel
          (presentation.apply returnType)
          (fromLeaTTaAtom
            (Metta.instantiate leaOutput (toLeaTTaAtom returnType))) := by
  obtain ⟨presentation, specOutput, fold, state⟩ :=
    matchApplicationTypeArguments_presentation_sound
      expectedTypes actualTypes typePresentationSimulationState_empty success
  exact ⟨presentation, specOutput, fold, state,
    state.returnAlpha returnType⟩

/-! ## Boundary examples -/

/-- Positive: the empty application fold produces the empty exact
presentation and preserves its simulation state. -/
theorem empty_application_fold_exact :
    ∃ presentation specOutput,
      PresentationArgumentListMatchRel [] [] [] presentation ∧
        TypePresentationSimulationState presentation specOutput
          Metta.Bindings.empty := by
  exact ⟨[], Bindings.empty,
    PresentationArgumentListMatchRel.nil [],
    typePresentationSimulationState_empty⟩

/-- Negative: unequal argument arities admit no presentation derivation. -/
theorem unequal_arity_has_no_presentation
    (expected : Atom) :
    ¬∃ output,
      PresentationArgumentListMatchRel [expected] [] [] output := by
  rintro ⟨output, derivation⟩
  cases derivation

end Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationFoldConformance
